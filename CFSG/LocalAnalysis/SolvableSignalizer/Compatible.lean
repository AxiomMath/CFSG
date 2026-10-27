module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction

public section

namespace CFSG.SolvableSignalizer

section Auxiliary

variable {A G : Type*} [CommGroup A] [Group G] {α : A →* MulAut G} {θ : A → Subgroup G}

private theorem isInvariant_fixedBySubgroup (α : A →* MulAut G) (B : Subgroup A) :
    IsInvariant α (fixedBySubgroup α B) := by
  have stable : ∀ a : A, ∀ g ∈ fixedBySubgroup α B, α a g ∈ fixedBySubgroup α B := by
    intro a g hg
    rw [mem_fixedBySubgroup] at hg ⊢
    intro b hb
    have hcomm : α b (α a g) = α a (α b g) := by
      change (α b * α a) g = (α a * α b) g
      rw [← map_mul, ← map_mul, mul_comm b a]
    rw [hcomm, hg b hb]
  intro a
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    exact stable a x hx
  · intro g hg
    refine Subgroup.mem_map.mpr ⟨α a⁻¹ g, stable a⁻¹ g hg, ?_⟩
    change (α a * α a⁻¹) g = g
    simp

private theorem map_conj_value {c : G} (hc : c ∈ commonSignalizerWhole θ) {a : A}
    (ha : a ≠ 1) : (θ a).map (MulAut.conj c).toMonoidHom = θ a := by
  have h := (Subgroup.mem_normalizer_iff_map_conj_eq (H := θ a) (g := c)).mp
    (Subgroup.le_normalizer (mem_commonSignalizerWhole.mp hc a ha))
  simpa using h

private theorem conj_apply_comm {g : G} {a : A} (hfix : α a g = g) (x : G) :
    (MulAut.conj g).toMonoidHom (α a x) = α a ((MulAut.conj g).toMonoidHom x) := by
  simp [MulAut.conj_apply, hfix]

private theorem map_conj_inv_conj (H : Subgroup G) (c : G) :
    (H.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

private theorem map_conj_conj_inv (H : Subgroup G) (c : G) :
    (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = H := by
  simpa using map_conj_inv_conj H c⁻¹

private theorem isSolvable_map_conj {g : G} {H : Subgroup G} (hH : Group.IsSolvable H) :
    Group.IsSolvable (H.map (MulAut.conj g).toMonoidHom) := by
  let e := Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem map_conj_inv_iff {P : Subgroup G → Prop}
    (hP : ∀ {g : G}, g ∈ commonSignalizerWhole θ → ∀ {H : Subgroup G}, P H →
      P (H.map (MulAut.conj g).toMonoidHom))
    {c : G} (hc : c ∈ commonSignalizerWhole θ) (H : Subgroup G) :
    P (H.map (MulAut.conj c⁻¹).toMonoidHom) ↔ P H := by
  refine ⟨fun h => ?_, hP (inv_mem hc)⟩
  simpa only [map_conj_inv_conj] using hP hc h

end Auxiliary

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
  {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

theorem Compatible.of_le_of_isInvariant
    (_d : Datum p α θ) {H U : Subgroup G}
    (hH : Compatible p α θ H) (hUH : U ≤ H) (hU : IsInvariant α U) :
    Compatible p α θ U := by
  refine ⟨hU, ?_, ?_, ?_⟩
  · have : Group.IsSolvable H := hH.2.1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hUH)
  · exact hH.2.2.1.of_dvd_right (Subgroup.card_dvd_of_le hUH)
  · intro a ha
    exact (inf_le_inf_right _ hUH).trans (hH.2.2.2 a ha)

theorem compatible_bot (_d : Datum p α θ) : Compatible p α θ (⊥ : Subgroup G) := by
  refine ⟨fun a => ?_, inferInstance, ?_, fun a ha => ?_⟩
  · simp
  · simp
  · simp [fixedIn]

private theorem commonSignalizer_eq_fixedInBySubgroup (d : Datum p α θ)
    {B : Subgroup A} {a : A} (haB : a ∈ B) (ha : a ≠ 1) :
    commonSignalizer θ B = fixedInBySubgroup α (θ a) B := by
  apply le_antisymm
  · intro g hg
    have hall : ∀ b ∈ B, b ≠ 1 → g ∈ θ b := by
      simpa [commonSignalizer] using hg
    refine (mem_fixedInBySubgroup α (θ a) B g).mpr ⟨hall a haB ha, fun b hb => ?_⟩
    by_cases hbe : b = 1
    · simp [hbe]
    · exact d.central b hbe (hall b hb hbe)
  · intro g hg
    rw [mem_fixedInBySubgroup] at hg
    simp only [commonSignalizer, Subgroup.mem_iInf]
    intro b hb hbe
    exact d.balance a b ha hbe ⟨hg.1, hg.2 b hb⟩

theorem compatible_values_and_commonSignalizer (d : Datum p α θ) :
    (∀ a : A, a ≠ 1 → Compatible p α θ (θ a)) ∧
    (∀ B : Subgroup A, B ≠ ⊥ → ∀ a : A, a ∈ B → a ≠ 1 →
      commonSignalizer θ B = fixedInBySubgroup α (θ a) B ∧
      Compatible p α θ (commonSignalizer θ B)) ∧
    (∀ a : A, a ≠ 1 → fixedInBySubgroup α (θ a) ⊤ = commonSignalizerWhole θ) := by
  have hvalue : ∀ a : A, a ≠ 1 → Compatible p α θ (θ a) := fun a ha =>
    ⟨d.invariant a ha, d.solvable a ha, d.coprime a ha, fun b hb => d.balance a b ha hb⟩
  refine ⟨hvalue, fun B _ a haB ha => ?_, fun a ha => ?_⟩
  · have heq := commonSignalizer_eq_fixedInBySubgroup d haB ha
    refine ⟨heq, ?_⟩
    rw [heq]
    exact Compatible.of_le_of_isInvariant d (hvalue a ha) inf_le_left
      ((d.invariant a ha).inf (isInvariant_fixedBySubgroup α B))
  · exact (commonSignalizer_eq_fixedInBySubgroup d (Subgroup.mem_top a) ha).symm

private theorem iSup_fixedIn_eq_self (d : Datum p α θ) {H : Subgroup G}
    (hH : IsInvariant α H) (hcop : ¬ p ∣ Nat.card H) :
    ⨆ (a : A) (_ : a ≠ 1), fixedIn α H a = H := by
  have := d.isElementaryAbelian
  have h := congrArg (Subgroup.map H.subtype)
    (iSup_fixedSubgroup_eq_top p d.prime (restrictAction α H hH) d.rank_two hcop)
  simpa only [Subgroup.map_iSup, fixedSubgroup_restrictAction_map_subtype, Subgroup.map_top,
    Subgroup.range_subtype] using h

theorem eq_completionIn_and_le_completion (d : Datum p α θ)
    {H : Subgroup G} (hH : Compatible p α θ H) :
    H = completionIn θ H ∧ H ≤ completion θ := by
  obtain ⟨hInv, -, hCop, hFix⟩ := hH
  have hsup := iSup_fixedIn_eq_self d hInv (d.prime.coprime_iff_not_dvd.mp hCop)
  refine ⟨le_antisymm ?_ (completionIn_le θ H), ?_⟩
  · exact hsup.ge.trans (iSup₂_mono fun a ha => le_inf (hFix a ha) inf_le_left)
  · exact hsup.ge.trans (iSup₂_mono fun a ha => hFix a ha)

theorem primeSupported_spectrum_of_compatible (d : Datum p α θ)
    {H : Subgroup G} (hH : Compatible p α θ H) :
    primeSupported (spectrum θ) (Nat.card H) := by
  intro q hq hqdvd
  have := d.isElementaryAbelian
  have : Fact q.Prime := ⟨hq⟩
  have hcopH : ¬ p ∣ Nat.card H := d.prime.coprime_iff_not_dvd.mp hH.2.2.1
  obtain ⟨P, hPinv⟩ := exists_sylow_isInvariant p d.prime
    (CFSG.IsElementaryAbelian.isPGroup p A) (restrictAction α H hH.1) q hq hcopH
  let Q : Subgroup G := (P : Subgroup H).map H.subtype
  have hQle : Q ≤ H := Subgroup.map_subtype_le _
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card Q = 1 := by rw [hbot]; simp
    have hcardP : Nat.card (P : Subgroup H) = 1 := by
      rw [← Subgroup.card_map_of_injective (K := (P : Subgroup H)) (f := H.subtype)
        H.subtype_injective]
      exact hcard
    exact hq.not_dvd_one (hcardP ▸ P.dvd_card_of_dvd_card hqdvd)
  have hjoin : ⨆ (a : A) (_ : a ≠ 1), fixedIn α Q a = Q :=
    iSup_fixedIn_eq_self d ((isInvariant_restrictAction_iff hH.1 _).mp hPinv)
      fun h => hcopH (h.trans (Subgroup.card_dvd_of_le hQle))
  obtain ⟨a, ha, hne⟩ : ∃ a : A, a ≠ 1 ∧ fixedIn α Q a ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hQne (by rw [← hjoin]; exact iSup₂_eq_bot.mpr h)
  refine ⟨hq, a, ha, ?_⟩
  have hfixed : IsPGroup q (fixedIn α Q a) := (P.isPGroup'.map H.subtype).to_le inf_le_left
  rcases hfixed.card_eq_or_dvd with h1 | hdvd
  · exact absurd ((Subgroup.eq_bot_iff_card _).mpr h1) hne
  · exact hdvd.trans (Subgroup.card_dvd_of_le ((inf_le_inf_right _ hQle).trans (hH.2.2.2 a ha)))

theorem maxCompatibleWhole_completion_of_isComplete (d : Datum p α θ)
    (hc : IsComplete p α θ) :
    MaxCompatibleWhole p α θ (completion θ) ∧
    (∀ H : Subgroup G, MaxCompatibleWhole p α θ H → H = completion θ) ∧
    (∀ H : Subgroup G, Compatible p α θ H → H ≤ completion θ) := by
  have hcontains : ∀ H, Compatible p α θ H → H ≤ completion θ :=
    fun H hH => (eq_completionIn_and_le_completion d hH).2
  refine ⟨⟨hc, fun K hK _ => hcontains K hK⟩, fun H hH => ?_, hcontains⟩
  exact le_antisymm (hcontains H hH.1) (hH.2 _ hc (hcontains H hH.1))

theorem isComplete_iff_existsUnique_maxCompatibleWhole (d : Datum p α θ) :
    IsComplete p α θ ↔ ∃! H : Subgroup G, MaxCompatibleWhole p α θ H := by
  constructor
  · intro hc
    obtain ⟨hmax, huniq, -⟩ := maxCompatibleWhole_completion_of_isComplete d hc
    exact ⟨completion θ, hmax, huniq⟩
  · rintro ⟨M, hM, huniq⟩
    have hcontains : ∀ H, Compatible p α θ H → H ≤ M := by
      intro H hH
      obtain ⟨K, hHK, hK⟩ := Finite.exists_le_maximal hH
      rw [← huniq K ⟨hK.1, fun L hL hKL => hK.2 hL hKL⟩]
      exact hHK
    have hcM : completion θ ≤ M := iSup₂_le fun a ha =>
      hcontains (θ a) ((compatible_values_and_commonSignalizer d).1 a ha)
    have heq : completion θ = M := le_antisymm hcM (eq_completionIn_and_le_completion d hM.1).2
    simpa [IsComplete, heq] using hM.1

theorem fixedIn_completion_of_isComplete
    (d : Datum p α θ) (hc : IsComplete p α θ) :
    IsInvariant α (completion θ) ∧ Group.IsSolvable (completion θ) ∧
      Nat.Coprime p (Nat.card (completion θ)) ∧
      ∀ a : A, a ≠ 1 → fixedIn α (completion θ) a = θ a := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, fun a ha => ?_⟩
  exact le_antisymm (hc.2.2.2 a ha) (le_inf (le_iSup₂_of_le a ha le_rfl) (d.central a ha))

theorem compatible_completionIn_normalizer (d : Datum p α θ)
    (hloc : LocallyComplete p α θ) {W : Subgroup G}
    (hW : Compatible p α θ W) (hne : W ≠ ⊥) :
    let U := completionIn θ (Subgroup.normalizer (W : Set G))
    Compatible p α θ U ∧ W ≤ U ∧ (W.subgroupOf U).Normal ∧
      (∀ V : Subgroup G, Compatible p α θ V →
        V ≤ Subgroup.normalizer (W : Set G) → V ≤ U) ∧
      (∀ q : ℕ, IsPGroup q W → W ≤ (pCore q U).map U.subtype) := by
  intro U
  have hUN : U ≤ Subgroup.normalizer (W : Set G) := completionIn_le θ _
  have hcontains : ∀ V : Subgroup G, Compatible p α θ V →
      V ≤ Subgroup.normalizer (W : Set G) → V ≤ U := by
    intro V hV hVN
    rw [(eq_completionIn_and_le_completion d hV).1]
    exact iSup₂_mono fun _ _ => inf_le_inf_left _ hVN
  have hWU : W ≤ U := hcontains W hW Subgroup.le_normalizer
  have hnormal : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWU).mpr hUN
  refine ⟨hloc.1 W hW hne, hWU, hnormal, hcontains, fun q hWq => ?_⟩
  have hcore : W.subgroupOf U ≤ pCore q U :=
    le_sSup ⟨hnormal, hWq.of_equiv (Subgroup.subgroupOfEquivOfLe hWU).symm⟩
  intro w hw
  exact Subgroup.mem_map.mpr ⟨⟨w, hWU hw⟩, hcore hw, rfl⟩

private theorem apply_eq_of_mem_commonSignalizerWhole (d : Datum p α θ) {c : G}
    (hc : c ∈ commonSignalizerWhole θ) (a : A) : α a c = c := by
  by_cases ha : a = 1
  · simp [ha]
  · exact d.central a ha (mem_commonSignalizerWhole.mp hc a ha)

private theorem compatible_map_conj (d : Datum p α θ) {g : G}
    (hg : g ∈ commonSignalizerWhole θ) {H : Subgroup G} (hH : Compatible p α θ H) :
    Compatible p α θ (H.map (MulAut.conj g).toMonoidHom) := by
  have hfix := apply_eq_of_mem_commonSignalizerWhole d hg
  refine ⟨hH.1.map_conj hfix, isSolvable_map_conj hH.2.1, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hH.2.2.1
  · rintro a ha x ⟨hxH, hxa⟩
    obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp hxH
    have hyθ : y ∈ θ a := by
      refine hH.2.2.2 a ha ⟨hyH, (MulAut.conj g).injective ?_⟩
      have h : (MulAut.conj g).toMonoidHom (α a y) = (MulAut.conj g).toMonoidHom y := by
        rw [conj_apply_comm (hfix a) y]
        exact hxa
      exact h
    have hgθ := mem_commonSignalizerWhole.mp hg a ha
    simpa [MulAut.conj_apply] using
      (θ a).mul_mem ((θ a).mul_mem hgθ hyθ) ((θ a).inv_mem hgθ)

private theorem compatibleAt_map_conj (d : Datum p α θ) {g : G}
    (hg : g ∈ commonSignalizerWhole θ) {π : Set ℕ} {H : Subgroup G}
    (hH : CompatibleAt p α θ π H) :
    CompatibleAt p α θ π (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨compatible_map_conj d hg hH.1, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hH.2

private theorem maxCompatibleWhole_map_conj (d : Datum p α θ) {g : G}
    (hg : g ∈ commonSignalizerWhole θ) {H : Subgroup G} (hH : MaxCompatibleWhole p α θ H) :
    MaxCompatibleWhole p α θ (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨compatible_map_conj d hg hH.1, fun K hK hle => ?_⟩
  have hKH : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    refine hH.2 _ (compatible_map_conj d (inv_mem hg) hK) ?_
    rw [← map_conj_conj_inv H g]
    exact Subgroup.map_mono hle
  simpa only [map_conj_inv_conj] using Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKH

private theorem maxCompatible_map_conj (d : Datum p α θ) {g : G}
    (hg : g ∈ commonSignalizerWhole θ) {π : Set ℕ} {H : Subgroup G}
    (hH : MaxCompatible p α θ π H) :
    MaxCompatible p α θ π (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨compatibleAt_map_conj d hg hH.1, fun K hK hle => ?_⟩
  have hKH : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    refine hH.2 _ (compatibleAt_map_conj d (inv_mem hg) hK) ?_
    rw [← map_conj_conj_inv H g]
    exact Subgroup.map_mono hle
  simpa only [map_conj_inv_conj] using Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKH

theorem map_conj_of_mem_commonSignalizerWhole (d : Datum p α θ)
    {c : G} (hc : c ∈ commonSignalizerWhole θ) :
    (∀ a : A, a ≠ 1 → (θ a).map (MulAut.conj c⁻¹).toMonoidHom = θ a) ∧
    (∀ H : Subgroup G, Compatible p α θ (H.map (MulAut.conj c⁻¹).toMonoidHom) ↔
      Compatible p α θ H) ∧
    (∀ (π : Set ℕ) (H : Subgroup G),
      CompatibleAt p α θ π (H.map (MulAut.conj c⁻¹).toMonoidHom) ↔
      CompatibleAt p α θ π H) ∧
    (∀ H : Subgroup G,
      MaxCompatibleWhole p α θ (H.map (MulAut.conj c⁻¹).toMonoidHom) ↔
      MaxCompatibleWhole p α θ H) ∧
    (∀ (π : Set ℕ) (H : Subgroup G),
      MaxCompatible p α θ π (H.map (MulAut.conj c⁻¹).toMonoidHom) ↔
      MaxCompatible p α θ π H) :=
  ⟨fun _ ha => map_conj_value (inv_mem hc) ha,
    map_conj_inv_iff (compatible_map_conj d) hc,
    fun _ => map_conj_inv_iff (fun hg _ hH => compatibleAt_map_conj d hg hH) hc,
    map_conj_inv_iff (maxCompatibleWhole_map_conj d) hc,
    fun _ => map_conj_inv_iff (fun hg _ hH => maxCompatible_map_conj d hg hH) hc⟩

theorem map_conj_completionIn (d : Datum p α θ)
    {H : Subgroup G} (hH : IsInvariant α H) {c : G}
    (hc : c ∈ commonSignalizerWhole θ) :
    IsInvariant α (H.map (MulAut.conj c⁻¹).toMonoidHom) ∧
      (completionIn θ H).map (MulAut.conj c⁻¹).toMonoidHom =
        completionIn θ (H.map (MulAut.conj c⁻¹).toMonoidHom) := by
  refine ⟨hH.map_conj (apply_eq_of_mem_commonSignalizerWhole d (inv_mem hc)), ?_⟩
  rw [completionIn, completionIn, Subgroup.map_iSup]
  refine iSup_congr fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun ha => ?_
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c⁻¹).injective, map_conj_value (inv_mem hc) ha]

end CFSG.SolvableSignalizer
