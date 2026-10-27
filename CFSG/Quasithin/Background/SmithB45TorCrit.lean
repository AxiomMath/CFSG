module

public import CFSG.Quasithin.Background.SmithB45Disp
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

namespace B45Tor

open CFSG.QuasithinUnique.Setup.X5 CFSG.ComponentClassification B42Disp B45Disp

@[expose] def LineGenTop (M : Type*) [Group M] (E : Subgroup M) (n : ℕ) : Prop :=
  ∃ hs gs : List M,
    (∀ h ∈ hs, ∀ h' ∈ hs, ∀ a ∈ E, ∀ b ∈ E,
      h * a * h⁻¹ * (h' * b * h'⁻¹) = h' * b * h'⁻¹ * (h * a * h⁻¹)) ∧
    Subgroup.closure {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹} = ⊤ ∧
    Nat.card (Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹}) ^ (2 * gs.length) < n

section Offender

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem fixV_eq_bot_of_irr (L : Subgroup (MulAut V))
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) (hL : L ≠ ⊥) :
    fixV L = ⊥ := by
  rcases hirr (fixV L) (fun g _ u hu => by rw [hu g ‹_›]; exact hu) with h | h
  · exact h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixV L := by rw [h]; trivial
    exact hv g hg

theorem false_of_lineGenTop (L : Subgroup (MulAut V))
    (hZL : Subgroup.center L = ⊥)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {G A : Subgroup (MulAut V)}
    (hLG : L ≤ G) (hA : Is2FStar G A) (hAL : A ≤ L)
    (hE : LineGenTop M ((A.subgroupOf L).map (modelProj L e)) (Nat.card V)) : False := by
  obtain ⟨hs, gs, hcomm, hgen, hlt⟩ := hE
  have : Finite (MulAut V) := finite_mulAut
  set π := modelProj L e with hπdef
  set E := (A.subgroupOf L).map π with hEdef
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have := mem_center_of_modelProj_eq_one L e hl
    rwa [hZL, Subgroup.mem_bot] at this
  have : Finite M := Finite.of_equiv _ e.toEquiv
  choose lt hlt' using fun m : M => modelProj_surjective L e m
  have hπlt : ∀ m : M, π (lt m) = m := fun m => hlt' m
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2.2.1.2 a ha
  set ks : List (MulAut V) := hs.map fun h => (lt h : MulAut V) with hks
  have hksG : ∀ k ∈ ks, k ∈ G := by
    intro k hk
    obtain ⟨h, -, rfl⟩ := List.mem_map.1 hk
    exact hLG (lt h).2
  have hcommL : ∀ h ∈ hs, ∀ h' ∈ hs, ∀ a : L, (a : MulAut V) ∈ A → ∀ b : L,
      (b : MulAut V) ∈ A → lt h * a * (lt h)⁻¹ * (lt h' * b * (lt h')⁻¹) =
        lt h' * b * (lt h')⁻¹ * (lt h * a * (lt h)⁻¹) := by
    intro h hh h' hh' a ha b hb
    apply hπinj
    have hcm := hcomm h hh h' hh' (π a) ⟨a, ha, rfl⟩ (π b) ⟨b, hb, rfl⟩
    simp only [map_mul, map_inv, hπlt]
    exact hcm
  have hcommV : ∀ k ∈ ks, ∀ k' ∈ ks, ∀ a ∈ A, ∀ b ∈ A,
      k * a * k⁻¹ * (k' * b * k'⁻¹) = k' * b * k'⁻¹ * (k * a * k⁻¹) := by
    intro k hk k' hk' a ha b hb
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hk
    obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hk'
    exact congrArg Subtype.val (hcommL h hh h' hh' ⟨a, hAL ha⟩ ha ⟨b, hAL hb⟩ hb)
  set ΛV := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hΛV
  have hweight : Nat.card V ≤ Nat.card ΛV ^ 2 * Nat.card (fixV ΛV) :=
    card_le_weight2_closure_conj hA ks hksG hcommV
  set Λ := Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} with hΛ
  set SL : Set L := {y | ∃ h ∈ hs, ∃ a : L, (a : MulAut V) ∈ A ∧ y = lt h * a * (lt h)⁻¹}
    with hSL
  have hΛVmap : ΛV = (Subgroup.closure SL).map L.subtype := by
    rw [MonoidHom.map_closure, hΛV]
    congr 1
    ext y
    constructor
    · rintro ⟨k, hk, a, ha, rfl⟩
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hk
      exact ⟨_, ⟨h, hh, ⟨a, hAL ha⟩, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, hh, a, ha, rfl⟩, rfl⟩
      exact ⟨(lt h : MulAut V), List.mem_map_of_mem hh, a, ha, rfl⟩
  have hcardΛ : Nat.card ΛV ≤ Nat.card Λ := by
    have hle : (Subgroup.closure SL).map π ≤ Λ := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨h, hh, a, ha, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨h, hh, π a, ⟨a, ha, rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hπlt]
    calc Nat.card ΛV = Nat.card (Subgroup.closure SL) := by
          rw [hΛVmap]
          exact Subgroup.card_map_of_injective L.subtype_injective
      _ = Nat.card ((Subgroup.closure SL).map π) :=
          (Subgroup.card_map_of_injective hπinj).symm
      _ ≤ Nat.card Λ := Subgroup.card_le_of_le hle
  set gks : List (MulAut V) := gs.map fun g => (lt g : MulAut V) with hgks
  set YV := Subgroup.closure {y | ∃ k ∈ gks, ∃ a ∈ ΛV, y = k * a * k⁻¹} with hYV
  set TL : Set L := {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a : L, (a : MulAut V) ∈ A ∧
    y = lt g * (lt h * a * (lt h)⁻¹) * (lt g)⁻¹} with hTL
  have hTLmap : (Subgroup.closure TL).map π =
      Subgroup.closure {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, rfl⟩
      exact ⟨g, hg, h, hh, π a, ⟨a, ha, rfl⟩, by simp only [map_mul, map_inv, hπlt]⟩
    · rintro ⟨g, hg, h, hh, _, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, by simp only [map_mul, map_inv, hπlt]⟩
  rw [hgen] at hTLmap
  have hLY : L ≤ YV := by
    intro l hl
    have hmem : π ⟨l, hl⟩ ∈ (Subgroup.closure TL).map π := by rw [hTLmap]; trivial
    obtain ⟨y, hy, hyl⟩ := hmem
    have hyl' : y = ⟨l, hl⟩ := hπinj hyl
    have hle : (Subgroup.closure TL).map L.subtype ≤ YV := by
      rw [MonoidHom.map_closure, hYV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨(lt g : MulAut V), List.mem_map_of_mem hg,
        (lt h : MulAut V) * a * (lt h : MulAut V)⁻¹, ?_, rfl⟩
      exact Subgroup.subset_closure ⟨(lt h : MulAut V), List.mem_map_of_mem hh, a, ha, rfl⟩
    exact hle ⟨y, hy, by rw [hyl']; rfl⟩
  have hL1 : L ≠ ⊥ := by
    intro hL
    apply hA.2.1
    rw [eq_bot_iff]
    intro a ha
    have := hAL ha
    rwa [hL] at this
  have hfix : fixV YV = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [← fixV_eq_bot_of_irr L hirr hL1]
    exact fun x hx => hv x (hLY hx)
  have hidx : (fixV YV).index = Nat.card V := by rw [hfix, Subgroup.index_bot]
  have h3 : (fixV YV).index ≤ (fixV ΛV).index ^ gs.length := by
    have := index_fixV_closure_conj_le ΛV gks
    rwa [hgks, List.length_map] at this
  have h4 := index_fixV_le_card_sq_of_le hweight
  have h4' : (fixV ΛV).index ≤ Nat.card Λ ^ 2 :=
    h4.trans (Nat.pow_le_pow_left hcardΛ 2)
  have h5 := Nat.pow_le_pow_left h4' gs.length
  rw [← pow_mul] at h5
  omega

structure ClassTests (V : Type*) [CommGroup V] (L : Subgroup (MulAut V)) {M : Type*} [Group M]
    (e : L ⧸ Subgroup.center L ≃* M) (B : M → Prop) (r rA s : ℕ) : Prop where
  rank : ∀ E : Subgroup M, IsElem2 E → Nat.card E ≤ 2 ^ r
  pure : ∀ E : Subgroup M, IsElem2 E → (∀ ξ ∈ E, ξ ≠ 1 → ¬ B ξ) → Nat.card E ≤ 2 ^ rA
  index : ∀ F : Subgroup (MulAut M), IsElem2 F →
    Nat.card F ≤ 2 ^ s * Nat.card (F ⊓ (MulAut.conj : M →* MulAut M).range : Subgroup _)
  testB : ∀ x : L, (x : MulAut V) * x = 1 → x ≠ 1 → B (modelProj L e x) →
    2 ^ (2 * (r + s)) < (fixV (Subgroup.zpowers (x : MulAut V))).index
  testOut : ∀ x : Subgroup.normalizer (L : Set (MulAut V)), (x : MulAut V) * x = 1 →
    modelAct L e x ∉ (MulAut.conj : M →* MulAut M).range →
    2 ^ (2 * (rA + s)) < (fixV (Subgroup.zpowers (x : MulAut V))).index
  testPure : ∀ E : Subgroup M, E ≠ ⊥ → IsElem2 E → (∀ ξ ∈ E, ξ ≠ 1 → ¬ B ξ) →
    (∀ x : L, (x : MulAut V) * x = 1 → x ≠ 1 → modelProj L e x ∈ E →
      2 ^ (2 * rA) < (fixV (Subgroup.zpowers (x : MulAut V))).index) ∨
    LineGenTop M E (Nat.card V)

variable [Nontrivial V]

theorem not_is2FStar_of_classTests (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hperf : Group.IsPerfect L) (hZL : Subgroup.center L = ⊥)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {B : M → Prop} {r rA s : ℕ}
    (hT : ClassTests V L e B r rA s) {G A : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) : ¬ Is2FStar G A := by
  intro hA
  have := hperf
  have hoff := hA.card_le
  have hodd := centralizer_odd hV L hirr
  have hZ := center_eq_bot L e
  obtain ⟨hFcard, hF1, hFa⟩ := range_restrictAct hV L hperf hirr e hAN hA.2.1 hA.2.2.1
  set F := (restrictAct L e hAN).range with hFdef
  set F₀ := F ⊓ (MulAut.conj : M →* MulAut M).range with hF₀
  set E₀ := F₀.comap MulAut.conj with hE₀
  have hF₀le : F₀ ≤ (MulAut.conj : M →* MulAut M).range := inf_le_right
  have hF₀a : IsElem2 F₀ :=
    ⟨fun a ha b hb => hFa.1 a ha.1 b hb.1, fun a ha => hFa.2 a ha.1⟩
  have hE₀a : IsElem2 E₀ := isElem2_comap_conj hZ hF₀a
  have hE₀card : Nat.card E₀ = Nat.card F₀ := card_comap_conj hZ hF₀le
  have hFle := hT.index F hFa
  have hmemE₀ : ∀ ξ : M, ξ ∈ E₀ ↔ MulAut.conj ξ ∈ F := fun ξ =>
    ⟨fun h => h.1, fun h => ⟨h, ξ, rfl⟩⟩
  have hinner : ∀ (x : MulAut V) (hx : x ∈ A) (ξ : M),
      modelAct L e ⟨x, hAN hx⟩ = MulAut.conj ξ → ∃ hxL : x ∈ L, modelProj L e ⟨x, hxL⟩ = ξ := by
    intro x hx ξ hξ
    have h2 : x * x = 1 := by rw [← sq]; exact hA.2.2.1.2 x hx
    have hxL : x ∈ L := by
      refine mem_of_involution_inner L hodd (hAN hx) h2 ⟨e.symm ξ, (MulAut.congr e).injective ?_⟩
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ← modelAct_apply, hξ]
    refine ⟨hxL, conj_injective hZ ?_⟩
    rw [← hξ, modelProj_apply, ← modelAct_of_mem L e hxL]
  have hdisp : ∀ x ∈ A, (fixV (Subgroup.zpowers x)).index ≤ Nat.card F ^ 2 := fun x hx => by
    rw [hFcard]
    exact index_fixV_le_card_sq hoff hx
  by_cases hexB : ∃ ξ ∈ E₀, ξ ≠ 1 ∧ B ξ
  · obtain ⟨ξ, hξ, hξ1, hξB⟩ := hexB
    have hcard : Nat.card F ≤ 2 ^ (r + s) := by
      rw [pow_add, mul_comm]
      exact hFle.trans (Nat.mul_le_mul_left _ (hE₀card ▸ hT.rank E₀ hE₀a))
    obtain ⟨⟨x, hxA⟩, hxξ⟩ := (hmemE₀ ξ).1 hξ
    obtain ⟨hxL, hπx⟩ := hinner x hxA ξ hxξ
    have hx2 : x * x = 1 := by rw [← sq]; exact hA.2.2.1.2 x hxA
    have hx1 : (⟨x, hxL⟩ : L) ≠ 1 := fun h => hξ1 (by rw [← hπx, h, map_one])
    have h1 := hT.testB ⟨x, hxL⟩ hx2 hx1 (hπx ▸ hξB)
    have h2 := hdisp x hxA
    have h3 : Nat.card F ^ 2 ≤ 2 ^ (2 * (r + s)) :=
      calc Nat.card F ^ 2 ≤ (2 ^ (r + s)) ^ 2 := Nat.pow_le_pow_left hcard 2
        _ = 2 ^ (2 * (r + s)) := by rw [← pow_mul, mul_comm]
    exact absurd (h1.trans_le (h2.trans h3)) (lt_irrefl _)
  · push Not at hexB
    have hE₀pure : Nat.card E₀ ≤ 2 ^ rA := hT.pure E₀ hE₀a hexB
    by_cases hexO : ∃ α ∈ F, α ∉ (MulAut.conj : M →* MulAut M).range
    · obtain ⟨α, ⟨⟨x, hxA⟩, rfl⟩, hαO⟩ := hexO
      have hcard : Nat.card F ≤ 2 ^ (rA + s) := by
        rw [pow_add, mul_comm]
        exact hFle.trans (Nat.mul_le_mul_left _ (hE₀card ▸ hE₀pure))
      have hx2 : x * x = 1 := by rw [← sq]; exact hA.2.2.1.2 x hxA
      have h1 := hT.testOut ⟨x, hAN hxA⟩ hx2 hαO
      have h2 := hdisp x hxA
      have h3 : Nat.card F ^ 2 ≤ 2 ^ (2 * (rA + s)) :=
        calc Nat.card F ^ 2 ≤ (2 ^ (rA + s)) ^ 2 := Nat.pow_le_pow_left hcard 2
          _ = 2 ^ (2 * (rA + s)) := by rw [← pow_mul, mul_comm]
      exact absurd (h1.trans_le (h2.trans h3)) (lt_irrefl _)
    · push Not at hexO
      have hFinner : F ≤ (MulAut.conj : M →* MulAut M).range := fun α hα => hexO α hα
      have hFF₀ : F₀ = F := le_antisymm inf_le_left (le_inf le_rfl hFinner)
      have hcard : Nat.card F ≤ 2 ^ rA := by rw [← hFF₀, ← hE₀card]; exact hE₀pure
      have hAL : A ≤ L := by
        intro a ha
        obtain ⟨m, hm⟩ := hFinner ⟨⟨a, ha⟩, rfl⟩
        exact (hinner a ha m hm.symm).1
      have hEq : E₀ = (A.subgroupOf L).map (modelProj L e) := by
        ext m
        constructor
        · rintro ⟨⟨⟨a, ha⟩, ham⟩, -⟩
          obtain ⟨haL, hπa⟩ := hinner a ha m ham
          exact ⟨⟨a, haL⟩, ha, hπa⟩
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨⟨a, ha⟩, ?_⟩, ⟨_, rfl⟩⟩
          rw [modelProj_apply, ← modelAct_of_mem L e a.2]
          rfl
      have hE₀1 : E₀ ≠ ⊥ := by
        intro h
        apply hA.2.1
        rw [eq_bot_iff]
        intro a ha
        have hm : modelProj L e ⟨a, hAL ha⟩ ∈ E₀ := by rw [hEq]; exact ⟨⟨a, hAL ha⟩, ha, rfl⟩
        rw [h, Subgroup.mem_bot] at hm
        have := mem_center_of_modelProj_eq_one L e hm
        rw [hZL, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      rcases hT.testPure E₀ hE₀1 hE₀a hexB with hP | hline
      · obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA.2.1
        have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
        have ha2 : a * a = 1 := by rw [← sq]; exact hA.2.2.1.2 a haA
        have hx1 : (⟨a, hAL haA⟩ : L) ≠ 1 := fun h => ha1' (congrArg Subtype.val h)
        have hmem : modelProj L e ⟨a, hAL haA⟩ ∈ E₀ := by
          rw [hEq]
          exact ⟨⟨a, hAL haA⟩, haA, rfl⟩
        have h1 := hP ⟨a, hAL haA⟩ ha2 hx1 hmem
        have h2 := hdisp a haA
        have h3 : Nat.card F ^ 2 ≤ 2 ^ (2 * rA) :=
          calc Nat.card F ^ 2 ≤ (2 ^ rA) ^ 2 := Nat.pow_le_pow_left hcard 2
            _ = 2 ^ (2 * rA) := by rw [← pow_mul, mul_comm]
        exact absurd (h1.trans_le (h2.trans h3)) (lt_irrefl _)
      · rw [hEq] at hline
        exact false_of_lineGenTop L hZL hirr e hLG hA hAL hline

end Offender

theorem asB45No2FFor_of_classTests {Q : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ L : Subgroup (MulAut V), CFSG.IsQuasisimple ↥L →
        XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ → Q ↥L →
        Subgroup.center ↥L = ⊥ ∧ ∃ (M : Type) (_ : Group M) (e : ↥L ⧸ Subgroup.center ↥L ≃* M)
          (B : M → Prop) (r rA s : ℕ), ClassTests V L e B r rA s) :
    AsB45No2FFor Q := by
  intro V _ _ hV G L hHyp hQ
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := b4Hyp_data hHyp
  obtain ⟨hZL, M, _, e, B, r, rA, s, hT⟩ := h V hV L hHyp.2.2.1 hHyp.2.2.2 hQ
  unfold qhatOf
  rw [lt_kq_iff]
  intro A hA _
  by_contra hr
  push Not at hr
  have hoff := (rAV_le_two_iff hV hA).1 hr
  obtain ⟨B', hB'A, hB'⟩ := exists_is2FStar hA hoff
  exact not_is2FStar_of_classTests (fun v => by rw [← pow_two]; exact hV v) L hperf hZL hirr e hT
    hLG ((hB'A.trans hA.1).trans hGN) hB'

end B45Tor

end CFSG.Quasithin
