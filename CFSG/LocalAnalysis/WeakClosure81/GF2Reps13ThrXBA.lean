module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

private theorem w16g_map_mul (U : Subgroup W) (g h : MulAut W) :
    (U.map g.toMonoidHom).map h.toMonoidHom = U.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_map_map_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [w16g_map_mul, inv_mul_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_map_map_inv' (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [w16g_map_mul, mul_inv_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_isIrrOn_map_of_normalizes {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X)
    {U : Subgroup W} (hU : IsIrrOn X U ⊥) : IsIrrOn X (U.map g.toMonoidHom) ⊥ := by
  obtain ⟨hlt, hUstab, -, hirr⟩ := hU
  have hstab : StableUnder X (U.map g.toMonoidHom) :=
    stableUnder_map_of_normalizes hg' hUstab
  have hlt' : ⊥ < U.map g.toMonoidHom := by
    have h := (Subgroup.map_lt_map_iff_of_injective (f := g.toMonoidHom) g.injective
      (H := (⊥ : Subgroup W)) (K := U)).mpr hlt
    rwa [Subgroup.map_bot] at h
  refine ⟨hlt', hstab, w16g_stableUnder_bot, ?_⟩
  intro J hJstab hbotJ hJle
  have hJ'stab : StableUnder X (J.map (g⁻¹).toMonoidHom) :=
    stableUnder_map_of_normalizes (g := g⁻¹) (by simpa using hg) hJstab
  have hJ'le : J.map (g⁻¹).toMonoidHom ≤ U := by
    have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hJle
    rwa [w16g_map_map_inv] at h
  rcases hirr (J.map (g⁻¹).toMonoidHom) hJ'stab bot_le hJ'le with h | h
  · left
    have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = (⊥ : Subgroup W) := by
      rw [h, Subgroup.map_bot]
    rwa [w16g_map_map_inv'] at h'
  · right
    have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U.map g.toMonoidHom := by
      rw [h]
    rwa [w16g_map_map_inv'] at h'

private theorem w16g_le_fixV_iff_of_secIsoOn {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) : A ≤ fixV X ↔ B ≤ fixV X := by
  obtain ⟨-, -, hSA, -, -, -, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  constructor
  · intro hA b hb
    rw [mem_fixV]
    intro x hx
    obtain ⟨a, ha⟩ := hβsurj b hb
    have hba : β a = b := mul_inv_eq_one.mp (by simpa using ha)
    have h1 : β ⟨x (a : W), hSA x hx (a : W) a.2⟩ = x (β a) := by
      have h2 := hβeq x hx a ⟨x (a : W), hSA x hx (a : W) a.2⟩ rfl
      exact mul_inv_eq_one.mp (by simpa using h2)
    have h3 : x (a : W) = (a : W) := (mem_fixV.mp (hA a.2)) x hx
    have hxaeq : (⟨x (a : W), hSA x hx (a : W) a.2⟩ : ↥A) = a := Subtype.ext h3
    calc x b = x (β a) := by rw [← hba]
      _ = β ⟨x (a : W), hSA x hx (a : W) a.2⟩ := h1.symm
      _ = β a := by rw [hxaeq]
      _ = b := hba
  · intro hB a ha
    rw [mem_fixV]
    intro x hx
    have h1 : β ⟨x a, hSA x hx a ha⟩ = x (β ⟨a, ha⟩) := by
      have h2 := hβeq x hx ⟨a, ha⟩ ⟨x a, hSA x hx a ha⟩ rfl
      exact mul_inv_eq_one.mp (by simpa using h2)
    have h2 : x (β ⟨a, ha⟩) = β ⟨a, ha⟩ :=
      (mem_fixV.mp (hB (hβB ⟨a, ha⟩))) x hx
    have h3 : β (⟨x a, hSA x hx a ha⟩ * ⟨a, ha⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, h2, mul_inv_cancel]
    have h4 : (⟨x a, hSA x hx a ha⟩ * ⟨a, ha⟩⁻¹ : ↥A) = 1 :=
      Subtype.ext ((hβone _).mp h3)
    have h5 : x a * a⁻¹ = 1 := by simpa using congrArg Subtype.val h4
    exact mul_inv_eq_one.mp h5

private theorem w16g_commSub_eq_self_of_isIrrOn {X : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : IsIrrOn X V ⊥) (hbot : V ⊓ fixV X = ⊥) : commSub V X = V := by
  have hstab : StableUnder X (commSub V X) :=
    stableUnder_commSub (fun h hh x hx => X.mul_mem (X.mul_mem hh hx) (X.inv_mem hh)) hV.2.1
  have hne : commSub V X ≠ ⊥ := by
    intro h
    have hVfix : V ≤ fixV X := commSub_eq_bot_iff.mp h
    have : V ≤ (⊥ : Subgroup W) := by
      rw [← hbot]
      exact le_inf le_rfl hVfix
    exact hV.1.ne' (le_bot_iff.mp this)
  rcases hV.2.2.2 (commSub V X) hstab bot_le (commSub_le_of_invariant hV.2.1) with h | h
  · exact absurd h hne
  · exact h

private theorem w16g_commSub_map_conj (U : Subgroup W) (L : Subgroup (MulAut W))
    (g : MulAut W) :
    commSub (U.map g.toMonoidHom) (L.map (MulAut.conj g).toMonoidHom) =
      (commSub U L).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨y, ⟨l, hl, rfl⟩, w, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨l u * u⁻¹, ⟨l, hl, u, hu, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  · rintro ⟨d, ⟨l, hl, u, hu, rfl⟩, rfl⟩
    refine ⟨g * l * g⁻¹, ⟨l, hl, rfl⟩, g u, ⟨u, hu, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

private theorem w16g_le_s13IsoSum {X : Subgroup (MulAut W)} {U₀ V₁ : Subgroup W}
    (h : IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥) : V₁ ≤ s13IsoSum X U₀ := by
  unfold s13IsoSum
  exact le_iSup₂ (f := fun W₁ (_ : IsIrrOn X W₁ ⊥ ∧ SecIsoOn X W₁ ⊥ U₀ ⊥) => W₁) V₁ h

private theorem w16g_s13IsoSum_map {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) (U₀ : Subgroup W) :
    (s13IsoSum X U₀).map g.toMonoidHom = s13IsoSum X (U₀.map g.toMonoidHom) := by
  apply le_antisymm
  · unfold s13IsoSum
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_iSup]
    refine iSup_le fun V₁ => iSup_le fun h => ?_
    exact w16g_le_s13IsoSum ⟨w16g_isIrrOn_map_of_normalizes hg hg' h.1,
      by simpa only [Subgroup.map_bot] using secIsoOn_map hg hg' h.2⟩
  · conv_lhs => unfold s13IsoSum
    refine iSup_le fun V₁ => iSup_le fun h => ?_
    have hg1 : ∀ x ∈ X, g⁻¹ * x * (g⁻¹)⁻¹ ∈ X := by simpa using hg'
    have hg1' : ∀ x ∈ X, (g⁻¹)⁻¹ * x * g⁻¹ ∈ X := by simpa using hg
    have hV₁ : IsIrrOn X (V₁.map (g⁻¹).toMonoidHom) ⊥ ∧
        SecIsoOn X (V₁.map (g⁻¹).toMonoidHom) ⊥ U₀ ⊥ := by
      refine ⟨w16g_isIrrOn_map_of_normalizes hg1 hg1' h.1, ?_⟩
      have hsec := secIsoOn_map hg1 hg1' h.2
      simpa only [Subgroup.map_bot, w16g_map_map_inv] using hsec
    have hle : V₁.map (g⁻¹).toMonoidHom ≤ s13IsoSum X U₀ := w16g_le_s13IsoSum hV₁
    have := Subgroup.map_mono (f := g.toMonoidHom) hle
    rwa [w16g_map_map_inv'] at this

private theorem w16g_inv_mem_of_mapsTo {U : Subgroup W} {a : MulAut W}
    (hU : ∀ v ∈ U, a v ∈ U) : ∀ u ∈ U, a⁻¹ u ∈ U := by
  have hmap : U.map a.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨v, hv, rfl⟩
      exact hU v hv
    · rw [Subgroup.card_map_of_injective a.injective]
  intro u hu
  have hu' : u ∈ U.map a.toMonoidHom := by rw [hmap]; exact hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu'
  have hvu' : a v = u := hvu
  rw [← hvu', ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  exact hv

theorem w16g_commSub_sup_le_of_le_centSub (hW : ∀ w : W, w * w = 1)
    {U : Subgroup W} {H : Subgroup (MulAut W)} {X Z : Subgroup (MulAut W)}
    (hH : H ≤ centSub U) (hU : StableUnder X U) (hZ : Z ≤ X) :
    commSub U (H ⊔ Z) ≤ commSub U Z := by
  let T : Subgroup (MulAut W) :=
    { carrier := {x | ∀ u ∈ U, x u ∈ U ∧ x u * u⁻¹ ∈ commSub U Z}
      one_mem' := fun u hu => by
        refine ⟨?_, ?_⟩
        · rwa [MulAut.one_apply]
        · rw [MulAut.one_apply, mul_inv_cancel]; exact Subgroup.one_mem _
      mul_mem' := by
        intro a b ha hb u hu
        obtain ⟨hbu, hbcomm⟩ := hb u hu
        obtain ⟨habu, hacomm⟩ := ha (b u) hbu
        refine ⟨habu, ?_⟩
        have h5 : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
          rw [MulAut.mul_apply]; group
        rw [h5]
        exact (commSub U Z).mul_mem hacomm hbcomm
      inv_mem' := by
        intro a ha u hu
        have haU : ∀ v ∈ U, a v ∈ U := fun v hv => (ha v hv).1
        have hmem : a⁻¹ u ∈ U := w16g_inv_mem_of_mapsTo haU u hu
        have h2 : a (a⁻¹ u) * (a⁻¹ u)⁻¹ ∈ commSub U Z := (ha (a⁻¹ u) hmem).2
        refine ⟨hmem, ?_⟩
        have h4 : a (a⁻¹ u) = u := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        have h5 : a⁻¹ u * u⁻¹ = (a (a⁻¹ u) * (a⁻¹ u)⁻¹)⁻¹ := by
          rw [h4]; group
        rw [h5]
        exact (commSub U Z).inv_mem h2 }
  have hHT : H ≤ T := by
    intro h hh u hu
    have hz : h u = u := (mem_centSub.mp (hH hh)) u hu
    exact ⟨by rw [hz]; exact hu, by rw [hz, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  have hZT : Z ≤ T := by
    intro z hz u hu
    exact ⟨hU z (hZ hz) u hu, Subgroup.subset_closure ⟨z, hz, u, hu, rfl⟩⟩
  have hle : H ⊔ Z ≤ T := sup_le hHT hZT
  rw [commSub]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, u, hu, rfl⟩
  exact (hle hx u hu).2

private theorem w16g_commSub_iSup_left {ι : Sort*} (U : ι → Subgroup W)
    (X : Subgroup (MulAut W)) :
    commSub (⨆ i, U i) X = ⨆ i, commSub (U i) X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    refine Subgroup.iSup_induction U
      (C := fun w => x w * w⁻¹ ∈ ⨆ i, commSub (U i) X) hw ?_ ?_ ?_
    · intro i u hu
      exact Subgroup.mem_iSup_of_mem i (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
    · simp
    · intro a b ha hb
      have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h1]
      exact (⨆ i, commSub (U i) X).mul_mem ha hb
  · exact iSup_le fun i => commSub_mono (le_iSup U i) le_rfl

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Finite X := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 (x : MulAut W) x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn]
  exact Odd.pow (hp.odd_of_ne_two hp2)

theorem w16g_map_mem_s13IsoComps {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {U : Subgroup W}
    (hU : U ∈ s13IsoComps X) : U.map g.toMonoidHom ∈ s13IsoComps X := by
  obtain ⟨U₀, hirr₀, hne₀, hUeq⟩ := hU
  rw [hUeq]
  refine ⟨U₀.map g.toMonoidHom, w16g_isIrrOn_map_of_normalizes hg hg' hirr₀, ?_,
    w16g_s13IsoSum_map hg hg' U₀⟩
  rw [commSub_map_of_normalizes hg hg']
  intro h
  exact hne₀ ((Subgroup.map_eq_bot_iff_of_injective (commSub U₀ X) g.injective).mp h)

theorem w16g_s13Supp_conj {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    s13Supp X (L.map (MulAut.conj g).toMonoidHom) =
      (fun U : Subgroup W => U.map g.toMonoidHom) '' s13Supp X L := by
  ext U
  constructor
  · intro hU
    obtain ⟨hUcomp, hUne⟩ := hU
    refine ⟨U.map (g⁻¹).toMonoidHom, ⟨?_, ?_⟩, w16g_map_map_inv' U g⟩
    · exact w16g_map_mem_s13IsoComps (g := g⁻¹) (by simpa using hg') (by simpa using hg) hUcomp
    · intro h
      apply hUne
      have hform := w16g_commSub_map_conj (U.map (g⁻¹).toMonoidHom) L g
      rw [w16g_map_map_inv', h, Subgroup.map_bot] at hform
      exact hform
  · rintro ⟨V, hV, hVU⟩
    rw [← hVU]
    refine ⟨w16g_map_mem_s13IsoComps hg hg' hV.1, ?_⟩
    rw [w16g_commSub_map_conj V L g]
    intro h
    exact hV.2 ((Subgroup.map_eq_bot_iff_of_injective (commSub V L) g.injective).mp h)

private theorem w16g_sup_zpowers_eq_of_relIndex {H X : Subgroup (MulAut W)} {ℓ : MulAut W}
    {p : ℕ} (hp : p.Prime) (hHle : H ≤ X) (hHrel : H.relIndex X = p) (hℓX : ℓ ∈ X)
    (hℓnot : ℓ ∉ H) : H ⊔ Subgroup.zpowers ℓ = X := by
  have hle : H ⊔ Subgroup.zpowers ℓ ≤ X := sup_le hHle (Subgroup.zpowers_le.mpr hℓX)
  have h1 := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers ℓ) X le_sup_left hle
  rw [hHrel] at h1
  have hne1 : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ≠ 1 := by
    intro h
    have hle' : H ⊔ Subgroup.zpowers ℓ ≤ H := Subgroup.relIndex_eq_one.mp h
    have hzle : Subgroup.zpowers ℓ ≤ H :=
      le_trans (le_sup_right : Subgroup.zpowers ℓ ≤ H ⊔ Subgroup.zpowers ℓ) hle'
    exact hℓnot (hzle (Subgroup.mem_zpowers ℓ))
  have hdvd : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ∣ p := ⟨_, h1.symm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with hd1 | hdp
  · exact absurd hd1 hne1
  · have he1 : (H ⊔ Subgroup.zpowers ℓ).relIndex X = 1 := by
      have h1' := h1
      rw [hdp] at h1'
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1')
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp he1)

private theorem w16g_commSub_isotypic_eq_self {X : Subgroup (MulAut W)} {U₀ : Subgroup W}
    (hirr₀ : IsIrrOn X U₀ ⊥) (hne₀ : commSub U₀ X ≠ ⊥)
    (hUstab : StableUnder X (s13IsoSum X U₀)) :
    commSub (s13IsoSum X U₀) X = s13IsoSum X U₀ := by
  refine le_antisymm (commSub_le_of_invariant hUstab) ?_
  unfold s13IsoSum
  refine iSup_le fun V₁ => iSup_le fun hV₁ => ?_
  have hV₁bot : V₁ ⊓ fixV X = ⊥ := by
    have hstab : StableUnder X (V₁ ⊓ fixV X) :=
      stableUnder_inf hV₁.1.2.1
        (stableUnder_fixV (fun y hy h hh => X.mul_mem (X.mul_mem hy hh) (X.inv_mem hy)))
    rcases hV₁.1.2.2.2 (V₁ ⊓ fixV X) hstab bot_le inf_le_left with h | h
    · exact h
    · exfalso
      have hV₁fix : V₁ ≤ fixV X := by rw [← h]; exact inf_le_right
      have hU₀fix : U₀ ≤ fixV X := (w16g_le_fixV_iff_of_secIsoOn hV₁.2).mp hV₁fix
      exact hne₀ (commSub_eq_bot_iff.mpr hU₀fix)
  rw [← w16g_commSub_eq_self_of_isIrrOn hV₁.1 hV₁bot]
  exact commSub_mono (w16g_le_s13IsoSum hV₁) le_rfl

private theorem w16g_commSub_eq_of_not_le_ker (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    {L : Subgroup (MulAut W)} (hLX : L ≤ X) {U U₀ : Subgroup W}
    (hirr₀ : IsIrrOn X U₀ ⊥) (hne₀ : commSub U₀ X ≠ ⊥) (hUeq : U = s13IsoSum X U₀)
    (hUstab : StableUnder X U) (hLnot : ¬ L ≤ s13KerOn X U) : commSub U L = U := by
  have hUle : commSub U L ≤ U :=
    commSub_le_of_invariant (fun x hx => hUstab x (hLX hx))
  have hHleCent : s13KerOn X U ≤ centSub U := inf_le_right
  have hℓ : ∃ ℓ ∈ L, ℓ ∉ s13KerOn X U := by
    by_contra h
    push Not at h
    exact hLnot h
  obtain ⟨ℓ, hℓL, hℓnot⟩ := hℓ
  have hℓX : ℓ ∈ X := hLX hℓL
  have hHmem := s13KerOn_mem_hyperplanes hW hp hp2 hX (U := U) ⟨U₀, hirr₀, hne₀, hUeq⟩
  have hHle : s13KerOn X U ≤ X := hHmem.1
  have hHrel : (s13KerOn X U).relIndex X = p := hHmem.2
  have hsup : s13KerOn X U ⊔ Subgroup.zpowers ℓ = X :=
    w16g_sup_zpowers_eq_of_relIndex (H := s13KerOn X U) (X := X) (ℓ := ℓ) (p := p)
      hp hHle hHrel hℓX hℓnot
  have hcommUX : commSub U X = U := by
    rw [hUeq]
    exact w16g_commSub_isotypic_eq_self (X := X) (U₀ := U₀) hirr₀ hne₀
      (by rw [← hUeq]; exact hUstab)
  have hle1 : commSub U X ≤ commSub U (Subgroup.zpowers ℓ) := by
    rw [← hsup]
    exact w16g_commSub_sup_le_of_le_centSub hW (U := U) (H := s13KerOn X U) (X := X)
      (Z := Subgroup.zpowers ℓ) hHleCent hUstab (Subgroup.zpowers_le.mpr hℓX)
  have hmid : commSub U X ≤ commSub U L :=
    hle1.trans (commSub_mono (le_rfl : U ≤ U) (Subgroup.zpowers_le.mpr hℓL))
  have : U ≤ commSub U L := by rwa [hcommUX] at hmid
  exact le_antisymm hUle this

theorem w16g_s13IsoComps_commSub_eq (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {L : Subgroup (MulAut W)} (hLX : L ≤ X)
    {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    (L ≤ s13KerOn X U → commSub U L = ⊥) ∧ (¬ L ≤ s13KerOn X U → commSub U L = U) := by
  obtain ⟨U₀, hirr₀, hne₀, hUeq⟩ := hU
  have hUstab : StableUnder X U := s13IsoComps_stable ⟨U₀, hirr₀, hne₀, hUeq⟩
  have hHleCent : s13KerOn X U ≤ centSub U := inf_le_right
  constructor
  · intro hL
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro x hx
    exact (mem_centSub.mp (hHleCent (hL hx))) u hu
  · intro hLnot
    exact w16g_commSub_eq_of_not_le_ker hW hp hp2 hX hLX hirr₀ hne₀ hUeq hUstab hLnot

theorem w16g_commSub_top_eq_iSup_s13Supp (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    {L : Subgroup (MulAut W)} (hLX : L ≤ X) :
    commSub ⊤ L = ⨆ U ∈ s13Supp X L, U := by
  have hXodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 hX
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hdecomp : fixV X ⊔ commSub ⊤ X = ⊤ := by
    have h := (CFSG.Quasithin.B1.coprime_decomp hW2 hXodd (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).1
    rwa [top_inf_eq] at h
  have hXsum : (⨆ U ∈ s13IsoComps X, U) = commSub ⊤ X := iSup_s13IsoComps hW hXodd
  have hfix : commSub (fixV X) L = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro y hy
    exact (mem_fixV.mp hu) y (hLX hy)
  have h2 : commSub ⊤ L = commSub (⨆ U ∈ s13IsoComps X, U) L := by
    calc commSub ⊤ L = commSub (fixV X ⊔ commSub ⊤ X) L := by rw [hdecomp]
      _ = commSub (fixV X) L ⊔ commSub (commSub ⊤ X) L :=
            CFSG.Quasithin.commSub_sup_left (fixV X) (commSub ⊤ X) L
      _ = commSub (commSub ⊤ X) L := by rw [hfix, bot_sup_eq]
      _ = commSub (⨆ U ∈ s13IsoComps X, U) L := by rw [hXsum]
  have h3 : commSub (⨆ U ∈ s13IsoComps X, U) L = ⨆ U ∈ s13IsoComps X, commSub U L := by
    rw [← iSup_subtype'' (s13IsoComps X) (fun U : Subgroup W => U)]
    rw [w16g_commSub_iSup_left]
    rw [iSup_subtype'' (s13IsoComps X) (fun U : Subgroup W => commSub U L)]
  have h4 : (⨆ U ∈ s13IsoComps X, commSub U L) = ⨆ U ∈ s13Supp X L, U := by
    apply le_antisymm
    · refine iSup_le fun U => iSup_le fun hU => ?_
      by_cases hLk : L ≤ s13KerOn X U
      · rw [(w16g_s13IsoComps_commSub_eq hW hp hp2 hX hLX hU).1 hLk]
        exact bot_le
      · have heq := (w16g_s13IsoComps_commSub_eq hW hp hp2 hX hLX hU).2 hLk
        rw [heq]
        exact le_iSup₂ (f := fun U (_ : U ∈ s13Supp X L) => U) U
          ⟨hU, by rw [heq]; exact (s13IsoComps_le_commSub hW hXodd hU).1⟩
    · refine iSup_le fun U => iSup_le fun hU => ?_
      have hne : commSub U L ≠ ⊥ := hU.2
      have hLk : ¬ L ≤ s13KerOn X U := by
        intro hLk
        exact hne ((w16g_s13IsoComps_commSub_eq hW hp hp2 hX hLX hU.1).1 hLk)
      have heq := (w16g_s13IsoComps_commSub_eq hW hp hp2 hX hLX hU.1).2 hLk
      rw [← heq]
      exact le_iSup₂ (f := fun U (_ : U ∈ s13IsoComps X) => commSub U L) U hU.1
  rw [h2, h3, h4]

private theorem w16g_disjoint_sSup_sdiff_comps (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} (hXodd : Odd (Nat.card X)) {S : Set (Subgroup W)}
    (hS : S ⊆ s13IsoComps X) :
    Disjoint (sSup S) (sSup (s13IsoComps X \ S)) := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective (fun S : Subgroup W => (S : Set W))
    SetLike.coe_injective
  have hind : sSupIndep (s13IsoComps X) := s13IsoComps_sSupIndep hW hXodd
  have hi : iSupIndep ((↑) : s13IsoComps X → Subgroup W) := (sSupIndep_iff _).mp hind
  have hst : Disjoint {U : s13IsoComps X | (U : Subgroup W) ∈ S}
      {U : s13IsoComps X | (U : Subgroup W) ∈ s13IsoComps X \ S} := by
    rw [Set.disjoint_left]
    intro U hUS hUc
    exact hUc.2 hUS
  have hd := iSupIndep.disjoint_biSup_biSup' hi hst (Set.toFinite _)
  have hSsup : sSup S = ⨆ U ∈ {U : s13IsoComps X | (U : Subgroup W) ∈ S},
      (U : Subgroup W) := by
    apply le_antisymm
    · refine sSup_le fun U hU => ?_
      exact le_iSup₂ (f := fun U : s13IsoComps X => fun _ : (U : Subgroup W) ∈ S =>
        (U : Subgroup W)) ⟨U, hS hU⟩ hU
    · refine iSup₂_le fun U hU => ?_
      exact le_sSup hU
  have hScd : sSup (s13IsoComps X \ S) =
      ⨆ U ∈ {U : s13IsoComps X | (U : Subgroup W) ∈ s13IsoComps X \ S},
        (U : Subgroup W) := by
    apply le_antisymm
    · refine sSup_le fun U hU => ?_
      exact le_iSup₂ (f := fun U : s13IsoComps X =>
        fun _ : (U : Subgroup W) ∈ s13IsoComps X \ S => (U : Subgroup W)) ⟨U, hU.1⟩ hU
    · refine iSup₂_le fun U hU => ?_
      exact le_sSup hU
  rwa [hSsup, hScd]

private theorem w16g_s13Supp_conj_mul {X L : Subgroup (MulAut W)} {g k : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    s13Supp X (L.map (MulAut.conj (g * k)).toMonoidHom) =
      (fun U : Subgroup W => U.map g.toMonoidHom) ''
        s13Supp X (L.map (MulAut.conj k).toMonoidHom) := by
  have h1 : L.map (MulAut.conj (g * k)).toMonoidHom =
      (L.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map,
      show MulAut.conj (g * k) = MulAut.conj g * MulAut.conj k from map_mul _ _ _]
    rfl
  rw [h1, w16g_s13Supp_conj hg hg']

theorem w16g_sSupIndep_conjSubs_of_s13Supp (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A X L : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hLX : L ≤ X)
    (hdisj : ∀ g ∈ A, s13Supp X (L.map (MulAut.conj g).toMonoidHom) = s13Supp X L ∨
      Disjoint (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) (s13Supp X L)) :
    sSupIndep (conjSubs A (commSub ⊤ L)) := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective (fun S : Subgroup W => (S : Set W))
    SetLike.coe_injective
  have hXodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 hX
  have hnorm : ∀ g ∈ A, ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
    intro g hg x hx
    simpa using hXA g⁻¹ (A.inv_mem hg) x hx
  have hLsub : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom ≤ X := by
    intro g hg
    rintro l ⟨l', hl', rfl⟩
    simpa [MulAut.conj_apply] using hXA g hg l' (hLX hl')
  have hmap : ∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom =
      sSup (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) := by
    intro g hg
    rw [← w16g_commSub_map_conj ⊤ L g,
      Subgroup.map_top_of_surjective g.toMonoidHom g.surjective,
      w16g_commSub_top_eq_iSup_s13Supp hW hp hp2 hX (hLsub g hg), ← sSup_eq_iSup]
  have hblocks : ∀ g ∈ A, ∀ h ∈ A,
      s13Supp X (L.map (MulAut.conj h).toMonoidHom) =
        s13Supp X (L.map (MulAut.conj g).toMonoidHom) ∨
      Disjoint (s13Supp X (L.map (MulAut.conj h).toMonoidHom))
        (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) := by
    intro g hg h hh
    have hkA : g⁻¹ * h ∈ A := A.mul_mem (A.inv_mem hg) hh
    have htrans : s13Supp X (L.map (MulAut.conj h).toMonoidHom) =
        (fun U : Subgroup W => U.map g.toMonoidHom) ''
          s13Supp X (L.map (MulAut.conj (g⁻¹ * h)).toMonoidHom) := by
      conv_lhs => rw [show h = g * (g⁻¹ * h) from by group]
      exact w16g_s13Supp_conj_mul (hXA g hg) (hnorm g hg)
    have htrans' : s13Supp X (L.map (MulAut.conj g).toMonoidHom) =
        (fun U : Subgroup W => U.map g.toMonoidHom) '' s13Supp X L :=
      w16g_s13Supp_conj (hXA g hg) (hnorm g hg)
    rcases hdisj (g⁻¹ * h) hkA with heq | hdj
    · left
      rw [htrans, heq, ← htrans']
    · right
      rw [htrans, htrans']
      exact Set.disjoint_image_of_injective (Subgroup.map_injective g.injective) hdj
  intro B hB
  obtain ⟨g, hgA, hBeq⟩ := hB
  let Sg : Set (Subgroup W) := s13Supp X (L.map (MulAut.conj g).toMonoidHom)
  have hBsup : B = sSup Sg := by
    rw [hBeq]
    exact hmap g hgA
  have hdisjSg : Disjoint (sSup Sg) (sSup (s13IsoComps X \ Sg)) :=
    w16g_disjoint_sSup_sdiff_comps hW hXodd (S := Sg) (fun U hU => hU.1)
  have hmain : Disjoint B (sSup (s13IsoComps X \ Sg)) :=
    hdisjSg.mono_left (le_of_eq hBsup)
  have hle : sSup (conjSubs A (commSub ⊤ L) \ {B}) ≤ sSup (s13IsoComps X \ Sg) := by
    refine sSup_le fun B' hB' => ?_
    obtain ⟨hB'mem, hB'notin⟩ := hB'
    obtain ⟨h, hhA, hB'eq⟩ := hB'mem
    have hB'sup : B' = sSup (s13Supp X (L.map (MulAut.conj h).toMonoidHom)) := by
      rw [hB'eq]
      exact hmap h hhA
    have hB'ne : B' ≠ B := by
      intro hEq
      exact hB'notin (by simpa using hEq)
    have hdisjh : Disjoint (s13Supp X (L.map (MulAut.conj h).toMonoidHom)) Sg := by
      rcases hblocks g hgA h hhA with heq | hdj
      · exfalso
        apply hB'ne
        rw [hB'sup, hBsup]
        exact congrArg sSup heq
      · exact hdj
    have hsub : s13Supp X (L.map (MulAut.conj h).toMonoidHom) ⊆ s13IsoComps X \ Sg := by
      intro U hU
      exact ⟨hU.1, fun hUSg => (Set.disjoint_left.mp hdisjh hU) hUSg⟩
    rw [hB'sup]
    exact sSup_le_sSup hsub
  exact hmain.mono_right hle

end CFSG.LocalAnalysis.WeakClosure81
