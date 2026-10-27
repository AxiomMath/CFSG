module

public import CFSG.Quasithin.Background.F918C4
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section ModLevel

variable {W : Type} [CommGroup W]

@[expose] def ModDynkin (L : Subgroup (MulAut W)) (σ : MulAut W) : Prop :=
  (IsPSL 3 2 1 ↥L ∧ ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)) ∨
    (IsAlt 6 ↥L ∧ ∃ x ∈ L, x ^ 3 = 1 ∧ ∀ l ∈ L, l * x * l⁻¹ ≠ σ * x * σ⁻¹)

@[expose] def ModNaturalType (L : Subgroup (MulAut W)) (V : Subgroup W) : Prop :=
  (IsPSL 3 2 1 ↥L → BinaryNaturalSL L V (V ⊓ fixV L) 3 1) ∧
    (IsAlt 6 ↥L → AlternatingNatural L V (V ⊓ fixV L) 6)

theorem not_stable_of_modDynkin {L : Subgroup (MulAut W)} {V : Subgroup W} {σ : MulAut W}
    (hnat : ModNaturalType L V) (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hD : ModDynkin L σ) : σ ∉ stabSub V := by
  intro hst
  have hV : V.map σ.toMonoidHom = V := map_eq_of_mem_stabSub hst
  have hZ : (V ⊓ fixV L).map σ.toMonoidHom = V ⊓ fixV L := A6Twist.map_inf_fixV_eq hσ hV
  rcases hD with ⟨hL, hout⟩ | ⟨hL, x, hxL, hx3, hx⟩
  · exact hout (A6Twist.inner_of_stable_nat3 (hnat.1 hL) hσ hV hZ)
  · obtain ⟨l, hl, hle⟩ := A6Twist.alt6_class_stable (hnat.2 hL) hσ hV hZ x hxL hx3
    exact hx l hl hle

theorem case1_module [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {σ : MulAut W}
    (hfour : M ≤ stabSub V ∨ ModFourRest Mp T L V) (hσT : σ ∈ T) (hσM : σ ∈ M)
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hnat : ModNaturalType L V)
    (hD : ModDynkin L σ) :
    σ ∉ stabSub V ∧ IsSumMod (fixV L) V (V.map σ.toMonoidHom) ⊤ := by
  have hns := not_stable_of_modDynkin hnat hσ hD
  refine ⟨hns, ?_⟩
  rcases hfour with hst | ⟨⟨hVT, -⟩ | h2⟩
  · exact absurd (hst hσM) hns
  · exact absurd (stab_of_orbSup_eq hVT.symm σ hσT) hns
  · exact (h2.2.2 σ hσT hns).1

theorem commV_eq_top_of_generated {L M : Subgroup (MulAut W)} {V : Subgroup W}
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤)
    (hM : ∀ m ∈ M, m ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hV : XMod.commOf ↥L V = V) : commV L = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [← hV] at hv
  induction hv using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨a, l, hl, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨m * (a : MulAut W) * m⁻¹, ?_, m l, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hM m hm) _).mp a.2
    · have h1 : m⁻¹ (m l) = l := by simp
      simp only [MulAut.mul_apply, map_mul, map_inv, h1]
      rfl
  | one => simp
  | mul c d hc hd ihc ihd =>
    rw [map_mul]
    exact mul_mem ihc ihd
  | inv c hc ih =>
    rw [map_inv]
    exact inv_mem ih

theorem eq_sup_of_sum {L : Subgroup (MulAut W)} {V V' : Subgroup W}
    (hsum : IsSumMod (fixV L) V V' ⊤) (hinv : ∀ x ∈ L, ∀ v ∈ V ⊔ V', x v ∈ V ⊔ V')
    (hperf : commV L = ⊤) : V ⊔ V' = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  have hw : w ∈ commV L := by rw [hperf]; trivial
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, v, rfl⟩ := hc
    have hv : v ∈ (V ⊔ V') ⊔ fixV L := by rw [← hsum.1]; trivial
    obtain ⟨a, ha, c₀, hc₀, rfl⟩ := Subgroup.mem_sup.1 hv
    have h1 : x (a * c₀) * (a * c₀)⁻¹ = x a * a⁻¹ := by
      rw [map_mul, mem_fixV.1 hc₀ x hx]
      group
    rw [h1]
    exact (V ⊔ V').mul_mem (hinv x hx a ha) ((V ⊔ V').inv_mem ha)
  | one => exact one_mem _
  | mul c d hc hd ihc ihd => exact mul_mem ihc ihd
  | inv c hc ih => exact inv_mem ih

theorem inv_map_of_normalizes {L : Subgroup (MulAut W)} {V : Subgroup W} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hV : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) :
    ∀ x ∈ L, ∀ v ∈ V.map σ.toMonoidHom, x v ∈ V.map σ.toMonoidHom := by
  rintro x hx _ ⟨v, hv, rfl⟩
  have hx' : σ⁻¹ * x * σ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hσ (σ⁻¹ * x * σ)).mpr (by simpa [mul_assoc] using hx)
  refine ⟨(σ⁻¹ * x * σ) v, hV _ hx' v hv, ?_⟩
  simp [MulAut.mul_apply]

theorem inv_sup {L : Subgroup (MulAut W)} {V V' : Subgroup W} (hV : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hV' : ∀ x ∈ L, ∀ v ∈ V', x v ∈ V') : ∀ x ∈ L, ∀ v ∈ V ⊔ V', x v ∈ V ⊔ V' := by
  intro x hx v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul]
  exact (V ⊔ V').mul_mem (Subgroup.mem_sup_left (hV x hx a ha)) (Subgroup.mem_sup_right (hV' x hx b hb))

end ModLevel

@[expose] def Insp14622Nat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → ModNaturalType L V


end CFSG.Quasithin
