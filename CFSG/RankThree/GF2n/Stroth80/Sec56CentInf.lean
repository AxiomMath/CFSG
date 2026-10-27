module

public import CFSG.RankThree.GF2n.Stroth80.DictModel
public import CFSG.CGT.Timmesfeld75.Sec78Linear

public section

namespace CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

namespace QuadModel

variable (M₀ : QuadModel QF V K γ)

variable {M₀}

private theorem exists_orth_ne_zero {e e' : M₀.E} (he0 : e ≠ 0)
    (hind : ∀ s : K, e' ≠ s • e) : ∃ f : M₀.E, M₀.B f e = 0 ∧ M₀.B f e' ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨f₀, hf₀⟩ : ∃ f : M₀.E, M₀.B f e ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 (M₀.nondeg e fun f => by rw [B_comm, h f, neg_zero])
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : M₀.E, M₀.B w₀ e = 1 :=
    ⟨(M₀.B f₀ e)⁻¹ • f₀, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]⟩
  have key := CFSG.CGT.Timmesfeld75.apply_eq_mul_of_ker_le (f := LinearMap.flip M₀.B e)
    (f' := LinearMap.flip M₀.B e') (fun w hw => hcon w hw) (w₀ := w₀) hw₀
  have hz : e' - M₀.B w₀ e' • e = 0 := by
    refine M₀.nondeg _ fun g => ?_
    have hg := key g
    simp only [LinearMap.flip_apply] at hg
    rw [B_comm, map_sub, map_smul, smul_eq_mul]
    linear_combination -hg
  exact hind _ (sub_eq_zero.mp hz)

theorem card_centralizer_inf [Finite G] (R : GammaReg QF V γ) {U U' : Subgroup G}
    (hU : U ≤ QF) (hU' : U' ≤ QF) {e e' : M₀.E} (he0 : e ≠ 0)
    (he : ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e)
    (he' : ∀ v : M₀.E, v ∈ M₀.img U' ↔ ∃ s : K, v = s • e') (hind : ∀ s : K, e' ≠ s • e) :
    Nat.card ↥(QF ⊓ Subgroup.centralizer (U : Set G)) =
      Nat.card ↥(QF ⊓ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (U' : Set G)) *
        Nat.card K := by
  obtain ⟨f, hf, hf'⟩ := exists_orth_ne_zero he0 hind
  let φ : ↥(QF ⊓ Subgroup.centralizer (U : Set G)) →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (M₀.B (M₀.π x) e')
      map_one' := by simp [pi_one M₀]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul x x.2.1 y y.2.1, map_add, LinearMap.add_apply]
        rfl }
  have hker : φ.ker = (QF ⊓ Subgroup.centralizer (U : Set G) ⊓
      Subgroup.centralizer (U' : Set G)).subgroupOf (QF ⊓ Subgroup.centralizer (U : Set G)) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show Multiplicative.ofAdd (M₀.B (M₀.π x) e') = 1 ↔ _
    rw [ofAdd_eq_one, ← centralizer_iff R hU' he' x.2.1]
    exact ⟨fun h => ⟨⟨x.2.1, x.2.2⟩, h⟩, fun h => h.2⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj ((Multiplicative.toAdd y / M₀.B f e') • f)
    refine ⟨⟨x, ⟨hxQ, (centralizer_iff R hU he hxQ).mpr ?_⟩⟩, ?_⟩
    · rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul, hf, mul_zero]
    · show Multiplicative.ofAdd (M₀.B (M₀.π x) e') = y
      rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hf']
      rfl
  have hrange : Nat.card φ.range = Nat.card K := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact Nat.card_congr (Subgroup.topEquiv.toEquiv.trans Multiplicative.toAdd)
  have hcard : Nat.card φ.ker = Nat.card ↥(QF ⊓ Subgroup.centralizer (U : Set G) ⊓
      Subgroup.centralizer (U' : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcard, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

end QuadModel

end CFSG.RankThree.GF2n.Tim79

end
