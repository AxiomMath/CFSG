module

public import CFSG.RankThree.GF2n.Smith81.Lin26Torus
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem eq_of_inf_ne_bot_conj {P P' : Subgroup G} (hZ : IsTI Z) (hP : ∃ a : G, P = conjSubgroup a Z)
    (hP' : ∃ b : G, P' = conjSubgroup b Z) (h : P ⊓ P' ≠ ⊥) : P = P' := by
  obtain ⟨a, rfl⟩ := hP
  obtain ⟨b, rfl⟩ := hP'
  have hT : IsTI (conjSubgroup a Z) := isTI_conjSubgroup hZ a
  have e : conjSubgroup b Z = conjSubgroup (b * a⁻¹) (conjSubgroup a Z) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  rw [e] at h ⊢
  exact (conjSubgroup_eq_of_isTI hT h).symm

theorem exists_conj_eq_mul (hc : Ctx M Q Z B) {z p : G} (hz : z ∈ Z) (hp : p ∈ B) (hp1 : p ≠ 1) :
    ∃ q ∈ Q, q * p * q⁻¹ = z * p := by
  obtain ⟨m, φ, ψ, -, -, hcompat, hup, -, hV⟩ := Smith81.Ctx.inducesSL2' hc
  have hZW : Z ≤ Z ⊔ B := le_sup_left
  have hBW : B ≤ Z ⊔ B := le_sup_right
  set wz : ↥(Z ⊔ B) := ⟨z, hZW hz⟩ with hwz
  set wp : ↥(Z ⊔ B) := ⟨p, hBW hp⟩ with hwp
  have hz1 : Multiplicative.toAdd (ψ wz) 1 = 0 := (hV wz).mp hz
  have hp1' : Multiplicative.toAdd (ψ wp) 1 ≠ 0 := by
    intro h0
    have hpZ : p ∈ Z := (hV wp).mpr h0
    have : p ∈ Z ⊓ B := ⟨hpZ, hp⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at this
    exact hp1 this
  set a := Multiplicative.toAdd (ψ wp) 1 with ha
  set t : GaloisField 2 m := Multiplicative.toAdd (ψ wz) 0 / a with ht
  have hmem : CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 m) t ∈
      CFSG.Timmesfeld.upperUnipotent (GaloisField 2 m) :=
    (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff _).2 ⟨t, rfl⟩
  rw [← hup] at hmem
  obtain ⟨u, hu, hφu⟩ := Subgroup.mem_map.mp hmem
  have huQ : (u : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu
  have huH : (u : G) ∈ Q ⊔ QB B := u.2
  have hconj : (u : G) * p * (u : G)⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.sup_QB_le_normalizer_ZB hc huH) p).mp (hBW hp)
  refine ⟨u, huQ, ?_⟩
  have hprod : z * p ∈ Z ⊔ B := Subgroup.mul_mem _ (hZW hz) (hBW hp)
  have h1 := hcompat u wp ⟨(u : G) * p * (u : G)⁻¹, hconj⟩ rfl
  have h2 : ψ (wz * wp) = ψ wz * ψ wp := map_mul ψ wz wp
  have h3 : (⟨z * p, hprod⟩ : ↥(Z ⊔ B)) = wz * wp := rfl
  have key : ψ ⟨(u : G) * p * (u : G)⁻¹, hconj⟩ = ψ ⟨z * p, hprod⟩ := by
    apply Multiplicative.toAdd.injective
    rw [h3, h2, toAdd_mul]
    funext i
    rw [h1, hφu]
    fin_cases i
    · simp [CFSG.Timmesfeld.RankOne.upperElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ht]
      rw [← ha, div_mul_cancel₀ _ hp1', add_comm]
    · simp [CFSG.Timmesfeld.RankOne.upperElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1]
  have := ψ.injective key
  exact congrArg Subtype.val this

theorem eq_one_of_mem_sup_of_not_le (hc : Ctx M Q Z B) {F : Subgroup G} (hcF : Ctx M Q Z F)
    (hF : ¬ F ≤ Z ⊔ B) {f : G} (hf : f ∈ F) (hfW : f ∈ Z ⊔ B) : f = 1 := by
  by_contra hf1
  obtain ⟨z, hz, b, hb, rfl⟩ := (Smith81.Ctx.mem_sup_iff hc).mp hfW
  by_cases hb1 : b = 1
  · subst hb1
    have : z * 1 ∈ Z ⊓ F := ⟨by simpa using hz, hf⟩
    rw [hcF.inf_eq_bot, Subgroup.mem_bot] at this
    exact hf1 this
  · obtain ⟨q, hq, hqe⟩ := exists_conj_eq_mul hc hz hb hb1
    have hfB : z * b ∈ conjSubgroup q B := by
      rw [mem_conjSubgroup, ← hqe]
      simpa [mul_assoc] using hb
    have hne : F ⊓ conjSubgroup q B ≠ ⊥ := by
      intro h0
      have : z * b ∈ F ⊓ conjSubgroup q B := ⟨hf, hfB⟩
      rw [h0, Subgroup.mem_bot] at this
      exact hf1 this
    obtain ⟨gF, hgF⟩ := hcF.conj
    obtain ⟨gB, hgB⟩ := hc.conj
    have hFq : F = conjSubgroup q B :=
      eq_of_inf_ne_bot_conj hc.hyp.ti ⟨gF, hgF⟩ ⟨q * gB, by rw [hgB, conjSubgroup_mul]⟩ hne
    apply hF
    rw [hFq]
    intro x hx
    obtain ⟨b', hb', rfl⟩ : ∃ b' ∈ B, x = q * b' * q⁻¹ := by
      refine ⟨q⁻¹ * x * q, mem_conjSubgroup.mp hx, ?_⟩
      group
    exact (Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.Q_le_normalizer_ZB hc hq) b').mp
      (Subgroup.mem_sup_right hb')

end HS9

end CFSG.RankThree.GF2n.Stroth80
