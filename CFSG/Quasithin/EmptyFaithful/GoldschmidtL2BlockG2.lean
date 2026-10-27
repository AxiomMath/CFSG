module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Open

namespace L2Block

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)} {n : ℕ}

namespace Ctx

variable (C : Ctx G L n)

include C

theorem case4_false {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) (h : B42Case4 G L A) :
    False := by
  obtain ⟨⟨m, hm, -, -⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := TypeList.exists_equiv_of_g2Natural hm
  have hchar : CharP K 2 := charP_two_of_card hcard
  have hLJ := C.le_ffJ hA
  set J := ffJ G with hJ
  let c : ↥(cayleyGroup K) ≃* ↥(quasithinG2 K) :=
    MulEquiv.subgroupCongr (Alt57Model.quasithinG2_eq_cayleyGroup (K := K)).symm
  let ψ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥J :=
    (e.toMonoidHom.comp c.toMonoidHom).comp g2A
  have hψ : Function.Injective ψ :=
    e.injective.comp (c.injective.comp Alt57Model.g2A_injective)
  let N : Subgroup ↥J := L.subgroupOf J
  have hNn : N.Normal := C.hnorm
  have hsq : ∀ q : ↥J ⧸ N, q * q = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have := C.hsq (y : MulAut S) (Alt57.ffJ_le G y.2)
    simpa [sq] using this
  have hcomm : ∀ a b : ↥J ⧸ N, a * b = b * a := by
    intro a b
    have h1 : (a * b) * (a * b) = 1 := hsq _
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b * a := by rw [mul_inv_rev, ha, hb]
  let φ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥J ⧸ N := (QuotientGroup.mk' N).comp ψ
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K)
    (n := 3) le_rfl
  have hker : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K, φ s = 1 := by
    have hle : commutator (Matrix.SpecialLinearGroup (Fin 3) K) ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    intro s
    rw [hperf.commutator_eq_top] at hle
    exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top s))
  have hmem : ((ψ (GoldL2.unitri3 K) : ↥J) : MulAut S) ∈ L := by
    have := (QuotientGroup.eq_one_iff (ψ (GoldL2.unitri3 K))).1 (hker (GoldL2.unitri3 K))
    exact Subgroup.mem_subgroupOf.1 this
  let l : ↥L := ⟨_, hmem⟩
  have h4 : l ^ 4 = 1 := by
    apply Subtype.ext
    have : (ψ (GoldL2.unitri3 K)) ^ 4 = 1 := by
      rw [← map_pow, GoldL2.unitri3_pow_four, map_one]
    have h' := congrArg (fun x : ↥J => (x : MulAut S)) this
    simpa [l] using h'
  have h2 := C.no4 l h4
  apply GoldL2.unitri3_sq_ne_one K
  apply hψ
  rw [map_pow, map_one]
  apply Subtype.ext
  have h' := congrArg (fun x : ↥L => (x : MulAut S)) h2
  simpa [l] using h'

end Ctx

end L2Block

end CFSG.QuasithinUnique.Bridge
