module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec8.Hering611SInner
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section K1


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_mul_mem_zpowers_d (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hin : ∀ γ : MulAut (K ⧸ aschbacherSolvableCore 3 K), γ ^ 3 = 1 → KFacts.IsInnerAut γ)
    {x : G} (hx : x ∈ A) :
    ∃ k : K, (k : G) ∈ A ∧ x * (k : G)⁻¹ ∈ Subgroup.zpowers d ∧
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) =
        thetaQuotMulAut K (compAction K ⟨x, C.A_le_normalizer_K h45 hx⟩) := by
  have hAK := C.A_le_normalizer_K h45
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAK hx
  have hAe := C.toFrame611.isElemAbelian
  have hAmax := C.toFrame611.maximal
  set γ := Sec12.thetaBarAct K ⟨x, hxN⟩ with hγdef
  have hγ3 : γ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAe.2 x hx)
    rw [hγdef, ← map_pow, h1, map_one]
  obtain ⟨y, hy⟩ := hin γ hγ3
  have hmem : (MulAut.conj y : MulAut (K ⧸ aschbacherSolvableCore 3 K)) ∈ autThetaQuot A K := by
    rw [hy]
    exact mem_autThetaQuot_iff.mpr ⟨x, hxN, hx, rfl⟩
  obtain ⟨a, haA, hay⟩ := exists_mem_inf_of_conj_mem hAe hAmax hAK hZ hmem
  have hay' : QuotientGroup.mk' (aschbacherSolvableCore 3 K) a = y := hay
  have hact : Sec12.thetaBarAct K ⟨(a : G), Subgroup.le_normalizer a.2⟩ = γ := by
    rw [Sec12.thetaBarAct_of_mem a.2, hay', hy]
  refine ⟨a, haA, ?_, by rw [hay', hy]; rfl⟩
  have haN : (a : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.inv_mem _ (Subgroup.le_normalizer a.2)
  have hxaN : x * (a : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hxN haN
  have hcent : x * (a : G)⁻¹ ∈ A ⊓ thetaQuotCentralizer K := by
    refine ⟨A.mul_mem hx (A.inv_mem haA), ?_⟩
    show x * (a : G)⁻¹ ∈ thetaQuotCentralizer K
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hxaN]
    have : (⟨x * (a : G)⁻¹, hxaN⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨x, hxN⟩ * ⟨(a : G), Subgroup.le_normalizer a.2⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hact, ← hγdef, mul_inv_cancel]
  rw [← C.cent_K]
  exact hcent

end K1

end CFSG.RankThree.PartTwo.Sec8.Hering611
