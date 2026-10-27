module

public import CFSG.Quasithin.EmptyFaithful.SBc13JRaOdd
public import CFSG.Quasithin.EmptyFaithful.SBc13ACComp
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin

namespace SBc13

section Transport

variable {G : Type} [Group G]

theorem mem_cComp_conjSub_of_mem {X J : Subgroup G} (hJ : J ∈ cComp X) {y : G} (hy : y ∈ X) :
    conjSub y J ∈ cComp X := by
  have h1 := cComp_map_mulEquiv (MulAut.conj y) hJ
  have h2 : X.map (MulAut.conj y).toMonoidHom = X :=
    conjSub_eq_self_of_mem_normalizer (Subgroup.le_normalizer hy)
  rw [h2] at h1
  exact h1

theorem map_conjSub_hom {A B : Type*} [Group A] [Group B] (φ : A →* B) (a : A) (H : Subgroup A) :
    (conjSub a H).map φ = conjSub (φ a) (H.map φ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem modO2Image_conjSub {X J : Subgroup G} {y : G} (hy : y ∈ X) :
    modO2Image X (conjSub y J) =
      conjSub (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hy⟩) (modO2Image X J) := by
  have h1 : (conjSub y J).subgroupOf X = conjSub (⟨y, hy⟩ : ↥X) (J.subgroupOf X) := by
    ext x
    simp [Subgroup.mem_subgroupOf, mem_conjSub]
  unfold modO2Image
  rw [h1]
  exact map_conjSub_hom _ _ _

end Transport

section Quotient

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_normalizer_of_odd_of_A38Part3 (h : A38Part3 Q) {J : Subgroup Q}
    (hJ : J ∈ cComp (⊤ : Subgroup Q)) {y : Q} (hy : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (J : Set Q) := by
  rcases (h J hJ).1 with hn | ⟨-, t, htn, -, -, hcl⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.mem_top y
  · refine mem_normalizer_of_odd_of_two_conjugates htn (fun z => ?_) hy
    have htC : conjSub t J ∈ cComp (⊤ : Subgroup Q) :=
      mem_cComp_conjSub_of_mem hJ (Subgroup.mem_top t)
    have hzC : conjSub z J ∈ cComp (⊤ : Subgroup Q) :=
      mem_cComp_conjSub_of_mem hJ (Subgroup.mem_top z)
    have hz : conjSub z J ≤ conjClosure J ⊤ := by
      intro x hx
      simpa [mul_assoc] using mem_conjClosure (Subgroup.mem_top z) (mem_conjSub.mp hx)
    have hle : conjSub z J ≤ J ⊔ conjSub t J := hz.trans hcl.le
    rcases eq_or_eq_of_mem_cComp_of_le_sup hJ htC hzC hle with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

end Quotient

section Main

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_odd_of_sqtk (h38 : A38ForSQTK) {X J : Subgroup G} (hX : SQTKGroup ↥X)
    (hJ : J ∈ cComp X) {y : G} (hy : y ∈ X) (hodd : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (J : Set G) := by
  have hA := h38 (↥X ⧸ CFSG.pCore 2 ↥X) (SQTKHyp.of_sqtkGroup ↥X hX)
  have hyodd : Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨y, hy⟩ : ↥X))) := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (⟨y, hy⟩ : ↥X)
    rw [Subgroup.orderOf_mk] at hdvd
    exact hodd.of_dvd_nat hdvd
  have hfix := conjSub_eq_self_of_mem_normalizer
    (mem_normalizer_of_odd_of_A38Part3 hA (modO2Image_mem_cComp hJ) hyodd)
  have heq : conjSub y J = J :=
    modO2Image_injOn X (mem_cComp_conjSub_of_mem hJ hy) hJ ((modO2Image_conjSub hy).trans hfix)
  exact mem_normalizer_of_conjSub_eq_self heq

theorem le_normalizer_of_odd_gen (h38 : A38ForSQTK) {X J K : Subgroup G} (hX : SQTKGroup ↥X)
    (hJ : J ∈ cComp X) (hKX : K ≤ X) (hKodd : K ≤ oTwoUpper K) :
    K ≤ Subgroup.normalizer (J : Set G) := by
  refine hKodd.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨hyK, hyodd⟩
  exact mem_normalizer_of_odd_of_sqtk h38 hX hJ (hKX hyK) hyodd

end Main

end SBc13

end CFSG.Quasithin
