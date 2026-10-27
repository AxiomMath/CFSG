module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAction
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPerm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D} (F : A10Frame c)

theorem A_le_M : F.A ≤ D.M := F.A_le.trans (F.P_le_L.trans c.hyp81.1)

noncomputable def conjA : Equiv.Perm (Fin 10) :=
  Classical.choose F.exists_conj_map_A

noncomputable def phiA : ↥D.M →* Equiv.Perm (Fin 10) :=
  (MulAut.conj F.conjA).toMonoidHom.comp (c.a10Hom F.iso)

theorem map_A_phiA : (F.A.subgroupOf D.M).map F.phiA = A10Perm.atilde := by
  rw [A10Perm.atilde_eq_map_Ebar]
  exact Classical.choose_spec F.exists_conj_map_A

theorem ker_phiA : F.phiA.ker = (c.a10Hom F.iso).ker := by
  ext m
  simp only [MonoidHom.mem_ker, phiA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (MulAut.conj F.conjA).injective]

theorem coprime_card_ker_phiA : Nat.Coprime (Nat.card F.phiA.ker) 3 := by
  rw [ker_phiA]
  exact c.coprime_card_ker_a10Hom F.iso F.center (fun P hP => F.le_L_of_isSylowOf hP)

theorem alternatingGroup_le_range_phiA : alternatingGroup (Fin 10) ≤ F.phiA.range := by
  intro x hx
  have hx' : F.conjA⁻¹ * x * F.conjA ∈ alternatingGroup (Fin 10) := by
    simpa [mul_assoc] using
      (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem x hx F.conjA⁻¹
  obtain ⟨m, hm⟩ := c.alternatingGroup_le_range_a10Hom F.iso hx'
  refine ⟨m, ?_⟩
  simp only [phiA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hm]
  group

theorem deg_zpowers_eq {b : G} (hb : b ∈ c.L) :
    F.deg (Subgroup.zpowers b) = (F.phiA ⟨b, c.hyp81.1 hb⟩).support.card := by
  rw [deg_zpowers F hb]
  simp only [phiA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Equiv.Perm.card_support_conj]

theorem phiA_eq_one_iff {x : G} (hx : x ∈ c.L) :
    F.phiA ⟨x, c.hyp81.1 hx⟩ = 1 ↔ x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
  rw [← a10Hom_eq_one_iff F hx]
  simp only [phiA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (MulAut.conj F.conjA).injective]

theorem ne_one_of_deg_ne_zero {a : G} (haL : a ∈ c.L) (h : F.deg (Subgroup.zpowers a) ≠ 0) :
    a ≠ 1 := by
  rintro rfl
  apply h
  have h1 : (⟨1, c.hyp81.1 haL⟩ : ↥D.M) = 1 := rfl
  rw [deg_zpowers_eq F haL, h1, map_one, Equiv.Perm.support_one, Finset.card_empty]

theorem card_zpowers_of_mem_A {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.zpowers a) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (F.elemAbelian.2 a haA) ha1

theorem centralizer_le_M_of_deg_three (hF : A10Facts F) {a : G} (haA : a ∈ F.A)
    (ha3 : F.deg (Subgroup.zpowers a) = 3) : Subgroup.centralizer ({a} : Set G) ≤ D.M := by
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have ha1 : a ≠ 1 := F.ne_one_of_deg_ne_zero haL (by rw [ha3]; norm_num)
  refine le_trans ?_ (hF.normalizer_A1 (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA)
    (F.card_zpowers_of_mem_A haA ha1) ha3)
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
  exact Subgroup.centralizer_le_normalizer _

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
