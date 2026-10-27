module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylSlOnIso
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylCentOmega
public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

theorem eq_map_slOn_of_component {G : Type} [Group G] {m : ℕ} (hm : 3 ≤ m)
    {ψ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G} (hψ : Function.Injective ψ)
    {y : G} {P : Fin (m + 1 + 1)} {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ht : t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) P)) (ht1 : t ≠ 1)
    (hy : GGHalfActsAs ψ.range ψ y t) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({y} : Set G))) :
    J = (slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}).map ψ := by
  let w : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 := omegaBlock (m + 1 + 1) P
  let A : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := Subgroup.zpowers w
  let S : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :=
    slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}
  have hkP : P.castSucc ∉ ({i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} :
        Set (Fin (m + 1 + 1 + 1))) ∧
      P.succ ∉ ({i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} :
        Set (Fin (m + 1 + 1 + 1))) := by
    constructor <;> simp
  have hωS : ∀ s ∈ S, w * s = s * w := fun s hs => commute_omegaBlock_slOn (k := P) hkP hs
  have hA_comm_S : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a := by
    intro a ha s hs
    have hmem : w ∈ Subgroup.centralizer
        ({s} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hωS s hs)
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hmem ha)
  have hzpt : Subgroup.zpowers t = A := by
    change Subgroup.zpowers t = Subgroup.zpowers (omegaBlock (m + 1 + 1) P)
    exact TauCeti.zpowers_eq_zpowers_of_mem_zpowers (p := 3) Nat.prime_three
      (omegaBlock_pow_three (m + 1 + 1) P) ht1 ht
  have hw_mem_t : w ∈ Subgroup.zpowers t := by
    rw [hzpt]; exact Subgroup.mem_zpowers w
  have hHmap : ψ.range ⊓ Subgroup.centralizer ({y} : Set G) =
      (Subgroup.centralizer ({w} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))).map ψ := by
    refine le_antisymm ?_ ?_
    · rintro h ⟨hran, hcent⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hran
      have hgy : ψ g * y = y * ψ g := Subgroup.mem_centralizer_singleton_iff.mp hcent
      have h1 : y * ψ g * y⁻¹ = ψ g := by rw [← hgy]; group
      have h2 : ψ g = ψ (t * g * t⁻¹) := by
        rw [← h1, hy (ψ g) hran]
        simp only [map_mul, map_inv]
      have hgt : g * t = t * g := (mul_inv_eq_iff_eq_mul.mp (hψ h2).symm).symm
      have hgw : g * w = w * g := by
        have h1 : t ∈ Subgroup.centralizer
            ({g} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hgt.symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          ((Subgroup.zpowers_le.mpr h1) hw_mem_t)).symm
      exact Subgroup.mem_map.mpr ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgw, rfl⟩
    · intro h hh
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
      refine ⟨MonoidHom.mem_range.mpr ⟨g, rfl⟩, ?_⟩
      have hgw : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hgt : g * t = t * g := by
        have h1 : w ∈ Subgroup.centralizer
            ({g} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hgw.symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          ((Subgroup.zpowers_le.mpr h1) ht)).symm
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have htg : t * g * t⁻¹ = g := by rw [← hgt]; group
      have hy' : y * ψ g * y⁻¹ = ψ g := by
        rw [hy (ψ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)]
        rw [show ψ t * ψ g * (ψ t)⁻¹ = ψ (t * g * t⁻¹) by simp only [map_mul, map_inv]]
        rw [htg]
      exact (mul_inv_eq_iff_eq_mul.mp hy').symm
  have hCw : Subgroup.centralizer ({w} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) =
      A ⊔ S := by
    refine le_antisymm ?_ ?_
    · intro g hg
      have hgw : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      obtain ⟨a, ha, s, hs, rfl⟩ := mem_centralizer_omegaBlock m P g hgw
      exact Subgroup.mul_mem_sup (S := A) (T := S) ha hs
    · refine sup_le ?_ ?_
      · intro a ha
        exact Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl) ha
      · intro s hs
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hωS s hs).symm
  have hH_eq : ψ.range ⊓ Subgroup.centralizer ({y} : Set G) = A.map ψ ⊔ S.map ψ := by
    rw [hHmap, hCw, Subgroup.map_sup]
  have hA'cent : A.map ψ ≤ Subgroup.centralizer ((S.map ψ : Subgroup G) : Set G) := by
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← map_mul, ← map_mul, hA_comm_S a ha s hs]
  have hAw : A.map ψ = Subgroup.zpowers (ψ w) := by
    change (Subgroup.zpowers w).map ψ = Subgroup.zpowers (ψ w)
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton,
      ← Subgroup.zpowers_eq_closure]
  have hA'abel : ⁅A.map ψ, A.map ψ⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hAw]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hcomm : ⁅A.map ψ ⊔ S.map ψ, A.map ψ ⊔ S.map ψ⁆ ≤ S.map ψ := by
    refine (CFSG.Goldschmidt.Sec82.commutator_sup_le_of_le_centralizer
      (X := A.map ψ) (Y := S.map ψ) hA'cent).trans ?_
    refine sup_le ?_ (Subgroup.commutator_le_self (S.map ψ))
    rw [hA'abel]
    exact bot_le
  have hJJ : ⁅J, J⁆ = J := by
    have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap, hJ.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  have hJ_le_K : J ≤ S.map ψ := by
    have hperf : J ≤ ⁅J, J⁆ := le_of_eq hJJ.symm
    refine hperf.trans ?_
    calc ⁅J, J⁆ ≤ ⁅ψ.range ⊓ Subgroup.centralizer ({y} : Set G),
          ψ.range ⊓ Subgroup.centralizer ({y} : Set G)⁆ :=
          Subgroup.commutator_mono hJ.1 hJ.1
      _ = ⁅A.map ψ ⊔ S.map ψ, A.map ψ ⊔ S.map ψ⁆ := by rw [hH_eq]
      _ ≤ S.map ψ := hcomm
  have hK_le_H : S.map ψ ≤ ψ.range ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hH_eq]; exact le_sup_right
  have hJKsub : IsSubnormal J (S.map ψ) := by
    have h := (hJ.2.1).inf_of_le (L := S.map ψ) hK_le_H
    rwa [inf_eq_left.mpr hJ_le_K] at h
  have hSimpleSL : IsSimpleGroup (SpecialLinearGroup (Fin (m + 1)) F2) := by
    have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F2) :=
      (CFSG.LinearGroups.linear_projective_simple (K := F2) (n := m + 1) (by omega)
        (Or.inl (by omega))).2.1
    have eSL : SpecialLinearGroup (Fin (m + 1)) F2 ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F2 :=
      ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot (m + 1))).trans
        QuotientGroup.quotientBot).symm
    exact (MulEquiv.isSimpleGroup_congr eSL).mpr hPSL
  have e1 : ↥S ≃* ↥(S.map ψ) := Subgroup.equivMapOfInjective S ψ hψ
  obtain ⟨e2⟩ := exists_mulEquiv_slOn_compl m P
  have eK : ↥(S.map ψ) ≃* SpecialLinearGroup (Fin (m + 1)) F2 := e1.symm.trans e2
  have hSimpleK : IsSimpleGroup ↥(S.map ψ) := (MulEquiv.isSimpleGroup_congr eK).mpr hSimpleSL
  rcases IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJKsub hSimpleK with hbot | htop
  · exfalso
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
      rw [hbot]; infer_instance
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
    exact hab (Subsingleton.elim a b)
  · exact htop

end GGHalf

end CFSG.StandardType

end
