module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFive
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndNineSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.GroupTheory.ConjTransport
import CFSG.RankThree.PartTwo.Sec10.Item104

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem centralizer_A_le_M_of (F : A10Frame c)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 →
      Subgroup.normalizer (B : Set G) ≤ D.M) :
    Subgroup.centralizer (F.A : Set G) ≤ D.M := by
  obtain ⟨a, haA, ha3, -⟩ := F.exists_deg_three_not_mem_z2Of F.sylow F.A_le
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hcard : Nat.card (Subgroup.zpowers a) = 3 :=
    F.card_zpowers_of_mem_A haA
      (F.ne_one_of_deg_ne_zero haL (by rw [ha3]; norm_num))
  have hCa : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)).trans
    (hCa.trans (hN1 (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA) hcard ha3))

private theorem le_M_of_sylow_five (F : A10Frame c) {H Q : Subgroup G}
    (hQ5 : 5 ∣ Nat.card Q) (hQM : Q ≤ D.M)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) : H ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 ↥Q := Classical.choice Sylow.nonempty
  have hSne : (S : Subgroup ↥Q) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S hQ5
  let T : Subgroup G := (S : Subgroup ↥Q).map Q.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 5 T Q := ⟨S, rfl⟩
  have hTne : T ≠ ⊥ := fun h =>
    hSne ((Subgroup.map_eq_bot_iff_of_injective (H := (S : Subgroup ↥Q))
      Q.subtype_injective).mp h)
  have hTM : T ≤ D.M := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hQM y.2
  have hNT : Subgroup.normalizer (T : Set G) ≤ D.M :=
    F.normalizer_le_of_isPGroup_five hTsyl.isPGroup hTne hTM
  intro n hn
  have hQmap : Q.map (MulAut.conj n).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hn)
  have hTnsyl : CFSG.ABGLocalTools.IsSylowOf 5
      (T.map (MulAut.conj n).toMonoidHom) Q := by
    have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hTsyl n
    rw [hQmap] at h
    exact h
  obtain ⟨k, hkQ, hkT⟩ := hTsyl.exists_mem_conj hTnsyl
  have hEq : T.map (MulAut.conj n).toMonoidHom =
      T.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hkT x, CFSG.RankThree.PartTwo.Sec10.mem_map_conj_iff]
  have hmemN : k⁻¹ * n ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc T.map (MulAut.conj (k⁻¹ * n)).toMonoidHom
        = (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom :=
          (CFSG.GroupTheory.map_conj_map_conj k⁻¹ n T).symm
      _ = (T.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
            rw [hEq]
      _ = T.map (MulAut.conj (k⁻¹ * k)).toMonoidHom :=
            CFSG.GroupTheory.map_conj_map_conj k⁻¹ k T
      _ = T := by rw [inv_mul_cancel]; ext x; simp
  have hkM : k ∈ D.M := hQM hkQ
  rw [show n = k * (k⁻¹ * n) by group]
  exact D.M.mul_mem hkM (hNT hmemN)

theorem normalizer_A_le_of (F : A10Frame c)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M) :
    Subgroup.normalizer (F.A : Set G) ≤ D.M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (F.A : Set G)
  have hC_le_M : C ≤ D.M := centralizer_A_le_M_of F hN1
  have hC5 : 5 ∣ Nat.card C := by
    have h := five_dvd_card_centralizer_inf F
      (fun x hx h => (a10Hom_eq_one_iff F hx).mp h)
      (three_le_pRank_five F) (F.A_le.trans F.P_le_L) F.elemAbelian.isPGroup
    rwa [inf_eq_left.mpr hC_le_M] at h
  refine le_M_of_sylow_five F hC5 hC_le_M ?_
  intro n hn
  have hCmap : C.map (MulAut.conj n).toMonoidHom = C := by
    change (Subgroup.centralizer (F.A : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer (F.A : Set G)
    rw [← CFSG.GroupTheory.centralizer_map_conj n F.A]
    exact congrArg (fun H : Subgroup G => Subgroup.centralizer (H : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hCmap

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
