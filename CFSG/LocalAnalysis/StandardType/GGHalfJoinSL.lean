module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLCard
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLCore
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank GGHalf Matrix

private lemma comap_centralizer_singleton {G S : Type} [Group G] [Group S] (φ : S →* G)
    (hφi : Function.Injective φ) (a : S) :
    (Subgroup.centralizer ({φ a} : Set G)).comap φ = Subgroup.centralizer ({a} : Set S) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : y = a := by simpa using hy
    rw [hy']
    have h1 := h (φ a) (Set.mem_singleton _)
    apply hφi
    rw [map_mul, map_mul]
    exact h1
  · intro h y hy
    have hy' : y = φ a := by simpa using hy
    rw [hy']
    have h1 := h a (Set.mem_singleton _)
    rw [← map_mul, ← map_mul, h1]

theorem GGHalfJoin.fusion_SL (m : ℕ) (hm : 3 ≤ m) : GGHalfFusionAt ⟨.A, m + 2, 1⟩ m := by
  intro G _ _ K' J T kx hq hZ hlabK hkx hkxK hJc hZJ hlabJ hTJ hT hTcard
  have hΛ : LargeEvenInLambda2 (⟨.A, m + 2, 1⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    omega
  have hmod : StatedClassicalModel (↥K' ⧸ Subgroup.center ↥K') .PSL (m + 1 + 1 + 1) 2 1 :=
    statedClassicalModel_of_hasLabel_typeA hΛ hlabK
  obtain ⟨φ, hφr, hφi⟩ := GGHalf.exists_slLift_two (m := m) (by omega) hq.1 hmod
  rw [← hφr, MonoidHom.range_eq_map] at hkxK
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hkxK
  have ha : orderOf a = 3 := (orderOf_injective φ hφi a).symm.trans hkx
  have hJK' : J ≤ K' := fun x hx => (hJc.1 hx).1
  have hJrange : J ≤ φ.range := by rw [hφr]; exact hJK'
  have hmapJ : (J.comap φ).map φ = J := Subgroup.map_comap_eq_self hJrange
  let e : ↥(J.comap φ) ≃* ↥J :=
    (Subgroup.equivMapOfInjective (J.comap φ) φ hφi).trans (MulEquiv.subgroupCongr hmapJ)
  have hq₀ : CFSG.Assembly.IsQuasisimple ↥(J.comap φ) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hJc.2.2
  have hKcomap : K'.comap φ = ⊤ := by
    rw [← hφr, MonoidHom.range_eq_map, Subgroup.comap_map_eq_self_of_injective hφi]
  have hcomap : (K' ⊓ Subgroup.centralizer ({φ a} : Set G)).comap φ =
      Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by
    rw [Subgroup.comap_inf, hKcomap, comap_centralizer_singleton φ hφi a]
    simp
  have hJ₀a : J.comap φ ≤
      Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) := by
    rw [← hcomap]
    exact Subgroup.comap_mono hJc.1
  have hsub' : CFSG.Assembly.IsSubnormal (J.comap φ)
      (Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))) := by
    rw [← hcomap]
    exact hJc.2.1.comap φ
  have hcomp : IsComponentOf (J.comap φ)
      (Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))) :=
    ⟨hJ₀a, hsub', hq₀⟩
  have hcardJ : Nat.card ↥J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) :=
    GGHalfJoin.card_eq_of_hasLabel_typeA (m := m) (by omega) hZJ hlabJ
  have hcard : Nat.card ↥(J.comap φ) = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) :=
    (Nat.card_congr e.toEquiv).trans hcardJ
  have hs : GGHalf.supp a = 2 :=
    GGHalfJoin.supp_eq_two_of_component (m := m) hm ha hcomp hcard
  have hTrange : T ≤ φ.range := by rw [hφr]; exact hTJ.trans hJK'
  have hTmap : (T.comap φ).map φ = T := Subgroup.map_comap_eq_self hTrange
  have hT₀ : IsElemAbelian 3 (T.comap φ) := CFSG.Open.IsElemAbelian.comap hT hφi
  have hcardT : Nat.card ↥(T.comap φ) = Nat.card ↥T := by
    have h1 : Nat.card ↥(T.comap φ) = Nat.card ↥((T.comap φ).map φ) :=
      (Subgroup.card_map_of_injective (f := φ) hφi).symm
    rw [hTmap] at h1
    exact h1
  have hT₀card : Nat.card ↥(T.comap φ) = 3 ^ ((m + 1) / 2) := hcardT.trans hTcard
  have hT₀J₀ : T.comap φ ≤ J.comap φ := Subgroup.comap_mono hTJ
  obtain ⟨n₀, hn₀norm, hn₀T, hn₀ne⟩ :=
    GGHalfJoin.fusion_core (m := m) (by omega) ha hs hq₀.1 hJ₀a hT₀J₀ hT₀ hT₀card
  refine ⟨φ n₀, ?_, ?_, ?_, ?_⟩
  · rw [← hφr, MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨n₀, Subgroup.mem_top n₀, rfl⟩
  · have hmap : ((Subgroup.zpowers a ⊔ T.comap φ :
        Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)).map φ) =
        Subgroup.zpowers (φ a) ⊔ T := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hTmap]
    have hmem : φ n₀ ∈ Subgroup.normalizer
        (((Subgroup.zpowers a ⊔ T.comap φ : Subgroup _).map φ) : Set G) :=
      Subgroup.le_normalizer_map φ (Subgroup.mem_map.mpr ⟨n₀, hn₀norm, rfl⟩)
    rwa [hmap] at hmem
  · have hmemT : φ (n₀ * a * n₀⁻¹) ∈ T := by
      rw [← hTmap]
      exact Subgroup.mem_map.mpr ⟨n₀ * a * n₀⁻¹, hn₀T, rfl⟩
    simpa only [map_mul, map_inv] using hmemT
  · intro h
    apply hn₀ne
    apply hφi
    simpa only [map_mul, map_inv, map_one] using h

end CFSG.StandardType

end
