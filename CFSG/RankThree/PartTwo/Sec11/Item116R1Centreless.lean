module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1RankTwoPure
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusCfg
public import CFSG.RankThree.PartTwo.Sec11.DataExistsR
public import CFSG.RankThree.ThetaFree.OrbitProduct
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec11

theorem thetaFree_conjOrbit_bot {X : Type} [Group X] (J : Subgroup X) :
    CFSG.RankThree.ThetaFree.conjOrbit (⊥ : Subgroup X) J = {J} := by
  ext K
  constructor
  · rintro ⟨b, rfl⟩
    have hb : (b : X) = 1 := Subgroup.mem_bot.1 b.2
    have h1 : J.map (MulAut.conj (b : X)).toMonoidHom = J := by
      rw [hb]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [MulAut.conj_apply] using hy
      · intro hx
        exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [Set.mem_singleton_iff]
    exact h1
  · intro hK
    rw [Set.mem_singleton_iff] at hK
    rw [hK]
    exact CFSG.RankThree.ThetaFree.self_mem_conjOrbit _ _

theorem thetaFree_orbitProd_bot {X : Type} [Group X] (J : Subgroup X) :
    CFSG.RankThree.ThetaFree.orbitProd (⊥ : Subgroup X) J = J := by
  rw [CFSG.RankThree.ThetaFree.orbitProd, thetaFree_conjOrbit_bot J, sSup_singleton]

theorem isPGroup_center_component_of_theta {X : Type} [Group X] [Finite X]
    (hθ : aschbacherSolvableCore 3 X = ⊥) {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    IsPGroup 3 (Subgroup.center J) := by
  have h := CFSG.RankThree.ThetaFree.isPGroup_center_orbitProd (B := (⊥ : Subgroup X)) hθ hJ
  rw [thetaFree_orbitProd_bot J] at h
  exact h

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup
open CFSG.RankThree.GroupTheory

namespace CFSG.RankThree.PartTwo.Sec11

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem R_isRankTwoByCyclic (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) : IsRankTwoByCyclic ↥R := by
  have hs := h.toSec11Std hT
  obtain ⟨-, hcyc⟩ := h113 G A c L a R Y hs
  obtain ⟨x, hx⟩ := hs.exists_zpowers_eq_inf_L
  obtain ⟨s, hs'⟩ := RChoice.exists_zpowers_eq_of_isCyclic hcyc
  have hA : A = Subgroup.closure ({c, a, d} : Set G) := by
    rw [← h.closure_eq]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨r, hRgen, -⟩ := hs.exists_eq_closure h45 h.inf_eq_zpowers hA hx hs'
  have hsx : x * s = s * x := (hs.commute_s_x hx hs').symm
  have hRN : R ≤ Subgroup.normalizer (L : Set G) :=
    h.isSylowOf.le.trans (hs.normalizer_le_normalizer_L h45)
  have hxR : x ∈ R ⊓ L := hx ▸ Subgroup.mem_zpowers x
  have hsR : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := hs' ▸ Subgroup.mem_zpowers s
  have hrR : r ∈ R := hRgen ▸ Subgroup.subset_closure (by simp)
  have hnx : ∀ y ∈ R, ∃ e : ℤ, y * x * y⁻¹ = x ^ e := by
    intro y hy
    have hm : y * x * y⁻¹ ∈ R ⊓ L :=
      ⟨R.mul_mem (R.mul_mem hy hxR.1) (R.inv_mem hy),
        (Subgroup.mem_normalizer_iff.mp (hRN hy) x).mp hxR.2⟩
    rw [hx] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hns : ∀ y ∈ R, ∃ e : ℤ, y * s * y⁻¹ = s ^ e := by
    intro y hy
    have hm : y * s * y⁻¹ ∈ R ⊓ Sec4.thetaQuotCentralizer L :=
      ⟨R.mul_mem (R.mul_mem hy hsR.1) (R.inv_mem hy),
        Sec6.conj_mem_thetaQuotCentralizer hsR.2 (hRN hy)⟩
    rw [hs'] at hm
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact ⟨e, he.symm⟩
  have hgen : Subgroup.closure ({(⟨r, hrR⟩ : ↥R), ⟨x, hxR.1⟩, ⟨s, hsR.1⟩} : Set ↥R) = ⊤ := by
    refine Subgroup.map_injective R.subtype_injective ?_
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
    exact hRgen.symm
  have hxs : (⟨x, hxR.1⟩ : ↥R) * (⟨s, hsR.1⟩ : ↥R) = (⟨s, hsR.1⟩ : ↥R) * (⟨x, hxR.1⟩ : ↥R) :=
    Subtype.ext hsx
  have hnxR : ∀ y : ↥R, ∃ e : ℤ,
      y * (⟨x, hxR.1⟩ : ↥R) * y⁻¹ = (⟨x, hxR.1⟩ : ↥R) ^ e := by
    intro y
    obtain ⟨e, he⟩ := hnx (y : G) y.2
    exact ⟨e, Subtype.ext (by simpa using he)⟩
  have hnsR : ∀ y : ↥R, ∃ e : ℤ,
      y * (⟨s, hsR.1⟩ : ↥R) * y⁻¹ = (⟨s, hsR.1⟩ : ↥R) ^ e := by
    intro y
    obtain ⟨e, he⟩ := hns (y : G) y.2
    exact ⟨e, Subtype.ext (by simpa using he)⟩
  exact isRankTwoByCyclic_of_generators (⟨r, hrR⟩ : ↥R) (⟨x, hxR.1⟩ : ↥R) (⟨s, hsR.1⟩ : ↥R)
    hgen hxs hnxR hnsR

theorem cdSub_isRankTwoByCyclic (x : G) {S : Subgroup G}
    (hSx : S ≤ Subgroup.centralizer ({x} : Set G)) (hS : IsRankTwoByCyclic ↥S) :
    IsRankTwoByCyclic ↥(cdSub x S) := by
  have h1 : IsRankTwoByCyclic ↥(S.subgroupOf (Subgroup.centralizer ({x} : Set G))) :=
    IsRankTwoByCyclic.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSx).symm hS
  unfold cdSub
  exact IsRankTwoByCyclic.map h1 (cdπ x)

theorem cd_Rbar_shape (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) :
    ∃ Rs : Sylow 3 (QAt (c * d)), IsRankTwoByCyclic ↥(Rs : Subgroup (QAt (c * d))) ∧
      ∀ x ∈ (Rs : Subgroup (QAt (c * d))), ∀ y ∈ (Rs : Subgroup (QAt (c * d))),
        x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x := by
  obtain ⟨⟨Rs, hRs⟩, hΩ, -⟩ := cd_Rbar_data h113 h hT
  obtain ⟨-, -, hRc⟩ := cd_R_facts h113 h hT
  have hRx : R ≤ Subgroup.centralizer ({c * d} : Set G) := by
    intro r hr
    obtain ⟨hrc, hrd⟩ := hRc r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * (c * d) = r * c * d := (mul_assoc _ _ _).symm
      _ = c * r * d := by rw [hrc]
      _ = c * (r * d) := mul_assoc _ _ _
      _ = c * (d * r) := by rw [hrd]
      _ = c * d * r := (mul_assoc _ _ _).symm
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := h.d_mem
  have haA : a ∈ A := h.a_mem
  have hcdA : c * d ∈ A := mul_mem hcA hdA
  have hc : c ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcA (c * d) hcdA)
  have hd : d ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdA (c * d) hcdA)
  have ha : a ∈ Subgroup.centralizer ({c * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a haA (c * d) hcdA)
  refine ⟨Rs, ?_, ?_⟩
  · rw [hRs]
    exact cdSub_isRankTwoByCyclic (c * d) hRx (R_isRankTwoByCyclic h45 h113 h hT)
  · intro x hx y hy hx3 hy3
    rw [hRs] at hx hy
    exact (cd_Abar_data h hT hc hd ha).2.1 x (hΩ x hx hx3) y (hΩ y hy hy3)

end Certified

end CFSG.RankThree.PartTwo.Sec11

end
