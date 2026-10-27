module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312KG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped Pointwise

namespace L3312

variable {G : Type} [Group G] [Finite G]

theorem normalizer_sup_le {Y N : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hN : IsPGroup 2 ↥N)
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) :
    Subgroup.normalizer ((Y ⊔ N : Subgroup G) : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : perfectCore (Y ⊔ N) = Y := by
    refine le_antisymm (perfectCore_le_of_sup_solvable le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hNY)) rfl (by have := hN.isNilpotent; infer_instance)) ?_
    calc Y = perfectCore Y := (perfectCore_eq_self_of_perfect hY).symm
      _ ≤ perfectCore (Y ⊔ N) := perfectCore_mono le_sup_left
  have h2 := normalizer_le_normalizer_perfectCore (Y ⊔ N)
  rwa [h1] at h2


theorem isSylowTwoOf_map_range {X Y : Type*} [Group X] [Group Y] [Finite X] (ψ : X →* Y)
    {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) : IsSylowTwoOf (P.map ψ) ψ.range := by
  refine ⟨Subgroup.map_le_range ψ P, hP.2.1.map ψ, fun h2 => hP.2.2 ?_⟩
  have h1 : (P.map ψ).subgroupOf ψ.range = P.map ψ.rangeRestrict := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, Subtype.ext rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  have h3 : (P.map ψ).relIndex ψ.range = (P.map ψ.rangeRestrict).index := by
    rw [Subgroup.relIndex, h1]
  have h4 := Subgroup.index_map_dvd P ψ.rangeRestrict_surjective
  rw [Subgroup.relIndex] at h3
  show 2 ∣ P.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact (h3 ▸ h2).trans h4

@[expose] def OddNorm (Q : Type) [Group Q] (B : Subgroup Q) : Prop :=
  ∀ A S : Subgroup (MulAut Q), (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A →
    S ≤ MulAction.stabilizer (MulAut Q) B →
    ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A, Odd (orderOf d) →
      d ∈ MulAction.stabilizer (MulAut Q) B

omit [Finite G] in
theorem modO2Image_normal {X K : Subgroup G} (hKH : K ≤ X)
    (hHK : X ≤ Subgroup.normalizer (K : Set G)) : (modO2Image X K).Normal := by
  unfold modO2Image
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK).map _
    (QuotientGroup.mk'_surjective _)

theorem conjNormal_mem_stabilizer_iff {Hb : Type} [Group Hb] {Kb Yb : Subgroup Hb} [Kb.Normal]
    (hYK : Yb ≤ Kb) (x : Hb) :
    (MulAut.conjNormal x : MulAut ↥Kb) ∈ MulAction.stabilizer (MulAut ↥Kb) (Yb.subgroupOf Kb) ↔
      x ∈ Subgroup.normalizer (Yb : Set Hb) := by
  rw [mem_stabilizer_subgroup_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
  have hY : (Yb.subgroupOf Kb).map Kb.subtype = Yb := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hYK]
  have hcomm : ((Yb.subgroupOf Kb).map (MulAut.conjNormal x : MulAut ↥Kb).toMonoidHom).map
      Kb.subtype = Yb.map (MulAut.conj x).toMonoidHom := by
    rw [← hY, Subgroup.map_map, Subgroup.map_map, hY]
    congr 1
  constructor
  · intro h
    have h2 := hcomm
    rw [h, hY] at h2
    exact h2.symm
  · intro h
    apply Subgroup.map_injective Kb.subtype_injective
    rw [hcomm]
    exact h.trans hY.symm


omit [Finite G] in
theorem mk_mem_normalizer_modO2Image {X Y : Subgroup G} {x : G} (hxX : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) :
    (QuotientGroup.mk ⟨x, hxX⟩ : ↥X ⧸ CFSG.pCore 2 ↥X) ∈
      Subgroup.normalizer (modO2Image X Y : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  have h1 : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.normalizer (Y.subgroupOf X : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hxN) y
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) ⟨_, h1, rfl⟩

namespace Hyp3312

variable {T M L D Y : Subgroup G} (H : Hyp3312 G T M L D Y)

include H

theorem perfect_Y : ⁅Y, Y⁆ = Y := (cComp_of_isLocal H.isLocal).2.1

theorem isSylowTwoOf_modO2Image_T : IsSylowTwoOf (modO2Image (Y ⊔ T ⊔ D) T) ⊤ := by
  have hS := H.isSylowTwoOf_H
  have hT : IsSylowTwoOf (T.subgroupOf (Y ⊔ T ⊔ D)) ⊤ := by
    refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, fun h2 => hS.2.2 ?_⟩
    have h3 : ((T.subgroupOf (Y ⊔ T ⊔ D)).subgroupOf ⊤).index = T.relIndex (Y ⊔ T ⊔ D) :=
      Subgroup.relIndex_top_right _
    rw [h3] at h2
    exact h2
  have h := isSylowTwoOf_map_range (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y ⊔ T ⊔ D))) hT
  rwa [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h

theorem mem_normalizer_of_mk (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {h : G} (hh : h ∈ Y ⊔ T ⊔ D)
    (hN : (QuotientGroup.mk ⟨h, hh⟩ : ↥(Y ⊔ T ⊔ D) ⧸ CFSG.pCore 2 ↥(Y ⊔ T ⊔ D)) ∈
      Subgroup.normalizer (modO2Image (Y ⊔ T ⊔ D) Y : Set (↥(Y ⊔ T ⊔ D) ⧸
        CFSG.pCore 2 ↥(Y ⊔ T ⊔ D)))) :
    h ∈ Subgroup.normalizer (Y : Set G) := by
  set X := Y ⊔ T ⊔ D with hX
  have hYX : Y ≤ X := le_sup_left.trans le_sup_left
  have h1 : (⟨h, hh⟩ : ↥X) ∈ Subgroup.normalizer
      ((Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X : Subgroup ↥X) : Set ↥X) := by
    have hc : (modO2Image X Y).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) =
        Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
      unfold modO2Image
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have hmem : (⟨h, hh⟩ : ↥X) ∈ (Subgroup.normalizer (modO2Image X Y : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := hN
    rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _), hc] at hmem
    exact hmem
  have h2 : h ∈ Subgroup.normalizer
      (((Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X).map X.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map X.subtype ⟨_, h1, rfl⟩
  have h3 : (Y.subgroupOf X ⊔ CFSG.pCore 2 ↥X).map X.subtype = Y ⊔ pCoreOf 2 X := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYX, pCoreOf]
  rw [h3] at h2
  exact normalizer_sup_le H.perfect_Y (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_H).trans
      (H.le_normalizer_Y h14 h37 h128)) h2

theorem le_normalizer_D_of_oddNorm (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {K : Subgroup G} (hKH : K ≤ Y ⊔ T ⊔ D) (hYK : Y ≤ K)
    (hHK : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G))
    (hON : OddNorm ↥(modO2Image (Y ⊔ T ⊔ D) K)
      ((modO2Image (Y ⊔ T ⊔ D) Y).subgroupOf (modO2Image (Y ⊔ T ⊔ D) K))) :
    D ≤ Subgroup.normalizer (Y : Set G) := by
  set X := Y ⊔ T ⊔ D with hX
  have : (modO2Image X K).Normal := modO2Image_normal hKH hHK
  let ψ : (↥X ⧸ CFSG.pCore 2 ↥X) →* MulAut ↥(modO2Image X K) := MulAut.conjNormal
  have hInn : (MulAut.conj : ↥(modO2Image X K) →* MulAut ↥(modO2Image X K)).range ≤ ψ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, MulAut.conjNormal_val⟩
  have hS := isSylowTwoOf_map_range ψ H.isSylowTwoOf_modO2Image_T
  have hYK' : modO2Image X Y ≤ modO2Image X K :=
    Subgroup.map_mono fun y hy => hYK hy
  have hSB : (modO2Image X T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image X K))
      ((modO2Image X Y).subgroupOf (modO2Image X K)) := by
    rintro _ ⟨tb, htb, rfl⟩
    obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
    refine (conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
    exact mk_mem_normalizer_modO2Image htX (H.le_normalizer_Y h14 h37 h128 ht)
  intro d hd
  have hdX : d ∈ X := Subgroup.mem_sup_right hd
  apply H.mem_normalizer_of_mk h14 h37 h128 hdX
  refine (conjNormal_mem_stabilizer_iff hYK' _).mp ?_
  refine hON ψ.range _ hInn hS hSB _ ⟨?_, ⟨_, rfl⟩⟩ ?_
  · exact Subgroup.le_normalizer_map ψ ⟨_, mk_mem_normalizer_modO2Image hdX (H.DN hd), rfl⟩
  · refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ψ _)
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _)
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat H.Dodd h1

end Hyp3312

end L3312

end CFSG.Quasithin.H13
