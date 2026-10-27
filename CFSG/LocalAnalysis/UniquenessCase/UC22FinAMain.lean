module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinAIn
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22FinACore
import CFSG.LocalAnalysis.UniquenessCase.UC22FinAModel
import CFSG.LocalAnalysis.UniquenessCase.UC22FinAOppL
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_abelian_complement_of_le {W Y B : Subgroup G} (hYW : Y ≤ W) (hBW : B ≤ W)
    (h : ∃ A : Subgroup ↥W, B.subgroupOf W ≤ A ∧ IsMulCommutative A ∧
      A ⊓ Y.subgroupOf W ⊔ B.subgroupOf W = A ∧ A ⊓ Y.subgroupOf W ⊓ B.subgroupOf W = ⊥ ∧
      Nonempty (↥(A ⊓ Y.subgroupOf W) ≃* ↥(B.subgroupOf W))) :
    ∃ A : Subgroup G, B ≤ A ∧ A ≤ W ∧ IsMulCommutative A ∧ A ⊓ Y ⊔ B = A ∧
      A ⊓ Y ⊓ B = ⊥ ∧ Nonempty (↥(A ⊓ Y) ≃* ↥B) := by
  obtain ⟨A, hBA, hAab, hsup, hinf, ⟨e⟩⟩ := h
  have hmY : (Y.subgroupOf W).map W.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYW
  have hmB : (B.subgroupOf W).map W.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBW
  have hinj := W.subtype_injective
  have hmAY : (A ⊓ Y.subgroupOf W).map W.subtype = A.map W.subtype ⊓ Y := by
    rw [Subgroup.map_inf _ _ _ hinj, hmY]
  refine ⟨A.map W.subtype, ?_, Subgroup.map_subtype_le A, ?_, ?_, ?_, ?_⟩
  · rw [← hmB]
    exact Subgroup.map_mono hBA
  · let eA := A.equivMapOfInjective W.subtype hinj
    exact ⟨⟨fun x y => by
      obtain ⟨x', rfl⟩ := eA.surjective x
      obtain ⟨y', rfl⟩ := eA.surjective y
      rw [← map_mul, ← map_mul, hAab.is_comm.comm x' y']⟩⟩
  · rw [← hmAY, ← hmB, ← Subgroup.map_sup, hsup]
  · rw [← hmAY, ← hmB, ← Subgroup.map_inf _ _ _ hinj, hinf, Subgroup.map_bot]
  · exact ⟨(MulEquiv.subgroupCongr hmAY.symm).trans
      (((A ⊓ Y.subgroupOf W).equivMapOfInjective W.subtype hinj).symm.trans
        (e.trans (((B.subgroupOf W).equivMapOfInjective W.subtype hinj).trans
          (MulEquiv.subgroupCongr hmB))))⟩

theorem s22FinA_of_inputs (D : Data G) (Ch : Choice2011 G) (hB : ListBNonabelian)
    (h205 : S20_5 D) (hSg : UC6S846.SigmaStd D) : S22FinA D Ch := by
  intro h1930 c p hp H hH hZH _ hsp3 m hm hqR hLie hYcal hYiso
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨x, hxHM, hxo⟩ := exists_orderOf_eq_prime hpP (ne_bot_of_mem_calC hYcal)
  have hsp := sp_of_mem_calC hSg hp inf_le_left hYcal
  have hL0R := L0_le_opp D hB h1930 h205 c hpP hsp hH hZH hxHM.1 hxHM.2 hxo
  have hRL := opp_mem_calL D hpP hp2 hH hqR c.hL0.1 hL0R
  have hYle : Opp p (H ⊓ D.M) ≤ H ⊓ D.M := pElementSubgroup_le p _
  have hYR : Opp p (H ⊓ D.M) ≤ Opp p H := Subgroup.closure_mono fun y hy => ⟨hy.1.1, hy.2⟩
  have hYM : Opp p (H ⊓ D.M) ≤ D.M := hYle.trans inf_le_right
  have hZ : center (Bar2 (Opp p (H ⊓ D.M))) = ⊥ := center_eq_bot_of_mulEquiv_statedSL hYiso.some
  obtain ⟨K, hfield, hfinite, hchar, φ, hcard, hsurj, hker, hmem⟩ :=
    exists_model D hB h1930 hRL hm hLie hYR hYM hYcal.2.2 hZ
  let := hfield
  let := hfinite
  have := hchar
  have hq8 : 8 ≤ Nat.card K := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hWHM : D.M ⊓ Opp p H ≤ H ⊓ D.M := fun w hw => ⟨pElementSubgroup_le p H hw.2, hw.1⟩
  have hYW : Opp p (H ⊓ D.M) ≤ D.M ⊓ Opp p H := le_inf hYM hYR
  let φW : ↥(D.M ⊓ Opp p H) →* projectiveSL 3 K := φ.comp (Subgroup.inclusion inf_le_right)
  have hφW : φW.range = projStabilizer (flagSpace 3 K 1) := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact (hmem ⟨g, g.2.2⟩).2 g.2.1
    · intro hz
      obtain ⟨r, rfl⟩ := hsurj z
      exact ⟨⟨r, (hmem r).1 hz, r.2⟩, rfl⟩
  have : ((Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYW).2
      (hWHM.trans (le_normalizer_pElementSubgroup p (H ⊓ D.M)))
  have hN2 : IsPGroup 2 ↥(φW.ker ⊓ (Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H)) := by
    have h1 : IsPGroup 2 ↥((pCoreOf 2 (Opp p (H ⊓ D.M))).subgroupOf (D.M ⊓ Opp p H)) :=
      (uc22p20b_isPGroup_pCoreOf _).comap_subtype
    refine h1.to_le fun g hg => ?_
    exact mem_pCoreOf_of_central hYR hZ hg.2 ((hker ⟨g, g.2.2⟩).1 hg.1)
  have hperf : ⁅(Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H),
      (Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H)⁆ =
      (Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H) := by
    apply Subgroup.map_injective (D.M ⊓ Opp p H).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYW]
    exact hYcal.2.1
  have hns : ¬ Group.IsSolvable
      ↥(((Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H)).map φW) := by
    have h := not_isSolvable_image hYR hYcal.2.2 hZ φ (fun r hr => (hker r).1 hr)
    have heq : ((Opp p (H ⊓ D.M)).subgroupOf (D.M ⊓ Opp p H)).map φW =
        ((Opp p (H ⊓ D.M)).subgroupOf (Opp p H)).map φ := by
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, g.2.2⟩, hg, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, hYM hr, r.2⟩, hr, rfl⟩
    rwa [heq]
  obtain ⟨t, htL, htM, ht⟩ := exists_inverting c
  have htR : t ∈ Opp p H := hL0R htL
  have hBR : c.B0 ≤ Opp p H := c.hB0.1.trans hL0R
  have hBW : c.B0 ≤ D.M ⊓ Opp p H := le_inf c.hBM hBR
  have hBcard : Nat.card ↥(c.B0.subgroupOf (D.M ⊓ Opp p H)) = Nat.card c.B0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv
  have hBab : IsMulCommutative ↥(c.B0.subgroupOf (D.M ⊓ Opp p H)) := ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥c.B0 => (z : G)) (c.hB0.2.1.is_comm.comm
      ⟨((x : ↥(D.M ⊓ Opp p H)) : G), x.2⟩ ⟨((y : ↥(D.M ⊓ Opp p H)) : G), y.2⟩)⟩⟩
  have hBodd := uc22p2214_odd_card_B0 D c
  have hBker : ∀ b ∈ c.B0.subgroupOf (D.M ⊓ Opp p H), φW b = 1 → b = 1 := fun b hb hb1 =>
    Subtype.ext (eq_one_of_central_of_inverted hBR hBodd htR ht hb ((hker ⟨b, b.2.2⟩).1 hb1))
  have htφ : ∀ b ∈ c.B0.subgroupOf (D.M ⊓ Opp p H),
      φ ⟨t, htR⟩ * φW b * (φ ⟨t, htR⟩)⁻¹ = (φW b)⁻¹ := by
    intro b hb
    show φ ⟨t, htR⟩ * φ ⟨b, b.2.2⟩ * (φ ⟨t, htR⟩)⁻¹ = (φ ⟨b, b.2.2⟩)⁻¹
    have h : (⟨t, htR⟩ : ↥(Opp p H)) * ⟨b, b.2.2⟩ * (⟨t, htR⟩ : ↥(Opp p H))⁻¹ =
        (⟨b, b.2.2⟩ : ↥(Opp p H))⁻¹ := Subtype.ext (ht b hb)
    simpa only [map_mul, map_inv] using congrArg φ h
  obtain ⟨A, hBA, -, hAab, hsup, hinf, he⟩ :=
    fina_core hq8 φW hφW hN2 hperf hns hBab (hBcard ▸ hBodd)
      (hBcard ▸ not_dvd_card_of_inverted hsp3 c.hBM htM ht) hBker htφ
      (fun h => htM ((hmem ⟨t, htR⟩).1 h))
  exact exists_abelian_complement_of_le hYW hBW ⟨A, hBA, hAab, hsup, hinf, he⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
