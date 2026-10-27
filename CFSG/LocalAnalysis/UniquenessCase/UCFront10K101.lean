module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
import CFSG.LocalAnalysis.UniquenessCase.UCFront10Alt
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Alt
import CFSG.LocalAnalysis.WeakClosure81.FiveSixOdd
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Open Subgroup
open scoped Pointwise

theorem exists_conj_of_odd_orderOf_alt {X : Type*} [Group X] {m : ℕ} (hm : 5 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) (σ : MulAut X) (hσ : Odd (orderOf σ)) :
    ∃ x : X, σ = MulAut.conj x := by
  rcases eq_or_ne m 6 with rfl | h6
  · obtain ⟨l, hl⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_conj_eq_of_odd_orderOf_alt_six
      (α := MulAut.congr e σ) (by rwa [MulEquiv.orderOf_eq])
    refine ⟨e.symm l, MulEquiv.ext fun x => e.injective ?_⟩
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ (e x)) hl
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at h
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h
  · exact CFSG.GH74.GLS.Stage2.Bender.Thm2.L121.exists_conj_of_odd (by omega) e σ hσ

private theorem odd_orderOf_conjNormal {G : Type*} [Group G] {L B : Subgroup G} [L.Normal]
    (hBo : Odd (Nat.card ↥B)) {b : G} (hb : b ∈ B) :
    Odd (orderOf (MulAut.conjNormal (H := L) b)) :=
  Odd.of_dvd_nat (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hb))
    (orderOf_map_dvd _ b)

private theorem le_of_forall_conjNormal_eq_conj {G : Type*} [Group G] {L B : Subgroup G}
    [L.Normal] (hC : centralizer (L : Set G) ≤ L)
    (h : ∀ b ∈ B, ∃ l : ↥L, MulAut.conjNormal (H := L) b = MulAut.conj l) : B ≤ L := by
  intro b hb
  obtain ⟨l, hl⟩ := h b hb
  have hc : (l : G)⁻¹ * b ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hx'
    calc x * ((l : G)⁻¹ * b) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * b := by group
      _ = (l : G)⁻¹ * (b * x * b⁻¹) * b := by rw [hx']
      _ = (l : G)⁻¹ * b * x := by group
  have hb' : b = (l : G) * ((l : G)⁻¹ * b) := by group
  rw [hb']
  exact L.mul_mem l.2 (hC hc)

private theorem subgroupOf_mul_comm_inf {G : Type*} [Group G] {L B T : Subgroup G} (hBL : B ≤ L)
    (hBT : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) * ((T ⊓ L).subgroupOf L : Subgroup ↥L) =
      ((T ⊓ L).subgroupOf L : Subgroup ↥L) * (B.subgroupOf L : Subgroup ↥L) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨b, hbL⟩, hb, ⟨t, htL⟩, ht, hbt⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb ht
    have hbt' : b * t = x := congrArg Subtype.val hbt
    have hmem : b * t ∈ (B : Set G) * (T : Set G) := ⟨b, hb, t, ht.1, rfl⟩
    rw [hBT] at hmem
    obtain ⟨t', ht', b', hb', htb⟩ := hmem
    have htb' : t' * b' = b * t := htb
    have ht'L : t' ∈ L := by
      have : t' = b * t * b'⁻¹ := by rw [← htb']; group
      rw [this]
      exact L.mul_mem (L.mul_mem hbL htL) (L.inv_mem (hBL hb'))
    refine ⟨⟨t', ht'L⟩, ⟨ht', ht'L⟩, ⟨b', hBL hb'⟩, hb', Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul]
    rw [htb', hbt']
  · rintro ⟨⟨t, htL⟩, ht, ⟨b, hbL⟩, hb, htb⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb ht
    have htb' : t * b = x := congrArg Subtype.val htb
    have hmem : t * b ∈ (T : Set G) * (B : Set G) := ⟨t, ht.1, b, hb, rfl⟩
    rw [← hBT] at hmem
    obtain ⟨b', hb', t', ht', hbt⟩ := hmem
    have hbt' : b' * t' = t * b := hbt
    have ht'L : t' ∈ L := by
      have : t' = b'⁻¹ * (t * b) := by rw [← hbt']; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hBL hb')) (L.mul_mem htL hbL)
    refine ⟨⟨b', hBL hb'⟩, hb', ⟨t', ht'L⟩, ⟨ht', ht'L⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul]
    rw [hbt', htb']

theorem k101_holds : K101 := by
  intro G _ _ T B hB ⟨n, ⟨e⟩⟩
  obtain ⟨hT, hBab, hBo, hBT, -⟩ := hB
  haveI hLn : (genFittingFStar G).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal G
  have hC : centralizer ((genFittingFStar G : Subgroup G) : Set G) ≤ genFittingFStar G :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le G
  rcases (show n ≤ 3 ∨ n = 4 ∨ 5 ≤ n by omega) with hn | rfl | hn
  ·
    haveI : IsCyclic ↥(genFittingFStar G) := by
      haveI := alternatingGroup.isCyclic_of_card_le_three (α := Fin n) (by simpa using hn)
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hL3 : Nat.card ↥(genFittingFStar G) ∣ 3 := by
      rw [Nat.card_congr e.toEquiv]
      interval_cases n
      · rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
        exact one_dvd 3
      · rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
        exact one_dvd 3
      · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
    have hAut : Nat.card (MulAut ↥(genFittingFStar G)) ∣ 2 := by
      rw [IsCyclic.card_mulAut]
      rcases (Nat.dvd_prime Nat.prime_three).1 hL3 with h | h <;> rw [h] <;> decide
    have hBL : B ≤ genFittingFStar G := by
      refine le_of_forall_conjNormal_eq_conj hC fun b hb => ⟨1, ?_⟩
      have hodd := odd_orderOf_conjNormal (L := genFittingFStar G) hBo hb
      have h1 : orderOf (MulAut.conjNormal (H := genFittingFStar G) b) = 1 := by
        have h2 := (orderOf_dvd_natCard (MulAut.conjNormal (H := genFittingFStar G) b)).trans hAut
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff.mp h1, map_one]
    have hB3 : Nat.card ↥B ∣ 3 := (Subgroup.card_dvd_of_le hBL).trans hL3
    rcases (Nat.dvd_prime Nat.prime_three).1 hB3 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  ·
    exfalso
    haveI : Group.IsSolvable (alternatingGroup (Fin 4)) :=
      alternatingGroup.isSolvable (by simp)
    haveI : Group.IsSolvable ↥(genFittingFStar G) := solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hEL : genFittingLayer G ≤ genFittingFStar G := le_sup_right
    haveI : Group.IsSolvable ↥(genFittingLayer G) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hEL)
    haveI : Group.IsPerfect ↥(genFittingLayer G) := CFSG.ComponentClassification.Layer.perfect G
    have hEbot : genFittingLayer G = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥(genFittingLayer G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable (G := ↥(genFittingLayer G)) inferInstance
    have hLF : genFittingFStar G = CFSG.fittingSubgroup G := by
      rw [genFittingFStar.eq_sup, hEbot, sup_bot_eq]
      rfl
    haveI : Group.IsNilpotent ↥(genFittingFStar G) := by
      rw [hLF]
      infer_instance
    haveI : Group.IsNilpotent (alternatingGroup (Fin 4)) := Group.nilpotent_of_mulEquiv e
    haveI : Nontrivial (alternatingGroup (Fin 4)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp)
    exact Group.IsNilpotent.center_ne_bot (G := alternatingGroup (Fin 4))
      (alternatingGroup.center_eq_bot (by simp))
  ·
    have hBL : B ≤ genFittingFStar G :=
      le_of_forall_conjNormal_eq_conj hC fun b hb =>
        exists_conj_of_odd_orderOf_alt hn e _ (odd_orderOf_conjNormal hBo hb)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ genFittingFStar G) (genFittingFStar G) :=
      hT.inf_of_le_normalizer le_top (normalizer_eq_top (H := genFittingFStar G)).ge
    have hS : CFSG.ABGLocalTools.IsSylowOf 2 ((T ⊓ genFittingFStar G).subgroupOf (genFittingFStar G))
        (⊤ : Subgroup ↥(genFittingFStar G)) := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff, subgroupOf_map_subtype, Subgroup.map_top,
        Subgroup.range_subtype, inf_assoc, inf_idem]
      exact hTL
    have hS' := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
    have eB : ↥(B.subgroupOf (genFittingFStar G)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL
    haveI := hBab
    have h3 := isPGroup_three_of_permutes_alt hn e hS' (Group.nilpotent_of_mulEquiv eB.symm)
      (by rwa [Nat.card_congr eB.toEquiv]) (subgroupOf_mul_comm_inf hBL hBT)
    exact h3.of_equiv eB

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
