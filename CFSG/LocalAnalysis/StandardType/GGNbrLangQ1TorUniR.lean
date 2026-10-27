module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniScalar
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniMark

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


open CFSG.LieType.SemisimpleCentralizers

private theorem l02qu6_odd_of_dvd {m n : ℕ} (h : m ∣ n) (hn : Odd n) : Odd m := by
  obtain ⟨k, rfl⟩ := h
  exact (Nat.odd_mul.mp hn).1

private theorem l02qu6_odd_card_sub_one {m : ℕ} (hm : 1 ≤ m) :
    Odd ((2 ^ m) ^ 2 - 1) := by
  have hm0 : m ≠ 0 := by omega
  have h2m : Even (2 ^ m) := Even.pow_of_ne_zero even_two hm0
  have hsq : Even ((2 ^ m) ^ 2) := by rw [pow_two]; exact h2m.mul_right (2 ^ m)
  have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow 2 (2 ^ m) (pow_pos (by norm_num) m)
  exact Nat.Even.sub_odd h1 hsq odd_one

theorem q1RToral_uni : Q1RToralTransfer ToralUni UniOdd (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hU
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hdiv⟩ := hU
  dsimp only at ht
  subst ht
  dsimp only at hdiv
  dsimp only [LargeEvenInLambda2] at hlab
  have hm : 1 ≤ n := hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  have hln : l = 2 → 2 ≤ n := hlab.2.2
  have hd : 3 ≤ l + 1 := by omega
  have hdq : ((l + 1, 2 ^ n) : ℕ × ℕ) ≠ (3, 2) := by
    rintro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hln hl
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at hpow
    omega
  have hpq : p ∣ 2 ^ n + 1 := dvd_trans hdiv (Nat.gcd_dvd_right (l + 1) (2 ^ n + 1))
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  obtain ⟨τ, hτ, hτQ⟩ := exists_unitaryInvolution (m := n) hm hK
  intro A hAab hAI hTor u huA huord J hJ
  let H : Subgroup (GL (Fin (l + 1)) K) := LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)
  have hUF := unitaryFieldData_of_card (n := n) hm hK
  have hS : LargeEvenGUSet (Fin (l + 1)) K (2 ^ n) ⊆
      ↑(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K))) :=
    TableBUE.gu_subset_normalizer (n := n) (d := l + 1) hUF
  have htorus : IsMulCommutative ↥(A.comap (TableB.projConj H)) :=
    toralUni_commute_datum (d := l + 1) (m := n) (K := K) hK hTor
  obtain ⟨Mu, hMu, hu_eq⟩ := TableB.exists_eq_projConj (H := H) hS (hAI u huA)
  obtain ⟨cu, hcu⟩ := exists_heldGU_scalar_mul (d := l + 1) (m := n) hK hm τ hτ hτQ hMu
  let s : GL (Fin (l + 1)) K := Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) cu * Mu
  have hcu_scal : Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) cu ∈
      LargeEvenScalars (Fin (l + 1)) K := ⟨cu, rfl⟩
  have hsHN : Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) cu ∈
      Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)) :=
    TableB.scalar_mem_normalizer H hcu_scal
  have hsN : s ∈ Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)) :=
    Subgroup.mul_mem _ hsHN (hS hMu)
  have hs : s ∈ Held.heldGU (l + 1) K τ hτ := hcu
  have hs_proj : TableB.projConj H ⟨s, hsN⟩ = u := by
    have h1 : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) cu, hsHN⟩ :
          ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) * ⟨Mu, hS hMu⟩ := rfl
    rw [h1, map_mul, TableB.projConj_of_scalar H hcu_scal, one_mul]
    exact hu_eq.symm
  have hs_comap : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) ∈
      A.comap (TableB.projConj H) := by
    rw [Subgroup.mem_comap, hs_proj]
    exact huA
  have hspN : s ^ p ∈ Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)) :=
    Subgroup.pow_mem _ hsN p
  have hsp_proj : TableB.projConj H ⟨s ^ p, hspN⟩ = 1 := by
    have hpow : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) ^ p =
        ⟨s ^ p, hspN⟩ := rfl
    rw [← hpow, map_pow, hs_proj, ← huord, pow_orderOf_eq_one]
  have hsp_scal : s ^ p ∈ LargeEvenScalars (Fin (l + 1)) K :=
    TableBUE.mem_scalars_of_projConj_eq_one (n := n) (d := l + 1) (p := p)
      hUF hK hd hdq hp hpq hsp_proj
  obtain ⟨c, hc⟩ := hsp_scal
  have hcardodd : Odd (Nat.card K - 1) := by
    rw [hK]
    exact l02qu6_odd_card_sub_one hm
  have hordc : Odd (orderOf c) :=
    l02qu6_odd_of_dvd (by rw [← Nat.card_units K]; exact orderOf_dvd_natCard c) hcardodd
  have hord_sp : Odd (orderOf (s ^ p)) := by
    rw [← hc]
    exact l02qu6_odd_of_dvd
      (orderOf_map_dvd (Matrix.GeneralLinearGroup.scalar (Fin (l + 1))) c) hordc
  have hdvd_s : orderOf s ∣ p * orderOf (s ^ p) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc s ^ (p * orderOf (s ^ p)) = (s ^ p) ^ orderOf (s ^ p) := by rw [pow_mul]
      _ = 1 := pow_orderOf_eq_one (s ^ p)
  have hso : Odd (orderOf s) := l02qu6_odd_of_dvd hdvd_s (hpodd.mul hord_sp)
  have hJ' : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (TableB.projConj H ⟨s, hsN⟩)) := by
    rwa [hs_proj]
  obtain ⟨C, hC, hCSU, hJeq⟩ :=
    q1TorUni_component_lift (d := l + 1) (m := n) (K := K) τ hτ hτQ s hs hsN J hJ'
  have hmark :=
    q1TorUni_marking (d := l + 1) (m := n) (K := K) hK τ hτ hτQ s hs hso C hC hCSU J hJeq
  refine largeEvenMarking_mono (P' := fun labJ _ _ IJ _ θJ =>
      True ∧ (∀ a ∈ A, ∀ j ∈ J, a (j : LargeEvenProj H) ∈ J) ∧
        GGAutsInduceOn A J θJ IJ) ?_ hmark
  intro labJ R' instR' I F θJ hψ
  have key : ∀ a ∈ A, (∀ j ∈ J, a (j : LargeEvenProj H) ∈ J) ∧
      (∃ φ ∈ I,
        LargeEvenInduces θJ (fun j j' : ↥J =>
          a (j : LargeEvenProj H) = (j' : LargeEvenProj H)) φ) := by
    intro a ha
    obtain ⟨Ma, hMa, ha_eq⟩ := TableB.exists_eq_projConj (H := H) hS (hAI a ha)
    obtain ⟨ca, hca⟩ := exists_heldGU_scalar_mul (d := l + 1) (m := n) hK hm τ hτ hτQ hMa
    let ka : GL (Fin (l + 1)) K := Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) ca * Ma
    have hca_scal : Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) ca ∈
        LargeEvenScalars (Fin (l + 1)) K := ⟨ca, rfl⟩
    have hkaN : ka ∈ Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)) :=
      Subgroup.mul_mem _ (TableB.scalar_mem_normalizer H hca_scal) (hS hMa)
    have hka_held : ka ∈ Held.heldGU (l + 1) K τ hτ := hca
    have hka_proj : TableB.projConj H ⟨ka, hkaN⟩ = a := by
      have h1 : (⟨ka, hkaN⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) =
          (⟨Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) ca,
              TableB.scalar_mem_normalizer H hca_scal⟩ :
            ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) * ⟨Ma, hS hMa⟩ := rfl
      rw [h1, map_mul, TableB.projConj_of_scalar H hca_scal, one_mul]
      exact ha_eq.symm
    have hka_comap : (⟨ka, hkaN⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin (l + 1)) K)))) ∈
        A.comap (TableB.projConj H) := by
      rw [Subgroup.mem_comap, hka_proj]
      exact ha
    have hka_comm : ka * s = s * ka := by
      have hxy := (htorus.is_comm).comm
        (⟨⟨ka, hkaN⟩, hka_comap⟩ : ↥(A.comap (TableB.projConj H)))
        (⟨⟨s, hsN⟩, hs_comap⟩ : ↥(A.comap (TableB.projConj H)))
      simpa using congrArg (fun z : ↥(A.comap (TableB.projConj H)) =>
        (z : GL (Fin (l + 1)) K)) hxy
    obtain ⟨hnorm, hind⟩ := hψ ka hkaN hka_held hka_comm
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← hka_proj]
      exact hnorm j hj
    · rw [← hka_proj]
      exact hind
  refine ⟨trivial, ?_, ?_⟩
  · intro a ha j hj
    exact (key a ha).1 j hj
  · intro a ha
    exact (key a ha).2

end CFSG.StandardType
