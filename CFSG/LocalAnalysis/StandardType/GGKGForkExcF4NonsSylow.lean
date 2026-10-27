module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank

public section

namespace CFSG.StandardType

namespace ExcF4Nons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType

private theorem ggKGF4s_exists_conj_map_le_of_not_dvd_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : ¬ p ∣ H.index) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨S⟩ : Nonempty (Sylow p H) := inferInstance
  set S' := (S : Subgroup H).map H.subtype with hS'
  have hS'p : IsPGroup p S' := S.isPGroup'.map H.subtype
  have hS'idx : ¬ p ∣ S'.index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S.not_dvd_index hH
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hS'p.toSylow hS'idx)
  refine ⟨g, ?_⟩
  calc P.map (MulAut.conj g).toMonoidHom
      ≤ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hPQ
    _ = S' := by
        have h := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
        simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
        rw [← h, Subgroup.pointwise_smul_def]
        rfl
    _ ≤ H := Subgroup.map_subtype_le _

private theorem ggKGF4s_sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  calc q ^ 2 - 1 = q ^ 2 - 1 ^ 2 := by rw [one_pow]
    _ = (q + 1) * (q - 1) := Nat.sq_sub_sq q 1
    _ = (q - 1) * (q + 1) := by ring

private theorem ggKGF4s_not_dvd_six {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 6 := by
  intro h
  rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
  rcases hp.dvd_mul.mp h with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega

private theorem ggKGF4s_not_dvd_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 4 := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (by rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at h)
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  omega

private theorem ggKGF4s_not_dvd_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 3 := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  omega

private theorem ggKGF4s_val_pow_sub_one {p q e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : p ∣ q + 1) (he : ¬ p ∣ e) (he0 : e ≠ 0) :
    padicValNat p (q ^ (2 * e) - 1) = padicValNat p (q + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  have h1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hpq2 : p ∣ q ^ 2 - 1 := by
    have h : p ∣ (q + 1) * (q - 1) := dvd_mul_of_dvd_left hpq _
    rwa [ggKGF4s_sq_sub_one q, mul_comm]
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq h
    have : (q + 1) - q = 1 := by omega
    rw [this] at h1
    exact hp.not_dvd_one h1
  have hp_not_dvd_q2 : ¬ p ∣ q ^ 2 := fun h => hp_not_dvd_q (hp.dvd_of_dvd_pow h)
  have hval := padicValNat.pow_sub_pow (p := p) hpodd h1 hpq2 hp_not_dvd_q2 (n := e) he0
  have hq2e : q ^ (2 * e) = (q ^ 2) ^ e := by rw [pow_mul]
  rw [hq2e, show (q ^ 2) ^ e - 1 = (q ^ 2) ^ e - 1 ^ e by rw [one_pow], hval]
  have hq2minus : padicValNat p (q ^ 2 - 1) = padicValNat p (q + 1) := by
    rw [ggKGF4s_sq_sub_one q, padicValNat.mul (by omega) (by omega)]
    have hzero : padicValNat p (q - 1) = 0 := padicValNat.eq_zero_of_not_dvd (by
      intro h
      have hd : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h
      have h2 : (q + 1) - (q - 1) = 2 := by omega
      rw [h2] at hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
      omega)
    rw [hzero, zero_add]
  rw [hq2minus, padicValNat.eq_zero_of_not_dvd he, add_zero]

private theorem ggKGF4s_padicValNat_ordF4 {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 2 ≤ q) (hpq : p ∣ q + 1) :
    padicValNat p (CFSG.Open.ordF4 q) = 4 * padicValNat p (q + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h12 : padicValNat p (q ^ 12 - 1) = padicValNat p (q + 1) := by
    have h := ggKGF4s_val_pow_sub_one (e := 6) hp hp5 hq hpq
      (ggKGF4s_not_dvd_six hp hp5) (by norm_num)
    simpa using h
  have h8 : padicValNat p (q ^ 8 - 1) = padicValNat p (q + 1) := by
    have h := ggKGF4s_val_pow_sub_one (e := 4) hp hp5 hq hpq
      (ggKGF4s_not_dvd_four hp hp5) (by norm_num)
    simpa using h
  have h6 : padicValNat p (q ^ 6 - 1) = padicValNat p (q + 1) := by
    have h := ggKGF4s_val_pow_sub_one (e := 3) hp hp5 hq hpq
      (ggKGF4s_not_dvd_three hp hp5) (by norm_num)
    simpa using h
  have h2 : padicValNat p (q ^ 2 - 1) = padicValNat p (q + 1) := by
    have h := ggKGF4s_val_pow_sub_one (e := 1) hp hp5 hq hpq hp.not_dvd_one (by norm_num)
    simpa using h
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ (q + 1) - q := Nat.dvd_sub hpq hd
    have : (q + 1) - q = 1 := by omega
    rw [this] at h1
    exact hp.not_dvd_one h1
  have hq24 : padicValNat p (q ^ 24) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hp_not_dvd_q, mul_zero]
  have h12nz : q ^ 12 - 1 ≠ 0 := by
    have : 1 < q ^ 12 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h8nz : q ^ 8 - 1 ≠ 0 := by
    have : 1 < q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h6nz : q ^ 6 - 1 ≠ 0 := by
    have : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h2nz : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hq24nz : q ^ 24 ≠ 0 := pow_ne_zero 24 (by omega)
  rw [CFSG.Open.ordF4]
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hq24nz h12nz) h8nz) h6nz) h2nz]
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero hq24nz h12nz) h8nz) h6nz]
  rw [padicValNat.mul (mul_ne_zero hq24nz h12nz) h8nz]
  rw [padicValNat.mul hq24nz h12nz]
  rw [hq24, h12, h8, h6, h2]
  ring

private theorem ggKGF4s_padicValNat_ordF4_split {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 2 ≤ q) (hpq : p ∣ q - 1) :
    padicValNat p (CFSG.Open.ordF4 q) = 4 * padicValNat p (q - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ q := by omega
  have hnot := TableBF4.not_dvd_mul_geomSums hp hp5 hq1 hpq
  have hR : (q ^ 24 * ((∑ i ∈ Finset.range 12, q ^ i) *
      (∑ i ∈ Finset.range 8, q ^ i) * (∑ i ∈ Finset.range 6, q ^ i) *
      (∑ i ∈ Finset.range 2, q ^ i))) ≠ 0 := fun h => hnot (h ▸ dvd_zero p)
  rw [TableBF4.ordF4_eq_mul hq1]
  rw [padicValNat.mul (pow_ne_zero 4 (by omega : q - 1 ≠ 0)) hR]
  rw [padicValNat.eq_zero_of_not_dvd hnot, add_zero, padicValNat.pow]

theorem ggF4Nons_selfCentralizing_rank
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian p E)
    (hsc : ∀ g : adjointGroup .F4 K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    p ^ 4 ≤ Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  have hq2 : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hp_not_dvd_qm : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have h2 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h2] at h3
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3
    omega
  set a : ℕ := padicValNat p (Nat.card K + 1) with ha
  have hvalC : padicValNat p (Nat.card (adjointGroup .F4 K)) = 4 * a := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact ggKGF4s_padicValNat_ordF4 hp hp5 hq2 hpq
  have hEp : IsPGroup p E := TableB.isPGroup_of_isElemAbelian hE
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup (adjointGroup .F4 K)) = p ^ (4 * a) := by
    rw [P.card_eq_multiplicity, Nat.factorization_def (Nat.card (adjointGroup .F4 K)) hp, hvalC]
  haveI : Finite (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    CFSG.LieType.Chevalley.generated_group_finite .F4 _
  have hcardK₂ : Nat.card (FiniteField.Extension K 2 2) = Nat.card K ^ 2 := by
    rw [FiniteField.natCard_extension]
  have hK₂2 : 2 ≤ Nat.card (FiniteField.Extension K 2 2) := by
    rw [hcardK₂]
    nlinarith [hq2]
  have hpq₂ : p ∣ Nat.card (FiniteField.Extension K 2 2) - 1 := by
    rw [hcardK₂]
    have hfac : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) :=
      ggKGF4s_sq_sub_one (Nat.card K)
    rw [hfac]
    exact dvd_mul_of_dvd_right hpq _
  have hK₂val : padicValNat p (Nat.card (FiniteField.Extension K 2 2) - 1) = a := by
    rw [hcardK₂, ggKGF4s_sq_sub_one (Nat.card K),
      padicValNat.mul (by omega) (by omega),
      padicValNat.eq_zero_of_not_dvd hp_not_dvd_qm, zero_add, ha]
  have hvalC₂ : padicValNat p (Nat.card (adjointGroup .F4 (FiniteField.Extension K 2 2))) = 4
    * a := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      ggKGF4s_padicValNat_ordF4_split hp hp5 hK₂2 hpq₂, hK₂val]
  set φ : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2) :=
    TableBF4Two.adjointMap (algebraMap K (FiniteField.Extension K 2 2)) with hφdef
  have hφinj : Function.Injective φ := TableBF4Two.adjointMap_injective _
  set P' : Subgroup (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    (P : Subgroup (adjointGroup .F4 K)).map φ with hP'def
  have hP'card : Nat.card P' = p ^ (4 * a) := by
    rw [hP'def, Subgroup.card_map_of_injective hφinj, hPcard]
  have hP'p : IsPGroup p P' := by
    rw [hP'def]
    exact P.isPGroup'.map φ
  let P₂ : Sylow p (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    Sylow.ofCard P' (by
      rw [Nat.factorization_def (Nat.card (adjointGroup .F4 (FiniteField.Extension K 2 2))) hp,
        hvalC₂, hP'card])
  set H : Subgroup (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    (torusGroup .F4 (FiniteField.Extension K 2 2)).subgroupOf
      (adjointGroup .F4 (FiniteField.Extension K 2 2)) with hHdef
  have hidx : ¬ p ∣ H.index := by
    rw [hHdef]
    exact TableBF4.not_dvd_index_torusGroup hp hp5 hpq₂
  obtain ⟨g, hg⟩ :=
    ggKGF4s_exists_conj_map_le_of_not_dvd_index
      (G := adjointGroup .F4 (FiniteField.Extension K 2 2))
      hidx hP'p
  set ψ : adjointGroup .F4 K →* adjointGroup .F4 (FiniteField.Extension K 2 2) :=
    (MulAut.conj g).toMonoidHom.comp φ with hψdef
  have hψinj : Function.Injective ψ := (MulAut.conj g).injective.comp hφinj
  have hRleH : (P : Subgroup (adjointGroup .F4 K)).map ψ ≤ H := by
    rw [hψdef, ← Subgroup.map_map, ← hP'def]
    exact hg
  set R : Subgroup (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    (P : Subgroup (adjointGroup .F4 K)).map ψ with hRdef
  have hRleH' : R ≤ H := hRleH
  have hRcard : Nat.card R = p ^ (4 * a) := by
    rw [hRdef, Subgroup.card_map_of_injective hψinj, hPcard]
  have hcommH : ∀ x y : H, x * y = y * x := fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mul_comm_of_mem_diagonalGroup
      (CFSG.LieType.Chevalley.torusGroup_le_diagonalGroup (Subgroup.mem_subgroupOf.1 x.2))
      (CFSG.LieType.Chevalley.torusGroup_le_diagonalGroup (Subgroup.mem_subgroupOf.1 y.2))
  have hRcomm : ∀ x y : R, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hxy := hcommH ⟨x.1, hRleH' x.2⟩ ⟨y.1, hRleH' y.2⟩
    exact congrArg (fun z : H => (z : adjointGroup .F4 (FiniteField.Extension K 2 2))) hxy
  have hTH : (TableBF4.torusPow (FiniteField.Extension K 2 2) p) ≤ H := by
    intro x hx
    rw [hHdef, Subgroup.mem_subgroupOf]
    exact (TableBF4.mem_torusPow.1 hx).1
  have hHcard : Nat.card H = (Nat.card (FiniteField.Extension K 2 2) - 1) ^ 4 := by
    rw [hHdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4
          (k := FiniteField.Extension K 2 2))).toEquiv]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4
  have hHpadic : padicValNat p (Nat.card H) = 4 * a := by
    rw [hHcard, padicValNat.pow, hK₂val]
  set RH : Subgroup H := R.subgroupOf H with hRHdef
  have hRHcard_eq : Nat.card RH = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH').toEquiv
  have hRHcard : Nat.card RH = p ^ (Nat.card H).factorization p := by
    rw [Nat.factorization_def (Nat.card H) hp, hHpadic, hRHcard_eq, hRcard]
  let RHsyl : Sylow p H := Sylow.ofCard RH hRHcard
  have htp : IsPGroup p (TableBF4.torusPow (FiniteField.Extension K 2 2) p) := by
    rw [isPGroup_iff_card_dvd_pow]
    exact ⟨4, by rw [TableBF4.card_torusPow hp hpq₂]⟩
  haveI hNnormal : ((TableBF4.torusPow (FiniteField.Extension K 2 2) p).comap H.subtype).Normal :=
    Subgroup.Normal.mk (fun n hn g => by
      have h1 : g * n * g⁻¹ = n := by
        calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcommH g n]
          _ = n := by group
      rw [h1]
      exact hn)
  have hNle : (TableBF4.torusPow (FiniteField.Extension K 2 2) p).comap H.subtype ≤ RH :=
    htp.comap_subtype.le_sylow_of_normal RHsyl
  have hTleR : TableBF4.torusPow (FiniteField.Extension K 2 2) p ≤ R := by
    intro x hx
    have hxH : x ∈ H := hTH hx
    have hxRH : (⟨x, hxH⟩ : H) ∈ RH := hNle (Subgroup.mem_comap.2 hx)
    rw [hRHdef] at hxRH
    exact Subgroup.mem_subgroupOf.1 hxRH
  set A : Subgroup (adjointGroup .F4 K) :=
    (TableBF4.torusPow (FiniteField.Extension K 2 2) p).comap ψ with hAdef
  have hAmap : A.map ψ = TableBF4.torusPow (FiniteField.Extension K 2 2) p := by
    apply le_antisymm
    · rw [hAdef]
      exact Subgroup.map_comap_le _ _
    · intro t ht
      have htR : t ∈ R := hTleR ht
      rw [hRdef] at htR
      obtain ⟨q', hq'P, hq't⟩ := htR
      exact ⟨q', Subgroup.mem_comap.2 (hq't ▸ ht), hq't⟩
  have hAcard : Nat.card A = p ^ 4 := by
    rw [← Subgroup.card_map_of_injective hψinj, hAmap, TableBF4.card_torusPow hp hpq₂]
  have hA_le_P : A ≤ (P : Subgroup (adjointGroup .F4 K)) := by
    intro x hx
    have hxT : ψ x ∈ TableBF4.torusPow (FiniteField.Extension K 2 2) p := Subgroup.mem_comap.1 hx
    have hxR : ψ x ∈ R := hTleR hxT
    rw [hRdef] at hxR
    obtain ⟨q', hq'P, hq'x⟩ := hxR
    rw [← hψinj hq'x]
    exact hq'P
  have hApow : ∀ x ∈ A, x ^ p = 1 := by
    intro x hx
    have hxT : ψ x ∈ TableBF4.torusPow (FiniteField.Extension K 2 2) p := Subgroup.mem_comap.1 hx
    have hp1 : (ψ x) ^ p = 1 := (TableBF4.mem_torusPow.1 hxT).2
    apply hψinj
    rw [map_pow, hp1, map_one]
  have hPcomm : ∀ x y : (P : Subgroup (adjointGroup .F4 K)), x * y = y * x := by
    intro x y
    apply Subtype.ext
    apply hψinj
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg (fun z : R => (z : adjointGroup .F4 (FiniteField.Extension K 2 2)))
      (hRcomm ⟨ψ x, ⟨x, x.2, rfl⟩⟩ ⟨ψ y, ⟨y, y.2, rfl⟩⟩)
  have hAcomm : ∀ x ∈ A, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    exact congrArg (fun z : (P : Subgroup (adjointGroup .F4 K)) =>
      (z : adjointGroup .F4 K)) (hPcomm ⟨x, hA_le_P hx⟩ ⟨e, hEP he⟩)
  have hAE : A ≤ E := fun x hx => hsc x (fun e he => hAcomm x hx e he) (hApow x hx)
  calc p ^ 4 = Nat.card A := hAcard.symm
    _ ≤ Nat.card E := Subgroup.card_le_of_le hAE

end ExcF4Nons

end CFSG.StandardType

end
