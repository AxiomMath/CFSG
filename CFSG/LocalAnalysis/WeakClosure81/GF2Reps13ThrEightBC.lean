module

public import CFSG.Quasithin.MS93.S36SpSyl
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpA
public import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.A3Structure36BElemBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_card_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod p) = p ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem w16g_le_normalizer_zpowers_of_le_normalizer
    {P : Subgroup (MulAut W)} {z : MulAut W}
    (hzP : z ∈ P) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z)
    {O : Subgroup (MulAut W)} (hO : O ≤ Subgroup.normalizer (P : Set (MulAut W))) :
    O ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W)) := by
  rw [Subgroup.le_normalizer_iff]
  intro o ho x hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hz' : o * z * o⁻¹ ∈ Subgroup.zpowers z := by
    have hmemP : o * z * o⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hO ho) z).mp hzP
    refine hZP _ hmemP ?_
    intro y hy
    have hy' : o⁻¹ * y * o ∈ P := by
      refine (Subgroup.mem_normalizer_iff.mp (hO ho) (o⁻¹ * y * o)).mpr ?_
      show o * (o⁻¹ * y * o) * o⁻¹ ∈ P
      simpa [mul_assoc] using hy
    have hcy : y * (o * z * o⁻¹) = (o * z * o⁻¹) * y := by
      have h := hzc (o⁻¹ * y * o) hy'
      calc y * (o * z * o⁻¹) = o * ((o⁻¹ * y * o) * z) * o⁻¹ := by group
        _ = o * (z * (o⁻¹ * y * o)) * o⁻¹ := by rw [h]
        _ = (o * z * o⁻¹) * y := by group
    exact hcy
  have hpow : o * z ^ i * o⁻¹ = (o * z * o⁻¹) ^ i := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [hpow]
  exact Subgroup.zpow_mem (K := Subgroup.zpowers z) hz' i

theorem w16g_isPOnePlusTwo_sup {N M : Subgroup (MulAut W)}
    (hN : IsElemAbelianOfRank 3 2 ↥N) (hM : IsElemAbelianOfRank 3 2 ↥M)
    (hMN : M ≤ Subgroup.normalizer (N : Set (MulAut W)))
    (hNM : N ≤ Subgroup.normalizer (M : Set (MulAut W)))
    (hcomm : ⁅N, M⁆ ≠ ⊥) :
    IsPOnePlusTwo 3 ↥(N ⊔ M) := by
  obtain ⟨hNab, hNe⟩ := CFSG.Quasithin.A36B.IsElemAbelianOfRank.comm_pow hN
  obtain ⟨hMab, hMe⟩ := CFSG.Quasithin.A36B.IsElemAbelianOfRank.comm_pow hM
  have hN9 : Nat.card ↥N = 9 := by
    rw [w16g_card_of_isElemAbelianOfRank hN]; norm_num
  have hM9 : Nat.card ↥M = 9 := by
    rw [w16g_card_of_isElemAbelianOfRank hM]; norm_num
  have hNab' : ∀ a ∈ N, ∀ a' ∈ N, a * a' = a' * a :=
    fun a ha a' ha' => congrArg Subtype.val (hNab ⟨a, ha⟩ ⟨a', ha'⟩)
  have hMab' : ∀ a ∈ M, ∀ a' ∈ M, a * a' = a' * a :=
    fun a ha a' ha' => congrArg Subtype.val (hMab ⟨a, ha⟩ ⟨a', ha'⟩)
  have hL : N ⊔ M ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hMN
  have hL' : N ⊔ M ≤ Subgroup.normalizer (M : Set (MulAut W)) :=
    sup_le hNM Subgroup.le_normalizer
  have hcommSub : ⁅N, M⁆ ≤ N ⊓ M := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro n hn m hm
      have hm' : m * n⁻¹ * m⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hMN hm) n⁻¹).mp (N.inv_mem hn)
      have hcalc : ⁅n, m⁆ = n * (m * n⁻¹ * m⁻¹) := by rw [commutatorElement_def]; group
      rw [hcalc]
      exact N.mul_mem hn hm'
    · rw [Subgroup.commutator_le]
      intro n hn m hm
      have hn' : n * m * n⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hNM hn) m).mp hm
      have hcalc : ⁅n, m⁆ = (n * m * n⁻¹) * m⁻¹ := by rw [commutatorElement_def]
      rw [hcalc]
      exact M.mul_mem hn' (M.inv_mem hm)
  have hinf_ne : N ⊓ M ≠ ⊥ := by
    intro h
    exact hcomm (le_bot_iff.mp (hcommSub.trans (le_of_eq h)))
  have hinf_card : Nat.card (N ⊓ M : Subgroup (MulAut W)) = 3 := by
    have hdvd : Nat.card (N ⊓ M : Subgroup (MulAut W)) ∣ 3 ^ 2 := by
      have h1 : Nat.card (N ⊓ M : Subgroup (MulAut W)) ∣ Nat.card ↥N :=
        Subgroup.card_dvd_of_le inf_le_left
      rwa [hN9] at h1
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      haveI : Nontrivial ↥(N ⊓ M) := (Subgroup.nontrivial_iff_ne_bot _).mpr hinf_ne
      have hlt : 1 < Nat.card ↥(N ⊓ M) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hk
    · exfalso
      have hNMeq : N ⊓ M = N :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hN9, hk]; norm_num)
      have hNMle : N ≤ M := hNMeq ▸ inf_le_right
      have hNMeq2 : N = M := Subgroup.eq_of_le_of_card_ge hNMle (by rw [hN9, hM9])
      exact hcomm (le_bot_iff.mp (by
        rw [hNMeq2, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hMab' a ha b hb))
  have hcard : Nat.card ↥(N ⊔ M) = 27 := by
    have hcm := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf
      (X := N) (N := M) hNM
    rw [hN9, hM9, hinf_card] at hcm
    omega
  have hnc : ∃ u v : ↥(N ⊔ M), u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    apply hcomm
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro n hn m hm
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hcon ⟨n, Subgroup.mem_sup_left hn⟩ ⟨m, Subgroup.mem_sup_right hm⟩)
  have hgen : Subgroup.closure {x : ↥(N ⊔ M) | x ^ 3 = 1} = ⊤ := by
    refine le_antisymm le_top ?_
    intro x hx
    have hxL : (x : MulAut W) ∈ (N : Set (MulAut W)) * (M : Set (MulAut W)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N M hMN]
      exact x.2
    obtain ⟨n, hn, m, hm, hnm⟩ := hxL
    have hxeq : x = (⟨n, Subgroup.mem_sup_left hn⟩ : ↥(N ⊔ M)) *
        ⟨m, Subgroup.mem_sup_right hm⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hnm.symm
    rw [hxeq]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · show (⟨n, Subgroup.mem_sup_left hn⟩ : ↥(N ⊔ M)) ^ 3 = 1
      apply Subtype.ext
      simpa using congrArg Subtype.val (hNe ⟨n, hn⟩)
    · show (⟨m, Subgroup.mem_sup_right hm⟩ : ↥(N ⊔ M)) ^ 3 = 1
      apply Subtype.ext
      simpa using congrArg Subtype.val (hMe ⟨m, hm⟩)
  have hcl : ClassLeTwo (⊤ : Subgroup ↥(N ⊔ M)) :=
    classLeTwo_top_of (CFSG.Quasithin.MS93.S36SP.commutator_commutator_eq_bot_of_sup
      hNab' hMab' hL hL')
  have hexp : ∀ x : ↥(N ⊔ M), x ^ 3 = 1 :=
    pow_eq_one_of_classLeTwo (p := 3) (P := ↥(N ⊔ M)) (by norm_num) hcl hgen
  exact ⟨CFSG.Quasithin.SzN31.isExtraspecial_three_of_card_27 hcard hnc hexp,
    by rw [hcard]; norm_num, hexp⟩

end CFSG.LocalAnalysis.WeakClosure81
