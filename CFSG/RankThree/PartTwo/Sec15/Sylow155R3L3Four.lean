module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (descendAut projectiveSL)
open scoped commutatorElement

private theorem isInnerAut_of_orderOf_prime_card_four {k : Type} [Field k] (hk : Nat.card k = 4)
    {α : MulAut (projectiveSL 3 k)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hα : orderOf α = p) :
    KFacts.IsInnerAut α := by
  set Inn : Subgroup (MulAut (projectiveSL 3 k)) :=
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range with hInn
  haveI : Inn.Normal := ⟨fun τ hτ γ => (KFacts.isInnerAut_conj_iff γ τ).2 hτ⟩
  have hInnCard : Nat.card Inn = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (KFacts.L34.conj_injective hk)).toEquiv,
      KFacts.L34.card_projectiveSL hk]
  have hq : Nat.card (MulAut (projectiveSL 3 k) ⧸ Inn) = 12 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Inn
    rw [KFacts.L34.card_mulAut hk, hInnCard] at h
    omega
  have hcop : Nat.Coprime p 12 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h12] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · have := Nat.Prime.dvd_of_dvd_pow hp h
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  have h1 : orderOf ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn) ∣ p := by
    rw [← hα]
    exact orderOf_map_dvd (QuotientGroup.mk' Inn) α
  have h2 := orderOf_dvd_natCard
    ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn)
  rw [hq] at h2
  have h3 : orderOf ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact Nat.dvd_one.1 this
  have h4 : α ∈ Inn := (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)
  exact h4

theorem false_of_prime_order_commute_conj_card_four {K : Type} [Field K]
    (hK : Sec4.PiField true 2 2 K) {j : ↥(Sec4.slPi true 3 (2 ^ 2) K)} (hj3 : j ^ 3 = 1)
    (hjc : j ∉ Subgroup.center ↥(Sec4.slPi true 3 (2 ^ 2) K))
    {α : MulAut ↥(Sec4.slPi true 3 (2 ^ 2) K)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hα : orderOf α = p) (hcomm : Commute (MulAut.conj j) α) : False := by
  have hcard : Nat.card K = 4 := by simpa [Sec4.piCard] using hK.card
  have hq : Sec4.ModThree true (2 ^ 2) := by
    change 2 ^ 2 % 3 = 1
    norm_num
  have hinner : KFacts.IsInnerAut α := by
    set E := Sec4.slPiTrueEquiv (2 ^ 2) K with hE
    have hβo : orderOf (MulAut.congr E α) = p := by
      rw [MulEquiv.orderOf_eq]
      exact hα
    have hd : orderOf (descendAut 3 K (MulAut.congr E α)) = p := by
      have h1 : orderOf (descendAut 3 K (MulAut.congr E α)) ∣ p := by
        rw [← hβo]
        exact orderOf_map_dvd (descendAut 3 K) _
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exfalso
        have h2 : MulAut.congr E α = 1 :=
          KFacts.eq_of_descendAut_eq (by rw [orderOf_eq_one_iff.1 h, map_one])
        rw [h2, orderOf_one] at hβo
        exact hp.one_lt.ne hβo
      · exact h
    exact (KFacts.isInnerAut_congr E α).1
      ((KFacts.isInnerAut_descendAut_iff le_rfl).1
        (isInnerAut_of_orderOf_prime_card_four hcard hp hp5 hd))
  obtain ⟨s, hs⟩ := hinner
  have hz : MulAut.conj ⁅j, s⁆ = 1 := by
    rw [map_commutatorElement, hs]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq
  have hzc : ⁅j, s⁆ ∈ Subgroup.center ↥(Sec4.slPi true 3 (2 ^ 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut ↥(Sec4.slPi true 3 (2 ^ 2) K) => φ g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * ⁅j, s⁆ = ⁅j, s⁆ * g * ⁅j, s⁆⁻¹ * ⁅j, s⁆ := by rw [h]
      _ = ⁅j, s⁆ * g := by group
  have hz3 : ⁅j, s⁆ ^ 3 = 1 := Sec4.pow_three_eq_one_of_mem_center hK hq hzc
  have hjs3 : j * s ^ 3 * j⁻¹ = s ^ 3 := by
    have h1 : j * s * j⁻¹ = ⁅j, s⁆ * s := by
      rw [commutatorElement_def]
      group
    calc j * s ^ 3 * j⁻¹ = (j * s * j⁻¹) ^ 3 := conj_pow.symm
      _ = (⁅j, s⁆ * s) ^ 3 := by rw [h1]
      _ = ⁅j, s⁆ ^ 3 * s ^ 3 := Commute.mul_pow (Subgroup.mem_center_iff.1 hzc s).symm 3
      _ = s ^ 3 := by rw [hz3, one_mul]
  have hjt : j * s ^ 3 = s ^ 3 * j := by
    rw [mul_inv_eq_iff_eq_mul] at hjs3
    exact hjs3
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  obtain ⟨g, hg⟩ := Sec12.Hering129L.exists_conj_to_diagTau hK hq hτ hτ1 hj3 hjc
  have hcent : ((g * s ^ 3 * g⁻¹ : ↥(Sec4.slPi true 3 (2 ^ 2) K)) : GL (Fin 3) K) ∈
      Subgroup.centralizer {Sec4.diagTau hτ} := by
    have hcm : g * s ^ 3 * g⁻¹ * (g * j * g⁻¹) = g * j * g⁻¹ * (g * s ^ 3 * g⁻¹) :=
      calc g * s ^ 3 * g⁻¹ * (g * j * g⁻¹) = g * (s ^ 3 * j) * g⁻¹ := by group
        _ = g * (j * s ^ 3) * g⁻¹ := by rw [hjt]
        _ = g * j * g⁻¹ * (g * s ^ 3 * g⁻¹) := by group
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    exact congrArg Subtype.val hcm
  have hmem : ((g * s ^ 3 * g⁻¹ : ↥(Sec4.slPi true 3 (2 ^ 2) K)) : GL (Fin 3) K) ∈
      Sec4.slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer {Sec4.diagTau hτ} :=
    Subgroup.mem_inf.2 ⟨(g * s ^ 3 * g⁻¹).2, hcent⟩
  rw [Sec4.centralizer_diagTau_eq hK hq hτ hτ1] at hmem
  obtain ⟨⟨a, b⟩, hab⟩ := hmem
  have h3 : Sec4.qSubPi true (2 ^ 2) = 3 := by decide
  have hroot : ∀ {n : ℕ}, n = 3 → ∀ c : ↥(rootsOfUnity n K), c ^ 3 = 1 := by
    rintro n rfl c
    exact Subtype.ext ((mem_rootsOfUnity _ _).1 c.2)
  have hab3 : ((a, b) : ↥(rootsOfUnity (Sec4.qSubPi true (2 ^ 2)) K) ×
      ↥(rootsOfUnity (Sec4.qSubPi true (2 ^ 2)) K)) ^ 3 = 1 :=
    Prod.ext (hroot h3 a) (hroot h3 b)
  have hu3 : ((g * s ^ 3 * g⁻¹ : ↥(Sec4.slPi true 3 (2 ^ 2) K)) : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← hab, ← map_pow, hab3, map_one]
  have hu3' : (g * s ^ 3 * g⁻¹) ^ 3 = 1 := Subtype.ext hu3
  have hs9 : s ^ 9 = 1 := by
    rw [conj_pow] at hu3'
    simpa [← pow_mul] using hu3'
  have hα9 : α ^ 9 = 1 := by rw [← hs, ← map_pow, hs9, map_one]
  have hdvd : p ∣ 3 ^ 2 := by
    have := orderOf_dvd_of_pow_eq_one hα9
    rw [hα] at this
    exact this
  have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
  omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
