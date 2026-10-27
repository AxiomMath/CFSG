module

public import CFSG.Sporadic.HNOddCore.SylD
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem card_filter_fin_countP (n : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter fun k : Fin n => p k = true).card = (List.range n).countP p := by
  have h := card_filter_range_eq_countP' n (fun k => p k = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h]
  refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_range.2 k.2, by simpa using hk.2⟩
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

theorem card_fin_true (n : ℕ) (p : ℕ → Bool) :
    Nat.card {c : Fin n // p c = true} = (List.range n).countP p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter_fin_countP]

theorem card_fin_bool (n : ℕ) (p : ℕ → Bool) :
    Nat.card {c : Fin n // p c = true} + Nat.card {c : Fin n // p c = false} = n := by
  have e : {c : Fin n // p c = true} ⊕ {c : Fin n // p c = false} ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun c => by simp)).trans
      (Equiv.sumCompl fun c : Fin n => p c = true)
  rw [← Nat.card_sum, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem sub_orderOf_ne_four {G : Type*} [Group G] {H : Subgroup G} {a : H} (h : a ^ 2 = 1) :
    orderOf a ≠ 4 := by
  intro h4
  have := orderOf_dvd_of_pow_eq_one h
  rw [h4] at this
  exact absurd this (by norm_num)

theorem exists_cycleType_of_sq {σ : Perm (Fin 12)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (hord ▸ Nat.prime_two)
  rw [hord] at hn
  refine ⟨n + 1, by omega, ?_, hn⟩
  have hs := σ.sum_cycleType_le
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  omega

theorem PR_eq :
    PR = Subgroup.closure
    (Set.range (fun i : Fin 14 => wordVal gR pWords[(i : ℕ)]!) ∪ {jR t4J}) := by
  show Subgroup.map C4.subtype (Subgroup.closure _) = _
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, (⟨i, rfl⟩ | rfl), rfl⟩
    · exact Or.inl ⟨i, (gensC_coe i).symm⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨gensC i, Or.inl ⟨i, rfl⟩, gensC_coe i⟩
    · exact ⟨t4C, Or.inr rfl, rfl⟩

theorem nine_iff
    (c : Fin 29) : (∀ y ∈ Pc, rho4 y = repPerm c → orderOf y = 4) ↔
    InvData.nonRep.contains pReps[(c : ℕ)]! = true := by
  constructor
  · intro h
    by_contra hn
    rw [Bool.not_eq_true] at hn
    have := h _ (liftC_mem _) (by rw [← ePerm_eq (rep_lt c.2)]; rfl)
    exact sub_orderOf_ne_four (rep_sq c.2 hn) this
  · intro h y _ hy
    exact nonRep_orderOf c.2 h hy

theorem twenty_iff
    (c : Fin 29) : (∀ y ∈ Pc, rho4 y = repPerm c → y ^ 2 = 1) ↔
    InvData.nonRep.contains pReps[(c : ℕ)]! = false := by
  constructor
  · intro h
    by_contra hn
    rw [Bool.not_eq_false] at hn
    exact nonRep_sq hn (h _ (liftC_mem _) (by rw [← ePerm_eq (rep_lt c.2)]; rfl))
  · intro h y _ hy
    rcases lift_eq (rep_lt c.2) hy with rfl | rfl
    · exact rep_sq c.2 h
    · rw [mul_t4C_sq]
      exact rep_sq c.2 h

theorem card_nine :
    Nat.card {c : Fin 29 // ∀ y ∈ Pc, rho4 y = repPerm c → orderOf y = 4} = 9 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight nine_iff),
    card_fin_true 29 (fun c => InvData.nonRep.contains pReps[c]!)]
  exact wit_parts.2.2.2.2.2.1

theorem card_twenty :
    Nat.card {c : Fin 29 // ∀ y ∈ Pc, rho4 y = repPerm c → y ^ 2 = 1} = 20 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight twenty_iff)]
  have h := card_fin_bool 29 (fun c => InvData.nonRep.contains pReps[c]!)
  rw [card_fin_true 29 (fun c => InvData.nonRep.contains pReps[c]!), wit_parts.2.2.2.2.2.1] at h
  generalize Nat.card {c : Fin 29 // InvData.nonRep.contains pReps[(c : ℕ)]! = false} = x at h ⊢
  omega

theorem thetaR_conj_sq
    {y g : RH} (hy2 : y ^ 2 = 1) (hg : g * y * g⁻¹ ∈ RV) :
    thetaR ⟨g * y * g⁻¹, hg⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have e : (⟨g * y * g⁻¹, hg⟩ : RV) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (g * y * g⁻¹) ^ 2 = 1
    rw [conj_pow, hy2, mul_one, mul_inv_cancel]
  rw [e, map_one]

theorem thetaR_conj_ne_one
    {y g : RH} (hy1 : y ≠ 1) (hg : g * y * g⁻¹ ∈ RV) :
    thetaR ⟨g * y * g⁻¹, hg⟩ ≠ 1 := by
  intro h
  rw [← map_one thetaR] at h
  have h' := congrArg Subtype.val (thetaR.injective h)
  rw [Subgroup.coe_one] at h'
  apply hy1
  have h'' : g * y * g⁻¹ = 1 := h'
  rw [show y = g⁻¹ * (g * y * g⁻¹) * g by group, h'']
  group

theorem ctuc_hn_Sylow_two_complete_involution_coverage :
    PR = Subgroup.closure (Set.range (fun i : Fin 14 => wordVal gR pWords[(i : ℕ)]!) ∪ {jR t4J}) ∧
    (∃ S : Sylow 2 RH, (S : Subgroup RH) = PR) ∧ Nat.card PR = 32768 ∧
    Pc.map rho4 = Pbar ∧ Nat.card Pbar = 16384 ∧ Nat.card {x : Pbar // x ^ 2 = 1} = 880 ∧
    (∀ c : Fin 29, repPerm c ∈ Pbar ∧ repPerm c ^ 2 = 1) ∧
    (∀ x ∈ Pbar, x ^ 2 = 1 → ∃! c : Fin 29, ∃ y ∈ Pbar, y * repPerm c * y⁻¹ = x) ∧
    Nat.card {c : Fin 29 // ∀ y ∈ Pc, rho4 y = repPerm c → orderOf y = 4} = 9 ∧
    Nat.card {c : Fin 29 // ∀ y ∈ Pc, rho4 y = repPerm c → y ^ 2 = 1} = 20 ∧
    Nat.card InvLift = 39 ∧ (∀ u : InvLift, ∃ g : RH, g * (u.1 : RH) * g⁻¹ ∈ RV) ∧
    ∀ y : RH, y ^ 2 = 1 → y ≠ 1 → ∃ g : RH, ∃ hg : g * y * g⁻¹ ∈ RV,
      ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ (thetaR ⟨g * y * g⁻¹, hg⟩).cycleType = Multiset.replicate k 2 := by
  refine ⟨PR_eq, ⟨PR_isPGroup.toSylow PR_not_dvd, IsPGroup.toSylow_coe _ _⟩, card_PR, map_Pc,
    card_Pbar, card_inv_Pbar, fun c => ⟨repPerm_mem c.2, repPerm_sq c.2⟩, classes_Pbar,
    card_nine, card_twenty, card_invLift, ?_, ?_⟩
  · rintro ⟨u, -, hu2, hu1, -⟩
    refine exists_conj_RV ?_ ?_
    · rw [← Subgroup.coe_pow, hu2, Subgroup.coe_one]
    · intro h
      exact hu1 (Subtype.ext h)
  · intro y hy2 hy1
    obtain ⟨g, hg⟩ := exists_conj_RV hy2 hy1
    exact ⟨g, hg, exists_cycleType_of_sq (thetaR_conj_sq hy2 hg) (thetaR_conj_ne_one hy1 hg)⟩

end CFSG.Sporadic.HNOddCore
