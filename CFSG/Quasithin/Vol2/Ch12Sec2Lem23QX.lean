module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_eq {V : Subgroup G} {g t : G} (ht : t ∈ Subgroup.normalizer (V : Set G))
    (heq : ∀ x ∈ V, g * x * g⁻¹ = t * x * t⁻¹) :
    ∀ m : ℕ, ∀ x ∈ V, g ^ m * x * (g ^ m)⁻¹ = t ^ m * x * (t ^ m)⁻¹ := by
  intro m
  induction m with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have h1 : t ^ k * x * (t ^ k)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht k) x).mp hx
    calc g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = g * (t ^ k * x * (t ^ k)⁻¹) * g⁻¹ := by rw [ih x hx]
      _ = t * (t ^ k * x * (t ^ k)⁻¹) * t⁻¹ := heq _ h1
      _ = t ^ (k + 1) * x * (t ^ (k + 1))⁻¹ := by rw [pow_succ']; group

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem frattini_le_normalizer_CT (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (e : Extra3 T L V H P U I h) :
    (frattini ↥P).map P.subtype ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := e.pre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hΦP : Φ ≤ P := frattini_map_le P
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  intro f hf
  have hfV : f ∈ Subgroup.normalizer (V : Set G) := e.ΦV hf
  have hfH : f ∈ H := hPH (hΦP hf)
  refine Sec121Swap.mem_normalizer_of_conj_mem fun c hc => ?_
  have hcT : c ∈ T := hc.1
  have hfcV : f * c * f⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : f⁻¹ * x * f ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hfV) x).mp hx
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hc.2) _ hx'
    calc x * (f * c * f⁻¹) = f * ((f⁻¹ * x * f) * c) * f⁻¹ := by group
      _ = f * (c * (f⁻¹ * x * f)) * f⁻¹ := by rw [h1]
      _ = f * c * f⁻¹ * x := by group
  refine ⟨?_, hfcV⟩
  obtain ⟨q, hq, hn⟩ := exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1
    (hTH hcT)
  set n := q * c with hndef
  have hnT : n ∈ T := T.mul_mem (hQT hq) hcT
  have hfq : f * q * f⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hfH) q).mp hq
  set φ := f * n * f⁻¹ * n⁻¹ with hφdef
  have hφΦ : φ ∈ Φ := by
    have h1 : n * f⁻¹ * n⁻¹ ∈ Φ := conj_mem_frattini hn (Φ.inv_mem hf)
    have e1 : φ = f * (n * f⁻¹ * n⁻¹) := by rw [hφdef]; group
    rw [e1]
    exact Φ.mul_mem hf h1
  set t := (f * q * f⁻¹) * n⁻¹ with htdef
  have htT : t ∈ T := T.mul_mem (hQT hfq) (T.inv_mem hnT)
  have heq : ∀ x ∈ V, φ * x * φ⁻¹ = t * x * t⁻¹ := by
    intro x hx
    have hy : n⁻¹ * x * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem hnT)) x).mp hx
      simpa using this
    have h1 : (f * c * f⁻¹) * (n⁻¹ * x * n) = (n⁻¹ * x * n) * (f * c * f⁻¹) :=
      ((Subgroup.mem_centralizer_iff.mp hfcV) _ hy).symm
    have e1 : φ = (f * q * f⁻¹) * (f * c * f⁻¹) * n⁻¹ := by rw [hφdef, hndef]; group
    rw [e1, htdef]
    calc (f * q * f⁻¹) * (f * c * f⁻¹) * n⁻¹ * x * ((f * q * f⁻¹) * (f * c * f⁻¹) * n⁻¹)⁻¹
        = (f * q * f⁻¹) * ((f * c * f⁻¹) * (n⁻¹ * x * n)) * (f * c * f⁻¹)⁻¹ *
            (f * q * f⁻¹)⁻¹ := by group
      _ = (f * q * f⁻¹) * ((n⁻¹ * x * n) * (f * c * f⁻¹)) * (f * c * f⁻¹)⁻¹ *
            (f * q * f⁻¹)⁻¹ := by rw [h1]
      _ = (f * q * f⁻¹) * n⁻¹ * x * ((f * q * f⁻¹) * n⁻¹)⁻¹ := by group
  obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hφk : φ ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := conj_pow_eq (hTV htT) heq (2 ^ k) x hx
    rw [htk] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc x * φ ^ 2 ^ k = (φ ^ 2 ^ k * x * (φ ^ 2 ^ k)⁻¹) * φ ^ 2 ^ k := by rw [h1]
      _ = φ ^ 2 ^ k * x := by group
  have hφ3 : φ ^ 3 = 1 := e.exp φ (hΦP hφΦ)
  have hcop : Nat.Coprime (orderOf φ) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hφ3)
      (Nat.Coprime.pow_right _ (by norm_num))
  have hφV : φ ∈ Subgroup.centralizer (V : Set G) := B6.mem_of_pow_mem_of_coprime hφk hcop
  have hφ1 : φ = 1 := e.eq_one_of_comm_inf hφΦ fun u hu =>
    ((Subgroup.mem_centralizer_iff.mp hφV) u hu.1).symm
  have e1 : f * c * f⁻¹ = (f * q * f⁻¹)⁻¹ * (φ * n) := by rw [hφdef, hndef]; group
  rw [e1, hφ1, one_mul]
  exact T.mul_mem (T.inv_mem (hQT hfq)) hnT

end Extra3

end Lem22

end CFSG.Quasithin.H13
