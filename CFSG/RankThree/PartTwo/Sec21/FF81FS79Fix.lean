module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79N2
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79NF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.rho_pow (h : FS79Hyp b t b₁ b₂ J) {n : H} (hn : n ∈ Nor (Subgroup.zpowers b))
    (k : ℕ) : h.rho (n ^ k) = (h.rho n) ^ k := by
  induction k with
  | zero => simp [h.rho_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, h.rho_mul ((Nor (Subgroup.zpowers b)).pow_mem hn k) hn, ih]

theorem FS79Hyp.eq_one_of_odd_pow (h : FS79Hyp b t b₁ b₂ J) {a c : H}
    (ha : a ∈ Subgroup.closure ({b, t} : Set H)) (hc : c ∈ J) (hc2 : c * c = 1) {k : ℕ}
    (hk : Odd k) (hac : (a * c) ^ k = 1) : c = 1 := by
  have hcomm : Commute a c := h.Y_comm_J ha hc
  rw [hcomm.mul_pow] at hac
  have hck : c ^ k = (a ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hac
  have hmem : c ^ k ∈ Subgroup.closure ({b, t} : Set H) ⊓ J := by
    refine ⟨?_, J.pow_mem hc k⟩
    rw [hck]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ha k)
  rw [h.bt_inf_J, Subgroup.mem_bot] at hmem
  obtain ⟨m, rfl⟩ := hk
  have hcsq : c ^ 2 = 1 := by rw [pow_two]; exact hc2
  have : c ^ (2 * m + 1) = c := by
    rw [pow_succ, pow_mul, hcsq, one_pow, one_mul]
  rw [← this]
  exact hmem


namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem frame_le_M0 (A₁ : Subgroup J6.S6) :
    S.frame A₁ ≤ Subgroup.closure ({b, t} : Set H) ⊔ J := by
  refine sup_le ?_ ?_
  · refine le_trans ?_ le_sup_left
    rw [Subgroup.zpowers_le]
    exact FS79Hyp.t_mem_Y b t
  · refine le_trans ?_ le_sup_right
    rintro _ ⟨σ, -, rfl⟩
    exact S.ι_mem σ

theorem t_fix {A₁ : Subgroup J6.S6} (hsq : ∀ s ∈ A₁, s * s = 1)
    (h38 : R38Stmt b (A₁.map S.ι)) {n : H} (hn : n ∈ Nor (A₁.map S.ι))
    (hu : n * t * n⁻¹ ∈ S.frame A₁) : n * t * n⁻¹ = t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.hyp
  set L : Subgroup H := Nor (A₁.map S.ι) with hL
  set O₁ : Subgroup H := Opp 2 L with hO₁
  set M₁ : Subgroup H := Nor (Subgroup.zpowers b) ⊓ L with hM₁
  have hmem : n ∈ setMul O₁ M₁ := by
    have := h38
    unfold R38Stmt at this
    rw [hO₁, hM₁, hL, this]
    exact hn
  obtain ⟨o, ho, m, hm, rfl⟩ := hmem
  have ht2 := h.t_sq
  set t' : H := m * t * m⁻¹ with ht'
  have ht'2 : t' * t' = 1 := by
    rw [ht']
    calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have htL : t ∈ L := S.t_mem_Nor_map A₁
  have ht'L : t' ∈ L := L.mul_mem (L.mul_mem hm.2 htL) (L.inv_mem hm.2)
  have htb : t ∈ Nor (Subgroup.zpowers b) := h.t_mem_Nor
  have ht'b : t' ∈ Nor (Subgroup.zpowers b) :=
    (Nor (Subgroup.zpowers b)).mul_mem ((Nor (Subgroup.zpowers b)).mul_mem hm.1 htb)
      ((Nor (Subgroup.zpowers b)).inv_mem hm.1)
  have hnt : o * m * t * (o * m)⁻¹ = o * t' * o⁻¹ := by rw [ht']; group
  set u : H := o * m * t * (o * m)⁻¹ with hu_def
  have hub : u ∈ Nor (Subgroup.zpowers b) := S.frame_le_Nor_b A₁ hu
  have huM0 : u ∈ Subgroup.closure ({b, t} : Set H) ⊔ J := S.frame_le_M0 A₁ hu
  have huL : u ∈ L := L.mul_mem (L.mul_mem hn htL) (L.inv_mem hn)
  have hu1 : u ≠ 1 := by
    intro h1
    apply h.t_ne_one
    calc t = (o * m)⁻¹ * u * (o * m) := by rw [hu_def]; group
      _ = 1 := by rw [h1]; group
  have hwO : u * t' ∈ O₁ := by
    have h1 : u * t' = o * (t' * o⁻¹ * t'⁻¹) := by
      have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
      rw [hnt, ht'inv]
      group
    rw [h1]
    exact O₁.mul_mem ho (L14.Opp_conj_mem ht'L (O₁.inv_mem ho))
  have hwb : u * t' ∈ Nor (Subgroup.zpowers b) := (Nor (Subgroup.zpowers b)).mul_mem hub ht'b
  have hOodd : Odd (Nat.card O₁) := Nat.coprime_two_left.mp (L14.Opp_coprime 2 L)
  have hwodd : Odd (orderOf (u * t')) := by
    have := orderOf_dvd_natCard (⟨u * t', hwO⟩ : ↥O₁)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hOodd this
  have hρu : h.rho u = u := h.rho_of_mem_M0 huM0
  have hρt : h.rho t = t := h.rho_of_mem_M0 (Subgroup.mem_sup_left (FS79Hyp.t_mem_Y b t))
  obtain ⟨hρm, -⟩ := h.rho_spec hm.1
  obtain ⟨y, hy, j, hj, hyj⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hρm
  have hjt : j * t = t * j := S.J_comm_t hj
  have hρt' : h.rho t' = y * t * y⁻¹ := by
    rw [ht', h.rho_conj hm.1 htb, hρt, ← hyj]
    calc y * j * t * (y * j)⁻¹ = y * (j * t) * j⁻¹ * y⁻¹ := by group
      _ = y * (t * j) * j⁻¹ * y⁻¹ := by rw [hjt]
      _ = y * t * y⁻¹ := by group
  have hρw : h.rho (u * t') = u * (y * t * y⁻¹) := by
    rw [h.rho_mul hub ht'b, hρu, hρt']
  have hpow : (u * (y * t * y⁻¹)) ^ orderOf (u * t') = 1 := by
    rw [← hρw, ← h.rho_pow hwb, pow_orderOf_eq_one, h.rho_one]
  generalize orderOf (u * t') = k at hwodd hpow
  have hty : y * t * y⁻¹ ∈ Subgroup.closure ({b, t} : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hy (FS79Hyp.t_mem_Y b t)) (Subgroup.inv_mem _ hy)
  obtain ⟨s, hs, hus⟩ := (S.mem_frame_iff A₁ u).mp hu
  have hss : S.ι s * S.ι s = 1 := by rw [← map_mul, hsq s hs, map_one]
  have hcomm_s : (y * t * y⁻¹) * S.ι s = S.ι s * (y * t * y⁻¹) :=
    h.Y_comm_J hty (S.ι_mem s)
  rcases hus with hus | hus
  · exfalso
    apply hu1
    have : S.ι s = 1 := by
      refine h.eq_one_of_odd_pow hty (S.ι_mem s) hss hwodd ?_
      rw [hus, ← hcomm_s] at hpow
      exact hpow
    rw [hus, this]
  · have hts : S.ι s = 1 := by
      have hty2 : t * (y * t * y⁻¹) ∈ Subgroup.closure ({b, t} : Set H) :=
        Subgroup.mul_mem _ (FS79Hyp.t_mem_Y b t) hty
      refine h.eq_one_of_odd_pow hty2 (S.ι_mem s) hss hwodd ?_
      rw [hus] at hpow
      calc (t * (y * t * y⁻¹) * S.ι s) ^ k
          = (t * S.ι s * (y * t * y⁻¹)) ^ k := by
            congr 1
            calc t * (y * t * y⁻¹) * S.ι s = t * ((y * t * y⁻¹) * S.ι s) := by group
              _ = t * (S.ι s * (y * t * y⁻¹)) := by rw [hcomm_s]
              _ = t * S.ι s * (y * t * y⁻¹) := by group
        _ = 1 := hpow
    rw [hus, hts, mul_one]

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
