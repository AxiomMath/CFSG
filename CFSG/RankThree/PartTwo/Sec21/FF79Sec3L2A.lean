module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3Chr
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn
open scoped commutatorElement

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_top_of_nor {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    (h : Nat.Coprime p (P.relIndex (Nor P))) : IsSylowOf p P ⊤ := by
  refine ⟨le_top, hP, ?_⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [Subgroup.relIndex_top_right]
  by_contra hc
  have hdvd : p ∣ P.index := (Nat.Prime.coprime_iff_not_dvd hp.out).not_left.mp hc
  have h1 : p ^ (n + 1) ∣ Nat.card G := by
    rw [← P.card_mul_index, hn, pow_succ]
    exact Nat.mul_dvd_mul_left _ hdvd
  have h2 := Sylow.prime_dvd_card_quotient_normalizer h1 hn
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp h h2

theorem cube_aux {c a s : G} (h : c * a * c⁻¹ = s * a) (hsc : s * c = c * s)
    (hsa : s * a = a * s) (hs3 : s ^ 3 = 1) (hc3 : c ^ 3 = 1) : (c * a) ^ 3 = a ^ 3 := by
  have h2 : c * (s * a) * c⁻¹ = s * (s * a) := by
    calc c * (s * a) * c⁻¹ = (c * s * c⁻¹) * (c * a * c⁻¹) := by group
      _ = s * (s * a) := by rw [h, ← hsc]; group
  have h3 : c * (s * (s * a)) * c⁻¹ = s * (s * (s * a)) := by
    calc c * (s * (s * a)) * c⁻¹ = (c * s * c⁻¹) * (c * (s * a) * c⁻¹) := by group
      _ = s * (s * (s * a)) := by rw [h2, ← hsc]; group
  have e : (c * a) ^ 3 = (c * a * c⁻¹) * (c * (c * a * c⁻¹) * c⁻¹) *
      (c * (c * (c * a * c⁻¹) * c⁻¹) * c⁻¹) * c ^ 3 := by
    rw [pow_three, pow_three]; group
  rw [e, hc3, mul_one, h, h2, h3]
  have hsa' : Commute s a := hsa
  have c2 : a * s ^ 2 = s ^ 2 * a := ((Commute.pow_left hsa' 2).eq).symm
  have c3 : a ^ 2 * s ^ 3 = s ^ 3 * a ^ 2 := ((Commute.pow_pow hsa' 3 2).eq).symm
  calc s * a * (s * (s * a)) * (s * (s * (s * a))) = s * (a * s ^ 2) * a * (s ^ 3 * a) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = s * (s ^ 2 * a) * a * (s ^ 3 * a) := by rw [c2]
    _ = s ^ 3 * (a ^ 2 * s ^ 3) * a := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = s ^ 3 * (s ^ 3 * a ^ 2) * a := by rw [c3]
    _ = a ^ 3 := by rw [hs3]; group

theorem lin_10 (e₁ e₂ : Z3) : lin e₁ e₂ (1, 0) = e₁ := by rw [lin_eq]; ext <;> simp

theorem lin_01 (e₁ e₂ : Z3) : lin e₁ e₂ (0, 1) = e₂ := by rw [lin_eq]; ext <;> simp

theorem lin_cols (E₁ E₂ q : Z3) : lin (lin E₁ E₂ (1, 0)) (lin E₁ E₂ (0, 1)) q = lin E₁ E₂ q := by
  rw [lin_10, lin_01]

theorem two_ne_zero_z3 : (2 : ZMod 3) ≠ 0 := by decide

theorem one_val_smul (q : Z3) : (1 : ZMod 3).val • q = q := one_smul ℕ q

set_option maxRecDepth 4000 in
theorem scalar_check : ∀ l : ZMod 3, l ≠ 0 → ∀ f : Z3, f ≠ 0 →
    ((l * ((2 : ZMod 3) * f.1), l * ((2 : ZMod 3) * f.2)) : Z3) ≠ (l * f.1, l * f.2) := by
  decide

theorem scalar_inj : ∀ l : ZMod 3, l ≠ 0 → ∀ q : Z3, ((l * q.1, l * q.2) : Z3) = 0 → q = 0 := by
  decide

theorem noncomm_check :
    ∃ q : Z3, linHom (2, 0) (0, 1) (linHom (0, 1) (1, 0) q) ≠
      linHom (0, 1) (1, 0) (linHom (2, 0) (0, 1) q) := ⟨(1, 0), by decide⟩

theorem comm_conj {g a : G} (h : g * a * g⁻¹ = a) : g⁻¹ * a * g = a := by
  calc g⁻¹ * a * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]
    _ = a := by group

namespace PCtx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} {P : Subgroup G} {x y : G}
  (K : PCtx b J B u v r₁ r₂ w P x y)
include K

theorem cube_comm_J {c₁ c₂ : Z3} (h1 : x ^ 3 = ψ u v c₁) (h2 : y ^ 3 = ψ u v c₂) {r : G}
    (hrJ : r ∈ J) (hrN : r ∈ Nor B) {E₁ E₂ : Z3} (hr : ∀ p, r * ψ u v p * r⁻¹ = ψ u v (lin E₁ E₂ p))
    (q : Z3) : lin c₁ c₂ (lin E₁ E₂ q) = lin E₁ E₂ (lin c₁ c₂ q) := by
  obtain ⟨m, hmP, hmB, hmb, hmR⟩ := K.toCtx.realize K.hP hrN (n := 1)
    (by rw [pow_one]; exact K.toCtx.conj_b_of_J hrJ)
  rw [pow_one] at hmb
  have hf₁ : m * u * m⁻¹ = ψ u v (lin E₁ E₂ (1, 0)) := by
    rw [hmR u K.toCtx.uR, ← hr, ψ_10]
  have hf₂ : m * v * m⁻¹ = ψ u v (lin E₁ E₂ (0, 1)) := by
    rw [hmR v K.toCtx.vR, ← hr, ψ_01]
  have he : m⁻¹ * b * m = b ^ (1 : ZMod 3).val * ψ u v 0 := by
    rw [comm_conj hmb, ψ_zero, mul_one]; exact (pow_val_one b).symm
  have := K.cube_equivariant h1 h2 hmP hmB hf₁ hf₂ he q
  rwa [one_val_smul, lin_cols, lin_cols] at this

theorem cube_scalar {c₁ c₂ : Z3} (h1 : x ^ 3 = ψ u v c₁) (h2 : y ^ 3 = ψ u v c₂) :
    ∃ l : ZMod 3, ∀ q, lin c₁ c₂ q = (l * q.1, l * q.2) := by
  have e1 := K.cube_comm_J h1 h2 K.toCtx.r₁J K.toCtx.r₁N (nd_r₁_conj K.toCtx.nd)
  have e2 := K.cube_comm_J h1 h2 K.toCtx.wJ K.toCtx.wN (nd_w_conj K.toCtx.nd)
  exact E9.comm_scalar (linHom (2, 0) (0, 1)) (linHom (0, 1) (1, 0)) (linHom c₁ c₂)
    noncomm_check (fun q => e1 q) (fun q => e2 q)

theorem cube_bpow {a : G} (ha : a ∈ Agrp x y u v) (k : ℕ) : (b ^ k * a) ^ 3 = a ^ 3 := by
  have haT := K.A_le_T ha
  set s := (θ b a)⁻¹ ^ k with hs
  have hsR : s ∈ R u v := (R u v).pow_mem ((R u v).inv_mem (K.toCtx.θ_mem haT)) k
  refine cube_aux (s := s) ?_ ((Commute.pow_left (K.toCtx.comm_bR hsR) k).eq).symm ?_
    (K.toCtx.pow3_R hsR) ?_
  · have := K.toCtx.bpow_comm_T haT k
    calc b ^ k * a * (b ^ k)⁻¹ = (b ^ k * a) * (b ^ k)⁻¹ := rfl
      _ = a * s * b ^ k * (b ^ k)⁻¹ := by rw [this]
      _ = s * a := by
        rw [mul_inv_cancel_right]
        exact (Subgroup.mem_centralizer_iff.mp haT.2.1 s hsR).symm
  · exact (Subgroup.mem_centralizer_iff.mp haT.2.1 s hsR)
  · rw [← pow_mul, mul_comm, pow_mul, K.toCtx.b3, one_pow]

theorem inv_conj_sq {m : G} (hm : m * b * m⁻¹ = b ^ (2 : ZMod 3).val) :
    m⁻¹ * b * m = b ^ (2 : ZMod 3).val * ψ u v 0 := by
  rw [ψ_zero, mul_one, pow_val_two]
  have hc : ∀ n : ℕ, (m⁻¹ * b * m) ^ n = m⁻¹ * b ^ n * m := fun n => by
    have := map_pow (MulAut.conj m⁻¹) b n
    simpa [MulAut.conj_apply] using this.symm
  set t := m⁻¹ * b * m with ht
  have h2 : t ^ 2 = b := by
    rw [ht, hc]; rw [pow_val_two] at hm
    calc m⁻¹ * b ^ 2 * m = m⁻¹ * (m * b * m⁻¹) * m := by rw [hm]
      _ = b := by group
  have h3 : t ^ 3 = 1 := by rw [ht, hc, K.toCtx.b3]; group
  calc t = t ^ 3 * t := by rw [h3, one_mul]
    _ = (t ^ 2) ^ 2 := by rw [← pow_mul, ← pow_succ]
    _ = b ^ 2 := by rw [h2]

theorem cube_one_of_simple (hs : IsSimpleGroup G) (hna : ∃ g h : G, g * h ≠ h * g) {a : G}
    (ha : a ∈ Agrp x y u v) : a ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c₁, c₂, h1, h2⟩ := K.exists_cubes
  obtain ⟨l, hl⟩ := K.cube_scalar h1 h2
  by_cases hl0 : l = 0
  · obtain ⟨q, hq⟩ := exists_ψ K.toCtx.E (K.toCtx.θ_mem (K.A_le_T ha))
    rw [K.cube_eq h1 h2 ha hq, hl, hl0]
    have : (((0 : ZMod 3) * q.1, (0 : ZMod 3) * q.2) : Z3) = 0 := by ext <;> simp
    rw [this, ψ_zero]
  exfalso
  have hinj : ∀ a ∈ Agrp x y u v, a ^ 3 = 1 → a ∈ R u v := by
    intro a ha h3
    obtain ⟨q, hq⟩ := exists_ψ K.toCtx.E (K.toCtx.θ_mem (K.A_le_T ha))
    rw [K.cube_eq h1 h2 ha hq, hl] at h3
    have hq0 := scalar_inj l hl0 q (ψ_eq_one K.toCtx.E h3)
    rw [hq0, ψ_zero] at hq
    exact K.A_inf_B ha (K.toCtx.θ_eq_one_mem_B K.hP (K.A_le_P ha) hq)
  have hΩ : ∀ z ∈ P, z ^ 3 = 1 → z ∈ B := by
    intro z hz h3
    obtain ⟨k, a, ha, rfl⟩ := K.P_decomp hz
    rw [K.cube_bpow ha] at h3
    exact B.mul_mem (B.pow_mem K.toCtx.bB _) (K.toCtx.R_le_B (hinj a ha h3))
  have hNB : ∀ g : G, (∀ y ∈ B, g * y * g⁻¹ ∈ P) → g ∈ Nor B := fun g hg =>
    L41.mem_nor_of_forall fun y hy => hΩ _ (hg y hy) (by rw [conj_pow, K.toCtx.pow3_B hy]; group)
  have hsyl : IsSylowOf 3 P ⊤ := by
    have hle : Nor P ≤ Nor B := fun n hn => hNB n fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hn y).mp (K.hBP hy)
    exact isSylowOf_top_of_nor K.hP.2.1 (isSylowOf_mono K.hP Subgroup.le_normalizer hle).2.2
  have hnoinv : ∀ n ∈ Nor B, ∀ p : Z3, n * b * n⁻¹ ≠ b ^ (2 : ZMod 3).val * ψ u v p := by
    intro n hn p h
    obtain ⟨s, hs, hsb⟩ := K.toCtx.exists_T_fix hn h two_ne_zero_z3
    obtain ⟨m, hmP, hmB, hmb, -⟩ :=
      K.toCtx.realize K.hP (Subgroup.mul_mem _ (K.toCtx.T_le_N hs) hn) hsb
    obtain ⟨f₁, hf₁⟩ := exists_ψ K.toCtx.E (K.toCtx.nor0 hmB K.toCtx.uR)
    obtain ⟨f₂, hf₂⟩ := exists_ψ K.toCtx.E (K.toCtx.nor0 hmB K.toCtx.vR)
    have heq := K.cube_equivariant h1 h2 hmP hmB hf₁ hf₂ (K.inv_conj_sq hmb) (1, 0)
    rw [lin_10, hl, hl, val_nsmul, lin_eq] at heq
    have hf0 : f₁ ≠ 0 := fun h0 => K.u_ne (by
      rw [h0, ψ_zero] at hf₁
      calc u = m⁻¹ * (m * u * m⁻¹) * m := by group
        _ = 1 := by rw [hf₁]; group)
    refine scalar_check l hl0 f₁ hf0 ?_
    rw [heq]; ext <;> simp
  have hcardP : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    have := L41.isSylowOf_card_p hsyl
    rwa [Subgroup.card_top] at this
  let S : Sylow 3 G := Sylow.ofCard P hcardP
  have hSP : (S : Subgroup G) = P := Sylow.coe_ofCard _ _
  have hbn : ∀ n : ℕ, b ^ n ∈ Nor (Agrp x y u v) := fun n => (Nor (Agrp x y u v)).pow_mem K.b_nor n
  have hconjA : ∀ n : ℕ, ∀ {a : G}, a ∈ Agrp x y u v → b ^ n * a * (b ^ n)⁻¹ ∈ Agrp x y u v :=
    fun n a ha => (Subgroup.mem_normalizer_iff.mp (hbn n) a).mp ha
  have habel : ∀ y₁ ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G),
      y₁ * z * y₁⁻¹ * z⁻¹ ∈ Agrp x y u v := by
    intro y' hy' z hz
    rw [hSP] at hy' hz
    obtain ⟨i, a, ha, rfl⟩ := K.P_decomp hy'
    obtain ⟨j, a', ha', rfl⟩ := K.P_decomp hz
    have e : b ^ i.val * a * (b ^ j.val * a') * (b ^ i.val * a)⁻¹ * (b ^ j.val * a')⁻¹ =
        (b ^ i.val * a * (b ^ i.val)⁻¹) *
        (b ^ (i.val + j.val) * (a' * a⁻¹) * (b ^ (i.val + j.val))⁻¹) *
        (b ^ j.val * a'⁻¹ * (b ^ j.val)⁻¹) := by group
    rw [e]
    exact (Agrp x y u v).mul_mem ((Agrp x y u v).mul_mem (hconjA _ ha)
      (hconjA _ ((Agrp x y u v).mul_mem ha' ((Agrp x y u v).inv_mem ha))))
      (hconjA _ ((Agrp x y u v).inv_mem ha'))
  have hfus : ∀ g : G, (∀ y₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {b},
      g⁻¹ * y₁ * g ∈ (S : Subgroup G)) → b⁻¹ * (g⁻¹ * b * g) ∈ Agrp x y u v := by
    intro g hg
    have hgB : g⁻¹ ∈ Nor B := hNB g⁻¹ fun y₁ hy => by
      have := hg y₁ ⟨hSP ▸ K.hBP hy, K.toCtx.D.hB.1 hy⟩
      rw [hSP] at this; simpa using this
    obtain ⟨k, hk, p, hkp⟩ := K.toCtx.conj_b_form hgB
    rw [inv_inv] at hkp
    rw [hkp]
    rcases zmod3_cases k with rfl | rfl | rfl
    · exact absurd rfl hk
    · rw [pow_val_one, ← mul_assoc, inv_mul_cancel, one_mul]
      exact K.R_le_A (ψ_mem K.toCtx.E p)
    · exact absurd (by rw [inv_inv]; exact hkp) (hnoinv g⁻¹ hgB p)
  have hne := CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal S habel
    (hSP ▸ K.hBP K.toCtx.bB) K.b_not_A K.toCtx.b3 hfus
  apply hne
  rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨g, k, hgk⟩ := hna
    have hm := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k)
    rw [← commutator_def, h, Subgroup.mem_bot] at hm
    exact hgk (commutatorElement_eq_one_iff_mul_comm.mp hm)
  · exact h

end PCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
