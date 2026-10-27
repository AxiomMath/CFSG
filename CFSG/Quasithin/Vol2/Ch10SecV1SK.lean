module

public import CFSG.Quasithin.Vol2.Ch10SecV1SJ
public import CFSG.Quasithin.Vol2.Ch10SecV1M

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]
  {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {I : Subgroup H}

@[expose] noncomputable def diagSL (d : Fin 3 → K) (hd : d 0 * d 1 * d 2 = 1) :
    ↥(StatedSL 3 K) :=
  specialLinearGroupEquivStatedSL 3 K ⟨Matrix.diagonal d, by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    exact hd⟩

omit [Group H] in
theorem commute_of_comm_eq_one {Q : Type} [Group Q] {A B : Q} (h : A * B * A⁻¹ * B⁻¹ = 1) :
    Commute A B := by
  show A * B = B * A
  calc A * B = A * B * A⁻¹ * B⁻¹ * (B * A) := by group
    _ = B * A := by rw [h, one_mul]

namespace NatCoord

variable [Finite H]

theorem three_le_pRank (c : NatCoord φ I) (hLn : L.Normal) {ω : K} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {y : H} (hy : y ∈ Subgroup.normalizer (I : Set H)) (hy3 : y ^ 3 = 1)
    (hyL : y ∉ L)
    (hyd : ∀ d : Fin 3 → K, (∀ i, d i ^ 3 = 1) → ∀ x,
      c.cact y hy (Matrix.diagonal d *ᵥ x) = Matrix.diagonal d *ᵥ c.cact y hy x) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (O2 L).Normal := O2_normal hLn
  have hω6 : ω ^ 6 = 1 := by rw [show ω ^ 6 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  set d₁ : Fin 3 → K := ![ω, ω ^ 2, 1] with hd₁
  set d₂ : Fin 3 → K := ![1, ω, ω ^ 2] with hd₂
  have hc₁ : ∀ i, d₁ i ^ 3 = 1 := fun i => by
    fin_cases i <;> simp [hd₁, hω3, ← pow_mul, hω6]
  have hc₂ : ∀ i, d₂ i ^ 3 = 1 := fun i => by
    fin_cases i <;> simp [hd₂, hω3, ← pow_mul, hω6]
  obtain ⟨l₁, hl₁⟩ := exists_mat φ (diagSL d₁ (by
    show ω * ω ^ 2 * 1 = 1
    rw [mul_one, ← pow_succ', hω3]))
  obtain ⟨l₂, hl₂⟩ := exists_mat φ (diagSL d₂ (by
    show 1 * ω * ω ^ 2 = 1
    rw [one_mul, ← pow_succ', hω3]))
  have hm₁ : mat φ l₁ = Matrix.diagonal d₁ := hl₁
  have hm₂ : mat φ l₂ = Matrix.diagonal d₂ := hl₂
  have hmk : ∀ a b : ↥L, (QuotientGroup.mk (a : H) : H ⧸ O2 L) = QuotientGroup.mk (b : H) →
      mat φ a = mat φ b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have h1 := (mat_eq_one_iff φ (a⁻¹ * b)).mpr (by simpa using hab)
    have := mat_mul φ a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h1, mul_one] at this
    exact this.symm
  have hcube : ∀ (l : ↥L), mat φ l ^ 3 = 1 → (QuotientGroup.mk (l : H) : H ⧸ O2 L) ^ 3 = 1 := by
    intro l hl
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← Subgroup.coe_pow]
    exact (mat_eq_one_iff φ (l ^ 3)).mp (by rw [mat_pow, hl])
  have hdiag3 : ∀ d : Fin 3 → K, (∀ i, d i ^ 3 = 1) → Matrix.diagonal d ^ 3 = 1 := by
    intro d hd
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd i
  have hcomm : ∀ (g : H) (l : ↥L), g * l * g⁻¹ * (l : H)⁻¹ ∈ O2 L →
      Commute (QuotientGroup.mk g : H ⧸ O2 L) (QuotientGroup.mk (l : H)) := by
    intro g l hgl
    refine commute_of_comm_eq_one ?_
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hgl
  have hdcomm : ∀ (l : ↥L) (d : Fin 3 → K), mat φ l = Matrix.diagonal d → (∀ i, d i ^ 3 = 1) →
      ∀ x, c.cact y hy (mat φ l *ᵥ x) = mat φ l *ᵥ c.cact y hy x := fun l d hl hd x => by
    rw [hl]
    exact hyd d hd x
  have h12 : ∀ x, c.cact l₁ (c.le_normalizer l₁.2) (mat φ l₂ *ᵥ x) =
      mat φ l₂ *ᵥ c.cact l₁ (c.le_normalizer l₁.2) x := fun x => by
    rw [c.cact_of_mem, c.cact_of_mem, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm₁, hm₂,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  refine (three_le_pRank_of_gens (p := 3) (x := (QuotientGroup.mk (l₁ : H) : H ⧸ O2 L))
    (z := QuotientGroup.mk (l₂ : H)) (c := QuotientGroup.mk y)
    (hcube l₁ (by rw [hm₁]; exact hdiag3 d₁ hc₁)) (hcube l₂ (by rw [hm₂]; exact hdiag3 d₂ hc₂))
    (by rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one])
    (hcomm _ l₂ (c.comm_mem_O2 hLn _ l₂ h12))
    (hcomm _ l₁ (c.comm_mem_O2 hLn hy l₁ (hdcomm l₁ d₁ hm₁ hc₁))).symm
    (hcomm _ l₂ (c.comm_mem_O2 hLn hy l₂ (hdcomm l₂ d₂ hm₂ hc₂))).symm ?_ ?_ ?_).trans_eq
    (pRank_quotient_eq (O2 L) ?_)
  ·
    intro h1
    have h2 := hmk l₁ 1 (by rw [h1, Subgroup.coe_one, QuotientGroup.mk_one])
    rw [hm₁, mat_one] at h2
    have := congrFun (congrFun h2 0) 0
    simp [hd₁] at this
    exact hω1 this
  ·
    intro m hm
    have h2 := hmk (l₁ ^ m) l₂ (by rw [Subgroup.coe_pow, QuotientGroup.mk_pow, hm])
    rw [mat_pow, hm₁, hm₂, Matrix.diagonal_pow] at h2
    have e0 := congrFun (congrFun h2 0) 0
    have e1 := congrFun (congrFun h2 1) 1
    simp [hd₁, hd₂] at e0 e1
    rw [← pow_mul, mul_comm, pow_mul, e0, one_pow] at e1
    exact hω1 e1.symm
  ·
    intro a b hab
    apply hyL
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at hab
    have h1 : ((l₁ : H) ^ a * (l₂ : H) ^ b) ∈ L :=
      L.mul_mem (L.pow_mem l₁.2 a) (L.pow_mem l₂.2 b)
    have h2 := O2_le hab
    have e : y = ((l₁ : H) ^ a * (l₂ : H) ^ b) * (((l₁ : H) ^ a * (l₂ : H) ^ b)⁻¹ * y) := by group
    rw [e]
    exact L.mul_mem h1 h2
  ·
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [O2, Subgroup.card_map_of_injective L.subtype_injective, hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

end NatCoord

end CFSG.Quasithin.Vol2.Ch10.V1C.A319

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Assembly.LowTwoRank V1C.A319

theorem a319CoreFact_holds : A319CoreFact := by
  intro H _ _ hH L V _ hLn _ hVn hV hHyp _ h ⟨k, hk⟩ hh3
  classical
  by_contra hhL
  obtain ⟨n, s, K, _, _, φ, hn, hKn, hs1, hs2, hnat⟩ := hHyp
  have h2n : 2 ^ n % 3 = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hq3 : ¬ 3 ∣ Nat.card K + 1 := by
    rw [hKn]
    omega
  obtain ⟨I, ⟨c⟩, hhI⟩ :=
    exists_natCoord_inv hV hVn hs1 hs2 hnat hq3 hk (mem_normalizer_of_normal hLn h)
  obtain ⟨y, hy, hy3, hyL, hyd⟩ := c.exists_y hLn hhI hh3 hhL
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card (G := Kˣ) 3 (by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hKn]
    omega)
  have hω3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (ω : K) ≠ 1 := fun h1 => by
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    omega
  have h3 := c.three_le_pRank hLn hω3 hω1 hy hy3 hyL hyd
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 := hH.1 3 Nat.prime_three (by norm_num)
  omega

theorem a319Facts_holds : A319Facts := ⟨a319SL3Facts_holds, a319CoreFact_holds⟩

end CFSG.Quasithin.Vol2.Ch10
