module

public import CFSG.RankThree.GF2n.Smith81.TiD3Weights
public import CFSG.RankThree.GF2n.Smith81.TiRootLines
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaJ
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {H : Subgroup G} {m : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (h1 : m ^ a ∈ H) (h2 : m ^ b ∈ H) : m ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  have : m = (m ^ a) ^ u * (m ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm _ u,
      mul_comm _ v, huv, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem h1 u) (H.zpow_mem h2 v)

theorem exists_centralized_ne_one {G : Type*} [Group G] [Finite G] {T D : Subgroup G}
    (hT2 : IsPGroup 2 T) (hD2 : IsPGroup 2 D) (hDne : D ≠ ⊥)
    (hTD : ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D) :
    ∃ b ∈ D, b ≠ 1 ∧ ∀ t ∈ T, t * b * t⁻¹ = b := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥T ↥D :=
    { smul := fun t d => ⟨(t : G) * d * (t : G)⁻¹, hTD t t.2 d d.2⟩
      one_smul := fun d => Subtype.ext (by
        show (((1 : ↥T) : G)) * (d : G) * (((1 : ↥T) : G))⁻¹ = d
        simp)
      mul_smul := fun a b d => Subtype.ext (by
        show (((a * b : ↥T) : G)) * (d : G) * (((a * b : ↥T) : G))⁻¹ =
          (a : G) * ((b : G) * (d : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hdvd : 2 ∣ Nat.card ↥D := by
    rcases hD2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hDne
    · exact h
  have h1 : (⟨1, D.one_mem⟩ : ↥D) ∈ MulAction.fixedPoints ↥T ↥D := by
    rw [MulAction.mem_fixedPoints]
    intro t
    exact Subtype.ext (by
      show (t : G) * 1 * (t : G)⁻¹ = 1
      simp)
  obtain ⟨b, hb, hb1⟩ := hT2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥D hdvd h1
  rw [MulAction.mem_fixedPoints] at hb
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun t ht => ?_⟩
  exact congrArg Subtype.val (hb ⟨t, ht⟩)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3Ctx

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}
  {F : Type} [Field F] [Finite F] [Algebra K F]

theorem D3Data.exists_ctx_line (D : D3Data Q Z M₀ φS F) (hc : Ctx M Q Z B) (hSM : S ≤ M)
    (hφπ : ∀ (m : ↥S) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    {w₁ : Fin 2 → F} (hw₁ : w₁ ≠ 0)
    (hB : ∀ v, v ∈ M₀.img B ↔ ∃ μ : K, v = μ • D.ptv w₁)
    {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ A : Subgroup G, Ctx M Q Z A ∧ ∀ v, v ∈ M₀.img A ↔ ∃ μ : K, v = μ • D.ptv w := by
  obtain ⟨g, hg⟩ := D2.exists_sl_mulVec_eq hw₁ hw
  obtain ⟨m, hm⟩ := D.surj g
  have hmM : (m : G) ∈ M := hSM m.2
  have hkey : ∀ μ : K, φS m (μ • D.ptv w₁) = μ • D.ptv w := by
    intro μ
    rw [map_smul, D.φS_ptv, hm, hg]
  refine ⟨conjSubgroup m B, hc.conj_of_mem hmM, fun v => ?_⟩
  constructor
  · rintro ⟨x, hxA, hxQ, rfl⟩
    have hy : (m : G)⁻¹ * x * (m : G) ∈ B := mem_conjSubgroup.mp hxA
    have hyQ : (m : G)⁻¹ * x * (m : G) ∈ Q := hc.le hy
    have hπ := hφπ m _ hyQ
    rw [show (m : G) * ((m : G)⁻¹ * x * (m : G)) * (m : G)⁻¹ = x by group] at hπ
    obtain ⟨μ, hμ⟩ := (hB _).mp (M₀.pi_mem_img hy hyQ)
    exact ⟨μ, by rw [hπ, hμ, hkey]⟩
  · rintro ⟨μ, rfl⟩
    obtain ⟨y, hyB, hyQ, hyπ⟩ := (hB (μ • D.ptv w₁)).mpr ⟨μ, rfl⟩
    refine ⟨(m : G) * y * (m : G)⁻¹, ?_, conj_mem_Q hc.hyp hmM hyQ, ?_⟩
    · rw [mem_conjSubgroup, show (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹) * (m : G) = y by group]
      exact hyB
    · rw [hφπ m y hyQ, hyπ, hkey]

structure D3Ctx (M Q Z B : Subgroup G) (M₀ : Tim79.QuadModel Q Z K γ) (F : Type) [Field F]
    [Finite F] [Algebra K F] where
  hc : Ctx M Q Z B
  hw : Width Q Z 4
  hD : GlobalModelData M Q Z γ M₀
  φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  hφker : ∀ m : ↥(H0 M Z), φ m = 1 ↔ (m : G) ∈ Q
  hφQ : ∀ (m : ↥(H0 M Z)) e, M₀.Qf (φ m e) = M₀.Qf e
  hcent : CentTrivial M Q Z (Lgen M (LB M Q B))
  D : D3Data Q Z M₀ (φ.comp (Subgroup.inclusion hc.Lgen_le_H0)) F

namespace D3Ctx

variable [CharP F 2] (R : D3Ctx M Q Z B M₀ F)

theorem hφSπ (m : ↥(Lgen M (LB M Q B))) (x : G) (hx : x ∈ Q) :
    M₀.π ((m : G) * x * (m : G)⁻¹) =
      (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) m (M₀.π x) :=
  R.hφπ ⟨m, R.hc.Lgen_le_H0 m.2⟩ x hx

theorem hBinv (m : ↥(Lgen M (LB M Q B))) (e f : M₀.E) :
    M₀.B ((R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) m e)
      ((R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) m f) = M₀.B e f := by
  show M₀.B (R.φ ⟨m, R.hc.Lgen_le_H0 m.2⟩ e) (R.φ ⟨m, R.hc.Lgen_le_H0 m.2⟩ f) = M₀.B e f
  have h1 := M₀.Qf_add (R.φ ⟨m, R.hc.Lgen_le_H0 m.2⟩ e) (R.φ ⟨m, R.hc.Lgen_le_H0 m.2⟩ f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, R.hφQ, R.hφQ, R.hφQ] at h1
  linear_combination h2 - h1

include R in
theorem hK4 : 4 ≤ Nat.card K := by
  rw [R.hD.card]
  exact R.hc.hyp.q4

include R in
theorem mem_S_of_two_power {m : G} (hm : m ∈ H0 M Z) {k : ℕ} (hk : m ^ (2 ^ k) ∈ Q) :
    m ∈ Lgen M (LB M Q B) := by
  have h3 : m ^ 3 ∈ Lgen M (LB M Q B) :=
    R.D.cube_mem R.hK4 R.hc.Lgen_le_H0 R.hc.Q_le_Lgen
      (fun m hm s hs => R.hc.mem_Lgen_conj hm.1 hs)
      (fun m hm x hx => conj_mem_Q R.hc.hyp hm.1 hx) R.hcent R.φ (fun m => rfl) hm
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
    h3 (R.hc.Q_le_Lgen hk)

include R in
theorem line_of_root {A : Subgroup G} (hA : Ctx M Q Z A) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧
      ∀ v, v ∈ M₀.img A ↔ ∃ μ : K, v = μ • R.D.ptv w := by
  have hLS : LB M Q A ≤ Lgen M (LB M Q B) := fun t ht =>
    R.mem_S_of_two_power (hA.LB_le_H0 ht) (k := 1) (by simpa using hA.sq_mem_Q_of_mem_LB ht)
  have hT2 : ∀ t ∈ LB M Q A, ∃ k : ℕ, t ^ (2 ^ k) ∈ Q := fun t ht =>
    ⟨1, by simpa using hA.sq_mem_Q_of_mem_LB ht⟩
  have hQT : Q ≤ LB M Q A := le_sup_left
  have hcard : Nat.card F * Nat.card ↥(LB M Q A ⊓ Q) ≤ Nat.card (LB M Q A) := by
    rw [inf_eq_right.mpr hQT, R.D.card_F, R.hD.card]
    have := hA.card_LB_ge R.hw (by norm_num : 1 ≤ 4)
    calc Nat.card Z ^ 3 * Nat.card Q = Nat.card Q * Nat.card Z ^ (4 - 1) := by ring
      _ ≤ Nat.card (LB M Q A) := this
  obtain ⟨w, hw0, hw⟩ := R.D.fixed_in_line_of_card hLS hT2 hcard
  obtain ⟨b, hb0, hbs, hb, -, -⟩ := hA.dictB R.hD
  obtain ⟨a₀, ha₀A, ha₀Q, ha₀⟩ := (hb b).mpr ⟨1, (one_smul K b).symm⟩
  have hfix : ∀ (t : G) (ht : t ∈ LB M Q A),
      (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) ⟨t, hLS ht⟩ b = b := by
    intro t ht
    rw [← ha₀, ← R.hφSπ ⟨t, hLS ht⟩ a₀ ha₀Q]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) ha₀Q
      (conj_mem_Q R.hc.hyp (hA.LB_le_M ht) ha₀Q)).mp (hA.comm_B_mem_Z ht ha₀A)
  obtain ⟨μ, hμ⟩ := hw b hfix
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hμ, zero_smul])
  refine ⟨w, hw0, fun v => ?_⟩
  constructor
  · intro hv
    obtain ⟨s, hs⟩ := (hb v).mp hv
    exact ⟨s * μ, by rw [hs, hμ, smul_smul]⟩
  · rintro ⟨ν, hν⟩
    refine (hb v).mpr ⟨ν * μ⁻¹, ?_⟩
    rw [hν, hμ, smul_smul, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]

include R in
theorem omega : OmegaProp M Q Z := by
  refine omega_of_lines R.hc.hyp R.hD {v | ∃ w : Fin 2 → F, w ≠ 0 ∧ v = R.D.ptv w} ?_ ?_
  · rintro v ⟨w, hw0, rfl⟩ v' ⟨w', hw0', rfl⟩ hB
    obtain ⟨κ, hκ⟩ := R.D.exists_smul_of_B_eq_zero hw0 hB
    exact ⟨κ, hκ⟩
  · intro A hA
    obtain ⟨w, hw0, hl⟩ := R.line_of_root hA
    refine ⟨R.D.ptv w, ⟨w, hw0, rfl⟩, R.D.ptv_ne_zero hw0, fun a ha => ?_⟩
    exact (hl _).mp (M₀.pi_mem_img ha (hA.le ha))

end D3Ctx

end D3Ctx

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3Fusion

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}
  {F : Type} [Field F] [Finite F] [Algebra K F]

namespace D3Ctx

variable [CharP F 2] (R : D3Ctx M Q Z B M₀ F)

include R in
theorem not_typeA {x : G} (hxH : x ∈ H0 M Z) (hxQ : x ∉ Q) (hx2 : x * x = 1) :
    ¬ ∃ k, IsTypeA Q Z k x := by
  rintro ⟨k, -, -, hall⟩
  have hxS : x ∈ Lgen M (LB M Q B) :=
    R.mem_S_of_two_power hxH (k := 1) (by simpa [pow_two, hx2] using Q.one_mem)
  set t : ↥(Lgen M (LB M Q B)) := ⟨x, hxS⟩ with ht
  have ht1 : R.D.p t ≠ 1 := fun h => hxQ ((R.D.ker_iff t).mp h)
  have ht2 : R.D.p t * R.D.p t = 1 := by
    rw [← map_mul]
    refine (R.D.ker_iff _).mpr ?_
    show x * x ∈ Q
    rw [hx2]
    exact Q.one_mem
  obtain ⟨v, hv⟩ := R.D.exists_B_ne_zero ht1 ht2 (R.hBinv)
  obtain ⟨q, hqQ, rfl⟩ := M₀.π_surj v
  have hqq := conj_mem_Q R.hc.hyp hxH.1 hqQ
  have h1 : ⁅q, x * q * x⁻¹⁆ = 1 := hall q hqQ
  have h2 := (GM.comm_eq_one_iff R.hD hqQ hqq).mp h1
  rw [show x * q * x⁻¹ = (t : G) * q * (t : G)⁻¹ from rfl, R.hφSπ t q hqQ] at h2
  exact hv h2

include R in
theorem p2 : P2Prop M Q Z := by
  refine p2_of_conj R.hc.hyp fun X x hs => ?_
  have h12 := smith_1_12 hs
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hq4 : 4 ≤ Nat.card Z := R.hc.hyp.q4
  have hKZ : Nat.card K = Nat.card Z := R.hD.card
  have hFZ : Nat.card F = Nat.card Z ^ 3 := by rw [R.D.card_F, hKZ]
  have hQ2 : IsPGroup 2 Q := by
    rw [R.hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hQB2 : IsPGroup 2 (QB X) := by
    rw [hQB]
    exact hQ2.map (MulAut.conj g).toMonoidHom
  have hLxH : Lx M X ≤ H0 M Z := Lx_le_H0 hs h12
  have hLxQB : Lx M X ≤ QB X := inf_le_left
  have hLx2 : IsPGroup 2 ↥(Lx M X) := hQB2.to_le hLxQB
  have hLxpow : ∀ t ∈ Lx M X, ∃ k : ℕ, t ^ (2 ^ k) ∈ Q := by
    intro t ht
    obtain ⟨k, hk⟩ := hLx2 ⟨t, ht⟩
    refine ⟨k, ?_⟩
    have : t ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]
    exact Q.one_mem
  have hLxS : Lx M X ≤ Lgen M (LB M Q B) := fun t ht => by
    obtain ⟨k, hk⟩ := hLxpow t ht
    exact R.mem_S_of_two_power (hLxH ht) hk
  have hLxQ : Lx M X ⊓ Q ≤ Q ⊓ QB X := fun y hy => by
    have h1 : y ∈ QB X ⊓ M := (Subgroup.mem_inf.mp hy).1
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2, (Subgroup.mem_inf.mp h1).1⟩
  have hLxQcard : Nat.card ↥(Lx M X ⊓ Q) ≤ Nat.card ↥(Q ⊓ QB X) :=
    Subgroup.card_le_of_le hLxQ
  have hLxcard1 : Nat.card ↥(Lx M X) ≤ Nat.card ↥(Lx M X ⊓ Q) * Nat.card F :=
    R.D.card_le_mul hLxS hLx2
  have hLx4 : Nat.card Z ^ 4 ≤ Nat.card ↥(Lx M X) := hs.card_Lx_ge R.hw
  have hqpos : 0 < Nat.card Z ^ 3 := pow_pos (by omega) 3
  have hge : Nat.card Z ≤ Nat.card ↥(Q ⊓ QB X) := by
    have h1 : Nat.card Z * Nat.card Z ^ 3 ≤ Nat.card ↥(Q ⊓ QB X) * Nat.card Z ^ 3 := by
      calc Nat.card Z * Nat.card Z ^ 3 = Nat.card Z ^ 4 := by ring
        _ ≤ Nat.card ↥(Lx M X) := hLx4
        _ ≤ Nat.card ↥(Lx M X ⊓ Q) * Nat.card F := hLxcard1
        _ ≤ Nat.card ↥(Q ⊓ QB X) * Nat.card Z ^ 3 := by
          rw [hFZ]
          exact Nat.mul_le_mul_right _ hLxQcard
    exact Nat.le_of_mul_le_mul_right h1 hqpos
  rcases le_or_gt (Nat.card ↥(Q ⊓ QB X)) (Nat.card Z) with hle | hgt
  ·
    have hcard : Nat.card F * Nat.card ↥(Lx M X ⊓ Q) ≤ Nat.card ↥(Lx M X) := by
      calc Nat.card F * Nat.card ↥(Lx M X ⊓ Q) ≤ Nat.card Z ^ 3 * Nat.card Z := by
            rw [hFZ]
            exact Nat.mul_le_mul_left _ (hLxQcard.trans hle)
        _ = Nat.card Z ^ 4 := by ring
        _ ≤ Nat.card ↥(Lx M X) := hLx4
    obtain ⟨w, hw0, hwfix⟩ := R.D.fixed_in_line_of_card hLxS hLxpow hcard
    have hDne : Q ⊓ QB X ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥(Q ⊓ QB X) = 1 := by
        rw [hbot]
        exact Subgroup.card_bot
      omega
    have hDQB2 : IsPGroup 2 ↥(Q ⊓ QB X) := hQ2.to_inf_left
    have hTD : ∀ t ∈ Lx M X, ∀ d ∈ Q ⊓ QB X, t * d * t⁻¹ ∈ Q ⊓ QB X := by
      intro t ht d hd
      have ht' : t ∈ QB X ⊓ M := ht
      refine ⟨conj_mem_Q R.hc.hyp (Subgroup.mem_inf.mp ht').2 hd.1, ?_⟩
      exact (QB X).mul_mem ((QB X).mul_mem (Subgroup.mem_inf.mp ht').1 hd.2)
        ((QB X).inv_mem (Subgroup.mem_inf.mp ht').1)
    obtain ⟨b, hbD, hb1, hbfix⟩ := exists_centralized_ne_one hLx2 hDQB2 hDne hTD
    have hbQ : b ∈ Q := hbD.1
    have hfixb : ∀ (t : G) (ht : t ∈ Lx M X),
        (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) ⟨t, hLxS ht⟩ (M₀.π b) = M₀.π b := by
      intro t ht
      rw [← R.hφSπ ⟨t, hLxS ht⟩ b hbQ, hbfix t ht]
    obtain ⟨μ, hμ⟩ := hwfix _ hfixb
    obtain ⟨w₁, hw₁0, hB⟩ := R.line_of_root R.hc
    obtain ⟨A', hA', hl⟩ := R.D.exists_ctx_line R.hc R.hc.Lgen_le_M
      (fun m x hx => R.hφSπ m x hx) hw₁0 hB hw0
    have hπ : M₀.π b ∈ M₀.img A' := (hl _).mpr ⟨μ, hμ⟩
    have hbA : b ∈ A' ⊔ Z := (M₀.mem_img_iff (le_sup_right : Z ≤ A' ⊔ Z) hbQ).mp
      (M₀.img_mono le_sup_left hπ)
    rw [sup_comm] at hbA
    obtain ⟨h, hh⟩ := hA'.exists_conj_mem_Z hbA hb1
    exact ⟨b, hbD, hb1, h, h⁻¹ * b * h, hh, by group⟩
  ·
    have hJ := hs.card_inf_le_Jx
    have hJne : Jx Q X x ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot, mul_one] at hJ
      omega
    obtain ⟨⟨b, hbJ⟩, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJne
    have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
    have hbJ' : b ∈ ⁅Q, Subgroup.zpowers x⁆ ⊓ QB X := hbJ
    have hxM := hs.memM
    have hxQ := hs.notQ
    have hx2 := hs.x_sq
    have hxZ := hs.x_cent h12
    have hxH : x ∈ H0 M Z := h12.1 hs.mem
    have hna := R.not_typeA hxH hxQ hx2
    have hfuse := smith_1_11_not_typeA R.hc.hyp hxM hxQ hxZ hx2 hna
    obtain ⟨g₁, z, hz, hbg⟩ := smith_1_16 hs hbJ hb1
    have hxz : x * z ∈ conjOrbit Q x ∩ cosetSet x Z := by
      rw [hfuse]
      exact ⟨z, hz, rfl⟩
    obtain ⟨s, hsQ, hsx⟩ := hxz.1
    obtain ⟨g₀, hg₀⟩ := hs.conj
    have hxg : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (by rw [← hg₀]; exact hs.mem)
    have hBQ : ⁅Q, Subgroup.zpowers x⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro q hq t ht
      have htM : t ∈ M := (Subgroup.zpowers_le.mpr hxM) ht
      have h1 := conj_mem_Q R.hc.hyp htM (Q.inv_mem hq)
      rw [show ⁅q, t⁆ = q * (t * q⁻¹ * t⁻¹) by simp only [commutatorElement_def]; group]
      exact Q.mul_mem hq h1
    refine ⟨b, ⟨hBQ hbJ'.1, hbJ'.2⟩, hb1, g₁ * s * g₀, g₀⁻¹ * x * g₀, hxg, ?_⟩
    rw [hbg, hsx]
    group

end D3Ctx

end D3Fusion

theorem tiFusionD3_of_module (hMod : D3ModuleStatement) : TiFusionD3Statement := by
  intro G _ _ M Q Z B H hB hBQ hBZ hc
  have hC : Ctx M Q Z B := ⟨H, hB, hBQ, hBZ⟩
  have hw : Width Q Z 4 := by
    have := hc.1
    unfold Width
    simpa using this
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 H hD
  obtain ⟨F, _, _, _, hcardF, hfinrank, ⟨D⟩⟩ := exists_d3Data hMod hC hw hc.2.1 hD
    (φ.comp (Subgroup.inclusion hC.Lgen_le_H0))
    (fun m x hx => hφπ ⟨m, hC.Lgen_le_H0 m.2⟩ x hx)
    (fun m => hφker ⟨m, hC.Lgen_le_H0 m.2⟩)
    (fun m e => hφQ ⟨m, hC.Lgen_le_H0 m.2⟩ e)
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  let R : D3Ctx M Q Z B M₀ F := ⟨hC, hw, hD, φ, hφπ, hφker, hφQ, hc.2.2, D⟩
  exact tiFusion_of_omega_p2 H R.omega R.p2

end

end CFSG.RankThree.GF2n.Smith81
