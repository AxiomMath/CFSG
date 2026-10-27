module

public import CFSG.RankThree.GF2n.Stroth80.Sec11TorusPhi
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusComm
import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Field

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

namespace LBFrame

variable (fr : LBFrame Q Z B)

private theorem frame_m_ne_zero (hc : Ctx M Q Z B) : fr.m ≠ 0 := by
  intro h0
  have h4 : 4 ≤ Nat.card Z := hc.hyp.q4
  rw [fr.card, h0, pow_zero] at h4
  omega

theorem natCard_K_eq (hc : Ctx M Q Z B) : Nat.card fr.K = Nat.card Z := by
  rw [GaloisField.card (p := 2) (n := fr.m) (fr.frame_m_ne_zero hc), fr.card]

theorem exists_pow_lt_eq (hc : Ctx M Q Z B) {c : fr.Kˣ} (hc0 : orderOf c = Nat.card Z - 1)
    (u : fr.Kˣ) : ∃ k < Nat.card Z - 1, c ^ k = u := by
  classical
  have htop : Subgroup.zpowers c = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, hc0, Nat.card_units, fr.natCard_K_eq hc])
  have hu : u ∈ (Finset.range (orderOf c)).image (c ^ ·) :=
    mem_zpowers_iff_mem_range_orderOf.mp (htop ▸ Subgroup.mem_top u)
  obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp hu
  exact ⟨k, hc0 ▸ Finset.mem_range.mp hk, hku⟩

private theorem pow_diagElt {K : Type*} [Field K] (c : Kˣ) (n : ℕ) :
    Timmesfeld.ARS.NaturalModule.diagElt c ^ n = Timmesfeld.ARS.NaturalModule.diagElt (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Timmesfeld.ARS.NaturalModule.diagElt_one]
  | succ n ih => rw [pow_succ, ih, Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt, pow_succ]

private theorem eq_one_of_diagElt_eq_one {K : Type*} [Field K] {c : Kˣ}
    (h : Timmesfeld.ARS.NaturalModule.diagElt c = 1) : c = 1 := by
  apply Units.ext
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [Timmesfeld.ARS.NaturalModule.coe_diagElt] using this

private theorem orderOf_pow_two_pow_eq {x : G} {n f : ℕ} (hn : n ≠ 0) (hdvd : n ∣ orderOf x)
    (hf : orderOf (x ^ n) = 2 ^ f) : orderOf (x ^ 2 ^ f) = n := by
  have h1 := orderOf_pow_of_dvd hn hdvd
  rw [hf] at h1
  have hx : orderOf x = 2 ^ f * n := by
    have := (Nat.div_mul_cancel hdvd).symm
    rwa [← h1] at this
  rw [orderOf_pow_of_dvd (pow_ne_zero f two_ne_zero) ⟨n, hx⟩, hx,
    Nat.mul_div_cancel_left _ (by positivity)]

private theorem exists_unit_orderOf_card_sub_one (hc : Ctx M Q Z B) :
    ∃ c : fr.Kˣ, orderOf c = Nat.card Z - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := fr.Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, fr.natCard_K_eq hc]⟩

private theorem coprime_two_pow_card_sub_one (hc : Ctx M Q Z B) (f : ℕ) :
    Nat.Coprime (2 ^ f) (2 ^ fr.m - 1) :=
  Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.mpr ⟨even_two, fr.frame_m_ne_zero hc⟩) odd_one))

end LBFrame

end Field

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

namespace LBFrame

variable (fr : LBFrame Q Z B)

theorem lbVec_conj_lbTorusElt (hc : Ctx M Q Z B) {t : fr.K} (ht : t ≠ 0) {a : G}
    (ha : a ∈ QB B ⊓ M) :
    lbVec M Q B (fr.lbTorusElt t * a * (fr.lbTorusElt t)⁻¹) =
      fr.lbPhiHom hc t⁻¹ (lbVec M Q B a) := by
  have hw' := fr.conj_lbWeylL hc (one_ne_zero : (1 : fr.K) ≠ 0)
  have hw := fr.conj_lbWeylU hc ht
  have hp := hc.conj_PB_mem_P_of_swap hw'.1 hw'.2 ha
  have hn := hc.comm_Q_PB_mem (fr.lbRootU_mem 1) ha
  have h1 := hc.weylQB_conj_PB (fr.lbRootU_mem 1) (fr.lbRootL_mem 1) ha
  rw [show fr.lbRootL 1 * fr.lbRootU 1 * fr.lbRootL 1 = fr.lbWeylL 1 by
    rw [lbWeylL, inv_one]] at h1
  have h1' : (fr.lbWeylL 1 * a * (fr.lbWeylL 1)⁻¹)⁻¹ * ⁅fr.lbRootU 1, a⁆ ∈ QB B := by
    have := (QB B).inv_mem h1
    rwa [mul_inv_rev, inv_inv] at this
  have hA := hc.comm_QB_P_mem (fr.lbRootL_mem t⁻¹) hp
  have hAn := hc.comm_QB_P_mem (fr.lbRootL_mem t⁻¹) hn
  have hX := hc.conj_P_mem_PB_of_swap hw.1 hw.2 hp
  have hΦ := fr.lbPhi_mem hc t⁻¹ (fr.lbPhi_mem hc 1 ha)
  have e : fr.lbTorusElt t * a * (fr.lbTorusElt t)⁻¹ =
      fr.lbWeylU t * (fr.lbWeylL 1 * a * (fr.lbWeylL 1)⁻¹) * (fr.lbWeylU t)⁻¹ := by
    rw [lbTorusElt]
    group
  rw [e, ← (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hA) (mem_LB_of_mem_QB_inf hX)).mpr
      (hc.weylQ_conj_P (fr.lbRootU_mem t) (fr.lbRootL_mem t⁻¹) hp),
    (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hA) (mem_LB_of_mem_QB_inf hAn)).mpr
      (hc.comm_QB_P_congr_right (fr.lbRootL_mem t⁻¹) hp hn h1'),
    (lbVec_eq_iff hc (mem_LB_of_mem_QB_inf hAn) (mem_LB_of_mem_QB_inf hΦ)).mpr
      (fr.comm_lbRootL_lbPhi hc t⁻¹ hn),
    ← fr.lbPhiEnd_lbVec hc t⁻¹ (fr.lbPhi_mem hc 1 ha), ← fr.lbPhiEnd_lbVec hc 1 ha,
    ← fr.lbPhiHom_apply, ← fr.lbPhiHom_apply, fr.lbPhiHom_one_apply]

theorem lbVec_conj_pow (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {c : fr.K}
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a))
    (i : ℕ) {l : G} (hl : l ∈ LB M Q B) :
    lbVec M Q B (y ^ i * l * (y ^ i)⁻¹) = fr.lbPhiHom hc (c ^ i) (lbVec M Q B l) := by
  have hPi : ∀ (i : ℕ), ∀ a ∈ QB B ⊓ M,
      lbVec M Q B (y ^ i * a * (y ^ i)⁻¹) = fr.lbPhiHom hc (c ^ i) (lbVec M Q B a) := by
    intro i
    induction i with
    | zero =>
      intro a _
      simp only [pow_zero, one_mul, inv_one, mul_one, fr.lbPhiHom_one_apply]
    | succ i ih =>
      intro a ha
      have h1 := hc.conj_mem_PB_of_mem_normalizer (M.pow_mem hyM i)
        (Subgroup.pow_mem _ hyB i) ha
      have e : y ^ (i + 1) * a * (y ^ (i + 1))⁻¹ = y * (y ^ i * a * (y ^ i)⁻¹) * y⁻¹ := by
        rw [pow_succ']
        group
      rw [e, hact _ h1, ih a ha, pow_succ', fr.lbPhiHom_mul_apply]
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hqi : y ^ i * q * (y ^ i)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.pow_mem hyM i)) q).mp hq
  have hsi := hc.conj_mem_PB_of_mem_normalizer (M.pow_mem hyM i) (Subgroup.pow_mem _ hyB i) hs
  have hQ : ∀ {x : G}, x ∈ Q → x ∈ LB M Q B := fun hx => (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)) hx
  have e : y ^ i * (s * q) * (y ^ i)⁻¹ = (y ^ i * s * (y ^ i)⁻¹) * (y ^ i * q * (y ^ i)⁻¹) := by
    group
  rw [e, lbVec_mul hc (mem_LB_of_mem_QB_inf hsi) (hQ hqi), (lbVec_eq_zero_iff hc (hQ hqi)).mpr hqi,
    add_zero, hPi i s hs, lbVec_mul hc (mem_LB_of_mem_QB_inf hs) (hQ hq),
    (lbVec_eq_zero_iff hc (hQ hq)).mpr hq, add_zero]

private theorem exists_lbTorus_of (hc : Ctx M Q Z B) (x : ↥(Q ⊔ QB B)) {l : fr.Kˣ}
    (hl : orderOf l = Nat.card Z - 1) (hφx : fr.φ x = Timmesfeld.ARS.NaturalModule.diagElt l)
    (hact : ∀ a ∈ QB B ⊓ M, lbVec M Q B ((x : G) * a * (x : G)⁻¹) =
      fr.lbPhiHom hc (l : fr.K)⁻¹ (lbVec M Q B a)) :
    ∃ (y : G) (hy : y ∈ Q ⊔ QB B) (c : fr.Kˣ), orderOf c = Nat.card Z - 1 ∧
      orderOf y = Nat.card Z - 1 ∧
      fr.φ ⟨y, hy⟩ = Timmesfeld.ARS.NaturalModule.diagElt c⁻¹ ∧
      ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a) := by
  have hn0 : Nat.card Z - 1 ≠ 0 := by
    have := hc.hyp.q4
    omega
  have hφ : ∀ k : ℕ, fr.φ (x ^ k) = Timmesfeld.ARS.NaturalModule.diagElt (l ^ k) := fun k => by
    rw [map_pow, hφx, pow_diagElt]
  obtain ⟨f, hf⟩ := fr.exists_orderOf_of_phi_eq_one hc (x ^ (Nat.card Z - 1))
    (by rw [hφ, ← hl, pow_orderOf_eq_one, Timmesfeld.ARS.NaturalModule.diagElt_one])
  have hdvd : Nat.card Z - 1 ∣ orderOf (x : G) := by
    rw [← hl]
    refine orderOf_dvd_of_pow_eq_one (eq_one_of_diagElt_eq_one ?_)
    rw [← hφ, show x ^ orderOf (x : G) = 1 from Subtype.ext (by simp [pow_orderOf_eq_one]),
      map_one]
  obtain ⟨hZ0, hB0⟩ := fr.diag_normalizes hc x l hφx
  have hM0 : (x : G) ∈ M := hc.hyp.normalizer_Z.1 ▸ hZ0
  have hco : (orderOf l⁻¹).Coprime (2 ^ f) := by
    rw [orderOf_inv, hl, fr.card]
    exact (fr.coprime_two_pow_card_sub_one hc f).symm
  refine ⟨(x : G) ^ 2 ^ f, Subgroup.pow_mem _ x.2 _, l⁻¹ ^ 2 ^ f, ?_,
    orderOf_pow_two_pow_eq hn0 hdvd (by simpa using hf), ?_, fun a ha => ?_⟩
  · rw [Nat.Coprime.orderOf_pow hco, orderOf_inv, hl]
  · rw [show (⟨(x : G) ^ 2 ^ f, Subgroup.pow_mem _ x.2 _⟩ : ↥(Q ⊔ QB B)) = x ^ 2 ^ f from
      Subtype.ext (by simp), hφ, inv_pow, inv_inv]
  · rw [fr.lbVec_conj_pow hc hM0 hB0 hact (2 ^ f) (mem_LB_of_mem_QB_inf ha),
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]

theorem exists_lbTorus (hc : Ctx M Q Z B) :
    ∃ (y : G) (hy : y ∈ Q ⊔ QB B) (c : fr.Kˣ), orderOf c = Nat.card Z - 1 ∧
      orderOf y = Nat.card Z - 1 ∧
      fr.φ ⟨y, hy⟩ = Timmesfeld.ARS.NaturalModule.diagElt c⁻¹ ∧
      ∀ a ∈ QB B ⊓ M, lbVec M Q B (y * a * y⁻¹) = fr.lbPhiHom hc c (lbVec M Q B a) := by
  obtain ⟨l, hl⟩ := fr.exists_unit_orderOf_card_sub_one hc
  refine fr.exists_lbTorus_of hc ⟨fr.lbTorusElt l, fr.lbTorusElt_mem l⟩ hl ?_
    (fun a ha => fr.lbVec_conj_lbTorusElt hc l.ne_zero ha)
  rw [fr.phi_lbTorusElt l.ne_zero, Units.mk0_val]

end LBFrame

end CFSG.RankThree.GF2n.Stroth80
