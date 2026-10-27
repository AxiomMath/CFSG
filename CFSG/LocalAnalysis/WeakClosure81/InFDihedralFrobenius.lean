module

public import CFSG.LocalAnalysis.WeakClosure81.InFSqWreathThree
public import CFSG.GroupTheory.FixedPointFreeCommutator
public import CFSG.GroupTheory.Commutator.JoinNormalizer
import CFSG.GroupTheory.TwoReflections
import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InF InFFor)
open scoped commutatorElement Pointwise

variable {Q : Type} [Group Q] [Finite Q]

private theorem mul_eGenP_zpowers_eq_top {r p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup Q} (hRnorm : R.Normal)
    (hRabel : IsMulCommutative R) (hRr : IsPGroup r R) {b t : Q}
    (hb : orderOf b = p) (ht : orderOf t = 2)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t) ⊤)
    (htb : t * b * t⁻¹ = b⁻¹) (hcomm : ⁅R, Subgroup.zpowers b⁆ = R)
    (hgen : R ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers t = ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : CFSG.Quasithin.E1.IsInvColl ⊤ Ω)
    (hΩne : Ω.Nonempty) (hΩnt : ∀ A ∈ Ω, A ≠ ⊥) :
    ((eGenP 1 (⊤ : Subgroup Q) (Subgroup.zpowers t) Ω : Subgroup Q) : Set Q) *
      (Subgroup.zpowers t : Set Q) = (⊤ : Subgroup Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : R.Normal := hRnorm
  let T : Subgroup Q := Subgroup.zpowers t
  change ((eGenP 1 (⊤ : Subgroup Q) T Ω : Subgroup Q) : Set Q) * (T : Set Q) =
    (⊤ : Subgroup Q)
  have hTin : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl
  have ht2 : t * t = 1 := by
    have h : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    simpa [pow_two] using h
  have hbpow : b ^ p = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hbp : ⁅Subgroup.zpowers b, T⁆ = Subgroup.zpowers b := by
    have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers b : Set Q) :=
      CFSG.GroupTheory.mem_normalizer_zpowers_of_inv htb
    refine CFSG.commutator_zpowers_eq_of_fixedPointFree (Subgroup.zpowers b) t ?_ htN ?_
    · intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self b m n).eq
    · intro x hx hfix
      have hinv : t * x * t⁻¹ = x⁻¹ := CFSG.GroupTheory.inverted_zpowers_of_inv htb x hx
      rw [hfix] at hinv
      have hx2 : x ^ 2 = 1 := by
        have h := congrArg (fun z => x * z) hinv
        rw [mul_inv_cancel] at h
        simpa [pow_two] using h
      have hxp : x ^ p = 1 := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbpow, one_zpow]
      exact CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
        (orderOf_dvd_iff_pow_eq_one.mpr hx2) (orderOf_dvd_iff_pow_eq_one.mpr hxp)
  have hTcard : Nat.card T = 2 := by
    dsimp [T]; rw [Nat.card_zpowers, ht]
  have hTel : IsElemAbelian 2 T := by
    dsimp [T]
    refine CFSG.Open.isElemAbelian_zpowers (p := 2) ?_
    simpa [pow_two] using ht2
  have hτ : CFSG.Quasithin.E1.tauOf (⊤ : Subgroup Q) T T = T := by
    refine le_antisymm (CFSG.Quasithin.E1.tauOf_le _ _ _) ?_
    intro x hx
    rw [CFSG.Quasithin.E1.mem_tauOf]
    refine ⟨hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup Q)
      (Subgroup.mem_top x), fun a ha => ?_⟩
    have hcomm_xa : x * a = a * x := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_zpow_self t m n).eq
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm_xa]
    exact (CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q)).one_mem
  have hidx : ∀ P : Subgroup Q,
      (T ⊓ Subgroup.centralizer (P : Set Q)).relIndex T ≤ 2 := by
    intro P
    have h := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (P : Set Q)) T
    rw [inf_eq_left.mpr inf_le_left] at h
    calc (T ⊓ Subgroup.centralizer (P : Set Q)).relIndex T
        ≤ (T ⊓ Subgroup.centralizer (P : Set Q)).relIndex T *
            Nat.card ↥(T ⊓ Subgroup.centralizer (P : Set Q)) :=
          Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card ↥T := h
      _ = 2 := hTcard
  have hTmem : T ∈ Ω := by
    obtain ⟨A, hAΩ⟩ := hΩne
    have hAel : IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
    have hA2 : IsPGroup 2 ↥A := hAel.isPGroup
    have hAcard_ne1 : Nat.card ↥A ≠ 1 := by
      intro h
      exact hΩnt A hAΩ (Subgroup.card_eq_one.mp h)
    have hA2dvd : 2 ∣ Nat.card ↥A := by
      rcases hA2.card_eq_or_dvd with h1 | h2
      · exact absurd h1 hAcard_ne1
      · exact h2
    have hAge2 : 2 ≤ Nat.card ↥A := Nat.le_of_dvd Nat.card_pos hA2dvd
    obtain ⟨g, -, hAle⟩ :=
      CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hTin le_top hA2
    have hconjcard : Nat.card ↥(CFSG.Quasithin.conjSubgroup T g) = 2 := by
      rw [CFSG.Quasithin.E3.card_conjSubgroup, hTcard]
    have hAcard : Nat.card ↥A = 2 := by
      refine le_antisymm ?_ hAge2
      rw [← hconjcard]
      exact Subgroup.card_le_of_le hAle
    have hAeq : A = CFSG.Quasithin.conjSubgroup T g :=
      Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, hconjcard])
    have hTeq : T = CFSG.Quasithin.conjSubgroup A g⁻¹ := by
      rw [hAeq, CFSG.Quasithin.E3.conjSubgroup_conj_inv]
    rw [hTeq]
    have hconj : CFSG.Quasithin.conjSubgroup A g⁻¹ = CFSG.Quasithin.A1b.conjSub g A := by
      ext z
      simp [CFSG.Quasithin.conjSubgroup, CFSG.Quasithin.A1b.conjSub]
    rw [hconj]
    exact hΩ.conj A hAΩ g (Subgroup.mem_top _)
  let E : Subgroup Q := eGenP 1 (⊤ : Subgroup Q) T Ω
  have hP1 : IsPGroup p ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hP1ne : Subgroup.zpowers b ≠ ⊥ := by
    intro hz
    have hb1 : b = 1 := Subgroup.zpowers_eq_bot.mp hz
    rw [hb1, orderOf_one] at hb
    exact hp.ne_one hb.symm
  have hK1 : IsEP 1 ⊤ T T (Subgroup.zpowers b ⊔ T) := by
    have hτP : CFSG.Quasithin.E1.tauOf (⊤ : Subgroup Q) T T ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set Q) := by
      rw [hτ]
      exact Subgroup.zpowers_le.mpr (CFSG.GroupTheory.mem_normalizer_zpowers_of_inv htb)
    have h := isEP_one_of_pSubgroup (T := T) (A := T) (P := Subgroup.zpowers b)
      (p := p) hp hp2 hTin le_rfl hTel hP1 hP1ne hτP hbp (hidx _)
    simpa [hτ] using h
  have hK1le : Subgroup.zpowers b ⊔ T ≤ E := by
    dsimp [E]
    refine le_iSup₂_of_le T hTmem (le_iSup_of_le le_rfl (le_iSup₂_of_le
      (Subgroup.zpowers b ⊔ T) hK1 le_rfl))
  have hbE : b ∈ E :=
    hK1le (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have htE : t ∈ E :=
    hK1le (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  let P : Subgroup Q := ⁅R, T⁆
  have hPR : P ≤ R := Subgroup.commutator_le_left R T
  have hPleE : P ≤ E := by
    by_cases hPbot : P = ⊥
    · rw [hPbot]; exact bot_le
    · have hPinv : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := by
        refine conj_eq_inv_of_mem_commutator_zpowers (Xb := R) ht2 ?_
        intro a ha b' hb'
        exact congrArg Subtype.val (mul_comm' (⟨a, hPR ha⟩ : R) (⟨b', hPR hb'⟩ : R))
      have hPcomm : ⁅P, T⁆ = P := by
        refine CFSG.commutator_zpowers_eq_of_fixedPointFree P t ?_ ?_ ?_
        · intro a ha b' hb'
          exact congrArg Subtype.val
            (mul_comm' (⟨a, hPR ha⟩ : R) (⟨b', hPR hb'⟩ : R))
        · exact Subgroup.normalizer_commutator_ge_right R T (Subgroup.mem_zpowers t)
        · intro y hy hfix
          have hinv := hPinv y hy
          rw [hfix] at hinv
          have hy2 : y ^ 2 = 1 := by
            have h := congrArg (fun z => y * z) hinv
            rw [mul_inv_cancel] at h
            simpa [pow_two] using h
          have hyR : y ∈ R := hPR hy
          obtain ⟨k, hk⟩ := hRr.exists_card_eq
          have hdvd : orderOf y ∣ r ^ k := by
            rw [← hk]
            exact Subgroup.orderOf_dvd_natCard R hyR
          have hcop2 : Nat.Coprime 2 r := by
            rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
            intro h
            exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
          exact CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd
            (hcop2.pow_right k) (orderOf_dvd_iff_pow_eq_one.mpr hy2) hdvd
      have hK2 : IsEP 1 ⊤ T T (P ⊔ T) := by
        have hτP : CFSG.Quasithin.E1.tauOf (⊤ : Subgroup Q) T T ≤
            Subgroup.normalizer (P : Set Q) := by
          rw [hτ]
          exact Subgroup.normalizer_commutator_ge_right R T
        have h := isEP_one_of_pSubgroup (T := T) (A := T) (P := P) (p := r)
          hr hr2 hTin le_rfl hTel (hRr.to_le hPR) hPbot hτP hPcomm (hidx P)
        simpa [hτ] using h
      dsimp [E]
      calc P ≤ P ⊔ T := le_sup_left
        _ ≤ eGenP 1 (⊤ : Subgroup Q) T Ω :=
          le_iSup₂_of_le T hTmem (le_iSup_of_le le_rfl (le_iSup₂_of_le (P ⊔ T) hK2 le_rfl))
  let W : Subgroup Q := E ⊓ R
  have hPleW : P ≤ W := le_inf hPleE hPR
  have hWleR : W ≤ R := inf_le_right
  have hWleE : W ≤ E := inf_le_left
  have hNR : R ≤ Subgroup.normalizer (W : Set Q) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have hwR : w ∈ R := hWleR hw
      have hcommxw : x * w = w * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : R) (⟨w, hwR⟩ : R))
      have heq : x * w * x⁻¹ = w := by rw [hcommxw, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hw
    · intro hw
      have hwR : w ∈ R := by
        have h1 : x * w * x⁻¹ ∈ R := hWleR hw
        have h2 : w = x⁻¹ * (x * w * x⁻¹) * x := by group
        rw [h2]
        exact R.mul_mem (R.mul_mem (R.inv_mem hx) h1) hx
      have hcommxw : x * w = w * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : R) (⟨w, hwR⟩ : R))
      have heq : x * w * x⁻¹ = w := by rw [hcommxw, mul_assoc, mul_inv_cancel, mul_one]
      rwa [heq] at hw
  have hNb : b ∈ Subgroup.normalizer (W : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact ⟨E.mul_mem (E.mul_mem hbE hw.1) (E.inv_mem hbE),
        Subgroup.Normal.conj_mem hRnorm w (hWleR hw) b⟩
    · intro hw
      have hthis : w = b⁻¹ * (b * w * b⁻¹) * b := by group
      have hcm := Subgroup.Normal.conj_mem hRnorm (b * w * b⁻¹) hw.2 b⁻¹
      simp only [inv_inv] at hcm
      exact ⟨hthis.symm ▸ E.mul_mem (E.mul_mem (E.inv_mem hbE) hw.1) hbE,
        hthis.symm ▸ hcm⟩
  have hNt : t ∈ Subgroup.normalizer (W : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact ⟨E.mul_mem (E.mul_mem htE hw.1) (E.inv_mem htE),
        Subgroup.Normal.conj_mem hRnorm w (hWleR hw) t⟩
    · intro hw
      have hthis : w = t⁻¹ * (t * w * t⁻¹) * t := by group
      have hcm := Subgroup.Normal.conj_mem hRnorm (t * w * t⁻¹) hw.2 t⁻¹
      simp only [inv_inv] at hcm
      exact ⟨hthis.symm ▸ E.mul_mem (E.mul_mem (E.inv_mem htE) hw.1) htE,
        hthis.symm ▸ hcm⟩
  have hNtop : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (W : Set Q) := by
    rw [← hgen]
    exact sup_le (sup_le hNR (Subgroup.zpowers_le.mpr hNb))
      (Subgroup.zpowers_le.mpr hNt)
  have hWnorm : W.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro y
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNtop (Subgroup.mem_top y))
  have : W.Normal := hWnorm
  let π : Q →* Q ⧸ W := QuotientGroup.mk' W
  have hRbarNorm : (R.map π).Normal := hRnorm.map π (QuotientGroup.mk'_surjective W)
  have : (R.map π).Normal := hRbarNorm
  have htRbar : ∀ x ∈ R, ((t : Q) : Q ⧸ W) * ((x : Q) : Q ⧸ W) *
      (((t : Q) : Q ⧸ W))⁻¹ = ((x : Q) : Q ⧸ W) := by
    intro x hx
    have hmem : t * x * t⁻¹ * x⁻¹ ∈ W := by
      have h1 : t * x * t⁻¹ * x⁻¹ = ⁅x, t⁆⁻¹ := by
        rw [commutatorElement_def]; group
      rw [h1]
      exact hPleW (Subgroup.inv_mem P (Subgroup.commutator_mem_commutator hx
        (Subgroup.mem_zpowers t)))
    have h1 : ((t * x * t⁻¹ * x⁻¹ : Q) : Q ⧸ W) = 1 :=
      (QuotientGroup.eq_one_iff (N := W) _).mpr hmem
    have h2 : ((t : Q) : Q ⧸ W) * ((x : Q) : Q ⧸ W) * (((t : Q) : Q ⧸ W))⁻¹ *
        (((x : Q) : Q ⧸ W))⁻¹ = 1 := by
      simpa using h1
    exact mul_inv_eq_one.mp h2
  have hbquot : ∀ x ∈ R, ((b⁻¹ * x * b : Q) : Q ⧸ W) =
      ((b * x * b⁻¹ : Q) : Q ⧸ W) := by
    intro x hx
    set tq : Q ⧸ W := ((t : Q) : Q ⧸ W)
    set bq : Q ⧸ W := ((b : Q) : Q ⧸ W)
    set xq : Q ⧸ W := ((x : Q) : Q ⧸ W)
    have htq2 : tq * tq = 1 := by
      dsimp [tq]
      rw [← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
    have htqinv : tq⁻¹ = tq := inv_eq_of_mul_eq_one_right htq2
    have htqx : tq * xq * tq⁻¹ = xq := htRbar x hx
    have htqx' : tq⁻¹ * xq * tq = xq := by simpa [htqinv] using htqx
    have hb1 : bq⁻¹ = tq * bq * tq⁻¹ := by
      have h : ((t * b * t⁻¹ : Q) : Q ⧸ W) = ((b⁻¹ : Q) : Q ⧸ W) := by rw [htb]
      simpa [tq, bq] using h.symm
    have hb2 : bq = tq * bq⁻¹ * tq⁻¹ := by
      calc bq = (bq⁻¹)⁻¹ := (inv_inv bq).symm
        _ = (tq * bq * tq⁻¹)⁻¹ := by rw [hb1]
        _ = tq * bq⁻¹ * tq⁻¹ := by group
    have hbxq : ((b * x * b⁻¹ : Q) : Q ⧸ W) = bq * xq * bq⁻¹ := by
      simp [bq, xq]
    have hbtriv : tq * (bq * xq * bq⁻¹) * tq⁻¹ = bq * xq * bq⁻¹ := by
      rw [← hbxq]
      exact htRbar (b * x * b⁻¹) (Subgroup.Normal.conj_mem hRnorm x hx b)
    have hmain : bq⁻¹ * xq * bq * (bq * xq * bq⁻¹)⁻¹ = 1 := by
      calc bq⁻¹ * xq * bq * (bq * xq * bq⁻¹)⁻¹
          = bq⁻¹ * xq * (tq * bq⁻¹ * tq⁻¹) * (bq * xq * bq⁻¹)⁻¹ := by
              conv_lhs => arg 1; arg 2; rw [hb2]
        _ = (tq * bq * tq⁻¹) * xq * (tq * bq⁻¹ * tq⁻¹) *
              (bq * xq * bq⁻¹)⁻¹ := by
              conv_lhs => arg 1; arg 1; rw [hb1]
        _ = tq * bq * (tq⁻¹ * xq * tq) * bq⁻¹ * tq⁻¹ *
              (bq * xq * bq⁻¹)⁻¹ := by group
        _ = tq * bq * xq * bq⁻¹ * tq⁻¹ * (bq * xq * bq⁻¹)⁻¹ := by rw [htqx']
        _ = tq * (bq * xq * bq⁻¹) * tq⁻¹ * (bq * xq * bq⁻¹)⁻¹ := by group
        _ = 1 := by rw [hbtriv, mul_inv_cancel]
    have hmem : b⁻¹ * x * b * (b * x * b⁻¹)⁻¹ ∈ W := by
      have h : ((b⁻¹ * x * b * (b * x * b⁻¹)⁻¹ : Q) : Q ⧸ W) = 1 := by
        simpa [map_mul, map_inv, bq, xq] using hmain
      exact (QuotientGroup.eq_one_iff (N := W) _).mp h
    have h1 : ((b⁻¹ * x * b : Q) : Q ⧸ W) * (((b * x * b⁻¹ : Q)) : Q ⧸ W)⁻¹ = 1 := by
      simpa [map_mul, map_inv] using (QuotientGroup.eq_one_iff (N := W) _).mpr hmem
    exact mul_inv_eq_one.mp h1
  let φ : MulAut ↥(R.map π) := MulAut.conjNormal ((b : Q) : Q ⧸ W)
  have hφ2 : φ ^ 2 = 1 := by
    ext u
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp u.2
    have hu : u = ⟨((x : Q) : Q ⧸ W), ⟨x, hx, rfl⟩⟩ := Subtype.ext hxu.symm
    rw [hu]
    change ((φ ^ 2) ⟨((x : Q) : Q ⧸ W), ⟨x, hx, rfl⟩⟩ : Q ⧸ W) = ((x : Q) : Q ⧸ W)
    have hbq := hbquot x hx
    have hconj := congrArg (fun z => ((b : Q) : Q ⧸ W) * z * (((b : Q) : Q ⧸ W))⁻¹) hbq
    have hconj' : ((b * (b⁻¹ * x * b) * b⁻¹ : Q) : Q ⧸ W) =
        ((b * (b * x * b⁻¹) * b⁻¹ : Q) : Q ⧸ W) := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hconj
    have hleft : ((b * (b⁻¹ * x * b) * b⁻¹ : Q) : Q ⧸ W) = ((x : Q) : Q ⧸ W) := by
      have e : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [e]
    rw [hleft] at hconj'
    rw [pow_two, MulAut.mul_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    simpa [mul_assoc] using hconj'.symm
  have hφp : φ ^ p = 1 := by
    have hbqpow : ((b : Q) : Q ⧸ W) ^ p = 1 := by
      have h := congrArg (QuotientGroup.mk' W) hbpow
      simpa using h
    calc φ ^ p = (MulAut.conjNormal ((b : Q) : Q ⧸ W)) ^ p := rfl
      _ = MulAut.conjNormal (((b : Q) : Q ⧸ W) ^ p) := by rw [← map_pow]
      _ = 1 := by rw [hbqpow, map_one]
  have hφ1 : φ = 1 := by
    have h2 : orderOf φ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hφ2
    have hpdvd : orderOf φ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hφp
    have hcop2 : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 h2 hpdvd)
  have hbRbar : ∀ x ∈ R, ((b * x * b⁻¹ : Q) : Q ⧸ W) = ((x : Q) : Q ⧸ W) := by
    intro x hx
    have hu := congrArg (fun ψ : MulAut ↥(R.map π) =>
      ψ ⟨((x : Q) : Q ⧸ W), ⟨x, hx, rfl⟩⟩) hφ1
    simp only [MulAut.one_apply] at hu
    have := congrArg Subtype.val hu
    simpa [φ, MulAut.conjNormal_apply] using this
  have hcomm_le : ⁅R, Subgroup.zpowers b⁆ ≤ W := by
    refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hNb ?_
    intro x hx
    have h1 : ((x * b * x⁻¹ * b⁻¹ : Q) : Q ⧸ W) = 1 := by
      have hx' := hbRbar x⁻¹ (R.inv_mem hx)
      have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e]
      change (QuotientGroup.mk' W) (x * (b * x⁻¹ * b⁻¹)) = 1
      rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hx']
      exact mul_inv_cancel _
    have hmem : x * b * x⁻¹ * b⁻¹ ∈ W :=
      (QuotientGroup.eq_one_iff (N := W) _).mp h1
    simpa [commutatorElement_def] using hmem
  have hRleW : R ≤ W := by
    rw [← hcomm]
    exact hcomm_le
  have hRleE : R ≤ E := hRleW.trans hWleE
  have hEtop : E = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen]
    exact sup_le (sup_le hRleE (Subgroup.zpowers_le.mpr hbE))
      (Subgroup.zpowers_le.mpr htE)
  dsimp [E] at hEtop
  rw [hEtop]
  exact Set.univ_mul ⟨1, T.one_mem⟩

theorem inF_one_of_dihedral_frobenius {r p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup Q} (hRnorm : R.Normal)
    (hRabel : IsMulCommutative R) (hRr : IsPGroup r R) {b t : Q}
    (hb : orderOf b = p) (ht : orderOf t = 2)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t) ⊤)
    (htb : t * b * t⁻¹ = b⁻¹) (hcomm : ⁅R, Subgroup.zpowers b⁆ = R)
    (hgen : R ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers t = ⊤) :
    InF 1 (⊤ : Subgroup Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : R.Normal := hRnorm
  intro T hT
  unfold InFFor
  intro Ω hΩ hΩne hΩnt
  have hSin : IsSylowIn 2 (Subgroup.zpowers t) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl
  have hTin : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  obtain ⟨g, -, hleT⟩ :=
    CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hSin le_top hTin.isPGroup
  have hTcard2 : Nat.card T = 2 := by
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hT,
      ← CFSG.ABGLocalTools.IsSylowOf.card_eq hSyl, Nat.card_zpowers, ht]
  have hTeq : T = CFSG.Quasithin.conjSubgroup (Subgroup.zpowers t) g := by
    refine Subgroup.eq_of_le_of_card_ge hleT ?_
    rw [hTcard2, CFSG.Quasithin.E3.card_conjSubgroup, Nat.card_zpowers, ht]
  have hzn : Subgroup.zpowers (g⁻¹ * t * g) = T := by
    rw [hTeq, CFSG.Quasithin.conjSubgroup, MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply]
  let t' : Q := g⁻¹ * t * g
  let b' : Q := g⁻¹ * b * g
  have ht' : orderOf t' = 2 := by
    have h : t' = (MulAut.conj g⁻¹) t := by
      simp only [t', MulAut.conj_apply, inv_inv]
    rw [h, (MulAut.conj g⁻¹).orderOf_eq t, ht]
  have hb' : orderOf b' = p := by
    have h : b' = (MulAut.conj g⁻¹) b := by
      simp only [b', MulAut.conj_apply, inv_inv]
    rw [h, (MulAut.conj g⁻¹).orderOf_eq b, hb]
  have htb' : t' * b' * t'⁻¹ = b'⁻¹ := by
    simp only [t', b']
    rw [show (g⁻¹ * t * g) * (g⁻¹ * b * g) * (g⁻¹ * t * g)⁻¹ =
      g⁻¹ * (t * b * t⁻¹) * g by group, htb]
    group
  have hRmap : R.map (MulAut.conj g⁻¹).toMonoidHom = R :=
    Subgroup.Normal.map_conj_eq (H := R) g⁻¹
  have hb'eq : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) b = b' := by
    simp [b', MulAut.conj_apply]
  have ht'eq : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) t = t' := by
    simp [t', MulAut.conj_apply]
  have hcomm' : ⁅R, Subgroup.zpowers b'⁆ = R := by
    have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hcomm
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hb'eq, hRmap] at h
    exact h
  have hgen' : R ⊔ Subgroup.zpowers b' ⊔ Subgroup.zpowers t' = ⊤ := by
    have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers, hb'eq, ht'eq, hRmap] at h
    exact h
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t') ⊤ := by
    rw [hzn]
    exact hT
  have hprod := mul_eGenP_zpowers_eq_top hr hr2 hp hp2 hRnorm hRabel hRr hb' ht'
    hSyl' htb' hcomm' hgen' hΩ hΩne hΩnt
  rwa [hzn] at hprod

end CFSG.LocalAnalysis.WeakClosure81

end
