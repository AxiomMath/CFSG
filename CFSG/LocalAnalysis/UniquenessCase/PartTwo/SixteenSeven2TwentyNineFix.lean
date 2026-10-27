module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_rk_sup_of_inf_bot {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    rk ↥(A ⊔ B) = rk ↥A + rk ↥B := by
  have h1 := rk_sup_add_rk_inf A B
  rw [h, rk_bot] at h1
  omega

private theorem s16c167_inf_fixV_sup {Q : Subgroup (MulAut W)} {A B : Subgroup W}
    (hdisj : A ⊓ B = ⊥) (hA : ∀ q ∈ Q, ∀ x ∈ A, q x ∈ A)
    (hB : ∀ q ∈ Q, ∀ x ∈ B, q x ∈ B) :
    (A ⊔ B) ⊓ fixV Q = (A ⊓ fixV Q) ⊔ (B ⊓ fixV Q) := by
  have hdec : ∀ w ∈ A ⊔ B, ∃ x₁ ∈ A, ∃ x₂ ∈ B, x₁ * x₂ = w := by
    intro w hw
    rwa [Subgroup.mem_sup] at hw
  have huniq : ∀ {a a' b b' : W}, a ∈ A → a' ∈ A → b ∈ B → b' ∈ B →
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      have h2 : a'⁻¹ * a * b = b' := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← h2, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha,
        by rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : b' * b⁻¹ = 1 := by rw [← h1]; exact hmem
    exact ⟨(inv_mul_eq_one.mp hmem).symm, (mul_inv_eq_one.mp hb1).symm⟩
  have hfix : ∀ x₁ ∈ A, ∀ x₂ ∈ B,
      (x₁ * x₂ ∈ fixV Q ↔ x₁ ∈ fixV Q ∧ x₂ ∈ fixV Q) := by
    intro x₁ hx₁ x₂ hx₂
    rw [mem_fixV, mem_fixV, mem_fixV]
    constructor
    · intro h
      have h' : ∀ q ∈ Q, q x₁ * q x₂ = x₁ * x₂ := fun q hq => by
        rw [← map_mul]; exact h q hq
      exact ⟨fun q hq => (huniq (hA q hq x₁ hx₁) hx₁ (hB q hq x₂ hx₂) hx₂ (h' q hq)).1,
        fun q hq => (huniq (hA q hq x₁ hx₁) hx₁ (hB q hq x₂ hx₂) hx₂ (h' q hq)).2⟩
    · rintro ⟨h₁', h₂'⟩ q hq
      rw [map_mul, h₁' q hq, h₂' q hq]
  apply le_antisymm
  · intro w hw
    rw [Subgroup.mem_inf] at hw
    obtain ⟨x₁, hx₁, x₂, hx₂, hwx⟩ := hdec w hw.1
    rw [← hwx] at hw ⊢
    have hmem := (hfix x₁ hx₁ x₂ hx₂).mp hw.2
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hx₁, hmem.1⟩)
      (Subgroup.mem_inf.mpr ⟨hx₂, hmem.2⟩)
  · refine sup_le ?_ ?_
    · exact le_inf (le_trans inf_le_left le_sup_left) inf_le_right
    · exact le_inf (le_trans inf_le_left le_sup_right) inf_le_right

private theorem s16c167_one_le_rk_of_ne_bot {C I : Subgroup W} (hCI : C ≤ I)
    (hI : Nat.card ↥I = 8) (hne : C ≠ ⊥) : 1 ≤ rk ↥C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥C ∣ 8 := by
    rw [← hI]; exact Subgroup.card_dvd_of_le hCI
  have hne1 : Nat.card ↥C ≠ 1 := fun h => hne ((Subgroup.card_eq_one).mp h)
  have h2dvd : 2 ∣ Nat.card ↥C := by
    have hdvd' : Nat.card ↥C ∣ 2 ^ 3 := by simpa using hdvd
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk0 : k ≠ 0 := by
      rintro rfl; exact hne1 (by rw [hk', pow_zero])
    rw [hk']
    exact dvd_pow_self 2 hk0
  have hpos : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  show 1 ≤ padicValNat 2 (Nat.card ↥C)
  exact (padicValNat_dvd_iff_le (p := 2) (n := 1) hpos).mp (by simpa using h2dvd)

private theorem s16c167_fixV_inf_ne_bot {Q : Subgroup (MulAut W)} (hQ : IsPGroup 2 ↥Q)
    {I : Subgroup W} (hI : Nat.card ↥I = 8)
    (hinv : ∀ q ∈ Q, ∀ v ∈ I, q v ∈ I) : I ⊓ fixV Q ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥Q ↥I :=
    { smul := fun q v => ⟨q.1 v.1, hinv q.1 q.2 v.1 v.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  letI := act
  have hdvd : 2 ∣ Nat.card ↥I := by rw [hI]; norm_num
  have h1 : (1 : ↥I) ∈ MulAction.fixedPoints ↥Q ↥I := fun q => Subtype.ext (map_one q.1)
  obtain ⟨b, hb, hb1⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥I hdvd h1
  intro hbot
  have hbmem : b.1 ∈ I ⊓ fixV Q :=
    ⟨b.2, fun q hq => congrArg Subtype.val (hb ⟨q, hq⟩)⟩
  rw [hbot, Subgroup.mem_bot] at hbmem
  exact hb1 (Subtype.ext hbmem).symm

theorem s16c167_natSum3_fix_ge {L : Subgroup (MulAut W)} {J : Subgroup W} (hJ : NatSum3 L J)
    {Q : Subgroup (MulAut W)} (hQL : Q ≤ L) (hQ : IsPGroup 2 ↥Q) :
    3 ≤ rk ↥(J ⊓ fixV Q) := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := hJ
  have hinv₀ : ∀ q ∈ Q, ∀ v ∈ I₀, q v ∈ I₀ := fun q hq v hv => hi₀.1 ⟨q, hQL hq⟩ v hv
  have hinv₁ : ∀ q ∈ Q, ∀ v ∈ I₁, q v ∈ I₁ := fun q hq v hv => hi₁.1 ⟨q, hQL hq⟩ v hv
  have hinv₂ : ∀ q ∈ Q, ∀ v ∈ I₂, q v ∈ I₂ := fun q hq v hv => hi₂.1 ⟨q, hQL hq⟩ v hv
  have hinvSup : ∀ q ∈ Q, ∀ v ∈ I₀ ⊔ I₁, q v ∈ I₀ ⊔ I₁ := by
    intro q hq v hv
    rw [Subgroup.mem_sup] at hv ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    exact ⟨q a, hinv₀ q hq a ha, q b, hinv₁ q hq b hb, (map_mul q a b).symm⟩
  have hdec01 := s16c167_inf_fixV_sup (Q := Q) h01 hinv₀ hinv₁
  have hdec012 := s16c167_inf_fixV_sup (Q := Q) (A := I₀ ⊔ I₁) (B := I₂) h012 hinvSup hinv₂
  have hdecomp : J ⊓ fixV Q = ((I₀ ⊓ fixV Q) ⊔ (I₁ ⊓ fixV Q)) ⊔ (I₂ ⊓ fixV Q) := by
    rw [← hsum, hdec012, hdec01]
  have hCdisj01 : (I₀ ⊓ fixV Q) ⊓ (I₁ ⊓ fixV Q) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf inf_le_left inf_le_left) h01.le)
  have hCdisj012 : ((I₀ ⊓ fixV Q) ⊔ (I₁ ⊓ fixV Q)) ⊓ (I₂ ⊓ fixV Q) = ⊥ := by
    apply le_bot_iff.mp
    rw [← h012]
    exact inf_le_inf (sup_le (le_trans inf_le_left le_sup_left)
      (le_trans inf_le_left le_sup_right)) inf_le_left
  have hrank : rk ↥(J ⊓ fixV Q) =
      rk ↥(I₀ ⊓ fixV Q) + rk ↥(I₁ ⊓ fixV Q) + rk ↥(I₂ ⊓ fixV Q) := by
    rw [hdecomp, s16c167_rk_sup_of_inf_bot hCdisj012,
      s16c167_rk_sup_of_inf_bot hCdisj01]
  have h1₀ := s16c167_one_le_rk_of_ne_bot (C := I₀ ⊓ fixV Q) (I := I₀) inf_le_left hc₀
    (s16c167_fixV_inf_ne_bot hQ hc₀ hinv₀)
  have h1₁ := s16c167_one_le_rk_of_ne_bot (C := I₁ ⊓ fixV Q) (I := I₁) inf_le_left hc₁
    (s16c167_fixV_inf_ne_bot hQ hc₁ hinv₁)
  have h1₂ := s16c167_one_le_rk_of_ne_bot (C := I₂ ⊓ fixV Q) (I := I₂) inf_le_left hc₂
    (s16c167_fixV_inf_ne_bot hQ hc₂ hinv₂)
  omega

private theorem s16c167_isIrr_action_nontrivial {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : XMod.IsIrr ↥L V) (hc : Nat.card ↥V = 8) :
    ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
  by_contra hcon
  have htriv : ∀ x ∈ L, ∀ v ∈ V, x v = v := by
    intro x hx v hv
    by_contra hne
    exact hcon ⟨x, hx, v, hv, hne⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 2 (by rw [hc]; norm_num)
  let K : Subgroup W := Subgroup.zpowers (x₀ : W)
  have hxV : (x₀ : W) ∈ V := x₀.2
  have hKV : K ≤ V := Subgroup.zpowers_le.mpr hxV
  have hKcard : Nat.card K = 2 := by
    change Nat.card (Subgroup.zpowers (x₀ : W)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx₀]
  have hKinv : XMod.IsInv ↥L K := by
    intro a l hl
    have hlV : l ∈ V := hKV hl
    have hfix : (a : MulAut W) l = l := htriv a a.2 l hlV
    show (a : MulAut W) l ∈ K
    rw [hfix]; exact hl
  have hKbot : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hKcard
    omega
  have hKtop : K ≠ V := by
    intro h
    rw [h, hc] at hKcard
    omega
  rcases hV.2.2 K hKinv bot_le hKV with h | h
  · exact hKbot h
  · exact hKtop h

private theorem s16c167_faithful_of_isIrr {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {I : Subgroup W} (hI : XMod.IsIrr ↥L I) (hc : Nat.card ↥I = 8) :
    ∀ l ∈ L, (∀ v ∈ I, l v = v) → l = 1 := by
  haveI : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
  have hnt := s16c167_isIrr_action_nontrivial hI hc
  let K : Subgroup ↥L :=
    { carrier := {l | ∀ v ∈ I, (l : MulAut W) v = v}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {a b} ha hb => by
        intro v hv
        show ((a * b : ↥L) : MulAut W) v = v
        rw [Subgroup.coe_mul, MulAut.mul_apply, hb v hv]
        exact ha v hv
      inv_mem' := fun {a} ha => by
        intro v hv
        have hmem : ((a⁻¹ : ↥L) : MulAut W) v ∈ I := hI.1 a⁻¹ v hv
        have h1 : (a : MulAut W) (((a⁻¹ : ↥L) : MulAut W) v) = ((a⁻¹ : ↥L) : MulAut W) v :=
          ha _ hmem
        have h2 : (a : MulAut W) (((a⁻¹ : ↥L) : MulAut W) v) = v := by
          show (a : MulAut W) ((a : MulAut W)⁻¹ v) = v
          rw [mulAut_apply_inv_apply]
        rw [h2] at h1
        exact h1.symm }
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    dsimp only [K]
    intro v hv
    rw [Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply, MulAut.mul_apply]
    have hmem : ((g⁻¹ : ↥L) : MulAut W) v ∈ I := hI.1 g⁻¹ v hv
    rw [hn _ hmem, Subgroup.coe_inv]
    exact mulAut_apply_inv_apply g v
  haveI : K.Normal := hKnormal
  have hKproper : K ≠ ⊤ := by
    intro htop
    obtain ⟨l, hl, v, hv, hlv⟩ := hnt
    have hK : (⟨l, hl⟩ : ↥L) ∈ K := by rw [htop]; trivial
    exact hlv (hK v hv)
  have hKbot : K = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_right hKproper
  intro l hl hfix
  have hmem : (⟨l, hl⟩ : ↥L) ∈ K := hfix
  have hone : (⟨l, hl⟩ : ↥L) = 1 := by
    have : (⟨l, hl⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := hKbot ▸ hmem
    simpa using this
  exact congrArg Subtype.val hone

private theorem s16c167_mul_inv_mem_of_relIndex_two {H K : Subgroup W} (hrel : H.relIndex K = 2)
    {x y : W} (hxK : x ∈ K) (hyK : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : y * x⁻¹ ∈ H := by
  obtain ⟨a, haK, -, ha⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and (H := H) (K := K)).mp hrel
  have key : ∀ {y : W}, y ∈ K → y ∉ H → y * a⁻¹ ∈ H := by
    intro y hyK hyH
    rcases ha (y * a⁻¹) (K.mul_mem hyK (K.inv_mem haK)) with h | h
    · rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact absurd h hyH
    · exact h
  have hya := key hyK hyH
  have hxa := key hxK hxH
  have heq : (y * a⁻¹) * (x * a⁻¹)⁻¹ = y * x⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    conv_lhs => rw [mul_assoc]
    rw [← mul_assoc a⁻¹ a x⁻¹, inv_mul_cancel, one_mul]
  rw [← heq]
  exact H.mul_mem hya (H.inv_mem hxa)

theorem s16c167_natSum3_few_fixers (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hL : IsPSL 3 2 1 ↥L) (hJ : NatSum3 L J) {Q : Subgroup (MulAut W)}
    (hQL : Q ≤ L) (hQ : IsPGroup 2 ↥Q) {Y : Subgroup W} (hY : Y ≤ J ⊓ fixV Q)
    (hrk : 6 ≤ rk ↥Y) : Nat.card ↥Q ≤ 4 := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := hJ
  have hI₀rk : rk ↥I₀ = 3 := by
    show padicValNat 2 (Nat.card ↥I₀) = 3
    rw [hc₀, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hI₁rk : rk ↥I₁ = 3 := by
    show padicValNat 2 (Nat.card ↥I₁) = 3
    rw [hc₁, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hI₂rk : rk ↥I₂ = 3 := by
    show padicValNat 2 (Nat.card ↥I₂) = 3
    rw [hc₂, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hinv₀ : ∀ q ∈ Q, ∀ v ∈ I₀, q v ∈ I₀ := fun q hq v hv => hi₀.1 ⟨q, hQL hq⟩ v hv
  have hinv₁ : ∀ q ∈ Q, ∀ v ∈ I₁, q v ∈ I₁ := fun q hq v hv => hi₁.1 ⟨q, hQL hq⟩ v hv
  have hinv₂ : ∀ q ∈ Q, ∀ v ∈ I₂, q v ∈ I₂ := fun q hq v hv => hi₂.1 ⟨q, hQL hq⟩ v hv
  have hinvSup : ∀ q ∈ Q, ∀ v ∈ I₀ ⊔ I₁, q v ∈ I₀ ⊔ I₁ := by
    intro q hq v hv
    rw [Subgroup.mem_sup] at hv ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    exact ⟨q a, hinv₀ q hq a ha, q b, hinv₁ q hq b hb, (map_mul q a b).symm⟩
  have hdec01 := s16c167_inf_fixV_sup (Q := Q) h01 hinv₀ hinv₁
  have hdec012 := s16c167_inf_fixV_sup (Q := Q) (A := I₀ ⊔ I₁) (B := I₂) h012 hinvSup hinv₂
  have hdecomp : J ⊓ fixV Q = ((I₀ ⊓ fixV Q) ⊔ (I₁ ⊓ fixV Q)) ⊔ (I₂ ⊓ fixV Q) := by
    rw [← hsum, hdec012, hdec01]
  have hCdisj01 : (I₀ ⊓ fixV Q) ⊓ (I₁ ⊓ fixV Q) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf inf_le_left inf_le_left) h01.le)
  have hCdisj012 : ((I₀ ⊓ fixV Q) ⊔ (I₁ ⊓ fixV Q)) ⊓ (I₂ ⊓ fixV Q) = ⊥ := by
    apply le_bot_iff.mp
    rw [← h012]
    exact inf_le_inf (sup_le (le_trans inf_le_left le_sup_left)
      (le_trans inf_le_left le_sup_right)) inf_le_left
  have hrank : rk ↥(J ⊓ fixV Q) =
      rk ↥(I₀ ⊓ fixV Q) + rk ↥(I₁ ⊓ fixV Q) + rk ↥(I₂ ⊓ fixV Q) := by
    rw [hdecomp, s16c167_rk_sup_of_inf_bot hCdisj012,
      s16c167_rk_sup_of_inf_bot hCdisj01]
  have h6 : 6 ≤ rk ↥(J ⊓ fixV Q) := le_trans hrk (rk_mono hY)
  have hle₀ : rk ↥(I₀ ⊓ fixV Q) ≤ 3 := by
    have h := rk_mono (inf_le_left : I₀ ⊓ fixV Q ≤ I₀)
    rwa [hI₀rk] at h
  have hle₁ : rk ↥(I₁ ⊓ fixV Q) ≤ 3 := by
    have h := rk_mono (inf_le_left : I₁ ⊓ fixV Q ≤ I₁)
    rwa [hI₁rk] at h
  have hle₂ : rk ↥(I₂ ⊓ fixV Q) ≤ 3 := by
    have h := rk_mono (inf_le_left : I₂ ⊓ fixV Q ≤ I₂)
    rwa [hI₂rk] at h
  by_cases hQbot : Q = ⊥
  · rw [hQbot, Subgroup.card_bot]
    norm_num
  · have hfaith₀ := s16c167_faithful_of_isIrr hL hi₀ hc₀
    have hfaith₁ := s16c167_faithful_of_isIrr hL hi₁ hc₁
    have hfaith₂ := s16c167_faithful_of_isIrr hL hi₂ hc₂
    have hle2₀ : rk ↥(I₀ ⊓ fixV Q) ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ rk ↥(I₀ ⊓ fixV Q) := not_le.1 hcon
      have heq : I₀ ⊓ fixV Q = I₀ := eq_of_le_of_rk_le hW inf_le_left (by rw [hI₀rk]; exact h3)
      have hfixI : I₀ ≤ fixV Q := heq.symm.le.trans inf_le_right
      have hQle : Q ≤ ⊥ := by
        intro q hq
        exact hfaith₀ q (hQL hq) (fun v hv => (mem_fixV.mp (hfixI hv)) q hq)
      exact hQbot (le_bot_iff.mp hQle)
    have hle2₁ : rk ↥(I₁ ⊓ fixV Q) ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ rk ↥(I₁ ⊓ fixV Q) := not_le.1 hcon
      have heq : I₁ ⊓ fixV Q = I₁ := eq_of_le_of_rk_le hW inf_le_left (by rw [hI₁rk]; exact h3)
      have hfixI : I₁ ≤ fixV Q := heq.symm.le.trans inf_le_right
      have hQle : Q ≤ ⊥ := by
        intro q hq
        exact hfaith₁ q (hQL hq) (fun v hv => (mem_fixV.mp (hfixI hv)) q hq)
      exact hQbot (le_bot_iff.mp hQle)
    have hle2₂ : rk ↥(I₂ ⊓ fixV Q) ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ rk ↥(I₂ ⊓ fixV Q) := not_le.1 hcon
      have heq : I₂ ⊓ fixV Q = I₂ := eq_of_le_of_rk_le hW inf_le_left (by rw [hI₂rk]; exact h3)
      have hfixI : I₂ ≤ fixV Q := heq.symm.le.trans inf_le_right
      have hQle : Q ≤ ⊥ := by
        intro q hq
        exact hfaith₂ q (hQL hq) (fun v hv => (mem_fixV.mp (hfixI hv)) q hq)
      exact hQbot (le_bot_iff.mp hQle)
    have e₀ : rk ↥(I₀ ⊓ fixV Q) = 2 := by omega
    have hcardH : Nat.card ↥(I₀ ⊓ fixV Q) = 4 := by
      have h := card_eq_two_pow hW (I₀ ⊓ fixV Q)
      rw [e₀] at h
      simpa using h
    have hx : ∃ x ∈ I₀, x ∉ I₀ ⊓ fixV Q := by
      by_contra hcon
      have hle : I₀ ≤ I₀ ⊓ fixV Q := fun x hx => by
        by_contra hxc
        exact hcon ⟨x, hx, hxc⟩
      have heq : I₀ = I₀ ⊓ fixV Q := le_antisymm hle inf_le_left
      have hcard := congrArg (fun S : Subgroup W => Nat.card ↥S) heq
      rw [hc₀, hcardH] at hcard
      omega
    obtain ⟨x, hxI, hxC⟩ := hx
    have hrel : (I₀ ⊓ fixV Q).relIndex I₀ = 2 := by
      have h := Subgroup.relIndex_mul_card (I₀ ⊓ fixV Q) I₀
      rw [inf_eq_left.mpr inf_le_left, hcardH, hc₀] at h
      omega
    have hqxc : ∀ q : ↥Q, q.1 x ∉ I₀ ⊓ fixV Q := by
      intro q hmem
      have hfixmem : q.1 x ∈ fixV Q := hmem.2
      have h1 : q.1⁻¹ (q.1 x) = q.1 x :=
        (mem_fixV.mp hfixmem) q.1⁻¹ (Q.inv_mem q.2)
      have h2 : q.1⁻¹ (q.1 x) = x := mulAut_inv_apply_apply q.1 x
      have hxq : x = q.1 x := h2.symm.trans h1
      exact hxC (by rw [hxq]; exact hmem)
    let F : ↥Q → ↥(I₀ ⊓ fixV Q) := fun q =>
      ⟨q.1 x * x⁻¹,
        s16c167_mul_inv_mem_of_relIndex_two hrel hxI (hinv₀ q.1 q.2 x hxI) hxC (hqxc q)⟩
    have hgen : I₀ = (I₀ ⊓ fixV Q) ⊔ Subgroup.zpowers x := by
      apply le_antisymm
      · intro v hv
        by_cases hvH : v ∈ I₀ ⊓ fixV Q
        · exact Subgroup.mem_sup_left hvH
        · have hvz : v * x⁻¹ ∈ I₀ ⊓ fixV Q :=
            s16c167_mul_inv_mem_of_relIndex_two hrel hxI hv hxC hvH
          have hv_eq : v = (v * x⁻¹) * x := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
          rw [hv_eq]
          exact Subgroup.mul_mem_sup hvz (Subgroup.mem_zpowers x)
      · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxI)
    have hFinj : Function.Injective F := by
      intro q q' h
      have h1 : q.1 x * x⁻¹ = q'.1 x * x⁻¹ := congrArg Subtype.val h
      have h2 : q.1 x = q'.1 x := mul_right_cancel h1
      have h3 : ((q' : ↥Q)⁻¹ * q).1 x = x := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, h2]
        exact mulAut_inv_apply_apply q'.1 x
      have hfixI : ∀ v ∈ I₀, ((q' : ↥Q)⁻¹ * q).1 v = v := by
        intro v hv
        rw [hgen] at hv
        rw [Subgroup.mem_sup] at hv
        obtain ⟨a, ha, b, hb, rfl⟩ := hv
        have hafix : ((q' : ↥Q)⁻¹ * q).1 a = a :=
          (mem_fixV.mp ha.2) _ ((q' : ↥Q)⁻¹ * q).2
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [map_mul, hafix, map_zpow, h3]
      have hq1 : ((q' : ↥Q)⁻¹ * q).1 = 1 :=
        hfaith₀ _ (hQL ((q' : ↥Q)⁻¹ * q).2) hfixI
      have hq : (q' : ↥Q)⁻¹ * q = 1 := Subtype.ext hq1
      have hfin : q = q' := by
        have hc := congrArg (fun z : ↥Q => (q' : ↥Q) * z) hq
        simpa [mul_assoc] using hc
      exact hfin
    have hcard : Nat.card ↥Q ≤ Nat.card ↥(I₀ ⊓ fixV Q) :=
      Nat.card_le_card_of_injective F hFinj
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
