module

public import CFSG.Quasithin.Background.SmithB51SL3L

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section Bound

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_mul_card_fixK_sq_le {D : Subgroup ↥(StatedSL 3 K)} (hD : D ≠ ⊥)
    (hsq : ∀ g ∈ D, g * g = 1) (hcomm : ∀ g ∈ D, ∀ h ∈ D, g * h = h * g) :
    Nat.card D * Nat.card (fixK D) ^ 2 ≤ Nat.card K ^ 6 := by
  have hd := finrank_le_two_of_ne_top (fixK_ne_top hD)
  have h1 := card_le_sq hsq hcomm
  rw [Module.natCard_eq_pow_finrank (K := K) (V := fixK D)]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  calc Nat.card D * (Nat.card K ^ Module.finrank K (fixK D)) ^ 2
      ≤ Nat.card K ^ 2 * (Nat.card K ^ 2) ^ 2 :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left (Nat.pow_le_pow_right hq hd) 2)
    _ = Nat.card K ^ 6 := by ring

theorem eq_axisSub_of_le {D : Subgroup ↥(StatedSL 3 K)} (hD : D ≠ ⊥)
    (hsq : ∀ g ∈ D, g * g = 1) (hcomm : ∀ g ∈ D, ∀ h ∈ D, g * h = h * g)
    (h : Nat.card K ^ 6 ≤ Nat.card D * Nat.card (fixK D) ^ 2) :
    Module.finrank K (fixK D) = 2 ∧ D = axisSub (fixK D) := by
  have hd := finrank_le_two_of_ne_top (fixK_ne_top hD)
  have h1 := card_le_sq hsq hcomm
  rw [Module.natCard_eq_pow_finrank (K := K) (V := fixK D)] at h
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hd2 : Module.finrank K (fixK D) = 2 := by
    by_contra hne
    have hd1 : Module.finrank K (fixK D) ≤ 1 := by omega
    have h2 : Nat.card D * (Nat.card K ^ Module.finrank K (fixK D)) ^ 2 ≤
        Nat.card K ^ 2 * (Nat.card K ^ 1) ^ 2 :=
      Nat.mul_le_mul h1 (Nat.pow_le_pow_left (Nat.pow_le_pow_right hq.le hd1) 2)
    have h3 : Nat.card K ^ 2 * (Nat.card K ^ 1) ^ 2 < Nat.card K ^ 6 := by
      rw [pow_one, ← pow_add]
      exact Nat.pow_lt_pow_right hq (by norm_num)
    omega
  refine ⟨hd2, eq_axisSub_fixK hsq hd2 ?_⟩
  rw [hd2] at h
  have h3 : Nat.card K ^ 2 * (Nat.card K ^ 2) ^ 2 ≤ Nat.card D * (Nat.card K ^ 2) ^ 2 := by
    calc Nat.card K ^ 2 * (Nat.card K ^ 2) ^ 2 = Nat.card K ^ 6 := by ring
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

end Bound

section Pre

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem NatSec.pre_sq {W U : Subgroup V} (c : NatSec L W U K) {B : Subgroup (MulAut V)}
    (hB : IsElemAbelian2 B) : ∀ g ∈ c.pre B, g * g = 1 := by
  intro g hg
  apply c.hπ.1
  rw [map_mul, map_one]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
  exact hB.2 _ hg

theorem NatSec.pre_comm {W U : Subgroup V} (c : NatSec L W U K) {B : Subgroup (MulAut V)}
    (hB : IsElemAbelian2 B) : ∀ g ∈ c.pre B, ∀ h ∈ c.pre B, g * h = h * g := by
  intro g hg h hh
  apply c.hπ.1
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact hB.1 _ hg _ hh

theorem NatSec.pre_ne_bot {W U : Subgroup V} (c : NatSec L W U K) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) (hB : B ≠ ⊥) : c.pre B ≠ ⊥ := by
  intro h0
  apply hB
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨γ, hγ⟩ := c.hπ.2 ⟨b, hBL hb⟩
  have hγB : γ ∈ c.pre B := by
    show ((c.π γ : ↥L) : MulAut V) ∈ B
    rw [hγ]
    exact hb
  rw [h0, Subgroup.mem_bot] at hγB
  rw [hγB, map_one] at hγ
  rw [Subgroup.mem_bot]
  exact (congrArg Subtype.val hγ).symm

theorem NatSec.card_inf_fixV {W : Subgroup V} (c : NatSec L W ⊥ K) (hLW : L ≤ stabSub W)
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    Nat.card ↥(W ⊓ fixV B) = Nat.card (fixK (c.pre B)) := by
  have hbot : L ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by
    simp only [Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have h1 := card_fixSec_nat c.hπ.2 c.f c.hfs c.hfk c.hfe hLW hbot bot_le hBL
  rw [Subgroup.card_bot, one_mul] at h1
  have h2 : fixSec B W ⊥ = W ⊓ fixV B := by
    ext w
    simp only [mem_fixSec, Subgroup.mem_bot, mul_inv_eq_one, Subgroup.mem_inf]
    rfl
  rw [← h2, h1]
  rfl

end Pre

section Fix

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)} (s : SL3Split G L)

theorem SL3Split.card_inf_fixV {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    Nat.card ↥(commV L ⊓ fixV B) = Nat.card (fixK (s.e₁.pre B)) ^ 2 := by
  have hsplit : commV L ⊓ fixV B = (s.I' ⊓ fixV B) ⊔ (s.I ⊓ fixV B) := by
    refine le_antisymm (fun u hu => ?_) (sup_le (inf_le_inf_right _ s.I'_le)
      (inf_le_inf_right _ s.hIU))
    have hu' : u ∈ s.I' ⊔ s.I := by rw [s.sup_eq]; exact hu.1
    obtain ⟨y, hy, x, hx, rfl⟩ := Subgroup.mem_sup.1 hu'
    have key : ∀ b ∈ B, b y = y ∧ b x = x := by
      intro b hb
      have h1 : b (y * x) = y * x := hu.2 b hb
      rw [map_mul] at h1
      have hby : b y ∈ s.I' := ((s.hLI' (hBL hb)) y).2 hy
      have hbx : b x ∈ s.I := ((s.hLI (hBL hb)) x).2 hx
      have h2 : b y / y = x / b x := by
        rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      have h3 : b y / y ∈ s.I' ⊓ s.I := ⟨s.I'.div_mem hby hy, h2 ▸ s.I.div_mem hx hbx⟩
      rw [s.inf_eq_bot, Subgroup.mem_bot, div_eq_one] at h3
      refine ⟨h3, ?_⟩
      rw [h3] at h1
      exact mul_left_cancel h1
    exact Subgroup.mul_mem_sup ⟨hy, fun b hb => (key b hb).1⟩ ⟨hx, fun b hb => (key b hb).2⟩
  have hinf : (s.I' ⊓ fixV B) ⊓ (s.I ⊓ fixV B) = ⊥ := by
    rw [eq_bot_iff, ← s.inf_eq_bot]
    exact inf_le_inf inf_le_left inf_le_left
  have h := card_sup_mul_card_inf (s.I' ⊓ fixV B) (s.I ⊓ fixV B)
  rw [hinf, Subgroup.card_bot, mul_one, ← hsplit, s.e₁'.card_inf_fixV s.hLI' hBL,
    s.e₁.card_inf_fixV s.hLI hBL] at h
  rw [h, pow_two]
  congr 2
  unfold NatSec.pre
  rw [s.e₁'_π]

theorem SL3Split.card_mul_le (s : SL3Split G L) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hA : A ≠ ⊥)
    (hAel : IsElemAbelian2 A) :
    Nat.card A * Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card (commV L) := by
  have : CharP s.K 2 := charP_two_of_card_eq s.hK
  rw [s.card_inf_fixV hAL, s.card_U, ← s.e₁.card_pre hAL]
  exact card_mul_card_fixK_sq_le (s.e₁.pre_ne_bot hAL hA) (s.e₁.pre_sq hAel) (s.e₁.pre_comm hAel)

end Fix

section Offenders

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} (s : SL3Split G L)

theorem SL3Split.offender_iff (hGL : G = L) (A : Subgroup (MulAut V)) :
    IsFFStarOffenderOn G A (commV L) ↔ A ≤ L ∧
      ∃ W : Submodule s.K (Fin 3 → s.K), Module.finrank s.K W = 2 ∧
        ∀ g : ↥(StatedSL 3 s.K), g ∈ (A.subgroupOf L).comap s.e₁.π ↔
          (∀ w ∈ W, ((g : Matrix.GeneralLinearGroup (Fin 3) s.K) :
              Matrix (Fin 3) (Fin 3) s.K).mulVec w = w) ∧
            ∀ v, ((g : Matrix.GeneralLinearGroup (Fin 3) s.K) :
              Matrix (Fin 3) (Fin 3) s.K).mulVec v - v ∈ W := by
  have : CharP s.K 2 := charP_two_of_card_eq s.hK
  have hfixbot : fixV (⊥ : Subgroup (MulAut V)) ⊓ commV L = commV L := by
    rw [inf_eq_right]
    intro v _ x hx
    rw [Subgroup.mem_bot.1 hx]
    rfl
  constructor
  · rintro ⟨hAG, hAne, hAel, hoff⟩
    have hAL : A ≤ L := hGL ▸ hAG
    have h1 := hoff ⊥ bot_le
    rw [Subgroup.card_bot, one_mul, hfixbot, inf_comm, s.card_inf_fixV hAL, s.card_U,
      ← s.e₁.card_pre hAL] at h1
    obtain ⟨hd, heq⟩ := eq_axisSub_of_le (s.e₁.pre_ne_bot hAL hAne) (s.e₁.pre_sq hAel)
      (s.e₁.pre_comm hAel) h1
    refine ⟨hAL, fixK (s.e₁.pre A), hd, fun g => ?_⟩
    show g ∈ s.e₁.pre A ↔ _
    exact Iff.of_eq (congrArg (fun H => g ∈ H) heq)
  · rintro ⟨hAL, W, hW, hiff⟩
    have hpre : s.e₁.pre A = axisSub W := by
      ext g
      exact hiff g
    have hcardA : Nat.card A = Nat.card s.K ^ 2 := by
      rw [← s.e₁.card_pre hAL, hpre, card_axisSub hW]
    have hAne : A ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hcardA
      have h2 : 1 < Nat.card s.K := Finite.one_lt_card
      have h3 : 1 < Nat.card s.K ^ 2 := Nat.one_lt_pow (by norm_num) h2
      omega
    have hAel : IsElemAbelian2 A := by
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · obtain ⟨γ, hγ⟩ := s.e₁.hπ.2 ⟨a, hAL ha⟩
        obtain ⟨δ, hδ⟩ := s.e₁.hπ.2 ⟨b, hAL hb⟩
        have hγA : γ ∈ axisSub W := by
          rw [← hpre]
          show ((s.e₁.π γ : ↥L) : MulAut V) ∈ A
          rw [hγ]
          exact ha
        have hδA : δ ∈ axisSub W := by
          rw [← hpre]
          show ((s.e₁.π δ : ↥L) : MulAut V) ∈ A
          rw [hδ]
          exact hb
        have := congrArg (fun g => ((s.e₁.π g : ↥L) : MulAut V)) (axisSub_comm hγA hδA)
        simp only [map_mul, Subgroup.coe_mul, hγ, hδ] at this
        exact this
      · obtain ⟨γ, hγ⟩ := s.e₁.hπ.2 ⟨a, hAL ha⟩
        have hγA : γ ∈ axisSub W := by
          rw [← hpre]
          show ((s.e₁.π γ : ↥L) : MulAut V) ∈ A
          rw [hγ]
          exact ha
        have := congrArg (fun g => ((s.e₁.π g : ↥L) : MulAut V)) (axisSub_mul_self hγA)
        simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hγ] at this
        rw [pow_two]
        exact this
    have hfixA : fixK (s.e₁.pre A) = W := by
      rw [hpre]
      exact fixK_eq_of_le_axisSub hW le_rfl (by rw [← hpre]; exact s.e₁.pre_ne_bot hAL hAne)
    have hWcard : Nat.card W = Nat.card s.K ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := s.K) (V := W), hW]
    refine ⟨hGL ▸ hAL, hAne, hAel, fun B hBA => ?_⟩
    have hBL : B ≤ L := hBA.trans hAL
    rw [inf_comm, inf_comm (fixV A), s.card_inf_fixV hBL, s.card_inf_fixV hAL, hfixA, hWcard,
      hcardA]
    by_cases hB : B = ⊥
    · subst hB
      have h1 := s.card_inf_fixV (bot_le : (⊥ : Subgroup (MulAut V)) ≤ L)
      rw [inf_comm, hfixbot, s.card_U] at h1
      rw [Subgroup.card_bot, one_mul, ← h1]
      ring_nf
      exact le_rfl
    · have hfixB : fixK (s.e₁.pre B) = W := by
        refine fixK_eq_of_le_axisSub hW ?_ (s.e₁.pre_ne_bot hBL hB)
        rw [← hpre]
        exact fun g hg => hBA hg
      rw [hfixB, hWcard]
      have h1 : Nat.card B ≤ Nat.card s.K ^ 2 := by
        rw [← hcardA]
        exact Subgroup.card_le_of_le hBA
      exact Nat.mul_le_mul_right _ h1

omit [Finite V] in
theorem fixV_bot_eq_top : fixV (⊥ : Subgroup (MulAut V)) = ⊤ :=
  eq_top_iff.2 fun v _ x hx => by rw [Subgroup.mem_bot.1 hx]; rfl

theorem SL3Split.qOf_eq_one (s : SL3Split G L) (hV : ∀ v : V, v ^ 2 = 1) (hGL : G = L) :
    qOf G = ((1 : ℚ) : WithTop ℚ) := by
  have hA2 : IsA2 G s.A := ⟨s.hmin.1.1, s.hmin.1.2.1, s.hmin.1.2.2.1⟩
  apply le_antisymm
  · have h1 : qOf G ≤ ((rAV s.A : ℚ) : WithTop ℚ) := qOf_le_iff.2 ⟨s.A, hA2, s.hquad, le_rfl⟩
    have h2 : rAV s.A ≤ 1 := by
      refine (rAV_le_one_iff hV hA2).2 ?_
      have := s.hmin.1.2.2.2 ⊥ bot_le
      rw [Subgroup.card_bot, one_mul, fixV_bot_eq_top, Subgroup.card_top] at this
      exact this
    exact h1.trans (WithTop.coe_le_coe.2 h2)
  · show ((1 : ℚ) : WithTop ℚ) ≤ kq G 2
    refine le_kq_iff.2 fun B hB _ => ?_
    have hBL : B ≤ L := hGL ▸ hB.1
    have h1 := s.card_mul_le hBL hB.2.1 hB.2.2
    have h2 := Subgroup.relIndex_mul_card (fixV B) (commV L)
    rw [inf_comm] at h2
    have h3 : Nat.card B ≤ (fixV B).relIndex (commV L) := by
      have hpos : 0 < Nat.card ↥(commV L ⊓ fixV B) := Nat.card_pos
      rw [← h2] at h1
      exact Nat.le_of_mul_le_mul_right h1 hpos
    have h4 : (fixV B).relIndex (commV L) ≤ (fixV B).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.relIndex_dvd_index_of_normal _ _)
    have h5 : 2 ^ rk B ≤ 2 ^ rkIdx (fixV B) := by
      rw [← B1.card_elemAbelian hB.2.2, ← B1.index_eq_two_pow hV]
      exact h3.trans h4
    have h6 : rk B ≤ rkIdx (fixV B) := (Nat.pow_le_pow_iff_right (by norm_num)).1 h5
    have hrk : 0 < rk B := hB.rk_pos
    unfold rAV
    rw [le_div_iff₀ (by exact_mod_cast hrk), one_mul]
    exact_mod_cast h6

end Offenders

end B5

end CFSG.Quasithin
