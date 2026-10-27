module

public import CFSG.Quasithin.Background.SmithB51LnSecC
public import CFSG.Quasithin.Background.SmithB51LnChief

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W Y : Subgroup V}

theorem one_sub_le_one {n : ℕ} (hn : n = 4 ∨ n = 5) : (1 : ℚ) - 1 / ((n : ℚ) - 1) ≤ 1 := by
  rcases hn with rfl | rfl <;> norm_num

theorem chief_natural (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (c : SecCtx G L A W Y) (hAL : A ≤ L) (hquad : IsQuadratic A)
    (hcard : Nat.card (Sec W Y) < Nat.card V)
    (hch : ∀ X : Subgroup V, L ⊔ A ≤ stabSub X → Y ≤ X → X ≤ W → X = Y ∨ X = W)
    (hZ : Subgroup.center ↥L = ⊥) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hr : rAV (autSec A W Y) ≤ 1 - 1 / ((n : ℚ) - 1)) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥(autSec L W Y), RealM (autSec L W Y) ⊤ ⊥ π mat := by
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hr1 : rAV (autSec A W Y) ≤ 1 := hr.trans (one_sub_le_one hn)
  obtain ⟨B, -, -, -, -, hcase⟩ := sec_IH hA21 hIH hV h c hcard hr1
  have hlt : Y < W := by
    refine lt_of_le_of_ne c.hUW fun heq => c.hnc ?_
    exact (commSub_le_of_invariant (fun x hx w hw =>
      (c.hMW (Subgroup.mem_sup_left hx) w).2 hw)).trans heq.symm.le
  have hirrX := isIrrSec_secX c hlt hch
  rw [hLA] at hirrX
  set eS := secEquivSL h c hZ eL with heS
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hirr' : ∀ J : Subgroup (Sec W Y),
      (∀ l : ↥(autSec L W Y), ∀ s ∈ J, (l : MulAut (Sec W Y)) s ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJ => hirrX.2 J hJ bot_le le_top
  have hcommS : commV (autSec L W Y) = ⊤ := by
    rcases hirr' (commV (autSec L W Y)) (fun l s hs => by
      rw [commV_eq_commSub] at hs ⊢
      exact commSub_inv_H _ ⊤ l l.2 s hs) with h0 | h1
    · exfalso
      have hbot : autSec L W Y = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        apply MulEquiv.ext
        intro s
        have : x s * s⁻¹ ∈ commV (autSec L W Y) := Subgroup.subset_closure ⟨x, hx, s, rfl⟩
        rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
        exact this
      have h1 : Nat.card ↥(autSec L W Y) = Nat.card ↥(StatedSL n (ZMod 2)) :=
        Nat.card_congr eS.toEquiv
      rw [hbot, Subgroup.card_bot] at h1
      rcases card_statedSL_four_five hn with h4 | h4 <;> omega
    · exact h1
  rcases hcase with hi | hii | ⟨m, -, hm, π, U₁, U₂, ⟨-, hinf⟩, h1, h2⟩ |
    ⟨-, m, hm, k, hk1, -, I, π, -, hind, hsum, hreal⟩
  · have hirr := isIrrSec_secL_of_irrPlus h c (isIrrSec_secX c hlt hch) hi.1
    rcases irr_sec_cases hA21 hB42 hV h c hquad hirr hZ hn eL hr1 with ⟨hnat, -⟩ | ⟨h34, h5⟩
    · exact hnat
    · exfalso
      rcases hn with rfl | rfl
      · norm_num at hr; linarith
      · have := h5 rfl
        norm_num at hr; linarith
  · exact absurd hii (not_b51Case1ii hn eS)
  · exfalso
    have hR1 := realM_mat_iff.2 h1
    have hR2 := realM_dmat_iff.2 h2
    have hbij : Function.Bijective π := ⟨hR1.injective (Or.inl rfl), hR1.1⟩
    have hmn := eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans eS)
    subst hmn
    have hne1 := hR1.ne_bot hn1
    have hne2 := hR2.ne_bot hn1
    rcases hirr' U₁ (fun l s hs => hR1.2.2.1 l s hs) with h0 | h0
    · exact hne1 h0
    · apply hne2
      rw [← hinf, h0, top_inf_eq]
  · have hR0 := realM_mat_iff.2 (hreal ⟨0, hk1⟩)
    have hbij : Function.Bijective π := ⟨hR0.injective (Or.inl rfl), hR0.1⟩
    have hmn := eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans eS)
    subst hmn
    rcases Nat.lt_or_ge 1 k with hk2 | hk2
    · exfalso
      have hR1 := realM_mat_iff.2 (hreal ⟨1, hk2⟩)
      rcases hirr' (I ⟨0, hk1⟩) (fun l s hs => hR0.2.2.1 l s hs) with h0 | h0
      · exact hR0.ne_bot hn1 h0
      · apply hR1.ne_bot hn1
        have h3 := hind ⟨1, hk2⟩
        rw [bot_sup_eq] at h3
        have h4 : I ⟨0, hk1⟩ ≤ ⨆ (j : Fin k) (_ : j ≠ ⟨1, hk2⟩), I j :=
          le_iSup₂_of_le (f := fun (j : Fin k) (_ : j ≠ ⟨1, hk2⟩) => I j) ⟨0, hk1⟩
            (by simp [Fin.ext_iff]) le_rfl
        rw [eq_bot_iff, ← h3]
        exact le_inf le_rfl (h0 ▸ le_top |>.trans (h0.symm ▸ h4))
    · have hk : k = 1 := by omega
      subst hk
      have h0 : I ⟨0, hk1⟩ = ⊤ := by
        rw [bot_sup_eq, hcommS] at hsum
        rw [← hsum]
        apply le_antisymm (le_iSup I _)
        refine iSup_le fun i => ?_
        have : i = ⟨0, hk1⟩ := Subsingleton.elim _ _
        rw [this]
      rw [h0] at hR0
      exact ⟨π, hR0⟩

omit [Finite V] in
theorem le_stabSub_of_inv {X : Subgroup V} (hX : ∀ x ∈ L, ∀ w ∈ X, x w ∈ X) : L ≤ stabSub X :=
  fun l hl => mem_stabSub_of_inv (hX l hl) (hX l⁻¹ (L.inv_mem hl))

omit [Finite V] in
theorem le_stabSub_top (X : Subgroup (MulAut V)) : X ≤ stabSub (⊤ : Subgroup V) :=
  fun g _ u => by simp

omit [Finite V] in
theorem secImg_secPre {Z : Subgroup V} (hZW : Z ≤ W) (J : Subgroup (Sec W Z)) :
    secImg W Z (secPre W Z J) = J := by
  ext s
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  rw [mk_mem_secImg (le_secPre hZW J), mem_secPre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨w.2, h⟩⟩

theorem exists_max_sub {I : Subgroup V} (hIL : ∀ x ∈ L, ∀ w ∈ I, x w ∈ I) (hI : I ≠ ⊤) :
    ∃ U₀ : Subgroup V, (∀ x ∈ L, ∀ w ∈ U₀, x w ∈ U₀) ∧ I ≤ U₀ ∧ U₀ ≠ ⊤ ∧
      ∀ X : Subgroup V, (∀ x ∈ L, ∀ w ∈ X, x w ∈ X) → U₀ ≤ X → X = U₀ ∨ X = ⊤ := by
  classical
  let 𝒰 : Set (Subgroup V) := {X | (∀ x ∈ L, ∀ w ∈ X, x w ∈ X) ∧ I ≤ X ∧ X ≠ ⊤}
  obtain ⟨U₀, ⟨hU₀inv, hIU₀, hU₀top⟩, hmax⟩ :=
    Set.exists_max_image 𝒰 (fun X => Nat.card X) (Set.toFinite _) ⟨I, hIL, le_rfl, hI⟩
  refine ⟨U₀, hU₀inv, hIU₀, hU₀top, fun X hX hUX => ?_⟩
  by_cases hXt : X = ⊤
  · exact Or.inr hXt
  · left
    exact (Subgroup.eq_of_le_of_card_ge hUX (hmax X ⟨hX, hIU₀.trans hUX, hXt⟩)).symm

theorem commSub_eq_of_top_natural (hI16 : AsI16Cover) (hV : ∀ v : V, v ^ 2 = 1)
    (htop : commV L = ⊤) {U₀ : Subgroup V} (hU₀inv : ∀ x ∈ L, ∀ w ∈ U₀, x w ∈ U₀)
    (hU₀top : U₀ ≠ ⊤)
    (hch₀ : ∀ X : Subgroup V, (∀ x ∈ L, ∀ w ∈ X, x w ∈ X) → U₀ ≤ X → X = U₀ ∨ X = ⊤) {n : ℕ}
    (hn : n = 4 ∨ n = 5) {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hR : RealM L ⊤ U₀ π mat) :
    commSub U₀ L = U₀ := by
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  set Z := commSub U₀ L with hZ
  have hZinv : ∀ x ∈ L, ∀ z ∈ Z, x z ∈ Z := commSub_inv_H L U₀
  have hZU : Z ≤ U₀ := commSub_le_of_invariant hU₀inv
  have hLZ := le_stabSub_of_inv hZinv
  have hLtop := le_stabSub_top L
  set L' := autSec L ⊤ Z with hL'
  have hcomm' : commV L' = ⊤ :=
    commV_autSec_eq_top hLtop hLZ (by rw [← commV_eq_commSub, htop, top_sup_eq])
  have hR' := hR.toSec hZU hLZ
  have hfix' : fixV L' = secImg ⊤ Z U₀ := by
    ext s
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective s
    rw [mk_mem_fixV_autSec_iff hLtop hLZ, mk_mem_secImg hZU]
    constructor
    · intro hv
      exact hR.mem_of_fixed (Or.inl rfl) hn2 (Subgroup.mem_top _) fun l hl => hZU (hv l hl)
    · intro hv l hl
      exact Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩
  have hIrr : commV L' ∈ IrrPlus L' (⊤ : Subgroup (Sec ⊤ Z)) := by
    rw [hcomm', mem_irrPlus_top_iff]
    refine ⟨fun _ _ _ _ => trivial, by rw [← commV_eq_commSub]; exact hcomm', ?_, ?_⟩
    · rw [top_inf_eq, hfix', lt_top_iff_ne_top]
      intro h1
      apply hU₀top
      rw [eq_top_iff]
      intro v _
      have : (QuotientGroup.mk ⟨v, trivial⟩ : Sec ⊤ Z) ∈ secImg ⊤ Z U₀ := by rw [h1]; trivial
      exact (mk_mem_secImg hZU _).1 this
    · intro J hJ hJ1 _
      rw [top_inf_eq, hfix'] at hJ1 ⊢
      set J₀ := secPre ⊤ Z J with hJ₀
      have hJ₀inv : ∀ x ∈ L, ∀ w ∈ J₀, x w ∈ J₀ := by
        intro x hx w hw
        obtain ⟨hw', hs⟩ := mem_secPre.1 hw
        refine mem_secPre.2 ⟨trivial, ?_⟩
        have := hJ _ (secHomL L hLtop hLZ ⟨x, hx⟩).2 _ hs
        rw [show ((secHomL L hLtop hLZ ⟨x, hx⟩ : ↥(autSec L ⊤ Z)) : MulAut (Sec ⊤ Z)) =
          B5.secHom L hLtop hLZ ⟨x, hx⟩ from rfl, B5.secHom_mk] at this
        exact this
      have hUJ : U₀ ≤ J₀ := fun u hu =>
        mem_secPre.2 ⟨trivial, hJ1 ((mk_mem_secImg (W := ⊤) hZU ⟨u, trivial⟩).2 hu)⟩
      rcases hch₀ J₀ hJ₀inv hUJ with h1 | h1
      · left
        rw [← secImg_secPre le_top J, ← hJ₀, h1]
      · right
        rw [← secImg_secPre le_top J, ← hJ₀, h1, eq_top_iff]
        intro s _
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
        exact (mk_mem_secImg le_top w).2 trivial
  have hnat : BinaryNaturalSL L' (commV L') (fixV L' ⊓ commV L') n 1 := by
    rw [hcomm', inf_top_eq, hfix']
    exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨_, realM_mat_iff.1 hR'⟩⟩
  have hbot := hI16 (Sec ⊤ Z) (CFSG.Quasithin.sq_eq_one_sec hV ⊤ Z) L' hIrr (by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hnat)
    · exact Or.inr (Or.inr hnat))
  rw [hcomm', inf_top_eq, hfix'] at hbot
  refine le_antisymm hZU fun u hu => ?_
  have : (QuotientGroup.mk ⟨u, trivial⟩ : Sec ⊤ Z) ∈ secImg ⊤ Z U₀ :=
    (mk_mem_secImg hZU _).2 hu
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  exact this

omit [Finite V] in
theorem RealM.congr_sub {n : ℕ} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} {W' Y' : Subgroup V}
    (h : RealM L W Y π M) (hW : W = W') (hY : Y = Y') : RealM L W' Y' π M := by
  rw [← hW, ← hY]
  exact h

theorem RealM.one_div_le_rAV_sec {n : ℕ} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (h : RealM L W Y π M)
    (hM : M = mat ∨ M = dmat) (hn : 2 ≤ n) {B : Subgroup (MulAut V)} (hBL : B ≤ L)
    (hB2 : IsPGroup 2 ↥B) (hBne : B ≠ ⊥) (hf : B ⊓ centSec W Y = ⊥) :
    (1 / ((n : ℚ) - 1)) ≤ rAV (autSec B W Y) := by
  obtain ⟨h1, -⟩ := h.rk_le hM hBL hB2 hBne (by omega)
  have hrk := rk_autSec_eq (hBL.trans h.hLW) (hBL.trans h.hLY) hf
  have hpos : 0 < rk B := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hBne ((rk_eq_zero_iff_of_isPGroup hB2).1 h0)
  unfold rAV
  rw [hrk]
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_le_div_iff₀ hn1 (by exact_mod_cast hpos), one_mul]
  have h4 : (rk B : ℚ) ≤ ((n - 1 : ℕ) : ℚ) * (rkIdx (fixV (autSec B W Y)) : ℚ) := by
    exact_mod_cast h1
  have h5 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [h5] at h4
  linarith

theorem top_natural (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (htop : commV L = ⊤)
    (hA : IsFFStarMin G A) (hAL : A ≤ L) {I : Subgroup V} {π₁ : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hMI : L ⊔ A ≤ stabSub I) (hR₁ : RealM L I (I ⊓ fixV L) π₁ mat) {U₀ : Subgroup V}
    (hU₀inv : ∀ x ∈ L, ∀ w ∈ U₀, x w ∈ U₀) (hIU₀ : I ≤ U₀) (hU₀top : U₀ ≠ ⊤)
    (hch₀ : ∀ X : Subgroup V, (∀ x ∈ L, ∀ w ∈ X, x w ∈ X) → U₀ ≤ X → X = U₀ ∨ X = ⊤) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥L, RealM L ⊤ U₀ π mat := by
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) eL
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hquad : IsQuadratic A := B1_4_3 hV hA
  have hLU₀ := le_stabSub_of_inv hU₀inv
  have hMU₀ : L ⊔ A ≤ stabSub U₀ := by rw [hLA]; exact hLU₀
  have ctop : SecCtx G L A ⊤ U₀ := ⟨hA.1.1, hA.1.2.2.1, hA.1.2.1, le_top, le_stabSub_top _, hMU₀,
    by rw [← commV_eq_commSub, htop]; exact fun h0 => hU₀top (top_le_iff.1 h0)⟩
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcard : Nat.card (Sec ⊤ U₀) < Nat.card V := by
    have h1 := card_sec_mul (le_top : U₀ ≤ ⊤)
    rw [Subgroup.card_top] at h1
    have h2 := card_sec_mul (inf_le_left : I ⊓ fixV L ≤ I)
    rw [hR₁.card_sec] at h2
    have h3 : Nat.card I ≤ Nat.card U₀ := Subgroup.card_le_of_le hIU₀
    have h4 : 0 < Nat.card ↥(I ⊓ fixV L) := Nat.card_pos
    have h5 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    have h6 : 0 < Nat.card (Sec ⊤ U₀) := Nat.card_pos
    have hU2 : 2 ≤ Nat.card U₀ := by nlinarith
    nlinarith [Nat.mul_le_mul_left (Nat.card (Sec ⊤ U₀)) hU2]
  have hch : ∀ X : Subgroup V, L ⊔ A ≤ stabSub X → U₀ ≤ X → X ≤ ⊤ → X = U₀ ∨ X = ⊤ :=
    fun X hX hUX _ => hch₀ X (fun x hx w hw => (hX (Subgroup.mem_sup_left hx) w).2 hw) hUX
  have hAI : A ≤ stabSub I := le_sup_right.trans hMI
  have hA2 : IsPGroup 2 ↥A := hA.1.2.2.1.isPGroup
  have e1 := rkSub_ge_sec hV (le_top : U₀ ≤ ⊤) (le_stabSub_top A)
  have e2 := rkSub_top A
  have e3 := rkIdx_fixV_le_rk hV hA.1
  have e4 := rkSub_mono (A := A) hIU₀
  have e5 := rkSub_ge_sec hV (inf_le_left : I ⊓ fixV L ≤ I) hAI
  have e6 := (hR₁.rk_le (Or.inl rfl) hAL hA2 hA.1.2.1 hn1).1
  have hrk : rk (autSec A ⊤ U₀) = rk A :=
    rk_autSec_eq (le_stabSub_top A) (hAL.trans hLU₀) (sec_A_inf_centSec h ctop)
  have hpos : 0 < rk A := hA.1.isA2.rk_pos
  have hr : rAV (autSec A ⊤ U₀) ≤ 1 - 1 / ((n : ℚ) - 1) := by
    unfold rAV
    rw [hrk, div_le_iff₀ (by exact_mod_cast hpos)]
    rcases hn with rfl | rfl
    · have h7 : 3 * rkIdx (fixV (autSec A ⊤ U₀)) ≤ 2 * rk A := by omega
      have h8 : (3 : ℚ) * rkIdx (fixV (autSec A ⊤ U₀)) ≤ 2 * rk A := by exact_mod_cast h7
      norm_num
      linarith
    · have h7 : 4 * rkIdx (fixV (autSec A ⊤ U₀)) ≤ 3 * rk A := by omega
      have h8 : (4 : ℚ) * rkIdx (fixV (autSec A ⊤ U₀)) ≤ 3 * rk A := by exact_mod_cast h7
      norm_num
      linarith
  obtain ⟨π', hπ'⟩ := chief_natural hA21 hB42 hIH hV h ctop hAL hquad hcard hch hZ hn eL hr
  have hR := RealM.ofSec (le_stabSub_top L) hLU₀ (faithful_secL h ctop hZ) hπ'
  rw [secPre_top, secPre_bot le_top] at hR
  exact ⟨_, hR⟩

theorem sub_natural (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hI16 : AsI16Cover)
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hA : IsFFStarMin G A) (hAL : A ≤ L) {U₀ : Subgroup V}
    (hU₀inv : ∀ x ∈ L, ∀ w ∈ U₀, x w ∈ U₀) (hU₀top : U₀ ≠ ⊤) (hcomm : commSub U₀ L = U₀)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hRtop : RealM L ⊤ U₀ π mat)
    (hi : commV (autSec L U₀ ⊥) ∈ IrrPlus (autSec L U₀ ⊥) (⊤ : Subgroup (Sec U₀ ⊥))) :
    ∃ π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L, RealM L U₀ ⊥ π₀ mat := by
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) eL
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hquad : IsQuadratic A := B1_4_3 hV hA
  have hLU₀ := le_stabSub_of_inv hU₀inv
  have hMU₀ : L ⊔ A ≤ stabSub U₀ := by rw [hLA]; exact hLU₀
  have hAG : A ≤ G := hA.1.1
  have hA2 : IsPGroup 2 ↥A := hA.1.2.2.1.isPGroup
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hirrU := mem_irrPlus_of_sec hLU₀ hcomm hi
  obtain ⟨-, -, hlt, hirr⟩ := irr_data hirrU
  set Y₀ := U₀ ⊓ fixV L with hY₀
  have hMY₀ : L ⊔ A ≤ stabSub Y₀ := by
    rw [hLA]
    exact le_stabSub_of_inv fun x hx w hw => by rw [hw.2 x hx]; exact hw
  have hnc₁ : ¬ commSub U₀ L ≤ Y₀ := by
    rw [hcomm]
    intro hle
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  have c₁ : SecCtx G L A U₀ Y₀ := ⟨hAG, hA.1.2.2.1, hA.1.2.1, inf_le_left, hMU₀, hMY₀, hnc₁⟩
  have hnc : ¬ commSub ⊤ L ≤ U₀ := fun hle => hU₀top (by
    have := hRtop.commSub_sup (Or.inl rfl) hn2
    rwa [sup_eq_right.2 hle] at this)
  have ctop : SecCtx G L A ⊤ U₀ :=
    ⟨hAG, hA.1.2.2.1, hA.1.2.1, le_top, le_stabSub_top _, hMU₀, hnc⟩
  have hAU₀ : A ≤ stabSub U₀ := hAL.trans hLU₀
  have hAY₀ : A ≤ stabSub Y₀ := le_sup_right.trans hMY₀
  have hsum := rAV_add_le_one hV hA.1 (inf_le_left : Y₀ ≤ U₀) le_rfl le_top hAU₀
    (le_stabSub_top A) hAU₀ hAY₀ (sec_A_inf_centSec h c₁) (sec_A_inf_centSec h ctop)
  have hlow := hRtop.one_div_le_rAV_sec (Or.inl rfl) hn2 hAL hA2 hA.1.2.1
    (sec_A_inf_centSec h ctop)
  have hr : rAV (autSec A U₀ Y₀) ≤ 1 - 1 / ((n : ℚ) - 1) := by linarith
  have hr1 : rAV (autSec A U₀ Y₀) ≤ 1 := hr.trans (one_sub_le_one hn)
  have hirr₁ := isIrrSec_autSec hlt hirr hLU₀ (le_sup_left.trans hMY₀)
  rcases irr_sec_cases hA21 hB42 hV h c₁ hquad hirr₁ hZ hn eL hr1 with ⟨⟨π', hπ'⟩, -⟩ | ⟨h34, h5⟩
  swap
  · exfalso
    rcases hn with rfl | rfl
    · norm_num at hr
      linarith
    · have := h5 rfl
      norm_num at hr
      linarith
  have hR := (RealM.ofSec hLU₀ (le_sup_left.trans hMY₀) (faithful_secL h c₁ hZ) hπ').congr_sub
    secPre_top (secPre_bot (show Y₀ ≤ U₀ from inf_le_left))
  have hcommV : commV (autSec L U₀ ⊥) = ⊤ := commV_autSec_bot_eq_top hLU₀ hcomm
  have hR' := hR.toSec (bot_le : (⊥ : Subgroup V) ≤ Y₀) (stabSub_bot_le L)
  have hfix' : fixV (autSec L U₀ ⊥) = secImg U₀ ⊥ Y₀ := by
    ext s
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    rw [mk_secBot_fixed hLU₀, mk_mem_secImg bot_le]
    exact ⟨fun hu => ⟨u.2, hu⟩, fun hu => hu.2⟩
  have hnat : BinaryNaturalSL (autSec L U₀ ⊥) (commV (autSec L U₀ ⊥))
      (fixV (autSec L U₀ ⊥) ⊓ commV (autSec L U₀ ⊥)) n 1 := by
    rw [hcommV, inf_top_eq, hfix']
    exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨_, realM_mat_iff.1 hR'⟩⟩
  have hbot := hI16 (Sec U₀ ⊥) (CFSG.Quasithin.sq_eq_one_sec hV U₀ ⊥) _ hi (by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hnat)
    · exact Or.inr (Or.inr hnat))
  rw [hcommV, inf_top_eq, hfix'] at hbot
  have hY₀bot : Y₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : (QuotientGroup.mk ⟨y, hy.1⟩ : Sec U₀ ⊥) ∈ secImg U₀ ⊥ Y₀ :=
      (mk_mem_secImg bot_le _).2 hy
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    exact this
  exact ⟨_, hR.congr_sub rfl hY₀bot⟩

theorem sub_structure (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hI16 : AsI16Cover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hA : IsFFStarMin G A) (hAL : A ≤ L)
    {U₀ : Subgroup V} (hU₀inv : ∀ x ∈ L, ∀ w ∈ U₀, x w ∈ U₀) (hU₀top : U₀ ≠ ⊤) (hU₀ne : U₀ ≠ ⊥)
    (hcomm : commSub U₀ L = U₀) {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hRtop : RealM L ⊤ U₀ π mat) :
    (∃ π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L, RealM L U₀ ⊥ π₀ mat) ∨ (∃ m, SumNatDual L U₀ m) ∨
      (∃ m, (m = 4 ∨ m = 5) ∧ ∃ k, 1 ≤ k ∧ k ≤ m - 1 ∧
        DirectSumOfCopies L U₀ ⊥ (FFModel.nat (StatedSL m (ZMod 2))) k) := by
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) eL
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hLU₀ := le_stabSub_of_inv hU₀inv
  have hMU₀ : L ⊔ A ≤ stabSub U₀ := by rw [hLA]; exact hLU₀
  have c : SecCtx G L A U₀ ⊥ := ⟨hA.1.1, hA.1.2.2.1, hA.1.2.1, bot_le, hMU₀, stabSub_bot_le _,
    by rw [hcomm]; exact fun h0 => hU₀ne (le_bot_iff.1 h0)⟩
  have hcard : Nat.card (Sec U₀ ⊥) < Nat.card V := by
    have h1 := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ U₀)
    rw [Subgroup.card_bot, mul_one] at h1
    rw [h1]
    by_contra hge
    exact hU₀top (Subgroup.eq_top_of_le_card _ (not_lt.1 hge))
  have hA' : IsFFStarOffender (L ⊔ A) A := ⟨le_sup_right, hA.1.2.1, hA.1.2.2.1, hA.1.2.2.2⟩
  have hB := isFFStarOffender_autSec_bot hA' c.hMW (sec_A_inf_centSec h c)
  have hY := b51Hyp_secY h c hA21 hB
  obtain ⟨-, hcase⟩ := hIH (Sec U₀ ⊥) hcard (CFSG.Quasithin.sq_eq_one_sec hV _ _) _ _ hY
  have hfL := faithful_secL h c hZ
  have eL' : ↥(autSec L U₀ ⊥) ≃* ↥(StatedSL n (ZMod 2)) :=
    (B5.secEquiv L hLU₀ (stabSub_bot_le L) hfL).symm.trans eL
  have hcommV : commV (autSec L U₀ ⊥) = ⊤ := commV_autSec_bot_eq_top hLU₀ hcomm
  rcases hcase with hi | hii | ⟨m, -, hsum⟩ | ⟨-, m, hm, k, hk1, hk2, hdir⟩
  · exact Or.inl (sub_natural hA21 hB42 hI16 hV h hn eL hA hAL hU₀inv hU₀top hcomm hRtop hi.1)
  · exact absurd hii (not_b51Case1ii hn eL')
  · exact Or.inr (Or.inl ⟨m, sumNatDual_of_sec hLU₀ hfL hcommV hsum⟩)
  · exact Or.inr (Or.inr ⟨m, hm, k, hk1, hk2, directSumOfCopies_of_sec hLU₀ hfL hcommV hdir⟩)

end CFSG.Quasithin.B5.Ln
