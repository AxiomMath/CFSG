module

public import CFSG.Quasithin.Background.B5IrrA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B5

section Numerics

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isPGroup_sec (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) : IsPGroup 2 (Sec W U) := by
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨1, by
    rw [pow_one, ← QuotientGroup.mk_pow]
    have : (w ^ 2 : W) = 1 := Subtype.ext (hV (w : V))
    rw [this]; rfl⟩

theorem card_sec_eq_two_pow (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) :
    Nat.card (Sec W U) = 2 ^ rk (Sec W U) :=
  card_eq_two_pow_of_isPGroup (isPGroup_sec hV W U)

theorem rk_sec_add {W U : Subgroup V} (hUW : U ≤ W) : rk (Sec W U) + rk U = rk W := by
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_sec_mul hUW]

theorem rk_inf_fixV_le (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    rk ↥(W ⊓ fixV A) ≤ rk (fixV (autSec A W U)) + rk ↥(U ⊓ fixV A) := by
  have h := card_inf_fixV_le_autSec (A := A) hUW hAW
  have h1 : Nat.card ↥(W ⊓ fixV A) = 2 ^ rk ↥(W ⊓ fixV A) := card_eq_two_pow hV _
  have h2 : Nat.card ↥(U ⊓ fixV A) = 2 ^ rk ↥(U ⊓ fixV A) := card_eq_two_pow hV _
  have h3 : Nat.card (fixV (autSec A W U)) = 2 ^ rk (fixV (autSec A W U)) :=
    card_eq_two_pow_of_isPGroup (((isPGroup_sec hV W U).to_subgroup _))
  rw [h1, h2, h3, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem rk_mu_section (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    rkIdx (fixV (autSec A W U)) + (rk U - rk ↥(U ⊓ fixV A)) ≤ rk W - rk ↥(W ⊓ fixV A) := by
  have h1 := rk_sec_add hUW
  have h2 := rk_inf_fixV_le hV hUW hAW
  have h3 := rk_add_rkIdx (fixV (autSec A W U))
  have h4 : rk ↥(U ⊓ fixV A) ≤ rk U := rk_mono inf_le_left
  omega

theorem rkIdx_chain (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {Y I Y₂ W₂ : Subgroup V}
    (hYI : Y ≤ I) (hIY₂ : I ≤ Y₂) (hY₂W₂ : Y₂ ≤ W₂) (hAI : A ≤ stabSub I) (hAW₂ : A ≤ stabSub W₂)
    (hAY₂ : A ≤ stabSub Y₂) :
    rkIdx (fixV (autSec A I Y)) + rkIdx (fixV (autSec A W₂ Y₂)) ≤ rkIdx (fixV A) := by
  have e1 := rk_mu_section hV hYI hAI
  have e2 := rk_mu_section hV hY₂W₂ hAW₂
  have e3 := rk_mu_section hV hIY₂ hAY₂
  have hAtop : A ≤ stabSub (⊤ : Subgroup V) := fun g _ u => by simp
  have e4 := rk_mu_section hV (le_top : W₂ ≤ ⊤) hAtop
  have e5 := rk_add_rkIdx (fixV A)
  rw [top_inf_eq, rk_top] at e4
  omega

theorem rkIdx_fixV_le_rk (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : rkIdx (fixV A) ≤ rk A := by
  have h := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
  rw [B1.card_bot_mul_card_fixV] at h
  have hV' : Nat.card V = 2 ^ rk V := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hA2 : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.2.2.1.isPGroup
  have hF : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
  rw [hV', hA2, hF, ← pow_add] at h
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have h2 := rk_add_rkIdx (fixV A)
  omega

omit [Finite V] in
theorem rk_autSec_eq {A : Subgroup (MulAut V)} {W U : Subgroup V} (hAW : A ≤ stabSub W)
    (hAU : A ≤ stabSub U) (hf : A ⊓ centSec W U = ⊥) : rk (autSec A W U) = rk A := by
  have h := card_autSec_mul hAW hAU
  rw [hf, Subgroup.card_bot, mul_one] at h
  unfold rk
  rw [h]

theorem rAV_add_le_one (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {Y I Y₂ W₂ : Subgroup V}
    (hYI : Y ≤ I) (hIY₂ : I ≤ Y₂) (hY₂W₂ : Y₂ ≤ W₂) (hAI : A ≤ stabSub I) (hAW₂ : A ≤ stabSub W₂)
    (hAY₂ : A ≤ stabSub Y₂) (hAY : A ≤ stabSub Y) (hf₁ : A ⊓ centSec I Y = ⊥)
    (hf₂ : A ⊓ centSec W₂ Y₂ = ⊥) :
    rAV (autSec A I Y) + rAV (autSec A W₂ Y₂) ≤ 1 := by
  have h1 := rkIdx_chain hV hYI hIY₂ hY₂W₂ hAI hAW₂ hAY₂
  have h2 := rkIdx_fixV_le_rk hV hA
  have hpos : 0 < rk A := hA.isA2.rk_pos
  unfold rAV
  rw [rk_autSec_eq hAI hAY hf₁, rk_autSec_eq hAW₂ hAY₂ hf₂, ← add_div,
    div_le_one (by exact_mod_cast hpos)]
  exact_mod_cast h1.trans h2

end Numerics

section Choice

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

omit [Finite V] in
theorem commSub_commV_eq (hperf : ⁅L, L⁆ = L) : commSub (commV L) L = commV L := by
  have hU : ∀ x ∈ L, ∀ w ∈ commV L, x w ∈ commV L := fun x hx w hw =>
    commV_inv (fun l hl => L.mul_mem (L.mul_mem hx hl) (L.inv_mem hx)) w hw
  apply le_antisymm (commSub_le_of_invariant hU)
  set U' := commSub (commV L) L with hU'
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  let f : ↥L →* V ⧸ U' :=
    { toFun := fun l => QuotientGroup.mk ((l : MulAut V) v * v⁻¹)
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        have hw : (l₂ : MulAut V) v * v⁻¹ ∈ commV L :=
          Subgroup.subset_closure ⟨l₂, l₂.2, v, rfl⟩
        have h1 : (l₁ : MulAut V) ((l₂ : MulAut V) v * v⁻¹) * ((l₂ : MulAut V) v * v⁻¹)⁻¹ ∈ U' :=
          Subgroup.subset_closure ⟨l₁, l₁.2, _, hw, rfl⟩
        show (QuotientGroup.mk (((l₁ * l₂ : ↥L) : MulAut V) v * v⁻¹) : V ⧸ U') = _
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (((l₁ * l₂ : ↥L) : MulAut V) v * v⁻¹)⁻¹ *
            ((l₁ : MulAut V) v * v⁻¹ * ((l₂ : MulAut V) v * v⁻¹)) =
            ((l₁ : MulAut V) ((l₂ : MulAut V) v * v⁻¹) * ((l₂ : MulAut V) v * v⁻¹)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          cgroup
        rw [e]
        exact U'.inv_mem h1 }
  have hker : commutator ↥L ≤ f.ker := Abelianization.commutator_subset_ker f
  have hperf' : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have h1 : (⟨x, hx⟩ : ↥L) ∈ f.ker := hker (by rw [hperf'.commutator_eq_top]; trivial)
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem commutator_L_A_eq (h : B51Hyp G L) (hAG : A ≤ G) (hA2 : IsPGroup 2 A) (hAne : A ≠ ⊥) :
    ⁅L, A⁆ = L := by
  have hn : ∀ b ∈ A, ∀ k ∈ L, b * k * b⁻¹ ∈ L := fun b hb k hk => normal_L h b (hAG hb) k hk
  rcases B1Red.commutator_eq_or_commute (Or.inl (B1Red.isQuasisimple_to_open (quasi_L h))) hn
    with h1 | h1
  · exact h1
  · exfalso
    have hA' : A ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun l hl => (h1 a ha l hl).symm
    have h2 := two_inf_centralizer_eq_bot h hAG hA2
    exact hAne (eq_bot_iff.2 (h2 ▸ le_inf le_rfl hA'))

omit [Finite V] in
theorem sup_le_stabSub {J : Subgroup V} (hL : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J)
    (hA : ∀ a ∈ A, ∀ w ∈ J, a w ∈ J) : L ⊔ A ≤ stabSub J :=
  sup_le (fun x hx => mem_stabSub_of_inv (hL x hx) (hL x⁻¹ (L.inv_mem hx)))
    (fun a ha => mem_stabSub_of_inv (hA a ha) (hA a⁻¹ (A.inv_mem ha)))

theorem exists_chief_pair (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : ¬ commV L ∈ IrrPlus L ⊤) (hA : IsFFStarMin G A) :
    ∃ I Y₂ W₂ : Subgroup V, I ∈ IrrPlus L ⊤ ∧ L ⊔ A ≤ stabSub I ∧ I ≤ Y₂ ∧ Y₂ ≤ W₂ ∧
      L ⊔ A ≤ stabSub Y₂ ∧ L ⊔ A ≤ stabSub W₂ ∧ ¬ commSub W₂ L ≤ Y₂ ∧
      (∀ X, L ⊔ A ≤ stabSub X → Y₂ ≤ X → X ≤ W₂ → X = Y₂ ∨ X = W₂) := by
  classical
  have hAG : A ≤ G := hA.1.1
  have hA2 : IsPGroup 2 A := hA.1.2.2.1.isPGroup
  have hLq := quasi_L h
  have hLperf' : Group.IsPerfect ↥L := hLq.1
  have hLperf : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open hLq)
  have hLne : commV L ≠ ⊥ := by
    intro h0
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h0
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    apply hl
    apply Subtype.ext
    ext v
    exact h0 (Subgroup.mem_top v) l l.2
  obtain ⟨I, hI⟩ := B1Red.exists_mem_irrPlus hLperf hLne
  have hE : oTwoUpper L = L := B1Red.oTwoUpper_eq_of_perfect hLperf'
  have hCF := B1Red.allTwoChiefFactorsCentral_of_quasisimple (B1Red.isQuasisimple_to_open hLq)
  have hLA := commutator_L_A_eq h hAG hA2 hA.1.2.1
  have hIA : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I := by
    intro a ha w hw
    have h1 := B1_5_3 hV hA hE hLA hCF a ha I hI
    have h2 : a w ∈ I.map a.toMonoidHom := Subgroup.mem_map_of_mem _ hw
    rwa [h1] at h2
  obtain ⟨hIL, hIcomm, hIlt, hIirr⟩ := irr_data hI
  have hMI : L ⊔ A ≤ stabSub I := sup_le_stabSub hIL hIA
  have hnotU : ¬ commV L ≤ I := by
    intro hle
    apply hU
    have h1 : I ≤ commV L := by
      rw [commV_eq_commSub]
      calc I = commSub I L := hIcomm.symm
        _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
    rw [le_antisymm hle h1]; exact hI
  let 𝒴 : Set (Subgroup V) := {J | L ⊔ A ≤ stabSub J ∧ I ≤ J ∧ ¬ commV L ≤ J}
  have h𝒴 : 𝒴.Nonempty := ⟨I, hMI, le_rfl, hnotU⟩
  obtain ⟨Y₂, hY₂, hYmax⟩ := Set.exists_max_image 𝒴 (fun J => Nat.card J) (Set.toFinite 𝒴) h𝒴
  let 𝒲 : Set (Subgroup V) := {J | L ⊔ A ≤ stabSub J ∧ Y₂ ≤ J ∧ ¬ commSub J L ≤ Y₂}
  have hMtop : L ⊔ A ≤ stabSub (⊤ : Subgroup V) := fun g _ u => by simp
  have h𝒲 : 𝒲.Nonempty := ⟨⊤, hMtop, le_top, by
    rw [← commV_eq_commSub]; exact hY₂.2.2⟩
  obtain ⟨W₂, hW₂, hWmin⟩ := Set.exists_min_image 𝒲 (fun J => Nat.card J) (Set.toFinite 𝒲) h𝒲
  refine ⟨I, Y₂, W₂, hI, hMI, hY₂.2.1, hW₂.2.1, hY₂.1, hW₂.1, hW₂.2.2, ?_⟩
  intro X hMX hYX hXW
  by_cases hXW' : X = W₂
  · exact Or.inr hXW'
  · left
    have h1 : commSub X L ≤ Y₂ := by
      by_contra hcon
      have hmem : X ∈ 𝒲 := ⟨hMX, hYX, hcon⟩
      exact hXW' (Subgroup.eq_of_le_of_card_ge hXW (hWmin X hmem))
    by_contra hne
    have hlt : Y₂ < X := lt_of_le_of_ne hYX (Ne.symm hne)
    have hnotmem : X ∉ 𝒴 := fun hmem =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hYX (hYmax X hmem))
    have hUX : commV L ≤ X := by
      by_contra hcon
      exact hnotmem ⟨hMX, hY₂.2.1.trans hYX, hcon⟩
    apply hY₂.2.2
    calc commV L = commSub (commV L) L := (commSub_commV_eq hLperf).symm
      _ ≤ commSub X L := commSub_mono hUX le_rfl
      _ ≤ Y₂ := h1

end Choice

end B5

end CFSG.Quasithin
