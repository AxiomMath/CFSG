module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotTransvA
import CFSG.Quasithin.Background.Harris.R1.PerfectAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {U : Type} [CommGroup U] [Finite U]

theorem s15_semiBot_transv_struct (hU : ∀ u : U, u ^ 2 = 1) {t : MulAut U}
    (ht : InducesTransvection t (⊤ : Subgroup U)) :
    ∃ c : U, c ≠ 1 ∧ (∃ u, t u ≠ u) ∧ (∀ u, t u = u ∨ t u = u * c) ∧ t c = c ∧ t * t = 1 := by
  obtain ⟨c, hc1, htc, hN, hC⟩ := s15_Three_transv_cases hU ht
  refine ⟨c, hc1, ?_, hN, htc, ?_⟩
  · by_contra h
    have hfix : ∀ u, t u = u := by
      intro u
      by_contra hu
      exact h ⟨u, hu⟩
    have ht1 : t = 1 := by ext u; exact hfix u
    have hbot : commSub (⊤ : Subgroup U) (Subgroup.zpowers t) = ⊥ := by
      rw [ht1, Subgroup.zpowers_one_eq_bot, commSub_eq_bot_iff]
      intro w hw x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx, MulAut.one_apply]
    rw [hbot] at hC
    refine hc1 ?_
    have hc : c ∈ (⊥ : Subgroup U) := by rw [hC]; exact Subgroup.mem_zpowers c
    rwa [Subgroup.mem_bot] at hc
  · ext u
    simp only [MulAut.mul_apply, MulAut.one_apply]
    rcases hN u with h | h
    · simpa [h]
    · have hcc : c * c = 1 := by rw [← pow_two]; exact hU c
      rw [h, map_mul, htc, h, mul_assoc, hcc, mul_one]

theorem s15_semiBot_comm_values_small (hU : ∀ u : U, u ^ 2 = 1) {t : MulAut U} {c : U}
    (hN : ∀ u, t u = u ∨ t u = u * c) (htc : t c = c) (htt : t * t = 1) (a : MulAut U) :
    ∃ S : Subgroup U, Nat.card S ≤ 4 ∧ ∀ u, (t * a * t⁻¹ * a⁻¹) u * u⁻¹ ∈ S := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine ⟨Subgroup.zpowers c ⊔ Subgroup.zpowers (a c), ?_, ?_⟩
  · have h1 : Nat.card ↥(Subgroup.zpowers c) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (hU c))
    have h2 : Nat.card ↥(Subgroup.zpowers (a c)) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.2 (hU (a c)))
    have hinf : 0 < Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (a c)) := by
      haveI : Nonempty ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (a c)) :=
        ⟨⟨1, Subgroup.one_mem _⟩⟩
      exact Nat.card_pos
    have hmul := card_sup_mul_card_inf (Subgroup.zpowers c) (Subgroup.zpowers (a c))
    calc Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (a c))
        ≤ Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (a c)) *
            Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (a c)) :=
          Nat.le_mul_of_pos_right _ hinf
      _ = Nat.card ↥(Subgroup.zpowers c) * Nat.card ↥(Subgroup.zpowers (a c)) := hmul
      _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
      _ = 4 := by norm_num
  · intro u
    have hcS : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (a c) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    have hacS : a c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (a c) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (a c))
    have h1S : (1 : U) ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (a c) := Subgroup.one_mem _
    have htu : t u * u⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (a c) := by
      rcases hN u with h | h
      · rw [h, mul_inv_cancel]; exact h1S
      · rw [h, s15_semiBot_conj_eq u c]; exact hcS
    have htac : t (a c) ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (a c) := by
      rcases hN (a c) with h | h
      · rw [h]; exact hacS
      · rw [h]; exact Subgroup.mul_mem _ hacS hcS
    have hval : (t * a * t⁻¹ * a⁻¹) u * u⁻¹ = t (a (t (a⁻¹ u))) * u⁻¹ := by
      rw [ht']; simp only [MulAut.mul_apply]
    rw [hval]
    have haw : a (a⁻¹ u) = u := MulAut.apply_inv_self U a u
    rcases hN (a⁻¹ u) with hw | hw
    · have h1 : t (a (t (a⁻¹ u))) = t u := by rw [hw, haw]
      rw [h1]; exact htu
    · have h2 : t (a (t (a⁻¹ u))) = t u * t (a c) := by
        rw [hw, map_mul, map_mul, haw]
      rw [h2, s15_semiBot_mul_comm_mul]
      exact Subgroup.mul_mem _ htu htac

theorem s15_semiBot_c_mem_commSub {A A₀ : Subgroup (MulAut U)} (hUA : commSub ⊤ A = ⊤)
    (hA₀A : ∀ a ∈ A, ∀ x ∈ A₀, a * x * a⁻¹ ∈ A₀) {t : MulAut U} {c : U} (hex : ∃ u, t u ≠ u)
    (hc1 : c ≠ 1) (hN : ∀ u, t u = u ∨ t u = u * c) (hA₀t : ∀ x ∈ A₀, t * x * t⁻¹ ∈ A₀)
    (hcomm : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ A₀) : c ∈ commSub (⊤ : Subgroup U) A₀ := by
  let U₁ : Subgroup U := commSub (⊤ : Subgroup U) A₀
  by_contra hcU
  let N : U →* U := s15_semiBot_D t
  have hN_apply : ∀ u, N u = t u * u⁻¹ := fun u => s15_semiBot_D_apply t u
  have hN01 : ∀ u, N u = 1 ∨ N u = c := by
    intro u
    rcases hN u with h | h
    · left; rw [hN_apply, h, mul_inv_cancel]
    · right; rw [hN_apply, h, s15_semiBot_conj_eq u c]
  have hA_stab : ∀ a ∈ A, ∀ z ∈ U₁, a z ∈ U₁ := by
    intro a ha z hz
    refine Subgroup.closure_induction (p := fun z _ => a z ∈ U₁) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨x, hx, w, -, rfl⟩
      refine Subgroup.subset_closure ⟨a * x * a⁻¹, hA₀A a ha x hx, a w, Subgroup.mem_top _, ?_⟩
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
    · rw [map_one]; exact U₁.one_mem
    · intro x y _ _ hx hy; rw [map_mul]; exact U₁.mul_mem hx hy
    · intro x _ hx; rw [map_inv]; exact U₁.inv_mem hx
  have hkey : ∀ a ∈ A, ∀ w : U, t (a w) * (a (t w))⁻¹ ∈ U₁ := by
    intro a ha w
    have hxv : (t * a * t⁻¹ * a⁻¹) (a (t w)) = t (a w) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    exact Subgroup.subset_closure
      ⟨t * a * t⁻¹ * a⁻¹, hcomm a ha, a (t w), Subgroup.mem_top _, by rw [hxv]⟩
  obtain ⟨u₀, hu₀⟩ := hex
  have hu₀N : t u₀ = u₀ * c := by
    rcases hN u₀ with h | h
    · exact absurd h hu₀
    · exact h
  have hd1 : ∀ a ∈ A, a c * c⁻¹ ∈ U₁ := by
    intro a ha
    have hmem := hkey a ha u₀
    have hau : a (t u₀) = a u₀ * a c := by rw [hu₀N, map_mul]
    rw [hau] at hmem
    rcases hN (a u₀) with h | h
    · rw [h] at hmem
      have hac : a c ∈ U₁ := by
        have hinv := U₁.inv_mem hmem
        have heq : (a u₀ * (a u₀ * a c)⁻¹)⁻¹ = a c := by
          rw [s15_semiBot_mul_mul_inv_self (a u₀) (a c), inv_inv]
        rwa [heq] at hinv
      have hcU₁ : c ∈ U₁ := by
        have h2 := hA_stab a⁻¹ (A.inv_mem ha) (a c) hac
        rwa [show a⁻¹ (a c) = c from by simp] at h2
      exact absurd hcU₁ hcU
    · rw [h] at hmem
      have heq : (a u₀ * c) * (a u₀ * a c)⁻¹ = (a c * c⁻¹)⁻¹ := by
        rw [s15_semiBot_mul_mul_inv (a u₀) (a c) c, mul_inv_rev, inv_inv]
      rw [heq] at hmem
      simpa using U₁.inv_mem hmem
  have hd2 : ∀ a ∈ A, ∀ w : U, N (a w * w⁻¹) ∈ U₁ := by
    intro a ha w
    have hkey' : N (a w) * (a (N w))⁻¹ ∈ U₁ := by
      have h := hkey a ha w
      have h1 : N (a w) = t (a w) * (a w)⁻¹ := hN_apply (a w)
      have h2 : a (N w) = a (t w) * (a w)⁻¹ := by
        rw [hN_apply w, map_mul, map_inv]
      rw [h1, h2]
      have heq : (t (a w) * (a w)⁻¹) * (a (t w) * (a w)⁻¹)⁻¹ =
          t (a w) * (a (t w))⁻¹ := by
        rw [mul_inv_rev, inv_inv]; group
      rw [heq]; exact h
    have hsecond : a (N w) * (N w)⁻¹ ∈ U₁ := by
      rcases hN01 w with h | h
      · rw [h, map_one, inv_one, mul_one]; exact U₁.one_mem
      · rw [h]; exact hd1 a ha
    rw [show N (a w * w⁻¹) = N (a w) * (N w)⁻¹ from by rw [map_mul, map_inv]]
    rw [show N (a w) * (N w)⁻¹ =
        (N (a w) * (a (N w))⁻¹) * (a (N w) * (N w)⁻¹) from by group]
    exact U₁.mul_mem hkey' hsecond
  have hle : commSub (⊤ : Subgroup U) A ≤ U₁.comap N := by
    rw [commSub, Subgroup.closure_le]
    rintro z ⟨a, ha, w, -, rfl⟩
    exact hd2 a ha w
  have hcU₁ : c ∈ U₁ := by
    have hz : N u₀ ∈ U₁ := by
      have := hle (by rw [hUA]; exact Subgroup.mem_top u₀)
      rwa [Subgroup.mem_comap] at this
    have hNu : N u₀ = c := by rw [hN_apply, hu₀N, s15_semiBot_conj_eq u₀ c]
    rwa [hNu] at hz
  exact hcU hcU₁

theorem s15_semiBot_fixes_c (hU : ∀ u : U, u ^ 2 = 1) {A B : Subgroup (MulAut U)}
    (hAB : ⁅A, B⁆ = ⊥) (hB : ⁅B, B⁆ = B) (hUA : commSub ⊤ A = ⊤) {t : MulAut U} {c : U}
    (hc1 : c ≠ 1) (hex : ∃ u, t u ≠ u) (hN : ∀ u, t u = u ∨ t u = u * c) (htc : t c = c)
    (htt : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : ∀ b ∈ B, b c = c := by
  have hbA : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  haveI : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.2 hB
  have hF2 : ∀ a ∈ A, ∀ b ∈ B, ∀ u,
      b ((t * a * t⁻¹ * a⁻¹) u * u⁻¹) = (t * a * t⁻¹ * a⁻¹) u * u⁻¹ := by
    intro a ha b hb u
    have hxA : t * a * t⁻¹ * a⁻¹ ∈ A := A.mul_mem (htA a ha) (A.inv_mem ha)
    obtain ⟨S₄, hS₄card, hS₄mem⟩ := s15_semiBot_comm_values_small hU hN htc htt a
    let S₀ : Subgroup U :=
      Subgroup.closure (Set.range fun u => (t * a * t⁻¹ * a⁻¹) u * u⁻¹)
    have hS₀le : S₀ ≤ S₄ := by
      change Subgroup.closure (Set.range fun u => (t * a * t⁻¹ * a⁻¹) u * u⁻¹) ≤ S₄
      rw [Subgroup.closure_le]
      rintro z ⟨u, rfl⟩
      exact hS₄mem u
    have hS₀card : Nat.card S₀ ≤ 4 :=
      (Nat.card_le_card_of_injective (Subgroup.inclusion hS₀le)
        (Subgroup.inclusion_injective hS₀le)).trans hS₄card
    have hstab : ∀ k : ↥B, ∀ z ∈ S₀, B.subtype k z ∈ S₀ := by
      intro k z hz
      refine Subgroup.closure_induction (p := fun z _ => B.subtype k z ∈ S₀) ?_ ?_ ?_ ?_ hz
      · rintro z ⟨w, rfl⟩
        change (k : MulAut U) ((t * a * t⁻¹ * a⁻¹) w * w⁻¹) ∈ S₀
        have hbk : (k : MulAut U) * (t * a * t⁻¹ * a⁻¹) =
            (t * a * t⁻¹ * a⁻¹) * (k : MulAut U) :=
          (hbA (t * a * t⁻¹ * a⁻¹) hxA (k : MulAut U) k.2).symm
        have heq : (k : MulAut U) ((t * a * t⁻¹ * a⁻¹) w * w⁻¹) =
            (t * a * t⁻¹ * a⁻¹) ((k : MulAut U) w) * ((k : MulAut U) w)⁻¹ := by
          rw [map_mul, map_inv, ← MulAut.mul_apply, hbk, MulAut.mul_apply]
        rw [heq]
        exact Subgroup.subset_closure ⟨(k : MulAut U) w, rfl⟩
      · change B.subtype k 1 ∈ S₀
        rw [map_one]
        exact S₀.one_mem
      · intro x y hx hy hpx hpy
        rw [map_mul]
        exact S₀.mul_mem hpx hpy
      · intro x hx hpx
        rw [map_inv]
        exact S₀.inv_mem hpx
    have hfixall :=
      CFSG.Quasithin.Background.Harris.R1.perfect_fixes_of_card_le_four
        (K := ↥B) (N := U) B.subtype S₀ hstab hS₀card
    exact hfixall ⟨b, hb⟩ ((t * a * t⁻¹ * a⁻¹) u * u⁻¹)
      (Subgroup.subset_closure ⟨u, rfl⟩)
  let A₀ : Subgroup (MulAut U) :=
    { carrier := {x | x ∈ A ∧ ∀ b ∈ B, ∀ u, b (x u * u⁻¹) = x u * u⁻¹}
      one_mem' := by
        refine ⟨A.one_mem, ?_⟩
        intro b hb u
        rw [MulAut.one_apply, mul_inv_cancel, map_one]
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hxA, hxfix⟩ := hx
        obtain ⟨hyA, hyfix⟩ := hy
        refine ⟨A.mul_mem hxA hyA, ?_⟩
        intro b hb u
        have hsplit : (x * y) u * u⁻¹ = (x (y u) * (y u)⁻¹) * (y u * u⁻¹) := by
          rw [MulAut.mul_apply, mul_assoc, ← mul_assoc ((y u)⁻¹) (y u) (u⁻¹),
            inv_mul_cancel, one_mul]
        rw [hsplit, map_mul, hxfix b hb (y u), hyfix b hb u]
      inv_mem' := by
        intro x hx
        obtain ⟨hxA, hxfix⟩ := hx
        refine ⟨A.inv_mem hxA, ?_⟩
        intro b hb u
        have hfix := hxfix b hb (x⁻¹ u)
        have hxu : x (x⁻¹ u) = u := MulAut.apply_inv_self U x u
        rw [hxu] at hfix
        have hz : (u * (x⁻¹ u)⁻¹)⁻¹ = x⁻¹ u * u⁻¹ := by rw [mul_inv_rev, inv_inv]
        rw [← hz, map_inv, hfix] }
  have hA₀A : ∀ a ∈ A, ∀ x ∈ A₀, a * x * a⁻¹ ∈ A₀ := by
    intro a ha x hx
    obtain ⟨hxA, hxfix⟩ := hx
    refine ⟨A.mul_mem (A.mul_mem ha hxA) (A.inv_mem ha), ?_⟩
    intro b hb u
    set v : U := a⁻¹ u with hv
    have hav : a v = u := by rw [hv]; exact MulAut.apply_inv_self U a u
    have hval : (a * x * a⁻¹) u * u⁻¹ = a (x v * v⁻¹) := by
      have h1 : (a * x * a⁻¹) u = a (x v) := by
        simp only [MulAut.mul_apply]
        rw [← hv]
      have h2 : a (x v) * u⁻¹ = a (x v * v⁻¹) := by rw [map_mul, map_inv, hav]
      rw [h1, h2]
    have hcomm' : b (a (x v * v⁻¹)) = a (x v * v⁻¹) := by
      rw [← MulAut.mul_apply, ← hbA a ha b hb, MulAut.mul_apply, hxfix b hb v]
    rw [hval, hcomm']
  have hA₀t : ∀ x ∈ A₀, t * x * t⁻¹ ∈ A₀ := by
    intro x hx
    have h1 : t * x * t⁻¹ * x⁻¹ ∈ A₀ :=
      ⟨A.mul_mem (htA x hx.1) (A.inv_mem hx.1), fun b hb u => hF2 x hx.1 b hb u⟩
    have h2 : (t * x * t⁻¹ * x⁻¹) * x = t * x * t⁻¹ := by group
    rw [← h2]
    exact A₀.mul_mem h1 hx
  have hcommA : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ A₀ := by
    intro a ha
    refine ⟨A.mul_mem (htA a ha) (A.inv_mem ha), ?_⟩
    intro b hb u
    exact hF2 a ha b hb u
  have hcA₀ : c ∈ commSub (⊤ : Subgroup U) A₀ :=
    s15_semiBot_c_mem_commSub hUA hA₀A hex hc1 hN hA₀t hcommA
  have hle : commSub (⊤ : Subgroup U) A₀ ≤ fixV B := by
    rw [commSub, Subgroup.closure_le]
    rintro z ⟨x, hx, w, -, rfl⟩
    exact mem_fixV.2 (fun b hb => hx.2 b hb w)
  intro b hb
  exact mem_fixV.1 (hle hcA₀) b hb

theorem s15_semiBot_N_trivial (hU : ∀ u : U, u ^ 2 = 1) {A B : Subgroup (MulAut U)}
    (hAB : ⁅A, B⁆ = ⊥) (hUA : commSub ⊤ A = ⊤) (hUB : commSub ⊤ B = ⊤) {t : MulAut U} {c : U}
    (hc1 : c ≠ 1) (hex : ∃ u, t u ≠ u) (hN : ∀ u, t u = u ∨ t u = u * c) (htc : t c = c)
    (htt : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hBc : ∀ b ∈ B, b c = c) : False := by
  have hbA : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcc : c * c = 1 := by rw [← pow_two]; exact hU c
  let N : U →* U := s15_semiBot_D t
  have hN_apply : ∀ u, N u = t u * u⁻¹ := fun u => s15_semiBot_D_apply t u
  have hN01 : ∀ u, N u = 1 ∨ N u = c := by
    intro u
    rcases hN u with h | h
    · left; rw [hN_apply, h, mul_inv_cancel]
    · right; rw [hN_apply, h, s15_semiBot_conj_eq u c]
  have htN : ∀ w : U, t w = w * N w := by
    intro w
    rw [hN_apply w, ← mul_assoc, s15_semiBot_conj_eq]
  obtain ⟨u₁, hu₁⟩ : ∃ u, t u = u * c := by
    obtain ⟨u, hu⟩ := hex
    rcases hN u with h | h
    · exact absurd h hu
    · exact ⟨u, h⟩
  have hε1 : ∀ b ∈ B, ∀ u, N u * N (b⁻¹ u) = 1 :=
    s15_semiBot_epsilon_trivial hU hAB hUA hc1 hN htc htt htA hBc
  have hNtop : ∀ z, N z = 1 := by
    have hgen : ∀ b ∈ B, ∀ u, N (b u * u⁻¹) = 1 := by
      intro b hb u
      have h := hε1 b⁻¹ (B.inv_mem hb) u
      have hbN : N (b u) = N u := by
        have h1 : N (b u) = (N u)⁻¹ := by
          have h2 := mul_eq_one_iff_inv_eq.mp h
          simpa using h2.symm
        rw [h1]
        rcases hN01 u with h3 | h3
        · rw [h3]; simp
        · rw [h3]; exact inv_eq_of_mul_eq_one_right hcc
      rw [map_mul, map_inv, hbN, mul_inv_cancel]
    have hker : commSub (⊤ : Subgroup U) B ≤ N.ker := by
      rw [commSub, Subgroup.closure_le]
      rintro z ⟨b, hb, u, -, rfl⟩
      exact MonoidHom.mem_ker.2 (hgen b hb u)
    intro z
    exact MonoidHom.mem_ker.1 (hker (by rw [hUB]; exact Subgroup.mem_top z))
  have h1 : N u₁ = 1 := hNtop u₁
  have h2 : N u₁ = c := by rw [hN_apply, hu₁, s15_semiBot_conj_eq u₁ c]
  rw [h2] at h1
  exact hc1 h1

theorem s15_semiBot_noTransv (hU : ∀ u : U, u ^ 2 = 1) {A B : Subgroup (MulAut U)}
    (hAB : ⁅A, B⁆ = ⊥) (hB : ⁅B, B⁆ = B) (hUA : commSub ⊤ A = ⊤) (hUB : commSub ⊤ B = ⊤)
    {t : MulAut U} (ht : InducesTransvection t (⊤ : Subgroup U))
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : False := by
  obtain ⟨c, hc1, hex, hN, htc, htt⟩ := s15_semiBot_transv_struct hU ht
  exact s15_semiBot_N_trivial hU hAB hUA hUB hc1 hex hN htc htt htA
    (s15_semiBot_fixes_c hU hAB hB hUA hc1 hex hN htc htt htA)

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
