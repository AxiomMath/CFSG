module

public import CFSG.Quasithin.Background.SmithB57EG

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC CFSG.Quasithin.S143 CFSG.Quasithin.B3 Equiv
open scoped commutatorElement

section General

theorem exists_pair_of_three_le {Γ : Type*} [Group Γ] {H : Subgroup Γ} [Finite H]
    (h : 3 ≤ Nat.card H) : ∃ a ∈ H, ∃ b ∈ H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have hne : H ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  by_contra hcon
  push Not at hcon
  have hcases : ∀ x : H, (x : Γ) = 1 ∨ (x : Γ) = a := by
    intro x
    by_cases hx : (x : Γ) = 1
    · exact Or.inl hx
    · exact Or.inr (hcon x x.2 a ha hx ha1')
  have hinj : Function.Injective (fun x : H => decide ((x : Γ) = a)) := by
    intro x y hxy
    have hxy' : decide ((x : Γ) = a) = decide ((y : Γ) = a) := hxy
    apply Subtype.ext
    rcases hcases x with hx | hx <;> rcases hcases y with hy | hy
    · rw [hx, hy]
    · exfalso
      have h1 : decide ((x : Γ) = a) = true := by rw [hxy', hy]; exact decide_eq_true rfl
      rw [hx] at h1
      exact ha1' (of_decide_eq_true h1).symm
    · exfalso
      have h1 : decide ((y : Γ) = a) = true := by rw [← hxy', hx]; exact decide_eq_true rfl
      rw [hy] at h1
      exact ha1' (of_decide_eq_true h1).symm
    · rw [hx, hy]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

variable {V : Type} [CommGroup V]

theorem fix_of_perfect {L : Subgroup (MulAut V)} (hperf : commutator ↥L = ⊤) {C : Subgroup V}
    (hC : ∀ l ∈ L, ∀ c ∈ C, l c = c) {v : V} (hv : ∀ l ∈ L, l v * v⁻¹ ∈ C) :
    ∀ l ∈ L, l v = v := by
  let φ : ↥L →* ↥C :=
    { toFun := fun l => ⟨(l : MulAut V) v * v⁻¹, hv l l.2⟩
      map_one' := by
        apply Subtype.ext
        show (1 : MulAut V) v * v⁻¹ = 1
        rw [MulAut.one_apply, mul_inv_cancel]
      map_mul' := fun l l' => by
        apply Subtype.ext
        show ((l : MulAut V) * l') v * v⁻¹ =
          ((l : MulAut V) v * v⁻¹) * ((l' : MulAut V) v * v⁻¹)
        have h1 : (l : MulAut V) ((l' : MulAut V) v * v⁻¹) = (l' : MulAut V) v * v⁻¹ :=
          hC _ l.2 _ (hv l' l'.2)
        have h2 : (l : MulAut V) ((l' : MulAut V) v) =
            ((l' : MulAut V) v * v⁻¹) * (l : MulAut V) v := by
          conv_lhs => rw [← inv_mul_cancel_right ((l' : MulAut V) v) v]
          rw [map_mul, h1]
        rw [MulAut.mul_apply, h2, mul_assoc, mul_comm] }
  have hker : commutator ↥L ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hperf] at hker
  intro l hl
  have h := hker (Subgroup.mem_top ⟨l, hl⟩)
  rw [MonoidHom.mem_ker] at h
  have h' := congrArg Subtype.val h
  exact mul_inv_eq_one.1 h'

end General

variable {V : Type} [CommGroup V] [Finite V]

namespace SixData

variable {G L A : Subgroup (MulAut V)} {S : Hyp G L} (D : SixData S A)
include D

theorem move_mem (x : LG 6) (w : V) : D.f x w * w⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨D.f x, (D.mem_L_iff x).2 x.2, w, rfl⟩

@[expose] def mv (x : LG 6) (w : V) : ↥(commV L) := ⟨D.f x w * w⁻¹, D.move_mem x w⟩

@[expose] noncomputable def der (w : V) : LG 6 → N6 := fun x => D.theta (D.mv x w)

theorem der_isDer (w : V) : IsDer n6ActL (D.der w) := by
  intro x y
  have hmem : D.f x (D.mv y w : V) ∈ commV L :=
    FFC.commV_invariant (S.conj_mem D.hP4 (D.f_mem_G x)) (D.mv y w).2
  have e : D.mv (x * y) w = ⟨D.f x (D.mv y w : V), hmem⟩ * D.mv x w := by
    apply Subtype.ext
    show D.f ((x : Perm (Fin 6)) * y) w * w⁻¹ = D.f x (D.f y w * w⁻¹) * (D.f x w * w⁻¹)
    rw [D.f_mul, MulAut.mul_apply, map_mul, map_inv]
    group
  show D.theta (D.mv (x * y) w) = D.theta (D.mv x w) * n6Act x (D.theta (D.mv y w))
  rw [e, map_mul, D.theta_equiv x (D.mv y w) hmem, mul_comm]

theorem der_conj {w : V} {s : Perm (Fin 6)} (hs : D.f s w = w) (hs' : D.f s⁻¹ w = w)
    (x y : LG 6) (hy : (y : Perm (Fin 6)) = s * x * s⁻¹) :
    D.der w y = n6Act s (D.der w x) := by
  have hmem : D.f s (D.mv x w : V) ∈ commV L :=
    FFC.commV_invariant (S.conj_mem D.hP4 (D.f_mem_G s)) (D.mv x w).2
  have e : D.mv y w = ⟨D.f s (D.mv x w : V), hmem⟩ := by
    apply Subtype.ext
    show D.f y w * w⁻¹ = D.f s (D.f x w * w⁻¹)
    rw [hy, D.f_mul, D.f_mul, MulAut.mul_apply, MulAut.mul_apply, hs', map_mul, map_inv, hs]
  show D.theta (D.mv y w) = n6Act s (D.theta (D.mv x w))
  rw [e, D.theta_equiv s (D.mv x w) hmem]

theorem four_le_card_inf : 4 ≤ Nat.card ↥(alternatingGroup (Fin 6) ⊓ D.abar) := by
  have h8 : Nat.card D.abar = 8 := by rw [D.card_abar]; exact D.offender_eq.1
  have hrel := Subgroup.relIndex_mul_card (alternatingGroup (Fin 6)) D.abar
  have hdvd : (alternatingGroup (Fin 6)).relIndex D.abar ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin 6)) D.abar
    rwa [alternatingGroup.index_eq_two] at this
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  rw [h8] at hrel
  by_contra h
  have h3 : Nat.card ↥(alternatingGroup (Fin 6) ⊓ D.abar) ≤ 3 := by omega
  have := Nat.mul_le_mul hle h3
  omega

theorem split_W :
    fixV (pCoreOf 3 G) = commV L ⊔ (fixV (pCoreOf 3 G) ⊓ fixV (L ⊔ A)) := by
  refine le_antisymm ?_ (sup_le D.U_le_W inf_le_left)
  intro w hw
  obtain ⟨-, h4, -, hsplit, hsurj⟩ := D.offender_eq
  rw [← hsplit] at hw
  obtain ⟨u₁, hu₁, w₀, hw₀, rfl⟩ := Subgroup.mem_sup.1 hw
  have hw₀A : ∀ g ∈ A, g w₀ = w₀ := hw₀.2
  obtain ⟨σ₀, hσ₀, τ₀, hτ₀, hσ1, hτ1, hστ⟩ := exists_pair_of_three_le
    (le_trans (by norm_num) D.four_le_card_inf)
  set σ : LG 6 := ⟨σ₀, hσ₀.1⟩ with hσ
  set τ : LG 6 := ⟨τ₀, hτ₀.1⟩ with hτ
  have hder1 : ∀ x : LG 6, (x : Perm (Fin 6)) ∈ D.abar → D.der w₀ x = 1 := by
    intro x hx
    have e : D.mv x w₀ = 1 := by
      apply Subtype.ext
      show D.f x w₀ * w₀⁻¹ = 1
      rw [hw₀A _ ((D.mem_abar).1 hx), mul_inv_cancel]
    show D.theta (D.mv x w₀) = 1
    rw [e, map_one]
  have h4' : 4 ≤ Nat.card ↥(fixN6 (Subgroup.zpowers (σ : Perm (Fin 6))) ⊓
      fixN6 (Subgroup.zpowers (τ : Perm (Fin 6)))) := by
    rw [← h4]
    exact Subgroup.card_le_of_le (le_inf (fixN6_mono (Subgroup.zpowers_le.2 hσ₀.2))
      (fixN6_mono (Subgroup.zpowers_le.2 hτ₀.2)))
  obtain ⟨a, ha⟩ := isPrin_of_vanish (D.der_isDer w₀) (σ := σ) (τ := τ)
    (Subtype.ext (D.abar_sq _ hσ₀.2)) (Subtype.ext (D.abar_sq _ hτ₀.2))
    (fun h => hσ1 (congrArg Subtype.val h)) (fun h => hτ1 (congrArg Subtype.val h))
    (fun h => hστ (congrArg Subtype.val h)) (Subtype.ext (D.abar_comm _ hσ₀.2 _ hτ₀.2)) h4'
    (hder1 σ hσ₀.2) (hder1 τ hτ₀.2)
  have haA : a ∈ fixN6 D.abar := by
    rw [mem_fixN6]
    intro s hs
    have hs' : s⁻¹ ∈ D.abar := D.abar.inv_mem hs
    set b := n6Act s a with hb
    have hfix : ∀ y ∈ alternatingGroup (Fin 6), n6Act y (b * a⁻¹) = b * a⁻¹ := by
      intro y hy
      have hx : s⁻¹ * y * s ∈ alternatingGroup (Fin 6) := by
        have := (alternatingGroup.normal (α := Fin 6)).conj_mem y hy s⁻¹
        rwa [inv_inv] at this
      have h1 := D.der_conj (hw₀A _ ((D.mem_abar).1 hs)) (hw₀A _ ((D.mem_abar).1 hs'))
        ⟨s⁻¹ * y * s, hx⟩ ⟨y, hy⟩ (by show y = s * (s⁻¹ * y * s) * s⁻¹; group)
      rw [ha, ha] at h1
      have e : s * (s⁻¹ * y * s) = y * s := by group
      have h2 : n6Act y a * a⁻¹ = n6Act y b * b⁻¹ :=
        calc n6Act y a * a⁻¹ = n6ActL ⟨y, hy⟩ a * a⁻¹ := rfl
          _ = n6Act s (n6ActL ⟨s⁻¹ * y * s, hx⟩ a * a⁻¹) := h1
          _ = n6Act s (n6Act (s⁻¹ * y * s) a) * b⁻¹ := by rw [map_mul, map_inv]; rfl
          _ = n6Act (s * (s⁻¹ * y * s)) a * b⁻¹ := by
            rw [map_mul n6Act s (s⁻¹ * y * s), MulAut.mul_apply]
          _ = n6Act y b * b⁻¹ := by rw [e, map_mul, MulAut.mul_apply, hb]
      have h3 : n6Act y a / a = n6Act y b / b := by simpa only [div_eq_mul_inv] using h2
      rw [div_eq_div_iff_mul_eq_mul] at h3
      rw [map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, ← h3,
        mul_comm]
    have := fixed_alt6 _ hfix
    exact (mul_inv_eq_one.1 this)
  obtain ⟨u, huA, hua⟩ := hsurj a haA
  set v : V := w₀ * (u : V)⁻¹ with hv
  have hvL : ∀ l ∈ L, l v = v := by
    refine fix_of_perfect S.hL.2.2.1 (C := fixV L ⊓ commV L) (fun l hl c hc => hc.1 l hl) ?_
    intro l hl
    obtain ⟨σl, rfl⟩ := D.f_surj ((le_sup_left : L ≤ L ⊔ A) hl)
    set x : LG 6 := ⟨σl, (D.mem_L_iff σl).1 hl⟩ with hx
    have hlu : D.f σl u ∈ commV L := FFC.commV_invariant (S.conj_mem D.hP4 (D.f_mem_G σl)) u.2
    set m₂ : ↥(commV L) := ⟨D.f σl u, hlu⟩ * u⁻¹ with hm₂
    have hm : D.f σl v * v⁻¹ = ((D.mv x w₀ * m₂⁻¹ : ↥(commV L)) : V) := by
      show D.f σl (w₀ * (u : V)⁻¹) * (w₀ * (u : V)⁻¹)⁻¹ =
        D.f σl w₀ * w₀⁻¹ * (D.f σl u * (u : V)⁻¹)⁻¹
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hm]
    refine (D.theta_eq_one_iff _).1 ?_
    have h1 : D.theta (D.mv x w₀) = n6Act σl a * a⁻¹ := ha x
    have h2 : D.theta m₂ = n6Act σl a * a⁻¹ := by
      rw [hm₂, map_mul, map_inv, D.theta_equiv σl u hlu, hua]
    rw [map_mul, map_inv, h1, h2, mul_inv_cancel]
  have hvA : ∀ g ∈ A, g v = v := by
    intro g hg
    rw [hv, map_mul, map_inv, hw₀A g hg, huA g hg]
  have hvM : v ∈ fixV (L ⊔ A) := by
    rw [FFC.fixV_sup]
    exact ⟨hvL, hvA⟩
  have hvW : v ∈ fixV (pCoreOf 3 G) :=
    (fixV (pCoreOf 3 G)).mul_mem hw₀.1 ((fixV (pCoreOf 3 G)).inv_mem (D.U_le_W u.2))
  refine Subgroup.mem_sup.2 ⟨u₁ * u, (commV L).mul_mem hu₁ u.2, v, ⟨hvW, hvM⟩, ?_⟩
  rw [hv, mul_assoc, mul_inv_cancel_comm_assoc]

end SixData

end SmithB57E

end CFSG.Quasithin
