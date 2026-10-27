module

public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.Quasithin

namespace FFC

variable {V : Type} [CommGroup V] [Finite V]

structure S3Pair (F A : Subgroup (MulAut V)) : Prop where
  card_F : Nat.card F = 3
  card_A : Nat.card A = 2
  norm : ∀ a ∈ A, ∀ f ∈ F, a * f * a⁻¹ ∈ F
  noncomm : ∃ a ∈ A, ∃ f ∈ F, a * f ≠ f * a

namespace S3Pair

variable {F A : Subgroup (MulAut V)} (h : S3Pair F A)

include h in
theorem exists_gen_F : ∃ f₀ ∈ F, f₀ ≠ 1 ∧ f₀ ^ 3 = 1 ∧ Subgroup.zpowers f₀ = F := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbot : F ≠ ⊥ := by
    intro hb
    have := Subgroup.card_eq_one.2 hb
    rw [h.card_F] at this
    omega
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have hf₀ : (x : MulAut V) ∈ F := x.2
  have hf₀1 : (x : MulAut V) ≠ 1 := fun e => hx (Subtype.ext e)
  generalize (x : MulAut V) = f₀ at hf₀ hf₀1
  have hz := zpowers_eq_of_prime_card (p := 3) h.card_F hf₀ hf₀1
  refine ⟨f₀, hf₀, hf₀1, ?_, hz⟩
  have : orderOf f₀ = 3 := by
    have hdvd : orderOf f₀ ∣ 3 := by
      have : orderOf (⟨f₀, hf₀⟩ : F) ∣ Nat.card F := orderOf_dvd_natCard _
      rwa [h.card_F, Subgroup.orderOf_mk] at this
    exact ((Nat.dvd_prime Fact.out).mp hdvd).resolve_left fun h1 => hf₀1 (orderOf_eq_one_iff.mp h1)
  rw [← this]
  exact pow_orderOf_eq_one f₀


include h in
theorem exists_inv_A : ∃ a ∈ A, a ≠ 1 ∧ a ^ 2 = 1 ∧ ∀ b ∈ A, b = 1 ∨ b = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : A ≠ ⊥ := by
    intro hb
    have := Subgroup.card_eq_one.2 hb
    rw [h.card_A] at this
    omega
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have ha : (x : MulAut V) ∈ A := x.2
  have ha1 : (x : MulAut V) ≠ 1 := fun e => hx (Subtype.ext e)
  generalize (x : MulAut V) = a at ha ha1
  have hz := zpowers_eq_of_prime_card (p := 2) h.card_A ha ha1
  have hord : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := by
      have : orderOf (⟨a, ha⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
      rwa [h.card_A, Subgroup.orderOf_mk] at this
    exact ((Nat.dvd_prime Fact.out).mp hdvd).resolve_left fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
  refine ⟨a, ha, ha1, by rw [← hord]; exact pow_orderOf_eq_one a, fun b hb => ?_⟩
  rw [← hz, Subgroup.mem_zpowers_iff] at hb
  obtain ⟨k, rfl⟩ := hb
  have : a ^ k = a ^ (k % 2) := by
    have h2 := zpow_mod_orderOf a k
    rw [hord] at h2
    simpa using h2.symm
  rw [this]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · left; rw [hk]; simp
  · right; rw [hk]; simp

include h in
theorem conj_eq_inv {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) {f : MulAut V} (hf : f ∈ F) :
    a * f * a⁻¹ = f⁻¹ := by
  obtain ⟨f₀, hf₀, hf₀1, hf₀3, hz⟩ := h.exists_gen_F
  obtain ⟨a₀, ha₀, ha₀1, ha₀2, hA⟩ := h.exists_inv_A
  have haa : a = a₀ := (hA a ha).resolve_left ha1
  subst haa
  obtain ⟨a', ha', f', hf', hne⟩ := h.noncomm
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have haa' : a' = a := (hA a' ha').resolve_left ha'1
  subst haa'
  have hnc : a' * f₀ ≠ f₀ * a' := by
    intro hcomm
    apply hne
    have : f' ∈ Subgroup.zpowers f₀ := hz ▸ hf'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 this
    have : Commute a' f₀ := hcomm
    exact (this.zpow_right k).eq
  have hmem : a' * f₀ * a'⁻¹ ∈ Subgroup.zpowers f₀ := hz ▸ h.norm a' ha' f₀ hf₀
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord : orderOf f₀ = 3 := by
    have h3 : orderOf f₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hf₀3
    exact ((Nat.dvd_prime (by norm_num)).mp h3).resolve_left fun h1 => hf₀1 (orderOf_eq_one_iff.mp h1)
  have hk' : f₀ ^ (k % 3) = a' * f₀ * a'⁻¹ := by
    rw [← hk, ← zpow_mod_orderOf f₀ k, hord]
    simp
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hf₀inv : a' * f₀ * a'⁻¹ = f₀⁻¹ := by
    rcases hk3 with h0 | h1 | h2
    · exfalso
      have e : a' * f₀ * a'⁻¹ = 1 := by rw [← hk', h0]; simp
      have : f₀ = 1 := by
        calc f₀ = a'⁻¹ * (a' * f₀ * a'⁻¹) * a' := by group
          _ = 1 := by rw [e]; simp
      exact hf₀1 this
    · exfalso
      have e : a' * f₀ * a'⁻¹ = f₀ := by rw [← hk', h1]; simp
      apply hnc
      calc a' * f₀ = a' * f₀ * a'⁻¹ * a' := by group
        _ = f₀ * a' := by rw [e]
    · rw [h2] at hk'
      rw [← hk']
      have : f₀ ^ (2 : ℤ) = f₀⁻¹ := by
        have h3 : f₀ ^ (3 : ℤ) = 1 := by exact_mod_cast hf₀3
        calc f₀ ^ (2 : ℤ) = f₀ ^ (3 : ℤ) * f₀⁻¹ := by group
          _ = f₀⁻¹ := by rw [h3, one_mul]
      exact this
  have : f ∈ Subgroup.zpowers f₀ := hz ▸ hf
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 this
  calc a' * f₀ ^ j * a'⁻¹ = (a' * f₀ * a'⁻¹) ^ j := by
        have := map_zpow (MulAut.conj a') f₀ j
        simp
    _ = (f₀⁻¹) ^ j := by rw [hf₀inv]
    _ = (f₀ ^ j)⁻¹ := by rw [inv_zpow]


end S3Pair

omit [Finite V] in
theorem eq_of_mul_eq_of_disjoint {V₁ V₂ : Subgroup V} (h : V₁ ⊓ V₂ = ⊥) {y y' z z' : V}
    (hy : y ∈ V₁) (hy' : y' ∈ V₁) (hz : z ∈ V₂) (hz' : z' ∈ V₂) (hyz : y * z = y' * z') :
    y = y' ∧ z = z' := by
  have h1 : y'⁻¹ * y = z' * z⁻¹ := by
    have : y'⁻¹ * y * z = z' := by
      calc y'⁻¹ * y * z = y'⁻¹ * (y * z) := by rw [mul_assoc]
        _ = y'⁻¹ * (y' * z') := by rw [hyz]
        _ = z' := by rw [inv_mul_cancel_left]
    rw [eq_mul_inv_iff_mul_eq]
    exact this
  have h2 : y'⁻¹ * y ∈ V₁ ⊓ V₂ :=
    ⟨V₁.mul_mem (V₁.inv_mem hy') hy, h1 ▸ V₂.mul_mem hz' (V₂.inv_mem hz)⟩
  rw [h, Subgroup.mem_bot] at h2
  have hyy : y = y' := by
    calc y = y' * (y'⁻¹ * y) := by rw [mul_inv_cancel_left]
      _ = y' := by rw [h2, mul_one]
  refine ⟨hyy, ?_⟩
  rw [hyy] at hyz
  exact mul_left_cancel hyz

omit [Finite V] in
theorem card_fixV_of_decomp {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥)
    {B : Subgroup (MulAut V)} (h₁ : ∀ b ∈ B, ∀ v ∈ V₁, b v ∈ V₁) (h₂ : ∀ b ∈ B, ∀ v ∈ V₂, b v ∈ V₂) :
    Nat.card (fixV B) = Nat.card ↥(V₁ ⊓ fixV B) * Nat.card ↥(V₂ ⊓ fixV B) := by
  have hsup' : (V₁ ⊓ fixV B) ⊔ (V₂ ⊓ fixV B) = fixV B := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro v hv
    have hv' : v ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv'
    have hfix : ∀ b ∈ B, b y = y ∧ b z = z := by
      intro b hb
      have h1 := hv b hb
      rw [map_mul] at h1
      exact eq_of_mul_eq_of_disjoint hinf (h₁ b hb y hy) hy (h₂ b hb z hz) hz h1
    exact Subgroup.mul_mem_sup ⟨hy, fun b hb => (hfix b hb).1⟩ ⟨hz, fun b hb => (hfix b hb).2⟩
  have hinf' : (V₁ ⊓ fixV B) ⊓ (V₂ ⊓ fixV B) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ V₁ ⊓ V₂ := ⟨hx.1.1, hx.2.1⟩
    rw [hinf] at this
    exact this
  have := card_sup_mul_card_inf (V₁ ⊓ fixV B) (V₂ ⊓ fixV B)
  rw [hsup', hinf', Subgroup.card_bot, mul_one] at this
  exact this

omit [Finite V] in
theorem card_of_decomp {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥) :
    Nat.card V = Nat.card V₁ * Nat.card V₂ := by
  have := card_sup_mul_card_inf V₁ V₂
  rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top] at this
  exact this


namespace S3Pair

variable {F A : Subgroup (MulAut V)} (h : S3Pair F A)

omit [Finite V] in
include h in
theorem odd_card_F : Odd (Nat.card F) := by
  rw [h.card_F]
  decide

include h in
theorem decomp (hV : ∀ v : V, v ^ 2 = 1) : commV F ⊔ fixV F = ⊤ ∧ commV F ⊓ fixV F = ⊥ := by
  obtain ⟨h1, h2⟩ := B1.coprime_decomp hV h.odd_card_F (M := ⊤) (fun _ _ _ _ => trivial)
  rw [← commV_eq_commSub] at h1 h2
  rw [top_inf_eq] at h1 h2
  exact ⟨by rw [sup_comm]; exact h1, by rw [inf_comm]; exact h2⟩

omit [Finite V] in
include h in
theorem fixV_invariant {a : MulAut V} (ha : a ∈ A) {v : V} (hv : v ∈ fixV F) : a v ∈ fixV F := by
  intro f hf
  have hf' : a⁻¹ * f * a⁻¹⁻¹ ∈ F := h.norm a⁻¹ (A.inv_mem ha) f hf
  have h1 : ((a⁻¹ * f * a⁻¹⁻¹ : MulAut V)) v = v := hv _ hf'
  have h2 : f (a v) = a v := by
    have : a (((a⁻¹ * f * a⁻¹⁻¹ : MulAut V)) v) = a v := by rw [h1]
    simpa [MulAut.mul_apply] using this
  exact h2

omit [Finite V] in
include h in
theorem commV_invariant {a : MulAut V} (ha : a ∈ A) {v : V} (hv : v ∈ commV F) : a v ∈ commV F := by
  refine Subgroup.closure_induction (p := fun v _ => a v ∈ commV F) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, hx, w, rfl⟩
    have h1 : a (x w * w⁻¹) = (a * x * a⁻¹) (a w) * (a w)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨a * x * a⁻¹, h.norm a ha x hx, a w, rfl⟩
  · rw [map_one]
    exact (commV F).one_mem
  · intro x y _ _ hx hy
    rw [map_mul]
    exact (commV F).mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact (commV F).inv_mem hx

include h in
theorem not_trivial_on_comm (hV : ∀ v : V, v ^ 2 = 1) : ¬ ∀ a ∈ A, ∀ v ∈ commV F, a v = v := by
  intro htriv
  obtain ⟨a, ha, f, hf, hne⟩ := h.noncomm
  apply hne
  obtain ⟨hsup, hinf⟩ := h.decomp hV
  ext v
  have hv : v ∈ commV F ⊔ fixV F := by rw [hsup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  have hfy : f y ∈ commV F := by
    have : f y * y⁻¹ ∈ commV F := Subgroup.subset_closure ⟨f, hf, y, rfl⟩
    simpa using (commV F).mul_mem this hy
  have haz : a z ∈ fixV F := h.fixV_invariant ha hz
  simp only [MulAut.mul_apply, map_mul]
  rw [htriv a ha (f y) hfy, htriv a ha y hy, hz f hf, haz f hf]

include h in
theorem fixV_le_fixV (hV : ∀ v : V, v ^ 2 = 1) (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    fixV F ≤ fixV A := by
  obtain ⟨hsup, hinf⟩ := h.decomp hV
  have hV₁ : ∀ b ∈ A, ∀ v ∈ commV F, b v ∈ commV F := fun b hb v hv => h.commV_invariant hb hv
  have hV₂ : ∀ b ∈ A, ∀ v ∈ fixV F, b v ∈ fixV F := fun b hb v hv => h.fixV_invariant hb hv
  have hcard := card_fixV_of_decomp hsup hinf hV₁ hV₂
  have hcardV := card_of_decomp hsup hinf
  have hlt : commV F ⊓ fixV A ≠ commV F := by
    intro heq
    apply h.not_trivial_on_comm hV
    intro b hb v hv
    have : v ∈ commV F ⊓ fixV A := by rw [heq]; exact hv
    exact this.2 b hb
  have hdvd : Nat.card ↥(commV F ⊓ fixV A) ∣ Nat.card ↥(commV F) :=
    Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hlt
    exact (Subgroup.eq_of_le_of_card_ge (inf_le_left : commV F ⊓ fixV A ≤ commV F) (by omega))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card ↥(commV F) := Nat.card_pos
    omega
  have h2le : 2 * Nat.card ↥(commV F ⊓ fixV A) ≤ Nat.card ↥(commV F) := by
    rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have hpos1 : 0 < Nat.card ↥(fixV F ⊓ fixV A) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(commV F ⊓ fixV A) := Nat.card_pos
  rw [hcardV, hcard, h.card_A] at hoff
  have h3 : Nat.card ↥(fixV F) ≤ Nat.card ↥(fixV F ⊓ fixV A) := by
    have hle : Nat.card ↥(commV F) * Nat.card ↥(fixV F) ≤
        Nat.card ↥(commV F) * Nat.card ↥(fixV F ⊓ fixV A) := by
      calc Nat.card ↥(commV F) * Nat.card ↥(fixV F)
          ≤ 2 * (Nat.card ↥(commV F ⊓ fixV A) * Nat.card ↥(fixV F ⊓ fixV A)) := by
            rw [inf_comm (fixV F), inf_comm (commV F)] at hoff ⊢
            simpa [inf_comm] using hoff
        _ = (2 * Nat.card ↥(commV F ⊓ fixV A)) * Nat.card ↥(fixV F ⊓ fixV A) := by ring
        _ ≤ Nat.card ↥(commV F) * Nat.card ↥(fixV F ⊓ fixV A) := Nat.mul_le_mul_right _ h2le
    exact Nat.le_of_mul_le_mul_left hle Nat.card_pos
  have heq : fixV F ⊓ fixV A = fixV F :=
    Subgroup.eq_of_le_of_card_ge inf_le_left h3
  exact heq ▸ inf_le_right


include h in
theorem trivial_of_commute (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card (commV F) = 4) {g : MulAut V}
    (hgF : ∀ f ∈ F, g * f = f * g) (hgA : ∀ a ∈ A, g * a = a * g) :
    ∀ v ∈ commV F, g v = v := by
  obtain ⟨f₀, hf₀, hf₀1, hf₀3, hz⟩ := h.exists_gen_F
  obtain ⟨a₀, ha₀, ha₀1, ha₀2, hA⟩ := h.exists_inv_A
  obtain ⟨hsup, hinf⟩ := h.decomp hV
  have hf₀inv : a₀ * f₀ * a₀⁻¹ = f₀⁻¹ := h.conj_eq_inv ha₀ ha₀1 hf₀
  have hgV₁ : ∀ v ∈ commV F, g v ∈ commV F := by
    intro v hv
    refine Subgroup.closure_induction (p := fun v _ => g v ∈ commV F) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨x, hx, w, rfl⟩
      have h0 : g (x w) = x (g w) := by
        have := congrArg (fun t : MulAut V => t w) (hgF x hx)
        simpa only [MulAut.mul_apply] using this
      have h1 : g (x w * w⁻¹) = x (g w) * (g w)⁻¹ := by rw [map_mul, map_inv, h0]
      rw [h1]
      exact Subgroup.subset_closure ⟨x, hx, g w, rfl⟩
    · rw [map_one]
      exact (commV F).one_mem
    · intro x y _ _ hx hy
      rw [map_mul]
      exact (commV F).mul_mem hx hy
    · intro x _ hx
      rw [map_inv]
      exact (commV F).inv_mem hx
  have hne : commV F ≠ ⊥ := by
    intro hb
    have := Subgroup.card_eq_one.2 hb
    omega
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1 : (x : V) ≠ 1 := fun e => hx (Subtype.ext e)
  have hxV : (x : V) ∈ commV F := x.2
  generalize (x : V) = x at hx1 hxV
  have hfree : ∀ w ∈ commV F, w ≠ 1 → f₀ w ≠ w := by
    intro w hw hw1 hfw
    apply hw1
    have hwfix : w ∈ fixV F := by
      intro f hf
      rw [← hz] at hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      have : ∀ n : ℤ, (f₀ ^ n) w = w := by
        intro n
        induction n using Int.induction_on with
        | zero => simp
        | succ n ih =>
          rw [zpow_add_one, MulAut.mul_apply, hfw, ih]
        | pred n ih =>
          rw [zpow_sub_one, MulAut.mul_apply]
          have h2 : f₀⁻¹ w = w := by
            show f₀.symm w = w
            rw [MulEquiv.symm_apply_eq]
            exact hfw.symm
          rw [h2, ih]
      exact this k
    have : w ∈ commV F ⊓ fixV F := ⟨hw, hwfix⟩
    rw [hinf] at this
    exact this
  have hf₀inj : Function.Injective f₀ := f₀.injective
  have hf₁ : f₀ x ≠ x := hfree x hxV hx1
  have hfxV : f₀ x ∈ commV F := by
    have : f₀ x * x⁻¹ ∈ commV F := Subgroup.subset_closure ⟨f₀, hf₀, x, rfl⟩
    simpa using (commV F).mul_mem this hxV
  have hf₀cube : ∀ w, f₀ (f₀ (f₀ w)) = w := by
    intro w
    have := congrArg (fun t : MulAut V => t w) hf₀3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hf₂ : f₀ (f₀ x) ≠ x := by
    intro e
    apply hf₁
    have := congrArg f₀ e
    rw [hf₀cube] at this
    exact this.symm
  have hf₂' : f₀ (f₀ x) ≠ f₀ x := by
    intro e
    exact hf₁ (hf₀inj e)
  have hf₁1 : f₀ x ≠ 1 := by
    intro e
    apply hx1
    have : f₀ x = f₀ 1 := by rw [e, map_one]
    exact hf₀inj this
  have hf₂1 : f₀ (f₀ x) ≠ 1 := by
    intro e
    apply hf₁1
    have : f₀ (f₀ x) = f₀ 1 := by rw [e, map_one]
    exact hf₀inj this
  have hmemS : ∀ v ∈ commV F, v = 1 ∨ v = x ∨ v = f₀ x ∨ v = f₀ (f₀ x) := by
    classical
    have := Fintype.ofFinite V
    intro v hv
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, c4⟩ := hcon
    let S : Finset V := {1, x, f₀ x, f₀ (f₀ x), v}
    have hS : S ⊆ (commV F : Set V).toFinset := by
      intro y hy
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Set.mem_toFinset]
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact (commV F).one_mem
      · exact hxV
      · exact hfxV
      · have : f₀ (f₀ x) ∈ commV F := by
          have : f₀ (f₀ x) * (f₀ x)⁻¹ ∈ commV F := Subgroup.subset_closure ⟨f₀, hf₀, f₀ x, rfl⟩
          simpa using (commV F).mul_mem this hfxV
        exact this
      · exact hv
    have hcardS : S.card = 5 := by
      simp only [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact c4.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact not_or.2 ⟨hf₂'.symm, c3.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact not_or.2 ⟨hf₁.symm, not_or.2 ⟨hf₂.symm, c2.symm⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact not_or.2 ⟨hx1.symm, not_or.2 ⟨hf₁1.symm, not_or.2 ⟨hf₂1.symm, c1.symm⟩⟩⟩
    have hle := Finset.card_le_card hS
    have h4 : ((commV F : Set V).toFinset).card = 4 := by
      rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext y
      simp
    omega
  have hgx : g x = x ∨ g x = f₀ x ∨ g x = f₀ (f₀ x) := by
    have hgxV := hgV₁ x hxV
    have hg1 : g x ≠ 1 := by
      intro e
      apply hx1
      have : g x = g 1 := by rw [e, map_one]
      exact g.injective this
    rcases hmemS _ hgxV with e | e | e | e
    · exact absurd e hg1
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  have hgf : ∀ w, g (f₀ w) = f₀ (g w) := by
    intro w
    have := congrArg (fun t : MulAut V => t w) (hgF f₀ hf₀)
    simpa only [MulAut.mul_apply] using this
  have key : ∀ T : V → V, (∀ w, T (f₀ w) = f₀ (T w)) → T 1 = 1 → g x = T x →
      ∀ w ∈ commV F, g w = T w := by
    intro T hT hT1 hgxT w hw
    rcases hmemS w hw with rfl | rfl | rfl | rfl
    · rw [map_one, hT1]
    · exact hgxT
    · rw [hgf, hgxT, hT]
    · rw [hgf, hgf, hgxT, hT, hT]
  have hax : a₀⁻¹ x ∈ commV F := h.commV_invariant (A.inv_mem ha₀) hxV
  have hg1 : g x = a₀ (g (a₀⁻¹ x)) := by
    have := congrArg (fun t : MulAut V => t (a₀⁻¹ x)) (hgA a₀ ha₀)
    simpa [MulAut.mul_apply] using this
  have hconj1 : a₀ (f₀ (a₀⁻¹ x)) = f₀⁻¹ x := by
    have := congrArg (fun t : MulAut V => t x) hf₀inv
    simpa [MulAut.mul_apply] using this
  have hf₀inv_inv : ∀ w, f₀⁻¹ (f₀⁻¹ w) = f₀ w := by
    intro w
    have h3 : f₀ ^ 3 = 1 := hf₀3
    have : f₀⁻¹ * f₀⁻¹ = f₀ := by
      calc f₀⁻¹ * f₀⁻¹ = f₀ ^ 3 * (f₀⁻¹ * f₀⁻¹) * f₀ ^ 0 := by simp [h3]
        _ = f₀ := by group
    simpa [MulAut.mul_apply] using congrArg (fun t : MulAut V => t w) this
  rcases hgx with e | e | e
  · intro v hv
    exact key id (fun _ => rfl) rfl e v hv
  · exfalso
    have hT := key f₀ (fun w => rfl) (map_one f₀) e
    rw [hT _ hax, hconj1] at hg1
    apply hf₂
    have h3 : f₀ x = f₀⁻¹ x := by rw [← e, hg1]
    have := congrArg f₀ h3
    simpa using this
  · exfalso
    have hT := key (fun w => f₀ (f₀ w)) (fun w => rfl) (by simp) e
    rw [hT _ hax] at hg1
    have h4 : a₀ (f₀ (f₀ (a₀⁻¹ x))) = f₀⁻¹ (f₀⁻¹ x) := by
      have h5 : a₀ (f₀ (f₀ (a₀⁻¹ x))) = (a₀ * f₀ * a₀⁻¹) ((a₀ * f₀ * a₀⁻¹) x) := by
        simp [MulAut.mul_apply]
      rw [h5, hf₀inv]
    rw [h4, hf₀inv_inv] at hg1
    apply hf₂'
    rw [← e, hg1]

end S3Pair

end FFC

end CFSG.Quasithin
