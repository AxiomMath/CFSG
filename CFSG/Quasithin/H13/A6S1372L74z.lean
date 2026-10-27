module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin

namespace A6L74

variable {V : Type*} [CommGroup V]

theorem omega_cube_apply {ω : MulAut V} (hω3 : ω ^ 3 = 1) (v : V) : ω (ω (ω v)) = v := by
  have h := congrArg (fun φ : MulAut V => φ v) hω3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem mem_of_omega_mul_inv_mem (hV : ∀ v : V, v * v = 1) {ω : MulAut V} (hω3 : ω ^ 3 = 1)
    (hωf : ∀ v, ω v = v → v = 1) {C : Subgroup V} (hC : ∀ c ∈ C, ω c ∈ C) {u : V}
    (hu : ω u * u⁻¹ ∈ C) : u ∈ C := by
  obtain ⟨c, hcC, hcdef⟩ : ∃ c ∈ C, c = ω u * u⁻¹ := ⟨_, hu, rfl⟩
  have hωu : ω u = c * u := by rw [hcdef, inv_mul_cancel_right]
  have hN : ω (u * ω u * ω (ω u)) = u * ω u * ω (ω u) := by
    rw [map_mul, map_mul, omega_cube_apply hω3]
    calc ω u * ω (ω u) * u = u * (ω u * ω (ω u)) := mul_comm _ _
      _ = u * ω u * ω (ω u) := (mul_assoc _ _ _).symm
  have h1 := hωf _ hN
  have e : u * ω u * ω (ω u) = u * ω c := by
    rw [hωu, map_mul, hωu]
    calc u * (c * u) * (ω c * (c * u)) = (u * u) * (c * c) * ω c * u * u⁻¹ * u := by
          rw [mul_inv_cancel_right]; ac_rfl
      _ = u * ω c := by rw [hV u, hV c, one_mul, one_mul, mul_inv_cancel_right]; exact mul_comm _ _
  rw [e] at h1
  have h2 : u = (ω c)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2]
  exact C.inv_mem (hC c hcC)

theorem four_le_index [Finite V] (hV : ∀ v : V, v * v = 1) {ω : MulAut V} (hω3 : ω ^ 3 = 1)
    (hωf : ∀ v, ω v = v → v = 1) {H : Subgroup V} (hH : ∀ h ∈ H, ω h ∈ H) (hne : H ≠ ⊤) :
    4 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, pow_two, hV]⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : H.index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card H
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have h2 : H.index ≠ 2 := by
    intro h2
    obtain ⟨v, hv⟩ : ∃ v, v ∉ H := by
      by_contra hc
      push Not at hc
      exact hne (eq_top_iff.mpr fun v _ => hc v)
    have hωv : ω v ∉ H := fun h => hv (by
      have := hH _ (hH _ h)
      rwa [omega_cube_apply hω3] at this)
    have hcard : Nat.card (V ⧸ H) = 2 := by rw [← h2]; rfl
    have hq : (QuotientGroup.mk (ω v) : V ⧸ H) = QuotientGroup.mk v := by
      have hne1 : ∀ x : V, x ∉ H → (QuotientGroup.mk x : V ⧸ H) ≠ 1 := fun x hx h =>
        hx ((QuotientGroup.eq_one_iff x).mp h)
      by_contra hneq
      have : Nat.card (V ⧸ H) ≥ 3 := by
        classical
        have : Fintype (V ⧸ H) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        have hsub :
            ({1, QuotientGroup.mk (ω v), QuotientGroup.mk v} : Finset (V ⧸ H)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hneq]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨(hne1 _ hωv).symm, (hne1 _ hv).symm⟩
        rw [← hsub]
        exact Finset.card_le_univ _
      omega
    rw [QuotientGroup.eq] at hq
    apply hv
    refine mem_of_omega_mul_inv_mem hV hω3 hωf hH ?_
    have := H.inv_mem hq
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  rcases j with _ | _ | j
  · exact absurd (by simpa using hj) h1
  · exact absurd (by simpa using hj) h2
  · rw [hj, pow_succ, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega

theorem four_le_card_of_offender [Finite V] (hV : ∀ v : V, v * v = 1) {ω : MulAut V}
    (hω3 : ω ^ 3 = 1) (hωf : ∀ v, ω v = v → v = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hωA : ∀ a ∈ A, ω * a = a * ω) :
    (fixV A).index ≤ Nat.card A ∧ 4 ≤ Nat.card A := by
  have hfix : ∀ h ∈ fixV A, ω h ∈ fixV A := fun h hh a ha => by
    have e := congrArg (fun φ : MulAut V => φ h) (hωA a ha)
    simp only [MulAut.mul_apply] at e
    rw [← e, hh a ha]
  have hne : fixV A ≠ ⊤ := by
    intro htop
    apply hA.2.1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV A := by rw [htop]; exact Subgroup.mem_top v
    exact hv a ha
  have h4 := four_le_index hV hω3 hωf hfix hne
  have hle : (fixV A).index ≤ Nat.card A := by
    have h1 := hA.2.2.2 ⊥ bot_le
    have hfb : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ a ha
      rw [Subgroup.mem_bot.mp ha]
      rfl
    rw [Subgroup.card_bot, one_mul, hfb, Subgroup.card_top, ← (fixV A).index_mul_card] at h1
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  exact ⟨hle, h4.trans hle⟩

theorem mul_inv_mem_of_fix [Finite V] (hV : ∀ v : V, v * v = 1) {ω g : MulAut V}
    (hω3 : ω ^ 3 = 1) (hωf : ∀ v, ω v = v → v = 1) (hωg : ω * g = g * ω)
    {H : Subgroup V} (hH : ∀ h ∈ H, ω h ∈ H) (hH4 : H.index = 4)
    (hgH : ∀ h ∈ H, g h = h) {n : ℕ} (hgn : g ^ 2 ^ n = 1) (v : V) : g v * v⁻¹ ∈ H := by
  classical
  have hfpf : ∀ w, ω w * w⁻¹ ∈ H → w ∈ H := fun w hw =>
    mem_of_omega_mul_inv_mem hV hω3 hωf hH hw
  have hωp : ∀ a b, a * b⁻¹ ∈ H → ω a * (ω b)⁻¹ ∈ H := fun a b h => by
    rw [← map_inv, ← map_mul]
    exact hH _ h
  have hgp : ∀ a b, a * b⁻¹ ∈ H → g a * (g b)⁻¹ ∈ H := fun a b h => by
    rw [← map_inv, ← map_mul, hgH _ h]
    exact h
  have htr : ∀ a b c, a * b⁻¹ ∈ H → b * c⁻¹ ∈ H → a * c⁻¹ ∈ H := fun a b c h1 h2 => by
    have := H.mul_mem h1 h2
    rwa [mul_assoc, inv_mul_cancel_left] at this
  have hsy : ∀ a b, a * b⁻¹ ∈ H → b * a⁻¹ ∈ H := fun a b h => by
    have := H.inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have hωH' : ∀ w, ω w ∈ H → w ∈ H := fun w h => by
    have := hH _ (hH _ h)
    rwa [omega_cube_apply hω3] at this
  have hgcomm : ∀ w, g (ω w) = ω (g w) := fun w => by
    have := congrArg (fun φ : MulAut V => φ w) hωg
    simpa [MulAut.mul_apply] using this.symm
  by_contra hx
  have hvH : v ∉ H := fun hv => hx (by rw [hgH v hv, mul_inv_cancel]; exact H.one_mem)
  have hd1 : ¬ ω v * v⁻¹ ∈ H := fun h => hvH (hfpf v h)
  have hd2 : ¬ ω (ω v) * (ω v)⁻¹ ∈ H := fun h => hvH (hωH' v (hfpf _ h))
  have hd3 : ¬ ω (ω v) * v⁻¹ ∈ H := fun h => by
    have h' := hωp _ _ h
    rw [omega_cube_apply hω3] at h'
    exact hd1 (hsy _ _ h')
  have hωv : ω v ∉ H := fun h => hvH (hωH' v h)
  have hωωv : ω (ω v) ∉ H := fun h => hvH (hωH' v (hωH' _ h))
  have : Fintype (V ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (V ⧸ H) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← hH4]
    rfl
  have hmk : ∀ a b : V, (QuotientGroup.mk a : V ⧸ H) = QuotientGroup.mk b ↔ a * b⁻¹ ∈ H := by
    intro a b
    rw [QuotientGroup.eq]
    constructor
    · intro h
      have := H.inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at this
    · intro h
      have := H.inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at this
  have hmk1 : ∀ a : V, (QuotientGroup.mk a : V ⧸ H) = 1 ↔ a ∈ H := fun a =>
    QuotientGroup.eq_one_iff a
  have hall : ∀ w : V, w ∉ H → w * v⁻¹ ∈ H ∨ w * (ω v)⁻¹ ∈ H ∨ w * (ω (ω v))⁻¹ ∈ H := by
    intro w hw
    set F : Finset (V ⧸ H) := {1, QuotientGroup.mk v, QuotientGroup.mk (ω v),
      QuotientGroup.mk (ω (ω v))} with hF
    have hFc : F.card = 4 := by
      rw [hF, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        exact hd2 ((hmk _ _).1 h.symm)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hd1 ((hmk _ _).1 h.symm), fun h => hd3 ((hmk _ _).1 h.symm)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hvH ((hmk1 _).1 h.symm), fun h => hωv ((hmk1 _).1 h.symm),
          fun h => hωωv ((hmk1 _).1 h.symm)⟩
    have hFu : F = Finset.univ := Finset.eq_univ_of_card F (by rw [hFc, hcard])
    have hwF : (QuotientGroup.mk w : V ⧸ H) ∈ F := by rw [hFu]; exact Finset.mem_univ _
    simp only [hF, Finset.mem_insert, Finset.mem_singleton] at hwF
    rcases hwF with h | h | h | h
    · exact absurd ((hmk1 _).1 h) hw
    · exact Or.inl ((hmk _ _).1 h)
    · exact Or.inr (Or.inl ((hmk _ _).1 h))
    · exact Or.inr (Or.inr ((hmk _ _).1 h))
  have hgv : g v ∉ H := fun h => hvH (by
    have := hgH _ h
    have e : g (g v) = g v := this
    exact (g.injective e) ▸ h)
  have hpow : ∀ (i : ℕ), g v * ((ω ^ i) v)⁻¹ ∈ H → ∀ k : ℕ,
      (g ^ k) v * ((ω ^ (i * k)) v)⁻¹ ∈ H := by
    intro i hi k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (g ^ (k + 1)) v = g ((g ^ k) v) := by rw [pow_succ', MulAut.mul_apply]
      have h2 : (ω ^ (i * (k + 1))) v = (ω ^ (i * k)) ((ω ^ i) v) := by
        rw [mul_add, mul_one, pow_add, MulAut.mul_apply]
      have hgω : ∀ m : ℕ, ∀ w, g ((ω ^ m) w) = (ω ^ m) (g w) := by
        intro m
        induction m with
        | zero => intro w; simp
        | succ m ihm =>
          intro w
          rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply, hgcomm, ihm]
      have hωmp : ∀ m : ℕ, ∀ a b, a * b⁻¹ ∈ H → (ω ^ m) a * ((ω ^ m) b)⁻¹ ∈ H := by
        intro m
        induction m with
        | zero => intro a b h; simpa using h
        | succ m ihm =>
          intro a b h
          rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply]
          exact hωp _ _ (ihm a b h)
      rw [h1, h2]
      refine htr _ (g ((ω ^ (i * k)) v)) _ (hgp _ _ ih) ?_
      rw [hgω]
      exact hωmp _ _ _ hi
  have hgn' : (g ^ 2 ^ n) v = v := by rw [hgn]; rfl
  have hω3' : ∀ m : ℕ, (ω ^ m) v = (ω ^ (m % 3)) v := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  have h3m : ∀ m : ℕ, 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    intro m
    induction m with
    | zero => left; rfl
    | succ m ihm =>
      rcases ihm with h | h
      · right
        rw [pow_succ, Nat.mul_mod, h]
      · left
        rw [pow_succ, Nat.mul_mod, h]
  have hcases : ∀ i : ℕ, (i = 1 ∨ i = 2) → g v * ((ω ^ i) v)⁻¹ ∈ H → False := by
    intro i hi h
    have h1 := hpow i h (2 ^ n)
    rw [hgn', hω3'] at h1
    have h2 : (i * 2 ^ n) % 3 = 1 ∨ (i * 2 ^ n) % 3 = 2 := by
      rcases hi with rfl | rfl <;> rcases h3m n with h | h <;> simp [Nat.mul_mod, h]
    rcases h2 with h2 | h2 <;> rw [h2] at h1
    · exact hd1 (hsy _ _ (by simpa using h1))
    · exact hd3 (hsy _ _ (by simpa [pow_two, MulAut.mul_apply] using h1))
  rcases hall (g v) hgv with h | h | h
  · exact hx h
  · exact hcases 1 (Or.inl rfl) (by simpa using h)
  · exact hcases 2 (Or.inr rfl) (by simpa [pow_two, MulAut.mul_apply] using h)

theorem commute_of_fix {H : Subgroup V} {g h : MulAut V} (hgH : ∀ x ∈ H, g x = x)
    (hhH : ∀ x ∈ H, h x = x) (hg : ∀ v, g v * v⁻¹ ∈ H) (hh : ∀ v, h v * v⁻¹ ∈ H) :
    g * h = h * g := by
  refine MulEquiv.ext fun v => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have l1 : g (h v) = (h v * v⁻¹) * g v := by
    have e1 : h v = (h v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    conv_lhs => rw [e1]
    rw [map_mul, hgH _ (hh v)]
  have l2 : h (g v) = (g v * v⁻¹) * h v := by
    have e2 : g v = (g v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    conv_lhs => rw [e2]
    rw [map_mul, hhH _ (hg v)]
  rw [l1, l2]
  ac_rfl

end A6L74

end CFSG.Quasithin.H13.A6
