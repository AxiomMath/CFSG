module

public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.WeightBound
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddL2Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem sub_one_div_two_le_finrank [Finite V] {L : Subgroup (GLV V)} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {S : Type} [Group S] (e : ↥L ≃* S) {K : Type} [Field K] [Finite K]
    (u : Multiplicative K →* S) (hu : Function.Injective u) (hUel : IsElemAbelian p u.range)
    (d : Kˣ → S)
    (hd : ∀ (a : Kˣ) (t : K), d a * u (Multiplicative.ofAdd t) * (d a)⁻¹ =
      u (Multiplicative.ofAdd ((a : K) ^ 2 * t))) :
    (Nat.card K - 1) / 2 ≤ Module.finrank (ZMod 2) V := by
  classical
  have := Fintype.ofFinite K
  let ψ : Multiplicative K →* GLV V := L.subtype.comp (e.symm.toMonoidHom.comp u)
  have hψ : Function.Injective ψ := L.subtype_injective.comp (e.symm.injective.comp hu)
  let δ : Kˣ → GLV V := fun a => ((e.symm (d a) : ↥L) : GLV V)
  have hδ : ∀ (a : Kˣ) (t : K), δ a * ψ (Multiplicative.ofAdd t) * (δ a)⁻¹ =
      ψ (Multiplicative.ofAdd ((a : K) ^ 2 * t)) := by
    intro a t
    have := congrArg (fun x : S => ((e.symm x : ↥L) : GLV V)) (hd a t)
    simpa [δ, ψ] using this
  have hδ' : ∀ (a : Kˣ) (t : K), (δ a)⁻¹ * ψ (Multiplicative.ofAdd t) * δ a =
      ψ (Multiplicative.ofAdd (((a : K) ^ 2)⁻¹ * t)) := by
    intro a t
    have h1 := hδ a (((a : K) ^ 2)⁻¹ * t)
    have ha : (a : K) ^ 2 * (((a : K) ^ 2)⁻¹ * t) = t := by
      field_simp
    rw [ha] at h1
    rw [← h1]
    group
  have hP : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨s, hs⟩ := x.2
      obtain ⟨t, ht⟩ := y.2
      apply Subtype.ext
      change (x : GLV V) * y = y * x
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨t, rfl⟩
      have h1 : t ^ p = 1 := hu (by rw [map_pow, map_one]; exact hUel.2 _ ⟨t, rfl⟩)
      show ψ t ^ p = 1
      rw [← map_pow, h1, map_one]
  have hPne : ψ.range ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : K)
    have : ψ (Multiplicative.ofAdd x) ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx (by simpa using hψ (this.trans (map_one ψ).symm))
  let Q : Finset Kˣ := Finset.univ.image (fun a : Kˣ => a ^ 2)
  let rep : Kˣ → Kˣ := fun c => if h : ∃ a : Kˣ, a ^ 2 = c then h.choose else 1
  have hrep : ∀ c ∈ Q, rep c ^ 2 = c := by
    intro c hc
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    have h : ∃ b : Kˣ, b ^ 2 = a ^ 2 := ⟨a, rfl⟩
    simp only [rep, h, ↓reduceDIte]
    exact h.choose_spec
  have hδinj : ∀ a b : Kˣ, δ a = δ b → (a : K) ^ 2 = (b : K) ^ 2 := by
    intro a b hab
    have h1 := hδ a 1
    have h2 := hδ b 1
    rw [hab, h2] at h1
    have := hψ h1
    simpa using this.symm
  let S' : Finset (GLV V) := Q.image (fun c => δ (rep c))
  have hcardS : S'.card = Q.card := by
    refine Finset.card_image_of_injOn fun c hc c' hc' h => ?_
    have := hδinj _ _ h
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at this
    rw [← hrep c hc, ← hrep c' hc']
    exact Units.ext this
  have hQcard : Nat.card K - 1 ≤ 2 * Q.card := by
    have h1 : (Finset.univ : Finset Kˣ).card ≤ 2 * Q.card := by
      refine Finset.card_le_mul_card_image _ 2 fun c hc => ?_
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
      have hsub : Finset.univ.filter (fun b : Kˣ => b ^ 2 = a ^ 2) ⊆ {a, -a} := by
        intro b hb
        have hb2 : b ^ 2 = a ^ 2 := (Finset.mem_filter.1 hb).2
        have hb3 : ((b : K) - a) * ((b : K) + a) = 0 := by
          have : (b : K) ^ 2 = (a : K) ^ 2 := by
            rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hb2]
          linear_combination this
        rcases mul_eq_zero.1 hb3 with h | h
        · simp [Units.ext (sub_eq_zero.1 h)]
        · have : b = -a := Units.ext (by simpa [add_eq_zero_iff_eq_neg] using h)
          simp [this]
      calc _ ≤ ({a, -a} : Finset Kˣ).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have h2 : (Finset.univ : Finset Kˣ).card = Nat.card K - 1 := by
      rw [Finset.card_univ, Fintype.card_units, Nat.card_eq_fintype_card]
    omega
  have hmain := finrank_ge_card_of_free_action (p := p) (V := V) hp2 ψ.range hP hPne S'
    (fun s hs x hx => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨w, rfl⟩ := hx
      exact ⟨_, (hδ _ w.toAdd).symm⟩)
    (fun s hs x hx => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨w, rfl⟩ := hx
      exact ⟨_, (hδ' _ w.toAdd).symm⟩)
    (fun s hs s' hs' hne χ hχ => by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hs'
      have hcc' : c ≠ c' := fun h => hne (by rw [h])
      set a := rep c with ha
      set b := rep c' with hb
      have hab : (a : K) ^ 2 ≠ (b : K) ^ 2 := by
        intro h
        apply hcc'
        rw [← hrep c hc, ← hrep c' hc']
        exact Units.ext (by simpa [Units.val_pow_eq_pow_val] using h)
      have hα : ((a : K) ^ 2)⁻¹ - ((b : K) ^ 2)⁻¹ ≠ 0 := by
        intro h
        have ha0 : (a : K) ^ 2 ≠ 0 := pow_ne_zero _ a.ne_zero
        have hb0 : (b : K) ^ 2 ≠ 0 := pow_ne_zero _ b.ne_zero
        exact hab (inv_injective (sub_eq_zero.1 h))
      let χ' : Multiplicative K →* (AlgebraicClosure (ZMod 2))ˣ := χ.comp ψ.rangeRestrict
      have key : ∀ (c : Kˣ) (w : K) (h : (δ c)⁻¹ * ψ (Multiplicative.ofAdd w) * δ c ∈ ψ.range),
          χ ⟨(δ c)⁻¹ * ψ (Multiplicative.ofAdd w) * δ c, h⟩ =
            χ' (Multiplicative.ofAdd (((c : K) ^ 2)⁻¹ * w)) :=
        fun c w h => congrArg χ (Subtype.ext (hδ' c w))
      have hχ'1 : ∀ w : K, χ' (Multiplicative.ofAdd (((a : K) ^ 2)⁻¹ * w)) =
          χ' (Multiplicative.ofAdd (((b : K) ^ 2)⁻¹ * w)) := by
        intro w
        have := hcon ⟨ψ (Multiplicative.ofAdd w), ⟨_, rfl⟩⟩
        exact (key a w _).symm.trans (this.trans (key b w _))
      have hχ'v : ∀ v : K, χ' (Multiplicative.ofAdd v) = 1 := by
        intro v
        have h1 := hχ'1 ((((a : K) ^ 2)⁻¹ - ((b : K) ^ 2)⁻¹)⁻¹ * v)
        have h2 : ((a : K) ^ 2)⁻¹ * ((((a : K) ^ 2)⁻¹ - ((b : K) ^ 2)⁻¹)⁻¹ * v) =
            v + ((b : K) ^ 2)⁻¹ * ((((a : K) ^ 2)⁻¹ - ((b : K) ^ 2)⁻¹)⁻¹ * v) := by
          field_simp
          ring
        rw [h2, ofAdd_add, map_mul] at h1
        simpa using h1
      apply hχ
      refine MonoidHom.ext fun y => ?_
      obtain ⟨y, w, rfl⟩ := y
      exact hχ'v w.toAdd)
  have hSle : S'.card ≤ Module.finrank (ZMod 2) V := hmain
  omega

theorem oddL2_finrank_bound [Finite V] {L : Subgroup (GLV V)} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hmodel : StatedClassicalModel ↥L .PSL 2 p f) :
    (p ^ f - 1) / 2 ≤ Module.finrank (ZMod 2) V ∧ p ∣ Nat.card ↥L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  obtain ⟨-, -, hcard, hinj, ⟨U, hUeq, hUel, -⟩, hD, -⟩ := odd_psl_two_sylow_data hp2 hK
  refine ⟨?_, ?_⟩
  · have := sub_one_div_two_le_finrank hp2 e (stU K) hinj (hUeq ▸ hUel) stD hD
    rwa [hK] at this
  · rw [Nat.card_congr e.toEquiv, hcard]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by have := one_le_of_card_eq_pow hK; omega)) _

theorem g93Hyp_of_oneCompSetting [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : OneCompSetting Γ A L m) : G93Hyp Γ A L L m :=
  ⟨h.quotient, h.A_le, h.A_elem, h.A_card, h.bound, h.L_comp, h.L_comm, h.L_comp.1,
    h.L_normal, h.L_irr, Or.inl rfl⟩

theorem oddL2Big_orderOf_two_11 : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem oddL2Big_orderOf_two_13 : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

section
variable [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}

theorem false_of_oddL2Big_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : p ≠ 5) (h7 : p ≠ 7)
    (h : G93Hyp Γ A L L m) (hmodel : StatedClassicalModel ↥L .PSL 2 p 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hne3 : p ≠ 3 := by
    rintro rfl
    exact hmodel.1.2.2.2.2 (by norm_num)
  have hp11 : 11 ≤ p := by
    by_contra hlt
    push Not at hlt
    interval_cases p <;> first | omega | (exfalso; norm_num at hp)
  have hm : m ≤ 2 := m_le_of_autRank h (MulEquiv.refl ↥L)
    (fun B hc h2 => card_elemAbelian_mulAut_of_model_prime (by omega) hmodel B hc h2)
  obtain ⟨hd, hdvd⟩ := oddL2_finrank_bound hp hp2 hmodel
  have hb := h.bound
  rw [pow_one] at hd
  by_cases hp17 : 17 ≤ p
  · omega
  · have hp1113 : p = 11 ∨ p = 13 := by
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)
    have hord := orderOf_two_le_finrank_of_dvd_card L hp2 hdvd
    rcases hp1113 with rfl | rfl
    · rw [oddL2Big_orderOf_two_11] at hord
      omega
    · rw [oddL2Big_orderOf_two_13] at hord
      omega

theorem false_of_oddL2Big_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h9 : p ^ 2 ≠ 9)
    (h : G93Hyp Γ A L L m) (hmodel : StatedClassicalModel ↥L .PSL 2 p 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    push Not at hlt
    interval_cases p <;> first | omega | (exfalso; norm_num at hp)
  have hm : m ≤ 3 := m_le_of_autRank h (MulEquiv.refl ↥L)
    (fun B hc h2 => card_elemAbelian_mulAut_of_model_prime_sq hp5 hmodel B hc h2)
  obtain ⟨hd, -⟩ := oddL2_finrank_bound hp hp2 hmodel
  have hb := h.bound
  have : 25 ≤ p ^ 2 := by nlinarith
  omega

end

theorem oneCompFor_famOddL2Big : OneCompFor FamOddL2Big := by
  intro V _ _ _ Γ A L m hs ⟨_, p, hp, hp2, f, hf, h5, h7, h9, hmodel⟩
  exfalso
  have h := g93Hyp_of_oneCompSetting hs
  rcases hf with rfl | rfl
  · rw [pow_one] at h5 h7
    exact false_of_oddL2Big_prime hp hp2 h5 h7 h hmodel
  · exact false_of_oddL2Big_sq hp hp2 h9 h hmodel

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
