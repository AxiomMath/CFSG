module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8Basic
public import CFSG.Quasithin.EmptyFaithful.SBc8V2
public import CFSG.Quasithin.EmptyFaithful.SzC4Pair

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement

section Vec

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem s8b_vectors (h113 : StageLemma14113) (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    {F : Type} [Field F] [Fintype F] (hF2 : Fintype.card F = 2)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hE2 : IsE2 (2 * 1) ↥(c134CQ I L))
    (hdisj : c134CQ I L ⊓ ⁅centerOf (c134Q I L), L⁆ = ⊥)
    (hU : IsSumOfNaturalModulesVia L ⁅centerOf (c134Q I L), L⁆ ⊥ α false 1) :
    ∃ c₀ u₀ v : G, c₀ ∈ c134CQ I L ∧ c₀ ≠ 1 ∧ c₀ ∈ V₁ ∧ v ∈ V₁ ∧ v ≠ 1 ∧ v ≠ c₀ ∧
      (∀ e ∈ V₁, e = 1 ∨ e = c₀ ∨ e = v ∨ e = c₀ * v) ∧ c₀ * v = v * c₀ ∧
      (∀ s ∈ Sgp153 T V₁, s * c₀ = c₀ * s) ∧
      (∀ s ∈ Sgp153 T V₁, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = c₀ * v) ∧
      u₀ ∈ ⁅centerOf (c134Q I L), L⁆ ∧ u₀ ≠ 1 ∧ (∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s) ∧
      ∃ y ∈ Yp, y * u₀ * y⁻¹ ≠ u₀ := by
  classical
  obtain ⟨-, hLI, hIL, -, hsyl, -⟩ := ctx_basic c
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hdec : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  have hQS : c134Q I L ≤ Sgp153 T V₁ := s8_Q_le_S c
  have hQN : I ≤ Subgroup.normalizer (c134Q I L : Set G) := s8_I_le_normalizer_Q c
  have hZN : ∀ g ∈ Subgroup.normalizer (c134Q I L : Set G),
      g ∈ Subgroup.normalizer ((centerOf (c134Q I L) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hg, S153F.mem_normalizer_centralizer_of_mem_normalizer hg⟩
  have hCS : c134CQ I L ≤ Sgp153 T V₁ := (inf_le_left : c134CQ I L ≤ c134Q I L).trans hQS
  have hSC : Sgp153 T V₁ ≤ Subgroup.normalizer (c134CQ I L : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hQN (hSI hs),
      S153F.mem_normalizer_centralizer_of_mem_normalizer (hIL (hSI hs))⟩
  have hLZ : L ≤ Subgroup.normalizer ((centerOf (c134Q I L) : Subgroup G) : Set G) :=
    fun l hl => hZN l (hQN (hLI hl))
  have hUZ : ⁅centerOf (c134Q I L), L⁆ ≤ centerOf (c134Q I L) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLZ
  have hUS : ⁅centerOf (c134Q I L), L⁆ ≤ Sgp153 T V₁ :=
    hUZ.trans ((inf_le_left : centerOf (c134Q I L) ≤ c134Q I L).trans hQS)
  have hSU : Sgp153 T V₁ ≤
      Subgroup.normalizer ((⁅centerOf (c134Q I L), L⁆ : Subgroup G) : Set G) := fun s hs =>
    S153H.mem_normalizer_commutator (hZN s (hQN (hSI hs))) (hIL (hSI hs))
  have hC4 : Nat.card ↥(c134CQ I L) = 4 := by
    rw [s8_card_eq_of_isE2 hE2]
    norm_num
  have hCsq : ∀ x ∈ c134CQ I L, x * x = 1 := fun x hx => by
    have := s8_sq_eq_one_of_isE2 hE2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hE := s8_omegaOneCenter c
  obtain ⟨c₀, hc₀C, u₀, hu₀U, hc₀1, hu₀1, hcu1, hc₀S, hu₀S, hc₀E, hu₀E, hcuE, hEall⟩ :=
    case4_pair (E := omegaOneCenterOf (Sgp153 T V₁)) hF2 hU hS2 hC4 hCsq hCS hSC hUS hSU hdisj rfl
      hE.2
  have hc₀L : ∀ l ∈ L, l * c₀ = c₀ * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hc₀C.2 l hl
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  obtain ⟨-, -, hMN, hV₂card, hV₂fix⟩ := SBc8.V₂_facts h113 c.toCtx15330
  have hc₀V : c₀ ∈ VZ T M := by
    have h := hc₀E
    rw [hE.1] at h
    exact h.1
  have hYpL : Yp ≤ L := c.c27.Yp_le
  have hc₀V₁ : c₀ ∈ V₁ := by
    obtain ⟨a, ha, b, hb, hab⟩ := SBd2.exists_mul_of_mem_sup'
      (fun a ha b hb => hVab a (hdec.le₁ ha) b (hdec.le₂ hb)) (by rw [hdec.sup]; exact hc₀V)
    have hbfix : ∀ y ∈ Yp, y * b * y⁻¹ = b := by
      intro y hy
      have hya : y * a * y⁻¹ = a := by
        have := Subgroup.mem_centralizer_iff.mp (c.c29.cent hy) a ha
        calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [← this]
          _ = a := by group
      have hyc : y * c₀ * y⁻¹ = c₀ := by
        calc y * c₀ * y⁻¹ = c₀ * y * y⁻¹ := by rw [hc₀L y (hYpL hy)]
          _ = c₀ := by group
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [hab, hyc, hya] at e
      exact (mul_left_cancel (hab.trans e)).symm
    have hb1 : b = 1 := by
      by_contra hb1
      obtain ⟨y, hy, hne⟩ := hV₂fix b hb hb1
      exact hne (hbfix y hy)
    rw [hb1, mul_one] at hab
    rw [← hab]
    exact ha
  obtain ⟨v, hvV, hv1, hvc⟩ : ∃ v ∈ V₁, v ≠ 1 ∧ v ≠ c₀ := by
    by_contra hcon
    push Not at hcon
    have hsub : (V₁ : Set G) ⊆ {1, c₀} := fun x hx => by
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hcon x hx hx1]
    have h1 : Set.ncard (V₁ : Set G) ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le _ _ |>.trans (by simp))
    have h2 : Nat.card ↥V₁ = Set.ncard (V₁ : Set G) := Nat.card_coe_set_eq _
    have := hdec.card₁
    omega
  have hc₀sq : c₀ * c₀ = 1 := hCsq c₀ hc₀C
  have hcv1 : c₀ * v ≠ 1 := by
    intro h
    apply hvc
    have h1 : v = c₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hc₀sq
  have hVall : ∀ e ∈ V₁, e = 1 ∨ e = c₀ ∨ e = v ∨ e = c₀ * v :=
    mem_of_card_four hdec.card₁ hc₀V₁ hvV hc₀1 hv1 hvc.symm hcv1
  have hcomm : c₀ * v = v * c₀ := hVab c₀ (hdec.le₁ hc₀V₁) v (hdec.le₁ hvV)
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := fun s hs => hs.2
  have hsv : ∀ s ∈ Sgp153 T V₁, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = c₀ * v := by
    intro s hs
    have hmem : s * v * s⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hSN hs) v).mp hvV
    have hc₀s : s * c₀ * s⁻¹ = c₀ := by
      calc s * c₀ * s⁻¹ = c₀ * s * s⁻¹ := by rw [hc₀S s hs]
        _ = c₀ := by group
    rcases hVall _ hmem with h | h | h | h
    · exfalso
      apply hv1
      have : s * v * s⁻¹ = 1 := h
      simpa using this
    · exfalso
      apply hvc
      have h' : s * v * s⁻¹ = s * c₀ * s⁻¹ := by rw [h, hc₀s]
      have := mul_right_cancel (mul_left_cancel (a := s) (b := v * s⁻¹) (c := c₀ * s⁻¹)
        (by simpa [mul_assoc] using h'))
      exact this
    · exact Or.inl h
    · exact Or.inr h
  have hSM : Sgp153 T V₁ ≤ M ⊓ I := le_inf (inf_le_right.trans c.c29.norm_le) hSI
  obtain ⟨w, hwV, hw1, hwfix⟩ :=
    s8_exists_fixed hS2 (hSM.trans hMN) (by rw [hV₂card]; exact ⟨2, rfl⟩)
  have hwZ : w ∈ omegaOneCenterOf (Sgp153 T V₁) := by
    rw [hE.1]
    refine ⟨hdec.le₂ hwV, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have := hwfix s hs
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨y, hy, hne⟩ := hV₂fix w hwV hw1
  have hyc : y * c₀ * y⁻¹ = c₀ := by
    calc y * c₀ * y⁻¹ = c₀ * y * y⁻¹ := by rw [hc₀L y (hYpL hy)]
      _ = c₀ := by group
  have hmoved : ∃ y ∈ Yp, y * u₀ * y⁻¹ ≠ u₀ := by
    refine ⟨y, hy, fun hu => hne ?_⟩
    rcases hEall w hwZ with h | h | h | h
    · exact absurd h hw1
    · exfalso
      have hwV₁ : w ∈ V₁ := h ▸ hc₀V₁
      have : w ∈ V₁ ⊓ V₂ := ⟨hwV₁, hwV⟩
      rw [hdec.inf, Subgroup.mem_bot] at this
      exact hw1 this
    · rw [h]
      exact hu
    · rw [h]
      have e : y * (c₀ * u₀) * y⁻¹ = (y * c₀ * y⁻¹) * (y * u₀ * y⁻¹) := by group
      rw [e, hyc, hu]
  exact ⟨c₀, u₀, v, hc₀C, hc₀1, hc₀V₁, hvV, hv1, hvc, hVall, hcomm, hc₀S, hsv, hu₀U, hu₀1, hu₀S,
    hmoved⟩

end Vec

end CFSG.Quasithin.SzC4
