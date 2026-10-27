module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

private theorem uc119_mem_of_isTI (D : Data G) {V₀ : Subgroup G} (hV₀ : InCalV D.M V₀)
    (hTI₀ : IsTI V₀) {t g : G} (ht : t ∈ V₀) (ht1 : t ≠ 1) (hg : g⁻¹ * t * g ∈ V₀) :
    g ∈ D.M := by
  have hmem : t ∈ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ :=
    ⟨ht, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr hg⟩
  have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ ≠ ⊥ :=
    fun h => ht1 (Subgroup.mem_bot.mp (h ▸ hmem))
  have hle : V₀ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ :=
    inf_eq_left.mp ((hTI₀ g).resolve_left hne)
  have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup g V₀) ≤ Nat.card V₀ :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).le
  have heq : V₀ = CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hgN : g ∈ normalizer (V₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    rw [← CFSG.CGT.Timmesfeld75.mem_conjSubgroup, ← heq]
  rw [← PartTwo.normalizer_eq_of_inCalV D hV₀]
  exact hgN

private theorem uc119_mem_of_uniqueMax (D : Data G) {X : Subgroup G} (hU : UniqueMax D.M X)
    {a : G} (hXa : X ≤ centralizer ({a} : Set G)) (h : G)
    (hCb : centralizer ({h * a * h⁻¹} : Set G) ≤ D.M) : h ∈ D.M := by
  have hXM' : X ≤ uniqueFourConj h D.M := by
    intro x hx
    rw [UC6.mem_uniqueFourConj_iff]
    apply hCb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp (hXa hx) a rfl
    calc h * a * h⁻¹ * (h * x * h⁻¹) = h * (a * x) * h⁻¹ := by group
      _ = h * (x * a) * h⁻¹ := by rw [hxa]
      _ = h * x * h⁻¹ * (h * a * h⁻¹) := by group
  have hmem : uniqueFourConj h D.M ∈ calMOf X := ⟨UC6.isMaxTwoLocal_conj D.maxLocal h, hXM'⟩
  rw [hU] at hmem
  have hconj : uniqueFourConj h D.M = D.M := Set.mem_singleton_iff.mp hmem
  rw [← UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal]
  exact UC6.uniqueFourConj_eq_self_iff.mp hconj

theorem uniqueMax_map_conj (D : Data G) {X : Subgroup G} (hX : UniqueMax D.M X) {c : G}
    (hc : c ∈ D.M) : UniqueMax D.M (X.map (MulAut.conj c).toMonoidHom) := by
  unfold UniqueMax at hX ⊢
  have hXM : X ≤ D.M := by
    have hmem : D.M ∈ calMOf X := by
      rw [hX]
      exact Set.mem_singleton_iff.mpr rfl
    exact hmem.2
  ext N
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hX'N⟩
    have hconj : uniqueFourConj c N ∈ calMOf X := by
      refine ⟨UC6.isMaxTwoLocal_conj hN c, ?_⟩
      intro x hx
      rw [UC6.mem_uniqueFourConj_iff]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hX'N ⟨x, hx, rfl⟩
    rw [hX] at hconj
    have hNM : uniqueFourConj c N = D.M := Set.mem_singleton_iff.mp hconj
    have hle : N ≤ D.M := by
      intro n hn
      have hx : c⁻¹ * n * c ∈ uniqueFourConj c N := by
        rw [UC6.mem_uniqueFourConj_iff]
        rw [show c * (c⁻¹ * n * c) * c⁻¹ = n by group]
        exact hn
      have hxM : c⁻¹ * n * c ∈ D.M := hNM ▸ hx
      have : n = c * (c⁻¹ * n * c) * c⁻¹ := by group
      rw [this]
      exact D.M.mul_mem (D.M.mul_mem hc hxM) (D.M.inv_mem hc)
    have hle' : D.M ≤ N := by
      intro m hm
      have hx : c⁻¹ * m * c ∈ uniqueFourConj c N := by
        rw [hNM]
        exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hc) hm) hc
      rw [UC6.mem_uniqueFourConj_iff] at hx
      rwa [show c * (c⁻¹ * m * c) * c⁻¹ = m by group] at hx
    exact le_antisymm hle hle'
  · rintro rfl
    refine ⟨D.maxLocal, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hc (hXM hx)) (D.M.inv_mem hc)

theorem isTI_of_cover_uniqueMax (D : Data G) {V₀ V : Subgroup G} (hV : InCalV D.M V)
    (hV₀ : InCalV D.M V₀) (hTI₀ : IsTI V₀)
    (hcov : ∀ u ∈ V, u ∉ V₀ → ∃ X : Subgroup G, X ≤ D.M ∧ UniqueMax D.M X ∧
      X ≤ centralizer ({u} : Set G)) : IsTI V := by
  have hCA : ∀ t ∈ V, t ≠ 1 → centralizer ({t} : Set G) ≤ D.M := by
    intro t ht ht1
    by_cases htV₀ : t ∈ V₀
    · intro z hz
      have hzt : t * z = z * t := Subgroup.mem_centralizer_iff.mp hz t rfl
      have hconj : z⁻¹ * t * z = t := by
        calc z⁻¹ * t * z = z⁻¹ * (t * z) := by group
          _ = z⁻¹ * (z * t) := by rw [hzt]
          _ = t := by group
      exact uc119_mem_of_isTI D hV₀ hTI₀ htV₀ ht1 (by rw [hconj]; exact htV₀)
    · obtain ⟨X, -, hU, hXt⟩ := hcov t ht htV₀
      obtain ⟨N, hNmax, hCN⟩ := uc22p22u_exists_isMaxTwoLocal
        (uc22p22u_isTwoLocal_centralizer ht1 (hV.2.2.2.2 t ht))
      have hmem : N ∈ calMOf X := ⟨hNmax, hXt.trans hCN⟩
      rw [hU] at hmem
      have hNM : N = D.M := Set.mem_singleton_iff.mp hmem
      exact hCN.trans (le_of_eq hNM)
  intro g
  by_cases hbot : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huV : u ∈ V := hu.1
  have hw : g⁻¹ * u * g ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hu.2
  have hw1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hgM : g ∈ D.M := by
    by_cases huV₀ : u ∈ V₀
    · by_cases hwV₀ : g⁻¹ * u * g ∈ V₀
      · exact uc119_mem_of_isTI D hV₀ hTI₀ huV₀ hu1 hwV₀
      · obtain ⟨X, -, hU, hXw⟩ := hcov _ hw hwV₀
        refine uc119_mem_of_uniqueMax D hU hXw g ?_
        have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
        rw [e]
        exact hCA u huV hu1
    · obtain ⟨X, -, hU, hXu⟩ := hcov u huV huV₀
      have hg' : g⁻¹ ∈ D.M := by
        refine uc119_mem_of_uniqueMax D hU hXu g⁻¹ ?_
        rw [inv_inv]
        exact hCA _ hw hw1
      exact inv_mem_iff.mp hg'
  have hgV : g ∈ normalizer (V : Set G) := hV.2.2.1 hgM
  have hVc : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    exact ((Subgroup.mem_normalizer_iff'').mp hgV x).symm
  change V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = V
  rw [hVc, inf_idem]

theorem isCyclic_inf_ctilde (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup G} (hXM : X ≤ D.M) (hX : IsPGroup p X)
    (hΓ : rankThreeGamma 1 p X ≤ D.M ∨ p ∈ D.sig) :
    IsCyclic ↥(X ⊓ F11.CTilde D.M V₀ V) := by
  by_contra hnc
  obtain ⟨hV, hV₀V, hMV₀, hcase⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨E, hE, hEab, hEcard⟩ :=
    uc22p22u_exists_elemAbelian_sq hp hp2 hX.to_inf_left hnc
  have hEC : E ≤ F11.CTilde D.M V₀ V := hE.trans inf_le_right
  have hEX : E ≤ X := hE.trans inf_le_left
  have hEM : E ≤ D.M := hEC.trans uc22p22q_ctilde_le
  have hEp : IsPGroup p E := uc22p22e_isPGroup_of_elem hEab
  have hEnc : ¬ IsCyclic E := uc22p22n_not_isCyclic_of_card hp hEab hEcard.ge
  have hΓE : rankThreeGamma 1 p E ≤ D.M ∨ p ∈ D.sig :=
    hΓ.imp_left fun h => (uc22p22u_gamma_mono hEX).trans h
  have hUE : UniqueMax D.M E :=
    uc22p22u_uniqueMax_of_noncyclic D h61 h63 hp hp2 hEM hEp hEnc hΓE
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.2.2.2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVexp : ∀ d ∈ V, d ^ 2 = 1 := hV.2.2.2.2
  have hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1 := fun d hd => hVexp d (hV₀V hd)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEctil : ∀ e ∈ E, e ∈ D.M ∧ e ∈ normalizer (V₀ : Set G) ∧
      ∀ v ∈ V, e * v * e⁻¹ * v⁻¹ ∈ V₀ := fun e he => uc22p22q_mem_ctilde.1 (hEC he)
  by_cases hA : ∀ e ∈ E, ∀ d ∈ V₀, e * d * e⁻¹ = d
  · have hEcV : E ≤ centralizer (V : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := uc22p22q_conj_eq_of_trivial_action hp hp2 hV₀exp (hEab.2 e he) (hA e he)
        ((hEctil e he).2.2 v hv)
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    exact hH.2.1 (uc22p22u_isTI_of_uniqueMax D hV.2.2.2 hV.2.2.1 hEcV hUE)
  · push Not at hA
    obtain ⟨x, hxE, d₀, hd₀, hxd₀⟩ := hA
    have hxN : ∀ d ∈ V₀, x * d * x⁻¹ ∈ V₀ := fun d hd =>
      (mem_normalizer_iff.1 (hEctil x hxE).2.1 d).1 hd
    obtain ⟨h4eq, hp3, hfpf⟩ :=
      uc22p22q_klein_action h4 hV₀exp hp hp2 hxN (hEab.2 x hxE) ⟨d₀, hd₀, hxd₀⟩
    subst hp3
    have hd₀1 : d₀ ≠ 1 := fun h => hxd₀ (by rw [h]; group)
    have hV₀bot : V₀ ≠ ⊥ := fun h => hd₀1 (by simpa [h] using hd₀)
    obtain ⟨hV₀, hTI₀, hgen⟩ := hcase.resolve_left hV₀bot
    have hx3 : x ^ 3 = 1 := hEab.2 x hxE
    refine hH.2.1 (isTI_of_cover_uniqueMax D hV hV₀ hTI₀ ?_)
    intro u huV huV₀
    obtain ⟨d₁, hd₁, hfix⟩ := uc22p22q_exists_fixed_in_coset hVab hV₀exp hV₀V hxN hx3 huV
      ((hEctil x hxE).2.2 u huV)
    set u' : G := u * d₁ with hu'
    have hu'V : u' ∈ V := V.mul_mem huV (hV₀V hd₁)
    have hEfix : ∀ e ∈ E, e * u' * e⁻¹ = u' := by
      intro e he
      set d₂ : G := e * u' * e⁻¹ * u'⁻¹ with hd₂
      have hd₂V₀ : d₂ ∈ V₀ := (hEctil e he).2.2 u' hu'V
      have hw : e * u' * e⁻¹ = d₂ * u' := by simp [hd₂]
      have hxe : x * e = e * x := hEcomm x hxE e he
      have h1 : x * (e * u' * e⁻¹) * x⁻¹ = e * u' * e⁻¹ := by
        calc x * (e * u' * e⁻¹) * x⁻¹ = (x * e) * u' * (x * e)⁻¹ := by group
          _ = (e * x) * u' * (e * x)⁻¹ := by rw [hxe]
          _ = e * (x * u' * x⁻¹) * e⁻¹ := by group
          _ = e * u' * e⁻¹ := by rw [hfix]
      have h2 : x * (d₂ * u') * x⁻¹ = (x * d₂ * x⁻¹) * u' := by
        calc x * (d₂ * u') * x⁻¹ = (x * d₂ * x⁻¹) * (x * u' * x⁻¹) := by group
          _ = (x * d₂ * x⁻¹) * u' := by rw [hfix]
      rw [hw, h2] at h1
      have h3 : x * d₂ * x⁻¹ = d₂ := mul_right_cancel h1
      by_contra hne
      have hd21 : d₂ ≠ 1 := fun h => hne (by rw [hw, h, one_mul])
      exact hfpf d₂ hd₂V₀ hd21 h3
    obtain ⟨c, hcC, hcu⟩ := uc22p22q_coset_transitive
      (fun m hm c hc => uc22p22q_ctilde_conj_mem hV.2.2.1 hMV₀ hm hc) hV₀V hVab h4eq
      (fun c hc v hv => (uc22p22q_mem_ctilde.1 hc).2.2 v hv) hu'V (hgen u' hu'V (by
        intro h
        exact huV₀ (by
          have : u = u' * d₁⁻¹ := by simp [hu']
          rw [this]
          exact V₀.mul_mem h (V₀.inv_mem hd₁))))
      (hEC hxE) (hfix) hx3 hfpf d₁⁻¹ (V₀.inv_mem hd₁)
    have hcu' : c * u' * c⁻¹ = u := by
      rw [hcu]
      simp [hu']
    refine ⟨E.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      have hcM : c ∈ D.M := uc22p22q_ctilde_le hcC
      exact D.M.mul_mem (D.M.mul_mem hcM (hEM he)) (D.M.inv_mem hcM)
    · exact uniqueMax_map_conj D hUE (uc22p22q_ctilde_le hcC)
    · rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h1 := hEfix e he
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hcu']
      calc c * u' * c⁻¹ * (c * e * c⁻¹) = c * (u' * e) * c⁻¹ := by group
        _ = c * (e * u') * c⁻¹ := by
          rw [show u' * e = e * u' from by
            have := h1
            exact (mul_inv_eq_iff_eq_mul.1 this).symm]
        _ = c * e * c⁻¹ * (c * u' * c⁻¹) := by group

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
