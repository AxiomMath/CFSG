module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qr
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22q_ctilde_le {M V₀ V : Subgroup G} : F11.CTilde M V₀ V ≤ M :=
  fun _ hc => (uc22p22q_mem_ctilde.1 hc).1

theorem uc22p22q_hyp11_unpack (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    InCalV D.M V ∧ V₀ ≤ V ∧ D.M ≤ normalizer (V₀ : Set G) ∧
      (V₀ = ⊥ ∨ (InCalV D.M V₀ ∧ IsTI V₀ ∧
        ∀ v ∈ V, v ∉ V₀ → Subgroup.closure {x : G | ∃ m ∈ D.M, x = m * v * m⁻¹} = V)) := by
  rcases hH.1 with h | ⟨h0, hW⟩
  · obtain ⟨hV₀, hV, hle, hTI₀, -, hgen, -⟩ := h
    exact ⟨hV, hle, hV₀.2.2.1, Or.inr ⟨hV₀, hTI₀, hgen⟩⟩
  · subst h0
    refine ⟨hW.1.1, bot_le, fun m _ => ?_, Or.inl rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      simp
    · intro hh
      calc h = m⁻¹ * (m * h * m⁻¹) * m := by group
        _ = 1 := by rw [hh]; group

theorem uc22p22q_pRank_ctilde_le_one (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (F11.CTilde D.M V₀ V) ≤ 1 := by
  obtain ⟨hV, hV₀V, hMV₀, hcase⟩ := uc22p22q_hyp11_unpack D hH
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpP⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt (F11.CTilde D.M V₀ V)
  have hEM : E ≤ D.M := hEC.trans uc22p22q_ctilde_le
  have hEp : IsPGroup p E := uc22p22e_isPGroup_of_elem hE
  have hEnc : ¬ IsCyclic E := uc22p22n_not_isCyclic_of_card hpP hE (by
    rw [hEcard]
    exact Nat.pow_le_pow_right hpP.pos hlt)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.2.2.2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVexp : ∀ d ∈ V, d ^ 2 = 1 := hV.2.2.2.2
  have hV₀exp : ∀ d ∈ V₀, d ^ 2 = 1 := fun d hd => hVexp d (hV₀V hd)
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEctil : ∀ e ∈ E, e ∈ D.M ∧ e ∈ normalizer (V₀ : Set G) ∧ ∀ v ∈ V, e * v * e⁻¹ * v⁻¹ ∈ V₀ :=
    fun e he => uc22p22q_mem_ctilde.1 (hEC he)
  by_cases hA : ∀ e ∈ E, ∀ d ∈ V₀, e * d * e⁻¹ = d
  ·
    refine hH.2.1 (uc22p22n_isTI_of_noncyclic D h61 hp hV hEM hEp hEnc ?_)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := uc22p22q_conj_eq_of_trivial_action hpP hp2 hV₀exp (hE.2 e he) (hA e he)
      ((hEctil e he).2.2 v hv)
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · push Not at hA
    obtain ⟨x, hxE, d₀, hd₀, hxd₀⟩ := hA
    have hxN : ∀ d ∈ V₀, x * d * x⁻¹ ∈ V₀ := fun d hd =>
      (mem_normalizer_iff.1 (hEctil x hxE).2.1 d).1 hd
    obtain ⟨h4eq, hp3, hfpf⟩ := uc22p22q_klein_action h4 hV₀exp hpP hp2 hxN (hE.2 x hxE) ⟨d₀, hd₀, hxd₀⟩
    subst hp3
    have hd₀1 : d₀ ≠ 1 := fun h => hxd₀ (by rw [h]; group)
    have hV₀bot : V₀ ≠ ⊥ := fun h => hd₀1 (by simpa [h] using hd₀)
    obtain ⟨hV₀, hTI₀, hgen⟩ := hcase.resolve_left hV₀bot
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    refine hH.2.1 (uc22p22q_isTI_of_cover D h61 hp hV hV₀ hV₀V hTI₀ ?_)
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
      have hxe : x * e = e * x := hEab x hxE e he
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
    refine ⟨E.map (MulAut.conj c).toMonoidHom, ?_, hEp.map _, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      have hcM : c ∈ D.M := uc22p22q_ctilde_le hcC
      exact D.M.mul_mem (D.M.mul_mem hcM (hEM he)) (D.M.inv_mem hcM)
    · intro hcyc
      exact hEnc ((Subgroup.equivMapOfInjective E (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).isCyclic.2 hcyc)
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

theorem uc22p22q_r115_of (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) : F11.R115 D := by
  intro V₀ V hH h4 p hp
  have hA := uc22p22q_pRank_ctilde_le_one D h61 hH h4 hp
  refine ⟨hA, ?_, ?_⟩
  · intro hN
    exact uc22p22q_pRank_sub_one_le (D.sig_prime p hp).1 hA
  · have := hx.three_le p hp
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
