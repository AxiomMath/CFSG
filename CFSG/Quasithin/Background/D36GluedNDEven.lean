module

public import CFSG.Quasithin.Background.D36GluedNDBase
import CFSG.Quasithin.Background.D36GluedNDOut
import CFSG.Quasithin.Background.F918Z4bL2
import CFSG.Quasithin.Background.F918Z4c1PSL
import CFSG.Quasithin.Background.F918Z4c2Main

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

theorem conj_injective_of_simple {G : Type} [Group G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  have hc : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have : a ∈ Subgroup.center G := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.mp this) b).symm
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut G => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hc] at this
  exact Subgroup.mem_bot.mp this

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem false_of_psl2_two {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 2 2 n ↥L₀) : False := by
  have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hdim : ∀ {d : ℕ} (ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2)),
      Function.Injective ρ → 2 * n ≤ d := by
    intro d ρ hρ
    by_cases h3 : n = 3
    · subst h3
      have := Z4c2.six_le_of_psl2_eight hL hF2 ρ hρ
      omega
    · have := two_mul_le_of_psl2_two (by omega) h3 hL hF2 ρ hρ
      omega
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have h2n := hdim ρ hρ
  have hAut := autRankLe_psl2_two (by omega) hL
  have hk := S.rk_le hAut
  obtain ⟨hs1, -, hB⟩ := S.swap.shape_B S.exp
  have hkn : rk ↥(A ⊓ stabSub U) = n := by omega
  have hinj := conj_injective_of_simple S.simple S.nonab
  set E : Subgroup (MulAut ↥L₀) := S.theta.range with hEdef
  have hE : IsElemAb2 E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
      rw [← map_mul, ← map_mul, (S.elemAb.1 b₁ b₁.2 b₂ b₂.2 |> Subtype.ext : b₁ * b₂ = b₂ * b₁)]
    · rintro _ ⟨b, rfl⟩
      rw [← map_pow, (Subtype.ext (S.elemAb.2 b b.2) : b ^ 2 = 1), map_one]
  have hEk : rk E = n := by
    rw [← hkn]
    exact (rk_eq_of_mulEquiv (MonoidHom.ofInjective S.theta_injective)).symm
  have hOut := rk_le_rk_inf_inner_add_one (by omega) hL hE
  set R₀ : Subgroup ↥L₀ := (E ⊓ (MulAut.conj : ↥L₀ →* MulAut ↥L₀).range).comap
    (MulAut.conj : ↥L₀ →* MulAut ↥L₀) with hR₀def
  have hR₀el : IsElemAb2 R₀ := (hE.mono inf_le_left).comap _ hinj
  have hR₀rk : rk R₀ = rk ↥(E ⊓ (MulAut.conj : ↥L₀ →* MulAut ↥L₀).range) :=
    rk_comap_eq_of_le_range _ hinj inf_le_right
  have hR₀card : 2 ^ (n - 1) ≤ Nat.card R₀ := by
    rw [hR₀el.card_eq_two_pow]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨b, hb, hbnd⟩ : ∃ b ∈ A ⊓ stabSub U, ∀ l ∈ L₀, ∃ u ∈ U, b u ≠ l u := by
    by_contra hcon
    push Not at hcon
    exact S.nondiag hcon
  set φ : MulAut ↥L₀ := S.theta ⟨b, hb⟩ with hφdef
  have hφE : φ ∈ E := ⟨⟨b, hb⟩, rfl⟩
  have hφfix : ∀ r ∈ R₀, φ r = r := by
    intro r hr
    have hrE : MulAut.conj r ∈ E := hr.1
    have hcomm := hE.1 φ hφE _ hrE
    apply hinj
    rw [← mulAut_mul_conj_mul_inv_eq_conj φ r, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨e⟩ := exists_mulEquiv_psl2_galoisField (by omega) hL
  set φ' : MulAut (PSL2 (GaloisField 2 n)) := MulAut.congr e φ with hφ'def
  set R₀' : Subgroup (PSL2 (GaloisField 2 n)) := R₀.map e.toMonoidHom with hR₀'def
  have hR₀'card : Nat.card R₀' = Nat.card R₀ := by
    rw [hR₀'def, Subgroup.card_map_of_injective e.injective]
  have hR₀'p : IsPGroup 2 R₀' :=
    IsPGroup.of_card (n := rk R₀) (hR₀'card.trans hR₀el.card_eq_two_pow)
  obtain ⟨Q, hQ⟩ := hR₀'p.exists_le_sylow
  have hcongr : ∀ x, φ' x = e (φ (e.symm x)) := fun x => rfl
  have hfix' : ∀ x ∈ R₀', φ' x = x := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hcongr]
    show e (φ (e.symm (e r))) = e r
    rw [MulEquiv.symm_apply_apply, hφfix r hr]
  obtain ⟨s, -, hs⟩ := mulAut_inner_of_fixes_index_two hn Q R₀' hQ
    (by rw [hR₀'card]; exact hR₀card) φ' hfix'
  have hconj : ∀ l : ↥L₀, φ l = e.symm s * l * (e.symm s)⁻¹ := by
    intro l
    have h1 := congrArg (fun ψ : MulAut (PSL2 (GaloisField 2 n)) => ψ (e l)) hs
    simp only [hcongr, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    have h2 := congrArg e.symm h1
    simpa [map_mul, map_inv] using h2
  have hconj' : ∀ l ∈ L₀, b * l * b⁻¹ = (e.symm s : MulAut Y) * l * (e.symm s : MulAut Y)⁻¹ := by
    intro l hl
    have := congrArg (fun z : ↥L₀ => (z : MulAut Y)) (hconj ⟨l, hl⟩)
    simpa [hφdef, theta_apply] using this
  obtain ⟨u, hu, hne⟩ := hbnd (e.symm s) (e.symm s).2
  exact hne (S.inner b hb (e.symm s) (e.symm s).2 hconj' u hu)

end NDSetup

end CFSG.Quasithin
