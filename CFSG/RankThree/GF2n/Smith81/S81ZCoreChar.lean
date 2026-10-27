module

public import CFSG.RankThree.GF2n.Smith81.S81ZCoreFix
public import CFSG.RankThree.GF2n.Smith81.S81ZStab
public import CFSG.RankThree.GF2n.Smith81.S81ZTr
public import CFSG.RankThree.GF2n.Smith81.S81XE7Geom

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X

abbrev NormUA (K : Type) [Field K] : Subgroup (Gp K) :=
  Subgroup.normalizer ((UA K a7 : Subgroup (Gp K)) : Set (Gp K))

section Char

variable {K : Type} [Field K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]

theorem mem_normalizer_UA_of_line {g : Gp K} {c : K} (hc : c ≠ 0)
    (h : endoE g (w0 : V K) = c • (w0 : V K)) : g ∈ NormUA K := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_UA7_of_line hc h x hx
  · intro hx
    have hinv : endoE g⁻¹ (w0 : V K) = c⁻¹ • (w0 : V K) := by
      have h1 : endoE g (c⁻¹ • (w0 : V K)) = (w0 : V K) := by
        rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      have h2 := congrArg (fun v => endoE g⁻¹ v) h1
      simp only [map_smul, endoE_inv_endoE] at h2
      exact h2.symm
    have := conj_UA7_of_line (inv_ne_zero hc) hinv _ hx
    simpa [mul_assoc] using this

theorem fix7_map_le_of_normalizer (B : Gp K →* (X ≃ₗ[K] X)) {g : Gp K}
    (hg : g ∈ NormUA K) : (fix7 B).map (B g : X →ₗ[K] X) ≤ fix7 B := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_fix7]
  intro u hu
  have hc : g⁻¹ * u * g ∈ UA K a7 := by
    have := ((Subgroup.mem_normalizer_iff.1 ((NormUA K).inv_mem hg)) u).1 hu
    simpa using this
  have hfix : B (g⁻¹ * u * g) v = v := (mem_fix7 B).1 hv _ hc
  have key : B u * B g = B g * B (g⁻¹ * u * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg B (by group)
  have h2 : B u (B g v) = B g (B (g⁻¹ * u * g) v) := by
    rw [← LinearEquiv.mul_apply (B u) (B g), ← LinearEquiv.mul_apply (B g) (B (g⁻¹ * u * g)), key]
  show B u (B g v) = B g v
  rw [h2, hfix]

theorem scalar_mul (B : Gp K →* (X ≃ₗ[K] X)) {v₀ : X} (hne : v₀ ≠ 0) {g₁ g₂ : Gp K} {c₁ c₂ c : K}
    (h₁ : B g₁ v₀ = c₁ • v₀) (h₂ : B g₂ v₀ = c₂ • v₀) (h : B (g₁ * g₂) v₀ = c • v₀) :
    c = c₁ * c₂ := by
  rw [map_mul, LinearEquiv.mul_apply, h₂, map_smul, h₁, smul_smul] at h
  have := smul_left_injective K hne (h.symm.trans (by rw [mul_comm]))
  exact this

variable (B : Gp K →* (X ≃ₗ[K] X)) (hline : Module.finrank K (fix7 B) = 1) {v₀ : X}
  (hv₀ : v₀ ∈ fix7 B) (hne : v₀ ≠ 0)

include hline hv₀ hne

theorem exists_scalar_of_normalizer {g : Gp K} (hg : g ∈ NormUA K) :
    ∃ c : K, c ≠ 0 ∧ B g v₀ = c • v₀ := by
  have hmem : B g v₀ ∈ fix7 B := fix7_map_le_of_normalizer B hg (Submodule.mem_map_of_mem hv₀)
  have hnz : (⟨v₀, hv₀⟩ : ↥(fix7 B)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨B g v₀, hmem⟩
  have hc' : c • v₀ = B g v₀ := congrArg Subtype.val hc
  refine ⟨c, ?_, hc'.symm⟩
  rintro rfl
  rw [zero_smul] at hc'
  exact hne ((B g).injective (by rw [← hc', map_zero]))

noncomputable def charOf {H : Type} [Group H] (ι : H →* Gp K)
    (hι : ∀ h, ι h ∈ NormUA K) : H →* Kˣ :=
  MonoidHom.mk'
    (fun h => Units.mk0 (Classical.choose (exists_scalar_of_normalizer B hline hv₀ hne (hι h)))
      (Classical.choose_spec (exists_scalar_of_normalizer B hline hv₀ hne (hι h))).1)
    (fun h h' => by
      apply Units.ext
      set c := Classical.choose (exists_scalar_of_normalizer B hline hv₀ hne (hι (h * h'))) with hc
      set c₁ := Classical.choose (exists_scalar_of_normalizer B hline hv₀ hne (hι h)) with hc₁
      set c₂ := Classical.choose (exists_scalar_of_normalizer B hline hv₀ hne (hι h')) with hc₂
      have e := (Classical.choose_spec (exists_scalar_of_normalizer B hline hv₀ hne (hι (h * h')))).2
      have e1 := (Classical.choose_spec (exists_scalar_of_normalizer B hline hv₀ hne (hι h))).2
      have e2 := (Classical.choose_spec (exists_scalar_of_normalizer B hline hv₀ hne (hι h'))).2
      have e' : B (ι h * ι h') v₀ = c • v₀ := by rw [← map_mul]; exact e
      exact scalar_mul B hne e1 e2 e')

theorem charOf_spec {H : Type} [Group H] (ι : H →* Gp K) (hι : ∀ h, ι h ∈ NormUA K)
    (h : H) : B (ι h) v₀ = ((charOf B hline hv₀ hne ι hι h : Kˣ) : K) • v₀ :=
  (Classical.choose_spec (exists_scalar_of_normalizer B hline hv₀ hne (hι h))).2

omit hline hv₀ hne

theorem hhom_E5 (hChar : E5StabChar K) (B : Gp K →* (X ≃ₗ[K] X))
    (hline : Module.finrank K (fix7 B) = 1) {v₀ : X} (hv₀ : v₀ ∈ fix7 B) (hne : v₀ ≠ 0)
    (hd : ∀ c : Kˣ, B (e7Data_valid.hm K nodeA c) v₀ = (c : K) • v₀)
    {g g' : Gp K} {c : K} (hc : c ≠ 0)
    (h : endoE g (w0 : V K) = c • endoE g' (w0 : V K)) : B g v₀ = c • B g' v₀ := by
  set p : Gp K := g'⁻¹ * g with hp
  have hpw : endoE p (w0 : V K) = c • (w0 : V K) := by
    rw [hp, endoE_mul, Module.End.mul_apply, h, map_smul, endoE_inv_endoE]
  let ι : ↥(StabW0 K) →* Gp K := ((eAutEquiv K).symm.toMonoidHom).comp (StabW0 K).subtype
  have hι : ∀ q, ι q ∈ NormUA K := by
    intro q
    obtain ⟨c', hc', hq⟩ := q.2
    refine mem_normalizer_UA_of_line hc' ?_
    have : ((q : ↥(EAut K)) : V K ≃ₗ[K] V K) = (eAutEquiv K (ι q) : V K ≃ₗ[K] V K) := by
      simp [ι]
    rw [this] at hq
    exact hq
  let χ := charOf B hline hv₀ hne ι hι
  have hdmem : ∀ c : Kˣ, ι (d7 K c) = e7Data_valid.hm K nodeA c := by
    intro c
    show (eAutEquiv K).symm (d7Hom K c) = _
    have : d7Hom K c = eAutEquiv K (e7Data_valid.hm K node7' c) := rfl
    rw [this, MulEquiv.symm_apply_apply]
  have hχd : ∀ c : Kˣ, χ (d7 K c) = c := by
    intro c
    apply Units.ext
    have h1 := charOf_spec B hline hv₀ hne ι hι (d7 K c)
    rw [hdmem c, hd c] at h1
    exact (smul_left_injective K hne h1).symm
  let q : ↥(StabW0 K) := ⟨eAutEquiv K p, c, hc, by rw [eAutEquiv_apply]; exact hpw⟩
  have hιq : ι q = p := by
    show (eAutEquiv K).symm (eAutEquiv K p) = p
    exact MulEquiv.symm_apply_apply _ _
  have hC := hChar χ hχd q
  have hχq : ((χ q : Kˣ) : K) = c := by
    have h1 : ((q : ↥(EAut K)) : V K ≃ₗ[K] V K) (w0 : V K) = c • (w0 : V K) := by
      show ((eAutEquiv K p : ↥(EAut K)) : V K ≃ₗ[K] V K) (w0 : V K) = _
      rw [eAutEquiv_apply]
      exact hpw
    rw [h1] at hC
    exact (smul_left_injective K (w0_ne_zero (K := K)) hC).symm
  have hBp : B p v₀ = c • v₀ := by
    have := charOf_spec B hline hv₀ hne ι hι q
    rw [hιq, hχq] at this
    exact this
  calc B g v₀ = B (g' * p) v₀ := by rw [hp, mul_inv_cancel_left]
    _ = B g' (B p v₀) := by rw [map_mul, LinearEquiv.mul_apply]
    _ = c • B g' v₀ := by rw [hBp, map_smul]

end Char

end CFSG.RankThree.GF2n.Smith81.S81Z
