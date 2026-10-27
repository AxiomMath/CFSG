module

public import CFSG.Quasithin.Vol2.Ch10SecC3K
public import CFSG.Quasithin.Background.HL3WrNorm
public import CFSG.Quasithin.Vol2.Ch10SecC3J

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut exists_conj_mul_slFieldAut)
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def rhoEquiv : SL K × SL K ≃* ↥(img K) :=
  MonoidHom.ofInjective rho_injective

@[expose] noncomputable def conjAut (x : ↥(norm K)) : MulAut (SL K × SL K) :=
  (MulAut.congr rhoEquiv.symm) ((img K).normalizerMonoidHom x)

theorem rho_conjAut (x : ↥(norm K)) (g : SL K × SL K) :
    rho K (conjAut x g) = (x : MulAut (WM K)) * rho K g * (x : MulAut (WM K))⁻¹ := by
  have h : rho K (conjAut x g) = ((rhoEquiv (conjAut x g) : ↥(img K)) : MulAut (WM K)) := rfl
  rw [h]
  change ((rhoEquiv (rhoEquiv.symm ((img K).normalizerMonoidHom x (rhoEquiv g))) : ↥(img K)) :
    MulAut (WM K)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem exists_of_preserves [Finite K] (hK : 4 ≤ Nat.card K) {x : ↥(norm K)}
    (hx : ((⊤ : Subgroup (SL K)).prod ⊥).map (conjAut x).toMonoidHom =
      (⊤ : Subgroup (SL K)).prod ⊥) :
    ∃ (g : SL K × SL K) (y : Kˣ) (σ : K ≃+* K),
      (x : MulAut (WM K)) = rho K g * (sc y * fa σ) := by
  set α := conjAut x with hα
  have hs := isSimpleGroup_SL hK
  have hp := commutator_SL hK
  have hx2 : ((⊥ : Subgroup (SL K)).prod ⊤).map α.toMonoidHom = (⊥ : Subgroup (SL K)).prod ⊤ := by
    rcases H.L3Wr.map_prod_eq_or' hs hp α with h | h
    · exfalso
      rw [← hx] at h
      have h' := Subgroup.map_injective α.injective h
      have hmem : ((1 : SL K), (u : SL K)) ∈ (⊥ : Subgroup (SL K)).prod ⊤ :=
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
      rw [h'] at hmem
      have h1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).2
      have h2 := congrArg (fun M : SL K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h1
      simp [u] at h2
    · exact h
  have h1 : ∀ a : SL K, (α (a, 1)).2 = 1 := fun a => by
    have hm : α (a, 1) ∈ ((⊤ : Subgroup (SL K)).prod ⊥).map α.toMonoidHom :=
      ⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩, rfl⟩
    rw [hx] at hm
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hm).2
  have h2 : ∀ b : SL K, (α (1, b)).1 = 1 := fun b => by
    have hm : α (1, b) ∈ ((⊥ : Subgroup (SL K)).prod ⊤).map α.toMonoidHom :=
      ⟨(1, b), Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩, rfl⟩
    rw [hx2] at hm
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hm).1
  let f₁ : SL K →* SL K := (MonoidHom.fst _ _).comp (α.toMonoidHom.comp (MonoidHom.inl _ _))
  let f₂ : SL K →* SL K := (MonoidHom.snd _ _).comp (α.toMonoidHom.comp (MonoidHom.inr _ _))
  have hα12 : ∀ a b, α (a, b) = (f₁ a, f₂ b) := by
    intro a b
    have hab : ((a, b) : SL K × SL K) = (a, 1) * (1, b) := by simp
    rw [hab, map_mul]
    refine Prod.ext ?_ ?_
    · change (α (a, 1)).1 * (α (1, b)).1 = (α (a, 1)).1
      rw [h2, mul_one]
    · change (α (a, 1)).2 * (α (1, b)).2 = (α (1, b)).2
      rw [h1, one_mul]
  have hb₁ : Function.Bijective f₁ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro a ha
      have h3 : α (a, 1) = α 1 := by
        rw [map_one]
        exact Prod.ext ha (h1 a)
      exact congrArg Prod.fst (α.injective h3)
    · intro c
      have hc : (c, (1 : SL K)) ∈ ((⊤ : Subgroup (SL K)).prod ⊥).map α.toMonoidHom := by
        rw [hx]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
      obtain ⟨⟨a, b⟩, hab, he⟩ := hc
      have hb : b = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hab).2
      subst hb
      exact ⟨a, congrArg Prod.fst he⟩
  have hb₂ : Function.Bijective f₂ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro b hb
      have h3 : α (1, b) = α 1 := by
        rw [map_one]
        exact Prod.ext (h2 b) hb
      exact congrArg Prod.snd (α.injective h3)
    · intro c
      have hc : ((1 : SL K), c) ∈ ((⊥ : Subgroup (SL K)).prod ⊤).map α.toMonoidHom := by
        rw [hx2]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
      obtain ⟨⟨a, b⟩, hab, he⟩ := hc
      have ha : a = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hab).1
      subst ha
      exact ⟨b, congrArg Prod.snd he⟩
  obtain ⟨M₁, σ₁, hM₁⟩ := exists_conj_mul_slFieldAut (MulEquiv.ofBijective f₁ hb₁)
  obtain ⟨M₂, σ₂, hM₂⟩ := exists_conj_mul_slFieldAut (MulEquiv.ofBijective f₂ hb₂)
  have hf₁ : ∀ a, f₁ a = M₁ * slFieldAut K σ₁ a * M₁⁻¹ := fun a => by
    have := congrArg (fun φ : MulAut (SL K) => φ a) hM₁
    simpa [MulAut.mul_apply, MulAut.conj_apply] using this
  have hf₂ : ∀ b, f₂ b = M₂ * slFieldAut K σ₂ b * M₂⁻¹ := fun b => by
    have := congrArg (fun φ : MulAut (SL K) => φ b) hM₂
    simpa [MulAut.mul_apply, MulAut.conj_apply] using this
  set ψ : MulAut (WM K) := (rho K (M₁, M₂))⁻¹ * (x : MulAut (WM K)) with hψ
  have hψc : ∀ g : SL K × SL K,
      ψ * rho K g = rho K (slFieldAut K σ₁ g.1, slFieldAut K σ₂ g.2) * ψ := by
    intro g
    have h3 := rho_conjAut x g
    rw [← hα, hα12, hf₁, hf₂] at h3
    have h4 : rho K (M₁ * slFieldAut K σ₁ g.1 * M₁⁻¹, M₂ * slFieldAut K σ₂ g.2 * M₂⁻¹) =
        rho K (M₁, M₂) * rho K (slFieldAut K σ₁ g.1, slFieldAut K σ₂ g.2) *
          (rho K (M₁, M₂))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h4] at h3
    calc ψ * rho K g = (rho K (M₁, M₂))⁻¹ * ((x : MulAut (WM K)) * rho K g *
          (x : MulAut (WM K))⁻¹) * (x : MulAut (WM K)) := by rw [hψ]; group
      _ = rho K (slFieldAut K σ₁ g.1, slFieldAut K σ₂ g.2) * ψ := by rw [← h3, hψ]; group
  obtain ⟨-, y, hy⟩ := eq_sc_mul_fa hψc
  refine ⟨(M₁, M₂), y, σ₁, ?_⟩
  rw [← hy, hψ, mul_inv_cancel_left]

omit [CharP K 2] in
theorem tau_mul_sc_mul_fa (y : Kˣ) (σ : K ≃+* K) :
    tau K * (sc y * fa σ) = sc y * fa σ * tau K := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change ((y : K) • (Multiplicative.toAdd X).map σ)ᵀ = (y : K) • ((Multiplicative.toAdd X)ᵀ).map σ
  rw [Matrix.transpose_smul, Matrix.transpose_map]

theorem mem_norm_form [Finite K] (hK : 4 ≤ Nat.card K) {x : MulAut (WM K)} (hx : x ∈ norm K) :
    ∃ (g : SL K × SL K) (y : Kˣ) (σ : K ≃+* K),
      x = rho K g * (sc y * fa σ) ∨ x = rho K g * (sc y * fa σ) * tau K := by
  rcases H.L3Wr.map_prod_eq_or (isSimpleGroup_SL hK) (commutator_SL hK) (conjAut ⟨x, hx⟩) with
    h | h
  · obtain ⟨g, y, σ, hg⟩ := exists_of_preserves hK h
    exact ⟨g, y, σ, Or.inl hg⟩
  have hy : tau K * x ∈ norm K := (norm K).mul_mem tau_mem_norm hx
  have hconj : ∀ g, conjAut ⟨tau K * x, hy⟩ g = (conjAut ⟨x, hx⟩ g).swap := by
    intro g
    apply rho_injective
    rw [rho_conjAut, ← tau_conj_rho, rho_conjAut]
    change tau K * x * rho K g * (tau K * x)⁻¹ = tau K * (x * rho K g * x⁻¹) * (tau K)⁻¹
    group
  have hpres : ((⊤ : Subgroup (SL K)).prod ⊥).map (conjAut ⟨tau K * x, hy⟩).toMonoidHom =
      (⊤ : Subgroup (SL K)).prod ⊥ := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      change conjAut ⟨tau K * x, hy⟩ v ∈ (⊤ : Subgroup (SL K)).prod ⊥
      rw [hconj]
      have hm : conjAut ⟨x, hx⟩ v ∈ (⊥ : Subgroup (SL K)).prod ⊤ := by
        rw [← h]
        exact ⟨v, hv, rfl⟩
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (Subgroup.mem_prod.mp hm).1⟩
    · intro hz
      have hm : z.swap ∈ ((⊤ : Subgroup (SL K)).prod ⊥).map (conjAut ⟨x, hx⟩).toMonoidHom := by
        rw [h]
        exact Subgroup.mem_prod.mpr ⟨(Subgroup.mem_prod.mp hz).2, Subgroup.mem_top _⟩
      obtain ⟨v, hv, hve⟩ := hm
      refine ⟨v, hv, ?_⟩
      change conjAut ⟨tau K * x, hy⟩ v = z
      rw [hconj]
      change conjAut ⟨x, hx⟩ v = z.swap at hve
      rw [hve, Prod.swap_swap]
  obtain ⟨g, y, σ, hg⟩ := exists_of_preserves hK hpres
  refine ⟨g.swap, y, σ, Or.inr ?_⟩
  change tau K * x = rho K g * (sc y * fa σ) at hg
  calc x = tau K * (tau K * x) := by rw [← mul_assoc, tau_mul_self, one_mul]
    _ = tau K * (rho K g * (sc y * fa σ)) := by rw [hg]
    _ = rho K g.swap * (sc y * fa σ) * tau K := by
      rw [← mul_assoc, tau_mul_rho, mul_assoc, tau_mul_sc_mul_fa, ← mul_assoc]

end CFSG.Quasithin.Vol2.Ch10.C3.Om
