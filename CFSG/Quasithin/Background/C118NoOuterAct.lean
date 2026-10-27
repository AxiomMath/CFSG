module

public import CFSG.Quasithin.Background.C118BridgeOne
public import CFSG.Quasithin.Background.C118NoOuterAlg

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

section Fstar

variable {Ω : Type} [Group Ω]

theorem conjAct_apply_coe (V : Subgroup Ω) (g : ↥(Subgroup.normalizer (V : Set Ω))) (v : ↥V) :
    ((conjAct V g v : ↥V) : Ω) = (g : Ω) * v * (g : Ω)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

theorem conjAct_eq_one_iff (V : Subgroup Ω) (g : ↥(Subgroup.normalizer (V : Set Ω))) :
    conjAct V g = 1 ↔ (g : Ω) ∈ Subgroup.centralizer (V : Set Ω) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := conjAct_apply_coe V g ⟨v, hv⟩
    rw [h] at this
    have h2 : v = (g : Ω) * v * (g : Ω)⁻¹ := this
    calc v * (g : Ω) = ((g : Ω) * v * (g : Ω)⁻¹) * (g : Ω) := by rw [← h2]
      _ = (g : Ω) * v := by group
  · intro h
    ext v
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp h (v : Ω) v.2
    show (g : Ω) * v * (g : Ω)⁻¹ = v
    calc (g : Ω) * v * (g : Ω)⁻¹ = ((g : Ω) * v) * (g : Ω)⁻¹ := rfl
      _ = ((v : Ω) * (g : Ω)) * (g : Ω)⁻¹ := by rw [← this]
      _ = v := by group

theorem inf_centralizer_le_fstarPre (H V : Subgroup Ω)
    (hV : H ≤ Subgroup.normalizer (V : Set Ω)) :
    H ⊓ Subgroup.centralizer (V : Set Ω) ≤ fstarPre H V := by
  rintro g ⟨hgH, hgC⟩
  refine ⟨hgH, ⟨g, hV hgH⟩, ?_, rfl⟩
  show conjAct V ⟨g, hV hgH⟩ ∈ fstarAut H V
  have : conjAct V ⟨g, hV hgH⟩ = 1 := (conjAct_eq_one_iff V ⟨g, hV hgH⟩).mpr hgC
  rw [this]
  exact one_mem _

theorem mem_fstarPre_of_commutes [Finite Ω] (H V : Subgroup Ω)
    (hV : H ≤ Subgroup.normalizer (V : Set Ω)) {g : Ω} (hgH : g ∈ H)
    (hg : ∀ k ∈ fstarPre H V, g * k * g⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set Ω)) :
    g ∈ fstarPre H V := by
  have hgN : g ∈ Subgroup.normalizer (V : Set Ω) := hV hgH
  let gbar : ↥(autOn H V) :=
    ⟨conjAct V ⟨g, hgN⟩, ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hgH, rfl⟩⟩
  have hcent : gbar ∈
      Subgroup.centralizer (generalizedFitting ↥(autOn H V) : Set ↥(autOn H V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro φ hφ
    obtain ⟨n, hnH, hnφ⟩ := φ.2
    have hnK : (n : Ω) ∈ fstarPre H V := by
      refine ⟨Subgroup.mem_subgroupOf.mp hnH, n, ?_, rfl⟩
      show conjAct V n ∈ fstarAut H V
      rw [hnφ]
      exact ⟨φ, hφ, rfl⟩
    have hc := hg (n : Ω) hnK
    have hcN : g * (n : Ω) * g⁻¹ * (n : Ω)⁻¹ ∈ Subgroup.normalizer (V : Set Ω) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN n.2) (Subgroup.inv_mem _ hgN))
        (Subgroup.inv_mem _ n.2)
    have h1 : conjAct V ⟨g * (n : Ω) * g⁻¹ * (n : Ω)⁻¹, hcN⟩ = 1 :=
      (conjAct_eq_one_iff V _).mpr hc
    have h2 : conjAct V ⟨g, hgN⟩ * conjAct V n = conjAct V n * conjAct V ⟨g, hgN⟩ := by
      have h3 : (⟨g * (n : Ω) * g⁻¹ * (n : Ω)⁻¹, hcN⟩ : ↥(Subgroup.normalizer (V : Set Ω))) =
          ⟨g, hgN⟩ * n * ⟨g, hgN⟩⁻¹ * n⁻¹ := rfl
      rw [h3] at h1
      simp only [map_mul, map_inv] at h1
      set a := conjAct V ⟨g, hgN⟩
      set b := conjAct V n
      have h5 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h1
      calc a * b = (a * b * a⁻¹) * a := by group
        _ = b * a := by rw [h5]
    apply Subtype.ext
    show φ.1 * (conjAct V ⟨g, hgN⟩) = (conjAct V ⟨g, hgN⟩) * φ.1
    rw [← hnφ]
    exact h2.symm
  have hmem := CFSG.centralizer_generalizedFitting_le ↥(autOn H V) hcent
  refine ⟨hgH, ⟨g, hgN⟩, ?_, rfl⟩
  show conjAct V ⟨g, hgN⟩ ∈ fstarAut H V
  exact ⟨gbar, hmem, rfl⟩

end Fstar

section ActionData

variable {Ω : Type} [Group Ω] {B H : Subgroup Ω} {n : ℕ}

@[expose] noncomputable def actW1 (B H : Subgroup Ω) : ↥H →* MulAut ↥(clW1 B H) :=
  (clW1 B H).normalizerMonoidHom.comp (Subgroup.inclusion (H_le_normalizer_clW1 B H))

theorem actW1_coe (g : ↥H) (u : ↥(clW1 B H)) :
    ((actW1 B H g u : ↥(clW1 B H)) : Ω) = (g : Ω) * u * (g : Ω)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem C118NatData.beta_act_congr (d : C118NatData B H n) (g : ↥H) (u v : ↥(clW1 B H))
    (huv : d.β u = d.β v) : d.β (actW1 B H g u) = d.β (actW1 B H g v) := by
  have h1 : u⁻¹ * v ∈ d.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  rw [d.hβ_ker, Subgroup.mem_subgroupOf] at h1
  have h2 : (actW1 B H g u)⁻¹ * (actW1 B H g v) ∈ d.β.ker := by
    rw [d.hβ_ker, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clW0 B H g.2)
      ((u⁻¹ * v : ↥(clW1 B H)) : Ω)
    have h3 := this.mp h1
    have e : (actW1 B H g u)⁻¹ * (actW1 B H g v) = actW1 B H g (u⁻¹ * v) := by
      simp [map_mul, map_inv]
    rw [e, actW1_coe g (u⁻¹ * v)]
    exact h3
  rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
  exact inv_mul_eq_one.mp h2

@[expose] def IsActOn (d : C118NatData B H n) (ρ : ↥H →* Equiv.Perm (Fin 2 → d.F)) : Prop :=
  ∀ g u, ρ g (Multiplicative.toAdd (d.β u)) = Multiplicative.toAdd (d.β (actW1 B H g u))

theorem C118NatData.exists_permAction (d : C118NatData B H n) :
    ∃ ρ : ↥H →* Equiv.Perm (Fin 2 → d.F), (∀ g x y, ρ g (x + y) = ρ g x + ρ g y) ∧
      IsActOn d ρ :=
  exists_perm_action (actW1 B H) d.β d.hβ_surj (fun g u v h => d.beta_act_congr g u v h)

variable {d : C118NatData B H n} {ρ : ↥H →* Equiv.Perm (Fin 2 → d.F)}

theorem IsActOn.eq_mulVec (h : IsActOn d ρ) (g : ↥H) (M : Matrix (Fin 2) (Fin 2) d.F)
    (hM : ∀ u : ↥(clW1 B H), Multiplicative.toAdd (d.β (actW1 B H g u)) =
      M.mulVec (Multiplicative.toAdd (d.β u))) (x : Fin 2 → d.F) : ρ g x = M.mulVec x := by
  obtain ⟨u, hu⟩ := d.hβ_surj (Multiplicative.ofAdd x)
  have hux : Multiplicative.toAdd (d.β u) = x := by rw [hu]; rfl
  rw [← hux, h g u, hM u]

theorem IsActOn.incl (h : IsActOn d ρ) (k : ↥(clK B H)) (x : Fin 2 → d.F) :
    ρ (Subgroup.inclusion (clK_le B H) k) x =
      ((d.α k : Matrix.SpecialLinearGroup (Fin 2) d.F) :
        Matrix (Fin 2) (Fin 2) d.F).mulVec x :=
  h.eq_mulVec _ _ (fun u => d.hβ_equiv k u _
    (actW1_coe (Subgroup.inclusion (clK_le B H) k) u)) x

theorem IsActOn.normalizes (h : IsActOn d ρ) (hαs : Function.Surjective d.α) (g : ↥H)
    (A : Matrix.SpecialLinearGroup (Fin 2) d.F) :
    ∃ A' : Matrix.SpecialLinearGroup (Fin 2) d.F, ∀ v,
      ρ g ((A : Matrix (Fin 2) (Fin 2) d.F).mulVec v) =
        (A' : Matrix (Fin 2) (Fin 2) d.F).mulVec (ρ g v) := by
  obtain ⟨k, rfl⟩ := hαs A
  have hk' : (g : Ω) * k * (g : Ω)⁻¹ ∈ clK B H :=
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clK B H g.2) k).mp k.2
  refine ⟨d.α ⟨_, hk'⟩, fun v => ?_⟩
  rw [← h.incl k v, ← h.incl ⟨_, hk'⟩ (ρ g v), ← Equiv.Perm.mul_apply, ← map_mul,
    ← Equiv.Perm.mul_apply, ← map_mul]
  congr 2
  apply Subtype.ext
  show (g : Ω) * k = (g : Ω) * k * (g : Ω)⁻¹ * g
  group

theorem IsActOn.exists_semilinear [Finite d.F] (h : IsActOn d ρ)
    (hadd : ∀ g x y, ρ g (x + y) = ρ g x + ρ g y) (hαs : Function.Surjective d.α) (g : ↥H) :
    ∃ σ : d.F ≃+* d.F, IsSemilinearWith (ρ g) σ :=
  exists_semilinear_of_normalizes (ρ g) (hadd g) (h.normalizes hαs g) (fun A => by
    rw [← map_inv]
    exact h.normalizes hαs g⁻¹ A)

theorem IsActOn.mem_centralizer_of_eq_one [Finite Ω] (h : IsActOn d ρ) (g : ↥H) (hg : ρ g = 1) :
    (g : Ω) ∈ Subgroup.centralizer (clV B H : Set Ω) := by
  have step1 : ∀ k ∈ fstarPre H (VZ B H),
      (g : Ω) * k * (g : Ω)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (clV B H : Set Ω) := by
    intro k hk
    have hk' : k ∈ clK B H := hk
    have hc : (g : Ω) * k * (g : Ω)⁻¹ * k⁻¹ ∈ clK B H :=
      (clK B H).mul_mem ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clK B H g.2) k).mp hk')
        ((clK B H).inv_mem hk')
    have hαc : d.α ⟨_, hc⟩ = 1 := by
      apply eq_one_of_forall_smul_vec
      intro w
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ← h.incl ⟨_, hc⟩ w]
      have : Subgroup.inclusion (clK_le B H) (⟨_, hc⟩ : ↥(clK B H)) =
          g * Subgroup.inclusion (clK_le B H) ⟨k, hk'⟩ * g⁻¹ *
            (Subgroup.inclusion (clK_le B H) ⟨k, hk'⟩)⁻¹ := Subtype.ext rfl
      rw [this]
      simp [hg]
    have hker : (⟨_, hc⟩ : ↥(clK B H)) ∈ d.α.ker := hαc
    rw [d.hα_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  have hgK : (g : Ω) ∈ fstarPre H (VZ B H) :=
    mem_fstarPre_of_commutes H _ (H_le_normalizer_clV B H) g.2 step1
  have hαg : d.α ⟨(g : Ω), hgK⟩ = 1 := by
    apply eq_one_of_forall_smul_vec
    intro w
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ← h.incl ⟨(g : Ω), hgK⟩ w]
    have : Subgroup.inclusion (clK_le B H) (⟨(g : Ω), hgK⟩ : ↥(clK B H)) = g := Subtype.ext rfl
    rw [this, hg]
    rfl
  have hker : (⟨(g : Ω), hgK⟩ : ↥(clK B H)) ∈ d.α.ker := hαg
  rw [d.hα_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

end ActionData

end CFSG.Quasithin
