module

public import CFSG.Quasithin.Vol2.Ch10Reselect.NatMod
public import CFSG.Quasithin.Vol2.Ch10SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix CFSG.Quasithin.Vol2.Ch10.SecA

structure UModel {G : Type} [Group G] (A U Z L : Subgroup G) (K : Type) [Field K] where
  ψ : ↥U →* Multiplicative (UTilde K)
  surj : Function.Surjective ψ
  ker : ∀ u : ↥U, ψ u = 1 ↔ (u : G) ∈ Z
  γ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K
  γ_surj : Function.Surjective γ
  γ_ker : ∀ l : ↥L, γ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (A : Set G)
  equiv : ∀ (l : ↥L) (u : ↥U) (hu : (l : G) * (u : G) * (l : G)⁻¹ ∈ U),
    ψ ⟨(l : G) * (u : G) * (l : G)⁻¹, hu⟩ =
      Multiplicative.ofAdd (rhoSL K (γ l) (Multiplicative.toAdd (ψ u)))

namespace UModel

variable {G : Type} [Group G] {A U Z L : Subgroup G} {K : Type} [Field K]

@[expose] def acting (U Z : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (Z : Set G)

private lemma conj_mem_U (g : ↥(acting U Z)) (u : ↥U) : (g : G) * (u : G) * (g : G)⁻¹ ∈ U := by
  have h := Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp g.2).1 (u : G)
  exact h.mp u.2

private def conjUHom (g : ↥(acting U Z)) : ↥U →* ↥U where
  toFun u := ⟨(g : G) * (u : G) * (g : G)⁻¹, conj_mem_U g u⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private lemma conjUHom_val (g : ↥(acting U Z)) (u : ↥U) :
    ((conjUHom g u : ↥U) : G) = (g : G) * (u : G) * (g : G)⁻¹ := rfl

private lemma conjUHom_one (u : ↥U) : conjUHom (1 : ↥(acting U Z)) u = u := by
  apply Subtype.ext
  simp only [conjUHom_val, Subgroup.coe_one, inv_one, mul_one, one_mul]

private lemma conjUHom_mul (g h : ↥(acting U Z)) (u : ↥U) :
    conjUHom (g * h) u = conjUHom g (conjUHom h u) := by
  apply Subtype.ext
  simp only [conjUHom_val, Subgroup.coe_mul]
  group

private lemma conjUHom_inv_mul (g : ↥(acting U Z)) (u : ↥U) :
    conjUHom g⁻¹ (conjUHom g u) = u := by
  apply Subtype.ext
  simp only [conjUHom_val, Subgroup.coe_inv, inv_inv]
  group

private lemma conjUHom_mul_inv (g : ↥(acting U Z)) (u : ↥U) :
    conjUHom g (conjUHom g⁻¹ u) = u := by
  apply Subtype.ext
  simp only [conjUHom_val, Subgroup.coe_inv, inv_inv]
  group

private lemma conjUHom_ker (M : UModel A U Z L K) (g : ↥(acting U Z)) (w : ↥U) :
    M.ψ (conjUHom g w) = 1 ↔ M.ψ w = 1 := by
  have hZ : (w : G) ∈ Z ↔ (g : G) * (w : G) * (g : G)⁻¹ ∈ Z :=
    Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp g.2).2 (w : G)
  exact (M.ker _).trans (hZ.symm.trans (M.ker w).symm)

private lemma conjUHom_ψ_congr (M : UModel A U Z L K) (g : ↥(acting U Z)) {u u' : ↥U}
    (h : M.ψ u = M.ψ u') : M.ψ (conjUHom g u) = M.ψ (conjUHom g u') := by
  have h1 : M.ψ (u⁻¹ * u') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : M.ψ (conjUHom g (u⁻¹ * u')) = 1 := (conjUHom_ker M g _).mpr h1
  simp only [map_mul, map_inv] at h2
  exact inv_mul_eq_one.mp h2

private noncomputable def preim (M : UModel A U Z L K) (p : UTilde K) : ↥U :=
  Classical.choose (M.surj (Multiplicative.ofAdd p))

private lemma preim_spec (M : UModel A U Z L K) (p : UTilde K) :
    M.ψ (preim M p) = Multiplicative.ofAdd p :=
  Classical.choose_spec (M.surj (Multiplicative.ofAdd p))

private lemma toAdd_preim (M : UModel A U Z L K) (p : UTilde K) :
    Multiplicative.toAdd (M.ψ (preim M p)) = p :=
  congrArg Multiplicative.toAdd (preim_spec M p)

private noncomputable def actFun (M : UModel A U Z L K) (g : ↥(acting U Z)) (p : UTilde K) :
    UTilde K :=
  Multiplicative.toAdd (M.ψ (conjUHom g (preim M p)))

private lemma actFun_ψ (M : UModel A U Z L K) (g : ↥(acting U Z)) (u : ↥U) :
    actFun M g (Multiplicative.toAdd (M.ψ u)) = Multiplicative.toAdd (M.ψ (conjUHom g u)) := by
  have hpre : M.ψ (preim M (Multiplicative.toAdd (M.ψ u))) = M.ψ u :=
    (preim_spec M _).trans rfl
  unfold actFun
  exact congrArg Multiplicative.toAdd (conjUHom_ψ_congr M g hpre)

private lemma actFun_add (M : UModel A U Z L K) (g : ↥(acting U Z)) (p q : UTilde K) :
    actFun M g (p + q) = actFun M g p + actFun M g q := by
  have hpq : p + q = Multiplicative.toAdd (M.ψ (preim M p * preim M q)) := by
    rw [map_mul, preim_spec, preim_spec]
    rfl
  calc actFun M g (p + q)
      = actFun M g (Multiplicative.toAdd (M.ψ (preim M p * preim M q))) := by rw [← hpq]
    _ = Multiplicative.toAdd (M.ψ (conjUHom g (preim M p * preim M q))) := actFun_ψ M g _
    _ = Multiplicative.toAdd (M.ψ (conjUHom g (preim M p) * conjUHom g (preim M q))) := by
        rw [map_mul]
    _ = Multiplicative.toAdd (M.ψ (conjUHom g (preim M p))) +
          Multiplicative.toAdd (M.ψ (conjUHom g (preim M q))) := by
        rw [map_mul]
        rfl
    _ = actFun M g p + actFun M g q := rfl

private lemma actFun_one (M : UModel A U Z L K) (p : UTilde K) : actFun M 1 p = p := by
  unfold actFun
  rw [conjUHom_one, toAdd_preim]

private lemma actFun_mul (M : UModel A U Z L K) (g h : ↥(acting U Z)) (p : UTilde K) :
    actFun M (g * h) p = actFun M g (actFun M h p) := by
  have hp : actFun M h p = Multiplicative.toAdd (M.ψ (conjUHom h (preim M p))) := rfl
  rw [hp, actFun_ψ]
  unfold actFun
  rw [conjUHom_mul]

private lemma actFun_left_inv (M : UModel A U Z L K) (g : ↥(acting U Z)) (p : UTilde K) :
    actFun M g⁻¹ (actFun M g p) = p := by
  have hp : actFun M g p = Multiplicative.toAdd (M.ψ (conjUHom g (preim M p))) := rfl
  rw [hp, actFun_ψ, conjUHom_inv_mul, toAdd_preim]

private lemma actFun_right_inv (M : UModel A U Z L K) (g : ↥(acting U Z)) (p : UTilde K) :
    actFun M g (actFun M g⁻¹ p) = p := by
  have hp : actFun M g⁻¹ p = Multiplicative.toAdd (M.ψ (conjUHom g⁻¹ (preim M p))) := rfl
  rw [hp, actFun_ψ, conjUHom_mul_inv, toAdd_preim]

private noncomputable def actPerm (M : UModel A U Z L K) (g : ↥(acting U Z)) :
    Equiv.Perm (UTilde K) where
  toFun := actFun M g
  invFun := actFun M g⁻¹
  left_inv := actFun_left_inv M g
  right_inv := actFun_right_inv M g

noncomputable def actHom (M : UModel A U Z L K) : ↥(acting U Z) →* Equiv.Perm (UTilde K) where
  toFun g := actPerm M g
  map_one' := Equiv.ext fun p => actFun_one M p
  map_mul' g h := Equiv.ext fun p => actFun_mul M g h p

theorem actHom_ψ (M : UModel A U Z L K) (g : ↥(acting U Z)) (u : ↥U)
    (hu : (g : G) * (u : G) * (g : G)⁻¹ ∈ U) :
    Multiplicative.toAdd (M.ψ ⟨(g : G) * (u : G) * (g : G)⁻¹, hu⟩) =
      M.actHom g (Multiplicative.toAdd (M.ψ u)) :=
  (actFun_ψ M g u).symm

theorem actHom_add (M : UModel A U Z L K) (g : ↥(acting U Z)) (p q : UTilde K) :
    M.actHom g (p + q) = M.actHom g p + M.actHom g q :=
  actFun_add M g p q

theorem actHom_of_mem_L (M : UModel A U Z L K) (g : ↥(acting U Z)) (hg : (g : G) ∈ L) :
    M.actHom g = rhoSL K (M.γ ⟨g, hg⟩) := by
  refine Equiv.ext fun p => ?_
  have h : Multiplicative.toAdd (M.ψ ⟨(g : G) * (preim M p : G) * (g : G)⁻¹,
      conj_mem_U g (preim M p)⟩) =
      rhoSL K (M.γ ⟨(g : G), hg⟩) (Multiplicative.toAdd (M.ψ (preim M p))) :=
    congrArg Multiplicative.toAdd
      (M.equiv ⟨(g : G), hg⟩ (preim M p) (conj_mem_U g (preim M p)))
  rw [toAdd_preim] at h
  exact h

theorem actHom_eq_one_iff (M : UModel A U Z L K) (g : ↥(acting U Z)) :
    M.actHom g = 1 ↔ ∀ u ∈ U, (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h u hu
    have h1 : actFun M g (Multiplicative.toAdd (M.ψ ⟨u, hu⟩)) =
        Multiplicative.toAdd (M.ψ ⟨u, hu⟩) :=
      congrArg (fun φ : Equiv.Perm (UTilde K) => φ (Multiplicative.toAdd (M.ψ ⟨u, hu⟩))) h
    rw [actFun_ψ] at h1
    have h2 : M.ψ (conjUHom g ⟨u, hu⟩) = M.ψ ⟨u, hu⟩ := Multiplicative.toAdd.injective h1
    have h3 : M.ψ (conjUHom g ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (M.ker _).mp h3
    have h5 : ((conjUHom g ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ : ↥U) : G) =
        (g : G) * u * (g : G)⁻¹ * u⁻¹ := by
      simp [conjUHom_val]
    rw [h5] at h4
    exact h4
  · intro h
    refine Equiv.ext fun p => ?_
    have hw : (g : G) * ((preim M p : ↥U) : G) * (g : G)⁻¹ * ((preim M p : ↥U) : G)⁻¹ ∈ Z :=
      h (preim M p) (preim M p).2
    have hψ : M.ψ (conjUHom g (preim M p) * (preim M p)⁻¹) = 1 :=
      (M.ker _).mpr (by simpa [conjUHom_val] using hw)
    have h2 : M.ψ (conjUHom g (preim M p)) = M.ψ (preim M p) := by
      rw [map_mul, map_inv] at hψ
      exact mul_inv_eq_one.mp hψ
    show Multiplicative.toAdd (M.ψ (conjUHom g (preim M p))) = p
    rw [h2, toAdd_preim]

theorem mem_of_commutators_mem [Nontrivial K] (M : UModel A U Z L K) (hZU : Z ≤ U)
    {u : G} (hu : u ∈ U) (h : ∀ l ∈ L, l * u * l⁻¹ * u⁻¹ ∈ Z) : u ∈ Z := by
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      rhoSL K g (Multiplicative.toAdd (M.ψ ⟨u, hu⟩)) = Multiplicative.toAdd (M.ψ ⟨u, hu⟩) := by
    intro g
    obtain ⟨l, hl⟩ := M.γ_surj g
    have hcomm : (l : G) * u * (l : G)⁻¹ ∈ U := by
      have h1 : (l : G) * u * (l : G)⁻¹ * u⁻¹ ∈ U := hZU (h (l : G) l.2)
      have h2 := U.mul_mem h1 hu
      simpa [mul_assoc] using h2
    have hc : M.ψ (⟨(l : G) * u * (l : G)⁻¹, hcomm⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 :=
      (M.ker _).mpr (by simpa [mul_assoc] using h (l : G) l.2)
    have hψ : M.ψ ⟨(l : G) * u * (l : G)⁻¹, hcomm⟩ = M.ψ ⟨u, hu⟩ := by
      rw [map_mul, map_inv] at hc
      exact mul_inv_eq_one.mp hc
    have heq2 : M.ψ ⟨u, hu⟩ = Multiplicative.ofAdd (rhoSL K (M.γ l) (Multiplicative.toAdd (M.ψ ⟨u, hu⟩))) :=
      hψ.symm.trans (M.equiv l ⟨u, hu⟩ hcomm)
    rw [hl] at heq2
    exact (congrArg Multiplicative.toAdd heq2).symm
  have hp0 : Multiplicative.toAdd (M.ψ ⟨u, hu⟩) = 0 := rhoSL_fixed_eq_zero hfix
  have hψ1 : M.ψ ⟨u, hu⟩ = 1 := Multiplicative.toAdd.injective (hp0.trans rfl)
  exact (M.ker ⟨u, hu⟩).mp hψ1

end UModel

end CFSG.Quasithin.Vol2.Ch10Reselect
