module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgId
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

private theorem subgroupOf_bot_top_eq_bot (A : Type) [CommGroup A] :
    (⊥ : Subgroup A).subgroupOf ⊤ = ⊥ := by
  ext x
  simp [Subgroup.mem_subgroupOf]

private noncomputable def quotTopBotEquiv (A : Type) [CommGroup A] :
    ↥(⊤ : Subgroup A) ⧸ ((⊥ : Subgroup A).subgroupOf ⊤) ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq (subgroupOf_bot_top_eq_bot A)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

private noncomputable def quotEquiv {A : Type} [CommGroup A] (S N : Subgroup A) (hS : S = ⊤)
    (hN : N = ⊥) : ↥S ⧸ N.subgroupOf S ≃* A := by
  subst hS
  subst hN
  exact quotTopBotEquiv A

private theorem natHom_of_realizes {V : Type} [CommGroup V] {K : Type} [Field K]
    (Γ : Subgroup (GL (Fin 2) K)) (H : Subgroup (MulAut V)) (U' Z : Subgroup V)
    (π : ↥Γ →* ↥H) (hR : (FFModel.nat Γ).RealizesVia H U' Z π) :
    ∃ β : ↥U' →* Multiplicative (Fin 2 → K),
      Function.Surjective β ∧ (∀ u : ↥U', β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥U') (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U'),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = natAct Γ γ (β u) := by
  obtain ⟨_, _, _, _, _, _, _, β₀, hβsurj, hβker, hβeq⟩ := hR
  let Θ : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec ≃*
      Multiplicative (Fin 2 → K) := quotEquiv (FFModel.nat Γ).sec (FFModel.nat Γ).ker rfl rfl
  refine ⟨Θ.toMonoidHom.comp β₀, ?_, ?_, ?_⟩
  · exact Θ.surjective.comp hβsurj
  · intro u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff]
    exact hβker u
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hm' : (FFModel.nat Γ).act γ m.1 ∈ (FFModel.nat Γ).sec := Subgroup.mem_top _
    have key : β₀ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
        QuotientGroup.mk (⟨(FFModel.nat Γ).act γ m.1, hm'⟩ : ↥(FFModel.nat Γ).sec) :=
      hβeq γ u m hu hm' hm.symm
    show Θ (β₀ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩) = natAct Γ γ (Θ (β₀ u))
    rw [key, ← hm]
    rfl

private theorem matrix_eq_one_of_mulVec {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (h : ∀ y : Fin 2 → K, M *ᵥ y = y) : M = 1 := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hj
  simpa [Matrix.one_apply, Pi.single_apply] using hj

private theorem nat_gamma_eq_one {V : Type} [CommGroup V] {K : Type} [Field K]
    (Γ : Subgroup (GL (Fin 2) K)) (H : Subgroup (MulAut V)) {U' : Subgroup V}
    (π : ↥Γ →* ↥H) (β : ↥U' →* Multiplicative (Fin 2 → K))
    (hsurj : Function.Surjective β)
    (hequi : ∀ (γ : ↥Γ) (u : ↥U') (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U'),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = natAct Γ γ (β u))
    (γ : ↥Γ) (hγ : π γ = 1) : γ = 1 := by
  have hfix : ∀ y : Fin 2 → K, ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ y = y := by
    intro y
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.ofAdd y)
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U' := by
      rw [hγ]
      simpa using u.2
    have hsub : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U') = u := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
      rw [hγ]
      rfl
    have key := hequi γ u hu'
    rw [hsub, hu] at key
    have key' := congrArg Multiplicative.toAdd key
    simpa [natAct] using key'.symm
  have hM : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    matrix_eq_one_of_mulVec _ hfix
  exact Subtype.ext (Units.ext hM)

private theorem cancel_comm {V : Type} [CommGroup V] (z a b : V) :
    z⁻¹ * (z * a * b) * a⁻¹ = b := by
  calc z⁻¹ * (z * a * b) * a⁻¹ = (z⁻¹ * z) * (a * a⁻¹) * b := by ac_rfl
    _ = b := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

private theorem indep_aux {V : Type} [CommGroup V] {Z I0 I1 : Subgroup V}
    (hind0 : I0 ⊓ (Z ⊔ I1) ≤ Z) (hind1 : I1 ⊓ (Z ⊔ I0) ≤ Z)
    {z z' x₀ x₀' x₁ x₁' : V} (hz : z ∈ Z) (hz' : z' ∈ Z)
    (hx₀ : x₀ ∈ I0) (hx₀' : x₀' ∈ I0) (hx₁ : x₁ ∈ I1) (hx₁' : x₁' ∈ I1)
    (h : z * x₀ * x₁ = z' * x₀' * x₁') :
    x₀ * x₀'⁻¹ ∈ Z ∧ x₁ * x₁'⁻¹ ∈ Z := by
  have e1 : x₀ = z⁻¹ * (z' * x₀' * x₁') * x₁⁻¹ := by
    rw [← h]
    group
  have e2 : x₁ = z⁻¹ * (z' * x₀' * x₁') * x₀⁻¹ := by
    rw [← h]
    exact (cancel_comm z x₀ x₁).symm
  constructor
  · have key : x₀ * x₀'⁻¹ = (z⁻¹ * z') * (x₁' * x₁⁻¹) := by
      calc x₀ * x₀'⁻¹ = (z⁻¹ * (z' * x₀' * x₁') * x₁⁻¹) * x₀'⁻¹ := congrArg (· * x₀'⁻¹) e1
        _ = (z⁻¹ * z') * (x₁' * x₁⁻¹) * (x₀' * x₀'⁻¹) := by ac_rfl
        _ = (z⁻¹ * z') * (x₁' * x₁⁻¹) := by rw [mul_inv_cancel, mul_one]
    have hmem : x₀ * x₀'⁻¹ ∈ I0 ⊓ (Z ⊔ I1) := by
      refine Subgroup.mem_inf.mpr ⟨I0.mul_mem hx₀ (I0.inv_mem hx₀'), ?_⟩
      rw [key]
      exact (Z ⊔ I1).mul_mem (Subgroup.mem_sup_left (Z.mul_mem (Z.inv_mem hz) hz'))
        (Subgroup.mem_sup_right (I1.mul_mem hx₁' (I1.inv_mem hx₁)))
    exact hind0 hmem
  · have key : x₁ * x₁'⁻¹ = (z⁻¹ * z') * (x₀' * x₀⁻¹) := by
      calc x₁ * x₁'⁻¹ = (z⁻¹ * (z' * x₀' * x₁') * x₀⁻¹) * x₁'⁻¹ := congrArg (· * x₁'⁻¹) e2
        _ = (z⁻¹ * z') * (x₀' * x₀⁻¹) * (x₁' * x₁'⁻¹) := by ac_rfl
        _ = (z⁻¹ * z') * (x₀' * x₀⁻¹) := by rw [mul_inv_cancel, mul_one]
    have hmem : x₁ * x₁'⁻¹ ∈ I1 ⊓ (Z ⊔ I0) := by
      refine Subgroup.mem_inf.mpr ⟨I1.mul_mem hx₁ (I1.inv_mem hx₁'), ?_⟩
      rw [key]
      exact (Z ⊔ I0).mul_mem (Subgroup.mem_sup_left (Z.mul_mem (Z.inv_mem hz) hz'))
        (Subgroup.mem_sup_right (I0.mul_mem hx₀' (I0.inv_mem hx₀)))
    exact hind1 hmem

private theorem eq_of_div_mem {A : Type} [Group A] {V : Type} [CommGroup V] {Z I : Subgroup V}
    (β : ↥I →* A) (hk : ∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) {a b : ↥I}
    (hab : (a : V) * (b : V)⁻¹ ∈ Z) : β a = β b := by
  have h1 : β (a * b⁻¹) = 1 := by
    rw [hk, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hab
  calc β a = β (a * b⁻¹ * b) := by group
    _ = β (a * b⁻¹) * β b := map_mul β _ _
    _ = β b := by rw [h1, one_mul]

theorem exists_model_of_directSumOfCopies {V : Type} [CommGroup V] (H : Subgroup (MulAut V))
    (U Z : Subgroup V) {K : Type} [Field K]
    (h : DirectSumOfCopies H U Z (FFModel.nat (StatedSL 2 K)) 2) :
    ∃ (π : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H)
      (ψ : ↥U →* Multiplicative ((Fin 2 → K) × (Fin 2 → K))),
      Function.Surjective ψ ∧ (∀ u : ↥U, ψ u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U) (hu : (π g : MulAut V) (u : V) ∈ U),
        ψ ⟨(π g : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (rhoSL K g (Multiplicative.toAdd (ψ u))) := by
  classical
  obtain ⟨I, π₀, -, hind, hsup, hR⟩ := h
  obtain ⟨β0, hβ0s, hβ0k, hβ0e⟩ :=
    natHom_of_realizes (K := K) (V := V) (StatedSL 2 K) H (I 0) Z π₀ (hR 0)
  obtain ⟨β1, hβ1s, hβ1k, hβ1e⟩ :=
    natHom_of_realizes (K := K) (V := V) (StatedSL 2 K) H (I 1) Z π₀ (hR 1)
  let e := specialLinearGroupEquivStatedSL 2 K
  let f : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H := π₀.comp e.toMonoidHom
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : e g = 1 := nat_gamma_eq_one (StatedSL 2 K) H π₀ β0 hβ0s hβ0e (e g) hg
    exact (e.map_eq_one_iff).mp hg'
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 2 K), π₀ γ = p := (hR 0).1 p
    refine ⟨e.symm γ, ?_⟩
    show π₀ (e (e.symm γ)) = p
    rw [MulEquiv.apply_symm_apply]
    exact hγ
  let π' : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hI1 : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
    le_iSup₂ (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide)
  have hI0 : I 0 ≤ ⨆ (j : Fin 2) (_ : j ≠ 1), I j :=
    le_iSup₂ (f := fun (j : Fin 2) (_ : j ≠ 1) => I j) 0 (by decide)
  have hind0 : I 0 ⊓ (Z ⊔ I 1) ≤ Z :=
    (inf_le_inf_left (I 0) (sup_le_sup_left hI1 Z)).trans (hind 0).le
  have hind1 : I 1 ⊓ (Z ⊔ I 0) ≤ Z :=
    (inf_le_inf_left (I 1) (sup_le_sup_left hI0 Z)).trans (hind 1).le
  have hwI : (⨆ i, I i) ≤ I 0 ⊔ I 1 :=
    iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩)
  have hIU : ∀ i, I i ≤ U := fun i => by
    rw [← hsup]
    exact le_sup_of_le_right (le_iSup I i)
  have hdec : ∀ u : V, u ∈ U → ∃ z ∈ Z, ∃ x₀ ∈ I 0, ∃ x₁ ∈ I 1, u = z * x₀ * x₁ := by
    intro u hu
    rw [← hsup, Subgroup.mem_sup] at hu
    obtain ⟨z, hz, w, hw, rfl⟩ := hu
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Subgroup.mem_sup.mp (hwI hw)
    exact ⟨z, hz, x₀, hx₀, x₁, hx₁, (mul_assoc _ _ _).symm⟩
  have hdecU : ∀ u : ↥U, ∃ (z : ↥Z) (x₀ : ↥(I 0)) (x₁ : ↥(I 1)),
      (u : V) = (z : V) * (x₀ : V) * (x₁ : V) := by
    intro u
    obtain ⟨z, hz, x₀, hx₀, x₁, hx₁, huv⟩ := hdec u u.2
    exact ⟨⟨z, hz⟩, ⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩, huv⟩
  choose z x₀ x₁ hdecU' using hdecU
  have wd : ∀ (u : ↥U) (z' : ↥Z) (x₀' : ↥(I 0)) (x₁' : ↥(I 1)),
      (u : V) = (z' : V) * (x₀' : V) * (x₁' : V) →
      β0 (x₀ u) = β0 x₀' ∧ β1 (x₁ u) = β1 x₁' := by
    intro u z' x₀' x₁' hd
    obtain ⟨h0, h1⟩ := indep_aux hind0 hind1 (z u).2 z'.2 (x₀ u).2 x₀'.2 (x₁ u).2 x₁'.2
      ((hdecU' u).symm.trans hd)
    exact ⟨eq_of_div_mem β0 hβ0k h0, eq_of_div_mem β1 hβ1k h1⟩
  let ψfun : ↥U → Multiplicative ((Fin 2 → K) × (Fin 2 → K)) := fun u =>
    Multiplicative.ofAdd (Multiplicative.toAdd (β0 (x₀ u)), Multiplicative.toAdd (β1 (x₁ u)))
  have hψmul : ∀ u v : ↥U, ψfun (u * v) = ψfun u * ψfun v := by
    intro u v
    have eq : ((u * v : ↥U) : V) = ((z u * z v : ↥Z) : V) * ((x₀ u * x₀ v : ↥(I 0)) : V) *
        ((x₁ u * x₁ v : ↥(I 1)) : V) := by
      simp only [Subgroup.coe_mul]
      rw [hdecU' u, hdecU' v]
      ac_rfl
    obtain ⟨h0, h1⟩ := wd (u * v) _ _ _ eq
    simp only [ψfun]
    rw [h0, h1, map_mul β0, map_mul β1]
    simp only [toAdd_mul, ← ofAdd_add, Prod.mk_add_mk]
  let ψ : ↥U →* Multiplicative ((Fin 2 → K) × (Fin 2 → K)) := MonoidHom.mk' ψfun hψmul
  have hψ : ∀ u, ψ u = ψfun u := fun u => rfl
  have hψsurj : Function.Surjective ψ := by
    intro p
    obtain ⟨x₀', hx₀'⟩ := hβ0s (Multiplicative.ofAdd (Multiplicative.toAdd p).1)
    obtain ⟨x₁', hx₁'⟩ := hβ1s (Multiplicative.ofAdd (Multiplicative.toAdd p).2)
    have hmemU : (x₀' : V) * (x₁' : V) ∈ U := U.mul_mem (hIU 0 x₀'.2) (hIU 1 x₁'.2)
    refine ⟨⟨(x₀' : V) * (x₁' : V), hmemU⟩, ?_⟩
    have hu : ((⟨(x₀' : V) * (x₁' : V), hmemU⟩ : ↥U) : V) =
        ((1 : ↥Z) : V) * (x₀' : V) * (x₁' : V) := by
      simp
    obtain ⟨h0, h1⟩ := wd _ 1 x₀' x₁' hu
    rw [hψ]
    simp only [ψfun]
    rw [h0, h1, hx₀', hx₁']
    simp
  have hψker : ∀ u : ↥U, ψ u = 1 ↔ (u : V) ∈ Z := by
    intro u
    rw [hψ]
    constructor
    · intro hu
      have hu' := congrArg Multiplicative.toAdd hu
      simp only [ψfun, toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero] at hu'
      have h0 : β0 (x₀ u) = 1 := toAdd_eq_zero.mp hu'.1
      have h1 : β1 (x₁ u) = 1 := toAdd_eq_zero.mp hu'.2
      have hx0 : ((x₀ u : ↥(I 0)) : V) ∈ Z := (hβ0k (x₀ u)).mp h0
      have hx1 : ((x₁ u : ↥(I 1)) : V) ∈ Z := (hβ1k (x₁ u)).mp h1
      rw [hdecU' u]
      exact Z.mul_mem (Z.mul_mem (z u).2 hx0) hx1
    · intro hu
      obtain ⟨h0, h1⟩ := wd u ⟨(u : V), hu⟩ 1 1 (by simp)
      simp [ψfun, h0, h1]
  have hcoe : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ((e g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K) :=
    fun g => specialLinearGroupEquivStatedSL_coe 2 K g
  have hequi : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
      (hu : (π' g : MulAut V) (u : V) ∈ U),
      ψ ⟨(π' g : MulAut V) (u : V), hu⟩ =
        Multiplicative.ofAdd (rhoSL K g (Multiplicative.toAdd (ψ u))) := by
    intro g u hu
    have hw : ((π₀ (e g) : ↥H) : MulAut V) (u : V) =
        ((π₀ (e g) : ↥H) : MulAut V) (z u : V) * ((π₀ (e g) : ↥H) : MulAut V) (x₀ u : V) *
          ((π₀ (e g) : ↥H) : MulAut V) (x₁ u : V) := by
      rw [hdecU' u, map_mul, map_mul]
    have hz0 : ((π₀ (e g) : ↥H) : MulAut V) (z u : V) ∈ Z :=
      (hR 0).2.2.2.2.1 (π₀ (e g)) (z u : V) (z u).2
    have hx0 : ((π₀ (e g) : ↥H) : MulAut V) (x₀ u : V) ∈ I 0 :=
      (hR 0).2.2.2.1 (π₀ (e g)) (x₀ u : V) (x₀ u).2
    have hx1 : ((π₀ (e g) : ↥H) : MulAut V) (x₁ u : V) ∈ I 1 :=
      (hR 1).2.2.2.1 (π₀ (e g)) (x₁ u : V) (x₁ u).2
    obtain ⟨h0, h1⟩ :=
      wd ⟨((π₀ (e g) : ↥H) : MulAut V) (u : V), hu⟩ ⟨_, hz0⟩ ⟨_, hx0⟩ ⟨_, hx1⟩ hw
    show ψfun ⟨((π₀ (e g) : ↥H) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (rhoSL K g (Multiplicative.toAdd (ψfun u)))
    dsimp only [ψfun]
    rw [h0.trans (hβ0e (e g) (x₀ u) hx0), h1.trans (hβ1e (e g) (x₁ u) hx1)]
    simp only [natAct, toAdd_ofAdd, rhoSL_apply, hcoe]
  exact ⟨π', ψ, hψsurj, hψker, hequi⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
