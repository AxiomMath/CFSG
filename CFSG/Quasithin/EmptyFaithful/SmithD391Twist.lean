module

public import CFSG.Quasithin.Background.F918X0
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.EmptyFaithful.S153ZE
public import CFSG.Quasithin.EmptyFaithful.S153ZK

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391

open scoped Pointwise
open CFSG.Quasithin.F918X

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] noncomputable def actAut (Λ : Subgroup Γ) (V : Subgroup Q)
    (hV : ∀ l : ↥Λ, ∀ v ∈ V, l • v ∈ V) : ↥Λ →* MulAut ↥V :=
  letI := subAct (Γ := ↥Λ) V hV
  MulDistribMulAction.toMulAut ↥Λ ↥V

theorem actAut_apply {Λ : Subgroup Γ} {V : Subgroup Q} (hV : ∀ l : ↥Λ, ∀ v ∈ V, l • v ∈ V)
    (l : ↥Λ) (v : ↥V) : ((actAut Λ V hV l v : ↥V) : Q) = (l : Γ) • (v : Q) := rfl

section Twist

variable {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q}
  (hV : ∀ l : ↥Λ, ∀ v ∈ V, l • v ∈ V) (hinj : Function.Injective (actAut Λ V hV))

@[expose] noncomputable def actEquiv : ↥Λ ≃* ↥(actAut Λ V hV).range :=
  MonoidHom.ofInjective hinj

theorem actEquiv_apply (l : ↥Λ) :
    ((actEquiv hV hinj l : ↥(actAut Λ V hV).range) : MulAut ↥V) = actAut Λ V hV l := rfl

@[expose] noncomputable def twistAut : Γ →* MulAut ↥(actAut Λ V hV).range :=
  letI : Λ.Normal := ⟨fun n hn g => hΛ g n hn⟩
  (MulAut.congr (actEquiv hV hinj)).toMonoidHom.comp MulAut.conjNormal

theorem twistAut_actEquiv (g : Γ) (l : ↥Λ) :
    ((twistAut hΛ hV hinj g (actEquiv hV hinj l) : ↥(actAut Λ V hV).range) : MulAut ↥V) =
      actAut Λ V hV ⟨g * l * g⁻¹, hΛ g l l.2⟩ := by
  have : Λ.Normal := ⟨fun n hn g => hΛ g n hn⟩
  have h1 : (twistAut hΛ hV hinj g) (actEquiv hV hinj l) =
      actEquiv hV hinj (MulAut.conjNormal g l) := by
    show (actEquiv hV hinj) ((MulAut.conjNormal g) ((actEquiv hV hinj).symm
      (actEquiv hV hinj l))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h1, actEquiv_apply]
  congr 1

theorem iso_of_twistAut_mem (g : Γ)
    (h : twistAut hΛ hV hinj g⁻¹ ∈ realized (actAut Λ V hV).range) :
    XMod.Iso ↥Λ V (g • V) := by
  obtain ⟨θ, hθ⟩ := mem_realized.mp h
  refine ⟨θ.trans (XMod.smulEquiv g V), fun a v v' hvv' => ?_⟩
  set a' : ↥Λ := ⟨g⁻¹ * (a : Γ) * g⁻¹⁻¹, hΛ g⁻¹ a a.2⟩ with ha'
  have key := hθ (actEquiv hV hinj a)
  rw [twistAut_actEquiv, actEquiv_apply] at key
  have hv' : actAut Λ V hV a v = v' := Subtype.ext hvv'
  have h1 : θ v' = actAut Λ V hV a' (θ v) := by
    rw [← hv']
    have := congrArg (fun φ : MulAut ↥V => φ (θ v)) key
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
    rw [← this]
  show (a : Γ) • g • ((θ v : ↥V) : Q) = g • ((θ v' : ↥V) : Q)
  rw [h1, actAut_apply, smul_smul, smul_smul]
  congr 1
  rw [ha']
  simp [mul_assoc]

include hΛ hinj in
theorem iso_or_iso_of_twoClass [Finite Q] (htc : TwoClassMod (actAut Λ V hV).range) {t : Γ}
    (ht : ¬ XMod.Iso ↥Λ V (t • V)) (g : Γ) :
    XMod.Iso ↥Λ V (g • V) ∨ XMod.Iso ↥Λ (t • V) (g • V) := by
  set R := realized (actAut Λ V hV).range with hR
  by_cases h1 : twistAut hΛ hV hinj g⁻¹ ∈ R
  · exact Or.inl (iso_of_twistAut_mem hΛ hV hinj g h1)
  right
  have h2 : twistAut hΛ hV hinj t⁻¹ ∉ R := fun h => ht (iso_of_twistAut_mem hΛ hV hinj t h)
  have hidx : R.index = 2 := by
    have hle : R.index ≤ 2 := htc
    have hne0 : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hne1 : R.index ≠ 1 := fun h => h1 ((Subgroup.index_eq_one.mp h) ▸ Subgroup.mem_top _)
    omega
  have h2' : twistAut hΛ hV hinj t ∉ R := by
    intro h
    apply h2
    rw [map_inv]
    exact R.inv_mem h
  have h3 : twistAut hΛ hV hinj (t⁻¹ * g)⁻¹ ∈ R := by
    rw [mul_inv_rev, inv_inv, map_mul]
    exact (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false h1 h2')
  have h4 := iso_of_twistAut_mem hΛ hV hinj (t⁻¹ * g) h3
  have h5 := XMod.iso_smul (normalizes_whole Λ hΛ) t h4
  rwa [smul_smul, mul_inv_cancel_left] at h5

end Twist

section Transfer

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W} {D : FFModel}
  {π₀ : D.Gam →* ↥H} {Λ : Subgroup Γ} {V : Subgroup Q} (hV : ∀ l : ↥Λ, ∀ v ∈ V, l • v ∈ V)

theorem realizesVia_actAut (hR : D.RealizesVia H U Z π₀) (ψ : ↥H →* ↥Λ)
    (hψ : Function.Surjective ψ) (f : ↥U →* ↥V) (hf : Function.Surjective f)
    (hfker : ∀ u : ↥U, f u = 1 ↔ (u : W) ∈ Z)
    (hfeq : ∀ (h : ↥H) (u : ↥U) (hu : (h : MulAut W) (u : W) ∈ U),
      f ⟨_, hu⟩ = actAut Λ V hV (ψ h) (f u)) :
    D.RealizesVia (actAut Λ V hV).range ⊤ ⊥
      ((actAut Λ V hV).rangeRestrict.comp (ψ.comp π₀)) := by
  obtain ⟨hsurj, -, hkerle, hUinv, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hR
  have hkle : f.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (hβk u).2 ((hfker u).1 hu)
  let e : (↥U ⧸ f.ker) ≃* ↥V := QuotientGroup.quotientKerEquivOfSurjective f hf
  let βbar : ↥V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.lift f.ker β hkle).comp e.symm.toMonoidHom
  have hβbar : ∀ u : ↥U, βbar (f u) = β u := by
    intro u
    have h1 : e.symm (f u) = (QuotientGroup.mk u : ↥U ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift f.ker β hkle (e.symm (f u)) = β u
    rw [h1]
    rfl
  let β' : ↥(⊤ : Subgroup ↥V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    βbar.comp (⊤ : Subgroup ↥V).subtype
  refine ⟨?_, bot_le, hkerle, fun _ _ _ => trivial, ?_, hsec, hkerinv, β', ?_, ?_, ?_⟩
  · intro x
    obtain ⟨φ, ⟨l, rfl⟩⟩ := x
    obtain ⟨h, rfl⟩ := hψ l
    obtain ⟨γ, rfl⟩ := hsurj h
    exact ⟨γ, rfl⟩
  · intro g z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    refine ⟨⟨f u, trivial⟩, ?_⟩
    show βbar (f u) = β u
    exact hβbar u
  · intro y
    obtain ⟨u, hu⟩ := hf (y : ↥V)
    show βbar (y : ↥V) = 1 ↔ (y : ↥V) ∈ (⊥ : Subgroup ↥V)
    rw [← hu, hβbar, hβk, Subgroup.mem_bot, ← hfker]
  · intro γ y m hy hm hym
    obtain ⟨u, hu⟩ := hf (y : ↥V)
    have hum : β u = QuotientGroup.mk m := by
      rw [← hβbar, hu]
      exact hym
    have hgu : ((π₀ γ : ↥H) : MulAut W) (u : W) ∈ U := hUinv (π₀ γ) u u.2
    have key := hβe γ u m hgu hm hum
    set x : ↥(actAut Λ V hV).range := ((actAut Λ V hV).rangeRestrict.comp (ψ.comp π₀)) γ
      with hx
    have hact : (x : MulAut ↥V) (y : ↥V) = f ⟨_, hgu⟩ := by
      rw [hfeq (π₀ γ) u hgu, hu]
      rfl
    show βbar ((x : MulAut ↥V) (y : ↥V)) = _
    rw [hact, hβbar]
    exact key

end Transfer

end CFSG.Quasithin.SmithD391
