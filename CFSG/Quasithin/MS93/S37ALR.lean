module

public import CFSG.Quasithin.MS93.S37Part

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2 CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix IsMulCommutative

theorem modelCover_of_realizesVia {D : FFModel} {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {Z : Subgroup V} {π : D.Gam →* ↥H} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : D.RealizesVia H ⊤ Z π) :
    ∃ C : H13.VolI.ModelCover D V, (∀ γ, C.ρ γ = (π γ : MulAut V)) ∧
      ∀ v, C.β v = 1 ↔ v ∈ Z := by
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let β' : V →* D.Sec :=
    { toFun := fun v => β ⟨v, Subgroup.mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩ }
  have hρH : ∀ γ, (H.subtype.comp π) γ ∈ H := fun γ => (π γ).2
  have hρs : ∀ x ∈ H, ∃ γ, (H.subtype.comp π) γ = x := fun x hx => by
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  refine ⟨⟨H.subtype.comp π, β', fun s => ?_, fun γ v hv => ?_,
    fun γ v m hm hvm => hβe γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) hm hvm,
    mem_closure_of_commV hρH hρs hcomm⟩, fun _ => rfl, fun v => hβk ⟨v, Subgroup.mem_top v⟩⟩
  · obtain ⟨u, hu⟩ := hβs s
    exact ⟨u, hu⟩
  · exact hZ ((hβk ⟨v, Subgroup.mem_top v⟩).1 hv) _ (π γ).2

theorem omega5_comm_transv {F : Type} [Field F] {c : F} (hc : c ≠ 0) :
    omega5Act F (transv (e₁ F) c⁻¹) (Multiplicative.ofAdd (c • f₁ F, 0)) *
        (Multiplicative.ofAdd (c • f₁ F, (0 : F)))⁻¹ =
      Multiplicative.ofAdd (e₁ F, c) := by
  rw [omega5_comm]
  congr 1
  have hm : spMat (transv (e₁ F) c⁻¹) *ᵥ (c • f₁ F) = c • f₁ F + e₁ F := by
    show mat (transv (e₁ F) c⁻¹) *ᵥ (c • f₁ F) = _
    rw [transv_mulVec, form_e₁]
    simp [f₁, inv_mul_cancel₀ hc]
  rw [hm]
  refine Prod.ext (by simp) ?_
  simp only [sp4Quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e₁, f₁]
  simp

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem A_le_closure (hq : 2 < Nat.card F) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.closure
      {x | ∃ (l : G) (hl : l ∈ L) (u : G), u ∈ Uq M T L ∧ C.α ⟨l, hl⟩ ∈ X₂ F ∧
        x = l * u * l⁻¹ * u⁻¹} := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hFn : Nat.card F = 2 ^ C.k := by rw [Nat.card_eq_fintype_card, C.hF]
  have := Sp4L.isMulCommutative_uq C.h
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := C.hnat.1
  obtain ⟨π, hπs, hπa⟩ := exists_piL C.h C.hα C.hnat C.hVU
  have hreal := realizesVia_natL C.hα C.hnat hπs hπa
  have hreal5 := omega5_realizesVia_of_nat hreal
  have hV : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq C.h w.2)
  have hcommL : commV (autOn L (Uq M T L)) = ⊤ :=
    InternalSec.commV_autOn_eq_top hLU C.h.commutator_uq
  have hCL : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn L (Uq M T L)) := InternalSec.le_fixV_autOn inf_le_right
  obtain ⟨Cv, hρ, hβk⟩ := modelCover_of_realizesVia hCL hcommL hreal5
  have hD : (FFModel.omega5 F (omega5Rad F)).IsActionModel := omega5_isActionModel le_rfl
  have : Finite (FFModel.omega5 F (omega5Rad F)).Amb :=
    (inferInstance : Finite (Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)))
  have : Finite ↥(FFModel.omega5 F (omega5Rad F)).sec := Subtype.finite
  have hE2' : ∀ m : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F), m ^ 2 = 1 := by
    intro m
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    refine Prod.ext ?_ ?_
    · funext i
      exact CharTwo.add_self_eq_zero _
    · exact CharTwo.add_self_eq_zero _
  have hE2 : ∀ m : ↥(FFModel.omega5 F (omega5Rad F)).sec, m ^ 2 = 1 := fun m =>
    Subtype.ext (hE2' m.1)
  have hRc : Nat.card ↥((FFModel.omega5 F (omega5Rad F)).ker.subgroupOf
      (FFModel.omega5 F (omega5Rad F)).sec) = 2 ^ C.k := by
    show Nat.card ↥((omega5Rad F).subgroupOf ⊤) = 2 ^ C.k
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, ← hFn]
    have e : F ≃ ↥(omega5Rad F) :=
      { toFun := fun c => ⟨Multiplicative.ofAdd (0, c), rfl⟩
        invFun := fun x => (Multiplicative.toAdd x.1).2
        left_inv := fun _ => rfl
        right_inv := fun x => by
          obtain ⟨y, hy⟩ := x
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          exact Prod.ext (hy : (Multiplicative.toAdd y).1 = 0).symm rfl }
    exact (Nat.card_congr e).symm
  have hkfix : ∀ γ (m : ↥(FFModel.omega5 F (omega5Rad F)).sec),
      (m : (FFModel.omega5 F (omega5Rad F)).Amb) ∈ (FFModel.omega5 F (omega5Rad F)).ker →
        secAut hD γ m = m :=
    fun γ m hm => Subtype.ext (omega5Act_rad γ hm)
  have hgenE : ∀ m : ↥(FFModel.omega5 F (omega5Rad F)).sec,
      m ∈ Subgroup.closure {x | ∃ γ y, x = secAut hD γ y * y⁻¹} := by
    intro m
    have hle : Subgroup.closure {x : (FFModel.omega5 F (omega5Rad F)).Amb |
        ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)),
          x = omega5Act F g z * z⁻¹} ≤
        (Subgroup.closure {x : ↥(FFModel.omega5 F (omega5Rad F)).sec |
          ∃ γ y, x = secAut hD γ y * y⁻¹}).map (FFModel.omega5 F (omega5Rad F)).sec.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g, z, rfl⟩
      exact ⟨secAut hD g ⟨z, Subgroup.mem_top _⟩ *
        (⟨z, Subgroup.mem_top _⟩ : ↥(FFModel.omega5 F (omega5Rad F)).sec)⁻¹,
        Subgroup.subset_closure ⟨g, _, rfl⟩, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle (Sp4L.omega5_gen_all m.1)
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  have hbound : ∀ (W' : Type) [CommGroup W'] [Finite W'], (∀ w : W', w ^ 2 = 1) →
      ∀ C' : H13.VolI.ModelCover (FFModel.omega5 F (omega5Rad F)) W',
        Nat.card C'.β.ker ≤ Nat.card ↥((FFModel.omega5 F (omega5Rad F)).ker.subgroupOf
          (FFModel.omega5 F (omega5Rad F)).sec) := by
    intro W' _ _ hW' C'
    have hR' := MS93.ModelCover.realizesVia_range hD C'
    have hfix : C'.β.ker ≤ fixV C'.ρ.range := by
      intro z hz x hx
      obtain ⟨γ, rfl⟩ := hx
      exact C'.fix γ z (MonoidHom.mem_ker.1 hz)
    rw [hRc]
    exact card_le_of_omega5_realizesVia hW' C'.ρ.range ⊤ C'.β.ker le_top
      (fun z hz x hx => hfix hz x hx) (fun _ _ _ _ => Subgroup.mem_top _)
      (MS93.ModelCover.commOf_range C') C.hk hFn hR'
  obtain ⟨ψ, hψs, -, hψe, hψβ⟩ :=
    MS93.ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl) hkfix hgenE hE2 hbound hV Cv
  set S := {x | ∃ (l : G) (hl : l ∈ L) (u : G), u ∈ Uq M T L ∧ C.α ⟨l, hl⟩ ∈ X₂ F ∧
    x = l * u * l⁻¹ * u⁻¹} with hS
  have hgen : ∀ c : F, c ≠ 0 →
      ((ψ ⟨Multiplicative.ofAdd (e₁ F, c), Subgroup.mem_top _⟩ : ↥(Uq M T L)) : G) ∈
        Subgroup.closure S := by
    intro c hc
    set y : ↥(FFModel.omega5 F (omega5Rad F)).sec :=
      ⟨Multiplicative.ofAdd (c • f₁ F, 0), Subgroup.mem_top _⟩ with hy
    set g : ↥(StatedSp 2 F) := transv (e₁ F) c⁻¹ with hg
    have e1 : (⟨Multiplicative.ofAdd (e₁ F, c), Subgroup.mem_top _⟩ :
        ↥(FFModel.omega5 F (omega5Rad F)).sec) = secAut hD g y * y⁻¹ :=
      Subtype.ext (omega5_comm_transv hc).symm
    have h2 := hψe g y
    rw [e1, map_mul, map_inv, h2, hρ g]
    set l := C.lift g with hl
    have hlL := C.lift_mem g
    have hlα : C.α ⟨l, hlL⟩ = g := C.alpha_lift g
    have hπl : ((π g : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
        conjAct (Uq M T L) ⟨l, hLU hlL⟩ := by
      rw [← hlα]
      exact hπa ⟨l, hlL⟩
    have hval : ((((π.comp (MonoidHom.id (FFModel.omega5 F (omega5Rad F)).Gam)) g :
        ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) (ψ y) : G) = l * (ψ y : G) * l⁻¹ := by
      show ((((π g : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) (ψ y)) : G) = _
      rw [hπl]
      exact InternalSec.coe_conjAct_apply _ _
    refine Subgroup.subset_closure ⟨l, hlL, (ψ y : G), (ψ y).2, ?_, ?_⟩
    · rw [hlα, hg]
      exact transv_mem_X₂ _
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hval]
  intro a ha
  obtain ⟨m, hm⟩ := hψs ⟨a, ha.1⟩
  have haZ : (⟨a, ha.1⟩ : ↥(Uq M T L)) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf
      (Uq M T L) := ha.2
  have hm0 : (Multiplicative.toAdd m.1).1 = 0 := by
    have h1 : Cv.β (ψ m) = 1 := by rw [hm]; exact (hβk _).2 haZ
    rw [hψβ] at h1
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  set s := (Multiplicative.toAdd m.1).2 with hs
  have hma : (a : G) = ((ψ m : ↥(Uq M T L)) : G) := by rw [hm]
  by_cases hs0 : s = 0
  · have hm1 : m = 1 := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      exact Prod.ext hm0 hs0
    rw [hma, hm1, map_one]
    exact (Subgroup.closure S).one_mem
  · obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one hq
    set c₂ := μ * s with hc₂
    have hc₂0 : c₂ ≠ 0 := mul_ne_zero hμ0 hs0
    have hc₁0 : c₂ + s ≠ 0 := by
      intro h
      apply hμ1
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have : (μ - 1) * s = 0 := by linear_combination h - (s) * h2
      have := (mul_eq_zero.1 this).resolve_right hs0
      exact sub_eq_zero.1 this
    have e : m = ⟨Multiplicative.ofAdd (e₁ F, c₂ + s), Subgroup.mem_top _⟩ *
        (⟨Multiplicative.ofAdd (e₁ F, c₂), Subgroup.mem_top _⟩ :
          ↥(FFModel.omega5 F (omega5Rad F)).sec)⁻¹ := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd m.1 = (e₁ F, c₂ + s) + -(e₁ F, c₂)
      refine Prod.ext ?_ ?_
      · rw [hm0]
        simp
      · simp [hs]
    rw [hma, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.closure S).mul_mem (hgen _ hc₁0) ((Subgroup.closure S).inv_mem (hgen _ hc₂0))

theorem A_le_Rt (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Rt M T L θ := by
  refine (C.A_le_closure hq).trans (Subgroup.closure_le _ |>.2 ?_)
  rintro _ ⟨l, hl, u, hu, hlX, rfl⟩
  have hlK : l ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hl
  have hm : C.rho ⟨l, hlK⟩ ∈ C.rhoIm (Ut M T L θ) := by
    rw [hE, C.rho_of_mem_L hl]
    exact hlX
  obtain ⟨t, htK, ht, hρ⟩ := (C.mem_rhoIm).1 hm
  have hyK : l⁻¹ * t ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).mul_mem
    ((L ⊔ pCoreOf 2 M).inv_mem hlK) htK
  have hyQ : l⁻¹ * t ∈ pCoreOf 2 M := by
    refine (C.rho_eq_one_iff ⟨_, hyK⟩).1 ?_
    have e : (⟨l⁻¹ * t, hyK⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨l, hlK⟩)⁻¹ * ⟨t, htK⟩ := rfl
    rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
  have hyu : (l⁻¹ * t) * u = u * (l⁻¹ * t) := comm_of_mem_Uq C.h hu hyQ
  have e : l * u * l⁻¹ * u⁻¹ = ⁅u, t⁆⁻¹ := by
    have ht' : t = l * (l⁻¹ * t) := by group
    rw [commutatorElement_def, ht']
    calc l * u * l⁻¹ * u⁻¹ = l * (u * (l⁻¹ * t)) * (l⁻¹ * t)⁻¹ * l⁻¹ * u⁻¹ := by group
      _ = l * ((l⁻¹ * t) * u) * (l⁻¹ * t)⁻¹ * l⁻¹ * u⁻¹ := by rw [hyu]
      _ = (u * (l * (l⁻¹ * t)) * u⁻¹ * (l * (l⁻¹ * t))⁻¹)⁻¹ := by group
  rw [e]
  exact (Rt M T L θ).inv_mem (Subgroup.commutator_mem_commutator hu ht)

end Cfg

end CFSG.Quasithin.MS93.S37
