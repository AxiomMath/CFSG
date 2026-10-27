module

public import CFSG.Quasithin.MS93.MSPOmega
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.MS93.M15LiftGen

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix IsMulCommutative

theorem exists_cover_of_realizesVia {D : FFModel} {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {Z : Subgroup V} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ Z π) :
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
    H13.VolI.mem_closure_of_commV hρH hρs hcomm⟩, fun _ => rfl,
    fun v => hβk ⟨v, Subgroup.mem_top v⟩⟩
  · obtain ⟨u, hu⟩ := hβs s
    exact ⟨u, hu⟩
  · exact hZ ((hβk ⟨v, Subgroup.mem_top v⟩).1 hv) _ (π γ).2

section Omega5

variable {F : Type} [Field F] [CharP F 2]

theorem exists_omega5_quotient [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) {π : ↥(StatedSp 2 F) →* ↥H}
    (hreal : (FFModel.nat (StatedSp 2 F)).RealizesVia H ⊤ Z π) :
    ∃ ψ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) →* W, Function.Surjective ψ ∧
      (∀ γ y, ψ (omega5Act F γ y) = (π γ : MulAut W) (ψ y)) ∧
      ∀ y, ψ y ∈ Z → y ∈ omega5Rad F := by
  have hD : (FFModel.omega5 F (omega5Rad F)).IsActionModel := omega5_isActionModel le_rfl
  have : Finite (FFModel.omega5 F (omega5Rad F)).Amb :=
    (inferInstance : Finite (Multiplicative ((Ix → F) × F)))
  have : Finite ↥(FFModel.omega5 F (omega5Rad F)).sec := Subtype.finite
  have hE2' : ∀ m : Multiplicative ((Ix → F) × F), m ^ 2 = 1 := by
    intro m
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hE2 : ∀ m : ↥(FFModel.omega5 F (omega5Rad F)).sec, m ^ 2 = 1 := fun m =>
    Subtype.ext (hE2' m.1)
  have hRc : Nat.card ↥((FFModel.omega5 F (omega5Rad F)).ker.subgroupOf
      (FFModel.omega5 F (omega5Rad F)).sec) = 2 ^ n := by
    show Nat.card ↥((omega5Rad F).subgroupOf ⊤) = 2 ^ n
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, ← hF]
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
        ∃ (g : ↥(StatedSp 2 F)) (z : Multiplicative ((Ix → F) × F)),
          x = omega5Act F g z * z⁻¹} ≤
        (Subgroup.closure {x : ↥(FFModel.omega5 F (omega5Rad F)).sec |
          ∃ γ y, x = secAut hD γ y * y⁻¹}).map
          (FFModel.omega5 F (omega5Rad F)).sec.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g, z, rfl⟩
      exact ⟨secAut hD g ⟨z, Subgroup.mem_top _⟩ *
          (⟨z, Subgroup.mem_top _⟩ : ↥(FFModel.omega5 F (omega5Rad F)).sec)⁻¹,
        Subgroup.subset_closure ⟨g, _, rfl⟩, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle (Sp4L.omega5_gen_all m.1)
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  have hbound : ∀ (W' : Type) [CommGroup W'] [Finite W'], (∀ w : W', w ^ 2 = 1) →
      ∀ C : H13.VolI.ModelCover (FFModel.omega5 F (omega5Rad F)) W',
        Nat.card C.β.ker ≤ Nat.card ↥((FFModel.omega5 F (omega5Rad F)).ker.subgroupOf
          (FFModel.omega5 F (omega5Rad F)).sec) := by
    intro W' _ _ hW' C
    have hR' := MS93.ModelCover.realizesVia_range hD C
    have hfix : C.β.ker ≤ fixV C.ρ.range := by
      intro z hz x hx
      obtain ⟨γ, rfl⟩ := hx
      exact C.fix γ z (MonoidHom.mem_ker.1 hz)
    rw [hRc]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · have hcomm' : commV C.ρ.range = ⊤ := eq_top_iff.2 fun v _ =>
        Subgroup.closure_mono (by
          rintro _ ⟨γ, w, rfl⟩
          exact ⟨C.ρ γ, ⟨γ, rfl⟩, w, rfl⟩) (C.gen v)
      have hS := asSp4S6 W' C.ρ.range ⊤ C.β.ker
        ⟨F, inferInstance, inferInstance, hF, ⟨_, Sp4L.natRealizesVia_of_omega5 hR'⟩⟩
      rw [pow_one]
      exact Sp4L.card_le_two_of_symNatural hW' hS
        (fun z hz x hx => hfix hz x (Subgroup.commutator_le_self _ hx)) hcomm'
    · exact card_le_of_omega5_realizesVia hW' C.ρ.range ⊤ C.β.ker le_top
        (fun z hz x hx => hfix hz x hx) (fun _ _ _ _ => Subgroup.mem_top _)
        (MS93.ModelCover.commOf_range C) hn2 hF hR'
  obtain ⟨C, hρ, hβk⟩ := exists_cover_of_realizesVia hZ hcomm (omega5_realizesVia_of_nat hreal)
  obtain ⟨ψ, hψs, -, hψe, hψβ⟩ :=
    MS93.ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl) hkfix hgenE hE2 hbound hW C
  refine ⟨ψ.comp Subgroup.topEquiv.symm.toMonoidHom, fun w => ?_, fun γ y => ?_, fun y hy => ?_⟩
  · obtain ⟨m, rfl⟩ := hψs w
    exact ⟨m.1, congrArg ψ (Subtype.ext rfl)⟩
  · have h1 := hψe γ ⟨y, Subgroup.mem_top y⟩
    exact (congrArg ψ (Subtype.ext rfl)).trans (h1.trans (DFunLike.congr_fun (hρ γ) _))
  · have h1 : C.β (ψ ⟨y, Subgroup.mem_top y⟩) = 1 := (hβk _).2 hy
    rw [hψβ, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1

theorem exists_hom_two_of_not_mem {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {D : Subgroup W} {z : W} (hz : z ∉ D) :
    ∃ f : W →* Multiplicative (ZMod 2), (∀ d ∈ D, f d = 1) ∧ f z ≠ 1 := by
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    have := hW (Additive.toMul x)
    apply Additive.toMul.injective
    rw [toMul_nsmul, this, toMul_zero]
  let D' : Submodule (ZMod 2) (Additive W) :=
    { carrier := {x | Additive.toMul x ∈ D}
      add_mem' := fun ha hb => D.mul_mem ha hb
      zero_mem' := D.one_mem
      smul_mem' := fun c x hx => by
        fin_cases c
        · show Additive.toMul ((0 : ZMod 2) • x) ∈ D
          rw [zero_smul]
          exact D.one_mem
        · show Additive.toMul ((1 : ZMod 2) • x) ∈ D
          rw [one_smul]
          exact hx }
  have hz' : Submodule.Quotient.mk (p := D') (Additive.ofMul z) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hz
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive W ⧸ D'),
      φ (Submodule.Quotient.mk (Additive.ofMul z)) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz' ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 hall)
  let f : W →* Multiplicative (ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul w)))
      map_one' := by
        show Multiplicative.ofAdd (φ (D'.mkQ 0)) = 1
        rw [map_zero, map_zero]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul a + Additive.ofMul b))) = _
        rw [map_add, map_add, ofAdd_add] }
  refine ⟨f, fun d hd => ?_, fun h1 => hφ ?_⟩
  · have h0 : D'.mkQ (Additive.ofMul d) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hd
    show Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul d))) = 1
    rw [h0, map_zero]
    rfl
  · have : Multiplicative.ofAdd (φ (D'.mkQ (Additive.ofMul z))) = 1 := h1
    exact this

theorem le_orthSp_of_omega5 [Finite F] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} {π : ↥(StatedSp 2 F) →* ↥H}
    {ψ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) →* W} (hψs : Function.Surjective ψ)
    (hψe : ∀ γ y, ψ (omega5Act F γ y) = (π γ : MulAut W) (ψ y))
    {Z D : Subgroup W} (hψZ : ∀ y, ψ y ∈ Z → y ∈ omega5Rad F) (hZD : ¬ Z ≤ D) :
    ∃ Q : MSP.V4 F → F, MSP.IsQuadOf Q ∧ ∀ g : MSP.Sp4 F,
      (∀ w : W, (π g : MulAut W) w * w⁻¹ ∈ D) → g ∈ MSP.orthSp Q := by
  obtain ⟨z, hzZ, hzD⟩ := Set.not_subset.1 hZD
  obtain ⟨f₀, hf₀D, hf₀z⟩ := exists_hom_two_of_not_mem hW hzD
  obtain ⟨y₀, rfl⟩ := hψs z
  obtain ⟨Q, hQ, hQg⟩ := MSP.exists_isQuadOf_of_omega5_fix (f₀.comp ψ) ⟨y₀, hψZ y₀ hzZ, hf₀z⟩
  refine ⟨Q, hQ, fun g hg => hQg g fun y => ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hψe]
  have e : (π g : MulAut W) (ψ y) = ((π g : MulAut W) (ψ y) * (ψ y)⁻¹) * ψ y := by group
  rw [e, map_mul, hf₀D _ (hg _), one_mul]

end Omega5

section Module

variable {G : Type} [Group G] {A U : Subgroup G} {F : Type} [Field F]
  {α : ↥A →* ↥(StatedSp 2 F)}

theorem exists_pi_of_ker (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hsurj : Function.Surjective α)
    (hker : ∀ a : ↥A, α a = 1 → (a : G) ∈ Subgroup.centralizer (U : Set G)) :
    ∃ π : ↥(StatedSp 2 F) →* ↥(autOn A U), Function.Surjective π ∧
      ∀ a : ↥A, ((π (α a) : ↥(autOn A U)) : MulAut ↥U) = conjAct U ⟨a, hAU a.2⟩ := by
  let χ : ↥A →* ↥(autOn A U) :=
    ((conjAct U).comp (Subgroup.inclusion hAU)).codRestrict (autOn A U)
      (fun a => Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hAU a, a.2, rfl⟩)
  have hker' : α.ker ≤ χ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct U (Subgroup.inclusion hAU a) = 1
    apply InternalSec.conjAct_eq_one_of_mem_centralizer
    exact hker a ha
  let π := (QuotientGroup.lift α.ker χ hker').comp
    (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm.toMonoidHom
  have hπa : ∀ a, π (α a) = χ a := by
    intro a
    have e : (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α a) =
        QuotientGroup.mk a := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift α.ker χ hker'
      ((QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α a)) = χ a
    rw [e, QuotientGroup.lift_mk]
  refine ⟨π, fun x => ?_, fun a => by rw [hπa]; rfl⟩
  obtain ⟨g, hgA, hgx⟩ := Setup.mem_autOn_iff.1 x.2
  refine ⟨α ⟨g, hgA⟩, ?_⟩
  rw [hπa]
  apply Subtype.ext
  rw [← hgx]
  rfl

theorem realizesVia_nat_of (hAU : A ≤ Subgroup.normalizer (U : Set G)) {Y : Subgroup G}
    (hsurj : Function.Surjective α) [IsMulCommutative ↥U]
    (hnat : IsSumOfNaturalModulesVia A U (U ⊓ Y) α false 1)
    (hAY : A ≤ Subgroup.normalizer ((U ⊓ Y : Subgroup G) : Set G))
    {π : ↥(StatedSp 2 F) →* ↥(autOn A U)} (hπs : Function.Surjective π)
    (hπa : ∀ a : ↥A, ((π (α a) : ↥(autOn A U)) : MulAut ↥U) = conjAct U ⟨a, hAU a.2⟩) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia (autOn A U) ⊤ (Y.subgroupOf U) π := by
  obtain ⟨-, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hnat
  let β₁ : ↥U →* Multiplicative (Fin 2 ⊕ Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0)
      map_one' := by simp
      map_mul' := fun u v => by simp }
  have hβ₁ : ∀ u, β₁ u = Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0) := fun _ => rfl
  have hβ₁s : Function.Surjective β₁ := by
    intro x
    obtain ⟨u, hu⟩ := hβ₀s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd x)
    exact ⟨u, by rw [hβ₁, hu]; rfl⟩
  have hβ₁k : ∀ u, β₁ u = 1 ↔ (u : G) ∈ Y := by
    intro u
    have e1 : β₁ u = 1 ↔ β₀ u = 1 := by
      constructor
      · intro h1
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact congrArg Multiplicative.toAdd h1
      · intro h1
        rw [hβ₁, h1]
        rfl
    rw [e1, ← MonoidHom.mem_ker, hβ₀k, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hβ₁e : ∀ (a : ↥A) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      β₁ v = Multiplicative.ofAdd ((((α a : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β₁ u)) := by
    intro a u v huv
    have := hβ₀e a u v huv 0
    rw [hβ₁, hβ₁, this]
    simp [moduleAct]
  have hstab := InternalSec.autOn_le_stabSub hAY
  refine ⟨hπs, le_top, bot_le, fun _ _ _ => Subgroup.mem_top _, fun x z hz => (hstab x.2 z).2 hz,
    (FFModel.nat_isActionModel _).sec_inv, (FFModel.nat_isActionModel _).ker_inv, ?_⟩
  let β : ↥(⊤ : Subgroup ↥U) →* (FFModel.nat (StatedSp 2 F)).Sec :=
    (QuotientGroup.mk' _).comp
      (Subgroup.topEquiv.symm.toMonoidHom.comp (β₁.comp (⊤ : Subgroup ↥U).subtype))
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥U),
      β u = QuotientGroup.mk ⟨β₁ u, Subgroup.mem_top _⟩ := fun _ => rfl
  refine ⟨β, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨⟨x, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hβ₁s x
    exact ⟨⟨u, Subgroup.mem_top _⟩, by rw [hβ]; congr 1; exact Subtype.ext hu⟩
  · rw [hβ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show β₁ u ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → F))) ↔ _
    rw [Subgroup.mem_bot, hβ₁k, Subgroup.mem_subgroupOf]
  · rw [hβ] at hum ⊢
    have h3 : (⟨β₁ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat (StatedSp 2 F)).sec) = m := by
      have h1 := QuotientGroup.eq.1 hum
      exact inv_mul_eq_one.1 (Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)))
    subst h3
    congr 1
    apply Subtype.ext
    obtain ⟨a₀, rfl⟩ := hsurj γ
    have hval : ((((π (α a₀) : ↥(autOn A U)) : MulAut ↥U) (u : ↥U) : ↥U) : G) =
        (a₀ : G) * ((u : ↥U) : G) * (a₀ : G)⁻¹ := by
      rw [hπa]
      exact InternalSec.coe_conjAct_apply _ _
    exact hβ₁e a₀ (u : ↥U) _ hval

end Module

end CFSG.Quasithin.MS93.S33
