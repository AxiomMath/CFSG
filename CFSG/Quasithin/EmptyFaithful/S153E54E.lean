module

public import CFSG.Quasithin.EmptyFaithful.S153E54D
public import CFSG.Quasithin.EmptyFaithful.S153E52G
public import CFSG.Quasithin.EmptyFaithful.S153EInputs
public import CFSG.Quasithin.EmptyFaithful.S153E53A

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem YU_le_normalizer (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
  sup_le ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx)

theorem mem_autI_YU_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂)
    (g : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)) :
    g ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) ↔
      g ∈ orthogonalGroupOf (qW cx) ∧ Even (rk (commV (Subgroup.zpowers g))) := by
  obtain ⟨Ω, hΩ, hsup, -⟩ := c.h53one.omega
  have hY : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans cx.c.hyp.le_normalizer
  have hsup' : autOn (Y153 Mc M ⊔ UH153 T M V₁ Mc) (VZ T M) = Ω := by
    show autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) = Ω
    rw [autI_sup cx.c.hyp.elemAbelian hY (U_le_N cx), sup_comm]
    exact hsup
  have h1 : g ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) ↔ g ∈ Ω :=
    Iff.of_eq (congrArg (fun K : Subgroup (MulAut ↥(VZ T M)) => g ∈ K) hsup')
  refine h1.trans ((hΩ g).trans (and_congr ?_ Iff.rfl))
  exact Iff.of_eq (congrArg
    (fun K : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)) => g ∈ K)
    (qW_spec cx).2.2.2)

structure Setup54 (cx : Ctx15350 T Mc M V₁ V₂ t) where
  ψ : IntMod (VZ T M) cx.c.hyp.elemAbelian ≃* Multiplicative Mt
  α : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc) →* OmG
  surj : Function.Surjective α
  ker : ∀ x : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc),
    α x = 1 ↔ (x : G) ∈ Subgroup.centralizer (VZ T M : Set G)
  equiv : ∀ (a : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)) (v : IntMod (VZ T M) cx.c.hyp.elemAbelian),
    Multiplicative.toAdd (ψ (convI cx.c.hyp.elemAbelian ⟨a, YU_le_normalizer cx a.2⟩ v)) =
      omSmul (α a) (Multiplicative.toAdd (ψ v))
  polar : ∀ x y : IntMod (VZ T M) cx.c.hyp.elemAbelian, quadPolar (qW cx) x y =
    polarDet (Multiplicative.toAdd (ψ x)) (Multiplicative.toAdd (ψ y))
  det : ∀ x : IntMod (VZ T M) cx.c.hyp.elemAbelian, qW cx x = (Multiplicative.toAdd (ψ x)).det

theorem nonempty_setup (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    Nonempty (Setup54 cx) := by
  obtain ⟨ψ, α, h1, h2, h3, h4, h5⟩ := exists_action_model cx.c.hyp.elemAbelian cx.c.hyp.card_VZ
    (YU_le_normalizer cx) (q := qW cx) (qW_spec cx).1 (qW_spec cx).2.1 (qW_spec cx).2.2.1
    (mem_autI_YU_iff cx c)
  exact ⟨⟨ψ, α, h1, h2, h3, h4, h5⟩⟩

@[expose] noncomputable def actYU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc) →* MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) :=
  (convI cx.c.hyp.elemAbelian).comp (Subgroup.inclusion (YU_le_normalizer cx))

theorem actYU_apply (cx : Ctx15350 T Mc M V₁ V₂ t) (a : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)) :
    actYU cx a = convI cx.c.hyp.elemAbelian ⟨a, YU_le_normalizer cx a.2⟩ := rfl

theorem actYU_eq_one_iff {cx : Ctx15350 T Mc M V₁ V₂ t} (S : Setup54 cx)
    (x : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)) : actYU cx x = 1 ↔ S.α x = 1 := by
  rw [S.ker, actYU_apply]
  exact convI_eq_one_iff _ _

theorem alpha_eq_iff {cx : Ctx15350 T Mc M V₁ V₂ t} (S : Setup54 cx)
    (a b : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)) : S.α a = S.α b ↔ actYU cx a = actYU cx b := by
  have h1 : S.α a = S.α b ↔ S.α (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
  have h2 : actYU cx a = actYU cx b ↔ actYU cx (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
  rw [h1, h2, actYU_eq_one_iff S]

theorem omG_pow_six : ∀ x : OmG, x ^ 6 = 1 := by decide +kernel

theorem alpha_cube_Y (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (S : Setup54 cx)
    {y : G} (hy : y ∈ Y153 Mc M) : (S.α ⟨y, Subgroup.mem_sup_left hy⟩) ^ 3 = 1 := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hV := cx.c.hyp.elemAbelian
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 9 := by
    rw [hYbar]
    exact hS.card_oTwoUpper cx.c.hyp.isSylowTwoOf_autI
  have hmem : actYU cx ⟨y, Subgroup.mem_sup_left hy⟩ ∈ autI hV (Y153 Mc M) :=
    convI_mem_autI hV hy (YU_le_normalizer cx (Subgroup.mem_sup_left hy))
  have h9 : (actYU cx ⟨y, Subgroup.mem_sup_left hy⟩) ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥(autI hV (Y153 Mc M))) (x := ⟨_, hmem⟩)
    rw [hY9] at this
    exact congrArg Subtype.val this
  have h9' : (S.α ⟨y, Subgroup.mem_sup_left hy⟩) ^ 9 = 1 := by
    have : S.α (⟨y, Subgroup.mem_sup_left hy⟩ ^ 9) = S.α 1 :=
      (alpha_eq_iff S _ _).2 (by rw [map_pow, h9, map_one])
    rwa [map_pow, map_one] at this
  have h := pow_gcd_eq_one.2 ⟨h9', omG_pow_six (S.α ⟨y, Subgroup.mem_sup_left hy⟩)⟩
  simpa using h

theorem alpha_sq_U (cx : Ctx15350 T Mc M V₁ V₂ t) (S : Setup54 cx) {u : G}
    (hu : u ∈ UH153 T M V₁ Mc) : (S.α ⟨u, Subgroup.mem_sup_right hu⟩) ^ 2 = 1 := by
  have h : S.α (⟨u, Subgroup.mem_sup_right hu⟩ ^ 2) = 1 := by
    rw [S.ker]
    show u ^ 2 ∈ Subgroup.centralizer (VZ T M : Set G)
    rw [pow_two]
    exact Z_le_centralizer cx (sq_U_mem cx hu)
  rwa [map_pow] at h

theorem exists_Y_of_cube (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (S : Setup54 cx)
    {l : OmG} (hl : l ^ 3 = 1) : ∃ (y : G) (hy : y ∈ Y153 Mc M), S.α ⟨y, Subgroup.mem_sup_left hy⟩ = l := by
  obtain ⟨x, rfl⟩ := S.surj l
  have hV := cx.c.hyp.elemAbelian
  have h3 : (actYU cx x) ^ 3 = 1 := by
    have : actYU cx (x ^ 3) = actYU cx 1 :=
      (alpha_eq_iff S _ _).1 (by rw [map_pow, hl, map_one])
    rwa [map_pow, map_one] at this
  have hodd : Odd (orderOf (actYU cx x)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
  have hYU_M : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ M :=
    sup_le (Y153_le Mc M) ((U_le_T cx).trans (T_le_M cx))
  have hxM : actYU cx x ∈ autI hV M :=
    autI_mono hV hYU_M (convI_mem_autI hV x.2 (YU_le_normalizer cx x.2))
  have hmem : actYU cx x ∈ oTwoUpper (autI hV M) := mem_oTwoUpper_of_odd hxM hodd
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  rw [← hYbar] at hmem
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hmem
  refine ⟨g, hgY, ?_⟩
  refine (alpha_eq_iff S _ x).2 ?_
  rw [actYU_apply]
  exact hg

theorem YU_coe_eq_mul (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ((Y153 Mc M ⊔ UH153 T M V₁ Mc : Subgroup G) : Set G) =
      (Y153 Mc M : Set G) * (UH153 T M V₁ Mc : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (((U_le_T cx).trans (T_le_M cx)).trans (le_normalizer_Y153 Mc M))

theorem mem_T_of_alpha_eq_one (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (S : Setup54 cx) {x : G} (hx : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (h1 : S.α ⟨x, hx⟩ = 1) : x ∈ T := by
  have hx' : x ∈ ((Y153 Mc M ⊔ UH153 T M V₁ Mc : Subgroup G) : Set G) := hx
  rw [YU_coe_eq_mul cx] at hx'
  obtain ⟨y, hy, u, hu, rfl⟩ := hx'
  have hprod : (⟨y * u, hx⟩ : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)) =
      ⟨y, Subgroup.mem_sup_left hy⟩ * ⟨u, Subgroup.mem_sup_right hu⟩ := rfl
  rw [hprod, map_mul] at h1
  have h3 := alpha_cube_Y h113 cx S hy
  have h2 := alpha_sq_U cx S hu
  have heq : S.α ⟨y, Subgroup.mem_sup_left hy⟩ = (S.α ⟨u, Subgroup.mem_sup_right hu⟩)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  have h2' : (S.α ⟨y, Subgroup.mem_sup_left hy⟩) ^ 2 = 1 := by
    rw [heq, inv_pow, h2, inv_one]
  have hα1 : S.α ⟨y, Subgroup.mem_sup_left hy⟩ = 1 := by
    calc S.α ⟨y, Subgroup.mem_sup_left hy⟩
        = (S.α ⟨y, Subgroup.mem_sup_left hy⟩) ^ 3 * ((S.α ⟨y, Subgroup.mem_sup_left hy⟩) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [h3, h2']; simp
  have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (S.ker _).1 hα1
  have hyO : y ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [cx.r49.case_one.1]
    exact ⟨hy, hyC⟩
  exact T.mul_mem (pCoreOf_Y_le_T cx hyO) (U_le_T cx hu)

theorem exists_Z_gen (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z := by
  have h := cx.hF.card_V₁
  rw [Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))] at h
  obtain ⟨y, hy, huniq⟩ := h
  refine ⟨y, y.2, fun h1 => hy (Subtype.ext h1), fun w hw => ?_⟩
  by_cases h1 : w = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨w, hw⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem U_centralizes_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {u z : G} (hu : u ∈ UH153 T M V₁ Mc)
    (hz : z ∈ quasithinOmegaOneCenter T) : u * z * u⁻¹ = z := by
  have hT : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two cx.hF.card_V₁]
    exact cx.hF.T_normalizes_V₁
  have := Subgroup.mem_centralizer_iff.mp (hT (U_le_T cx hu)) z hz
  calc u * z * u⁻¹ = (z * u) * u⁻¹ := by rw [this]
    _ = z := by group

theorem Z_singular (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (S : Setup54 cx) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) :
    (Multiplicative.toAdd (S.ψ (IntMod.mk cx.c.hyp.elemAbelian ⟨z, cx.c.hyp.Z_le_VZ hz⟩))).det = 0 := by
  have hV := cx.c.hyp.elemAbelian
  set zV : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, cx.c.hyp.Z_le_VZ hz⟩ with hzV
  have hdec : ∀ y : OmG, ∃ l υ : OmG, l ^ 3 = 1 ∧
      (∃ (u : G) (hu : u ∈ UH153 T M V₁ Mc), S.α ⟨u, Subgroup.mem_sup_right hu⟩ = υ) ∧
      y = l * υ := by
    intro y
    obtain ⟨x, rfl⟩ := S.surj y
    have hx' : (x : G) ∈ ((Y153 Mc M ⊔ UH153 T M V₁ Mc : Subgroup G) : Set G) := x.2
    rw [YU_coe_eq_mul cx] at hx'
    obtain ⟨y', hy', u, hu, hxe⟩ := hx'
    refine ⟨S.α ⟨y', Subgroup.mem_sup_left hy'⟩, S.α ⟨u, Subgroup.mem_sup_right hu⟩,
      alpha_cube_Y h113 cx S hy', ⟨u, hu, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hxe.symm
  have hfix : ∀ υ : OmG, (∃ (u : G) (hu : u ∈ UH153 T M V₁ Mc),
      S.α ⟨u, Subgroup.mem_sup_right hu⟩ = υ) →
      omSmul υ (Multiplicative.toAdd (S.ψ zV)) = Multiplicative.toAdd (S.ψ zV) := by
    rintro υ ⟨u, hu, rfl⟩
    rw [← S.equiv ⟨u, Subgroup.mem_sup_right hu⟩ zV]
    have : convI hV ⟨(⟨u, Subgroup.mem_sup_right hu⟩ : ↥(Y153 Mc M ⊔ UH153 T M V₁ Mc)),
        YU_le_normalizer cx (Subgroup.mem_sup_right hu)⟩ zV = zV :=
      IntMod.val_injective (by
        rw [convI_apply_val]
        exact U_centralizes_Z cx hu hz)
    rw [this]
  exact det_eq_zero_of_decomp hdec hfix

theorem conjClosure_Z_Y (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) :
    conjClosure (quasithinOmegaOneCenter T) (Y153 Mc M) = VZ T M := by
  obtain ⟨S⟩ := nonempty_setup cx c
  obtain ⟨z, hz, hz1, -⟩ := exists_Z_gen cx
  have hV := cx.c.hyp.elemAbelian
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans cx.c.hyp.le_normalizer
  apply le_antisymm
  · refine conjClosure_le fun y hy w hw => ?_
    exact (Subgroup.mem_normalizer_iff.1 (hYN hy) w).1 (cx.c.hyp.Z_le_VZ hw)
  · intro v hv
    set zV : IntMod (VZ T M) hV := IntMod.mk hV ⟨z, cx.c.hyp.Z_le_VZ hz⟩ with hzV
    have hzV1 : zV ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have hX₀ : Multiplicative.toAdd (S.ψ zV) ≠ 0 := fun h =>
      hzV1 (S.ψ.injective (by rw [map_one]; exact toAdd_eq_zero.1 h))
    have hdet := Z_singular h113 cx S hz
    obtain ⟨l₁, l₂, h₁, h₂, hvv⟩ := orbit_span_mt _ hX₀ hdet
      (Multiplicative.toAdd (S.ψ (IntMod.mk hV ⟨v, hv⟩)))
    obtain ⟨y₁, hy₁, e₁⟩ := exists_Y_of_cube h113 cx S h₁
    obtain ⟨y₂, hy₂, e₂⟩ := exists_Y_of_cube h113 cx S h₂
    have k₁ := S.equiv ⟨y₁, Subgroup.mem_sup_left hy₁⟩ zV
    have k₂ := S.equiv ⟨y₂, Subgroup.mem_sup_left hy₂⟩ zV
    rw [e₁] at k₁
    rw [e₂] at k₂
    dsimp only at k₁ k₂
    have hmul : IntMod.mk hV ⟨v, hv⟩ =
        convI hV ⟨y₁, YU_le_normalizer cx (Subgroup.mem_sup_left hy₁)⟩ zV *
          convI hV ⟨y₂, YU_le_normalizer cx (Subgroup.mem_sup_left hy₂)⟩ zV := by
      apply S.ψ.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, toAdd_mul, k₁, k₂]
      exact hvv
    have hval := congrArg IntMod.val hmul
    rw [IntMod.val_mul, convI_apply_val, convI_apply_val] at hval
    have hv' : v = y₁ * z * y₁⁻¹ * (y₂ * z * y₂⁻¹) := hval
    rw [hv']
    exact (conjClosure (quasithinOmegaOneCenter T) (Y153 Mc M)).mul_mem
      (mem_conjClosure hy₁ hz) (mem_conjClosure hy₂ hz)

end Setup

end S153E54

end CFSG.Quasithin
