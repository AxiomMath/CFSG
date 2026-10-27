module

public import CFSG.Quasithin.MS93.S37ALR

public section

namespace CFSG.Quasithin.MS93.S37R

section Schur

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open scoped Matrix

variable {F : Type} [Field F]

theorem exists_form_eq_one {e : V4 F} (he : e ≠ 0) : ∃ w, form F e w = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ w, form F e w = 0 := fun w => by
    by_contra hw
    apply h ((form F e w)⁻¹ • w)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]
  exact he (form_nondegenerate.1 e h0)

theorem exists_line_scalar {f : V4 F →+ V4 F}
    (hf : ∀ (g : Sp4 F) v, f (mat g *ᵥ v) = mat g *ᵥ f v) {e : V4 F} (he : e ≠ 0) :
    ∃ c : F, ∀ l : F, f (l • e) = (l * c) • e := by
  obtain ⟨w, hw⟩ := exists_form_eq_one he
  refine ⟨form F e (f w), fun l => ?_⟩
  have h := hf (transv e l) w
  rw [transv_mulVec, transv_mulVec, map_add, hw, mul_one] at h
  exact add_left_cancel h

theorem eq_smul_of_comm_sp4 {f : V4 F →+ V4 F}
    (hf : ∀ (g : Sp4 F) v, f (mat g *ᵥ v) = mat g *ᵥ f v) : ∃ c : F, ∀ v, f v = c • v := by
  have he₀ : (e₁ F) ≠ 0 := fun h => by
    have := congrFun h (.inl 0)
    simp [e₁] at this
  obtain ⟨c, hc⟩ := exists_line_scalar hf he₀
  refine ⟨c, fun v => ?_⟩
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, smul_zero]
  obtain ⟨cv, hcv⟩ := exists_line_scalar hf hv0
  have hfv : f v = cv • v := by simpa using hcv 1
  by_cases hdep : ∃ μ : F, v = μ • e₁ F
  · obtain ⟨μ, rfl⟩ := hdep
    rw [hc μ, smul_smul, mul_comm]
  · push Not at hdep
    have hs0 : e₁ F + v ≠ 0 := fun h => hdep (-1) (by
      rw [neg_one_smul]
      exact (neg_eq_of_add_eq_zero_right h).symm)
    obtain ⟨cs, hcs⟩ := exists_line_scalar hf hs0
    have h1 : f (e₁ F + v) = cs • (e₁ F + v) := by simpa using hcs 1
    rw [map_add, hfv, show f (e₁ F) = c • e₁ F by simpa using hc 1] at h1
    have h2 : (cs - c) • e₁ F + (cs - cv) • v = 0 := by
      calc (cs - c) • e₁ F + (cs - cv) • v = (cs • e₁ F + cs • v) - (c • e₁ F + cv • v) := by
            rw [sub_smul, sub_smul]; abel
        _ = 0 := by rw [h1, smul_add, sub_self]
    by_cases hne : cs - cv = 0
    · rw [hne, zero_smul, add_zero] at h2
      have hcs' : cs = c := by
        rcases smul_eq_zero.1 h2 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h he₀
      rw [hfv, ← sub_eq_zero.1 hne, hcs']
    · exfalso
      apply hdep (-(cs - c) / (cs - cv))
      have : (cs - cv) • v = -((cs - c) • e₁ F) := eq_neg_of_add_eq_zero_right h2
      calc v = (cs - cv)⁻¹ • ((cs - cv) • v) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = (-(cs - c) / (cs - cv)) • e₁ F := by
          rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul, neg_mul_eq_mul_neg]

@[expose] def rescale (c : F) : Multiplicative (V4 F × F) →* Multiplicative (V4 F × F) where
  toFun w :=
    Multiplicative.ofAdd (c • (Multiplicative.toAdd w).1, c ^ 2 * (Multiplicative.toAdd w).2)
  map_one' := by simp
  map_mul' w w' := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, smul_add, mul_add,
      Prod.mk_add_mk]

theorem rescale_toAdd (c : F) (w : Multiplicative (V4 F × F)) :
    Multiplicative.toAdd (rescale c w) =
      (c • (Multiplicative.toAdd w).1, c ^ 2 * (Multiplicative.toAdd w).2) := rfl

theorem rescale_rescale (c c' : F) (w : Multiplicative (V4 F × F)) :
    rescale c (rescale c' w) = rescale (c * c') w := by
  apply Multiplicative.toAdd.injective
  simp only [rescale_toAdd, smul_smul, mul_pow]
  refine Prod.ext rfl ?_
  simp only
  ring

theorem rescale_one (w : Multiplicative (V4 F × F)) : rescale 1 w = w := by
  apply Multiplicative.toAdd.injective
  simp [rescale_toAdd]

theorem omega5Act_rescale (g : Sp4 F) (c : F) (w : Multiplicative (V4 F × F)) :
    omega5Act F g (rescale c w) = rescale c (omega5Act F g w) := by
  apply Multiplicative.toAdd.injective
  simp only [omega5Act, toAdd_ofAdd, rescale_toAdd, Matrix.mulVec_smul]
  refine Prod.ext rfl ?_
  simp only [sp4Quad, Pi.smul_apply, smul_eq_mul]
  ring

end Schur

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2 CFSG.Quasithin.H13.VolI
open CFSG.Quasithin.MS93.S37
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix IsMulCommutative

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  (C : Cfg M T L F)
include C

theorem exists_cover₀ : ∃ Ψ : Multiplicative (V4 F × F) →* G,
    (∀ w, Ψ w ∈ Uq M T L) ∧ (∀ u ∈ Uq M T L, ∃ w, Ψ w = u) ∧
    (∀ w, Ψ w = 1 → (Multiplicative.toAdd w).1 = 0) ∧
    ∀ (l : G) (hl : l ∈ L) w, Ψ (omega5Act F (C.α ⟨l, hl⟩) w) = l * Ψ w * l⁻¹ := by
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
  obtain ⟨Cv, hρ, -⟩ := modelCover_of_realizesVia hCL hcommL hreal5
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
  obtain ⟨ψ, hψs, hψk, hψe, -⟩ :=
    MS93.ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl) hkfix hgenE hE2 hbound hV Cv
  let Ψ : Multiplicative (V4 F × F) →* G :=
    { toFun := fun x => ((ψ ⟨x, Subgroup.mem_top _⟩ : ↥(Uq M T L)) : G)
      map_one' := by
        show ((ψ 1 : ↥(Uq M T L)) : G) = 1
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        show ((ψ (⟨x, Subgroup.mem_top _⟩ * ⟨y, Subgroup.mem_top _⟩) : ↥(Uq M T L)) : G) = _
        rw [map_mul]
        rfl }
  refine ⟨Ψ, fun w => (ψ ⟨w, Subgroup.mem_top _⟩).2, fun u hu => ?_, fun w hw => ?_,
    fun l hl w => ?_⟩
  · obtain ⟨m, hm⟩ := hψs ⟨u, hu⟩
    refine ⟨m.1, ?_⟩
    show ((ψ ⟨m.1, Subgroup.mem_top _⟩ : ↥(Uq M T L)) : G) = u
    rw [show (⟨m.1, Subgroup.mem_top _⟩ : ↥(FFModel.omega5 F (omega5Rad F)).sec) = m from rfl, hm]
  · have h1 : ψ ⟨w, Subgroup.mem_top _⟩ = 1 := Subtype.ext hw
    exact hψk _ h1
  · set g := C.α ⟨l, hl⟩ with hg
    set y : ↥(FFModel.omega5 F (omega5Rad F)).sec := ⟨w, Subgroup.mem_top _⟩ with hy
    have e1 : (⟨omega5Act F g w, Subgroup.mem_top _⟩ : ↥(FFModel.omega5 F (omega5Rad F)).sec) =
        secAut hD g y := rfl
    have h2 := hψe g y
    have hπl : ((π g : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
        conjAct (Uq M T L) ⟨l, hLU hl⟩ := hπa ⟨l, hl⟩
    show ((ψ ⟨omega5Act F g w, Subgroup.mem_top _⟩ : ↥(Uq M T L)) : G) = l * (ψ y : G) * l⁻¹
    rw [e1, h2, hρ g]
    show ((((π g : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) (ψ y)) : G) = _
    rw [hπl]
    exact InternalSec.coe_conjAct_apply _ _

theorem exists_cover : ∃ Ψ : Multiplicative (V4 F × F) →* G,
    (∀ w, Ψ w ∈ Uq M T L) ∧ (∀ u ∈ Uq M T L, ∃ w, Ψ w = u) ∧
    (∀ w, Ψ w = 1 → (Multiplicative.toAdd w).1 = 0) ∧
    (∀ (l : G) (hl : l ∈ L) w, Ψ (omega5Act F (C.α ⟨l, hl⟩) w) = l * Ψ w * l⁻¹) ∧
    ∀ w (hw : Ψ w ∈ Uq M T L), C.N.co ⟨Ψ w, hw⟩ = (Multiplicative.toAdd w).1 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨Ψ₀, hU, hs, hk, he⟩ := exists_cover₀ C
  have hrad : ∀ s : F, C.N.co ⟨Ψ₀ (Multiplicative.ofAdd (0, s)), hU _⟩ = 0 := fun s => by
    rw [C.N.co_eq_zero_iff]
    refine ⟨hU _, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have h := he l hl (Multiplicative.ofAdd (0, s))
    rw [omega5Act_rad _ (show Multiplicative.ofAdd ((0 : V4 F), s) ∈ omega5Rad F from rfl)] at h
    calc l * Ψ₀ (Multiplicative.ofAdd (0, s)) = l * Ψ₀ (Multiplicative.ofAdd (0, s)) * l⁻¹ * l :=
          by group
      _ = Ψ₀ (Multiplicative.ofAdd (0, s)) * l := by rw [← h]
  have hsplit : ∀ w : Multiplicative (V4 F × F), w = Multiplicative.ofAdd
      ((Multiplicative.toAdd w).1, 0) * Multiplicative.ofAdd (0, (Multiplicative.toAdd w).2) :=
    fun w => by
      apply Multiplicative.toAdd.injective
      simp
  have hco : ∀ w, C.N.co ⟨Ψ₀ w, hU w⟩ =
      C.N.co ⟨Ψ₀ (Multiplicative.ofAdd ((Multiplicative.toAdd w).1, 0)), hU _⟩ := fun w => by
    conv_lhs => rw [show (⟨Ψ₀ w, hU w⟩ : ↥(Uq M T L)) =
      ⟨Ψ₀ (Multiplicative.ofAdd ((Multiplicative.toAdd w).1, 0)), hU _⟩ *
        ⟨Ψ₀ (Multiplicative.ofAdd (0, (Multiplicative.toAdd w).2)), hU _⟩ from
        Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, ← hsplit])]
    rw [C.N.co_mul, hrad, add_zero]
  let f : V4 F →+ V4 F :=
    { toFun := fun v => C.N.co ⟨Ψ₀ (Multiplicative.ofAdd (v, 0)), hU _⟩
      map_zero' := by
        show C.N.co ⟨Ψ₀ 1, hU _⟩ = 0
        rw [show (⟨Ψ₀ 1, hU _⟩ : ↥(Uq M T L)) = 1 from Subtype.ext (map_one Ψ₀)]
        exact C.N.co_one
      map_add' := fun v v' => by
        show C.N.co ⟨Ψ₀ (Multiplicative.ofAdd (v + v', 0)), hU _⟩ = _
        rw [show (⟨Ψ₀ (Multiplicative.ofAdd (v + v', 0)), hU _⟩ : ↥(Uq M T L)) =
          ⟨Ψ₀ (Multiplicative.ofAdd (v, 0)), hU _⟩ * ⟨Ψ₀ (Multiplicative.ofAdd (v', 0)), hU _⟩ from
          Subtype.ext (by
            rw [Subgroup.coe_mul, ← map_mul]
            show Ψ₀ _ = Ψ₀ _
            congr 1
            apply Multiplicative.toAdd.injective
            simp)]
        exact C.N.co_mul _ _ }
  have hf : ∀ (g : Sp4 F) v, f (mat g *ᵥ v) = mat g *ᵥ f v := fun g v => by
    obtain ⟨⟨l, hl⟩, rfl⟩ := C.hα g
    have hc : l * Ψ₀ (Multiplicative.ofAdd (v, 0)) * l⁻¹ ∈ Uq M T L := by
      rw [← he l hl]; exact hU _
    have h2 : C.N.co ⟨Ψ₀ (omega5Act F (C.α ⟨l, hl⟩) (Multiplicative.ofAdd (v, 0))), hU _⟩ =
        C.N.co ⟨Ψ₀ (Multiplicative.ofAdd (mat (C.α ⟨l, hl⟩) *ᵥ v, 0)), hU _⟩ := hco _
    show C.N.co ⟨Ψ₀ (Multiplicative.ofAdd (mat (C.α ⟨l, hl⟩) *ᵥ v, 0)), hU _⟩ = _
    rw [← h2, show (⟨Ψ₀ (omega5Act F (C.α ⟨l, hl⟩) (Multiplicative.ofAdd (v, 0))), hU _⟩ :
        ↥(Uq M T L)) = ⟨l * Ψ₀ (Multiplicative.ofAdd (v, 0)) * l⁻¹, hc⟩ from
      Subtype.ext (he l hl _)]
    exact C.co_conj_L hl (hU _) hc
  obtain ⟨c, hcf⟩ := eq_smul_of_comm_sp4 hf
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu⟩ := C.N.co_surj (e₁ F)
    obtain ⟨w, hw⟩ := hs u u.2
    have h1 : C.N.co ⟨Ψ₀ w, hU w⟩ = 0 := by
      rw [hco]
      exact (hcf _).trans (zero_smul _ _)
    have e : (⟨Ψ₀ w, hU w⟩ : ↥(Uq M T L)) = u := Subtype.ext hw
    rw [e, hu] at h1
    have := congrFun h1 (.inl 0)
    simp [e₁] at this
  refine ⟨Ψ₀.comp (rescale c⁻¹), fun w => hU _, fun u hu => ?_, fun w hw => ?_, fun l hl w => ?_,
    fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := hs u hu
    refine ⟨rescale c w, ?_⟩
    rw [MonoidHom.comp_apply, rescale_rescale, inv_mul_cancel₀ hc0, rescale_one, hw]
  · have h := hk _ hw
    rw [rescale_toAdd] at h
    exact (smul_eq_zero.1 h).resolve_left (inv_ne_zero hc0)
  · rw [MonoidHom.comp_apply, ← omega5Act_rescale, he, MonoidHom.comp_apply]
  · rw [show (⟨(Ψ₀.comp (rescale c⁻¹)) w, hw⟩ : ↥(Uq M T L)) = ⟨Ψ₀ (rescale c⁻¹ w), hU _⟩ from
      rfl, hco, rescale_toAdd]
    show f (c⁻¹ • (Multiplicative.toAdd w).1) = _
    rw [hcf, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end CFSG.Quasithin.MS93.S37R
