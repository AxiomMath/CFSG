module

public import CFSG.Quasithin.MS93.S37ALR
public import CFSG.Quasithin.MS93.S37Res

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2 CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix IsMulCommutative

section Sp

variable {F : Type} [Field F] [CharP F 2]

noncomputable abbrev dQ (g : Sp4 F) : F :=
  mat g (.inl 0) (.inr 0) * mat g (.inl 1) (.inr 1) + mat g (.inl 0) (.inr 1) ^ 2

noncomputable abbrev hQ (g₀ g : Sp4 F) (w : Fin 2 → F) : F :=
  mat g₀ (.inl 1) (.inr 1) * (mat g (.inl 0) (.inr 0) * w 0 + mat g (.inl 0) (.inr 1) * w 1) ^ 2 +
    mat g₀ (.inl 0) (.inr 0) * (mat g (.inl 0) (.inr 1) * w 0 + mat g (.inl 1) (.inr 1) * w 1) ^ 2 +
    dQ g₀ * (mat g (.inl 0) (.inr 0) * w 0 ^ 2 + mat g (.inl 1) (.inr 1) * w 1 ^ 2)

noncomputable abbrev fv (w : Fin 2 → F) : V4 F := Sum.elim 0 w

theorem omega5_comm_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (w : Fin 2 → F) :
    omega5Act F g (Multiplicative.ofAdd (fv w, 0)) * (Multiplicative.ofAdd (fv w, (0 : F)))⁻¹ =
      Multiplicative.ofAdd (Sum.elim
        ![mat g (.inl 0) (.inr 0) * w 0 + mat g (.inl 0) (.inr 1) * w 1,
          mat g (.inl 0) (.inr 1) * w 0 + mat g (.inl 1) (.inr 1) * w 1] 0,
        mat g (.inl 0) (.inr 0) * w 0 ^ 2 + mat g (.inl 1) (.inr 1) * w 1 ^ 2) := by
  rw [omega5_comm]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hm : spMat g *ᵥ fv w = fv w + (mat g (.inl 0) (.inr 0) * w 0 +
      mat g (.inl 0) (.inr 1) * w 1) • e₁ F + (mat g (.inl 0) (.inr 1) * w 0 +
      mat g (.inl 1) (.inr 1) * w 1) • e₂ F := by
    show mat g *ᵥ fv w = _
    rw [mulVec_of_mem_Q₁ hg]
    simp [fv]
  rw [hm]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    rcases i with i | i <;> fin_cases i <;> simp [fv, e₁, e₂]
  · simp only [sp4Quad, fv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e₁, e₂]
    simp
    linear_combination mat g (.inl 0) (.inr 1) * w 0 * w 1 * h2

theorem omega5_comm_mul_comm {g₀ g : Sp4 F} (hg₀ : g₀ ∈ Q₁ F) (hg : g ∈ Q₁ F)
    (w : Fin 2 → F) (t : F) :
    ∃ u : Fin 2 → F,
      (omega5Act F g₀ (Multiplicative.ofAdd (fv u, 0)) * (Multiplicative.ofAdd (fv u, (0 : F)))⁻¹) *
        (omega5Act F g (Multiplicative.ofAdd (fv ((dQ g₀ * t) • w), 0)) *
          (Multiplicative.ofAdd (fv ((dQ g₀ * t) • w), (0 : F)))⁻¹) =
      Multiplicative.ofAdd ((0 : V4 F), dQ g₀ * t ^ 2 * hQ g₀ g w) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  refine ⟨![mat g₀ (.inl 1) (.inr 1) * (t * (mat g (.inl 0) (.inr 0) * w 0 +
      mat g (.inl 0) (.inr 1) * w 1)) + mat g₀ (.inl 0) (.inr 1) * (t * (mat g (.inl 0) (.inr 1) *
      w 0 + mat g (.inl 1) (.inr 1) * w 1)), mat g₀ (.inl 0) (.inr 1) * (t * (mat g (.inl 0)
      (.inr 0) * w 0 + mat g (.inl 0) (.inr 1) * w 1)) + mat g₀ (.inl 0) (.inr 0) * (t *
      (mat g (.inl 0) (.inr 1) * w 0 + mat g (.inl 1) (.inr 1) * w 1))], ?_⟩
  rw [omega5_comm_Q₁ hg₀, omega5_comm_Q₁ hg]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd]
  refine Prod.ext ?_ ?_
  · funext i
    rcases i with i | i <;> fin_cases i <;> simp [dQ, Pi.smul_apply, smul_eq_mul] <;> ring_nf <;>
      simp [h2]
  · simp [dQ, hQ, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp [h2, h4]

omit [CharP F 2] in
theorem exists_dQ_ne_zero [Finite F] {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F < Nat.card E) : ∃ g ∈ E, dQ g ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine absurd hc (not_lt.2 ?_)
  have hb : ∀ x ∈ E, mat x (.inl 0) (.inr 0) = 0 → mat x (.inl 0) (.inr 1) = 0 := by
    intro x hx ha
    have h := hcon x hx
    simp only [dQ, ha, zero_mul, zero_add] at h
    exact (pow_eq_zero_iff two_ne_zero).1 h
  by_cases hA : ∀ g ∈ E, mat g (.inl 0) (.inr 0) = 0
  · refine Nat.card_le_card_of_injective (fun g : E => mat (g : Sp4 F) (.inl 1) (.inr 1)) ?_
    intro g g' hgg'
    exact Subtype.ext (eq_of_mem_Q₁ (hE g.2) (hE g'.2) (by rw [hA _ g.2, hA _ g'.2])
      (by rw [hb _ g.2 (hA _ g.2), hb _ g'.2 (hA _ g'.2)]) hgg')
  · push Not at hA
    obtain ⟨g₁, hg₁, ha₁⟩ := hA
    refine Nat.card_le_card_of_injective (fun g : E => mat (g : Sp4 F) (.inl 0) (.inr 0)) ?_
    intro g g' hgg'
    have hgg'' : mat (g : Sp4 F) (.inl 0) (.inr 0) = mat (g' : Sp4 F) (.inl 0) (.inr 0) := hgg'
    set k : Sp4 F := (g : Sp4 F)⁻¹ * (g' : Sp4 F) with hk
    have hkE : k ∈ E := E.mul_mem (E.inv_mem g.2) g'.2
    have hkQ := hE hkE
    have ha : mat k (.inl 0) (.inr 0) = 0 := by
      rw [hk, entry_mul_of_mem_Q₁ ((Q₁ F).inv_mem (hE g.2)) (hE g'.2), entry_inv_of_mem_Q₁ (hE g.2),
        hgg'']
      ring
    have hb' := hb _ hkE ha
    have hd : mat k (.inl 1) (.inr 1) = 0 := by
      have h := hcon (g₁ * k) (E.mul_mem hg₁ hkE)
      have h1 := hcon g₁ hg₁
      simp only [dQ, entry_mul_of_mem_Q₁ (hE hg₁) hkQ, ha, hb', add_zero] at h h1
      have h3 : mat g₁ (.inl 0) (.inr 0) * mat k (.inl 1) (.inr 1) = 0 := by
        linear_combination h - h1
      exact (mul_eq_zero.1 h3).resolve_left ha₁
    have h1 : k = 1 :=
      eq_of_mem_Q₁ hkQ (Q₁ F).one_mem (by rw [ha, entry_one]) (by rw [hb', entry_one])
        (by rw [hd, entry_one])
    exact Subtype.ext (inv_mul_eq_one.1 h1)

theorem card_le_of_hQ_eq_zero [Finite F] {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F) {g₀ : Sp4 F}
    (hδ : dQ g₀ ≠ 0) (h1 : ∀ g ∈ E, hQ g₀ g ![1, 0] = 0) (h2 : ∀ g ∈ E, hQ g₀ g ![0, 1] = 0) :
    Nat.card E ≤ 4 * Nat.card F := by
  classical
  have e2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let f : ↥E →* Multiplicative F :=
    { toFun := fun g => Multiplicative.ofAdd (mat (g : Sp4 F) (.inl 0) (.inr 1))
      map_one' := by
        show Multiplicative.ofAdd (mat (1 : Sp4 F) (.inl 0) (.inr 1)) = 1
        rw [entry_one]
        rfl
      map_mul' := fun g g' => by
        show Multiplicative.ofAdd (mat ((g : Sp4 F) * (g' : Sp4 F)) (.inl 0) (.inr 1)) = _
        rw [entry_mul_of_mem_Q₁ (hE g.2) (hE g'.2)]
        rfl }
  have hcard := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card f.range ≤ Nat.card F :=
    (Subgroup.card_le_card_group _).trans (by rw [Nat.card_congr Multiplicative.toAdd])
  set δ := dQ g₀ with hδdef
  set S : Finset (F × F) := ({0, δ / mat g₀ (.inl 1) (.inr 1)} : Finset F) ×ˢ
    ({0, δ / mat g₀ (.inl 0) (.inr 0)} : Finset F) with hS
  have hroot : ∀ c x : F, c * x ^ 2 + δ * x = 0 → x ∈ ({0, δ / c} : Finset F) := by
    intro c x hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have h3 : c * x + δ = 0 := by
        have : x * (c * x + δ) = 0 := by linear_combination hx
        exact (mul_eq_zero.1 this).resolve_left hx0
      have hc : c ≠ 0 := by
        rintro rfl
        exact hδ (by simpa using h3)
      field_simp
      linear_combination h3 - δ * e2
  have hker : Nat.card f.ker ≤ 4 := by
    have hinj : Function.Injective (fun g : ↥f.ker => (⟨(mat ((g : ↥E) : Sp4 F) (.inl 0) (.inr 0),
        mat ((g : ↥E) : Sp4 F) (.inl 1) (.inr 1)), by
          have hb : mat ((g : ↥E) : Sp4 F) (.inl 0) (.inr 1) = 0 := by
            have := g.2
            rw [MonoidHom.mem_ker] at this
            exact Multiplicative.ofAdd.injective this
          have hg1 := h1 _ (g : ↥E).2
          have hg2 := h2 _ (g : ↥E).2
          simp only [hQ, hb, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
            add_zero, zero_add, one_pow, zero_pow two_ne_zero] at hg1 hg2
          rw [Finset.mem_product]
          refine ⟨hroot _ _ ?_, hroot _ _ ?_⟩
          · linear_combination hg1
          · linear_combination hg2⟩ : ↥S)) := by
      intro g g' hgg'
      have hb : ∀ x : ↥f.ker, mat ((x : ↥E) : Sp4 F) (.inl 0) (.inr 1) = 0 := fun x => by
        have := x.2
        rw [MonoidHom.mem_ker] at this
        exact Multiplicative.ofAdd.injective this
      have e := congrArg Subtype.val hgg'
      simp only [Prod.mk.injEq] at e
      exact Subtype.ext (Subtype.ext (eq_of_mem_Q₁ (hE (g : ↥E).2) (hE (g' : ↥E).2) e.1
        (by rw [hb g, hb g']) e.2))
    have := Nat.card_le_card_of_injective _ hinj
    refine this.trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS, Finset.card_product]
    have hc2 : ∀ x y : F, ({x, y} : Finset F).card ≤ 2 := fun x y =>
      (Finset.card_insert_le _ _).trans (by simp)
    calc _ ≤ 2 * 2 := Nat.mul_le_mul (hc2 _ _) (hc2 _ _)
      _ = 4 := rfl
  rw [← hcard]
  calc Nat.card f.ker * Nat.card f.range ≤ 4 * Nat.card F := Nat.mul_le_mul hker hrange

theorem omega5_rad_mem_closure [Finite F] (hq : 8 ≤ Nat.card F) {E : Subgroup (Sp4 F)}
    (hE : E ≤ Q₁ F) (hcard : Nat.card E = Nat.card F ^ 2) (s : F) :
    Multiplicative.ofAdd ((0 : V4 F), s) ∈ Subgroup.closure
      {x | ∃ g ∈ E, ∃ z : Multiplicative (V4 F × F), x = omega5Act F g z * z⁻¹} := by
  have hq' : Nat.card F < Nat.card E := by
    rw [hcard]
    nlinarith
  obtain ⟨g₀, hg₀E, hδ⟩ := exists_dQ_ne_zero hE hq'
  obtain ⟨g, hgE, w, hw⟩ : ∃ g ∈ E, ∃ w : Fin 2 → F, hQ g₀ g w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := card_le_of_hQ_eq_zero hE hδ (fun g hg => hcon g hg _) (fun g hg => hcon g hg _)
    rw [hcard] at h
    nlinarith
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (s / (dQ g₀ * hQ g₀ g w))
  obtain ⟨u, hu⟩ := omega5_comm_mul_comm (hE hg₀E) (hE hgE) w r
  have hδH : dQ g₀ * hQ g₀ g w ≠ 0 := mul_ne_zero hδ hw
  have hs : s = dQ g₀ * r ^ 2 * hQ g₀ g w :=
    calc s = s / (dQ g₀ * hQ g₀ g w) * (dQ g₀ * hQ g₀ g w) := (div_mul_cancel₀ s hδH).symm
      _ = dQ g₀ * r ^ 2 * hQ g₀ g w := by rw [hr]; ring
  rw [hs, ← hu]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨g₀, hg₀E, _, rfl⟩)
    (Subgroup.subset_closure ⟨g, hgE, _, rfl⟩)

end Sp

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem A_le_closure_of (E : Subgroup (Sp4 F))
    (hR : ∀ s : F, Multiplicative.ofAdd ((0 : V4 F), s) ∈ Subgroup.closure
      {x | ∃ g ∈ E, ∃ z : Multiplicative (V4 F × F), x = omega5Act F g z * z⁻¹}) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.closure
      {x | ∃ (l : G) (hl : l ∈ L) (u : G), u ∈ Uq M T L ∧ C.α ⟨l, hl⟩ ∈ E ∧
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
  set S := {x | ∃ (l : G) (hl : l ∈ L) (u : G), u ∈ Uq M T L ∧ C.α ⟨l, hl⟩ ∈ E ∧
    x = l * u * l⁻¹ * u⁻¹} with hS
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
  have hcl : Subgroup.closure
      {x | ∃ g ∈ E, ∃ z : Multiplicative (V4 F × F), x = omega5Act F g z * z⁻¹} ≤
        (Subgroup.closure S).comap Ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, z, rfl⟩
    set y : ↥(FFModel.omega5 F (omega5Rad F)).sec := ⟨z, Subgroup.mem_top _⟩ with hy
    have e1 : (⟨omega5Act F g z * z⁻¹, Subgroup.mem_top _⟩ :
        ↥(FFModel.omega5 F (omega5Rad F)).sec) = secAut hD g y * y⁻¹ := rfl
    have h2 := hψe g y
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
    show ((ψ ⟨omega5Act F g z * z⁻¹, Subgroup.mem_top _⟩ : ↥(Uq M T L)) : G) ∈
      Subgroup.closure S
    rw [e1, map_mul, map_inv, h2, hρ g]
    refine Subgroup.subset_closure ⟨l, hlL, (ψ y : G), (ψ y).2, by rw [hlα]; exact hg, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hval]
  intro a ha
  obtain ⟨m, hm⟩ := hψs ⟨a, ha.1⟩
  have haZ : (⟨a, ha.1⟩ : ↥(Uq M T L)) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf
      (Uq M T L) := ha.2
  have hm0 : (Multiplicative.toAdd m.1).1 = 0 := by
    have h1 : Cv.β (ψ m) = 1 := by rw [hm]; exact (hβk _).2 haZ
    rw [hψβ] at h1
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hmE : m = ⟨Multiplicative.ofAdd ((0 : V4 F), (Multiplicative.toAdd m.1).2),
      Subgroup.mem_top _⟩ := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact Prod.ext hm0 rfl
  have hma : Ψ (Multiplicative.ofAdd ((0 : V4 F), (Multiplicative.toAdd m.1).2)) = a := by
    have e : ((ψ m : ↥(Uq M T L)) : G) = a := by rw [hm]
    rw [← e]
    exact congrArg (fun x => ((ψ x : ↥(Uq M T L)) : G)) hmE.symm
  rw [← hma]
  exact hcl (hR _)

theorem A_le_Rt_of (θ : MulAut ↥(T1 M T L))
    (hR : ∀ s : F, Multiplicative.ofAdd ((0 : V4 F), s) ∈ Subgroup.closure
      {x | ∃ g ∈ C.rhoIm (Ut M T L θ), ∃ z : Multiplicative (V4 F × F),
        x = omega5Act F g z * z⁻¹}) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Rt M T L θ := by
  refine (C.A_le_closure_of _ hR).trans (Subgroup.closure_le _ |>.2 ?_)
  rintro _ ⟨l, hl, u, hu, hlX, rfl⟩
  have hlK : l ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hl
  have hm : C.rho ⟨l, hlK⟩ ∈ C.rhoIm (Ut M T L θ) := by
    rw [C.rho_of_mem_L hl]
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

theorem card_rhoIm_Ut_of_caseII (θ : MulAut ↥(T1 M T L)) (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) :
    Nat.card ↥(C.rhoIm (Ut M T L θ)) = Nat.card F ^ 2 := by
  have hfix := (C.relIndex_inv_eq C.pCore_le_T1 T1_le_T θ hcrit (tImage_le θ _)
    (tImage_le θ⁻¹ _) (C.partner_relIndex_eq θ hcrit).le).2
  have hc2 : Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hII.1]
  have hV := C.card_V4_eq C.pCore_le_T1 T1_le_T θ⁻¹ (tImage_le θ⁻¹ _)
  rw [C.relIndex_Qt_eq C.pCore_le_T1 θ⁻¹, inv_inv, MSP.card_V4, hfix, hc2,
    ← C.card_rhoIm ((tImage_le θ _).trans T1_le_sup)] at hV
  have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
  have h4 : Nat.card F ^ 4 = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
  rw [h4] at hV
  exact (Nat.eq_of_mul_eq_mul_right hq hV).symm

theorem A_le_Rt_of_caseII (hT : C.T0bar = Q₁ F) (hq : 8 ≤ Nat.card F) (θ : MulAut ↥(T1 M T L))
    (hcrit : ¬ Uq M T L ≤ Qt M θ) (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Rt M T L θ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hEQ : C.rhoIm (Ut M T L θ) ≤ Q₁ F := fun g hg => by
    rw [← hT]
    obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
    exact ⟨⟨x, tImage_le θ _ hx⟩, rfl⟩
  exact C.A_le_Rt_of θ
    (omega5_rad_mem_closure hq hEQ (C.card_rhoIm_Ut_of_caseII θ hcrit hII))

end Cfg

end CFSG.Quasithin.MS93.S37
