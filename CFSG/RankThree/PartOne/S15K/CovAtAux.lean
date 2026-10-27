module

public import CFSG.RankThree.PartOne.S15K.Refl
public import CFSG.RankThree.PartOne.S15K.ReflGroup
import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S12.KFTransfer

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem reflCtx_of_hyp [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) : ReflCtx p E where
  prime := h.prime
  odd := by have := h.three_lt; omega
  comm := fun a b => h.E_elem.is_comm.comm a b
  pow := fun a => Subtype.ext (by
    have hE : IsElementaryAbelian p E := h.E_elem
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a.1 a.2
    simpa using this)

theorem reflectionGroup_le_torusWeyl (p : ℕ) (E : Subgroup G) :
    reflectionGroup p E ≤ torusWeyl E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro t ⟨-, X, -, htX⟩
  exact Subgroup.map_le_range _ _ htX

theorem conj_mem_reflectionGroup [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {z : MulAut E} (hz : z ∈ reflectionGroup p E) :
    conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ reflectionGroup p E := by
  refine Subgroup.closure_induction
    (p := fun z _ => conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ reflectionGroup p E) ?_ ?_ ?_ ?_ hz
  · intro t ht
    exact Subgroup.subset_closure (conj_mem_reflectionSet hp ht hw)
  · simp
  · intro x y _ _ hx hy
    have := mul_mem hx hy
    simpa [mul_assoc] using this
  · intro x _ hx
    have := inv_mem hx
    simpa [mul_assoc] using this

theorem conj_mem_reflectionSet' [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G} {x t : MulAut E}
    (hx : x ∈ reflectionGroup p E) (ht : t ∈ reflectionSet p E) :
    x * t * x⁻¹ ∈ reflectionSet p E := by
  have hW : x ∈ torusWeyl E := reflectionGroup_le_torusWeyl p E hx
  obtain ⟨⟨w, hw⟩, rfl⟩ := hW
  exact conj_mem_reflectionSet hp ht hw

@[expose] def refSetR (p : ℕ) (E : Subgroup G) : Set ↥(reflectionGroup p E) :=
  {x | (x : MulAut E) ∈ reflectionSet p E}

variable {p : ℕ} {E : Subgroup G}

theorem refSetR_conj [Finite G] (hp : p.Prime) (x t : ↥(reflectionGroup p E)) (ht : t ∈ refSetR p E) :
    x * t * x⁻¹ ∈ refSetR p E := conj_mem_reflectionSet' hp x.2 ht

theorem refSetR_sq {t : ↥(reflectionGroup p E)} (ht : t ∈ refSetR p E) : t * t = 1 :=
  Subtype.ext (ReflCtx.mul_self_eq_one_of ht.1)

theorem refSetR_ne_one {t : ↥(reflectionGroup p E)} (ht : t ∈ refSetR p E) : t ≠ 1 := by
  intro h
  have h1 : orderOf (t : MulAut E) = 2 := ht.1.1
  have : (t : MulAut E) = 1 := congrArg Subtype.val h
  rw [this, orderOf_one] at h1
  exact absurd h1 (by norm_num)

theorem refSetR_F2 [Finite G] (C : ReflCtx p E) {x y : ↥(reflectionGroup p E)} (hx : x ∈ refSetR p E)
    (hy : y ∈ refSetR p E) (hne : x ≠ y) (hcomm : x * y = y * x) : x * y ∉ refSetR p E :=
  fun hmem => C.not_isAutReflection_mul hx.1 hy.1 (congrArg Subtype.val hcomm)
    (fun h => hne (Subtype.ext h)) hmem.1

theorem refSetR_gen : Subgroup.closure (refSetR p E) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem rowOne_frame [Finite G] (C : ReflCtx p E) (σ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4))
    {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    ∃ s ∈ reflectionSet p E, ∃ t' ∈ reflectionSet p E, ∃ s' ∈ reflectionSet p E,
      t * s = s * t ∧ t ≠ s ∧ t' * s' = s' * t' ∧ t' ≠ s' ∧ (t' * s') * t * (t' * s')⁻¹ = s := by
  obtain ⟨s, hs, t', ht', s', hs', h1, h2, h3, h4, h5⟩ := s4_frame σ (refSetR p E)
    (refSetR_conj C.prime) (fun t ht => refSetR_sq ht) (fun t ht => refSetR_ne_one ht)
    (fun x hx y hy hne hc => refSetR_F2 C hx hy hne hc)
    (t := (⟨t, Subgroup.subset_closure ht⟩ : ↥(reflectionGroup p E))) ht
  refine ⟨(s : MulAut E), hs, (t' : MulAut E), ht', (s' : MulAut E), hs', ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val h1
  · exact fun h => h2 (Subtype.ext h)
  · exact congrArg Subtype.val h3
  · exact fun h => h4 (Subtype.ext h)
  · exact congrArg Subtype.val h5

theorem central_unique (σ : ↥(reflectionGroup p E) ≃* R2S4) :
    ∀ x y : ↥(reflectionGroup p E), (∀ g, g * x = x * g) → (∀ g, g * y = y * g) → x ≠ 1 → y ≠ 1 →
      x = y := by
  intro x y hx hy hx1 hy1
  have hcx : ∀ g : R2S4, g * σ x = σ x * g := fun g => by
    apply σ.symm.injective
    simpa using hx (σ.symm g)
  have hcy : ∀ g : R2S4, g * σ y = σ y * g := fun g => by
    apply σ.symm.injective
    simpa using hy (σ.symm g)
  have hx' : σ x = zz := (r2_center _ hcx).resolve_left fun h => hx1 (σ.injective (by rw [h, map_one]))
  have hy' : σ y = zz := (r2_center _ hcy).resolve_left fun h => hy1 (σ.injective (by rw [h, map_one]))
  exact σ.injective (hx'.trans hy'.symm)

theorem not_central_of_fixed [Finite G] (C : ReflCtx p E) (hirr : torusIrreducible E)
    (hZ : ∀ x y : ↥(reflectionGroup p E), (∀ g, g * x = x * g) → (∀ g, g * y = y * g) → x ≠ 1 →
      y ≠ 1 → x = y)
    {z : ↥(reflectionGroup p E)} (hz1 : z ≠ 1) (hzfix : autFixed E (z : MulAut E) ≠ ⊥) :
    ¬ ∀ g : ↥(reflectionGroup p E), g * z = z * g := by
  intro hcen
  have hinv : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹ = z := by
    intro w hw
    have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := inv_mem hw
    have hinvc : conjAut E w⁻¹ hw' = (conjAut E w hw)⁻¹ := Equivariance.conjAut_inv hw
    have hy : conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹ ∈ reflectionGroup p E :=
      conj_mem_reflectionGroup C.prime hw z.2
    let y : ↥(reflectionGroup p E) := ⟨conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹, hy⟩
    have hy1 : y ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      have h' : conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹ = 1 := congrArg Subtype.val h
      calc (z : MulAut E) = (conjAut E w hw)⁻¹ * (conjAut E w hw * (z : MulAut E) *
            (conjAut E w hw)⁻¹) * conjAut E w hw := by group
        _ = 1 := by rw [h']; group
    have hycen : ∀ g : ↥(reflectionGroup p E), g * y = y * g := by
      intro g
      have hg' : (conjAut E w hw)⁻¹ * (g : MulAut E) * conjAut E w hw ∈ reflectionGroup p E := by
        have := conj_mem_reflectionGroup C.prime hw' g.2
        rwa [hinvc, inv_inv] at this
      have h2 : ((conjAut E w hw)⁻¹ * (g : MulAut E) * conjAut E w hw) * (z : MulAut E) =
          (z : MulAut E) * ((conjAut E w hw)⁻¹ * (g : MulAut E) * conjAut E w hw) :=
        congrArg Subtype.val (hcen ⟨_, hg'⟩)
      apply Subtype.ext
      show (g : MulAut E) * (conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹) =
        (conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹) * (g : MulAut E)
      calc (g : MulAut E) * (conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹)
          = conjAut E w hw * (((conjAut E w hw)⁻¹ * (g : MulAut E) * conjAut E w hw) *
              (z : MulAut E)) * (conjAut E w hw)⁻¹ := by group
        _ = conjAut E w hw * ((z : MulAut E) * ((conjAut E w hw)⁻¹ * (g : MulAut E) *
              conjAut E w hw)) * (conjAut E w hw)⁻¹ := by rw [h2]
        _ = (conjAut E w hw * (z : MulAut E) * (conjAut E w hw)⁻¹) * (g : MulAut E) := by group
    exact (congrArg Subtype.val (hZ z y hcen hycen hz1 hy1)).symm
  rcases ReflCtx.fixed_eq_bot_or_top_of_inv hirr hinv with h | h
  · exact hzfix h
  · apply hz1
    apply Subtype.ext
    refine MulEquiv.ext fun e => ?_
    have : e ∈ autFixed E (z : MulAut E) := by rw [h]; trivial
    exact this

theorem refSetR_not_central [Finite G] (C : ReflCtx p E) (hirr : torusIrreducible E)
    (hE3 : Nat.card E = p ^ 3)
    (hZ : ∀ x y : ↥(reflectionGroup p E), (∀ g, g * x = x * g) → (∀ g, g * y = y * g) → x ≠ 1 →
      y ≠ 1 → x = y)
    {x : ↥(reflectionGroup p E)} (hx : x ∈ refSetR p E) : ¬ ∀ g, g * x = x * g := by
  refine not_central_of_fixed C hirr hZ (refSetR_ne_one hx) ?_
  intro hbot
  have h := Sec13Base.card_eq_mul C.comm (x : MulAut E)
  rw [hbot, Subgroup.card_bot, hx.1.2, hE3] at h
  have hp := C.prime.two_le
  have h4 : 4 ≤ p * p := Nat.mul_le_mul hp hp
  have h3 : p ^ 3 = p * p * p := by ring
  nlinarith [h, h3, h4]

theorem refSetR_not_central_mul [Finite G] (C : ReflCtx p E) (hirr : torusIrreducible E)
    (hE3 : Nat.card E = p ^ 3)
    (hZ : ∀ x y : ↥(reflectionGroup p E), (∀ g, g * x = x * g) → (∀ g, g * y = y * g) → x ≠ 1 →
      y ≠ 1 → x = y)
    {x y : ↥(reflectionGroup p E)} (hx : x ∈ refSetR p E) (hy : y ∈ refSetR p E) (hne : x ≠ y)
    (_hcomm : x * y = y * x) : ¬ ∀ g, g * (x * y) = (x * y) * g := by
  refine not_central_of_fixed C hirr hZ ?_ ?_
  · intro h
    apply hne
    have hxx := refSetR_sq hx
    have : y = x⁻¹ := by
      calc y = x⁻¹ * (x * y) := by group
        _ = x⁻¹ := by rw [h, mul_one]
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hxx).symm
  · intro hbot
    apply C.fixed_inf_fixed_ne_bot hx.1 hy.1 hE3
    rw [eq_bot_iff]
    intro e he
    have hex : (x : MulAut E) e = e := he.1
    have hey : (y : MulAut E) e = e := he.2
    have : e ∈ autFixed E ((x * y : ↥(reflectionGroup p E)) : MulAut E) := by
      show (x : MulAut E) ((y : MulAut E) e) = e
      rw [hey, hex]
    rw [hbot] at this
    exact this

theorem rowB_frame [Finite G] (C : ReflCtx p E) (hirr : torusIrreducible E)
    (hE3 : Nat.card E = p ^ 3) (σ : ↥(reflectionGroup p E) ≃* R2S4) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) :
    ∃ s₁ ∈ reflectionSet p E, ∃ s₂ ∈ reflectionSet p E, s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ ≠ s₂ ∧
      t * s₁ = s₁ * t ∧ t * s₂ = s₂ * t ∧ s₁ * s₂ = s₂ * s₁ := by
  have hZ := central_unique σ
  obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h3, h4, h5, h6⟩ := b3_frame σ (refSetR p E)
    (refSetR_conj C.prime) (fun t ht => refSetR_sq ht) (fun t ht => refSetR_ne_one ht) refSetR_gen
    (fun x hx => refSetR_not_central C hirr hE3 hZ hx)
    (fun x hx y hy hne hc => refSetR_not_central_mul C hirr hE3 hZ hx hy hne hc)
    (t := (⟨t, Subgroup.subset_closure ht⟩ : ↥(reflectionGroup p E))) ht
  refine ⟨(s₁ : MulAut E), hs₁, (s₂ : MulAut E), hs₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => h1 (Subtype.ext h)
  · exact fun h => h2 (Subtype.ext h)
  · exact fun h => h3 (Subtype.ext h)
  · exact congrArg Subtype.val h4
  · exact congrArg Subtype.val h5
  · exact congrArg Subtype.val h6

end CFSG.RankThree.PartOne.S15K
