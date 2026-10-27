module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8PermA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Def

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}

theorem s16k_tri8_exists_natProj {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {U Z B : Subgroup V}
    {K : Type} [Field K] [Finite K]
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).RealizesVia H U Z π)
    (hHB : ∀ h : ↥H, ∀ b ∈ B, (h : MulAut V) b ∈ B)
    (hind : U ⊓ (Z ⊔ B) ≤ Z) (hsup : Z ⊔ (U ⊔ B) = ⊤) :
    ∃ (f : ↥U →* Multiplicative (Fin 4 ⊕ Fin 4 → K))
      (κ : V →* Multiplicative (Fin 4 ⊕ Fin 4 → K)),
      Function.Surjective f ∧ (∀ u, f u = 1 ↔ (u : V) ∈ Z) ∧
      (∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K))) (u : ↥U)
          (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        f ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f u)) ∧
      κ.ker = Z ⊔ B ∧ (∀ u : ↥U, κ (u : V) = f u) ∧
      (∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K))) (v : V),
        κ (((π γ : ↥H) : MulAut V) v) =
          natAct (StatedOmega (StatedQuadPlus 4 K)) γ (κ v)) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.FFC.exists_natMap
    (Γ := StatedOmega (StatedQuadPlus 4 K)) hR
  let q : V →* V ⧸ (Z ⊔ B) := QuotientGroup.mk' (Z ⊔ B)
  let qI : ↥U →* V ⧸ (Z ⊔ B) := q.comp U.subtype
  have hqIs : Function.Surjective qI := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z ⊔ B) y
    have hv : v ∈ Z ⊔ (U ⊔ B) := by rw [hsup]; exact Subgroup.mem_top v
    obtain ⟨z, w, hzw⟩ := (Subgroup.mem_sup').1 hv
    obtain ⟨u, b, hub⟩ := (Subgroup.mem_sup').1 w.2
    refine ⟨u, ?_⟩
    show q (u : V) = q v
    rw [← hzw, ← hub, map_mul, map_mul]
    have hz : q (z : V) = 1 := (QuotientGroup.eq_one_iff _).2 ((le_sup_left : Z ≤ Z ⊔ B) z.2)
    have hb : q (b : V) = 1 := (QuotientGroup.eq_one_iff _).2 ((le_sup_right : B ≤ Z ⊔ B) b.2)
    rw [hz, hb, one_mul, mul_one]
  have hqIk : qI.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hind ⟨u.2, (QuotientGroup.eq_one_iff _).1 h⟩
    · intro h
      exact (QuotientGroup.eq_one_iff _).2 ((le_sup_left : Z ≤ Z ⊔ B) h)
  have hfker : f.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hfk u
  let e₁ : ↥U ⧸ Z.subgroupOf U ≃* V ⧸ (Z ⊔ B) :=
    (QuotientGroup.quotientMulEquivOfEq hqIk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := qI) hqIs)
  let e₂ : ↥U ⧸ Z.subgroupOf U ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := f) hfs)
  let κ : V →* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    ((e₁.symm.trans e₂).toMonoidHom).comp q
  have hκker : κ.ker = Z ⊔ B := by
    have hker : κ.ker = q.ker := by
      ext v
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show ((e₁.symm.trans e₂).toMonoidHom) (q v) = 1 ↔ q v = 1
      exact MulEquiv.map_eq_one_iff (e₁.symm.trans e₂)
    rw [hker, QuotientGroup.ker_mk']
  have hκU : ∀ u : ↥U, κ (u : V) = f u := by
    intro u
    have he₁ : e₁ (QuotientGroup.mk u) = qI u := by
      simp only [e₁, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact QuotientGroup.kerLift_mk (φ := qI) u
    have he₂ : e₂ (QuotientGroup.mk u) = f u := by
      simp only [e₂, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact QuotientGroup.kerLift_mk (φ := f) u
    change e₂ (e₁.symm (q (u : V))) = f u
    have hqu : q (u : V) = e₁ (QuotientGroup.mk u) := by rw [he₁]; rfl
    rw [hqu, MulEquiv.symm_apply_apply, he₂]
  have hκZ : ∀ z : Z, κ (z : V) = 1 := fun z => by
    rw [← MonoidHom.mem_ker, hκker]
    exact (le_sup_left : Z ≤ Z ⊔ B) z.2
  have hκB : ∀ b : B, κ (b : V) = 1 := fun b => by
    rw [← MonoidHom.mem_ker, hκker]
    exact (le_sup_right : B ≤ Z ⊔ B) b.2
  have hκf : ∀ (z : Z) (u : U) (b : B), κ ((z : V) * ((u : V) * (b : V))) = f u := by
    intro z u b
    rw [show (z : V) * ((u : V) * (b : V)) = ((z : V) * (u : V)) * (b : V) by
      rw [mul_assoc]]
    simp only [map_mul, hκZ z, hκU u, hκB b, one_mul, mul_one]
  refine ⟨f, κ, hfs, hfk, hfe, hκker, hκU, ?_⟩
  intro γ v
  have hv : v ∈ Z ⊔ (U ⊔ B) := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨z, w, hzw⟩ := (Subgroup.mem_sup').1 hv
  obtain ⟨u, b, hub⟩ := (Subgroup.mem_sup').1 w.2
  have hzZ : ((π γ : ↥H) : MulAut V) (z : V) ∈ Z :=
    hR.2.2.2.2.1 (π γ) (z : V) z.2
  have huU : ((π γ : ↥H) : MulAut V) (u : V) ∈ U :=
    hR.2.2.2.1 (π γ) (u : V) u.2
  have hbB : ((π γ : ↥H) : MulAut V) (b : V) ∈ B := hHB (π γ) (b : V) b.2
  have hmap : ((π γ : ↥H) : MulAut V) ((z : V) * ((u : V) * (b : V))) =
      ((π γ : ↥H) : MulAut V) (z : V) *
        (((π γ : ↥H) : MulAut V) (u : V) * ((π γ : ↥H) : MulAut V) (b : V)) := by
    rw [map_mul, map_mul]
  calc κ (((π γ : ↥H) : MulAut V) v)
      = κ (((π γ : ↥H) : MulAut V) ((z : V) * ((u : V) * (b : V)))) := by
        rw [← hzw, ← hub]
    _ = κ (((π γ : ↥H) : MulAut V) (z : V) *
          (((π γ : ↥H) : MulAut V) (u : V) * ((π γ : ↥H) : MulAut V) (b : V))) := by
        rw [hmap]
    _ = f ⟨((π γ : ↥H) : MulAut V) (u : V), huU⟩ :=
        hκf ⟨_, hzZ⟩ ⟨_, huU⟩ ⟨_, hbB⟩
    _ = natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f u) := hfe γ u huU
    _ = natAct (StatedOmega (StatedQuadPlus 4 K)) γ (κ v) := by
        have hfu : f u = κ v := by
          rw [show v = (z : V) * ((u : V) * (b : V)) by rw [← hzw, ← hub], hκf z u b]
        rw [hfu]

theorem s16k_tri8_summands_of_irr (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂)
    {X : Subgroup (Vtil V₀ V hV)}
    (hstab : StableUnder (lBar V₀ V hV L) X)
    (hZX : fixV (lBar V₀ V hV L) ≤ X)
    (hirrX : IsIrrOn (lBar V₀ V hV L) X (fixV (lBar V₀ V hV L))) :
    X = I₁ ∨ X = I₂ := by
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Z : Subgroup (Vtil V₀ V hV) := fixV (lBar V₀ V hV L)
  obtain ⟨f₁, κ₁, hf₁s, hf₁k, hf₁e, hκ₁ker, hκ₁eq, hκ₁equiv⟩ :=
    s16k_tri8_exists_natProj (H := H) (U := I₁) (Z := Z) (B := I₂)
      hc.real₁ hc.real₂.2.2.2.1 hc.ind₁ hc.sup
  obtain ⟨f₂, κ₂, hf₂s, hf₂k, hf₂e, hκ₂ker, hκ₂eq, hκ₂equiv⟩ :=
    s16k_tri8_exists_natProj (H := H) (U := I₂) (Z := Z) (B := I₁)
      hc.real₂ hc.real₁.2.2.2.1 hc.ind₂ (by
        rw [show I₂ ⊔ I₁ = I₁ ⊔ I₂ from sup_comm _ _]; exact hc.sup)
  have hirr₁ : IsIrrOn H I₁ Z := s16k_tri8_isIrrOn_of_realizes hc.card₁ hc.real₁
  have hirr₂ : IsIrrOn H I₂ Z := s16k_tri8_isIrrOn_of_realizes hc.card₂ hc.real₂
  have hP₁ : ∀ γ : ↥(StatedOmega (StatedQuadPlus 4 K₁)), ∀ p ∈ X.map κ₁,
      natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ p ∈ X.map κ₁ := by
    intro γ p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    rw [← hκ₁equiv γ x]
    exact Subgroup.mem_map.2 ⟨((π₁ γ : ↥H) : MulAut _) x, hstab (π₁ γ) (π₁ γ).2 x hx, rfl⟩
  have hP₂ : ∀ γ : ↥(StatedOmega (StatedQuadPlus 4 K₂)), ∀ p ∈ X.map κ₂,
      natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ p ∈ X.map κ₂ := by
    intro γ p hp
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
    rw [← hκ₂equiv γ x]
    exact Subgroup.mem_map.2 ⟨((π₂ γ : ↥H) : MulAut _) x, hstab (π₂ γ) (π₂ γ).2 x hx, rfl⟩
  rcases s16k_tri8_statedOmega_stable_eq_bot_or_top hc.card₁ hP₁ with hbot₁ | htop₁
  · right
    have hXI₂ : X ≤ I₂ := by
      intro x hx
      have hxker : κ₁ x = 1 := by
        have : κ₁ x ∈ X.map κ₁ := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
        rw [hbot₁, Subgroup.mem_bot] at this
        exact this
      have hxmem : x ∈ κ₁.ker := MonoidHom.mem_ker.2 hxker
      rw [hκ₁ker, sup_eq_right.mpr hc.le₂] at hxmem
      exact hxmem
    rcases hirr₂.2.2.2 X hstab hZX hXI₂ with h | h
    · exact (hirrX.1.ne h.symm).elim
    · exact h
  rcases s16k_tri8_statedOmega_stable_eq_bot_or_top hc.card₂ hP₂ with hbot₂ | htop₂
  · left
    have hXI₁ : X ≤ I₁ := by
      intro x hx
      have hxker : κ₂ x = 1 := by
        have : κ₂ x ∈ X.map κ₂ := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
        rw [hbot₂, Subgroup.mem_bot] at this
        exact this
      have hxmem : x ∈ κ₂.ker := MonoidHom.mem_ker.2 hxker
      rw [hκ₂ker, sup_eq_right.mpr hc.le₁] at hxmem
      exact hxmem
    rcases hirr₁.2.2.2 X hstab hZX hXI₁ with h | h
    · exact (hirrX.1.ne h.symm).elim
    · exact h
  exfalso
  have hκ₁kerstab : StableUnder H κ₁.ker := by
    intro x hx y hy
    obtain ⟨γ, hγ⟩ := hc.real₁.1 ⟨x, hx⟩
    have hxγ : ((π₁ γ : ↥H) : MulAut _) = x := congrArg Subtype.val hγ
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [← hxγ]
    rw [hκ₁equiv γ y, hy]
    exact CFSG.Quasithin.FFC.natAct_one_right γ
  have hK₁ : X ⊓ κ₁.ker = Z := by
    have hKstab : StableUnder H (X ⊓ κ₁.ker) :=
      fun x hx y hy => ⟨hstab x hx (y : Vtil V₀ V hV) hy.1, hκ₁kerstab x hx (y : Vtil V₀ V hV) hy.2⟩
    have hZK : Z ≤ X ⊓ κ₁.ker := le_inf hZX (by rw [hκ₁ker]; exact le_sup_left)
    rcases hirrX.2.2.2 (X ⊓ κ₁.ker) hKstab hZK inf_le_left with h | h
    · exact h
    · exfalso
      have hXle : X ≤ κ₁.ker := by rw [← h]; exact inf_le_right
      have hbot : X.map κ₁ = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall (X.map κ₁)).2 fun p hp => ?_
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
        exact MonoidHom.mem_ker.2 (hXle hx)
      exact top_ne_bot (htop₁.symm.trans hbot)
  have hκ₂kerstab : StableUnder H κ₂.ker := by
    intro x hx y hy
    obtain ⟨γ, hγ⟩ := hc.real₂.1 ⟨x, hx⟩
    have hxγ : ((π₂ γ : ↥H) : MulAut _) = x := congrArg Subtype.val hγ
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [← hxγ]
    rw [hκ₂equiv γ y, hy]
    exact CFSG.Quasithin.FFC.natAct_one_right γ
  have hK₂ : X ⊓ κ₂.ker = Z := by
    have hKstab : StableUnder H (X ⊓ κ₂.ker) :=
      fun x hx y hy => ⟨hstab x hx (y : Vtil V₀ V hV) hy.1, hκ₂kerstab x hx (y : Vtil V₀ V hV) hy.2⟩
    have hZK : Z ≤ X ⊓ κ₂.ker := le_inf hZX (by rw [hκ₂ker]; exact le_sup_left)
    rcases hirrX.2.2.2 (X ⊓ κ₂.ker) hKstab hZK inf_le_left with h | h
    · exact h
    · exfalso
      have hXle : X ≤ κ₂.ker := by rw [← h]; exact inf_le_right
      have hbot : X.map κ₂ = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall (X.map κ₂)).2 fun p hp => ?_
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
        exact MonoidHom.mem_ker.2 (hXle hx)
      exact top_ne_bot (htop₂.symm.trans hbot)
  have hK₁' : X ⊓ (Z ⊔ I₂) = Z := by rw [← hκ₁ker]; exact hK₁
  have hkerX₁ : (κ₁.comp X.subtype).ker = Z.subgroupOf X := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : Vtil V₀ V hV) ∈ κ₁.ker := hx
      rw [hκ₁ker] at h1
      have h2 : (x : Vtil V₀ V hV) ∈ X ⊓ (Z ⊔ I₂) := ⟨x.2, h1⟩
      rwa [hK₁'] at h2
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      show (κ₁.comp X.subtype) x = 1
      have h1 : (x : Vtil V₀ V hV) ∈ κ₁.ker := by
        rw [hκ₁ker]
        exact (le_sup_left : Z ≤ Z ⊔ I₂) hx
      exact h1
  have hK₂' : X ⊓ (Z ⊔ I₁) = Z := by rw [← hκ₂ker]; exact hK₂
  have hkerX₂ : (κ₂.comp X.subtype).ker = Z.subgroupOf X := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : Vtil V₀ V hV) ∈ κ₂.ker := hx
      rw [hκ₂ker] at h1
      have h2 : (x : Vtil V₀ V hV) ∈ X ⊓ (Z ⊔ I₁) := ⟨x.2, h1⟩
      rwa [hK₂'] at h2
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      show (κ₂.comp X.subtype) x = 1
      have h1 : (x : Vtil V₀ V hV) ∈ κ₂.ker := by
        rw [hκ₂ker]
        exact (le_sup_left : Z ≤ Z ⊔ I₁) hx
      exact h1
  have hsurj₁X : Function.Surjective (κ₁.comp X.subtype) := by
    intro y
    have : y ∈ X.map κ₁ := by rw [htop₁]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨x, hx⟩, hxy⟩
  have hsurj₂X : Function.Surjective (κ₂.comp X.subtype) := by
    intro y
    have : y ∈ X.map κ₂ := by rw [htop₂]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨x, hx⟩, hxy⟩
  let eX₁ : ↥X ⧸ Z.subgroupOf X ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K₁) :=
    (QuotientGroup.quotientMulEquivOfEq hkerX₁.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := κ₁.comp X.subtype) hsurj₁X)
  let eX₂ : ↥X ⧸ Z.subgroupOf X ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K₂) :=
    (QuotientGroup.quotientMulEquivOfEq hkerX₂.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := κ₂.comp X.subtype) hsurj₂X)
  have heX₁ : ∀ x : ↥X, eX₁ (QuotientGroup.mk x) = (κ₁.comp X.subtype) x := by
    intro x
    simp only [eX₁, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk (φ := κ₁.comp X.subtype) x
  have heX₂ : ∀ x : ↥X, eX₂ (QuotientGroup.mk x) = (κ₂.comp X.subtype) x := by
    intro x
    simp only [eX₂, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk (φ := κ₂.comp X.subtype) x
  have heX₁_equiv : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K₁))) (x : ↥X),
      natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ (eX₁ (QuotientGroup.mk x)) =
        eX₁ (QuotientGroup.mk ⟨((π₁ γ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
          hstab (π₁ γ) (π₁ γ).2 (x : Vtil V₀ V hV) x.2⟩) := by
    intro γ x
    rw [heX₁ x, heX₁ ⟨_, _⟩]
    exact (hκ₁equiv γ (x : Vtil V₀ V hV)).symm
  have heX₂_equiv : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K₂))) (x : ↥X),
      natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ (eX₂ (QuotientGroup.mk x)) =
        eX₂ (QuotientGroup.mk ⟨((π₂ γ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
          hstab (π₂ γ) (π₂ γ).2 (x : Vtil V₀ V hV) x.2⟩) := by
    intro γ x
    rw [heX₂ x, heX₂ ⟨_, _⟩]
    exact (hκ₂equiv γ (x : Vtil V₀ V hV)).symm
  apply hc.ne
  refine ⟨eX₁.symm.trans eX₂, ?_, ?_, ?_⟩
  · intro m
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
  · intro m
    change m = 1 ↔ (eX₁.symm.trans eX₂) m = 1
    exact (MulEquiv.map_eq_one_iff (eX₁.symm.trans eX₂)).symm
  · intro γ₁ γ₂ hγ m
    obtain ⟨x, hx⟩ : ∃ x : ↥X, eX₁ (QuotientGroup.mk x) = m := by
      obtain ⟨qm, hqm⟩ := eX₁.surjective m
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective qm
      exact ⟨x, hqm⟩
    have hxA₁ : (⟨((π₁ γ₁ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
          hstab (π₁ γ₁) (π₁ γ₁).2 (x : Vtil V₀ V hV) x.2⟩ : ↥X) =
        ⟨((π₂ γ₂ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
          hstab (π₂ γ₂) (π₂ γ₂).2 (x : Vtil V₀ V hV) x.2⟩ := by
      apply Subtype.ext
      exact congrArg (fun f : ↥H => (f : MulAut _) (x : Vtil V₀ V hV)) hγ
    change (eX₁.symm.trans eX₂) (natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ₁ m) =
      natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂ ((eX₁.symm.trans eX₂) m)
    calc (eX₁.symm.trans eX₂) (natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ₁ m)
      _ = (eX₁.symm.trans eX₂)
            (natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ₁ (eX₁ (QuotientGroup.mk x))) := by
            rw [hx.symm]
      _ = (eX₁.symm.trans eX₂)
            (eX₁ (QuotientGroup.mk ⟨((π₁ γ₁ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
              hstab (π₁ γ₁) (π₁ γ₁).2 (x : Vtil V₀ V hV) x.2⟩)) := by
            rw [heX₁_equiv γ₁ x]
      _ = eX₂ (QuotientGroup.mk ⟨((π₁ γ₁ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
              hstab (π₁ γ₁) (π₁ γ₁).2 (x : Vtil V₀ V hV) x.2⟩) := by
            simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      _ = eX₂ (QuotientGroup.mk ⟨((π₂ γ₂ : ↥H) : MulAut _) (x : Vtil V₀ V hV),
              hstab (π₂ γ₂) (π₂ γ₂).2 (x : Vtil V₀ V hV) x.2⟩) := by
            rw [hxA₁]
      _ = natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂ (eX₂ (QuotientGroup.mk x)) := by
            rw [← heX₂_equiv γ₂ x]
      _ = natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂
            ((eX₁.symm.trans eX₂) (eX₁ (QuotientGroup.mk x))) := by
            simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      _ = natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂ ((eX₁.symm.trans eX₂) m) := by
            rw [hx.symm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
