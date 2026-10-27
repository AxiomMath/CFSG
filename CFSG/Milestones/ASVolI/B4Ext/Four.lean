module

public import CFSG.Milestones.ASVolI.B4Natural
public import CFSG.Quasithin.Background.SmithB49
public import CFSG.Quasithin.Background.SmithB51LnRealB

public section

namespace CFSG.ASVolI

section Offender

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

theorem burnsideB49x_exists_quadratic_offender {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G T A : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hA : IsFFStarOffender T A) :
    ∃ B : Subgroup (MulAut V), IsFFStarOffender G B ∧ IsQuadratic B := by
  have hAG : IsFFStarOffender G A := ⟨hA.1.trans hTG, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image {B : Subgroup (MulAut V) | IsFFStarOffender G B}
    (fun B => Nat.card B) (Set.toFinite _) ⟨A, hAG⟩
  exact ⟨B, hB, CFSG.Quasithin.B1_4_3_of_minimal hV hB fun B' hB' hB'B =>
    Subgroup.eq_of_le_of_card_ge hB'B (hmin B' hB')⟩

end Offender

section FieldTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def burnsideB49x_slMap (hK : Nat.card K = 2) (e : K ≃+* ZMod 2) :
    ↥(StatedSL n (ZMod 2)) →* ↥(StatedSL n K) :=
  ((Matrix.GeneralLinearGroup.map e.symm.toRingHom).comp (StatedSL n (ZMod 2)).subtype).codRestrict
    (StatedSL n K) fun _ => by
      rw [StatedAPI.statedSL_eq_top_of_card_two hK n]
      exact Subgroup.mem_top _

theorem burnsideB49x_slMap_coe (hK : Nat.card K = 2) (e : K ≃+* ZMod 2)
    (γ : ↥(StatedSL n (ZMod 2))) :
    (((burnsideB49x_slMap hK e γ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map e.symm := rfl

theorem burnsideB49x_slMap_surjective (hK : Nat.card K = 2) (e : K ≃+* ZMod 2) :
    Function.Surjective (burnsideB49x_slMap (n := n) hK e) := by
  intro δ
  refine ⟨⟨Matrix.GeneralLinearGroup.map e.toRingHom (δ : GL (Fin n) K),
    StatedAPI.mem_statedSL_zmod_two _⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [burnsideB49x_slMap_coe]
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

@[expose] def burnsideB49x_vecEquiv (e : K ≃+* ZMod 2) :
    Multiplicative (Fin n → K) ≃* Multiplicative (Fin n → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun i => e (Multiplicative.toAdd x i)
  invFun y := Multiplicative.ofAdd fun i => e.symm (Multiplicative.toAdd y i)
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [map_add]

theorem burnsideB49x_vecEquiv_apply (e : K ≃+* ZMod 2) (x : Multiplicative (Fin n → K)) :
    Multiplicative.toAdd (burnsideB49x_vecEquiv e x) = fun i => e (Multiplicative.toAdd x i) :=
  rfl

theorem burnsideB49x_map_mulVec (e : K ≃+* ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : Fin n → K) : (fun i => e ((M.map e.symm *ᵥ x) i)) = M *ᵥ fun i => e (x i) := by
  funext i
  have hM : (M.map e.symm).map e = M := Matrix.ext fun i j => by simp
  have h := RingHom.map_mulVec (e : K →+* ZMod 2) (M.map e.symm) x i
  rw [RingEquiv.coe_toRingHom, hM] at h
  exact h

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(StatedSL n K) →* ↥G}

theorem burnsideB49x_coords_two (hK : Nat.card K = 2) (e : K ≃+* ZMod 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) :
    ∃ β : ↥U →* Multiplicative (Fin n → ZMod 2), Function.Bijective β ∧
      ∀ (γ : ↥(StatedSL n (ZMod 2))) (u : ↥U)
        (hu : (((π.comp (burnsideB49x_slMap hK e)) γ : ↥G) : MulAut V) (u : V) ∈ U),
        Multiplicative.toAdd
            (β ⟨(((π.comp (burnsideB49x_slMap hK e)) γ : ↥G) : MulAut V) (u : V), hu⟩) =
          B5.Ln.mat γ *ᵥ Multiplicative.toAdd (β u) := by
  obtain ⟨β₀, hβb, hβe⟩ := burnsideB49_coords hreal
  refine ⟨(burnsideB49x_vecEquiv e).toMonoidHom.comp β₀,
    (burnsideB49x_vecEquiv e).bijective.comp hβb, fun γ u hu => ?_⟩
  have h1 := hβe (burnsideB49x_slMap hK e γ) u hu
  show Multiplicative.toAdd (burnsideB49x_vecEquiv e
      (β₀ ⟨((π (burnsideB49x_slMap hK e γ) : ↥G) : MulAut V) (u : V), hu⟩)) =
    B5.Ln.mat γ *ᵥ Multiplicative.toAdd (burnsideB49x_vecEquiv e (β₀ u))
  rw [h1, burnsideB49x_vecEquiv_apply, burnsideB49x_vecEquiv_apply, toAdd_ofAdd,
    burnsideB49x_slMap_coe]
  exact burnsideB49x_map_mulVec e _ _

end FieldTwo

section QuotNat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π' : ↥(StatedSL n (ZMod 2)) →* ↥G}

theorem burnsideB49x_realM_quot_nat (hπ' : Function.Surjective π')
    (hGU : ∀ g : ↥G, ∀ u ∈ U, (g : MulAut V) u ∈ U)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β)
    (hβe : ∀ (γ : ↥(StatedSL n (ZMod 2))) (u : ↥U)
      (hu : ((π' γ : ↥G) : MulAut V) (u : V) ∈ U),
      Multiplicative.toAdd (β ⟨((π' γ : ↥G) : MulAut V) (u : V), hu⟩) =
        B5.Ln.mat γ *ᵥ Multiplicative.toAdd (β u))
    (hq : ChB.QuotIsoSub G U) : B5.Ln.RealM G ⊤ U π' B5.Ln.mat := by
  obtain ⟨φ, hφ⟩ := hq
  refine ⟨hπ', le_top, fun _ _ _ => Subgroup.mem_top _, hGU,
    β.comp (φ.toMonoidHom.comp ((QuotientGroup.mk' U).comp (⊤ : Subgroup V).subtype)), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, rfl⟩ := hβb.2 y
    obtain ⟨x, rfl⟩ := φ.surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩
  · intro w
    show β (φ (QuotientGroup.mk (w : V))) = 1 ↔ (w : V) ∈ U
    rw [map_eq_one_iff β hβb.1, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  · intro γ w hw
    show Multiplicative.toAdd (β (φ (QuotientGroup.mk (((π' γ : ↥G) : MulAut V) (w : V))))) =
      B5.Ln.mat γ *ᵥ Multiplicative.toAdd (β (φ (QuotientGroup.mk (w : V))))
    have hu : ((π' γ : ↥G) : MulAut V) ((φ (QuotientGroup.mk (w : V)) : ↥U) : V) ∈ U :=
      hGU _ _ (φ _).2
    have h1 : φ (QuotientGroup.mk (((π' γ : ↥G) : MulAut V) (w : V))) =
        ⟨((π' γ : ↥G) : MulAut V) ((φ (QuotientGroup.mk (w : V)) : ↥U) : V), hu⟩ :=
      Subtype.ext (hφ _ (π' γ).2 (w : V))
    rw [h1]
    exact hβe γ _ hu

end QuotNat

section QuotDual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Open
open scoped Matrix

variable {n : ℕ} {V : Type} [CommGroup V] {U : Subgroup V}

@[expose] def burnsideB49x_pair (β : ↥U →* Multiplicative (Fin n → ZMod 2)) :
    Multiplicative (Fin n → ZMod 2) →* DualGrp ↥U where
  toFun y :=
    { toFun := fun u => Multiplicative.ofAdd
        (Multiplicative.toAdd y ⬝ᵥ Multiplicative.toAdd (β u))
      map_one' := by simp
      map_mul' := fun a b => by simp [dotProduct_add] }
  map_one' := by
    apply MonoidHom.ext
    intro u
    change Multiplicative.ofAdd ((0 : Fin n → ZMod 2) ⬝ᵥ Multiplicative.toAdd (β u)) = 1
    simp
  map_mul' := fun a b => by
    apply MonoidHom.ext
    intro u
    change Multiplicative.ofAdd ((Multiplicative.toAdd a + Multiplicative.toAdd b) ⬝ᵥ
        Multiplicative.toAdd (β u)) =
      Multiplicative.ofAdd (Multiplicative.toAdd a ⬝ᵥ Multiplicative.toAdd (β u)) *
        Multiplicative.ofAdd (Multiplicative.toAdd b ⬝ᵥ Multiplicative.toAdd (β u))
    rw [add_dotProduct, ofAdd_add]

theorem burnsideB49x_pair_apply (β : ↥U →* Multiplicative (Fin n → ZMod 2))
    (y : Multiplicative (Fin n → ZMod 2)) (u : ↥U) :
    burnsideB49x_pair β y u =
      Multiplicative.ofAdd (Multiplicative.toAdd y ⬝ᵥ Multiplicative.toAdd (β u)) := rfl

theorem burnsideB49x_pair_injective {β : ↥U →* Multiplicative (Fin n → ZMod 2)}
    (hβs : Function.Surjective β) : Function.Injective (burnsideB49x_pair β) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  apply Multiplicative.toAdd.injective
  funext i
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single i 1))
  have h : Multiplicative.ofAdd (Multiplicative.toAdd y ⬝ᵥ Multiplicative.toAdd (β u)) = 1 :=
    congrArg (fun χ : DualGrp ↥U => χ u) hy
  rw [hu, toAdd_ofAdd, dotProduct_single_one] at h
  simpa using h

theorem burnsideB49x_pair_bijective [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β) :
    Function.Bijective (burnsideB49x_pair β) := by
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨burnsideB49x_pair_injective hβb.2, ?_⟩
  rw [card_dualGrp hU2]
  exact (Nat.card_congr (Equiv.ofBijective β hβb)).symm

@[expose] noncomputable def burnsideB49x_dualCoord [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β) :
    DualGrp ↥U ≃* Multiplicative (Fin n → ZMod 2) :=
  (MulEquiv.ofBijective (burnsideB49x_pair β) (burnsideB49x_pair_bijective hV hβb)).symm

theorem burnsideB49x_dualCoord_spec [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β)
    (χ : DualGrp ↥U) (u : ↥U) :
    χ u = Multiplicative.ofAdd
      (Multiplicative.toAdd (burnsideB49x_dualCoord hV hβb χ) ⬝ᵥ Multiplicative.toAdd (β u)) :=
  (congrArg (fun f : DualGrp ↥U => f u)
    ((MulEquiv.ofBijective (burnsideB49x_pair β)
      (burnsideB49x_pair_bijective hV hβb)).apply_symm_apply χ)).symm

theorem burnsideB49x_dualCoord_unique [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β)
    (χ : DualGrp ↥U) (z : Fin n → ZMod 2)
    (h : ∀ u, χ u = Multiplicative.ofAdd (z ⬝ᵥ Multiplicative.toAdd (β u))) :
    burnsideB49x_dualCoord hV hβb χ = Multiplicative.ofAdd z := by
  have hχ : χ = burnsideB49x_pair β (Multiplicative.ofAdd z) := by
    apply MonoidHom.ext
    intro u
    rw [h u, burnsideB49x_pair_apply, toAdd_ofAdd]
  rw [hχ]
  exact (MulEquiv.ofBijective (burnsideB49x_pair β)
    (burnsideB49x_pair_bijective hV hβb)).symm_apply_apply _

variable {G : Subgroup (MulAut V)} {π' : ↥(StatedSL n (ZMod 2)) →* ↥G}

theorem burnsideB49x_realM_quot_dual [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hπ' : Function.Surjective π') (hGU : ∀ g : ↥G, ∀ u ∈ U, (g : MulAut V) u ∈ U)
    {β : ↥U →* Multiplicative (Fin n → ZMod 2)} (hβb : Function.Bijective β)
    (hβe : ∀ (γ : ↥(StatedSL n (ZMod 2))) (u : ↥U)
      (hu : ((π' γ : ↥G) : MulAut V) (u : V) ∈ U),
      Multiplicative.toAdd (β ⟨((π' γ : ↥G) : MulAut V) (u : V), hu⟩) =
        B5.Ln.mat γ *ᵥ Multiplicative.toAdd (β u))
    (hq : ChB.QuotIsoDual G U) : B5.Ln.RealM G ⊤ U π' B5.Ln.dmat := by
  obtain ⟨φ, hφ⟩ := hq
  refine ⟨hπ', le_top, fun _ _ _ => Subgroup.mem_top _, hGU,
    (burnsideB49x_dualCoord hV hβb).toMonoidHom.comp
      (φ.toMonoidHom.comp ((QuotientGroup.mk' U).comp (⊤ : Subgroup V).subtype)), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨χ, rfl⟩ := (burnsideB49x_dualCoord hV hβb).surjective y
    obtain ⟨x, rfl⟩ := φ.surjective χ
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩
  · intro w
    show burnsideB49x_dualCoord hV hβb (φ (QuotientGroup.mk (w : V))) = 1 ↔ (w : V) ∈ U
    exact (MulEquiv.map_eq_one_iff _).trans
      ((MulEquiv.map_eq_one_iff φ).trans (QuotientGroup.eq_one_iff _))
  · intro γ w hw
    show Multiplicative.toAdd (burnsideB49x_dualCoord hV hβb
        (φ (QuotientGroup.mk (((π' γ : ↥G) : MulAut V) (w : V))))) =
      B5.Ln.dmat γ *ᵥ Multiplicative.toAdd
        (burnsideB49x_dualCoord hV hβb (φ (QuotientGroup.mk (w : V))))
    rw [burnsideB49x_dualCoord_unique hV hβb _ (B5.Ln.dmat γ *ᵥ Multiplicative.toAdd
        (burnsideB49x_dualCoord hV hβb (φ (QuotientGroup.mk (w : V))))) fun u => ?_, toAdd_ofAdd]
    obtain ⟨u', hu'⟩ : ∃ u' : ↥U, ((π' γ : ↥G) : MulAut V) (u' : V) = (u : V) :=
      ⟨⟨((π' γ : ↥G) : MulAut V)⁻¹ (u : V), hGU (π' γ)⁻¹ _ u.2⟩, by
        change ((π' γ : ↥G) : MulAut V) (((π' γ : ↥G) : MulAut V)⁻¹ (u : V)) = _
        rw [← MulAut.mul_apply, mul_inv_cancel]
        rfl⟩
    rw [hφ _ (π' γ).2 (w : V) u u' hu', burnsideB49x_dualCoord_spec hV hβb _ u']
    have hmem : ((π' γ : ↥G) : MulAut V) (u' : V) ∈ U := hu' ▸ u.2
    have h1 := hβe γ u' hmem
    have h3 : (⟨((π' γ : ↥G) : MulAut V) (u' : V), hmem⟩ : ↥U) = u := Subtype.ext hu'
    rw [h3] at h1
    rw [h1, B5.Ln.dmat, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
      B5.Ln.mulVec_inv_mulVec]

end QuotDual

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB CFSG.Open in
theorem burnsideB49x_part2i_four_five {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {G : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSL n K) →* ↥G}
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : QuotIsoSub G U ∨ QuotIsoDual G U)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender T A) : SplitsOver G U := by
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let e : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardK
  have hπ' : Function.Surjective (π.comp (burnsideB49x_slMap hK e)) :=
    hreal.1.comp (burnsideB49x_slMap_surjective hK e)
  have hGU : ∀ g : ↥G, ∀ u ∈ U, (g : MulAut V) u ∈ U := hreal.2.2.2.1
  obtain ⟨β, hβb, hβe⟩ := burnsideB49x_coords_two hK e hreal
  have hU : B5.Ln.RealM G U ⊥ (π.comp (burnsideB49x_slMap hK e)) B5.Ln.mat := by
    refine ⟨hπ', bot_le, hGU, fun _ y hy => ?_, β, hβb.2, fun w => ?_, hβe⟩
    · rw [Subgroup.mem_bot] at hy ⊢
      rw [hy, map_one]
    · rw [map_eq_one_iff β hβb.1, Subgroup.mem_bot]
      constructor
      · rintro rfl
        rfl
      · exact fun h => Subtype.ext h
  have hQ : B5.Ln.RealM G ⊤ U (π.comp (burnsideB49x_slMap hK e)) B5.Ln.mat ∨
      B5.Ln.RealM G ⊤ U (π.comp (burnsideB49x_slMap hK e)) B5.Ln.dmat :=
    hquot.imp (burnsideB49x_realM_quot_nat hπ' hGU hβb hβe)
      (burnsideB49x_realM_quot_dual hV hπ' hGU hβb hβe)
  obtain ⟨B, hB, hBq⟩ := burnsideB49x_exists_quadratic_offender hV hT.1 hA
  obtain ⟨X, hXinv, hXU⟩ := CFSG.Quasithin.B5.asB492Split_holds V hV n hn G U _
    (B5.Ln.realM_mat_iff.1 hU) (hQ.imp B5.Ln.realM_mat_iff.1 B5.Ln.realM_dmat_iff.1) ⟨B, hB, hBq⟩
  exact ⟨X, hXinv, hXU.2, hXU.1⟩

end Final

end CFSG.ASVolI
