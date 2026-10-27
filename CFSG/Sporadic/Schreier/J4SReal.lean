module

public import CFSG.Sporadic.Schreier.J4SRealCheck
public import CFSG.Sporadic.Schreier.J4SRealGen
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.Schreier.J4SNChar
public import CFSG.LinearAlgebra.DistinctSubdegreesLinearization
public import Certificates.Certificate2168
public import Certificates.Certificate2171
public import Certificates.Certificate2172
public import Certificates.Certificate2174
public import Certificates.Certificate2177
public import Certificates.Certificate2181
public import Certificates.Certificate2182
public import Certificates.Certificate3084
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.GLQ
open MulAction
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section RowAct

variable {G' : Type*} [Group G'] {R : Type*} [CommRing R] {m : ℕ}
  (ψ : G' →* (Matrix (Fin m) (Fin m) R)ˣ)

@[expose] def rowAct : G' →* ((Fin m → R) ≃ₗ[R] (Fin m → R)) where
  toFun g :=
    { toFun := fun w => w ᵥ* (↑(ψ g)⁻¹ : Matrix (Fin m) (Fin m) R)
      invFun := fun w => w ᵥ* (↑(ψ g) : Matrix (Fin m) (Fin m) R)
      map_add' := fun x y => Matrix.add_vecMul _ x y
      map_smul' := fun c x => Matrix.smul_vecMul c x _
      left_inv := fun w => by
        dsimp only
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.vecMul_one]
      right_inv := fun w => by
        dsimp only
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one] }
  map_one' := LinearEquiv.ext fun w => by
    show w ᵥ* (↑(ψ 1)⁻¹ : Matrix (Fin m) (Fin m) R) = w
    rw [map_one, inv_one, Units.val_one, Matrix.vecMul_one]
  map_mul' g h := LinearEquiv.ext fun w => by
    show w ᵥ* (↑(ψ (g * h))⁻¹ : Matrix (Fin m) (Fin m) R) =
      (w ᵥ* (↑(ψ h)⁻¹ : Matrix (Fin m) (Fin m) R)) ᵥ* (↑(ψ g)⁻¹ : Matrix (Fin m) (Fin m) R)
    rw [map_mul, mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul]

theorem rowAct_apply (g : G') (w : Fin m → R) :
    rowAct ψ g w = w ᵥ* (↑(ψ g)⁻¹ : Matrix (Fin m) (Fin m) R) := rfl

theorem rowAct_injective (hψ : Function.Injective ψ) : Function.Injective (rowAct ψ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h : ∀ w : Fin m → R, w ᵥ* (↑(ψ g)⁻¹ : Matrix (Fin m) (Fin m) R) = w := fun w => by
    rw [← rowAct_apply, hg]
    rfl
  have h1 : (↑(ψ g)⁻¹ : Matrix (Fin m) (Fin m) R) = 1 := by
    ext i j
    have := congrFun (h (Pi.single i 1)) j
    rw [Matrix.single_vecMul, one_smul, Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h2 : (ψ g)⁻¹ = 1 := Units.ext h1
  rw [Subgroup.mem_bot]
  exact hψ (by rw [inv_eq_one.1 h2, map_one])

end RowAct

@[expose] def rowLin : J →* ((Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :=
  @rowAct J (Subgroup.toGroup J) (ZMod 2) _ 112 J.subtype

theorem rowLin_apply (g : J) (w : Fin 112 → ZMod 2) :
    rowLin g w = w ᵥ* ((((g : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2))) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  @rowAct_apply J (Subgroup.toGroup J) (ZMod 2) _ 112 J.subtype g w

theorem rowLin_injective : Function.Injective rowLin :=
  @rowAct_injective J (Subgroup.toGroup J) (ZMod 2) _ 112 J.subtype J.subtype_injective

abbrev rowGroup : Subgroup ((Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :=
  rowLin.range

theorem rowGroup_le_orthogonal :
    rowGroup ≤ TauCeti.QuadraticMap.orthogonalGroup jq := by
  rintro _ ⟨g, rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [rowLin_apply]
  have h := jq_vecMul g⁻¹ w
  rw [φ_apply, Subgroup.coe_inv] at h
  exact h

@[expose] def rootVec : Fin 112 → ZMod 2 := toVecD 112 rootBits

theorem rowLin_eq_smul (g : J) (w : Row) : rowLin g (ofRow w) = ofRow (g • w) := by
  rw [rowLin_apply, smul_row, Subgroup.coe_inv]

theorem rootVec_eq_ofRow : rootVec = ofRow v := rfl

theorem rowLin_rootVec (g : J) : rowLin g rootVec = ofRow (g • v) := by
  rw [rootVec_eq_ofRow, rowLin_eq_smul]

theorem rowLin_rootVec_eq_iff
    (g : J) : rowLin g rootVec = rootVec ↔ g ∈ H := by
  rw [rowLin_rootVec, rootVec_eq_ofRow, ofRow_inj, H_eq_Hj, ← stabilizer_v_eq_Hj,
    mem_stabilizer_iff]

abbrev XOrb : Type := orbit rowGroup rootVec

instance xOrbAction : MulAction J XOrb := MulAction.compHom _ rowLin.rangeRestrict

theorem coe_smul_xOrb (g : J) (x : XOrb) : ((g • x : XOrb) : Fin 112 → ZMod 2) = rowLin g x :=
  rfl

@[expose] def xBase : XOrb := ⟨rootVec, mem_orbit_self rootVec⟩

theorem rowAct_cancel {G' : Type*} [Group G'] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : G' →* (M ≃ₗ[ZMod 2] M)) (g₁ g₂ : G') (v : M) : ρ (g₂ * g₁⁻¹) (ρ g₁ v) = ρ g₂ v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel_right]

instance : IsPretransitive J XOrb := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨k₁, hk₁⟩ := mem_orbit_iff.1 x.2
  obtain ⟨k₂, hk₂⟩ := mem_orbit_iff.1 y.2
  obtain ⟨g₁, hg₁⟩ := MonoidHom.mem_range.1 k₁.2
  obtain ⟨g₂, hg₂⟩ := MonoidHom.mem_range.1 k₂.2
  refine ⟨g₂ * g₁⁻¹, Subtype.ext ?_⟩
  have hx : (x : Fin 112 → ZMod 2) = rowLin g₁ rootVec := by
    rw [← hk₁, hg₁]
    rfl
  have hy : (y : Fin 112 → ZMod 2) = rowLin g₂ rootVec := by
    rw [← hk₂, hg₂]
    rfl
  rw [coe_smul_xOrb, hx, hy]
  exact @rowAct_cancel J (Subgroup.toGroup J) _ _ _ rowLin g₁ g₂ rootVec

theorem smul_xBase_eq_iff
    (g : J) : g • xBase = xBase ↔ g ∈ H := by
  rw [← rowLin_rootVec_eq_iff]
  constructor
  · intro h
    have h1 := Subtype.ext_iff.1 h
    rw [coe_smul_xOrb] at h1
    exact h1
  · intro h
    exact Subtype.ext (by rw [coe_smul_xOrb]; exact h)

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_of_unique {p : ℕ} [Fact p.Prime] (P : Sylow p G) {N H : Subgroup G}
    (hNP : N ≤ P) (huniq : ∀ A : Subgroup G, A ≤ P → (∀ s ∈ (P : Subgroup G), ∀ a ∈ A,
      s * a * s⁻¹ ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = Nat.card N → A = N)
    (hNn : ∀ s ∈ (P : Subgroup G), ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hH : Subgroup.normalizer (N : Set G) = H)
    (α : MulAut G) : ∃ j : G, ∀ h, h ∈ H ↔ j⁻¹ * α h * j ∈ H := by
  have hcardP : Nat.card ((P : Subgroup G).map α.toMonoidHom) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective α.injective, Sylow.card_eq_multiplicity]
  obtain ⟨j, hj⟩ := exists_smul_eq G P (Sylow.ofCard _ hcardP)
  have hPj : ((P : Subgroup G).map α.toMonoidHom) =
      (P : Subgroup G).map (MulAut.conj j).toMonoidHom := by
    have h1 := congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hj
    simp only [Sylow.coe_ofCard] at h1
    rw [← h1, Sylow.coe_subgroup_smul]
    rfl
  set β : MulAut G := (MulAut.conj j)⁻¹ * α with hβ
  have hβapp : ∀ h, β h = j⁻¹ * α h * j := fun h => by
    rw [hβ, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hβP : (P : Subgroup G).map β.toMonoidHom = P := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective β.injective])
    rintro _ ⟨y, hy, rfl⟩
    have h1 : α y ∈ (P : Subgroup G).map (MulAut.conj j).toMonoidHom := by
      rw [← hPj]
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := h1
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    show β y ∈ (P : Subgroup G)
    rw [hβapp, ← hzy]
    rwa [show j⁻¹ * (j * z * j⁻¹) * j = z by group]
  have hβN : N.map β.toMonoidHom = N := by
    refine huniq _ ?_ ?_ ?_ (Subgroup.card_map_of_injective β.injective)
    · rw [← hβP]
      exact Subgroup.map_mono hNP
    · rintro s hs _ ⟨n, hn, rfl⟩
      rw [← hβP] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      refine ⟨t * n * t⁻¹, hNn t ht n hn, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hNc a ha b hb]
  have hβH : H.map β.toMonoidHom = H := by
    rw [← hH, Subgroup.map_equiv_normalizer_eq, hβN]
  refine ⟨j, fun h => ?_⟩
  rw [← hβapp]
  constructor
  · intro hh
    rw [← hβH]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hβH] at hh
    obtain ⟨h', hh', hh'h⟩ := hh
    rwa [β.injective hh'h] at hh'

end Conj

theorem normalizer_H :
    Subgroup.normalizer (H : Set J) = H := by
  have := isSimpleGroup_J j4Facts
  rcases H_isCoatom.le_iff.1 (Subgroup.le_normalizer (H := H)) with h | h
  · exfalso
    have hN : H.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h1 | h1
    · have h2 := card_H
      rw [h1, Subgroup.card_bot] at h2
      norm_num at h2
    · exact H_isCoatom.1 h1
  · exact h

theorem selfNormalizing_xBase :
    SelfNormalizing (G := J) xBase := by
  intro g hg
  rw [smul_xBase_eq_iff]
  have hg' : ∀ h, h ∈ H ↔ g⁻¹ * h * g ∈ H := fun h => by
    rw [← smul_xBase_eq_iff, ← smul_xBase_eq_iff]
    exact hg h
  have h1 : g⁻¹ ∈ Subgroup.normalizer (H : Set J) :=
    Subgroup.mem_normalizer_iff.2 fun h => by rw [inv_inv]; exact hg' h
  rw [normalizer_H] at h1
  exact (H.inv_mem_iff).1 h1

theorem exists_stabConj
    (α : MulAut J) :
    ∃ j, @StabConj J (Subgroup.toGroup J) XOrb _ xBase α j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := exists_conj_of_unique S0Sylow (N := N) (H := H)
    (by rw [S0Sylow_coe]; exact N_le_S0)
    (fun A hAS hAn hAc hcard => R3E_J4_normal_eleven_space_characteristic_in_Sylow_two.2.1 A
      (by rw [← S0Sylow_coe]; exact hAS) (fun s hs a ha => hAn s (by rw [S0Sylow_coe]; exact hs)
        a ha) hAc (by rw [hcard, card_N]; norm_num))
    (fun s hs n hn => conj_mem_N_of_mem_H s (S0_le_H (by rw [← S0Sylow_coe]; exact hs)) n hn)
    N_comm normalizer_N α
  obtain ⟨j, hj⟩ := h
  refine ⟨j, fun h => ?_⟩
  rw [smul_xBase_eq_iff, smul_xBase_eq_iff]
  exact hj h

@[expose] def sigmaX :
    MulAut J →* Equiv.Perm XOrb :=
  @sigmaHom J (Subgroup.toGroup J) XOrb _ _ xBase selfNormalizing_xBase exists_stabConj

theorem sigmaX_equivariant
    (α : MulAut J) (h : J) (x : XOrb) :
    sigmaX α (h • x) = α h • sigmaX α x :=
  @sigmaHom_equivariant J (Subgroup.toGroup J) XOrb _ _ xBase selfNormalizing_xBase
    exists_stabConj α h x

theorem sigmaX_conj
    (g : J) (x : XOrb) :
    sigmaX (@MulAut.conj J (Subgroup.toGroup J) g) x = g • x :=
  @sigmaHom_conj J (Subgroup.toGroup J) XOrb _ _ xBase selfNormalizing_xBase exists_stabConj g x

theorem perm_apply_inv_self {Y : Type*} (f : Equiv.Perm Y) (y : Y) : f (f⁻¹ y) = y :=
  f.apply_symm_apply y

theorem toPermHom_J_eq (g : J) :
    MulAction.toPermHom J XOrb g = MulAction.toPermHom rowGroup XOrb (rowLin.rangeRestrict g) :=
  Equiv.ext fun _ => rfl

theorem sigmaX_mul_toPerm
    (α : MulAut J) (g : J) :
    sigmaX α * MulAction.toPermHom J XOrb g * (sigmaX α)⁻¹ = MulAction.toPermHom J XOrb (α g) := by
  refine Equiv.ext fun x => ?_
  show sigmaX α (g • (sigmaX α)⁻¹ x) = α g • x
  rw [sigmaX_equivariant, perm_apply_inv_self]

theorem sigmaX_mem_normalizer
    (α : MulAut J) :
    sigmaX α ∈ Subgroup.normalizer
      ((MulAction.toPermHom rowGroup XOrb).range : Set (Equiv.Perm XOrb)) := by
  have key : ∀ (β : MulAut J) (π : Equiv.Perm XOrb),
      π ∈ (MulAction.toPermHom rowGroup XOrb).range →
        sigmaX β * π * (sigmaX β)⁻¹ ∈ (MulAction.toPermHom rowGroup XOrb).range := by
    rintro β _ ⟨k, rfl⟩
    obtain ⟨g, rfl⟩ := rowLin.rangeRestrict_surjective k
    rw [← toPermHom_J_eq, sigmaX_mul_toPerm, toPermHom_J_eq]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro π
  refine ⟨key α π, fun h => ?_⟩
  have h2 := key α⁻¹ _ h
  rw [map_inv, inv_inv, show (sigmaX α)⁻¹ * (sigmaX α * π * (sigmaX α)⁻¹) * sigmaX α = π by
    group] at h2
  exact h2

theorem rowLin_spanWord (i : Fin 112) :
    toVecD 112 (spanRows[i.val]?.getD 0) = rowLin (signedWord a b spanWords[i.val]!) rootVec := by
  have hi : spanRows[i.val]?.getD 0 = vecMulN 112 (wordP An Bn spanWords[i.val]!).2 rootBits := by
    unfold spanRows
    simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  have hrep : rowsMatrix 112 (wordP An Bn spanWords[i.val]!).2 =
      φ (signedWord a b spanWords[i.val]!)⁻¹ :=
    (rep_wordP (rep_a matFacts) (rep_b matFacts) spanWords[i.val]!).2.2.2
  rw [hi, SmallF2.toVecD_vecMulN, rowLin_apply, hrep, φ_apply, Subgroup.coe_inv]
  rfl

theorem span_orbit :
    Submodule.span (ZMod 2) (orbit rowGroup rootVec) = ⊤ := by
  have hW : ∀ i : Fin 112, (rowsMatrix 112 spanRows) i ∈ orbit rowGroup rootVec := by
    intro i
    have e : (rowsMatrix 112 spanRows) i = toVecD 112 (spanRows[i.val]?.getD 0) := rfl
    rw [e, rowLin_spanWord]
    exact ⟨⟨rowLin _, ⟨_, rfl⟩⟩, rfl⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x ᵥ* rowsMatrix 112 spanInvRows) ᵥ* rowsMatrix 112 spanRows := by
    rw [Matrix.vecMul_vecMul, ← SmallF2.rowsMatrix_mulRows, span_check,
      SmallF2.rowsMatrix_idRows, Matrix.vecMul_one]
  rw [hx, Matrix.vecMul_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hW i))

theorem rowGroup_smul (k : rowGroup) (v : Fin 112 → ZMod 2) :
    k • v = (k : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) v := rfl

theorem stab_smul (k : stabilizer rowGroup rootVec) (v : Fin 112 → ZMod 2) :
    k • v = ((k : rowGroup) : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) v := rfl

theorem ofRow_injective : Function.Injective ofRow := fun _ _ h => ofRow_inj.1 h

theorem orbit_stab_ofRow
    (x : Row) :
    orbit (stabilizer rowGroup rootVec) (ofRow x) = ofRow '' orbit H x := by
  ext y
  constructor
  · rintro ⟨⟨⟨_, ⟨g, rfl⟩⟩, hs⟩, rfl⟩
    have hs' := mem_stabilizer_iff.1 hs
    rw [rowGroup_smul] at hs'
    have hg : g ∈ H := (rowLin_rootVec_eq_iff g).1 hs'
    refine ⟨g • x, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    dsimp only
    rw [stab_smul, rowLin_eq_smul]
  · rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    have hs : (⟨rowLin h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩ : rowGroup) ∈
        stabilizer rowGroup rootVec := by
      rw [mem_stabilizer_iff, rowGroup_smul]
      exact (rowLin_rootVec_eq_iff h).2 hh
    refine ⟨⟨⟨rowLin h, MonoidHom.mem_range.2 ⟨h, rfl⟩⟩, hs⟩, ?_⟩
    dsimp only
    rw [stab_smul, Subgroup.mk_smul, rowLin_eq_smul]

theorem subdegrees_distinct :
    ∀ y ∈ orbit rowGroup rootVec, ∀ y' ∈ orbit rowGroup rootVec,
    Nat.card (orbit (stabilizer rowGroup rootVec) y) =
        Nat.card (orbit (stabilizer rowGroup rootVec) y') →
      orbit (stabilizer rowGroup rootVec) y = orbit (stabilizer rowGroup rootVec) y' := by
  intro y hy y' hy' h
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hy
  obtain ⟨⟨_, ⟨g', rfl⟩⟩, rfl⟩ := hy'
  change orbit _ (rowLin g rootVec) = orbit _ (rowLin g' rootVec)
  change Nat.card (orbit _ (rowLin g rootVec)) = Nat.card (orbit _ (rowLin g' rootVec)) at h
  rw [rowLin_rootVec, rowLin_rootVec, orbit_stab_ofRow, orbit_stab_ofRow] at h ⊢
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ ofRow_injective,
    Set.ncard_image_of_injective _ ofRow_injective] at h
  rw [orbit_H_eq_of_ncard_row ⟨g, rfl⟩ ⟨g', rfl⟩ h]

theorem exists_isometry
    (α : MulAut J) :
    ∃ L : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2),
      L ∈ TauCeti.QuadraticMap.orthogonalGroup jq ∧ ∀ x : XOrb, L x = sigmaX α x := by
  obtain ⟨L, hL, hLx, -⟩ :=
    (CFSG.LinearAlgebra.distinct_subdegrees_spanning_orbit_linearizes_normalizer jq
      jq_nondegenerate rowGroup_le_orthogonal span_orbit subdegrees_distinct (sigmaX α)
      (sigmaX_mem_normalizer α)).2
  exact ⟨L, hL, hLx⟩

@[expose] def isoL
    (α : MulAut J) : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2) :=
  Classical.choose (exists_isometry α)

theorem isoL_mem
    (α : MulAut J) : isoL α ∈ TauCeti.QuadraticMap.orthogonalGroup jq :=
  (Classical.choose_spec (exists_isometry α)).1

theorem isoL_apply
    (α : MulAut J) (x : XOrb) : isoL α x = sigmaX α x :=
  (Classical.choose_spec (exists_isometry α)).2 x

theorem linearMap_ext_X
    {f g : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)}
    (h : ∀ x : XOrb, f x = g x) : f = g :=
  LinearMap.ext_on span_orbit fun x hx => h ⟨x, hx⟩

theorem linearEquiv_ext_X
    {f g : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)}
    (h : ∀ x : XOrb, f x = g x) : f = g :=
  LinearEquiv.toLinearMap_injective (linearMap_ext_X h)

@[expose] def isoHom :
       MulAut J →* ((Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) where
  toFun := isoL
  map_one' := linearEquiv_ext_X fun x => by rw [isoL_apply, map_one]; rfl
  map_mul' α β := linearEquiv_ext_X fun x => by
    rw [LinearEquiv.mul_apply, isoL_apply, isoL_apply, isoL_apply, map_mul]
    rfl

theorem isoHom_apply
    (α : MulAut J) (x : XOrb) : isoHom α x = sigmaX α x := isoL_apply α x

theorem isoHom_inv_apply
    (α : MulAut J) (x : XOrb) : (isoHom α)⁻¹ x = (sigmaX α)⁻¹ x := by
  rw [← map_inv, isoHom_apply, map_inv]

theorem isoHom_conj
    (g : J) : isoHom (@MulAut.conj J (Subgroup.toGroup J) g) = rowLin g :=
  linearEquiv_ext_X fun x => by rw [isoHom_apply, sigmaX_conj, coe_smul_xOrb]

theorem rowLin_aut
    (α : MulAut J) (h : J) :
    rowLin (α h) = isoHom α * rowLin h * (isoHom α)⁻¹ :=
  linearEquiv_ext_X fun x => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, isoHom_inv_apply, ← coe_smul_xOrb h,
      isoHom_apply, sigmaX_equivariant, perm_apply_inv_self, coe_smul_xOrb]

theorem isoHom_injective :
       Function.Injective isoHom := by
  refine (injective_iff_map_eq_one _).2 fun α hα => MulEquiv.ext fun h => ?_
  have e := rowLin_aut α h
  rw [hα, one_mul, inv_one, mul_one] at e
  exact rowLin_injective e

theorem isoHom_mem
    (α : MulAut J) : isoHom α ∈ TauCeti.QuadraticMap.orthogonalGroup jq :=
  isoL_mem α

section RowMat

variable {R : Type*} [CommRing R] {m : ℕ}

@[expose] def rowMat (L : (Fin m → R) →ₗ[R] (Fin m → R)) : Matrix (Fin m) (Fin m) R :=
  (LinearMap.toMatrix' L)ᵀ

theorem vecMul_rowMat (L : (Fin m → R) →ₗ[R] (Fin m → R)) (w : Fin m → R) :
    w ᵥ* rowMat L = L w := by
  rw [rowMat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]

theorem matrix_ext_vecMul {A B : Matrix (Fin m) (Fin m) R} (h : ∀ w, w ᵥ* A = w ᵥ* B) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single i 1)) j
  rwa [Matrix.single_vecMul, Matrix.single_vecMul, one_smul, one_smul, Matrix.row_apply,
    Matrix.row_apply] at this

@[expose] def toGL (L : (Fin m → R) ≃ₗ[R] (Fin m → R)) : GL (Fin m) R where
  val := rowMat L.symm.toLinearMap
  inv := rowMat L.toLinearMap
  val_inv := matrix_ext_vecMul fun w => by
    rw [← Matrix.vecMul_vecMul, vecMul_rowMat, vecMul_rowMat, Matrix.vecMul_one,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  inv_val := matrix_ext_vecMul fun w => by
    rw [← Matrix.vecMul_vecMul, vecMul_rowMat, vecMul_rowMat, Matrix.vecMul_one,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem vecMul_toGL (L : (Fin m → R) ≃ₗ[R] (Fin m → R)) (w : Fin m → R) :
    w ᵥ* ((toGL L : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = L.symm w :=
  vecMul_rowMat _ w

theorem vecMul_toGL_inv (L : (Fin m → R) ≃ₗ[R] (Fin m → R)) (w : Fin m → R) :
    w ᵥ* (((toGL L)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = L w :=
  vecMul_rowMat _ w

@[expose] def toGLHom : ((Fin m → R) ≃ₗ[R] (Fin m → R)) →* GL (Fin m) R where
  toFun := toGL
  map_one' := Units.ext (matrix_ext_vecMul fun w => by
    rw [vecMul_toGL, Units.val_one, Matrix.vecMul_one]
    rfl)
  map_mul' L₁ L₂ := Units.ext (matrix_ext_vecMul fun w => by
    rw [vecMul_toGL, Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_toGL, vecMul_toGL]
    rfl)

theorem toGLHom_rowAct (g : GL (Fin m) R) : toGLHom (rowAct (MonoidHom.id _) g) = g :=
  Units.ext (matrix_ext_vecMul fun w => by
    rw [show toGLHom (rowAct (MonoidHom.id _) g) = toGL (rowAct (MonoidHom.id _) g) from rfl,
      vecMul_toGL]
    rfl)

theorem rowAct_toGLHom (L : (Fin m → R) ≃ₗ[R] (Fin m → R)) :
    rowAct (MonoidHom.id _) (toGLHom L) = L :=
  LinearEquiv.ext fun w => by
    rw [rowAct_apply, MonoidHom.id_apply]
    exact vecMul_toGL_inv L w

theorem toGLHom_injective : Function.Injective (toGLHom (R := R) (m := m)) :=
  Function.LeftInverse.injective rowAct_toGLHom

end RowMat

theorem rowLin_eq_rowAct (g : J) :
    rowLin g = rowAct (MonoidHom.id (GL (Fin 112) (ZMod 2))) (g : GL (Fin 112) (ZMod 2)) :=
  LinearEquiv.ext fun w => by rw [rowLin_apply, rowAct_apply, MonoidHom.id_apply]

@[expose] def autRep :
       MulAut J →* GL (Fin 112) (ZMod 2) := toGLHom.comp isoHom

theorem autRep_conj
    (g : J) :
    autRep (@MulAut.conj J (Subgroup.toGroup J) g) = (g : GL (Fin 112) (ZMod 2)) := by
  rw [autRep, MonoidHom.comp_apply, isoHom_conj, rowLin_eq_rowAct, toGLHom_rowAct]

theorem autRep_aut
    (α : MulAut J) (h : J) :
    ((α h : J) : GL (Fin 112) (ZMod 2)) = autRep α * h * (autRep α)⁻¹ := by
  have e := congrArg toGLHom (rowLin_aut α h)
  rw [rowLin_eq_rowAct, toGLHom_rowAct, map_mul, map_mul, map_inv, rowLin_eq_rowAct,
    toGLHom_rowAct] at e
  exact e

theorem autRep_injective :
       Function.Injective autRep :=
  toGLHom_injective.comp isoHom_injective

theorem jq_vecMul_autRep
    (α : MulAut J) (v : Fin 112 → ZMod 2) :
    jq (v ᵥ* ((autRep α : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))) =
      jq v := by
  rw [autRep, MonoidHom.comp_apply, show toGLHom (isoHom α) = toGL (isoHom α) from rfl,
    vecMul_toGL]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
    ((TauCeti.QuadraticMap.orthogonalGroup jq).inv_mem (isoHom_mem α)) v

theorem R3E_J4_all_automorphisms_realized_by_binary_isometries :
    ∃ ρ : MulAut J →* GL (Fin 112) (ZMod 2), Function.Injective ρ ∧
      (∀ α : MulAut J, ∀ v : Fin 112 → ZMod 2,
        jq (v ᵥ* ((ρ α : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))) =
          jq v) ∧
      (∀ g : J, ρ (@MulAut.conj J (Subgroup.toGroup J) g) = (g : GL (Fin 112) (ZMod 2))) ∧
      ∀ (α : MulAut J) (h : J), ((α h : J) : GL (Fin 112) (ZMod 2)) = ρ α * h * (ρ α)⁻¹ :=
  ⟨autRep, autRep_injective, jq_vecMul_autRep, autRep_conj, autRep_aut⟩

end CFSG.Sporadic.J4Schreier
