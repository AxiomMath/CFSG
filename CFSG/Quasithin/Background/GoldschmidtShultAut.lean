module

public import CFSG.Quasithin.Background.GoldschmidtShultBender
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.GoldschmidtShultLink

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def autStab (K : Type*) [Group K] (W : Subgroup K) : Subgroup (MulAut K) where
  carrier := {α | ∀ x, x ∈ W ↔ α x ∈ W}
  mul_mem' := fun {α β} hα hβ x => (hβ x).trans (hα (β x))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := by
    intro α hα x
    have h1 := hα (α⁻¹ x)
    have h2 : α (α⁻¹ x) = x := by simp
    rw [h2] at h1
    exact h1.symm

theorem conj_mem_autStab {K : Type*} [Group K] {W : Subgroup K} {k : K}
    (hk : k ∈ Subgroup.normalizer (W : Set K)) : MulAut.conj k ∈ autStab K W := fun x => by
  simpa [MulAut.conj_apply] using Subgroup.mem_normalizer_iff.mp hk x

theorem isSolvable_autStab {K : Type}
    [Group K] [Finite K] (hK : fusionIsBenderGroup K) {W : Subgroup K} (hW : W ≠ ⊥)
    (hW2 : IsPGroup 2 W) : Group.IsSolvable (autStab K W) := by
  have hN := isSolvable_normalizer_of_bender hK hW hW2
  have hO := isSolvable_outer_of_bender hK
  let f : ↥(Subgroup.normalizer (W : Set K)) →* ↥(autStab K W) :=
    { toFun := fun k => ⟨MulAut.conj (k : K), conj_mem_autStab k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  let g : ↥(autStab K W) →* Outer K :=
    (QuotientGroup.mk' (inner K)).comp (autStab K W).subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro α hα
  have hin : (α : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.mp hα)
  obtain ⟨k, hk⟩ := hin
  have hkN : k ∈ Subgroup.normalizer (W : Set K) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    have := α.2 x
    rw [← hk] at this
    simpa [MulAut.conj_apply] using this
  exact ⟨⟨k, hkN⟩, Subtype.ext hk⟩

@[expose] noncomputable def autQuot (X : Type*) [Group X] (Z : Subgroup X) [Z.Characteristic] :
    MulAut X →* MulAut (X ⧸ Z) where
  toFun φ := QuotientGroup.congr Z Z φ (Subgroup.characteristic_iff_map_eq.mp ‹_› φ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

@[expose] noncomputable def actK {G : Type*} [Group G] (L : Subgroup G) [L.Normal] :
    G →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  (autQuot ↥L (Subgroup.center ↥L)).comp MulAut.conjNormal

theorem actK_mk {G : Type*} [Group G] (L : Subgroup G) [L.Normal] (m : G) (x : ↥L) :
    actK L m (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal m x) :=
  rfl

theorem isSolvable_quotient_of_bender_hull
    {G : Type} [Group G] [Finite G] {M V L : Subgroup G} [L.Normal]
    (hM : Subgroup.normalizer (V : Set G) = M) (hVL : V ≤ L) (hV : V ≠ ⊥)
    (hVel : IsElemAbelian 2 V) (hH : IsBenderHull L)
    [((Subgroup.centralizer (V : Set G)).subgroupOf M).Normal] :
    Group.IsSolvable (↥M ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf M) := by
  set Z := Subgroup.center ↥L with hZ
  have hZodd : Odd (Nat.card Z) := by
    rw [hZ, hH.2.1]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  let π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  let Vb : Subgroup (↥L ⧸ Z) := (V.subgroupOf L).map π
  have hxsq : ∀ x ∈ V.subgroupOf L, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (hVel.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))
  have hVb2 : IsPGroup 2 Vb := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hxy, ← map_pow, hxsq x hx, map_one]
  have hVb : Vb ≠ ⊥ := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
    intro hbot
    have hxV : (⟨v, hVL hv⟩ : ↥L) ∈ V.subgroupOf L := Subgroup.mem_subgroupOf.mpr hv
    have hmem : π ⟨v, hVL hv⟩ ∈ Vb := Subgroup.mem_map_of_mem π hxV
    rw [hbot, Subgroup.mem_bot] at hmem
    have hz : (⟨v, hVL hv⟩ : ↥L) ∈ Z := (QuotientGroup.eq_one_iff _).1 hmem
    have hone := eq_one_of_mem_odd hZodd hz ⟨1, by simpa using hxsq _ hxV⟩
    have hvone : v = 1 := congrArg (fun y : ↥L => (y : G)) hone
    exact hv1 (Subtype.ext hvone)
  have hSolv := isSolvable_autStab hH.2.2 hVb hVb2
  have hmap : ∀ m ∈ Subgroup.normalizer (V : Set G), ∀ y ∈ Vb, actK L m y ∈ Vb := by
    intro m hm y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨MulAut.conjNormal m x, ?_, rfl⟩
    change MulAut.conjNormal m x ∈ V.subgroupOf L
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp hm x).mp (Subgroup.mem_subgroupOf.mp hx)
  have hstab : ∀ m ∈ M, actK L m ∈ autStab (↥L ⧸ Z) Vb := by
    intro m hm y
    rw [← hM] at hm
    refine ⟨hmap m hm y, fun hy => ?_⟩
    have h1 := hmap m⁻¹ ((Subgroup.normalizer (V : Set G)).inv_mem hm) _ hy
    have h2 : (actK L m⁻¹) ((actK L m) y) = y := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rwa [h2] at h1
  let ρ : ↥M →* ↥(autStab (↥L ⧸ Z) Vb) :=
    ((actK L).comp M.subtype).codRestrict (autStab (↥L ⧸ Z) Vb) (fun m => hstab m m.2)
  have hker : ρ.ker ≤ (Subgroup.centralizer (V : Set G)).subgroupOf M := by
    intro m hm
    have hρ : actK L (m : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro v hv
    have hmv : (m : G) * v * (m : G)⁻¹ ∈ V := by
      have hm' : (m : G) ∈ Subgroup.normalizer (V : Set G) := hM ▸ m.2
      exact (Subgroup.mem_normalizer_iff.mp hm' v).mp hv
    let x : ↥L := ⟨v, hVL hv⟩
    let x' : ↥L := ⟨(m : G) * v * (m : G)⁻¹, hVL hmv⟩
    have hxx' : (QuotientGroup.mk x : ↥L ⧸ Z) = QuotientGroup.mk x' := by
      have := actK_mk L (m : G) x
      rw [hρ, MulAut.one_apply] at this
      exact this
    have hzmem : x⁻¹ * x' ∈ Z := QuotientGroup.eq.1 hxx'
    have hx2 : x ^ 2 = 1 := Subtype.ext (hVel.2 v hv)
    have hx'2 : x' ^ 2 = 1 := Subtype.ext (hVel.2 _ hmv)
    have hcomm : x * (x⁻¹ * x') = (x⁻¹ * x') * x := Subgroup.mem_center_iff.mp hzmem x
    have hz2 : (x⁻¹ * x') ^ 2 = 1 := by
      have e1 : x' = x * (x⁻¹ * x') := by group
      have e2 : x' ^ 2 = x ^ 2 * (x⁻¹ * x') ^ 2 := by
        conv_lhs => rw [e1]
        rw [sq, sq, sq, mul_assoc, ← mul_assoc (x⁻¹ * x') x, ← hcomm, mul_assoc, mul_assoc,
          ← mul_assoc x⁻¹]
        group
      rw [hx'2, hx2, one_mul] at e2
      exact e2.symm
    have hz1 : x⁻¹ * x' = 1 := eq_one_of_mem_odd hZodd hzmem ⟨1, by simpa using hz2⟩
    have hxe : x' = x := by
      have := mul_left_cancel (a := x⁻¹) (by simpa using hz1 : x⁻¹ * x' = x⁻¹ * x)
      exact this
    have hvv : (m : G) * v * (m : G)⁻¹ = v := congrArg Subtype.val hxe
    calc v * (m : G) = ((m : G) * v * (m : G)⁻¹) * (m : G) := by rw [hvv]
      _ = (m : G) * v := by group
  have : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have : Group.IsSolvable ↥(autStab (↥L ⧸ Z) Vb) := hSolv
  have : Group.IsSolvable ρ.range := inferInstance
  have hsolvM : Group.IsSolvable (↥M ⧸ ρ.ker) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange ρ).symm.surjective
  refine Group.isSolvable_of_surjective (f := QuotientGroup.map ρ.ker
    ((Subgroup.centralizer (V : Set G)).subgroupOf M) (MonoidHom.id _) hker) ?_
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk m, rfl⟩

end CFSG.Quasithin.Shult
