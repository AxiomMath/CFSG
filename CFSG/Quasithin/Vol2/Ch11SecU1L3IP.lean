module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IO
public import CFSG.Quasithin.Vol2.Ch11SecU1L3ID
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IR
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IL
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IM
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IN

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_centralizer_of_inf {L : Subgroup G} (hAS : SecE3.AlmostSimple L)
    {Y : Subgroup G} (hCs : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G))) :
    Group.IsSolvable ↥(Subgroup.centralizer (Y : Set G)) := by
  have := hAS.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (Y : Set G)
  have : Group.IsNilpotent (G ⧸ L) := hAS.isPGroup_quotient.isNilpotent
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_right : L ⊓ C ≤ C))
    ((QuotientGroup.mk' L).comp C.subtype) fun x hx => ?_
  have hxL : (x : G) ∈ L := (QuotientGroup.eq_one_iff _).mp hx
  exact ⟨⟨x, hxL, x.2⟩, rfl⟩

omit [Finite G] in
theorem exists_hom_pgl2_centralizer {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {y : G}
    {Y : Subgroup G} (hYC : Y ≤ Subgroup.centralizer ({y} : Set G))
    (hYn : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (e : ↥Y ≃* SL(2, ZMod p)) :
    ∃ φ : ↥(Subgroup.centralizer ({y} : Set G)) →* PGL2 (ZMod p),
      (∀ h ∈ φ.ker, (h : G) ∈ Subgroup.centralizer (Y : Set G)) ∧
      (Y.subgroupOf (Subgroup.centralizer ({y} : Set G))).map φ = pslRange (ZMod p) ∧
      ∀ h, φ h ∈ pslRange (ZMod p) → ∃ s ∈ Y, s⁻¹ * (h : G) ∈ Subgroup.centralizer (Y : Set G) := by
  set C := Subgroup.centralizer ({y} : Set G) with hC
  have : (Y.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYn
  have := zmod_ringEquiv_subsingleton p
  let e' : ↥(Y.subgroupOf C) ≃* SL(2, ZMod p) := (Subgroup.subgroupOfEquivOfLe hYC).trans e
  obtain ⟨φ, hker, hmap, hpsl⟩ := exists_hom_pgl2_of_normal_sl2
    (isOddPrimePower_zmod (by omega)) (by rw [Nat.card_zmod]; omega) (Y.subgroupOf C) e'
  have hcen : ∀ h : ↥C, h ∈ Subgroup.centralizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) →
      (h : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro s hs
    exact congrArg Subtype.val (hh ⟨s, hYC hs⟩ (Subgroup.mem_subgroupOf.mpr hs))
  refine ⟨φ, fun h hh => hcen h (hker hh), hmap, fun h hh => ?_⟩
  obtain ⟨s, hs, hsc⟩ := hpsl h hh
  exact ⟨s, Subgroup.mem_subgroupOf.mp hs, hcen _ hsc⟩

theorem nParam_centralizer_le_one_of_sl2
    {L : Subgroup G} (hAS : SecE3.AlmostSimple L) {p : ℕ}
    [Fact p.Prime] (hp7 : 7 ≤ p) {y : G} {Y : Subgroup G}
    (hYC : Y ≤ Subgroup.centralizer ({y} : Set G))
    (hYn : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (e : ↥Y ≃* SL(2, ZMod p)) (hCs : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G))) :
    nParam (Subgroup.centralizer ({y} : Set G)) ≤ 1 := by
  set C := Subgroup.centralizer ({y} : Set G) with hC
  obtain ⟨φ, hker, hmap, -⟩ := exists_hom_pgl2_centralizer (by omega) hYC hYn e
  have hCY := isSolvable_centralizer_of_inf hAS hCs
  have hks : Group.IsSolvable ↥φ.ker := by
    let f : ↥φ.ker →* ↥(Subgroup.centralizer (Y : Set G)) :=
      (C.subtype.comp φ.ker.subtype).codRestrict _ fun k => hker k k.2
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h0)
  have hrange : pslRange (ZMod p) ≤ φ.range := by
    rw [← hmap]
    exact Subgroup.map_le_range _ _
  have hQ : nParam (⊤ : Subgroup (↥C ⧸ φ.ker)) ≤ 1 := by
    rw [E1.Eleven.nParam_top_mulEquiv (QuotientGroup.quotientKerEquivRange φ),
      ← nParam_subgroupOf]
    exact nParam_le_one_of_pslRange_le hp7 hrange
  rw [nParam_subgroupOf]
  exact nParam_le_one_of_quotient hks hQ

theorem sl2_center_mul_self {F : Type} [Field F] {A : SL(2, F)}
    (hA : A ∈ Subgroup.center SL(2, F)) : A * A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrA, ← map_mul, ← pow_two, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem inner_torus_of_sl2 {L : Subgroup G} {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {y : G}
    {Y : Subgroup G} (hYL : Y ≤ L) (hYC : Y ≤ Subgroup.centralizer ({y} : Set G))
    (hYn : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (e : ↥Y ≃* SL(2, ZMod p)) {x : G} (hxL : x ∈ L) (hx2 : orderOf x = 2) (hxy : x * y = y * x)
    (hxY : ∀ s ∈ Y, ∀ c ∈ L ⊓ Subgroup.centralizer (Y : Set G), x ≠ s * c)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧ ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
  set C := Subgroup.centralizer ({y} : Set G) with hC
  obtain ⟨φ, hker, hmap, hpsl⟩ := exists_hom_pgl2_centralizer hp5 hYC hYn e
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hxy
  set x' : ↥C := ⟨x, hxC⟩ with hx'
  have hYCn : (Y.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYn
  have hφx2 : φ x' ^ 2 = 1 := by
    rw [← map_pow]
    have : x' ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx2, pow_orderOf_eq_one])
    rw [this, map_one]
  have hφxJ : φ x' ∉ pslRange (ZMod p) := by
    intro h
    obtain ⟨s, hs, hsc⟩ := hpsl x' h
    exact hxY s hs (s⁻¹ * x) ⟨L.mul_mem (L.inv_mem (hYL hs)) hxL, hsc⟩ (by group)
  set Q' := Q.subgroupOf C with hQ'def
  have hQ' : IsPGroup 2 ↥(Q'.map φ) :=
    (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe (hQC.trans inf_le_right)).symm).map φ
  have hQ'C : Q'.map φ ≤ Subgroup.centralizer ({φ x'} : Set (PGL2 (ZMod p))) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hQC (Subgroup.mem_subgroupOf.mp hq)).1)
  obtain ⟨Pbar, hPJ, hPp, hP2, hQN, hPx⟩ := exists_odd_torus_of_outer_involution
    (isOddPrimePower_zmod (by omega)) (by rw [Nat.card_zmod]; omega) hφx2 hφxJ hQ' hQ'C
  have hcen : ∀ k ∈ Y.subgroupOf C, φ k = 1 → ∀ y' ∈ Y.subgroupOf C, k * y' = y' * k := by
    intro k _ hk y' hy'
    have h1 := Subgroup.mem_centralizer_iff.mp (hker k hk) y' (Subgroup.mem_subgroupOf.mp hy')
    exact Subtype.ext h1.symm
  have h2 : ∀ k ∈ Y.subgroupOf C, φ k = 1 → k * k = 1 := by
    intro k hkY hk
    have hkY' : (k : G) ∈ Y := Subgroup.mem_subgroupOf.mp hkY
    have hcomm : ∀ s : ↥Y, (⟨k, hkY'⟩ : ↥Y) * s = s * ⟨k, hkY'⟩ := fun s => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hker k hk) s s.2).symm
    have hZ : e ⟨k, hkY'⟩ ∈ Subgroup.center SL(2, ZMod p) := by
      rw [Subgroup.mem_center_iff]
      intro B
      obtain ⟨b, rfl⟩ := e.surjective B
      rw [← map_mul, ← map_mul, hcomm b]
    have h3 := sl2_center_mul_self hZ
    rw [← map_mul] at h3
    have h4 : (⟨k, hkY'⟩ : ↥Y) * ⟨k, hkY'⟩ = 1 := e.injective (by rw [h3, map_one])
    have h5 := congrArg Subtype.val h4
    exact Subtype.ext h5
  obtain ⟨P, -, hPcard, hPmap, hPN⟩ := exists_lift_odd_prime φ hcen h2 hPp hP2
    (by rw [hmap]; exact hPJ)
  have hcardP : Nat.card (P.map C.subtype) = Nat.card Pbar := by
    rw [← hPcard]
    exact Subgroup.card_map_of_injective C.subtype_injective
  refine ⟨P.map C.subtype, hcardP ▸ hPp, hcardP ▸ hP2, fun q hq => ?_, fun hle => hPx ?_⟩
  · have hqC : q ∈ C := (hQC hq).2
    have hqN := hPN ⟨q, hqC⟩ (by rw [Subgroup.normalizer_eq_top_iff.mpr hYCn]; trivial)
      (hQN ⟨⟨q, hqC⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩)
    have hsub : (P.map C.subtype).subgroupOf C = P :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective P
    exact mem_normalizer_of_subgroupOf (V := P.map C.subtype) (J := C)
      (Subgroup.map_subtype_le P) (n := ⟨q, hqC⟩) (by rw [hsub]; exact hqN)
  · rw [← hPmap]
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨r, hr, rfl⟩))

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
