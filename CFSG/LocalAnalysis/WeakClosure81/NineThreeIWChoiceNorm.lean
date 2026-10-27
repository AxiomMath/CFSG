module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Timmesfeld75.Dihedral
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeModule
public import CFSG.Quasithin.EmptyFaithful.S151S5A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] noncomputable def nine3ConjHom (I : Subgroup G) {u : G}
    (hu : u ∈ Subgroup.normalizer (I : Set G)) : ↥I →* ↥I where
  toFun v := ⟨u * (v : G) * u⁻¹,
    (Subgroup.mem_normalizer_iff.mp hu (v : G)).mp v.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc]

@[expose] noncomputable def nine3Norm (I P : Subgroup G) [IsMulCommutative ↥I]
    [Fintype ↥P] (hP : P ≤ Subgroup.normalizer (I : Set G)) : ↥I →* ↥I where
  toFun v := ∏ g : ↥P, ⟨(g : G) * (v : G) * (g : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hP g.2) (v : G)).mp v.2⟩
  map_one' := Finset.prod_eq_one fun g _ => Subtype.ext (by simp)
  map_mul' v w := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => Subtype.ext ?_
    simp [mul_assoc]

theorem nine3Norm_conj {I P : Subgroup G} [IsMulCommutative ↥I] [Fintype ↥P]
    (hP : P ≤ Subgroup.normalizer (I : Set G)) {h : G} (hh : h ∈ P) (v : ↥I)
    (hv : h * (v : G) * h⁻¹ ∈ I) :
    nine3Norm I P hP ⟨h * (v : G) * h⁻¹, hv⟩ = nine3Norm I P hP v := by
  change (∏ g : ↥P, (⟨(g : G) * (h * (v : G) * h⁻¹) * (g : G)⁻¹, _⟩ : ↥I)) =
    ∏ g : ↥P, (⟨(g : G) * (v : G) * (g : G)⁻¹, _⟩ : ↥I)
  refine Fintype.prod_equiv (Equiv.mulRight ⟨h, hh⟩) _ _ (fun g => ?_)
  apply Subtype.ext
  simp [mul_assoc]

theorem nine3Norm_equivariant {I P : Subgroup G} [IsMulCommutative ↥I] [Fintype ↥P]
    (hP : P ≤ Subgroup.normalizer (I : Set G)) {u : G}
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (huI : u ∈ Subgroup.normalizer (I : Set G)) (v : ↥I) :
    nine3Norm I P hP
        ⟨u * (v : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp huI (v : G)).mp v.2⟩ =
      nine3ConjHom I huI (nine3Norm I P hP v) := by
  let e : ↥P ≃ ↥P := (MulAut.conj u⁻¹).toEquiv.subtypeEquiv
    (fun g : G => Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huP) g)
  have he_apply : ∀ g : ↥P, ((e g : ↥P) : G) = u⁻¹ * (g : G) * u := by
    intro g
    simp [e, MulAut.conj_apply]
  change (∏ g : ↥P, (⟨(g : G) * (u * (v : G) * u⁻¹) * (g : G)⁻¹, _⟩ : ↥I)) =
    nine3ConjHom I huI (∏ g : ↥P, (⟨(g : G) * (v : G) * (g : G)⁻¹, _⟩ : ↥I))
  rw [map_prod]
  refine Fintype.prod_equiv e _ _ (fun g => ?_)
  apply Subtype.ext
  dsimp only [nine3ConjHom, MonoidHom.coe_mk, OneHom.coe_mk, MulHom.coe_mk]
  change (g : G) * (u * (v : G) * u⁻¹) * (g : G)⁻¹ =
    u * (((e g : ↥P) : G) * (v : G) * (((e g : ↥P) : G))⁻¹) * u⁻¹
  rw [he_apply g]
  group

theorem nine3Norm_range_le_centralizer {I P : Subgroup G} [IsMulCommutative ↥I]
    [Fintype ↥P] (hP : P ≤ Subgroup.normalizer (I : Set G)) :
    (nine3Norm I P hP).range ≤
      (Subgroup.centralizer (P : Set G) ⊓ I).subgroupOf I := by
  rintro x ⟨v, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ⟨?_, (nine3Norm I P hP v).2⟩
  change (nine3Norm I P hP v : G) ∈ Subgroup.centralizer (P : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have heq := nine3Norm_equivariant hP (P.le_normalizer hh) (hP hh) v
  have h2 := nine3Norm_conj hP hh v
    ((Subgroup.mem_normalizer_iff.mp (hP hh) (v : G)).mp v.2)
  have h4 : nine3ConjHom I (hP hh) (nine3Norm I P hP v) = nine3Norm I P hP v := by
    rw [← heq, h2]
  have h3 : h * (nine3Norm I P hP v : G) * h⁻¹ = (nine3Norm I P hP v : G) := by
    simpa [nine3ConjHom] using congrArg Subtype.val h4
  calc h * (nine3Norm I P hP v : G) = (h * (nine3Norm I P hP v : G) * h⁻¹) * h := by
        group
    _ = (nine3Norm I P hP v : G) * h := by rw [h3]

theorem nine3Norm_of_centralizer {I P : Subgroup G} [IsMulCommutative ↥I]
    [Fintype ↥P] (hP : P ≤ Subgroup.normalizer (I : Set G))
    (hPcard : Nat.card ↥P = p) (hpodd : Odd p) (v : ↥I)
    (hv : ∀ g ∈ P, g * (v : G) = (v : G) * g) (hv2 : (v : G) * (v : G) = 1) :
    (nine3Norm I P hP v : G) = (v : G) := by
  have hprod : nine3Norm I P hP v = v ^ Fintype.card ↥P := by
    change (∏ g : ↥P, (⟨(g : G) * (v : G) * (g : G)⁻¹, _⟩ : ↥I)) =
      v ^ (Finset.univ : Finset ↥P).card
    rw [← Finset.prod_const (s := (Finset.univ : Finset ↥P)) v]
    refine Finset.prod_congr rfl fun g _ => ?_
    apply Subtype.ext
    simp [hv g g.2]
  have hcard : Fintype.card ↥P = p := by
    rw [← Nat.card_eq_fintype_card]; exact hPcard
  have hv2' : v ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hv2
  obtain ⟨k, hk⟩ := hpodd
  have hval : v ^ Fintype.card ↥P = v := by
    rw [hcard, hk, pow_succ, pow_mul, hv2', one_pow, one_mul]
  rw [hprod, hval]

theorem nine3Norm_range_le_of_image_le {I P : Subgroup G} [IsMulCommutative ↥I] [Fintype ↥P]
    (hP : P ≤ Subgroup.normalizer (I : Set G)) {ι : Type*} (S : ι → Subgroup G)
    (hS : ∀ i, S i ≤ I) (hIeq : I = ⨆ i, S i)
    {H : Subgroup ↥I}
    (himg : ∀ i, ((S i).subgroupOf I).map (nine3Norm I P hP) ≤ H) :
    (nine3Norm I P hP).range ≤ H := by
  let C : G → Prop := fun x => x ∈ I ∧ ∀ hx : x ∈ I,
    (nine3Norm I P hP) ⟨x, hx⟩ ∈ H
  have hgen : ∀ x ∈ I, C x := by
    intro x hx
    apply Subgroup.iSup_induction (S := S) (C := C) ?_ ?_ ?_ ?_
    · rwa [← hIeq]
    · intro i g hg
      exact ⟨hS i hg, fun hg' => by
        have hEq : (⟨g, hg'⟩ : ↥I) = ⟨g, hS i hg⟩ := rfl
        rw [hEq]
        exact himg i (Subgroup.mem_map_of_mem (nine3Norm I P hP)
          (Subgroup.mem_subgroupOf.mpr hg))⟩
    · refine ⟨I.one_mem, fun h1 => ?_⟩
      have hEq : (⟨1, h1⟩ : ↥I) = 1 := rfl
      rw [hEq, map_one]
      exact H.one_mem
    · intro x y hx hy
      refine ⟨I.mul_mem hx.1 hy.1, fun hxy => ?_⟩
      have hEq : (⟨x * y, hxy⟩ : ↥I) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := rfl
      rw [hEq, map_mul]
      exact H.mul_mem (hx.2 hx.1) (hy.2 hy.1)
  rintro _ ⟨x, rfl⟩
  exact (hgen x x.2).2 x.2

end CFSG.LocalAnalysis.WeakClosure81
