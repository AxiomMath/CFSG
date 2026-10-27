module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828A
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H
open scoped IsMulCommutative

section L828B

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_centralizer_828 {L V : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hperf : ⁅L, L⁆ = L)
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hLC : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
  set C := (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L with hCdef
  have hCn : C.Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [hCdef, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(l * x * l⁻¹ : ↥L).2, ?_⟩
    show ((l * x * l⁻¹ : ↥L) : G) ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : (l : G)⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLN l.2)) v).mp hv
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * (l * x * (l : G)⁻¹) = l * ((l : G)⁻¹ * v * l * x) * (l : G)⁻¹ := by group
      _ = l * (x * ((l : G)⁻¹ * v * l)) * (l : G)⁻¹ := by rw [h1]
      _ = l * x * (l : G)⁻¹ * v := by group
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  have hCQn : (C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hCn.map _ (QuotientGroup.mk'_surjective _)
  have hO : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).isNilpotent
    infer_instance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hCQn with h | h
  ·
    exfalso
    apply hLC
    have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp (CFSG.pCore 2 ↥L).subtype) := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective C q
      have hl : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
          C.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hcl⟩ := hl
      have hm : c⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk c : Q) = QuotientGroup.mk l := hcl
        rw [this, inv_mul_cancel]
      refine ⟨⟨c⁻¹ * l, hm⟩, ?_⟩
      show QuotientGroup.mk' C (c⁻¹ * l) = QuotientGroup.mk' C l
      have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
      rw [map_mul, map_inv, hc1, inv_one, one_mul]
    have hLp : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
    have hQp : Group.IsPerfect (↥L ⧸ C) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
    have hQs : Group.IsSolvable (↥L ⧸ C) := Group.isSolvable_of_surjective hsurj
    have hsub : Subsingleton (↥L ⧸ C) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ C) hQs
    intro x hx
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ C) = 1 := Subsingleton.elim _ _
    have h2 := (QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥L)).mp h1
    rw [hCdef, Subgroup.mem_subgroupOf] at h2
    exact h2.2
  ·
    have hCs : Group.IsSolvable ↥C := by
      let r : ↥C →* ↥(Subgroup.center Q) :=
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp C.subtype).codRestrict _ fun c =>
          h ⟨c, c.2, rfl⟩
      have hp2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥L).subgroupOf C) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective C.subtype C.subtype_injective
      have hOC : Group.IsSolvable ↥((CFSG.pCore 2 ↥L).subgroupOf C) := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact @IsNilpotent.to_isSolvable _ _ hp2.isNilpotent
      refine Group.isSolvable_of_ker_le_range
        (((CFSG.pCore 2 ↥L).subgroupOf C).subtype) r ?_
      intro c hc
      rw [MonoidHom.mem_ker] at hc
      have hc' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (c : ↥L) = 1 := congrArg Subtype.val hc
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
      exact ⟨⟨c, hc'⟩, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        L ⊓ Subgroup.centralizer (V : Set G) ≤ L)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe _).symm.injective

theorem mem_cComp_of_autOn_828 {X V Y : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hC : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (V : Set G)))
    (hP : CFSG.IsQuasisimple (↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V)))
    (hsub : IsSubnormal X Y) : X ∈ cComp Y := by
  have := finite_mulAut_82 (W := ↥V)
  obtain ⟨S, _, _, g, hg, hgk⟩ := exists_simple_quot_828 hP
  set φ := actHom82 hXN with hφdef
  have hφ := actHom82_surjective hXN
  refine mem_cComp_of_hom_828 hX ?_ hsub (g.comp φ) (hg.comp hφ) ?_
  · intro hX1
    obtain ⟨-, -, a, b, hab⟩ := hP
    apply hab
    have hsub1 : Subsingleton ↥(autOn X V) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨x', rfl⟩ := hφ x
      obtain ⟨y', rfl⟩ := hφ y
      have hx : x' = 1 := Subtype.ext (Subgroup.mem_bot.mp ((le_of_eq hX1) x'.2))
      have hy : y' = 1 := Subtype.ext (Subgroup.mem_bot.mp ((le_of_eq hX1) y'.2))
      rw [hx, hy]
    have : Subsingleton (↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V)) :=
      ⟨fun x y => by
        obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [Subsingleton.elim x' y']⟩
    have : Subsingleton ((↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V)) ⧸
        Subgroup.center (↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V))) :=
      ⟨fun x y => by
        obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [Subsingleton.elim x' y']⟩
    exact Subsingleton.elim _ _
  ·
    let r : ↥(g.comp φ).ker →* ↥g.ker :=
      (φ.comp (g.comp φ).ker.subtype).codRestrict g.ker fun x => x.2
    let f : ↥(X ⊓ Subgroup.centralizer (V : Set G)) →* ↥(g.comp φ).ker :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          have hx : φ ⟨x, x.2.1⟩ = 1 := by
            rw [← MonoidHom.mem_ker, mem_ker_actHom82]
            exact x.2.2
          rw [hx, map_one]⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_ker_le_range f r ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : φ (x : ↥X) = 1 := congrArg Subtype.val hx
    rw [← MonoidHom.mem_ker, mem_ker_actHom82] at hx'
    exact ⟨⟨(x : G), (x : ↥X).2, hx'⟩, rfl⟩

end L828B

end CFSG.Quasithin.H13
