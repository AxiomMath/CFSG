module

public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.A7Coordinates
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem map_center_mulEquiv {R : Type*} [Group R] (α : R ≃* R) :
    (center R).map α.toMonoidHom = center R := by
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hz
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := α.surjective y
    show α x * α z = α z * α x
    rw [← map_mul, ← map_mul, hz x]
  · refine ⟨α.symm z, ?_, by simp⟩
    rw [mem_center_iff] at hz
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (α y)

theorem exists_sq_eq_conj_of_A5 {R : Type*} [Group R] (hperf : Group.IsPerfect R)
    (e : R ⧸ center R ≃* alternatingGroup (Fin 5)) (α : R ≃* R) :
    ∃ r : R, ∀ x, α (α x) = r * x * r⁻¹ := by
  classical
  set q := QuotientGroup.mk' (center R) with hq
  set ᾱ : R ⧸ center R ≃* R ⧸ center R :=
    QuotientGroup.congr (center R) (center R) α (map_center_mulEquiv α) with hᾱ
  have hᾱq : ∀ x, ᾱ (q x) = q (α x) := fun x => QuotientGroup.congr_mk' _ _ _ _ x
  set β : MulAut (alternatingGroup (Fin 5)) := (e.symm.trans ᾱ).trans e with hβ
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 β
  have hσ2 : σ * σ ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, map_mul, Int.units_mul_self]
  set a : alternatingGroup (Fin 5) := ⟨σ * σ, hσ2⟩ with ha
  have hββ : ∀ y, β (β y) = a * y * a⁻¹ := by
    intro y
    rw [← hσ]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, ha]
    group
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (center R) (e.symm a)
  refine ⟨r, ?_⟩
  have hmod : ∀ x, (r * x * r⁻¹)⁻¹ * α (α x) ∈ center R := by
    intro x
    rw [← QuotientGroup.eq_one_iff (N := center R), QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 : (QuotientGroup.mk (α (α x)) : R ⧸ center R) = ᾱ (ᾱ (q x)) := by
      rw [hᾱq, hᾱq]
      rfl
    have h2 : e (ᾱ (ᾱ (q x))) = β (β (e (q x))) := by
      simp [hβ]
    have h3 : ᾱ (ᾱ (q x)) = q r * q x * (q r)⁻¹ := by
      apply e.injective
      have hr' : q r = e.symm a := hr
      rw [h2, hββ, map_mul, map_mul, map_inv, hr', MulEquiv.apply_symm_apply]
    rw [h1, h3]
    simp only [hq, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    group
    rfl
  set z : R →* center R :=
    { toFun := fun x => ⟨(r * x * r⁻¹)⁻¹ * α (α x), hmod x⟩
      map_one' := by
        apply Subtype.ext
        simp only [mul_one, mul_inv_cancel, inv_one, map_one]
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul]
        have hy := mem_center_iff.1 (hmod y)
        have hx := mem_center_iff.1 (hmod x)
        calc (r * (x * y) * r⁻¹)⁻¹ * (α (α x) * α (α y))
            = (r * y * r⁻¹)⁻¹ * (((r * x * r⁻¹)⁻¹ * α (α x)) * (r * y * r⁻¹)) *
                ((r * y * r⁻¹)⁻¹ * α (α y)) := by group
          _ = (r * y * r⁻¹)⁻¹ * ((r * y * r⁻¹) * ((r * x * r⁻¹)⁻¹ * α (α x))) *
                ((r * y * r⁻¹)⁻¹ * α (α y)) := by rw [hx (r * y * r⁻¹)]
          _ = (r * x * r⁻¹)⁻¹ * α (α x) * ((r * y * r⁻¹)⁻¹ * α (α y)) := by group }
    with hz
  have hz1 : ∀ x, z x = 1 := by
    intro x
    have hker := Abelianization.commutator_subset_ker z
    rw [Group.isPerfect_def.1 hperf] at hker
    exact (MonoidHom.mem_ker).1 (hker (mem_top x))
  intro x
  have h1 := congrArg Subtype.val (hz1 x)
  simp only [hz, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h1
  calc α (α x) = (r * x * r⁻¹) * ((r * x * r⁻¹)⁻¹ * α (α x)) := by group
    _ = r * x * r⁻¹ := by rw [h1, mul_one]

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjOf {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 x.2
    rwa [inv_inv] at this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem conjOf_coe {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) (x : K) :
    ((conjOf hg x : K) : G) = g * x * g⁻¹ := rfl

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem le_sup_centralizerSection_sup_of_A5 {H K T : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hKp : ⁅K, K⁆ = K)
    (hA5 : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      alternatingGroup (Fin 5)))
    (hT : IsSylowTwoOf T H) :
    H ≤ K ⊔ centralizerSection H K (pCoreOf 2 K) ⊔ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := hA5
  set Y := centralizerSection H K (pCoreOf 2 K) with hYdef
  have hperfK : Group.IsPerfect ↥K := (Subgroup.isPerfect_iff).2 hKp
  have hperfR : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have hPK : ∀ k ∈ K, k ∈ normalizer ((pCoreOf 2 K : Subgroup G) : Set G) := fun k hk =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
  have hsq : ∀ g ∈ H, g * g ∈ K ⊔ Y := by
    intro g hg
    have hgN := hHK hg
    set φ := conjOf hgN with hφ
    set α : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
      QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ) with hα
    obtain ⟨r, hr⟩ := exists_sq_eq_conj_of_A5 hperfR e5 α
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) r
    have hm : (k : G)⁻¹ * (g * g) ∈ Y := by
      have hmN : (k : G)⁻¹ * (g * g) ∈ normalizer (K : Set G) :=
        mul_mem (inv_mem (le_normalizer k.2)) (mul_mem hgN hgN)
      refine ⟨H.mul_mem (H.inv_mem (hKH k.2)) (H.mul_mem hg hg), hmN,
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hmN, fun x hx => ?_⟩
      have hαmk : ∀ y : ↥K, α (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
      have h1 := hr (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥K))
      rw [hαmk, hαmk, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      set p : ↥K := (φ (φ (⟨x, hx⟩⁻¹ : ↥K)))⁻¹ * (k * (⟨x, hx⟩⁻¹ : ↥K) * k⁻¹) with hp
      have hpG : (p : G) = (g * (g * x⁻¹ * g⁻¹) * g⁻¹)⁻¹ * ((k : G) * x⁻¹ * (k : G)⁻¹) := by
        simp only [hp, Subgroup.coe_mul, Subgroup.coe_inv, conjOf_coe, hφ]
      have hpP : (p : G)⁻¹ ∈ pCoreOf 2 K := by
        rw [pCoreOf_eq_map_cfsgPCore]
        exact ⟨p⁻¹, inv_mem h1, rfl⟩
      have hconj := (mem_normalizer_iff.1 (hPK _ (K.inv_mem k.2)) ((p : G)⁻¹)).1 hpP
      have he : x * ((k : G)⁻¹ * (g * g)) * x⁻¹ * ((k : G)⁻¹ * (g * g))⁻¹ =
          (k : G)⁻¹ * (p : G)⁻¹ * (k : G)⁻¹⁻¹ := by
        rw [hpG]
        simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rw [he]
      exact hconj
    have h2 : g * g = (k : G) * ((k : G)⁻¹ * (g * g)) := by group
    rw [h2]
    exact mul_mem (mem_sup_left k.2) (mem_sup_right hm)
  set N := K ⊔ Y with hNdef
  have hNH : N ≤ H := sup_le hKH (centralizerSection_le_left _ _ _)
  have hHY : H ≤ normalizer (Y : Set G) := centralizerSection_normal hHK
  have hHN : H ≤ normalizer (N : Set G) := fun g hg => mem_normalizer_sup (hHK hg) (hHY hg)
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  have h2 : IsPGroup 2 (↥H ⧸ N.subgroupOf H) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hsq g g.2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h2
  set X := N ⊔ T with hXdef
  have hXH : X ≤ H := sup_le hNH hT.1
  have hdvd : X.relIndex H ∣ 2 ^ m := by
    have h3 := Subgroup.relIndex_dvd_of_le_left H (le_sup_left : N ≤ X)
    have h4 : N.relIndex H = 2 ^ m := by
      rw [Subgroup.relIndex, Subgroup.index, hm]
    rwa [h4] at h3
  have hodd : ¬ 2 ∣ X.relIndex H := by
    intro h5
    apply hT.2.2
    show 2 ∣ T.relIndex H
    rw [← Subgroup.relIndex_mul_relIndex T X H le_sup_right hXH]
    exact dvd_mul_of_dvd_right h5 _
  have h1 : X.relIndex H = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hj] at hodd ⊢
    rcases j with _ | j
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero j)) hodd
  exact Subgroup.relIndex_eq_one.1 h1

end Main

end CFSG.Quasithin.H13.A7
