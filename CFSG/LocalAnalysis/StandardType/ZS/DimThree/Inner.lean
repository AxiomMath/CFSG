module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Transport
import CFSG.LocalAnalysis.StandardType.ZS.DimThree.InnerDirect
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def ExcData (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U] (k : ExcRow)
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  k.admissible p ∧ Module.finrank (ZMod p) U = k.deg ∧ Nat.card A = k.ord ∧
    Nat.card (center A) = k.cen ∧ DMax p A k.dmax ∧ OneClass p A

theorem family_of_excData {k : ExcRow} {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : ExcData p k A)
    (hnm : ¬ k.needsModel) : Family p A :=
  Family.exc k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 fun h' => absurd h' hnm

private lemma isRefl_iff_zi (hp : p ≠ 2) {G H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    {x : GL (Fin 3) (ZMod p)} (hx : x ∈ G) :
    N1322.IsRefl x ↔ ∃ a ∈ H, a * a = 1 ∧ a ≠ 1 ∧ x = (-1 : GL (Fin 3) (ZMod p)) * a := by
  constructor
  · intro h
    obtain ⟨a, ha, ha2, hxa⟩ := eq_neg_one_mul_of_inner hdet hsch hinn hx h
    refine ⟨a, ha, ha2, ?_, hxa⟩
    intro ha1
    have hxneg : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) = -1 := by
      rw [hxa, ha1, mul_one]
      exact (Units.val_neg (1 : GL (Fin 3) (ZMod p))).trans
        (congrArg Neg.neg Units.val_one)
    exact N1322.IsRefl.ne_neg_one (four_ne_zero_of_ne_two hp) h hxneg
  · rintro ⟨a, ha, ha2, ha1, hxa⟩
    rw [hxa]
    exact isRefl_neg_one_mul hp (hdet a ha) ha2 ha1

private lemma card_map_autGL_zi (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    Nat.card A = Nat.card (A.map (autGL e).toMonoidHom) ∧
      Nat.card (center A) = Nat.card (center (A.map (autGL e).toMonoidHom)) := by
  have hiso : A ≃* A.map (autGL e).toMonoidHom :=
    Subgroup.equivMapOfInjective A (autGL e).toMonoidHom (autGL e).injective
  exact ⟨Nat.card_congr hiso.toEquiv,
    Nat.card_congr (Subgroup.centerCongr hiso).toEquiv⟩

private lemma autGL_mul_neg_zi (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {x y : U ≃ₗ[ZMod p] U} {a b : GL (Fin 3) (ZMod p)}
    (hx : autGL e x = (-1) * a) (hy : autGL e y = (-1) * b) :
    autGL e (x * y) = a * b := by
  rw [map_mul, hx, hy, neg_one_mul, neg_one_mul, neg_mul_neg]

theorem orderOf_mul_eq_of_autGL_eq_neg_mul (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {x y : U ≃ₗ[ZMod p] U} {a b : GL (Fin 3) (ZMod p)}
    (hx : autGL e x = (-1) * a) (hy : autGL e y = (-1) * b) :
    orderOf (x * y) = orderOf (a * b) := by
  rw [← autGL_mul_neg_zi e hx hy]
  exact (orderOf_injective (autGL e).toMonoidHom (autGL e).injective (x * y)).symm

theorem commute_iff_of_autGL_eq_neg_mul (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {x y : U ≃ₗ[ZMod p] U} {a b : GL (Fin 3) (ZMod p)}
    (hx : autGL e x = (-1) * a) (hy : autGL e y = (-1) * b) :
    Commute x y ↔ Commute a b := by
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    have h' := congrArg (autGL e) h
    rwa [autGL_mul_neg_zi e hx hy, autGL_mul_neg_zi e hy hx] at h'
  · intro h
    apply (autGL e).injective
    rw [autGL_mul_neg_zi e hx hy, autGL_mul_neg_zi e hy hx]
    exact h

theorem ne_iff_of_autGL_eq_neg_mul (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {x y : U ≃ₗ[ZMod p] U} {a b : GL (Fin 3) (ZMod p)}
    (hx : autGL e x = (-1) * a) (hy : autGL e y = (-1) * b) :
    x ≠ y ↔ a ≠ b := by
  constructor
  · intro h hab
    exact h ((autGL e).injective (by rw [hx, hy, hab]))
  · intro h hxy
    exact h (mul_left_cancel (by rw [← hx, ← hy, hxy]))

private lemma exists_isRefl_of_involution_of_neg (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hneg : (-1 : GL (Fin 3) (ZMod p)) ∈ A.map (autGL e).toMonoidHom)
    {a : GL (Fin 3) (ZMod p)} (ha : a ∈ H) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ x ∈ A, IsRefl p x ∧ autGL e x = (-1) * a := by
  have hua : (-1) * a ∈ A.map (autGL e).toMonoidHom :=
    (A.map (autGL e).toMonoidHom).mul_mem hneg (hHG ha)
  obtain ⟨x, hxA, hxmap⟩ := Subgroup.mem_map.mp hua
  have hxmap' : autGL e x = (-1) * a := hxmap
  exact ⟨x, hxA, (isRefl_iff_autGL hp e x).mpr (by
    rw [hxmap']
    exact isRefl_neg_one_mul hp (hdet a ha) ha2 ha1), hxmap'⟩

private lemma dMax_zi (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (hneg : (-1 : GL (Fin 3) (ZMod p)) ∈ A.map (autGL e).toMonoidHom) {d : ℕ}
    (hle : ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → orderOf (a * b) ≤ d)
    (hatt : ∃ a ∈ H, ∃ b ∈ H, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ orderOf (a * b) = d) :
    DMax p A d := by
  constructor
  · intro x hxA y hyA hxr hyr
    obtain ⟨a, ha, ha2, ha1, hxa⟩ :=
      (isRefl_iff_zi hp hdet hsch hinn (Subgroup.mem_map_of_mem _ hxA)).mp
        ((isRefl_iff_autGL hp e x).mp hxr)
    obtain ⟨b, hb, hb2, hb1, hyb⟩ :=
      (isRefl_iff_zi hp hdet hsch hinn (Subgroup.mem_map_of_mem _ hyA)).mp
        ((isRefl_iff_autGL hp e y).mp hyr)
    have hxy := autGL_mul_neg_zi e hxa hyb
    have hord : orderOf (x * y) = orderOf (autGL e (x * y)) :=
      (orderOf_injective (autGL e).toMonoidHom (autGL e).injective (x * y)).symm
    rw [hord, hxy]
    exact hle a ha b hb ha2 ha1 hb2 hb1
  · obtain ⟨a, ha, b, hb, ha2, ha1, hb2, hb1, hab⟩ := hatt
    obtain ⟨x, hxA, hxr, hxa⟩ :=
      exists_isRefl_of_involution_of_neg hp e hHG hdet hneg ha ha2 ha1
    obtain ⟨y, hyA, hyr, hyb⟩ :=
      exists_isRefl_of_involution_of_neg hp e hHG hdet hneg hb hb2 hb1
    exact ⟨x, hxA, y, hyA, hxr, hyr, by rw [orderOf_mul_eq_of_autGL_eq_neg_mul e hxa hyb, hab]⟩

private lemma oneClass_zi (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (hone : ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      ∃ g ∈ H, b = g * a * g⁻¹) :
    OneClass p A := by
  intro x hxA y hyA hxr hyr
  obtain ⟨a, ha, ha2, ha1, hxa⟩ :=
    (isRefl_iff_zi hp hdet hsch hinn (Subgroup.mem_map_of_mem _ hxA)).mp
      ((isRefl_iff_autGL hp e x).mp hxr)
  obtain ⟨b, hb, hb2, hb1, hyb⟩ :=
    (isRefl_iff_zi hp hdet hsch hinn (Subgroup.mem_map_of_mem _ hyA)).mp
      ((isRefl_iff_autGL hp e y).mp hyr)
  have hxa' : autGL e x = (-1) * a := hxa
  have hyb' : autGL e y = (-1) * b := hyb
  obtain ⟨g₀, hg₀H, hg₀⟩ := hone a ha b hb ha2 ha1 hb2 hb1
  obtain ⟨g, hgA, hgmap⟩ := Subgroup.mem_map.mp (hHG hg₀H)
  have hgmap' : autGL e g = g₀ := hgmap
  refine ⟨g, hgA, ?_⟩
  apply (autGL e).injective
  rw [map_mul, map_mul, map_inv, hgmap', hxa', hyb', hg₀]
  simp only [mul_neg, neg_mul, one_mul]

theorem exists_isRefl_of_involution (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    {a : GL (Fin 3) (ZMod p)} (ha : a ∈ H) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ x ∈ A, IsRefl p x ∧ autGL e x = (-1) * a := by
  have hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    fun _ hx => N1322.det_eq_one_of_perfect hx
  have hsch := N1322.scalar_commutant_of_noncomm hirr hnc
  exact exists_isRefl_of_involution_of_neg hp e hHG hdet
    (neg_one_mem_of_inner hHG hdet hsch hinn (exists_isRefl_mem hp e hR hI)) ha ha2 ha1

theorem excData_of_inner (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (k : ExcRow) (hk : k.admissible p) (hdeg : k.deg = 3)
    (hcard : 2 * Nat.card H = k.ord) (hcen : 2 * Nat.card (center H) = k.cen)
    (hle : ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      orderOf (a * b) ≤ k.dmax)
    (hatt : ∃ a ∈ H, ∃ b ∈ H, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      orderOf (a * b) = k.dmax)
    (hone : ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      ∃ g ∈ H, b = g * a * g⁻¹) :
    ExcData p k A := by
  have hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    fun _ hx => N1322.det_eq_one_of_perfect hx
  have hsch := N1322.scalar_commutant_of_noncomm hirr hnc
  have hG := map_autGL_eq_closure hp e hR
  have hex := exists_isRefl_mem hp e hR hI
  obtain ⟨hcA, hzA⟩ := card_map_autGL_zi e A
  refine ⟨hk, ?_, ?_, ?_,
    dMax_zi hp e hHG hdet hsch hinn (neg_one_mem_of_inner hHG hdet hsch hinn hex) hle hatt,
    oneClass_zi hp e hHG hdet hsch hinn hone⟩
  · rw [hdeg, LinearEquiv.finrank_eq e, Module.finrank_fin_fun]
  · rw [hcA, card_eq_two_mul_of_inner hp hG hHG hdet hsch hinn hex, hcard]
  · rw [hzA, card_center_eq_two_mul_of_inner hp hG hHG hdet hsch hinn hex, hcen]

private lemma map_ne_one_of_involution_zd {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {a : H} (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    f a ≠ 1 := by
  intro h1
  have h3 : a ^ 3 = 1 := by
    simpa using hker3 a (MonoidHom.mem_ker.mpr h1)
  exact ha1 (CFSG.RankThree.SubgroupLists.eq_one_of_pow_three_of_pow h3 (n := 2) (by norm_num)
    (by rw [pow_two]; exact ha2))

private lemma orderOf_mul_eq_orderOf_map_zd {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hker : f.ker ≤ Subgroup.center H)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {a b : H} (ha : a * a = 1) (hb : b * b = 1) :
    orderOf (a * b) = orderOf (f a * f b) := by
  set m : ℕ := orderOf (f a * f b) with hm
  have hmem : (a * b) ^ m ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hm]
    exact pow_orderOf_eq_one _
  have hconj0 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    calc a * (a * b) * a⁻¹ = (a * a) * (b * a⁻¹) := by group
      _ = b * a⁻¹ := by rw [ha, one_mul]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, ha', hb']
  have hinv : a * (a * b) ^ m * a⁻¹ = ((a * b) ^ m)⁻¹ := by
    rw [← conj_pow, hconj0, inv_pow]
  have hcomm : a * (a * b) ^ m * a⁻¹ = (a * b) ^ m := by
    have h2 := (Subgroup.mem_center_iff.mp (hker hmem)) a
    rw [h2]
    group
  have hsq : ((a * b) ^ m) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp (by rw [← hinv, hcomm])
  have hone : (a * b) ^ m = 1 :=
    CFSG.RankThree.SubgroupLists.eq_one_of_pow_three_of_pow (hker3 _ hmem) (n := 2)
      (by norm_num) hsq
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hone) ?_
  rw [hm]
  have h := orderOf_map_dvd f (a * b)
  rwa [map_mul] at h

private lemma exists_involution_lift_zd {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center H)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {a' : K} (ha' : a' * a' = 1) (ha'1 : a' ≠ 1) :
    ∃ a : H, a * a = 1 ∧ a ≠ 1 ∧ f a = a' := by
  let q : H ⧸ f.ker ≃* K := QuotientGroup.liftEquiv (φ := f) (N := f.ker) hf rfl
  have hq : ∀ x : H, q (QuotientGroup.mk x) = f x :=
    fun x => QuotientGroup.liftEquiv_mk (φ := f) (N := f.ker) hf rfl x
  have hs : (q.symm a') ^ 2 = 1 := by
    rw [← map_pow, pow_two, ha', map_one]
  obtain ⟨a, haq, ha2⟩ :=
    CFSG.RankThree.SubgroupLists.exists_lift_pow_eq_one (G := H) (Z := f.ker) hker hker3
      (n := 2) (by norm_num) (q.symm a') hs
  have hfa : f a = a' := by rw [← hq a, haq, q.apply_symm_apply]
  exact ⟨a, by rwa [pow_two] at ha2, fun h1 => ha'1 (by rw [← hfa, h1, map_one]), hfa⟩

private lemma isConj_of_isConj_map_zd {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center H)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (h : IsConj (f a) (f b)) : IsConj a b := by
  let q : H ⧸ f.ker ≃* K := QuotientGroup.liftEquiv (φ := f) (N := f.ker) hf rfl
  have hq : ∀ x : H, q (QuotientGroup.mk x) = f x :=
    fun x => QuotientGroup.liftEquiv_mk (φ := f) (N := f.ker) hf rfl x
  have hconj : IsConj ((a : H ⧸ f.ker)) (b : H ⧸ f.ker) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨q.symm c, ?_⟩
    apply q.injective
    rw [map_mul, map_mul, map_inv, hq, hq, q.apply_symm_apply]
    exact hc
  exact CFSG.RankThree.SubgroupLists.isConj_of_isConj_mk (G := H) (Z := f.ker) hker hker3
    (n := 2) (by norm_num) (by rw [pow_two]; exact ha) (by rw [pow_two]; exact hb) hconj

private lemma exists_noncomm_coe_zd {G : Type*} [Group G] {H : Subgroup G}
    {K : Type*} [Group K] (f : H →* K) (hf : Function.Surjective f)
    (h : ∃ a b : K, a * b ≠ b * a) : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  refine ⟨(x : G), x.2, (y : G), y.2, ?_⟩
  intro hxy
  exact hab (by rw [← map_mul, ← map_mul, show x * y = y * x from Subtype.ext hxy])

private lemma involution_orderOf_mul_le_coe_zd {G : Type*} [Group G] {H : Subgroup G}
    {K : Type*} [Group K] (f : H →* K) (hker : f.ker ≤ Subgroup.center H)
    (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {d : ℕ}
    (h : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → orderOf (a * b) ≤ d) :
    ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → orderOf (a * b) ≤ d := by
  intro a ha b hb ha2 ha1 hb2 hb1
  have ha2' : (⟨a, ha⟩ : H) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa using ha2)
  have hb2' : (⟨b, hb⟩ : H) * ⟨b, hb⟩ = 1 := Subtype.ext (by simpa using hb2)
  have ha1' : (⟨a, ha⟩ : H) ≠ 1 := fun h1 => ha1 (by simpa using congrArg Subtype.val h1)
  have hb1' : (⟨b, hb⟩ : H) ≠ 1 := fun h1 => hb1 (by simpa using congrArg Subtype.val h1)
  rw [show a * b = ((⟨a, ha⟩ * ⟨b, hb⟩ : H) : G) from rfl, Subgroup.orderOf_coe,
    orderOf_mul_eq_orderOf_map_zd f hker hker3 ha2' hb2']
  exact h (f ⟨a, ha⟩) (f ⟨b, hb⟩) (by rw [← map_mul, ha2', map_one])
    (map_ne_one_of_involution_zd f hker3 ha2' ha1')
    (by rw [← map_mul, hb2', map_one])
    (map_ne_one_of_involution_zd f hker3 hb2' hb1')

private lemma exists_involutions_orderOf_mul_eq_coe_zd {G : Type*} [Group G] {H : Subgroup G}
    {K : Type*} [Group K] (f : H →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1) {d : ℕ}
    (h : ∃ a b : K, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ orderOf (a * b) = d) :
    ∃ a ∈ H, ∃ b ∈ H, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ orderOf (a * b) = d := by
  obtain ⟨a, b, ha2, ha1, hb2, hb1, hord⟩ := h
  obtain ⟨a', ha'2, ha'1, hfa⟩ := exists_involution_lift_zd f hf hker hker3 ha2 ha1
  obtain ⟨b', hb'2, hb'1, hfb⟩ := exists_involution_lift_zd f hf hker hker3 hb2 hb1
  refine ⟨(a' : G), a'.2, (b' : G), b'.2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val ha'2
  · exact fun h1 => ha'1 (Subtype.ext h1)
  · simpa using congrArg Subtype.val hb'2
  · exact fun h1 => hb'1 (Subtype.ext h1)
  · rw [show (a' : G) * b' = ((a' * b' : H) : G) from rfl, Subgroup.orderOf_coe,
      orderOf_mul_eq_orderOf_map_zd f hker hker3 ha'2 hb'2, hfa, hfb, hord]

private lemma involution_conj_coe_zd {G : Type*} [Group G] {H : Subgroup G}
    {K : Type*} [Group K] (f : H →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1)
    (h : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → IsConj a b) :
    ∀ a ∈ H, ∀ b ∈ H, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      ∃ g ∈ H, b = g * a * g⁻¹ := by
  intro a ha b hb ha2 ha1 hb2 hb1
  have ha2' : (⟨a, ha⟩ : H) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa using ha2)
  have hb2' : (⟨b, hb⟩ : H) * ⟨b, hb⟩ = 1 := Subtype.ext (by simpa using hb2)
  have ha1' : (⟨a, ha⟩ : H) ≠ 1 := fun h1 => ha1 (by simpa using congrArg Subtype.val h1)
  have hb1' : (⟨b, hb⟩ : H) ≠ 1 := fun h1 => hb1 (by simpa using congrArg Subtype.val h1)
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (isConj_of_isConj_map_zd f hf hker hker3 ha2' hb2'
      (h (f ⟨a, ha⟩) (f ⟨b, hb⟩) (by rw [← map_mul, ha2', map_one])
        (map_ne_one_of_involution_zd f hker3 ha2' ha1')
        (by rw [← map_mul, hb2', map_one])
        (map_ne_one_of_involution_zd f hker3 hb2' hb1')))
  exact ⟨(g : G), g.2, (congrArg Subtype.val hg).symm⟩

theorem excData_of_inner_of_hom (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hdec : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z)
    {K : Type*} [Group K] (f : H →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ center H) (hker3 : ∀ z ∈ f.ker, z ^ 3 = 1)
    (k : ExcRow) (hk : k.admissible p) (hdeg : k.deg = 3)
    (hcard : 2 * Nat.card f.ker * Nat.card K = k.ord) (hZK : center K = ⊥)
    (hcen : 2 * Nat.card f.ker = k.cen) (hnc : ∃ a b : K, a * b ≠ b * a)
    (hle : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → orderOf (a * b) ≤ k.dmax)
    (hatt : ∃ a b : K, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ orderOf (a * b) = k.dmax)
    (hone : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → IsConj a b) :
    ExcData p k A := by
  have hncH := exists_noncomm_coe_zd f hf hnc
  have hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹ := by
    intro t ht hrefl
    obtain ⟨h, hh, z, hzc, htz⟩ := hdec t ht hrefl
    refine ⟨h, hh, fun x hx => ?_⟩
    rw [htz]
    calc h * z * x * (h * z)⁻¹ = h * (z * x * z⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hzc x hx]; group
  have hcardH : 2 * Nat.card H = k.ord := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hf, ← mul_assoc]
    exact hcard
  have hcenter : Subgroup.center H = f.ker :=
    le_antisymm (MonoidHom.center_le_ker f hf hZK) hker
  have hcenH : 2 * Nat.card (Subgroup.center H) = k.cen := by
    rw [hcenter]
    exact hcen
  exact excData_of_inner hp e hR hI hHG hirr hncH hinn k hk hdeg hcardH hcenH
    (involution_orderOf_mul_le_coe_zd f hker hker3 hle)
    (exists_involutions_orderOf_mul_eq_coe_zd f hf hker hker3 hatt)
    (involution_conj_coe_zd f hf hker hker3 hone)

theorem excData_of_inner_of_mulEquiv (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hirr : IsIrreducibleMatrixRep H.subtype)
    (hdec : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z)
    {K : Type*} [Group K] [Group.IsPerfect K] (eK : H ≃* K)
    (k : ExcRow) (hk : k.admissible p) (hdeg : k.deg = 3)
    (hcard : 2 * Nat.card K = k.ord) (hZK : center K = ⊥) (hcen : 2 = k.cen)
    (hnc : ∃ a b : K, a * b ≠ b * a)
    (hle : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → orderOf (a * b) ≤ k.dmax)
    (hatt : ∃ a b : K, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ orderOf (a * b) = k.dmax)
    (hone : ∀ a b : K, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → IsConj a b) :
    ExcData p k A := by
  let : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hker_bot : eK.toMonoidHom.ker = ⊥ :=
    MonoidHom.ker_eq_bot eK.toMonoidHom eK.injective
  exact excData_of_inner_of_hom hp e hR hI hHG hirr hdec eK.toMonoidHom eK.surjective
    (by rw [hker_bot]; exact bot_le)
    (fun z hz => by rw [hker_bot, Subgroup.mem_bot] at hz; rw [hz, one_pow])
    k hk hdeg
    (by rw [hker_bot, Subgroup.card_bot]; simpa using hcard)
    hZK (by rw [hker_bot, Subgroup.card_bot]; simpa using hcen)
    hnc hle hatt hone

end CFSG.StandardType.ZS.DimThree
