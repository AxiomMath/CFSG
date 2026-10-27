module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiWeights
import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiExtra

public section

namespace CFSG.StandardType.FrameRoute

open Matrix

private theorem exists_maximal_abelian_centerZ
    {M : Type} [Group M] [Finite M] (Z E : Subgroup M) (hZE : Z ≤ E)
    (hZc : ∀ z ∈ Z, ∀ a ∈ E, z * a = a * z)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z) :
    ∃ C : Subgroup M, C ≤ E ∧ (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∧
      (∀ a ∈ E, (∀ c ∈ C, a * c = c * a) → a ∈ C) ∧ Z ≤ C ∧
      (∀ x ∈ E, ∀ c ∈ C, x * c * x⁻¹ ∈ C) := by
  classical
  have : Finite (Subgroup M) :=
    Finite.of_injective (fun C : Subgroup M => (C : Set M)) SetLike.coe_injective
  let s : Set (Subgroup M) := {C | C ≤ E ∧ ∀ a ∈ C, ∀ b ∈ C, a * b = b * a}
  obtain ⟨C, hCmax⟩ := (Set.toFinite s).exists_maximalFor (fun C : Subgroup M => Nat.card C) s
    ⟨Z, hZE, fun a ha b hb => hZc a ha b (hZE hb)⟩
  have hCs : C ∈ s := hCmax.1
  have hCmax' : ∀ D ∈ s, Nat.card C ≤ Nat.card D → Nat.card D ≤ Nat.card C :=
    fun D hD hle => hCmax.2 hD hle
  have hmax : ∀ a ∈ E, (∀ c ∈ C, a * c = c * a) → a ∈ C := by
    intro a haE hcommC
    let D : Subgroup M := Subgroup.closure ((C : Set M) ∪ {a})
    have hCD : C ≤ D := fun c hc => Subgroup.subset_closure (Set.mem_union_left _ hc)
    have hpair : ((C : Set M) ∪ {a}).Pairwise Commute := by
      rintro x hx y hy hxy
      rw [Set.mem_union] at hx hy
      rcases hx with hxC | hxa
      · rcases hy with hyC | hya
        · exact hCs.2 x hxC y hyC
        · rw [Set.mem_singleton_iff] at hya; subst hya; exact (hcommC x hxC).symm
      · rw [Set.mem_singleton_iff] at hxa; subst hxa
        rcases hy with hyC | hya
        · exact hcommC y hyC
        · rw [Set.mem_singleton_iff] at hya; subst hya; exact absurd rfl hxy
    have hDab : IsMulCommutative ↥D := Subgroup.isMulCommutative_closure hpair
    have hDs : D ∈ s := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.closure_le]
        rintro x (hxC | hxa)
        · exact hCs.1 hxC
        · rw [Set.mem_singleton_iff] at hxa; subst hxa; exact haE
      · have : IsMulCommutative ↥D := hDab
        intro x hx y hy
        exact Subgroup.mul_comm_of_mem_isMulCommutative D hx hy
    have hle1 : Nat.card C ≤ Nat.card D := Subgroup.card_le_of_le hCD
    have hle2 : Nat.card D ≤ Nat.card C := hCmax' D hDs hle1
    have hCD_eq : C = D := Subgroup.eq_of_le_of_card_ge hCD hle2
    have : a ∈ D := Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton a))
    rw [← hCD_eq] at this
    exact this
  have hZC : Z ≤ C := by
    intro z hz
    let D : Subgroup M := Subgroup.closure ((C : Set M) ∪ {z})
    have hCD : C ≤ D := fun c hc => Subgroup.subset_closure (Set.mem_union_left _ hc)
    have hpair : ((C : Set M) ∪ {z}).Pairwise Commute := by
      rintro x hx y hy hxy
      rw [Set.mem_union] at hx hy
      rcases hx with hxC | hxz
      · rcases hy with hyC | hyz
        · exact hCs.2 x hxC y hyC
        · rw [Set.mem_singleton_iff] at hyz; rw [hyz]; exact (hZc z hz x (hCs.1 hxC)).symm
      · rw [Set.mem_singleton_iff] at hxz; rw [hxz]
        rcases hy with hyC | hyz
        · exact hZc z hz y (hCs.1 hyC)
        · rw [Set.mem_singleton_iff] at hyz
          exact absurd (by rw [hxz, hyz]) hxy
    have hDab : IsMulCommutative ↥D := Subgroup.isMulCommutative_closure hpair
    have hDs : D ∈ s := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.closure_le]
        rintro x (hxC | hxz)
        · exact hCs.1 hxC
        · rw [Set.mem_singleton_iff] at hxz; subst hxz; exact hZE hz
      · have : IsMulCommutative ↥D := hDab
        intro x hx y hy
        exact Subgroup.mul_comm_of_mem_isMulCommutative D hx hy
    have hle1 : Nat.card C ≤ Nat.card D := Subgroup.card_le_of_le hCD
    have hle2 : Nat.card D ≤ Nat.card C := hCmax' D hDs hle1
    have hCD_eq : C = D := Subgroup.eq_of_le_of_card_ge hCD hle2
    have : z ∈ D := Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton z))
    rw [← hCD_eq] at this
    exact this
  have hCnorm : ∀ x ∈ E, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    have hmemZ : x * c * x⁻¹ * c⁻¹ ∈ Z := hcomm x hx c (hCs.1 hc)
    have hmemC : x * c * x⁻¹ * c⁻¹ ∈ C := hZC hmemZ
    have heq : x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
    rw [heq]
    exact C.mul_mem hmemC hc
  exact ⟨C, hCs.1, hCs.2, hmax, hZC, hCnorm⟩

private theorem card_maximal_abelian
    {M : Type} [Group M] [Finite M] (Z E : Subgroup M) (m : ℕ)
    (C : Subgroup M) (hCE : C ≤ E) (hZE : Z ≤ E)
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hCmax : ∀ a ∈ E, (∀ c ∈ C, a * c = c * a) → a ∈ C)
    (hZ : Nat.card Z = 3) (hE : Nat.card E = 3 ^ (m + 1))
    (hZc : ∀ z ∈ Z, ∀ a ∈ E, z * a = a * z)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hexp : ∀ a ∈ E, a ^ 3 ∈ Z)
    (hcen : ∀ a ∈ E, (∀ b ∈ E, a * b = b * a) → a ∈ Z) :
    Nat.card C = 3 ^ (m / 2 + 1) ∧ m % 2 = 0 := by
  have hZ' : Nat.card (Z.subgroupOf E) = 3 := by
    rw [← hZ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  have hZc' : ∀ z ∈ Z.subgroupOf E, ∀ a : ↥E, z * a = a * z := by
    intro z hz a
    apply Subtype.ext
    exact hZc z hz a a.2
  have hcen' : ∀ a : ↥E, (∀ b : ↥E, a * b = b * a) → a ∈ Z.subgroupOf E := by
    intro a ha
    exact hcen a a.2 (fun b hb => by
      have h := congrArg Subtype.val (ha ⟨b, hb⟩)
      simpa using h)
  have hcomm' : ∀ a b : ↥E, a * b * a⁻¹ * b⁻¹ ∈ Z.subgroupOf E := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    simpa using hcomm a a.2 b b.2
  have hexp' : ∀ a : ↥E, a ^ 3 ∈ Z.subgroupOf E := by
    intro a
    rw [Subgroup.mem_subgroupOf]
    simpa using hexp a a.2
  have hCab' : ∀ a ∈ C.subgroupOf E, ∀ b ∈ C.subgroupOf E, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hCab a ha b hb
  have hCmax' : ∀ a : ↥E, (∀ c ∈ C.subgroupOf E, a * c = c * a) → a ∈ C.subgroupOf E := by
    intro a ha
    exact hCmax a a.2 (fun c hc => by
      have h := congrArg Subtype.val (ha ⟨c, hCE hc⟩ hc)
      simpa using h)
  have hExtra := tmExtra_card_maxAbelian (P := ↥E) (Z.subgroupOf E) hZ' hZc' hcen' hcomm' hexp'
    (C.subgroupOf E) hCab' hCmax'
  have hcardC0 : Nat.card (C.subgroupOf E) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCE).toEquiv
  have hcardCsq : Nat.card C ^ 2 = 3 ^ (m + 2) := by
    rw [← hcardC0]
    rw [hExtra]
    rw [hE]
    rw [pow_succ]
    ring
  have hdvd : Nat.card C ∣ 3 ^ (m + 1) := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le hCE
  obtain ⟨k, _hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h1 : ((3 : ℕ) ^ k) ^ 2 = 3 ^ (m + 2) := by
    rw [← hk_eq]
    exact hcardCsq
  have hkmul : k * 2 = m + 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) ((pow_mul 3 k 2).trans h1)
  have hm_even : m % 2 = 0 := by omega
  have hk : k = m / 2 + 1 := by omega
  exact ⟨by rw [hk_eq, hk], hm_even⟩

private theorem weight_eq_one_of_scalar
    {F : Type} [Field F] (d : ℕ) (C' : Subgroup (GL (Fin d) F))
    (χ : ↥C' →* (AlgebraicClosure F)ˣ) (v : Fin d → AlgebraicClosure F) (hv : v ≠ 0)
    (hχv : ∀ a : ↥C',
      (((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map
        (algebraMap F (AlgebraicClosure F))).mulVec v =
          ((χ a : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) • v)
    (a : ↥C') (c : F)
    (ha : ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) c) :
    χ a = 1 → c = 1 := by
  intro hχ1
  have he := hχv a
  rw [ha] at he
  have hmap : (Matrix.scalar (Fin d) c).map (algebraMap F (AlgebraicClosure F))
      = Matrix.scalar (Fin d) (algebraMap F (AlgebraicClosure F) c) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.scalar_apply]
  rw [hmap] at he
  have hsmul : (Matrix.scalar (Fin d) (algebraMap F (AlgebraicClosure F) c)).mulVec v
      = (algebraMap F (AlgebraicClosure F) c) • v := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  rw [hsmul] at he
  have hca : algebraMap F (AlgebraicClosure F) c = (χ a : AlgebraicClosure F) :=
    smul_left_injective (AlgebraicClosure F) hv he
  have h1 : algebraMap F (AlgebraicClosure F) c = algebraMap F (AlgebraicClosure F) 1 := by
    rw [hca, hχ1]; simp
  exact FaithfulSMul.algebraMap_injective F (AlgebraicClosure F) h1

private theorem weight_orbit_le_degree
    {F : Type} [Field F] [Finite F] [CharP F 2] (d m : ℕ)
    {M : Type} [Group M] [Finite M] (Z E M0 C : Subgroup M)
    (hEM0 : E ≤ M0) (hCE : C ≤ E)
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hCmax : ∀ a ∈ E, (∀ c ∈ C, a * c = c * a) → a ∈ C)
    (hCnorm : ∀ x ∈ E, ∀ c ∈ C, x * c * x⁻¹ ∈ C)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hcardC : Nat.card C = 3 ^ (m / 2 + 1)) (hE : Nat.card E = 3 ^ (m + 1))
    (hm_even : m % 2 = 0)
    (ρ : ↥M0 →* GL (Fin d) F) (hρ : Function.Injective ρ)
    (hρZ : ∀ z : ↥M0, (z : M) ∈ Z → ∃ c : F,
      ((ρ z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) c) :
    3 ^ (m / 2) ≤ d := by
  classical
  have hCM0 : C ≤ M0 := hCE.trans hEM0
  let C0 : Subgroup ↥M0 := C.subgroupOf M0
  let E0 : Subgroup ↥M0 := E.subgroupOf M0
  have hC0E0 : C0 ≤ E0 := fun x hx => hCE hx
  let C' : Subgroup (GL (Fin d) F) := C0.map ρ
  let E' : Subgroup (GL (Fin d) F) := E0.map ρ
  have hC'E' : C' ≤ E' := Subgroup.map_mono hC0E0
  have hC'ab : ∀ a ∈ C', ∀ b ∈ C', a * b = b * a := by
    rintro a ⟨a0, ha0, rfl⟩ b ⟨b0, hb0, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hCab a0 ha0 b0 hb0)
  have hcardC' : Nat.card C' = Nat.card C := by
    change Nat.card (C0.map ρ) = Nat.card C
    rw [Subgroup.card_map_of_injective hρ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM0).toEquiv
  have hC'odd : Odd (Nat.card C') := by
    rw [hcardC', hcardC]
    exact Odd.pow (by decide : Odd 3)
  obtain ⟨Λ, hΛcard, hΛeig, hΛsep, hΛstab⟩ := tmWt_weights d C' hC'ab hC'odd
  have hΛne : Λ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hsub : Subsingleton ↥C' := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := hΛsep a (by simp [h])
      have hb : b = 1 := hΛsep b (by simp [h])
      rw [ha, hb]
    have hcard_le : Nat.card C' ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have hgt : 1 < Nat.card C' := by
      rw [hcardC', hcardC]
      exact one_lt_pow' (by norm_num : 1 < 3) (by omega : m / 2 + 1 ≠ 0)
    omega
  obtain ⟨χ, hχΛ⟩ := hΛne
  obtain ⟨v, hv_ne, hv_eig⟩ := hΛeig χ hχΛ
  have hC'norm : ∀ x ∈ E', ∀ c ∈ C', x * c * x⁻¹ ∈ C' := by
    rintro x ⟨x0, hx0, rfl⟩ c ⟨c0, hc0, rfl⟩
    have hmem : x0 * c0 * x0⁻¹ ∈ C0 := hCnorm x0 hx0 c0 hc0
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem ρ hmem
  have hNormal : (C'.subgroupOf E').Normal :=
    (Subgroup.normal_subgroupOf_iff hC'E').mpr (fun h k hh hk => hC'norm k hk h hh)
  let eE0 : ↥E ≃* ↥E0 := (Subgroup.subgroupOfEquivOfLe hEM0).symm
  let eE' : ↥E0 ≃* ↥E' := Subgroup.equivMapOfInjective E0 ρ hρ
  let eC' : ↥C0 ≃* ↥C' := Subgroup.equivMapOfInjective C0 ρ hρ
  let eSub : ↥(C'.subgroupOf E') ≃* ↥C' := Subgroup.subgroupOfEquivOfLe hC'E'
  let gE0 : ↥E0 →* GL (Fin d) F := ρ.comp E0.subtype
  let actFun (x : ↥E) : MulAut ↥C' :=
    { toFun := fun a => eSub (MulAut.conjNormal (eE' (eE0 x)) (eSub.symm a))
      invFun := fun a => eSub ((MulAut.conjNormal (eE' (eE0 x)))⁻¹ (eSub.symm a))
      left_inv := by intro a; simp
      right_inv := by intro a; simp
      map_mul' := by intro a b; simp [map_mul] }
  have eE'_val : ∀ y : ↥E0, ((eE' y : ↥E') : GL (Fin d) F) = gE0 y := by
    intro y
    rw [Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have eSub_val : ∀ y : ↥(C'.subgroupOf E'),
      ((eSub y : ↥C') : GL (Fin d) F) = (y : GL (Fin d) F) := by
    intro y; rfl
  have eSub_symm_val : ∀ y : ↥C',
      (((eSub.symm y : ↥(C'.subgroupOf E')) : ↥E') : GL (Fin d) F) = (y : GL (Fin d) F) := by
    intro y; rfl
  have eC'_val : ∀ c : ↥C0, ((eC' c : ↥C') : GL (Fin d) F) = ρ (c : ↥M0) := by
    intro c
    rw [Subgroup.coe_equivMapOfInjective_apply]
  have act_val : ∀ (x : ↥E) (a : ↥C'),
      (((actFun x) a : ↥C') : GL (Fin d) F)
        = gE0 (eE0 x) * (a : GL (Fin d) F) * (gE0 (eE0 x))⁻¹ := by
    intro x a
    change ((eSub (MulAut.conjNormal (eE' (eE0 x)) (eSub.symm a)) : ↥C') : GL (Fin d) F) = _
    rw [eSub_val]
    rw [MulAut.conjNormal_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [eSub_symm_val, eE'_val]
  let conjC (x : ↥E) (c : ↥C0) : ↥C0 :=
    ⟨⟨(x : M) * (c : M) * (x : M)⁻¹, hCM0 (hCnorm x x.2 (c : M) c.2)⟩,
      hCnorm x x.2 (c : M) c.2⟩
  have act_eC' : ∀ (x : ↥E) (c : ↥C0), (actFun x) (eC' c) = eC' (conjC x c) := by
    intro x c
    apply Subtype.ext
    rw [act_val]
    simp only [eC'_val, conjC]
    have hg : gE0 (eE0 x) = ρ (⟨(x : M), hEM0 x.2⟩ : ↥M0) :=
      congrArg ρ (Subtype.ext rfl)
    have harg : (⟨(x : M) * (c : M) * (x : M)⁻¹, hCM0 (hCnorm x x.2 (c : M) c.2)⟩ : ↥M0)
        = (⟨(x : M), hEM0 x.2⟩ : ↥M0) * (c : ↥M0) * (⟨(x : M), hEM0 x.2⟩ : ↥M0)⁻¹ := by
      ext; rfl
    rw [harg, map_mul, map_mul, map_inv, ← hg]
  have gE0_mem' : ∀ (x : ↥E), x ∈ C.subgroupOf E → gE0 (eE0 x) ∈ C' := by
    intro x hx
    have hx' : gE0 (eE0 x) = (eC' ⟨⟨(x : M), hCM0 hx⟩, hx⟩ : GL (Fin d) F) := by
      calc gE0 (eE0 x) = ρ (eE0 x : ↥M0) := rfl
        _ = ρ ((⟨⟨(x : M), hCM0 hx⟩, hx⟩ : ↥C0) : ↥M0) :=
              congrArg ρ (Subtype.ext rfl)
        _ = (eC' ⟨⟨(x : M), hCM0 hx⟩, hx⟩ : GL (Fin d) F) := (eC'_val _).symm
    rw [hx']
    exact (eC' ⟨⟨(x : M), hCM0 hx⟩, hx⟩ : ↥C').2
  have hfaith : ∀ z : ↥C0, (z : M) ∈ Z → χ (eC' z) = 1 → (z : M) = 1 := by
    intro z hz hχ1
    obtain ⟨c, hc⟩ := hρZ (z : ↥M0) hz
    have ha : (((eC' z : ↥C') : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        = Matrix.scalar (Fin d) c := by
      rw [eC'_val]; exact hc
    have hc1 : c = 1 := weight_eq_one_of_scalar d C' χ v hv_ne hv_eig (eC' z) c ha hχ1
    have hmat : (((eC' z : ↥C') : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [ha, hc1]; simp
    have hunit : (eC' z : ↥C') = 1 := Subtype.ext (Units.ext hmat)
    have hz1 : z = 1 := eC'.injective (by rw [hunit, map_one])
    rw [hz1]; rfl
  let χx (x : ↥E) : ↥C' →* (AlgebraicClosure F)ˣ := χ.comp (actFun x).toMonoidHom
  have hχx_mem : ∀ x : ↥E, χx x ∈ Λ := by
    intro x
    exact hΛstab (gE0 (eE0 x)) (actFun x) (fun a => act_val x a) χ hχΛ
  let H : Subgroup ↥E := C.subgroupOf E
  have : H.Normal := (Subgroup.normal_subgroupOf_iff hCE).mpr (fun h k hh hk => hCnorm k hk h hh)
  have hwd : ∀ a b : ↥E, QuotientGroup.leftRel H a b →
      (⟨χx a, hχx_mem a⟩ : ↥Λ) = ⟨χx b, hχx_mem b⟩ := by
    intro a b hab
    have hwC : (a⁻¹ * b : ↥E) ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hba : b = a * (a⁻¹ * b) := by group
    have hmap : gE0 (eE0 (a * (a⁻¹ * b))) = gE0 (eE0 a) * gE0 (eE0 (a⁻¹ * b)) := by
      rw [map_mul, map_mul]
    have hconj : actFun b = actFun a := by
      apply MulEquiv.ext
      intro d
      apply Subtype.ext
      rw [act_val, act_val, hba, hmap]
      have hcw : gE0 (eE0 (a⁻¹ * b)) ∈ C' := gE0_mem' (a⁻¹ * b) hwC
      have hcomm' : gE0 (eE0 (a⁻¹ * b)) * d = d * gE0 (eE0 (a⁻¹ * b)) :=
        hC'ab _ hcw d d.2
      have hconj2 : gE0 (eE0 (a⁻¹ * b)) * d * (gE0 (eE0 (a⁻¹ * b)))⁻¹ = d := by
        rw [hcomm']; group
      have key : (gE0 (eE0 a) * gE0 (eE0 (a⁻¹ * b))) * d
            * ((gE0 (eE0 a) * gE0 (eE0 (a⁻¹ * b))))⁻¹
          = gE0 (eE0 a) * (gE0 (eE0 (a⁻¹ * b)) * d
              * (gE0 (eE0 (a⁻¹ * b)))⁻¹) * (gE0 (eE0 a))⁻¹ := by group
      rw [key, hconj2]
    have : χx b = χx a := by simp only [χx, hconj]
    exact Subtype.ext this.symm
  let F' : (↥E ⧸ H) → ↥Λ := Quotient.lift (fun x => (⟨χx x, hχx_mem x⟩ : ↥Λ)) hwd
  have hF'inj : Function.Injective F' := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
        apply QuotientGroup.eq.mpr
        have hab : χx a = χx b := by
          have h := Subtype.ext_iff.mp hpq
          simpa only [F', Quotient.lift_mk] using h
        have hcommC : ∀ c ∈ C, (b⁻¹ * a : M) * c = c * (b⁻¹ * a : M) := by
          intro c hc
          let c0 : ↥C0 := ⟨⟨c, hCM0 hc⟩, hc⟩
          have h1 : χ (eC' (conjC a c0)) = χ (eC' (conjC b c0)) := by
            have h := DFunLike.congr_fun hab (eC' c0)
            simp only [χx, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
            rw [act_eC', act_eC'] at h
            exact h
          have h2 : χ (eC' (conjC a c0 * (conjC b c0)⁻¹)) = 1 := by
            simp only [map_mul, map_inv]
            rw [h1]
            simp
          have hid : ((conjC a c0 * (conjC b c0)⁻¹ : ↥C0) : M)
              = ((a : M) * (c : M) * (a : M)⁻¹ * (c : M)⁻¹)
                * (((b : M) * (c : M) * (b : M)⁻¹ * (c : M)⁻¹))⁻¹ := by
            simp only [conjC, c0, Subgroup.coe_mul, Subgroup.coe_inv]
            group
          have hwZ : ((conjC a c0 * (conjC b c0)⁻¹ : ↥C0) : M) ∈ Z := by
            rw [hid]
            exact Z.mul_mem (hcomm a a.2 c (hCE hc)) (Z.inv_mem (hcomm b b.2 c (hCE hc)))
          have hw1 : ((conjC a c0 * (conjC b c0)⁻¹ : ↥C0) : M) = 1 :=
            hfaith (conjC a c0 * (conjC b c0)⁻¹) hwZ h2
          have hcu : (conjC a c0 : M) = (conjC b c0 : M) := by
            have h' : (conjC a c0 : M) * (conjC b c0 : M)⁻¹ = 1 := by simpa using hw1
            exact eq_of_mul_inv_eq_one h'
          have h2' : (a : M) * (c : M) * (a : M)⁻¹ = (b : M) * (c : M) * (b : M)⁻¹ := by
            simpa only [conjC, Subtype.coe_mk] using hcu
          have hstep : ((b : M)⁻¹ * (a : M)) * (c : M) = (c : M) * ((b : M)⁻¹ * (a : M)) := by
            have hb := congrArg (fun t => (b : M)⁻¹ * t * (b : M)) h2'
            rw [show (b : M)⁻¹ * ((b : M) * (c : M) * (b : M)⁻¹) * (b : M) = (c : M)
                from by group] at hb
            rw [show (b : M)⁻¹ * ((a : M) * (c : M) * (a : M)⁻¹) * (b : M)
                = ((b : M)⁻¹ * (a : M)) * (c : M) * ((b : M)⁻¹ * (a : M))⁻¹
                from by group] at hb
            calc ((b : M)⁻¹ * (a : M)) * (c : M)
                = (((b : M)⁻¹ * (a : M)) * (c : M) * ((b : M)⁻¹ * (a : M))⁻¹)
                    * ((b : M)⁻¹ * (a : M)) := by group
              _ = (c : M) * ((b : M)⁻¹ * (a : M)) := by rw [hb]
          exact hstep
        have hmem : (b⁻¹ * a : ↥E) ∈ H :=
          hCmax (b⁻¹ * a) (mul_mem (inv_mem b.2) a.2) hcommC
        have : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by group
        rw [this]
        exact H.inv_mem hmem
  have hΛcard' : Nat.card ↥Λ = Λ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcardQuot : Nat.card (↥E ⧸ H) ≤ d := by
    calc Nat.card (↥E ⧸ H) ≤ Nat.card ↥Λ := Nat.card_le_card_of_injective F' hF'inj
      _ = Λ.card := hΛcard'
      _ ≤ d := hΛcard
  have hcardH : Nat.card H = Nat.card C := by
    change Nat.card (C.subgroupOf E) = Nat.card C
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCE).toEquiv
  have hindex : H.index = 3 ^ (m / 2) := by
    have h := H.index_mul_card
    rw [hcardH, hE, hcardC] at h
    have hpow : 3 ^ (m + 1) = 3 ^ (m / 2 + 1) * 3 ^ (m / 2) := by
      rw [show m + 1 = (m / 2 + 1) + (m / 2) by omega, pow_add]
    rw [hpow] at h
    rw [mul_comm (3 ^ (m / 2 + 1)) (3 ^ (m / 2))] at h
    exact Nat.mul_right_cancel (pow_pos (by norm_num : (0 : ℕ) < 3) _) h
  have hle : 3 ^ (m / 2) ≤ d := by
    rw [← hindex, Subgroup.index_eq_card H]
    exact hcardQuot
  exact hle

theorem tmSemi_core_centerZ {F : Type} [Field F] [Finite F] [CharP F 2] (d m : ℕ)
    (hdm : m % 2 = 1 ∨ d < 3 ^ (m / 2))
    {M : Type} [Group M] [Finite M] (Z E M0 : Subgroup M)
    (hZE : Z ≤ E) (hEM0 : E ≤ M0)
    (hZ : Nat.card Z = 3) (hE : Nat.card E = 3 ^ (m + 1))
    (hZc : ∀ z ∈ Z, ∀ a ∈ E, z * a = a * z)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hexp : ∀ a ∈ E, a ^ 3 ∈ Z)
    (hcen : ∀ a ∈ E, (∀ b ∈ E, a * b = b * a) → a ∈ Z)
    (ρ : ↥M0 →* GL (Fin d) F) (hρ : Function.Injective ρ)
    (hρZ : ∀ z : ↥M0, (z : M) ∈ Z → ∃ c : F,
      ((ρ z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) c) :
    False := by
  obtain ⟨C, hCE, hCab, hCmax, hZC, hCnorm⟩ :=
    exists_maximal_abelian_centerZ Z E hZE hZc hcomm
  obtain ⟨hcardC, hm_even⟩ :=
    card_maximal_abelian Z E m C hCE hZE hCab hCmax hZ hE hZc hcomm hexp hcen
  have hle := weight_orbit_le_degree d m Z E M0 C hEM0 hCE hCab hCmax hCnorm hcomm hcardC hE
    hm_even ρ hρ hρZ
  rcases hdm with hm_odd | hd_lt
  · omega
  · omega

end CFSG.StandardType.FrameRoute

end
