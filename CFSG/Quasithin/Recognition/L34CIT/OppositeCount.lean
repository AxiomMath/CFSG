module

public import CFSG.Quasithin.Recognition.L34CIT.Opposite

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

@[expose] def nonidentityInvolutions (H : Subgroup A) : Set A := {e | e * e = 1 ∧ e ≠ 1 ∧ e ∈ H}

private theorem ncard_nonidentityInvolutions_of_elemAbelian {H : Subgroup A}
    (hea : IsElemAbelian 2 H) :
    (nonidentityInvolutions H).ncard = Nat.card ↥H - 1 := by
  have hset : nonidentityInvolutions H = (H : Set A) \ {1} := by
    ext e
    constructor
    · rintro ⟨-, he1, heH⟩
      exact ⟨heH, fun h => he1 (by simpa using h)⟩
    · rintro ⟨heH, he1⟩
      refine ⟨?_, fun h => he1 (by simpa using h), heH⟩
      have := hea.2 e heH
      simpa [pow_two] using this
  rw [hset, Set.ncard_diff_singleton_of_mem (H.one_mem)]
  rfl

namespace Config

@[expose] def OppositeCount (C : Config A) : Prop :=
  {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥}.ncard = 64

theorem ncard_nonidentityInvolutions_L (C : Config A) [Finite A] :
    (nonidentityInvolutions C.L).ncard = 15 := by
  rw [ncard_nonidentityInvolutions_of_elemAbelian C.isElemAbelian_L, C.card_L]

theorem ncard_nonidentityInvolutions_point (C : Config A) [Finite A] (P : Sylow 2 A) :
    (nonidentityInvolutions (C.point P)).ncard = 15 := by
  rw [ncard_nonidentityInvolutions_of_elemAbelian (C.point_ea P), C.card_point P]

theorem ncard_nonidentityInvolutions_line (C : Config A) [Finite A] (P : Sylow 2 A) :
    (nonidentityInvolutions (C.line P)).ncard = 15 := by
  rw [ncard_nonidentityInvolutions_of_elemAbelian (C.line_ea P), C.card_line P]

theorem nonidentityInvolutions_sylow_eq (C : Config A) [Finite A] (P : Sylow 2 A) :
    nonidentityInvolutions (P : Subgroup A) =
      nonidentityInvolutions (C.point P) ∪ nonidentityInvolutions (C.line P) := by
  ext e
  constructor
  · rintro ⟨he2, he1, heP⟩
    rcases C.mem_point_or_line heP he2 he1 with h | h
    · exact Or.inl ⟨he2, he1, h⟩
    · exact Or.inr ⟨he2, he1, h⟩
  · rintro (⟨he2, he1, h⟩ | ⟨he2, he1, h⟩)
    · exact ⟨he2, he1, C.point_le P h⟩
    · exact ⟨he2, he1, C.line_le P h⟩

theorem ncard_nonidentityInvolutions_sylow (C : Config A) [Finite A] (P : Sylow 2 A) :
    (nonidentityInvolutions (P : Subgroup A)).ncard = 27 := by
  have hcap : nonidentityInvolutions (C.point P) ∩ nonidentityInvolutions (C.line P) =
      nonidentityInvolutions (C.point P ⊓ C.line P) := by
    ext e
    constructor
    · rintro ⟨⟨he2, he1, h1⟩, ⟨-, -, h2⟩⟩
      exact ⟨he2, he1, h1, h2⟩
    · rintro ⟨he2, he1, h1, h2⟩
      exact ⟨⟨he2, he1, h1⟩, ⟨he2, he1, h2⟩⟩
  have hea : IsElemAbelian 2 (C.point P ⊓ C.line P) := by
    refine ⟨isMulCommutative_iff.mpr fun x y => Subtype.ext ?_, fun x hx => ?_⟩
    · show ((x : A) * y) = ((y : A) * x)
      haveI : IsMulCommutative ↥(C.point P) := (C.point_ea P).1
      exact congrArg Subtype.val
        (mul_comm' (⟨x.1, x.2.1⟩ : ↥(C.point P)) ⟨y.1, y.2.1⟩)
    · exact (C.point_ea P).2 x hx.1
  have h := Set.ncard_union_add_ncard_inter (nonidentityInvolutions (C.point P))
    (nonidentityInvolutions (C.line P))
  rw [← C.nonidentityInvolutions_sylow_eq, hcap, C.ncard_nonidentityInvolutions_point,
    C.ncard_nonidentityInvolutions_line, ncard_nonidentityInvolutions_of_elemAbelian hea,
    C.card_inf_point_line_sylow P] at h
  omega

theorem mem_point_line_of_central (C : Config A) [Finite A] {P : Sylow 2 A} {e : A}
    (heP : e ∈ (P : Subgroup A)) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hcent : ∀ y ∈ (P : Subgroup A), e * y = y * e) :
    e ∈ C.point P ⊓ C.line P := by
  by_contra hmem
  have hcen : centralizer ({e} : Set A) = (P : Subgroup A) :=
    C.centralizer_eq_of_mem_center he2 he1 heP hcent
  rcases C.mem_point_or_line heP he2 he1 with h | h
  · have h1 : centralizer ({e} : Set A) ⊓ (P : Subgroup A) = C.point P :=
      C.centralizer_point h hmem
    rw [hcen, inf_idem] at h1
    have hcard := C.card_point P
    rw [← h1, C.card_sylow P, C.card_T] at hcard
    norm_num at hcard
  · have h1 : centralizer ({e} : Set A) ⊓ (P : Subgroup A) = C.line P :=
      C.centralizer_line h hmem
    rw [hcen, inf_idem] at h1
    have hcard := C.card_line P
    rw [← h1, C.card_sylow P, C.card_T] at hcard
    norm_num at hcard

private def centreFiberEquiv (C : Config A) [Finite A] (P : Sylow 2 A) :
    {e : A // e * e = 1 ∧ e ≠ 1 ∧ e ∈ C.point P ⊓ C.line P} ≃
      {x : ↥(C.point P ⊓ C.line P) // x ≠ 1} where
  toFun e := ⟨⟨e.1, e.2.2.2⟩, fun h => e.2.2.1 (congrArg Subtype.val h)⟩
  invFun x := ⟨x.1.1, by
    have := (C.point_ea P).2 x.1.1 x.1.2.1
    simpa [pow_two] using this, fun h => x.2 (Subtype.ext h), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_fiber_centre (C : Config A) [Finite A] (P : Sylow 2 A) :
    Nat.card {e : A // e * e = 1 ∧ e ≠ 1 ∧ e ∈ C.point P ⊓ C.line P} = 3 := by
  rw [Nat.card_congr (centreFiberEquiv C P)]
  have hset : {x : ↥(C.point P ⊓ C.line P) | x ≠ 1} =
      (Set.univ : Set ↥(C.point P ⊓ C.line P)) \ {1} := by
    ext x
    simp
  rw [show Nat.card {x : ↥(C.point P ⊓ C.line P) // x ≠ 1} =
      ({x : ↥(C.point P ⊓ C.line P) | x ≠ 1}).ncard from rfl]
  rw [hset, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
    C.card_inf_point_line_sylow P]

theorem ncard_involutions (C : Config A) [Finite A] :
    {e : A | e * e = 1 ∧ e ≠ 1}.ncard = 3 * Nat.card (Sylow 2 A) := by
  classical
  haveI : Fintype (Sylow 2 A) := Fintype.ofFinite _
  have hsum : Nat.card (Σ P : Sylow 2 A,
      {e : A // e * e = 1 ∧ e ≠ 1 ∧ e ∈ C.point P ⊓ C.line P}) =
      3 * Nat.card (Sylow 2 A) := by
    rw [Nat.card_sigma]
    have hcongr : (∑ P : Sylow 2 A, Nat.card
        {e : A // e * e = 1 ∧ e ≠ 1 ∧ e ∈ C.point P ⊓ C.line P}) =
        ∑ _ : Sylow 2 A, 3 :=
      Finset.sum_congr rfl fun P _ => C.card_fiber_centre P
    rw [hcongr, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul,
      mul_comm]
  have hbij : Nat.card (Σ P : Sylow 2 A,
      {e : A // e * e = 1 ∧ e ≠ 1 ∧ e ∈ C.point P ⊓ C.line P}) =
      Nat.card {e : A // e * e = 1 ∧ e ≠ 1} := by
    refine Nat.card_eq_of_bijective (fun pe => ⟨pe.2.1, pe.2.2.1, pe.2.2.2.1⟩)
      ⟨fun x y hEq => ?_, fun e => ?_⟩
    ·
      obtain ⟨P, e⟩ := x
      obtain ⟨Q, f⟩ := y
      have hval : (e : A) = f.1 := congrArg Subtype.val hEq
      have hP : P = Q := by
        have he2 : (e : A) * e = 1 := e.2.1
        have he1 : (e : A) ≠ 1 := e.2.2.1
        have hce : centralizer ({(e : A)} : Set A) = (P : Subgroup A) :=
          C.centralizer_eq_of_mem_center he2 he1 (C.point_le P e.2.2.2.1) fun y hy =>
            (Subgroup.mem_centralizer_iff.mp (C.inf_le_centralizer_point_line P e.2.2.2) y hy).symm
        have hcf : centralizer ({(e : A)} : Set A) = (Q : Subgroup A) :=
          C.centralizer_eq_of_mem_center (hval ▸ f.2.1) (by rw [hval]; exact f.2.2.1)
            (hval ▸ C.point_le Q f.2.2.2.1) fun y hy =>
              (Subgroup.mem_centralizer_iff.mp (hval ▸ C.inf_le_centralizer_point_line Q f.2.2.2)
                y hy).symm
        exact Sylow.ext (hce.symm.trans hcf)
      subst hP
      have hfe : e = f := Subtype.ext hval
      subst hfe
      rfl
    ·
      obtain ⟨e, he2, he1⟩ := e
      obtain ⟨P, hP⟩ := C.exists_sylow_eq_centralizer he2 he1
      have heP : (e : A) ∈ (P : Subgroup A) := by
        rw [← hP]
        exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
      have hmem : (e : A) ∈ C.point P ⊓ C.line P :=
        C.mem_point_line_of_central heP he2 he1 fun y hy => by
          rw [← hP] at hy
          exact Subgroup.mem_centralizer_iff.mp hy e (Set.mem_singleton _)
      exact ⟨⟨P, ⟨e, he2, he1, hmem⟩⟩, rfl⟩
  change Nat.card {e : A // e * e = 1 ∧ e ≠ 1} = 3 * Nat.card (Sylow 2 A)
  rw [← hbij, hsum]

theorem exists_sylowThroughL_of_mem (C : Config A) [Finite A] {e : A} (he2 : e * e = 1)
    (he1 : e ≠ 1) (he : e ∈ C.K₁) :
    ∃ P : Sylow 2 A, C.L ≤ (P : Subgroup A) ∧ e ∈ (P : Subgroup A) := by
  have hH : IsPGroup 2 ↥(Subgroup.zpowers e) :=
    (CFSG.Open.isElemAbelian_zpowers (p := 2) (by rwa [pow_two])).isPGroup
  have hK : IsPGroup 2 ↥C.L := C.isElemAbelian_L.isPGroup
  have hHK : Subgroup.zpowers e ≤ normalizer (C.L : Set A) := by
    rw [Subgroup.zpowers_le]
    exact he
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers e ⊔ C.L) := hH.to_sup_of_normal_right' hK hHK
  obtain ⟨P, hP⟩ := hsup.exists_le_sylow
  exact ⟨P, le_trans le_sup_right hP, hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers e))⟩

theorem ncard_involutions_sylow_sdiff (C : Config A) [Finite A] (P : Sylow 2 A)
    (hP : C.L ≤ (P : Subgroup A)) :
    Nat.card {e : A // e ∈ nonidentityInvolutions (P : Subgroup A) ∧
      e ∉ nonidentityInvolutions C.L} = 12 := by
  have hsub : nonidentityInvolutions C.L ⊆ nonidentityInvolutions (P : Subgroup A) := by
    rintro e ⟨he2, he1, heL⟩
    exact ⟨he2, he1, hP heL⟩
  have hcoe : Nat.card {e : A // e ∈ nonidentityInvolutions (P : Subgroup A) ∧
      e ∉ nonidentityInvolutions C.L} =
      (nonidentityInvolutions (P : Subgroup A) \ nonidentityInvolutions C.L).ncard := rfl
  rw [hcoe, Set.ncard_sdiff hsub, C.ncard_nonidentityInvolutions_sylow P,
    C.ncard_nonidentityInvolutions_L]

end Config

end CFSG.Quasithin.L34CIT
