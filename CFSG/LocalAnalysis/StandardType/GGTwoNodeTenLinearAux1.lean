module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCore
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGReflExtLin
public import CFSG.LocalAnalysis.StandardType.GGMaxRankNine
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleReflRestrict
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tenLinAux_reflTransGen_symm {α : Type} {r : α → α → Prop}
    (hsym : ∀ a b, r a b → r b a) {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact Relation.ReflTransGen.head (hsym _ _ hbc) ih

theorem tenLinAux_tree_conn {ι : Type} [DecidableEq ι] (C : Matrix ι ι ℤ)
    (hT : SecFiveRootRefl.CartanTree C) :
    ∀ i j : ι, Relation.ReflTransGen (fun a b => C a b ≠ 0) i j := by
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  have hedge : ∀ i, i ≠ root → C i (par i) ≠ 0 := by
    intro i hi
    have hne : i ≠ par i := by
      intro he
      have hlt := hdepth i hi
      rw [← he] at hlt
      exact lt_irrefl _ hlt
    exact (hpar i (par i) hne).mpr (Or.inl ⟨hi, rfl⟩)
  have hroot : ∀ i, Relation.ReflTransGen (fun a b => C a b ≠ 0) i root := by
    intro i
    induction hdn : depth i using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      by_cases hi : i = root
      · subst hi; exact Relation.ReflTransGen.refl
      · have hlt : depth (par i) < n := hdn ▸ hdepth i hi
        have hsingle : Relation.ReflTransGen (fun a b => C a b ≠ 0) i (par i) :=
          Relation.ReflTransGen.single (hedge i hi)
        exact hsingle.trans (ih _ hlt (par i) rfl)
  have hsym : ∀ a b, C a b ≠ 0 → C b a ≠ 0 := by
    intro a b hab
    by_cases hab' : a = b
    · subst hab'; exact hab
    · rcases (hpar a b hab').mp hab with ⟨ha, hp⟩ | ⟨hb, hp⟩
      · exact (hpar b a (Ne.symm hab')).mpr (Or.inr ⟨ha, hp⟩)
      · exact (hpar b a (Ne.symm hab')).mpr (Or.inl ⟨hb, hp⟩)
  intro i j
  exact (hroot i).trans (tenLinAux_reflTransGen_symm hsym (hroot j))

theorem tenLinAux_closure_comm {G : Type} [Group G] {ι κ : Type}
    {f : ι → G} {g : κ → G} (hcomm : ∀ i j, f i * g j = g j * f i) :
    ∀ a ∈ Subgroup.closure (Set.range f), ∀ b ∈ Subgroup.closure (Set.range g),
      a * b = b * a := by
  have h1 : Subgroup.closure (Set.range g) ≤ Subgroup.centralizer (Set.range f) := by
    rw [Subgroup.closure_le]
    rintro x ⟨j, rfl⟩
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    rintro y ⟨i, rfl⟩
    exact hcomm i j
  have h2 : Subgroup.closure (Set.range f) ≤
      Subgroup.centralizer (Subgroup.closure (Set.range g)) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro b hb
    exact ((h1 hb) (f i) ⟨i, rfl⟩).symm
  intro a ha b hb
  exact ((h2 ha) b hb).symm

theorem tenLinAux_reflTransGen_lift {α β : Type} {r : α → α → Prop} {p : β → β → Prop}
    (F : α → β) (h : ∀ a b, r a b → p (F a) (F b)) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (F a) (F b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

private theorem tenLinAux_A9_ne_six (a b : Fin 9) : (CoxeterMatrix.A 9).M a b ≠ 6 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem tenLinAux_B9_ne_six (a b : Fin 9) : (CoxeterMatrix.B 9).M a b ≠ 6 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem tenLinAux_D9_ne_six (a b : Fin 9) : (ggCoxeterMatrixD 9).M a b ≠ 6 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem tenLinAux_M_ne_six {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = 9)
    {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) (i j : ι) : M.M i j ≠ 6 := by
  unfold GGIsWeylMatrix at hM
  rcases hM with ⟨n, e, hn, hAD⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · have hn9 : n = 9 := by
      have h := Fintype.card_congr e
      rw [Fintype.card_fin, hcard] at h
      exact h
    subst hn9
    rcases hAD with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · rw [hA, CoxeterMatrix.reindex_apply]
      exact tenLinAux_A9_ne_six _ _
    · rw [hB, CoxeterMatrix.reindex_apply]
      exact tenLinAux_B9_ne_six _ _
    · rw [hD, CoxeterMatrix.reindex_apply]
      exact tenLinAux_D9_ne_six _ _
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard] at h
    omega

theorem tenLinAux_off_cast {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = 9)
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {i j : ι} (hij : i ≠ j) : (C i j : ZMod 3) ≠ 0 ↔ 3 ≤ M.M i j := by
  rcases hC.2 i j hij with ⟨hM2, hCij0, -⟩ | ⟨hM3, hCij, -⟩ | ⟨hM4, hprod, hCi, hCj⟩ |
    ⟨hM6, hprod, hCi, hCj⟩
  · rw [hM2, hCij0]; norm_num
  · rw [hM3, hCij]; norm_num
  · have hndvd : ¬ (3 : ℤ) ∣ C i j := by
      intro hdvd
      have h32 : (3 : ℤ) ∣ 2 := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hdvd (C j i)
      norm_num at h32
    rw [hM4]
    exact ⟨fun _ => by norm_num, fun _ hzero =>
      hndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd (C i j) 3).mp hzero)⟩
  · exact absurd hM6 (tenLinAux_M_ne_six hcard hM i j)

theorem tenLinAux_A8_cast (i j : Fin 8) :
    (CartanMatrix.A 8 i j : ZMod 3) ≠ 0 ↔ CartanMatrix.A 8 i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem tenLinAux_zero_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type}
    (h : ι → V) (α : ι → Module.Dual (ZMod 3) V) (r : ι → V ≃ₗ[ZMod 3] V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hα : ∀ i, α i (h i) = 2)
    (hr : ∀ i v, r i v = v - α i v • h i)
    (hA : A = Subgroup.closure (Set.range r))
    (hnt : ∀ g ∈ A, ¬ CFSG.TwoNodeSmall.IsTransv g) :
    ∀ a b : ι, α a (h b) = 0 ↔ α b (h a) = 0 := by
  have key : ∀ a b : ι, α a (h b) = 0 → α b (h a) = 0 := by
    intro a b hab
    by_contra hba
    have hmem : r a * r b * r a * r b ∈ A := by
      rw [hA]
      exact mul_mem (mul_mem (mul_mem (Subgroup.subset_closure ⟨a, rfl⟩)
        (Subgroup.subset_closure ⟨b, rfl⟩)) (Subgroup.subset_closure ⟨a, rfl⟩))
        (Subgroup.subset_closure ⟨b, rfl⟩)
    exact hnt _ hmem (CFSG.ReflExt.refl_asym_transv (p := 3) (by norm_num) (r a) (r b)
      (α a) (α b) (h a) (h b) (hr a) (hr b) (hα a) (hα b) hab hba)
  intro a b
  exact ⟨key a b, key b a⟩

theorem tenLinAux_comm_of_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type}
    (h : ι → V) (α : ι → Module.Dual (ZMod 3) V) (r : ι → V ≃ₗ[ZMod 3] V)
    (hr : ∀ i v, r i v = v - α i v • h i) {a b : ι}
    (hab : α a (h b) = 0) (hba : α b (h a) = 0) : r a * r b = r b * r a := by
  ext v
  simp only [LinearEquiv.mul_apply, hr, map_sub, map_smul, smul_eq_mul, hab, hba,
    mul_zero, sub_zero]
  abel

theorem tenLinAux_stabilizer_card {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (x : V) :
    Nat.card (MulAction.stabilizer ↥A x) =
      Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) := by
  have hstab_eq : MulAction.stabilizer ↥A x =
      (A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x).subgroupOf A := by
    ext a
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  rw [hstab_eq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem tenLinAux_orbit_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (hdim : Module.finrank (ZMod 3) V = 10) (A : Subgroup (V ≃ₗ[ZMod 3] V)) (x : V) :
    Nat.card (MulAction.orbit ↥A x) ≤ 3 ^ 10 := by
  have h1 : Nat.card (MulAction.orbit ↥A x) ≤ Nat.card V :=
    Nat.card_le_card_of_injective (fun v : MulAction.orbit ↥A x => (v : V))
      Subtype.val_injective
  rwa [← FiniteField.pow_finrank_eq_natCard 3 V, hdim] at h1


theorem tenLinAux_reflTransGen_imp {α : Type} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen s a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

private theorem tenLinAux_cast_ne_zero_iff_bond
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {σ : Type}
    (h : σ → V) (α : σ → Module.Dual (ZMod 3) V) (r : σ → V ≃ₗ[ZMod 3] V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hα : ∀ i, α i (h i) = 2)
    (hr : ∀ i v, r i v = v - α i v • h i)
    (hA : A = Subgroup.closure (Set.range r))
    (hnt : ∀ g ∈ A, ¬ CFSG.TwoNodeSmall.IsTransv g)
    {ι : Type} (e : ι → σ) {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) (hP : ∀ i j, α (e i) (h (e j)) = (C i j : ZMod 3))
    {i j : ι} (hij : i ≠ j) : (C i j : ZMod 3) ≠ 0 ↔ 3 ≤ M.M i j := by
  have hz : (C i j : ZMod 3) = 0 ↔ (C j i : ZMod 3) = 0 := by
    simpa only [hP i j, hP j i] using
      tenLinAux_zero_iff h α r A hα hr hA hnt (e i) (e j)
  rcases hC.2 i j hij with ⟨hM2, hCij, -⟩ | ⟨hM3, hCij, -⟩ |
    ⟨hM4, hprod, -, -⟩ | ⟨-, hprod, -, -⟩
  · rw [hM2, hCij]
    norm_num
  · rw [hM3, hCij]
    norm_num
  · have hnd : ¬ (3 : ℤ) ∣ C i j := by
      intro hd
      have h32 : (3 : ℤ) ∣ 2 := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hd (C j i)
      exact absurd h32 (by norm_num)
    rw [hM4]
    exact ⟨fun _ => by norm_num, fun _ h0 =>
      hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd (C i j) 3).mp h0)⟩
  · have hprod0 : (C i j : ZMod 3) * (C j i : ZMod 3) = 0 := by
      rw [← Int.cast_mul, hprod]
      decide
    have hboth : (C i j : ZMod 3) = 0 ∧ (C j i : ZMod 3) = 0 := by
      rcases mul_eq_zero.mp hprod0 with h0 | h0
      · exact ⟨h0, hz.mp h0⟩
      · exact ⟨hz.mpr h0, h0⟩
    have h3ij : (3 : ℤ) ∣ C i j :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j) 3).mp hboth.1
    have h3ji : (3 : ℤ) ∣ C j i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (C j i) 3).mp hboth.2
    obtain ⟨a, ha⟩ := h3ij
    obtain ⟨b, hb⟩ := h3ji
    have h9 : (9 : ℤ) ∣ C i j * C j i := ⟨a * b, by rw [ha, hb]; ring⟩
    rw [hprod] at h9
    exact absurd h9 (by norm_num)

theorem tenLinAux_join_connected_of_shared
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Λ : Type} [Fintype Λ] {Λa : Type} [Fintype Λa]
    (S : Finset Λ) (hS : Nonempty {i : Λ // i ∉ S})
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hWML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hα : ∀ i, α i (h i) = 2) (hr : ∀ i v, r i v = v - α i v • h i)
    (hA : A = Subgroup.closure (Set.range r))
    (hnt : ∀ g ∈ A, ¬ CFSG.TwoNodeSmall.IsTransv g)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ i j : {i : Λ // i ∉ S} ⊕ Λa,
      α (i.map Subtype.val id) (h (j.map Subtype.val id)) = (CK i j : ZMod 3)) :
    ∀ i j : Λ ⊕ Λa, Relation.ReflTransGen
      (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j := by
  classical
  have hziff := tenLinAux_zero_iff h α r A hα hr hA hnt
  have hcastL : ∀ {i j : Λ}, i ≠ j → ((CL i j : ZMod 3) ≠ 0 ↔ 3 ≤ ML.M i j) := by
    intro i j hij
    exact tenLinAux_cast_ne_zero_iff_bond h α r A hα hr hA hnt Sum.inl hCL hpairL hij
  have hcastK : ∀ {i j : {i : Λ // i ∉ S} ⊕ Λa}, i ≠ j →
      ((CK i j : ZMod 3) ≠ 0 ↔ 3 ≤ MK.M i j) := by
    intro i j hij
    exact tenLinAux_cast_ne_zero_iff_bond h α r A hα hr hA hnt
      (Sum.map (Subtype.val : {i : Λ // i ∉ S} → Λ) id) hCK hpairK hij
  obtain ⟨CLt, hCLtree, hCLbonds⟩ := ggFLW_cartanTree_bonds hWML
  obtain ⟨CKt, hCKtree, hCKbonds⟩ := ggFLW_cartanTree_bonds hWMK
  have hLconn : ∀ a b : Λ, Relation.ReflTransGen
      (fun x y : Λ ⊕ Λa => α x (h y) ≠ 0) (Sum.inl a) (Sum.inl b) := by
    intro a b
    refine tenLinAux_reflTransGen_lift (F := Sum.inl) (h := ?_)
      (tenLinAux_tree_conn CLt hCLtree a b)
    intro x y hxy
    by_cases hxy' : x = y
    · have hdiag : α (Sum.inl x) (h (Sum.inl x)) ≠ 0 := by
        rw [hα (Sum.inl x)]
        decide
      simpa [hxy'] using hdiag
    · have hM3 : 3 ≤ ML.M x y := (hCLbonds x y hxy').mp hxy
      have hCLne : (CL x y : ZMod 3) ≠ 0 := (hcastL hxy').mpr hM3
      rw [hpairL x y]
      exact hCLne
  have hKconn : ∀ a b : {i : Λ // i ∉ S} ⊕ Λa, Relation.ReflTransGen
      (fun x y : Λ ⊕ Λa => α x (h y) ≠ 0)
      (a.map Subtype.val id) (b.map Subtype.val id) := by
    intro a b
    refine tenLinAux_reflTransGen_lift
      (F := fun z : {i : Λ // i ∉ S} ⊕ Λa => z.map Subtype.val id) (h := ?_)
      (tenLinAux_tree_conn CKt hCKtree a b)
    intro x y hxy
    by_cases hxy' : x = y
    · have hdiag : α (x.map Subtype.val id) (h (x.map Subtype.val id)) ≠ 0 := by
        rw [hα (x.map Subtype.val id)]
        decide
      simpa [hxy'] using hdiag
    · have hM3 : 3 ≤ MK.M x y := (hCKbonds x y hxy').mp hxy
      have hCKne : (CK x y : ZMod 3) ≠ 0 := (hcastK hxy').mpr hM3
      rw [hpairK x y]
      exact hCKne
  obtain ⟨p⟩ := hS
  have hsymm : ∀ a b : Λ ⊕ Λa, α a (h b) ≠ 0 → α b (h a) ≠ 0 := by
    intro a b hab h0
    exact hab ((hziff a b).mpr h0)
  have hto : ∀ o : Λ ⊕ Λa, Relation.ReflTransGen
      (fun a b : Λ ⊕ Λa => α a (h b) ≠ 0) o (Sum.inl p.1) := by
    intro o
    rcases o with a | b
    · exact hLconn a p.1
    · simpa using hKconn (Sum.inr b) (Sum.inl ⟨p.1, p.2⟩)
  intro i j
  have hconn : Relation.ReflTransGen (fun a b : Λ ⊕ Λa => α a (h b) ≠ 0) i j :=
    (hto i).trans (tenLinAux_reflTransGen_symm hsymm (hto j))
  exact tenLinAux_reflTransGen_imp (fun a b hab => ⟨hab, hsymm a b hab⟩) hconn

end CFSG.StandardType

end
