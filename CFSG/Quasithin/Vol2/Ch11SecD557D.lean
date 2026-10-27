module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G25Eight
public import CFSG.Quasithin.H13.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section Sum

variable {F : Type*} [Field F] {r : ℕ} {M Sx N : Subgroup G} {θ : ↥M →* SL(3, F)}
  {φ : ↥Sx →* Multiplicative (Fin r → Fin 3 → F)}

theorem smul_eq_of_conj_eq (hφ : IsSumOfSL3ModulesVia r M Sx N θ φ) (a : ↥M) (x : ↥Sx)
    (hx : (a : G) * x * (a : G)⁻¹ = x) (l : Fin r) :
    θ a • Multiplicative.toAdd (φ x) l = Multiplicative.toAdd (φ x) l :=
  (congrArg (fun w : Multiplicative (Fin r → Fin 3 → F) => Multiplicative.toAdd w l)
    (hφ.2.2 a x x hx.symm)).symm

theorem mem_of_forall_conj_eq (hφ : IsSumOfSL3ModulesVia r M Sx N θ φ) (X : Set ↥M)
    (hfix : ∀ v : Fin 3 → F, (∀ a ∈ X, θ a • v = v) → v = 0) (x : ↥Sx)
    (hx : ∀ a ∈ X, (a : G) * x * (a : G)⁻¹ = x) : (x : G) ∈ N := by
  refine (hφ.2.1 x).mp ?_
  apply Multiplicative.toAdd.injective
  funext l
  exact hfix _ fun a ha => smul_eq_of_conj_eq hφ a x (hx a ha) l

theorem le_commutator_sup_of_span (hφ : IsSumOfSL3ModulesVia r M Sx N θ φ) {A : Subgroup G}
    (hAM : A ≤ M) (hAS : ∀ a ∈ A, ∀ x ∈ Sx, a * x * a⁻¹ ∈ Sx)
    (hspan : ∀ w : Fin 3 → F, w ∈ AddSubgroup.closure
      {u | ∃ v : Fin 3 → F, ∃ a : ↥A, u = v - θ ⟨a, hAM a.2⟩ • v}) :
    Sx ≤ ⁅Sx, A⁆ ⊔ N := by
  classical
  obtain ⟨hs, hk, he⟩ := hφ
  set Q : Subgroup (Multiplicative (Fin r → Fin 3 → F)) := (⁅Sx, A⁆.subgroupOf Sx).map φ
  have hgen : ∀ (l : Fin r) (v : Fin 3 → F) (a : ↥A),
      Multiplicative.ofAdd (Pi.single l (v - θ ⟨a, hAM a.2⟩ • v)) ∈ Q := by
    intro l v a
    obtain ⟨x, hx⟩ := hs (Multiplicative.ofAdd (Pi.single l v))
    let y : ↥Sx := ⟨(a : G) * x * (a : G)⁻¹, hAS a a.2 x x.2⟩
    have hy := he ⟨a, hAM a.2⟩ x y rfl
    refine ⟨x * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have e : ((x * y⁻¹ : ↥Sx) : G) = ⁅(x : G), (a : G)⁆ := by
        simp [y, commutatorElement_def, mul_assoc]
      rw [e]
      exact Subgroup.commutator_mem_commutator x.2 a.2
    · rw [map_mul, map_inv, hy, hx]
      apply Multiplicative.toAdd.injective
      funext l'
      by_cases hl : l' = l
      · subst hl
        simp [sub_eq_add_neg]
      · simp [hl]
  have hsingle : ∀ (l : Fin r) (w : Fin 3 → F), Multiplicative.ofAdd (Pi.single l w) ∈ Q := by
    intro l w
    let B : AddSubgroup (Fin 3 → F) :=
      { carrier := {w | Multiplicative.ofAdd (Pi.single l w) ∈ Q}
        add_mem' := fun {a b} ha hb => by
          change Multiplicative.ofAdd (Pi.single l a) ∈ Q at ha
          change Multiplicative.ofAdd (Pi.single l b) ∈ Q at hb
          show Multiplicative.ofAdd (Pi.single l (a + b)) ∈ Q
          rw [Pi.single_add, ofAdd_add]
          exact Q.mul_mem ha hb
        zero_mem' := by
          show Multiplicative.ofAdd (Pi.single l 0) ∈ Q
          rw [Pi.single_zero, ofAdd_zero]
          exact Q.one_mem
        neg_mem' := fun {a} ha => by
          change Multiplicative.ofAdd (Pi.single l a) ∈ Q at ha
          show Multiplicative.ofAdd (Pi.single l (-a)) ∈ Q
          rw [Pi.single_neg, ofAdd_neg]
          exact Q.inv_mem ha }
    have hle : AddSubgroup.closure
        {u | ∃ v : Fin 3 → F, ∃ a : ↥A, u = v - θ ⟨a, hAM a.2⟩ • v} ≤ B := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, a, rfl⟩
      exact hgen l v a
    exact hle (hspan w)
  have hall : ∀ f : Fin r → Fin 3 → F, Multiplicative.ofAdd f ∈ Q := by
    intro f
    rw [← Finset.univ_sum_single f, ofAdd_sum]
    exact Q.prod_mem fun l _ => hsingle l (f l)
  intro x hx
  obtain ⟨c, hc, hcx⟩ := hall (Multiplicative.toAdd (φ ⟨x, hx⟩))
  have h1 : φ (c⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hcx]
    simp
  have e : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥Sx) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hc))
    (Subgroup.mem_sup_right ((hk _).mp h1))

end Sum

section Kernel

variable {F : Type*} [Field F] {r : ℕ} {Sx N : Subgroup G}
  {φ : ↥Sx →* Multiplicative (Fin r → Fin 3 → F)}

theorem commutator_mem_of_ker (hk : ∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) {a b : G} (ha : a ∈ Sx)
    (hb : b ∈ Sx) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have h := (hk (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹)).mp (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ ⟨a, ha⟩) (φ ⟨b, hb⟩),
      mul_inv_cancel_right, mul_inv_cancel])
  simpa using h

theorem sq_mem_of_ker [CharP F 2] (hk : ∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) {a : G} (ha : a ∈ Sx) :
    a ^ 2 ∈ N := by
  have h := (hk (⟨a, ha⟩ ^ 2)).mp (by
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext l i
    simp only [Pi.smul_apply, Pi.zero_apply, two_nsmul]
    exact CharTwo.add_self_eq_zero _)
  simpa using h

end Kernel

theorem frattini_map_le_of_forall' [Finite G] {P N : Subgroup G} (hP : IsPGroup 2 P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) (hsq : ∀ x ∈ P, x ^ 2 ∈ N) :
    (frattini P).map P.subtype ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, hx | ⟨y, rfl⟩, rfl⟩
  · have h1 : (_root_.commutator P).map P.subtype ≤ N := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      have e : (⊤ : Subgroup P).map P.subtype = P := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [e, Subgroup.commutator_le]
      exact fun a ha b hb => hcomm a ha b hb
    exact h1 ⟨x, hx, rfl⟩
  · exact hsq y y.2

section Nat

variable {n : ℕ} {L K V V₁ : Subgroup G}

theorem span_of_commutator_eq (D : NatData3 n L K V V₁) {A : Subgroup G} (hAL : A ≤ L)
    (hcomm : ⁅V, A⁆ = V) (w : Fin 3 → GaloisField 2 n) :
    w ∈ AddSubgroup.closure
      {u | ∃ v : Fin 3 → GaloisField 2 n, ∃ a : ↥A, u = v - D.θ ⟨a, hAL a.2⟩ • v} := by
  set C := AddSubgroup.closure
    {u | ∃ v : Fin 3 → GaloisField 2 n, ∃ a : ↥A, u = v - D.θ ⟨a, hAL a.2⟩ • v} with hC
  let B : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ V, Multiplicative.toAdd (D.ψ ⟨g, hg⟩) ∈ C}
      mul_mem' := fun {g h} ⟨hg, hgC⟩ ⟨hh, hhC⟩ => by
        refine ⟨V.mul_mem hg hh, ?_⟩
        show Multiplicative.toAdd (D.ψ (⟨g, hg⟩ * ⟨h, hh⟩)) ∈ C
        rw [map_mul, toAdd_mul]
        exact C.add_mem hgC hhC
      one_mem' := by
        refine ⟨V.one_mem, ?_⟩
        show Multiplicative.toAdd (D.ψ 1) ∈ C
        rw [map_one, toAdd_one]
        exact C.zero_mem
      inv_mem' := fun {g} ⟨hg, hgC⟩ => by
        refine ⟨V.inv_mem hg, ?_⟩
        show Multiplicative.toAdd (D.ψ (⟨g, hg⟩⁻¹)) ∈ C
        rw [map_inv, toAdd_inv]
        exact C.neg_mem hgC }
  have hle : ⁅V, A⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have haL : a ∈ L := hAL ha
    have hconj : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (D.hnorm haL) v).mp hv
    have hvV : ⁅v, a⁆ ∈ V := by
      rw [commutatorElement_def]
      have h1 := V.mul_mem hv (V.inv_mem hconj)
      simpa [mul_assoc] using h1
    refine ⟨hvV, ?_⟩
    have e : (⟨⁅v, a⁆, hvV⟩ : ↥V) =
        ⟨v, hv⟩ * (conjAct V ⟨a, D.hnorm haL⟩ ⟨v, hv⟩)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_coe_apply]
      show ⁅v, a⁆ = v * (a * v * a⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    rw [e, map_mul, map_inv, D.equiv ⟨a, haL⟩ ⟨v, hv⟩, toAdd_mul, toAdd_inv, natAct3_apply,
      toAdd_ofAdd, ← sub_eq_add_neg]
    exact AddSubgroup.subset_closure ⟨_, ⟨a, ha⟩, rfl⟩
  have hmem : ((D.ψ.symm (Multiplicative.ofAdd w) : ↥V) : G) ∈ ⁅V, A⁆ := by
    rw [hcomm]
    exact (D.ψ.symm _).2
  obtain ⟨hg, hgC⟩ := hle hmem
  have e : (⟨_, hg⟩ : ↥V) = D.ψ.symm (Multiplicative.ofAdd w) := rfl
  rw [e, MulEquiv.apply_symm_apply, toAdd_ofAdd] at hgC
  exact hgC

theorem fix_eq_zero_of_inf_centralizer (D : NatData3 n L K V V₁) {X : Subgroup G} (hXL : X ≤ L)
    (hfix : V ⊓ Subgroup.centralizer (X : Set G) = ⊥) (v : Fin 3 → GaloisField 2 n)
    (hv : ∀ a : ↥X, D.θ ⟨a, hXL a.2⟩ • v = v) : v = 0 := by
  set c : ↥V := D.ψ.symm (Multiplicative.ofAdd v) with hcdef
  have hc : (c : G) ∈ V ⊓ Subgroup.centralizer (X : Set G) := by
    refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have h2 : D.ψ (conjAct V ⟨a, D.hnorm (hXL ha)⟩ c) = D.ψ c := by
      rw [D.equiv ⟨a, hXL ha⟩ c, natAct3_apply, hcdef, MulEquiv.apply_symm_apply, toAdd_ofAdd,
        hv ⟨a, ha⟩]
    have h3 := congrArg Subtype.val (D.ψ.injective h2)
    rw [conjAct_coe_apply] at h3
    calc a * (c : G) = a * c * a⁻¹ * a := by group
      _ = c * a := by rw [h3]
  rw [hfix] at hc
  have hc1 : c = 1 := Subtype.ext (Subgroup.mem_bot.mp hc)
  have h4 : Multiplicative.ofAdd v = 1 := by
    rw [← D.ψ.apply_symm_apply (Multiplicative.ofAdd v), ← hcdef, hc1, map_one]
  simpa using congrArg Multiplicative.toAdd h4

end Nat

end CFSG.Quasithin.Vol2.Ch11.SecD
