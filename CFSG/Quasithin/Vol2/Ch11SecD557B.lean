module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.Quasithin.Background.G25Eight
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem le_commutator_sup_centralizer [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

theorem commutator_commutator_eq [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  ·
    have hN : X ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
      intro r hr
      apply A4.mem_normalizer_of_conj_mem
      have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj r).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro p hp x hx
        show r * ⁅p, x⁆ * r⁻¹ ∈ ⁅P, X⁆
        have e : r * ⁅p, x⁆ * r⁻¹ = ⁅r * p * r⁻¹, r * x * r⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.commutator_mem_commutator
          ((Subgroup.mem_normalizer_iff.mp (hXP hr) p).mp hp)
          (X.mul_mem (X.mul_mem hr hx) (X.inv_mem hr))
      exact fun y hy => hle hy
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hN
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

omit [Group G] in
theorem eq_one_of_forall_smul_eq {F : Type*} [Field F] (A : SL(3, F))
    (h : ∀ v : Fin 3 → F, A • v = v) : A = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single_one]
    at h1
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using h1

theorem eq_zero_of_isSumOfSL3ModulesVia {F : Type*} [Field F] {r : ℕ} {M Sx N : Subgroup G}
    {θ : ↥M →* SL(3, F)} {φ : ↥Sx →* Multiplicative (Fin r → Fin 3 → F)}
    (hφ : IsSumOfSL3ModulesVia r M Sx N θ φ) (a : ↥M)
    (haS : ∀ x ∈ Sx, (a : G) * x * (a : G)⁻¹ ∈ Sx)
    (htriv : ∀ x ∈ Sx, (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ N) (hθ : θ a ≠ 1) : r = 0 := by
  obtain ⟨hs, hk, he⟩ := hφ
  by_contra hr
  apply hθ
  apply eq_one_of_forall_smul_eq
  intro v
  set l₀ : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  obtain ⟨x, hx⟩ := hs (Multiplicative.ofAdd (Pi.single l₀ v))
  let y : ↥Sx := ⟨(a : G) * x * (a : G)⁻¹, haS x x.2⟩
  have h1 := he a x y rfl
  have h2 : φ y = φ x := by
    have hyx := (hk (y * x⁻¹)).mpr (by simpa [y] using htriv x x.2)
    rw [map_mul, map_inv, mul_inv_eq_one] at hyx
    exact hyx
  rw [h2, hx] at h1
  have h3 := congrArg (fun w : Multiplicative (Fin r → Fin 3 → F) => Multiplicative.toAdd w l₀) h1
  simpa using h3.symm

end CFSG.Quasithin.Vol2.Ch11.SecD
