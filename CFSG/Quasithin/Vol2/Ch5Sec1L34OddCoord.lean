module

public import CFSG.Quasithin.Vol2.Ch6NatSemi
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL exists_conj_unip)
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure OddCoord (T L V : Subgroup G) (n : ℕ) : Type 1 where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  card : Nat.card K = 2 ^ n
  ε : ↥V → (Fin 2 → K)
  ε_mul : ∀ v w : ↥V, ε (v * w) = ε v + ε w
  ε_bij : Function.Bijective ε
  act : Subgroup.normalizer (V : Set G) → (Fin 2 → K) → (Fin 2 → K)
  act_ε : ∀ g v, act g (ε v) = ε (conjAct V g v)
  mat : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ L →
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ w, act g w = (A : Matrix (Fin 2) (Fin 2) K).mulVec w
  unip : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ T ⊓ L →
    ∃ b : K, ∀ w, act g w = (unipSL b : Matrix (Fin 2) (Fin 2) K).mulVec w
  unip_surj : ∀ b : K, ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ T ⊓ L ∧
    ∀ w, act g w = (unipSL b : Matrix (Fin 2) (Fin 2) K).mulVec w
  semi : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ Subgroup.normalizer (L : Set G) →
    ∃ σ : K ≃+* K, ∀ (a : K) (w : Fin 2 → K), act g (a • w) = σ a • act g w

attribute [instance] OddCoord.instField OddCoord.instFinite OddCoord.instChar

theorem sl2_eq_of_mulVec_eq {K : Type} [Field K] {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : ∀ w, (A : Matrix (Fin 2) (Fin 2) K).mulVec w = (B : Matrix (Fin 2) (Fin 2) K).mulVec w) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem IsNatModCh5.nonempty_oddCoord [Finite G] {T L V : Subgroup G} {n : ℕ}
    (hV : IsNatModCh5 L V n) (hn : 1 ≤ n) (hTL : IsSylowTwoOf (T ⊓ L) L) :
    Nonempty (OddCoord T L V n) := by
  obtain ⟨D₀⟩ := hV.nonempty_data
  have : CharP D₀.K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) D₀.card
  have hLV := D₀.le_normalizer
  have hmat : ∀ g : ↥L, ∃ A : Matrix.SpecialLinearGroup (Fin 2) D₀.K,
      ∀ w, D₀.conj ⟨g, hLV g.2⟩ w = (A : Matrix (Fin 2) (Fin 2) D₀.K).mulVec w :=
    fun g => D₀.exists_matrix_of_mem ⟨g, hLV g.2⟩ g.2
  choose matOf hmatOf using hmat
  have hone : D₀.conj (1 : Subgroup.normalizer (V : Set G)) = AddEquiv.refl _ := by
    ext w i
    change Multiplicative.toAdd (D₀.E (conjAct V 1 (D₀.E.symm (Multiplicative.ofAdd w)))) i = w i
    rw [map_one, MulAut.one_apply, MulEquiv.apply_symm_apply]
    rfl
  let ψ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) D₀.K :=
    { toFun := matOf
      map_one' := sl2_eq_of_mulVec_eq fun w => by
        rw [← hmatOf, show (⟨((1 : ↥L) : G), hLV (1 : ↥L).2⟩ : Subgroup.normalizer (V : Set G)) =
          1 from rfl, hone]
        simp
      map_mul' := fun g h => sl2_eq_of_mulVec_eq fun w => by
        rw [← hmatOf, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hmatOf,
          ← hmatOf, ← D₀.conj_mul]
        rfl }
  have hψ : ∀ g : ↥L, ∀ w, D₀.conj ⟨g, hLV g.2⟩ w = (ψ g : Matrix (Fin 2) (Fin 2) D₀.K).mulVec w :=
    hmatOf
  have hψs : Function.Surjective ψ := by
    intro A
    obtain ⟨g, hgL, hg⟩ := D₀.exists_mem_of_matrix A
    refine ⟨⟨g, hgL⟩, sl2_eq_of_mulVec_eq fun w => ?_⟩
    rw [← hψ, ← hg]
  set P := ((T ⊓ L).subgroupOf L).map ψ with hPdef
  have hP2 : IsPGroup 2 P :=
    (hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL.1).symm).map ψ
  have hPidx : ¬ 2 ∣ P.index := fun h2 =>
    hTL.2.2 (h2.trans (Subgroup.index_map_dvd _ hψs))
  obtain ⟨g₀, hg₀P, hg₀U⟩ := exists_conj_unip D₀.card hP2 hPidx
  have h01 : ∀ w, (g₀ : Matrix (Fin 2) (Fin 2) D₀.K).mulVec
      (((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) D₀.K) : Matrix (Fin 2) (Fin 2) D₀.K).mulVec w) =
        w := fun w => by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have h10 : ∀ w, ((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) D₀.K) :
      Matrix (Fin 2) (Fin 2) D₀.K).mulVec ((g₀ : Matrix (Fin 2) (Fin 2) D₀.K).mulVec w) = w :=
    fun w => by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨{ K := D₀.K
            card := D₀.card
            ε := fun v => (g₀ : Matrix (Fin 2) (Fin 2) D₀.K).mulVec (Multiplicative.toAdd (D₀.E v))
            ε_mul := fun v w => by
              simp only [map_mul, toAdd_mul, Matrix.mulVec_add]
            ε_bij := ⟨fun v w h => D₀.E.injective (Multiplicative.toAdd.injective (by
                have := congrArg (((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) D₀.K) :
                  Matrix (Fin 2) (Fin 2) D₀.K).mulVec) h
                simpa only [h10] using this)),
              fun w => ⟨D₀.E.symm (Multiplicative.ofAdd (((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2)
                  D₀.K) : Matrix (Fin 2) (Fin 2) D₀.K).mulVec w)), by
                simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, h01]⟩⟩
            act := fun g w => (g₀ : Matrix (Fin 2) (Fin 2) D₀.K).mulVec (D₀.conj g
              (((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) D₀.K) :
                Matrix (Fin 2) (Fin 2) D₀.K).mulVec w))
            act_ε := fun g v => by
              simp only [h10, D₀.conj_apply]
            mat := fun g hgL => ⟨g₀ * ψ ⟨g, hgL⟩ * g₀⁻¹, fun w => by
              have h1 : D₀.conj g = D₀.conj ⟨((⟨g, hgL⟩ : ↥L) : G), hLV hgL⟩ := rfl
              simp only [h1, hψ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]⟩
            unip := fun g hg => by
              obtain ⟨b, hb⟩ := hg₀P (ψ ⟨g, hg.2⟩) ⟨⟨g, hg.2⟩, hg, rfl⟩
              refine ⟨b, fun w => ?_⟩
              have h1 : D₀.conj g = D₀.conj ⟨((⟨g, hg.2⟩ : ↥L) : G), hLV hg.2⟩ := rfl
              rw [← hb]
              simp only [h1, hψ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
            unip_surj := fun b => by
              obtain ⟨x, hx, hxb⟩ := hg₀U b
              refine ⟨⟨x, hLV x.2⟩, hx, fun w => ?_⟩
              show (g₀ : Matrix (Fin 2) (Fin 2) D₀.K).mulVec (D₀.conj ⟨x, hLV x.2⟩
                (((g₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) D₀.K) :
                  Matrix (Fin 2) (Fin 2) D₀.K).mulVec w)) = _
              rw [hψ x, hxb]
              simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h01]
            semi := fun g hg => by
              obtain ⟨σ, hσ⟩ := D₀.exists_semilinear g hg
              exact ⟨σ, fun a w => by
                simp only [Matrix.mulVec_smul, hσ]⟩ }⟩

end CFSG.Quasithin.H13
