module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2SpBlock
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedSL StatedSp StatedSU StatedScalars StatedProj)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.ClassicalBlocks CFSG.StandardType.ClassicalPosition


private lemma q2cSpN_add_sq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    {a c : Matrix ι ι F} (h : a * c = c * a) :
    (a + c) * (a + c) = a * a + c * c := by
  have h2 : ∀ x : Matrix ι ι F, x + x = 0 := by
    intro x
    ext i j
    exact CharTwo.add_self_eq_zero (x i j)
  rw [add_mul, mul_add, mul_add, ← h]
  rw [add_assoc, ← add_assoc (a * c) (a * c) (c * c), h2 (a * c), zero_add]

private lemma q2cSpN_formAdj_eq_mul_self {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2) (b : GL (Fin n ⊕ Fin n) F) (hb : b ∈ StatedSp n F)
    (hb3 : b ^ 3 = 1) {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hG : IsUnit G.det)
    (hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)), Commute s s')
    (hSUmap : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F)) *
        G * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = G)
    {a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (ha : a ∈ Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)))) :
    formAdj (RingHom.id F) G a = a * a := by
  let A : Subalgebra F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)))
  have hcommS : (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)) :
      Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise Commute := by
    rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩ _
    show (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (v : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (v : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS u hu v hv).eq
  letI : CommSemiring A := Algebra.adjoinCommSemiringOfComm F hcommS
  have hcommA : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p := by
    intro p hp q hq
    have h := mul_comm (⟨p, hp⟩ : A) (⟨q, hq⟩ : A)
    simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
  have hr : ∀ r : F, r * r = r := by
    intro r
    have h := FiniteField.pow_card r
    rw [hF] at h
    simpa [pow_two] using h
  have hb2inv : b ^ 2 = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ b 2, show (2 : ℕ) + 1 = 3 from rfl, hb3]
  refine Algebra.adjoin_induction
    (p := fun x _ => formAdj (RingHom.id F) G x = x * x) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    have hsb : s = b := Set.mem_singleton_iff.mp hs
    have hs2 : s ^ 2 = s⁻¹ := by
      rw [hsb]
      exact hb2inv
    rw [Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (hSUmap s hs)]
    rw [← hs2, Units.val_pow_eq_pow_val, pow_two]
  · intro r
    have hform : formAdj (RingHom.id F) G
        (algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r) =
        algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r := by
      simp only [Algebra.algebraMap_eq_smul_one, Geo.formAdj_smul,
        Geo.formAdj_one (RingHom.id F) hG, RingHom.id_apply]
    have hmul : algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r *
        algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r =
        algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r := by
      rw [← map_mul, hr r]
    rw [hform, hmul]
  · intro x y hx hy hpx hpy
    rw [Geo.formAdj_add, hpx, hpy]
    rw [q2cSpN_add_sq (hcommA x hx y hy)]
  · intro x y hx hy hpx hpy
    rw [Geo.formAdj_mul (RingHom.id F) hG, hpx, hpy]
    have hA : (⟨y, hy⟩ : A) * ⟨y, hy⟩ * ((⟨x, hx⟩ : A) * ⟨x, hx⟩) =
        ((⟨x, hx⟩ : A) * ⟨y, hy⟩) * ((⟨x, hx⟩ : A) * ⟨y, hy⟩) := by
      ring
    exact congrArg Subtype.val hA

private theorem q2cSpN_blockGroup_two {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2) (b : GL (Fin n ⊕ Fin n) F) (hb : b ∈ StatedSp n F)
    (hb3 : b ^ 3 = 1) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Algebra.adjoin F (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)))) ε) :
    (∃ n₁ : ℕ,
      Nonempty (↥(glBlockCentralizer (StatedSp n F).subtype {b} ε) ≃* ↥(StatedSp n₁ F))) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = Q ^ 2 ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n F).subtype {b} ε) ≃* ↥(GUFull m Q E))) := by
  classical
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  have hG : IsUnit G.det := by
    change IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det
    exact spBlockGram_isUnit_det
  have hGt : Matrix.transpose G = G := by
    change Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Matrix.fromBlocks 0 1 (-1) 0
    exact spBlockGram_transpose
  have hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSUmap : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) F)),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F)) *
        G * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
    simpa [G, Matrix.map_id] using h
  obtain ⟨e, he, heε, hcase⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id F)
    (fun _ => rfl) (G := G) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  have hfix : formAdj (RingHom.id F) G e = e := by
    have hsq := q2cSpN_formAdj_eq_mul_self hF b hb hb3 hG hS hSUmap he.1
    rw [hsq, he.2.1.eq]
  rcases hcase with heq | ⟨hne, hstarne, hεe⟩
  · have heprimε : IsPrimIdemIn (Algebra.adjoin F
        (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) F)))) ε := heq ▸ he
    by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε = ε
    · obtain ⟨n₁, -, ⟨iso⟩⟩ := blockGroup_iso_Sp_one b hb hodd hε h1
      exact Or.inl ⟨n₁, ⟨iso⟩⟩
    · exact Or.inr (spBlockGroup_moved_eq_unitary b hb hodd hε heprimε h1)
  · exact absurd hfix hstarne

theorem q2cSp_statedSp_nonsplit_component_psl {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ d m : ℕ} [NeZero ℓ] (hd : 3 ≤ d) (hF : Nat.card F = 2)
    {s : ↥(CFSG.Open.StatedSp ℓ F)} (hs : s ^ 3 = 1) (hs1 : s ≠ 1)
    {C : Subgroup ↥(CFSG.Open.StatedSp ℓ F)}
    (hC : CFSG.Open.IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSp ℓ F))))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (hne : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K))) : False := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP K 2 := charP_two_of_card hK
  have hF' : Fintype.card F = 2 := by rwa [← Nat.card_eq_fintype_card]
  let b : GL (Fin ℓ ⊕ Fin ℓ) F := (s : GL (Fin ℓ ⊕ Fin ℓ) F)
  have hb : b ∈ StatedSp ℓ F := s.2
  have hb3 : b ^ 3 = 1 := by
    change (s : GL (Fin ℓ ⊕ Fin ℓ) F) ^ 3 = 1
    simpa using congrArg Subtype.val hs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder : orderOf s = 3 := orderOf_eq_prime hs hs1
  have hodd : Odd (orderOf b) := by
    change Odd (orderOf (s : GL (Fin ℓ ⊕ Fin ℓ) F))
    rw [Subgroup.orderOf_coe, horder]
    norm_num
  have hCa : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({s} : Set ↥(StatedSp ℓ F))) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hC
  obtain ⟨P, hPprim, hPorth, hPsum, hPcomm, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp (b : GL (Fin ℓ ⊕ Fin ℓ) F) hb hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(StatedSp ℓ F)) =
      (Subgroup.centralizer {(b : GL (Fin ℓ ⊕ Fin ℓ) F)}).comap
        (StatedSp ℓ F).subtype := by
    change Subgroup.centralizer ({s} : Set ↥(StatedSp ℓ F)) =
      (Subgroup.centralizer {((s : GL (Fin ℓ ⊕ Fin ℓ) F))}).comap
        (StatedSp ℓ F).subtype
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hPsup] at hCa
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P
    (fun ε => glBlockCentralizer (StatedSp ℓ F).subtype {b} ε) hPcomm hCa
  rcases q2cSpN_blockGroup_two hF' b hb hb3 hodd (hPprim ε hε) with
    ⟨n₁, ⟨eS⟩⟩ | ⟨m, Q, E, hEfield, hEfin, hEchar, hEcard, ⟨eU⟩⟩
  · exact l02qq2spb_symp_excl hd hCε eS hne.some
  · exact l02qq2spb_unitary_excl hd hEcard hCε eU hne.some

end CFSG.StandardType
