module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer_Sp
    {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : StatedSp n K) (hodd : Odd (orderOf b))
    (J : Subgroup (StatedSp n K)) (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {b})) :
    ∃ ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
      IsPrimAdjIdemIn (RingHom.id K)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (Algebra.adjoin K (Units.val '' ({(b : GL (Fin n ⊕ Fin n) K)} :
          Set (GL (Fin n ⊕ Fin n) K)))) ε ∧
      CFSG.Assembly.IsComponentOf J
        (glBlockCentralizer (StatedSp n K).subtype
          ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε) := by
  have hodd' : Odd (orderOf (b : GL (Fin n ⊕ Fin n) K)) := by simpa using hodd
  obtain ⟨P, hP, _, _, hc, hsup, _⟩ :=
    centralizer_block_decomp_Sp (b : GL (Fin n ⊕ Fin n) K) b.2 hodd'
  have hcent :
      (Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} :
        Set (GL (Fin n ⊕ Fin n) K))).comap (StatedSp n K).subtype =
      Subgroup.centralizer ({b} : Set (StatedSp n K)) := by
    ext z
    constructor
    · intro hz
      apply Subgroup.mem_centralizer_iff.mpr
      intro s hs
      have hs' := Set.mem_singleton_iff.mp hs
      subst s
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hz)
        (b : GL (Fin n ⊕ Fin n) K) rfl
    · intro hz
      apply Subgroup.mem_comap.mpr
      apply Subgroup.mem_centralizer_iff.mpr
      intro s hs
      have hs' := Set.mem_singleton_iff.mp hs
      subst s
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hz b rfl)
  have hJ' : CFSG.Assembly.IsComponentOf J
      (⨆ ε ∈ P, glBlockCentralizer (StatedSp n K).subtype
        ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε) := by
    rwa [hsup, hcent]
  obtain ⟨ε, hεP, hJε⟩ := exists_isComponentOf_block P
    (fun ε => glBlockCentralizer (StatedSp n K).subtype
      ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε) hc hJ'
  exact ⟨ε, hP ε hεP, hJε⟩

theorem isPrimIdemIn_and_blockDegree_eq_one_of_mul_eq_self
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (b : GL ι K)
    {ε : Matrix ι ι K}
    (hεA : ε ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    (hεid : IsIdempotentElem ε) (hεne : ε ≠ 0) (hfix : (b : Matrix ι ι K) * ε = ε) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε = 1 := by
  apply TableCRes.isPrimIdemIn_of_smul_block hεA hεid hεne
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      have hu0 := Set.mem_singleton_iff.mp hu
      subst u
      exact ⟨1, by simpa using hfix⟩
  | algebraMap c =>
      exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      exact ⟨c + d, by rw [add_mul, hc, hd, add_smul]⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      exact ⟨d * c, by rw [mul_assoc, hd, Matrix.mul_smul, hc, smul_smul]⟩

end CFSG.StandardType.ClassicalBlocks

end
