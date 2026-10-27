module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitFold
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bookkeeping

variable {p : ℕ} [NeZero p]

@[expose] def twE6Split_orbitIdx (i : Fin TwistTag.E6.tag.rank) : Fin Tag.F4.rank :=
  ⟨(TwistTag.E6.orbitIndex i).val, (TwistTag.E6.orbitIndex i).isLt⟩

theorem twE6Split_foldMap_apply (u : Fin Tag.F4.rank → ℤ) (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.foldMap TwistTag.E6 u i = u (twE6Split_orbitIdx i) := by
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 u i
  rw [h]
  exact congrArg u (Fin.ext rfl)

theorem twE6Split_theta_apply (s : Fin Tag.F4.rank → ZMod p) (i : Fin TwistTag.E6.tag.rank) :
    ExcFrames.twE6SplitTheta p s i = s (twE6Split_orbitIdx i) := by
  show ((TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) i : ℤ) : ZMod p) = _
  rw [twE6Split_foldMap_apply]
  show (((s (twE6Split_orbitIdx i)).val : ℤ) : ZMod p) = _
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem twE6Split_orbitIdx_perm (i : Fin TwistTag.E6.tag.rank) :
    twE6Split_orbitIdx (TwistTag.E6.perm i) = twE6Split_orbitIdx i := by
  apply Fin.ext
  exact congrArg Fin.val (TwistTag.E6.orbitIndex_perm i)

theorem twE6Split_theta_perm (s : Fin Tag.F4.rank → ZMod p) (i : Fin TwistTag.E6.tag.rank) :
    ExcFrames.twE6SplitTheta p s (TwistTag.E6.perm i) = ExcFrames.twE6SplitTheta p s i := by
  rw [twE6Split_theta_apply, twE6Split_theta_apply, twE6Split_orbitIdx_perm]

theorem twE6Split_frameCoord_perm (s : Fin Tag.F4.rank → ZMod p)
    (i : Fin TwistTag.E6.tag.rank) :
    ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s)
        (TwistTag.E6.perm i) =
      ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) i := by
  rw [TwE6SplitRootGen.frameCoord_twE6SplitTheta]
  exact twE6Split_theta_perm _ i

theorem twE6Split_frameCoord_F4 (s : Fin Tag.F4.rank → ZMod p) (b : Fin Tag.F4.rank) :
    ExcFrames.frameCoord .F4 p s b =
      (((![2, 2, 1, 1] : Fin 4 → ℤ) b : ℤ) : ZMod p) *
        ∑ k, ((Tag.cartan .F4 b k : ℤ) : ZMod p) * s k := by
  rw [ExcFrames.frameCoord, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Tag.symmetrizedCartan .F4 b k = (![2, 2, 1, 1] : Fin 4 → ℤ) b * Tag.cartan .F4 b k := by
    fin_cases b <;> fin_cases k <;> rfl
  rw [h]
  push_cast
  ring

theorem twE6Split_card_orbit (b : Fin Tag.F4.rank) :
    ((TwistTag.E6.orbit b).card : ℤ) = (![2, 2, 1, 1] : Fin 4 → ℤ) b := by
  fin_cases b <;> decide

theorem twE6Split_frameCoord_sum (s : Fin Tag.F4.rank → ZMod p) (b : Fin Tag.F4.rank) :
    ∑ i ∈ TwistTag.E6.orbit b,
        ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) i =
      ExcFrames.frameCoord .F4 p s b := by
  rw [twE6Split_frameCoord_F4]
  have h : ∀ i ∈ TwistTag.E6.orbit b,
      ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) i =
        ∑ k, ((Tag.cartan .F4 b k : ℤ) : ZMod p) * s k := by
    intro i hi
    rw [TwE6SplitRootGen.frameCoord_twE6SplitTheta, twE6Split_theta_apply]
    have hb : twE6Split_orbitIdx i = b := by
      apply Fin.ext
      exact congrArg Fin.val (TwistTag.E6.mem_orbit_iff.1 hi)
    rw [hb]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  have := twE6Split_card_orbit b
  rw [← this]
  push_cast
  rfl

end Bookkeeping

section Pairing

variable {p : ℕ} [NeZero p]

theorem twE6Split_pairing_permPow {y : Fin TwistTag.E6.tag.rank → ZMod p}
    (hy : ∀ i, y (TwistTag.E6.perm i) = y i) (k : ℕ) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    ∑ j, ((permLattice (TwistTag.E6.perm ^ k) v j : ℤ) : ZMod p) * y j =
      ∑ j, ((v j : ℤ) : ZMod p) * y j := by
  have hyk : ∀ j, y ((TwistTag.E6.perm ^ k) j) = y j := by
    induction k with
    | zero => intro j; rfl
    | succ k ih =>
      intro j
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hy]
  calc ∑ j, ((permLattice (TwistTag.E6.perm ^ k) v j : ℤ) : ZMod p) * y j
      = ∑ j, ((permLattice (TwistTag.E6.perm ^ k) v ((TwistTag.E6.perm ^ k) j) : ℤ) : ZMod p) *
          y ((TwistTag.E6.perm ^ k) j) :=
        (Equiv.sum_comp (TwistTag.E6.perm ^ k)
          (fun j => ((permLattice (TwistTag.E6.perm ^ k) v j : ℤ) : ZMod p) * y j)).symm
    _ = ∑ j, ((v j : ℤ) : ZMod p) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hyk j]
        simp [permLattice]

theorem twE6Split_card_diagramOrbit (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (TwistTag.E6.diagramOrbit v).card = 1 ∨ (TwistTag.E6.diagramOrbit v).card = 2 := by
  have h1 : 0 < (TwistTag.E6.diagramOrbit v).card :=
    Finset.card_pos.2 ⟨v, TwistTag.E6.self_mem_diagramOrbit v⟩
  have h2 : (TwistTag.E6.diagramOrbit v).card ≤ 2 :=
    (Finset.card_image_le).trans (by simp [TwistTag.order])
  omega

theorem twE6Split_pairing_orbSum {y : Fin TwistTag.E6.tag.rank → ZMod p}
    (hy : ∀ i, y (TwistTag.E6.perm i) = y i) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    ∑ j, ((TwE6SplitFold.twE6OrbSum v j : ℤ) : ZMod p) * y j =
      ((TwistTag.E6.diagramOrbit v).card : ZMod p) * ∑ j, ((v j : ℤ) : ZMod p) * y j := by
  have h : ∀ α ∈ TwistTag.E6.diagramOrbit v,
      ∑ j, ((α j : ℤ) : ZMod p) * y j = ∑ j, ((v j : ℤ) : ZMod p) * y j := by
    intro α hα
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
    exact twE6Split_pairing_permPow hy k v
  calc ∑ j, ((TwE6SplitFold.twE6OrbSum v j : ℤ) : ZMod p) * y j
      = ∑ j, ∑ α ∈ TwistTag.E6.diagramOrbit v, ((α j : ℤ) : ZMod p) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TwE6SplitFold.twE6OrbSum, Finset.sum_apply, Int.cast_sum, Finset.sum_mul]
    _ = ∑ α ∈ TwistTag.E6.diagramOrbit v, ∑ j, ((α j : ℤ) : ZMod p) * y j :=
        Finset.sum_comm
    _ = _ := by rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

theorem twE6Split_pairing_orbSum_eq_zero [Fact p.Prime] (hp2 : p ≠ 2)
    {y : Fin TwistTag.E6.tag.rank → ZMod p} (hy : ∀ i, y (TwistTag.E6.perm i) = y i)
    (v : Fin TwistTag.E6.tag.rank → ℤ)
    (h : ∑ j, ((TwE6SplitFold.twE6OrbSum v j : ℤ) : ZMod p) * y j = 0) :
    ∑ j, ((v j : ℤ) : ZMod p) * y j = 0 := by
  rw [twE6Split_pairing_orbSum hy] at h
  have hne : ((TwistTag.E6.diagramOrbit v).card : ZMod p) ≠ 0 := by
    rcases twE6Split_card_diagramOrbit v with hc | hc
    · rw [hc]; simp
    · rw [hc, Ne, show ((2 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) from rfl,
        ZMod.natCast_eq_zero_iff]
      intro h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2)
  exact (mul_eq_zero.1 h).resolve_left hne

theorem twE6Split_pairing_foldMap (γ : Fin Tag.F4.rank → ℤ)
    (y : Fin TwistTag.E6.tag.rank → ZMod p) :
    ∑ j, ((TwistTag.E6.foldMap γ j : ℤ) : ZMod p) * y j =
      ∑ b, ((γ b : ℤ) : ZMod p) * ∑ i ∈ TwistTag.E6.orbit b, y i := by
  classical
  have hfilter : ∀ b : Fin Tag.F4.rank,
      Finset.univ.filter (fun j : Fin TwistTag.E6.tag.rank => twE6Split_orbitIdx j = b) =
        TwistTag.E6.orbit b := by
    intro b
    ext j
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      apply TwistTag.E6.mem_orbit_iff.2
      exact Fin.ext (congrArg Fin.val h)
    · intro h
      apply Fin.ext
      exact congrArg Fin.val (TwistTag.E6.mem_orbit_iff.1 h)
  calc ∑ j, ((TwistTag.E6.foldMap γ j : ℤ) : ZMod p) * y j
      = ∑ j, ((γ (twE6Split_orbitIdx j) : ℤ) : ZMod p) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [twE6Split_foldMap_apply]
    _ = ∑ b : Fin Tag.F4.rank, ∑ j ∈ Finset.univ.filter
          (fun j : Fin TwistTag.E6.tag.rank => twE6Split_orbitIdx j = b),
          ((γ (twE6Split_orbitIdx j) : ℤ) : ZMod p) * y j :=
        (Finset.sum_fiberwise Finset.univ (fun j => twE6Split_orbitIdx j)
          (fun j => ((γ (twE6Split_orbitIdx j) : ℤ) : ZMod p) * y j)).symm
    _ = ∑ b, ((γ b : ℤ) : ZMod p) * ∑ i ∈ TwistTag.E6.orbit b, y i := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hfilter b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hb : twE6Split_orbitIdx j = b := by
          apply Fin.ext
          exact congrArg Fin.val (TwistTag.E6.mem_orbit_iff.1 hj)
        rw [hb]

end Pairing

section Characters


variable {p : ℕ} [NeZero p]

theorem twE6Split_zetaVec_perm {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ p = 1)
    (t : Fin Tag.F4.rank → ZMod p) (i : Fin TwistTag.E6.tag.rank) :
    TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t))
        (TwistTag.E6.perm i) =
      TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) i := by
  rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply, twE6Split_frameCoord_perm]

theorem twE6Split_rootChar_perm {L : Type} [Field L] {a : Fin TwistTag.E6.tag.rank → Lˣ}
    (ha : ∀ i, a (TwistTag.E6.perm i) = a i) (x : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar a (permLattice TwistTag.E6.perm x) = rootChar a x := by
  unfold rootChar
  calc ∏ i, a i ^ permLattice TwistTag.E6.perm x i
      = ∏ j, a (TwistTag.E6.perm j) ^ permLattice TwistTag.E6.perm x (TwistTag.E6.perm j) :=
        (Equiv.prod_comp TwistTag.E6.perm
          (fun i => a i ^ permLattice TwistTag.E6.perm x i)).symm
    _ = ∏ j, a j ^ x j := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [ha j]
        simp [permLattice]

theorem twE6Split_two_torsion {L : Type} [Field L] [CharP L 2] (m : Lˣ) (h : m ^ 2 = 1) :
    m = 1 := by
  have h1 : (m : L) ^ 2 = 1 := by
    have := congrArg Units.val h
    simpa using this
  have h2 : (2 : L) = 0 := by simpa using CharP.cast_eq_zero L 2
  have h3 : ((m : L) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (m : L)) * h2
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3))

theorem twE6Split_baseChange_frameDiag {K L : Type} [Field K] [Field L] (f : K →+* L)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζL : (Units.map f.toMonoidHom ζ) ^ p = 1)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    baseChangeGL f (ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ x) =
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) (Units.map f.toMonoidHom ζ) hζL x := by
  rw [ExcFrames.frameDiag, ExcFrames.frameDiag, baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply, map_pow]

theorem twE6Split_char_fold {K L : Type} [Field K] [Field L] (f : K →+* L)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζL : (Units.map f.toMonoidHom ζ) ^ p = 1)
    (t : Fin Tag.F4.rank → ZMod p) (γ : Fin Tag.F4.rank → ℤ) :
    Units.map f.toMonoidHom
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))
          (Multiplicative.ofAdd γ)) =
      rootCharHom (TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
          (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)))
        (Multiplicative.ofAdd (TwistTag.E6.foldMap γ)) := by
  classical
  have hrc : ∀ {τ : Tag} {M : Type} [Field M] (a : Fin τ.rank → Mˣ) (v : Fin τ.rank → ℤ),
      rootCharHom a (Multiplicative.ofAdd v) = ∏ i, a i ^ v i := fun _ _ => rfl
  rw [hrc, hrc, map_prod]
  have hfilter : ∀ b : Fin Tag.F4.rank,
      Finset.univ.filter (fun j : Fin TwistTag.E6.tag.rank => twE6Split_orbitIdx j = b) =
        TwistTag.E6.orbit b := by
    intro b
    ext j
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      apply TwistTag.E6.mem_orbit_iff.2
      exact Fin.ext (congrArg Fin.val h)
    · intro h
      apply Fin.ext
      exact congrArg Fin.val (TwistTag.E6.mem_orbit_iff.1 h)
  have hR : ∏ i, TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) i ^
          TwistTag.E6.foldMap γ i =
      ∏ b : Fin Tag.F4.rank, (∏ i ∈ TwistTag.E6.orbit b,
        TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
          (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) i) ^ γ b := by
    calc _ = ∏ j, TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
          (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) j ^
            γ (twE6Split_orbitIdx j) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [twE6Split_foldMap_apply]
      _ = ∏ b : Fin Tag.F4.rank, ∏ j ∈ Finset.univ.filter
            (fun j : Fin TwistTag.E6.tag.rank => twE6Split_orbitIdx j = b),
            TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
              (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) j ^
                γ (twE6Split_orbitIdx j) :=
          (Finset.prod_fiberwise Finset.univ (fun j => twE6Split_orbitIdx j)
            (fun j => TableBExc.E6Three.zetaVec (Units.map f.toMonoidHom ζ) hζL
              (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t)) j ^
                γ (twE6Split_orbitIdx j))).symm
      _ = _ := by
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [hfilter b, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun j hj => ?_
          have hb : twE6Split_orbitIdx j = b := by
            apply Fin.ext
            exact congrArg Fin.val (TwistTag.E6.mem_orbit_iff.1 hj)
          rw [hb]
  rw [hR]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_zpow]
  congr 1
  have hz : ∀ (ζ' : Lˣ) (hζ' : ζ' ^ p = 1) (x : Fin TwistTag.E6.tag.rank → ZMod p),
      ∏ i ∈ TwistTag.E6.orbit b, TableBExc.E6Three.zetaVec ζ' hζ' x i =
        CFSG.RankThree.CentralCover.zmodPowHom ζ' hζ'
          (Multiplicative.ofAdd (∑ i ∈ TwistTag.E6.orbit b, x i)) := by
    intro ζ' hζ' x
    rw [ofAdd_sum, map_prod]
    rfl
  rw [hz, twE6Split_frameCoord_sum]
  rw [TableBExc.E6Three.zetaVec_apply, CFSG.RankThree.CentralCover.zmodPowHom_apply, map_pow]

end Characters

end CFSG.StandardType

end
