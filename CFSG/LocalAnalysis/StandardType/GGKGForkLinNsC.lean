module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneLinearLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkSignedPow
public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix Polynomial Multiplicative

private theorem ggKGLn_exists_irreducible_dvd_cyclotomic {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) :
    ∃ g : Polynomial K, Irreducible g ∧ g ∣ Polynomial.cyclotomic p K := by
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (cyclotomic_ne_zero p K), natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  exact WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p K)

private theorem ggKGLn_card_le_psl_small {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1)
    (hd : 1 ≤ d) (hd5 : d ≤ 5) (E : Subgroup (projectiveSL d K)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  classical
  haveI : Nonempty K := ⟨0⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq
  obtain ⟨g, hg, hgd⟩ := ggKGLn_exists_irreducible_dvd_cyclotomic (K := K) (p := p) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζo := CoordSL.root_isPrimitiveRoot (g := g) hp hpK0 hgd
  have hCdet : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : (CoordSL.rootMat g) ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hker : (proj d K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K) := by
    intro x hx
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx
  have hcp : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) := by
    intro h
    exact hpK' (h.trans (card_center_specialLinear_dvd (by omega)))
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2) }
  have hV : ∀ v : ↥E, v ^ p = 1 := fun v => Subtype.ext (hE.2 v v.2)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime hp (proj_surjective d K) hker hcp
    (V := ↥E) hV E.subtype
  set S : Set (Matrix (Fin d) (Fin d) K) :=
    {x | ∃ e : ↥E, ((s e : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = x}
    with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have h1 : s e * s e' = s e' * s e := by rw [← map_mul, ← map_mul, mul_comm]
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, rfl⟩
    have h1 : (s e) ^ p = 1 := hsp e
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  obtain ⟨t, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd S hSc hSp
  have hdim : (CoordSL.rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK0 hgd hpq
  have hτinj : Function.Injective (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp) :=
    CoordSL.frameHom_injective _ A₀ ε hCdet hCp (by rw [MonoidHom.ker_id]; exact bot_le)
      (by rw [hdim]; norm_num)
      (CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd)
  have hcard_range : Nat.card (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp).range = p ^ t := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coeSort_range hτinj,
      Fintype.card_multiplicative, Fintype.card_pi_const, ZMod.card]
  have hmem : ∀ e : ↥E, s e ∈ (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp).range := by
    intro e
    obtain ⟨k, hk⟩ := hframe _ ⟨e, rfl⟩
    refine ⟨ofAdd (fun i => (k i : ZMod p)), ?_⟩
    rw [CoordSL.frameHom_natCast, SLRep.ggFrame_apply, MonoidHom.id_apply]
    have hkSL : s e * A₀ = A₀ * SLNS.nsSL ε hCdet k := Subtype.ext hk
    rw [← hkSL]
    group
  have hcardE : Nat.card E ≤ Nat.card (CoordSL.frameHom (MonoidHom.id
      (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range := by
    refine Nat.card_le_card_of_injective
      (f := fun e : ↥E => (⟨s e, hmem e⟩ : (CoordSL.frameHom (MonoidHom.id
        (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range)) ?_
    intro a b hab
    apply Subtype.ext
    have h1 : s a = s b := congrArg Subtype.val hab
    calc (a : projectiveSL d K) = proj d K (s a) := (hs a).symm
      _ = proj d K (s b) := by rw [h1]
      _ = b := hs b
  have ht2 : t ≤ 2 := by
    have hcard : Fintype.card ((Fin (CoordSL.rootPB g).dim × Fin t) ⊕ Fin r) = d := by
      rw [← Fintype.card_fin d, ← Fintype.card_congr ε]
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hdim] at hcard
    omega
  calc Nat.card E ≤ Nat.card (CoordSL.frameHom (MonoidHom.id
        (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range := hcardE
    _ = p ^ t := hcard_range
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos ht2

private theorem ggKGLn_tbGroup_false_of_pRank_le_two {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hrk : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hA : GGTorusTBGroup p r R I L' ψ A) : False := by
  classical
  obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, _hsc⟩ := hA
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hle : Nat.card E ≤ p ^ 2 := hrk E hEab
  rw [← hcardE] at h3
  exact absurd (le_trans h3 hle)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))


private theorem ggKGLn_center_projectiveSL_two {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (projectiveSL 2 K) = ⊥ := by
  have h1 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [← scalars_eq_center 2 K, LinearCover.scalars_two_eq_bot]
  have h2 := Subgroup.map_center_eq (LinearCover.projectiveSLTwoEquivSL K)
  rw [h1] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (f := (LinearCover.projectiveSLTwoEquivSL K : projectiveSL 2 K →*
      Matrix.SpecialLinearGroup (Fin 2) K))
    (LinearCover.projectiveSLTwoEquivSL K).injective).mp h2

theorem ggKGLn_recipeLinear_lattice {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N + 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK; omega
    · exact h0
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hm hpN
  haveI : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hm hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpN
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hpK0 : (p : K) ≠ 0 := by
    intro hzero
    exact hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp hzero)).symm)
  let e := TypeA.recipeEquiv d K
  have hZpsl : Subgroup.center (projectiveSL d K) = ⊥ := by
    rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | h3
    · exact ggKGLn_center_projectiveSL_two (K := K)
    · exact CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := d) (k := K) h3
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hZpsl] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (e : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →* projectiveSL d K))
      e.injective).mp h1
  have hIp := NbrInnerMore.ggOutdiagPrime_linear (d := d) hp hpK' (by omega)
  have hlift : GGTorusLift p 0 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    TypeA.ggTorusLift_of_mulEquiv e (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by omega)))
  rcases lt_or_ge d 6 with hd5 | hd6
  · have hd5' : d ≤ 5 := by omega
    refine ⟨0, hlift, ?_⟩
    have hrk : ∀ E : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
      intro E hE
      have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
        Subgroup.card_map_of_injective e.injective
      have hE' : IsElemAbelian p (E.map e.toMonoidHom) := TableB.isElemAbelian_map hE _
      rw [← hcard]
      exact ggKGLn_card_le_psl_small hp hp2 hpK0 hpK (by omega) hd5' _ hE'
    intro L' _ _ ψ A hA
    exact (ggKGLn_tbGroup_false_of_pRank_le_two hp hIp hZ hrk hA).elim
  · have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK' (by omega))
    refine ⟨0, hlift, ?_⟩
    exact ggTorusLattice_of_signedEltSC_pow hp hp2 hIp hZ hcp
      (ggKGLn_signedEltSC_linearNonsplit hp hp2 hpK0 hpK (by omega))

theorem ggKGLn_kgTwoOn_linearNonsplit :
    GGKGTwoOn fun p lab => (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  obtain ⟨h, hpn⟩ := hs
  rcases h with hA | ⟨hD, hl3⟩
  · dsimp only at hA hpn
    subst hA
    have hl1 : 1 ≤ l := hlab.2.1
    have hd2 : 2 ≤ l + 1 := by omega
    exact ggKGLn_recipeLinear_lattice hp hpn ⟨n, rfl⟩ hd2 hQ
  · dsimp only at hD hl3 hpn
    subst hD hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    exact ggKGLn_recipeLinear_lattice hp hpn ⟨n, rfl⟩ (by norm_num) hQ

end CFSG.StandardType
