module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgLabel
public import
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgTorus
public import
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgTorusRank
public import
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4McClurgAdjInput
public import CFSG.HardMathSupport.U4FF.ClassClassifHolds
public import CFSG.HardMathSupport.U4FF.Natural4
public import CFSG.HardMathSupport.U4FF.Omega2Gen
public import CFSG.HardMathSupport.U4FF.ClassFinalConj
public import CFSG.HardMathSupport.U4FF.ClassFinalDim
public import CFSG.HardMathSupport.U4FF.ClassFinalRep
public import CFSG.HardMathSupport.U4FF.ClassRank
public import CFSG.HardMathSupport.U4FF.ClassRankF2
public import CFSG.HardMathSupport.U4FF.OuterTransvection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.HardMathSupport.U4FF CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7 (matRep)
open CFSG.QuasithinUnique.Setup.Family
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing finite_endRing)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem isU4Group_of_isU4' {U : Type} [CommGroup U] [Finite U] {S : Subgroup (MulAut U)}
    {n : ℕ} (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsU4 ↥S n) : IsU4Group n S := by
  have hC := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨q, hv, hp, he, ⟨φ⟩⟩ :=
    KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
  exact ⟨⟨_, hv⟩, ⟨q, hp, he, rfl⟩, ⟨φ⟩⟩

private theorem naturalU4Mod_of_singleN
    {U : Type} [CommGroup U] [Finite U] [Fact (∀ s : U, s * s = 1)]
    {S : Subgroup (MulAut U)} {n : ℕ} [NeZero n] {K : Type} [Field K] [Finite K] [CharP K 2]
    (hL : IsU4Group n S) (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn S)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥S ≃* SU4 K n) (ρ : Representation (ZMod 2) (SU4 K n) (Additive U))
    [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥S) (s : U),
      ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut U) s))
    (hC : Classif K n) (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    (l : Lbl n) (hdimW : Module.finrank (EndRing ρ) (Additive U) = l.dim)
    (hinv : l.RotInv d) (hSN : l.SingleN) : NaturalU4Mod n S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive U) := Module.Finite.of_finite
  have h4 : Module.finrank (EndRing ρ) (Additive U) = 4 := by
    rw [hdimW]
    exact Lbl.dim_eq_four_of_singleN hSN
  have h2n : 2 * n ∣ d := Lbl.SingleN.two_mul_dvd hSN hinv
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := ClassFinal.exists_ringHom_of_dvd hK' hDcard h2n
  letI : Algebra K (EndRing ρ) := ι.toAlgebra
  let b : Module.Basis (Fin 4) (EndRing ρ) (Additive U) :=
    Module.finBasisOfFinrankEq _ _ h4
  obtain ⟨l', -, ⟨Φ'⟩, hdim'⟩ := u4_exists_label hC hnt b ι (RingHom.id (EndRing ρ))
  obtain ⟨i₁, hz, hb1, hac⟩ := Lbl.singleN_of_dim_eq_four (hdim'.symm : l'.dim = 4)
  obtain ⟨ε, R, hR, hRval⟩ := ClassFinal.exists_coords η ρ hρ b
  have Φ'' : (matRep (Tmod K l' (EndRing ρ))).Equiv
      (matRep (u4MatHomE b (RingHom.id (EndRing ρ)))) := by
    rw [matRep_u4MatHomE]
    exact Φ'
  have hmap : ∀ x : ↥S, ((R x : GL (Fin 4) (EndRing ρ)) :
      Matrix (Fin 4) (Fin 4) (EndRing ρ)).map (algebraMap (EndRing ρ) (EndRing ρ)) =
      u4MatHomE b (RingHom.id (EndRing ρ)) (η x) := fun x => by
    rw [hRval x, u4MatHomE_apply, Algebra.algebraMap_self]
  have hfr : ∀ (j : ℕ) (g : SU4 K n),
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K (EndRing ρ) j) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
        (fun y => algebraMap (EndRing ρ) (EndRing ρ) (ι (y ^ 2 ^ j))) := by
    intro j g
    ext a c
    simp only [Matrix.map_apply, frobTw_apply]
    rfl
  rcases hac with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · obtain ⟨e, P', hP'⟩ := Tmod_single_N (K := K) (E := EndRing ρ) l' i₁ hz ha hb1 hc
    obtain ⟨P, hP⟩ := ClassFinal.exists_conj_of_single (Tmod K l' (EndRing ρ))
      (u4MatHomE b (RingHom.id (EndRing ρ)))
      (fun g => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
        (frobTw K (EndRing ρ) (i₁ : ℕ))) Φ'' e P' hP'
    exact (natural4Input_holds U n S hL hirr K hK η (EndRing ρ) ι ε R hR (EndRing ρ) P
      (i₁ : ℕ) (fun x => by rw [hmap x, hP (η x), hfr])).naturalU4Mod
  · obtain ⟨e, P', hP'⟩ := Tmod_single_S (K := K) (E := EndRing ρ) l' i₁ hz ha hb1 hc
    obtain ⟨P, hP⟩ := ClassFinal.exists_conj_of_single (Tmod K l' (EndRing ρ))
      (u4MatHomE b (RingHom.id (EndRing ρ)))
      (fun g => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
        (frobTw K (EndRing ρ) ((i₁ : ℕ) + n))) Φ'' e P' hP'
    exact (natural4Input_holds U n S hL hirr K hK η (EndRing ρ) ι ε R hR (EndRing ρ) P
      ((i₁ : ℕ) + n) (fun x => by rw [hmap x, hP (η x), hfr])).naturalU4Mod

private theorem naturalU4Mod_of_singleO
    {U : Type} [CommGroup U] [Finite U] [Fact (∀ s : U, s * s = 1)]
    {S : Subgroup (MulAut U)} {n : ℕ} [NeZero n] {K E : Type} [Field K] [Finite K]
    [CharP K 2] [Field E] [Finite E] [CharP E 2]
    (hL : IsU4Group n S) (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn S)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥S ≃* SU4 K n) (ρ : Representation (ZMod 2) (SU4 K n) (Additive U))
    [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥S) (s : U),
      ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut U) s))
    (hC : Classif K n) (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    (l : Lbl n) (hdimW : Module.finrank (EndRing ρ) (Additive U) = l.dim)
    (hinv : l.RotInv d) (hSO : l.SingleO) (ιK : K →+* E) (ιD : EndRing ρ →+* E) :
    NaturalU4Mod n S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive U) := Module.Finite.of_finite
  letI : Algebra K E := ιK.toAlgebra
  letI : Algebra (EndRing ρ) E := ιD.toAlgebra
  have h6 : Module.finrank (EndRing ρ) (Additive U) = 6 := by
    rw [hdimW]
    exact Lbl.dim_eq_six_of_singleO hSO
  obtain ⟨m', hm'⟩ := Lbl.SingleO.dvd hSO hinv
  let b : Module.Basis (Fin 6) (EndRing ρ) (Additive U) :=
    Module.finBasisOfFinrankEq _ _ h6
  obtain ⟨l', -, ⟨Φ'⟩, hdim'⟩ := u4_exists_label hC hnt b ιK ιD
  obtain ⟨i₁, hz, ha, hb1, hc⟩ := Lbl.singleO_of_dim_eq_six (hdim'.symm : l'.dim = 6)
  obtain ⟨ε, R, hR, hRval⟩ := ClassFinal.exists_coords η ρ hρ b
  have Φ'' : (matRep (Tmod K l' E)).Equiv (matRep (u4MatHomE b ιD)) := by
    rw [matRep_u4MatHomE]
    exact Φ'
  obtain ⟨e, P', hP'⟩ := Tmod_single_O (K := K) (E := E) l' i₁ hz ha hb1 hc
  obtain ⟨P, hP⟩ := ClassFinal.exists_conj_of_single (Tmod K l' E) (u4MatHomE b ιD)
    (fun g => comp2 (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
      (frobTw K E (i₁ : ℕ)))) Φ'' e P' hP'
  have hDcard' : Nat.card (EndRing ρ) = 2 ^ (n * m') := by rw [hDcard, hm']
  refine (omega2InputGen_holds U n S hL hirr K hK η (EndRing ρ) m' hDcard' ε R hR E P
    (i₁ : ℕ) (fun x => ?_)).naturalU4Mod
  have hmap : ((R x : GL (Fin 6) (EndRing ρ)) :
      Matrix (Fin 6) (Fin 6) (EndRing ρ)).map (algebraMap (EndRing ρ) E) =
      u4MatHomE b ιD (η x) := by
    rw [hRval x, u4MatHomE_apply]
    rfl
  have hfr : ((η x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E (i₁ : ℕ)) =
      ((η x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
        (fun y => algebraMap K E (y ^ 2 ^ (i₁ : ℕ))) := by
    ext a c
    simp only [Matrix.map_apply, frobTw_apply]
  rw [hmap, hP (η x), hfr]

private theorem eight_le_rank_Tmod_single101
    {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [CharP E 2] [Algebra K E]
    {n : ℕ} [NeZero n] {l : Lbl n} {i₀ : Fin n}
    (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (ha : l.a i₀ = true) (hb : l.b i₀ = false)
    (hc : l.c i₀ = true) (g : SU4 K n) (w : K) (hw1 : w ≠ 1)
    (hxt : (((g : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![w, w⁻¹, w⁻¹, w]) :
    8 ≤ (Tmod K l E g - 1).rank := by
  classical
  obtain ⟨e, he⟩ := Tmod_single (K := K) (E := E) l i₀ hz true false true ha hb hc
  set w' : E := frobTw K E i₀ w with hw'def
  have hw' : w' ^ 2 ≠ 1 := by
    intro h
    have h1 : w' = 1 := by
      have h2 : w' ^ 2 = (1 : E) ^ 2 := by simpa using h
      exact CharTwo.sq_inj.mp h2
    exact hw1 ((frobTw K E i₀).injective (by rw [← hw'def, h1, map_one]))
  have hD : (↑(twistHom n (frobTw K E i₀) g) : Matrix (Fin 4) (Fin 4) E) =
      Matrix.diagonal ![w', w'⁻¹, w'⁻¹, w'] := by
    rw [twistHom_val, hxt, Matrix.diagonal_map (map_zero (frobTw K E i₀))]
    congr 1
    funext i
    fin_cases i <;> simp [hw'def, map_inv₀]
  have hEq : Matrix.reindex e e (Tmod K l E g - 1) =
      Matrix.reindex e e (Tmod K l E g) - 1 := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_sub]
    change ((Tmod K l E) g).submatrix e.symm e.symm -
        (1 : Matrix (TIdx l) (TIdx l) E).submatrix e.symm e.symm =
      ((Tmod K l E) g).submatrix e.symm e.symm - 1
    rw [Matrix.submatrix_one_equiv e.symm]
  have hrank : (Tmod K l E g - 1).rank =
      (locR true false true E (twistHom n (frobTw K E i₀) g) - 1).rank := by
    rw [← Matrix.rank_reindex e e (Tmod K l E g - 1), hEq, he g]
  rw [hrank]
  exact eight_le_rank_locR101_diag (twistHom n (frobTw K E i₀) g) w' hw' hD

private theorem adjointOmega6_of_single101
    {U : Type} [CommGroup U] [Finite U] [Fact (∀ s : U, s * s = 1)]
    {S : Subgroup (MulAut U)} {n : ℕ} [NeZero n] {K E : Type} [Field K] [Finite K]
    [CharP K 2] [Field E] [Finite E] [CharP E 2]
    (hL : IsU4Group n S) (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥S ≃* SU4 K n) (ρ : Representation (ZMod 2) (SU4 K n) (Additive U))
    [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥S) (s : U),
      ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut U) s))
    (hC : Classif K n) (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) (hdn : d = n)
    (l : Lbl n) (hdimW : Module.finrank (EndRing ρ) (Additive U) = l.dim)
    {i₀ : Fin n} (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (ha : l.a i₀ = true)
    (hb : l.b i₀ = false) (hc : l.c i₀ = true)
    (ιK : K →+* E) (ιD : EndRing ρ →+* E) : AdjointOmega6 n S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive U) := Module.Finite.of_finite
  letI : Algebra K E := ιK.toAlgebra
  letI : Algebra (EndRing ρ) E := ιD.toAlgebra
  have h14 : Module.finrank (EndRing ρ) (Additive U) = 14 := by
    rw [hdimW]
    exact dim_eq_fourteen_of_single101 hz ha hb hc
  let b : Module.Basis (Fin 14) (EndRing ρ) (Additive U) :=
    Module.finBasisOfFinrankEq _ _ h14
  obtain ⟨l', -, ⟨Φ'⟩, hdim'⟩ := u4_exists_label hC hnt b ιK ιD
  obtain ⟨i₁, hz', ha', hb', hc'⟩ := single101_of_dim_eq_fourteen (hdim'.symm : l'.dim = 14)
  obtain ⟨ε, R, hR, hRval⟩ := ClassFinal.exists_coords η ρ hρ b
  have Φ'' : (matRep (Tmod K l' E)).Equiv (matRep (u4MatHomE b ιD)) := by
    rw [matRep_u4MatHomE]
    exact Φ'
  obtain ⟨e₀, he₀⟩ := Tmod_single (K := K) (E := E) l' i₁ hz' true false true ha' hb' hc'
  let e : TIdx l' ≃ Fin 14 := e₀
  have he : ∀ g : SU4 K n,
      ((1 : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E) * Matrix.reindex e e ((Tmod K l' E) g) =
      locR101 E (twistHom n (frobTw K E i₁) g) *
        ((1 : GL (Fin 14) E) : Matrix (Fin 14) (Fin 14) E) := fun g => by
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
    exact he₀ g
  obtain ⟨P, hP⟩ := ClassFinal.exists_conj_of_single (Tmod K l' E) (u4MatHomE b ιD)
    (fun g => locR101 E (twistHom n (frobTw K E i₁) g)) Φ'' e 1 he
  have hmap : ∀ x : ↥S, ((R x : GL (Fin 14) (EndRing ρ)) :
      Matrix (Fin 14) (Fin 14) (EndRing ρ)).map (algebraMap (EndRing ρ) E) =
      u4MatHomE b ιD (η x) := fun x => by
    rw [hRval x, u4MatHomE_apply]
    rfl
  exact adjointOmega6_of_locR101 U n S hL K hK η (EndRing ρ) (by rw [hDcard, hdn])
    ε R hR E P (i₁ : ℕ) (fun x => by rw [hmap x, hP (η x)])

theorem k146U4OuterMcClurg_holds :
    K146U4OuterMcClurg := by
  intro U _ _ hU2 S n σ hU4 hn hirr hbig hσN hσS hσ2 hσm
  classical
  haveI : Fact (∀ s : U, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hU2 s⟩
  have hL : IsU4Group n S := isU4Group_of_isU4' hU4
  have hirrG : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn S := fun J hJ => hirr.2.2.2 J hJ bot_le le_top
  have hbigD : ∀ t ∈ S, t ≠ 1 → t * t = 1 → 4 * n + 2 ≤ disp t := fun t ht ht1 ht2 => by
    simpa only [Thm14_5.rkIdx_fixV_zpowers_eq_disp] using hbig t ht ht1 ht2
  have hσD : disp σ ≤ 3 * n + 2 := by
    simpa only [Thm14_5.rkIdx_fixV_zpowers_eq_disp] using hσm
  have hA : IsElemAbelian2 (Subgroup.zpowers σ) := by
    constructor
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have h2 : σ ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, sq, hσ2]
      calc (σ ^ m) ^ 2 = (σ ^ m) ^ ((2 : ℕ) : ℤ) := (zpow_natCast (σ ^ m) 2).symm
        _ = σ ^ (m * ((2 : ℕ) : ℤ)) := (zpow_mul σ m _).symm
        _ = σ ^ (((2 : ℕ) : ℤ) * m) := by rw [mul_comm]
        _ = (σ ^ ((2 : ℕ) : ℤ)) ^ m := zpow_mul σ _ m
        _ = 1 := by rw [h2, one_zpow]
  have hAN : Subgroup.zpowers σ ≤ Subgroup.normalizer (S : Set (MulAut U)) :=
    (Subgroup.zpowers_le).2 hσN
  have hirrA : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn (S ⊔ Subgroup.zpowers σ) := fun W hW =>
    hirrG W fun x hx => hW x (le_sup_left (a := S) hx)
  obtain ⟨t₀, ht₀S, ht₀1, ht₀2, ht₀σ⟩ :=
    exists_small_involution hL hA hAN hirrA (Subgroup.mem_zpowers σ) hσS
  have hnat : ¬ NaturalU4Mod n S := fun h => by
    have h1 := disp_le_of_naturalU4Mod h ht₀2
    have h2 := hbigD t₀ ht₀S ht₀1 ht₀2
    omega
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨K, _, _, _, hK, ⟨η⟩⟩ := exists_equiv_SU hL
  obtain ⟨hSnt, x₀, hx₀⟩ := ClassFinal.nontrivial_of_isU4Group hL
  haveI := hSnt
  let ρ := ClassFinal.binRep S η
  haveI : Fact ρ.IsIrreducible := ⟨ClassFinal.binRep_isIrreducible η hirrG⟩
  have hnt : ∃ g, ρ g ≠ 1 := ⟨η x₀, ClassFinal.binRep_ne_one S η x₀ hx₀⟩
  have hlin : ∀ x : ↥S, ρ (η x) =
      (binaryLin ((x : ↥S) : MulAut U) : Additive U →ₗ[ZMod 2] Additive U) :=
    ClassFinal.binRep_eta_lin S η
  have hC := classif_holds hK
  obtain ⟨d, hd1, hDcard, hdesc⟩ := u4_descent hC hK hnt
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive U) := Module.Finite.of_finite
  let b₀ : Module.Basis (Fin (Module.finrank (EndRing ρ) (Additive U))) (EndRing ρ)
      (Additive U) := Module.finBasis (EndRing ρ) (Additive U)
  obtain ⟨E, _, _, _, ιK, ιD, l, hl0, ⟨Φ⟩, hm1, hm2, hdimW⟩ := hdesc b₀
  letI : Algebra K E := ιK.toAlgebra
  have hinv : l.RotInv d := by
    refine Lbl.rotInv_of_modEq l d ?_ hm2
    rwa [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]] at hm1
  have hdispT : ∀ x : ↥S, disp (x : MulAut U) = d * (Tmod K l E (η x) - 1).rank := fun x => by
    have h1 := finrank_range_Tmod hDcard b₀ ιD l Φ hdimW (η x)
    rw [hlin x] at h1
    exact h1
  have hρ : ∀ (x : ↥S) (s : U),
      ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut U) s) :=
    ClassFinal.binRep_eta S η
  by_cases hSN : l.SingleN
  · exact absurd
      (naturalU4Mod_of_singleN hL hirrG hK η ρ hρ hC hnt hDcard l hdimW hinv hSN) hnat
  by_cases hSO : l.SingleO
  · exact absurd
      (naturalU4Mod_of_singleO hL hirrG hK η ρ hρ hC hnt hDcard l hdimW hinv hSO ιK ιD) hnat
  have hrk : d * l.rk1 ≤ 6 * n + 4 := by
    have hxt₀ : (⟨t₀, ht₀S⟩ : ↥S) * ⟨t₀, ht₀S⟩ = 1 := Subtype.ext ht₀2
    have hηt : η ⟨t₀, ht₀S⟩ * η ⟨t₀, ht₀S⟩ = 1 := by rw [← map_mul, hxt₀, map_one]
    have hηt1 : η ⟨t₀, ht₀S⟩ ≠ 1 := by
      intro h
      apply ht₀1
      have := η.injective (h.trans (map_one η).symm)
      exact congrArg Subtype.val this
    have h1 := rank_Tmod_invol_ge (k := E) l (t := η ⟨t₀, ht₀S⟩) hηt hηt1
    have h2 := hdispT ⟨t₀, ht₀S⟩
    have h3 := Nat.mul_le_mul_left d h1
    simp only at h2
    omega
  obtain ⟨x, t, w, hw1, hwq, hxσ, hxt⟩ := exists_torus_commutator_SU hL hirrG hσ2 hσN hσS hK η
  have hxconj : (Tmod K l E (η x) - 1).rank = (Tmod K l E (t * η x * t⁻¹) - 1).rank :=
    (rank_Tmod_conj l t (η x)).symm
  rcases lbl_cases (by omega) l hl0 (by omega) hinv hSN hSO hrk with
    ⟨hdn, i₀, hz, ha, hb, hc⟩ | ⟨hn2, hd1', hl2⟩
  · have h8 : 8 ≤ (Tmod K l E (t * η x * t⁻¹) - 1).rank :=
      eight_le_rank_Tmod_single101 hz ha hb hc (t * η x * t⁻¹) w hw1 hxt
    have hn2 : n = 2 := by
      have hle : d * 8 ≤ 6 * n + 4 := by
        calc d * 8 ≤ d * (Tmod K l E (t * η x * t⁻¹) - 1).rank :=
              Nat.mul_le_mul_left d h8
          _ = d * (Tmod K l E (η x) - 1).rank := by rw [hxconj]
          _ = disp (x : MulAut U) := (hdispT x).symm
          _ ≤ 2 * disp σ := hxσ
          _ ≤ 2 * (3 * n + 2) := Nat.mul_le_mul_left 2 hσD
          _ = 6 * n + 4 := by ring
      rw [hdn] at hle
      omega
    exact ⟨hn2, adjointOmega6_of_single101 hL hK η ρ hρ hC hnt hDcard hdn l hdimW hz ha hb hc
      ιK ιD⟩
  · exfalso
    subst hn2
    have h17 := seventeen_le_rank_Tmod_omega2_pair (k := E) l hl2 (t * η x * t⁻¹) w hw1
      (by simpa using hwq) hxt
    have := hdispT x
    rw [hd1', one_mul, hxconj] at this
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
