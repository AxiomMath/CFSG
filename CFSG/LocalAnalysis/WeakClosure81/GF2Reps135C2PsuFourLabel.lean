module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.HardMathSupport.U4FF.ClassComb
public import CFSG.HardMathSupport.U4FF.Disp
import CFSG.HardMathSupport.U4FF.ClassClassifHolds
import CFSG.HardMathSupport.U4FF.Natural4
import CFSG.HardMathSupport.U4FF.Omega2Gen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
import CFSG.HardMathSupport.U4FF.ClassFinalConj
import CFSG.HardMathSupport.U4FF.ClassFinalDim
import CFSG.HardMathSupport.U4FF.ClassFinalRep
import CFSG.HardMathSupport.U4FF.ClassRank
import CFSG.HardMathSupport.U4FF.ClassRankF2
import CFSG.HardMathSupport.U4FF.ClassSingle

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC (IsU4Group NaturalU4Mod)
open CFSG.HardMathSupport.U4FF
open CFSG.QuasithinUnique.Setup.Family (binaryLin)
open CFSG.QuasithinUnique.Setup.X7 (matRep)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing finite_endRing)

private theorem w135c2_psu_four_natural_of_singleN
    {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)] {n : ℕ} [NeZero n]
    {L : Subgroup (MulAut S)} (hL : IsU4Group n L)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥L ≃* SU4 K n)
    {ρ : Representation (ZMod 2) (SU4 K n) (Additive S)} [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥L) (s : S), ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut S) s))
    (hnt : ∃ g, ρ g ≠ 1) {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    {l : Lbl n} (hdimW : Module.finrank (EndRing ρ) (Additive S) = l.dim)
    (hinv : l.RotInv d) (hSN : l.SingleN) :
    NaturalU4Mod n L := by
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive S) := Module.Finite.of_finite
  have h4 : Module.finrank (EndRing ρ) (Additive S) = 4 := by
    rw [hdimW]
    exact Lbl.dim_eq_four_of_singleN hSN
  have h2n : 2 * n ∣ d := Lbl.SingleN.two_mul_dvd hSN hinv
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := ClassFinal.exists_ringHom_of_dvd hK' hDcard h2n
  letI : Algebra K (EndRing ρ) := ι.toAlgebra
  let b : Module.Basis (Fin 4) (EndRing ρ) (Additive S) :=
    Module.finBasisOfFinrankEq _ _ h4
  obtain ⟨l', -, ⟨Φ'⟩, hdim'⟩ :=
    u4_exists_label (classif_holds hK) hnt b ι (RingHom.id (EndRing ρ))
  obtain ⟨i₁, hz, hb1, hac⟩ := Lbl.singleN_of_dim_eq_four (hdim'.symm : l'.dim = 4)
  obtain ⟨ε, R, hR, hRval⟩ := ClassFinal.exists_coords η ρ hρ b
  have Φ'' : (matRep (Tmod K l' (EndRing ρ))).Equiv
      (matRep (u4MatHomE b (RingHom.id (EndRing ρ)))) := by
    rw [matRep_u4MatHomE]
    exact Φ'
  have hmap : ∀ x : ↥L, ((R x : GL (Fin 4) (EndRing ρ)) :
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
    exact (natural4Input_holds S n L hL hirr K hK η (EndRing ρ) ι ε R hR (EndRing ρ) P
      (i₁ : ℕ) (fun x => by rw [hmap x, hP (η x), hfr])).naturalU4Mod
  · obtain ⟨e, P', hP'⟩ := Tmod_single_S (K := K) (E := EndRing ρ) l' i₁ hz ha hb1 hc
    obtain ⟨P, hP⟩ := ClassFinal.exists_conj_of_single (Tmod K l' (EndRing ρ))
      (u4MatHomE b (RingHom.id (EndRing ρ)))
      (fun g => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
        (frobTw K (EndRing ρ) ((i₁ : ℕ) + n))) Φ'' e P' hP'
    exact (natural4Input_holds S n L hL hirr K hK η (EndRing ρ) ι ε R hR (EndRing ρ) P
      ((i₁ : ℕ) + n) (fun x => by rw [hmap x, hP (η x), hfr])).naturalU4Mod

private theorem w135c2_psu_four_natural_of_singleO
    {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)] {n : ℕ} [NeZero n]
    {L : Subgroup (MulAut S)} (hL : IsU4Group n L)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (η : ↥L ≃* SU4 K n)
    {ρ : Representation (ZMod 2) (SU4 K n) (Additive S)} [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥L) (s : S), ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut S) s))
    (hnt : ∃ g, ρ g ≠ 1) {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    {E : Type} [Field E] [Finite E] [CharP E 2] (ιK : K →+* E)
    (ιD : EndRing ρ →+* E) {l : Lbl n}
    (hdimW : Module.finrank (EndRing ρ) (Additive S) = l.dim)
    (hinv : l.RotInv d) (hSO : l.SingleO) :
    NaturalU4Mod n L := by
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive S) := Module.Finite.of_finite
  have h6 : Module.finrank (EndRing ρ) (Additive S) = 6 := by
    rw [hdimW]
    exact Lbl.dim_eq_six_of_singleO hSO
  obtain ⟨m', hm'⟩ := Lbl.SingleO.dvd hSO hinv
  letI : Algebra K E := ιK.toAlgebra
  letI : Algebra (EndRing ρ) E := ιD.toAlgebra
  let b : Module.Basis (Fin 6) (EndRing ρ) (Additive S) :=
    Module.finBasisOfFinrankEq _ _ h6
  obtain ⟨l', -, ⟨Φ'⟩, hdim'⟩ := u4_exists_label (classif_holds hK) hnt b ιK ιD
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
  refine (omega2InputGen_holds S n L hL hirr K hK η (EndRing ρ) m' hDcard' ε R hR E P
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

theorem w135c2_psu_four_label
    {S : Type} [CommGroup S]
    [Finite S] [Fact (∀ s : S, s * s = 1)] {n : ℕ} {L : Subgroup (MulAut S)} (hn : 1 ≤ n)
    (hL : IsU4Group n L) (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L) :
    NaturalU4Mod n L ∨
      ∃ (d : ℕ) (l : Lbl n), 1 ≤ d ∧ ¬ l.IsZero ∧ ¬ l.SingleN ∧ ¬ l.SingleO ∧
        Nat.card S = 2 ^ (d * l.dim) ∧
        ∀ t ∈ L, t ≠ 1 → t * t = 1 → d * l.rk1 ≤ disp t := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨K, _, _, _, hK, ⟨η⟩⟩ := exists_equiv_SU hL
  obtain ⟨hSnt, x₀, hx₀⟩ := ClassFinal.nontrivial_of_isU4Group hL
  haveI : Nontrivial S := hSnt
  let ρ := ClassFinal.binRep L η
  haveI : Fact ρ.IsIrreducible := ⟨ClassFinal.binRep_isIrreducible η hirr⟩
  have hnt : ∃ g, ρ g ≠ 1 := ⟨η x₀, ClassFinal.binRep_ne_one L η x₀ hx₀⟩
  have hρ : ∀ (x : ↥L) (s : S),
      ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut S) s) :=
    ClassFinal.binRep_eta L η
  have hlin : ∀ x : ↥L, ρ (η x) =
      (binaryLin ((x : ↥L) : MulAut S) : Additive S →ₗ[ZMod 2] Additive S) :=
    ClassFinal.binRep_eta_lin L η
  have hC : Classif K n := classif_holds hK
  obtain ⟨d, hd1, hDcard, hdesc⟩ := u4_descent hC hK hnt
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI : Module.Finite (EndRing ρ) (Additive S) := Module.Finite.of_finite
  let b₀ : Module.Basis (Fin (Module.finrank (EndRing ρ) (Additive S))) (EndRing ρ)
      (Additive S) := Module.finBasis (EndRing ρ) (Additive S)
  obtain ⟨E, _, _, _, ιK, ιD, l, hl0, ⟨Φ⟩, _hm1, _hm2, hdimW⟩ := hdesc b₀
  have hinv : l.RotInv d := by
    refine Lbl.rotInv_of_modEq l d ?_ _hm2
    rwa [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]] at _hm1
  by_cases hs : l.SingleN ∨ l.SingleO
  · rcases hs with hSN | hSO
    · exact Or.inl (w135c2_psu_four_natural_of_singleN hL hirr hK η hρ hnt hDcard hdimW hinv hSN)
    · exact Or.inl
        (w135c2_psu_four_natural_of_singleO hL hirr hK η hρ hnt hDcard ιK ιD hdimW hinv hSO)
  · refine Or.inr ⟨d, l, hd1, hl0, fun h => hs (Or.inl h), fun h => hs (Or.inr h), ?_, ?_⟩
    · have h1 : Nat.card (Additive S) =
          (2 ^ d) ^ Module.finrank (EndRing ρ) (Additive S) := by
        rw [Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := Additive S), hDcard]
      rw [hdimW, ← pow_mul] at h1
      exact (Nat.card_congr Additive.toMul).symm.trans h1
    · intro t ht ht1 ht2
      letI : Algebra K E := ιK.toAlgebra
      have hxt : (⟨t, ht⟩ : ↥L) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
      have hηt : η ⟨t, ht⟩ * η ⟨t, ht⟩ = 1 := by rw [← map_mul, hxt, map_one]
      have hηt1 : η ⟨t, ht⟩ ≠ 1 := by
        intro h
        apply ht1
        have := η.injective (h.trans (map_one η).symm)
        exact congrArg Subtype.val this
      have h1 := finrank_range_Tmod hDcard b₀ ιD l Φ hdimW (η ⟨t, ht⟩)
      have h2 := rank_Tmod_invol_ge (k := E) l hηt hηt1
      have h3 := Nat.mul_le_mul_left d h2
      rw [hlin ⟨t, ht⟩] at h1
      have h4 : Module.finrank (ZMod 2)
          (LinearMap.range ((binaryLin t : Additive S →ₗ[ZMod 2] Additive S) - 1)) =
          d * (Tmod K l E (η ⟨t, ht⟩) - 1).rank := h1
      unfold disp
      rw [h4]
      exact h3

end CFSG.LocalAnalysis.WeakClosure81
