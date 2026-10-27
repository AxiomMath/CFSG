module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
import CFSG.LieType.Chevalley.TorusCoordinates
import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.StandardType.ExcFrames.E6QPlusThree CFSG.RankThree.PartOne.KE6

open scoped Matrix


private def e6w_A : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) :=
  (Int.castRingHom (ZMod 3)).mapMatrix (Tag.cartan .F4)

private def e6w_S : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) :=
  (Int.castRingHom (ZMod 3)).mapMatrix (Tag.symmetrizedCartan .F4)

private def e6w_SinvInt : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 2, 1; 0, 0, 1, 2; 2, 1, 0, 0; 1, 2, 0, 2]

private def e6w_Sinv : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) :=
  (Int.castRingHom (ZMod 3)).mapMatrix e6w_SinvInt

private theorem e6w_S_mul_Sinv : e6w_S * e6w_Sinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e6w_Sinv_mul_S : e6w_Sinv * e6w_S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e6w_cartanInv_mul_cartan : cartanInvF4 * Tag.F4.cartan = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.F4.rank))).mp cartan_mul_cartanInv_F4

private theorem e6w_cartanTranspose_mul :
    Tag.F4.cartan.transpose * cartanInvF4.transpose = 1 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
    congrArg Matrix.transpose e6w_cartanInv_mul_cartan

private theorem e6w_cartanInvTranspose_mul :
    cartanInvF4.transpose * Tag.F4.cartan.transpose = 1 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
    congrArg Matrix.transpose cartan_mul_cartanInv_F4

private noncomputable def e6w_T (v : Fin Tag.F4.rank → ZMod 3) : Fin Tag.F4.rank → ZMod 3 :=
  e6w_Sinv *ᵥ v

private theorem e6w_T_add (v w : Fin Tag.F4.rank → ZMod 3) :
    e6w_T (v + w) = e6w_T v + e6w_T w := by
  change e6w_Sinv *ᵥ (v + w) = e6w_Sinv *ᵥ v + e6w_Sinv *ᵥ w
  rw [Matrix.mulVec_add]

private theorem e6w_T_zero : e6w_T (0 : Fin Tag.F4.rank → ZMod 3) = 0 := by
  change e6w_Sinv *ᵥ (0 : Fin Tag.F4.rank → ZMod 3) = 0
  rw [Matrix.mulVec_zero]

private noncomputable def e6w_coord :
    (Fin Tag.F4.rank → Multiplicative (ZMod 3)) →*
      Multiplicative (Fin Tag.F4.rank → ZMod 3) where
  toFun a := Multiplicative.ofAdd (e6w_T (fun j => (a j).toAdd))
  map_one' := by
    apply Multiplicative.ofAdd.injective
    change e6w_T (0 : Fin Tag.F4.rank → ZMod 3) = 0
    rw [e6w_T_zero]
  map_mul' a b := by
    apply Multiplicative.ofAdd.injective
    change e6w_T ((fun j => (a j).toAdd) + (fun j => (b j).toAdd)) =
      e6w_T (fun j => (a j).toAdd) + e6w_T (fun j => (b j).toAdd)
    rw [e6w_T_add]

private theorem e6w_coord_apply (a : Fin Tag.F4.rank → Multiplicative (ZMod 3)) :
    e6w_coord a = Multiplicative.ofAdd (e6w_T (fun j => (a j).toAdd)) := rfl

private theorem e6w_S_mulVec_T (v : Fin Tag.F4.rank → ZMod 3) : e6w_S *ᵥ e6w_T v = v := by
  change e6w_S *ᵥ (e6w_Sinv *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, e6w_S_mul_Sinv, Matrix.one_mulVec]

private theorem e6w_T_mulVec_S (v : Fin Tag.F4.rank → ZMod 3) : e6w_T (e6w_S *ᵥ v) = v := by
  change e6w_Sinv *ᵥ (e6w_S *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, e6w_Sinv_mul_S, Matrix.one_mulVec]

private theorem e6w_T_injective : Function.Injective e6w_T := by
  intro v w h
  have hv := e6w_S_mulVec_T v
  have hw := e6w_S_mulVec_T w
  rw [h] at hv
  rw [hv] at hw
  exact hw

private theorem e6w_torusAct_simple (k : Fin Tag.F4.rank)
    (s : Fin Tag.F4.rank → ZMod 3) :
    TableBExc.torusAct .F4 3 (simple .F4 k) s =
      s - (∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod 3) * s j) • Pi.single k 1 := by
  rw [TableBExc.torusAct, simple_smul]
  funext i
  simp only [TableBExc.redMod, TableBExc.liftMod, reflect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  rw [ZMod.natCast_zmod_val]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.natCast_zmod_val]
  · by_cases hi : i = k
    · subst hi
      simp
    · simp [hi]

private def e6w_d : Fin Tag.F4.rank → ZMod 3 :=
  fun i => if i.val < 2 then 2 else 1

private def e6w_Dinv : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) :=
  Matrix.diagonal e6w_d

private theorem e6w_A_mul_Sinv : e6w_A * e6w_Sinv = e6w_Dinv := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e6w_Sinv_mul_AT : e6w_Sinv * e6w_A.transpose = e6w_Dinv := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e6w_Dinv_mulVec (v : Fin Tag.F4.rank → ZMod 3) :
    e6w_Dinv *ᵥ v = fun i => e6w_d i * v i := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [e6w_Dinv, Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [e6w_Dinv, Matrix.diagonal_apply, if_neg (Ne.symm hj), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem e6w_torusAct_coord (k : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ZMod 3) :
    TableBExc.torusAct .F4 3 (simple .F4 k) (e6w_T v) =
      e6w_T v - e6w_T (e6w_A.transpose *ᵥ (v k • Pi.single k 1)) := by
  have h1 : (∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod 3) * (e6w_T v) j) =
      (e6w_Dinv *ᵥ v) k := by
    rw [show (∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod 3) * (e6w_T v) j) =
        (e6w_A *ᵥ e6w_T v) k from by
      simp [e6w_A, Matrix.mulVec, dotProduct]]
    change (e6w_A *ᵥ (e6w_Sinv *ᵥ v)) k = (e6w_Dinv *ᵥ v) k
    rw [Matrix.mulVec_mulVec, e6w_A_mul_Sinv]
  have h2 : e6w_T (e6w_A.transpose *ᵥ (v k • Pi.single k 1)) =
      e6w_Dinv *ᵥ (v k • Pi.single k 1) := by
    change e6w_Sinv *ᵥ (e6w_A.transpose *ᵥ (v k • Pi.single k 1)) =
      e6w_Dinv *ᵥ (v k • Pi.single k 1)
    rw [Matrix.mulVec_mulVec, e6w_Sinv_mul_AT]
  rw [e6w_torusAct_simple, h1, h2, e6w_Dinv_mulVec v,
    e6w_Dinv_mulVec (v k • Pi.single k 1)]
  funext i
  by_cases hi : i = k
  · subst hi
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, mul_one]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, mul_zero]
    ring

private theorem e6w_cartanF4_eq : Tag.F4.cartan.transpose = CartanMatrix.F₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem e6w_coxeterF4_eq :
    CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
  FrameRoute.coxeterF4_eq.symm

private theorem e6w_weylTuple_pow {L : Type} [Field L]
    (w : WeylGroup .E6) (a : Fin Tag.E6.rank → Lˣ) (q : ℕ) :
    weylTuple w (a ^ q) = (weylTuple w a) ^ q := by
  funext i
  change rootChar (a ^ q) (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
    (rootChar a (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) ^ q
  rw [CFSG.RankThree.Chevalley.rootChar_pow_tuple]

private theorem e6w_eqpN_pow_sq {L : Type} [Field L] [IsAlgClosed L]
    {Fr : L →+* L} {q : ℕ} (hq1 : 1 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    {t : ModGL .E6 L} (ht : t ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN L) Fr) :
    t ^ (q ^ 2 - 1) = 1 := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht.1
  rw [ha] at ht ⊢
  have hfix : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.negPhi Fr (eqpN L)
      (rootDiagUnit .E6 a) = rootDiagUnit .E6 a :=
    ((CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mem_twistedTorusOf_iff_negPhi).1 ht).2
  have ha' : weylTuple e6W0 (a ^ q) = a := by
    rw [show eqpN L = canonicalRep (coxeterSystem .E6) L e6W0 from rfl,
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.negPhi_rootDiagUnit_gen_pow Fr e6W0
        hFr] at hfix
    exact rootDiagUnit_injective hfix
  have h1 : a ^ q = weylTuple e6W0 a := by
    have h := congrArg (weylTuple e6W0) ha'
    rw [weylTuple_weylTuple, e6W0_mul_self, weylTuple_one] at h
    exact h
  have h2 : a ^ (q ^ 2) = a := by
    calc a ^ (q ^ 2) = (a ^ q) ^ q := by rw [← pow_mul, sq]
      _ = (weylTuple e6W0 a) ^ q := by rw [h1]
      _ = weylTuple e6W0 (a ^ q) := (e6w_weylTuple_pow e6W0 a q).symm
      _ = a := ha'
  have h3 : a ^ (q ^ 2 - 1) = 1 := by
    have h4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    have : a ^ (q ^ 2 - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel h4, h2, one_mul]
    exact mul_right_cancel this
  have := map_pow (rootDiagUnitHom .E6 L) a (q ^ 2 - 1)
  rw [h3, map_one] at this
  exact this.symm

theorem e6Two_frame_selfCentralizing {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g0 : ModGL .E6 (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (D : E6QPlusThreeFrame K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hg0C : g0 ∈ adjointGroup .E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * eqpN (AlgebraicClosure K))
    (hζo : orderOf ζ = 3) (hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ 2)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
      g0 * e6ThreeDiag ζ hζ s * g0⁻¹) :
    ∀ g : adjointGroup .E6 K, (∀ s, g * D.frame s = D.frame s * g) → g ∈ D.frame.range := by
  classical
  intro g hg
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let D0 : LangDatum .E6 L := LangDatum.ofFrobenius Fr (Nat.card K) hFr e6W0 hg0C hg0
  have hd : LangDescent D0 7 ((baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.langDescent_ofFrobenius (Or.inr (Or.inl rfl)) e6W0 K
      hFr hg0C hg0
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK2 : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hqpow : IsPrimePow D0.q ∧ ((D0.q : ℕ) : L) = 0 := by
    refine ⟨?_, ?_⟩
    · show IsPrimePow (Nat.card K)
      rw [hK2]
      exact Nat.prime_two.isPrimePow.pow f.ne_zero
    · show ((Nat.card K : ℕ) : L) = 0
      rw [hK2]
      exact (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 f.ne_zero)
  have hpq : ¬ 5 ∣ D0.q := by
    show ¬ 5 ∣ Nat.card K
    rw [hK2]
    intro h5
    have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h5
    norm_num at h52
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved .E6 L D0
  let S : LangSetup .E6 L 5 :=
    D0.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model
  have hSD : S.D = D0 := rfl
  let bc : adjointGroup .E6 K →* ModGL .E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype
  let ι : adjointGroup .E6 K →* ModGL .E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  have hι : ∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0 := by
    intro c
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (c : ModGL .E6 K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hrange : ι.range = S.Γ := by
    have hcomp : ι = (MulAut.conj g0⁻¹).toMonoidHom.comp bc := rfl
    rw [hcomp, MonoidHom.range_comp, show S.Γ = S.D.Γ from rfl, hSD, hd.Γ_eq]
    rfl
  have hinjι : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  have hιframe : ∀ s, ι (D.frame s) = e6ThreeDiag ζ hζ s := by
    intro s
    rw [hι, hcoord s]
    group
  have hΓle : S.Γ ≤ adjointGroup .E6 L := by
    rw [show S.Γ = S.D.Γ from rfl, hSD, LangDatum.Γ]
    exact (Subgroup.commutator_le_self D0.model).trans (by
      rw [LangDatum.model]
      exact inf_le_left)
  have hιgC : ι g ∈ adjointGroup .E6 L := hΓle (by rw [← hrange]; exact ⟨g, rfl⟩)
  have hcomm : ∀ s, ι g * e6ThreeDiag ζ hζ s = e6ThreeDiag ζ hζ s * ι g := by
    intro s
    rw [← hιframe s, ← map_mul, ← map_mul]
    exact congrArg ι (hg s)
  have hιgT : ι g ∈ torusGroup .E6 L :=
    mem_torusGroup_of_commute_e6ThreeDiag hζo hζ hιgC hcomm
  have hιgModel : ι g ∈ S.D.model := by
    have h1 : ι g ∈ S.Γ := by rw [← hrange]; exact ⟨g, rfl⟩
    exact Subgroup.commutator_le_self S.D.model h1
  have hιgFix : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.negPhi Fr (eqpN L)
      (ι g) = ι g := by
    have h := ((LangDatum.mem_model D0).mp (by rw [← hSD]; exact hιgModel)).2
    change D0.n * Units.map (entrywiseHom Fr) (ι g) * D0.n⁻¹ = ι g at h
    rw [show D0.n = eqpN L from rfl] at h
    rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.negPhi_apply]
    exact h
  have hιgTorus : ι g ∈ CFSG.RankThree.PartOne.KE.twistedTorus (eqpN L) Fr :=
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mem_twistedTorusOf_iff_negPhi).2
      ⟨hιgT, hιgFix⟩
  have hpow : (ι g) ^ (Nat.card K ^ 2 - 1) = 1 :=
    e6w_eqpN_pow_sq (by omega) (fun c => hFr c) hιgTorus
  have hpow3 : (ι g) ^ 3 = 1 := by
    have h3 : Nat.card K ^ 2 - 1 = 3 := by rw [hK]; norm_num
    rwa [h3] at hpow
  have hg3 : g ^ 3 = 1 := by
    apply hinjι
    rw [map_pow, hpow3, map_one]
  exact D.mem_frame_range_of_commute g hg hg3

theorem e6Two_torusWitness {K : Type} [Field K] [Finite K] [CharP K 2] (D : E6QPlusThreeFrame K)
    (hsurj : Function.Surjective D.weyl)
    (hSC : ∀ g : adjointGroup .E6 K, (∀ s, g * D.frame s = D.frame s * g) → g ∈ D.frame.range) :
    ∃ (nk : Fin Tag.F4.rank → adjointGroup .E6 K)
      (wt : GGTorusTorWit 3 4 (adjointGroup .E6 K)
        (D.frame.range.map (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)))),
      (∀ k s, nk k * D.frame (Multiplicative.ofAdd s) * (nk k)⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 k) s))) ∧
      (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
  classical
  let G := adjointGroup .E6 K
  let E : Subgroup G := D.frame.range
  have hex : ∀ k : Fin Tag.F4.rank, ∃ a : D.N, D.weyl a = simple .F4 k :=
    fun k => hsurj (simple .F4 k)
  let nk : Fin Tag.F4.rank → adjointGroup .E6 K :=
    fun k => (Classical.choose (hex k)).1
  have hnkN : ∀ k, nk k ∈ D.N := fun k => (Classical.choose (hex k)).2
  have hnkweyl : ∀ k, D.weyl ⟨nk k, hnkN k⟩ = simple .F4 k := by
    intro k
    have h : (⟨nk k, hnkN k⟩ : D.N) = Classical.choose (hex k) := Subtype.ext rfl
    rw [h]
    exact Classical.choose_spec (hex k)
  have hact : ∀ k s, nk k * D.frame (Multiplicative.ofAdd s) * (nk k)⁻¹ =
      D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 k) s)) := by
    intro k s
    have h := D.conj_frame ⟨nk k, hnkN k⟩ s
    rwa [hnkweyl k] at h
  have hact_inv : ∀ k s, (nk k)⁻¹ * D.frame (Multiplicative.ofAdd s) * nk k =
      D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 k) s)) := by
    intro k s
    have h := hact k (TableBExc.torusAct .F4 3 (simple .F4 k) s)
    rw [← TableBExc.torusAct_mul, simple_mul_simple_self, TableBExc.torusAct_one] at h
    rw [← h]
    group
  have hnk_norm : ∀ k, nk k ∈ Subgroup.normalizer (E : Set G) := by
    intro k
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨s, rfl⟩ := hx
      rw [← ofAdd_toAdd s, hact k (Multiplicative.toAdd s)]
      exact ⟨Multiplicative.ofAdd
        (TableBExc.torusAct .F4 3 (simple .F4 k) (Multiplicative.toAdd s)), rfl⟩
    · intro hx
      obtain ⟨s, hs⟩ := hx
      have hx' : x = (nk k)⁻¹ * D.frame s * nk k := by
        rw [hs]; group
      rw [hx', ← ofAdd_toAdd s, hact_inv k (Multiplicative.toAdd s)]
      exact ⟨Multiplicative.ofAdd
        (TableBExc.torusAct .F4 3 (simple .F4 k) (Multiplicative.toAdd s)), rfl⟩
  have hn : ∀ k, MulAut.conj (nk k) ∈
      Subgroup.normalizer ((scalarA E) : Set (MulAut G)) := fun k =>
    Subgroup.le_normalizer_map (MulAut.conj : G →* MulAut G)
      (Subgroup.mem_map_of_mem (MulAut.conj : G →* MulAut G) (hnk_norm k))
  have hN : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ v : WeylGroup .F4, ∀ s,
      g * D.frame (Multiplicative.ofAdd s) * g⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 v s)) := by
    intro g hg
    have hmemN : g ∈ D.N := D.mem_N_of_conj g fun s =>
      (Subgroup.mem_normalizer_iff.mp hg (D.frame s)).1 ⟨s, rfl⟩
    exact ⟨D.weyl ⟨g, hmemN⟩, fun s => D.conj_frame ⟨g, hmemN⟩ s⟩
  let φ : (Fin Tag.F4.rank → Multiplicative (ZMod 3)) →* G := D.frame.comp e6w_coord
  have hφ_apply : ∀ a, φ a =
      D.frame (Multiplicative.ofAdd (e6w_T (fun j => (a j).toAdd))) := by
    intro a
    change D.frame (e6w_coord a) = _
    rw [e6w_coord_apply]
  have hφ : Function.Injective φ := by
    intro a b hab
    change D.frame (e6w_coord a) = D.frame (e6w_coord b) at hab
    have h1 : e6w_coord a = e6w_coord b := D.frame_injective hab
    rw [e6w_coord_apply, e6w_coord_apply] at h1
    have h2 : e6w_T (fun j => (a j).toAdd) = e6w_T (fun j => (b j).toAdd) :=
      Multiplicative.ofAdd.injective h1
    have h3 : (fun j => (a j).toAdd) = (fun j => (b j).toAdd) := e6w_T_injective h2
    funext j
    have hj := congrFun h3 j
    calc a j = Multiplicative.ofAdd ((a j).toAdd) := (ofAdd_toAdd (a j)).symm
      _ = Multiplicative.ofAdd ((b j).toAdd) := by rw [hj]
      _ = b j := ofAdd_toAdd (b j)
  have hrange_φ : φ.range = E := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact ⟨e6w_coord a, rfl⟩
    · rintro _ ⟨s, rfl⟩
      refine ⟨fun j => Multiplicative.ofAdd ((e6w_S *ᵥ Multiplicative.toAdd s) j), ?_⟩
      rw [hφ_apply]
      have h1 : (fun j => Multiplicative.toAdd
          (Multiplicative.ofAdd ((e6w_S *ᵥ Multiplicative.toAdd s) j))) =
          e6w_S *ᵥ Multiplicative.toAdd s := by
        funext j; rw [toAdd_ofAdd]
      rw [h1, ← ofAdd_toAdd s]
      exact congrArg (fun z => D.frame z)
        (congrArg Multiplicative.ofAdd (e6w_T_mulVec_S (Multiplicative.toAdd s)))
  have hE : ∀ g : G, g ∈ E ↔ g ^ 3 = 1 ∧ g ∈ φ.range := by
    intro g
    constructor
    · intro hg
      refine ⟨?_, ?_⟩
      · obtain ⟨s, rfl⟩ := hg
        rw [← map_pow]
        have hs3 : s ^ 3 = 1 := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_pow, toAdd_one]
          funext j
          simp [nsmul_eq_mul, show (3 : ZMod 3) = 0 from by decide]
        rw [hs3, map_one]
      · rw [hrange_φ]; exact hg
    · rintro ⟨-, hgφ⟩
      rw [hrange_φ] at hgφ
      exact hgφ
  have hcent : Subgroup.centralizer (E : Set G) ≤ φ.range := by
    intro g hg
    rw [hrange_φ]
    exact hSC g fun s =>
      (Subgroup.mem_centralizer_iff.mp hg (D.frame s) ⟨s, rfl⟩).symm
  have hnformula : ∀ k (a : Fin Tag.F4.rank → Multiplicative (ZMod 3)),
      nk k * φ a * (nk k)⁻¹ =
        φ a * (φ (corTuple (Tag.F4.cartan) k (a k)))⁻¹ := by
    intro k a
    have hcor : (fun i => ((corTuple (Tag.F4.cartan) k (a k)) i).toAdd) =
        e6w_A.transpose *ᵥ ((fun j => (a j).toAdd) k • Pi.single k (1 : ZMod 3)) := by
      funext i
      calc ((corTuple (Tag.F4.cartan) k (a k)) i).toAdd
          = ((Tag.F4.cartan k i : ℤ) : ZMod 3) * Multiplicative.toAdd (a k) := by
            rw [corTuple_apply,
              show a k = Multiplicative.ofAdd (Multiplicative.toAdd (a k)) from
                (ofAdd_toAdd (a k)).symm, ← ofAdd_zsmul, toAdd_ofAdd]
            exact zsmul_eq_mul _ _
        _ = (e6w_A.transpose *ᵥ
              (Multiplicative.toAdd (a k) • Pi.single k (1 : ZMod 3))) i := by
            change ((Tag.F4.cartan k i : ℤ) : ZMod 3) * Multiplicative.toAdd (a k) =
              ∑ j : Fin Tag.F4.rank, ((Tag.F4.cartan j i : ℤ) : ZMod 3) *
                (Multiplicative.toAdd (a k) *
                  (Pi.single k (1 : ZMod 3) : Fin Tag.F4.rank → ZMod 3) j)
            rw [Finset.sum_eq_single k]
            · simp
            · intro j _ hj
              simp [Pi.single_eq_of_ne hj]
            · intro hk
              exact absurd (Finset.mem_univ k) hk
    have hwT : e6w_T (fun i => ((corTuple (Tag.F4.cartan) k (a k)) i).toAdd) =
        e6w_T (e6w_A.transpose *ᵥ
          ((fun j => (a j).toAdd) k • Pi.single k (1 : ZMod 3))) := by
      rw [hcor]
    rw [hφ_apply a, hφ_apply (corTuple (Tag.F4.cartan) k (a k)),
      hact k (e6w_T (fun j => (a j).toAdd))]
    rw [← map_inv, ← map_mul, hwT, ← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg]
    exact congrArg (fun z => D.frame z)
      (congrArg Multiplicative.ofAdd (e6w_torusAct_coord k (fun j => (a j).toAdd)))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨_hnA, ρ, hρ, hρrange, hρsimple⟩ :=
    exists_markedWeyl_innerHom (τ := .F4) (p := 3) (by decide : Odd 3) E
      (CFSG.mulAutConj_injective_of_center_eq_bot
        (center_adjointGroup_eq_bot (τ := .E6) (K := K)))
      D.frame D.frame_injective rfl nk hact hN
  have hζp : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide +revert
  have hζ1 : (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by decide +revert
  obtain ⟨w, _hwT, _hwTsc, _hwcor, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
      (m := 3) (N := Tag.F4.rank) (p := 3) (μ := Multiplicative (ZMod 3))
      (MulEquiv.refl (Multiplicative (ZMod 3))) φ hφ
      (Tag.F4.cartan.transpose) cartanInvF4.transpose
      (by rw [e6w_cartanTranspose_mul, map_one])
      (by rw [e6w_cartanInvTranspose_mul, map_one])
      (center_adjointGroup_eq_bot (τ := .E6) (K := K)) E hE
      (Multiplicative.ofAdd (1 : ZMod 3)) hζp hζ1 nk hn hnformula hcent
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      ρ hρ hρrange hρsimple
  refine ⟨nk, w, hact, hwn, ?_⟩
  have hwh' : w.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
    unfold GGTorusTorWit.Holds at hwh ⊢
    rw [e6w_cartanF4_eq, e6w_coxeterF4_eq] at hwh
    exact hwh
  exact hwh'

end CFSG.StandardType

end
