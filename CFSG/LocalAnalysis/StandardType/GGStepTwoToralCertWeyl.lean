module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertKac

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag} {p : ℕ}

theorem tcCartan_getD (τ : Tag) (i j : Fin τ.rank) :
    tcEnt ((tcCartan τ ()).getD i #[]) j = τ.cartan i j := by
  simp [tcCartan, tcEnt]

theorem tcW_latChar_single (f : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    latChar p f (Pi.single i 1) = f i := by
  simp [latChar, Pi.single_apply]

theorem tcW_latChar_sub (f : Fin τ.rank → ZMod p) (α β : Fin τ.rank → ℤ) :
    latChar p f (α - β) = latChar p f α - latChar p f β := by
  simp [latChar, sub_mul, Finset.sum_sub_distrib]

theorem tcW_latChar_zsmul (f : Fin τ.rank → ZMod p) (c : ℤ) (α : Fin τ.rank → ℤ) :
    latChar p f (c • α) = c * latChar p f α := by
  simp [latChar, Finset.mul_sum, mul_assoc]

theorem tcW_latChar_sum (f : Fin τ.rank → ZMod p) (c : Fin τ.rank → ℤ)
    (g : Fin τ.rank → Fin τ.rank → ℤ) :
    latChar p f (∑ l, c l • g l) = ∑ l, (c l : ZMod p) * latChar p f (g l) := by
  simp only [latChar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

theorem latChar_weyl_smul (u : WeylGroup τ) (f : Fin τ.rank → ZMod p) (α : Fin τ.rank → ℤ) :
    latChar p f (u • α) = latChar p (cowAct u⁻¹ f) α := by
  have hsum : (∑ l, α l • (Pi.single l 1 : Fin τ.rank → ℤ)) = α := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← hsum, Finset.smul_sum]
  simp_rw [smul_comm u (α _)]
  rw [tcW_latChar_sum]
  conv_rhs => rw [latChar]
  simp only [cowAct, inv_inv]

theorem cowAct_one (f : Fin τ.rank → ZMod p) : cowAct (1 : WeylGroup τ) f = f := by
  funext i
  simp only [cowAct, inv_one, one_smul, tcW_latChar_single]

theorem cowAct_mul (u v : WeylGroup τ) (f : Fin τ.rank → ZMod p) :
    cowAct (u * v) f = cowAct u (cowAct v f) := by
  funext i
  change latChar p f ((u * v)⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) =
    latChar p (cowAct v f) (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
  rw [mul_inv_rev, mul_smul, latChar_weyl_smul, inv_inv]

theorem cowAct_inv_cowAct (u : WeylGroup τ) (f : Fin τ.rank → ZMod p) :
    cowAct u⁻¹ (cowAct u f) = f := by
  rw [← cowAct_mul, inv_mul_cancel, cowAct_one]

theorem cowAct_zero (u : WeylGroup τ) : cowAct u (0 : Fin τ.rank → ZMod p) = 0 := by
  funext i
  simp [cowAct, latChar]

theorem cowAct_simple (i : Fin τ.rank) (f : Fin τ.rank → ZMod p) (j : Fin τ.rank) :
    cowAct (simple τ i) f j = f j - (τ.cartan i j : ZMod p) * f i := by
  change latChar p f ((simple τ i)⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) = _
  have hs : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  rw [(coxeterSystem τ).inv_simple, simple_smul, reflect, hs, tcW_latChar_sub,
    tcW_latChar_zsmul, tcW_latChar_single, tcW_latChar_single]

theorem cowAct_rootReflection_θ (f : Fin τ.rank → ZMod p) (j : Fin τ.rank) :
    cowAct (rootReflection (kacOf τ).θ) f j =
      f j - ((kacOf τ).c j : ZMod p) * latChar p f (kacOf τ).θ := by
  change latChar p f ((rootReflection (kacOf τ).θ)⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) = _
  rw [rootReflection_inv (kacOf τ).isRoot_θ, rootReflection_smul (kacOf τ).isRoot_θ,
    KacData.corootPair_θ, dotProduct_single, mul_one, tcW_latChar_sub, tcW_latChar_zsmul,
    tcW_latChar_single]

@[expose] noncomputable def tcLetterElt (τ : Tag) (l : ℕ) : WeylGroup τ :=
  if h : l < τ.rank then simple τ ⟨l, h⟩ else rootReflection (kacOf τ).θ

@[expose] noncomputable def tcWordElt (τ : Tag) : List ℕ → WeylGroup τ
  | [] => 1
  | l :: w => tcWordElt τ w * tcLetterElt τ l

@[expose] noncomputable def tcGenWordElt (τ : Tag) (gens : Array (List ℕ)) :
    List ℕ → WeylGroup τ
  | [] => 1
  | gi :: w => tcGenWordElt τ gens w * tcWordElt τ (gens.getD gi [])

theorem tcLetter_cast (l : ℕ) (f : Array ℤ) :
    tcVec p τ.rank (tcLetter p τ.rank (tcCartan τ ()) (tcTheta τ) (tcCoTheta τ) l f) =
      cowAct (tcLetterElt τ l) (tcVec p τ.rank f) := by
  funext j
  by_cases h : l < τ.rank
  · have hc := tcCartan_getD τ ⟨l, h⟩ j
    rw [tcLetter, if_pos h, tcLetterElt, dif_pos h, cowAct_simple, tcVec_ofFn]
    simp only [ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, tcVec_apply] at hc ⊢
    rw [hc]
  · rw [tcLetter, if_neg h, tcLetterElt, dif_neg h, cowAct_rootReflection_θ, tcVec_ofFn]
    simp only [ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, tcDot_cast, kacOf_c_apply,
      tcVec_apply]
    congr 2
    simp only [latChar, tcFun, kacOf_θ_apply]

theorem tcWord_cast (w : List ℕ) (f : Array ℤ) :
    tcVec p τ.rank (tcWord p τ.rank (tcCartan τ ()) (tcTheta τ) (tcCoTheta τ) w f) =
      cowAct (tcWordElt τ w) (tcVec p τ.rank f) := by
  induction w generalizing f with
  | nil => exact (cowAct_one _).symm
  | cons l w ih =>
    rw [tcWordElt, cowAct_mul, ← tcLetter_cast]
    exact ih _

theorem tcGenWord_cast (gens : Array (List ℕ)) (w : List ℕ) (f : Array ℤ) :
    tcVec p τ.rank (tcGenWord p τ.rank (tcCartan τ ()) (tcTheta τ) (tcCoTheta τ) gens w f) =
      cowAct (tcGenWordElt τ gens w) (tcVec p τ.rank f) := by
  induction w generalizing f with
  | nil => exact (cowAct_one _).symm
  | cons gi w ih =>
    rw [tcGenWordElt, cowAct_mul, ← tcWord_cast]
    exact ih _

theorem commutesPi_one (π : Equiv.Perm (Fin τ.rank)) : CommutesPi π (1 : WeylGroup τ) := by
  intro α
  simp only [one_smul]

theorem commutesPi_mul {π : Equiv.Perm (Fin τ.rank)} {u v : WeylGroup τ} (hu : CommutesPi π u)
    (hv : CommutesPi π v) : CommutesPi π (u * v) := by
  intro α
  rw [mul_smul, hv, hu, mul_smul]

theorem commutesPi_inv {π : Equiv.Perm (Fin τ.rank)} {u : WeylGroup τ} (hu : CommutesPi π u) :
    CommutesPi π u⁻¹ := by
  intro α
  have h := hu (u⁻¹ • α)
  rw [smul_inv_smul] at h
  rw [← h, inv_smul_smul]

theorem commutesPi_perm_one (u : WeylGroup τ) :
    CommutesPi (1 : Equiv.Perm (Fin τ.rank)) u := by
  intro α
  rfl

theorem commutesPi_genWordElt {π : Equiv.Perm (Fin τ.rank)} {gens : Array (List ℕ)}
    (h : ∀ gi, CommutesPi π (tcWordElt τ (gens.getD gi []))) (w : List ℕ) :
    CommutesPi π (tcGenWordElt τ gens w) := by
  induction w with
  | nil => exact commutesPi_one π
  | cons gi w ih => exact commutesPi_mul ih (h gi)

theorem tcW_latPerm_simple_smul {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    latPerm π (simple τ i • α) = simple τ (π i) • latPerm π α := by
  rw [simple_smul, simple_smul]
  exact permLattice_reflect hπ i α

theorem tcW_commutesPi_simple {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {i : Fin τ.rank} (hi : π i = i) :
    CommutesPi π (simple τ i) := by
  intro α
  rw [tcW_latPerm_simple_smul hπ, hi]

theorem tcW_commutesPi_simple_mul_simple {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {i j : Fin τ.rank} (hij : π i = j)
    (hji : π j = i) (h : τ.cartan j i = 0) : CommutesPi π (simple τ j * simple τ i) := by
  intro α
  rw [mul_smul, mul_smul, tcW_latPerm_simple_smul hπ, tcW_latPerm_simple_smul hπ, hij, hji,
    ← mul_smul, ← mul_smul, LieType.Steinberg.simple_mul_simple_comm (isFiniteType_cartan τ) h]

theorem tcW_e6Gamma_cartan (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (e6Gamma i) (e6Gamma j) = Tag.E6.cartan i j :=
  TwistTag.cartan_perm .E6 i j

theorem commutesPi_twistGen (gi : ℕ) :
    CommutesPi e6Gamma (tcWordElt Tag.E6 ((tcTwistGens ()).getD gi [])) := by
  rcases gi with _ | _ | _ | _ | gi
  · change CommutesPi e6Gamma (1 * tcLetterElt Tag.E6 1)
    rw [one_mul, tcLetterElt, dif_pos (by decide)]
    exact tcW_commutesPi_simple tcW_e6Gamma_cartan (by decide)
  · change CommutesPi e6Gamma (1 * tcLetterElt Tag.E6 3)
    rw [one_mul, tcLetterElt, dif_pos (by decide)]
    exact tcW_commutesPi_simple tcW_e6Gamma_cartan (by decide)
  · change CommutesPi e6Gamma (1 * tcLetterElt Tag.E6 4 * tcLetterElt Tag.E6 2)
    rw [one_mul, tcLetterElt, dif_pos (by decide), tcLetterElt, dif_pos (by decide)]
    exact tcW_commutesPi_simple_mul_simple tcW_e6Gamma_cartan (by decide) (by decide)
      (by decide)
  · change CommutesPi e6Gamma (1 * tcLetterElt Tag.E6 5 * tcLetterElt Tag.E6 0)
    rw [one_mul, tcLetterElt, dif_pos (by decide), tcLetterElt, dif_pos (by decide)]
    exact tcW_commutesPi_simple_mul_simple tcW_e6Gamma_cartan (by decide) (by decide)
      (by decide)
  · have h : (tcTwistGens ()).getD (gi + 4) [] = [] := by
      simp [tcTwistGens]
    rw [h]
    exact commutesPi_one e6Gamma

theorem e6Gamma_apply (i : Fin Tag.E6.rank) : ((e6Gamma i : Fin Tag.E6.rank) : ℕ) =
    tcGammaArr.getD i 0 := by
  revert i
  decide

theorem e6Gamma_symm (i : Fin Tag.E6.rank) : e6Gamma.symm i = e6Gamma i := by
  revert i
  decide

end CFSG.StandardType.StepTwoToralCert
