module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixSylow
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.Quasithin.Background.SmithB45TorOrbit
public import CFSG.RankThree.PartOne.KE.CTStatement
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.Quasithin.B45Tor

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Words

@[expose] def d4wI : List (Fin TwistTag.D4.tag.rank) := [0, 2, 0, 1, 2, 3]

@[expose] def d4wJ : List (Fin TwistTag.D4.tag.rank) := [0, 2, 1, 3, 2, 1]

@[expose] def d4wH : List (Fin TwistTag.D4.tag.rank) := [1, 2]

@[expose] def d4wW0 : List (Fin TwistTag.D4.tag.rank) := [0, 1, 2, 0, 1, 2, 3, 2, 0, 1, 2, 3]

@[expose] def d4wTw (l : List (Fin TwistTag.D4.tag.rank)) : List (Fin TwistTag.D4.tag.rank) :=
  [2, 0] ++ l.map (![1, 3, 2, 0] : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank) ++ [0, 2]

theorem d4_perm_vec (k : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.perm k =
      (![1, 3, 2, 0] : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank) k := by
  fin_cases k <;> rfl

theorem map_perm_D4 (l : List (Fin TwistTag.D4.tag.rank)) :
    l.map TwistTag.D4.perm =
      l.map (![1, 3, 2, 0] : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank) :=
  List.map_congr_left fun k _ => d4_perm_vec k

theorem conj_pow_succ' {G : Type*} [Group G] (M x : G) (k : ℕ) :
    M ^ (k + 1) * x * (M ^ (k + 1))⁻¹ = M * (M ^ k * x * (M ^ k)⁻¹) * M⁻¹ := by
  rw [pow_succ']
  group

theorem conj_mul_inv_conj {G : Type*} [Group G] (A P x : G) :
    A * P⁻¹ * (P * x * P⁻¹) * (A * P⁻¹)⁻¹ = A * x * A⁻¹ := by
  group

theorem conj_frob_eq {G : Type*} [Group G] (g n x : G) :
    g * n * x * (g * n)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by
  group

end Words

section Lattice


theorem d4_wordProd_eq {l l' : List (Fin TwistTag.D4.tag.rank)}
    (h : lword TwistTag.D4.tag.rank (cartanList TwistTag.D4.tag) (l.map Fin.val) =
      lword TwistTag.D4.tag.rank (cartanList TwistTag.D4.tag) (l'.map Fin.val)) :
    (coxeterSystem TwistTag.D4.tag).wordProd l = (coxeterSystem TwistTag.D4.tag).wordProd l' := by
  have hm : wordMat TwistTag.D4.tag l = wordMat TwistTag.D4.tag l' := by
    rw [← toMat_lword TwistTag.D4.tag (toMat_cartanList TwistTag.D4.tag),
      ← toMat_lword TwistTag.D4.tag (toMat_cartanList TwistTag.D4.tag), h]
  refine ext_single fun i => ?_
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec,
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, hm]

theorem d4_relations :
    (coxeterSystem TwistTag.D4.tag).wordProd (d4wI ++ d4wI) =
        (coxeterSystem TwistTag.D4.tag).wordProd d4wW0 ∧
      (coxeterSystem TwistTag.D4.tag).wordProd (d4wJ ++ d4wJ) =
        (coxeterSystem TwistTag.D4.tag).wordProd d4wW0 ∧
      (coxeterSystem TwistTag.D4.tag).wordProd (d4wI ++ d4wJ ++ d4wI.reverse ++ d4wJ.reverse) =
        (coxeterSystem TwistTag.D4.tag).wordProd d4wW0 ∧
      (coxeterSystem TwistTag.D4.tag).wordProd (d4wH ++ d4wI ++ d4wH.reverse) =
        (coxeterSystem TwistTag.D4.tag).wordProd d4wJ ∧
      (coxeterSystem TwistTag.D4.tag).wordProd (d4wH ++ d4wJ ++ d4wH.reverse) =
        (coxeterSystem TwistTag.D4.tag).wordProd (d4wI ++ d4wJ) ∧
      (coxeterSystem TwistTag.D4.tag).wordProd (d4wW0 ++ d4wW0) =
        (coxeterSystem TwistTag.D4.tag).wordProd [] :=
  ⟨d4_wordProd_eq (by decide +kernel), d4_wordProd_eq (by decide +kernel),
    d4_wordProd_eq (by decide +kernel), d4_wordProd_eq (by decide +kernel),
    d4_wordProd_eq (by decide +kernel), d4_wordProd_eq (by decide +kernel)⟩

theorem d4_twist_fixed {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (l : List (Fin TwistTag.D4.tag.rank))
    (hl : l = d4wI ∨ l = d4wJ ∨ l = d4wH ∨ l = d4wW0) :
    (coxeterSystem TwistTag.D4.tag).wordProd (d4wTw^[threeSixExp ε] l) =
      (coxeterSystem TwistTag.D4.tag).wordProd l := by
  rcases hε with rfl | rfl <;> rcases hl with rfl | rfl | rfl | rfl <;>
    exact d4_wordProd_eq (by decide +kernel)

theorem d4_W0_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd d4wW0 • v = -v := by
  have h : wordMat TwistTag.D4.tag d4wW0 =
      toMat TwistTag.D4.tag.rank [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] :=
    wordMat_eq_toMat TwistTag.D4.tag _ (by decide +kernel)
  have h1 : toMat TwistTag.D4.tag.rank
      [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, h, h1, Matrix.neg_mulVec,
    Matrix.one_mulVec]

end Lattice

section LiftsBasic


variable (Ω : Type) [Field Ω]

@[expose] def d4n (l : List (Fin TwistTag.D4.tag.rank)) : ModGL TwistTag.D4.tag Ω :=
  (l.map fun i => weylElt TwistTag.D4.tag Ω i 1).prod

variable {Ω}

theorem d4n_append (l l' : List (Fin TwistTag.D4.tag.rank)) :
    d4n Ω (l ++ l') = d4n Ω l * d4n Ω l' := by
  rw [d4n, d4n, d4n, List.map_append, List.prod_append]

theorem d4n_cons (i : Fin TwistTag.D4.tag.rank) (l : List (Fin TwistTag.D4.tag.rank)) :
    d4n Ω (i :: l) = weylElt TwistTag.D4.tag Ω i 1 * d4n Ω l := by
  rw [d4n, d4n, List.map_cons, List.prod_cons]

theorem d4n_mem_adjointGroup (l : List (Fin TwistTag.D4.tag.rank)) :
    d4n Ω l ∈ adjointGroup TwistTag.D4.tag Ω := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_adjointGroup i 1

variable [CharP Ω 2]

theorem d4n_eq_canonicalRep (l : List (Fin TwistTag.D4.tag.rank)) :
    d4n Ω l = canonicalRep (coxeterSystem TwistTag.D4.tag) Ω
      ((coxeterSystem TwistTag.D4.tag).wordProd l) :=
  (EvenF4QPlus.canonicalRep_wordProd_of_charTwo l).symm

theorem d4n_eq_of_wordProd_eq {l l' : List (Fin TwistTag.D4.tag.rank)}
    (h : (coxeterSystem TwistTag.D4.tag).wordProd l = (coxeterSystem TwistTag.D4.tag).wordProd l') :
    d4n Ω l = d4n Ω l' := by
  rw [d4n_eq_canonicalRep, d4n_eq_canonicalRep, h]

theorem weylElt_inv_of_charTwo (i : Fin TwistTag.D4.tag.rank) :
    (weylElt TwistTag.D4.tag Ω i 1)⁻¹ = weylElt TwistTag.D4.tag Ω i 1 := by
  have h := weylElt_one_mul_self TwistTag.D4.tag Ω i
  rw [show (-1 : Ωˣ) = 1 from Units.ext (CharTwo.neg_eq (1 : Ω)), torusElt_one] at h
  exact inv_eq_of_mul_eq_one_right h

theorem d4n_reverse (l : List (Fin TwistTag.D4.tag.rank)) :
    d4n Ω l.reverse = (d4n Ω l)⁻¹ := by
  rw [d4n, d4n, List.prod_inv_reverse, List.map_map, List.map_reverse]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  exact (weylElt_inv_of_charTwo i).symm

omit [CharP Ω 2] in
theorem canonicalRep_conj_rootDiagUnit_eq (w : WeylGroup TwistTag.D4.tag)
    (b : Fin TwistTag.D4.tag.rank → Ωˣ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) Ω w * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) Ω w)⁻¹ =
      rootDiagUnit TwistTag.D4.tag
        (fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ))) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ b w).2 fun v => ?_).symm
  conv_rhs => rw [← inv_smul_smul w v]
  set u := w • v
  conv_rhs => rw [pi_eq_sum_univ u]
  rw [Finset.smul_sum, rootChar_sum, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm, rootChar_zsmul]

theorem d4n_conj_mem_torusGroup (l : List (Fin TwistTag.D4.tag.rank))
    {x : ModGL TwistTag.D4.tag Ω} (hx : x ∈ torusGroup TwistTag.D4.tag Ω) [IsAlgClosed Ω] :
    d4n Ω l * x * (d4n Ω l)⁻¹ ∈ torusGroup TwistTag.D4.tag Ω := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [d4n_eq_canonicalRep, canonicalRep_conj_rootDiagUnit_eq]
  exact rootDiagUnit_mem_torusGroup _

end LiftsBasic

section LiftsTwist


variable {Ω : Type} [Field Ω]

theorem entrywise_d4n (F : Ω →+* Ω) (l : List (Fin TwistTag.D4.tag.rank)) :
    Units.map (entrywiseHom F) (d4n Ω l) = d4n Ω l := by
  rw [d4n, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul,
    units_map_entrywiseHom_xUnit, units_map_entrywiseHom_yUnit]
  simp

theorem diagramMap_mul_d4n (l : List (Fin TwistTag.D4.tag.rank)) :
    diagramMap TwistTag.D4 Ω * d4n Ω l =
      d4n Ω (l.map TwistTag.D4.perm) * diagramMap TwistTag.D4 Ω := by
  induction l with
  | nil =>
    show diagramMap TwistTag.D4 Ω * 1 = 1 * diagramMap TwistTag.D4 Ω
    rw [mul_one, one_mul]
  | cons i l ih =>
    calc diagramMap TwistTag.D4 Ω * d4n Ω (i :: l) =
        (diagramMap TwistTag.D4 Ω * weylElt TwistTag.D4.tag Ω i 1) * d4n Ω l := by
          rw [d4n_cons, mul_assoc]
      _ = weylElt TwistTag.D4.tag Ω (TwistTag.D4.perm i) 1 *
          (diagramMap TwistTag.D4 Ω * d4n Ω l) := by
          rw [diagramMap_mul_weylElt_one, mul_assoc]
      _ = weylElt TwistTag.D4.tag Ω (TwistTag.D4.perm i) 1 * d4n Ω (l.map TwistTag.D4.perm) *
          diagramMap TwistTag.D4 Ω := by rw [ih, mul_assoc]
      _ = d4n Ω ((i :: l).map TwistTag.D4.perm) * diagramMap TwistTag.D4 Ω := by
          rw [← d4n_cons]
          rfl

variable [CharP Ω 2]

theorem trialityM_conj_d4n (l : List (Fin TwistTag.D4.tag.rank)) :
    trialityM Ω * d4n Ω l * (trialityM Ω)⁻¹ = d4n Ω (d4wTw l) := by
  have hn : trialityTwistN Ω = d4n Ω [2, 0] := by simp [d4n]
  have hn' : (trialityTwistN Ω)⁻¹ = d4n Ω [0, 2] := by
    rw [hn, ← d4n_reverse]
    rfl
  calc trialityM Ω * d4n Ω l * (trialityM Ω)⁻¹ =
      trialityTwistN Ω * (diagramMap TwistTag.D4 Ω * d4n Ω l) *
        (diagramMap TwistTag.D4 Ω)⁻¹ * (trialityTwistN Ω)⁻¹ := by
        simp only [trialityM, mul_inv_rev]
        group
    _ = trialityTwistN Ω * d4n Ω (l.map TwistTag.D4.perm) * (trialityTwistN Ω)⁻¹ := by
        rw [diagramMap_mul_d4n]
        group
    _ = d4n Ω (d4wTw l) := by rw [hn', hn, d4wTw, d4n_append, d4n_append, map_perm_D4]

theorem threeSixFrob_d4n (F : Ω →+* Ω) (ε : ℤ) (l : List (Fin TwistTag.D4.tag.rank)) :
    threeSixFrob Ω F ε (d4n Ω l) = d4n Ω (d4wTw^[threeSixExp ε] l) := by
  have hk : ∀ (k : ℕ) (l : List (Fin TwistTag.D4.tag.rank)),
      trialityM Ω ^ k * d4n Ω l * (trialityM Ω ^ k)⁻¹ = d4n Ω (d4wTw^[k] l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
      intro l
      rw [conj_pow_succ', ih, trialityM_conj_d4n, Function.iterate_succ_apply']
  rw [threeSixFrob_apply, trialityFrob_apply, entrywise_d4n, ← hk]
  exact conj_mul_inv_conj _ _ _

theorem threeSixFrob_d4n_eq (F : Ω →+* Ω) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {l : List (Fin TwistTag.D4.tag.rank)} (hl : l = d4wI ∨ l = d4wJ ∨ l = d4wH ∨ l = d4wW0) :
    threeSixFrob Ω F ε (d4n Ω l) = d4n Ω l := by
  rw [threeSixFrob_d4n]
  exact d4n_eq_of_wordProd_eq (d4_twist_fixed hε l hl)

theorem d4n_W0_conj_torus {x : ModGL TwistTag.D4.tag Ω} (hx : x ∈ torusGroup TwistTag.D4.tag Ω) :
    d4n Ω d4wW0 * x * (d4n Ω d4wW0)⁻¹ = x⁻¹ := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [d4n_eq_canonicalRep, rootDiagUnit_inv]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff b⁻¹ b _).2 fun v => ?_).symm
  rw [d4_W0_smul, rootChar, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.inv_apply, Pi.neg_apply, zpow_neg, inv_zpow, inv_inv]

end LiftsTwist

section Plane


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hf hK hσ in
theorem exists_threeSix_q8 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) :
    ∃ (R : Subgroup C₀) (i j h : C₀),
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ (∀ r ∈ R, r ^ p = 1) ∧ Nat.card R = p ^ 2 ∧
      IsQ8Data R i j h ∧ i * i * (i * i) = 1 ∧
      ∀ x : C₀, orderOf x = p → ∃ c : C₀, c * x * c⁻¹ ∈ R := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := f * 3)
    (by omega) (by rw [hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels Nat.prime_two hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨hTcι, -, hpart⟩ := hall g hgG hFg
  obtain ⟨-, hconjT, -, hcardTp, -⟩ := hpart p hp hp3 hpd
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group 2
    f Nat.prime_two hf K hK Ω 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
    Fr hFr
  set ι := threeSixEmb K Ω σ with hιdef
  have hιinj : Function.Injective ι :=
    (baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K Ω)).comp Subtype.val_injective
  have hrange : ι.range = adjointGroup TwistTag.D4.tag Ω ⊓
      (trialityFrob Ω Fr).eqLocus (MonoidHom.id _) := by
    rw [hιdef, threeSixEmb, MonoidHom.range_comp, Subgroup.range_subtype]
    refine SetLike.coe_injective ?_
    rw [← hfix]
    ext x
    simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
    rfl
  have hlift : ∀ x ∈ adjointGroup TwistTag.D4.tag Ω, threeSixFrob Ω Fr ε x = x →
      ∃ c : C₀, ι c = g * x * g⁻¹ := by
    intro x hx hFx
    have hmem : g * x * g⁻¹ ∈ ι.range := by
      rw [hrange]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG hx) (inv_mem hgG), ?_⟩
      change trialityFrob Ω Fr (g * x * g⁻¹) = g * x * g⁻¹
      rw [map_mul, map_mul, map_inv, hFg, conj_frob_eq g _ (trialityFrob Ω Fr x),
        ← threeSixFrob_apply, hFx]
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  have hfixed : ∀ l, (l = d4wI ∨ l = d4wJ ∨ l = d4wH ∨ l = d4wW0) →
      threeSixFrob Ω Fr ε (d4n Ω l) = d4n Ω l := fun l hl => threeSixFrob_d4n_eq Fr hε hl
  obtain ⟨cI, hcI⟩ := hlift _ (d4n_mem_adjointGroup d4wI) (hfixed _ (Or.inl rfl))
  obtain ⟨cJ, hcJ⟩ := hlift _ (d4n_mem_adjointGroup d4wJ) (hfixed _ (Or.inr (Or.inl rfl)))
  obtain ⟨cH, hcH⟩ := hlift _ (d4n_mem_adjointGroup d4wH) (hfixed _ (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨cW, hcW⟩ := hlift _ (d4n_mem_adjointGroup d4wW0)
    (hfixed _ (Or.inr (Or.inr (Or.inr rfl))))
  set R := threeSixFixedTorsion K Ω σ Fr ε p g with hRdef
  have hmemR : ∀ r : C₀, r ∈ R ↔ ∃ u ∈ threeSixTorsion Ω Fr ε p, ι r = g * u * g⁻¹ := by
    intro r
    constructor
    · rintro ⟨u, hu, hur⟩
      exact ⟨u, hu, hur.symm⟩
    · rintro ⟨u, hu, hur⟩
      exact ⟨u, hu, hur.symm⟩
  have hHcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag Ω).1
  have hnorm : ∀ l, (l = d4wI ∨ l = d4wJ ∨ l = d4wH ∨ l = d4wW0) →
      ∀ u ∈ threeSixTorsion Ω Fr ε p,
        d4n Ω l * u * (d4n Ω l)⁻¹ ∈ threeSixTorsion Ω Fr ε p ∧
          (d4n Ω l)⁻¹ * u * d4n Ω l ∈ threeSixTorsion Ω Fr ε p := by
    intro l hl u hu
    obtain ⟨⟨huH, huF⟩, hup⟩ := hu
    have hF := hfixed l hl
    have hF' : threeSixFrob Ω Fr ε (d4n Ω l)⁻¹ = (d4n Ω l)⁻¹ := by rw [map_inv, hF]
    have huF' : threeSixFrob Ω Fr ε u = u := huF
    refine ⟨⟨⟨d4n_conj_mem_torusGroup l huH, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · change threeSixFrob Ω Fr ε (d4n Ω l * u * (d4n Ω l)⁻¹) = d4n Ω l * u * (d4n Ω l)⁻¹
      rw [map_mul, map_mul, hF, huF', hF']
    · rw [conj_pow, hup, mul_one, mul_inv_cancel]
    · have := d4n_conj_mem_torusGroup l.reverse huH
      rwa [d4n_reverse, inv_inv] at this
    · change threeSixFrob Ω Fr ε ((d4n Ω l)⁻¹ * u * d4n Ω l) = (d4n Ω l)⁻¹ * u * d4n Ω l
      rw [map_mul, map_mul, hF, huF', hF']
    · have : (d4n Ω l)⁻¹ * u * d4n Ω l = (d4n Ω l)⁻¹ * u * ((d4n Ω l)⁻¹)⁻¹ := by rw [inv_inv]
      rw [this, conj_pow, hup, mul_one, mul_inv_cancel]
  have hnormR : ∀ {c : C₀} {l : List (Fin TwistTag.D4.tag.rank)},
      (l = d4wI ∨ l = d4wJ ∨ l = d4wH ∨ l = d4wW0) → ι c = g * d4n Ω l * g⁻¹ →
      c ∈ Subgroup.normalizer (R : Set C₀) := by
    intro c l hl hc
    refine Subgroup.mem_normalizer_iff.2 fun r => ?_
    rw [hmemR, hmemR]
    constructor
    · rintro ⟨u, hu, hur⟩
      refine ⟨d4n Ω l * u * (d4n Ω l)⁻¹, (hnorm l hl u hu).1, ?_⟩
      rw [map_mul, map_mul, map_inv, hc, hur]
      group
    · rintro ⟨u, hu, hur⟩
      refine ⟨(d4n Ω l)⁻¹ * u * d4n Ω l, (hnorm l hl u hu).2, ?_⟩
      have h1 : ι r = (ι c)⁻¹ * ι (c * r * c⁻¹) * ι c := by
        rw [map_mul, map_mul, map_inv]
        group
      rw [h1, hur, hc]
      group
  have hinvW : InvOn R cW := by
    intro r hr
    obtain ⟨u, hu, hur⟩ := (hmemR r).1 hr
    apply hιinj
    rw [map_mul, map_mul, map_inv, map_inv, hcW, hur]
    have h1 := d4n_W0_conj_torus (Ω := Ω) hu.1.1
    calc g * d4n Ω d4wW0 * g⁻¹ * (g * u * g⁻¹) * (g * d4n Ω d4wW0 * g⁻¹)⁻¹ =
        g * (d4n Ω d4wW0 * u * (d4n Ω d4wW0)⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [h1]; group
  obtain ⟨rII, rJJ, rIJ, rHI, rHJ, rWW⟩ := d4_relations
  have hrel : ∀ {a b : C₀} {l l' : List (Fin TwistTag.D4.tag.rank)},
      ι a = g * d4n Ω l * g⁻¹ → ι b = g * d4n Ω l' * g⁻¹ →
      (coxeterSystem TwistTag.D4.tag).wordProd l = (coxeterSystem TwistTag.D4.tag).wordProd l' →
      a = b := by
    intro a b l l' ha hb hll'
    apply hιinj
    rw [ha, hb, d4n_eq_of_wordProd_eq hll']
  have eII : cI * cI = cW := hrel (l := d4wI ++ d4wI) (by rw [map_mul, hcI, d4n_append]; group)
    hcW rII
  have eJJ : cJ * cJ = cW := hrel (l := d4wJ ++ d4wJ) (by rw [map_mul, hcJ, d4n_append]; group)
    hcW rJJ
  have eIJ : ⁅cI, cJ⁆ = cW := by
    refine hrel (l := d4wI ++ d4wJ ++ d4wI.reverse ++ d4wJ.reverse) ?_ hcW rIJ
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcI, hcJ, d4n_append,
      d4n_append, d4n_append, d4n_reverse, d4n_reverse]
    group
  have eHI : cH * cI * cH⁻¹ = cJ := by
    refine hrel (l := d4wH ++ d4wI ++ d4wH.reverse) ?_ hcJ rHI
    rw [map_mul, map_mul, map_inv, hcH, hcI, d4n_append, d4n_append, d4n_reverse]
    group
  have eHJ : cH * cJ * cH⁻¹ = cI * cJ := by
    refine hrel (l := d4wH ++ d4wJ ++ d4wH.reverse) ?_
      (by rw [map_mul, hcI, hcJ, d4n_append]; group) rHJ
    rw [map_mul, map_mul, map_inv, hcH, hcJ, d4n_append, d4n_append, d4n_reverse]
    group
  have eWW : cW * cW = 1 := by
    apply hιinj
    have h1 := d4n_eq_of_wordProd_eq (Ω := Ω) rWW
    rw [d4n_append] at h1
    have h2 : d4n Ω ([] : List (Fin TwistTag.D4.tag.rank)) = 1 := rfl
    rw [map_mul, hcW, map_one]
    calc g * d4n Ω d4wW0 * g⁻¹ * (g * d4n Ω d4wW0 * g⁻¹) =
        g * (d4n Ω d4wW0 * d4n Ω d4wW0) * g⁻¹ := by group
      _ = 1 := by rw [h1, h2]; group
  refine ⟨R, cI, cJ, cH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a ha b hb
    obtain ⟨u, hu, hua⟩ := (hmemR a).1 ha
    obtain ⟨u', hu', hub⟩ := (hmemR b).1 hb
    apply hιinj
    rw [map_mul, map_mul, hua, hub]
    have hc := hHcomm u hu.1.1 u' hu'.1.1
    calc g * u * g⁻¹ * (g * u' * g⁻¹) = g * (u * u') * g⁻¹ := by group
      _ = g * (u' * u) * g⁻¹ := by rw [hc]
      _ = g * u' * g⁻¹ * (g * u * g⁻¹) := by group
  ·
    intro r hr
    obtain ⟨u, hu, hur⟩ := (hmemR r).1 hr
    apply hιinj
    rw [map_pow, hur, conj_pow, hu.2, map_one, mul_one, mul_inv_cancel]
  ·
    have hle : (threeSixTorsion Ω Fr ε p).map (MulAut.conj g).toMonoidHom ≤ ι.range :=
      (Subgroup.map_mono (threeSixTorsion_le Fr ε p)).trans hTcι
    rw [← hcardTp, hRdef, threeSixFixedTorsion, ← Subgroup.card_map_of_injective hιinj,
      Subgroup.map_comap_eq_self hle, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  · exact ⟨hnormR (Or.inl rfl) hcI, hnormR (Or.inr (Or.inl rfl)) hcJ,
      hnormR (Or.inr (Or.inr (Or.inl rfl))) hcH, by rw [eIJ]; exact hinvW,
      by rw [eII]; exact hinvW, by rw [eJJ]; exact hinvW, by rw [eHI]; exact AgreeOn.refl _,
      by rw [eHJ]; exact AgreeOn.refl _⟩
  · rw [eII, eWW]
  ·
    intro x hx
    have : Fact p.Prime := ⟨hp⟩
    have hP : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconjT _ hP
    have hcx : c * x * c⁻¹ ∈ threeSixFixedTorus K Ω σ Fr ε g := hc ⟨x, Subgroup.mem_zpowers x, rfl⟩
    obtain ⟨u, hu, hux⟩ := hcx
    refine ⟨c, (hmemR _).2 ⟨u, ⟨hu, ?_⟩, hux.symm⟩⟩
    have h1 : g * u ^ p * g⁻¹ = 1 := by
      have := congrArg ι (show (c * x * c⁻¹) ^ p = 1 by
        rw [conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel])
      rw [map_pow, map_one, ← hux] at this
      simpa [conj_pow] using this
    calc u ^ p = g⁻¹ * (g * u ^ p * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end Plane

end CFSG.Quasithin.B45Tor
