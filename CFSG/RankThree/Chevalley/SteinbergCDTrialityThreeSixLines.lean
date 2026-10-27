module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLines
public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KCUnitaryPlane
open scoped Matrix

theorem mem_of_trialityColMat_det {S : AddSubgroup (Fin Tag.D4.rank → ℤ)}
    {x₁ x₂ x₃ x₄ : Fin Tag.D4.rank → ℤ} (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) (h₃ : x₃ ∈ S) (h₄ : x₄ ∈ S)
    (hdet : (trialityColMat x₁ x₂ x₃ x₄).det = -1) (y : Fin Tag.D4.rank → ℤ) : y ∈ S := by
  have hcol : ∀ k, (fun r => trialityColMat x₁ x₂ x₃ x₄ r k) ∈ S := by
    intro k
    fin_cases k
    exacts [h₁, h₂, h₃, h₄]
  have hmul : ∀ z, trialityColMat x₁ x₂ x₃ x₄ *ᵥ z ∈ S := fun z => by
    have hz : trialityColMat x₁ x₂ x₃ x₄ *ᵥ z =
        ∑ k, z k • fun r => trialityColMat x₁ x₂ x₃ x₄ r k := by
      funext r
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hz]
    exact S.sum_mem fun k _ => S.zsmul_mem (hcol k) _
  have hy : y = trialityColMat x₁ x₂ x₃ x₄ *ᵥ (-((trialityColMat x₁ x₂ x₃ x₄).adjugate *ᵥ y)) := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, neg_one_smul,
      Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  rw [hy]
  exact hmul _

section Kernel

variable {L : Type} [Field L]

@[expose] def threeSixCharKer (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    AddSubgroup (Fin TwistTag.D4.tag.rank → ℤ) where
  carrier := {v | rootChar a v = 1}
  add_mem' := fun {u v} hu hv => by
    have hu' : rootChar a u = 1 := hu
    have hv' : rootChar a v = 1 := hv
    exact (rootChar_add a u v).trans (by rw [hu', hv', one_mul])
  zero_mem' := rootChar_zero a
  neg_mem' := fun {v} hv => by
    have hv' : rootChar a v = 1 := hv
    exact (rootChar_neg' a v).trans (by rw [hv', inv_one])

abbrev threeSixU (i : Fin 4) : Fin TwistTag.D4.tag.rank → ℤ := trialityU i

theorem mem_trialitySigma_iff {j : Fin 4} {β : Fin TwistTag.D4.tag.rank → ℤ} :
    β ∈ trialitySigma j ↔ ∃ k < 3, β = ((twelveW ^ 4) ^ k) *ᵥ threeSixU j ∨
      β = -(((twelveW ^ 4) ^ k) *ᵥ threeSixU j) :=
  Iff.rfl

theorem threeSixU_mem (i : Fin 4) : threeSixU i ∈ trialitySigma i :=
  mem_trialitySigma_iff.2 ⟨0, by norm_num, Or.inl (by rw [pow_zero, Matrix.one_mulVec])⟩

theorem rootChar_pow_mulVec_eq_one {q : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hfix : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q)
    {x : Fin TwistTag.D4.tag.rank → ℤ} (hx : rootChar a x = 1) (k : ℕ) :
    rootChar a (((twelveW ^ 4) ^ k) *ᵥ x) = 1 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have hA : (twelveW ^ 4) *ᵥ (((twelveW ^ 4) ^ k) *ᵥ x) =
        ε • ((ε • twelveW ^ 4) *ᵥ (((twelveW ^ 4) ^ k) *ᵥ x)) := by
      rw [Matrix.smul_mulVec, smul_smul, hε2, one_smul]
    rw [hA, rootChar_zsmul, hfix, ih, one_pow, one_zpow]

theorem rootChar_eq_one_of_mem_trialitySigma {q : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hfix : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q)
    {j : Fin 4} {β : Fin TwistTag.D4.tag.rank → ℤ} (hβ : β ∈ trialitySigma j)
    (hβ1 : rootChar a β = 1) {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ trialitySigma j) :
    rootChar a α = 1 := by
  have hA3 : (twelveW ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact trialityCoxeter_pow_twelve
  have hu : rootChar a (threeSixU j) = 1 := by
    obtain ⟨k, hk, h⟩ := mem_trialitySigma_iff.1 hβ
    have hk' : (twelveW ^ 4) ^ (3 - k) * (twelveW ^ 4) ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hk.le, hA3]
    have hβ' : rootChar a (((twelveW ^ 4) ^ k) *ᵥ threeSixU j) = 1 := by
      rcases h with h | h
      · rwa [h] at hβ1
      · rw [h, rootChar_neg'] at hβ1
        exact inv_eq_one.1 hβ1
    have := rootChar_pow_mulVec_eq_one hε hfix hβ' (3 - k)
    rwa [Matrix.mulVec_mulVec, hk', Matrix.one_mulVec] at this
  obtain ⟨m, -, h⟩ := mem_trialitySigma_iff.1 hα
  rcases h with h | h
  · rw [h]
    exact rootChar_pow_mulVec_eq_one hε hfix hu m
  · rw [h, rootChar_neg', rootChar_pow_mulVec_eq_one hε hfix hu m, inv_one]

theorem eq_one_of_rootChar_eq_one_of_ne {q : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hfix : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q)
    {i j : Fin 4} (hij : i ≠ j) {u v : Fin TwistTag.D4.tag.rank → ℤ} (hu : u ∈ trialitySigma i)
    (hv : v ∈ trialitySigma j) (hu1 : rootChar a u = 1) (hv1 : rootChar a v = 1) : a = 1 := by
  have hur : IsRoot Tag.D4 u := (isRootComponent_trialitySigma i).isRoot u hu
  have hvr : IsRoot Tag.D4 v := (isRootComponent_trialitySigma j).isRoot v hv
  have hnot : ¬∃ k, u ∈ trialitySigma k ∧ v ∈ trialitySigma k := by
    rintro ⟨k, huk, hvk⟩
    have hik : i = k := by
      by_contra hik
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hik) hu huk
    have hjk : j = k := by
      by_contra hjk
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hjk) hv hvk
    exact hij (hik.trans hjk.symm)
  have hdet := (trialityColMat_det hε hur hvr).2 hnot
  have hwu : rootChar a ((ε • twelveW ^ 4) *ᵥ u) = 1 := by rw [hfix, hu1, one_pow]
  have hwv : rootChar a ((ε • twelveW ^ 4) *ᵥ v) = 1 := by rw [hfix, hv1, one_pow]
  have hall := mem_of_trialityColMat_det (S := threeSixCharKer a) (x₁ := u)
    (x₂ := (ε • trialityA) *ᵥ u) (x₃ := v) (x₄ := (ε • trialityA) *ᵥ v) hu1 hwu hv1 hwv hdet
  funext k
  have h1 : rootChar a (Pi.single k 1) = 1 := hall _
  rw [rootChar_single] at h1
  exact h1

end Kernel

section Lines

variable {L : Type} [Field L]

@[expose] def survivingRoots (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {α | IsRoot TwistTag.D4.tag α ∧ rootChar a α = 1}

variable (L) in
@[expose] def threeSixEval (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (Fin TwistTag.D4.tag.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a v
  map_one' := by simp [rootChar]
  map_mul' a b := rootChar_mul_tuple a b v

variable (L) in
@[expose] def sigmaKernel (i : Fin 4) : Subgroup (Fin TwistTag.D4.tag.rank → Lˣ) where
  carrier := {a | ∀ α : Fin TwistTag.D4.tag.rank → ℤ, α ∈ trialitySigma i → rootChar a α = 1}
  mul_mem' := fun {a b} ha hb α hα => by rw [rootChar_mul_tuple, ha α hα, hb α hα, one_mul]
  one_mem' := fun α _ => by simp [rootChar]
  inv_mem' := fun {a} ha α hα => by rw [rootChar_inv_apply, ha α hα, inv_one]

variable (L) in
@[expose] def threeSixLine
    (F : L →+* L) (ε : ℤ) (p : ℕ) (i : Fin 4) :
    Subgroup (ModGL TwistTag.D4.tag L) :=
  threeSixTorsion L F ε p ⊓ (sigmaKernel L i).map (rootDiagUnitHom TwistTag.D4.tag L)

theorem threeSixEval_apply (v : Fin TwistTag.D4.tag.rank → ℤ) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    threeSixEval L v a = rootChar a v :=
  rfl

theorem ncard_lines_of_le {G : Type*} [Group G] {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card P = p ^ 2) (hpow : ∀ x ∈ P, x ^ p = 1) :
    {M : Subgroup G | M ≤ P ∧ Nat.card M = p}.ncard = p + 1 := by
  classical
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have : Fintype P := Fintype.ofFinite P
  have hP : IsPlane p P := ⟨hp, hcard, fun x => Subtype.ext (hpow x x.2)⟩
  have hlines := hP.card_lines
  have himage : {M : Subgroup G | M ≤ P ∧ Nat.card M = p} =
      (fun X : Subgroup P => X.map P.subtype) '' ((lines p P : Finset (Subgroup P)) : Set _) := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, mem_lines]
    constructor
    · rintro ⟨hMP, hM⟩
      refine ⟨M.subgroupOf P, ?_, ?_⟩
      · rw [← hM, ← Subgroup.card_map_of_injective P.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_of_le_left hMP]
      · rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hMP]
    · rintro ⟨X, hX, rfl⟩
      exact ⟨Subgroup.map_subtype_le X,
        by rw [Subgroup.card_map_of_injective P.subtype_injective, hX]⟩
  rw [himage, Set.ncard_image_of_injective _ (Subgroup.map_injective P.subtype_injective),
    Set.ncard_coe_finset, hlines]

theorem threeSix_lines
    [IsAlgClosed L] (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    (hqL : (q : L) = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d) :
    IsElementaryAbelian p (threeSixTorsion L F ε p) ∧
    Nat.card (threeSixTorsion L F ε p) = p ^ 2 ∧
    (∀ i, Nat.card (threeSixLine L F ε p i) = p) ∧
    (Pairwise fun i j => threeSixLine L F ε p i ≠ threeSixLine L F ε p j) ∧
    {M : Subgroup (ModGL TwistTag.D4.tag L) | M ≤ threeSixTorsion L F ε p ∧ Nat.card M = p ∧
      ∀ i, M ≠ threeSixLine L F ε p i}.ncard = p - 3 ∧
    ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion L F ε p →
      rootDiagUnit TwistTag.D4.tag a ≠ 1 →
      (∀ i, rootDiagUnit TwistTag.D4.tag a ∈ threeSixLine L F ε p i →
        survivingRoots a = trialitySigma i) ∧
      ((∀ i, rootDiagUnit TwistTag.D4.tag a ∉ threeSixLine L F ε p i) → survivingRoots a = ∅) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdL : (d : L) = 1 := by
    have h := congrArg (Int.cast : ℤ → L) hd
    push_cast at h
    rw [h, hqL]
    ring
  have hpL : (p : L) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hpd
    have h1 : (d : L) = 0 := by rw [hk, Nat.cast_mul, h0, zero_mul]
    rw [hdL] at h1
    exact one_ne_zero h1
  have : NeZero (p : L) := ⟨hpL⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := p)
  have hμ : Nat.card (rootsOfUnity p L) = p := hζ.card_rootsOfUnity
  have hcardTp : Nat.card (threeSixTorsion L F ε p) = p ^ 2 := by
    rw [threeSixTorsion_eq_map F hF hε hd hpd,
      Subgroup.card_map_of_injective (injective_threeSixParam _ _),
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hμ, sq]
  have hHcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag L).1
  have hEA : IsElementaryAbelian p (threeSixTorsion L F ε p) :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hHcomm _ x.2.1.1 _ y.2.1.1)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using x.2.2) }
  have hfixOf : ∀ a, rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion L F ε p →
      (∀ v, rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ q) ∧ a ^ p = 1 := by
    intro a ha
    refine ⟨(rootDiagUnit_mem_threeSixTorus_iff F hF hε a).1 ha.1, rootDiagUnit_injective ?_⟩
    rw [rootDiagUnit_one]
    exact (map_pow (rootDiagUnitHom TwistTag.D4.tag L) a p).trans ha.2
  have hDinj : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) :=
    fun a b h => rootDiagUnit_injective h
  have hTpD : threeSixTorsion L F ε p ≤ (rootDiagUnitHom TwistTag.D4.tag L).range := by
    intro h hh
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh.1.1
    exact ⟨a, rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ Pp : Subgroup (Fin TwistTag.D4.tag.rank → Lˣ),
      Pp = (threeSixTorsion L F ε p).comap (rootDiagUnitHom TwistTag.D4.tag L) := ⟨_, rfl⟩
  have hPpmap : Pp.map (rootDiagUnitHom TwistTag.D4.tag L) = threeSixTorsion L F ε p := by
    rw [hPp]
    exact Subgroup.map_comap_eq_self hTpD
  have hcardPp : Nat.card Pp = p ^ 2 := by
    rw [← hcardTp, ← hPpmap, Subgroup.card_map_of_injective hDinj]
  have : Finite Pp := Nat.finite_of_card_ne_zero (by rw [hcardPp]; exact pow_ne_zero _ hp.ne_zero)
  have hmemPp : ∀ a, a ∈ Pp ↔ rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion L F ε p := by
    intro a
    rw [hPp]
    rfl
  have hLine : ∀ i, threeSixLine L F ε p i =
      (Pp ⊓ sigmaKernel L i).map (rootDiagUnitHom TwistTag.D4.tag L) := by
    intro i
    rw [Subgroup.map_inf_eq _ _ _ hDinj, hPpmap]
    rfl
  have hK : ∀ i, Pp ⊓ sigmaKernel L i = Pp ⊓ (threeSixEval L (threeSixU i)).ker := by
    intro i
    ext a
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, threeSixEval_apply]
    constructor
    · rintro ⟨ha, hk⟩
      exact ⟨ha, hk _ (threeSixU_mem i)⟩
    · rintro ⟨ha, hk⟩
      exact ⟨ha, fun α hα => rootChar_eq_one_of_mem_trialitySigma hε
        (hfixOf a ((hmemPp a).1 ha)).1 (threeSixU_mem i) hk hα⟩
  have hge : ∀ i, p ≤ Nat.card ↥(Pp ⊓ sigmaKernel L i) := by
    intro i
    rw [hK i]
    obtain ⟨φ, hφ⟩ : ∃ φ : Pp →* Lˣ, φ = (threeSixEval L (threeSixU i)).comp Pp.subtype :=
      ⟨_, rfl⟩
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hcardPp] at h1
    have hrange : φ.range ≤ rootsOfUnity p L := by
      rintro _ ⟨x, rfl⟩
      rw [mem_rootsOfUnity, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, threeSixEval_apply,
        ← rootChar_pow_tuple, (hfixOf x ((hmemPp x).1 x.2)).2]
      simp [rootChar]
    have hle : Nat.card φ.range ≤ p := hμ ▸ Subgroup.card_le_of_le hrange
    have hker : Nat.card φ.ker = Nat.card ↥(Pp ⊓ (threeSixEval L (threeSixU i)).ker) := by
      rw [← Subgroup.card_map_of_injective Pp.subtype_injective, hφ, ← MonoidHom.comap_ker,
        ← Subgroup.subgroupOf, Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [← hker]
    have h2 : p * p ≤ Nat.card φ.ker * p := by
      calc p * p = Nat.card φ.ker * Nat.card φ.range := by rw [h1, sq]
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hle
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have hdisj : ∀ i j, i ≠ j → (Pp ⊓ sigmaKernel L i) ⊓ (Pp ⊓ sigmaKernel L j) = ⊥ := by
    intro i j hij
    rw [eq_bot_iff]
    rintro a ⟨⟨ha, hai⟩, -, haj⟩
    exact Subgroup.mem_bot.2 (eq_one_of_rootChar_eq_one_of_ne hε (hfixOf a ((hmemPp a).1 ha)).1
      hij (threeSixU_mem i) (threeSixU_mem j) (hai _ (threeSixU_mem i)) (haj _ (threeSixU_mem j)))
  have hcardK : ∀ i, Nat.card ↥(Pp ⊓ sigmaKernel L i) = p := by
    intro i
    have hdvd : Nat.card ↥(Pp ⊓ sigmaKernel L i) ∣ p ^ 2 :=
      hcardPp ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hgi := hge i
    interval_cases k
    · rw [hk', pow_zero] at hgi
      omega
    · rw [hk', pow_one]
    · exfalso
      have hKi : Pp ⊓ sigmaKernel L i = Pp :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardPp, hk'])
      obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := by
        by_cases hi : i = 0
        · exact ⟨1, by rw [hi]; decide⟩
        · exact ⟨0, fun h => hi h.symm⟩
      have h := hdisj j i hj
      rw [hKi, inf_of_le_left inf_le_left] at h
      have hgj := hge j
      rw [h, Subgroup.card_bot] at hgj
      omega
  have hcardL : ∀ i, Nat.card (threeSixLine L F ε p i) = p := by
    intro i
    rw [hLine i, Subgroup.card_map_of_injective hDinj, hcardK i]
  have hne : Pairwise fun i j => threeSixLine L F ε p i ≠ threeSixLine L F ε p j := by
    intro i j hij heq
    rw [hLine i, hLine j] at heq
    have heq' := Subgroup.map_injective hDinj heq
    have h := hdisj i j hij
    rw [heq', inf_idem] at h
    have hj := hcardK j
    rw [h, Subgroup.card_bot] at hj
    exact hp.one_lt.ne hj
  have hcount : {M : Subgroup (ModGL TwistTag.D4.tag L) | M ≤ threeSixTorsion L F ε p ∧
      Nat.card M = p ∧ ∀ i, M ≠ threeSixLine L F ε p i}.ncard = p - 3 := by
    have hall := ncard_lines_of_le hp hcardTp fun x hx => hx.2
    have hsub : Set.range (threeSixLine L F ε p) ⊆
        {M | M ≤ threeSixTorsion L F ε p ∧ Nat.card M = p} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨inf_le_left, hcardL i⟩
    have hrange : (Set.range (threeSixLine L F ε p)).ncard = 4 := by
      rw [Set.ncard_range_of_injective fun i j h => by
          by_contra hij
          exact hne hij h, Nat.card_eq_fintype_card, Fintype.card_fin]
    have heq : {M : Subgroup (ModGL TwistTag.D4.tag L) | M ≤ threeSixTorsion L F ε p ∧
        Nat.card M = p ∧ ∀ i, M ≠ threeSixLine L F ε p i} =
        {M | M ≤ threeSixTorsion L F ε p ∧ Nat.card M = p} \ Set.range (threeSixLine L F ε p) := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_range, not_exists]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun i h => h3 i h.symm⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun i h => h3 i h.symm⟩
    rw [heq, Set.ncard_sdiff hsub, hall, hrange]
    omega
  refine ⟨hEA, hcardTp, hcardL, hne, hcount, fun a ha ha1 => ?_⟩
  have hfa := (hfixOf a ha).1
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, rootDiagUnit_one])
  have hmemL : ∀ i, rootDiagUnit TwistTag.D4.tag a ∈ threeSixLine L F ε p i ↔
      a ∈ sigmaKernel L i := by
    intro i
    constructor
    · rintro ⟨-, b, hb, hba⟩
      rwa [← rootDiagUnit_injective hba]
    · intro h
      exact ⟨ha, a, h, rfl⟩
  have hroot : ∀ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α →
      ∃ j, α ∈ trialitySigma j := by
    intro α hα
    have h : α ∈ ⋃ j, trialitySigma j := by
      rw [← isRoot_eq_iUnion_trialitySigma]
      exact hα
    exact Set.mem_iUnion.1 h
  refine ⟨fun i hi => ?_, fun hnot => ?_⟩
  · have hai := (hmemL i).1 hi
    ext α
    constructor
    · rintro ⟨hα, hα1⟩
      obtain ⟨j, hj⟩ := hroot α hα
      by_contra hni
      have hij : i ≠ j := fun h => hni (h ▸ hj)
      exact ha1' (eq_one_of_rootChar_eq_one_of_ne hε hfa hij (threeSixU_mem i) hj
        (hai _ (threeSixU_mem i)) hα1)
    · intro hα
      exact ⟨(isRootComponent_trialitySigma i).isRoot α hα, hai α hα⟩
  · ext α
    simp only [survivingRoots, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hα hα1
    obtain ⟨j, hj⟩ := hroot α hα
    apply hnot j
    rw [hmemL j]
    exact fun β hβ => rootChar_eq_one_of_mem_trialitySigma hε hfa hj hα1 hβ

end Lines

end CFSG.RankThree.Chevalley
