module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocks
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneShapes
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.SUFour

public section

namespace CFSG.StandardType.CommonJOmPlusTwo

open CFSG.Assembly CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.OrthBlocks
  CFSG.StandardType.GGQ2Frame.PlaneRaw

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem ggCommonJOmPlusTwo_otau_span (hK : Nat.card K = 2) (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3)) :
    ∀ u ∈ Submodule.span (ZMod 3) {fun i => (f i).toAdd},
      otau (otc_zeta K) m 1 u = 1 ∨
        otau (otc_zeta K) m 1 u = otau (otc_zeta K) m 1 (fun i => (f i).toAdd) ∨
        otau (otc_zeta K) m 1 u = otau (otc_zeta K) m 1 (fun i => (f i).toAdd) ^ 2 := by
  intro u hu
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  rw [← ha]
  have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1 := by decide
  rcases hcases a with rfl | rfl | rfl
  · rw [zero_smul, otau_zero]
    exact Or.inl rfl
  · rw [one_smul]
    exact Or.inr (Or.inl rfl)
  · rw [neg_one_smul]
    have hmul : otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
        otau (otc_zeta K) m 1 (-(fun i => (f i).toAdd)) = 1 := by
      rw [← otau_add]
      simp [otau_zero]
    have hinv : otau (otc_zeta K) m 1 (-(fun i => (f i).toAdd)) =
        (otau (otc_zeta K) m 1 (fun i => (f i).toAdd))⁻¹ :=
      (mul_eq_one_iff_inv_eq.mp hmul).symm
    rw [hinv]
    have hx3 : ∀ x : Multiplicative (ZMod 3), x ^ 3 = 1 := by decide
    have hf3 : (f : Fin m → Multiplicative (ZMod 3)) ^ 3 = 1 := by
      funext i
      rw [Pi.pow_apply]
      exact hx3 (f i)
    have h3 : (otau (otc_zeta K) m 1 (fun i => (f i).toAdd)) ^ 3 = 1 := by
      have h := congrArg (fun x : ↥(omegaQ (K := K) m 1) =>
        (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
        (map_pow (ggCommonJOmPlusTwo_tau hK m) f 3)
      rw [hf3, map_one] at h
      simpa [ggCommonJOmPlusTwo_tau, otau_zero] using h.symm
    have hsq : (otau (otc_zeta K) m 1 (fun i => (f i).toAdd))⁻¹ =
        (otau (otc_zeta K) m 1 (fun i => (f i).toAdd)) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', show 2 + 1 = 3 by norm_num, h3]
    rw [hsq]
    exact Or.inr (Or.inr rfl)

theorem ggCommonJOmPlusTwo_centralizer_span (hK : Nat.card K = 2) (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3)) :
    Subgroup.centralizer
        ({(ggCommonJOmPlusTwo_tau hK m f)} : Set ↥(omegaQ (K := K) m 1)) =
      (Subgroup.centralizer (oTorusSet (otc_zeta K) m 1
        (Submodule.span (ZMod 3) {fun i => (f i).toAdd}))).comap
        (omegaQ (K := K) m 1).subtype := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    obtain ⟨w, hw, rfl⟩ := hg
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    change otau (otc_zeta K) m 1 u * (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
      (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * otau (otc_zeta K) m 1 u
    have hx : otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
        (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
        (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) *
          otau (otc_zeta K) m 1 (fun i => (f i).toAdd) := by
      simpa [ggCommonJOmPlusTwo_tau] using congrArg Subtype.val (h _ (Set.mem_singleton _))
    rcases ggCommonJOmPlusTwo_otau_span hK m f u hu with h1 | h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]; exact hx
    · rw [h1]
      calc
        otau (otc_zeta K) m 1 (fun i => (f i).toAdd) ^ 2 *
            (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
          otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
            (otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
              (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) := by rw [pow_two, mul_assoc]
        _ = otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
            ((x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) *
              otau (otc_zeta K) m 1 (fun i => (f i).toAdd)) := by rw [hx]
        _ = (otau (otc_zeta K) m 1 (fun i => (f i).toAdd) *
              (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)) *
              otau (otc_zeta K) m 1 (fun i => (f i).toAdd) := by rw [mul_assoc]
        _ = ((x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) *
              otau (otc_zeta K) m 1 (fun i => (f i).toAdd)) *
              otau (otc_zeta K) m 1 (fun i => (f i).toAdd) := by rw [hx]
        _ = (x : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) *
              otau (otc_zeta K) m 1 (fun i => (f i).toAdd) ^ 2 := by
          rw [pow_two, mul_assoc]
  · intro hB g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hmem : (ggCommonJOmPlusTwo_tau hK m f : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) ∈
        oTorusSet (otc_zeta K) m 1 (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) :=
      ⟨liftV m 1 (fun i => (f i).toAdd),
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _), rfl⟩
    exact Subtype.ext
      (by simpa only [Subgroup.coe_mul, Subgroup.coe_subtype] using hB _ hmem)


theorem ggCommonJOmPlusTwo_components (hK : Nat.card K = 2) {m : ℕ}
    (f : Fin m → Multiplicative (ZMod 3)) {J : Subgroup ↥(omegaQ (K := K) m 1)}
    (hJ : IsComponentOf J (Subgroup.centralizer
      ({(ggCommonJOmPlusTwo_tau hK m f)} : Set ↥(omegaQ (K := K) m 1)))) :
    ∃ c : PlaneRaw.Code m, PlaneRaw.admissible (.orthogonal 1) c ∧
      PlaneRaw.occurs (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) c ∧
      J = oYcode (otc_zeta K) m 1 c := by
  rw [ggCommonJOmPlusTwo_centralizer_span (K := K) hK m f] at hJ
  exact (orthIsComponentOfCentralizerTorusSetIff_holds (otc_zeta K) m 1 hK
    (otc_zeta_injective K) (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) J).mp hJ


private theorem ggCommonJOmPlusTwo_mem_cent_of_occurs (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3)) (c : PlaneRaw.Code m)
    (hocc : PlaneRaw.occurs (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) c) :
    (fun i => (f i).toAdd) ∈ PlaneRaw.cent (.orthogonal 1) c := by
  cases c with
  | zero S =>
      rw [PlaneRaw.mem_cent_zero]
      intro i hi
      have h := (hocc i).mp hi
      exact h ⟨fun j => (f j).toAdd, Submodule.mem_span_singleton_self _⟩
  | extension e =>
      obtain ⟨he, χ, hχne, hχ, hχzero⟩ := hocc
      rw [PlaneRaw.mem_cent_extension]
      have hsq : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
      intro i hi j hj
      let x : ↥(Submodule.span (ZMod 3) {fun k => (f k).toAdd}) :=
        ⟨fun k => (f k).toAdd, Submodule.mem_span_singleton_self _⟩
      have h1f : (f i).toAdd = e i * χ x := by
        have h := congrArg (fun φ : ↥(Submodule.span (ZMod 3)
            {fun k => (f k).toAdd}) →ₗ[ZMod 3] ZMod 3 => φ x) (hχ i (by simpa using hi))
        simpa only [PlaneRaw.evalRestr, LinearMap.comp_apply, PlaneRaw.coordProj_apply,
          LinearMap.smul_apply, smul_eq_mul, Submodule.coe_subtype] using h
      have h2f : (f j).toAdd = e j * χ x := by
        have h := congrArg (fun φ : ↥(Submodule.span (ZMod 3)
            {fun k => (f k).toAdd}) →ₗ[ZMod 3] ZMod 3 => φ x) (hχ j (by simpa using hj))
        simpa only [PlaneRaw.evalRestr, LinearMap.comp_apply, PlaneRaw.coordProj_apply,
          LinearMap.smul_apply, smul_eq_mul, Submodule.coe_subtype] using h
      calc e i * (f i).toAdd = e i * (e i * χ x) := by rw [h1f]
        _ = (e i * e i) * χ x := by rw [mul_assoc]
        _ = 1 * χ x := by rw [hsq (e i) (by simpa using hi)]
        _ = (e j * e j) * χ x := by rw [hsq (e j) (by simpa using hj)]
        _ = e j * (e j * χ x) := by rw [mul_assoc]
        _ = e j * (f j).toAdd := by rw [h2f]

private theorem ggCommonJOmPlusTwo_ne_zero_of_occurs (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3)) (c : PlaneRaw.Code m)
    (hcentcard : Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c) = 3)
    (hocc : PlaneRaw.occurs (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) c) :
    (fun i => (f i).toAdd) ≠ 0 := by
  intro h0
  have hspan : Submodule.span (ZMod 3) {fun i => (f i).toAdd} = ⊥ := by
    rw [Submodule.span_singleton_eq_bot]
    exact h0
  rw [hspan] at hocc
  cases c with
  | zero S =>
      have hS : S = Finset.univ := by
        ext i
        rw [hocc i]
        simp
      subst hS
      have hbot : PlaneRaw.cent (.orthogonal 1) (.zero (Finset.univ : Finset (Fin m))) = ⊥ := by
        change PlaneRaw.centZero (Finset.univ : Finset (Fin m)) = ⊥
        ext v
        rw [PlaneRaw.mem_centZero, Submodule.mem_bot]
        constructor
        · intro h
          funext i
          exact h i (Finset.mem_univ i)
        · intro h i _
          rw [h]
          rfl
      rw [hbot] at hcentcard
      haveI : Unique ↥(⊥ : Submodule (ZMod 3) (Fin m → ZMod 3)) := Submodule.uniqueBot
      rw [Nat.card_unique] at hcentcard
      omega
  | extension e =>
      obtain ⟨he, χ, hχne, -⟩ := hocc
      apply hχne
      ext y
      have hy : y = 0 := Subsingleton.elim y 0
      rw [hy]
      simpa using map_zero χ

private theorem ggCommonJOmPlusTwo_card_inf_cent (hK : Nat.card K = 2) (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3)) (c : PlaneRaw.Code m)
    (hc : PlaneRaw.admissible (.orthogonal 1) c) :
    Nat.card ↥((ggCommonJOmPlusTwo_tau hK m).range ⊓
        Subgroup.centralizer
          (oYcode (otc_zeta K) m 1 c : Set ↥(omegaQ (K := K) m 1))) =
      Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c) := by
  let τ := ggCommonJOmPlusTwo_tau hK m
  let C : Subgroup ↥(omegaQ (K := K) m 1) :=
    Subgroup.centralizer (oYcode (otc_zeta K) m 1 c : Set ↥(omegaQ (K := K) m 1))
  have hτinj : Function.Injective τ := ggCommonJOmPlusTwo_tau_injective hK m
  have hI : Nat.card ↥(τ.range ⊓ C) = Nat.card ↥((τ.range ⊓ C).comap τ) := by
    rw [← Subgroup.card_map_of_injective (f := τ) hτinj,
      Subgroup.map_comap_eq_self (f := τ) inf_le_left]
  have hcomap : (τ.range ⊓ C).comap τ = C.comap τ := by
    rw [Subgroup.comap_inf, MonoidHom.comap_range_self, top_inf_eq]
  have hcent : Nat.card ↥(C.comap τ) = Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun u => ⟨fun i => (u.1 i).toAdd, ?_⟩
        invFun := fun v => ⟨fun i => Multiplicative.ofAdd (v.1 i), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact (orthTauCommuteYcodeIff_holds (otc_zeta K) m 1 hK (otc_zeta_injective K) c hc
        (fun i => (u.1 i).toAdd)).mp fun g hg => by
          change ↑(τ ↑u) * (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) =
            (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * ↑(τ ↑u)
          simpa only [Subgroup.coe_mul, Subgroup.coe_subtype] using
            congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp
              (Subgroup.mem_comap.mp u.2)) g hg).symm
    · refine Subgroup.mem_comap.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hv := (orthTauCommuteYcodeIff_holds (otc_zeta K) m 1 hK (otc_zeta_injective K)
        c hc v.1).mpr v.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      change (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) * otau (otc_zeta K) m 1 v.1 =
        otau (otc_zeta K) m 1 v.1 * (g : GL (Fin (m + 1) ⊕ Fin (m + 1)) K)
      exact (hv g hg).symm
    · intro u
      apply Subtype.ext
      funext i
      simp
    · intro v
      apply Subtype.ext
      funext i
      simp
  change Nat.card ↥(τ.range ⊓ C) = Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c)
  calc Nat.card ↥(τ.range ⊓ C) = Nat.card ↥((τ.range ⊓ C).comap τ) := hI
    _ = Nat.card ↥(C.comap τ) := by rw [hcomap]
    _ = Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c) := hcent

private theorem ggCommonJOmPlusTwo_dense_of_ne_zero (m : ℕ)
    (f : Fin m → Multiplicative (ZMod 3))
    (h : ∀ i, (f i).toAdd ≠ 0) : GGCoordDense f := by
  intro i
  constructor
  · intro h1
    exact h i (by rw [h1]; rfl)
  · intro j
    have hi := h i
    have hj := h j
    revert hi hj
    generalize (f i) = x
    generalize (f j) = y
    revert x y
    decide

theorem ggCommonJOmPlusTwo_position (hK : Nat.card K = 2) {m : ℕ}
    (f : Fin m → Multiplicative (ZMod 3)) (c : PlaneRaw.Code m)
    (hc : PlaneRaw.admissible (.orthogonal 1) c)
    (hocc : PlaneRaw.occurs (Submodule.span (ZMod 3) {fun i => (f i).toAdd}) c) :
    Nat.card ↥((ggCommonJOmPlusTwo_tau hK m).range ⊓
        Subgroup.centralizer
          (oYcode (otc_zeta K) m 1 c : Set ↥(omegaQ (K := K) m 1))) =
        Nat.card ↥(PlaneRaw.cent (.orthogonal 1) c) ∧
      (Nat.card ↥((ggCommonJOmPlusTwo_tau hK m).range ⊓
          Subgroup.centralizer
            (oYcode (otc_zeta K) m 1 c : Set ↥(omegaQ (K := K) m 1))) = 3 →
        (∃ e : PlaneRaw.V m, c = .extension e ∧ (PlaneRaw.Code.extSupport e).card = m ∧
            GGCoordDense f) ∨
        (∃ S : Finset (Fin m), c = .zero S ∧ S.card = m - 1 ∧ GGCoordSparse f)) := by
  classical
  let F' : PlaneRaw.V m := fun i => (f i).toAdd
  let τ := ggCommonJOmPlusTwo_tau hK m
  let C : Subgroup ↥(omegaQ (K := K) m 1) :=
    Subgroup.centralizer (oYcode (otc_zeta K) m 1 c : Set ↥(omegaQ (K := K) m 1))
  let cent := PlaneRaw.cent (.orthogonal 1) c
  have hcard : Nat.card ↥(τ.range ⊓ C) = Nat.card ↥cent :=
    ggCommonJOmPlusTwo_card_inf_cent hK m f c hc
  refine ⟨hcard, ?_⟩
  intro hthree
  have hcentcard : Nat.card ↥cent = 3 := by rw [← hcard]; exact hthree
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : 3 ^ Module.finrank (ZMod 3) ↥cent = 3 := by
    rw [FiniteField.pow_finrank_eq_natCard]
    exact hcentcard
  have hfr : Module.finrank (ZMod 3) ↥cent = 1 := by
    have h1 : 3 ^ Module.finrank (ZMod 3) ↥cent = 3 ^ 1 := by rw [hpow, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hmem : F' ∈ cent := ggCommonJOmPlusTwo_mem_cent_of_occurs m f c hocc
  have hne : F' ≠ 0 := ggCommonJOmPlusTwo_ne_zero_of_occurs m f c hcentcard hocc
  have hspan : cent = Submodule.span (ZMod 3) {F'} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfr hmem hne
  have hline := PlaneRaw.lineShapes_holds m (.orthogonal 1) F' c hne hocc hspan
  rcases hline with ⟨a, s, hs, hv, hc0⟩ | ⟨hfull, hcext⟩
  · right
    refine ⟨Finset.univ.erase a, hc0, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
        Fintype.card_fin]
    · refine ⟨a, fun j hj => ?_⟩
      have hvj : F' j = 0 := by
        rw [hv]
        simp [PlaneRaw.unitVec, Pi.smul_apply, hj]
      exact toAdd_eq_zero.mp hvj
  · left
    have hdense : GGCoordDense f := ggCommonJOmPlusTwo_dense_of_ne_zero m f hfull
    rcases hcext with hext | hext
    · refine ⟨F', hext, ?_, hdense⟩
      have hsupp : PlaneRaw.Code.extSupport F' = Finset.univ := by
        ext i
        rw [PlaneRaw.mem_extSupport]
        exact ⟨fun _ => Finset.mem_univ i, fun _ => hfull i⟩
      rw [hsupp, Finset.card_univ, Fintype.card_fin]
    · refine ⟨-F', hext, ?_, hdense⟩
      have hsupp : PlaneRaw.Code.extSupport (-F') = Finset.univ := by
        ext i
        rw [PlaneRaw.mem_extSupport]
        exact ⟨fun _ => Finset.mem_univ i, fun _ =>
          neg_ne_zero.mpr (hfull i)⟩
      rw [hsupp, Finset.card_univ, Fintype.card_fin]


private theorem ggCommonJOmPlusTwo_center_statedSU_four {E : Type} [Field E] [Finite E]
    [CharP E 2] (hE : Nat.card E = 4) :
    Subgroup.center (CFSG.Open.StatedSU 4 (2 ^ 1) E) = ⊥ := by
  have hF : Nat.card E = (2 ^ 1) ^ 2 := by rw [hE]; norm_num
  have hcenterSu : Subgroup.center
      (CFSG.ClassicalInvolution.Phan.Su E 2 1 4) = ⊥ :=
    CFSG.ClassicalInvolution.PhanDn.QTwo.center_Su_four_eq_bot hE
  have hEq : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution E 2 1) 4 =
      CFSG.Open.StatedSU 4 (2 ^ 1) E :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hmap := Subgroup.map_center_eq (MulEquiv.subgroupCongr hEq)
  rw [hcenterSu] at hmap
  simpa using hmap.symm

theorem ggCommonJOmPlusTwo_label (hK : Nat.card K = 2) {m : ℕ}
    (c : PlaneRaw.Code m) (hc : PlaneRaw.admissible (.orthogonal 1) c) :
    LargeEvenInLambda2 (PlaneRaw.label (.orthogonal 1) c) ∧
      GGHasLabel (PlaneRaw.label (.orthogonal 1) c)
        (↥(oYcode (otc_zeta K) m 1 c) ⧸
          Subgroup.center ↥(oYcode (otc_zeta K) m 1 c)) ∧
      (PlaneRaw.label (.orthogonal 1) c = ⟨.twA, 3, 1⟩ →
        Subgroup.center ↥(oYcode (otc_zeta K) m 1 c) = ⊥) := by
  classical
  have hmark := orthMarkedYcode_holds (otc_zeta K) m 1 hK (otc_zeta_injective K) c hc
  obtain ⟨lab, hlam, hhas, R, hR, I, Fset, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hlab : lab = PlaneRaw.label (.orthogonal 1) c := hP
  refine ⟨?_, ?_, ?_⟩
  · rwa [← hlab]
  · rwa [← hlab]
  · intro hlabel
    cases c with
    | zero S =>
        rw [PlaneRaw.label] at hlabel
        split_ifs at hlabel <;> cases hlabel
    | extension e =>
        obtain ⟨he, h4⟩ := hc
        have hsupp : (PlaneRaw.Code.extSupport e).card = 4 := by
          have hrank : (PlaneRaw.Code.extSupport e).card - 1 = 3 := by
            have := congrArg (fun l : LargeEvenLabel => l.rank) hlabel
            simpa [PlaneRaw.label] using this
          omega
        have he' : liftV m 1 e ≠ 0 := by
          intro h0
          have hzero : liftV m 1 (0 : PlaneRaw.V m) = 0 := by
            funext i
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
              simp [liftV, Fin.append_left, Fin.append_right]
          exact he (liftV_injective m 1 (h0.trans hzero.symm))
        obtain ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨φB⟩⟩ :=
          SpBlocks.exists_blockGroup_extension_mulEquiv (ζ := otc_zeta K) (m := m + 1)
            hK (otc_zeta_injective K) he'
        letI : Field E := hEfield
        letI : Finite E := hEfin
        letI : CharP E 2 := hEchar
        let k := (PlaneRaw.Code.extSupport (liftV m 1 e)).card
        have hk : k = 4 := by
          dsimp only [k]
          rw [card_extSupport_liftV, hsupp]
        let B := SpBlocks.blockGroup (otc_zeta K) (m + 1) (.extension (liftV m 1 e))
        let GU := ClassicalBlocks.GUFull k 2 E
        let ψB : ↥⁅B, B⁆ ≃* ↥⁅GU, GU⁆ :=
          let c₁ : ↥⁅B, B⁆ ≃* ↥(commutator ↥B) :=
            (((commutator ↥B).equivMapOfInjective B.subtype B.subtype_injective).trans
              (MulEquiv.subgroupCongr B.map_subtype_commutator)).symm
          let c₂ : ↥(commutator ↥B) ≃* ↥(commutator ↥GU) :=
            ((commutator ↥B).equivMapOfInjective φB.toMonoidHom φB.injective).trans
              (MulEquiv.subgroupCongr (by
                rw [commutator_def, commutator_def, Subgroup.map_commutator,
                  ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φB.surjective]))
          let c₃ : ↥(commutator ↥GU) ≃* ↥⁅GU, GU⁆ :=
            ((commutator ↥GU).equivMapOfInjective GU.subtype
              (Subgroup.subtype_injective _)).trans
              (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator GU))
          c₁.trans (c₂.trans c₃)
        let ψSU : ↥(SpBlocks.Ycode (otc_zeta K) (m + 1) (.extension (liftV m 1 e))) ≃*
            ↥(CFSG.Open.StatedSU k 2 E) :=
          ψB.trans (MulEquiv.subgroupCongr
            (SpBlocks.commutator_guFull_eq_statedSU hEcard (by omega : 4 ≤ k)))
        have hcenterSU : Subgroup.center ↥(CFSG.Open.StatedSU k 2 E) = ⊥ := by
          rw [hk]
          exact ggCommonJOmPlusTwo_center_statedSU_four hEcard
        have hcenterY : Subgroup.center ↥(SpBlocks.Ycode (otc_zeta K) (m + 1)
            (.extension (liftV m 1 e))) = ⊥ := by
          have hmap := Subgroup.map_center_eq ψSU
          rw [hcenterSU] at hmap
          have hmap' : (Subgroup.center ↥(SpBlocks.Ycode (otc_zeta K) (m + 1)
              (.extension (liftV m 1 e)))).map ψSU.toMonoidHom = ⊥ := by simpa using hmap
          exact (Subgroup.map_eq_bot_iff_of_injective _ ψSU.injective).mp hmap'
        let ψ : ↥(oYcode (otc_zeta K) m 1 (.extension e)) ≃*
            ↥(SpBlocks.Ycode (otc_zeta K) (m + 1) (.extension (liftV m 1 e))) :=
          ((oYcode (otc_zeta K) m 1 (.extension e)).equivMapOfInjective
            (omegaQ (K := K) m 1).subtype (Subgroup.subtype_injective _)).trans
          ((MulEquiv.subgroupCongr (oYcode_extension_map_eq (otc_zeta K) m 1 hK
            (otc_zeta_injective K) e ⟨he, h4⟩)).trans
          ((SpBlocks.Ycode (otc_zeta K) (m + 1) (.extension (liftV m 1 e))).equivMapOfInjective
            (CFSG.Open.StatedSp (m + 1) K).subtype (Subgroup.subtype_injective _)).symm)
        have hcenterO : Subgroup.center ↥(oYcode (otc_zeta K) m 1 (.extension e)) = ⊥ := by
          have hmap := Subgroup.map_center_eq ψ
          rw [hcenterY] at hmap
          have hmap' : (Subgroup.center
              ↥(oYcode (otc_zeta K) m 1 (.extension e))).map ψ.toMonoidHom = ⊥ := by
            simpa using hmap
          exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp hmap'
        exact hcenterO

end CFSG.StandardType.CommonJOmPlusTwo

end
