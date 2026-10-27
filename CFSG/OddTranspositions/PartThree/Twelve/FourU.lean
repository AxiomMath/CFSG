module

public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockUnitary
import CFSG.ClassicalGroups.Unitary.Generation
import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.OddTranspositions.WidthSylow
import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
  CFSG.OddTranspositions.PartFour

section UnitaryCentres

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem exists_iso_herm_eq_zero_forall_ne_smul (hσ : IsUnitaryInvolution σ) (hm : 4 ≤ m)
    {u : Fin m → F} (hu0 : u ≠ 0) (hu : herm σ u u = 0) :
    ∃ w, herm σ w w = 0 ∧ herm σ u w = 0 ∧ ∀ c : F, w ≠ c • u := by
  have hinv := hσ.invol
  obtain ⟨d, hd, hud, -⟩ := exists_cno hσ hu0 hu hu0
  have hd' : herm σ ((herm σ u d)⁻¹ • d) ((herm σ u d)⁻¹ • d) = 0 := by
    rw [herm_smul_left, herm_smul_right, hd, mul_zero, mul_zero]
  have hud' : herm σ u ((herm σ u d)⁻¹ • d) = 1 := by
    rw [herm_smul_right, inv_mul_cancel₀ hud]
  obtain ⟨z, hz, huz, hdz⟩ := exists_norm_one_perp_pair hσ (by omega) hu hd' hud'
  obtain ⟨w, hw, hwu, hwd, hwz⟩ := exists_iso_perp_pair_herm_eq hσ hm hu hd' hud' (v := z)
    (by rw [hdz, huz, zero_smul, zero_smul, sub_zero, sub_zero, hz]; exact one_ne_zero) 1
  refine ⟨w, hw, herm_eq_zero_comm σ hinv hwu, fun c hc => ?_⟩
  rw [hc, herm_smul_left, hud', mul_one] at hwd
  have hc0 : c = 0 := by
    by_contra hc0
    exact ((map_ne_zero σ).mpr hc0) hwd
  rw [hc, hc0, zero_smul, herm_zero_left] at hwz
  exact zero_ne_one hwz

theorem suTv_mul_mul_smul (hσ : IsUnitaryInvolution σ) {a b e : Fin m → F}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (he : herm σ e e = 0) (hab : herm σ a b = 0)
    (hae : herm σ a e = 0) (hbe : herm σ b e = 0) {c : F} (hc : c + σ c = 0) (v : Fin m → F) :
    (suTv hσ a c * suTv hσ b c * suTv hσ e c) • v =
      v + (c * herm σ e v) • e + (c * herm σ b v) • b + (c * herm σ a v) • a := by
  rw [mul_smul, mul_smul, suTv_smul hσ he hc, suTv_smul hσ hb hc, suTv_smul hσ ha hc]
  simp only [herm_add_right, herm_smul_right, hbe, hae, hab, mul_zero, add_zero]

theorem suTv_eq_mul_mul [CharP F 2] (hσ : IsUnitaryInvolution σ) {u w : Fin m → F}
    (hu : herm σ u u = 0) (hw : herm σ w w = 0) (huw : herm σ u w = 0) {c : F}
    (hc : c + σ c = 0) {l : F} (hl : σ l = l) :
    suTv hσ u c = suTv hσ (u + l • w) c * suTv hσ (u + w) c *
      suTv hσ (u + (l + 1) • w) c := by
  have hwu : herm σ w u = 0 := herm_eq_zero_comm σ hσ.invol huw
  have hB : ∀ a b : F, herm σ (u + a • w) (u + b • w) = 0 := by
    intro a b
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu, hw, huw, hwu,
      mul_zero, add_zero]
  have hB1 : ∀ a : F, herm σ (u + a • w) (u + w) = 0 := fun a => by
    have := hB a 1
    rwa [one_smul] at this
  have hB2 : ∀ b : F, herm σ (u + w) (u + b • w) = 0 := fun b => by
    have := hB 1 b
    rwa [one_smul] at this
  have hI : ∀ a : F, herm σ (u + a • w) (u + a • w) = 0 := fun a => hB a a
  have hI1 : herm σ (u + w) (u + w) = 0 := by
    have := hB 1 1
    rwa [one_smul] at this
  have hl1 : σ (l + 1) = l + 1 := by rw [map_add, map_one, hl]
  refine ext_smul σ fun v => ?_
  rw [suTv_mul_mul_smul hσ (hI l) hI1 (hI (l + 1)) (hB1 l) (hB l (l + 1)) (hB2 (l + 1)) hc,
    suTv_smul hσ hu hc]
  simp only [herm_add_left, herm_smul_left, hl, hl1]
  generalize herm σ u v = p
  generalize herm σ w v = q
  have key : v + (c * (p + (l + 1) * q)) • (u + (l + 1) • w) + (c * (p + q)) • (u + w) +
      (c * (p + l * q)) • (u + l • w) = v + (c * p) • u +
      (2 : F) • ((c * p + c * (l + 1) * q) • u +
        (c * p * (l + 1) + c * q * (l ^ 2 + l + 1)) • w) := by
    module
  rw [key, CharTwo.two_eq_zero, zero_smul, add_zero]

end UnitaryCentres

section UnitaryModel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_unitaryInvolution_eq_self_ne_zero_ne_one (hF : Nat.card F = (2 ^ n) ^ 2)
    (hn : 2 ≤ n) : ∃ l : F, unitaryInvolution F 2 n l = l ∧ l ≠ 0 ∧ l ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hcon
  push Not at hcon
  have hcard : Fintype.card F = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hF, hq]
  have hpow : ∀ t : F, t ^ (q ^ 2) = t := fun t => by
    rw [← hcard]
    exact FiniteField.pow_card t
  have hnorm : ∀ t : Fˣ, (t : F) ^ (q + 1) = 1 := by
    intro t
    refine hcon _ ?_ (pow_ne_zero _ t.ne_zero)
    rw [unitaryInvolution_apply, ← hq, ← pow_mul]
    calc (t : F) ^ ((q + 1) * q) = (t : F) ^ (q ^ 2) * (t : F) ^ q := by
          rw [← pow_add]
          congr 1
          ring
      _ = (t : F) ^ (q + 1) := by rw [hpow, pow_succ, mul_comm]
  have hdeg : (Polynomial.X ^ (q + 1) - Polynomial.C (1 : F)).natDegree = q + 1 :=
    Polynomial.natDegree_X_pow_sub_C
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ (q + 1) - Polynomial.C (1 : F)) (f := ((↑) : Fˣ → F)) Units.val_injective
    (fun t => by simp [hnorm t])
    (by
      rw [hdeg, Fintype.card_units, hcard]
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = q ^ 2 := ⟨_, rfl⟩
      have hQq : q + 3 ≤ Q := by rw [hQ]; nlinarith
      rw [← hQ]
      omega)
  exact Polynomial.X_pow_sub_C_ne_zero (by omega) (1 : F) hP

theorem isRootTriple_of_isUnitaryTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f) (h : IsUnitaryTransvection X m f s) :
    IsRootTriple E s := by
  classical
  obtain ⟨F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set π := kFactsSuProj hF m with hπdef
  set ψ : X →* StatedProj (StatedSU m (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h2 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h2
    obtain ⟨z, hz, hzb⟩ := h2
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  obtain ⟨u, hu0, hu, hψs⟩ := kFacts_su_exists_centre hF hrank
  change ψ s = π (suTv hσ u 1) at hψs
  replace hu : herm σ u u = 0 := hu
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hEmem : ∀ v, v ≠ 0 → herm σ v v = 0 → ∃ y ∈ E, ψ y = π (suTv hσ v 1) := by
    intro v hv0 hv
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (by omega) hu0 hu hv0 hv
    obtain ⟨g, hg⟩ := hψsurj (π t)
    refine ⟨g * s * g⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hψs, ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ t hu h1, ht]
  have hcommE : ∀ a b : Fin m → F, a ≠ 0 → herm σ a a = 0 → herm σ b b = 0 →
      (Commute (π (suTv hσ a 1)) (π (suTv hσ b 1)) ↔ herm σ a b = 0) := by
    intro a b ha0 ha hb
    exact ⟨herm_eq_zero_of_commute_kFactsSuProjTv hF (by omega) ha0 ha hb,
      fun hab => kFacts_suProjTv_comm_of_herm_eq_zero hF ha hb hab h1 h1⟩
  have hout : ∀ y ∈ E, ∀ a, a ≠ 0 → herm σ a a = 0 → herm σ u a = 0 →
      ψ y = π (suTv hσ a 1) → (∀ t : F, a ≠ t • u) → y ∉ rootBlock E s := by
    intro y _ a ha0 ha hua hya hau hyr
    obtain ⟨x, hx, hux, hax⟩ := exists_iso_perp hσ hu0 hu ha hua hau
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hax (herm_zero_right σ a)
    obtain ⟨z, hz, hψz⟩ := hEmem x hx0 hx
    have h2 : Commute z s := by
      rw [hcomm, hψz, hψs, hcommE x u hx0 hx hu]
      exact herm_eq_zero_comm σ hinv hux
    have h3 : ¬ Commute z y := by
      rw [hcomm, hψz, hya, hcommE x a hx0 hx ha]
      intro hxa
      exact hax (herm_eq_zero_comm σ hinv hxa)
    exact h3 ((hyr.2 z hz).mpr h2)
  obtain ⟨w, hw, huw, hwu⟩ := exists_iso_herm_eq_zero_forall_ne_smul hσ hm hu0 hu
  obtain ⟨l, hl, hl0, hl1⟩ := exists_unitaryInvolution_eq_self_ne_zero_ne_one hF hf
  have hl1' : l + 1 ≠ 0 := by
    intro h
    apply hl1
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hnot : ∀ t : F, t ≠ 0 → ∀ r : F, u + t • w ≠ r • u := by
    intro t ht r hr
    apply hwu (t⁻¹ * (r - 1))
    have htw : t • w = (r - 1) • u := by
      rw [sub_smul, one_smul, ← hr]
      abel
    rw [mul_smul, ← htw, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hne0 : ∀ t : F, t ≠ 0 → u + t • w ≠ 0 := fun t ht h0 =>
    hnot t ht 0 (by rw [h0, zero_smul])
  have hwu' : herm σ w u = 0 := herm_eq_zero_comm σ hinv huw
  have hB : ∀ a b : F, herm σ (u + a • w) (u + b • w) = 0 := by
    intro a b
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu, hw, huw, hwu',
      mul_zero, add_zero]
  have hU : ∀ b : F, herm σ u (u + b • w) = 0 := by
    intro b
    simp only [herm_add_right, herm_smul_right, hu, huw, mul_zero, add_zero]
  obtain ⟨y₁, hy₁, hψ₁⟩ := hEmem _ (hne0 l hl0) (hB l l)
  obtain ⟨y₂, hy₂, hψ₂⟩ := hEmem _ (hne0 1 one_ne_zero) (hB 1 1)
  obtain ⟨y₃, hy₃, hψ₃⟩ := hEmem _ (hne0 (l + 1) hl1') (hB (l + 1) (l + 1))
  refine ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃,
    hout y₁ hy₁ _ (hne0 l hl0) (hB l l) (hU l) hψ₁ (hnot l hl0),
    hout y₂ hy₂ _ (hne0 1 one_ne_zero) (hB 1 1) (hU 1) hψ₂ (hnot 1 one_ne_zero),
    hout y₃ hy₃ _ (hne0 _ hl1') (hB _ _) (hU _) hψ₃ (hnot _ hl1'), ?_, ?_, ?_, ?_⟩
  · rw [hcomm, hψ₁, hψ₂, hcommE _ _ (hne0 l hl0) (hB l l) (hB 1 1)]
    exact hB l 1
  · rw [hcomm, hψ₁, hψ₃, hcommE _ _ (hne0 l hl0) (hB l l) (hB _ _)]
    exact hB l (l + 1)
  · rw [hcomm, hψ₂, hψ₃, hcommE _ _ (hne0 1 one_ne_zero) (hB 1 1) (hB _ _)]
    exact hB 1 (l + 1)
  · apply hψinj
    rw [map_mul, map_mul, hψ₁, hψ₂, hψ₃, hψs, ← map_mul, ← map_mul, one_smul,
      ← suTv_eq_mul_mul hσ hu hw huw h1 hl]

theorem commutator_eq_top_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 4 ≤ m)
    (h : IsUnitaryTransvection X m f s) : commutator X = ⊤ := by
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  let ψ : X ≃* StatedProj (StatedSU m (2 ^ f) F) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have : Group.IsPerfect (StatedSU m (2 ^ f) F) :=
    CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF hm
  have : Group.IsPerfect (StatedProj (StatedSU m (2 ^ f) F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem odd_card_ker_of_isUnitaryTransvection
    {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsUnitaryTransvection X m f s) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* X), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → Odd (Nat.card φ.ker) := by
  have htop := commutator_eq_top_of_isUnitaryTransvection hZ hm h
  intro Γ _ _ φ hφ hcen hcomm
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  let ψ : X ≃* StatedProj (StatedSU m (2 ^ f) F) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hΓ : commutator Γ = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    have h1 : φ γ ∈ (commutator Γ).map φ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hφ, ← commutator_def, htop]
      exact Subgroup.mem_top _
    obtain ⟨γ', hγ', hγγ'⟩ := h1
    have hk : γ'⁻¹ * γ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hγγ', inv_mul_cancel]
    have e1 : γ = γ' * (γ'⁻¹ * γ) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hγ' (hcomm hk)
  have : Group.IsPerfect Γ := ⟨hΓ⟩
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let q : Γ →* StatedProj (StatedSU m (2 ^ f) F) := ψ.toMonoidHom.comp φ
  have hq : Function.Surjective q := ψ.surjective.comp hφ
  have hqker : q.ker = φ.ker := by
    ext g
    simp [q, MonoidHom.mem_ker]
  have hker : q.ker ≤ Subgroup.center Γ := by rw [hqker]; exact hcen
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hker)
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker)
  obtain ⟨e'⟩ : Nonempty (griessHopfMultiplier (StatedProj (StatedSU m (2 ^ f) F)) ≃*
      Multiplicative (ZMod (Nat.gcd m (2 ^ f + 1)))) := by
    by_cases he : Even m
    · exact (CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hF he hm hq4).2
    · refine (CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hF (by omega)
        (by omega) he fun h3 => ?_).2
      have h4 : m = 3 := congrArg Prod.fst h3
      omega
  have hcardM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSU m (2 ^ f) F))) = Nat.gcd m (2 ^ f + 1) := by
    rw [← Nat.card_congr ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.trans
      e').toEquiv.symm]
    exact Nat.card_zmod _
  have hodd : Odd (Nat.gcd m (2 ^ f + 1)) :=
    Odd.of_dvd_nat (by rw [Nat.odd_add_one, Nat.not_odd_iff_even]; exact (Nat.even_pow.mpr
      ⟨even_two, by omega⟩)) (Nat.gcd_dvd_right _ _)
  rw [← hqker]
  exact Odd.of_dvd_nat hodd (hcardM ▸ hdvd)

end UnitaryModel

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem alpha_eq_singleton_of_isUnitaryTransvection_of_mult (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)
    (hmult : ∀ (Γ : Type) [Group Γ] [Finite Γ]
      (φ : Γ →* Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
        Odd (Nat.card φ.ker)) :
    hC.alpha = {hC.d} := by
  have hZ : Subgroup.center
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
    have h1 := center_le_solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    rw [solvableRadical_quotient_H hC] at h1
    exact le_bot_iff.mp h1
  obtain ⟨hb1, hne⟩ :=
    subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs hm h
  have htri := isRootTriple_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs hm hf h
  have htop := commutator_eq_top_of_isUnitaryTransvection hZ hm h
  have hodd := odd_card_center_inf_commutator_of_multiplier hC hMZ
    (by rw [htop, ← commutator_def, htop]) (by
      intro Γ _ _ φ hφ hcen hcomm
      let θ : ↥(commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) ≃*
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have hker : (θ.toMonoidHom.comp φ).ker = φ.ker := by
        ext g
        simp [MonoidHom.mem_ker]
      have h1 := hmult Γ (θ.toMonoidHom.comp φ) (θ.surjective.comp hφ)
        (by rw [hker]; exact hcen) (by rw [hker]; exact hcomm)
      rwa [hker] at h1)
  exact alpha_eq_singleton_of_isRootTriple hC hMZ hs hb1 hne htri hodd

theorem alpha_eq_singleton_of_isUnitaryTransvection
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) :
    hC.alpha = {hC.d} := by
  have hZ : Subgroup.center
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
    have h1 := center_le_solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    rw [solvableRadical_quotient_H hC] at h1
    exact le_bot_iff.mp h1
  exact alpha_eq_singleton_of_isUnitaryTransvection_of_mult hC hMZ hs hm hf h
    (odd_card_ker_of_isUnitaryTransvection hZ hm hf h)

end CFSG.OddTranspositions.PartThree
