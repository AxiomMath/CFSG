module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearVac
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition CFSG.Timmesfeld.LieEmbed
open Matrix
open CFSG.ComponentClassification.RankTwoOddLie (CenterPPrime)

private theorem exists_mul_sub_ne_zero {F : Type*} [Field F] {n : ℕ} {v w : Fin n → F}
    (hv : v ≠ 0) (hprop : ¬ ∃ l : F, w = l • v) :
    ∃ p q : Fin n, v p * w q - v q * w p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hv
  have hp0 : v p ≠ 0 := by simpa using hp
  apply hprop
  refine ⟨w p / v p, ?_⟩
  funext k
  have hk := h p k
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hp0]
  linear_combination hk

private theorem unitTransvGroup_matrix_eq_one_or {F : Type} [Field F] [CharP F 2]
    {σ : F ≃+* F} (hσ2 : ∀ c, σ c = c ^ 2) (hF4 : Nat.card F = 4) {n : ℕ}
    {v : Fin n → F} (hvv : uForm σ v v = 0) {g : GL (Fin n) F}
    (hg : g ∈ CFSG.StandardType.ClassicalPosition.unitTransvGroup (F := F) σ.toRingHom
      (CFSG.LieType.Universal.Unitary.antidiag n) v) :
    (g : Matrix (Fin n) (Fin n) F) = 1 ∨
      (g : Matrix (Fin n) (Fin n) F) = uTrans σ v 1 := by
  classical
  have hfix : ∀ c : F, σ c = c → c = 0 ∨ c = 1 := by
    intro c hc
    have h2 : c ^ 2 = c := by rw [← hσ2, hc]
    have hmul : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  refine Subgroup.closure_induction (p := fun (g : GL (Fin n) F) _ =>
    (g : Matrix (Fin n) (Fin n) F) = 1 ∨
      (g : Matrix (Fin n) (Fin n) F) = uTrans σ v 1) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨c, hc, hg⟩
    have hc' : σ c = c := hc
    rw [hg]
    rcases hfix c hc' with rfl | rfl
    · left
      simp
    · right
      simp [uTrans, uNil, uRow]
  · left
    simp
  · rintro g h _ _ (hg | hg) (hh | hh)
    · left
      rw [Units.val_mul, hg, hh, mul_one]
    · right
      rw [Units.val_mul, hg, hh, one_mul]
    · right
      rw [Units.val_mul, hg, hh, mul_one]
    · left
      rw [Units.val_mul, hg, hh, uTrans_mul_uTrans σ hvv,
        show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1, uTrans_zero]
  · rintro g _ (hg | hg)
    · left
      have hg1 : g = 1 := Units.ext hg
      rw [hg1]
      simp
    · right
      have hgg : g * g = 1 := by
        ext
        rw [Units.val_mul, hg, uTrans_mul_uTrans σ hvv,
          show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1, uTrans_zero, Units.val_one]
      have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
      rw [hginv, hg]

private theorem uTrans_mul_ne_uTrans {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (hσ2 : ∀ c, σ c = c ^ 2)
    (hF4 : Nat.card F = 4) {n : ℕ} {v w : Fin n → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvv : uForm σ v v = 0) (hww : uForm σ w w = 0)
    (hne : uTrans σ v 1 ≠ uTrans σ w 1)
    (hcomm : uTrans σ v 1 * uTrans σ w 1 = uTrans σ w 1 * uTrans σ v 1) :
    ∀ u : Fin n → F, u ≠ 0 → uForm σ u u = 0 →
      uTrans σ v 1 * uTrans σ w 1 ≠ uTrans σ u 1 := by
  intro u _hu _huu heq
  have hnorm : ∀ l : F, l ≠ 0 → l * σ l = 1 := by
    intro l hl
    have hcard : Nat.card Fˣ = 3 := by
      have hF' : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF4]; norm_num
      have h := CFSG.ClassicalGroups.Unitary.card_units_of_card (p := 2) (f := 1) hF'
      rw [h]
      norm_num
    have hpow : l ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := Units.mk0 l hl)
      rw [hcard] at h
      have h' := congrArg Units.val h
      simpa using h'
    rw [hσ2 l, show l * l ^ 2 = l ^ 3 from by ring]
    exact hpow
  have hnotprop : ¬ ∃ l : F, w = l • v := by
    rintro ⟨l, rfl⟩
    apply hne
    have hl0 : l ≠ 0 := by
      intro h
      apply hw
      rw [h, zero_smul]
    rw [uTrans_smul, hnorm l hl0, one_mul]
  have hvw : uForm σ v w = 0 := by
    rcases uForm_eq_zero_of_commute σ hσ hv one_ne_zero one_ne_zero hcomm with h | h
    · exact h
    · exact absurd h hnotprop
  have hwv : uForm σ w v = 0 := by
    rw [← uForm_conj σ hσ v w, hvw, map_zero]
  have hNvw : uNil σ v * uNil σ w = 0 := by
    rw [uNil_mul_uNil, hvw, zero_smul]
  have hNu : uNil σ v + uNil σ w = uNil σ u := by
    have h := heq
    simp only [uTrans, one_smul] at h
    have h' : 1 + (uNil σ v + uNil σ w) = 1 + uNil σ u := by
      have hexp : (1 + uNil σ v) * (1 + uNil σ w) =
          1 + (uNil σ v + uNil σ w) + uNil σ v * uNil σ w := by noncomm_ring
      rw [← h, hexp, hNvw, add_zero]
    exact add_left_cancel h'
  obtain ⟨p, q, hpq⟩ := exists_mul_sub_ne_zero (F := F) hv hnotprop
  have hbc : ¬ ∃ μ : F, uRow σ w = μ • uRow σ v := by
    rintro ⟨μ, hμ⟩
    apply hnotprop
    refine ⟨σ μ, ?_⟩
    funext i
    have h := congrFun hμ (Fin.rev i)
    rw [uRow_apply, Pi.smul_apply, smul_eq_mul, uRow_apply, Fin.rev_rev] at h
    show w i = σ μ * v i
    calc w i = σ (σ (w i)) := (hσ (w i)).symm
      _ = σ (μ * σ (v i)) := by rw [h]
      _ = σ μ * v i := by rw [map_mul, hσ]
  obtain ⟨r, s, hrs⟩ := exists_mul_sub_ne_zero (F := F) (uRow_ne_zero σ hv) hbc
  have hminor : (uNil σ v + uNil σ w) p r * (uNil σ v + uNil σ w) q s -
      (uNil σ v + uNil σ w) p s * (uNil σ v + uNil σ w) q r =
      (v p * w q - v q * w p) *
        (uRow σ v r * uRow σ w s - uRow σ v s * uRow σ w r) := by
    simp only [Matrix.add_apply, uNil, Matrix.vecMulVec_apply]
    ring
  have hminorU : (uNil σ u) p r * (uNil σ u) q s -
      (uNil σ u) p s * (uNil σ u) q r = 0 := by
    simp only [uNil, Matrix.vecMulVec_apply]
    ring
  have hzero : (v p * w q - v q * w p) *
      (uRow σ v r * uRow σ w s - uRow σ v s * uRow σ w r) = 0 := by
    rw [← hminor]
    have heq2 : (uNil σ v + uNil σ w) p r * (uNil σ v + uNil σ w) q s -
        (uNil σ v + uNil σ w) p s * (uNil σ v + uNil σ w) q r =
        (uNil σ u) p r * (uNil σ u) q s - (uNil σ u) p s * (uNil σ u) q r := by
      rw [hNu]
    rw [heq2, hminorU]
  exact mul_ne_zero hpq hrs hzero

theorem rckCollinearVia_PSU_long_two
    {m : ℕ} {β : Fin (ggU .PSU m 1).D.rank → ℤ} (hβ : β ∈ (ggU .PSU m 1).D.roots)
    (hl : GGLongRoot (ggU .PSU m 1).D β) : RCKCollinearVia (ggU .PSU m 1) β := by
  have h1 : (1 : ℕ) ≤ 1 := le_rfl
  let F := GaloisField 2 (2 * 1)
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 1
  have hF : Nat.card F = (2 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 1 le_rfl
  let M0 : LieUniversal := ⟨CFSG.LieType.Universal.Unitary.SU σ m,
    CFSG.LieType.Universal.Unitary.rootDatum hF m⟩
  have e : ggU .PSU m 1 = M0 := by
    simp only [ggU, lieUniversal, M0, F, σ, ↓reduceDIte, h1]
  have hZ0 : CenterPPrime (ggU .PSU m 1).K 2 :=
    rckGL1_centerPPrime_ggU (t := .PSU) (Or.inr (Or.inl rfl)) le_rfl (fun h => by cases h)
  suffices h : ∀ (M : LieUniversal), M = M0 → ∀ (β : Fin M.D.rank → ℤ),
      β ∈ M.D.roots → GGLongRoot M.D β → RCKCollinearVia M β by
    exact h (ggU .PSU m 1) e β hβ hl
  intro M hM β hβ hl
  subst hM
  have hZ : CenterPPrime M0.K 2 := by
    have h := hZ0
    rw [e] at h
    exact h
  have hβ' : β ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots := hβ
  have hσ : ∀ c : F, σ (σ c) = c := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hF c
  have hσ2 : ∀ c : F, σ c = c ^ 2 := by
    intro c
    change CFSG.LieType.BorelTits.unitaryInvolution F 2 1 c = c ^ 2
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  have hF4 : Nat.card F = 4 := by
    rw [hF]
    norm_num
  obtain ⟨v, w, hvv0, hww0, hvw0, hmap, -⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitTransvGroup_eq_conj_rootGroup_SU
      (f := 1) hF m hβ' hl (1 : CFSG.LieType.Universal.Unitary.SU σ m)
  have hvv : uForm σ v v = 0 := by
    rw [← uRow_dotProduct]
    exact hvv0
  have hww : uForm σ w w = 0 := by
    rw [← uRow_dotProduct]
    exact hww0
  have hvw : uForm σ v w = 1 := by
    rw [← uRow_dotProduct]
    exact hvw0
  have hv0 : v ≠ 0 := by
    intro h
    have hzero : uForm σ (0 : Fin m → F) w = 0 := by simp [uForm]
    rw [h, hzero] at hvw
    exact one_ne_zero hvw.symm
  let C : Set M0.K := {x | ∃ v : Fin m → F, v ≠ 0 ∧ uForm σ v v = 0 ∧
    suMat σ m x = uTrans σ v 1}
  have hmap' : (((CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β).map
      (CFSG.LieType.Universal.Unitary.SU σ m).subtype) =
      unitTransvGroup σ.toRingHom (CFSG.LieType.Universal.Unitary.antidiag m) v := by
    have hconj1 : (MulAut.conj (1 : CFSG.LieType.Universal.Unitary.SU σ m)).toMonoidHom =
        MonoidHom.id (CFSG.LieType.Universal.Unitary.SU σ m) := by
      ext y
      simp [MulAut.conj_apply]
    have h := hmap
    rw [hconj1] at h
    simpa [σ] using h
  have hX : ∀ x ∈ M0.D.rootGroup β, x ≠ 1 → x ∈ C := by
    intro x hx hx1
    have hmem : ((x : CFSG.LieType.Universal.Unitary.SU σ m) : GL (Fin m) F) ∈
        (((CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β).map
          (CFSG.LieType.Universal.Unitary.SU σ m).subtype) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap'] at hmem
    rcases unitTransvGroup_matrix_eq_one_or hσ2 hF4 hvv hmem with h1 | h1
    · exfalso
      apply hx1
      apply Subtype.ext
      apply Units.ext
      simpa using h1
    · exact ⟨v, hv0, hvv, h1⟩
  have hconj : ∀ x ∈ C, ∀ g : M0.K, g * x * g⁻¹ ∈ C := by
    rintro x ⟨u, hu0, huu, hx⟩ g
    exact ⟨suMat σ m g *ᵥ u, suMat_mulVec_ne_zero σ g hu0,
      by rw [uForm_mulVec]; exact huu, suMat_conj_of_eq σ hx g⟩
  have hinv : ∀ x ∈ C, x * x = 1 := by
    rintro x ⟨u, -, huu, hx⟩
    apply suMat_injective (σ := σ) (n := m)
    rw [map_mul, hx, uTrans_mul_uTrans σ huu,
      show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1, uTrans_zero, map_one]
  have hprod : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x * y = y * x → x * y ∉ C := by
    rintro x ⟨u, hu0, huu, hx⟩ y ⟨y', hy'0, hy'u, hy⟩ hne hcomm hxy
    obtain ⟨z, hz0, hzu, hxz⟩ := hxy
    have hne' : uTrans σ u 1 ≠ uTrans σ y' 1 := by
      intro h
      apply hne
      apply suMat_injective (σ := σ) (n := m)
      rw [hx, hy, h]
    have hcomm' : uTrans σ u 1 * uTrans σ y' 1 = uTrans σ y' 1 * uTrans σ u 1 := by
      have h := congrArg (suMat σ m) hcomm
      rwa [map_mul, map_mul, hx, hy] at h
    have hmat : uTrans σ u 1 * uTrans σ y' 1 = uTrans σ z 1 := by
      rw [← hx, ← hy, ← map_mul, hxz]
    exact uTrans_mul_ne_uTrans hσ hσ2 hF4 hu0 hy'0 huu hy'u hne' hcomm' z hz0 hzu hmat
  exact rckCollinearVia_of_noFour hZ C hconj hinv hX hprod

theorem rckCollinearVia_PSU_long_of_two_le
    {m g : ℕ} (hg : 2 ≤ g) {β : Fin (ggU .PSU m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSU m g).D.roots) (hl : GGLongRoot (ggU .PSU m g).D β) :
    RCKCollinearVia (ggU .PSU m g) β := by
  have h1 : 1 ≤ g := by omega
  let F := GaloisField 2 (2 * g)
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 g
  have hF : Nat.card F = (2 ^ g) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 g h1
  let M0 : LieUniversal := ⟨CFSG.LieType.Universal.Unitary.SU σ m,
    CFSG.LieType.Universal.Unitary.rootDatum hF m⟩
  have e : ggU .PSU m g = M0 := by
    simp only [ggU, lieUniversal, M0, F, σ, ↓reduceDIte, h1]
  have hZ0 : CenterPPrime (ggU .PSU m g).K 2 :=
    rckGL1_centerPPrime_ggU (t := .PSU) (Or.inr (Or.inl rfl)) h1 (fun h => by cases h)
  suffices h : ∀ (M : LieUniversal), M = M0 → ∀ (β : Fin M.D.rank → ℤ),
      β ∈ M.D.roots → GGLongRoot M.D β → RCKCollinearVia M β by
    exact h (ggU .PSU m g) e β hβ hl
  intro M hM β hβ hl
  subst hM
  have hZ : CenterPPrime M0.K 2 := by
    have h := hZ0
    rw [e] at h
    exact h
  have hβ' : β ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots := hβ
  have hm : 1 ≤ m := by
    have hroots : β ∈ CFSG.LieType.RootSystem.roots
        (CFSG.LieType.Universal.Unitary.isFiniteType_cartan m)
        (CFSG.LieType.Universal.Unitary.divisible m) := hβ'
    rw [CFSG.LieType.Universal.Unitary.roots_eq] at hroots
    rcases hroots with ⟨i, j, -⟩ | ⟨i, -⟩ | ⟨-, i, -⟩
    · exact i.pos
    · exact i.pos
    · exact i.pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M0.K := inferInstance
  have hX : IsPGroup 2 (M0.D.rootGroup β) := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF)
      (CFSG.LieType.Universal.Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ')
  have hc : Nat.card (M0.D.rootGroup β) ≠ 2 := by
    have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
    obtain ⟨i, hi, hw⟩ :=
      CFSG.StandardType.LieKnownR2.Geo.exists_weight_of_ggLongRoot hF hβ' hl
    have hle : (CFSG.LieType.Universal.Unitary.longRootHom σ hi).range ≤
        M0.D.rootGroup β := by
      rintro x ⟨c, rfl⟩
      exact CFSG.LieType.Universal.Unitary.SUExtras.longRootHom_mem hσ hi hw.symm c
    have hcard : Nat.card (CFSG.LieType.Universal.Unitary.longRootHom σ hi).range = 2 ^ g := by
      rw [CFSG.LieType.Universal.Unitary.card_longRootHom_range hi,
        CFSG.LieType.Steinberg.card_traceZero hF]
    have hle2 : 2 ^ g ≤ Nat.card (M0.D.rootGroup β) := by
      rw [← hcard]
      exact Subgroup.card_le_of_le hle
    have h4 : 4 ≤ 2 ^ g := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  exact rckCollinearVia_of_card_ne_two hZ hX hc

end CFSG.StandardType.RCKC1
