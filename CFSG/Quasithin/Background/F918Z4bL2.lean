module

public import CFSG.Quasithin.Background.F918Z4bAut
public import CFSG.Quasithin.Background.F918Z4bL2Syl
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Adapters.LinearFieldTransport
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner_map_congr)
open scoped MatrixGroups

theorem conj_injective_of_finite_psl2 (K : Type) [Field K] [Finite K] :
    Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) := by
  intro x y h
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  apply pglAction_injective_of_finite K
  rw [pglAction_toPGL, pglAction_toPGL]
  exact h

theorem mulAut_mul_conj_mul_inv_eq_conj {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp [MulAut.conj_apply]

theorem rk_map_congr_inf_inner {L M : Type*} [Group L] [Group M] (e : L ≃* M)
    (E : Subgroup (MulAut L)) :
    rk ↥(E.map (MulAut.congr e).toMonoidHom ⊓ (MulAut.conj : M →* MulAut M).range) =
      rk ↥(E ⊓ (MulAut.conj : L →* MulAut L).range) := by
  have h : E.map (MulAut.congr e).toMonoidHom ⊓ (MulAut.conj : M →* MulAut M).range =
      (E ⊓ (MulAut.conj : L →* MulAut L).range).map (MulAut.congr e).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.congr e).injective]
    exact congrArg _ (inner_map_congr e).symm
  rw [h, rk_map_eq_of_injective _ (MulAut.congr e).injective]

theorem exists_mulEquiv_psl2_galoisField {n : ℕ} (hn : 2 ≤ n) {L : Type} [Group L]
    (h : IsPSL 2 2 n L) : Nonempty (L ≃* PSL2 (GaloisField 2 n)) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 n (by omega) hK)⟩

theorem rk_le_of_isElemAb2_psl2_galoisField {n : ℕ} (hn : 2 ≤ n)
    {E : Subgroup (MulAut (PSL2 (GaloisField 2 n)))} (hE : IsElemAb2 E) : rk E ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective
      (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n))) :=
    conj_injective_of_finite_psl2 _
  set Inn : Subgroup (MulAut (PSL2 (GaloisField 2 n))) := (MulAut.conj :
    PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n))).range with hInn
  have hP : rk (PSL2 (GaloisField 2 n)) = n := by
    unfold rk
    rw [CFSG.Walter.psl2_even_card (by omega)]
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    have hq : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
      have : 2 ∣ (2 ^ n) ^ 2 := dvd_pow hq two_ne_zero
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h4 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    rw [padicValNat.mul (by positivity) h4, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd h1]
    rfl
  have hE0 : rk ↥(E ⊓ Inn) ≤ n :=
    calc rk ↥(E ⊓ Inn) ≤ rk Inn := rk_mono inf_le_right
      _ = rk (PSL2 (GaloisField 2 n)) := (rk_eq_of_mulEquiv (MonoidHom.ofInjective hinj)).symm
      _ = n := hP
  by_cases hEI : E ≤ Inn
  · rwa [inf_eq_left.mpr hEI] at hE0
  ·
    have hlt : rk ↥(E ⊓ Inn) < n := by
      by_contra hge
      have heq : rk ↥(E ⊓ Inn) = n := le_antisymm hE0 (not_lt.mp hge)
      apply hEI
      have hE0le : E ⊓ Inn ≤ Inn := inf_le_right
      have hS₀ : IsElemAb2 ((E ⊓ Inn).comap
          (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n)))) :=
        (hE.mono inf_le_left).comap _ hinj
      have hS₀rk : rk ↥((E ⊓ Inn).comap
          (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n)))) = n := by
        rw [rk_comap_eq_of_le_range _ hinj hE0le, heq]
      obtain ⟨Q, hQ⟩ := hS₀.isPGroup.exists_le_sylow
      have hcardQ : Nat.card (Q : Subgroup (PSL2 (GaloisField 2 n))) = 2 ^ n :=
        (CFSG.Walter.psl2_even_sylow_two hn Q).2
      have hcardS₀ : Nat.card ↥((E ⊓ Inn).comap
          (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n)))) = 2 ^ n := by
        rw [hS₀.card_eq_two_pow, hS₀rk]
      have hQeq : (E ⊓ Inn).comap
          (MulAut.conj : PSL2 (GaloisField 2 n) →* MulAut (PSL2 (GaloisField 2 n))) =
            (Q : Subgroup (PSL2 (GaloisField 2 n))) :=
        Subgroup.eq_of_le_of_card_ge hQ (by rw [hcardQ, hcardS₀])
      have hmem : ∀ x : PSL2 (GaloisField 2 n), x ∈ (Q : Subgroup (PSL2 (GaloisField 2 n))) →
          MulAut.conj x ∈ E := fun x hx => by
        rw [← hQeq] at hx
        exact hx.1
      intro φ hφ
      obtain ⟨s, -, hs⟩ := mulAut_eq_conj_of_fixes_sylow hn Q
        (fun a ha b hb => hinj (by
          rw [map_mul, map_mul]
          exact hE.1 _ (hmem a ha) _ (hmem b hb)))
        φ (fun x hx => hinj (by
          rw [← mulAut_mul_conj_mul_inv_eq_conj φ x]
          have := hE.1 φ hφ _ (hmem x hx)
          rw [this, mul_assoc, mul_inv_cancel, mul_one]))
      exact ⟨s, hs.symm⟩
    have h1 : rk E ≤ rk ↥(E ⊓ Inn) + 1 := rk_le_rk_inf_inner_add_one_psl2 hE
    omega

theorem autRankLe_psl2_two {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n L) : AutRankLe L n := by
  obtain ⟨e⟩ := exists_mulEquiv_psl2_galoisField hn h
  exact AutRankLe.of_mulEquiv e fun E hE => rk_le_of_isElemAb2_psl2_galoisField hn hE

theorem rk_le_rk_inf_inner_add_one {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n L) {E : Subgroup (MulAut L)} (hE : IsElemAb2 E) :
    rk E ≤ rk ↥(E ⊓ (MulAut.conj : L →* MulAut L).range) + 1 := by
  obtain ⟨e⟩ := exists_mulEquiv_psl2_galoisField hn h
  have := rk_le_rk_inf_inner_add_one_psl2 (hE.map (MulAut.congr e).toMonoidHom)
  rwa [rk_map_eq_of_injective _ (MulAut.congr e).injective, rk_map_congr_inf_inner e E] at this

theorem rk_le_one_of_inner_trivial {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n L) {E : Subgroup (MulAut L)} (hE : IsElemAb2 E)
    (hin : ∀ g : L, MulAut.conj g ∈ E → MulAut.conj g = 1) : rk E ≤ 1 := by
  have hbot : E ⊓ (MulAut.conj : L →* MulAut L).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro α ⟨hαE, g, rfl⟩
    exact hin g hαE
  have := rk_le_rk_inf_inner_add_one hn h hE
  rwa [hbot, rk_bot, zero_add] at this

theorem exists_inner_of_two_le_rk {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n L) {E : Subgroup (MulAut L)} (hE : IsElemAb2 E) (hrk : 2 ≤ rk E) :
    ∃ g : L, MulAut.conj g ∈ E ∧ MulAut.conj g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have := rk_le_one_of_inner_trivial hn h hE hcon
  omega

end CFSG.Quasithin
