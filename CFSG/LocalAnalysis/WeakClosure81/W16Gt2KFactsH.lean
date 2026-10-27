module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUTv
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def kFactsSuProj (hF : Nat.card F = (2 ^ n) ^ 2) (m : ℕ) :
    ↥(SUid (unitaryInvolution F 2 n) m) →* StatedProj (StatedSU m (2 ^ n) F) :=
  (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ n) F))).comp
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)).toMonoidHom

@[expose] noncomputable def kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2) (m : ℕ)
    (e : Fin m → F) (s : F) : StatedProj (StatedSU m (2 ^ n) F) :=
  kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) e s)

theorem kFacts_suProj_surjective (hF : Nat.card F = (2 ^ n) ^ 2) (m : ℕ) :
    Function.Surjective (kFactsSuProj hF m) := by
  unfold kFactsSuProj
  exact (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

theorem kFacts_suProj_eq_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (g g' : ↥(SUid (unitaryInvolution F 2 n) m)) :
    kFactsSuProj hF m g = kFactsSuProj hF m g' ↔
      ∃ u : Fˣ, ((g' : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          ((u : F) • (1 : Matrix (Fin m) (Fin m) F)) := by
  unfold kFactsSuProj
  exact CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSU m (2 ^ n) F)
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF m) g)
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF m) g')

theorem kFacts_card_traceZero (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card {s : F // s + unitaryInvolution F 2 n s = 0} = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h := CFSG.LieType.Steinberg.card_traceZero (F := F) (p := 2) (f := n) hF
  exact (Nat.card_congr (Equiv.subtypeEquivRight
    (fun s => (mem_traceZero (unitaryInvolution F 2 n)).symm))).trans h

theorem kFacts_exists_herm_eq_pair (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e e' : Fin m → F}
    (he : e ≠ 0) (he' : ∀ c : F, e' ≠ c • e) (α β : F) :
    ∃ u : Fin m → F, herm (unitaryInvolution F 2 n) e u = α ∧
      herm (unitaryInvolution F 2 n) e' u = β := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hinv : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have key : ∀ {x y : Fin m → F}, x ≠ 0 → (∀ c : F, y ≠ c • x) →
      ∃ w, herm σ x w = 0 ∧ herm σ y w = 1 := by
    intro x y hx hy
    obtain ⟨u₁, hu₁⟩ := exists_herm_ne_zero σ hx
    set u₀ := (herm σ x u₁)⁻¹ • u₁ with hu₀
    have hu₀x : herm σ x u₀ = 1 := by rw [hu₀, herm_smul_right, inv_mul_cancel₀ hu₁]
    obtain ⟨w, hwx, hwy⟩ : ∃ w, herm σ x w = 0 ∧ herm σ y w ≠ 0 := by
      by_contra hcon
      apply hy (σ (herm σ y u₀))
      have h0 : y - σ (herm σ y u₀) • x = 0 := by
        apply eq_zero_of_herm σ
        intro w
        have h1 : herm σ x (w - herm σ x w • u₀) = 0 := by
          rw [herm_sub_right, herm_smul_right, hu₀x, mul_one, sub_self]
        have h2 : herm σ y (w - herm σ x w • u₀) = 0 := by
          by_contra h
          exact hcon ⟨_, h1, h⟩
        rw [herm_sub_right, herm_smul_right, sub_eq_zero] at h2
        rw [herm_sub_left, herm_smul_left, hinv, h2, mul_comm, sub_self]
      exact sub_eq_zero.mp h0
    refine ⟨(herm σ y w)⁻¹ • w, ?_, ?_⟩
    · rw [herm_smul_right, hwx, mul_zero]
    · rw [herm_smul_right, inv_mul_cancel₀ hwy]
  obtain ⟨w₁, hw₁a, hw₁a'⟩ := key he he'
  have he'0 : e' ≠ 0 := fun h => he' 0 (by rw [h, zero_smul])
  have he'' : ∀ c : F, e ≠ c • e' := by
    intro c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact he (by rw [h, zero_smul])
    exact he' c⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul])
  obtain ⟨w₂, hw₂a', hw₂a⟩ := key he'0 he''
  refine ⟨α • w₂ + β • w₁, ?_, ?_⟩
  · rw [herm_add_right, herm_smul_right, herm_smul_right, hw₂a, hw₁a]
    ring
  · rw [herm_add_right, herm_smul_right, herm_smul_right, hw₂a', hw₁a']
    ring

theorem kFacts_suProjTv_injective (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he0 : e ≠ 0) (he : herm (unitaryInvolution F 2 n) e e = 0) {s s' : F}
    (hs : s + unitaryInvolution F 2 n s = 0) (hs' : s' + unitaryInvolution F 2 n s' = 0)
    (h : kFactsSuProjTv hF m e s = kFactsSuProjTv hF m e s') : s = s' := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  unfold kFactsSuProjTv at h
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF _ _).mp h
  have hact : ∀ v : Fin m → F,
      suTv hσ e s' • v = (u : F) • (suTv hσ e s • v) := by
    intro v
    rw [smul_def, smul_def, hu, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Matrix.mulVec_smul _ _ _
  have h1 : suTv hσ e s' • e = e := by
    rw [suTv_smul hσ he hs', he, mul_zero, zero_smul, add_zero]
  have h2 : suTv hσ e s • e = e := by
    rw [suTv_smul hσ he hs, he, mul_zero, zero_smul, add_zero]
  have hu1 : (u : F) = 1 := by
    have h3 := hact e
    rw [h1, h2] at h3
    have h4 : ((u : F) - 1) • e = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 he0
  obtain ⟨v, hv⟩ := exists_herm_eq_one (unitaryInvolution F 2 n) he0
  have h5 := hact v
  rw [hu1, one_smul, suTv_smul hσ he hs', suTv_smul hσ he hs, hv] at h5
  have h6 := smul_left_injective F he0 (add_left_cancel h5)
  simpa using h6.symm

theorem kFacts_suProj_conj_suProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    (t : ↥(SUid (unitaryInvolution F 2 n) m)) {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) {s : F}
    (hs : s + unitaryInvolution F 2 n s = 0) :
    kFactsSuProj hF m t * kFactsSuProjTv hF m e s * (kFactsSuProj hF m t)⁻¹ =
      kFactsSuProjTv hF m (t • e) s := by
  unfold kFactsSuProjTv
  rw [← map_inv, ← map_mul, ← map_mul,
    suTv_conj (isUnitaryInvolution_unitaryInvolution hF) t he hs]

theorem kFacts_suProjTv_smul_vec (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) {s : F}
    (hs : s + unitaryInvolution F 2 n s = 0) (l : F) :
    kFactsSuProjTv hF m (l • e) s =
      kFactsSuProjTv hF m e (unitaryInvolution F 2 n l * l * s) := by
  unfold kFactsSuProjTv
  rw [suTv_smul_vec (isUnitaryInvolution_unitaryInvolution hF) he hs l]

end CFSG.LocalAnalysis.WeakClosure81
