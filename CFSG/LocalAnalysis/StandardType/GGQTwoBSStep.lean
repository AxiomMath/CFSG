module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoBSStab
import CFSG.LocalAnalysis.StandardType.GGQTwoBSGen
import CFSG.LocalAnalysis.StandardType.GGQTwoBSStepTits

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bsi_blockEmb_index_congr {m k i i' : ℕ} (h : i + k ≤ m) (h' : i' + k ≤ m)
    (hi : i = i') : blockEmb K 2 1 m k i h = blockEmb K 2 1 m k i' h' := by
  subst hi
  rfl

private theorem bsi_comp_blockEmb_eq {n : ℕ} {Y : Type} [Group Y]
    (Φ : Su K 2 1 (n + 2) →* Y) (ψ₀ : Su K 2 1 (n + 1) →* Y)
    (hΦ : Φ.comp (blockEmb K 2 1 (n + 2) (n + 1) 0 (by omega)) = ψ₀)
    {k i : ℕ} (hi : i + k ≤ n + 1) :
    Φ.comp (blockEmb K 2 1 (n + 2) k i (by omega)) =
      ψ₀.comp (blockEmb K 2 1 (n + 1) k i hi) := by
  ext A
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have h1 : blockEmb K 2 1 (n + 2) (n + 1) 0 (by omega)
      (blockEmb K 2 1 (n + 1) k i hi A) =
      blockEmb K 2 1 (n + 2) k i (by omega) A := by
    rw [blockEmb_comp_apply]
    exact DFunLike.congr_fun
      (bsi_blockEmb_index_congr (K := K) (m := n + 2) (k := k) (i := 0 + i) (i' := i)
        (by omega) (by omega) (by omega)) A
  rw [← h1]
  exact DFunLike.congr_fun hΦ _

private theorem bsi_comp_blockEmb2_of_lt {n : ℕ} {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (n + 1)) (ψ₀ : Su K 2 1 (n + 1) →* Y)
    (Φ : Su K 2 1 (n + 2) →* Y)
    (hΦ : Φ.comp (blockEmb K 2 1 (n + 2) (n + 1) 0 (by omega)) = ψ₀)
    (hι : ∀ i : Fin n, ψ₀.comp (blockEmb2 K 2 1 n i) = F.ι i.castSucc)
    {i : Fin (n + 1)} (hi : (i : ℕ) < n) :
    Φ.comp (blockEmb2 K 2 1 (n + 1) i) = F.ι i := by
  have h := bsi_comp_blockEmb_eq (n := n) Φ ψ₀ hΦ (k := 2) (i := (i : ℕ)) (by omega)
  have hcast : (⟨(i : ℕ), hi⟩ : Fin n).castSucc = i := Fin.ext rfl
  simpa [blockEmb2, QTwoPhanFamily.restrict, hcast] using
    h.trans (hι ⟨(i : ℕ), hi⟩)

private theorem bsi_comp_blockEmb3_of_lt {n : ℕ} {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (n + 1)) (ψ₀ : Su K 2 1 (n + 1) →* Y)
    (Φ : Su K 2 1 (n + 2) →* Y)
    (hΦ : Φ.comp (blockEmb K 2 1 (n + 2) (n + 1) 0 (by omega)) = ψ₀)
    (hθ : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ψ₀.comp (blockEmb3 K 2 1 n i h) = F.θ i.castSucc)
    {i : Fin (n + 1)} (hi : (i : ℕ) + 1 < n) :
    Φ.comp (blockEmb3 K 2 1 (n + 1) i (by omega)) = F.θ i := by
  have h := bsi_comp_blockEmb_eq (n := n) Φ ψ₀ hΦ (k := 3) (i := (i : ℕ)) (by omega)
  have hcast : (⟨(i : ℕ), by omega⟩ : Fin n).castSucc = i := Fin.ext rfl
  simpa [blockEmb3, QTwoPhanFamily.restrict, hcast] using
    h.trans (hθ ⟨(i : ℕ), by omega⟩ hi)

private theorem bsi_four_swapAt {n : ℕ} (hn : 5 ≤ n) {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (n + 1)) (Θ : Su K 2 1 4 →* Y)
    (h1 : Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      F.θ ⟨(n - 2) + 1, by omega⟩) :
    Θ (swapAt K 4 2 (by norm_num)) =
      F.ι (Fin.last n) (rotSU (unitaryInvolution K 2 1)) := by
  dsimp only [swapAt]
  have he : blockEmb K 2 1 4 2 2 (by norm_num) (rotSU (unitaryInvolution K 2 1)) =
      blockEmb K 2 1 4 3 1 (by norm_num)
        (embSUid (unitaryInvolution K 2 1) 0 (rotSU (unitaryInvolution K 2 1))) := by
    rw [embSUid_zero_eq_blockEmb, blockEmb_comp_apply]
  rw [he]
  have h1x := DFunLike.congr_fun h1
    (embSUid (unitaryInvolution K 2 1) 0 (rotSU (unitaryInvolution K 2 1)))
  simp only [MonoidHom.comp_apply] at h1x
  rw [h1x]
  have hi1 : (n - 2) + 1 + 1 < n + 1 := by omega
  have hfr := F.right (⟨(n - 2) + 1, by omega⟩ : Fin (n + 1)) hi1
  rw [← MonoidHom.comp_apply, hfr]
  have hidx : (⟨((⟨(n - 2) + 1, by omega⟩ : Fin (n + 1)) : ℕ) + 1, by omega⟩
      : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  rw [hidx]

private theorem bsi_comp_blockEmb_four {n : ℕ} (hn : 5 ≤ n) (hK : Nat.card K = 4)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (n + 1))
    (ψ₀ : Su K 2 1 (n + 1) →* Y) (Φ : Su K 2 1 (n + 2) →* Y)
    (hΦ : Φ.comp (blockEmb K 2 1 (n + 2) (n + 1) 0 (by omega)) = ψ₀)
    (hτ : Φ (swapAt K (n + 2) n (by omega)) =
      F.ι (Fin.last n) (rotSU (unitaryInvolution K 2 1)))
    (hθ : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ψ₀.comp (blockEmb3 K 2 1 n i h) = F.θ i.castSucc)
    (Θ : Su K 2 1 4 →* Y)
    (h0 : Θ.comp (blockEmb K 2 1 4 3 0 (by norm_num)) = F.θ ⟨n - 2, by omega⟩)
    (h1 : Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      F.θ ⟨(n - 2) + 1, by omega⟩) :
    Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)) = Θ := by
  have hle : (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔
      Subgroup.zpowers (swapAt K 4 2 (by norm_num)) ≤
      (Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega))).eqLocus Θ := by
    apply sup_le
    · rintro x ⟨A, rfl⟩
      change (Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)))
          (blockEmb K 2 1 4 3 0 (by norm_num) A) =
        Θ (blockEmb K 2 1 4 3 0 (by norm_num) A)
      have hi0 : (n - 2) + 1 < n := by omega
      have hstep := bsi_comp_blockEmb3_of_lt F ψ₀ Φ hΦ hθ
        (i := (⟨n - 2, by omega⟩ : Fin (n + 1))) hi0
      have hleft : (Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)))
          (blockEmb K 2 1 4 3 0 (by norm_num) A) = F.θ ⟨n - 2, by omega⟩ A := by
        rw [MonoidHom.comp_apply, blockEmb_comp_apply]
        rw [bsi_blockEmb_index_congr (i := (n - 2) + 0) (i' := n - 2) (by omega) (by omega)
          (by omega)]
        exact DFunLike.congr_fun hstep A
      have hright : Θ (blockEmb K 2 1 4 3 0 (by norm_num) A) =
          F.θ ⟨n - 2, by omega⟩ A := DFunLike.congr_fun h0 A
      exact hleft.trans hright.symm
    · apply Subgroup.zpowers_le.mpr
      change (Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)))
          (swapAt K 4 2 (by norm_num)) = Θ (swapAt K 4 2 (by norm_num))
      dsimp only [swapAt]
      rw [MonoidHom.comp_apply, blockEmb_comp_apply]
      have hleft : Φ (blockEmb K 2 1 (n + 2) 2 ((n - 2) + 2) (by omega)
          (rotSU (unitaryInvolution K 2 1))) =
          F.ι (Fin.last n) (rotSU (unitaryInvolution K 2 1)) := by
        rw [bsi_blockEmb_index_congr (i := (n - 2) + 2) (i' := n) (by omega) (by omega)
          (by omega)]
        simpa only [swapAt] using hτ
      have hright := bsi_four_swapAt hn F Θ h1
      exact hleft.trans hright.symm
  have htop : (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔
      Subgroup.zpowers (swapAt K 4 2 (by norm_num)) = ⊤ :=
    range_blockEmb_three_sup_zpowers_swapAt hK
  ext x
  have hx : x ∈ (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔
      Subgroup.zpowers (swapAt K 4 2 (by norm_num)) := by
    rw [htop]
    exact Subgroup.mem_top x
  exact hle hx

private theorem bsi_comp_blockEmb3_last {n : ℕ} (hn : 5 ≤ n) {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (n + 1)) (Φ : Su K 2 1 (n + 2) →* Y)
    (Θ : Su K 2 1 4 →* Y)
    (hΘ : Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)) = Θ)
    (h1 : Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      F.θ ⟨(n - 2) + 1, by omega⟩) :
    Φ.comp (blockEmb3 K 2 1 (n + 1) ⟨n - 1, by omega⟩
      (by change (n - 1) + 1 < n + 1; omega)) =
      F.θ ⟨n - 1, by omega⟩ := by
  have e : (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)).comp
      (blockEmb K 2 1 4 3 1 (by norm_num)) =
      blockEmb3 K 2 1 (n + 1) ⟨n - 1, by omega⟩
      (by change (n - 1) + 1 < n + 1; omega) := by
    simp only [blockEmb3]
    rw [blockEmb_comp]
    exact bsi_blockEmb_index_congr (i := (n - 2) + 1) (i' := n - 1) (by omega) (by omega)
      (by omega)
  rw [← e, ← MonoidHom.comp_assoc, hΘ, h1]
  have hidx : (⟨(n - 2) + 1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ :=
    Fin.ext (by change (n - 2) + 1 = n - 1; omega)
  rw [hidx]

private theorem bsi_comp_blockEmb2_last {n : ℕ} (hn : 5 ≤ n) {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (n + 1)) (Φ : Su K 2 1 (n + 2) →* Y)
    (Θ : Su K 2 1 4 →* Y)
    (hΘ : Φ.comp (blockEmb K 2 1 (n + 2) 4 (n - 2) (by omega)) = Θ)
    (h1 : Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      F.θ ⟨(n - 2) + 1, by omega⟩) :
    Φ.comp (blockEmb2 K 2 1 (n + 1) (Fin.last n)) = F.ι (Fin.last n) := by
  have hedge := bsi_comp_blockEmb3_last (K := K) hn F Φ Θ hΘ h1
  have e : blockEmb2 K 2 1 (n + 1) (Fin.last n) =
      (blockEmb3 K 2 1 (n + 1) ⟨n - 1, by omega⟩
        (by change (n - 1) + 1 < n + 1; omega)).comp (embSUid (unitaryInvolution K 2 1) 0) := by
    rw [blockEmb3_comp_embSUid_zero]
    congr 1
    exact Fin.ext (by change n = (n - 1) + 1; omega)
  rw [e, ← MonoidHom.comp_assoc, hedge]
  have hi1 : (n - 1) + 1 < n + 1 := by omega
  have hfr := F.right (⟨n - 1, by omega⟩ : Fin (n + 1)) hi1
  rw [hfr]
  have hidx : (⟨(n - 1) + 1, by omega⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  rw [hidx]

theorem qTwoPhanUniversalAt_succ (hK : Nat.card K = 4) {n : ℕ} (hn : 5 ≤ n)
    (ih : QTwoPhanUniversalAt K n) : QTwoPhanUniversalAt K (n + 1) := by
  intro Y _ F
  obtain ⟨ψ₀, hι, hθ⟩ := ih F.restrict
  obtain ⟨Φ, hΦ, hτ⟩ := exists_hom_comp_blockEmb_eq hK hn F ψ₀ hι hθ
  have hi0four : (n - 2) + 2 < n + 1 := by omega
  obtain ⟨Θ, h0, h1⟩ := F.four (⟨n - 2, by omega⟩ : Fin (n + 1)) hi0four
  have h1' : Θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      F.θ ⟨(n - 2) + 1, by omega⟩ := h1
  have hΘ := bsi_comp_blockEmb_four hn hK F ψ₀ Φ hΦ hτ hθ Θ h0 h1'
  refine ⟨Φ, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) < n
    · exact bsi_comp_blockEmb2_of_lt F ψ₀ Φ hΦ hι hi
    · have hlast : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      have h := bsi_comp_blockEmb2_last hn F Φ Θ hΘ h1'
      rw [← hlast] at h
      exact h
  · intro i hi
    by_cases hlt : (i : ℕ) + 1 < n
    · exact bsi_comp_blockEmb3_of_lt F ψ₀ Φ hΦ hθ hlt
    · have hlast : i = (⟨n - 1, Nat.lt_succ_of_le (Nat.sub_le n 1)⟩ : Fin (n + 1)) := by
        apply Fin.ext
        change (i : ℕ) = n - 1
        omega
      subst i
      exact bsi_comp_blockEmb3_last hn F Φ Θ hΘ h1'

end CFSG.StandardType.QTwo

end
