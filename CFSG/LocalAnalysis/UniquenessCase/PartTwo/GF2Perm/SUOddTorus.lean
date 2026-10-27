module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank Matrix

private structure OddTorusNodes (n : ℕ) where
  k₁ : Fin (n / 2)
  k₂ : Fin (n / 2)
  mid : Fin n
  hk₁ : k₁.val + 1 < n / 2
  hk₂ : k₂ = ⟨k₁.val + 1, hk₁⟩
  hlast : ¬ k₂.val + 1 < n / 2
  hmidrev : Fin.rev mid = mid
  hlow : lowIdx k₁ ≠ lowIdx k₂
  hlowrev : lowIdx k₁ ≠ Fin.rev (lowIdx k₂)
  hrevlow : Fin.rev (lowIdx k₁) ≠ lowIdx k₁
  hmid₁ : mid ≠ lowIdx k₂
  hmid₂ : mid ≠ Fin.rev (lowIdx k₂)
  hsupp : ¬ (mid.val = k₁.val ∨ mid.val = k₁.val + 1 ∨ mid.val = n - 1 - k₁.val ∨
    mid.val = n - 2 - k₁.val)

private def oddTorusNodes {n : ℕ} (hodd : ¬ Even n) (hn : 5 ≤ n) :
    OddTorusNodes n := by
  have hodd' : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
  have hk2 : 2 ≤ n / 2 := by omega
  let k₁ : Fin (n / 2) := ⟨n / 2 - 2, by omega⟩
  let k₂ : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩
  let mid : Fin n := ⟨n / 2, by omega⟩
  have hk₁val : k₁.val = n / 2 - 2 := rfl
  have hk₂val : k₂.val = n / 2 - 1 := rfl
  have hmidval : mid.val = n / 2 := rfl
  have hk₁ : k₁.val + 1 < n / 2 := by rw [hk₁val]; omega
  have hlast : ¬ k₂.val + 1 < n / 2 := by rw [hk₂val]; omega
  have hk₂ : k₂ = ⟨k₁.val + 1, hk₁⟩ := by
    apply Fin.ext
    show k₂.val = k₁.val + 1
    rw [hk₁val, hk₂val]
    omega
  refine ⟨k₁, k₂, mid, hk₁, hk₂, hlast, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [Fin.val_rev, hmidval]
    omega
  · intro h'
    have := congrArg Fin.val h'
    simp only [val_lowIdx, hk₁val, hk₂val] at this
    omega
  · exact lowIdx_ne_rev k₁ k₂
  · exact (lowIdx_ne_rev k₁ k₁).symm
  · intro h'
    have := congrArg Fin.val h'
    simp only [hmidval, val_lowIdx, hk₂val] at this
    omega
  · intro h'
    have := congrArg Fin.val h'
    simp only [hmidval, Fin.val_rev, val_lowIdx, hk₂val] at this
    omega
  · rintro (h' | h' | h' | h') <;> simp only [hmidval, hk₁val] at h' <;> omega

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}
  {Y : Type} [Group Y]

private theorem heisTorusFun_mid {k : Fin (n / 2)} {mid : Fin n}
    (h1 : mid ≠ lowIdx k) (h2 : mid ≠ Fin.rev (lowIdx k)) (hrev : Fin.rev mid = mid)
    {c : F} (hc : c ≠ 0) :
    heisTorusFun (unitaryInvolution F 2 1) (lowIdx k) c mid = c := by
  have hσ : unitaryInvolution F 2 1 c = c ^ 2 := by
    rw [unitaryInvolution_apply]
    norm_num
  rw [heisTorusFun, if_neg h1, if_neg h2, if_pos hrev, hσ, pow_two]
  exact mul_div_cancel_left₀ c hc

private theorem tFun_last_mid {k : Fin (n / 2)} (hlast : ¬ k.val + 1 < n / 2)
    (hn : ¬ Even n) {mid : Fin n} (h1 : mid ≠ lowIdx k) (h2 : mid ≠ Fin.rev (lowIdx k))
    (hrev : Fin.rev mid = mid) {c : F} (hc : c ≠ 0) :
    tFun (unitaryInvolution F 2 1) k c mid = c := by
  unfold tFun
  rw [dite_eq_right hlast, ite_eq_right hn]
  exact heisTorusFun_mid h1 h2 hrev hc

private theorem oddTorus_indep (nodes : OddTorusNodes n) (hodd : ¬ Even n) {ω : Fˣ}
    (hω : orderOf ω = 3)
    {π : SU (unitaryInvolution F 2 1) n →* Y}
    {t₁ z : SU (unitaryInvolution F 2 1) n}
    (ht₁ : mat (unitaryInvolution F 2 1) n t₁ =
      diagonal (tFun (unitaryInvolution F 2 1) nodes.k₁ (ω : F)))
    (hz : mat (unitaryInvolution F 2 1) n z =
      diagonal (tFun (unitaryInvolution F 2 1) nodes.k₂ (ω : F)))
    (hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F)) :
    ∀ i j : ℕ, i < 3 → j < 3 → π t₁ ^ i * π z ^ j = 1 → i = 0 ∧ j = 0 := by
  have hωne : (ω : F) ≠ 0 := ω.ne_zero
  have hω1 : ∀ i : ℕ, i < 3 → (ω : F) ^ i = 1 → i = 0 := fun i hi h' => by
    have h1 : ω ^ i = 1 := Units.ext (by simpa using h')
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at this
    exact Nat.eq_zero_of_dvd_of_lt this hi
  intro i j hi hj hij
  have hzk : t₁ ^ i * z ^ j ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow]
    exact hij
  obtain ⟨u, hu⟩ := hker _ hzk
  have hm : mat (unitaryInvolution F 2 1) n (t₁ ^ i * z ^ j) =
      diagonal (fun s => tFun (unitaryInvolution F 2 1) nodes.k₁ (ω : F) s ^ i *
        tFun (unitaryInvolution F 2 1) nodes.k₂ (ω : F) s ^ j) := by
    rw [map_mul, map_pow, map_pow, ht₁, hz, diagonal_pow, diagonal_pow,
      diagonal_mul_diagonal]
    rfl
  rw [hm] at hu
  have hd := diag_eq_scalar_apply hu
  have ha := hd (lowIdx nodes.k₁)
  rw [tFun_short_self nodes.hk₁,
    tFun_of_last nodes.hlast (s := lowIdx nodes.k₁) nodes.hlow nodes.hlowrev nodes.hrevlow] at ha
  simp only [one_pow, mul_one] at ha
  have hb := hd (lowIdx nodes.k₂)
  rw [show lowIdx nodes.k₂ = lowIdx (n := n) ⟨nodes.k₁.val + 1, nodes.hk₁⟩ by
      rw [nodes.hk₂],
    tFun_short_succ nodes.hk₁, ← nodes.hk₂, tFun_lowIdx_of_last nodes.hlast] at hb
  have hc := hd nodes.mid
  rw [tFun_short_of_not_supp nodes.hk₁ (ω : F) nodes.hsupp,
    tFun_last_mid nodes.hlast hodd nodes.hmid₁ nodes.hmid₂ nodes.hmidrev hωne] at hc
  simp only [one_pow, one_mul] at hc
  have hi0 : i = 0 := by
    have hb' : ((ω : F)⁻¹) ^ i * (ω : F) ^ j = 1 * (ω : F) ^ j := by
      simpa using hb.trans hc.symm
    have h1 : ((ω : F)⁻¹) ^ i = 1 :=
      mul_right_cancel₀ (pow_ne_zero j hωne) hb'
    rw [inv_pow] at h1
    exact hω1 i hi (inv_eq_one.mp h1)
  rw [hi0] at ha
  simp only [pow_zero] at ha
  exact ⟨hi0, hω1 j hj (hc.trans ha.symm)⟩

theorem su_exists_E9_le_borel_odd (hodd : ¬ Even n) (hn : 5 ≤ n)
    {π : SU (unitaryInvolution F 2 1) n →* Y}
    {nn : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 1) n}
    (h : BorelQuotient (rootDatum hF n) nn (levelTorus (unitaryInvolution F 2 1)) π 3)
    (hker : ∀ z ∈ π.ker, ∃ u : Fˣ,
      mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) (u : F)) :
    ∃ E : Subgroup Y,
      E ≤ (parJ (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ∅).map π ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  let nodes := oddTorusNodes hodd hn
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF
  obtain ⟨t₁, ht₁, ht₁m⟩ := exists_short_torus hF nodes.hk₁ ω
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  obtain ⟨z, -, hzm⟩ := exists_heisGen_mem_rankOne (unitaryInvolution_involutive hF) hζ
    (fun _ hx => CFSG.LieType.Universal.Unitary.exists_norm_eq hF hx) nodes.hlast hodd ω
  have hz : z ∈ levelTorus (unitaryInvolution F 2 1) nodes.k₂ :=
    heisGen_mem_levelTorus nodes.hlast hodd ω hzm
  have hzm' : mat (unitaryInvolution F 2 1) n z =
      diagonal (tFun (unitaryInvolution F 2 1) nodes.k₂ (ω : F)) := by
    rw [mat_apply, hzm]
    unfold tFun
    rw [dite_eq_right nodes.hlast, ite_eq_right hodd]
  have h13 : t₁ ^ 3 = 1 := h.torus_pow nodes.k₁ t₁ ht₁
  have h23 : z ^ 3 = 1 := h.torus_pow nodes.k₂ z hz
  have hcomm : Commute t₁ z := h.extras.torus_commute nodes.k₁ nodes.k₂ t₁ ht₁ z hz
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_two_elements (e₁ := π t₁) (e₂ := π z)
    (hcomm.map π) (by rw [← map_pow, h13, map_one]) (by rw [← map_pow, h23, map_one])
    (oddTorus_indep nodes hodd hω ht₁m hzm' hker)
  have ht₁B : t₁ ∈ parJ (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ∅ :=
    borel_le_parJ (D := rootDatum hF n) (H := levelTorus (unitaryInvolution F 2 1)) ∅
      (iSup_le_borel (D := rootDatum hF n) (H := levelTorus (unitaryInvolution F 2 1))
        (Subgroup.mem_iSup_of_mem nodes.k₁ ht₁))
  have hzB : z ∈ parJ (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ∅ :=
    borel_le_parJ (D := rootDatum hF n) (H := levelTorus (unitaryInvolution F 2 1)) ∅
      (iSup_le_borel (D := rootDatum hF n) (H := levelTorus (unitaryInvolution F 2 1))
        (Subgroup.mem_iSup_of_mem nodes.k₂ hz))
  exact ⟨E, hE.trans (sup_le (Subgroup.zpowers_le.2 ⟨t₁, ht₁B, rfl⟩)
    (Subgroup.zpowers_le.2 ⟨z, hzB, rfl⟩)), hel, hcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
