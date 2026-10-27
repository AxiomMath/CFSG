module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3SwapCase
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Kern2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem w183k3m2_four_le_card_of_two_le_mRank {D : Subgroup (LGL 2 V)} (h : 2 ≤ mRank D) :
    4 ≤ Nat.card D := by
  have hne : Nat.card D ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, D.one_mem⟩, inferInstance⟩
  have hlog : 2 ≤ Nat.log 2 (Nat.card D) := by simpa only [mRank] using h
  have hpow : 2 ^ 2 ≤ Nat.card D := Nat.pow_le_of_le_log hne hlog
  simpa using hpow

theorem w183k3m2_mOf_le_mRank {A B : Subgroup (LGL 2 V)} (hBA : B ≤ A) : mOf A B ≤ mRank A := by
  unfold mOf mRank
  apply Nat.log_mono_right
  rw [← Subgroup.index_bot]
  exact Subgroup.index_antitone (show (⊥ : Subgroup ↥A) ≤ B.subgroupOf A from bot_le)

theorem w183k3m2_card_eq_four_of_mRank_eq_two {D : Subgroup (LGL 2 V)}
    (hel : IsElemAbelian 2 D) (h : mRank D = 2) : Nat.card D = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hel.isPGroup)
  have hlog : Nat.log 2 (2 ^ n) = 2 := by rw [← hn]; simpa only [mRank] using h
  have hn2 : n = 2 := by
    have := hlog
    rw [Nat.log_pow (by norm_num : 1 < 2)] at this
    exact this
  rw [hn, hn2]
  norm_num

theorem w183k3m2_mem_normalizer (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br3TwoComp Y T L₁ L₂) (hall : ∀ D ∈ Γ, 2 ≤ mRank D) {D : Subgroup (LGL 2 V)}
    (hD : D ∈ Γ) :
    D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ∧
      D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  have h4 : 4 ≤ Nat.card D := w183k3m2_four_le_card_of_two_le_mRank (hall D hD)
  refine ⟨?_, ?_⟩ <;> intro d hd
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases htwo.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exact (w183k3_false_of_swap_common hc htwo hD h4 hd h1).elim
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases htwo.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · exact (w183k3_false_of_swap_common hc htwo hD h4 hd h1).elim

theorem w183k3m2_three_le_mOf_or (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br3TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) (hrk : 3 ≤ mRank D) :
    3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
  by_contra hcon
  have hm₁ : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inl h))
  have hm₂ : mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inr h))
  have hn₁ := (w183k3m2_mem_normalizer hc htwo hall hD).1
  have hn₂ := (w183k3m2_mem_normalizer hc htwo hall hD).2
  have hle := hc.h131.le_G D hD
  have hel := hc.h131.isElemAb D hD
  have hi : 2 ≤ m - i₀ - 1 := by have := hc.hmi; omega
  have hAn₁ : ∀ a ∈ D, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hn₁ ha) l).mp hl
  have hAn₂ : ∀ a ∈ D, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hn₂ ha) l).mp hl
  have hDne : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₁
    omega
  have hFne : (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₂
    omega
  have hDF : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ⊓
      (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨⟨hyA, hyC₁⟩, -, hyC₂⟩ := hy
    refine htwo.eq_one_of_isPGroup_cent (hle hyA) (k := 1) (by simpa using hel.2 y hyA) ?_ ?_
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₁ l hl).symm
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₂ l hl).symm
  exact hc.h131.false_of_two_kernels_quasi hD htwo.le₁ htwo.le₂ htwo.quasi₁ htwo.quasi₂
    htwo.odd₁ htwo.odd₂ htwo.comm hAn₁ hAn₂ rfl rfl hDne hFne hDF (hm₁.trans hi)

theorem w183k3m2_centralizer_cj (g : LGL 2 V) (S : Subgroup (LGL 2 V)) :
    (Subgroup.centralizer (S : Set (LGL 2 V))).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  rw [CFSG.Walter.map_centralizer_mulEquiv, cj, Subgroup.coe_map]
  simp only [MulEquiv.coe_toMonoidHom]

theorem w183k3m2_not_centralizes_cj {g : LGL 2 V} {D S : Subgroup (LGL 2 V)}
    (h : ¬ D ≤ Subgroup.centralizer (S : Set (LGL 2 V))) :
    ¬ cj g D ≤ Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  intro hle
  apply h
  calc D = cj g⁻¹ (cj g D) := (cj_self_inv g D).symm
    _ ≤ cj g⁻¹ (Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V))) :=
      Subgroup.map_mono hle
    _ = Subgroup.centralizer ((cj g⁻¹ (cj g S) : Subgroup (LGL 2 V)) : Set (LGL 2 V)) :=
      w183k3m2_centralizer_cj g⁻¹ (cj g S)
    _ = Subgroup.centralizer (S : Set (LGL 2 V)) := by rw [cj_self_inv]

theorem w183k3m2_exists_conj_le_T {D : Subgroup (LGL 2 V)} (hSY : IsSylowIn 2 T Y)
    (hDY : D ≤ Y) (hD2 : IsPGroup 2 D) : ∃ y ∈ Y, cj y D ≤ T :=
  exists_conj_le_of_isSylowTwoOf (A := D) hSY hDY hD2

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
