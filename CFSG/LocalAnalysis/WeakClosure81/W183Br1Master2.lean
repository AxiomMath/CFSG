module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rows
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1I2Free
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1AlphaShapes
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Close
public import CFSG.LocalAnalysis.WeakClosure81.W183L39Main
import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.LocalAnalysis.WeakClosure81.W183B2OneSided
public import CFSG.LocalAnalysis.WeakClosure81.W183B2TwoSided

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem w183_twoComp_symm {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br2TwoComp Y T L₁ L₂) :
    Br2TwoComp Y T L₂ L₁ := by
  refine
    { le₁ := htwo.le₂
      le₂ := htwo.le₁
      simple₁ := htwo.simple₂
      simple₂ := htwo.simple₁
      nonab₁ := htwo.nonab₂
      nonab₂ := htwo.nonab₁
      comm := fun a ha b hb => (htwo.comm b hb a ha).symm
      ne := htwo.ne.symm
      perm := ?_
      swap := ?_
      cent := fun y hy h₂ h₁ => htwo.cent y hy h₁ h₂
      gen := ?_ }
  · intro y hy
    rcases htwo.perm y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · obtain ⟨x, hxT, hx⟩ := htwo.swap
    exact ⟨x⁻¹, T.inv_mem hxT, by rw [← hx]; exact cj_self_inv x L₁⟩
  · intro y hy
    obtain ⟨l, hl, t, ht, rfl⟩ := htwo.gen y hy
    exact ⟨l, by rw [sup_comm]; exact hl, t, ht, rfl⟩

private theorem w183_master2_four_le_card_of_two_le_mRank {D : Subgroup (LGL 2 V)}
    (h : 2 ≤ mRank D) : 4 ≤ Nat.card D := by
  have hne : Nat.card D ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, D.one_mem⟩, inferInstance⟩
  have hlog : 2 ≤ Nat.log 2 (Nat.card D) := by simpa only [mRank] using h
  have hpow : 2 ^ 2 ≤ Nat.card D := Nat.pow_le_of_le_log hne hlog
  simpa using hpow

private theorem w183_master2_mOf_le_mRank {A B : Subgroup (LGL 2 V)} (hBA : B ≤ A) :
    mOf A B ≤ mRank A := by
  unfold mOf mRank
  apply Nat.log_mono_right
  rw [← Subgroup.index_bot]
  exact Subgroup.index_antitone (show (⊥ : Subgroup ↥A) ≤ B.subgroupOf A from bot_le)

private noncomputable def w183_master2_swapEquiv (hL : Br2TwoComp Y T L₁ L₂) : ↥L₁ ≃* ↥L₂ :=
  (Subgroup.equivMapOfInjective L₁ (MulAut.conj (Classical.choose hL.swap)).toMonoidHom
      (MulAut.conj (Classical.choose hL.swap)).injective).trans
    (MulEquiv.subgroupCongr
      (show L₁.map (MulAut.conj (Classical.choose hL.swap)).toMonoidHom = L₂ from
        (Classical.choose_spec hL.swap).2))

private theorem w183_master2_shape_swap (hL : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsU3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨
      IsAlt ↥L₁ 6) :
    IsL2 ↥L₂ 2 ∨ IsL3 ↥L₂ 2 ∨ IsU3 ↥L₂ 2 ∨ IsSp4 ↥L₂ 2 ∨ IsL3 ↥L₂ 1 ∨ IsAlt ↥L₂ 6 := by
  let e := w183_master2_swapEquiv hL
  rcases hshape with h | h | h | h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))))
  · rcases h with ⟨f⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩))))

private theorem w183_master2_mem_normalizer (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂) (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) :
    D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ∧
      D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  have h4 : 4 ≤ Nat.card D := w183_master2_four_le_card_of_two_le_mRank (hall D hD)
  refine ⟨?_, ?_⟩ <;> intro d hd
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases hL.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exact (w183l39_false_of_swap_common hc hL hD h4 hd h1).elim
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases hL.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · exact (w183l39_false_of_swap_common hc hL hD h4 hd h1).elim

private theorem w183_master2_shape_small_swap (hL : Br2TwoComp Y T L₁ L₂)
    (h : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 1) : IsL2 ↥L₂ 2 ∨ IsL3 ↥L₂ 1 := by
  let e := w183_master2_swapEquiv hL
  rcases h with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)

private theorem w183_master2_rank3_small (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 1)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) (hne : Γ.Nonempty)
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) : False := by
  obtain ⟨D₀, hD₀⟩ := hne
  have hn₁ := (w183_master2_mem_normalizer hB htwo hall hD₀).1
  have hn₂ := (w183_master2_mem_normalizer hB htwo hall hD₀).2
  have hel := hB.h131.isElemAb D₀ hD₀
  have hle := hB.h131.le_G D₀ hD₀
  have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
  by_cases h3₁ : 3 ≤ mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
  · exact (br1_rank_false_two rows.rk2 htwo hshape hle hn₁ hel h3₁).elim
  by_cases h3₂ : 3 ≤ mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
  · exact (br1_rank_false_two rows.rk2 (w183_twoComp_symm htwo)
      (w183_master2_shape_small_swap htwo hshape) hle hn₂ hel h3₂).elim
  have hm₁ : mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 := not_lt.1 h3₁
  have hm₂ : mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 := not_lt.1 h3₂
  have hDne : (D₀ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₁
    have := hrk D₀ hD₀
    omega
  have hFne : (D₀ ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₂
    have := hrk D₀ hD₀
    omega
  haveI := htwo.simple₁
  haveI := htwo.simple₂
  refine Assumption131.false_of_two_kernels hB.h131 hD₀ htwo.le₁ htwo.le₂ htwo.nonab₁
    htwo.nonab₂ htwo.comm ?_ ?_ rfl rfl hDne hFne ?_ (hm₁.trans hi)
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₁ ha) l).mp hl
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₂ ha) l).mp hl
  · rw [eq_bot_iff]
    rintro y ⟨⟨hyA, hy₁⟩, -, hy₂⟩
    exact Subgroup.mem_bot.mpr (htwo.cent y (hle hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₂ l hl).symm))

private theorem w183_master2_centralizer_cj (g : LGL 2 V) (S : Subgroup (LGL 2 V)) :
    (Subgroup.centralizer (S : Set (LGL 2 V))).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  rw [CFSG.Walter.map_centralizer_mulEquiv, cj, Subgroup.coe_map]
  simp only [MulEquiv.coe_toMonoidHom]

private theorem w183_master2_not_centralizes_cj' {g : LGL 2 V} {D S : Subgroup (LGL 2 V)}
    (h : ¬ D ≤ Subgroup.centralizer (S : Set (LGL 2 V))) :
    ¬ cj g D ≤ Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V)) := by
  intro hle
  apply h
  calc D = cj g⁻¹ (cj g D) := (cj_self_inv g D).symm
    _ ≤ cj g⁻¹ (Subgroup.centralizer ((cj g S : Subgroup (LGL 2 V)) : Set (LGL 2 V))) :=
      Subgroup.map_mono hle
    _ = Subgroup.centralizer ((cj g⁻¹ (cj g S) : Subgroup (LGL 2 V)) : Set (LGL 2 V)) :=
      w183_master2_centralizer_cj g⁻¹ (cj g S)
    _ = Subgroup.centralizer (S : Set (LGL 2 V)) := by rw [cj_self_inv]

private theorem w183_master2_exists_conj_le_T {D : Subgroup (LGL 2 V)}
    (hSY : IsSylowIn 2 T Y) (hDY : D ≤ Y) (hD2 : IsPGroup 2 D) :
    ∃ y ∈ Y, cj y D ≤ T :=
  exists_conj_le_of_isSylowTwoOf (A := D) hSY hDY hD2

private theorem w183_master2_three_le_mOf_or (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂) (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hrk : 3 ≤ mRank D) :
    3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
  by_contra hcon
  have hm₁ : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inl h))
  have hm₂ : mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inr h))
  have hn₁ := (w183_master2_mem_normalizer hB htwo hall hD).1
  have hn₂ := (w183_master2_mem_normalizer hB htwo hall hD).2
  have hle := hB.h131.le_G D hD
  have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
  have hDne : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₁
    omega
  have hFne : (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₂
    omega
  haveI := htwo.simple₁
  haveI := htwo.simple₂
  refine Assumption131.false_of_two_kernels hB.h131 hD htwo.le₁ htwo.le₂ htwo.nonab₁
    htwo.nonab₂ htwo.comm ?_ ?_ rfl rfl hDne hFne ?_ (hm₁.trans hi)
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₁ ha) l).mp hl
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₂ ha) l).mp hl
  · rw [eq_bot_iff]
    rintro y ⟨⟨hyA, hy₁⟩, -, hy₂⟩
    exact Subgroup.mem_bot.mpr (htwo.cent y (hle hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₂ l hl).symm))

private theorem w183_master2_rank3_big (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL3 ↥L₁ 2 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) (hne : Γ.Nonempty)
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D)
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    (h5 : IsSp4 ↥L₁ 2 → ∀ D ∈ Γ, ∀ P : Subgroup (LGL 2 V),
      IsSylowIn 5 P (Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V))) → IsCyclic ↥P) :
    False := by
  by_cases hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  · exact br2_false_of_one_sided hB htwo
      (fun D hD => (w183_master2_mem_normalizer hB htwo hall hD).1)
      hone hrk hne hshape rows.h65f rows.g4l34 rows.g4a6 h5 rows.sp5
  · obtain ⟨D, hDnot⟩ := not_forall.1 hone
    have hD : D ∈ Γ := by
      by_contra h
      exact hDnot (fun hmem => absurd hmem h)
    have hDnot' : ¬ (D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := fun hp => hDnot (fun _ => hp)
    have hDnot₁ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
      fun h => hDnot' (Or.inl h)
    have hDnot₂ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
      fun h => hDnot' (Or.inr h)
    have hD2 : IsPGroup 2 D := (hB.h131.isElemAb D hD).isPGroup
    obtain ⟨y, hyY, hyDT⟩ := w183_master2_exists_conj_le_T hB.sylow (hB.h131.le_G D hD) hD2
    have hD'mem : cj y D ∈ Γ := hB.h131.invariant D hD y hyY
    have hD'3 := w183_master2_three_le_mOf_or hB htwo hall hD'mem (hrk (cj y D) hD'mem)
    have hD'₁ : ¬ cj y D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rcases htwo.perm y hyY with ⟨hyL₁, hyL₂⟩ | ⟨hyL₁, hyL₂⟩
      · have := w183_master2_not_centralizes_cj' (g := y) (D := D) (S := L₂) hDnot₂
        rwa [hyL₂] at this
      · have := w183_master2_not_centralizes_cj' (g := y) (D := D) (S := L₁) hDnot₁
        rwa [hyL₁] at this
    have hD'₂ : ¬ cj y D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      rcases htwo.perm y hyY with ⟨hyL₁, hyL₂⟩ | ⟨hyL₁, hyL₂⟩
      · have := w183_master2_not_centralizes_cj' (g := y) (D := D) (S := L₁) hDnot₁
        rwa [hyL₁] at this
      · have := w183_master2_not_centralizes_cj' (g := y) (D := D) (S := L₂) hDnot₂
        rwa [hyL₂] at this
    exact br2_false_of_two_sided hB htwo
      (fun D hD => (w183_master2_mem_normalizer hB htwo hall hD).1)
      hED hD'mem hyDT hD'₁ hD'₂ hD'3 hshape rows.g11

private theorem w183_master2_card_eq_four_of_mRank_eq_two {D : Subgroup (LGL 2 V)}
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

private theorem w183_master2_isL2_of_alpha_left (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    (hτ : (IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 2) →
      ∃ τ ∈ T, ActsOnDynkinMod ⊥ L₁ τ)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hcard : Nat.card D = 4)
    (hker₁ : D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hcent₂ : D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) :
    IsL2 ↥L₁ 2 := by
  have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
  have hrank : mRank D ≤ m - i₀ - 1 := by
    have h2 : mRank D = 2 := by rw [mRank, hcard]; norm_num
    omega
  let c : Br1Alpha Y T L₁ L₂ D Γ VA (m - i₀ - 1) :=
    { h := hB.h131
      vfix := hB.vfix
      two := htwo
      mem := hD
      rank := hrank
      card := hcard
      norm₁ := (w183_master2_mem_normalizer hB htwo hall hD).1
      ker₁ := hker₁
      cent₂ := hcent₂ }
  have hτY : (IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 2) →
      ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L₁ τ := by
    intro hh
    obtain ⟨τ, hτT, hτd⟩ := hτ hh
    exact ⟨τ, hB.sylow.1 hτT, hτd⟩
  rcases hshape with h | h | h | h | h
  · exact h
  · exact (br1_alpha_false_L34 rows.h65f rows.g1 c h).elim
  · exact (br1_alpha_false_Sp44 rows.sp c h (hτY (Or.inr (Or.inr (Or.inl h))))).elim
  · exact (br1_alpha_false_L32 rows.l32 c h (hτY (Or.inl h))).elim
  · exact (br1_alpha_false_A6 rows.a6 c h (hτY (Or.inr (Or.inl h)))).elim

private theorem w183_master2_isL2_of_rank_two (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    (hτ : (IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 2) →
      ∃ τ ∈ T, ActsOnDynkinMod ⊥ L₁ τ)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hcard : Nat.card D = 4)
    (hconfig : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
      (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) :
    IsL2 ↥L₁ 2 := by
  rcases hconfig with ⟨hker₁, hcent₂⟩ | ⟨hker₂, hcent₁⟩
  · exact w183_master2_isL2_of_alpha_left rows hB htwo hall hτ hshape hD hcard hker₁ hcent₂
  · obtain ⟨x, hxT, hxL⟩ := htwo.swap
    have hxY : x ∈ Y := hB.sylow.1 hxT
    have hxL₂ : cj x L₂ = L₁ := by
      rcases htwo.perm x hxY with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (h1.symm.trans hxL) htwo.ne
      · exact h2
    have hcard' : Nat.card (cj x D) = 4 := by
      rw [cj, Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hcard
    have hker₁' : cj x D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ := by
      have hmap : Subgroup.centralizer (L₁ : Set (LGL 2 V)) =
          (Subgroup.centralizer (L₂ : Set (LGL 2 V))).map (MulAut.conj x).toMonoidHom := by
        rw [w183_master2_centralizer_cj x L₂, hxL₂]
      rw [hmap, cj, ← Subgroup.map_inf D (Subgroup.centralizer (L₂ : Set (LGL 2 V)))
        (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hker₂, Subgroup.map_bot]
    have hcent₂' : cj x D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      have hmap : Subgroup.centralizer (L₂ : Set (LGL 2 V)) =
          (Subgroup.centralizer (L₁ : Set (LGL 2 V))).map (MulAut.conj x).toMonoidHom := by
        rw [w183_master2_centralizer_cj x L₁, hxL]
      rw [hmap]
      exact Subgroup.map_mono hcent₁
    exact w183_master2_isL2_of_alpha_left rows hB htwo hall hτ hshape
      (hB.h131.invariant D hD x hxY) hcard' hker₁' hcent₂'

private theorem w183_master2_member_le_of_config (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    (hL1 : IsL2 ↥L₁ 2) (hL2 : IsL2 ↥L₂ 2)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hcard : Nat.card D = 4)
    (hconfig : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
      (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) :
    D ≤ L₁ ∨ D ≤ L₂ := by
  have hrank : mRank D ≤ m - i₀ - 1 := by
    have h2 : mRank D = 2 := by rw [mRank, hcard]; norm_num
    have := hB.hmi; omega
  rcases hconfig with ⟨hker₁, hcent₂⟩ | ⟨hker₂, hcent₁⟩
  · let c : Br1Alpha Y T L₁ L₂ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2_mem_normalizer hB htwo hall hD).1
        ker₁ := hker₁
        cent₂ := hcent₂ }
    exact Or.inl (br1_alpha_sylow_L24 rows.a5 c hL1).le
  · let c : Br1Alpha Y T L₂ L₁ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := w183_twoComp_symm htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2_mem_normalizer hB htwo hall hD).2
        ker₁ := hker₂
        cent₂ := hcent₁ }
    exact Or.inr (br1_alpha_sylow_L24 rows.a5 c hL2).le

private theorem w183_master2_normalizer_normal (htwo : Br2TwoComp Y T L₁ L₂) :
    ((Y ⊓ Subgroup.normalizer (L₁ : Set (LGL 2 V))).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnY, hnN⟩ := Subgroup.mem_inf.mp hn
  change (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈
    Y ⊓ Subgroup.normalizer (L₁ : Set (LGL 2 V))
  refine ⟨Y.mul_mem (Y.mul_mem g.2 hnY) (Y.inv_mem g.2), ?_⟩
  show (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈
    Subgroup.normalizer (L₁ : Set (LGL 2 V))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rcases htwo.perm (g : LGL 2 V) g.2 with ⟨hgL₁, hgL₂⟩ | ⟨hgL₁, hgL₂⟩
  · have hgN : (g : LGL 2 V) ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgL₁
    have hgn : cj (g : LGL 2 V)⁻¹ L₁ = L₁ := by
      have := cj_self_inv (g : LGL 2 V) L₁
      rwa [hgL₁] at this
    have hng : cj (n : LGL 2 V) L₁ = L₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
    calc cj ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) L₁
        = cj (g : LGL 2 V) (cj (n : LGL 2 V) (cj (g : LGL 2 V)⁻¹ L₁)) := by
          rw [← cj_cj, ← cj_cj]
      _ = cj (g : LGL 2 V) L₁ := by rw [hgn, hng]
      _ = L₁ := hgL₁
  · have hnN₂ : (n : LGL 2 V) ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
      (Br2TwoComp.mem_normalizer_iff htwo hnY).mp hnN
    have hng : cj (n : LGL 2 V) L₂ = L₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN₂
    have hgn : cj (g : LGL 2 V)⁻¹ L₁ = L₂ := by
      have := cj_self_inv (g : LGL 2 V) L₂
      rwa [hgL₂] at this
    calc cj ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) L₁
        = cj (g : LGL 2 V) (cj (n : LGL 2 V) (cj (g : LGL 2 V)⁻¹ L₁)) := by
          rw [← cj_cj, ← cj_cj]
      _ = cj (g : LGL 2 V) L₂ := by rw [hgn, hng]
      _ = L₁ := hgL₂

private theorem w183_master2_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

private theorem w183_master2_sylow_T_inf_L1 (hSY : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) : IsSylowIn 2 (T ⊓ L₁) L₁ := by
  let Y₀ : Subgroup (LGL 2 V) := Y ⊓ Subgroup.normalizer (L₁ : Set (LGL 2 V))
  have hY₀n : (Y₀.subgroupOf Y).Normal := w183_master2_normalizer_normal htwo
  have hY₀le : Y₀ ≤ Y := inf_le_left
  have hSyl : IsSylowIn 2 (T ⊓ Y₀) Y₀ := hSY.inf_normal hY₀le hY₀n
  have hL₁Y₀ : L₁ ≤ Y₀ := fun x hx => ⟨htwo.le₁ hx, Subgroup.le_normalizer hx⟩
  have hL₁n : (L₁.subgroupOf Y₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹ ∈ L₁
    have hgN : (g : LGL 2 V) ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
      (Subgroup.mem_inf.mp g.2).2
    exact (Subgroup.mem_normalizer_iff.mp hgN (n : LGL 2 V)).mp hn
  have h := hSyl.inf_normal hL₁Y₀ hL₁n
  rwa [inf_assoc, inf_eq_right.mpr hL₁Y₀] at h

private theorem w183_master2_inf_L1_mem (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂) (hSyl : IsSylowIn 2 (T ⊓ L₁) L₁)
    {D₁ : Subgroup (LGL 2 V)} (hD₁ : D₁ ∈ Γ) (hD₁syl : IsSylowIn 2 D₁ L₁) :
    T ⊓ L₁ ∈ Γ := by
  haveI : Finite (LGL 2 V) := w183_master2_finite_lgl
  obtain ⟨l, hl, hle⟩ :=
    exists_conj_le_of_isSylowTwoOf (A := D₁) hSyl hD₁syl.le hD₁syl.isPGroup
  have hcard : Nat.card ↥(cj l D₁) = Nat.card ↥D₁ :=
    Subgroup.card_map_of_injective (MulAut.conj l).injective
  have hcardS : Nat.card ↥(T ⊓ L₁) = Nat.card ↥D₁ := by
    rw [hSyl.card_eq, hD₁syl.card_eq]
  have heq : cj l D₁ = T ⊓ L₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, ← hcard])
  rw [← heq]
  exact hB.h131.invariant D₁ hD₁ l (htwo.le₁ hl)

private theorem w183_master2_isL2_swap (hL : Br2TwoComp Y T L₁ L₂) (h : IsL2 ↥L₁ 2) :
    IsL2 ↥L₂ 2 :=
  CFSG.Blueprint.LieModel.of_mulEquiv (w183_master2_swapEquiv hL) h

private theorem w183_master2_isSylowIn_cj {P H : Subgroup (LGL 2 V)} (g : LGL 2 V)
    (h : IsSylowIn 2 P H) : IsSylowIn 2 (cj g P) (cj g H) := by
  refine ⟨Subgroup.map_mono h.le, h.isPGroup.map _, ?_⟩
  have hidx : (cj g P).relIndex (cj g H) = P.relIndex H :=
    Subgroup.relIndex_map_map_of_injective P H (MulAut.conj g).injective
  rw [hidx]
  exact h.not_dvd_relIndex

private theorem w183_master2_sylow_member_of_config (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    (hL1 : IsL2 ↥L₁ 2) (hL2 : IsL2 ↥L₂ 2)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hcard : Nat.card D = 4)
    (hconfig : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
      (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) :
    IsSylowIn 2 D L₁ ∨ IsSylowIn 2 D L₂ := by
  have hrank : mRank D ≤ m - i₀ - 1 := by
    have h2 : mRank D = 2 := by rw [mRank, hcard]; norm_num
    have := hB.hmi; omega
  rcases hconfig with ⟨hker₁, hcent₂⟩ | ⟨hker₂, hcent₁⟩
  · let c : Br1Alpha Y T L₁ L₂ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2_mem_normalizer hB htwo hall hD).1
        ker₁ := hker₁
        cent₂ := hcent₂ }
    exact Or.inl (br1_alpha_sylow_L24 rows.a5 c hL1)
  · let c : Br1Alpha Y T L₂ L₁ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := w183_twoComp_symm htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2_mem_normalizer hB htwo hall hD).2
        ker₁ := hker₂
        cent₂ := hcent₁ }
    exact Or.inr (br1_alpha_sylow_L24 rows.a5 c hL2)

theorem br1_master_two (rows : Br1Rows) {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6)
    (hτ : (IsL3 ↥L₁ 1 ∨ IsAlt ↥L₁ 6 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 2) → ∃ τ ∈ T, ActsOnDynkinMod ⊥ L₁ τ)
    (hne : Γ.Nonempty) (hall : ∀ D ∈ Γ, 2 ≤ mRank D)
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED)
    (hPT : IsSp4 ↥L₁ 2 → PairTest Y Γ)
    (h5 : IsSp4 ↥L₁ 2 → ∀ D ∈ Γ, ∀ P : Subgroup (LGL 2 V),
      IsSylowIn 5 P (Y ⊓ Subgroup.normalizer (D : Set (LGL 2 V))) → IsCyclic ↥P) : False := by
  by_cases hrk : ∀ D ∈ Γ, 3 ≤ mRank D
  · rcases hshape with h | h | h | h | h
    · exact w183_master2_rank3_small rows hB htwo (Or.inl h) hall hne hrk
    · exact w183_master2_rank3_big rows hB htwo (Or.inl h) hall hne hrk hED h5
    · exact w183_master2_rank3_big rows hB htwo (Or.inr (Or.inr h)) hall hne hrk hED h5
    · exact w183_master2_rank3_small rows hB htwo (Or.inr h) hall hne hrk
    · exact w183_master2_rank3_big rows hB htwo (Or.inr (Or.inl h)) hall hne hrk hED h5
  · obtain ⟨D₀, hD₀not⟩ := not_forall.1 hrk
    have hD₀ : D₀ ∈ Γ := by
      by_contra h
      exact hD₀not (fun hmem => absurd hmem h)
    have hD₀not' : ¬ 3 ≤ mRank D₀ := fun h => hD₀not (fun _ => h)
    have hrank₀ : mRank D₀ = 2 := by have := hall D₀ hD₀; omega
    have hcard₀ : Nat.card D₀ = 4 :=
      w183_master2_card_eq_four_of_mRank_eq_two (hB.h131.isElemAb D₀ hD₀) hrank₀
    have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
    have hshape₁6 : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsU3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨
        IsAlt ↥L₁ 6 := by
      rcases hshape with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have hshape₂6 := w183_master2_shape_swap htwo hshape₁6
    have hm₀₁ : mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 := by
      exact (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank₀)
    have hm₀₂ : mOf D₀ (D₀ ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 := by
      exact (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank₀)
    have hI2 := br1_I2_member_free rows.g3 hB.h131 hB.vfix hi htwo hshape₁6 hshape₂6 hD₀
      (w183_master2_four_le_card_of_two_le_mRank (hall D₀ hD₀))
      (w183_master2_mem_normalizer hB htwo hall hD₀).1
      (w183_master2_mem_normalizer hB htwo hall hD₀).2 hm₀₁ hm₀₂
    have hL1 : IsL2 ↥L₁ 2 :=
      w183_master2_isL2_of_rank_two rows hB htwo hall hτ hshape hD₀ hcard₀ hI2.2
    have hL2 : IsL2 ↥L₂ 2 := w183_master2_isL2_swap htwo hL1
    have hmem : ∀ D ∈ Γ, 2 < Nat.card D → D ≤ L₁ ∨ D ≤ L₂ := by
      intro D hD hcard
      by_cases h3 : 3 ≤ mRank D
      · have h3' := w183_master2_three_le_mOf_or hB htwo hall hD h3
        rcases h3' with h3₁ | h3₂
        · exact (br1_rank_false_two rows.rk2 htwo (Or.inl hL1) (hB.h131.le_G D hD)
            (w183_master2_mem_normalizer hB htwo hall hD).1 (hB.h131.isElemAb D hD) h3₁).elim
        · exact (br1_rank_false_two rows.rk2 (w183_twoComp_symm htwo) (Or.inl hL2)
            (hB.h131.le_G D hD) (w183_master2_mem_normalizer hB htwo hall hD).2
            (hB.h131.isElemAb D hD) h3₂).elim
      · have hrankD : mRank D = 2 := by have := hall D hD; omega
        have hcardD : Nat.card D = 4 :=
          w183_master2_card_eq_four_of_mRank_eq_two (hB.h131.isElemAb D hD) hrankD
        have hmD₁ : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 := by
          exact (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrankD)
        have hmD₂ : mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 := by
          exact (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrankD)
        have hI2D := br1_I2_member_free rows.g3 hB.h131 hB.vfix hi htwo (Or.inl hL1) (Or.inl hL2)
          hD (w183_master2_four_le_card_of_two_le_mRank (hall D hD))
          (w183_master2_mem_normalizer hB htwo hall hD).1
          (w183_master2_mem_normalizer hB htwo hall hD).2 hmD₁ hmD₂
        exact w183_master2_member_le_of_config rows hB htwo hall hL1 hL2 hD hcardD hI2D.2
    have hD₀syl := w183_master2_sylow_member_of_config rows hB htwo hall hL1 hL2 hD₀ hcard₀ hI2.2
    obtain ⟨D₁, hD₁mem, hD₁syl, hD₁card⟩ : ∃ D₁ ∈ Γ, IsSylowIn 2 D₁ L₁ ∧ Nat.card D₁ = 4 := by
      rcases hD₀syl with hsyl | hsyl
      · exact ⟨D₀, hD₀, hsyl, hcard₀⟩
      · obtain ⟨x, hxT, hxL⟩ := htwo.swap
        have hxY : x ∈ Y := hB.sylow.1 hxT
        have hxL₂ : cj x L₂ = L₁ := by
          rcases htwo.perm x hxY with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd (h1.symm.trans hxL) htwo.ne
          · exact h2
        refine ⟨cj x D₀, hB.h131.invariant D₀ hD₀ x hxY, ?_, ?_⟩
        · have h := w183_master2_isSylowIn_cj x hsyl
          rwa [hxL₂] at h
        · rw [cj, Subgroup.card_map_of_injective (MulAut.conj x).injective]
          exact hcard₀
    have hSylT : IsSylowIn 2 (T ⊓ L₁) L₁ := w183_master2_sylow_T_inf_L1 hB.sylow htwo
    have hS : T ⊓ L₁ ∈ Γ := w183_master2_inf_L1_mem hB htwo hSylT hD₁mem hD₁syl
    have hcardS : Nat.card ↥(T ⊓ L₁) = Nat.card ↥D₁ :=
      hSylT.card_eq.trans hD₁syl.card_eq.symm
    have hmRankS : mRank (T ⊓ L₁) = 2 := by
      rw [mRank, hcardS.trans hD₁card]; norm_num
    exact br1_false_closing hB.toBr1Base htwo hS (by rw [hmRankS]; exact hi) hmem

private theorem w183_master2s_two_le_mRank_of_two_lt {D : Subgroup (LGL 2 V)}
    (hel : IsElemAbelian 2 D) (h : 2 < Nat.card D) : 2 ≤ mRank D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hel)
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hn1 : n ≤ 1 := by omega
    have hle : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    rw [hn] at h
    omega
  rw [mRank, hn, Nat.log_pow (by norm_num : 1 < 2)]
  exact hn2

private theorem w183_master2s_mem_normalizer (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hL : Br2TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (h4 : 4 ≤ Nat.card D) :
    D ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) ∧
      D ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := by
  refine ⟨?_, ?_⟩ <;> intro d hd
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases hL.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
    · exact (w183l39_false_of_swap_common hc hL hD h4 hd h1).elim
  · have hdY : d ∈ Y := hc.h131.le_G D hD hd
    rcases hL.perm d hdY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · exact (w183l39_false_of_swap_common hc hL hD h4 hd h1).elim

private theorem w183_master2s_three_le_mOf_or (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂) {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ)
    (h4 : 4 ≤ Nat.card D) (hrk : 3 ≤ mRank D) :
    3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ∨
      3 ≤ mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
  by_contra hcon
  have hm₁ : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inl h))
  have hm₂ : mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
    not_lt.1 (fun h => hcon (Or.inr h))
  have hn₁ := (w183_master2s_mem_normalizer hB htwo hD h4).1
  have hn₂ := (w183_master2s_mem_normalizer hB htwo hD h4).2
  have hle := hB.h131.le_G D hD
  have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
  have hDne : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₁
    omega
  have hFne : (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≠ ⊥ := by
    intro hbot
    rw [hbot, mOf_bot] at hm₂
    omega
  haveI := htwo.simple₁
  haveI := htwo.simple₂
  refine Assumption131.false_of_two_kernels hB.h131 hD htwo.le₁ htwo.le₂ htwo.nonab₁
    htwo.nonab₂ htwo.comm ?_ ?_ rfl rfl hDne hFne ?_ (hm₁.trans hi)
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₁ ha) l).mp hl
  · intro a ha l hl
    exact (Subgroup.mem_normalizer_iff.mp (hn₂ ha) l).mp hl
  · rw [eq_bot_iff]
    rintro y ⟨⟨hyA, hy₁⟩, -, hy₂⟩
    exact Subgroup.mem_bot.mpr (htwo.cent y (hle hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₂ l hl).symm))

private theorem w183_master2s_sylow_member_of_config (rows : Br1Rows)
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hL1 : IsL2 ↥L₁ 2) (hL2 : IsL2 ↥L₂ 2)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (hcard : Nat.card D = 4)
    (hconfig : (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
      (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
        D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) :
    IsSylowIn 2 D L₁ ∨ IsSylowIn 2 D L₂ := by
  have h4 : 4 ≤ Nat.card D := by rw [hcard]
  have hrank : mRank D ≤ m - i₀ - 1 := by
    have h2 : mRank D = 2 := by rw [mRank, hcard]; norm_num
    have := hB.hmi; omega
  rcases hconfig with ⟨hker₁, hcent₂⟩ | ⟨hker₂, hcent₁⟩
  · let c : Br1Alpha Y T L₁ L₂ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2s_mem_normalizer hB htwo hD h4).1
        ker₁ := hker₁
        cent₂ := hcent₂ }
    exact Or.inl (br1_alpha_sylow_L24 rows.a5 c hL1)
  · let c : Br1Alpha Y T L₂ L₁ D Γ VA (m - i₀ - 1) :=
      { h := hB.h131
        vfix := hB.vfix
        two := w183_twoComp_symm htwo
        mem := hD
        rank := hrank
        card := hcard
        norm₁ := (w183_master2s_mem_normalizer hB htwo hD h4).2
        ker₁ := hker₂
        cent₂ := hcent₁ }
    exact Or.inr (br1_alpha_sylow_L24 rows.a5 c hL2)

theorem br1_master_two_small (rows : Br1Rows) {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (htwo : Br2TwoComp Y T L₁ L₂) (hshape : IsL2 ↥L₁ 2)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) (h4 : 4 ≤ Nat.card ↥A₀) : False := by
  have hL1 : IsL2 ↥L₁ 2 := hshape
  have hL2 : IsL2 ↥L₂ 2 := w183_master2_isL2_swap htwo hshape
  have h2A : 2 < Nat.card A₀ := by omega
  have hrankA : 2 ≤ mRank A₀ :=
    w183_master2s_two_le_mRank_of_two_lt (hB.h131.isElemAb A₀ hA₀) h2A
  by_cases h3 : 3 ≤ mRank A₀
  · have h3' := w183_master2s_three_le_mOf_or hB htwo hA₀ h4 h3
    rcases h3' with h3₁ | h3₂
    · exact (br1_rank_false_two rows.rk2 htwo (Or.inl hL1) (hB.h131.le_G A₀ hA₀)
        (w183_master2s_mem_normalizer hB htwo hA₀ h4).1 (hB.h131.isElemAb A₀ hA₀) h3₁).elim
    · exact (br1_rank_false_two rows.rk2 (w183_twoComp_symm htwo) (Or.inl hL2)
        (hB.h131.le_G A₀ hA₀) (w183_master2s_mem_normalizer hB htwo hA₀ h4).2
        (hB.h131.isElemAb A₀ hA₀) h3₂).elim
  · have hrank₀ : mRank A₀ = 2 := by have := not_le.1 h3; omega
    have hi : 2 ≤ m - i₀ - 1 := by have := hB.hmi; omega
    have hm₀₁ : mOf A₀ (A₀ ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
      (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank₀)
    have hm₀₂ : mOf A₀ (A₀ ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
      (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrank₀)
    have hI2 := br1_I2_member_free rows.g3 hB.h131 hB.vfix hi htwo (Or.inl hL1) (Or.inl hL2)
      hA₀ h4 (w183_master2s_mem_normalizer hB htwo hA₀ h4).1
      (w183_master2s_mem_normalizer hB htwo hA₀ h4).2 hm₀₁ hm₀₂
    have hcard₀ : Nat.card A₀ = 4 := hI2.1
    have hmem : ∀ D ∈ Γ, 2 < Nat.card D → D ≤ L₁ ∨ D ≤ L₂ := by
      intro D hD hcard
      have hel := hB.h131.isElemAb D hD
      have h2D : 2 ≤ mRank D := w183_master2s_two_le_mRank_of_two_lt hel hcard
      have h4D : 4 ≤ Nat.card D := w183_master2_four_le_card_of_two_le_mRank h2D
      have hDn := w183_master2s_mem_normalizer hB htwo hD h4D
      by_cases h3D : 3 ≤ mRank D
      · have h3D' := w183_master2s_three_le_mOf_or hB htwo hD h4D h3D
        rcases h3D' with h3₁ | h3₂
        · exact (br1_rank_false_two rows.rk2 htwo (Or.inl hL1) (hB.h131.le_G D hD)
            hDn.1 hel h3₁).elim
        · exact (br1_rank_false_two rows.rk2 (w183_twoComp_symm htwo) (Or.inl hL2)
            (hB.h131.le_G D hD) hDn.2 hel h3₂).elim
      · have hrankD : mRank D = 2 := by have := not_le.1 h3D; omega
        have hcardD : Nat.card D = 4 :=
          w183_master2_card_eq_four_of_mRank_eq_two hel hrankD
        have hmD₁ : mOf D (D ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2 :=
          (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrankD)
        have hmD₂ : mOf D (D ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2 :=
          (w183_master2_mOf_le_mRank inf_le_left).trans (le_of_eq hrankD)
        have hI2D := br1_I2_member_free rows.g3 hB.h131 hB.vfix hi htwo (Or.inl hL1)
          (Or.inl hL2) hD h4D hDn.1 hDn.2 hmD₁ hmD₂
        rcases w183_master2s_sylow_member_of_config rows hB htwo hL1 hL2 hD hcardD hI2D.2
          with hsyl | hsyl
        · exact Or.inl hsyl.le
        · exact Or.inr hsyl.le
    have hD₀syl := w183_master2s_sylow_member_of_config rows hB htwo hL1 hL2 hA₀ hcard₀ hI2.2
    obtain ⟨D₁, hD₁mem, hD₁syl, hD₁card⟩ : ∃ D₁ ∈ Γ, IsSylowIn 2 D₁ L₁ ∧ Nat.card D₁ = 4 := by
      rcases hD₀syl with hsyl | hsyl
      · exact ⟨A₀, hA₀, hsyl, hcard₀⟩
      · obtain ⟨x, hxT, hxL⟩ := htwo.swap
        have hxY : x ∈ Y := hB.sylow.1 hxT
        have hxL₂ : cj x L₂ = L₁ := by
          rcases htwo.perm x hxY with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd (h1.symm.trans hxL) htwo.ne
          · exact h2
        refine ⟨cj x A₀, hB.h131.invariant A₀ hA₀ x hxY, ?_, ?_⟩
        · have h := w183_master2_isSylowIn_cj x hsyl
          rwa [hxL₂] at h
        · rw [cj, Subgroup.card_map_of_injective (MulAut.conj x).injective]
          exact hcard₀
    have hSylT : IsSylowIn 2 (T ⊓ L₁) L₁ := w183_master2_sylow_T_inf_L1 hB.sylow htwo
    have hS : T ⊓ L₁ ∈ Γ := w183_master2_inf_L1_mem hB htwo hSylT hD₁mem hD₁syl
    have hcardS : Nat.card ↥(T ⊓ L₁) = Nat.card ↥D₁ :=
      hSylT.card_eq.trans hD₁syl.card_eq.symm
    have hmRankS : mRank (T ⊓ L₁) = 2 := by
      rw [mRank, hcardS.trans hD₁card]; norm_num
    exact br1_false_closing hB.toBr1Base htwo hS (by rw [hmRankS]; exact hi) hmem

end CFSG.LocalAnalysis.WeakClosure81

end
