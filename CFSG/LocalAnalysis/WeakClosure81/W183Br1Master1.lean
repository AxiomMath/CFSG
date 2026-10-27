module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rows
public import CFSG.LocalAnalysis.WeakClosure81.W183B2OneA6
public import CFSG.LocalAnalysis.WeakClosure81.W183B2OneL34
public import CFSG.LocalAnalysis.WeakClosure81.W183B2OneSp44

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem w183_master1_eight_le_card_of_three_le_mRank {A : Subgroup (LGL 2 V)}
    (h : 3 ≤ mRank A) : 8 ≤ Nat.card A := by
  have hne : Nat.card A ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, A.one_mem⟩, inferInstance⟩
  have hlog : 3 ≤ Nat.log 2 (Nat.card A) := by simpa only [mRank] using h
  have hpow : 2 ^ 3 ≤ Nat.card A := Nat.pow_le_of_le_log hne hlog
  simpa using hpow

private theorem w183_master1_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

private theorem w183_master1_mem_normalizer_of_normal {Y L : Subgroup (LGL 2 V)}
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) {y : LGL 2 V} (hy : y ∈ Y) :
    y ∈ Subgroup.normalizer (L : Set (LGL 2 V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact hLn y hy l hl
  · intro hl
    have h := hLn y⁻¹ (Y.inv_mem hy) (y * l * y⁻¹) hl
    rwa [show y⁻¹ * (y * l * y⁻¹) * (y⁻¹)⁻¹ = l by group] at h

private theorem w183_master1_cj_map_center {S : Subgroup (LGL 2 V)} {y : LGL 2 V} :
    cj y ((Subgroup.center ↥S).map S.subtype) =
      (Subgroup.center ↥(cj y S)).map (cj y S).subtype := by
  let e : ↥S ≃* ↥(cj y S) :=
    Subgroup.equivMapOfInjective S (MulAut.conj y).toMonoidHom (MulEquiv.injective _)
  have hcomp : (cj y S).subtype.comp (e : ↥S →* ↥(cj y S)) =
      (MulAut.conj y).toMonoidHom.comp S.subtype := by
    ext x : 1
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact Subgroup.coe_equivMapOfInjective_apply S (MulAut.conj y).toMonoidHom
      (MulEquiv.injective _) x
  calc cj y ((Subgroup.center ↥S).map S.subtype)
      = ((Subgroup.center ↥S).map S.subtype).map (MulAut.conj y).toMonoidHom := rfl
    _ = (Subgroup.center ↥S).map ((MulAut.conj y).toMonoidHom.comp S.subtype) := by
        rw [Subgroup.map_map]
    _ = (Subgroup.center ↥S).map ((cj y S).subtype.comp (e : ↥S →* ↥(cj y S))) := by
        rw [hcomp]
    _ = ((Subgroup.center ↥S).map (e : ↥S →* ↥(cj y S))).map (cj y S).subtype := by
        rw [← Subgroup.map_map]
    _ = (Subgroup.center ↥(cj y S)).map (cj y S).subtype := by
        rw [Subgroup.map_center_eq]

theorem br1_I1_outcome_small (hA5 : FinA5) (hU34 : FinU34)
    {Y L A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (h : Assumption131 Y Γ VA i) (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1)
    (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) :
    (IsL2 ↥L 2 ∧ IsSylowIn 2 A L) ∨
      (IsU3 ↥L 2 ∧ ∃ S : Subgroup (LGL 2 V), IsSylowIn 2 S L ∧
        A = (Subgroup.center ↥S).map S.subtype) := by
  rcases hshape with hs | hs
  · exact Or.inl ⟨hs, br1_sylow_of_L24 hA5 h hLY hLn hcent hs hA hr hcard hel⟩
  · exact Or.inr ⟨hs, br1_center_of_U34 hU34 h hLY hLn hcent hs hA hr hcard hel⟩

theorem br1_master_one_small (rows : Br1Rows) {Y T L : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1)
    (hshape : IsL2 ↥L 2 ∨ IsU3 ↥L 2)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) (h4 : 4 ≤ Nat.card ↥A₀) :
    (IsL2 ↥L 2 ∧ ∃ A ∈ Γ, A ≤ T ∧ IsSylowIn 2 A L) ∨
      (IsU3 ↥L 2 ∧ ∃ A ∈ Γ, A ≤ T ∧ ∃ S : Subgroup (LGL 2 V), IsSylowIn 2 S L ∧
        A = (Subgroup.center ↥S).map S.subtype) := by
  classical
  by_cases h3 : 3 ≤ mRank A₀
  ·
    have h8 : 8 ≤ Nat.card ↥A₀ := w183_master1_eight_le_card_of_three_le_mRank h3
    rcases hshape with hs | hs
    · exact (br1_rank_false_one rows.rk2 rows.rkU rows.h65f hB.h131 hLY hLn hcent
        (Or.inl hs) hA₀ h8).elim
    · exact (br1_rank_false_one rows.rk2 rows.rkU rows.h65f hB.h131 hLY hLn hcent
        (Or.inr (Or.inr hs)) hA₀ h8).elim
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite (LGL 2 V) := w183_master1_finite_lgl
    have h2 : 2 ≤ mRank A₀ := by
      have hp : 2 ^ 2 ≤ Nat.card ↥A₀ := by simpa using h4
      have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hp
      simpa only [mRank] using hlog
    have hrank2 : mRank A₀ = 2 := le_antisymm (by omega) h2
    have hel : IsElemAbelian 2 A₀ := hB.h131.isElemAb A₀ hA₀
    have hcard : Nat.card ↥A₀ = 4 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A₀)).mp hel.isPGroup
      have hlog : mRank A₀ = k := by
        rw [mRank, hk, Nat.log_pow (by norm_num : 1 < 2)]
      have hk2 : k = 2 := by omega
      rw [hk, hk2]
      norm_num
    have hr : mRank A₀ ≤ m - i₀ - 1 := by
      have := hB.hmi
      omega
    have hout := br1_I1_outcome_small rows.a5 rows.u34 hB.h131 hLY hLn hcent hshape hA₀ hr
      hcard hel
    obtain ⟨y, hyY, hDy⟩ := CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hB.sylow
      (hB.h131.le_G A₀ hA₀) hel.isPGroup
    have hA_mem : cj y A₀ ∈ Γ := hB.h131.invariant A₀ hA₀ y hyY
    have hA_le_T : cj y A₀ ≤ T := by
      have hcj : cj y A₀ = conjSubgroup A₀ y⁻¹ := by simp only [cj, conjSubgroup, inv_inv]
      calc cj y A₀ = conjSubgroup A₀ y⁻¹ := hcj
        _ ≤ conjSubgroup (conjSubgroup T y) y⁻¹ :=
            CFSG.Quasithin.E3.conjSubgroup_mono_left y⁻¹ hDy
        _ = T := CFSG.Quasithin.E3.conjSubgroup_conj_inv T y
    have hy_norm : y ∈ Subgroup.normalizer (L : Set (LGL 2 V)) :=
      w183_master1_mem_normalizer_of_normal hLn hyY
    rcases hout with ⟨hL2, hAsyl⟩ | ⟨hU3, S, hSsyl, hAeq⟩
    · exact Or.inl ⟨hL2, cj y A₀, hA_mem, hA_le_T,
        by simpa only [cj] using CFSG.Quasithin.Ch1Sec3.isSylowIn_map_conj hAsyl hy_norm⟩
    · refine Or.inr ⟨hU3, cj y A₀, hA_mem, hA_le_T, cj y S, ?_, ?_⟩
      · simpa only [cj] using CFSG.Quasithin.Ch1Sec3.isSylowIn_map_conj hSsyl hy_norm
      · rw [hAeq, w183_master1_cj_map_center]

theorem br1_master_one_big (rows : Br1Rows) {Y T L : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}
    {𝒢 : Set (Subgroup (LGL 2 V))} {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ}
    {δ : Subgroup (LGL 2 V) → ℕ} (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1)
    (hshape : IsL3 ↥L 1 ∨ IsAlt ↥L 6 ∨ IsL3 ↥L 2 ∨ IsSp4 ↥L 2)
    (hτ : ∃ τ ∈ T, ActsOnDynkinMod ⊥ L τ) (hne : Γ.Nonempty)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) (hPT : IsSp4 ↥L 2 → PairTest Y Γ) : False := by
  classical
  by_cases hrk : ∀ D ∈ Γ, 3 ≤ mRank D
  ·
    have hne' : Γ.Nonempty := hne
    obtain ⟨D₀, hD₀⟩ := hne'
    have h8 : 8 ≤ Nat.card ↥D₀ :=
      w183_master1_eight_le_card_of_three_le_mRank (hrk D₀ hD₀)
    rcases hshape with hs | hs | hs | hs
    · exact (br1_rank_false_one rows.rk2 rows.rkU rows.h65f hB.h131 hLY hLn hcent
        (Or.inr (Or.inl hs)) hD₀ h8).elim
    · have hL : Br2OneComp Y T L := ⟨hLY, hLn, hsimple, hnab, hcent, hτ⟩
      exact (br2_false_of_one_A6 hB hL hs hrk hne rows.g4a6).elim
    · have hL : Br2OneComp Y T L := ⟨hLY, hLn, hsimple, hnab, hcent, hτ⟩
      exact (br2_false_of_one_L34 hB hL hs hrk hne rows.h65f rows.g4l34).elim
    · have hL : Br2OneComp Y T L := ⟨hLY, hLn, hsimple, hnab, hcent, hτ⟩
      exact (br2_false_of_one_Sp44 hB hL hs hrk hne (hPT hs) rows.g45).elim
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite (LGL 2 V) := w183_master1_finite_lgl
    rw [not_forall] at hrk
    obtain ⟨D, hrk'⟩ := hrk
    rw [not_imp, not_le] at hrk'
    obtain ⟨hD, hrlt⟩ := hrk'
    have hrank2 : mRank D = 2 := by
      have := hall D hD
      omega
    have hel : IsElemAbelian 2 D := hB.h131.isElemAb D hD
    have hcard : Nat.card ↥D = 4 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥D)).mp hel.isPGroup
      have hlog : mRank D = k := by
        rw [mRank, hk, Nat.log_pow (by norm_num : 1 < 2)]
      have hk2 : k = 2 := by omega
      rw [hk, hk2]
      norm_num
    have hr : mRank D ≤ m - i₀ - 1 := by
      have := hB.hmi
      omega
    obtain ⟨τ, hτT, hτd⟩ := hτ
    have hτ' : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L τ := ⟨τ, hB.sylow.le hτT, hτd⟩
    rcases hshape with hs | hs | hs | hs
    · exact (br1_false_of_L32 rows.l32 hB.h131 hLY hLn hcent hs hτ' hD hr hcard hel).elim
    · exact (br1_false_of_A6 rows.a6 hB.h131 hLY hLn hcent hs hτ' hD hr hcard hel).elim
    · exact (br1_false_of_L34 rows.h65f rows.g1 hB.h131 hB.vfix hLY hLn hcent hs hD hr hcard
        hel).elim
    · exact (br1_false_of_Sp44 rows.sp hB.h131 hB.vfix hLY hLn hcent hs hτ' hD hr hcard
        hel).elim

end CFSG.LocalAnalysis.WeakClosure81

end
