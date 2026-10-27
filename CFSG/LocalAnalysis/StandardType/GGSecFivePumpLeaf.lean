module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem root_pm {k : ℕ} (hk : 2 ≤ k) {t : ggWeylD k} {γ γ' : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t γ') : γ' = γ ∨ γ' = -γ := by
  have hγ := ggDDot_self_of_mem (h.mem (by omega))
  have hγ' := ggDDot_self_of_mem (h'.mem (by omega))
  obtain ⟨w, i, -, hw⟩ := id h
  have key : ggDReflect γ' γ = ggDReflect γ γ := by
    have h1 := (h'.action hk (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))).symm.trans
      (h.action hk _)
    rwa [hw] at h1
  have hneg : ∀ δ v : Fin k → ℤ, ggDReflect δ (-v) = -ggDReflect δ v := fun δ v => by
    simp only [ggDReflect, ggDDot_eq_dotProduct, neg_dotProduct, neg_smul]
    abel
  have hself : ggDReflect γ γ = -γ := by
    funext c
    rw [ggDReflect_apply, hγ, Pi.neg_apply]
    ring
  rcases ggDReflect_comm_dot hγ hγ' (by rw [key, hself, hneg, hneg, key]) with h0 | h0 | h0
  · exfalso
    have h1 : ggDReflect γ' γ = γ := by
      funext c
      rw [ggDReflect_apply, h0, zero_mul, sub_zero]
    rw [key, hself] at h1
    have h2 := congrArg (fun v => ggDDot v γ) h1
    simp only [ggDDot_eq_dotProduct, neg_dotProduct] at h2 hγ
    omega
  · exact Or.inl h0
  · exact Or.inr h0

private theorem partner_pm {k : ℕ} {a b a' b' : Fin k} {s s' ε : ℤ} (hab : a ≠ b)
    (hab' : a' ≠ b') (hs' : s' = 1 ∨ s' = -1) (hε : ε = 1 ∨ ε = -1)
    (h : (Pi.single a' 1 + Pi.single b' s' : Fin k → ℤ) = ε • (Pi.single a 1 + Pi.single b s)) :
    (Pi.single a' 1 - Pi.single b' s' : Fin k → ℤ) = Pi.single a 1 - Pi.single b s ∨
      (Pi.single a' 1 - Pi.single b' s' : Fin k → ℤ) = -(Pi.single a 1 - Pi.single b s) := by
  have hx : ∀ y, (Pi.single a' 1 + Pi.single b' s' : Fin k → ℤ) y =
      ε * (Pi.single a 1 + Pi.single b s : Fin k → ℤ) y := fun y => by
    rw [h, Pi.smul_apply, smul_eq_mul]
  have h1 := hx a'
  have h2 := hx b'
  rw [ggDPair_apply_left hab'] at h1
  rw [ggDPair_apply_right hab'] at h2
  by_cases hb : b' = b
  · subst hb
    rw [ggDPair_apply_right hab] at h2
    by_cases ha : a' = a
    · subst ha
      rw [ggDPair_apply_left hab] at h1
      have : s' = s := by rcases hε with rfl | rfl <;> omega
      exact Or.inl (by rw [this])
    · rw [ggDPair_apply_of_ne ha hab'] at h1
      omega
  by_cases hb2 : b' = a
  · subst hb2
    rw [ggDPair_apply_left hab] at h2
    by_cases ha : a' = b
    · subst ha
      rw [ggDPair_apply_right hab] at h1
      rcases hε with rfl | rfl
      · obtain rfl : s = 1 := by omega
        obtain rfl : s' = 1 := by omega
        exact Or.inr (by rw [neg_sub])
      · obtain rfl : s = -1 := by omega
        obtain rfl : s' = -1 := by omega
        exact Or.inl (by simp only [Pi.single_neg, sub_neg_eq_add, add_comm])
    · rw [ggDPair_apply_of_ne hab' ha] at h1
      omega
  · rw [ggDPair_apply_of_ne hb2 hb] at h2
    rcases hs' with rfl | rfl <;> omega

private theorem disjSupp_of_three {k : ℕ} (hk : 4 ≤ k) {t t₁ t₂ : ggWeylD k}
    (ht : ∃ γ, GGDReflRoot k t γ) (ht₁ : ∃ γ, GGDReflRoot k t₁ γ)
    (ht₂ : ∃ γ, GGDReflRoot k t₂ γ) (h₁ : t ≠ t₁) (h₂ : t ≠ t₂) (h₁₂ : t₁ ≠ t₂)
    (hc₁ : t * t₁ = t₁ * t) (hc₂ : t * t₂ = t₂ * t) :
    GGDDisjSupp k t t₁ ∨ GGDDisjSupp k t t₂ := by
  rcases ggDk_orth_dichotomy hk ht ht₁ h₁ hc₁ with ⟨a, b, s, hab, -, hP, hQ⟩ | hd
  · rcases ggDk_orth_dichotomy hk ht ht₂ h₂ hc₂ with ⟨a', b', s', hab', hs', hP', hQ'⟩ | hd
    · obtain ⟨ε, hε, hεP⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Pi.single a' 1 + Pi.single b' s' :
          Fin k → ℤ) = ε • (Pi.single a 1 + Pi.single b s) := by
        rcases root_pm (by omega) hP hP' with h | h
        · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
        · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
      exact absurd (hQ.unique (by omega) hQ' (partner_pm hab hab' hs' hε hεP)) h₁₂
    · exact Or.inr hd
  · exact Or.inl hd

private theorem entry_zero {n : ℕ} (hn : 4 ≤ n) {N : CoxeterMatrix (Fin n)}
    (hN : N = CoxeterMatrix.A n ∨ N = CoxeterMatrix.B n ∨ N = ggCoxeterMatrixD n)
    {i j : Fin n} (hi : i.val = 0) (hj : 2 ≤ j.val) : N.M i j = 2 := by
  have := j.isLt
  rcases hN with rfl | rfl | rfl
  · simp only [CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h := ggCoxeterMatrixD_apply n i j
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h
    rw [h]
    split_ifs <;> omega

private theorem exists_two_nonadj {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hcard : 4 ≤ Nat.card ι) :
    ∃ u b c : ι, u ≠ b ∧ u ≠ c ∧ b ≠ c ∧ M.M u b = 2 ∧ M.M u c = 2 := by
  rcases hM with ⟨n, e, -, hX⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hG⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    obtain ⟨N, hN, rfl⟩ : ∃ N : CoxeterMatrix (Fin n), (N = CoxeterMatrix.A n ∨
        N = CoxeterMatrix.B n ∨ N = ggCoxeterMatrixD n) ∧ M = N.reindex e := by
      rcases hX with hA | ⟨-, hB⟩ | ⟨-, hD⟩
      · exact ⟨_, Or.inl rfl, hA⟩
      · exact ⟨_, Or.inr (Or.inl rfl), hB⟩
      · exact ⟨_, Or.inr (Or.inr rfl), hD⟩
    refine ⟨e ⟨0, by omega⟩, e ⟨2, by omega⟩, e ⟨3, by omega⟩, e.injective.ne (by simp),
      e.injective.ne (by simp), e.injective.ne (by simp), ?_, ?_⟩ <;>
    · rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact entry_zero hcard hN rfl (by simp)
  all_goals first
    | (refine ⟨e 0, e 1, e 3, e.injective.ne (by decide), e.injective.ne (by decide),
        e.injective.ne (by decide), ?_, ?_⟩ <;>
      · rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl)
    | (refine ⟨e 0, e 2, e 3, e.injective.ne (by decide), e.injective.ne (by decide),
        e.injective.ne (by decide), ?_, ?_⟩ <;>
      · rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl)
    | (rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
       omega)

theorem ggDk_memberRoots_L_disjSupp
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 5 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) :
    ∃ t t' : M.Group, GGDDisjSupp k (φ t) (φ t') ∧
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
  obtain ⟨tg, n, f, ψ, hadm, -, -, -, htag, -, hTB⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
  have hkℓ := (ggDk_card_bstar_bounds hcfg hpres (by omega) hM hTB).2.2
  obtain ⟨ε, hεr, -, -⟩ := hTB
  obtain ⟨u, b, c, hub, huc, hbc, h2b, h2c⟩ := exists_two_nonadj (ggTag_weylMatrix htag hadm).1
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hτ : ∀ i, ∃ τ : M.Group, (∃ γ, GGDReflRoot k (φ τ) γ) ∧
      ((e τ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((ε ((coxeterMatrix (ggU tg n f).D.isFiniteType).simple i) : ↥(ggAutomizer L Bs)) :
          MulAut ↥Bs) := fun i => by
    obtain ⟨w, j, hwj⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (ε _).2) (hεr i)
    exact ⟨w * M.simple j * w⁻¹, ⟨_, φ w, σ.symm j, by
      rw [map_mul, map_mul, map_inv, ← hφ, Equiv.apply_symm_apply], rfl⟩, hwj.symm⟩
  choose τ hτr hτe using hτ
  have hL : ∀ i, ((e (τ i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs :=
    fun i => hτe i ▸ (ε _).2
  have hsi : Function.Injective (coxeterMatrix (ggU tg n f).D.isFiniteType).simple := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.simple_injective _
  have hne : ∀ i j, i ≠ j → φ (τ i) ≠ φ (τ j) := fun i j hij h =>
    hij (hsi (ε.injective (Subtype.ext (by rw [← hτe, ← hτe, φ.injective h]))))
  have hcomm : ∀ i j, (coxeterMatrix (ggU tg n f).D.isFiniteType).M i j = 2 →
      φ (τ i) * φ (τ j) = φ (τ j) * φ (τ i) := fun i j h => by
    have h1 := congrArg (fun g => ((ε g : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (ggSimplyLaced_simple_comm h)
    simp only [map_mul, Subgroup.coe_mul, ← hτe] at h1
    have h2 : τ i * τ j = τ j * τ i :=
      e.injective (Subtype.ext (by simp only [map_mul, Subgroup.coe_mul, h1]))
    rw [← map_mul, ← map_mul, h2]
  rcases disjSupp_of_three (by omega) (hτr u) (hτr b) (hτr c) (hne u b hub) (hne u c huc)
      (hne b c hbc) (hcomm u b h2b) (hcomm u c h2c) with h | h
  · exact ⟨τ u, τ b, h, hL u, hL b⟩
  · exact ⟨τ u, τ c, h, hL u, hL c⟩

end CFSG.StandardType

end
