module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType.BorelTits

section Transport

variable {S K : Type} [Group S] [Group K]

private theorem pCoreOf_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ)
    (H : Subgroup S) : pCoreOf 2 (H.map Φ) = (pCoreOf 2 H).map Φ := by
  have h := pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective Φ hΦ) H
  have he : (MulEquiv.ofBijective Φ hΦ).toMonoidHom = Φ := MonoidHom.ext fun _ => rfl
  rwa [he] at h

private theorem pCoreOf_normalizer_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ)
    (T : Subgroup S) :
    pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set S))).map Φ := by
  rw [← Subgroup.map_normalizer_eq_of_bijective T hΦ, pCoreOf_map_of_bijective Φ hΦ]

theorem rootIrrModel_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ) {T : Subgroup S}
    (h : RootIrrModel S T) : RootIrrModel K (T.map Φ) := by
  intro R hTR hRP hRn
  rw [pCoreOf_normalizer_map_of_bijective Φ hΦ] at hRP ⊢
  rw [← Subgroup.map_normalizer_eq_of_bijective T hΦ] at hRn
  have hR : (R.comap Φ).map Φ = R := Subgroup.map_comap_eq_self_of_surjective hΦ.2 R
  have key := h (R.comap Φ) (Subgroup.map_le_iff_le_comap.1 hTR)
    (by
      rw [← Subgroup.comap_map_eq_self_of_injective hΦ.1 (pCoreOf 2 _)]
      exact Subgroup.comap_mono hRP)
    (fun b hb r hr => by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hRn (Φ b) (Subgroup.mem_map_of_mem Φ hb) (Φ r) hr)
  rcases key with h1 | h1
  · left
    rw [← hR, h1]
  · right
    rw [← hR, h1]

private noncomputable def mulAutPullback (Φ : S →* K) (hΦ : Function.Bijective Φ)
    (α : MulAut K) : MulAut S :=
  ((MulEquiv.ofBijective Φ hΦ).trans α).trans (MulEquiv.ofBijective Φ hΦ).symm

private theorem map_mulAutPullback (Φ : S →* K) (hΦ : Function.Bijective Φ) (α : MulAut K)
    (x : S) : Φ (mulAutPullback Φ hΦ α x) = α (Φ x) := by
  simp [mulAutPullback]

private theorem eq_conj_of_mulAutPullback (Φ : S →* K) (hΦ : Function.Bijective Φ)
    {α : MulAut K} {s : S} (h : mulAutPullback Φ hΦ α = MulAut.conj s) :
    α = MulAut.conj (Φ s) := by
  ext y
  obtain ⟨x, rfl⟩ := hΦ.2 y
  rw [← map_mulAutPullback Φ hΦ, h, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

theorem rootInnerModel_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ)
    {T : Subgroup S} (h : RootInnerModel S T) : RootInnerModel K (T.map Φ) := by
  intro α hαA hαN
  obtain ⟨s, hs, hβs⟩ := h (mulAutPullback Φ hΦ α)
    (fun a ha => hΦ.1 (by
      rw [map_mulAutPullback, hαA _ (Subgroup.mem_map_of_mem Φ ha)]))
    (fun b hb => by
      have := hαN (Φ b) (by
        rw [← Subgroup.map_normalizer_eq_of_bijective T hΦ]
        exact Subgroup.mem_map_of_mem Φ hb)
      rw [← Subgroup.mem_map_iff_mem hΦ.1, map_mul, map_inv, map_mulAutPullback]
      exact this)
  exact ⟨Φ s, Subgroup.mem_map_of_mem Φ hs, eq_conj_of_mulAutPullback Φ hΦ hβs⟩

theorem rootS2Model_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ) {T : Subgroup S}
    (h : RootS2Model S T) : RootS2Model K (T.map Φ) := by
  intro α hαA hαN
  rw [pCoreOf_normalizer_map_of_bijective Φ hΦ] at hαN ⊢
  obtain ⟨s, hs, hβs⟩ := h (mulAutPullback Φ hΦ α)
    (fun a ha => hΦ.1 (by
      rw [map_mulAutPullback, hαA _ (Subgroup.mem_map_of_mem Φ ha)]))
    (fun b hb => by
      have := hαN (Φ b) (Subgroup.mem_map_of_mem Φ hb)
      rw [← Subgroup.mem_map_iff_mem hΦ.1, map_mul, map_inv, map_mulAutPullback]
      exact this)
  exact ⟨Φ s, Subgroup.mem_map_of_mem Φ hs, eq_conj_of_mulAutPullback Φ hΦ hβs⟩

theorem rootS1Model_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ) {T : Subgroup S}
    (h : RootS1Model S T) : RootS1Model K (T.map Φ) := by
  intro g hg a ha ha1
  obtain ⟨g', rfl⟩ := hΦ.2 g
  rw [ModelRank.conjSub_map] at hg ha
  obtain ⟨a', ha', rfl⟩ := ha
  have hS := h g' (fun hc => hg (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hc x hx y hy])) a' ha' (fun h1 => ha1 (by rw [h1, map_one]))
  rw [pCoreOf_normalizer_map_of_bijective Φ hΦ, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hS,
    Subgroup.map_top_of_surjective Φ hΦ.2]

end Transport

section Extraction

theorem exists_isTransGroup_of_transvConclusionSp {K : Type} [Group K] {Δ : Set (Subgroup K)}
    {f : ℕ} (hf : 1 ≤ f) (h : TransvConclusionSp K Δ f) {A : Subgroup K} (hA : A ∈ Δ) :
    ∃ (n : ℕ) (Φ : StatedSp n (GaloisField 2 f) →* K) (a : Fin n ⊕ Fin n → GaloisField 2 f)
      (T : Subgroup (StatedSp n (GaloisField 2 f))),
      Function.Bijective Φ ∧ a ≠ 0 ∧ CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T ∧
        A = T.map Φ := by
  obtain ⟨n, hn, Φ, hΦ, hΔ⟩ := h
  obtain ⟨g, rfl⟩ := (hΔ A).1 hA
  have hv : (Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1 :
      Fin n ⊕ Fin n → GaloisField 2 f) ≠ 0 :=
    Pi.single_ne_zero_iff.2 one_ne_zero
  exact ⟨n, Φ, _, _, hΦ, ModelRank.mat_mulVec_ne_zero' g hv,
    (ModelRank.isTransGroup_rootGroup_last (by omega)).conjSub g, rfl⟩

end Extraction

section Assembly

@[expose] def SpModelIrr : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
    (T : Subgroup (StatedSp n F)), a ≠ 0 → CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T →
      RootIrrModel (StatedSp n F) T

@[expose] def SpModelInner : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
    (T : Subgroup (StatedSp n F)), a ≠ 0 → CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T →
      RootInnerModel (StatedSp n F) T

@[expose] def SpModelS2 : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
    (T : Subgroup (StatedSp n F)), a ≠ 0 → CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T →
      RootS2Model (StatedSp n F) T

@[expose] def SpModelS1 : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
    (T : Subgroup (StatedSp n F)), a ≠ 0 → CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T →
      RootS1Model (StatedSp n F) T

@[expose] def ClassicalRootSp (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∃ f : ℕ, ∃ Δ : Set (Subgroup K), 1 ≤ f ∧ TransvConclusionSp K Δ f ∧ A ∈ Δ

@[expose] def ClassicalRootSU (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∃ f : ℕ, ∃ hf : 1 ≤ f, ∃ Δ : Set (Subgroup K), TransvConclusionSU K Δ f hf ∧ A ∈ Δ

theorem classicalRoot_iff (K : Type) [Group K] (A : Subgroup K) :
    ClassicalRoot K A ↔ ClassicalRootSp K A ∨ ClassicalRootSU K A :=
  Iff.rfl

@[expose] def ClassicalRootSpIrrStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → RootIrrModel K A

@[expose] def ClassicalRootSpInnerStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → RootInnerModel K A

@[expose] def ClassicalRootSpS2Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → RootS2Model K A

@[expose] def ClassicalRootSpS1Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → RootS1Model K A

@[expose] def ClassicalRootSUIrrStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSU K A → RootIrrModel K A

@[expose] def ClassicalRootSUInnerStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSU K A → RootInnerModel K A

@[expose] def ClassicalRootSUS2Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSU K A → RootS2Model K A

@[expose] def ClassicalRootSUS1Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSU K A → RootS1Model K A

theorem classicalRootSpIrrStatement_of_model (h : SpModelIrr) : ClassicalRootSpIrrStatement := by
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, ha, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  exact rootIrrModel_map_of_bijective Φ hΦ (h n (GaloisField 2 f) a T ha hT)

theorem classicalRootSpInnerStatement_of_model (h : SpModelInner) :
    ClassicalRootSpInnerStatement := by
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, ha, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  exact rootInnerModel_map_of_bijective Φ hΦ (h n (GaloisField 2 f) a T ha hT)

theorem classicalRootSpS2Statement_of_model (h : SpModelS2) : ClassicalRootSpS2Statement := by
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, ha, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  exact rootS2Model_map_of_bijective Φ hΦ (h n (GaloisField 2 f) a T ha hT)

theorem classicalRootSpS1Statement_of_model (h : SpModelS1) : ClassicalRootSpS1Statement := by
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, ha, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  exact rootS1Model_map_of_bijective Φ hΦ (h n (GaloisField 2 f) a T ha hT)

theorem classicalRootIrrStatement_of_sp_su (hsp : ClassicalRootSpIrrStatement)
    (hsu : ClassicalRootSUIrrStatement) : ClassicalRootIrrStatement := by
  intro K _ _ A hA
  rcases (classicalRoot_iff K A).1 hA with h | h
  · exact hsp K A h
  · exact hsu K A h

theorem classicalRootInnerStatement_of_sp_su (hsp : ClassicalRootSpInnerStatement)
    (hsu : ClassicalRootSUInnerStatement) : ClassicalRootInnerStatement := by
  intro K _ _ A hA
  rcases (classicalRoot_iff K A).1 hA with h | h
  · exact hsp K A h
  · exact hsu K A h

theorem classicalRootS2Statement_of_sp_su (hsp : ClassicalRootSpS2Statement)
    (hsu : ClassicalRootSUS2Statement) : ClassicalRootS2Statement := by
  intro K _ _ A hA
  rcases (classicalRoot_iff K A).1 hA with h | h
  · exact hsp K A h
  · exact hsu K A h

theorem classicalRootS1Statement_of_sp_su (hsp : ClassicalRootSpS1Statement)
    (hsu : ClassicalRootSUS1Statement) : ClassicalRootS1Statement := by
  intro K _ _ A hA
  rcases (classicalRoot_iff K A).1 hA with h | h
  · exact hsp K A h
  · exact hsu K A h

end Assembly

end CFSG.RankThree.GF2n.Tim79a
