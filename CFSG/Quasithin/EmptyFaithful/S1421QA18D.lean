module

public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421QA18

open scoped Pointwise

variable {D : Type} [Group D]

theorem normalizer_eq_of_isMaximalTwoLocal {P : Subgroup D} [Finite ↥P]
    (h : IsMaximalTwoLocal P) : Subgroup.normalizer (P : Set D) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨R, hR, hR2, hPR⟩, hmax⟩ := h
  have hRP : R ≤ P := hPR ▸ Subgroup.le_normalizer
  have hO : R ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRP hPR.le hR2
  have hOne : pCoreOf 2 P ≠ ⊥ := fun hb => hR (le_bot_iff.mp (hb ▸ hO))
  have hOp : IsPGroup 2 (pCoreOf 2 P) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥P) 2).map P.subtype
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 P : Set D)) :=
    ⟨pCoreOf 2 P, hOne, hOp, rfl⟩
  have heq := hmax _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  exact le_antisymm
    ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P).trans heq.le)
    Subgroup.le_normalizer

theorem exists_mem_normalizer_of_normalizes {TD H : Subgroup D} [Finite ↥H] (hTH : TD ≤ H)
    (hp : IsPGroup 2 TD) (hi : ¬ 2 ∣ TD.index) {d : D} (hd : d ∈ Subgroup.normalizer (H : Set D)) :
    ∃ g ∈ H, g⁻¹ * d ∈ Subgroup.normalizer (TD : Set D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup ↥H := TD.subgroupOf H with hS
  have hSp : IsPGroup 2 ↥S := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hSi : ¬ 2 ∣ S.index := by
    have h1 : S.index = TD.relIndex H := rfl
    have h2 := Subgroup.relIndex_mul_relIndex TD H ⊤ hTH le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h2
    intro hd2
    have h3 : 2 ∣ TD.relIndex H * H.index := Dvd.dvd.mul_right (h1 ▸ hd2) _
    rw [h2] at h3
    exact hi h3
  let σ : ↥H ≃* ↥H := H.normalizerMonoidHom ⟨d, hd⟩
  have hσ : ∀ a : ↥H, ((σ a : ↥H) : D) = d * a * d⁻¹ := fun a =>
    H.normalizerMonoidHom_apply_apply_coe ⟨d, hd⟩ a
  have hS'p : IsPGroup 2 ↥(S.map σ.toMonoidHom) := hSp.map σ.toMonoidHom
  have hS'i : ¬ 2 ∣ (S.map σ.toMonoidHom).index := by
    rw [show (S.map σ.toMonoidHom).index = S.index from Subgroup.index_map_equiv S σ]
    exact hSi
  let P₀ : Sylow 2 ↥H := hSp.toSylow hSi
  let P₁ : Sylow 2 ↥H := hS'p.toSylow hS'i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) P₀ P₁
  have hgsub : MulAut.conj g • S = S.map σ.toMonoidHom := by
    have := congrArg (fun P : Sylow 2 ↥H => (P : Subgroup ↥H)) hg
    simpa [Sylow.coe_subgroup_smul, P₀, P₁] using this
  refine ⟨(g : D), g.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have htS : (⟨t, hTH ht⟩ : ↥H) ∈ S := ht
    have h1 : σ ⟨t, hTH ht⟩ ∈ MulAut.conj g • S := by
      rw [hgsub]; exact ⟨_, htS, rfl⟩
    rw [Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hsg⟩ := h1
    have hs' : ((s : ↥H) : D) ∈ TD := hs
    have e : (g : D) * (s : D) * (g : D)⁻¹ = d * t * d⁻¹ := by
      have := congrArg Subtype.val hsg
      rw [hσ] at this
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have : (g : D)⁻¹ * d * t * ((g : D)⁻¹ * d)⁻¹ = (s : D) := by
      calc (g : D)⁻¹ * d * t * ((g : D)⁻¹ * d)⁻¹
          = (g : D)⁻¹ * (d * t * d⁻¹) * (g : D) := by group
        _ = (g : D)⁻¹ * ((g : D) * (s : D) * (g : D)⁻¹) * (g : D) := by rw [e]
        _ = (s : D) := by group
    rw [this]; exact hs'
  · intro ht
    have hu : (g : D)⁻¹ * d * t * ((g : D)⁻¹ * d)⁻¹ ∈ TD := ht
    set u : D := (g : D)⁻¹ * d * t * ((g : D)⁻¹ * d)⁻¹ with hu_def
    have e : d * t * d⁻¹ = (g : D) * u * (g : D)⁻¹ := by
      rw [hu_def]; group
    have huS : (⟨u, hTH hu⟩ : ↥H) ∈ S := hu
    have h1 : MulAut.conj g • (⟨u, hTH hu⟩ : ↥H) ∈ MulAut.conj g • S :=
      ⟨_, huS, rfl⟩
    rw [hgsub] at h1
    obtain ⟨s, hs, hsg⟩ := h1
    have e2 : d * (s : D) * d⁻¹ = (g : D) * u * (g : D)⁻¹ := by
      have := congrArg Subtype.val hsg
      have h5 : ((σ.toMonoidHom s : ↥H) : D) = d * (s : D) * d⁻¹ := hσ s
      rw [h5] at this
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have : (s : D) = t := by
      have h3 : d * (s : D) * d⁻¹ = d * t * d⁻¹ := e2.trans e.symm
      have h4 : d * (s : D) = d * t := mul_right_cancel h3
      exact mul_left_cancel h4
    rw [← this]; exact hs

theorem yamPair_normalizer_le {TD P₁ P₂ : Subgroup D} (h : IsYAmalgamPair TD P₁ P₂) :
    Subgroup.normalizer (TD : Set D) ≤ P₁ ⊓ P₂ :=
  le_inf ((h.2.2 P₁).mpr (Or.inl rfl)).2 ((h.2.2 P₂).mpr (Or.inr rfl)).2

theorem yamPair_left {TD P₁ P₂ : Subgroup D} (h : IsYAmalgamPair TD P₁ P₂) :
    IsMaximalTwoLocal P₁ := ((h.2.2 P₁).mpr (Or.inl rfl)).1

theorem yamPair_right {TD P₁ P₂ : Subgroup D} (h : IsYAmalgamPair TD P₁ P₂) :
    IsMaximalTwoLocal P₂ := ((h.2.2 P₂).mpr (Or.inr rfl)).1

theorem normalizer_inf_eq {TD P₁ P₂ : Subgroup D} (h : IsYAmalgamPair TD P₁ P₂)
    [Finite ↥(P₁ ⊓ P₂)] : Subgroup.normalizer ((P₁ ⊓ P₂ : Subgroup D) : Set D) = P₁ ⊓ P₂ := by
  refine le_antisymm (fun d hd => ?_) Subgroup.le_normalizer
  have hTH : TD ≤ P₁ ⊓ P₂ := Subgroup.le_normalizer.trans (yamPair_normalizer_le h)
  have hi : ¬ 2 ∣ TD.index := by
    have := h.1.2.2
    rwa [show (TD.subgroupOf ⊤).index = TD.index from Subgroup.relIndex_top_right TD] at this
  obtain ⟨g, hg, hgn⟩ := exists_mem_normalizer_of_normalizes hTH h.1.2.1 hi hd
  have : g⁻¹ * d ∈ P₁ ⊓ P₂ := yamPair_normalizer_le h hgn
  have := (P₁ ⊓ P₂).mul_mem hg this
  simpa using this

end S1421QA18

end CFSG.Quasithin
