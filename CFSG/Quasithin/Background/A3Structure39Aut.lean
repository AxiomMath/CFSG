
module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.A3Structure38Facts

public section

namespace CFSG.Quasithin

namespace A38

open CFSG.Open CFSG.SectionRank

theorem exists_inner_of_outSolvable {X : Type} [Group X] (hX : OutSolvable X) {Γ : Type} [Group Γ]
    (hΓ : Group.IsPerfect Γ) (ψ : Γ →* MulAut X) (γ : Γ) :
    ∃ x : X, ψ γ = MulAut.conj x := by
  obtain ⟨n, hn⟩ := hX
  have hds : ∀ m : ℕ, derivedSeries Γ m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero Γ
    | succ m ih => rw [derivedSeries_succ, ih]; exact Group.isPerfect_def.mp hΓ
  have h1 : ψ γ ∈ (derivedSeries Γ n).map ψ := Subgroup.mem_map_of_mem ψ (by rw [hds n]; trivial)
  have h2 := hn (map_derivedSeries_le_derivedSeries ψ n h1)
  obtain ⟨x, hx⟩ := h2
  exact ⟨x, hx.symm⟩

variable {G : Type} [Group G]

theorem eq_or_eq_of_le_sup [Finite G] (h37 : A37Statement G) {K L M : Subgroup G}
    (hK : K ∈ cComp (⊤ : Subgroup G)) (hL : L ∈ cComp (⊤ : Subgroup G))
    (hM : M ∈ cComp (⊤ : Subgroup G)) (hKLM : K ≤ L ⊔ M) : K = L ∨ K = M := by
  by_contra hcon
  push Not at hcon
  have h1 := h37 K hK L hL hcon.1
  have h2 := h37 K hK M hM hcon.2
  have hcL : ∀ k ∈ K, ∀ l ∈ L, l * k = k * l := fun k hk l hl =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hk) l hl
  have hcM : ∀ k ∈ K, ∀ l ∈ M, l * k = k * l := fun k hk l hl =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2 hk) l hl
  have hKabel : ⁅K, K⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    have hle : L ⊔ M ≤ Subgroup.centralizer ({k} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hcL k hk l hl).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hcM k hk l hl).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle (hKLM hk')) k rfl).symm
  exact ne_bot_of_mem_cComp hK (by rw [← perfect_of_mem_cComp hK]; exact hKabel)

theorem perfectCore_le_layer {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.solvableRadical Q = ⊥)
    (hnorm : ∀ K : Subgroup Q, CFSG.IsComponent K →
      perfectCore (⊤ : Subgroup Q) ≤ Subgroup.normalizer (K : Set Q))
    (hout : ∀ K : Subgroup Q, CFSG.IsComponent K → OutSolvable ↥K) :
    perfectCore (⊤ : Subgroup Q) ≤ CFSG.layer Q := by
  classical
  intro t ht
  have hinner : ∀ K : Subgroup Q, CFSG.IsComponent K →
      ∃ k ∈ K, ∀ y ∈ K, t * y * t⁻¹ = k * y * k⁻¹ := by
    intro K hK
    have hT : perfectCore (⊤ : Subgroup Q) ≤ Subgroup.normalizer (K : Set Q) := hnorm K hK
    let ψ : ↥(perfectCore (⊤ : Subgroup Q)) →* MulAut ↥K :=
      (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hT)
    have hperf : Group.IsPerfect ↥(perfectCore (⊤ : Subgroup Q)) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect ⊤)
    obtain ⟨x, hx⟩ := exists_inner_of_outSolvable (hout K hK) hperf ψ ⟨t, ht⟩
    refine ⟨x, x.2, fun y hy => ?_⟩
    have := congrArg (fun φ => ((φ ⟨y, hy⟩ : ↥K) : Q)) hx
    simpa [ψ, MulAut.conj_apply] using this
  have key : ∀ S : Finset (Subgroup Q), (∀ K ∈ S, CFSG.IsComponent K) →
      ∃ e ∈ (⨆ K ∈ S, K : Subgroup Q), ∀ K ∈ S, ∀ y ∈ K, t * y * t⁻¹ = e * y * e⁻¹ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    | insert K₀ S hK₀ ih =>
      intro hS
      obtain ⟨e, he, hes⟩ := ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
      have hK₀c : CFSG.IsComponent K₀ := hS K₀ (Finset.mem_insert_self _ _)
      obtain ⟨k₀, hk₀, hk₀y⟩ := hinner K₀ hK₀c
      have hcomm : ∀ K ∈ S, ∀ x ∈ K, ∀ y ∈ K₀, x * y = y * x := by
        intro K hK x hx y hy
        have hKc : CFSG.IsComponent K := hS K (Finset.mem_insert_of_mem hK)
        rcases CFSG.LocalCores.distinct_components_commute hKc hK₀c with h | h
        · exact absurd (h ▸ hK) hK₀
        · exact Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy |>.symm
      have heK₀ : ∀ y ∈ K₀, e * y = y * e := by
        have hle : (⨆ K ∈ S, K : Subgroup Q) ≤ Subgroup.centralizer (K₀ : Set Q) := by
          refine iSup₂_le fun K hK x hx => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (hcomm K hK x hx y hy).symm
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hle he) y hy).symm
      have hle1 : (⨆ K ∈ S, K : Subgroup Q) ≤ ⨆ K ∈ insert K₀ S, K :=
        iSup₂_le fun K hK => le_iSup₂_of_le K (Finset.mem_insert_of_mem hK) le_rfl
      have hle2 : K₀ ≤ ⨆ K ∈ insert K₀ S, K :=
        le_iSup₂_of_le K₀ (Finset.mem_insert_self _ _) le_rfl
      refine ⟨e * k₀, Subgroup.mul_mem _ (hle1 he) (hle2 hk₀), fun K hK y hy => ?_⟩
      have hconj : (e * k₀) * y * (e * k₀)⁻¹ = e * (k₀ * y * k₀⁻¹) * e⁻¹ := by group
      rw [hconj]
      rcases Finset.mem_insert.mp hK with rfl | hK'
      · rw [hk₀y y hy]
        have hym : k₀ * y * k₀⁻¹ ∈ K := Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₀ hy)
          (Subgroup.inv_mem _ hk₀)
        rw [heK₀ _ hym]
        group
      · have h1 : k₀ * y * k₀⁻¹ = y := by
          rw [(hcomm K hK' y hy k₀ hk₀).symm]
          group
        rw [h1]
        exact hes K hK' y hy
  have hfin : Set.Finite {K : Subgroup Q | CFSG.IsComponent K} := Set.toFinite _
  obtain ⟨e, he, hes⟩ := key hfin.toFinset (fun K hK => by simpa using hK)
  have heL : e ∈ CFSG.layer Q := by
    have : (⨆ K ∈ hfin.toFinset, K : Subgroup Q) ≤ CFSG.layer Q :=
      iSup₂_le fun K hK => le_sSup (by simpa using hK)
    exact this he
  have hc : e⁻¹ * t ∈ Subgroup.centralizer (CFSG.layer Q : Set Q) := by
    have hle : CFSG.layer Q ≤ Subgroup.centralizer ({e⁻¹ * t} : Set Q) := by
      refine sSup_le fun K hK z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := hes K (by simpa using hK) z hz
      have h2 : (e⁻¹ * t) * z * (e⁻¹ * t)⁻¹ = z := by
        have : (e⁻¹ * t) * z * (e⁻¹ * t)⁻¹ = e⁻¹ * (t * z * t⁻¹) * e := by group
        rw [this, h1]
        group
      calc (e⁻¹ * t) * z = ((e⁻¹ * t) * z * (e⁻¹ * t)⁻¹) * (e⁻¹ * t) := by group
        _ = z * (e⁻¹ * t) := by rw [h2]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (hle hz) (e⁻¹ * t) rfl
    exact this.symm
  have hF : CFSG.fittingSubgroup Q = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hQ]
    exact A3.le_solvableRadical inferInstance inferInstance
  have hgf : CFSG.generalizedFitting Q = CFSG.layer Q := by
    rw [CFSG.generalizedFitting, hF, bot_sup_eq]
  have hcL : e⁻¹ * t ∈ CFSG.layer Q := by
    have := CFSG.centralizer_generalizedFitting_le Q
    rw [hgf] at this
    exact this hc
  have : t = e * (e⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem _ heL hcL

end A38

end CFSG.Quasithin
