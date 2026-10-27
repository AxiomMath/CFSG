module

public import CFSG.Quasithin.Vol2.Ch11SecU1Out2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem pslRange_le_range {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι) :
    pGammaL2PSLRange K ≤ ι.range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨embL e c, iota_embL h c⟩

omit [Finite K] in
theorem sigmaFacts_of_adapted {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι)
    {b : G} (hσ : SigmaFacts (pGammaL2PSLRange K) (ι b)) : SigmaFacts L b := by
  obtain ⟨M, hM, hs, ⟨x, y, hxy⟩, hnorm, hcent⟩ := hσ
  have hMr : M ≤ ι.range := (hM.trans inf_le_left).trans (pslRange_le_range h)
  set L₀ := M.comap ι with hL₀
  have hmap : L₀.map ι = M := by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hMr]
  set d : ↥L₀ ≃* ↥M := (L₀.equivMapOfInjective ι h.1).trans (MulEquiv.subgroupCongr hmap)
  have hcomm : ∀ u w : G, ι u * ι w = ι w * ι u → u * w = w * u := fun u w huw =>
    h.1 (by rw [map_mul, map_mul, huw])
  refine ⟨L₀, fun w hw => ?_, d.isSimpleGroup, ⟨d.symm x, d.symm y, fun he => hxy ?_⟩,
    fun c hc => ?_, ?_⟩
  · have hw' := hM hw
    refine ⟨(mem_iff_of_adapted h).mpr hw'.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact hcomm w b (Subgroup.mem_centralizer_singleton_iff.mp hw'.2)
  · exact d.symm.injective (by rw [map_mul, map_mul, he])
  · have hc' : ι c ∈ Subgroup.centralizer ({ι b} : Set (PGammaL2 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have := Subgroup.mem_normalizer_iff.mp (hnorm hc') (ι w)
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact this
  · refine le_bot_iff.mp fun w hw => ?_
    have hw' : ι w ∈ pGammaL2PSLRange K ⊓ Subgroup.centralizer (M : Set (PGammaL2 K)) := by
      refine ⟨(mem_iff_of_adapted h).mp hw.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      obtain ⟨u, hu⟩ := hMr hz
      have huL₀ : u ∈ L₀ := by rw [hL₀, Subgroup.mem_comap, hu]; exact hz
      rw [← hu, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hw.2 u huL₀]
    rw [hcent, Subgroup.mem_bot] at hw'
    exact Subgroup.mem_bot.mpr (h.1 (hw'.trans (map_one ι).symm))

theorem ringAut_eq_of_sq' {σ τ : K ≃+* K} (hσ : σ * σ = 1) (hτ : τ * τ = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  by_contra hne
  have := isCyclic_ringAut K
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) two_pos
  have hsub : ({1, σ, τ} : Finset (K ≃+* K)) ⊆ Finset.univ.filter fun x => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
    rcases hx with rfl | rfl | rfl
    · exact mul_one 1
    · exact hσ
    · exact hτ
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hσ1, Ne.symm hτ1]),
    Finset.card_pair hne] at hcard
  omega

theorem outer_pair_of_adapted {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKc : Nat.card K = p ^ 2) {t₁ t₂ : G} (h₁ : t₁ ∉ L)
    (h₂ : t₂ ∉ L) (o₁ : orderOf t₁ = 2) (o₂ : orderOf t₂ = 2) (hc : t₁ * t₂ = t₂ * t₁) :
    t₁ * t₂ ∈ L := by
  have hsq : ∀ t : G, orderOf t = 2 → ι t * ι t = 1 := fun t ht => by
    have h1 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    rw [← map_mul, ← sq, h1, map_one]
  have hJ : ∀ t : G, t ∉ L → ι t ∉ pGammaL2PSLRange K := fun t ht hJ =>
    ht ((mem_iff_of_adapted h).mpr hJ)
  have hinl : ∀ v : PGammaL2 K, v.right = 1 → v = SemidirectProduct.inl v.left := fun v hv => by
    rw [← SemidirectProduct.inl_left_mul_inr_right v, hv, map_one, mul_one,
      SemidirectProduct.left_inl]
  have hcI : ι t₁ * ι t₂ = ι t₂ * ι t₁ := by rw [← map_mul, ← map_mul, hc]
  rw [mem_iff_of_adapted h, map_mul]
  by_cases r₁ : (ι t₁).right = 1 <;> by_cases r₂ : (ι t₂).right = 1
  · have hs : ∀ t : G, t ∉ L → (ι t).right = 1 → ¬ SqLeft (ι t) := fun t ht hr hs =>
      hJ t ht ((mem_pslRange_iff _).mpr ⟨hr, hs⟩)
    exact mul_mem_pslRange_of_not r₁ r₂ (hs t₁ h₁ r₁) (hs t₂ h₂ r₂)
  · exfalso
    apply hJ t₁ h₁
    obtain ⟨g, hg⟩ : ∃ g, ι t₁ = SemidirectProduct.inl g := ⟨_, hinl _ r₁⟩
    rw [hg] at hcI ⊢
    exact mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₂) (hsq t₂ o₂) r₂ g hcI.symm
  · exfalso
    apply hJ t₂ h₂
    obtain ⟨g, hg⟩ : ∃ g, ι t₂ = SemidirectProduct.inl g := ⟨_, hinl _ r₂⟩
    rw [hg] at hcI ⊢
    exact mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₁) (hsq t₁ o₁) r₁ g hcI
  · have hrr : ∀ t : G, orderOf t = 2 → (ι t).right * (ι t).right = 1 := fun t ht => by
      have := congrArg SemidirectProduct.right (hsq t ht)
      simpa using this
    have heq := ringAut_eq_of_sq' (hrr t₁ o₁) (hrr t₂ o₂) r₁ r₂
    have hr : (ι t₁ * ι t₂).right = 1 := by
      rw [SemidirectProduct.mul_right, heq, hrr t₂ o₂]
    obtain ⟨g, hg⟩ : ∃ g, ι t₁ * ι t₂ = SemidirectProduct.inl g := ⟨_, hinl _ hr⟩
    rw [hg]
    refine mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₁) (hsq t₁ o₁) r₁ g ?_
    rw [← hg]
    calc ι t₁ * (ι t₁ * ι t₂) = ι t₁ * (ι t₂ * ι t₁) := by rw [hcI]
      _ = ι t₁ * ι t₂ * ι t₁ := by rw [mul_assoc]

end CFSG.Quasithin.Vol2.Ch11.SecU1
