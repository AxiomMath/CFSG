module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Goursat
public import CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.NonabelianOrder
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

section

variable {K M : Type*} [Group K] [Group M]

theorem ker_pr₁_eq_bot [IsSimpleGroup M] (D : Subgroup (K × M)) (h₁ : Function.Surjective (pr₁ D))
    (h₂ : Function.Surjective (pr₂ D)) (hD : D ≠ ⊤) : (pr₁ D).ker = ⊥ := by
  have : ((pr₁ D).ker.map (pr₂ D)).Normal := Subgroup.Normal.map inferInstance _ h₂
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pr₁ D).ker.map (pr₂ D)) with h | h
  · rw [eq_bot_iff]
    intro d hd
    have : pr₂ D d ∈ ((pr₁ D).ker.map (pr₂ D)) := Subgroup.mem_map_of_mem _ hd
    rw [h] at this
    have h2 : pr₂ D d = 1 := by simpa using this
    have h1 : pr₁ D d = 1 := hd
    have : d = 1 := Subtype.ext (Prod.ext h1 h2)
    simpa using this
  · exfalso
    apply hD
    rw [eq_top_iff]
    rintro ⟨g, m⟩ -
    obtain ⟨d, hd⟩ := h₁ g
    have hm : d.1.2⁻¹ * m ∈ ((pr₁ D).ker.map (pr₂ D)) := by rw [h]; trivial
    obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.mp hm
    have hk1 : k.1.1 = 1 := hk
    have hkm' : k.1.2 = d.1.2⁻¹ * m := hkm
    have : (g, m) = (d * k : D).1 := by
      ext
      · simp [hk1, ← hd]
      · simp [hkm']
    rw [this]
    exact (d * k).2

theorem eq_top_of_index_le_two [Finite M] [IsSimpleGroup M] (hM : ∃ a b : M, a * b ≠ b * a)
    {X : Subgroup M} (hX : X.index ≤ 2) : X = ⊤ := by
  have hpos : X.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : X.index = 1 ∨ X.index = 2 := by omega
  rcases h12 with hi | hi
  · exact Subgroup.index_eq_one.mp hi
  · have hnorm : X.Normal := Subgroup.normal_of_index_eq_two hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
    · exfalso
      rw [h, Subgroup.index_bot] at hi
      have := CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.three_lt_natCard_of_noncomm hM
      omega
    · exact h

theorem ker_le_center_of_card_le_three [Finite K] [Finite M] [IsSimpleGroup M]
    (hM : ∃ a b : M, a * b ≠ b * a) (ρ : K →* M) (hρ : Function.Surjective ρ)
    (hN : Nat.card ρ.ker ≤ 3) : ρ.ker ≤ Subgroup.center K := by
  set N := ρ.ker with hNdef
  have hcomm : ∀ a b : N, a * b = b * a :=
    CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.commute_of_natCard_le_three hN
  intro n hn
  by_cases hn1 : n = 1
  · rw [hn1]; exact Subgroup.one_mem _
  have hcls : (conjugatesOf n).ncard ≤ 2 := by
    have hsub : conjugatesOf n ⊆ (N : Set K) \ {1} := by
      intro x hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hxN : x ∈ N := by
        rw [← hc]
        exact (inferInstance : N.Normal).conj_mem n hn c
      refine ⟨hxN, ?_⟩
      rintro (h : x = 1)
      apply hn1
      have : c * n * c⁻¹ = 1 := hc.trans h
      calc n = c⁻¹ * (c * n * c⁻¹) * c := by group
        _ = 1 := by rw [this]; group
    have h1 : (N : Set K).ncard ≤ 3 := by
      rw [← Nat.card_coe_set_eq]; exact hN
    have h2 : ((N : Set K) \ {1}).ncard = (N : Set K).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem N)
    calc (conjugatesOf n).ncard ≤ ((N : Set K) \ {1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by omega
  have hidx : (Subgroup.centralizer ({n} : Set K)).index ≤ 2 := by
    rw [Subgroup.index_centralizer_eq_ncard]; exact hcls
  have hNC : N ≤ Subgroup.centralizer ({n} : Set K) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hcomm ⟨n, hn⟩ ⟨m, hm⟩)).symm
  set C := Subgroup.centralizer ({n} : Set K) with hC
  have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmap : (C.map ρ).index ≤ 2 :=
    (Nat.le_of_dvd hpos (Subgroup.index_map_dvd C hρ)).trans hidx
  have htop : C.map ρ = ⊤ := eq_top_of_index_le_two hM hmap
  have hCtop : C = ⊤ := by
    rw [eq_top_iff]
    intro c _
    have : ρ c ∈ C.map ρ := by rw [htop]; trivial
    obtain ⟨c', hc', hcc⟩ := Subgroup.mem_map.mp this
    have hmem : c'⁻¹ * c ∈ N := by
      rw [hNdef, MonoidHom.mem_ker, map_mul, map_inv, hcc, inv_mul_cancel]
    have := C.mul_mem hc' (hNC hmem)
    simpa using this
  rw [Subgroup.mem_center_iff]
  intro c
  have hc : c ∈ C := by rw [hCtop]; trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp hc

theorem exists_mulEquiv_of_subdirect_center_trivial [Finite K] [Finite M] [IsSimpleGroup M]
    (hM : ∃ a b : M, a * b ≠ b * a) (D : Subgroup (K × M))
    (h₁ : Function.Surjective (pr₁ D)) (h₂ : Function.Surjective (pr₂ D))
    (hD : Nat.card D < Nat.card K * Nat.card M) (hker : Nat.card (pr₂ D).ker ≤ 3)
    (hZ : ∀ c ∈ Subgroup.center K, c = 1) : ∃ Θ : K ≃* M, ∀ d ∈ D, Θ d.1 = d.2 := by
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, Nat.card_congr (Subgroup.topEquiv (G := K × M)).toEquiv, Nat.card_prod] at hD
    exact lt_irrefl _ hD
  have hk1 := ker_pr₁_eq_bot D h₁ h₂ hDtop
  have hbij : Function.Bijective (pr₁ D) := ⟨(MonoidHom.ker_eq_bot_iff _).mp hk1, h₁⟩
  let eK : D ≃* K := MulEquiv.ofBijective (pr₁ D) hbij
  let ρ : K →* M := (pr₂ D).comp eK.symm.toMonoidHom
  have hρ : Function.Surjective ρ := h₂.comp eK.symm.surjective
  have hρker : Nat.card ρ.ker ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : ρ.ker => (⟨eK.symm k.1, k.2⟩ : (pr₂ D).ker)) ?_) hker
    intro a b hab
    apply Subtype.ext
    exact eK.symm.injective (congrArg (fun x : (pr₂ D).ker => (x : D)) hab)
  have hc := ker_le_center_of_card_le_three hM ρ hρ hρker
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have := hZ k (hc hk)
    simpa using this
  refine ⟨MulEquiv.ofBijective ρ ⟨hρinj, hρ⟩, fun d hd => ?_⟩
  have h1 : eK.symm d.1 = ⟨d, hd⟩ := by
    apply eK.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show ρ d.1 = d.2
  simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  rfl

theorem exists_mulEquiv_of_closure_pairs {ι : Type*} [Finite K] [Finite M] [IsSimpleGroup M]
    (hM : ∃ a b : M, a * b ≠ b * a) (g : ι → K) (m : ι → M)
    (h₁ : Function.Surjective (pr₁ (Subgroup.closure (Set.range fun i => (g i, m i)))))
    (h₂ : Function.Surjective (pr₂ (Subgroup.closure (Set.range fun i => (g i, m i)))))
    (hD : Nat.card (Subgroup.closure (Set.range fun i => (g i, m i))) < Nat.card K * Nat.card M)
    (hker : Nat.card (pr₂ (Subgroup.closure (Set.range fun i => (g i, m i)))).ker ≤ 3)
    (hZ : ∀ c ∈ Subgroup.center K, c = 1) : ∃ Θ : K ≃* M, ∀ i, Θ (g i) = m i := by
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_of_subdirect_center_trivial hM
    (Subgroup.closure (Set.range fun i => (g i, m i))) h₁ h₂ hD hker hZ
  exact ⟨Θ, fun i => hΘ (g i, m i) (Subgroup.subset_closure ⟨i, rfl⟩)⟩

end

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
