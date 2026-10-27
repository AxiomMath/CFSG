module

public import CFSG.Milestones.ASVolI.A3Aut.Model

public section

namespace CFSG.ASVolI

open CFSG.Open

section Case5

variable {G : Type} [Group G]

theorem burnsideAut_conjNormal_injective {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    [L.Normal] : Function.Injective (MulAut.conjNormal : G →* MulAut ↥L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [burnsideA315x_centralizer_eq_bot h] at hc
  exact hc

theorem burnsideAut_map_le_normalizer_map {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f : H₁ →* H₂)
    {X Y : Subgroup H₁} (hY : Y ≤ Subgroup.normalizer (X : Set H₁)) :
    Y.map f ≤ Subgroup.normalizer ((X.map f : Subgroup H₂) : Set H₂) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hY hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hy'
  conv_rhs => rw [← hy']
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem burnsideAut_map_equiv_le_normalizer {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f : H₁ ≃* H₂)
    {X Y : Subgroup H₁} (hY : Y ≤ Subgroup.normalizer (X : Set H₁)) :
    Y.map f.toMonoidHom ≤ Subgroup.normalizer ((X.map f.toMonoidHom : Subgroup H₂) : Set H₂) :=
  burnsideAut_map_le_normalizer_map f.toMonoidHom hY

theorem burnsideAut_map_inf_normalizer {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f : H₁ ≃* H₂)
    (X Y : Subgroup H₁) :
    (X ⊓ Subgroup.normalizer (Y : Set H₁)).map f.toMonoidHom =
      X.map f.toMonoidHom ⊓ Subgroup.normalizer ((Y.map f.toMonoidHom : Subgroup H₂) : Set H₂) := by
  rw [Subgroup.map_inf _ _ _ f.injective, Subgroup.map_equiv_normalizer_eq]

theorem burnsideAut_congr_symm_congr {S M : Type*} [Group S] [Group M] (e : S ≃* M) (x : MulAut S) :
    MulAut.congr e.symm (MulAut.congr e x) = x := by
  ext y
  simp [MulAut.congr_apply]

theorem burnsideAut_case5_of_model {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) [hLn : L.Normal]
    (n : ℕ) (hn : 2 ≤ n) (hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L)
    {M : Type} [Group M] (e : ↥L ≃* M) {UM : Subgroup M}
    (heU : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = UM)
    {IM ΦM HM : Subgroup (MulAut M)}
    (hInn : (MulAut.conj : M →* MulAut M).range ≤ IM)
    (hIJ : IM.map (MulAut.congr e.symm).toMonoidHom ≤ ChA.innDiagSubgroup ↥L)
    (hΦI : ΦM ≤ Subgroup.normalizer (IM : Set (MulAut M))) (hIΦ : IM ⊓ ΦM = ⊥)
    (hΦU : ΦM ≤ Subgroup.normalizer
      ((UM.map (MulAut.conj : M →* MulAut M) : Subgroup (MulAut M)) : Set (MulAut M)))
    (hNU : IM ⊓ Subgroup.normalizer
      ((UM.map (MulAut.conj : M →* MulAut M) : Subgroup (MulAut M)) : Set (MulAut M)) =
        UM.map (MulAut.conj : M →* MulAut M) ⊔ HM)
    (hHI : HM ≤ IM)
    (hHU : HM ≤ Subgroup.normalizer
      ((UM.map (MulAut.conj : M →* MulAut M) : Subgroup (MulAut M)) : Set (MulAut M)))
    (hHodd : Odd (Nat.card HM)) (hΦH : ΦM ≤ Subgroup.normalizer (HM : Set (MulAut M)))
    (hB : ∀ b ∈ B, MulAut.congr e (MulAut.conjNormal b) ∈ IM ⊔ ΦM)
    (hsb : burnsideAut_SolvBorel M UM)
    (hpin : ∀ ε : ↥L ≃* M, ((T ⊓ L).subgroupOf L).map ε.toMonoidHom = UM →
      ∀ F : Subgroup (MulAut ↥L), F ≤ ΦM.map (MulAut.congr ε.symm).toMonoidHom →
        Odd (Nat.card F) →
        (∀ x ∈ F, ∃ b ∈ B, x * (MulAut.conjNormal b)⁻¹ ∈
          IM.map (MulAut.congr ε.symm).toMonoidHom) →
        IsCyclic F ∧ Nat.card F ∣ n ∧ ChA.A315PinnedFieldGroup n ↥L ((T ⊓ L).subgroupOf L) F) :
    ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  set α : G →* MulAut ↥L := MulAut.conjNormal with hα
  have hαinj : Function.Injective α := burnsideAut_conjNormal_injective h
  set S : Subgroup ↥L := (T ⊓ L).subgroupOf L with hS
  set ψ : MulAut M ≃* MulAut ↥L := MulAut.congr e.symm with hψ
  set I : Subgroup (MulAut ↥L) := IM.map ψ.toMonoidHom with hI
  set Φ : Subgroup (MulAut ↥L) := ΦM.map ψ.toMonoidHom with hΦ
  set H₀ : Subgroup (MulAut ↥L) := HM.map ψ.toMonoidHom with hH₀
  set J : Subgroup (MulAut ↥L) := ChA.innDiagSubgroup ↥L with hJ
  set Lb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L L with hLb
  set Sb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L (T ⊓ L) with hSb
  set Bb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L B with hBb
  set UbM : Subgroup (MulAut M) := UM.map (MulAut.conj : M →* MulAut M) with hUbM
  have hSbeq : Sb = S.map (MulAut.conj : ↥L →* MulAut ↥L) :=
    burnsideAut_autImage_of_le inf_le_right
  have hLbeq : Lb = (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rw [hLb, burnsideAut_autImage_of_le le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have heS : UM.map e.symm.toMonoidHom = S := by
    rw [← heU, Subgroup.map_map]
    convert Subgroup.map_id S
    ext x
    simp
  have hSbψ : Sb = UbM.map ψ.toMonoidHom := by
    rw [hSbeq, hUbM, hψ]
    have := burnsideAut_map_congr_conj e.symm UM
    rw [this, heS]
  have hSbLb : Sb ≤ Lb := by
    rw [hSbeq, hLbeq]
    exact Subgroup.map_le_range _ _
  have hLbI : Lb ≤ I := by
    rw [hLbeq]
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e y), hInn ⟨e y, rfl⟩, ?_⟩
    change MulAut.congr e.symm (MulAut.conj (e y)) = MulAut.conj y
    rw [burnsideAut_congr_conj]
    simp
  have hIJ' : I ≤ J := hIJ
  have hΦI' : Φ ≤ Subgroup.normalizer (I : Set (MulAut ↥L)) := burnsideAut_map_equiv_le_normalizer ψ hΦI
  have hIΦ' : I ⊓ Φ = ⊥ := by
    rw [hI, hΦ, ← Subgroup.map_inf _ _ _ ψ.injective, hIΦ, Subgroup.map_bot]
  have hΦJ : Φ ≤ Subgroup.normalizer (J : Set (MulAut ↥L)) := by
    haveI := burnsideAut_innDiag_normal ↥L
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hΦS : Φ ≤ Subgroup.normalizer (Sb : Set (MulAut ↥L)) := by
    rw [hSbψ]
    exact burnsideAut_map_equiv_le_normalizer ψ hΦU
  have hNS : I ⊓ Subgroup.normalizer (Sb : Set (MulAut ↥L)) = Sb ⊔ H₀ := by
    rw [hSbψ, hI, hH₀, ← burnsideAut_map_inf_normalizer, hNU, Subgroup.map_sup]
  have hH₀I : H₀ ≤ I := Subgroup.map_mono hHI
  have hH₀S : H₀ ≤ Subgroup.normalizer (Sb : Set (MulAut ↥L)) := by
    rw [hSbψ]
    exact burnsideAut_map_equiv_le_normalizer ψ hHU
  have hH₀odd : Odd (Nat.card H₀) := by
    rw [hH₀, Subgroup.card_map_of_injective ψ.injective]
    exact hHodd
  have hΦH₀ : Φ ≤ Subgroup.normalizer (H₀ : Set (MulAut ↥L)) :=
    burnsideAut_map_equiv_le_normalizer ψ hΦH
  have hSb2 : IsPGroup 2 Sb := (h.sylow.2.1.to_le inf_le_left).map α
  have hBΦ : Bb ≤ I ⊔ Φ := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := hB b hb
    have h2 : ψ (MulAut.congr e (α b)) = α b := burnsideAut_congr_symm_congr e (α b)
    rw [← h2, hI, hΦ, ← Subgroup.map_sup]
    exact ⟨_, h1, rfl⟩
  have hsbL : burnsideAut_SolvBorel ↥L S := by
    refine burnsideAut_solvBorel_of_mulEquiv e ?_
    rw [heU]
    exact hsb
  have hBN : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    burnsideAut_le_normalizer_of_hyp h hsbL
  have hBS : Bb ≤ Subgroup.normalizer (Sb : Set (MulAut ↥L)) :=
    burnsideAut_map_le_normalizer_map α hBN
  have hBodd : Odd (Nat.card Bb) := by
    rw [hBb, CFSG.Quasithin.A315.autImage, Subgroup.card_map_of_injective hαinj]
    exact h.odd
  obtain ⟨s, hs, F, H, hFΦ, hFdvd, hFS, hFH, hcart, heq, hle, hFI⟩ :=
    burnsideAut_case5_core hSbLb hLbI hIJ' hΦI' hIΦ' hΦJ hΦS hNS hH₀I hH₀S hH₀odd hΦH₀ hSb2 hBΦ
      hBS hBodd
  rw [hSbeq] at hs
  obtain ⟨l₀, hl₀, rfl⟩ := hs
  set ε : ↥L ≃* M := (MulAut.conj l₀⁻¹).trans e with hε
  have hεU : S.map ε.toMonoidHom = UM := by
    have h1 : S.map (MulAut.conj l₀⁻¹).toMonoidHom = S :=
      burnsideAut_map_conj_self (S.inv_mem hl₀)
    calc S.map ε.toMonoidHom
        = (S.map (MulAut.conj l₀⁻¹).toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map]; rfl
      _ = S.map e.toMonoidHom := by rw [h1]
      _ = UM := heU
  have hconj : ∀ X : Subgroup (MulAut M), (X.map ψ.toMonoidHom).map
      (MulAut.conj (MulAut.conj l₀)).toMonoidHom = X.map (MulAut.congr ε.symm).toMonoidHom := by
    intro X
    rw [Subgroup.map_map]
    congr 1
    ext x : 1
    exact burnsideAut_conj_congr_symm e l₀ x
  have hΦε : Φ.map (MulAut.conj (MulAut.conj l₀)).toMonoidHom =
      ΦM.map (MulAut.congr ε.symm).toMonoidHom := hconj ΦM
  have hIε : IM.map (MulAut.congr ε.symm).toMonoidHom = I := by
    rw [← hconj IM]
    exact burnsideAut_map_conj_self (hLbI (hSbLb (hSbeq ▸ ⟨l₀, hl₀, rfl⟩)))
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat hBodd hFdvd
  have hcond : ∀ x ∈ F, ∃ b ∈ B, x * (MulAut.conjNormal b)⁻¹ ∈
      IM.map (MulAut.congr ε.symm).toMonoidHom := by
    intro x hx
    obtain ⟨b', ⟨b, hb, rfl⟩, hxb⟩ := hFI x hx
    exact ⟨b, hb, hIε.symm ▸ hxb⟩
  obtain ⟨hcyc, hdvdn, hpinF⟩ := hpin ε hεU F (hΦε ▸ hFΦ) hFodd hcond
  exact ⟨hLn, n, hn, hLie, F, H, hcyc, hdvdn, hpinF, hFS, hFH, hcart, heq, hle⟩

end Case5

end CFSG.ASVolI
