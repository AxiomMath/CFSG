module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransBase

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

section Facts

theorem isSylowTwoOf_P0 :
    IsSylowTwoOf P0 ⊤ := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  let P0s : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  have h := K1.isSylowTwoOf_top_iff.2 ⟨P0s.isPGroup', P0s.not_dvd_index⟩
  rwa [Sylow.coe_ofCard] at h

theorem z0L_closed : 0 ∈ z0L ∧ ∀ x ∈ z0L, ∀ y ∈ z0L, x ^^^ y ∈ z0L := by
  refine ⟨by simp [z0L], ?_⟩
  intro x hx y hy
  simp only [z0L, List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem z0_eq : z0 = eta uJ 11 1131 := rfl

theorem mem_z0Sub (hM : MatFacts) {x : J} :
    x ∈ maskSub z0L ↔ x = 1 ∨ x = z0 := by
  rw [mem_maskSub_iff hM z0L_closed.1 z0L_closed.2]
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [z0L, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl (eta_zero _ _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [z0L], (eta_zero _ _).symm⟩
    · exact ⟨1131, by simp [z0L], rfl⟩

theorem z0_ne_one (hM : MatFacts) : z0 ≠ 1 := by
  intro h
  have h1 : eta uJ 11 1131 = eta uJ 11 0 := by rw [eta_zero]; exact h
  have := eta_inj' hM (by norm_num) (by norm_num) h1
  omega

theorem Eg_ne_bot (hF : J4Facts) : Eg uJ 11 ≠ ⊥ := by
  intro h
  have h1 := card_Eg_uJ hF.mat
  rw [h, Subgroup.card_bot] at h1
  norm_num at h1

theorem Eg_ne_top (hF : J4Facts) : Eg uJ 11 ≠ ⊤ := by
  intro h
  have h1 := card_Eg_uJ hF.mat
  rw [h, Subgroup.card_top, card_J hF] at h1
  norm_num at h1

theorem le_Eg_ne_top (hF : J4Facts) {N : Subgroup J} (h : N ≤ Eg uJ 11) : N ≠ ⊤ := fun hN =>
  Eg_ne_top hF (top_le_iff.1 (hN ▸ h))

theorem isPGroup_of_le_Eg (hF : J4Facts) {N : Subgroup J} (h : N ≤ Eg uJ 11) : IsPGroup 2 N :=
  (isPGroup_Eg (elem_uJ hF.mat)).to_le h

theorem Hj_isTwoLocalSub (hF : J4Facts) : ModH.IsTwoLocalSub Hj := by
  have := isSimpleGroup_J hF
  have h := isTwoLocalSub_normalizer (isPGroup_Eg (elem_uJ hF.mat)) (Eg_ne_bot hF) (Eg_ne_top hF)
  rwa [normalizer_Eg_eq_Hj hF] at h

theorem centralizer_z0_isTwoLocalSub (hF : J4Facts) :
    ModH.IsTwoLocalSub (Subgroup.centralizer ({z0} : Set J)) := by
  have hM := hF.mat
  have := isSimpleGroup_J hF
  have hle : maskSub z0L ≤ Eg uJ 11 := maskSub_le_Eg z0L
  have hne : maskSub z0L ≠ ⊥ := by
    intro h
    have : z0 ∈ maskSub z0L := (mem_z0Sub hM).2 (Or.inr rfl)
    rw [h, Subgroup.mem_bot] at this
    exact z0_ne_one hM this
  have h := isTwoLocalSub_normalizer (isPGroup_of_le_Eg hF hle) hne (le_Eg_ne_top hF hle)
  have heq : Subgroup.normalizer ((maskSub z0L : Subgroup J) : Set J) =
      Subgroup.centralizer ({z0} : Set J) := by
    ext x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 : x * z0 * x⁻¹ ∈ maskSub z0L := (hx z0).1 ((mem_z0Sub hM).2 (Or.inr rfl))
      rcases (mem_z0Sub hM).1 h1 with h2 | h2
      · exfalso
        apply z0_ne_one hM
        have e : z0 = x⁻¹ * (x * z0 * x⁻¹) * x := by group
        rw [e, h2]
        group
      · calc x * z0 = (x * z0 * x⁻¹) * x := by group
          _ = z0 * x := by rw [h2]
    · intro hx y
      have hc : ∀ w : J, w = 1 ∨ w = z0 → x * w * x⁻¹ = w := by
        rintro w (rfl | rfl)
        · group
        · calc x * z0 * x⁻¹ = (z0 * x) * x⁻¹ := by rw [hx]
            _ = z0 := by group
      constructor
      · intro hy
        rw [hc y ((mem_z0Sub hM).1 hy)]
        exact hy
      · intro hy
        have hy' := (mem_z0Sub hM).1 hy
        rcases hy' with h2 | h2
        · have : y = 1 := by
            have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
            rw [e, h2]
            group
          rw [this]
          exact Subgroup.one_mem _
        · have : y = z0 := by
            have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
            rw [e, h2]
            calc x⁻¹ * z0 * x = x⁻¹ * (z0 * x) := by group
              _ = x⁻¹ * (x * z0) := by rw [← hx]
              _ = z0 := by group
          rw [this]
          exact (mem_z0Sub hM).2 (Or.inr rfl)
  rwa [heq] at h

theorem V0_isTwoLocalSub (hF : J4Facts) :
    ModH.IsTwoLocalSub (Subgroup.normalizer (V0 : Set J)) := by
  have hM := hF.mat
  have := isSimpleGroup_J hF
  have hle : V0 ≤ Eg uJ 11 := fun x hx => V0_le_Eg hM hx
  have hne : V0 ≠ ⊥ := by
    intro h
    have h1 : eta uJ 11 422 ∈ V0 := Subgroup.subset_closure (by simp)
    rw [h, Subgroup.mem_bot] at h1
    have h2 : eta uJ 11 422 = eta uJ 11 0 := by rw [eta_zero]; exact h1
    have := eta_inj' hM (by norm_num) (by norm_num) h2
    omega
  exact isTwoLocalSub_normalizer (isPGroup_of_le_Eg hF hle) hne (le_Eg_ne_top hF hle)

end Facts

section Main

theorem j4MaxTwoLocalList :
    ∀ M : Subgroup J, ModH.IsMaxTwoLocal M → P0 ≤ M →
      M = Hj ∨ M = Subgroup.centralizer ({z0} : Set J) ∨ M = Subgroup.normalizer (V0 : Set J) := by
  intro M hM hP
  have hF : J4Facts := j4Facts
  obtain ⟨⟨hMtop, N, hN, hne, hMN⟩, hmax⟩ := hM
  have hP' : P0 ≤ Subgroup.normalizer (N : Set J) := by
    rw [hMN]
    exact hP
  rcases j4TwoLocalOvergroups N hN hne hP' with h | h | h
  · exact Or.inl (hmax Hj (Hj_isTwoLocalSub hF) (hMN ▸ h)).symm
  · exact Or.inr (Or.inl (hmax _ (centralizer_z0_isTwoLocalSub hF) (hMN ▸ h)).symm)
  · exact Or.inr (Or.inr (hmax _ (V0_isTwoLocalSub hF) (hMN ▸ h)).symm)

theorem j4MaxTwoLocalList_of_iso {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.Carrier .J4) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤)
    {M : Subgroup Q} (hM : ModH.IsMaxTwoLocal M) (hSM : S ≤ M) :
    ∃ ψ : Q ≃* J, Subgroup.map (ψ : Q →* ↥J) S = P0 ∧
      (Subgroup.map (ψ : Q →* ↥J) M = Hj ∨
        Subgroup.map (ψ : Q →* ↥J) M = Subgroup.centralizer ({z0} : Set J) ∨
        Subgroup.map (ψ : Q →* ↥J) M = Subgroup.normalizer (V0 : Set J)) := by
  have hF : J4Facts := j4Facts
  obtain ⟨ψ, hψ⟩ := sylow_transport (Γ := J) isSylowTwoOf_P0 (e.trans (seedEquiv hF.mat)) hS
  refine ⟨ψ, hψ, j4MaxTwoLocalList _ (isMaxTwoLocal_map ψ hM) ?_⟩
  rw [← hψ]
  exact Subgroup.map_mono hSM

end Main

end CFSG.Quasithin.J4Loc
