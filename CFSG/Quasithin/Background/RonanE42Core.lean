module

public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G V : Type} [Group G] [Finite G] [CommGroup V]

structure Setup (ρ : G →* MulAut V) (T : Subgroup G) (Δ : Finset (Subgroup G))
    (c : Subgroup G → ℕ) (Ω : Set (Subgroup G)) : Prop where
  conj : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω
  elem : ∀ A ∈ Ω, A ≠ ⊥ ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  fix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ ∑ H ∈ Δ, c H → Fx ρ B = Fx ρ A
  sylow : IsSylowIn 2 T ⊤
  memT : ∀ H ∈ Δ, T ≤ H
  rank : ∀ H ∈ Δ, ∀ B : Subgroup G, B ≤ H → (∀ b ∈ B, b ^ 2 = 1) →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → mQuot B (B ⊓ pCoreOf 2 H) ≤ c H
  good : ∀ H ∈ Δ, ∀ Y : Subgroup G, Y ≤ H → (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
    ¬ (Y ⊓ T ≤ pCoreOf 2 H) → (∀ A ∈ Ω, A ≤ H → A ≤ Y) →
    H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y)

section Core

variable {ρ : G →* MulAut V} {T : Subgroup G} {Δ : Finset (Subgroup G)} {c : Subgroup G → ℕ}
  {Ω : Set (Subgroup G)}

@[expose] def Sig (ρ : G →* MulAut V) (T : Subgroup G) (Ω : Set (Subgroup G)) (c : ℕ) :
    Subgroup G :=
  Subgroup.normalizer (T : Set G) ⊔ (T ⊔ cenV ρ (Fx ρ (Wcl Ω c T)))

theorem Sig_mono {a b : ℕ} (hab : a ≤ b) : Sig ρ T Ω a ≤ Sig ρ T Ω b := by
  have h1 : Fx ρ (Wcl Ω b T) ≤ Fx ρ (Wcl Ω a T) := Fx_anti (Wcl_mono_level hab T)
  have h2 : cenV ρ (Fx ρ (Wcl Ω a T)) ≤ cenV ρ (Fx ρ (Wcl Ω b T)) := cenV_anti ρ h1
  exact sup_le_sup_left (sup_le_sup_left h2 _) _

theorem Sig_le_stabV (h : Setup ρ T Δ c Ω) (a : ℕ) :
    Sig ρ T Ω a ≤ stabV ρ (Fx ρ (Wcl Ω a T)) := by
  refine sup_le (fun g hg => ?_) (sup_le (fun g hg => ?_) (cenV_le_stabV ρ _))
  · exact mem_stabV_Fx_of_conj
      (conjSubgroup_Wcl_eq h.conj a (conjSubgroup_eq_iff_mem_normalizer.2 hg))
  · exact mem_stabV_Fx_of_conj
      (conjSubgroup_Wcl_eq h.conj a
        (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hg)))

theorem kstep (h : Setup ρ T Δ c Ω) {K : Subgroup G} (hK : K ∈ Δ) {j : ℕ}
    (hjm : j + c K ≤ ∑ H ∈ Δ, c H) (hnot : ¬ Wcl Ω j T ≤ pCoreOf 2 K) :
    K ≤ Sig ρ T Ω (j + c K) := by
  have hTK : T ≤ K := h.memT K hK
  have hRT : pCoreOf 2 K ≤ T := pCoreOf_le_of_sylow h.sylow hTK
  set R := pCoreOf 2 K with hR
  set m := j + c K with hm
  set U : Subgroup V := Fx ρ (Wcl Ω m R) with hU
  have hKst : ∀ g ∈ K, g ∈ stabV ρ U := fun g hg =>
    mem_stabV_Fx_of_conj (conjSubgroup_Wcl_eq h.conj m (conjSubgroup_pCoreOf hg))
  set Y : Subgroup G := K ⊓ cenV ρ U with hY
  have hYK : Y ≤ K := inf_le_left
  have hYn : ∀ g ∈ K, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine ⟨K.mul_mem (K.mul_mem hg (hYK hy)) (K.inv_mem hg), fun u hu => ?_⟩
    have hu' : ρ g⁻¹ u ∈ U := (hKst g⁻¹ (K.inv_mem hg) u).2 hu
    have hy' : ρ y (ρ g⁻¹ u) = ρ g⁻¹ u := hy.2 _ hu'
    calc ρ (g * y * g⁻¹) u = ρ g (ρ y (ρ g⁻¹ u)) := by
          simp only [map_mul, MulAut.mul_apply]
      _ = ρ g (ρ g⁻¹ u) := by rw [hy']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hWjY : Wcl Ω j T ≤ Y := by
    refine sSup_le fun B hB => ?_
    obtain ⟨hBT, A, hAΩ, hBA, hmA⟩ := hB
    have hBK : B ≤ K := hBT.trans hTK
    have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb => (h.elem A hAΩ).2.1 b (hBA hb)
    have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      (h.elem A hAΩ).2.2 a (hBA ha) b (hBA hb)
    have hDA : B ⊓ R ≤ A := inf_le_left.trans hBA
    have hmD : mQuot A (B ⊓ R) ≤ m := by
      have h1 := mQuot_add (inf_le_left : B ⊓ R ≤ B) hBA
      have h2 : mQuot B (B ⊓ R) ≤ c K := h.rank K hK B hBK hB2 hBc
      omega
    have hFx : Fx ρ (B ⊓ R) = Fx ρ A := h.fix A hAΩ _ hDA (hmD.trans hjm)
    have hDW : B ⊓ R ≤ Wcl Ω m R := le_Wcl inf_le_right ⟨A, hAΩ, hDA, hmD⟩
    have hUB : U ≤ Fx ρ B := (Fx_anti hDW).trans (hFx.le.trans (Fx_anti hBA))
    exact fun b hb => ⟨hBK hb, fun u hu => (mem_Fx.1 (hUB hu)) b hb⟩
  have hYT : ¬ (Y ⊓ T ≤ R) := fun hle => hnot ((le_inf hWjY (Wcl_le_self Ω j T)).trans hle)
  have hΩY : ∀ A ∈ Ω, A ≤ K → A ≤ Y := by
    intro A hAΩ hAK
    have hA2 : ∀ a ∈ A, a ^ 2 = 1 := (h.elem A hAΩ).2.1
    have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := (h.elem A hAΩ).2.2
    have hDA : A ⊓ R ≤ A := inf_le_left
    have hmD : mQuot A (A ⊓ R) ≤ m :=
      (h.rank K hK A hAK hA2 hAc).trans (Nat.le_add_left (c K) j)
    have hFx : Fx ρ (A ⊓ R) = Fx ρ A := h.fix A hAΩ _ hDA (hmD.trans hjm)
    have hDW : A ⊓ R ≤ Wcl Ω m R := le_Wcl inf_le_right ⟨A, hAΩ, hDA, hmD⟩
    have hUA : U ≤ Fx ρ A := (Fx_anti hDW).trans hFx.le
    exact fun a ha => ⟨hAK ha, fun u hu => (mem_Fx.1 (hUA hu)) a ha⟩
  have hgood := h.good K hK Y hYK hYn hYT hΩY
  have hYle : Y ≤ cenV ρ (Fx ρ (Wcl Ω m T)) := by
    intro y hy u hu
    have hu' : u ∈ U := Fx_anti (Wcl_mono_base m hRT) hu
    exact hy.2 u hu'
  exact hgood.trans (sup_le_sup_left (sup_le_sup_left hYle _) _)

theorem exists_level (h : Setup ρ T Δ c Ω) :
    ∃ j, j ≤ ∑ H ∈ Δ, c H ∧ ∀ H ∈ Δ, H ≤ stabV ρ (Fx ρ (Wcl Ω j T)) := by
  classical
  let S𝒮 : Finset (Finset (Subgroup G)) :=
    Δ.powerset.filter (fun Γ => ∀ H ∈ Γ, H ≤ Sig ρ T Ω (∑ H' ∈ Γ, c H'))
  have hne : S𝒮.Nonempty := ⟨∅, by simp [S𝒮]⟩
  obtain ⟨Γ, hmax⟩ := S𝒮.exists_maximal hne
  have hΓ := hmax.1
  simp only [S𝒮, Finset.mem_filter, Finset.mem_powerset] at hΓ
  obtain ⟨hΓΔ, hΓgood⟩ := hΓ
  set j := ∑ H ∈ Γ, c H with hj
  have hjk : j ≤ ∑ H ∈ Δ, c H := Finset.sum_le_sum_of_subset hΓΔ
  have hall : ∀ K ∈ Δ, K ∉ Γ → Wcl Ω j T ≤ pCoreOf 2 K := by
    intro K hKΔ hKΓ
    by_contra hnot
    have hsum : ∑ H ∈ insert K Γ, c H = j + c K := by
      rw [Finset.sum_insert hKΓ]; ring
    have hjm : j + c K ≤ ∑ H ∈ Δ, c H := by
      rw [← hsum]; exact Finset.sum_le_sum_of_subset (Finset.insert_subset hKΔ hΓΔ)
    have hKs := kstep h hKΔ hjm hnot
    have hmem : insert K Γ ∈ S𝒮 := by
      simp only [S𝒮, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hKΔ hΓΔ, fun H hH => ?_⟩
      rw [hsum]
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · exact hKs
      · exact (hΓgood H hH').trans (Sig_mono (Nat.le_add_right j (c K)))
    exact hKΓ (hmax.2 hmem (Finset.subset_insert K Γ) (Finset.mem_insert_self K Γ))
  refine ⟨j, hjk, fun H hH => ?_⟩
  by_cases hHΓ : H ∈ Γ
  · exact (hΓgood H hHΓ).trans (Sig_le_stabV h j)
  · intro g hg
    have hRT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow h.sylow (h.memT H hH)
    have heq : Wcl Ω j T = Wcl Ω j (pCoreOf 2 H) := Wcl_eq_of_le hRT (hall H hH hHΓ)
    have hconj : conjSubgroup (Wcl Ω j T) g = Wcl Ω j T := by
      rw [heq]; exact conjSubgroup_Wcl_eq h.conj j (conjSubgroup_pCoreOf hg)
    exact mem_stabV_Fx_of_conj hconj

theorem core (h : Setup ρ T Δ c Ω) (hgen : (⨆ H ∈ Δ, H) = ⊤) {A₀ : Subgroup G} (hA₀ : A₀ ∈ Ω)
    {L : Subgroup G} (hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L) :
    ∀ v ∈ Fx ρ T, ∀ l ∈ L, ρ l v = v := by
  obtain ⟨j, -, hst⟩ := exists_level h
  have hall : ∀ g : G, g ∈ stabV ρ (Fx ρ (Wcl Ω j T)) := by
    intro g
    have hle : (⨆ H ∈ Δ, H) ≤ stabV ρ (Fx ρ (Wcl Ω j T)) :=
      iSup₂_le fun H hH => hst H hH
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  obtain ⟨A₁, hA₁Ω, hA₁T⟩ := exists_mem_le_of_sylow h.sylow h.conj
    (fun A hA a ha => (h.elem A hA).2.1 a ha) hA₀
  have hW : Wcl Ω j T ≠ ⊥ := by
    intro hbot
    have hle : A₁ ≤ Wcl Ω j T :=
      le_Wcl hA₁T ⟨A₁, hA₁Ω, le_rfl, by simp [mQuot_self]⟩
    rw [hbot] at hle
    exact (h.elem A₁ hA₁Ω).1 (le_bot_iff.1 hle)
  have hcomm : ⁅L, Wcl Ω j T⁆ = L := hL _ (Wcl_le_self Ω j T) hW
  have hcen : ⁅L, Wcl Ω j T⁆ ≤ cenV ρ (Fx ρ (Wcl Ω j T)) := by
    rw [Subgroup.commutator_le]
    intro l _ w hw u hu
    have hw' : ρ w⁻¹ u = u := mem_Fx.1 hu w⁻¹ ((Wcl Ω j T).inv_mem hw)
    have hu' : ρ l⁻¹ u ∈ Fx ρ (Wcl Ω j T) := (hall l⁻¹ u).2 hu
    have hw'' : ρ w (ρ l⁻¹ u) = ρ l⁻¹ u := mem_Fx.1 hu' w hw
    calc ρ ⁅l, w⁆ u = ρ l (ρ w (ρ l⁻¹ (ρ w⁻¹ u))) := by
          simp only [commutatorElement_def, map_mul, MulAut.mul_apply]
      _ = ρ l (ρ w (ρ l⁻¹ u)) := by rw [hw']
      _ = ρ l (ρ l⁻¹ u) := by rw [hw'']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [hcomm] at hcen
  intro v hv l hl
  have hv' : v ∈ Fx ρ (Wcl Ω j T) := Fx_anti (Wcl_le_self Ω j T) hv
  exact hcen hl v hv'

end Core

end CFSG.Quasithin.RonanE42
