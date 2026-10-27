module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZN2
public import CFSG.Quasithin.Vol2.Ch11SKFA1TwoA
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs
public import CFSG.Quasithin.Vol2.Ch11SecS12ZJ
public import CFSG.Quasithin.Vol2.Ch11SecS12ZK
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ZN3

omit [Finite G] in
theorem le_normalizer_of_inner {L J : Subgroup G}
    (hinn : ∀ ℓ ∈ L, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G)) :
    L ≤ Subgroup.normalizer (J : Set G) := by
  intro ℓ hℓ
  obtain ⟨j, hj, hjc⟩ := hinn ℓ hℓ
  have e : ℓ = j * (j⁻¹ * ℓ) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hj) (Subgroup.centralizer_le_normalizer _ hjc)

end ZN3

open ZN3 in
theorem false_of_two_moved_of_uniqueM {M X₁ L J₁ J₂ : Subgroup G} (hUM : IsUniqueM L M)
    (hMN : M ⊓ Subgroup.normalizer (X₁ : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hJ₁ : CFSG.GorensteinWalter.IsComponentOf J₁ (Subgroup.normalizer (X₁ : Set G)))
    (hJ₂ : CFSG.GorensteinWalter.IsComponentOf J₂ (Subgroup.normalizer (X₁ : Set G)))
    (hne : J₁ ≠ J₂) (hL : commutator ↥L = ⊤) {F : Type} [Field F] [Fintype F]
    (π : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hinn₁ : ∀ ℓ ∈ L, ∃ j ∈ J₁, j⁻¹ * ℓ ∈ Subgroup.centralizer (J₁ : Set G))
    (hinn₂ : ∀ ℓ ∈ L, ∃ j ∈ J₂, j⁻¹ * ℓ ∈ Subgroup.centralizer (J₂ : Set G))
    {q : G} (hqO : q ∈ pCoreOf 2 L) (hq : q ∉ Subgroup.centralizer (J₁ : Set G))
    (hL₂ : ¬ L ≤ Subgroup.centralizer (J₂ : Set G)) : False := by
  have h12 : ⁅J₁, J₂⁆ = ⊥ := commutator_eq_bot_of_ne hJ₁ hJ₂ hne
  have hJ₁C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h12
  have hJ₂C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_ne hJ₂ hJ₁ (Ne.symm hne))
  have h1Y : J₁ ≤ J₁ ⊔ J₂ := le_sup_left
  have h2Y : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  obtain ⟨τ₁, hτ₁, hk₁⟩ := exists_proj h1Y
    (fun z hz hzc => mem_center_of_mem h1Y le_rfl h12 hz hzc) hinn₁
  obtain ⟨q', hq', rfl⟩ := hqO
  have hL₁ : ¬ L ≤ Subgroup.centralizer (J₁ : Set G) := fun h => hq (h q'.2)
  have hPn : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set R := (CFSG.Open.pCore 2 ↥L).map τ₁ with hRdef
  have hR2 : IsPGroup 2 ↥R := (CFSG.LieType.BorelTits.pCore_isPGroup 2).map τ₁
  have hRne : R ≠ ⊥ := by
    intro h
    apply hq
    have : τ₁ q' ∈ R := ⟨q', hq', rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (hk₁ q').mp this
  have hRJ : R ≤ imgZ (J₁ ⊔ J₂) J₁ := by
    rintro _ ⟨o, -, rfl⟩
    obtain ⟨j, hj, hjc⟩ := hinn₁ o o.2
    rw [hτ₁ o j hj hjc]
    exact ⟨⟨j, h1Y hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hN₁ : ∀ s : ↥L, τ₁ s ∈ Subgroup.normalizer (R : Set _) := by
    intro s
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨s * o * s⁻¹, hPn.conj_mem o ho s, by simp [map_mul, map_inv]⟩
    · rintro ⟨o, ho, hor⟩
      refine ⟨s⁻¹ * o * s, by simpa using hPn.conj_mem o ho s⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, hor]
      group
  have hN₂ : ∀ y ∈ imgZ (J₁ ⊔ J₂) J₂, y ∈ Subgroup.normalizer (R : Set _) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      rw [← commute_imgZ h12 (hRJ hr) hy, mul_inv_cancel_right]
      exact hr
    · intro hr
      have hc := commute_imgZ h12 (hRJ hr) hy
      have e : r = y * r * y⁻¹ := by
        calc r = y⁻¹ * (y * r * y⁻¹) * y := by group
          _ = y⁻¹ * (y * (y * r * y⁻¹)) := by rw [mul_assoc, hc]
          _ = y * r * y⁻¹ := by group
      rw [e]
      exact hr
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := KF.exists_two_subgroup_normalized hRne hR2
  set P := R₂.map (J₁ ⊔ J₂).subtype with hPdef
  have hPne : P ≠ ⊥ := fun h =>
    hR₂ ((Subgroup.map_eq_bot_iff_of_injective _ (J₁ ⊔ J₂).subtype_injective).mp h)
  have hYP : ∀ w : ↥(J₁ ⊔ J₂), (w : ↥(J₁ ⊔ J₂) ⧸ Subgroup.center ↥(J₁ ⊔ J₂)) ∈
      Subgroup.normalizer (R : Set _) → (w : G) ∈ Subgroup.normalizer (P : Set G) :=
    fun w hw => Subgroup.le_normalizer_map _ ⟨w, hR₂N w hw, rfl⟩
  have hJ₂P : J₂ ≤ Subgroup.normalizer (P : Set G) := fun w hw =>
    hYP ⟨w, h2Y hw⟩ (hN₂ _ ⟨⟨w, h2Y hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩)
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := by
    intro ℓ hℓ
    obtain ⟨j₁, hj₁, hc₁⟩ := hinn₁ ℓ hℓ
    obtain ⟨j₂, hj₂, hc₂⟩ := hinn₂ ℓ hℓ
    have hj : j₂ * j₁ = j₁ * j₂ := (Subgroup.mem_centralizer_iff.mp (hJ₁C hj₁)) j₂ hj₂
    set z := (j₁ * j₂)⁻¹ * ℓ with hz
    have hz₁ : z ∈ Subgroup.centralizer (J₁ : Set G) := by
      have e : z = j₂⁻¹ * (j₁⁻¹ * ℓ) := by rw [hz]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJ₂C hj₂)) hc₁
    have hz₂ : z ∈ Subgroup.centralizer (J₂ : Set G) := by
      have e : z = j₁⁻¹ * (j₂⁻¹ * ℓ) := by rw [hz, ← hj]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJ₁C hj₁)) hc₂
    have hzY : J₁ ⊔ J₂ ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hz₁) x hx)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hz₂) x hx)
    have hzP : z ∈ Subgroup.normalizer (P : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro p hp
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hzY (Subgroup.map_subtype_le R₂ hp)))
    have hy : j₁ * j₂ ∈ J₁ ⊔ J₂ := (J₁ ⊔ J₂).mul_mem (h1Y hj₁) (h2Y hj₂)
    have hyN : ((⟨j₁ * j₂, hy⟩ : ↥(J₁ ⊔ J₂)) : ↥(J₁ ⊔ J₂) ⧸ Subgroup.center ↥(J₁ ⊔ J₂)) ∈
        Subgroup.normalizer (R : Set _) := by
      have e : ((⟨j₁ * j₂, hy⟩ : ↥(J₁ ⊔ J₂)) : ↥(J₁ ⊔ J₂) ⧸ Subgroup.center ↥(J₁ ⊔ J₂)) =
          τ₁ ⟨ℓ, hℓ⟩ * ((⟨j₂, h2Y hj₂⟩ : ↥(J₁ ⊔ J₂)) :
            ↥(J₁ ⊔ J₂) ⧸ Subgroup.center ↥(J₁ ⊔ J₂)) := by
        rw [hτ₁ ⟨ℓ, hℓ⟩ j₁ hj₁ hc₁, ← QuotientGroup.mk_mul]
        rfl
      rw [e]
      exact Subgroup.mul_mem _ (hN₁ _)
        (hN₂ _ ⟨⟨j₂, h2Y hj₂⟩, Subgroup.mem_subgroupOf.mpr hj₂, rfl⟩)
    have e : ℓ = (j₁ * j₂) * z := by rw [hz]; group
    rw [e]
    exact Subgroup.mul_mem _ (hYP _ hyN) hzP
  have hJ₂M : J₂ ≤ M := hJ₂P.trans (H13.Ch4.isUniqueM_normalizer_le hUM hPne (hR₂2.map _) hLP)
  exact false_of_component_le_normalizer hJ₁ hJ₂ hne hL π hπ hker (le_normalizer_of_inner hinn₁)
    (le_normalizer_of_inner hinn₂) (fun w hw => hMN ⟨hJ₂M hw, hJ₂.1 hw⟩) hL₁ hL₂

theorem exists_component_le_of_uniqueM {M X₁ L : Subgroup G} (hUM : IsUniqueM L M)
    (hMN : M ⊓ Subgroup.normalizer (X₁ : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLperf : ⁅L, L⁆ = L) (hL : commutator ↥L = ⊤) {F : Type} [Field F] [Fintype F]
    (π : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hLE : L ≤ CFSG.GorensteinWalter.componentLayerOf (Subgroup.normalizer (X₁ : Set G)))
    (hinn : ∀ J, CFSG.GorensteinWalter.IsComponentOf J (Subgroup.normalizer (X₁ : Set G)) →
      ∀ ℓ ∈ L, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G))
    {q l : G} (hq : q ∈ pCoreOf 2 L) (hl : l ∈ L) (hql : l * q * l⁻¹ * q⁻¹ ≠ 1) :
    ∃ K, CFSG.GorensteinWalter.IsComponentOf K (Subgroup.normalizer (X₁ : Set G)) ∧ L ≤ K := by
  set H := Subgroup.normalizer (X₁ : Set G) with hH
  set E := CFSG.GorensteinWalter.componentLayerOf H with hE
  have hcentE : ∀ c : G, (∀ J, CFSG.GorensteinWalter.IsComponentOf J H →
      c ∈ Subgroup.centralizer (J : Set G)) → E ≤ Subgroup.centralizer ({c} : Set G) := by
    intro c hc
    refine sSup_le fun J hJ x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hc J hJ) x hx
  obtain ⟨K, hK, hqK⟩ : ∃ K, CFSG.GorensteinWalter.IsComponentOf K H ∧
      q ∉ Subgroup.centralizer (K : Set G) := by
    by_contra hall
    push Not at hall
    apply hql
    have h1 := hcentE q hall (hLE hl)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]
  have hcent : ∀ J, CFSG.GorensteinWalter.IsComponentOf J H → J ≠ K →
      L ≤ Subgroup.centralizer (J : Set G) := fun J hJ hJK => by
    by_contra hL₂
    exact false_of_two_moved_of_uniqueM hUM hMN hK hJ (Ne.symm hJK) hL π hπ hker
      (hinn K hK) (hinn J hJ) hq hqK hL₂
  refine ⟨K, hK, ?_⟩
  have hKE : K ≤ E := le_sSup hK
  have hdec : ∀ ℓ ∈ L, ∃ k ∈ K, k⁻¹ * ℓ ∈ E ∧
      E ≤ Subgroup.centralizer ({k⁻¹ * ℓ} : Set G) := by
    intro ℓ hℓ
    obtain ⟨k, hk, hkc⟩ := hinn K hK ℓ hℓ
    refine ⟨k, hk, E.mul_mem (E.inv_mem (hKE hk)) (hLE hℓ), hcentE _ fun J hJ => ?_⟩
    by_cases hJK : J = K
    · subst hJK
      exact hkc
    · have hkJ : k ∈ Subgroup.centralizer (J : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_ne hK hJ
          (Ne.symm hJK)) hk
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkJ) (hcent J hJ hJK hℓ)
  rw [← hLperf, Subgroup.commutator_le]
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂
  obtain ⟨k₁, hk₁, hc₁E, hc₁⟩ := hdec ℓ₁ hℓ₁
  obtain ⟨k₂, hk₂, hc₂E, hc₂⟩ := hdec ℓ₂ hℓ₂
  have hcomm : ∀ {c x : G}, E ≤ Subgroup.centralizer ({c} : Set G) → x ∈ E → Commute c x := by
    intro c x hc hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hc hx)).symm
  have e₁ : ℓ₁ = k₁ * (k₁⁻¹ * ℓ₁) := by group
  have e₂ : ℓ₂ = k₂ * (k₂⁻¹ * ℓ₂) := by group
  rw [e₁, e₂, commutatorElement_mul_mul (hcomm hc₁ (hKE hk₂)) (hcomm hc₁ hc₂E)
    (hcomm hc₂ (hKE hk₁)), commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
