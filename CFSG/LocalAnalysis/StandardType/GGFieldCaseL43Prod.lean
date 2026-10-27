module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseModule

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_ne_one_mem_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {V X : Subgroup G} (hpV : p ∣ Nat.card V) (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (X : Set G) := by
  set A : Subgroup (MulAut V) :=
    (X.subgroupOf (Subgroup.normalizer (V : Set G))).map V.normalizerMonoidHom with hAdef
  have hA : IsPGroup p A := by
    rintro ⟨a, g, hg, rfl⟩
    obtain ⟨k, hk⟩ := hXp g (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨k, Subtype.ext ?_⟩
    have hker : g ^ p ^ k ∈ V.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
    simpa [map_pow] using hker
  have h1 : (1 : V) ∈ MulAction.fixedPoints A V := fun a => by
    change (a : MulAut V) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥V) hpV h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : (⟨g, hXN hg⟩ : Subgroup.normalizer (V : Set G)) ∈
      X.subgroupOf (Subgroup.normalizer (V : Set G)) := Subgroup.mem_subgroupOf.mpr hg
  have hfix := hb ⟨_, ⟨_, hg', rfl⟩⟩
  have hval : g * (b : G) * g⁻¹ = b := congrArg Subtype.val hfix
  calc g * (b : G) = g * b * g⁻¹ * g := by group
    _ = b * g := by rw [hval]

@[expose] def GGL43HardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCase p B Bs x L D J X → GGTableBModule p Bs x L B₂ →
      x ∉ Bs ⊓ Subgroup.centralizer (X : Set G) →
      (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x = B₂ → B₂ ≠ Bs → False

theorem ggL43ProdInput_of_hard (hTBM : GGTableBModuleInput) (hhard : GGL43HardInput) :
    GGL43ProdInput := by
  intro G _ _ p B Bs x L D J X hFC hxB₁
  obtain ⟨hcfg, -, hXN, -, hXn, hXp, -⟩ := id hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  obtain ⟨B₂, hM⟩ := hTBM G p B Bs x L D J hcfg
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hBsp := isPGroup_of_isElemAbelian hBs
  have hpBs : p ∣ Nat.card Bs := by
    have h := orderOf_dvd_natCard (⟨x, hxBs⟩ : Bs)
    rwa [orderOf_eq_prime (Subtype.ext (by simpa using hBs.2 x hxBs))
      (fun h => hx1 (congrArg Subtype.val h))] at h
  obtain ⟨b, hbBs, hb1, hbX⟩ := exists_ne_one_mem_centralizer hpBs hXN hXp
  have hbB₁ : b ∈ B₁ := ⟨hbBs, hbX⟩
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x * n⁻¹ = x := by
    intro n hn
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hB₁inv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ c ∈ B₁, n * c * n⁻¹ ∈ B₁ := by
    intro n hn c hc
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn.2 c).mp hc.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ X := hconj _ (Subgroup.inv_mem _ hn.2) g hg
    have hcg := Subgroup.mem_centralizer_iff.mp hc.2 _ hg'
    rw [inv_inv] at hcg
    calc g * (n * c * n⁻¹) = n * ((n⁻¹ * g * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * g * n)) * n⁻¹ := by rw [hcg]
      _ = n * c * n⁻¹ * g := by group
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hSV : B₁ ⊔ Subgroup.zpowers x ≤ Bs := sup_le inf_le_left (Subgroup.zpowers_le.mpr hxBs)
  have hSne : B₁ ⊔ Subgroup.zpowers x ≠ Subgroup.zpowers x := by
    intro hSZ
    have hbZ : b ∈ Subgroup.zpowers x := hSZ ▸ le_sup_left (a := B₁) hbB₁
    have hz := zpowers_eq_of_mem_of_ne_one (hBs.2 x hxBs) hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hbB₁
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  have hB₂S : B₂ ≤ B₁ ⊔ Subgroup.zpowers x :=
    le_of_ggTableBModule hBsp hM le_sup_right hSV
      (fun n hn => conj_mem_sup_of_conj_mem (hB₁inv n hn) (hZinv n hn)) hSne
  by_contra hne
  have hSB₂ : B₁ ⊔ Subgroup.zpowers x = B₂ := by
    by_contra hne'
    exact hne (eq_of_lt_of_card_le_mul hBsp (lt_of_le_of_ne hB₂S (Ne.symm hne')) hSV
      hM.2.2.1).symm
  exact hhard G p B Bs x L D J X B₂ hFC hM hxB₁ hSB₂
    (fun h => hne (by rw [hSB₂, h]))

end CFSG.StandardType

end
