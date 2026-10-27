module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseDefs
public import CFSG.LocalAnalysis.StandardType.GGPropFourOneTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTableBCxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({x} : Set G) →
      Y ≤ Subgroup.normalizer (Bs : Set G) → Subgroup.centralizer (Bs : Set G) ≤ Y →
      (∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G), ∀ g ∈ Y,
        n * g * n⁻¹ ∈ Y) →
      (∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
      ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x

@[expose] def GGXNotNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
      ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G)

@[expose] def GGL43ProdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G),
    GGFieldCase p B Bs x L D J X → x ∉ Bs ⊓ Subgroup.centralizer (X : Set G) →
      Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x

section Proofs

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_mem_of_ne_one {p : ℕ} [Fact p.Prime] {x c : G} (hxp : x ^ p = 1)
    (hc : c ∈ Subgroup.zpowers x) (hc1 : c ≠ 1) : Subgroup.zpowers c = Subgroup.zpowers x := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hc1 (by simpa using hc)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hcp : (x ^ k) ^ p = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hxp, one_zpow]
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hc) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hx1, orderOf_eq_prime hcp hc1]

theorem not_mem_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X) :
    x ∉ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  obtain ⟨hcfg, -, hXN, hCX, hXn, hXp, hXC⟩ := hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  intro hxB₁
  have hXx : X ≤ Subgroup.centralizer ({x} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    exact (Subgroup.mem_centralizer_iff.mp hxB₁.2 g hg).symm
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hcomm := hTB G p B Bs x L D J hcfg X hXx hXN hCX
    (fun n hn g hg => hconj n hn.1 g hg) hXp
  obtain ⟨g, hg, hgC⟩ := Set.not_subset.mp hXC
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hgC
  push Not at hgC
  obtain ⟨b, hb, hbg⟩ := hgC
  have hc1 : g * b * g⁻¹ * b⁻¹ ≠ 1 := by
    intro h
    apply hbg
    have h' : g * b * g⁻¹ = b := by
      calc g * b * g⁻¹ = g * b * g⁻¹ * b⁻¹ * b := by group
        _ = b := by rw [h, one_mul]
    calc b * g = g * b * g⁻¹ * g := by rw [h']
      _ = g * b := by group
  have hzc := zpowers_eq_of_mem_of_ne_one (hBs.2 x hxBs) (hcomm g hg b hb) hc1
  apply hNN G p B Bs x L D J hcfg
  intro n hn
  apply mem_normalizer_of_forall_conj_mem
  intro w hw
  rw [← hzc] at hw ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hn' : n⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hn
  have hmem : n⁻¹ * (g * b * g⁻¹ * b⁻¹) * n⁻¹⁻¹ ∈ Subgroup.zpowers x := by
    have e : n⁻¹ * (g * b * g⁻¹ * b⁻¹) * n⁻¹⁻¹ =
        (n⁻¹ * g * n⁻¹⁻¹) * (n⁻¹ * b * n⁻¹⁻¹) * (n⁻¹ * g * n⁻¹⁻¹)⁻¹ *
          (n⁻¹ * b * n⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact hcomm _ (hconj _ hn' g hg) _ ((Subgroup.mem_normalizer_iff.mp hn' b).mp hb)
  rw [hzc]
  have e2 : n⁻¹ * (g * b * g⁻¹ * b⁻¹) ^ k * n = (n⁻¹ * (g * b * g⁻¹ * b⁻¹) * n⁻¹⁻¹) ^ k := by
    rw [conj_zpow, inv_inv]
  rw [e2]
  exact Subgroup.zpow_mem _ hmem k

theorem ggL43Input_of_inputs (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hprod : GGL43ProdInput) : GGL43Input := by
  intro G _ _ p B Bs x L D J X hFC
  have hx := not_mem_of_tableB hTB hNN hFC
  exact ⟨hx, hprod G p B Bs x L D J X hFC hx⟩

end Proofs

end CFSG.StandardType

end
