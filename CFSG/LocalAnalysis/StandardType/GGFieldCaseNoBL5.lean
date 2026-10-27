module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43Hard
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGFieldCaseNoBL5 (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G) :
    Prop :=
  GGConfig p B Bs x L D J ∧
    X ≤ Subgroup.normalizer (Bs : Set G) ∧ Subgroup.centralizer (Bs : Set G) ≤ X ∧
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal ∧
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) ∧
    ¬ X ≤ Subgroup.centralizer (Bs : Set G)

end Defs

section Proofs

variable {G : Type} [Group G] [Finite G]

theorem GGFieldCase.noBL5 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (h : GGFieldCase p B Bs x L D J X) : GGFieldCaseNoBL5 p B Bs x L D J X :=
  ⟨h.1, h.2.2⟩

theorem not_mem_of_tableB_noBL5 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G} (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) :
    x ∉ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  obtain ⟨hcfg, hXN, hCX, hXn, hXp, hXC⟩ := hFC
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

theorem ggL43Hard_noBL5 (hTB : GGTableBCxInput) (hTBA : GGTableBActionInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (hM : GGTableBModule p Bs x L B₂)
    (hxB₁ : x ∉ Bs ⊓ Subgroup.centralizer (X : Set G))
    (hB₂eq : (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x = B₂)
    (hB₂ne : B₂ ≠ Bs) : False := by
  obtain ⟨hcfg, hXN, hCX, hXn, hXp, hXC⟩ := id hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  obtain ⟨hCN, hH⟩ := hTBA G p B Bs x L D J B₂ hcfg hM
  obtain ⟨hxB₂, hB₂V, hcardB₂, hB₂inv, hirr₂, -⟩ := hM
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hcV : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isElemAbelian hBs ha hb
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x = x * n := fun n hn =>
    (Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl).symm
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
  have hB₁Z1 : ∀ b ∈ B₁, b ∈ Subgroup.zpowers x → b = 1 := by
    intro b hb hbZ
    by_contra hb1
    have hz := zpowers_eq_of_mem_of_ne_one hxp hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  have hB₁Z : B₁ ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    exact (Subgroup.mem_bot).mpr (hB₁Z1 b hb.1 hb.2)
  have hB₁B₂ : B₁ ≤ B₂ := hB₂eq ▸ le_sup_left
  obtain ⟨hNT, hEnd⟩ := hH B₁ hB₁B₂ hB₁inv hB₂eq hB₁Z
  obtain ⟨d, hdBs, hdB₂⟩ : ∃ d ∈ Bs, d ∉ B₂ := by
    by_contra h
    push Not at h
    exact hB₂ne (le_antisymm hB₂V h)
  have hBsp := isPGroup_of_isElemAbelian hBs
  have hVgen : Bs = (B₁ ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers d := by
    rw [hB₂eq]
    refine (eq_of_lt_of_card_le_mul hBsp (lt_of_le_of_ne le_sup_left ?_)
      (sup_le hB₂V (Subgroup.zpowers_le.mpr hdBs)) hcardB₂).symm
    intro h
    apply hdB₂
    rw [h]
    exact le_sup_right (a := B₂) (Subgroup.mem_zpowers d)
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hirr : ∀ S : Subgroup G, S ≤ B₁ →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = ⊥ ∨ S = B₁ := by
    intro S hSB hSinv
    have hZB₂ : Subgroup.zpowers x ≤ B₂ := Subgroup.zpowers_le.mpr hxB₂
    rcases hirr₂ (S ⊔ Subgroup.zpowers x) le_sup_right (sup_le (hSB.trans hB₁B₂) hZB₂)
      (fun n hn => conj_mem_sup_of_conj_mem (hSinv n hn) (hZinv n hn)) with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      have hsZ : s ∈ Subgroup.zpowers x := by rw [← h]; exact le_sup_left (a := S) hs
      exact (Subgroup.mem_bot).mpr (hB₁Z1 s (hSB hs) hsZ)
    · right
      refine le_antisymm hSB (fun b hb => ?_)
      have hbS : b ∈ S ⊔ Subgroup.zpowers x := by rw [h, ← hB₂eq]; exact le_sup_left (a := B₁) hb
      have hxS : ∀ s ∈ S, x * s = s * x := fun s hs => hcV _ hxBs _ (hSB hs).1
      obtain ⟨s, hs, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxS hbS
      have hxi : x ^ i ∈ B₁ := by
        have := B₁.mul_mem (B₁.inv_mem (hSB hs)) hb
        simpa using this
      rw [hB₁Z1 _ hxi (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i), mul_one]
      exact hs
  have hCx : ∀ g ∈ X, g * x = x * g → ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ Subgroup.zpowers x := by
    intro g hg hgx v hv
    have hCxle : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxBs)
    have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y rfl
      exact hgx.symm
    refine hTB G p B Bs x L D J hcfg (X ⊓ Subgroup.centralizer ({x} : Set G)) inf_le_right
      (inf_le_left.trans hXN) (le_inf hCX hCxle)
      (fun n hn h hh => Subgroup.mem_inf.mpr ⟨hconj n hn.1 h hh.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hn.2 hh.2) (Subgroup.inv_mem _ hn.2)⟩)
      (fun h hh => hXp h hh.1) g (Subgroup.mem_inf.mpr ⟨hg, hgC⟩) v hv
  have hcard : p < Nat.card B₁ := by
    have hp := (Fact.out : p.Prime)
    have hB4 : p ^ 4 ≤ Nat.card Bs := by
      have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
      have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
      calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
        _ = Nat.card B := hBc.symm
        _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
    have hZcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun b hb => hcV _ hb.1 _ hxBs)
    have hB₂card : Nat.card B₂ ≤ Nat.card B₁ * p := by
      have h1 := Set.natCard_mul_le (s := (B₁ : Set G)) (t := (Subgroup.zpowers x : Set G))
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B₁ _ hxN, hB₂eq] at h1
      rw [← hZcard]
      exact h1
    have h2 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₁ := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card Bs := hB4
        _ ≤ p * Nat.card B₂ := hcardB₂
        _ ≤ p * (Nat.card B₁ * p) := Nat.mul_le_mul_left p hB₂card
        _ = p ^ 2 * Nat.card B₁ := by ring
    have h3 : p ^ 2 ≤ Nat.card B₁ := Nat.le_of_mul_le_mul_left h2 (pow_pos hp.pos 2)
    have h4 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  exact hardCase_false (V := Bs) (X := X) (N := L ⊓ Subgroup.normalizer (Bs : Set G)) (B₁ := B₁)
    (x := x) (d := d) hBs hxBs hdBs inf_le_left
    (fun b hb g hg => Subgroup.mem_centralizer_iff.mp hb.2 g hg)
    (fun v hv hvX => ⟨hv, Subgroup.mem_centralizer_iff.mpr hvX⟩)
    hXN hXp (fun n hn g hg => hconj n hn.2 g hg) inf_le_right hnx hxB₁
    (by rw [hB₂eq]; exact hdB₂) hVgen hB₁inv hirr hCN hNT hEnd hCx hcard


theorem ggL43Prod_noBL5 (hTB : GGTableBCxInput) (hTBM : GGTableBModuleInput)
    (hTBA : GGTableBActionInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (hxB₁ : x ∉ Bs ⊓ Subgroup.centralizer (X : Set G)) :
    Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x := by
  obtain ⟨hcfg, hXN, -, hXn, hXp, -⟩ := id hFC
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
  exact ggL43Hard_noBL5 hTB hTBA hFC hM hxB₁ hSB₂ (fun h => hne (by rw [hSB₂, h]))

theorem ggL43_noBL5 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) : GGL43 Bs x X :=
  have hx := not_mem_of_tableB_noBL5 hTB hNN hFC
  ⟨hx, ggL43Prod_noBL5 hTB hTBM hTBA hFC hx⟩

theorem ggFieldNbrSplit_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) : GGFieldNbrSplit p Bs x :=
  fun _ hXN hCX hXn hXp hXC =>
    (ggL43_noBL5 hTB hNN hTBM hTBA (L := L) (D := D) (J := J)
      ⟨hcfg, hXN, hCX, hXn, hXp, hXC⟩).2.le


theorem ggL44ii_of_ggL43_noBL5 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (hM : GGTableBModule p Bs x L B₂)
    (h43 : GGL43 Bs x X) (h44 : GGL44i p Bs x X) : GGL44ii Bs x X B₂ := by
  obtain ⟨hcfg, hXN, -, hXn, -, hXC⟩ := hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hxB₁ : x ∉ B₁ := h43.1
  have hgB₁ : ∀ g ∈ X, ∀ b ∈ B₁, g * b = b * g := fun g hg b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 g hg
  have hθB₁ : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ B₁ := fun g hg => h44.2.1 g hg x hxBs
  let θ : X →* G := MonoidHom.mk' (fun g => (g : G) * x * (g : G)⁻¹ * x⁻¹) (fun g h => by
    simp only [Subgroup.coe_mul]
    exact comm_mul_eq (hgB₁ g g.2) (hθB₁ h h.2)
      (mul_comm_of_isElemAbelian hBs (hθB₁ g g.2).1 (hθB₁ h h.2).1))
  set I : Subgroup G := θ.range with hIdef
  have hmemI : ∀ b, b ∈ I ↔ ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b := by
    intro b
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hIB₁ : I ≤ B₁ := by
    rintro _ ⟨g, rfl⟩
    exact hθB₁ g g.2
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x * n⁻¹ = x := by
    intro n hn
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hIinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ i ∈ I, n * i * n⁻¹ ∈ I := by
    intro n hn i hi
    obtain ⟨g, hg, rfl⟩ := (hmemI i).mp hi
    refine (hmemI _).mpr ⟨n * g * n⁻¹, hconj n hn.2 g hg, ?_⟩
    calc n * g * n⁻¹ * x * (n * g * n⁻¹)⁻¹ * x⁻¹
        = n * g * n⁻¹ * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ * (n * x * n⁻¹)⁻¹ := by
          rw [hnx n hn]
      _ = n * (g * x * g⁻¹ * x⁻¹) * n⁻¹ := by group
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hSinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ I ⊔ Subgroup.zpowers x,
      n * s * n⁻¹ ∈ I ⊔ Subgroup.zpowers x := fun n hn =>
    conj_mem_sup_of_conj_mem (hIinv n hn) (hZinv n hn)
  have hSV : I ⊔ Subgroup.zpowers x ≤ Bs :=
    sup_le (hIB₁.trans inf_le_left) (Subgroup.zpowers_le.mpr hxBs)
  have hB₁Z : ∀ b ∈ B₁, b ∈ Subgroup.zpowers x → b = 1 := by
    intro b hb hbZ
    by_contra hb1
    have hz := zpowers_eq_of_mem_of_ne_one (hBs.2 x hxBs) hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  have hSne : I ⊔ Subgroup.zpowers x ≠ Subgroup.zpowers x := by
    intro hSZ
    obtain ⟨g, hg, hgC⟩ := Set.not_subset.mp hXC
    have hθ1 : g * x * g⁻¹ * x⁻¹ ≠ 1 := by
      intro h1
      apply hgC
      refine h44.1 g hg ?_
      calc g * x = g * x * g⁻¹ * x⁻¹ * x * g := by group
        _ = x * g := by rw [h1, one_mul]
    apply hθ1
    refine hB₁Z _ (hθB₁ g hg) ?_
    rw [← hSZ]
    exact le_sup_left (a := I) ((hmemI _).mpr ⟨g, hg, rfl⟩)
  have hBsp := isPGroup_of_isElemAbelian hBs
  have hB₂S : B₂ ≤ I ⊔ Subgroup.zpowers x :=
    le_of_ggTableBModule hBsp hM le_sup_right hSV hSinv hSne
  have hded : ∀ b ∈ B₁, b ∈ I ⊔ Subgroup.zpowers x → b ∈ I := by
    intro b hb hbS
    have hxI : ∀ i ∈ I, x * i = i * x := fun i hi =>
      mul_comm_of_isElemAbelian hBs hxBs (hIB₁ hi).1
    obtain ⟨i, hi, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxI hbS
    have hxj : x ^ j ∈ B₁ := by
      have := B₁.mul_mem (B₁.inv_mem (hIB₁ hi)) hb
      simpa using this
    rw [hB₁Z _ hxj (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j), mul_one]
    exact hi
  by_cases hSBs : I ⊔ Subgroup.zpowers x = Bs
  · left
    intro b
    constructor
    · intro hb
      exact (hmemI b).mp (hded b hb (by rw [hSBs]; exact hb.1))
    · rintro ⟨g, hg, rfl⟩
      exact hθB₁ g hg
  · right
    have hB₂ne : B₂ ≠ Bs := fun h => hSBs (le_antisymm hSV (h ▸ hB₂S))
    have hSB₂ : I ⊔ Subgroup.zpowers x = B₂ := by
      by_contra hne
      exact hSBs (eq_of_lt_of_card_le_mul hBsp (lt_of_le_of_ne hB₂S (Ne.symm hne)) hSV
        hM.2.2.1)
    refine ⟨lt_of_le_of_ne hM.2.1 hB₂ne, fun b => ⟨fun hb => ?_, ?_⟩⟩
    · exact (hmemI b).mp (hded b hb.1 (by rw [hSB₂]; exact hb.2))
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hθB₁ g hg, ?_⟩
      rw [← hSB₂]
      exact le_sup_left (a := I) ((hmemI _).mpr ⟨g, hg, rfl⟩)

theorem ggL43HardInput_of_tableB_noBL5 (hTB : GGTableBCxInput) (hTBA : GGTableBActionInput) :
    GGL43HardInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hFC hM hxB₁ hB₂eq hB₂ne =>
    ggL43Hard_noBL5 hTB hTBA hFC.noBL5 hM hxB₁ hB₂eq hB₂ne

theorem ggL43Input_of_tableB_noBL5 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) : GGL43Input :=
  fun _ _ _ _ _ _ _ _ _ _ _ hFC => ggL43_noBL5 hTB hNN hTBM hTBA hFC.noBL5

end Proofs

end CFSG.StandardType

end
