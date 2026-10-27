module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5L47

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggL45_card_sup_zpowers_le {a b : G} (hab : Commute a b) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≤ orderOf a * orderOf b := by
  have hle : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨k, rfl⟩
    exact (hab.zpow_left k).eq
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle
  have h := Set.natCard_mul_le (s := (Subgroup.zpowers a : Set G))
    (t := (Subgroup.zpowers b : Set G))
  rw [← hcoe] at h
  have h1 : Nat.card (Subgroup.zpowers a : Set G) = orderOf a := Nat.card_zpowers a
  have h2 : Nat.card (Subgroup.zpowers b : Set G) = orderOf b := Nat.card_zpowers b
  rw [h1, h2] at h
  exact h

theorem ggL45_exists_not_normalizer_zpowers {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X)
    (hM : GGTableBModule p Bs x L B₂) (h43 : GGL43 Bs x X) (hK : GGL44iii p B Bs x D J X d y K) :
    ∃ t ∈ L ⊓ Subgroup.normalizer (Bs : Set G),
      t ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  obtain ⟨hcfg, -⟩ := hFC
  have hpp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hpp⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hxBs : x ∈ Bs := hBBs hcfg.1.2.2.2.2.2.2.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hrank : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hdDB₁ : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hK.1]
    exact Subgroup.mem_zpowers d
  have hdB₁ : d ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := hdDB₁.2
  have hdBs : d ∈ Bs := hdB₁.1
  have hd1 : d ≠ 1 := hK.2.1
  have hdx : d ∉ Subgroup.zpowers x := by
    intro hdx
    have heq := zpowers_eq_of_mem_of_ne_one (hBs.2 x hxBs) hdx hd1
    have hxd : x ∈ Subgroup.zpowers d := heq ▸ Subgroup.mem_zpowers x
    exact h43.1 ((Subgroup.zpowers_le.mpr hdB₁) hxd)
  by_contra hcon
  push Not at hcon
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x * n⁻¹ = x := by
    intro n hn
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hTinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G),
      ∀ s ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers x,
        n * s * n⁻¹ ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers x := fun n hn =>
    conj_mem_sup_of_conj_mem
      (fun i hi => (Subgroup.mem_normalizer_iff.mp (hcon n hn) i).mp hi) (hZinv n hn)
  have hTne : Subgroup.zpowers d ⊔ Subgroup.zpowers x ≠ Subgroup.zpowers x := by
    intro h
    exact hdx (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  have hTBs : Subgroup.zpowers d ⊔ Subgroup.zpowers x ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hdBs) (Subgroup.zpowers_le.mpr hxBs)
  have hB₂T : B₂ ≤ Subgroup.zpowers d ⊔ Subgroup.zpowers x :=
    le_of_ggTableBModule (isPGroup_of_isElemAbelian hBs) hM le_sup_right hTBs hTinv hTne
  have hcomm : Commute d x := mul_comm_of_isElemAbelian hBs hdBs hxBs
  have hod : orderOf d ≤ p := orderOf_le_of_pow_eq_one hpp.pos (hBs.2 d hdBs)
  have hox : orderOf x ≤ p := orderOf_le_of_pow_eq_one hpp.pos (hBs.2 x hxBs)
  have hT : Nat.card ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers x) ≤ p * p :=
    (ggL45_card_sup_zpowers_le hcomm).trans (Nat.mul_le_mul hod hox)
  have hB₂ : Nat.card B₂ ≤ p * p := (Subgroup.card_le_of_le hB₂T).trans hT
  have hBs4 : p ^ 4 ≤ Nat.card Bs := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hrank
      _ = Nat.card B := hcardB.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
  have h3 : Nat.card Bs ≤ p * (p * p) := hM.2.2.1.trans (Nat.mul_le_mul_left p hB₂)
  have hp2 : 2 ≤ p := hpp.two_le
  have : p * (p * p) < p ^ 4 := by
    have : p ^ 4 = p * (p * p) * p := by ring
    rw [this]
    exact lt_mul_of_one_lt_right (by positivity) (by omega)
  omega

theorem ggL45_exists_moving {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X)
    (hM : GGTableBModule p Bs x L B₂) (h43 : GGL43 Bs x X) (hK : GGL44iii p B Bs x D J X d y K)
    (hsetup : GGL45Setup p Bs X U) :
    ∃ r ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  obtain ⟨t, ht, htd⟩ := ggL45_exists_not_normalizer_zpowers hFC hM h43 hK
  have : Fact p.Prime := ⟨hFC.1.1.2.2.2.2.2.1.1⟩
  have hXN := hFC.2.2.1
  have hXn := hFC.2.2.2.2.1
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff.mpr hconj ht.2
  have htB₁ : t ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨ht.2, ggNormalizer_le_normalizer_centralizer X htX⟩
  have htC := ggNormalizer_le_normalizer_centralizer _ htB₁
  obtain ⟨c, hc, hcU⟩ :=
    exists_mul_mem_normalizer_of_maxPSubgroup htC hsetup.2.1 hsetup.1 hsetup.2.2.1
  have hdB₁ : d ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
    have : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [hK.1]
      exact Subgroup.mem_zpowers d
    exact this.2
  have hcd : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_normalizer_zpowers_of_le hdB₁ le_rfl hc
  refine ⟨c * t, ⟨hcU, mul_mem (Subgroup.centralizer_le_normalizer _ hc) htB₁⟩, fun h => htd ?_⟩
  have := mul_mem (inv_mem hcd) h
  rwa [inv_mul_cancel_left] at this

end CFSG.StandardType

end
