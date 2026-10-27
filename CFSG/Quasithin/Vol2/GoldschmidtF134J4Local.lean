module

public import CFSG.Quasithin.Vol2.GoldschmidtF134J4M24
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot

public section

namespace CFSG.Quasithin.F134.J4E9

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.QuasithinUnique.Setup.X1

@[expose] noncomputable def starImg
    (K : Subgroup J) : Subgroup (Equiv.Perm (Fin 24)) :=
  (K.subgroupOf Hj).map starHom

theorem card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (K : Subgroup G) : Nat.card (K.map f) * Nat.card ↥(K ⊓ f.ker) = Nat.card K := by
  let g : K →* H := f.comp K.subtype
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at h1
  have hr : g.range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card g.ker = Nat.card ↥(K ⊓ f.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hr, hk] at h1
  exact h1.symm

theorem card_starImg_mul
    {K : Subgroup J} (hK : K ≤ Hj) :
    Nat.card (starImg K) * Nat.card ↥(K ⊓ Eg uJ 11) = Nat.card K := by
  have h := card_map_mul_card_inf_ker starHom (K.subgroupOf Hj)
  have e1 : (K.subgroupOf Hj) ⊓ starHom.ker = (K ⊓ Eg uJ 11).subgroupOf Hj := by
    rw [ker_starHom]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [e1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hK)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h
  exact h

theorem starImg_le
    (K : Subgroup J) :
    starImg K ≤ CFSG.Blueprint.NativeSporadic.M24 := by
  rw [← range_starHom_eq]
  exact Subgroup.map_le_range _ _

theorem mem_starImg
    {K : Subgroup J} {σ : Equiv.Perm (Fin 24)} :
    σ ∈ starImg K ↔ ∃ x : Hj, (x : J) ∈ K ∧ starHom x = σ := by
  unfold starImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem starImg_mono
    {K L : Subgroup J} (h : K ≤ L) : starImg K ≤ starImg L := by
  intro σ hσ
  obtain ⟨x, hx, rfl⟩ := mem_starImg.mp hσ
  exact mem_starImg.mpr ⟨x, h hx, rfl⟩

theorem eq_one_of_mul_self_eq_one_of_pow_three {G : Type*} [Group G] {x : G} (h2 : x * x = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have : x = x ^ 3 * (x * x)⁻¹ := by group
  rw [this, h3, h2]
  simp

theorem mem_normalizer_of_conj {G : Type*} [Group G] (A B U : Subgroup G)
    (hconj : ∀ l ∈ A, l ∈ B → ∀ u ∈ U, l * u * l⁻¹ ∈ U) :
    ∀ l ∈ A, l ∈ B → l ∈ Subgroup.normalizer (U : Set G) := by
  intro l hlA hlB
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact hconj l hlA hlB z hz
  · intro hz
    have := hconj l⁻¹ (A.inv_mem hlA) (B.inv_mem hlB) _ hz
    rwa [show l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z by group] at this

theorem exists_normalized_of_le_Hj
    {Pt K : Subgroup J} (hKH : K ≤ Hj) (hP0K : P0 ≤ K)
    (hPtK : Pt ≤ K) (hK : Nat.card K = 9 * 2 ^ 21) (hPt : Nat.card Pt = 9)
    (hPt3 : ∀ x ∈ Pt, x ^ 3 = 1) :
    ∃ U : Subgroup J, U ≤ Pt ∧ U ≠ ⊥ ∧ U ≠ Pt ∧
      ∀ l ∈ P0, l ∈ Subgroup.normalizer (Pt : Set J) → l ∈ Subgroup.normalizer (U : Set J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := j4Facts.mat
  have hF := j4Facts
  have hEl := elem_uJ hM
  have hEP0 : Eg uJ 11 ≤ P0 := Eg_le_P0
  have hEcard : Nat.card (Eg uJ 11) = 2 ^ 11 := card_Eg_uJ hM
  have hPtH : Pt ≤ Hj := hPtK.trans hKH
  have hKcard : Nat.card (starImg K) = 9 * 2 ^ 10 := by
    have h := card_starImg_mul hKH
    rw [inf_eq_right.mpr (hEP0.trans hP0K), hEcard, hK] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 11) (h.trans (by norm_num))
  have hTcard : Nat.card (starImg P0) = 2 ^ 10 := by
    have h := card_starImg_mul (P0_le_Hj : P0 ≤ Hj)
    rw [inf_eq_right.mpr hEP0, hEcard, card_P0 hM hF] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 11) (h.trans (by norm_num))
  have hPtbot : Pt ⊓ Eg uJ 11 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mul_self_eq_one_of_pow_three (Eg_sq hEl hx.2) (hPt3 x hx.1)
  have hQcard : Nat.card (starImg Pt) = 9 := by
    have h := card_starImg_mul hPtH
    rw [hPtbot, hPt] at h
    simpa using h
  obtain ⟨y₀, hy₀Q, hy₀o, hy₀⟩ := m24_core' (K := starImg K) (Q := starImg Pt) (T := starImg P0)
    (starImg_le K) (starImg_mono hP0K) hTcard hKcard (starImg_mono hPtK) hQcard
  obtain ⟨x, hxPt, hxy⟩ := mem_starImg.mp hy₀Q
  have hy1 : (x : J) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hxy
    rw [← hxy, orderOf_one] at hy₀o
    omega
  have hyo : orderOf (x : J) = 3 := orderOf_eq_prime (hPt3 _ hxPt) hy1
  have hconj : ∀ l ∈ P0, l ∈ Subgroup.normalizer (Pt : Set J) →
      l * (x : J) * l⁻¹ ∈ Subgroup.zpowers (x : J) := by
    intro l hlP0 hlN
    have hlH : l ∈ Hj := P0_le_Hj hlP0
    have hconjQ : ∀ l' (hl'P0 : l' ∈ P0), l' ∈ Subgroup.normalizer (Pt : Set J) →
        ∀ σ ∈ starImg Pt, starHom ⟨l', P0_le_Hj hl'P0⟩ * σ * (starHom ⟨l', P0_le_Hj hl'P0⟩)⁻¹ ∈
          starImg Pt := by
      intro l' hl'P0 hl'N σ hσ
      obtain ⟨z, hzPt, rfl⟩ := mem_starImg.mp hσ
      refine mem_starImg.mpr ⟨⟨l', P0_le_Hj hl'P0⟩ * z * ⟨l', P0_le_Hj hl'P0⟩⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hl'N _).mp hzPt
      · rw [map_mul, map_mul, map_inv]
    have hτT : starHom ⟨l, hlH⟩ ∈ starImg P0 := mem_starImg.mpr ⟨⟨l, hlH⟩, hlP0, rfl⟩
    have hτN : starHom ⟨l, hlH⟩ ∈ Subgroup.normalizer ((starImg Pt : Subgroup _) :
        Set (Equiv.Perm (Fin 24))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro σ
      constructor
      · intro hσ
        exact hconjQ l hlP0 hlN σ hσ
      · intro hσ
        have := hconjQ l⁻¹ (P0.inv_mem hlP0)
          ((Subgroup.normalizer (Pt : Set J)).inv_mem hlN) _ hσ
        have hinv : starHom ⟨l⁻¹, P0_le_Hj (P0.inv_mem hlP0)⟩ = (starHom ⟨l, hlH⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [hinv, inv_inv] at this
        simpa [mul_assoc] using this
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hy₀ _ hτT hτN)
    have hlyl : l * (x : J) * l⁻¹ ∈ Pt := (Subgroup.mem_normalizer_iff.mp hlN _).mp hxPt
    have hyn : (x : J) ^ n ∈ Pt := Subgroup.zpow_mem _ hxPt n
    let xl : Hj := ⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹
    have hxl : (xl : J) = l * (x : J) * l⁻¹ := rfl
    have hxn : ((x ^ n : Hj) : J) = (x : J) ^ n := Subgroup.coe_zpow _ _ _
    have hstar : starHom xl = starHom (x ^ n) := by
      rw [map_zpow, hxy, hn]
      simp only [xl, map_mul, map_inv, hxy]
    have hker : xl * (x ^ n)⁻¹ ∈ starHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, hstar, map_inv, mul_inv_cancel]
    rw [ker_starHom, Subgroup.mem_subgroupOf] at hker
    have hPtmem : (xl : J) * ((x ^ n : Hj) : J)⁻¹ ∈ Pt := by
      rw [hxl, hxn]
      exact Pt.mul_mem hlyl (Pt.inv_mem hyn)
    have h1 : (xl : J) * ((x ^ n : Hj) : J)⁻¹ ∈ Pt ⊓ Eg uJ 11 := ⟨hPtmem, hker⟩
    rw [hPtbot, Subgroup.mem_bot, mul_inv_eq_one, hxl, hxn] at h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, h1.symm⟩
  refine ⟨Subgroup.zpowers (x : J), Subgroup.zpowers_le.mpr hxPt, ?_, ?_, ?_⟩
  · intro h
    exact hy1 (Subgroup.zpowers_eq_bot.mp h)
  · intro h
    have h3 : Nat.card (Subgroup.zpowers (x : J)) = 3 := by rw [Nat.card_zpowers, hyo]
    rw [h, hPt] at h3
    omega
  · refine mem_normalizer_of_conj P0 (Subgroup.normalizer (Pt : Set J)) _ ?_
    intro l hlA hlB u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hconj l hlA hlB) k

end CFSG.Quasithin.F134.J4E9
