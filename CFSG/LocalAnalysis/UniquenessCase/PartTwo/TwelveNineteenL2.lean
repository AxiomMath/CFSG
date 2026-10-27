module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qy
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qd
import CFSG.GH74.GLS.IVK.L2.Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveNineteen

theorem exists_torus_of_lieModel {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel K .PSL 2 p n) {W : Subgroup K} (hW : IsSylowOf p W ⊤) :
    ∃ D : Subgroup K, D ≤ normalizer (W : Set K) ∧ 2 * Nat.card D + 1 = Nat.card W ∧
      ∀ d ∈ D, d ≠ 1 → ∀ w ∈ W, d * w = w * d → w = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFf, hFfin, e, hF, hFq⟩ :=
    CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hp hp2 hL
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hW
  let W' : Sylow p K := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  have hWW' : (W' : Subgroup K) = W := rfl
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hF.1
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_psiEquiv_eq e hp hFq W'
  have hWcard : Nat.card W = Nat.card F := by
    haveI := Fintype.ofFinite F
    rw [← hWW', hc, Subgroup.card_map_of_injective
      (CFSG.GH74.GLS.IVK.L2Borel.psiEquiv e c).injective, CFSG.PSL2Table.card_unipotent h2,
      Nat.card_eq_fintype_card]
  have hW1 : (W' : Subgroup K) ≠ ⊥ := by
    intro hb
    have h1 : Nat.card W = 1 := by rw [← hWW', hb, Subgroup.card_bot]
    have := hF.2
    omega
  obtain ⟨-, D₀, -, hD₀, hfrob⟩ :=
    CFSG.GH74.GLS.IVK.ivk_1_4g F hF K e p n hp hFq W' W' le_rfl hW1
  obtain ⟨-, hDN, -, -, -, hfpf⟩ := hfrob
  refine ⟨D₀, hDN, ?_, hfpf⟩
  obtain ⟨k, hk⟩ := hF.1
  rw [hD₀, hWcard, hk]
  omega

theorem exists_torus {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L P₁ : Subgroup G}
    (hL : LieModel L .PSL 2 p n) (hP₁ : IsSylowOf p P₁ L) :
    ∃ D : Subgroup G, D ≤ L ∧ D ≤ normalizer (P₁ : Set G) ∧ 2 * Nat.card D + 1 = Nat.card P₁ ∧
      ∀ d ∈ D, d ≠ 1 → ∀ w ∈ P₁, d * w = w * d → w = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : P₁ ≤ L := hP₁.le
  have hS' : IsSylowOf p (P₁.subgroupOf L) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) L (A := P₁.subgroupOf L) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hP₁
  obtain ⟨D₀, hDN, hcard, hfpf⟩ := exists_torus_of_lieModel hp hp2 hL hS'
  have hc1 : Nat.card (P₁.subgroupOf L) = Nat.card P₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  refine ⟨D₀.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    have hdn := hDN hd
    rw [mem_normalizer_iff] at hdn ⊢
    intro w
    simp only [Subgroup.coe_subtype]
    constructor
    · intro hw
      have h1 := (hdn ⟨w, hle hw⟩).1 (Subgroup.mem_subgroupOf.2 hw)
      simpa using Subgroup.mem_subgroupOf.1 h1
    · intro hw
      have hwL : w ∈ L := by
        have h' : (d : G) * w * (d : G)⁻¹ ∈ L := hle hw
        have e : w = (d : G)⁻¹ * ((d : G) * w * (d : G)⁻¹) * (d : G) := by group
        rw [e]
        exact L.mul_mem (L.mul_mem (L.inv_mem d.2) h') d.2
      have h1 := (hdn ⟨w, hwL⟩).2 (Subgroup.mem_subgroupOf.2 (by simpa using hw))
      exact Subgroup.mem_subgroupOf.1 h1
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard, hc1]
  · rintro _ ⟨d, hd, rfl⟩ hd1 w hw hdw
    have hd1' : d ≠ 1 := fun h => hd1 (by rw [h]; rfl)
    have hwL : w ∈ L := hle hw
    have := hfpf d hd hd1' ⟨w, hwL⟩ (Subgroup.mem_subgroupOf.2 hw) (Subtype.ext hdw)
    exact congrArg Subtype.val this

theorem le_normalizer_P1 {p : ℕ} (hp : p.Prime) {P P₀ : Subgroup G} (hP : IsPGroup p P)
    (hP₀ : P₀ ≤ P) (hcard : Nat.card P₀ = p) (hwc : IsWeaklyClosedIn P₀ P) :
    P ≤ normalizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) := by
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hp hP hP₀ hcard (uc22p22q_weak_elem hwc)
  set K : Subgroup G := centralizer (P₀ : Set G) with hK
  set L : Subgroup G := UC6.inftyOf K with hLdef
  have hPK : P ≤ K := fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => (hcen₀ y hy z hz).symm
  have hKL : K ≤ normalizer (L : Set G) := by
    intro c hc
    have hcn : c ∈ normalizer (K : Set G) := Subgroup.le_normalizer hc
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => uc22p22q_inftyOf_conj hcn hx
    · intro hx
      have := uc22p22q_inftyOf_conj (inv_mem hcn) hx
      simpa [mul_assoc] using this
  exact fun y hy => inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hKL (hPK hy)⟩

theorem not_le_P1 (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R6_13 D) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀) :
    ¬ P₀ ≤ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) := by
  obtain ⟨⟨-, -, hwc, -, hL, -⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨n, hn, hE, hcard⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  obtain ⟨m, -, hLm⟩ := hL
  set L : Subgroup G := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  intro hle
  have hP₀L : P₀ ≤ L := hle.trans inf_le_right
  haveI := CFSG.GH74.GLS.EvenSelP.isSimpleGroup_of_lieModel' hpP hp2 hLm
  have hLK : L ≤ centralizer (P₀ : Set G) := Subgroup.map_subtype_le _
  have hnorm : (P₀.subgroupOf L).Normal := by
    refine ⟨fun a ha l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hc := Subgroup.mem_centralizer_iff.1 (hLK l.2) _ ha
    have : ((l * a * l⁻¹ : L) : G) = (a : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc]
      group
    rw [this]
    exact ha
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · have : P₀ = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hP₀L, hb, Subgroup.map_bot]
    have hc := hH.card
    rw [this, Subgroup.card_bot] at hc
    exact hpP.one_lt.ne hc
  · have hLP₀ : L ≤ P₀ := by
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ P₀.subgroupOf L := by rw [ht]; exact Subgroup.mem_top _
      exact this
    have h1 : Nat.card (P ⊓ L : Subgroup G) ≤ Nat.card P₀ :=
      Subgroup.card_le_of_le (inf_le_right.trans hLP₀)
    rw [hcard, hH.card] at h1
    have : p ^ n ≤ p ^ 1 := by simpa using h1
    have := (Nat.pow_le_pow_iff_right hpP.one_lt).1 this
    omega

private theorem card_sup_mul_card_inf {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem isElemAbelian_sup_P1 (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R6_13 D) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀) :
    IsElemAbelian p (P₀ ⊔ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ∧
      p ^ 2 < Nat.card (P₀ ⊔ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) := by
  obtain ⟨⟨-, -, hwc, -, hL, -⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨n, hn, hE, hcard⟩ := uc22p22q_P1_elem D hstd hH hwc hL hp2
  have hnot := not_le_P1 D hstd h613 hH
  set L : Subgroup G := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  set P₁ : Subgroup G := P ⊓ L with hP₁def
  have hLK : L ≤ centralizer (P₀ : Set G) := Subgroup.map_subtype_le _
  have hcomm : ∀ a ∈ P₀, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hLK hb.2) a ha
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hpP hH.sylow.isPGroup hH.le hH.card (uc22p22q_weak_elem hwc)
  have hP₀c : ∀ a ∈ P₀, ∀ b ∈ P₀, a * b = b * a := fun a ha b hb => hcen₀ a (hH.le ha) b hb
  have hP₁c : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hP₀p : ∀ a ∈ P₀, a ^ p = 1 := fun a ha => by
    have h1 : orderOf a ∣ p := hH.card ▸ Subgroup.orderOf_dvd_natCard P₀ ha
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hnorm : P₀ ≤ normalizer (P₁ : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun b hb =>
      (hcomm a ha b hb).symm)
  have hset : ((P₀ ⊔ P₁ : Subgroup G) : Set G) = (P₀ : Set G) * (P₁ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P₀ P₁ hnorm
  have hmem : ∀ x ∈ P₀ ⊔ P₁, ∃ a ∈ P₀, ∃ b ∈ P₁, a * b = x := by
    intro x hx
    have hx' : x ∈ ((P₀ ⊔ P₁ : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy]
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hcomm a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hP₀c a ha a' ha', hP₁c b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcomm a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    rw [(Commute.mul_pow (hcomm a ha b hb) p), hP₀p a ha, hE.2 b hb, one_mul]
  · have hprod := card_sup_mul_card_inf hnorm
    have hbot : P₀ ⊓ P₁ = ⊥ := by
      have hdvd : Nat.card (P₀ ⊓ P₁ : Subgroup G) ∣ p := by
        rw [← hH.card]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hpP).1 hdvd with h1 | h1
      · exact Subgroup.card_eq_one.1 h1
      · exfalso
        apply hnot
        have : P₀ ⊓ P₁ = P₀ :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hH.card, h1])
        rw [← this]
        exact inf_le_right
    rw [hbot, Subgroup.card_bot, mul_one, hH.card, hcard] at hprod
    rw [hprod]
    calc p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpP.one_lt (by norm_num)
      _ ≤ p * p ^ n := by
        rw [show p * p ^ n = p ^ (n + 1) by ring]
        exact Nat.pow_le_pow_right hpP.pos (by omega)

end TwelveNineteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
