module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2Exp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2Inner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RH2EF
public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S CFSG.RankThree.PartTwo.Sec14.Ronan148S

section Exclusion

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_centralizer {L : Subgroup G} (hZ : Subgroup.center L = ⊥) {x : G}
    (hxL : x ∈ L) (hxC : x ∈ Subgroup.centralizer (L : Set G)) : x = 1 := by
  have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem false_of_e9Move_EF (hEF : partTwoE G = partTwoF G) {L A : Subgroup G} {d t : G}
    (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L) (hLn : L.Normal)
    (h9 : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hmove : E9Move L) (hA : Late.IsE27 A) (hdA : d ∈ A)
    (hdC : d ∉ Subgroup.centralizer (L : Set G))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htL : t ∈ L) (ht2 : orderOf t = 2) (htd : t * d = d * t)
    (hP : ∃ P : Subgroup G, P ≤ L ∧ (∀ g ∈ P, g * d = d * g) ∧ 9 ≤ Nat.card P ∧
      ∀ g ∈ P, g ^ 3 = 1) : False := by
  have hNL : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top g
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  obtain ⟨dL, hdLL, hdL3, hrep⟩ := exists_inner_rep hZ hcube (hNL d) hd3
  have hcomm : ∀ l ∈ L, l * d = d * l → l * dL = dL * l := by
    intro l hl h
    have h1 : d * l * d⁻¹ = l := by rw [← h]; group
    rw [hrep l hl] at h1
    calc l * dL = dL * l * dL⁻¹ * dL := by rw [h1]
      _ = dL * l := by group
  have hdL1 : dL ≠ 1 := by
    rintro rfl
    apply hdC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hrep l hl
    simp only [one_mul, inv_one, mul_one] at h1
    calc l * d = d * l * d⁻¹ * d := by rw [h1]
      _ = d * l := by group
  have htdL : t * dL = dL * t := hcomm t htL htd
  obtain ⟨P, hPL, hPd, hP9, hP3⟩ := hP
  have hD3 : Nat.card (Subgroup.zpowers dL) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hdL3 hdL1
  obtain ⟨f, hfP, hfn⟩ : ∃ f ∈ P, f ∉ Subgroup.zpowers dL := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ Subgroup.zpowers dL := fun g hg => hcon g hg
    have := Subgroup.card_le_of_le hle
    omega
  have hfL : f ∈ L := hPL hfP
  have hfdL : f * dL = dL * f := hcomm f hfL (hPd f hfP)
  have hX3 : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (L : Set G) →
      CFSG.Assembly.IsElemAbelian 3 W → Nat.card W ≤ 3 := fun W hW hWe =>
    card_le_three_of_partTwo hEF hZ hdLL hdL3 hdL1 htL ht2 htdL hfL (hP3 f hfP) hfdL hfn hW hWe
  have hG3 : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have h1 := card_le_nine_mul_of_inner hZ hcube (fun g _ => hNL g) hE h9
    have h2 := hX3 _ inf_le_right (isElemAbelian_mono inf_le_left hE)
    omega
  have hL9 : ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hEL hE
    have hE' : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf L) :=
      isElemAbelian_comap L.subtype L.subtype_injective hE
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
    exact h9 _ hE'
  have hLE : ∃ E : Subgroup G, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hE9⟩ := hE9
    refine ⟨E.map L.subtype, Subgroup.map_subtype_le E, Ronan148S.isElemAbelian_map _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE9]
  obtain ⟨hAL9, -, hsplit⟩ := inner_split hZ hcube (fun g _ => hNL g) hA hG3 hL9 hLE
  have hcAL : ∀ x ∈ A ⊓ L, ∀ y ∈ A ⊓ Subgroup.centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) x
      (Subgroup.mem_inf.mp hx).2
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcAL).2
  have hdmem : d ∈ ((A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [hsplit]
    exact hdA
  rw [hset] at hdmem
  obtain ⟨a₁, ha₁, a₂, ha₂, hda⟩ := Set.mem_mul.mp hdmem
  have ha₁A : a₁ ∈ A := (Subgroup.mem_inf.mp ha₁).1
  have ha₁L : a₁ ∈ L := (Subgroup.mem_inf.mp ha₁).2
  have ha₂C : a₂ ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp ha₂).2
  have ha₁1 : a₁ ≠ 1 := by
    rintro rfl
    apply hdC
    rw [← hda, one_mul]
    exact ha₂C
  set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_comap L.subtype L.subtype_injective (isElemAbelian_mono inf_le_left hA.1)
  have hEcard : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
      hAL9]
  have hsE : (⟨a₁, ha₁L⟩ : L) ∈ E := ⟨ha₁A, ha₁L⟩
  have hs1 : (⟨a₁, ha₁L⟩ : L) ≠ 1 := fun h => ha₁1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hns⟩ := hmove E hEab hEcard _ hsE hs1
  have hnA : (n : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_of_subgroupOf inf_le_right hn
  have hnAA := mem_normalizer_of_split hsplit n.2 hnA
  have hnd := hN hnAA
  apply hns
  rw [← zpowers_subgroupOf ha₁L]
  refine mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr ha₁L) ?_
  have hmem : (n : G) * d * (n : G)⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hna₂ : (n : G) * a₂ = a₂ * (n : G) := (Subgroup.mem_centralizer_iff.mp ha₂C) _ n.2
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := (Subgroup.mem_centralizer_iff.mp ha₂C) _ ha₁L
  have hdk : d ^ k = a₁ ^ k * a₂ ^ k := by
    rw [← hda]
    exact (Commute.mul_zpow ha₁₂ k)
  have hnd' : (n : G) * d * (n : G)⁻¹ = ((n : G) * a₁ * (n : G)⁻¹) * a₂ := by
    rw [← hda]
    calc (n : G) * (a₁ * a₂) * (n : G)⁻¹
        = ((n : G) * a₁ * (n : G)⁻¹) * ((n : G) * a₂ * (n : G)⁻¹) := by group
      _ = ((n : G) * a₁ * (n : G)⁻¹) * a₂ := by rw [hna₂, mul_inv_cancel_right]
  have hv : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) = a₂ ^ k * a₂⁻¹ := by
    have h := hk.trans hnd'
    rw [hdk] at h
    calc (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹)
        = (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹ * a₂) * a₂⁻¹ := by group
      _ = (a₁ ^ k)⁻¹ * (a₁ ^ k * a₂ ^ k) * a₂⁻¹ := by rw [h]
      _ = a₂ ^ k * a₂⁻¹ := by group
  have hvL : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem (L.zpow_mem ha₁L k)) (L.mul_mem (L.mul_mem n.2 ha₁L) (L.inv_mem n.2))
  have hvC : (a₁ ^ k)⁻¹ * ((n : G) * a₁ * (n : G)⁻¹) ∈ Subgroup.centralizer (L : Set G) := by
    rw [hv]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ ha₂C k) (Subgroup.inv_mem _ ha₂C)
  have hv1 := eq_one_of_mem_centralizer hZ hvL hvC
  have hconj : (n : G) * a₁ * (n : G)⁻¹ = a₁ ^ k := by
    rw [inv_mul_eq_one] at hv1
    exact hv1.symm
  refine mem_normalizer_of_map_le ?_
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
  show (n : G) * a₁ * (n : G)⁻¹ ∈ _
  rw [hconj]
  exact Subgroup.zpow_mem_zpowers a₁ k

end Exclusion

section Row


theorem rowH2_of_e9Move {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData S) (hmove : E9Move S) (hexp : ∀ g : S, g ^ 9 = 1 → g ^ 3 = 1) :
    RowH2 S := by
  intro Γ _ _ C hC4 hCθ hEF A L K d hA hLA hdA hd1 hNd hLq hCL hLd hKM _ _ _ hA6 ⟨e⟩ _
  exfalso
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hAC : A ≤ C := hLA ▸ le_sup_right
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer {d} := hKM.trans inf_le_right
  have hKC : K ≤ C := hKL.trans hLC
  have hSL : SectionFourHyp ↥L :=
    Census.sectionFourHyp_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC)
      (sectionFourHyp_subgroup hC4 (L.subgroupOf C))
  have hZ : Subgroup.center ↥L = ⊥ :=
    hZS ↥L hSL hLq (isPGroup_center_of_normal hCθ hLC hCL hLq) ⟨e⟩
  set eL : ↥L ≃* S := (quotCenterEquivOfEqBot hZ).trans e with heL
  set L' : Subgroup C := L.subgroupOf C with hL'
  set A' : Subgroup C := A.subgroupOf C with hA'
  have eLL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have eL' : ↥L' ≃* S := eLL.trans eL
  have hZ' : Subgroup.center ↥L' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : eLL x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨g', rfl⟩ := eLL.surjective g
      rw [← map_mul, ← map_mul, hx g']
    rw [hZ, Subgroup.mem_bot] at hx'
    exact (map_eq_one_iff eLL eLL.injective).mp hx'
  have hcube' : CubeInner ↥L' := cubeInner_of_mulEquiv eL' hR.cubeInner
  have h9' : ∀ E : Subgroup ↥L', CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have := hR.card_le (E.map eL'.toMonoidHom) (Ronan148S.isElemAbelian_map _ hE)
    rwa [Subgroup.card_map_of_injective eL'.injective] at this
  have hE9' : ∃ E : Subgroup ↥L', CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨E, hE, hE9⟩ := hR.exists_e9
    exact ⟨E.map eL'.symm.toMonoidHom, Ronan148S.isElemAbelian_map _ hE,
      by rw [Subgroup.card_map_of_injective eL'.symm.injective, hE9]⟩
  have hmove' : E9Move ↥L' := hmove.of_mulEquiv eL'
  have hLn' : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hCL
  have hA'27 : Late.IsE27 A' := by
    refine ⟨isElemAbelian_comap C.subtype C.subtype_injective hA.1, ?_⟩
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA.2]
  set d' : C := ⟨d, hAC hdA⟩ with hd'
  have hd'A : d' ∈ A' := hdA
  have hd'C : d' ∉ Subgroup.centralizer (L' : Set C) := by
    intro h
    apply hLd
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := (Subgroup.mem_centralizer_iff.mp h) ⟨l, hLC hl⟩ hl
    exact congrArg Subtype.val h1
  have hN' : Subgroup.normalizer (A' : Set C) ≤
      Subgroup.normalizer (Subgroup.zpowers d' : Set C) := by
    intro g hg
    have h1 : (g : Γ) ∈ Subgroup.normalizer (A : Set Γ) := mem_normalizer_of_subgroupOf hAC hg
    have h2 := hNd g g.2 h1
    rw [← zpowers_subgroupOf (hAC hdA)]
    exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr (hAC hdA)) h2
  have h1080 : 1080 ∣ Nat.card ↥K := by
    rw [← Sec13.card_eq_of_isTripleCover_six hA6]
    exact Subgroup.card_quotient_dvd_card _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2
    (dvd_trans (by norm_num) h1080)
  set t : C := ⟨(t₀ : Γ), hKC t₀.2⟩ with ht
  have htL : t ∈ L' := hKL t₀.2
  have ht2 : orderOf t = 2 := by
    rw [← ht₀, ← Subgroup.orderOf_coe t₀]
    exact (Subgroup.orderOf_coe t).symm
  have htd : t * d' = d' * t := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKd t₀.2)
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3)
    (G := ↥K) (dvd_trans (by norm_num) h1080)
  set incl : ↥K →* ↥C := Subgroup.inclusion hKC with hincl
  have hincl_inj : Function.Injective incl := Subgroup.inclusion_injective hKC
  refine false_of_e9Move_EF hEF hZ' hcube' hLn' h9' hE9' hmove' hA'27 hd'A hd'C hN' htL ht2 htd
    ⟨P₀.map incl, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact hKL k.2
  · rintro _ ⟨k, -, rfl⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKd k.2)
  · rw [Subgroup.card_map_of_injective hincl_inj, hP₀]
    norm_num
  · rintro _ ⟨k, hk, rfl⟩
    have hk27 : k ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥P₀) (x := ⟨k, hk⟩)
      rw [hP₀] at this
      exact congrArg Subtype.val this
    have hkL : (k : Γ) ∈ L := hKL k.2
    set x : S := eL ⟨(k : Γ), hkL⟩ with hx
    have hx27 : x ^ 27 = 1 := by
      rw [hx, ← map_pow]
      have : (⟨(k : Γ), hkL⟩ : ↥L) ^ 27 = 1 := Subtype.ext (by
        simpa using congrArg (fun z : ↥K => (z : Γ)) hk27)
      rw [this, map_one]
    have hx9 : x ^ 9 = 1 := by
      have := hexp (x ^ 3) (by rw [← pow_mul]; exact hx27)
      rw [← pow_mul] at this
      exact this
    have hx3 := hexp x hx9
    have hk3 : (⟨(k : Γ), hkL⟩ : ↥L) ^ 3 = 1 := by
      apply eL.injective
      rw [map_pow, ← hx, hx3, map_one]
    have hik : ((incl k : C) : Γ) = (k : Γ) := rfl
    apply Subtype.ext
    rw [Subgroup.coe_pow, hik, Subgroup.coe_one]
    simpa using congrArg Subtype.val hk3

theorem rowOfH2_of_e9Move {X : Type} [Group X] [Finite X]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData X)
    (hmove : ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* X) → E9Move S)
    (hexp : ∀ g : X, g ^ 9 = 1 → g ^ 3 = 1) : RowOfH2 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine rowH2_of_e9Move ?_ (RankTwoData.of_mulEquiv eSX hR) (hmove S ⟨eSX⟩) ?_
  · intro L _ _ hS hL hZ3 ⟨e'⟩
    exact hZS L hS hL hZ3 ⟨e'.trans eSX⟩
  · intro g hg
    have h := hexp (eSX g) (by rw [← map_pow, hg, map_one])
    exact eSX.injective (by rw [map_pow, h, map_one])

end Row

section Rows


theorem rowOfH2_j4
    : RowOfH2 (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  haveI : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J4) := Finite.of_equiv _ b'.symm.toEquiv
  refine rowOfH2_of_e9Move ?_ rankTwo_spor_j4 (fun S _ _ ⟨e⟩ => e9Move_of_j4 ⟨e.trans b'.symm⟩) ?_
  · intro L _ _ hSL hL hZ3 ⟨e'⟩
    exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
      j4_orderChecks.1 j4_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro g hg
    obtain ⟨x, y, -, hx, hy, -, hzx, hzy, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact pow_three_of_pow_nine_of_mulEquiv (b'.symm : Spor .J4 ≃* Blueprint.NativeSporadic.J4)
      hx hy hzx hzy hc CFSG.RankThree.Asc83Table.J4.factorization_card hg

theorem rowOfH2_ru
    : RowOfH2 (Spor .Ru) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  haveI : Finite (Spor .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ru) := Finite.of_equiv _ b'.symm.toEquiv
  refine rowOfH2_of_e9Move ?_ rankTwo_spor_ru (fun S _ _ ⟨e⟩ => e9Move_of_ru ⟨e.trans b'.symm⟩) ?_
  · intro L _ _ hSL hL hZ3 ⟨e'⟩
    exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
      ru_orderChecks.1 ru_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro g hg
    obtain ⟨x, y, -, hx, hy, -, hzx, hzy, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact pow_three_of_pow_nine_of_mulEquiv (b'.symm : Spor .Ru ≃* Blueprint.NativeSporadic.Ru)
      hx hy hzx hzy hc CFSG.RankThree.Asc83Table.Ru.factorization_card hg

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
