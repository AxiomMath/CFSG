module

public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow
public import CFSG.RankThree.GF2n.Parrott.Section4EInv
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LinearAlgebra.F2Cube (fixedCount)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)

section Rest

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

@[expose] def FixedByE (h : Tim79a.ParrottHyp z) (E : Subgroup G) (hEH : E ≤ H z)
    (v : QuotientV.V z) : Prop :=
  ∀ (e : G) (he : e ∈ E), conjV h ⟨e, hEH he⟩ v = v

theorem exists_conj_imageQA45 {E : Subgroup G} (hE : IsParrottE z E) (hEH : E ≤ H z) :
    ∃ g : A45, ∀ a : A45, a ∈ imageQA45 D hEH ↔ g * a * g⁻¹ ∈ sQA45 := by
  obtain ⟨-, hEHJ, -, hEab, hEcard, hFcard, -, -⟩ := hE
  have h1 := card_eq_card_inf_J_mul_card_imageQA45 D hEH
  rw [hEcard, hFcard] at h1
  have hcard : Nat.card (imageQA45 D hEH) = 16 := by
    have h2 : 2 ^ 10 = 2 ^ 6 * Nat.card (imageQA45 D hEH) := h1
    omega
  have hab : IsElemAbelian 2 (imageQA45 D hEH) := isElemAbelian_imageQA45 D hEH hEab
  have hle := imageQA45_le_Q D hEH hEHJ
  obtain ⟨g, hg⟩ := qa45_elemAbelian_sixteen.2 (imageQA45 D hEH) hab hcard hle
  refine ⟨g, fun a => ?_⟩
  rw [← hg]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a', ha', hae⟩
    have h2 : a' = a := by
      have h3 : g * a' * g⁻¹ = g * a * g⁻¹ := hae
      exact mul_left_cancel (mul_right_cancel h3)
    rwa [h2] at ha'

variable (h : Tim79a.ParrottHyp z)

omit
  hN in
theorem fixedByE_pi_of_mem {E : Subgroup G} (hEH : E ≤ H z)
    (hEab : IsElemAbelian 2 E) {x : G} (hxE : x ∈ E) (hxJ : x ∈ J z) :
    FixedByE h E hEH (QuotientV.pi z ⟨x, hxJ⟩) := by
  intro e he
  rw [conjV_pi_conj h ⟨e, hEH he⟩ hxJ]
  congr 1
  apply Subtype.ext
  show e * x * e⁻¹ = x
  rw [hEab.comm he hxE]
  group

theorem fixedByE_spinVecToV_iff (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {E : Subgroup G}
    (hEH : E ≤ H z) (w : V) :
    FixedByE h E hEH (spinVecToV h P w) ↔
      ∀ a ∈ imageQA45 D hEH, SpinFixes a w := by
  constructor
  · intro hw a ha
    obtain ⟨e, he, rfl⟩ := (mem_imageQA45_iff D hEH a).mp ha
    have h1 := hw e he
    rw [conjV_spinVecToV D h P hP] at h1
    exact spinVecToV_injective h P h1
  · intro hw e he
    rw [conjV_spinVecToV D h P hP]
    congr 1
    exact hw _ ((mem_imageQA45_iff D hEH _).mpr ⟨e, he, rfl⟩)

theorem polarVZMod_eq_zero_of_fixedByE (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hEH : E ≤ H z)
    {g : A45} (hg : ∀ a : A45, a ∈ imageQA45 D hEH ↔ g * a * g⁻¹ ∈ sQA45)
    {v v' : QuotientV.V z} (hv : FixedByE h E hEH v) (hv' : FixedByE h E hEH v') :
    polarVZMod h v v' = 0 := by
  obtain ⟨w, rfl⟩ := spinVecToV_surjective h P v
  obtain ⟨w', rfl⟩ := spinVecToV_surjective h P v'
  rw [polarVZMod_spinVecToV_eq_b D h P hP]
  have key : ∀ u : V, FixedByE h E hEH (spinVecToV h P u) →
      ∀ s ∈ sQA45, SpinFixes s (((rhoA g : GL8) : Mat8) *ᵥ u) := by
    intro u hu s hs
    have h1 := (fixedByE_spinVecToV_iff D h P hP hEH u).mp hu
    have hs' : g⁻¹ * s * g ∈ imageQA45 D hEH := by
      rw [hg]
      have h2 : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
      rw [h2]
      exact hs
    exact spinFixes_mulVec_of_conj (h1 _ hs')
  have h3 := spinIsotropicFact _ _ (key w hv) (key w' hv')
  rwa [spinB_invariant] at h3

theorem mem_of_fixedByE (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hEH : E ≤ H z)
    (hEab : IsElemAbelian 2 E)
    (hEcent : E = H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G))
    {g : A45} (hg : ∀ a : A45, a ∈ imageQA45 D hEH ↔ g * a * g⁻¹ ∈ sQA45) {x : G}
    (hxJ : x ∈ J z) (hx : FixedByE h E hEH (QuotientV.pi z ⟨x, hxJ⟩)) : x ∈ E := by
  suffices hx' : x ∈ H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) by
    rwa [← hEcent] at hx'
  refine Subgroup.mem_inf.mpr ⟨J_le_H hxJ, Subgroup.mem_centralizer_iff.mpr (fun x' hx' => ?_)⟩
  have hx'E : x' ∈ E := (Subgroup.mem_inf.mp hx').1
  have hx'J : x' ∈ J z := (Subgroup.mem_inf.mp hx').2
  have hpol := polarVZMod_eq_zero_of_fixedByE D h P hP hEH hg
    (fixedByE_pi_of_mem h hEH hEab hx'E hx'J) hx
  exact ((polarVZMod_pi_eq_zero_iff h ⟨x', hx'J⟩ ⟨x, hxJ⟩).mp hpol).eq

theorem fixedByE_conj {E : Subgroup G} (hEH : E ≤ H z) {r : ↥(H z)}
    (hr' : ∀ a ∈ imageQA45 D hEH, (qH D r)⁻¹ * a * qH D r ∈ imageQA45 D hEH)
    {v : QuotientV.V z} (hv : FixedByE h E hEH v) : FixedByE h E hEH (conjV h r v) := by
  intro e he
  obtain ⟨e', he', hee'⟩ := (mem_imageQA45_iff D hEH _).mp
    (hr' (qH D ⟨e, hEH he⟩) ((mem_imageQA45_iff D hEH _).mpr ⟨e, he, rfl⟩))
  have h1 : conjV h (r⁻¹ * ⟨e, hEH he⟩ * r) = conjV h ⟨e', hEH he'⟩ := by
    symm
    apply conjV_eq_of_qH_eq h D
    rw [hee', map_mul, map_mul, map_inv]
  have h2 : conjV h ⟨e, hEH he⟩ (conjV h r v) =
      conjV h r (conjV h (r⁻¹ * ⟨e, hEH he⟩ * r) v) := by
    have h3 : (⟨e, hEH he⟩ : ↥(H z)) * r = r * (r⁻¹ * ⟨e, hEH he⟩ * r) := by group
    calc conjV h ⟨e, hEH he⟩ (conjV h r v) = conjV h (⟨e, hEH he⟩ * r) v := by
          rw [map_mul]; rfl
      _ = conjV h (r * (r⁻¹ * ⟨e, hEH he⟩ * r)) v := by rw [h3]
      _ = conjV h r (conjV h (r⁻¹ * ⟨e, hEH he⟩ * r) v) := by rw [map_mul]; rfl
  rw [h2, h1, hv e' he']

theorem conj_mem_of_mem_inf (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hEH : E ≤ H z) (hEab : IsElemAbelian 2 E)
    (hEcent : E = H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G))
    {g : A45} (hg : ∀ a : A45, a ∈ imageQA45 D hEH ↔ g * a * g⁻¹ ∈ sQA45) {r : ↥(H z)}
    (hr' : ∀ a ∈ imageQA45 D hEH, (qH D r)⁻¹ * a * qH D r ∈ imageQA45 D hEH) {x : G}
    (hxE : x ∈ E) (hxJ : x ∈ J z) : (r : G) * x * (r : G)⁻¹ ∈ E := by
  have hfix := fixedByE_conj D h hEH hr' (fixedByE_pi_of_mem h hEH hEab hxE hxJ)
  rw [conjV_pi_conj h r hxJ] at hfix
  exact mem_of_fixedByE D h P hP hEH hEab hEcent hg (H_conj_mem_J r hxJ) hfix

theorem conj_mem_of_normalizes (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hEH : E ≤ H z) (hEab : IsElemAbelian 2 E)
    (hEcent : E = H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G))
    {g : A45} (hg : ∀ a : A45, a ∈ imageQA45 D hEH ↔ g * a * g⁻¹ ∈ sQA45) {r : ↥(H z)}
    (hr : ∀ a ∈ imageQA45 D hEH, qH D r * a * (qH D r)⁻¹ ∈ imageQA45 D hEH) {e : G}
    (he : e ∈ E) : (r : G) * e * (r : G)⁻¹ ∈ E := by
  have hmem : (r : G) * e * (r : G)⁻¹ ∈
      H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(H z).mul_mem ((H z).mul_mem r.2 (hEH he)) ((H z).inv_mem r.2),
      Subgroup.mem_centralizer_iff.mpr (fun x hx => ?_)⟩
    have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).1
    have hxJ : x ∈ J z := (Subgroup.mem_inf.mp hx).2
    have hx' : (r : G)⁻¹ * x * ((r : G)⁻¹)⁻¹ ∈ E := by
      have hr'' : ∀ a ∈ imageQA45 D hEH, (qH D r⁻¹)⁻¹ * a * qH D r⁻¹ ∈ imageQA45 D hEH := by
        intro a ha
        rw [map_inv, inv_inv]
        exact hr a ha
      exact conj_mem_of_mem_inf D h P hP hEH hEab hEcent hg (r := r⁻¹) hr'' hxE hxJ
    rw [inv_inv] at hx'
    have hcomm : (r : G)⁻¹ * x * (r : G) * e = e * ((r : G)⁻¹ * x * (r : G)) :=
      hEab.comm hx' he
    calc x * ((r : G) * e * (r : G)⁻¹)
        = (r : G) * ((r : G)⁻¹ * x * (r : G) * e) * (r : G)⁻¹ := by group
      _ = (r : G) * (e * ((r : G)⁻¹ * x * (r : G))) * (r : G)⁻¹ := by rw [hcomm]
      _ = (r : G) * e * (r : G)⁻¹ * x := by group
  rwa [← hEcent] at hmem

theorem hrest_t_of_spin (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) tA → ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  intro E hE y hy hy2 hyc
  have hyH : y ∈ H z := commutator_sup_centerIn_le_H hy
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  have hEH : E ≤ H z := hE.1
  obtain ⟨g, hg⟩ := exists_conj_imageQA45 D hE hEH
  obtain ⟨-, -, -, hEab, -, hFcard, hEcent, -⟩ := hE
  obtain ⟨hr3, hr1, hrt, hrfix⟩ := spinOddFact
  obtain ⟨sb, hsb⟩ : ∃ sb : A45, sb = g⁻¹ * tA * g := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ rb : A45, rb = g⁻¹ * spinR0 * g := ⟨_, rfl⟩
  have hsbE : sb ∈ imageQA45 D hEH := by
    rw [hg]
    have h1 : g * sb * g⁻¹ = tA := by rw [hsb]; group
    rw [h1]
    exact tA_mem_S
  have hrb3 : rb ^ 3 = 1 := by
    have h1 : (g⁻¹ * spinR0 * g⁻¹⁻¹) ^ 3 = g⁻¹ * spinR0 ^ 3 * g⁻¹⁻¹ := conj_pow
    rw [inv_inv, hr3] at h1
    rw [hrb, h1]
    group
  have hrb1 : rb ≠ 1 := by
    intro h1
    apply hr1
    have h2 : spinR0 = g * rb * g⁻¹ := by rw [hrb]; group
    rw [h2, h1]
    group
  have hrbs : rb * sb = sb * rb := by
    rw [hrb, hsb]
    calc g⁻¹ * spinR0 * g * (g⁻¹ * tA * g) = g⁻¹ * (spinR0 * tA) * g := by group
      _ = g⁻¹ * (tA * spinR0) * g := by rw [hrt]
      _ = g⁻¹ * tA * g * (g⁻¹ * spinR0 * g) := by group
  have hrbfix : fixedCount ((rhoA rb : GL8) : Mat8) = 1 := by
    rw [fixedCount_apply_of_isConj rhoA (a := rb) (b := spinR0)
      (isConj_iff.mpr ⟨g, by rw [hrb]; group⟩)]
    exact hrfix
  have hrbN : ∀ a ∈ imageQA45 D hEH, rb * a * rb⁻¹ ∈ imageQA45 D hEH := by
    intro a ha
    rw [hg] at ha ⊢
    have h1 := spinNormFact _ ha
    have h2 : g * (rb * a * rb⁻¹) * g⁻¹ = spinR0 * (g * a * g⁻¹) * spinR0⁻¹ := by
      rw [hrb]; group
    rw [h2]
    exact h1
  obtain ⟨r, hrq, hr3'⟩ := exists_orderOf_three_lift D hrb3 hrb1
  have hrv : ∀ v : QuotientV.V z, conjV h r v = v → v = 1 :=
    fixed_point_free_of_fixedCount D h P hP (by rw [hrq]; exact hrbfix)
  have hrN : ∀ a ∈ imageQA45 D hEH, qH D r * a * (qH D r)⁻¹ ∈ imageQA45 D hEH := by
    rw [hrq]; exact hrbN
  obtain ⟨s₀, hs₀E, hs₀q⟩ := (mem_imageQA45_iff D hEH sb).mp hsbE
  have hKJ : ¬ 3 ∣ Nat.card ↥(E.subgroupOf (H z) ⊓ (J z).subgroupOf (H z)) := by
    have h1 : E.subgroupOf (H z) ⊓ (J z).subgroupOf (H z) = (E ⊓ J z).subgroupOf (H z) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1]
    have h2 : Nat.card ↥((E ⊓ J z).subgroupOf (H z)) = Nat.card ↥(E ⊓ J z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_of_left_le hEH)).toEquiv
    rw [h2, hFcard]
    norm_num
  obtain ⟨s, hsK, hsq, hsr⟩ := exists_lift_centralizer_of_le D (K := E.subgroupOf (H z)) (r := r)
    hr3' (fun x hx => Subgroup.mem_subgroupOf.mpr
      (conj_mem_of_normalizes D h P hP hEH hEab hEcent hg hrN
        (Subgroup.mem_subgroupOf.mp hx))) hKJ (s₀ := ⟨s₀, hEH hs₀E⟩)
    (Subgroup.mem_subgroupOf.mpr hs₀E) (by rw [hs₀q, hrq]; exact hrbs.symm)
  have hsE : (s : G) ∈ E := Subgroup.mem_subgroupOf.mp hsK
  have hsqb : qH D s = sb := hsq.trans hs₀q
  have hss1 : (s : G) * s = 1 := hEab.mul_self_eq_one hsE
  obtain ⟨d, hd⟩ := isConj_iff.mp hyc
  obtain ⟨c₁, hc₁⟩ := qH_surjective D (g⁻¹ * d)
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ↥(H z), y₁ = c₁ * ⟨y, hyH⟩ * c₁⁻¹ := ⟨_, rfl⟩
  have hy₁y : (y₁ : G) = (c₁ : G) * y * (c₁ : G)⁻¹ := by rw [hy₁]; rfl
  have hy₁sq : y₁ * y₁ = 1 := by
    have h1 : (⟨y, hyH⟩ : ↥(H z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
    rw [hy₁]
    calc c₁ * ⟨y, hyH⟩ * c₁⁻¹ * (c₁ * ⟨y, hyH⟩ * c₁⁻¹)
        = c₁ * (⟨y, hyH⟩ * ⟨y, hyH⟩) * c₁⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hy₁q : qH D y₁ = sb := by
    rw [hy₁, map_mul, map_mul, map_inv, hc₁, hsb, ← hd]
    group
  have hjJ : (y₁ : G) * (s : G)⁻¹ ∈ J z := by
    have h1 : y₁ * s⁻¹ ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).2 (by rw [map_mul, map_inv, hy₁q, hsqb, mul_inv_cancel])
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨j, hj⟩ : ∃ j : G, j = (y₁ : G) * (s : G)⁻¹ := ⟨_, rfl⟩
  have hjJ' : j ∈ J z := by rw [hj]; exact hjJ
  have hy₁j : (y₁ : G) = j * (s : G) := by rw [hj]; group
  have hy₁sq' : (y₁ : G) * y₁ = 1 := congrArg Subtype.val hy₁sq
  have hss : (s : G) * s ∈ J z := by rw [hss1]; exact (J z).one_mem
  have hjs : (j * (s : G)) * (j * (s : G)) ∈ centerIn (J z) := by
    rw [← hy₁j, hy₁sq']
    exact (centerIn (J z)).one_mem
  have hfixj := fixed_of_sq_mem_centerIn h hr3' hsr hrv hss hjJ' hjs
  have hsj : (s : G) * j * (s : G)⁻¹ = j := conj_eq_of_fixed h hZ hr3' hsr hrv hss hjJ' hfixj
  have hjj : j * j = 1 := by
    have h1 : (j * (s : G)) * (j * (s : G)) = (j * ((s : G) * j * (s : G)⁻¹)) * ((s : G) * s) := by
      group
    rw [hsj, hss1, ← hy₁j, hy₁sq'] at h1
    simpa using h1.symm
  have hq0 : ∀ (x : G) (hx : x ∈ J z), x * x = 1 → qVZMod h (QuotientV.pi z ⟨x, hx⟩) = 0 := by
    intro x hx hxx
    rw [qVZMod_eq_zero_iff]
    apply Subtype.ext
    rw [qV_pi_coe, pow_two]
    exact hxx
  obtain ⟨w₁, hw₁⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨j, hjJ'⟩)
  have hw₁fix : SpinFixes sb w₁ := by
    have h1 := hfixj
    rw [← hw₁, conjV_spinVecToV D h P hP s w₁, hsqb] at h1
    exact spinVecToV_injective h P h1
  have hw₁q : q w₁ = 0 := by
    have h1 := hq0 j hjJ' hjj
    rwa [← hw₁, qVZMod_spinVecToV_eq_q D h P hP] at h1
  have hwfix : SpinFixes tA (((rhoA g : GL8) : Mat8) *ᵥ w₁) :=
    spinFixes_mulVec_of_conj (by rw [← hsb]; exact hw₁fix)
  have hwq : q (((rhoA g : GL8) : Mat8) *ᵥ w₁) = 0 := by
    rw [spinQuad_invariant]
    exact hw₁q
  obtain ⟨g₂, hg₂t, hg₂r, hg₂S⟩ := spinRestFact _ hwfix hwq
  obtain ⟨gb, hgb⟩ : ∃ gb : A45, gb = g⁻¹ * g₂ * g := ⟨_, rfl⟩
  have hgbs : gb * sb = sb * gb := by
    rw [hgb, hsb]
    calc g⁻¹ * g₂ * g * (g⁻¹ * tA * g) = g⁻¹ * (g₂ * tA) * g := by group
      _ = g⁻¹ * (tA * g₂) * g := by rw [hg₂t]
      _ = g⁻¹ * tA * g * (g⁻¹ * g₂ * g) := by group
  have hgbr : gb * rb = rb * gb := by
    rw [hgb, hrb]
    calc g⁻¹ * g₂ * g * (g⁻¹ * spinR0 * g) = g⁻¹ * (g₂ * spinR0) * g := by group
      _ = g⁻¹ * (spinR0 * g₂) * g := by rw [hg₂r]
      _ = g⁻¹ * spinR0 * g * (g⁻¹ * g₂ * g) := by group
  obtain ⟨c, hcq, hcr⟩ := exists_lift_centralizer D hr3' (g := gb) (by rw [hrq]; exact hgbr)
  have hFix : ∀ a ∈ imageQA45 D hEH, SpinFixes a (((rhoA gb : GL8) : Mat8) *ᵥ w₁) := by
    intro a ha
    have h1 := spinFixes_mulVec_inv_of_conj (hg₂S _ ((hg a).1 ha))
    have h2 : ((rhoA gb : GL8) : Mat8) *ᵥ w₁ =
        ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ (((rhoA g₂ : GL8) : Mat8) *ᵥ
          (((rhoA g : GL8) : Mat8) *ᵥ w₁)) := by
      rw [hgb, rhoA_mulVec_mul, rhoA_mulVec_mul]
    rw [h2]
    exact h1
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ↥(H z), ζ = c * s * c⁻¹ * s⁻¹ := ⟨_, rfl⟩
  have hζJ : (ζ : G) ∈ J z := by
    have h1 : ζ ∈ (J z).subgroupOf (H z) := (J_mem_iff D _).2 (by
      rw [hζ, map_mul, map_mul, map_mul, map_inv, map_inv, hcq, hsqb]
      calc gb * sb * gb⁻¹ * sb⁻¹ = (gb * sb) * gb⁻¹ * sb⁻¹ := by group
        _ = (sb * gb) * gb⁻¹ * sb⁻¹ := by rw [hgbs]
        _ = 1 := by group)
    exact Subgroup.mem_subgroupOf.mp h1
  have hrζ : (r : G) * (ζ : G) * (r : G)⁻¹ = ζ := by
    have h1 : Commute ζ r := by
      rw [hζ]
      have hc : Commute c r := hcr
      have hs : Commute s r := hsr
      exact (((hc.mul_left hs).mul_left hc.inv_left).mul_left hs.inv_left)
    have h2 : (ζ : G) * r = r * ζ := congrArg Subtype.val h1.eq
    rw [← h2]
    group
  have hζZ : (ζ : G) ∈ centerIn (J z) := mem_centerIn_of_centralizes h hrv hζJ hrζ
  have hcs : (c : G) * s * (c : G)⁻¹ = (ζ : G) * s := by
    rw [hζ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hj''J : (c : G) * j * (c : G)⁻¹ * (ζ : G) ∈ J z :=
    (J z).mul_mem (H_conj_mem_J c hjJ') hζJ
  have hπ : QuotientV.pi z ⟨(c : G) * j * (c : G)⁻¹ * (ζ : G), hj''J⟩ =
      spinVecToV h P (((rhoA gb : GL8) : Mat8) *ᵥ w₁) := by
    have h1 : QuotientV.pi z ⟨(c : G) * j * (c : G)⁻¹ * (ζ : G), hj''J⟩ =
        QuotientV.pi z ⟨(c : G) * j * (c : G)⁻¹, H_conj_mem_J c hjJ'⟩ *
          QuotientV.pi z ⟨(ζ : G), hζJ⟩ := by
      rw [← map_mul]
      rfl
    have h2 : QuotientV.pi z ⟨(ζ : G), hζJ⟩ = 1 := (pi_eq_one_iff_mem_centerIn hζJ).mpr hζZ
    rw [h1, h2, mul_one, ← conjV_pi_conj h c hjJ', ← hw₁, conjV_spinVecToV D h P hP, hcq]
  have hj''E : (c : G) * j * (c : G)⁻¹ * (ζ : G) ∈ E := by
    refine mem_of_fixedByE D h P hP hEH hEab hEcent hg hj''J ?_
    rw [hπ]
    exact (fixedByE_spinVecToV_iff D h P hP hEH _).mpr hFix
  refine ⟨((c * c₁ : ↥(H z)) : G), (c * c₁).2, ?_⟩
  have key : ((c * c₁ : ↥(H z)) : G) * y * ((c * c₁ : ↥(H z)) : G)⁻¹ =
      ((c : G) * j * (c : G)⁻¹ * (ζ : G)) * (s : G) := by
    calc ((c * c₁ : ↥(H z)) : G) * y * ((c * c₁ : ↥(H z)) : G)⁻¹
        = (c : G) * ((c₁ : G) * y * (c₁ : G)⁻¹) * (c : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
      _ = (c : G) * (y₁ : G) * (c : G)⁻¹ := by rw [hy₁y]
      _ = (c : G) * (j * (s : G)) * (c : G)⁻¹ := by rw [hy₁j]
      _ = ((c : G) * j * (c : G)⁻¹) * ((c : G) * s * (c : G)⁻¹) := by group
      _ = ((c : G) * j * (c : G)⁻¹) * ((ζ : G) * s) := by rw [hcs]
      _ = ((c : G) * j * (c : G)⁻¹ * (ζ : G)) * (s : G) := by group
  rw [key]
  exact E.mul_mem hj''E hsE

theorem hrest_t_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) tA → ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact hrest_t_of_spin D h hZ P (fun a => by simpa [rhoA, toQAct] using hP a)

end Rest

end CFSG.RankThree.GF2n.Parrott
