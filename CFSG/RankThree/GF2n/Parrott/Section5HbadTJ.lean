module

public import CFSG.RankThree.GF2n.Parrott.SpinHbadTFacts
public import CFSG.RankThree.GF2n.Parrott.Section5HbadUTCoord
public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceT1
public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceS0
public import CFSG.RankThree.GF2n.Parrott.Section5FusionConj
public import CFSG.RankThree.GF2n.Parrott.SpinHvChecks

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem exists_centerIn_not_mem_J (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    (hZcard : Nat.card (centerIn T₁) = 8) :
  ∃ x ∈ centerIn T₁, x ∉ J z := by
  classical
  have hJT : J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) ≤ T₁ :=
  J_inf_centralizer_le_of_isSylowOf (z := z) h hT₁
  have hZJ : centerIn (J z ⊓ centralizer
  ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) = centerIn (J z) :=
  centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h
  by_contra hcon
  push Not at hcon
  have hsub : centerIn T₁ ≤ centerIn (J z) := by
    intro x hx
    obtain ⟨hxT, hxcen⟩ := Subgroup.mem_inf.mp hx
    have hxJ : x ∈ J z := hcon x hx
    have hxσ : x ∈ centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
      (Subgroup.mem_inf.mp (hT₁.le hxT)).2
    have hxN : x ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxJ, hxσ⟩
    have hxcN : x ∈ Subgroup.centralizer
        ((J z ⊓ centralizer
          ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hxcen y (hJT hy)
    rw [← hZJ]
    exact Subgroup.mem_inf.mpr ⟨hxN, hxcN⟩
  have hle : Nat.card (centerIn T₁) ≤ Nat.card (centerIn (J z)) :=
    Nat.card_le_card_of_injective
      (fun x : ↥(centerIn T₁) => (⟨(x : G), hsub x.2⟩ : ↥(centerIn (J z))))
      (fun x y hxy => Subtype.ext (congrArg (fun t : ↥(centerIn (J z)) => (t : G)) hxy))
  rw [hZcard, card_centerIn_J (z := z) h] at hle
  norm_num at hle

private theorem exists_tau_over_tA (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    ∃ τ : ↥(H z), qH (z := z) D τ = tA ∧ τ * τ = 1 ∧ (τ : G) ∉ J z ∧
      τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ ∧ τ * σ₂ = σ₂ * τ := by
  classical
  obtain ⟨T₁, hT₁, hmap⟩ := exists_isSylowOf_centralizer_sigma1Nine_map_eq (z := z) D h
  obtain ⟨hZcard, hZsq⟩ :=
    card_centerIn_and_mul_self_eq_one_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  obtain ⟨τG, hτZ, hτJ⟩ := exists_centerIn_not_mem_J (z := z) (D := D) h hT₁ hZcard
  have hτT : τG ∈ T₁ := hτZ.1
  have hτH : τG ∈ H z := (hT₁.le hτT).1
  have hτσ₁ : τG * ((sigma1Nine (z := z) D : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D : ↥(H z)) : G) * τG :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hT₁.le hτT)).2
  have hτ2G : τG * τG = 1 := hZsq τG hτZ
  let τ : ↥(H z) := ⟨τG, hτH⟩
  have hqτ : qH (z := z) D τ = tA :=
    qH_eq_t_of_mem_of_map_eq (z := z) D (T₁ := T₁) hmap hτT hτ2G hτJ
  have hτ2 : τ * τ = 1 := Subtype.ext hτ2G
  have hτne : (τ : G) ∉ J z := hτJ
  have hτσ₁' : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ :=
    Subtype.ext hτσ₁
  have hτσ₂' : τ * σ₂ = σ₂ * τ :=
    Subtype.ext (commute_of_mem_centerIn_of_map_eq (z := z) D h hT₁ hmap hσ₂ hq₂ hc₂ τG hτZ).symm
  exact ⟨τ, hqτ, hτ2, hτne, hτσ₁', hτσ₂'⟩

private def IsFixedT (h : Tim79a.ParrottHyp z) (P : GL8) (x : J z) : Prop :=
  ((rhoA tA : GL8) : Mat8) *ᵥ hbadCoord h P (x : G) = hbadCoord h P (x : G)

private theorem conjV_tau_eq_self_of_fixedT (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) {x : J z} (hx : IsFixedT h P x) :
    conjV h τ (QuotientV.pi z x) = QuotientV.pi z x := by
  rw [(spinVecToV_hbadCoord h P (x).2).symm, conjV_spinVecToV D h P hP, hqτ, hx]

private noncomputable def hbCocycle (τ : ↥(H z)) (x : J z) : J z :=
  x⁻¹ * conjJ' z τ x

private theorem conjJ'_eq_mul_cocycle {τ : ↥(H z)} (x : J z) :
    conjJ' z τ x = x * hbCocycle τ x := by
  unfold hbCocycle
  group

private theorem hbCocycle_mem_centerIn (h : Tim79a.ParrottHyp z) (P : GL8) {τ : ↥(H z)} {x : J z}
    (hx : conjV h τ (QuotientV.pi z x) = QuotientV.pi z x) :
    (hbCocycle τ x : G) ∈ centerIn (J z) := by
  have hpi : QuotientV.pi z (hbCocycle τ x) = 1 := by
    unfold hbCocycle
    rw [map_mul, map_inv, ← conjV_mk h τ x, hx, inv_mul_cancel]
  refine (hbadCoord_eq_zero_iff h P (hbCocycle τ x).2).mp ?_
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P (hbCocycle τ x).2, hpi, spinVecToV_zero]

private theorem hbConjJ'_eq_self_of_mem_centerIn {s : ↥(H z)} (hZs : conjZ z s = 1) {c : J z}
    (hc : (c : G) ∈ centerIn (J z)) : conjJ' z s c = c := by
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hcent : (c : G) * (s : G) = (s : G) * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (centerIn_le_centralizer_of_conjZ_eq_one hZs hc)
  rw [← hcent]
  group

private theorem hbConjZ_tau_eq_one (h : Tim79a.ParrottHyp z) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) : conjZ z τ = 1 :=
  conjZ_eq_one_of_qH_mem_QP45 (z := z) D h τ (by rw [hqτ]; exact t_mem_Q)

private theorem hbConjZ_sigma_eq_one (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = s2A) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  have h2 : conjZ z σ₂ = 1 :=
    conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
  rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D, h2, inv_one, mul_one]

private theorem exists_involution_coord_range_t (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1) (m : V) :
    ∃ n : J z, hbadCoord h P (n : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m ∧ n * n = 1 ∧
      conjJ' z τ n = n := by
  classical
  obtain ⟨mm, hmm⟩ := QuotientV.pi_surjective z (spinVecToV h P m)
  let n : J z := conjJ' z τ mm * mm⁻¹
  have hcoord : hbadCoord h P (n : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m := by
    apply spinVecToV_injective h P
    rw [← (spinVecToV_hbadCoord h P (n).2).symm, map_mul, map_inv, ← conjV_mk h τ mm, hmm,
      conjV_spinVecToV D h P hP, hqτ]
    have hinv : (spinVecToV h P m)⁻¹ = spinVecToV h P m :=
      inv_eq_of_mul_eq_one_right (by
        simpa [pow_two] using QuotientV.pow_two_eq_one_V h (spinVecToV h P m))
    rw [hinv, ← spinVecToV_add]
  have hq0 : q (hbadCoord h P (n : G)) = 0 := by
    rw [hcoord, spin_q_mul_t_add_eq_zero]
  have hn2 : n * n = 1 :=
    Subtype.ext ((mul_self_eq_one_iff_hbadCoord D h P hP n.2).mpr hq0)
  have hττ : conjJ' z τ (conjJ' z τ mm) = mm := by
    have hsq : conjJ' z τ * conjJ' z τ = 1 := by
      rw [← map_mul, hτ2, map_one]
    have := congrArg (fun f : MulAut (J z) => f mm) hsq
    simpa [MulAut.mul_apply] using this
  have hconj : conjJ' z τ n = n⁻¹ := by
    dsimp only [n]
    rw [map_mul, map_inv, hττ]
    group
  refine ⟨n, hcoord, hn2, ?_⟩
  rw [hconj, inv_eq_of_mul_eq_one_right hn2]

private theorem commute_tau_sigma {σ₂ τ : ↥(H z)}
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) :
    τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have h1 : (τ : G) * ((sigma1Nine (z := z) D : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D : ↥(H z)) : G) * (τ : G) := congrArg Subtype.val hτσ₁
  have h2 : (τ : G) * (σ₂ : G) = (σ₂ : G) * (τ : G) := congrArg Subtype.val hτσ₂
  calc (τ : G) * (((sigma1Nine (z := z) D : ↥(H z)) : G) * (σ₂ : G)⁻¹)
      = ((τ : G) * ((sigma1Nine (z := z) D : ↥(H z)) : G)) * (σ₂ : G)⁻¹ := by group
    _ = (((sigma1Nine (z := z) D : ↥(H z)) : G) * (τ : G)) * (σ₂ : G)⁻¹ := by rw [h1]
    _ = ((sigma1Nine (z := z) D : ↥(H z)) : G) * ((τ : G) * (σ₂ : G)⁻¹) := by group
    _ = ((sigma1Nine (z := z) D : ↥(H z)) : G) * ((σ₂ : G)⁻¹ * (τ : G)) := by
          congr 1
          exact (show Commute (τ : G) (σ₂ : G) from h2).inv_right.eq
    _ = (((sigma1Nine (z := z) D : ↥(H z)) : G) * (σ₂ : G)⁻¹) * (τ : G) := by group

private theorem conjJ'_eq_self_of_product {τ σ : ↥(H z)} {b n : J z}
    (ha : conjJ' z τ (conjJ' z σ b) = conjJ' z σ (conjJ' z τ b)) (hn : conjJ' z τ n = n)
    (hc2 : hbCocycle τ b * hbCocycle τ b = 1)
    (hcσ : conjJ' z σ (hbCocycle τ b) = hbCocycle τ b)
    (hcentral : ∀ d : J z, hbCocycle τ b * d = d * hbCocycle τ b) :
    conjJ' z τ (conjJ' z σ b * b * n) = conjJ' z σ b * b * n := by
  have hstep : hbCocycle τ b * (b * hbCocycle τ b) = b * (hbCocycle τ b * hbCocycle τ b) := by
    rw [← mul_assoc, hcentral b, mul_assoc]
  calc conjJ' z τ (conjJ' z σ b * b * n)
      = conjJ' z τ (conjJ' z σ b) * conjJ' z τ b * conjJ' z τ n := by rw [map_mul, map_mul]
    _ = (conjJ' z σ (conjJ' z τ b)) * (conjJ' z τ b) * n := by rw [ha, hn]
    _ = (conjJ' z σ (b * hbCocycle τ b)) * (b * hbCocycle τ b) * n := by
          rw [show conjJ' z τ b = b * hbCocycle τ b from conjJ'_eq_mul_cocycle b]
    _ = (conjJ' z σ b * hbCocycle τ b) * (b * hbCocycle τ b) * n := by rw [map_mul, hcσ]
    _ = conjJ' z σ b * (hbCocycle τ b * (b * hbCocycle τ b)) * n := by
          rw [mul_assoc (conjJ' z σ b) (hbCocycle τ b) (b * hbCocycle τ b)]
    _ = conjJ' z σ b * (b * (hbCocycle τ b * hbCocycle τ b)) * n := by rw [hstep]
    _ = conjJ' z σ b * (b * 1) * n := by rw [hc2]
    _ = conjJ' z σ b * b * n := by rw [mul_one]

private theorem conjJ'_eq_self_of_fixedT (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {k : J z} (hk : IsFixedT h P k) :
    conjJ' z τ k = k := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hqσ : qH (z := z) D σ = (⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hτσ : τ * σ = σ * τ := commute_tau_sigma (D := D) hτσ₁ hτσ₂
  have hZτ : conjZ z τ = 1 := hbConjZ_tau_eq_one (z := z) D h hqτ
  have hZσ : conjZ z σ = 1 := hbConjZ_sigma_eq_one (z := z) (D := D) h hq₂
  obtain ⟨u, hu, m, hm⟩ := spin_fixed_t_eq_sigma_add (hbadCoord h P (k : G)) hk
  obtain ⟨ũ, hũ⟩ := QuotientV.pi_surjective z (spinVecToV h P u)
  obtain ⟨n, hncoord, hn2, hnτ⟩ := exists_involution_coord_range_t (z := z) D h P hP hqτ hτ2 m
  let p : J z := conjJ' z σ ũ * ũ * n
  have hcpp : QuotientV.pi z p = spinVecToV h P (hbadCoord h P (k : G)) := by
    rw [show QuotientV.pi z p =
      QuotientV.pi z (conjJ' z σ ũ) * QuotientV.pi z ũ * QuotientV.pi z n from rfl]
    rw [← conjV_mk h σ ũ, hũ, conjV_spinVecToV D h P hP, hqσ,
      (spinVecToV_hbadCoord h P (n).2).symm, hncoord, ← spinVecToV_add,
      ← spinVecToV_add, hm]
  let ζ : J z := k * p⁻¹
  have hζ : (ζ : G) ∈ centerIn (J z) := by
    have hpi : QuotientV.pi z ζ = 1 := by
      unfold ζ
      rw [map_mul, map_inv, hcpp, ← (spinVecToV_hbadCoord h P (k).2).symm, mul_inv_cancel]
    refine (hbadCoord_eq_zero_iff h P ζ.2).mp ?_
    apply spinVecToV_injective h P
    rw [spinVecToV_hbadCoord h P ζ.2, hpi, spinVecToV_zero]
  have hk_eq : k = ζ * p := by unfold ζ; group
  have hsp : hbadCoord h P (ũ : G) = u :=
    spinVecToV_injective h P (by rw [← (spinVecToV_hbadCoord h P (ũ).2).symm, hũ])
  have hc := hbCocycle_mem_centerIn (z := z) h P
    (conjV_tau_eq_self_of_fixedT (z := z) D h P hP hqτ
      (x := ũ) (by rw [IsFixedT, hsp, hu]))
  have hc2 : hbCocycle τ ũ * hbCocycle τ ũ = 1 := Subtype.ext (centerIn_J_sq h hc)
  have hcσ : conjJ' z σ (hbCocycle τ ũ) = hbCocycle τ ũ :=
    hbConjJ'_eq_self_of_mem_centerIn (z := z) hZσ hc
  have hcτ : conjJ' z τ (hbCocycle τ ũ) = hbCocycle τ ũ :=
    hbConjJ'_eq_self_of_mem_centerIn (z := z) hZτ hc
  have hσŨ : conjJ' z τ (conjJ' z σ ũ) = conjJ' z σ (conjJ' z τ ũ) := by
    have hmul : conjJ' z τ * conjJ' z σ = conjJ' z σ * conjJ' z τ := by
      rw [← map_mul, ← map_mul, hτσ]
    have := congrArg (fun f : MulAut (J z) => f ũ) hmul
    simpa [MulAut.mul_apply] using this
  have hcentral : ∀ d : J z, hbCocycle τ ũ * d = d * hbCocycle τ ũ := by
    intro d
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hc.2 (d : G) d.2).symm
  have hfix : conjJ' z τ p = p := by
    dsimp only [p]
    exact conjJ'_eq_self_of_product hσŨ hnτ hc2 hcσ hcentral
  rw [hk_eq, map_mul, hfix, hbConjJ'_eq_self_of_mem_centerIn (z := z) hZτ hζ]

private noncomputable def Vfix (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) :
    Subgroup (QuotientV.V z) where
  carrier := {v | conjV h τ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (conjV h τ) (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change (conjV h τ) a⁻¹ = a⁻¹
    rw [map_inv, ha]

private noncomputable def polarKer (h : Tim79a.ParrottHyp z) (P : GL8) (wj : V) :
    Subgroup (QuotientV.V z) where
  carrier := {v | polarVZMod h (spinVecToV h P wj) v = 0}
  one_mem' := by
    change polarVZMod h (spinVecToV h P wj) 1 = 0
    rw [polarVZMod_one_right]
  mul_mem' := by
    intro a b ha hb
    change polarVZMod h (spinVecToV h P wj) (a * b) = 0
    rw [polarVZMod_add_right, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    have haa : a * a = 1 := by
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h a
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left haa
    rw [hinv]
    exact ha

private noncomputable def Qbar (h : Tim79a.ParrottHyp z) (P : GL8) (τ : ↥(H z)) (wj : V) :
    Subgroup (QuotientV.V z) :=
  Vfix h τ ⊓ polarKer h P wj

private noncomputable def Chat (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) :
    Subgroup (J z) :=
  (Vfix h τ).comap (QuotientV.pi z)

private theorem mem_Chat_iff (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) {x : J z} :
    x ∈ Chat h τ ↔ IsFixedT h P x := by
  constructor
  · intro hx
    have h1 : conjV h τ (QuotientV.pi z x) = QuotientV.pi z x := hx
    rw [(spinVecToV_hbadCoord h P (x).2).symm, conjV_spinVecToV D h P hP, hqτ] at h1
    exact spinVecToV_injective h P h1
  · intro hx
    exact conjV_tau_eq_self_of_fixedT (z := z) D h P hP hqτ hx

private noncomputable def hbToH (x : J z) : ↥(H z) := ⟨(x : G), J_le_H (z := z) x.2⟩

private theorem conjV_toH_eq_one (h : Tim79a.ParrottHyp z) (x : J z) :
    conjV h (hbToH (z := z) x) = 1 :=
  MonoidHom.mem_ker.mp (J_le_ker_conjV (z := z) h (Subgroup.mem_subgroupOf.mpr x.2))

private theorem mem_Qbar_of_mem_centralizer (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {x : J z}
    (hx : (x : G) ∈ J z ⊓ centralizer ({y} : Set G)) :
    QuotientV.pi z x ∈ Qbar h P τ (hbadCoord h P (j : G)) := by
  have hcomm : (x : G) * y = y * (x : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hyx : y * (x : G) * y⁻¹ = (x : G) := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfixY : conjV h ⟨y, hyH⟩ (QuotientV.pi z x) = QuotientV.pi z x := by
    rw [conjV_mk h ⟨y, hyH⟩ x]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    exact hyx
  have hyHeq : (⟨y, hyH⟩ : ↥(H z)) = τ * hbToH (z := z) j := Subtype.ext hyj
  have hconjVy : conjV h ⟨y, hyH⟩ = conjV h τ := by
    rw [hyHeq, map_mul, conjV_toH_eq_one, mul_one]
  have hfixT : conjV h τ (QuotientV.pi z x) = QuotientV.pi z x := by
    rw [← hconjVy]
    exact hfixY
  have hfx : IsFixedT h P x := by
    have h2 := hfixT
    rw [(spinVecToV_hbadCoord h P (x).2).symm, conjV_spinVecToV D h P hP, hqτ] at h2
    exact spinVecToV_injective h P h2
  have hτx : conjJ' z τ x = x :=
    conjJ'_eq_self_of_fixedT (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hfx
  have hτxG : (τ : G) * (x : G) * (τ : G)⁻¹ = (x : G) := congrArg Subtype.val hτx
  have hτinv : (τ : G)⁻¹ = (τ : G) :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using congrArg Subtype.val hτ2)
  have hτxG' : (τ : G) * (x : G) * (τ : G) = (x : G) := by simpa [hτinv] using hτxG
  have hjx' : (j : G) * (x : G) * (j : G)⁻¹ = (x : G) := by
    calc (j : G) * (x : G) * (j : G)⁻¹
        = (τ : G)⁻¹ * ((τ : G) * (j : G) * (x : G) * ((τ : G) * (j : G))⁻¹) * (τ : G) := by
          group
      _ = (τ : G)⁻¹ * (y * (x : G) * y⁻¹) * (τ : G) := by rw [← hyj]
      _ = (τ : G)⁻¹ * (x : G) * (τ : G) := by rw [hyx]
      _ = (x : G) := by rw [hτinv]; exact hτxG'
  have hjx : (j : G) * (x : G) = (x : G) * (j : G) := by
    calc (j : G) * (x : G) = ((j : G) * (x : G) * (j : G)⁻¹) * (j : G) := by group
      _ = (x : G) * (j : G) := by rw [hjx']
  have hb : b (hbadCoord h P (j : G)) (hbadCoord h P (x : G)) = 0 :=
    (commute_iff_hbadCoord D h P hP j.2 x.2).mp hjx
  refine Subgroup.mem_inf.mpr
    ⟨conjV_tau_eq_self_of_fixedT (z := z) D h P hP hqτ hfx, ?_⟩
  change polarVZMod h (spinVecToV h P (hbadCoord h P (j : G))) (QuotientV.pi z x) = 0
  rw [(spinVecToV_hbadCoord h P (x).2).symm, polarVZMod_spinVecToV_eq_b D h P hP]
  exact hb

private theorem mem_centralizer_of_mem_Qbar (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {x : J z}
    (hx : QuotientV.pi z x ∈ Qbar h P τ (hbadCoord h P (j : G))) :
    (x : G) ∈ J z ⊓ centralizer ({y} : Set G) := by
  obtain ⟨hfix, hb⟩ := Subgroup.mem_inf.mp hx
  change polarVZMod h (spinVecToV h P (hbadCoord h P (j : G))) (QuotientV.pi z x) = 0 at hb
  rw [(spinVecToV_hbadCoord h P (x).2).symm, polarVZMod_spinVecToV_eq_b D h P hP] at hb
  have hfx : IsFixedT h P x := (mem_Chat_iff (z := z) D h P hP hqτ).mp hfix
  have hτx : conjJ' z τ x = x :=
    conjJ'_eq_self_of_fixedT (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hfx
  have hb' : b (hbadCoord h P (j : G)) (hbadCoord h P (x : G)) = 0 := hb
  have hjx : Commute (j : G) (x : G) :=
    (commute_iff_hbadCoord D h P hP j.2 x.2).mpr hb'
  have hjx' : (j : G) * (x : G) * (j : G)⁻¹ = (x : G) := by
    rw [hjx.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hyx : y * (x : G) * y⁻¹ = (x : G) := by
    calc y * (x : G) * y⁻¹
        = (τ : G) * (j : G) * (x : G) * ((τ : G) * (j : G))⁻¹ := by rw [hyj]
      _ = (τ : G) * ((j : G) * (x : G) * (j : G)⁻¹) * (τ : G)⁻¹ := by group
      _ = (τ : G) * (x : G) * (τ : G)⁻¹ := by rw [hjx']
      _ = (x : G) := congrArg Subtype.val hτx
  have hyx' : y * (x : G) = (x : G) * y := by
    calc y * (x : G) = (y * (x : G) * y⁻¹) * y := by group
      _ = (x : G) * y := by rw [hyx]
  refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr hyx'.symm

private noncomputable def CJy (h : Tim79a.ParrottHyp z) (P : GL8) (τ : ↥(H z)) (wj : V) :
    Subgroup (J z) :=
  (Qbar h P τ wj).comap (QuotientV.pi z)

private theorem card_pi_ker (h : Tim79a.ParrottHyp z) :
    Nat.card (QuotientV.pi z).ker = 4 := by
  rw [QuotientV.pi_ker]
  rw [show Nat.card ↥((centerIn (J z)).subgroupOf (J z)) = Nat.card ↥(centerIn (J z)) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : centerIn (J z) ≤ J z)).toEquiv]
  exact card_centerIn_J (z := z) h

private noncomputable def qbarEquiv (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (wj : V) :
    ↥(Qbar h P τ wj) ≃
      {v : V // ((rhoA tA : GL8) : Mat8) *ᵥ v = v ∧ b wj v = 0} where
  toFun v :=
    ⟨Classical.choose (spinVecToV_surjective h P (v : QuotientV.V z)), by
      obtain ⟨hv, hp⟩ := Subgroup.mem_inf.mp v.2
      have hfix : conjV h τ (v : QuotientV.V z) = (v : QuotientV.V z) := hv
      rw [← Classical.choose_spec (spinVecToV_surjective h P (v : QuotientV.V z))] at hfix
      rw [conjV_spinVecToV D h P hP, hqτ] at hfix
      refine ⟨spinVecToV_injective h P hfix, ?_⟩
      change polarVZMod h (spinVecToV h P wj) (v : QuotientV.V z) = 0 at hp
      rw [← Classical.choose_spec (spinVecToV_surjective h P (v : QuotientV.V z)),
        polarVZMod_spinVecToV_eq_b D h P hP] at hp
      exact hp⟩
  invFun w :=
    ⟨spinVecToV h P w.1, by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · change conjV h τ (spinVecToV h P w.1) = spinVecToV h P w.1
        rw [conjV_spinVecToV D h P hP, hqτ, w.2.1]
      · change polarVZMod h (spinVecToV h P wj) (spinVecToV h P w.1) = 0
        rw [polarVZMod_spinVecToV_eq_b D h P hP]
        exact w.2.2⟩
  left_inv v := by
    apply Subtype.ext
    dsimp only
    exact Classical.choose_spec (spinVecToV_surjective h P (v : QuotientV.V z))
  right_inv w := by
    apply Subtype.ext
    dsimp only
    exact spinVecToV_injective h P
      (Classical.choose_spec (spinVecToV_surjective h P (spinVecToV h P w.1)))

private theorem card_Qbar (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (wj : V)
    (hwj : ((rhoA tA : GL8) : Mat8) *ᵥ wj = wj)
    (hj' : ¬ ∃ m : V, wj = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    Nat.card ↥(Qbar h P τ wj) = 32 := by
  rw [Nat.card_congr (qbarEquiv (z := z) D h P hP hqτ wj)]
  exact spin_card_fixed_t_perp wj hwj hj'

private theorem card_CJy (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (wj : V)
    (hwj : ((rhoA tA : GL8) : Mat8) *ᵥ wj = wj)
    (hj' : ¬ ∃ m : V, wj = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    Nat.card ↥(CJy h P τ wj) = 128 := by
  have hcard := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card (QuotientV.pi z)
    (QuotientV.pi_surjective z) (Qbar h P τ wj)
  dsimp only [CJy] at hcard ⊢
  rw [card_pi_ker (z := z) h, card_Qbar (z := z) D h P hP hqτ wj hwj hj'] at hcard
  exact hcard.trans (by norm_num)

private theorem mem_CJy_iff (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (x : J z) :
    x ∈ CJy h P τ (hbadCoord h P (j : G)) ↔
      (x : G) ∈ J z ⊓ centralizer ({y} : Set G) :=
  ⟨mem_centralizer_of_mem_Qbar (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj,
    mem_Qbar_of_mem_centralizer (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj⟩

private theorem card_J_inf_centralizer (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G))
    (hwj : ((rhoA tA : GL8) : Mat8) *ᵥ hbadCoord h P (j : G) = hbadCoord h P (j : G))
    (hj' : ¬ ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) = 128 := by
  have hsub : (J z ⊓ centralizer ({y} : Set G)).subgroupOf (J z) =
      CJy h P τ (hbadCoord h P (j : G)) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact (mem_CJy_iff (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj x).symm
  calc Nat.card ↥(J z ⊓ centralizer ({y} : Set G))
      = Nat.card ↥((J z ⊓ centralizer ({y} : Set G)).subgroupOf (J z)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : J z ⊓ centralizer ({y} : Set G) ≤ J z)).toEquiv).symm
    _ = Nat.card ↥(CJy h P τ (hbadCoord h P (j : G))) := by rw [hsub]
    _ = 128 := card_CJy (z := z) D h P hP hqτ (hbadCoord h P (j : G)) hwj hj'

private theorem vec_add_t_eq_zero {T : Mat8} (hT : T * T = 1) {wj m : V}
    (hm : wj = T *ᵥ m + m) :
    m + T *ᵥ wj + T *ᵥ m = 0 := by
  have h2 : ∀ x : V, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  rw [hm, Matrix.mulVec_add, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  calc m + (m + T *ᵥ m) + T *ᵥ m = (m + m) + (T *ᵥ m + T *ᵥ m) := by abel
    _ = 0 := by rw [h2 m, h2 (T *ᵥ m), add_zero]

private theorem hbadCoord_zetaJ_eq_zero (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {m : V}
    (hm : hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    {mJ : J z} (hmJ : hbadCoord h P (mJ : G) = m) :
    hbadCoord h P ((mJ * conjJ' z τ j * conjJ' z τ mJ⁻¹ : J z) : G) = 0 := by
  classical
  let T : Mat8 := ((rhoA tA : GL8) : Mat8)
  have hT : T * T = 1 := by
    rw [show T = ((rhoA tA : GL8) : Mat8) from rfl, rhoA_t_eq_Mx]
    change Mt * Mt = 1
    exact Mt_sq
  let ζJ : J z := mJ * conjJ' z τ j * conjJ' z τ mJ⁻¹
  have hmJinv : hbadCoord h P ((mJ⁻¹ : J z) : G) = m := by
    rw [show ((mJ⁻¹ : J z) : G) = (mJ : G)⁻¹ from rfl, hbadCoord_inv h P mJ.2, hmJ]
  have hcoord : QuotientV.pi z ζJ =
      spinVecToV h P (m + T *ᵥ hbadCoord h P (j : G) + T *ᵥ m) := by
    dsimp only [ζJ]
    rw [map_mul, map_mul]
    rw [← conjV_mk h τ j, ← conjV_mk h τ mJ⁻¹]
    rw [(spinVecToV_hbadCoord h P (mJ).2).symm, (spinVecToV_hbadCoord h P (j).2).symm,
      (spinVecToV_hbadCoord h P (mJ⁻¹).2).symm, hmJinv]
    rw [conjV_spinVecToV D h P hP, hqτ, conjV_spinVecToV D h P hP, hqτ]
    rw [← spinVecToV_add, ← spinVecToV_add, hmJ]
  have hmT : hbadCoord h P (j : G) = T *ᵥ m + m := hm
  have hzero : m + T *ᵥ hbadCoord h P (j : G) + T *ᵥ m = 0 :=
    vec_add_t_eq_zero hT hmT
  have hpi : QuotientV.pi z ζJ = 1 := by
    rw [hcoord, hzero, spinVecToV_zero]
  change hbadCoord h P (ζJ : G) = 0
  apply spinVecToV_injective h P
  rw [spinVecToV_hbadCoord h P ζJ.2, hpi, spinVecToV_zero]

private theorem exists_zeta_of_coord_range (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {m : V}
    (hm : hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    {mJ : J z} (hmJ : hbadCoord h P (mJ : G) = m) :
    ∃ ζ : J z, (ζ : G) ∈ centerIn (J z) ∧
      hbToH (z := z) mJ * ⟨y, hyH⟩ * (hbToH (z := z) mJ)⁻¹ = τ * hbToH (z := z) ζ := by
  classical
  let ζJ : J z := mJ * conjJ' z τ j * conjJ' z τ mJ⁻¹
  have hζZ : (ζJ : G) ∈ centerIn (J z) :=
    (hbadCoord_eq_zero_iff h P ζJ.2).mp
      (hbadCoord_zetaJ_eq_zero (z := z) (D := D) h P hP hqτ hτ2 hyH hyj hm hmJ)
  have hζτ : conjJ' z τ ζJ = ζJ :=
    hbConjJ'_eq_self_of_mem_centerIn (z := z)
      (hbConjZ_tau_eq_one (z := z) D h hqτ) hζZ
  have hx : (hbToH (z := z) mJ * ⟨y, hyH⟩ * (hbToH (z := z) mJ)⁻¹ : ↥(H z)) =
      τ * hbToH (z := z) ζJ := by
    apply Subtype.ext
    change (mJ : G) * y * (mJ : G)⁻¹ = (τ : G) * (ζJ : G)
    have hζcoe : (ζJ : G) = (mJ : G) * ((τ : G) * (j : G) * (τ : G)⁻¹) *
        ((τ : G) * (mJ : G)⁻¹ * (τ : G)⁻¹) := by
      dsimp only [ζJ]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, conjJ'_apply_coe, conjJ'_apply_coe,
        Subgroup.coe_inv]
    have hτinv : (τ : G)⁻¹ = (τ : G) :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using congrArg Subtype.val hτ2)
    have hτsq : (τ : G) * (τ : G) = 1 := congrArg Subtype.val hτ2
    have hcommG : (τ : G) * (ζJ : G) = (ζJ : G) * (τ : G) := by
      have h := congrArg Subtype.val hζτ
      rw [conjJ'_apply_coe] at h
      calc (τ : G) * (ζJ : G) = ((τ : G) * (ζJ : G) * (τ : G)⁻¹) * (τ : G) := by group
        _ = (ζJ : G) * (τ : G) := by rw [h]
    calc (mJ : G) * y * (mJ : G)⁻¹ = (mJ : G) * ((τ : G) * (j : G)) * (mJ : G)⁻¹ := by
          rw [hyj]
      _ = (ζJ : G) * (τ : G) := by
          rw [hζcoe, hτinv]
          simp only [mul_assoc]
          rw [hτsq, mul_one]
          rw [← mul_assoc (τ : G) (τ : G) (mJ : G)⁻¹, hτsq, one_mul]
      _ = (τ : G) * (ζJ : G) := hcommG.symm
  exact ⟨ζJ, hζZ, hx⟩
private theorem mul_mem_lemma54T₂ (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = s2A) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {ζ : J z} (hζZ : (ζ : G) ∈ centerIn (J z)) :
    (τ : G) * (ζ : G) ∈
      lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hcommτσ : τ * σ = σ * τ := commute_tau_sigma (z := z) (D := D) hτσ₁ hτσ₂
  have hζH : (ζ : G) ∈ H z := J_le_H (z := z) ζ.2
  have hxH : (τ : G) * (ζ : G) ∈ H z := (H z).mul_mem τ.2 hζH
  have hxτσ : ((τ : G) * (ζ : G)) * (σ : G) = (σ : G) * ((τ : G) * (ζ : G)) := by
    have h1 : (τ : G) * (σ : G) = (σ : G) * (τ : G) := congrArg Subtype.val hcommτσ
    have h2 : (ζ : G) * (σ : G) = (σ : G) * (ζ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centerIn_le_centralizer_of_conjZ_eq_one (hbConjZ_sigma_eq_one (z := z) (D := D) h hq₂) hζZ)
    calc ((τ : G) * (ζ : G)) * (σ : G) = (τ : G) * ((ζ : G) * (σ : G)) := by group
      _ = (τ : G) * ((σ : G) * (ζ : G)) := by rw [h2]
      _ = ((τ : G) * (σ : G)) * (ζ : G) := by group
      _ = ((σ : G) * (τ : G)) * (ζ : G) := by rw [h1]
      _ = (σ : G) * ((τ : G) * (ζ : G)) := by group
  have hq : qH (z := z) D ⟨(τ : G) * (ζ : G), hxH⟩ = tA := by
    have heq : (⟨(τ : G) * (ζ : G), hxH⟩ : ↥(H z)) = τ * hbToH (z := z) ζ := Subtype.ext rfl
    have hζ1 : qH (z := z) D (hbToH (z := z) ζ) = 1 := by
      have hmem : hbToH (z := z) ζ ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr ζ.2
      exact (J_mem_iff (z := z) D _).mp hmem
    rw [heq, map_mul, hqτ, hζ1, mul_one]
  have hmem : tA ∈ Subgroup.closure ({tA, uA * vA} : Set A45) :=
    Subgroup.subset_closure (by simp)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxH, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hxτσ
  · refine Subgroup.mem_map.mpr ⟨⟨(τ : G) * (ζ : G), hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    rw [hq]
    exact hmem

private theorem false_of_coord_range_t (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G))
    (hbad : ∀ c ∈ H z,
      c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hmem : ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) : False := by
  obtain ⟨m, hm⟩ := hmem
  obtain ⟨mJ, hmJ⟩ := QuotientV.pi_surjective z (spinVecToV h P m)
  have hmJcoord : hbadCoord h P (mJ : G) = m :=
    spinVecToV_injective h P (by rw [← (spinVecToV_hbadCoord h P (mJ).2).symm, hmJ])
  obtain ⟨ζ, hζZ, hx⟩ :=
    exists_zeta_of_coord_range (z := z) D h P hP hqτ hτ2 hyH hyj hm hmJcoord
  have hT₂ : (τ : G) * (ζ : G) ∈
      lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) :=
    mul_mem_lemma54T₂ (z := z) D h hq₂ hqτ hτσ₁ hτσ₂ hζZ
  apply hbad (mJ : G) (J_le_H (z := z) mJ.2)
  have hxG : (mJ : G) * y * (mJ : G)⁻¹ = (τ : G) * (ζ : G) := by
    have := congrArg Subtype.val hx
    simpa [hbToH] using this
  rwa [hxG]

private theorem exists_coord_fixed_not_orthogonal {wj : V}
    (hwj : ((rhoA tA : GL8) : Mat8) *ᵥ wj = wj)
    (hj' : ¬ ∃ m : V, wj = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    ∃ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k ∧ b wj k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hj' (spin_exists_eq_mul_t_add_of_perp wj (fun k hk => hcon k hk))

private theorem exists_mem_Chat_not_orthogonal (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) {j : J z}
    (hwj : ((rhoA tA : GL8) : Mat8) *ᵥ hbadCoord h P (j : G) = hbadCoord h P (j : G))
    (hj' : ¬ ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    ∃ k₀ : J z, k₀ ∈ Chat h τ ∧ b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0 := by
  obtain ⟨k, hkfix, hkb⟩ :=
    exists_coord_fixed_not_orthogonal hwj hj'
  obtain ⟨k₀, hk₀⟩ := QuotientV.pi_surjective z (spinVecToV h P k)
  have hcoord : hbadCoord h P (k₀ : G) = k :=
    spinVecToV_injective h P (by rw [← (spinVecToV_hbadCoord h P (k₀).2).symm, hk₀])
  refine ⟨k₀, ?_, ?_⟩
  · rw [mem_Chat_iff (z := z) D h P hP hqτ, IsFixedT, hcoord]
    exact hkfix
  · rwa [hcoord]

private noncomputable def comY (yH : ↥(H z)) (k : J z) : J z :=
  k * (conjJ' z yH k)⁻¹

private theorem comY_mul_y {y : G} {k : J z} (yH : ↥(H z))
    (hy : y = (yH : G)) :
    (comY yH k : G) * y = (k : G) * y * (k : G)⁻¹ := by
  have hconj : (conjJ' z yH k : G) = (yH : G) * (k : G) * (yH : G)⁻¹ :=
    conjJ'_apply_coe (z := z) yH k
  unfold comY
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hconj]
  rw [← hy]
  group

private theorem comY_chat_eq_z (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (hb : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) :
    comY (⟨y, hyH⟩ : ↥(H z)) k₀ = ⟨z, z_mem_J h⟩ := by
  classical
  let yH : ↥(H z) := ⟨y, hyH⟩
  let jH : ↥(H z) := hbToH (z := z) j
  have hyHeq : yH = τ * jH := Subtype.ext hyj
  have hkfix : IsFixedT h P k₀ := (mem_Chat_iff (z := z) D h P hP hqτ).mp hk₀
  have hτk : conjJ' z τ k₀ = k₀ :=
    conjJ'_eq_self_of_fixedT (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hkfix
  have hb1 : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) = 1 := by
    have hZ2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact hZ2 _ hb
  let d : J z := conjJ' z jH k₀ * k₀⁻¹
  have hd_eq : d = ⟨z, z_mem_J h⟩ := by
    apply Subtype.ext
    rw [show (d : G) = (j : G) * (k₀ : G) * (j : G)⁻¹ * (k₀ : G)⁻¹ from by
      dsimp only [d, jH, hbToH]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]]
    exact commutator_eq_z_of_hbadCoord D h P hP j.2 k₀.2 hb1
  have hdz : conjJ' z τ d = d := by
    rw [hd_eq]
    exact hbConjJ'_eq_self_of_mem_centerIn (z := z)
      (hbConjZ_tau_eq_one (z := z) D h hqτ) (z_mem_centerIn_J h)
  have hsplit : conjJ' z jH k₀ = d * k₀ := by
    dsimp only [d]
    group
  have hconj : conjJ' z yH k₀ = d * k₀ := by
    rw [hyHeq, map_mul]
    change conjJ' z τ (conjJ' z jH k₀) = d * k₀
    rw [hsplit, map_mul, hdz, hτk]
  have hd2 : d * d = 1 := by
    rw [hd_eq]
    exact Subtype.ext (centerIn_J_sq h (z_mem_centerIn_J h))
  have hcomY : comY yH k₀ = d := by
    unfold comY
    rw [hconj, mul_inv_rev, show d⁻¹ = d from inv_eq_of_mul_eq_one_right hd2]
    group
  change comY yH k₀ = ⟨z, z_mem_J h⟩
  rw [hcomY, hd_eq]

private noncomputable def hbPhi (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) :
    QuotientV.V z →* QuotientV.V z where
  toFun v := v * conjV h τ v
  map_one' := by simp
  map_mul' v w := by
    change v * w * conjV h τ (v * w) = (v * conjV h τ v) * (w * conjV h τ w)
    rw [map_mul]
    have hc : w * conjV h τ v = conjV h τ v * w :=
      (QuotientV.isMulCommutative_V h).is_comm.comm _ _
    calc v * w * (conjV h τ v * conjV h τ w)
        = v * (w * conjV h τ v) * conjV h τ w := by group
      _ = v * (conjV h τ v * w) * conjV h τ w := by rw [hc]
      _ = (v * conjV h τ v) * (w * conjV h τ w) := by group

private noncomputable def Vt (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) :
    Subgroup (QuotientV.V z) :=
  (hbPhi h τ).range

private noncomputable def R (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) : Subgroup (J z) :=
  (Vt h τ).comap (QuotientV.pi z)

private theorem pi_comY (h : Tim79a.ParrottHyp z) {τ yH : ↥(H z)}
    (hyHτ : conjV h yH = conjV h τ) (k : J z) :
    QuotientV.pi z (comY yH k) = hbPhi h τ (QuotientV.pi z k) := by
  have hp2 : QuotientV.pi z k * QuotientV.pi z k = 1 := by
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z k)
  have hinv : (conjV h τ (QuotientV.pi z k))⁻¹ = conjV h τ (QuotientV.pi z k) := by
    apply inv_eq_of_mul_eq_one_right
    calc conjV h τ (QuotientV.pi z k) * conjV h τ (QuotientV.pi z k)
        = conjV h τ (QuotientV.pi z k * QuotientV.pi z k) := by rw [map_mul]
      _ = conjV h τ 1 := by rw [hp2]
      _ = 1 := map_one _
  unfold comY hbPhi
  change QuotientV.pi z k * (QuotientV.pi z (conjJ' z yH k))⁻¹ =
    QuotientV.pi z k * conjV h τ (QuotientV.pi z k)
  rw [← conjV_mk h yH k, hyHτ, hinv]

private theorem mem_R_iff (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) (n : J z) :
    n ∈ R h τ ↔ ∃ m : V, hbadCoord h P (n : G) = m + ((rhoA tA : GL8) : Mat8) *ᵥ m := by
  constructor
  · intro hn
    obtain ⟨m, hm⟩ := Subgroup.mem_comap.mp hn
    obtain ⟨m', hm'⟩ := spinVecToV_surjective h P m
    refine ⟨m', ?_⟩
    apply spinVecToV_injective h P
    rw [show spinVecToV h P (hbadCoord h P (n : G)) = hbPhi h τ m from
      (hm.trans ((spinVecToV_hbadCoord h P (n).2).symm)).symm, ← hm']
    unfold hbPhi
    change spinVecToV h P m' * conjV h τ (spinVecToV h P m') =
      spinVecToV h P (m' + ((rhoA tA : GL8) : Mat8) *ᵥ m')
    rw [conjV_spinVecToV D h P hP, hqτ, ← spinVecToV_add]
  · rintro ⟨m, hm⟩
    refine Subgroup.mem_comap.mpr ⟨spinVecToV h P m, ?_⟩
    rw [show (QuotientV.pi z n) = spinVecToV h P (m + ((rhoA tA : GL8) : Mat8) *ᵥ m) by
      rw [← spinVecToV_hbadCoord h P n.2, hm]]
    unfold hbPhi
    change spinVecToV h P m * conjV h τ (spinVecToV h P m) =
      spinVecToV h P (m + ((rhoA tA : GL8) : Mat8) *ᵥ m)
    rw [conjV_spinVecToV D h P hP, hqτ, ← spinVecToV_add]

private noncomputable def Xset (yH : ↥(H z)) : Set (J z) :=
  Set.range (comY yH)

private def Xz1 (yH : ↥(H z)) (z₁ : G) : Set (J z) :=
  {j | ∃ x ∈ Xset (z := z) yH, (j : G) = (x : G) * z₁}

private theorem comY_mul_eq (yH : ↥(H z)) (k k' : J z) :
    comY yH (k * k') = (k * comY yH k' * k⁻¹) * comY yH k := by
  unfold comY
  rw [map_mul, mul_inv_rev]
  group

private theorem comY_conj_mem_zpowers (h : Tim79a.ParrottHyp z) (yH : ↥(H z))
    (k k' : J z) :
    ((k * comY yH k' * k⁻¹ * (comY yH k')⁻¹ : J z) : G) ∈ Subgroup.zpowers z := by
  have hmem := commutator_mem_zpowers_z (z := z) h k.2 (comY yH k').2
  have heq : ((k * comY yH k' * k⁻¹ * (comY yH k')⁻¹ : J z) : G) =
      ⁅(k : G), ((comY yH k' : J z) : G)⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, commutatorElement_def]
  rwa [heq]

private theorem one_mem_Xset (yH : ↥(H z)) : (1 : J z) ∈ Xset (z := z) yH :=
  ⟨1, by simp [comY]⟩

private theorem mul_z_mem_Xset (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {x : J z}
    (hx : x ∈ Xset (z := z) ⟨y, hyH⟩) :
    x * ⟨z, z_mem_J h⟩ ∈ Xset (z := z) ⟨y, hyH⟩ := by
  obtain ⟨k, rfl⟩ := hx
  have hzk : comY (⟨y, hyH⟩ : ↥(H z)) k₀ = ⟨z, z_mem_J h⟩ :=
    comY_chat_eq_z (z := z) D h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth
  have hzc : (k : J z) * ⟨z, z_mem_J h⟩ * k⁻¹ = ⟨z, z_mem_J h⟩ := by
    have hcomm : Commute (k : J z) ⟨z, z_mem_J h⟩ := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 (k : G) k.2
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hzcomm : Commute ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z)) ⟨z, z_mem_J h⟩ := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2
      ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) (comY _ k).2
  refine ⟨k * k₀, ?_⟩
  rw [comY_mul_eq, hzk, hzc]
  exact hzcomm.eq.symm

private theorem zpowers_mul_mem_Xset (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {ζ x : J z}
    (hζ : (ζ : G) ∈ Subgroup.zpowers z) (hx : x ∈ Xset (z := z) ⟨y, hyH⟩) :
    ζ * x ∈ Xset (z := z) ⟨y, hyH⟩ := by
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hζ with h1 | h1
  · have hζ1 : ζ = 1 := Subtype.ext h1
    rw [hζ1, one_mul]
    exact hx
  · have hζz : ζ = ⟨z, z_mem_J h⟩ := Subtype.ext h1
    rw [hζz]
    have hzx : (⟨z, z_mem_J h⟩ : J z) * x = x * ⟨z, z_mem_J h⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 (x : G) x.2).symm
    rw [hzx]
    exact mul_z_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hx

private theorem mul_mem_Xset (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {x x' : J z}
    (hx : x ∈ Xset (z := z) ⟨y, hyH⟩) (hx' : x' ∈ Xset (z := z) ⟨y, hyH⟩) :
    x * x' ∈ Xset (z := z) ⟨y, hyH⟩ := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨k', rfl⟩ := hx'
  let c : J z := comY (⟨y, hyH⟩ : ↥(H z)) k
  let c' : J z := comY (⟨y, hyH⟩ : ↥(H z)) k'
  let ζ1 : J z := k * c' * k⁻¹ * c'⁻¹
  let ζ2 : J z := c * c' * c⁻¹ * c'⁻¹
  have hζ1 : (ζ1 : G) ∈ Subgroup.zpowers z :=
    comY_conj_mem_zpowers (z := z) h ⟨y, hyH⟩ k k'
  have hζ2 : (ζ2 : G) ∈ Subgroup.zpowers z := by
    have h := commutator_mem_zpowers_z (z := z) h c.2 c'.2
    simpa only [ζ2, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using h
  have hζ1eq : (k : J z) * c' * k⁻¹ = ζ1 * c' := by
    dsimp only [ζ1]
    group
  have hζ2eq : c * c' = ζ2 * (c' * c) := by
    dsimp only [ζ2]
    group
  have hζ1sq : ζ1 * ζ1 = 1 := by
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hζ1 with h1 | h1
    · have hζ1' : ζ1 = 1 := Subtype.ext h1
      rw [hζ1']
      exact one_mul _
    · have hζ1' : ζ1 = ⟨z, z_mem_J h⟩ := Subtype.ext h1
      rw [hζ1']
      exact Subtype.ext (centerIn_J_sq h (z_mem_centerIn_J h))
  have hCeq : comY (⟨y, hyH⟩ : ↥(H z)) (k * k') = ζ1 * (c' * c) := by
    rw [comY_mul_eq, hζ1eq]
    dsimp only [c]
    group
  have hc'c : c' * c = ζ1 * comY (⟨y, hyH⟩ : ↥(H z)) (k * k') := by
    calc c' * c = ζ1 * (ζ1 * (c' * c)) := by rw [← mul_assoc, hζ1sq, one_mul]
      _ = ζ1 * comY (⟨y, hyH⟩ : ↥(H z)) (k * k') := by rw [← hCeq]
  have hfin : (c * c' : J z) = ζ2 * (ζ1 * comY (⟨y, hyH⟩ : ↥(H z)) (k * k')) := by
    rw [hζ2eq, hc'c]
  have hstart : comY (⟨y, hyH⟩ : ↥(H z)) (k * k') ∈ Xset (z := z) ⟨y, hyH⟩ :=
    ⟨k * k', rfl⟩
  have h1 : ζ1 * comY (⟨y, hyH⟩ : ↥(H z)) (k * k') ∈ Xset (z := z) ⟨y, hyH⟩ :=
    zpowers_mul_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hζ1 hstart
  have h2 : ζ2 * (ζ1 * comY (⟨y, hyH⟩ : ↥(H z)) (k * k')) ∈
      Xset (z := z) ⟨y, hyH⟩ :=
    zpowers_mul_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hζ2 h1
  rw [hfin]
  exact h2
private theorem Xset_pow_mem (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {x : J z}
    (hx : x ∈ Xset (z := z) ⟨y, hyH⟩) (n : ℕ) :
    x ^ n ∈ Xset (z := z) ⟨y, hyH⟩ := by
  induction n with
  | zero => simpa using one_mem_Xset (z := z) (⟨y, hyH⟩ : ↥(H z))
  | succ n ih =>
      rw [pow_succ]
      exact mul_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth ih hx

private noncomputable def Xsub (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) : Subgroup (J z) where
  carrier := Xset (z := z) ⟨y, hyH⟩
  one_mem' := one_mem_Xset (z := z) (⟨y, hyH⟩ : ↥(H z))
  mul_mem' := mul_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth
  inv_mem' := by
    intro x hx
    have h1 : 1 ≤ orderOf x := Nat.one_le_iff_ne_zero.mpr (orderOf_pos x).ne'
    have hpow : x ^ (orderOf x - 1) ∈ Xset (z := z) ⟨y, hyH⟩ :=
      Xset_pow_mem (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hx _
    have hmul : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel h1, pow_orderOf_eq_one]
    have hxinv : x⁻¹ = x ^ (orderOf x - 1) := inv_eq_of_mul_eq_one_left hmul
    rwa [hxinv]

private theorem Xset_subset_R (h : Tim79a.ParrottHyp z) {τ yH : ↥(H z)}
    (hyHτ : conjV h yH = conjV h τ) :
    Xset (z := z) yH ⊆ (R h τ : Set (J z)) := by
  rintro x ⟨k, rfl⟩
  exact Subgroup.mem_comap.mpr
    (MonoidHom.mem_range.mpr ⟨QuotientV.pi z k, (pi_comY (z := z) h hyHτ k).symm⟩)
private theorem z_mul_eq_mul_z (h : Tim79a.ParrottHyp z) (x : J z) :
    (⟨z, z_mem_J h⟩ : J z) * x = x * ⟨z, z_mem_J h⟩ := by
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 (x : G) x.2).symm

private theorem R_subset_X_union (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {r : J z} (hr : r ∈ R h τ) :
    r ∈ Xset (z := z) ⟨y, hyH⟩ ∨ r ∈ Xz1 (z := z) ⟨y, hyH⟩ z₁ := by
  classical
  have hyHτ : conjV h (⟨y, hyH⟩ : ↥(H z)) = conjV h τ := by
    rw [show (⟨y, hyH⟩ : ↥(H z)) = τ * hbToH (z := z) j from Subtype.ext hyj,
      map_mul, conjV_toH_eq_one, mul_one]
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hr)
  obtain ⟨k, hk⟩ := QuotientV.pi_surjective z v
  have hcom : QuotientV.pi z (comY (⟨y, hyH⟩ : ↥(H z)) k) = QuotientV.pi z r := by
    rw [pi_comY (z := z) h hyHτ k, hk, hv]
  let ζ : J z := r * (comY (⟨y, hyH⟩ : ↥(H z)) k)⁻¹
  have hζπ : QuotientV.pi z ζ = 1 := by unfold ζ; rw [map_mul, map_inv, hcom, mul_inv_cancel]
  have hζcenter : (ζ : G) ∈ centerIn (J z) := by
    refine (hbadCoord_eq_zero_iff h P ζ.2).mp ?_
    apply spinVecToV_injective h P
    rw [spinVecToV_hbadCoord h P ζ.2, hζπ, spinVecToV_zero]
  have hrζ : r = ζ * comY (⟨y, hyH⟩ : ↥(H z)) k := by unfold ζ; group
  have hz1c : ∀ x : J z, (⟨z₁, hz₁.1⟩ : J z) * x = x * ⟨z₁, hz₁.1⟩ := by
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hz₁.2 (x : G) x.2).symm
  have hXk : comY (⟨y, hyH⟩ : ↥(H z)) k ∈ Xset (z := z) ⟨y, hyH⟩ := ⟨k, rfl⟩
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hζcenter with h1 | h1 | h1 | h1
  · left
    have hζ1 : ζ = 1 := Subtype.ext h1
    rw [hrζ, hζ1, one_mul]; exact hXk
  · left
    have hζz : ζ = ⟨z, z_mem_J h⟩ := Subtype.ext h1
    rw [hrζ, hζz, z_mul_eq_mul_z (z := z) h]
    exact mul_z_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hXk
  · right
    refine ⟨comY (⟨y, hyH⟩ : ↥(H z)) k, hXk, ?_⟩
    have hζz : ζ = ⟨z₁, hz₁.1⟩ := Subtype.ext h1
    rw [hrζ, hζz, hz1c]
    simp only [Subgroup.coe_mul]
  · right
    have hζz : ζ = ⟨z * z₁, (J z).mul_mem (z_mem_J h) hz₁.1⟩ := Subtype.ext h1
    refine ⟨comY (⟨y, hyH⟩ : ↥(H z)) k * ⟨z, z_mem_J h⟩,
      mul_z_mem_Xset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth hXk, ?_⟩
    rw [hrζ, hζz]
    simp only [Subgroup.coe_mul]
    have hzc : (z : G) * ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) =
        ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) * z :=
      congrArg Subtype.val (z_mul_eq_mul_z (z := z) h (comY (⟨y, hyH⟩ : ↥(H z)) k))
    have hz1cG : z₁ * ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) =
        ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) * z₁ :=
      congrArg Subtype.val (hz1c (comY (⟨y, hyH⟩ : ↥(H z)) k))
    calc (z : G) * z₁ * ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G)
        = (z : G) * (((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) * z₁) := by
          rw [mul_assoc, hz1cG]
      _ = ((comY (⟨y, hyH⟩ : ↥(H z)) k : J z) : G) * z * z₁ := by rw [← mul_assoc, hzc]
private theorem card_R_le_two_mul_card_X (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card ↥(R h τ) ≤
      2 * Nat.card ↥(Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth) := by
  classical
  let X : Subgroup (J z) := Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth
  have hcover : ∀ r : ↥(R h τ), (r : J z) ∈ Xset (z := z) ⟨y, hyH⟩ ∨
      (r : J z) ∈ Xz1 (z := z) ⟨y, hyH⟩ z₁ :=
    fun r => R_subset_X_union (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj
      hk₀ horth hz₁ hz₁z hord r.2
  let f : ↥(R h τ) → ↥X × Bool := fun r =>
    if hx : (r : J z) ∈ Xset (z := z) ⟨y, hyH⟩ then
      (⟨(r : J z), hx⟩, true)
    else
      (⟨Classical.choose ((hcover r).resolve_left hx),
        (Classical.choose_spec ((hcover r).resolve_left hx)).1⟩, false)
  have hf : Function.Injective f := by
    intro r1 r2 h12
    by_cases hx1 : (r1 : J z) ∈ Xset (z := z) ⟨y, hyH⟩
    · by_cases hx2 : (r2 : J z) ∈ Xset (z := z) ⟨y, hyH⟩
      · simp only [f, dif_pos hx1, dif_pos hx2] at h12
        exact Subtype.ext (congrArg (fun x : ↥X => (x : J z)) (Prod.mk.inj h12).1)
      · simp only [f, dif_pos hx1, dif_neg hx2] at h12
        exact absurd (Prod.mk.inj h12).2 (by simp)
    · by_cases hx2 : (r2 : J z) ∈ Xset (z := z) ⟨y, hyH⟩
      · simp only [f, dif_neg hx1, dif_pos hx2] at h12
        exact absurd (Prod.mk.inj h12).2 (by simp)
      · simp only [f, dif_neg hx1, dif_neg hx2] at h12
        have hval : Classical.choose ((hcover r1).resolve_left hx1) =
            Classical.choose ((hcover r2).resolve_left hx2) :=
          congrArg Subtype.val (Prod.mk.inj h12).1
        have hr1 : (r1 : J z) = Classical.choose ((hcover r1).resolve_left hx1) *
            ⟨z₁, hz₁.1⟩ :=
          Subtype.ext ((Classical.choose_spec ((hcover r1).resolve_left hx1)).2)
        have hr2 : (r2 : J z) = Classical.choose ((hcover r2).resolve_left hx2) *
            ⟨z₁, hz₁.1⟩ :=
          Subtype.ext ((Classical.choose_spec ((hcover r2).resolve_left hx2)).2)
        apply Subtype.ext
        rw [hr1, hr2, hval]
  calc Nat.card ↥(R h τ) ≤ Nat.card (↥X × Bool) := Nat.card_le_card_of_injective f hf
    _ = Nat.card ↥X * Nat.card Bool := Nat.card_prod _ _
    _ = Nat.card ↥X * 2 := by rw [show Nat.card Bool = 2 from by
          rw [Nat.card_eq_fintype_card]; decide]
    _ = 2 * Nat.card ↥X := Nat.mul_comm _ _

private noncomputable def NJ (B : Subgroup G) : Subgroup (J z) :=
  B.comap (J z).subtype

private theorem mem_NJ {B : Subgroup G} {x : J z} : x ∈ NJ (z := z) B ↔ (x : G) ∈ B :=
  Iff.rfl

private noncomputable def N0 (B : Subgroup G) (h : Tim79a.ParrottHyp z) (τ : ↥(H z)) :
    Subgroup (J z) :=
  NJ (z := z) B ⊓ R h τ

private theorem NJ_inf_Xsub_eq_bot (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) (B : Subgroup G)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    NJ (z := z) B ⊓ Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxN, hxX⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := hxX
  have hxB : (x : G) ∈ B := hxN
  have hxy : (x : G) * y = (k : G) * y * (k : G)⁻¹ := by
    rw [← hk]
    exact comY_mul_y (z := z) (⟨y, hyH⟩ : ↥(H z)) (k := k) rfl
  have hmem : (k : G) * y * (k : G)⁻¹ ∈ B := by
    rw [← hxy]
    exact B.mul_mem hxB hyB
  by_contra hxne
  apply hno
  refine ⟨(k : G), k.2, hmem, ?_⟩
  intro heq
  apply hxne
  apply Subtype.ext
  calc (x : G) = (x : G) * (y * y) := by rw [hy2, mul_one]
    _ = ((x : G) * y) * y := by group
    _ = ((k : G) * y * (k : G)⁻¹) * y := by rw [hxy]
    _ = y * y := by rw [heq]
    _ = 1 := hy2

private theorem card_N0_mul_card_X_le (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) (B : Subgroup G)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    Nat.card ↥(N0 (z := z) B h τ) *
      Nat.card ↥(Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth) ≤
      Nat.card ↥(R h τ) := by
  classical
  have hyHτ : conjV h (⟨y, hyH⟩ : ↥(H z)) = conjV h τ := by
    rw [show (⟨y, hyH⟩ : ↥(H z)) = τ * hbToH (z := z) j from Subtype.ext hyj,
      map_mul, conjV_toH_eq_one, mul_one]
  let X : Subgroup (J z) := Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hyj hk₀ horth
  have hbot : NJ (z := z) B ⊓ X = ⊥ :=
    NJ_inf_Xsub_eq_bot (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
      hk₀ horth B hyB hzB hno
  let f : ↥(N0 (z := z) B h τ) × ↥X → ↥(R h τ) := fun p =>
    ⟨(p.1 : J z) * (p.2 : J z),
      (R h τ).mul_mem (Subgroup.mem_inf.mp p.1.2).2
        (Xset_subset_R (z := z) h hyHτ p.2.2)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hEq : (p.1 : J z) * (p.2 : J z) = (q.1 : J z) * (q.2 : J z) :=
      congrArg Subtype.val hpq
    have heq : (p.1 : J z)⁻¹ * (q.1 : J z) = (p.2 : J z) * (q.2 : J z)⁻¹ := by
      calc (p.1 : J z)⁻¹ * (q.1 : J z)
          = (p.1 : J z)⁻¹ * ((q.1 : J z) * (q.2 : J z)) * (q.2 : J z)⁻¹ := by group
        _ = (p.1 : J z)⁻¹ * ((p.1 : J z) * (p.2 : J z)) * (q.2 : J z)⁻¹ := by rw [← hEq]
        _ = (p.2 : J z) * (q.2 : J z)⁻¹ := by group
    have hmemN : (p.1 : J z)⁻¹ * (q.1 : J z) ∈ (N0 (z := z) B h τ) :=
      (N0 (z := z) B h τ).mul_mem ((N0 (z := z) B h τ).inv_mem p.1.2) q.1.2
    have hmemX : (p.2 : J z) * (q.2 : J z)⁻¹ ∈ X :=
      X.mul_mem p.2.2 (X.inv_mem q.2.2)
    have hmem : (p.1 : J z)⁻¹ * (q.1 : J z) ∈ (⊥ : Subgroup (J z)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hmemN).1, heq ▸ hmemX⟩
    have h1 : (p.1 : J z)⁻¹ * (q.1 : J z) = 1 := by simpa using hmem
    have hp1 : p.1 = q.1 := by
      apply Subtype.ext
      have hq : (q.1 : J z) = (p.1 : J z) := by
        calc (q.1 : J z) = ((p.1 : J z) * (p.1 : J z)⁻¹) * (q.1 : J z) := by group
          _ = (p.1 : J z) * ((p.1 : J z)⁻¹ * (q.1 : J z)) := by group
          _ = (p.1 : J z) * 1 := by rw [h1]
          _ = (p.1 : J z) := mul_one _
      exact hq.symm
    have hp2 : p.2 = q.2 := by
      apply Subtype.ext
      have h2 : (p.2 : J z) * (q.2 : J z)⁻¹ = 1 := by
        rw [← heq, hp1, inv_mul_cancel]
      calc (p.2 : J z) = ((p.2 : J z) * (q.2 : J z)⁻¹) * (q.2 : J z) := by group
        _ = 1 * (q.2 : J z) := by rw [h2]
        _ = (q.2 : J z) := one_mul _
    exact Prod.ext hp1 hp2
  calc Nat.card ↥(N0 (z := z) B h τ) * Nat.card ↥X
      = Nat.card (↥(N0 (z := z) B h τ) × ↥X) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card ↥(R h τ) := Nat.card_le_card_of_injective f hf

private theorem NJ_commute_of_mem_CJy (h : Tim79a.ParrottHyp z) (B : Subgroup G)
    {y : G}
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyH : y ∈ H z) (hzB : z ∉ B) {n : J z} (hn : (n : G) ∈ B) {c : J z}
    (hcy : (c : G) ∈ Subgroup.centralizer ({y} : Set G)) :
    Commute (n : G) (c : G) := by
  have hc' : (c : G) ∈ H z ⊓ centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨J_le_H (z := z) c.2, hcy⟩
  have h1 : (c : G) * (n : G)⁻¹ * (c : G)⁻¹ ∈ B := hBn (c : G) hc' (n : G)⁻¹ (B.inv_mem hn)
  have hζB : ((n : J z) * c * (n : J z)⁻¹ * c⁻¹ : J z) ∈ NJ (z := z) B := by
    rw [mem_NJ]
    have : ((n * c * n⁻¹ * c⁻¹ : J z) : G) = (n : G) * ((c : G) * (n : G)⁻¹ * (c : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact B.mul_mem hn h1
  have hζzp : ((((n : J z) * c * (n : J z)⁻¹ * c⁻¹ : J z) : G)) ∈ Subgroup.zpowers z := by
    have h := commutator_mem_zpowers_z (z := z) h n.2 c.2
    have heq : (((n * c * n⁻¹ * c⁻¹ : J z) : G)) = ⁅(n : G), (c : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rwa [heq]
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hζzp with h1' | h1'
  · have hζ1 : (n : J z) * c * (n : J z)⁻¹ * c⁻¹ = 1 := Subtype.ext h1'
    have hcomm : (n : G) * (c : G) = (c : G) * (n : G) := by
      have hc := congrArg Subtype.val hζ1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at hc
      calc (n : G) * (c : G) = ((n : G) * (c : G) * (n : G)⁻¹ * (c : G)⁻¹) * (c : G) * (n : G) := by
            group
        _ = 1 * (c : G) * (n : G) := by rw [hc]
        _ = (c : G) * (n : G) := by group
    exact hcomm
  · exfalso
    apply hzB
    have hζz : ((n : J z) * c * (n : J z)⁻¹ * c⁻¹ : J z) = ⟨z, z_mem_J h⟩ := Subtype.ext h1'
    have hζzG : (((n : J z) * c * (n : J z)⁻¹ * c⁻¹ : J z) : G) = z := congrArg Subtype.val hζz
    rw [← hζzG]
    exact (mem_NJ.mp hζB)

private theorem NJ_mem_Qbar (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (B : Subgroup G)
    (hBC : B ≤ H z ⊓ centralizer ({y} : Set G)) {n : J z} (hn : (n : G) ∈ B) :
    QuotientV.pi z n ∈ Qbar h P τ (hbadCoord h P (j : G)) :=
  mem_Qbar_of_mem_centralizer (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
    (Subgroup.mem_inf.mpr ⟨n.2, (Subgroup.mem_inf.mp (hBC hn)).2⟩)

private theorem NJ_coord_dichotomy (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (B : Subgroup G)
    (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hzB : z ∉ B) (hwj : IsFixedT (z := z) h P j) {n : J z} (hn : (n : G) ∈ B) :
    (∃ m : V, hbadCoord h P (n : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) ∨
      (∃ m : V, hbadCoord h P (n : G) = hbadCoord h P (j : G) +
        (((rhoA tA : GL8) : Mat8) *ᵥ m + m)) := by
  have hq := NJ_mem_Qbar (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj B hBC hn
  have hfixV : QuotientV.pi z n ∈ Vfix h τ := (Subgroup.mem_inf.mp hq).1
  have hfix : IsFixedT (z := z) h P n :=
    (mem_Chat_iff (z := z) D h P hP hqτ).mp (Subgroup.mem_comap.mpr hfixV)
  have hperp : ∀ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k →
      b (hbadCoord h P (j : G)) k = 0 → b (hbadCoord h P (n : G)) k = 0 := by
    intro k hk hbk
    obtain ⟨c, hc⟩ := QuotientV.pi_surjective z (spinVecToV h P k)
    have hcQ : QuotientV.pi z c ∈ Qbar h P τ (hbadCoord h P (j : G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hc]
        change conjV h τ (spinVecToV h P k) = spinVecToV h P k
        rw [conjV_spinVecToV D h P hP, hqτ, hk]
      · rw [hc]
        change polarVZMod h (spinVecToV h P (hbadCoord h P (j : G))) (spinVecToV h P k) = 0
        rw [polarVZMod_spinVecToV_eq_b D h P hP]
        exact hbk
    have hcCJy : c ∈ CJy h P τ (hbadCoord h P (j : G)) := Subgroup.mem_comap.mpr hcQ
    have hcy : (c : G) ∈ Subgroup.centralizer ({y} : Set G) :=
      (Subgroup.mem_inf.mp ((mem_CJy_iff (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
        hyH hy2 hyj c).mp hcCJy)).2
    have hcomm : Commute (n : G) (c : G) :=
      NJ_commute_of_mem_CJy (z := z) h B hBn hyH hzB hn hcy
    have hb0 : b (hbadCoord h P (n : G)) (hbadCoord h P (c : G)) = 0 :=
      (commute_iff_hbadCoord D h P hP n.2 c.2).mp hcomm
    have hck : hbadCoord h P (c : G) = k := by
      apply spinVecToV_injective h P
      rw [spinVecToV_hbadCoord h P c.2]
      exact hc
    have h1 : b (hbadCoord h P (n : G)) k = 0 := by
      rwa [hck] at hb0
    exact h1
  obtain ⟨m, hm | hm⟩ :=
    spin_exists_of_perp_fixed_t_perp (hbadCoord h P (j : G)) hwj (hbadCoord h P (n : G)) hfix hperp
  · exact Or.inl ⟨m, hm⟩
  · exact Or.inr ⟨m, hm⟩

private theorem card_N0_le_two (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0) (B : Subgroup G)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card ↥(N0 (z := z) B h τ) ≤ 2 := by
  have h1 := card_N0_mul_card_X_le (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
    hyH hy2 hyj hk₀ horth B hyB hzB hno
  have h2 := card_R_le_two_mul_card_X (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
    hyH hyj hk₀ horth hz₁ hz₁z hord
  haveI : Nonempty ↥(Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
      hyH hyj hk₀ horth) := ⟨⟨1, one_mem_Xset (z := z) (⟨y, hyH⟩ : ↥(H z))⟩⟩
  have hpos : 0 < Nat.card ↥(Xsub (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
      hyH hyj hk₀ horth) := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (h1.trans h2) hpos

private theorem hbadCoord_mul_inv (h : Tim79a.ParrottHyp z) (P : GL8) (a b : J z) :
    hbadCoord h P ((a * b⁻¹ : J z) : G) = hbadCoord h P (a : G) + hbadCoord h P (b : G) := by
  rw [show ((a * b⁻¹ : J z) : G) = (a : G) * ((b⁻¹ : J z) : G) from rfl,
    hbadCoord_mul h P a.2 (b⁻¹).2]
  have hinv : hbadCoord h P (((b⁻¹ : J z) : G)) = hbadCoord h P (b : G) := by
    rw [Subgroup.coe_inv, hbadCoord_inv h P b.2]
  rw [hinv]

private theorem mem_N0_of_second (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) {j : J z} {B : Subgroup G}
    {a b : J z} (ha : a ∈ NJ (z := z) B) (hb : b ∈ NJ (z := z) B)
    (ha2 : ∃ m : V, hbadCoord h P (a : G) = hbadCoord h P (j : G) +
      (((rhoA tA : GL8) : Mat8) *ᵥ m + m))
    (hb2 : ∃ m : V, hbadCoord h P (b : G) = hbadCoord h P (j : G) +
      (((rhoA tA : GL8) : Mat8) *ᵥ m + m)) :
    a * b⁻¹ ∈ N0 (z := z) B h τ := by
  obtain ⟨m, hm⟩ := ha2
  obtain ⟨m', hm'⟩ := hb2
  refine Subgroup.mem_inf.mpr ⟨(NJ (z := z) B).mul_mem ha ((NJ (z := z) B).inv_mem hb), ?_⟩
  refine (mem_R_iff (z := z) D h P hP hqτ (a * b⁻¹)).mpr ⟨m + m', ?_⟩
  change hbadCoord h P ((a * b⁻¹ : J z) : G) =
    m + m' + ((rhoA tA : GL8) : Mat8) *ᵥ (m + m')
  rw [hbadCoord_mul_inv h P a b, hm, hm', Matrix.mulVec_add]
  have hself : hbadCoord h P (j : G) + hbadCoord h P (j : G) = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  abel_nf
  rw [two_smul, hself, zero_add]

private theorem N0_pair (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) {k₀ : J z}
    (hk₀ : k₀ ∈ Chat h τ) (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hne : N0 (z := z) B h τ ≠ ⊥) :
    ∃ n₀ : J z, n₀ ∈ N0 (z := z) B h τ ∧ n₀ ≠ 1 ∧
      ∀ n ∈ N0 (z := z) B h τ, n = 1 ∨ n = n₀ := by
  have hN0card : Nat.card ↥(N0 (z := z) B h τ) ≤ 2 :=
    card_N0_le_two (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
      hk₀ horth B hyB hzB hno hz₁ hz₁z hord
  haveI : Nontrivial ↥(N0 (z := z) B h τ) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n₀, hn₀, hn₀ne⟩ := Subgroup.exists_ne_one_of_nontrivial (N0 (z := z) B h τ)
  refine ⟨n₀, hn₀, hn₀ne, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · exact Or.inl hn1
  · right
    by_contra hne'
    haveI : Fintype ↥(N0 (z := z) B h τ) := Fintype.ofFinite _
    let g : Fin 3 → ↥(N0 (z := z) B h τ) := fun i =>
      if i = 0 then ⟨1, (N0 (z := z) B h τ).one_mem⟩
      else if i = 1 then ⟨n₀, hn₀⟩ else ⟨n, hn⟩
    have hg : Function.Injective g := by
      intro i k hik
      fin_cases i <;> fin_cases k <;> simp_all [g]
    have hle := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin] at hle
    have hc : Fintype.card ↥(N0 (z := z) B h τ) ≤ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hN0card
    omega

private theorem exists_ell_N0 (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1)
    {j : J z} (hyj : y = (τ : G) * (j : G)) {k₀ : J z}
    (hk₀ : k₀ ∈ Chat h τ) (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    ∃ ℓ : V, (∃ m : V, ℓ = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) ∧
      ∀ n ∈ N0 (z := z) B h τ, hbadCoord h P (n : G) = 0 ∨ hbadCoord h P (n : G) = ℓ := by
  by_cases hbot : N0 (z := z) B h τ = ⊥
  · refine ⟨0, ⟨0, by simp⟩, ?_⟩
    intro n hn
    left
    have hn1 : n = 1 := (Subgroup.eq_bot_iff_forall _).mp hbot n hn
    rw [hn1]
    exact (hbadCoord_eq_zero_iff h P (Subgroup.one_mem (J z))).mpr
      (Subgroup.one_mem (centerIn (J z)))
  · obtain ⟨n₀, hn₀, hn₀ne, hpair⟩ :=
      N0_pair (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj hk₀ horth
        B hyB hzB hno hz₁ hz₁z hord hbot
    refine ⟨hbadCoord h P (n₀ : G), ?_, ?_⟩
    · have hn₀R : n₀ ∈ R h τ := (Subgroup.mem_inf.mp hn₀).2
      obtain ⟨m, hm⟩ := (mem_R_iff (z := z) D h P hP hqτ n₀).mp hn₀R
      exact ⟨m, by rw [hm, add_comm]⟩
    · intro n hn
      rcases hpair n hn with rfl | rfl
      · left
        exact (hbadCoord_eq_zero_iff h P (Subgroup.one_mem (J z))).mpr
          (Subgroup.one_mem (centerIn (J z)))
      · right; rfl

private theorem NJ_coord_second (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (hwj : IsFixedT (z := z) h P j) {k₀ : J z}
    (hk₀ : k₀ ∈ Chat h τ) (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {n : J z} (hn : n ∈ NJ (z := z) B) (hn0 : n ∉ N0 (z := z) B h τ) :
    ∃ m : V, hbadCoord h P (n : G) = hbadCoord h P (j : G) +
      (((rhoA tA : GL8) : Mat8) *ᵥ m + m) := by
  rcases NJ_coord_dichotomy (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
    hyj B hBC hBn hzB hwj hn with hcase | hcase
  · exfalso
    apply hn0
    refine Subgroup.mem_inf.mpr ⟨hn, ?_⟩
    exact (mem_R_iff (z := z) D h P hP hqτ n).mpr (by
      obtain ⟨m, hm⟩ := hcase
      exact ⟨m, by rw [hm, add_comm]⟩)
  · exact hcase

private theorem exists_ell_j1_coord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (hwj : IsFixedT (z := z) h P j) {k₀ : J z}
    (hk₀ : k₀ ∈ Chat h τ) (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    ∃ ℓ j₁ : V,
      (∃ m : V, ℓ = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) ∧
      (∃ m : V, j₁ = hbadCoord h P (j : G) + (((rhoA tA : GL8) : Mat8) *ᵥ m + m)) ∧
      ∀ n : J z, n ∈ NJ (z := z) B →
        hbadCoord h P (n : G) = 0 ∨ hbadCoord h P (n : G) = ℓ ∨
          hbadCoord h P (n : G) = j₁ ∨ hbadCoord h P (n : G) = j₁ + ℓ := by
  classical
  obtain ⟨ℓ, hℓ, hN0desc⟩ :=
    exists_ell_N0 (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
      (j := j) hk₀ horth B hyB hzB hno hz₁ hz₁z hord
  by_cases hN1 : ∃ n₁ : J z, n₁ ∈ NJ (z := z) B ∧ n₁ ∉ N0 (z := z) B h τ
  · obtain ⟨n₁, hn₁N, hn₁0⟩ := hN1
    refine ⟨ℓ, hbadCoord h P (n₁ : G), hℓ, ?_, ?_⟩
    · exact NJ_coord_second (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
        hyj hwj hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord hn₁N hn₁0
    · intro n hn
      by_cases hn0 : n ∈ N0 (z := z) B h τ
      · rcases hN0desc n hn0 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hquot : n * n₁⁻¹ ∈ N0 (z := z) B h τ :=
          mem_N0_of_second (z := z) (D := D) h P hP hqτ hn hn₁N
            (NJ_coord_second (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
              hyj hwj hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord hn hn0)
            (NJ_coord_second (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
              hyj hwj hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord hn₁N hn₁0)
        have hself : hbadCoord h P (n₁ : G) + hbadCoord h P (n₁ : G) = 0 := by
          ext i
          simp only [Pi.add_apply, Pi.zero_apply]
          rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
        have hrev : hbadCoord h P (n : G) =
            hbadCoord h P ((n * n₁⁻¹) : G) + hbadCoord h P (n₁ : G) := by
          change hbadCoord h P (n : G) =
            hbadCoord h P ((n * n₁⁻¹ : J z) : G) + hbadCoord h P (n₁ : G)
          rw [hbadCoord_mul_inv h P n n₁, add_assoc, hself, add_zero]
        rcases hN0desc _ hquot with hq | hq
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [hrev]
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv, zero_add] using
            congrArg (fun t => t + hbadCoord h P (n₁ : G)) hq
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [hrev]
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv, zero_add, add_comm] using
            congrArg (fun t => t + hbadCoord h P (n₁ : G)) hq
  · refine ⟨ℓ, hbadCoord h P (j : G), hℓ, ⟨0, by simp⟩, ?_⟩
    intro n hn
    have hn0 : n ∈ N0 (z := z) B h τ := by
      by_contra hc
      exact hN1 ⟨n, hn, hc⟩
    rcases hN0desc n hn0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem NJ_commutator_coord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (B : Subgroup G)
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    {bH : ↥(H z)} (hbB : (bH : G) ∈ B) {c : J z}
    (hcQ : QuotientV.pi z c ∈ Qbar h P τ (hbadCoord h P (j : G))) :
    conjJ' z bH c * c⁻¹ ∈ NJ (z := z) B ∧
      hbadCoord h P ((conjJ' z bH c * c⁻¹) : G) =
        ((rhoA (qH (z := z) D bH) : GL8) : Mat8) *ᵥ hbadCoord h P (c : G) +
          hbadCoord h P (c : G) := by
  have hcCJy : c ∈ CJy h P τ (hbadCoord h P (j : G)) := Subgroup.mem_comap.mpr hcQ
  have hcy : (c : G) ∈ Subgroup.centralizer ({y} : Set G) :=
    (Subgroup.mem_inf.mp ((mem_CJy_iff (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
      hyH hy2 hyj c).mp hcCJy)).2
  have hcH : (c : G) ∈ H z := J_le_H (z := z) c.2
  have hcHy : (c : G) ∈ H z ⊓ centralizer ({y} : Set G) := Subgroup.mem_inf.mpr ⟨hcH, hcy⟩
  have h1 : (c : G) * (bH : G)⁻¹ * (c : G)⁻¹ ∈ B :=
    hBn (c : G) hcHy (bH : G)⁻¹ (B.inv_mem hbB)
  have heB : ((conjJ' z bH c * c⁻¹ : J z) : G) ∈ B := by
    have heq : ((conjJ' z bH c * c⁻¹ : J z) : G) =
        (bH : G) * ((c : G) * (bH : G)⁻¹ * (c : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conjJ'_apply_coe]
      group
    rw [heq]
    exact B.mul_mem hbB h1
  refine ⟨mem_NJ.mpr heB, ?_⟩
  change hbadCoord h P (((conjJ' z bH c) * c⁻¹ : J z) : G) =
    ((rhoA (qH (z := z) D bH) : GL8) : Mat8) *ᵥ hbadCoord h P (c : G) + hbadCoord h P (c : G)
  rw [hbadCoord_mul_inv h P (conjJ' z bH c) c]
  rw [show hbadCoord h P ((conjJ' z bH c : J z) : G) =
      ((rhoA (qH (z := z) D bH) : GL8) : Mat8) *ᵥ hbadCoord h P (c : G) from by
    rw [conjJ'_apply_coe]
    exact hbadCoord_conj D h P hP bH.2 c.2]

private noncomputable def qHB (B : Subgroup G) : Subgroup A45 :=
  (B.subgroupOf (H z)).map (qH (z := z) D)

private def Mset (wj ℓ j₁ : V) : Set A45 :=
  {a | a * tA = tA * a ∧ ∀ k : V,
    ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b wj k = 0 →
      ((rhoA a : GL8) : Mat8) *ᵥ k + k ∈ ({0, ℓ, j₁, j₁ + ℓ} : Set V)}

private theorem qHB_mem_Mset (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1)
    (hqy : qH (z := z) D ⟨y, hyH⟩ = tA) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (B : Subgroup G)
    (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    {ℓ j₁ : V} (hcov : ∀ n : J z, n ∈ NJ (z := z) B →
      hbadCoord h P (n : G) = 0 ∨ hbadCoord h P (n : G) = ℓ ∨
        hbadCoord h P (n : G) = j₁ ∨ hbadCoord h P (n : G) = j₁ + ℓ) :
    ∀ x : ↥(qHB (z := z) D B), (x : A45) ∈ Mset (hbadCoord h P (j : G)) ℓ j₁ := by
  intro x
  obtain ⟨bH, hbHmem, hq⟩ := Subgroup.mem_map.mp x.2
  have hbB : (bH : G) ∈ B := Subgroup.mem_subgroupOf.mp hbHmem
  have hbC : (bH : G) ∈ H z ⊓ centralizer ({y} : Set G) := hBC hbB
  have hby : (bH : G) * y = y * (bH : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hbC.2
  have hconjH : (bH : G) * y * (bH : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem bH.2 hyH) ((H z).inv_mem bH.2)
  have hqconj : qH (z := z) D ⟨(bH : G) * y * (bH : G)⁻¹, hconjH⟩ = tA := by
    have heq2 : (bH : G) * y * (bH : G)⁻¹ = y := by rw [hby]; group
    rw [show (⟨(bH : G) * y * (bH : G)⁻¹, hconjH⟩ : ↥(H z)) = ⟨y, hyH⟩ from
      Subtype.ext heq2, hqy]
  have hxconj : (x : A45) * tA * (x : A45)⁻¹ = tA := by
    have hmap : qH (z := z) D ⟨(bH : G) * y * (bH : G)⁻¹, hconjH⟩ =
        (x : A45) * tA * (x : A45)⁻¹ := by
      have heq : (⟨(bH : G) * y * (bH : G)⁻¹, hconjH⟩ : ↥(H z)) =
          bH * ⟨y, hyH⟩ * bH⁻¹ := Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_inv, hq, hqy]
    rw [hqconj] at hmap
    exact hmap.symm
  constructor
  · calc (x : A45) * tA = ((x : A45) * tA * (x : A45)⁻¹) * (x : A45) := by group
      _ = tA * (x : A45) := by rw [hxconj]
  · intro k hk hbk
    obtain ⟨c, hcπ⟩ := QuotientV.pi_surjective z (spinVecToV h P k)
    have hcsc : hbadCoord h P (c : G) = k :=
      spinVecToV_injective h P (by rw [← (spinVecToV_hbadCoord h P (c).2).symm, hcπ])
    have hcQ : QuotientV.pi z c ∈ Qbar h P τ (hbadCoord h P (j : G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · change conjV h τ (QuotientV.pi z c) = QuotientV.pi z c
        rw [hcπ, conjV_spinVecToV D h P hP, hqτ, hk]
      · change polarVZMod h (spinVecToV h P (hbadCoord h P (j : G))) (QuotientV.pi z c) = 0
        rw [hcπ, polarVZMod_spinVecToV_eq_b D h P hP]
        exact hbk
    obtain ⟨heN, hecoord⟩ :=
      NJ_commutator_coord (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
        B hBn hbB hcQ
    have hecoord' : hbadCoord h P (((conjJ' z bH c) * c⁻¹ : J z) : G) =
        ((rhoA (qH (z := z) D bH) : GL8) : Mat8) *ᵥ hbadCoord h P (c : G) +
          hbadCoord h P (c : G) := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hecoord
    have hcov' := hcov (conjJ' z bH c * c⁻¹) heN
    rw [hecoord'] at hcov'
    rw [hq, hcsc] at hcov'
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcov'

private theorem card_qH_image_le_sixteen (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1)
    (hqy : qH (z := z) D ⟨y, hyH⟩ = tA) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (hwj : IsFixedT (z := z) h P j)
    (hj' : ¬ ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card ↥(qHB (z := z) D B) ≤ 16 := by
  classical
  obtain ⟨ℓ, j₁, hℓ, hj₁, hcov⟩ :=
    exists_ell_j1_coord (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
      hwj hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord
  have hM : Nat.card {a : A45 // a ∈ Mset (hbadCoord h P (j : G)) ℓ j₁} ≤ 16 :=
    spin_card_centralizer_t_le_sixteen (hbadCoord h P (j : G)) hwj hj' ℓ j₁ hℓ hj₁
  have hmemM : ∀ x : ↥(qHB (z := z) D B),
      (x : A45) ∈ Mset (hbadCoord h P (j : G)) ℓ j₁ :=
    qHB_mem_Mset (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hqy hyj
      B hBC hBn hcov
  exact (Nat.card_le_card_of_injective (fun x : ↥(qHB (z := z) D B) =>
    (⟨(x : A45), hmemM x⟩ : {a : A45 // a ∈ Mset (hbadCoord h P (j : G)) ℓ j₁}))
    (fun x x' hxx => Subtype.ext
      (congrArg (fun z : {a : A45 // a ∈ Mset (hbadCoord h P (j : G)) ℓ j₁} =>
        (z : A45)) hxx))).trans hM

private theorem card_NJ_le_four (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (hwj : IsFixedT (z := z) h P j) {k₀ : J z}
    (hk₀ : k₀ ∈ Chat h τ) (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card ↥(NJ (z := z) B) ≤ 4 := by
  classical
  let N : Subgroup (J z) := NJ (z := z) B
  let N0 : Subgroup (J z) := N0 (z := z) B h τ
  have hN0card : Nat.card ↥N0 ≤ 2 :=
    card_N0_le_two (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
      hk₀ horth B hyB hzB hno hz₁ hz₁z hord
  have hsecond : ∀ {n : J z}, n ∈ N → n ∉ N0 →
      ∃ m : V, hbadCoord h P (n : G) = hbadCoord h P (j : G) +
        (((rhoA tA : GL8) : Mat8) *ᵥ m + m) := by
    intro n hn hn0; rcases NJ_coord_dichotomy (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
      hyj B hBC hBn hzB hwj hn with hcase | hcase
    · obtain ⟨m, hm⟩ := hcase; exfalso
      exact hn0 (Subgroup.mem_inf.mpr ⟨hn, (mem_R_iff (z := z) D h P hP hqτ n).mpr
        ⟨m, by rw [hm, add_comm]⟩⟩)
    · exact hcase
  have hmul_mem_N0 : ∀ {a b : J z}, a ∈ N → b ∈ N → a ∉ N0 → b ∉ N0 → a * b⁻¹ ∈ N0 := by
    intro a b ha hb ha0 hb0
    exact mem_N0_of_second D h P hP hqτ ha hb (hsecond ha ha0) (hsecond hb hb0)
  by_cases hN1 : ∃ n₁ : J z, n₁ ∈ N ∧ n₁ ∉ N0
  · obtain ⟨n₁, hn₁N, hn₁0⟩ := hN1
    let f : ↥N → ↥N0 × Bool := fun n =>
      if hn : (n : J z) ∈ N0 then (⟨(n : J z), hn⟩, false)
      else (⟨(n : J z) * n₁⁻¹, hmul_mem_N0 n.2 hn₁N hn hn₁0⟩, true)
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : (a : J z) ∈ N0 <;> by_cases hb : (b : J z) ∈ N0
      · simp only [f, dif_pos ha, dif_pos hb, Prod.mk.injEq] at hab
        exact Subtype.ext (congrArg (fun x : ↥N0 => (x : J z)) hab.1)
      · simp only [f, dif_pos ha, dif_neg hb, Prod.mk.injEq] at hab
        exact absurd hab.2 (by decide)
      · simp only [f, dif_neg ha, dif_pos hb, Prod.mk.injEq] at hab
        exact absurd hab.2 (by decide)
      · simp only [f, dif_neg ha, dif_neg hb, Prod.mk.injEq] at hab
        exact Subtype.ext (mul_right_cancel (congrArg (fun x : ↥N0 => (x : J z)) hab.1))
    have hle := Nat.card_le_card_of_injective f hf
    calc Nat.card ↥N ≤ Nat.card (↥N0 × Bool) := hle
      _ = Nat.card ↥N0 * Nat.card Bool := Nat.card_prod _ _
      _ = Nat.card ↥N0 * 2 := by rw [show Nat.card Bool = 2 from by simp]
      _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 hN0card
      _ = 4 := by norm_num
  · have hsub : N ≤ N0 := by
      intro n hn; by_contra hn0
      exact hN1 ⟨n, hn, hn0⟩
    have hle : Nat.card ↥N ≤ Nat.card ↥N0 :=
      Nat.card_le_card_of_injective (fun n : ↥N => (⟨(n : J z), hsub n.2⟩ : ↥N0))
        (fun a b hab => Subtype.ext (congrArg (fun x : ↥N0 => (x : J z)) hab))
    exact (hle.trans hN0card).trans (by norm_num)

private theorem card_B_le_sixty_four (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ2 : τ * τ = 1)
    (hτσ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτσ₂ : τ * σ₂ = σ₂ * τ) {y : G} (hyH : y ∈ H z) (hy2 : y * y = 1)
    (hqy : qH (z := z) D ⟨y, hyH⟩ = tA) {j : J z}
    (hyj : y = (τ : G) * (j : G)) (hwj : IsFixedT (z := z) h P j)
    (hj' : ¬ ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    {k₀ : J z} (hk₀ : k₀ ∈ Chat h τ)
    (horth : b (hbadCoord h P (j : G)) (hbadCoord h P (k₀ : G)) ≠ 0)
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hno : ¬ ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card B ≤ 64 := by
  classical
  have hBleH : B ≤ H z := hBC.trans inf_le_left
  let f : ↥(B.subgroupOf (H z)) →* A45 :=
    (qH (z := z) D).comp (B.subgroupOf (H z)).subtype
  have hrange : f.range = qHB (z := z) D B := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let g : ↥f.ker → ↥(NJ (z := z) B) := fun x =>
    ⟨⟨(x.1.1 : G), by
        have hxq : qH (z := z) D x.1.1 = 1 := MonoidHom.mem_ker.mp x.2
        have hxJsub : x.1.1 ∈ (J z).subgroupOf (H z) :=
          (J_mem_iff (z := z) D x.1.1).mpr hxq
        exact Subgroup.mem_subgroupOf.mp hxJsub⟩,
      mem_NJ.mpr (Subgroup.mem_subgroupOf.mp x.1.2)⟩
  have hg : Function.Injective g := by
    intro x x' hxx
    have hval : (x.1.1 : G) = (x'.1.1 : G) :=
      congrArg (fun y : ↥(NJ (z := z) B) => ((y : J z) : G)) hxx
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  have hker : Nat.card ↥f.ker ≤ 4 :=
    (Nat.card_le_card_of_injective g hg).trans
      (card_NJ_le_four (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2 hyj
        hwj hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord)
  have hq : Nat.card ↥(qHB (z := z) D B) ≤ 16 :=
    card_qH_image_le_sixteen (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
      hqy hyj hwj hj' hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord
  have hcardB : Nat.card ↥(B.subgroupOf (H z)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleH).toEquiv
  calc Nat.card B = Nat.card ↥(B.subgroupOf (H z)) := hcardB.symm
    _ = Nat.card ↥f.ker * Nat.card ↥f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ↥f.ker * Nat.card ↥(qHB (z := z) D B) := by rw [hrange]
    _ ≤ 4 * 16 := Nat.mul_le_mul hker hq
    _ = 64 := by norm_num

private theorem exists_y_tau_j_data (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hqy : qH (z := z) D ⟨y, hyH⟩ = tA) :
    ∃ (τ : ↥(H z)) (j : J z), qH (z := z) D τ = tA ∧ τ * τ = 1 ∧
      τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ ∧ τ * σ₂ = σ₂ * τ ∧
      y = (τ : G) * (j : G) ∧ IsFixedT (z := z) h P j := by
  classical
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy, pow_two] at h
  obtain ⟨τ, hqτ, hτ2, hτne, hτσ₁, hτσ₂⟩ :=
    exists_tau_over_tA (z := z) (D := D) h hσ₂ hq₂ hc₂
  have hτinv : (τ : G)⁻¹ = (τ : G) :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using congrArg Subtype.val hτ2)
  have htA2 : tA * tA = 1 := Subtype.ext t_sq
  have htAinv : tA⁻¹ = tA := inv_eq_of_mul_eq_one_right htA2
  have hyjH : (τ : G)⁻¹ * y ∈ H z := (H z).mul_mem ((H z).inv_mem τ.2) hyH
  have hqjH : qH (z := z) D ⟨(τ : G)⁻¹ * y, hyjH⟩ = 1 := by
    have heq : (⟨(τ : G)⁻¹ * y, hyjH⟩ : ↥(H z)) = τ⁻¹ * ⟨y, hyH⟩ := Subtype.ext rfl
    rw [heq, map_mul, map_inv, hqτ, hqy, htAinv, htA2]
  have hjJ : (τ : G)⁻¹ * y ∈ J z := by
    have hmem : (⟨(τ : G)⁻¹ * y, hyjH⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff (z := z) D _).mpr hqjH
    simpa using Subgroup.mem_subgroupOf.mp hmem
  let j : J z := ⟨(τ : G)⁻¹ * y, hjJ⟩
  have hyj : y = (τ : G) * (j : G) := by
    change y = (τ : G) * ((τ : G)⁻¹ * y)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hconjτj : conjJ' z τ j = j⁻¹ := by
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have h1 : (τ : G) * (j : G) * (τ : G) * (j : G) = 1 := by
      calc (τ : G) * (j : G) * (τ : G) * (j : G) =
          ((τ : G) * (j : G)) * ((τ : G) * (j : G)) := by group
        _ = y * y := by rw [hyj.symm]
        _ = 1 := hy2
    calc (τ : G) * (j : G) * (τ : G)⁻¹ = (τ : G) * (j : G) * (τ : G) := by rw [hτinv]
      _ = ((τ : G) * (j : G) * (τ : G) * (j : G)) * (j : G)⁻¹ := by group
      _ = (j : G)⁻¹ := by rw [h1, one_mul]
  have hfixV : conjV h τ (QuotientV.pi z j) = QuotientV.pi z j := by
    rw [conjV_mk h τ j, hconjτj, map_inv]
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z j))
  have hwj : IsFixedT (z := z) h P j := by
    have h2 := hfixV
    rw [(spinVecToV_hbadCoord h P (j).2).symm, conjV_spinVecToV D h P hP, hqτ] at h2
    exact spinVecToV_injective h P h2
  exact ⟨τ, j, hqτ, hτ2, hτσ₁, hτσ₂, hyj, hwj⟩

theorem exists_J_conj_mem_of_qH_eq_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hqy : qH (z := z) D ⟨y, hyH⟩ = tA)
    (hbad : ∀ c ∈ H z,
      c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (B : Subgroup G) (hBC : B ≤ H z ⊓ centralizer ({y} : Set G))
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hyB : y ∈ B) (hzB : z ∉ B)
    (hcard : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B) :
    ∃ c ∈ J z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  classical
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy, pow_two] at h
  obtain ⟨τ, j, hqτ, hτ2, hτσ₁, hτσ₂, hyj, hwj⟩ :=
    exists_y_tau_j_data (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hyH hy hqy
  by_cases hmem : ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m
  · exact (false_of_coord_range_t (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH
      hyj hbad hmem).elim
  · have hj' : ¬ ∃ m : V, hbadCoord h P (j : G) = ((rhoA tA : GL8) : Mat8) *ᵥ m + m := hmem
    obtain ⟨k₀, hk₀, horth⟩ :=
      exists_mem_Chat_not_orthogonal (z := z) (D := D) h P hP hqτ hwj hj'
    obtain ⟨z₁, hZeq, hz₁z, hord⟩ := exists_z1 (z := z) h
    have hz₁ : z₁ ∈ centerIn (J z) := by
      rw [hZeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
    by_contra hno
    have h64 : Nat.card B ≤ 64 :=
      card_B_le_sixty_four (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂ hyH hy2
        hqy hyj hwj hj' hk₀ horth B hBC hBn hyB hzB hno hz₁ hz₁z hord
    have h128 : 128 ≤ Nat.card B := by
      rw [← card_J_inf_centralizer (z := z) (D := D) h P hP hq₂ hqτ hτ2 hτσ₁ hτσ₂
        hyH hy2 hyj hwj hj']
      exact hcard
    omega

end CFSG.RankThree.GF2n.Parrott