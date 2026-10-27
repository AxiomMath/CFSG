module

public import CFSG.Quasithin.Background.RonanF95Nondeg
public import CFSG.Quasithin.Background.RonanF95Ggt

public section

namespace CFSG.Quasithin.RonanF95

variable {G : Type*} [Group G]

@[instance_reducible] noncomputable def ebarCG {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal]
    (hP : FormHyp V₁ P) :
    CommGroup (Ebar V₁ P) :=
  { (inferInstance : Group (Ebar V₁ P)) with
    mul_comm := fun x y => by
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      have key : ((p : G) * r)⁻¹ * ((r : G) * p) =
          (r : G)⁻¹ * (p : G)⁻¹ * ((r : G)⁻¹)⁻¹ * ((p : G)⁻¹)⁻¹ := by
        group
      rw [key]
      exact hP.comm _ (P.inv_mem r.2) _ (P.inv_mem p.2) }

theorem core_conj_mem_iff {V₁ P : Subgroup G} (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    {c : G} (hc : c ∈ P) (t : G) : c * t * c⁻¹ ∈ V₁ ↔ t ∈ V₁ := by
  constructor
  · intro h
    have hcu := hcen _ h c hc
    have e : t = c * t * c⁻¹ := by
      calc t = c⁻¹ * ((c * t * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * t * c⁻¹)) := by rw [hcu]
        _ = c * t * c⁻¹ := by group
    rw [e]
    exact h
  · intro h
    have hct := hcen t h c hc
    have e : c * t * c⁻¹ = t := by
      rw [hct]
      group
    rw [e]
    exact h

theorem core_inv_mul_mem_iff {V₁ P : Subgroup G} (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    {c : G} (hc : c ∈ P) (p : G) : c⁻¹ * p ∈ V₁ ↔ c * p⁻¹ ∈ V₁ := by
  have e : c * p⁻¹ = c * (c⁻¹ * p)⁻¹ * c⁻¹ := by group
  rw [e, core_conj_mem_iff hcen hc, Subgroup.inv_mem_iff]

theorem core_invol_conj (v : G) (hv2 : v * v = 1) (p : G) : v * (v * p * v⁻¹) * v⁻¹ = p := by
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [hv]
  calc v * (v * p * v) * v = (v * v) * p * (v * v) := by group
    _ = p := by rw [hv2]; simp

theorem core_mk_eq_iff {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal] (c p : ↥P) :
    (QuotientGroup.mk c : Ebar V₁ P) = QuotientGroup.mk p ↔ (c : G)⁻¹ * (p : G) ∈ V₁ := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

theorem core_mk_eq_one_iff {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal] (p : ↥P) :
    (QuotientGroup.mk p : Ebar V₁ P) = 1 ↔ (p : G) ∈ V₁ := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem core_bf_eq_zero_iff {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal] (hP : FormHyp V₁ P)
    (p r : ↥P) : hP.bf (QuotientGroup.mk p) (QuotientGroup.mk r) = 0 ↔ (p : G) * r = r * p := by
  rw [FormHyp.bf_mk]
  constructor
  · intro h
    by_contra hne
    have hne' : (p : G) * r * (p : G)⁻¹ * (r : G)⁻¹ ≠ 1 := by
      intro h1
      apply hne
      calc (p : G) * r = (p : G) * r * (p : G)⁻¹ * (r : G)⁻¹ * ((r : G) * (p : G)) := by group
        _ = (r : G) * p := by rw [h1, one_mul]
    rw [if_neg hne'] at h
    exact one_ne_zero h
  · intro h
    have h1 : (p : G) * r * (p : G)⁻¹ * (r : G)⁻¹ = 1 := by
      calc (p : G) * r * (p : G)⁻¹ * (r : G)⁻¹ = (r : G) * p * (p : G)⁻¹ * (r : G)⁻¹ := by
            rw [h]
        _ = 1 := by group
    rw [if_pos h1]

theorem core_qf_eq_zero {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal] (hP : FormHyp V₁ P)
    {Y : Subgroup G} (hV : V₁ ≤ Y) (hYe : ∀ y ∈ Y, y * y = 1) (x : Ebar V₁ P)
    (hx : x ∈ FormHyp.imgE V₁ P Y) : hP.qf x = 0 := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [FormHyp.mem_imgE hV] at hx
  rw [FormHyp.qf_mk, if_pos (hYe _ hx)]

theorem core_mem_imgE_iff_fix {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal]
    (hP : FormHyp V₁ P) {v : G} (hvN : ∀ p ∈ P, v * p * v⁻¹ ∈ P) {a : Ebar V₁ P ≃* Ebar V₁ P}
    (ha_mk : ∀ p : ↥P, a (QuotientGroup.mk p) = QuotientGroup.mk ⟨v * p * v⁻¹, hvN p p.2⟩)
    {Y : Subgroup G} (hV : V₁ ≤ Y) (hY1 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Y)
    (x : Ebar V₁ P) : x ∈ FormHyp.imgE V₁ P Y ↔ a x = x := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [FormHyp.mem_imgE hV, ha_mk, core_mk_eq_iff]
  show (p : G) ∈ Y ↔ (v * (p : G) * v⁻¹)⁻¹ * (p : G) ∈ V₁
  rw [core_inv_mul_mem_iff hP.central (hvN (p : G) p.2), hY1 (p : G) p.2]

theorem core_mul_mem_imgE {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal]
    {v : G} (hvN : ∀ p ∈ P, v * p * v⁻¹ ∈ P) {a : Ebar V₁ P ≃* Ebar V₁ P}
    (ha_mk : ∀ p : ↥P, a (QuotientGroup.mk p) = QuotientGroup.mk ⟨v * p * v⁻¹, hvN p p.2⟩)
    {Y : Subgroup G} (hV : V₁ ≤ Y) (hsq : ∀ p ∈ P, p * p ∈ V₁)
    (hY2 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Y) (x : Ebar V₁ P) :
    a x * x ∈ FormHyp.imgE V₁ P Y := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [ha_mk, ← QuotientGroup.mk_mul, FormHyp.mem_imgE hV]
  show v * (p : G) * v⁻¹ * (p : G) ∈ Y
  have e : v * (p : G) * v⁻¹ * (p : G) =
      (v * (p : G) * v⁻¹ * (p : G)⁻¹) * ((p : G) * p) := by
    group
  rw [e]
  exact Y.mul_mem (hY2 (p : G) p.2) (hV (hsq (p : G) p.2))

theorem core_isCompl {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal] {Xg Yg : Subgroup G}
    (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hV₁X : V₁ ≤ Xg) (hV₁Y : V₁ ≤ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXYs : Xg ⊔ Yg = P) :
    IsCompl (FormHyp.imgE V₁ P Xg) (FormHyp.imgE V₁ P Yg) := by
  refine isCompl_iff.mpr ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_inf, FormHyp.mem_imgE hV₁X, FormHyp.mem_imgE hV₁Y] at hx
    have hmem : (p : G) ∈ Xg ⊓ Yg := Subgroup.mem_inf.mpr hx
    rw [hXY] at hmem
    exact (core_mk_eq_one_iff p).mpr hmem
  · have hsup : Xg.subgroupOf P ⊔ Yg.subgroupOf P = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hXP hYP, hXYs, Subgroup.subgroupOf_self]
    have hT : Xg.subgroupOf P ⊔ Yg.subgroupOf P ≤
        (FormHyp.imgE V₁ P Xg ⊔ FormHyp.imgE V₁ P Yg).comap (QuotientGroup.mk' (V₁.subgroupOf P)) := by
      apply sup_le
      · intro q hq
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
        exact Subgroup.mem_sup_left
          ((FormHyp.mem_imgE hV₁X q).mpr (Subgroup.mem_subgroupOf.mp hq))
      · intro q hq
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
        exact Subgroup.mem_sup_right
          ((FormHyp.mem_imgE hV₁Y q).mpr (Subgroup.mem_subgroupOf.mp hq))
    rw [hsup] at hT
    rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    exact Subgroup.mem_comap.mp (hT (Subgroup.mem_top q))

theorem center_le [Finite G] {V₁ P Xg Yg : Subgroup G} {v i : G} (hcard : Nat.card V₁ = 2)
    (hV₁P : V₁ ≤ P) (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    (hsq : ∀ p ∈ P, p * p ∈ V₁) (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁)
    (hvN : ∀ p ∈ P, v * p * v⁻¹ ∈ P) (hvN' : ∀ p ∈ P, v⁻¹ * p * v ∈ P)
    (hiN : ∀ p ∈ P, i * p * i⁻¹ ∈ P) (hiN' : ∀ p ∈ P, i⁻¹ * p * i ∈ P)
    (hv₁ : ∀ z ∈ V₁, v * z * v⁻¹ = z) (hi₁ : ∀ z ∈ V₁, i * z * i⁻¹ = z)
    (hv2 : v * v = 1) (hi2 : i * i = 1) (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hV₁X : V₁ ≤ Xg)
    (hV₁Y : V₁ ≤ Yg)
    (hX1 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Xg) (hX2 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Xg)
    (hY1 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Yg) (hY2 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXYs : Xg ⊔ Yg = P)
    (hXe : ∀ x ∈ Xg, x * x = 1) (hXc : ∀ x ∈ Xg, ∀ x' ∈ Xg, x * x' = x' * x)
    (hYe : ∀ y ∈ Yg, y * y = 1) (hYc : ∀ y ∈ Yg, ∀ y' ∈ Yg, y * y' = y' * y)
    (hXYcard : Nat.card Xg = Nat.card Yg)
    (hcase : (Nat.card Xg = 2 ^ 3 ∧ ∃ p ∈ P, ∃ r ∈ P, p * r ≠ r * p) ∨
      (Nat.card Xg = 2 ^ 5 ∧ ∀ y ∈ Yg, (∀ x ∈ Xg, y * x = x * y) → y ∈ V₁)) :
    ∀ p ∈ P, (∀ r ∈ P, p * r = r * p) → p ∈ V₁ := by
  have hP : FormHyp V₁ P := ⟨hcard, hV₁P, hcen, hsq, hcomm⟩
  haveI : (V₁.subgroupOf P).Normal := hP.normal
  obtain ⟨a, ha_def⟩ : ∃ a : Ebar V₁ P ≃* Ebar V₁ P, a = hP.conjE v hvN hvN' hv₁ := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Ebar V₁ P ≃* Ebar V₁ P, b = hP.conjE i hiN hiN' hi₁ := ⟨_, rfl⟩
  have ha_mk : ∀ p : ↥P, a (QuotientGroup.mk p) = QuotientGroup.mk ⟨v * p * v⁻¹, hvN p p.2⟩ := by
    intro p
    rw [ha_def]
    exact FormHyp.conjE_mk hP v hvN hvN' hv₁ p
  have hb_mk : ∀ p : ↥P, b (QuotientGroup.mk p) = QuotientGroup.mk ⟨i * p * i⁻¹, hiN p p.2⟩ := by
    intro p
    rw [hb_def]
    exact FormHyp.conjE_mk hP i hiN hiN' hi₁ p
  have ha : ∀ x, a (a x) = x := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [ha_mk, ha_mk]
    congr 1
    exact Subtype.ext (core_invol_conj v hv2 (p : G))
  have hb : ∀ y, b (b y) = y := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hb_mk, hb_mk]
    congr 1
    exact Subtype.ext (core_invol_conj i hi2 (p : G))
  have hqa : ∀ x, hP.qf (a x) = hP.qf x := by
    intro x
    rw [ha_def]
    exact FormHyp.qf_conjE hP v hvN hvN' hv₁ x
  have hqb : ∀ x, hP.qf (b x) = hP.qf x := by
    intro x
    rw [hb_def]
    exact FormHyp.qf_conjE hP i hiN hiN' hi₁ x
  have hXa : ∀ x, x ∈ FormHyp.imgE V₁ P Xg ↔ a x = x :=
    core_mem_imgE_iff_fix hP hvN ha_mk hV₁X hX1
  have hYb : ∀ y, y ∈ FormHyp.imgE V₁ P Yg ↔ b y = y :=
    core_mem_imgE_iff_fix hP hiN hb_mk hV₁Y hY1
  have haX : ∀ x, a x * x ∈ FormHyp.imgE V₁ P Xg :=
    core_mul_mem_imgE hvN ha_mk hV₁X hsq hX2
  have hbY : ∀ y, b y * y ∈ FormHyp.imgE V₁ P Yg :=
    core_mul_mem_imgE hiN hb_mk hV₁Y hsq hY2
  have hXYc : IsCompl (FormHyp.imgE V₁ P Xg) (FormHyp.imgE V₁ P Yg) :=
    core_isCompl hXP hYP hV₁X hV₁Y hXY hXYs
  have hqX : ∀ x ∈ FormHyp.imgE V₁ P Xg, hP.qf x = 0 :=
    fun x hx => core_qf_eq_zero hP hV₁X hXe x hx
  have hqY : ∀ y ∈ FormHyp.imgE V₁ P Yg, hP.qf y = 0 :=
    fun y hy => core_qf_eq_zero hP hV₁Y hYe y hy
  have hcX := FormHyp.card_imgE_mul hV₁X hXP
  have hcY := FormHyp.card_imgE_mul hV₁Y hYP
  rw [hcard] at hcX hcY
  have hXYcard' : Nat.card (FormHyp.imgE V₁ P Xg) = Nat.card (FormHyp.imgE V₁ P Yg) := by
    omega
  have hnd : ∀ x : Ebar V₁ P, (∀ y, hP.bf x y = 0) → x = 1 := by
    rcases hcase with ⟨hX8, p₀, hp₀, r₀, hr₀, hne⟩ | ⟨_, hrad⟩
    · have hX4 : Nat.card (FormHyp.imgE V₁ P Xg) = 4 := by
        norm_num at hX8
        omega
      exact @nondeg_dim_two (Ebar V₁ P) (ebarCG hP) hP.finite hP.exp hP.qf hP.bf
        (FormHyp.bf_left hP) (FormHyp.bf_right hP)
        (FormHyp.qf_mul hP) (FormHyp.bf_alt hP) a b ha hb hqa hqb
        (FormHyp.imgE V₁ P Xg) (FormHyp.imgE V₁ P Yg) hXa hYb haX hbY hXYc hqX hqY hX4
        ⟨QuotientGroup.mk ⟨p₀, hp₀⟩, QuotientGroup.mk ⟨r₀, hr₀⟩,
          fun h => hne ((core_bf_eq_zero_iff hP _ _).mp h)⟩
    · have hXX : ∀ x ∈ FormHyp.imgE V₁ P Xg, ∀ x' ∈ FormHyp.imgE V₁ P Xg, hP.bf x x' = 0 := by
        intro x hx x' hx'
        obtain ⟨p₁, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨p₂, rfl⟩ := QuotientGroup.mk_surjective x'
        rw [FormHyp.mem_imgE hV₁X] at hx hx'
        exact (core_bf_eq_zero_iff hP p₁ p₂).mpr (hXc _ hx _ hx')
      have hYY : ∀ y ∈ FormHyp.imgE V₁ P Yg, ∀ y' ∈ FormHyp.imgE V₁ P Yg, hP.bf y y' = 0 := by
        intro y hy y' hy'
        obtain ⟨q₁, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨q₂, rfl⟩ := QuotientGroup.mk_surjective y'
        rw [FormHyp.mem_imgE hV₁Y] at hy hy'
        exact (core_bf_eq_zero_iff hP q₁ q₂).mpr (hYc _ hy _ hy')
      have hYrad : ∀ y ∈ FormHyp.imgE V₁ P Yg,
          (∀ x ∈ FormHyp.imgE V₁ P Xg, hP.bf x y = 0) → y = 1 := by
        intro y hy hrad'
        obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
        rw [FormHyp.mem_imgE hV₁Y] at hy
        rw [core_mk_eq_one_iff]
        apply hrad (q : G) hy
        intro x hx
        have hxX : (QuotientGroup.mk ⟨x, hXP hx⟩ : Ebar V₁ P) ∈ FormHyp.imgE V₁ P Xg :=
          (FormHyp.mem_imgE hV₁X _).mpr hx
        exact ((core_bf_eq_zero_iff hP _ _).mp (hrad' _ hxX)).symm
      exact @nondeg_of_rad_Y (Ebar V₁ P) (ebarCG hP) hP.finite hP.exp hP.bf
        (FormHyp.bf_left hP) (FormHyp.bf_right hP)
        (FormHyp.bf_alt hP) (FormHyp.imgE V₁ P Xg) (FormHyp.imgE V₁ P Yg) hXYc hXX hYY
        hXYcard' hYrad
  intro p hp hcp
  have hz : (QuotientGroup.mk ⟨p, hp⟩ : Ebar V₁ P) = 1 := by
    apply hnd
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    exact (core_bf_eq_zero_iff hP _ _).mpr (hcp (r : G) r.2)
  exact (core_mk_eq_one_iff _).mp hz

theorem ggt_main [Finite G] {V₁ P Xg Yg : Subgroup G} {v i : G} (hcard : Nat.card V₁ = 2)
    (hV₁P : V₁ ≤ P) (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    (hsq : ∀ p ∈ P, p * p ∈ V₁) (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁)
    (hvN : ∀ p ∈ P, v * p * v⁻¹ ∈ P) (hvN' : ∀ p ∈ P, v⁻¹ * p * v ∈ P)
    (hiN : ∀ p ∈ P, i * p * i⁻¹ ∈ P) (hiN' : ∀ p ∈ P, i⁻¹ * p * i ∈ P)
    (hv₁ : ∀ z ∈ V₁, v * z * v⁻¹ = z) (hi₁ : ∀ z ∈ V₁, i * z * i⁻¹ = z)
    (hv2 : v * v = 1) (hi2 : i * i = 1) (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hV₁X : V₁ ≤ Xg)
    (hV₁Y : V₁ ≤ Yg)
    (hX1 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Xg) (hX2 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Xg)
    (hY1 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Yg) (hY2 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXYs : Xg ⊔ Yg = P)
    (hXe : ∀ x ∈ Xg, x * x = 1) (hXc : ∀ x ∈ Xg, ∀ x' ∈ Xg, x * x' = x' * x)
    (hYe : ∀ y ∈ Yg, y * y = 1) (hYc : ∀ y ∈ Yg, ∀ y' ∈ Yg, y * y' = y' * y)
    (hXYcard : Nat.card Xg = Nat.card Yg)
    (hnd : ∀ p ∈ P, (∀ r ∈ P, p * r = r * p) → p ∈ V₁)
    (hX : Nat.card Xg = 2 ^ 3 ∨ Nat.card Xg = 2 ^ 5) :
    (∃ p ∈ P, (v * i) ^ 2 * p * ((v * i) ^ 2)⁻¹ * p⁻¹ ∉ V₁) ∧
      ((∀ p ∈ P, (v * i) ^ 3 * p * ((v * i) ^ 3)⁻¹ * p⁻¹ ∈ V₁) ∨
        (Nat.card Xg = 2 ^ 5 ∧
          ((∀ p ∈ P, (v * i) ^ 5 * p * ((v * i) ^ 5)⁻¹ * p⁻¹ ∈ V₁) ∨
            (∀ p ∈ P, (v * i) ^ 6 * p * ((v * i) ^ 6)⁻¹ * p⁻¹ ∈ V₁)))) := by
  exact ggt_main_proof hcard hV₁P hcen hsq hcomm hvN hvN' hiN hiN' hv₁ hi₁ hv2 hi2 hXP hYP hV₁X
    hV₁Y hX1 hX2 hY1 hY2 hXY hXYs hXe hXc hYe hYc hXYcard hnd hX

end CFSG.Quasithin.RonanF95
