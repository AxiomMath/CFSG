module

public import CFSG.Quasithin.EmptyFaithful.S153G23
public import CFSG.Quasithin.Background.C1PackS15207
public import CFSG.Quasithin.EmptyFaithful.S153D51

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3SolvableOverSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S Z : Subgroup G), IsLnTwoQuot L 3 → IsSylowTwoOf S L →
    Z ≤ L → Group.IsSolvable ↥Z → S ≤ Subgroup.normalizer (Z : Set G) → 3 ∣ Nat.card ↥Z →
      ⁅oTwoUpper Z, S⁆ = oTwoUpper Z

@[expose] def YLCommSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅YL153 Yp L, Sgp153 T V₁ ⊓ L⁆ = YL153 Yp L

@[expose] def YCEqCentralizerO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L → Concl15314Two T Mc M →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ →
      (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
        Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) →
      YC153 Yp L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))

namespace SBd2

section Generic

variable {Q : Type} [Group Q]

theorem exists_mul_of_mem_sup' {A B : Subgroup Q} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Q}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup Q :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        rw [mul_inv_rev, h1] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem inf_eq_bot_or_eq_of_card_three [Finite Q] {A : Subgroup Q} (hA : Nat.card A = 3)
    (E : Subgroup Q) : E ⊓ A = ⊥ ∨ E ⊓ A = A := by
  have h1 : Nat.card ↥(E ⊓ A) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le (inf_le_right : E ⊓ A ≤ A)
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact Or.inl (Subgroup.card_eq_one.mp h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge inf_le_right (by omega))

theorem decomp_of_invariant (hq3 : ∀ q : Q, q ^ 3 = 1) {A B E : Subgroup Q} (φ : Q →* Q)
    (hA : ∀ a ∈ A, φ a = a⁻¹) (hB : ∀ b ∈ B, φ b = b) (hE : ∀ e ∈ E, φ e ∈ E)
    {a b : Q} (ha : a ∈ A) (hb : b ∈ B) (hq : a * b ∈ E) : a ∈ E ∧ b ∈ E := by
  have h1 : φ (a * b) = a⁻¹ * b := by rw [map_mul, hA a ha, hB b hb]
  have h2 : φ (a * b) ∈ E := hE _ hq
  rw [h1] at h2
  have h3 : a * a ∈ E := by
    have := E.mul_mem hq (E.inv_mem h2)
    have e : a * b * (a⁻¹ * b)⁻¹ = a * a := by group
    rwa [e] at this
  have h4 : a ∈ E := by
    have e : a = a * a * (a * a) := by
      have := hq3 a
      calc a = a ^ 3 * a := by rw [this, one_mul]
        _ = a * a * (a * a) := by simp [pow_succ, mul_assoc]
    rw [e]
    exact E.mul_mem h3 h3
  refine ⟨h4, ?_⟩
  have e : b = a⁻¹ * (a * b) := by group
  rw [e]
  exact E.mul_mem (E.inv_mem h4) hq

theorem cases_of_invariant [Finite Q] (hq3 : ∀ q : Q, q ^ 3 = 1) {A B E : Subgroup Q}
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (hAB : ∀ q : Q, ∃ a ∈ A, ∃ b ∈ B, a * b = q)
    (φ : Q →* Q) (hA : ∀ a ∈ A, φ a = a⁻¹) (hB : ∀ b ∈ B, φ b = b) (hE : ∀ e ∈ E, φ e ∈ E) :
    E = ⊥ ∨ E = A ∨ E = B ∨ E = ⊤ := by
  have key : ∀ q ∈ E, ∃ a ∈ E ⊓ A, ∃ b ∈ E ⊓ B, a * b = q := by
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hAB q
    obtain ⟨h1, h2⟩ := decomp_of_invariant hq3 φ hA hB hE ha hb hq
    exact ⟨a, ⟨h1, ha⟩, b, ⟨h2, hb⟩, rfl⟩
  rcases inf_eq_bot_or_eq_of_card_three hA3 E with hEA | hEA <;>
    rcases inf_eq_bot_or_eq_of_card_three hB3 E with hEB | hEB
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := key q hq
    rw [hEA, Subgroup.mem_bot] at ha
    rw [hEB, Subgroup.mem_bot] at hb
    simp [ha, hb]
  · right; right; left
    refine le_antisymm (fun q hq => ?_) (fun b hb => ?_)
    · obtain ⟨a, ha, b, hb, rfl⟩ := key q hq
      rw [hEA, Subgroup.mem_bot] at ha
      rw [ha, one_mul]
      exact hb.2
    · rw [← hEB] at hb
      exact hb.1
  · right; left
    refine le_antisymm (fun q hq => ?_) (fun a ha => ?_)
    · obtain ⟨a, ha, b, hb, rfl⟩ := key q hq
      rw [hEB, Subgroup.mem_bot] at hb
      rw [hb, mul_one]
      exact ha.2
    · rw [← hEA] at ha
      exact ha.1
  · right; right; right
    rw [eq_top_iff]
    intro q _
    obtain ⟨a, ha, b, hb, rfl⟩ := hAB q
    have haE : a ∈ E := by rw [← hEA] at ha; exact ha.1
    have hbE : b ∈ E := by rw [← hEB] at hb; exact hb.1
    exact E.mul_mem haE hbE

theorem inv_of_card_three [Finite Q] {A : Subgroup Q} (hA : Nat.card A = 3) (hq3 : ∀ q : Q, q ^ 3 = 1)
    (φ : Q →* Q) {u : Q} (hu : u ∈ A) (hu1 : u ≠ 1) (hφA : φ u ∈ A) (hφ1 : φ u ≠ 1)
    (hφu : φ u ≠ u) : ∀ a ∈ A, φ a = a⁻¹ := by
  have hord : orderOf u = 3 := orderOf_eq_prime (hq3 u) hu1
  have hzp : Subgroup.zpowers u = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_
    rw [Nat.card_zpowers, hord, hA]
  have hφinv : φ u = u⁻¹ := by
    have hmem : φ u ∈ Subgroup.zpowers u := hzp ▸ hφA
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hj' : u ^ (j % 3) = φ u := by
      rw [← hj]
      have := zpow_mod_orderOf u j
      rwa [hord, Nat.cast_ofNat] at this
    have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hr with h | h | h
    · rw [h, zpow_zero] at hj'
      exact absurd hj'.symm hφ1
    · rw [h, zpow_one] at hj'
      exact absurd hj'.symm hφu
    · rw [h] at hj'
      rw [← hj']
      have h3 : u ^ (3 : ℤ) = 1 := by simpa using hq3 u
      have : u ^ (2 : ℤ) * u = 1 := by
        rw [← zpow_add_one]
        simpa using h3
      exact eq_inv_of_mul_eq_one_left this
  intro a ha
  rw [← hzp] at ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [map_zpow, hφinv, inv_zpow]

end Generic

section Star

variable {G : Type} [Group G]

theorem mem_pCoreOf_of_mk_eq {Y : Subgroup G} {x y : ↥Y}
    (h : (QuotientGroup.mk x : OTwoQuot Y) = QuotientGroup.mk y) :
    (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 Y := by
  have : (QuotientGroup.mk (x⁻¹ * y) : OTwoQuot Y) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]
  exact (mk_eq_one_iff_mem_pCoreOf (x⁻¹ * y)).mp this

theorem mk_eq_of_mem_pCoreOf {Y : Subgroup G} {x y : ↥Y}
    (h : (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 Y) :
    (QuotientGroup.mk x : OTwoQuot Y) = QuotientGroup.mk y := by
  have h1 : (QuotientGroup.mk (x⁻¹ * y) : OTwoQuot Y) = 1 :=
    (mk_eq_one_iff_mem_pCoreOf (x⁻¹ * y)).mpr h
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  exact inv_mul_eq_one.mp h1

@[expose] def conjHomOn (Y : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (Y : Set G)) : ↥Y →* ↥Y where
  toFun y := ⟨s * y * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs y).mp y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show s * ((a : G) * (b : G)) * s⁻¹ = s * (a : G) * s⁻¹ * (s * (b : G) * s⁻¹)
    group)

@[expose] def starConj (Y : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (Y : Set G)) :
    OTwoQuot Y →* OTwoQuot Y :=
  QuotientGroup.map (CFSG.Open.pCore 2 ↥Y) (CFSG.Open.pCore 2 ↥Y) (conjHomOn Y s hs) (by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 Y :=
      (mk_eq_one_iff_mem_pCoreOf x).mp ((QuotientGroup.eq_one_iff x).mpr hx)
    have h2 : s * (x : G) * s⁻¹ ∈ pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 Y hs) _).mp h1
    show conjHomOn Y s hs x ∈ CFSG.Open.pCore 2 ↥Y
    exact (QuotientGroup.eq_one_iff _).mp
      ((mk_eq_one_iff_mem_pCoreOf (conjHomOn Y s hs x)).mpr h2))

end Star

section StarFacts

variable {G : Type} [Group G] [Finite G]

theorem card_image_eq_three {Y X : Subgroup G} (hXY : X ≤ Y) (hQ3 : ∀ q : OTwoQuot Y, q ^ 3 = 1)
    (hX : padicValNat 3 (Nat.card ↥X) = 1) (hnot : ¬ X ≤ pCoreOf 2 Y) :
    Nat.card ↥(imageOTwoQuot Y X) = 3 := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥(imageOTwoQuot Y X) := fun g =>
    ⟨1, Subtype.ext (by simpa using hQ3 g.1)⟩
  obtain ⟨k, hk⟩ := hA3.exists_card_eq
  have hdvd : Nat.card ↥(imageOTwoQuot Y X) ∣ Nat.card ↥X := by
    have h1 := Subgroup.card_map_dvd (H := X.subgroupOf Y)
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))
    have h2 : Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv
    rwa [h2] at h1
  have hX0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  have hk1 : k ≤ 1 := by
    rw [hk] at hdvd
    have := (padicValNat_dvd_iff_le hX0).mp hdvd
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hnot
    intro x hx
    have hxY := hXY hx
    have hmem : (QuotientGroup.mk ⟨x, hxY⟩ : OTwoQuot Y) ∈ imageOTwoQuot Y X :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hxY, hx, rfl⟩
    have hbot : imageOTwoQuot Y X = ⊥ := Subgroup.card_eq_one.mp (by simpa using hk)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxY⟩).mp hmem
  have hk' : k = 1 := by omega
  rw [hk, hk']
  simp

theorem not_le_pCoreOf_of_padicValNat {Y X : Subgroup G}
    (hX : padicValNat 3 (Nat.card ↥X) = 1) : ¬ X ≤ pCoreOf 2 Y := by
  intro hle
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := ((pCoreOf_isPGroup 2 Y).to_le hle).exists_card_eq
  rw [hj, padicValNat.eq_zero_of_not_dvd] at hX
  · exact absurd hX (by norm_num)
  · intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

omit [Finite G] in
theorem le_sup_pCoreOf_of_image_le {Y X Z : Subgroup G} (hX : X ≤ Y)
    (h : imageOTwoQuot Y X ≤ imageOTwoQuot Y Z) : X ≤ Z ⊔ pCoreOf 2 Y := by
  intro x hx
  obtain ⟨z, hzY, hzZ, hz⟩ :=
    mem_imageOTwoQuot_iff.mp (h (mem_imageOTwoQuot_iff.mpr ⟨x, hX hx, hx, rfl⟩))
  have h1 := mem_pCoreOf_of_mk_eq hz
  have e : x = z * (z⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hzZ h1

omit [Finite G] in
theorem oTwoUpper_le_of_le_sup_two {X A B : Subgroup G} (hXAB : X ≤ A ⊔ B) (hB : IsPGroup 2 B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : oTwoUpper X ≤ A :=
  oTwoUpper_le_of_pow_mem fun _ hx => C1Pack153.exists_pow_mem_of_mem_sup_two hB hBA (hXAB hx)

end StarFacts

section PartA

variable {G : Type} [Group G] [Finite G]

theorem ycEq_of_comm (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hres : YLCommSL) :
    YCEqCentralizerO2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 c14 hV hU
  have hh15 : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
  have hh : Hyp153 G T Mc M := hh15.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hh15.decomp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.toCtx15313L.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.toCtx15313L.facts
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.toCtx15313L.conc.1
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 hh15 hI hLc
  have hSYN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) :=
    S153D.sup_Sgp153_le_normalizer_Yp hh15 hI hF
  have hcomm : ⁅YL153 Yp L, Sgp153 T V₁ ⊓ L⁆ = YL153 Yp L :=
    hres G T Mc M V₁ V₂ Yp I L t c hq c12
  obtain ⟨hYp, hLg3, hCg3, hQ⟩ := c12
  set P : Subgroup G := pCoreOf 2 L with hP
  set Pp : Subgroup G := pCoreOf 2 Yp with hPpdef
  set X' : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) with hX'
  set D : Subgroup G := oTwoUpper X' with hD
  set YLg : Subgroup G := YL153 Yp L with hYLg
  set YCg : Subgroup G := YC153 Yp L with hYCg
  set C : Subgroup G := centralizerSection Yp L P with hC
  have hYpY : Yp ≤ Y153 Mc M := by
    have := (oTwoUpper_le (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))).trans inf_le_left
    rwa [← hU.2] at this
  have hYpM : Yp ≤ M := hYpY.trans (Y153_le Mc M)
  have hDYp : D ≤ Yp := by
    have : D ≤ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
      oTwoUpper_mono (inf_le_inf_left _ (Subgroup.centralizer_le (fun x hx => Dc.le₁ hx)))
    rwa [← hU.2] at this
  have hMN := hh.le_normalizer
  have hDM : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M hm, B2F.le_normalizer_centralizer hMN hm⟩)
  have hDO : D = oTwoUpper D := (A4.oTwoUpper_oTwoUpper _).symm
  have hDYpN : Yp ≤ Subgroup.normalizer (D : Set G) := hYpM.trans hDM
  have hDc : D ≤ Subgroup.centralizer (VZ T M : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have hrel : (pCoreOf 2 X').relIndex X' = 3 := c14.2
    have hX'p : IsPGroup 2 ↥X' := by
      intro x
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X' x.2
      refine ⟨k, Subtype.ext ?_⟩
      have : (x : G) ^ 2 ^ k ∈ D := hk
      rw [hbot, Subgroup.mem_bot] at this
      simpa using this
    have hle : X' ≤ pCoreOf 2 X' :=
      le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hX'p
    have h1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  have hPpN : Yp ≤ Subgroup.normalizer (Pp : Set G) := le_normalizer_pCoreOf 2 Yp
  have hPpg : IsPGroup 2 ↥Pp := pCoreOf_isPGroup 2 Yp
  have hPpYp : Pp ≤ Yp := pCoreOf_le 2 Yp
  have hPpD : Pp ≤ Subgroup.normalizer (D : Set G) := fun x hx => hDYpN (hPpYp hx)
  have hPN' : Yp ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hYN hg)
  have hPLYp : P ⊓ Yp ≤ Pp :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hPN' hg, Subgroup.le_normalizer hg⟩)
      ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
  have hYLle : YLg ≤ Yp ⊓ L := oTwoUpper_le _
  have hYLY : YLg ≤ Yp := hYLle.trans inf_le_left
  have hYCsec : YCg ≤ C := oTwoUpper_le _
  have hYCY : YCg ≤ Yp := fun y hy => (hYCsec hy).1
  have hYLO : YLg = oTwoUpper YLg := (A4.oTwoUpper_oTwoUpper _).symm
  have hYCO : YCg = oTwoUpper YCg := (A4.oTwoUpper_oTwoUpper _).symm
  have hYCn : Yp ≤ Subgroup.normalizer (YCg : Set G) := fun g hg =>
    normalizer_le_normalizer_oTwoUpper _ (A4.mem_normalizer_of_conj_mem fun k hk =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hg) (hYN hg) (hPN' hg) hk)
  have hPpYC : Pp ≤ Subgroup.normalizer (YCg : Set G) := fun x hx => hYCn (hPpYp hx)
  have hLnot : ¬ YLg ≤ Pp := not_le_pCoreOf_of_padicValNat hLg3
  obtain ⟨s, hsS, a₀, ha₀, hs0⟩ :
      ∃ s ∈ Sgp153 T V₁ ⊓ L, ∃ a ∈ YLg, ¬ (s * a * s⁻¹ * a⁻¹ ∈ Pp) := by
    by_contra hno
    push Not at hno
    apply hLnot
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr fun a ha s hs => ?_
    have h1 := hno s hs a ha
    have e : ⁅a, s⁆ = (s * a * s⁻¹ * a⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Pp.inv_mem h1
  have hsSg : s ∈ Sgp153 T V₁ := hsS.1
  have hsL : s ∈ L := hsS.2
  have hsYp : s ∈ Subgroup.normalizer (Yp : Set G) := hSYN (Subgroup.mem_sup_right hsSg)
  have hsM : s ∈ M := hh.T_le hsSg.1
  have hsD : s ∈ Subgroup.normalizer (D : Set G) := hDM hsM
  have hsPp : s ∈ Subgroup.normalizer (Pp : Set G) := normalizer_le_normalizer_pCoreOf 2 Yp hsYp
  have hsYL : s ∈ Subgroup.normalizer (YLg : Set G) :=
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hsYp, Subgroup.le_normalizer hsL⟩)
  obtain ⟨e⟩ := hQ
  have hcommQ : ∀ x y : OTwoQuot Yp, x * y = y * x := fun x y => by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hq3 : ∀ q : OTwoQuot Yp, q ^ 3 = 1 := by
    have h : ∀ v : Multiplicative (Fin 2 → ZMod 3), v ^ 3 = 1 := by decide
    intro q
    apply e.injective
    rw [map_pow, map_one]
    exact h _
  set A : Subgroup (OTwoQuot Yp) := imageOTwoQuot Yp YLg with hA
  set B : Subgroup (OTwoQuot Yp) := imageOTwoQuot Yp YCg with hB
  set E : Subgroup (OTwoQuot Yp) := imageOTwoQuot Yp D with hE
  have hA3 : Nat.card A = 3 := card_image_eq_three hYLY hq3 hLg3 hLnot
  have hB3 : Nat.card B = 3 :=
    card_image_eq_three hYCY hq3 hCg3 (not_le_pCoreOf_of_padicValNat hCg3)
  have hAB : ∀ q : OTwoQuot Yp, ∃ a ∈ A, ∃ b ∈ B, a * b = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxm : (x : G) ∈ YLg ⊔ YCg := by rw [← hYp]; exact x.2
    have hq : (QuotientGroup.mk x : OTwoQuot Yp) ∈ imageOTwoQuot Yp (YLg ⊔ YCg) :=
      mem_imageOTwoQuot_iff.mpr ⟨(x : G), x.2, hxm, rfl⟩
    rw [imageOTwoQuot_sup hYLY hYCY] at hq
    exact exists_mul_of_mem_sup' (fun a _ b _ => hcommQ a b) hq
  let φ : OTwoQuot Yp →* OTwoQuot Yp := starConj Yp s hsYp
  have hφmk : ∀ (x : G) (hx : x ∈ Yp), φ (QuotientGroup.mk ⟨x, hx⟩) =
      QuotientGroup.mk ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsYp x).mp hx⟩ :=
    fun x hx => rfl
  have hφB : ∀ b ∈ B, φ b = b := by
    intro b hb
    obtain ⟨y, hyY, hyC, rfl⟩ := mem_imageOTwoQuot_iff.mp hb
    rw [hφmk]
    refine (mk_eq_of_mem_pCoreOf ?_).symm
    show y⁻¹ * (s * y * s⁻¹) ∈ Pp
    have h1 : s * y * s⁻¹ * y⁻¹ ∈ P := (oTwoUpper_le _ hyC).2.2.2 s hsL
    have h2 : s * y * s⁻¹ * y⁻¹ ∈ Yp :=
      Yp.mul_mem ((Subgroup.mem_normalizer_iff.mp hsYp y).mp hyY) (Yp.inv_mem hyY)
    have h3 : s * y * s⁻¹ * y⁻¹ ∈ Pp := hPLYp ⟨h1, h2⟩
    have h4 := (Subgroup.mem_normalizer_iff.mp (hPpN (Yp.inv_mem hyY)) _).mp h3
    have e' : y⁻¹ * (s * y * s⁻¹ * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * (s * y * s⁻¹) := by group
    rwa [e'] at h4
  have hφE : ∀ x ∈ E, φ x ∈ E := by
    intro x hx
    obtain ⟨d, hdY, hdD, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    rw [hφmk]
    exact mem_imageOTwoQuot_iff.mpr
      ⟨s * d * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsYp d).mp hdY,
        (Subgroup.mem_normalizer_iff.mp hsD d).mp hdD, rfl⟩
  have hφA : ∀ a ∈ A, φ a = a⁻¹ := by
    have ha₀Y : a₀ ∈ Yp := hYLY ha₀
    have huA : (QuotientGroup.mk ⟨a₀, ha₀Y⟩ : OTwoQuot Yp) ∈ A :=
      mem_imageOTwoQuot_iff.mpr ⟨a₀, ha₀Y, ha₀, rfl⟩
    have hu1 : (QuotientGroup.mk ⟨a₀, ha₀Y⟩ : OTwoQuot Yp) ≠ 1 := by
      intro h1
      have h2 : a₀ ∈ Pp := (mk_eq_one_iff_mem_pCoreOf ⟨a₀, ha₀Y⟩).mp h1
      apply hs0
      have h3 : s * a₀ * s⁻¹ ∈ Pp := (Subgroup.mem_normalizer_iff.mp hsPp a₀).mp h2
      exact Pp.mul_mem h3 (Pp.inv_mem h2)
    have hφuA : φ (QuotientGroup.mk ⟨a₀, ha₀Y⟩) ∈ A := by
      rw [hφmk]
      exact mem_imageOTwoQuot_iff.mpr
        ⟨s * a₀ * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsYp a₀).mp ha₀Y,
          (Subgroup.mem_normalizer_iff.mp hsYL a₀).mp ha₀, rfl⟩
    have hφu1 : φ (QuotientGroup.mk ⟨a₀, ha₀Y⟩) ≠ 1 := by
      intro h1
      rw [hφmk] at h1
      have h2 : s * a₀ * s⁻¹ ∈ Pp := (mk_eq_one_iff_mem_pCoreOf _).mp h1
      apply hu1
      refine (mk_eq_one_iff_mem_pCoreOf ⟨a₀, ha₀Y⟩).mpr ?_
      have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsPp) _).mp h2
      have e' : s⁻¹ * (s * a₀ * s⁻¹) * s⁻¹⁻¹ = a₀ := by group
      rwa [e'] at h3
    have hφuu : φ (QuotientGroup.mk ⟨a₀, ha₀Y⟩) ≠ QuotientGroup.mk ⟨a₀, ha₀Y⟩ := by
      intro h1
      rw [hφmk] at h1
      have h2 : a₀⁻¹ * (s * a₀ * s⁻¹) ∈ Pp := mem_pCoreOf_of_mk_eq h1.symm
      apply hs0
      have h3 := (Subgroup.mem_normalizer_iff.mp (hPpN ha₀Y) _).mp h2
      have e' : a₀ * (a₀⁻¹ * (s * a₀ * s⁻¹)) * a₀⁻¹ = s * a₀ * s⁻¹ * a₀⁻¹ := by group
      rwa [e'] at h3
    exact inv_of_card_three hA3 hq3 φ huA hu1 hφuA hφu1 hφuu
  have hLD' : ¬ YLg ≤ D := by
    intro h
    apply hV
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h.trans hDc)
  have hDnot : ¬ D ≤ Pp := by
    intro hle
    apply hD1
    have h0 : oTwoUpper D ≤ ⊥ := by
      rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxD, hxodd⟩
      obtain ⟨j, hj⟩ := hPpg ⟨x, hle hxD⟩
      have hx2 : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        ((Nat.coprime_two_right.mpr hxodd).pow_right j) dvd_rfl (orderOf_dvd_of_pow_eq_one hx2)))
    exact le_bot_iff.mp (hDO.le.trans h0)
  rcases cases_of_invariant hq3 hA3 hB3 hAB φ hφA hφB hφE with hE0 | hEA | hEB | hET
  ·
    exfalso
    apply hDnot
    intro d hd
    have hdY := hDYp hd
    have hmem : (QuotientGroup.mk ⟨d, hdY⟩ : OTwoQuot Yp) ∈ E :=
      mem_imageOTwoQuot_iff.mpr ⟨d, hdY, hd, rfl⟩
    rw [hE0, Subgroup.mem_bot] at hmem
    exact (mk_eq_one_iff_mem_pCoreOf _).mp hmem
  ·
    exfalso
    have h1 : YLg ≤ D ⊔ Pp := le_sup_pCoreOf_of_image_le hYLY hEA.ge
    exact hLD' (hYLO.le.trans (oTwoUpper_le_of_le_sup_two h1 hPpg hPpD))
  ·
    have h1 : YCg ≤ D ⊔ Pp := le_sup_pCoreOf_of_image_le hYCY hEB.ge
    have h2 : D ≤ YCg ⊔ Pp := le_sup_pCoreOf_of_image_le hDYp hEB.le
    exact le_antisymm (hYCO.le.trans (oTwoUpper_le_of_le_sup_two h1 hPpg hPpD))
      (hDO.le.trans (oTwoUpper_le_of_le_sup_two h2 hPpg hPpYC))
  ·
    exfalso
    have h1 : Yp ≤ D ⊔ Pp := le_sup_pCoreOf_of_image_le le_rfl (by
      intro q _
      show q ∈ E
      rw [hET]
      exact Subgroup.mem_top q)
    have hYpO : oTwoUpper Yp = Yp := hh15.oTwoUpper_eq
    exact hLD' (hYLY.trans (hYpO.symm.le.trans (oTwoUpper_le_of_le_sup_two h1 hPpg hPpD)))

end PartA

section PartB

variable {G : Type} [Group G] [Finite G]

theorem l3Branch2_of_yc (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hyc : YCEqCentralizerO2) :
    L3Branch2 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 c14 hV hU
  have hh15 : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
  have hh : Hyp153 G T Mc M := hh15.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.toCtx15313L.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.toCtx15313L.facts
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.toCtx15313L.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.toCtx15313L.conc.2.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hyc' := hyc G T Mc M V₁ V₂ Yp I L t c hq c12 c14 hV hU
  set D := oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) with hD
  have hMN := hh.le_normalizer
  have hDM : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M hm, B2F.le_normalizer_centralizer hMN hm⟩)
  have hDO : D = oTwoUpper D := (A4.oTwoUpper_oTwoUpper _).symm
  have hDleM : D ≤ M := (oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have h1 : YC153 Yp L = ⊥ := hyc'.trans hbot
    have h2 := c12.2.2.1
    rw [h1, Subgroup.card_bot, padicValNat_one_right] at h2
    exact absurd h2 (by norm_num)
  have hcharM : CharTwo M := by
    obtain ⟨S, hS⟩ := hh.qtfe.exists_sylow
    have hSM : (S : Subgroup G) ≤ M := hS ▸ hh.T_le
    exact hh.qtfe.qtke.2.1 M hh.inM.1.1 ⟨S, hSM⟩
  have hne : pCoreOf 2 D ≠ ⊥ :=
    C1Pack153.pCoreOf_ne_bot_of_normal hcharM hDleM hDM hD1 hDO.symm
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 D : Set G)) :=
    ⟨pCoreOf 2 D, hne, pCoreOf_isPGroup 2 D, rfl⟩
  have hMle : M ≤ Subgroup.normalizer (pCoreOf 2 D : Set G) :=
    hDM.trans (normalizer_le_normalizer_pCoreOf 2 D)
  have hMeq : Subgroup.normalizer (pCoreOf 2 D : Set G) = M := hh.inM.1.2 _ hloc hMle
  have hNDM : Subgroup.normalizer (D : Set G) ≤ M :=
    (normalizer_le_normalizer_pCoreOf 2 D).trans hMeq.le
  have hPR : pCoreOf 2 L ≤ R153 T V₁ Yp :=
    le_sup_left.trans (S153D.pCoreOf_sup_le_R153 h37 h38 hh15 hI hF hLc)
  have hRT : R153 T V₁ Yp ≤ T := by
    rw [hF.R_eq]
    exact inf_le_left
  have hPN : pCoreOf 2 L ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    hDM (hh.T_le (hRT (hPR hx)))
  have hLD : L ≤ Subgroup.normalizer (D : Set G) := by
    refine C1Pack152.normalizes_of_commutator_le (pCoreOf_isPGroup 2 L) hPN
      (le_normalizer_pCoreOf 2 L) hDO fun l hl x hx => ?_
    have hx' : x ∈ YC153 Yp L := hyc' ▸ hx
    exact (oTwoUpper_le _ hx').2.2.2 l hl
  exact hLn (le_inf (hLD.trans hNDM) hLI)

end PartB

section Derive

variable {G : Type} [Group G] [Finite G]

theorem yLCommSL_of_l3 (hres : L3SolvableOverSylow) : YLCommSL := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12
  have hh15 : Hyp15310 G T Mc M V₁ V₂ Yp t := c.toCtx15313L.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.toCtx15313L.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.toCtx15313L.facts
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.toCtx15313L.conc.1
  have hSYN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) :=
    S153D.sup_Sgp153_le_normalizer_Yp hh15 hI hF
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLc) hF.sylow
  have hYsolv : Group.IsSolvable ↥Yp := S153D.isSolvable_Yp hF
  have hZsolv : Group.IsSolvable ↥(Yp ⊓ L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : Yp ⊓ L ≤ Yp)) (Subgroup.inclusion_injective _)
  have hSZ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer ((Yp ⊓ L : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSYN (Subgroup.mem_sup_right hs.1),
      Subgroup.le_normalizer hs.2⟩
  have h3 : 3 ∣ Nat.card ↥(Yp ⊓ L) := by
    have hYLZ : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
    have h1 : 3 ∣ Nat.card ↥(YL153 Yp L) := by
      have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact dvd_of_one_le_padicValNat (by rw [c12.2.1])
    exact h1.trans (Subgroup.card_dvd_of_le hYLZ)
  exact hres G L (Sgp153 T V₁ ⊓ L) (Yp ⊓ L) hq hSL inf_le_right hZsolv hSZ h3

theorem l3Branch2_of_l3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hres : L3SolvableOverSylow) :
    L3Branch2 :=
  l3Branch2_of_yc h37 h38 (ycEq_of_comm h37 h38 (yLCommSL_of_l3 hres))

end Derive

end SBd2

end CFSG.Quasithin
