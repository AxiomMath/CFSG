module

public import CFSG.Quasithin.Background.S1549CBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S1549C

theorem exists_mul_of_mem_sup_of_comm {K : Type*} [Group K] {A B : Subgroup K}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : K} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup K :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have := hAB a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := hAB a ha b hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have h2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
              rw [← mul_inv_rev, ← mul_inv_rev, this]
            exact h2.symm }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem false_of_comm_mem_pCoreOf (hc2 : Case157Two T Mc M) {a b : G} (haY : a ∈ Y153 Mc M)
    (hbY : b ∈ Y153 Mc M)
    (hgen : ∀ y ∈ Y153 Mc M, ∃ (i j : ℤ) (c : G),
      c ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ∧ y = a ^ i * b ^ j * c)
    (hz : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (Y153 Mc M)) : False := by
  set Y := Y153 Mc M with hY
  set P := OTwoQuot Y with hP
  let A : P := QuotientGroup.mk (⟨a, haY⟩ : ↥Y)
  let B : P := QuotientGroup.mk (⟨b, hbY⟩ : ↥Y)
  have hAB : A * B = B * A := (mk_commute_iff (⟨a, haY⟩ : ↥Y) ⟨b, hbY⟩).mpr hz
  have hcen : ∀ c : G, c ∈ Y ⊓ Subgroup.centralizer (VZ T M : Set G) →
      ∃ hc : c ∈ Y, (QuotientGroup.mk (⟨c, hc⟩ : ↥Y) : P) ∈ Subgroup.center P := fun c hc => by
    have : c ∈ O2Z Y := hc2.2 ▸ hc
    exact mem_O2Z_iff.mp this
  have hall : ∀ y : ↥Y, ∃ (i j : ℤ) (C : P), C ∈ Subgroup.center P ∧
      (QuotientGroup.mk y : P) = A ^ i * B ^ j * C := by
    intro y
    obtain ⟨i, j, c, hc, hyc⟩ := hgen y y.2
    obtain ⟨hcY, hcC⟩ := hcen c hc
    refine ⟨i, j, QuotientGroup.mk ⟨c, hcY⟩, hcC, ?_⟩
    have : (y : ↥Y) = (⟨a, haY⟩ : ↥Y) ^ i * ⟨b, hbY⟩ ^ j * ⟨c, hcY⟩ := Subtype.ext (by simpa using hyc)
    rw [this]
    simp [A, B]
  have hab : ∀ p q : P, p * q = q * p := by
    intro p q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, j, C, hC, hy⟩ := hall y
    obtain ⟨i', j', C', hC', hy'⟩ := hall y'
    rw [hy, hy']
    have hAB' : Commute A B := hAB
    have hX : Commute (A ^ i * B ^ j) (A ^ i' * B ^ j') := by
      refine Commute.mul_left (Commute.mul_right ?_ (hAB'.zpow_zpow i j')) (Commute.mul_right ?_ ?_)
      · exact (Commute.refl A).zpow_zpow i i'
      · exact (hAB'.zpow_zpow i' j).symm
      · exact (Commute.refl B).zpow_zpow j j'
    have hc1 : ∀ g : P, Commute g C' := fun g => (Subgroup.mem_center_iff.mp hC' g)
    have hc2' : ∀ g : P, Commute g C := fun g => (Subgroup.mem_center_iff.mp hC g)
    show (A ^ i * B ^ j * C) * (A ^ i' * B ^ j' * C') = (A ^ i' * B ^ j' * C') * (A ^ i * B ^ j * C)
    have e1 : Commute (A ^ i * B ^ j * C) (A ^ i' * B ^ j' * C') :=
      Commute.mul_left (Commute.mul_right hX (hc1 _)) ((hc2' _).symm.mul_right (hc1 _))
    exact e1.eq
  have hctop : Subgroup.center P = ⊤ :=
    eq_top_iff.mpr fun p _ => Subgroup.mem_center_iff.mpr fun q => hab q p
  have h3 := hc2.1.1.center_order_p
  have h27 := hc2.1.2.1
  rw [hctop, Subgroup.card_top] at h3
  omega

theorem exists_decomp_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {hV : IsElemAbelian 2 (VZ T M)}
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) hV))} {tb : MulAut (IntMod (VZ T M) hV)}
    (hS : OfourStruct (autI hV M) L₁ L₂ tb) {a b : G}
    (haN : a ∈ Subgroup.normalizer (VZ T M : Set G))
    (hbN : b ∈ Subgroup.normalizer (VZ T M : Set G)) (haY : a ∈ Y153 Mc M) (hbY : b ∈ Y153 Mc M)
    (haL : convI hV ⟨a, haN⟩ ∈ L₂) (hao : orderOf (convI hV ⟨a, haN⟩) = 3)
    (hbL : convI hV ⟨b, hbN⟩ ∈ L₁) (hbo : orderOf (convI hV ⟨b, hbN⟩) = 3) :
    ∀ y ∈ Y153 Mc M, ∃ (i j : ℤ) (c : G),
      c ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ∧ y = a ^ i * b ^ j * c := by
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans h.le_normalizer
  set ab := convI hV ⟨a, haN⟩ with hab
  set bb := convI hV ⟨b, hbN⟩ with hbb
  have hcomm : bb * ab = ab * bb := hS.comm bb hbL ab haL
  have hAB : ∀ u ∈ Subgroup.zpowers ab, ∀ v ∈ Subgroup.zpowers bb, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_zpow (show Commute ab bb from hcomm.symm) m n)).eq
  set A := Subgroup.zpowers ab with hA
  set B := Subgroup.zpowers bb with hB
  have hAL : A ≤ L₂ := (Subgroup.zpowers_le).mpr haL
  have hBL : B ≤ L₁ := (Subgroup.zpowers_le).mpr hbL
  have hinf : A ⊓ B = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have : g ∈ L₁ ⊓ L₂ := ⟨hBL hg.2, hAL hg.1⟩
    rwa [hS.Linf] at this
  have hY : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  have hX : autI hV M = autOn M (VZ T M) := rfl
  have habY : ab ∈ autI hV (Y153 Mc M) := convI_mem_autI hV haY haN
  have hbbY : bb ∈ autI hV (Y153 Mc M) := convI_mem_autI hV hbY hbN
  have hAY : A ≤ autI hV (Y153 Mc M) := (Subgroup.zpowers_le).mpr habY
  have hBY : B ≤ autI hV (Y153 Mc M) := (Subgroup.zpowers_le).mpr hbbY
  have hcard9 : Nat.card (autI hV (Y153 Mc M)) = 9 := by
    rw [hY]; exact hS.card_oTwoUpper h.isSylowTwoOf_autI
  have hAcard : Nat.card A = 3 := by rw [hA, Nat.card_zpowers, hao]
  have hBcard : Nat.card B = 3 := by rw [hB, Nat.card_zpowers, hbo]
  have hbb1 : bb ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hbo; omega
  have hbbA : bb ∉ A := fun hbA => hbb1 (by
    have : bb ∈ A ⊓ B := ⟨hbA, Subgroup.mem_zpowers bb⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this)
  have hsupY : A ⊔ B ≤ autI hV (Y153 Mc M) := sup_le hAY hBY
  have hdvd : Nat.card ↥(A ⊔ B) ∣ 9 := hcard9 ▸ Subgroup.card_dvd_of_le hsupY
  have hAd : 3 ∣ Nat.card ↥(A ⊔ B) := hAcard ▸ Subgroup.card_dvd_of_le le_sup_left
  have hsup9 : Nat.card ↥(A ⊔ B) = 9 := by
    have h3 : Nat.card ↥(A ⊔ B) ≠ 3 := by
      intro h3
      have : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hAcard])
      exact hbbA (this ▸ (le_sup_right : B ≤ A ⊔ B) (Subgroup.mem_zpowers bb))
    have hle9 : Nat.card ↥(A ⊔ B) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    interval_cases hh : Nat.card ↥(A ⊔ B) <;> omega
  have hsupeq : A ⊔ B = autI hV (Y153 Mc M) :=
    Subgroup.eq_of_le_of_card_ge hsupY (by rw [hsup9, hcard9])
  intro y hy
  have hyN := hYN hy
  have hyb : convI hV ⟨y, hyN⟩ ∈ A ⊔ B := hsupeq ▸ convI_mem_autI hV hy hyN
  obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_mem_sup_of_comm hAB hyb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have haiN : a ^ i ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.zpow_mem _ haN i
  have hbjN : b ^ j ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.zpow_mem _ hbN j
  have habN : a ^ i * b ^ j ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.mul_mem _ haiN hbjN
  have hconv : convI hV ⟨a ^ i * b ^ j, habN⟩ = ab ^ i * bb ^ j := by
    have e : (⟨a ^ i * b ^ j, habN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        (⟨a, haN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ i *
          (⟨b, hbN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ j := Subtype.ext (by simp)
    rw [e, map_mul, map_zpow, map_zpow]
  have hcN : (a ^ i * b ^ j)⁻¹ * y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ habN) hyN
  refine ⟨i, j, (a ^ i * b ^ j)⁻¹ * y, ⟨?_, ?_⟩, by group⟩
  · exact Y153 Mc M |>.mul_mem (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ haY i)
      (Subgroup.zpow_mem _ hbY j))) hy
  · refine (convI_eq_one_iff hV ⟨(a ^ i * b ^ j)⁻¹ * y, hcN⟩).mp ?_
    have e : (⟨(a ^ i * b ^ j)⁻¹ * y, hcN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        (⟨a ^ i * b ^ j, habN⟩ : Subgroup.normalizer (VZ T M : Set G))⁻¹ * ⟨y, hyN⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, hconv, huv, inv_mul_cancel]

@[expose] def commSub (Y : Subgroup G) (x : G) : Subgroup G where
  carrier := {z | z ∈ Y ∧ x * z * x⁻¹ * z⁻¹ ∈ pCoreOf 2 Y}
  one_mem' := ⟨Y.one_mem, by simp⟩
  mul_mem' := by
    rintro z z' ⟨hz, hzc⟩ ⟨hz', hz'c⟩
    refine ⟨Y.mul_mem hz hz', ?_⟩
    have e : x * (z * z') * x⁻¹ * (z * z')⁻¹ =
        (x * z * x⁻¹ * z⁻¹) * (z * (x * z' * x⁻¹ * z'⁻¹) * z⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 Y).mul_mem hzc
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hz) _).mp hz'c)
  inv_mem' := by
    rintro z ⟨hz, hzc⟩
    refine ⟨Y.inv_mem hz, ?_⟩
    have e : x * z⁻¹ * x⁻¹ * (z⁻¹)⁻¹ = z⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * z⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y (Y.inv_mem hz)) _).mp
      ((pCoreOf 2 Y).inv_mem hzc)

omit [Finite G] in
theorem pCoreOf_le_commSub {Y : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (pCoreOf 2 Y : Set G)) : pCoreOf 2 Y ≤ commSub Y x := by
  intro o ho
  refine ⟨pCoreOf_le 2 Y ho, (pCoreOf 2 Y).mul_mem ((Subgroup.mem_normalizer_iff.mp hx o).mp ho)
    ((pCoreOf 2 Y).inv_mem ho)⟩

theorem exists_comm_not_mem_pCoreOf (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (hc2 : Case157Two T Mc M) {x : G} (hxT : x ∈ T)
    (hxS : x ∉ Sgp153 T V₁) (hx2 : x ^ 2 = 1) :
    ∃ y ∈ Y0 T Mc M, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 (Y153 Mc M) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, a, haN, haY0, haL, hao⟩ := h.exists_mem_Yplus_acts h113 D
  have haY : a ∈ Y153 Mc M := (oTwoUpper_le _ haY0).1
  have hxM : x ∈ M := h.T_le hxT
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hxM
  set xb := convI hV ⟨x, hxN⟩ with hxb
  have hxX : xb ∈ autI hV M := convI_mem_autI hV hxM hxN
  have hsw : B1.conjAut xb L₁ = L₂ ∧ B1.conjAut xb L₂ = L₁ := by
    rcases hS.perm xb hxX with ⟨h1, -⟩ | h2
    · exfalso
      refine hxS ⟨hxT, ?_⟩
      have hst : xb ∈ stabSub (commV L₁) := by
        refine mem_stabSub_of_map_eq ?_
        rw [commV_map_conjAut, h1]
      have := (mem_normalizer_map_inclMod_iff hV hxN (commV L₁)).2 hst
      rwa [← hV₁] at this
    · exact h2
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans h.le_normalizer
  set b : G := x * a * x⁻¹ with hb
  have hbY : b ∈ Y153 Mc M :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M hxM) a).mp haY
  have hbN : b ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hbY
  set ab := convI hV ⟨a, haN⟩ with hab
  set bb := convI hV ⟨b, hbN⟩ with hbb
  have hconvb : bb = xb * ab * xb⁻¹ := by
    have e : (⟨b, hbN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨x, hxN⟩ * ⟨a, haN⟩ * ⟨x, hxN⟩⁻¹ := Subtype.ext (by simp [hb])
    rw [hbb, e, map_mul, map_mul, map_inv]
  have hbL : bb ∈ L₁ := by
    have : xb * ab * xb⁻¹ ∈ B1.conjAut xb L₂ := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using haL
    rw [hsw.2] at this
    rwa [hconvb]
  have hbo : orderOf bb = 3 := by
    rw [hconvb, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hao
  have hgen := exists_decomp_Y153 h113 h hS haN hbN haY hbY haL hao hbL hbo
  set z : G := a * b * a⁻¹ * b⁻¹ with hz
  have hzY : z ∈ Y153 Mc M :=
    (Y153 Mc M).mul_mem ((Y153 Mc M).mul_mem ((Y153 Mc M).mul_mem haY hbY)
      ((Y153 Mc M).inv_mem haY)) ((Y153 Mc M).inv_mem hbY)
  have hzN : z ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hzY
  have hzC : z ∈ Subgroup.centralizer (VZ T M : Set G) := by
    refine (convI_eq_one_iff hV ⟨z, hzN⟩).mp ?_
    have e : (⟨z, hzN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ := Subtype.ext (by simp [hz])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : ab * bb = bb * ab := (hS.comm bb hbL ab haL).symm
    calc ab * bb * ab⁻¹ * bb⁻¹ = bb * ab * ab⁻¹ * bb⁻¹ := by rw [hc]
      _ = 1 := by group
  have hnot : z ∉ pCoreOf 2 (Y153 Mc M) := fun hzO => false_of_comm_mem_pCoreOf hc2 haY hbY hgen hzO
  have hxx : x * x = 1 := by simpa [pow_two] using hx2
  have hxbx : x * b * x⁻¹ = a := by
    rw [hb]
    calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x⁻¹ * x⁻¹) := by group
      _ = a := by
        rw [hxx, show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group, hxx]
        simp
  have hxz : x * z * x⁻¹ = z⁻¹ := by
    have e : x * z * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by
      rw [hz]; group
    rw [e, hxbx, ← hb, hz]
    group
  have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_Y153 Mc M hxM)
  have hle : pCoreOf 2 (Y153 Mc M) ⊔ Y0 T Mc M ≤ commSub (Y153 Mc M) x :=
    sup_le (pCoreOf_le_commSub hxO) (fun y hy =>
      ⟨(Y0_le T Mc M hy).1, hcon y hy⟩)
  have hzc : z ∈ commSub (Y153 Mc M) x := hle (inf_le_sup_Y0 h113 h ⟨hzY, hzC⟩)
  have h1 : z⁻¹ * z⁻¹ ∈ pCoreOf 2 (Y153 Mc M) := by
    have := hzc.2
    rwa [hxz] at this
  have h3 := h.pow_three_mem_pCoreOf_Y153 h113 hzY
  apply hnot
  have e : z = z ^ 3 * (z⁻¹ * z⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 (Y153 Mc M)).mul_mem h3 h1

theorem le_normalizer_Y0 (h : Hyp153 G T Mc M) : M ≤ Subgroup.normalizer (Y0 T Mc M : Set G) := by
  intro g hg
  have hK : g ∈ Subgroup.normalizer
      ((Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_Y153 Mc M hg, B2F.le_normalizer_centralizer h.le_normalizer hg⟩
  exact normalizer_le_normalizer_oTwoUpper _ hK

theorem inf_pCoreOf_Y0_le (h : Hyp153 G T Mc M) {H : Subgroup G} (hY0 : Y0 T Mc M ≤ H) :
    pCoreOf 2 H ⊓ Y0 T Mc M ≤ pCoreOf 2 (Y153 Mc M) := by
  have hY0Y : Y0 T Mc M ≤ Y153 Mc M := (Y0_le T Mc M).trans inf_le_left
  have hR : pCoreOf 2 H ⊓ Y0 T Mc M ≤ pCoreOf 2 (Y0 T Mc M) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_pCoreOf 2 H (hY0 hy),
      Subgroup.le_normalizer hy⟩
  refine hR.trans ?_
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hY0Y) ?_ (pCoreOf_isPGroup 2 _)
  exact fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_Y0 h (Y153_le Mc M hg))

theorem claim_c (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : Adm T Mc M H) :
    omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ ∧
      UH T M V₁ H ≤ centerOf (omegaOneOf (pCoreOf 2 H)) := by
  have h := cx.c.hyp
  have hF := cx.hF91 h113 hH
  have hY0H : Y0 T Mc M ≤ H := le_sup_left.trans hH.hY0
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H
  have hΩS : omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxQ, hx2⟩ := hx
    have hxT := hQT hxQ
    by_contra hxS
    obtain ⟨y, hy, hyc⟩ := exists_comm_not_mem_pCoreOf h113 h cx.c.decomp cx.case2 hxT hxS hx2
    apply hyc
    refine inf_pCoreOf_Y0_le h hY0H ⟨?_, ?_⟩
    · have h1 : y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hY0H hy)) x⁻¹).mp
          ((pCoreOf 2 H).inv_mem hxQ)
      have := (pCoreOf 2 H).mul_mem hxQ h1
      simpa [mul_assoc] using this
    · have h1 : x * y * x⁻¹ ∈ Y0 T Mc M :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_Y0 h (h.T_le hxT)) y).mp hy
      exact (Y0 T Mc M).mul_mem h1 ((Y0 T Mc M).inv_mem hy)
  have hnormΩ : H ≤ Subgroup.normalizer (omegaOneOf (pCoreOf 2 H) : Set G) := by
    refine F7.le_normalizer_closure _ fun g hg s hs => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) s).mp hs.1
    · rw [conj_pow, hs.2]
      group
  have hZS : ∀ z ∈ ZS153 T M V₁, ∀ ω ∈ Sgp153 T V₁, ω * z = z * ω := fun z hz ω hω =>
    Subgroup.mem_centralizer_iff.mp hz.2 ω hω
  refine ⟨hΩS, fun u hu => ⟨?_, ?_⟩⟩
  ·
    revert u
    refine (conjClosure_le fun k hk z hz => ?_ : UH T M V₁ H ≤ _)
    have hu : k * z * k⁻¹ ∈ pCoreOf 2 H := hF.conjClosure_Vp_le_pCoreOf (mem_conjClosure hk hz)
    refine Subgroup.subset_closure ⟨hu, ?_⟩
    have hz2 : z ^ 2 = 1 := h.elemAbelian.2 z hz.1
    rw [conj_pow, hz2]
    group
  · revert u
    refine (conjClosure_le fun k hk z hz => ?_ : UH T M V₁ H ≤ Subgroup.centralizer _)
    refine Subgroup.mem_centralizer_iff.mpr fun ω hω => ?_
    have hω' : k⁻¹ * ω * k ∈ omegaOneOf (pCoreOf 2 H) :=
      (Subgroup.mem_normalizer_iff.mp (hnormΩ (H.inv_mem hk)) ω).mp hω |> fun h' => by
        simpa using h'
    have := hZS z hz _ (hΩS hω')
    calc ω * (k * z * k⁻¹) = k * ((k⁻¹ * ω * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * ω * k)) * k⁻¹ := by rw [this]
      _ = (k * z * k⁻¹) * ω := by group

end S1549C

end CFSG.Quasithin
