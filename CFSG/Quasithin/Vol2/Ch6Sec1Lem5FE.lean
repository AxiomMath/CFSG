module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Family
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

theorem fixed_unitri_ch615 : ∀ v : Fin 3 → ZMod 2, (∀ a b c : ZMod 2, unitri a b c *ᵥ v = v) →
    v = 0 ∨ v = Pi.single 0 1 := by
  decide

theorem fixed_row_unitri_ch615 : ∀ v : Fin 3 → ZMod 2,
    (∀ a b c : ZMod 2, v ᵥ* unitri a b c = v) → v = 0 ∨ v = Pi.single 2 1 := by
  decide

theorem eq_unitri_ch615 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hdet : M.det ≠ 0)
    (hcol : M *ᵥ Pi.single 0 1 = Pi.single 0 1) (hrow : Pi.single 2 1 ᵥ* M = Pi.single 2 1) :
    M = unitri (M 0 1) (M 0 2) (M 1 2) := by
  have hc : ∀ i, M i 0 = (Pi.single 0 1 : Fin 3 → ZMod 2) i := fun i => by
    have := congrFun hcol i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  have hr : ∀ j, M 2 j = (Pi.single 2 1 : Fin 3 → ZMod 2) j := fun j => by
    have := congrFun hrow j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  have h00 : M 0 0 = 1 := by simpa using hc 0
  have h10 : M 1 0 = 0 := by simpa using hc 1
  have h20 : M 2 0 = 0 := by simpa using hc 2
  have h21 : M 2 1 = 0 := by simpa using hr 1
  have h22 : M 2 2 = 1 := by simpa using hr 2
  have h11 : M 1 1 = 1 := by
    rw [Matrix.det_fin_three, h00, h10, h20, h21, h22] at hdet
    have key : ∀ x y z w : ZMod 2, 1 * x * 1 - 1 * y * 0 - z * 0 * 1 + z * y * 0 + w * 0 * 0 -
        w * x * 0 ≠ 0 → x = 1 := by decide
    exact key _ _ _ _ hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitri, h00, h10, h20, h21, h22, h11]

theorem unitri_fix_ch615 : ∀ a b c : ZMod 2, unitri a b c *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
    Pi.single 2 1 ᵥ* unitri a b c = Pi.single 2 1 := by
  decide

theorem mem_sylowT_of_conj_ch615 {g : GL32} (hg : ∀ s ∈ sylowT, g * s * g⁻¹ ∈ sylowT) :
    g ∈ sylowT := by
  classical
  have hsurj : ∀ s ∈ sylowT, g⁻¹ * s * g ∈ sylowT := by
    let f : sylowT → sylowT := fun t => ⟨g * t * g⁻¹, hg t t.2⟩
    have hf : Function.Injective f := fun a b hab => by
      have := congrArg Subtype.val hab
      exact Subtype.ext (by simpa [f] using this)
    intro s hs
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hf) ⟨s, hs⟩
    have ht' : g * t * g⁻¹ = s := congrArg Subtype.val ht
    rw [← ht']
    simp [mul_assoc]
  have hconj : ∀ a b c : ZMod 2, ∃ a' b' c' : ZMod 2,
      unitri a b c * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * unitri a' b' c' := by
    intro a b c
    obtain ⟨a', b', c', h⟩ := hsurj _ ⟨a, b, c, rfl⟩
    refine ⟨a', b', c', ?_⟩
    have h' : unitriGL a b c * g = g * unitriGL a' b' c' := by
      rw [← h]
      group
    exact congrArg Units.val h'
  have hconj' : ∀ a b c : ZMod 2, ∃ a' b' c' : ZMod 2,
      ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * unitri a b c =
        unitri a' b' c' * ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro a b c
    obtain ⟨a', b', c', h⟩ := hsurj _ ⟨a, b, c, rfl⟩
    refine ⟨a', b', c', ?_⟩
    have h' : g⁻¹ * unitriGL a b c = unitriGL a' b' c' * g⁻¹ := by
      rw [← h]
      group
    exact congrArg Units.val h'
  have hgg : ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg' : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcol : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rcases fixed_unitri_ch615 ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1)
      (fun a b c => by
        obtain ⟨a', b', c', h⟩ := hconj a b c
        rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, (unitri_fix_ch615 a' b' c').1])
      with h0 | h1
    · exfalso
      have := congrArg (fun v => ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) h0
      simp only [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      have h' := congrFun this 0
      simp at h'
    · exact h1
  have hrow : Pi.single 2 1 ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = Pi.single 2 1 := by
    rcases fixed_row_unitri_ch615
      (Pi.single 2 1 ᵥ* ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      (fun a b c => by
        obtain ⟨a', b', c', h⟩ := hconj' a b c
        rw [Matrix.vecMul_vecMul, h, ← Matrix.vecMul_vecMul, (unitri_fix_ch615 a' b' c').2])
      with h0 | h1
    · exfalso
      have := congrArg (fun v => v ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h0
      simp only [Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one, Matrix.zero_vecMul] at this
      have h' := congrFun this 2
      simp at h'
    · have := congrArg (fun v => v ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
      simp only [Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one] at this
      exact this.symm
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  exact ⟨_, _, _, Units.ext (eq_unitri_ch615 _ hdet hcol hrow)⟩

theorem exists_conj_le_sylowT_ch615 {K : Subgroup GL32} (hK : IsPGroup 2 K) :
    ∃ g : GL32, ∀ k ∈ K, g⁻¹ * k * g ∈ sylowT := by
  have hindex : sylowT.index = 21 := by
    have h := sylowT.index_mul_card
    rw [card_sylowT, CFSG.LieType.SteinbergBR.AutGL32.card_GL32] at h
    omega
  have hodd : ¬ 2 ∣ Nat.card (GL32 ⧸ sylowT) := by
    rw [← Subgroup.index, hindex]
    norm_num
  obtain ⟨q, hq⟩ := hK.nonempty_fixed_point_of_prime_not_dvd_card _ hodd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, fun k hk => ?_⟩
  have h := hq ⟨k⁻¹, K.inv_mem hk⟩
  change (QuotientGroup.mk (k⁻¹ * g) : GL32 ⧸ sylowT) = QuotientGroup.mk g at h
  rw [QuotientGroup.eq] at h
  simpa [mul_assoc] using h

section L32

variable {Γ : Type*} [Group Γ] [Finite Γ] {G₁ : Subgroup Γ} (e : ↥G₁ ≃* GL32)
include e

omit [Finite Γ] in
theorem card_l32_ch615 : Nat.card G₁ = 168 := by
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32

omit [Finite Γ] in
theorem isSimpleGroup_l32_ch615 : IsSimpleGroup ↥G₁ :=
  have := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  (e.trans (slEquivGL 3).symm).isSimpleGroup

omit [Finite Γ] in
theorem not_isSolvable_l32_ch615 : ¬ Group.IsSolvable ↥G₁ := by
  intro hs
  have := isSimpleGroup_l32_ch615 e
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_nonabelian
  apply hab
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  set f := e.trans (slEquivGL 3).symm
  have := hc (f.symm a) (f.symm b)
  have h2 := congrArg f this
  simpa using h2

omit [Finite Γ] in
theorem eq_one_of_commute_l32_ch615 {g : Γ} (hg : g ∈ G₁) (h : ∀ x ∈ G₁, g * x = x * g) :
    g = 1 := by
  have hc : e ⟨g, hg⟩ ∈ Subgroup.center GL32 := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h x x.2).symm
  rw [center_GL32, Subgroup.mem_bot] at hc
  have := e.injective (hc.trans (map_one e).symm)
  exact congrArg Subtype.val this

omit [Finite Γ] in
theorem exists_eq_conj_l32_ch615 (α : MulAut ↥G₁) (hα : Odd (orderOf α)) :
    ∃ g : ↥G₁, α = MulAut.conj g := by
  set β : MulAut GL32 := MulAut.congr e α with hβdef
  have hβ : Odd (orderOf β) := by rw [hβdef, MulEquiv.orderOf_eq]; exact hα
  set R := (MulAut.conj : GL32 →* MulAut GL32).range with hR
  have hR2 : R.index = 2 := CFSG.LieType.SteinbergBR.AutGL32.index_inner
  have hRn : R.Normal := Subgroup.normal_of_index_eq_two hR2
  have hβ2 : β ^ 2 ∈ R := by
    have := Subgroup.pow_index_mem R β
    rwa [hR2] at this
  have hβR : β ∈ R := by
    obtain ⟨k, hk⟩ := hβ
    have h1 : β ^ (orderOf β) = 1 := pow_orderOf_eq_one β
    have e1 : β = (β ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      calc β = β ^ (orderOf β) * β := by rw [h1, one_mul]
        _ = β ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
    rw [e1]
    exact R.pow_mem hβ2 _
  obtain ⟨s, hs⟩ := hβR
  refine ⟨e.symm s, MulEquiv.ext fun x => ?_⟩
  have hx : s * e x * s⁻¹ = e (α x) := by
    have := congrArg (fun φ : MulAut GL32 => φ (e x)) hs
    simpa [hβdef, MulAut.congr_apply] using this
  apply e.injective
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hx]

theorem card_sylow_l32_ch615 {S : Subgroup Γ} (hS : IsSylowTwoOf S G₁) : Nat.card S = 8 := by
  obtain ⟨hSG, hS2, hodd⟩ := hS
  have h := (S.subgroupOf G₁).index_mul_card
  rw [card_l32_ch615 e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  rw [hk] at h ⊢
  have hk8 : k < 8 := by
    by_contra hk'
    have h1 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk')
    have h2 : 2 ^ k ≤ 168 := Nat.le_of_dvd (by norm_num) ⟨_, (h.symm.trans (mul_comm _ _))⟩
    omega
  interval_cases k <;> omega

theorem index_ne_three_l32_ch615 (H : Subgroup ↥G₁) : H.index ≠ 3 := by
  intro h3
  have := isSimpleGroup_l32_ch615 e
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with hb | ht
  · have hinj : Function.Injective (MulAction.toPermHom ↥G₁ (↥G₁ ⧸ H)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, ← Subgroup.index, h3, card_l32_ch615 e] at this
    norm_num at this
  · have : H = ⊤ := top_le_iff.mp (ht ▸ Subgroup.normalCore_le H)
    rw [this, Subgroup.index_top] at h3
    norm_num at h3

theorem card_eq_24_l32_ch615 {S P : Subgroup Γ} (hS : IsSylowTwoOf S G₁) (hSP : S ≤ P)
    (hPG : P ≤ G₁) (hPS : P ≠ S) (hPG' : P ≠ G₁) : Nat.card P = 24 := by
  have h168 := card_l32_ch615 e
  have h8 := card_sylow_l32_ch615 e hS
  have hdvd1 : Nat.card P ∣ 168 := h168 ▸ Subgroup.card_dvd_of_le hPG
  have hdvd2 : 8 ∣ Nat.card P := h8 ▸ Subgroup.card_dvd_of_le hSP
  have hidx := (P.subgroupOf G₁).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, h168] at hidx
  obtain ⟨k, hk⟩ := hdvd2
  obtain ⟨m, hm⟩ := hdvd1
  rw [hk] at hidx hm ⊢
  have hkm : k * m = 21 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) (by rw [← mul_assoc, ← hm])
  have hk21 : k ≤ 21 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hkm; omega
    · exact hkm ▸ Nat.le_mul_of_pos_right k h0
  interval_cases k <;> try omega
  · exact absurd (Subgroup.eq_of_le_of_card_ge hSP (by rw [h8, hk])).symm hPS
  · exact absurd (index_ne_three_l32_ch615 e (P.subgroupOf G₁)) (by omega)
  · exact absurd (Subgroup.eq_of_le_of_card_ge hPG (by rw [h168, hk])) hPG'

theorem mem_of_conj_mem_l32_ch615 {S : Subgroup Γ} (hS : IsSylowTwoOf S G₁) {g : Γ}
    (hg : g ∈ G₁) (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ S := by
  set S' : Subgroup GL32 := (S.subgroupOf G₁).map e.toMonoidHom with hS'def
  have hS'2 : IsPGroup 2 S' :=
    (hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm).map _
  have hS'8 : Nat.card S' = 8 := by
    rw [hS'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.le).toEquiv, card_sylow_l32_ch615 e hS]
  obtain ⟨h, hh⟩ := exists_conj_le_sylowT_ch615 hS'2
  set K₀ : Subgroup GL32 := S'.map (MulAut.conj h⁻¹).toMonoidHom with hK₀
  have hK₀le : K₀ ≤ sylowT := by
    rintro _ ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hh k hk
  have hK₀eq : K₀ = sylowT := Subgroup.eq_of_le_of_card_ge hK₀le (by
    rw [card_sylowT, hK₀, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hS'8])
  set g' : GL32 := e ⟨g, hg⟩ with hg'
  have hg'S : ∀ s ∈ S', g' * s * g'⁻¹ ∈ S' := by
    rintro _ ⟨⟨s, hsG⟩, hs, rfl⟩
    refine ⟨⟨g * s * g⁻¹, G₁.mul_mem (G₁.mul_mem hg hsG) (G₁.inv_mem hg)⟩,
      Subgroup.mem_subgroupOf.mpr (hgS s (Subgroup.mem_subgroupOf.mp hs)), ?_⟩
    rw [hg']
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_inv]
    rfl
  have hx : h⁻¹ * g' * h ∈ sylowT := by
    refine mem_sylowT_of_conj_ch615 fun t ht => ?_
    rw [← hK₀eq] at ht ⊢
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨g' * s * g'⁻¹, hg'S s hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [← hK₀eq] at hx
  obtain ⟨s, hs, hse⟩ := hx
  have hgs : g' = s := by
    have hse' : h⁻¹ * s * h = h⁻¹ * g' * h := by simpa using hse
    exact (mul_left_cancel (mul_right_cancel hse')).symm
  rw [← hgs] at hs
  obtain ⟨⟨s₀, hs₀G⟩, hs₀, hs₀e⟩ := hs
  have : (⟨s₀, hs₀G⟩ : ↥G₁) = ⟨g, hg⟩ := e.injective hs₀e
  have hsg : s₀ = g := congrArg Subtype.val this
  rw [← hsg]
  exact Subgroup.mem_subgroupOf.mp hs₀

omit e in
theorem mem_normalizer_of_conj_mem_l32_ch615 {R : Subgroup Γ} {g : Γ}
    (h : ∀ r ∈ R, g * r * g⁻¹ ∈ R) : g ∈ Subgroup.normalizer (R : Set Γ) := by
  classical
  let f : R → R := fun r => ⟨g * r * g⁻¹, h r r.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa [f] using this)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => h x hx, fun hx => ?_⟩
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hx⟩
  have hr' : g * r * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hr
  have : (r : Γ) = x := mul_left_cancel (mul_right_cancel hr')
  rw [← this]
  exact r.2

omit e [Finite Γ] in
theorem eq_one_of_odd_of_mem_l32_ch615 {S : Subgroup Γ} (hS : IsPGroup 2 S) {g : Γ} (hgS : g ∈ S)
    (hg : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨g, hgS⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hg)) (orderOf_dvd_of_pow_eq_one hk'))

theorem exists_mem_of_not_le_centralizer_l32_ch615 {Y B D S : Subgroup Γ}
    (hS : IsSylowTwoOf S G₁) (hSY : S ≤ Y) (hDY : D ≤ Y) (hY : Group.IsSolvable ↥Y)
    (hDN : D ≤ Subgroup.normalizer (G₁ : Set Γ)) (hDodd : ∀ d ∈ D, Odd (orderOf d))
    (hYB : ∀ y ∈ Y, Odd (orderOf y) → y ∈ B)
    (h3 : ∀ x ∈ B, ∀ y ∈ B, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
      y ∈ Subgroup.zpowers x)
    (hD : ¬ D ≤ Subgroup.centralizer (G₁ : Set Γ)) :
    ∃ d ∈ D, d ∈ G₁ ∧ d ≠ 1 ∧ d ^ 3 = 1 := by
  classical
  have hsimple := isSimpleGroup_l32_ch615 e
  have h168 := card_l32_ch615 e
  have hinner : ∀ d ∈ D, ∃ g ∈ G₁, (∀ x ∈ G₁, d * x * d⁻¹ = g * x * g⁻¹) ∧
      orderOf g ∣ orderOf d := by
    intro d hd
    set φ := G₁.normalizerMonoidHom with hφ
    set α := φ ⟨d, hDN hd⟩ with hα
    have hαo : orderOf α ∣ orderOf d := by
      have := orderOf_map_dvd φ ⟨d, hDN hd⟩
      rwa [Subgroup.orderOf_mk] at this
    have hαodd : Odd (orderOf α) := Odd.of_dvd_nat (hDodd d hd) hαo
    obtain ⟨g, hg⟩ := exists_eq_conj_l32_ch615 e α hαodd
    refine ⟨g, g.2, fun x hx => ?_, ?_⟩
    · have := congrArg (fun β : MulAut ↥G₁ => ((β ⟨x, hx⟩ : ↥G₁) : Γ)) hg
      simpa [hα, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
    · have hinj : Function.Injective (MulAut.conj : ↥G₁ →* MulAut ↥G₁) := by
        rw [injective_iff_map_eq_one]
        intro y hy
        apply Subtype.ext
        refine eq_one_of_commute_l32_ch615 e y.2 fun x hx => ?_
        have := congrArg (fun β : MulAut ↥G₁ => ((β ⟨x, hx⟩ : ↥G₁) : Γ)) hy
        simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at this
        calc (y : Γ) * x = (y : Γ) * x * (y : Γ)⁻¹ * (y : Γ) := by group
          _ = x * y := by rw [this]
      have : orderOf (g : Γ) = orderOf α := by
        rw [hg, orderOf_injective _ hinj, Subgroup.orderOf_coe]
      rw [this]
      exact hαo
  have hR : ∀ d ∈ D, ∀ g ∈ G₁, (∀ x ∈ G₁, d * x * d⁻¹ = g * x * g⁻¹) → Odd (orderOf g) →
      g ≠ 1 → g ∈ Y ∧ Nat.card ↥(Y ⊓ G₁) = 24 := by
    intro d hd g hg hdg hgodd hg1
    have hgS : g ∉ S := fun hgS => hg1 (eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup hgS hgodd)
    have hex : ∃ s ∈ S, g * s * g⁻¹ ∉ S := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hgS (mem_of_conj_mem_l32_ch615 e hS hg hall)
    obtain ⟨s, hs, hgs⟩ := hex
    have hsG : s ∈ G₁ := hS.le hs
    have hxe : d * s * d⁻¹ = g * s * g⁻¹ := hdg s hsG
    have hxY : d * s * d⁻¹ * s⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (hDY hd) (hSY hs)) (Y.inv_mem (hDY hd)))
        (Y.inv_mem (hSY hs))
    have hxG : d * s * d⁻¹ * s⁻¹ ∈ G₁ := by
      rw [hxe]
      exact G₁.mul_mem (G₁.mul_mem (G₁.mul_mem hg hsG) (G₁.inv_mem hg)) (G₁.inv_mem hsG)
    have hxS : d * s * d⁻¹ * s⁻¹ ∉ S := fun hx => hgs (by
      have := S.mul_mem hx hs
      rwa [hxe, inv_mul_cancel_right] at this)
    set R := Y ⊓ G₁ with hRdef
    have hSR : S ≤ R := le_inf hSY hS.le
    have hRS : R ≠ S := fun h => hxS (h ▸ ⟨hxY, hxG⟩)
    have hRs : Group.IsSolvable ↥R :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (inf_le_left : R ≤ Y))
    have hRG : R ≠ G₁ := fun h => not_isSolvable_l32_ch615 e (by
      rw [h] at hRs
      exact hRs)
    have hR24 : Nat.card R = 24 := card_eq_24_l32_ch615 e hS hSR inf_le_right hRS hRG
    have hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
      intro r hr
      have hrG : r ∈ G₁ := hr.2
      rw [← hdg r hrG]
      refine ⟨Y.mul_mem (Y.mul_mem (hDY hd) hr.1) (Y.inv_mem (hDY hd)), ?_⟩
      rw [hdg r hrG]
      exact G₁.mul_mem (G₁.mul_mem hg hrG) (G₁.inv_mem hg)
    set N := G₁ ⊓ Subgroup.normalizer (R : Set Γ) with hNdef
    have hRN : R ≤ N := le_inf inf_le_right Subgroup.le_normalizer
    have hgN : g ∈ N := ⟨hg, mem_normalizer_of_conj_mem_l32_ch615 hgR⟩
    have hNG : N ≠ G₁ := by
      intro hN
      have hle : G₁ ≤ Subgroup.normalizer (R : Set Γ) := by
        rw [← hN]
        exact fun x hx => hx.2
      have hn : (R.subgroupOf G₁).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hle
      rcases hn.eq_bot_or_eq_top with hb | ht
      · have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ G₁)).toEquiv
        rw [hb, Subgroup.card_bot, hR24] at this
        omega
      · have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ G₁)).toEquiv
        rw [ht, Subgroup.card_top, hR24, h168] at this
        omega
    have hNS : N ≠ S := fun h => hRS (le_antisymm (h ▸ hRN) hSR)
    have hN24 : Nat.card N = 24 := card_eq_24_l32_ch615 e hS (hSR.trans hRN) inf_le_left hNS hNG
    have hNR : N = R := (Subgroup.eq_of_le_of_card_ge hRN (by rw [hN24, hR24])).symm
    exact ⟨(hNR ▸ hgN).1, hR24⟩
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ ∈ D, ¬ δ ∈ Subgroup.centralizer (G₁ : Set Γ) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hD h
  obtain ⟨gδ, hgδG, hδg, hgδo⟩ := hinner δ hδ
  have hgδodd : Odd (orderOf gδ) := Odd.of_dvd_nat (hDodd δ hδ) hgδo
  have hgδ1 : gδ ≠ 1 := by
    rintro rfl
    apply hδG
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hδg x hx
    simp only [one_mul, inv_one, mul_one] at this
    calc x * δ = δ * x * δ⁻¹ * δ := by rw [this]
      _ = δ * x := by group
  obtain ⟨hgδY, hR24⟩ := hR δ hδ gδ hgδG hδg hgδodd hgδ1
  have hgδB : gδ ∈ B := hYB gδ hgδY hgδodd
  have hgδ3 : orderOf gδ = 3 := by
    have hdvd : orderOf gδ ∣ 24 := by
      have := Subgroup.orderOf_dvd_natCard (Y ⊓ G₁) ⟨hgδY, hgδG⟩
      rwa [hR24] at this
    have hodd' := hgδodd
    have h1 : orderOf gδ ≠ 1 := fun h => hgδ1 (orderOf_eq_one_iff.mp h)
    have h24 : orderOf gδ ∣ 3 := by
      have hcop : Nat.Coprime (orderOf gδ) 8 :=
        Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd')
      exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_three).mp h24 with h | h
    · exact absurd h h1
    · exact h
  have h3δ : 3 ∣ orderOf δ := hgδ3 ▸ hgδo
  set d₃ := δ ^ (orderOf δ / 3) with hd₃
  have hd₃D : d₃ ∈ D := D.pow_mem hδ _
  have hd₃o : orderOf d₃ = 3 := by
    rw [hd₃, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos δ) h3δ) (by norm_num)).ne'
      (Nat.div_dvd_of_dvd h3δ)]
    exact Nat.div_div_self h3δ (orderOf_pos δ).ne'
  have hd₃3 : d₃ ^ 3 = 1 := by rw [← hd₃o]; exact pow_orderOf_eq_one d₃
  have hd₃1 : d₃ ≠ 1 := fun h => by rw [h, orderOf_one] at hd₃o; omega
  obtain ⟨g₃, hg₃G, hd₃g, hg₃o⟩ := hinner d₃ hd₃D
  have hg₃3 : g₃ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hd₃o ▸ hg₃o)
  have hg₃odd : Odd (orderOf g₃) := Odd.of_dvd_nat (hDodd d₃ hd₃D) hg₃o
  have hg₃B : g₃ ∈ B := by
    by_cases h1 : g₃ = 1
    · rw [h1]; exact B.one_mem
    · exact hYB g₃ (hR d₃ hd₃D g₃ hg₃G hd₃g hg₃odd h1).1 hg₃odd
  have hd₃B : d₃ ∈ B := hYB d₃ (hDY hd₃D) (Odd.of_dvd_nat (hDodd d₃ hd₃D) dvd_rfl)
  set c := d₃ * g₃⁻¹ with hc
  have hcC : ∀ x ∈ G₁, c * x = x * c := by
    intro x hx
    have hx' : g₃⁻¹ * x * g₃ ∈ G₁ := G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hg₃G) hx) hg₃G
    have := hd₃g _ hx'
    calc c * x = d₃ * (g₃⁻¹ * x * g₃) * d₃⁻¹ * (d₃ * g₃⁻¹) := by rw [hc]; group
      _ = x * c := by rw [this, hc]; group
  have hdg3 : d₃ * g₃ = g₃ * d₃ := by
    have := hd₃g g₃ hg₃G
    calc d₃ * g₃ = d₃ * g₃ * d₃⁻¹ * d₃ := by group
      _ = g₃ * d₃ := by rw [this]; group
  have hc3 : c ^ 3 = 1 := by
    have hcomm : Commute d₃ g₃⁻¹ := (Commute.inv_right hdg3)
    rw [hc, hcomm.mul_pow, hd₃3, one_mul, inv_pow, hg₃3, inv_one]
  have hcB : c ∈ B := B.mul_mem hd₃B (B.inv_mem hg₃B)
  have hcg : gδ * c = c * gδ := (hcC gδ hgδG).symm
  have hcz := h3 gδ hgδB c hcB (by rw [← hgδ3]; exact pow_orderOf_eq_one gδ) hc3 hcg hgδ1
  have hcG : c ∈ G₁ := (Subgroup.zpowers_le.mpr hgδG) hcz
  have hc1 : c = 1 := eq_one_of_commute_l32_ch615 e hcG hcC
  refine ⟨d₃, hd₃D, ?_, hd₃1, hd₃3⟩
  have : d₃ = g₃ := by
    rw [hc] at hc1
    exact mul_inv_eq_one.mp hc1
  rw [this]
  exact hg₃G

end L32

end CFSG.Quasithin.H13
