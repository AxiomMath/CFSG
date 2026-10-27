module

public import CFSG.Quasithin.EmptyFaithful.S151b13Four
public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import CFSG.Quasithin.EmptyFaithful.S151b13
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E2SolvBaumann

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement



section Bridge

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem commutator_map_valHom151b {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (X : Subgroup (IntMod V hV)) :
    ⁅X.map (E2.valHom hV), A⁆ = (commSub X (autI hV A)).map (E2.valHom hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ a ha
    set c : IntMod V hV := convI hV ⟨a, hA ha⟩ w * w⁻¹ with hc
    have hcmem : c ∈ commSub X (autI hV A) :=
      Subgroup.subset_closure ⟨_, convI_mem_autI hV ha (hA ha), w, hw, rfl⟩
    refine ⟨c⁻¹, (commSub X (autI hV A)).inv_mem hcmem, ?_⟩
    show (c⁻¹).val = ⁅w.val, a⁆
    rw [hc, IntMod.val_inv, IntMod.val_mul, IntMod.val_inv, convI_apply_val,
      commutatorElement_def]
    group
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    show (convI hV g w * w⁻¹).val ∈ ⁅X.map (E2.valHom hV), A⁆
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hg ⟨w, hw, rfl⟩

omit [Finite G] in
theorem commutator_eq_map_commSub151b {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, A⁆ = (commSub ⊤ (autI hV A)).map (E2.valHom hV) := by
  rw [← commutator_map_valHom151b hV hA ⊤, E2.map_valHom_top]

omit [Finite G] in
theorem six_bridge151b {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {A₁ A₂ : Subgroup (MulAut (IntMod V hV))} (hA₁ : A₁ ≤ autI hV M) (hA₂ : A₂ ≤ autI hV M)
    (hd : ⁅V, preOn M V A₁⁆ ⊓ ⁅V, preOn M V A₂⁆ = ⊥ ∧ ⁅V, preOn M V A₁⁆ ⊔ ⁅V, preOn M V A₂⁆ = V) :
    commSub (⊤ : Subgroup (IntMod V hV)) A₁ ⊓ commSub (⊤ : Subgroup (IntMod V hV)) A₂ = ⊥ ∧
      commSub (⊤ : Subgroup (IntMod V hV)) A₁ ⊔ commSub (⊤ : Subgroup (IntMod V hV)) A₂ = ⊤ := by
  have hN₁ : preOn M V A₁ ≤ Subgroup.normalizer (V : Set G) := (preOn_le M V A₁).trans hMN
  have hN₂ : preOn M V A₂ ≤ Subgroup.normalizer (V : Set G) := (preOn_le M V A₂).trans hMN
  have e₁ : autI hV (preOn M V A₁) = A₁ := autOn_preOn hA₁
  have e₂ : autI hV (preOn M V A₂) = A₂ := autOn_preOn hA₂
  rw [commutator_eq_map_commSub151b hV hN₁, commutator_eq_map_commSub151b hV hN₂, e₁, e₂] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have hinj : Function.Injective (E2.valHom hV) := IntMod.val_injective
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ _ hinj] at hd1
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hd1
  · rw [← Subgroup.map_sup] at hd2
    have h2 : (commSub (⊤ : Subgroup (IntMod V hV)) A₁ ⊔ commSub (⊤ : Subgroup (IntMod V hV)) A₂).map
        (E2.valHom hV) = (⊤ : Subgroup (IntMod V hV)).map (E2.valHom hV) := by
      rw [hd2]
      exact (E2.map_valHom_top (V := V) (hV := hV)).symm
    exact Subgroup.map_injective hinj h2

end Bridge

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian2_zpowers151b {W : Type*} [CommGroup W] {s : MulAut W} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

theorem jeq_case_six151b {T M V : Subgroup G} {A₀ : Subgroup (MulAut ↥V)}
    (hV : IsElemAbelian 2 V) (hTM : T ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hSyl : IsSylowTwoOf T M) (hA0 : A₀ = Jhat (autI hV M))
    (hJne : autI hV (thompsonJi T 1) ≠ ⊥)
    (hqhat : qhatOf (autI hV M) = ((2 : ℚ) : WithTop ℚ))
    (h3 : ∀ A : Subgroup G, IsElemAbelianCorank T 1 A → autOn A V ≠ ⊥ →
        Nat.card (autOn A V) = 2 ∧ autOn A V ∈ QhatStarOn M V)
    (hJ' : autI hV (thompsonJi T 1) ≤ autI hV T ⊓ Jhat (autI hV M))
    {p : ℕ} (hp : p = 3 ∨ p = 5) (c6 : Case1517Six T M V A₀ p) :
    autI hV (thompsonJi T 1) = autI hV T ⊓ Jhat (autI hV M) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hSylb : IsSylowTwoOf (autI hV T) (autI hV M) := B2F.isSylowTwoOf_autI hV hMN hSyl
  have hTbp : IsPGroup 2 (autI hV T) := hSylb.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  subst hA0
  obtain ⟨A₁, A₂, ⟨hA₀eq, hA12, hcomm⟩, ⟨e₁⟩, ⟨e₂⟩, ⟨t, htT, hconj⟩, hdsum⟩ :
      ∃ A₁ A₂ : Subgroup (MulAut (IntMod V hV)),
        IsInternalDirect (Jhat (autI hV M)) A₁ A₂ ∧ Nonempty (↥A₁ ≃* DihedralGroup p) ∧
        Nonempty (↥A₂ ≃* DihedralGroup p) ∧
        (∃ t ∈ T, (preOn M V A₁).map (MulAut.conj t).toMonoidHom = preOn M V A₂) ∧
        IsDirectSumOfCommutators M V A₁ A₂ := by
    obtain ⟨-, A₁, A₂, h⟩ := c6
    exact ⟨A₁, A₂, h⟩
  have hA₀X : Jhat (autI hV M) ≤ autI hV M := Jhat_le (autI hV M)
  have hA₁X : A₁ ≤ autI hV M := by
    have : A₁ ≤ Jhat (autI hV M) := by rw [hA₀eq]; exact le_sup_left
    exact this.trans hA₀X
  have hA₂X : A₂ ≤ autI hV M := by
    have : A₂ ≤ Jhat (autI hV M) := by rw [hA₀eq]; exact le_sup_right
    exact this.trans hA₀X
  obtain ⟨hW12inf, hW12sup⟩ := six_bridge151b hV hMN hA₁X hA₂X hdsum
  obtain ⟨s11, s22, s12, s21⟩ := six_module151b hcomm hW12inf
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hTN htT
  have hconj' : A₁.map (MulAut.conj (convI hV ⟨t, htN⟩)).toMonoidHom = A₂ := by
    have h1 := autI_cjSub hV htN (preOn M V A₁)
    have e₁' : autI hV (preOn M V A₁) = A₁ := autOn_preOn hA₁X
    have e₂' : autI hV (preOn M V A₂) = A₂ := autOn_preOn hA₂X
    have h2 : cjSub t (preOn M V A₁) = preOn M V A₂ := hconj
    rw [e₁', h2, e₂'] at h1
    exact h1
  have hJconj : ∀ s : G, ∀ hs : s ∈ T, ∀ y ∈ autI hV (thompsonJi T 1),
      convI hV ⟨s, hTN hs⟩ * y * (convI hV ⟨s, hTN hs⟩)⁻¹ ∈ autI hV (thompsonJi T 1) := by
    intro s hs y hy
    have hsJ : s ∈ Subgroup.normalizer (thompsonJi T 1 : Set G) :=
      normalizer_le_normalizer_thompsonJi151 T 1 (Subgroup.le_normalizer hs)
    have hcj : cjSub s (thompsonJi T 1) = thompsonJi T 1 := B2F.cjSub_eq_of_mem_normalizer hsJ
    have hmap := autI_cjSub hV (hTN hs) (thompsonJi T 1)
    rw [hcj] at hmap
    have : (MulAut.conj (convI hV ⟨s, hTN hs⟩)).toMonoidHom y ∈ autI hV (thompsonJi T 1) := by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    simpa using this
  obtain ⟨A, hA, hAne⟩ : ∃ A : Subgroup G, IsElemAbelianCorank T 1 A ∧ autI hV A ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hJne
    rw [autI_thompsonJi_eq_iSup151b hV hTN 1]
    refine le_bot_iff.mp (iSup_le fun A => iSup_le fun hA => ?_)
    rw [hcon A hA]
  obtain ⟨hcard2, hmemQ⟩ := h3 A hA hAne
  have hmem' : autI hV A ∈ QhatStar (autI hV M) := (mem_QhatStarOn_iff151b hV _).mp hmemQ
  obtain ⟨r, hr, -, ⟨⟨hB2, hrB⟩, -⟩, -⟩ := QhatStar_spec hmem'
  have hr2 : r = 2 := by
    have : (r : WithTop ℚ) = ((2 : ℚ) : WithTop ℚ) := hr.symm.trans hqhat
    exact WithTop.coe_injective this
  rw [hr2] at hrB
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b ^ 2 = 1 := hB2.2.2.2 b hbB
  have hBzp : autI hV A = Subgroup.zpowers b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_
    have : Nat.card (Subgroup.zpowers b) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb2 hb1']
    have hcardB : Nat.card (autI hV A) = 2 := hcard2
    omega
  rw [hBzp] at hrB
  have hbJ : b ∈ autI hV (thompsonJi T 1) :=
    autI_mono hV (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJi T 1) hbB
  have hbJhat : b ∈ Jhat (autI hV M) :=
    (le_iSup₂_of_le (autI hV A) hmem' le_rfl : autI hV A ≤ Jhat (autI hV M)) hbB
  have hset := (card_sup_mul_card_inf_of_commute151b A₁ A₂ hcomm).2
  have hbsup : b ∈ A₁ ⊔ A₂ := by rw [← hA₀eq]; exact hbJhat
  obtain ⟨a₁, ha₁, a₂, ha₂, hab⟩ : ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, a₁ * a₂ = b := by
    have : b ∈ ((A₁ ⊔ A₂ : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := hbsup
    rw [hset] at this
    exact this
  have hsq : a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 := by
    have hcomm12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    have h2 : (a₁ * a₂) ^ 2 = a₁ ^ 2 * a₂ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hcomm12]
        _ = a₁ * a₁ * (a₂ * a₂) := by group
    rw [hab] at h2
    have h3' : a₁ ^ 2 * a₂ ^ 2 = 1 := by rw [← h2]; exact hb2
    have h4 : a₁ ^ 2 = (a₂ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h3'
    have h5 : a₁ ^ 2 ∈ A₁ ⊓ A₂ :=
      ⟨A₁.pow_mem ha₁ 2, by rw [h4]; exact A₂.inv_mem (A₂.pow_mem ha₂ 2)⟩
    rw [hA12, Subgroup.mem_bot] at h5
    refine ⟨h5, ?_⟩
    rw [h5, one_mul] at h3'
    exact h3'
  obtain ⟨hsq1, hsq2⟩ := hsq
  have hrA : ∀ a : MulAut (IntMod V hV), a ∈ autI hV M → a ≠ 1 → a ^ 2 = 1 →
      (2 : ℚ) ≤ rAV (Subgroup.zpowers a) := by
    intro a haX ha1 ha2
    have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
    have hcard : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, hord]
    have hA2 : IsA2 (autI hV M) (Subgroup.zpowers a) :=
      ⟨Subgroup.zpowers_le.mpr haX, fun h => ha1 (Subgroup.zpowers_eq_bot.mp h),
        isElemAbelian2_zpowers151b ha2⟩
    have hcub : commSeries (Subgroup.zpowers a) 3 = ⊥ :=
      commSeries_three_eq_bot_of_card_le_four151b hW hA2.2.2 (by omega)
    have hqhat' : (((2 : ℚ) : WithTop ℚ)) ≤ kq (autI hV M) 3 := hqhat.ge
    exact le_kq_iff.mp hqhat' _ hA2 hcub
  have hrAeq : ∀ a : MulAut (IntMod V hV), a ≠ 1 → a ^ 2 = 1 →
      rAV (Subgroup.zpowers a) = (rkIdx (fixV (Subgroup.zpowers a)) : ℚ) := by
    intro a ha1 ha2
    rw [rAV_zpowers ha1 ha2, rkIdx_fixV_zpowers]
  set tb := convI hV ⟨t, htN⟩ with htb
  have hJc : ∀ y ∈ autI hV (thompsonJi T 1), tb * y * tb⁻¹ ∈ autI hV (thompsonJi T 1) :=
    fun y hy => hJconj t htT y hy
  have hJc' : ∀ y ∈ autI hV (thompsonJi T 1), tb⁻¹ * y * tb ∈ autI hV (thompsonJi T 1) := by
    intro y hy
    have h1 := hJconj t⁻¹ (T.inv_mem htT) y hy
    have h2 : convI hV ⟨t⁻¹, hTN (T.inv_mem htT)⟩ = tb⁻¹ := by
      have : (⟨t⁻¹, hTN (T.inv_mem htT)⟩ : Subgroup.normalizer (V : Set G)) = ⟨t, htN⟩⁻¹ := rfl
      rw [this, map_inv]
    rw [h2] at h1
    simpa using h1
  have hconjmem : ∀ x ∈ A₁, tb * x * tb⁻¹ ∈ A₂ := by
    intro x hx
    rw [← hconj']
    exact ⟨x, hx, by simp⟩
  have hconjmem' : ∀ y ∈ A₂, ∃ x ∈ A₁, tb * x * tb⁻¹ = y := by
    intro y hy
    rw [← hconj'] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  have hcJ : ∃ c₁ ∈ A₁, ∃ c₂ ∈ A₂, c₁ ∈ autI hV (thompsonJi T 1) ∧
      c₂ ∈ autI hV (thompsonJi T 1) ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ ^ 2 = 1 ∧ c₂ ^ 2 = 1 := by
    by_cases ha1 : a₁ = 1
    · have hbeq : b = a₂ := by rw [← hab, ha1, one_mul]
      have ha2 : a₂ ≠ 1 := by rw [← hbeq]; exact hb1'
      obtain ⟨c, hcA, hcb⟩ := hconjmem' a₂ ha₂
      have hcJ : c ∈ autI hV (thompsonJi T 1) := by
        have := hJc' b hbJ
        rw [hbeq, ← hcb] at this
        simpa [mul_assoc] using this
      refine ⟨c, hcA, a₂, ha₂, hcJ, hbeq ▸ hbJ, ?_, ha2, ?_, hsq2⟩
      · rintro rfl
        apply ha2
        rw [← hcb]
        simp
      · have : (tb * c * tb⁻¹) ^ 2 = tb * c ^ 2 * tb⁻¹ := by
          rw [pow_two, pow_two]
          group
        rw [hcb, hsq2] at this
        have h1 : tb * c ^ 2 * tb⁻¹ = 1 := this.symm
        simpa using h1
    · by_cases ha2 : a₂ = 1
      · have hbeq : b = a₁ := by rw [← hab, ha2, mul_one]
        refine ⟨a₁, ha₁, tb * a₁ * tb⁻¹, hconjmem a₁ ha₁, hbeq ▸ hbJ, ?_, ha1, ?_, hsq1, ?_⟩
        · have := hJc b hbJ
          rw [hbeq] at this
          exact this
        · intro h
          apply ha1
          have : tb * a₁ * tb⁻¹ = 1 := h
          simpa using this
        · have : (tb * a₁ * tb⁻¹) ^ 2 = tb * a₁ ^ 2 * tb⁻¹ := by
            rw [pow_two, pow_two]
            group
          rw [this, hsq1]
          simp
      · exfalso
        have hr1 := hrA a₁ (hA₁X ha₁) ha1 hsq1
        have hr2 := hrA a₂ (hA₂X ha₂) ha2 hsq2
        rw [hrAeq a₁ ha1 hsq1] at hr1
        rw [hrAeq a₂ ha2 hsq2] at hr2
        have hmul := rkIdx_fixV_mul151b hW12sup hW12inf (fun w hw => s11 a₁ ha₁ w hw)
          (fun w hw => s22 a₂ ha₂ w hw) (fun w hw => s12 a₁ ha₁ w hw) (fun w hw => s21 a₂ ha₂ w hw)
        rw [hrAeq b hb1' hb2] at hrB
        rw [hab] at hmul
        have hrB' : rkIdx (fixV (Subgroup.zpowers b)) = 2 := by exact_mod_cast hrB
        have hr1' : 2 ≤ rkIdx (fixV (Subgroup.zpowers a₁)) := by exact_mod_cast hr1
        have hr2' : 2 ≤ rkIdx (fixV (Subgroup.zpowers a₂)) := by exact_mod_cast hr2
        omega
  obtain ⟨c₁, hc₁A, c₂, hc₂A, hc₁J, hc₂J, hc₁1, hc₂1, hc₁2, hc₂2⟩ := hcJ
  have hcommE : ∀ x ∈ Subgroup.zpowers c₁, ∀ y ∈ Subgroup.zpowers c₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    have h12 : Commute c₁ c₂ := hcomm c₁ hc₁A c₂ hc₂A
    exact (h12.zpow_zpow m n).eq
  have hcard1 : Nat.card (Subgroup.zpowers c₁) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc₁2 hc₁1]
  have hcard2' : Nat.card (Subgroup.zpowers c₂) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc₂2 hc₂1]
  have hinfE : Subgroup.zpowers c₁ ⊓ Subgroup.zpowers c₂ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have h1 : x ∈ A₁ := Subgroup.zpowers_le.mpr hc₁A hx.1
    have h2 : x ∈ A₂ := Subgroup.zpowers_le.mpr hc₂A hx.2
    have : x ∈ A₁ ⊓ A₂ := ⟨h1, h2⟩
    rwa [hA12, Subgroup.mem_bot] at this
  have hcardE : Nat.card ↥(Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂) = 4 := by
    have := (card_sup_mul_card_inf_of_commute151b _ _ hcommE).1
    rw [hinfE, Subgroup.card_bot, hcard1, hcard2'] at this
    omega
  have hEJ : Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ ≤ autI hV (thompsonJi T 1) :=
    sup_le (Subgroup.zpowers_le.mpr hc₁J) (Subgroup.zpowers_le.mpr hc₂J)
  have hA₁card : Nat.card A₁ = 2 * p := by rw [Nat.card_congr e₁.toEquiv, DihedralGroup.nat_card]
  have hA₂card : Nat.card A₂ = 2 * p := by rw [Nat.card_congr e₂.toEquiv, DihedralGroup.nat_card]
  have hA₀card : Nat.card ↥(Jhat (autI hV M)) = 4 * p ^ 2 := by
    have := (card_sup_mul_card_inf_of_commute151b A₁ A₂ hcomm).1
    rw [hA12, Subgroup.card_bot, hA₁card, hA₂card, ← hA₀eq] at this
    nlinarith
  have hFcard : Nat.card ↥(autI hV T ⊓ Jhat (autI hV M)) ≤ 4 := by
    have hFp : IsPGroup 2 ↥(autI hV T ⊓ Jhat (autI hV M)) := hTbp.to_inf_left
    have hdvd : Nat.card ↥(autI hV T ⊓ Jhat (autI hV M)) ∣ 4 * p ^ 2 :=
      hA₀card ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 2 := by
      by_contra hgt
      have h1 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h2 := h1.trans hdvd
      rcases hp with rfl | rfl <;> omega
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  exact Subgroup.eq_of_le_of_card_ge hJ' (by
    have := Subgroup.card_le_of_le hEJ
    omega)

theorem lemma15113Four_of_cases151b {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (h157 : Lemma1517Concl T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hred : IsTwoReducedIn M (V154 T Mc M))
    (h110 : Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 3 →
      Nonempty (↥(autOn M (V154 T Mc M)) ≃* S152N.W3))
    (h5 : ∀ hV : IsElemAbelian 2 (V154 T Mc M),
      Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 5 →
      ∀ E : Subgroup (MulAut (IntMod (V154 T Mc M) hV)), E ≤ autI hV T → IsElemAbelian2 E →
        Nat.card E ≤ 4)
    (h2 : ⁅V154 T Mc M, thompsonJi T 1⁆ ≠ ⊥) : Lemma15113Four T Mc M := by
  have hV : IsElemAbelian 2 (V154 T Mc M) := hred.2.2.1
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMN
  have hSyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 h.sylow hTM
  have hJ1N : thompsonJi T 1 ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (iSup₂_le fun _ hA => hA.1).trans hTN
  have hJne : autI hV (thompsonJi T 1) ≠ ⊥ := by
    intro hbot
    exact h2 (commutator_eq_bot_of_le_centralizer ((autI_eq_bot_iff hV hJ1N).mp hbot))
  have h3 := lemma15113Three_of_cases151b h hM h157 h158 h159 hred h110 h5
  have hA0 : mBar0 T Mc M = Jhat (autI hV M) := JhatOn_eq hV
  exact four_of_cases151b hV hTM hMN hSyl hA0 hJne h157.1 h3
    (fun p hp hc3 c6 h3' hJ' => by
      have hq : qhatOn M (V154 T Mc M) = 2 := by
        rcases h158 with h1 | ⟨h3c, -⟩
        · exact h1.1
        · exact absurd h3c hc3
      have hqhat : qhatOf (autI hV M) = ((2 : ℚ) : WithTop ℚ) := by
        rw [← qhatOn_eq_qhatOf151b hV, hq]
        norm_cast
      exact jeq_case_six151b hV hTM hMN hSyl hA0 hJne hqhat h3' hJ' hp c6)

end Main

end CFSG.Quasithin
