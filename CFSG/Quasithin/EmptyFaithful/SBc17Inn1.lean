module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn0
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoZIn_le_pCoreOf_of_center_bot {J : Subgroup G} {S : Type*} [Group S] {α : ↥J →* S}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥J) (hZ : Subgroup.center S = ⊥) :
    oTwoZIn J ≤ pCoreOf 2 J := by
  intro x hx
  obtain ⟨hxJ, hxc⟩ := mem_oTwoZIn_iff.mp hx
  have h1 : α ⟨x, hxJ⟩ ∈ Subgroup.center S := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨ℓ, rfl⟩ := hα g
    have h2 := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk ℓ)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h2
    have h3 : α ((ℓ * ⟨x, hxJ⟩)⁻¹ * (⟨x, hxJ⟩ * ℓ)) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact h2
    rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h3
    exact h3
  rw [hZ, Subgroup.mem_bot] at h1
  exact (map_eq_one_iff_mem_pCoreOf hker ⟨x, hxJ⟩).mp h1

theorem act_five {J M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) {a : G} (haM : a ∈ M ⊓ J)
    (ha5 : orderOf a = 5) :
    conjAct V ⟨a, hJV haM.2⟩ ∈ autOn (M ⊓ J) V ∧ orderOf (conjAct V ⟨a, hJV haM.2⟩) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨mem_autOn_iff.mpr ⟨a, hJV haM.2, haM, rfl⟩, ?_⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨a, hJV haM.2⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 5 = 1 :=
      Subtype.ext (by simp [← ha5, pow_orderOf_eq_one])
    rw [this, map_one]
  · intro h1
    have h2 : actOn hJV ⟨a, haM.2⟩ = 1 := Subtype.ext h1
    have h3 := (actOn_eq_one_iff hJV ⟨a, haM.2⟩).mp h2
    exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) ha5
      (hD ⟨haM.2, h3⟩)

theorem false_of_hat6 {M J : Subgroup G} (h : IsHatA6Block J ∧ M.relIndex J = 15) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  obtain ⟨⟨-, hhat, -⟩, hidx⟩ := h
  obtain ⟨-, hc3, ⟨e⟩⟩ := hhat
  have h360 : Nat.card ((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 360 :=
    SBc11.card_of_isAlt_six ⟨e⟩
  have h1080 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)),
      h360, hc3]
  refine no_five_of_relIndex (by rw [hidx]; decide) (not_twentyfive_dvd_card J ?_) haM ha5
  rw [h1080]
  decide

theorem false_of_excA7 {M J : Subgroup G} (h : IsExcA7Block J ∧ M.relIndex J = 35) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  obtain ⟨⟨-, ⟨α, hα, hker⟩, -⟩, hidx⟩ := h
  have h2520 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 2520 := by
    have e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(alternatingGroup (Fin 7)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  refine no_five_of_relIndex (by rw [hidx]; decide) (not_twentyfive_dvd_card J ?_) haM ha5
  rw [h2520]
  decide

theorem false_of_g2 {J : Subgroup G} (h : IsG2Block J) {a : G} (haJ : a ∈ J)
    (ha5 : orderOf a = 5) : False := by
  obtain ⟨-, hpsu, -⟩ := h
  have h6048 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 6048 := SBc11.card_of_isPSU_three_three hpsu
  have h1 := not_five_dvd_card J (by rw [h6048]; decide)
  apply h1
  have := orderOf_dvd_natCard (⟨a, haJ⟩ : ↥J)
  rwa [Subgroup.orderOf_mk, ha5] at this

omit [Finite G] in
theorem autOn_mono_left {A B V : Subgroup G} (h : A ≤ B) : autOn A V ≤ autOn B V :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem image_act_five {J R M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) {Y : Type*} [Group Y]
    (e : ↥(autOn (J ⊔ R) V) ≃* Y) {Wsub : Subgroup Y}
    (hmap : ((autOn (M ⊓ J) V).subgroupOf (autOn (J ⊔ R) V)).map e.toMonoidHom = Wsub) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : ∃ σ ∈ Wsub, σ ^ 5 = 1 ∧ σ ≠ 1 := by
  obtain ⟨hmem, hord⟩ := act_five hJV hD haM ha5
  have hle : autOn (M ⊓ J) V ≤ autOn (J ⊔ R) V := autOn_mono_left (inf_le_right.trans le_sup_left)
  set x : ↥(autOn (J ⊔ R) V) := ⟨conjAct V ⟨a, hJV haM.2⟩, hle hmem⟩ with hx
  have hxmem : x ∈ (autOn (M ⊓ J) V).subgroupOf (autOn (J ⊔ R) V) := hmem
  have hx5 : x ^ 5 = 1 := by
    apply Subtype.ext
    show (conjAct V ⟨a, hJV haM.2⟩) ^ 5 = 1
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hx1 : x ≠ 1 := by
    intro h
    have h' : conjAct V ⟨a, hJV haM.2⟩ = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hord
    omega
  refine ⟨e x, ?_, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hxmem
  · rw [← map_pow, hx5, map_one]
  · intro h
    exact hx1 (e.injective (h.trans (map_one e).symm))

theorem false_of_a7_43 {J R M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J)
    (h : ∃ (e : ↥(autOn (J ⊔ R) V) ≃* Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))),
      IsPartitionOfType P {4, 3} ∧
        ((autOn (M ⊓ J) V).subgroupOf (autOn (J ⊔ R) V)).map e.toMonoidHom =
          MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  obtain ⟨e, P, hP, hmap⟩ := h
  obtain ⟨σ, hσ, hσ5, hσ1⟩ := image_act_five hJV hD e hmap haM ha5
  exact hσ1 (eq_one_of_stab_type_four_three hP hσ.1 hσ5)

theorem false_of_a7_2221 {J R M V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J)
    (h : ∃ (e : ↥(autOn (J ⊔ R) V) ≃* Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))),
      IsPartitionOfType P {2, 2, 2, 1} ∧
        ((autOn (M ⊓ J) V).subgroupOf (autOn (J ⊔ R) V)).map e.toMonoidHom =
          MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) {a : G}
    (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  obtain ⟨e, P, hP, hmap⟩ := h
  obtain ⟨σ, hσ, hσ5, hσ1⟩ := image_act_five hJV hD e hmap haM ha5
  exact hσ1 (eq_one_of_stab_type_two_two_two_one hP hσ.1 hσ5)

theorem false_of_alt_small {J R M V : Subgroup G} (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) {n : ℕ} (hn : n ≤ 6)
    {α : ↥J →* alternatingGroup (Fin n)} (hker : α.ker = CFSG.pCore 2 ↥J) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap)
    (hrel : ∀ (k : G) (hk : k ∈ J) (hk' : t * k * t⁻¹ ∈ J),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ J) V = autOn J V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haM : a ∈ M ⊓ J) (ha5 : orderOf a = 5) : False := by
  have haJ : a ∈ J := haM.2
  have haV : a ∈ Subgroup.normalizer (V : Set G) := hJV haJ
  have hmem : conjAct V ⟨a, haV⟩ ∈ autOn (M ⊓ J) V := mem_autOn_iff.mpr ⟨a, haV, haM, rfl⟩
  rw [hMK] at hmem
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ = conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ :=
    Subgroup.mem_centralizer_iff.mp hmem.2 _ (mem_autOn_iff.mpr ⟨t, htV, htR, rfl⟩)
  have hta : t * a⁻¹ * t⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hR htR) a⁻¹).mp (J.inv_mem haJ)
  have hw : a * (t * a⁻¹ * t⁻¹) ∈ J := J.mul_mem haJ hta
  have hwV : a * (t * a⁻¹ * t⁻¹) ∈ Subgroup.normalizer (V : Set G) := hJV hw
  have hw1 : actOn hJV ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := by
    apply Subtype.ext
    show conjAct V ⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ = 1
    have e : (⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨a, haV⟩ * (⟨t, htV⟩ * ⟨a, haV⟩⁻¹ * ⟨t, htV⟩⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h2 : conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ = conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ :=
      hcomm.symm
    calc conjAct V ⟨a, haV⟩ * (conjAct V ⟨t, htV⟩ * (conjAct V ⟨a, haV⟩)⁻¹ *
          (conjAct V ⟨t, htV⟩)⁻¹) = (conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩) *
            (conjAct V ⟨a, haV⟩)⁻¹ * (conjAct V ⟨t, htV⟩)⁻¹ := by group
      _ = (conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩) * (conjAct V ⟨a, haV⟩)⁻¹ *
            (conjAct V ⟨t, htV⟩)⁻¹ := by rw [h2]
      _ = 1 := by group
  have hwC := (actOn_eq_one_iff hJV _).mp hw1
  have hwO : a * (t * a⁻¹ * t⁻¹) ∈ pCoreOf 2 J := hD ⟨hw, hwC⟩
  have hα1 : α ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := (map_eq_one_iff_mem_pCoreOf hker _).mpr hwO
  have hsplit : (⟨a * (t * a⁻¹ * t⁻¹), hw⟩ : ↥J) = ⟨a, haJ⟩ * ⟨t * a⁻¹ * t⁻¹, hta⟩ := rfl
  rw [hsplit, map_mul] at hα1
  have hrel' := hrel a⁻¹ (J.inv_mem haJ) hta
  have hinvα : (α ⟨a⁻¹, J.inv_mem haJ⟩ : alternatingGroup (Fin n)) = (α ⟨a, haJ⟩)⁻¹ := by
    have : (⟨a⁻¹, J.inv_mem haJ⟩ : ↥J) = (⟨a, haJ⟩ : ↥J)⁻¹ := rfl
    rw [this, map_inv]
  rw [hinvα] at hrel'
  set c : Equiv.Perm (Fin n) := (α ⟨a, haJ⟩ : Equiv.Perm (Fin n)) with hc
  have h1 : c * (σ * c⁻¹ * σ⁻¹) = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n))) hα1
    simpa [hc, hrel'] using this
  have hcomm' : c * σ = σ * c := by
    have : c * σ * c⁻¹ * σ⁻¹ = 1 := by
      calc c * σ * c⁻¹ * σ⁻¹ = c * (σ * c⁻¹ * σ⁻¹) := by group
        _ = 1 := h1
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hc5 : c ^ 5 = 1 := by
    have h5 : (⟨a, haJ⟩ : ↥J) ^ 5 = 1 := Subtype.ext (by simp [← ha5, pow_orderOf_eq_one])
    have := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n)))
      (show (α ⟨a, haJ⟩) ^ 5 = 1 by rw [← map_pow, h5, map_one])
    simpa [hc] using this
  have hc1 : c = 1 := eq_one_of_commute_swap hn hσ hcomm' hc5
  have hα2 : α ⟨a, haJ⟩ = 1 := Subtype.ext (by simpa [hc] using hc1)
  exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) ha5
    ((map_eq_one_iff_mem_pCoreOf hker ⟨a, haJ⟩).mp hα2)

end SBc17

end CFSG.Quasithin
