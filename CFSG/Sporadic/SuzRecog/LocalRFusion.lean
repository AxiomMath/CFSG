module

public import CFSG.Sporadic.SuzRecog.LocalRFusionModel
public import CFSG.Sporadic.SuzRecog.Rigid

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.Open
  CFSG.LargeExtraspecial CFSG.ABGLocalTools CFSG.Sporadic.SuzRecog
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem card_centralizer_mulEquiv {Y : Type*} [Group Y] (e : G ≃* Y) (u : G) :
    Nat.card (centralizer ({e u} : Set Y)) = Nat.card (centralizer ({u} : Set G)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)).symm
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_centralizer_of_isConj {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (card_centralizer_mulEquiv (MulAut.conj c) a).symm

theorem eq_of_isConj_of_mem_center {a b : G} (h : IsConj a b) (hb : b ∈ center G) : a = b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hcb := mem_center_iff.mp hb c
  calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
    _ = c⁻¹ * (b * c) := by rw [hc, mul_assoc]
    _ = c⁻¹ * (c * b) := by rw [hcb]
    _ = b := by group

theorem mem_of_isConj_of_mem {N : Subgroup G} [N.Normal] {a b : G} (h : IsConj a b)
    (hb : b ∈ N) : a ∈ N := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have := Normal.conj_mem inferInstance _ hb c⁻¹
  simpa [mul_assoc] using this

variable [Finite G]

theorem exists_mem_normalizer_of_lt {P V : Subgroup G} (hP : IsPGroup 2 P) (hlt : V < P) :
    ∃ l ∈ P, l ∉ V ∧ ∀ v ∈ V, l * v * l⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set VP : Subgroup P := V.subgroupOf P with hVP
  have hne : VP < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    obtain ⟨x, hxP, hxV⟩ := IsConcreteLE.exists_of_lt hlt
    have hx : (⟨x, hxP⟩ : P) ∈ VP := h ▸ mem_top _
    exact hxV (mem_subgroupOf.mp hx)
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' := Group.normalizerCondition_of_isNilpotent (G := P) VP hne
  obtain ⟨y, hyN, hyV⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨y, y.2, fun h => hyV (mem_subgroupOf.mpr h), fun v hv => ?_⟩
  have hvP : v ∈ P := hlt.le hv
  have h := (mem_normalizer_iff.mp hyN ⟨v, hvP⟩).mp (mem_subgroupOf.mpr hv)
  rw [mem_subgroupOf] at h
  simpa using h

omit [Finite G] in
theorem exists_isSylowOf_le {V K : Subgroup G} (hVK : V ≤ K) (hV : IsPGroup 2 V) :
    ∃ P, IsSylowOf 2 P K ∧ V ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hV.comap_of_injective K.subtype K.subtype_injective).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hVK hx⟩, hQ hx, rfl⟩

theorem factorization_61440 : (61440 : ℕ).factorization 2 = 12 := by
  rw [show (61440 : ℕ) = 2 ^ 12 * 15 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_3317760 : (3317760 : ℕ).factorization 2 = 13 := by
  rw [show (3317760 : ℕ) = 2 ^ 13 * 405 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end General

section Fusion

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

omit [Finite G] in
theorem t1Elt_mem_center : t1Elt ∈ center ↥(invE 1) := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (invE_le g.2).2

omit [Finite G] in
theorem t1Elt_ne_one : t1Elt ≠ 1 := fun h =>
  suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)

omit [Finite G] in
theorem map_zM (σ : S.M ≃* ↥(invE 1)) : σ S.zM = t1Elt :=
  map_zM_eq S σ t1Elt_mem_center t1Elt_ne_one

@[expose] noncomputable def Q₁ : Subgroup ↥(invE 1) := coord_qVec.Q.subgroupOf (invE 1)

omit [Finite G] in
theorem Q₁_normal : (Q₁ : Subgroup ↥(invE 1)).Normal :=
  (normal_subgroupOf_iff_le_normalizer Q_le_invE).mpr (invE_le.trans inf_le_left)

omit [Finite G]
  in
theorem isPGroup_Q₁ : IsPGroup 2 (Q₁ : Subgroup ↥(invE 1)) :=
  coord_qVec.isPGroup_Q.comap_of_injective (invE 1).subtype (invE 1).subtype_injective

omit [Finite G] in
theorem qVec_mem_Q₁ {v : ℕ} (hv : v < 64) :
    (⟨qVec v, qVec_mem_invE v⟩ : ↥(invE 1)) ∈ (Q₁ : Subgroup ↥(invE 1)) := by
  rw [Q₁, mem_subgroupOf]
  exact coord_qVec.mem_Q_iff.mpr ⟨v, hv, 0, by norm_num, by rw [pow_zero, mul_one]⟩

omit [Finite G] in
theorem mem_QG_of_map_mem (σ : S.M ≃* ↥(invE 1)) {m : S.M}
    (hm : σ m ∈ (Q₁ : Subgroup ↥(invE 1))) : (m : G) ∈ S.QG := by
  have : (Q₁ : Subgroup ↥(invE 1)).Normal := Q₁_normal
  have hle := S.le_of_normal ((Q₁ : Subgroup ↥(invE 1)).comap σ.toMonoidHom)
    (Normal.comap inferInstance _) (isPGroup_Q₁.comap_of_injective _ σ.injective)
  exact ⟨m, hle hm, rfl⟩

omit
  [Finite G] in
theorem card_M (σ : S.M ≃* ↥(invE 1)) : Nat.card S.M = 3317760 := by
  rw [Nat.card_congr σ.toEquiv, card_invE (i := 1) (by norm_num)]
  rfl

omit
  [Finite G] in
theorem card_centralizer_inf (σ : S.M ≃* ↥(invE 1)) (t : S.M) :
    Nat.card ↥(centralizer ({(t : G)} : Set G) ⊓ centralizer ({S.z} : Set G)) =
      Nat.card (centralizer ({σ t} : Set ↥(invE 1))) := by
  rw [card_centralizer_mulEquiv σ t, card_centralizer_coe S.M t, inf_comm]

omit
  [Finite G] in
theorem isConj_of_isConj_map (σ : S.M ≃* ↥(invE 1)) {a b : S.M} (h : IsConj (σ a) (σ b)) :
    IsConj (a : G) (b : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨((σ.symm c : S.M) : G), ?_⟩
  have hab : σ.symm c * a * (σ.symm c)⁻¹ = b := σ.injective (by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc])
  exact congrArg Subtype.val hab

theorem sylow_of_isConj_lambda4 (σ : S.M ≃* ↥(invE 1)) {t : S.M} (ht : IsConj (σ t) lambda4) :
    IsSylowOf 2 (centralizer ({(t : G)} : Set G) ⊓ centralizer ({S.z} : Set G))
        (centralizer ({(t : G)} : Set G)) ∧
      Nat.card ↥(centralizer ({(t : G)} : Set G) ⊓ centralizer ({S.z} : Set G)) = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := centralizer ({(t : G)} : Set G) ⊓ centralizer ({S.z} : Set G) with hV
  have hcard : Nat.card V = 512 := by
    rw [hV, card_centralizer_inf S σ t, card_centralizer_of_isConj ht,
      card_centralizer_lambda4]
  obtain ⟨c, hc⟩ := isConj_iff.mp ht
  have hσz := map_zM S σ
  have hσt : σ t = c⁻¹ * lambda4 * c := by rw [← hc]; group
  have hcent : ∀ d : ↥(invE 1), d⁻¹ * t1Elt * d = t1Elt := fun d => by
    have := mem_center_iff.mp t1Elt_mem_center d
    calc d⁻¹ * t1Elt * d = d⁻¹ * (t1Elt * d) := by group
      _ = d⁻¹ * (d * t1Elt) := by rw [this]
      _ = t1Elt := by group
  have hconj4 : ∀ a : ↥(invE 1), (c⁻¹ * a * c) ^ 4 = c⁻¹ * a ^ 4 * c := fun a => by
    rw [show c⁻¹ * a * c = c⁻¹ * a * c⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have hpow : ∀ v ∈ V, v ^ 4 = 1 ∨ v ^ 4 = S.z := by
    intro v hv
    set v' : S.M := ⟨v, hv.2⟩ with hv'
    have hvt : v' * t = t * v' := Subtype.ext (mem_centralizer_singleton_iff.mp hv.1)
    set w := c * σ v' * c⁻¹ with hw
    have hwl : w * lambda4 = lambda4 * w := by
      rw [← hc, hw]
      calc c * σ v' * c⁻¹ * (c * σ t * c⁻¹) = c * σ (v' * t) * c⁻¹ := by rw [map_mul]; group
        _ = c * σ (t * v') * c⁻¹ := by rw [hvt]
        _ = c * σ t * c⁻¹ * (c * σ v' * c⁻¹) := by rw [map_mul]; group
    have h4 := pow_four_of_commute_lambda4 w.2 (congrArg Subtype.val hwl)
    have hw4 : w ^ 4 = 1 ∨ w ^ 4 = t1Elt := by
      rcases h4 with h | h
      · exact Or.inl (Subtype.ext (by simpa using h))
      · exact Or.inr (Subtype.ext (by simpa [t1Elt] using h))
    have hσv : σ v' = c⁻¹ * w * c := by rw [hw]; group
    rcases hw4 with h | h
    · left
      have : v' ^ 4 = 1 := σ.injective (by rw [map_pow, hσv, hconj4, h, map_one]; group)
      simpa [hv'] using congrArg Subtype.val this
    · right
      have : v' ^ 4 = S.zM := σ.injective (by rw [map_pow, hσv, hconj4, h, hcent, hσz])
      simpa [hv'] using congrArg Subtype.val this
  obtain ⟨w, hwC, hwl, hw4⟩ := exists_pow_four_lambda4
  set w' : ↥(invE 1) := ⟨w, hwC⟩ with hw'
  set v' : S.M := σ.symm (c⁻¹ * w' * c) with hv'
  have hv'V : (v' : G) ∈ V := by
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, v'.2⟩
    have hw'l : w' * lambda4 = lambda4 * w' := Subtype.ext hwl
    have : v' * t = t * v' := σ.injective (by
      rw [map_mul, map_mul, hv', MulEquiv.apply_symm_apply, hσt]
      calc c⁻¹ * w' * c * (c⁻¹ * lambda4 * c) = c⁻¹ * (w' * lambda4) * c := by group
        _ = c⁻¹ * (lambda4 * w') * c := by rw [hw'l]
        _ = c⁻¹ * lambda4 * c * (c⁻¹ * w' * c) := by group)
    exact congrArg Subtype.val this
  have hv'4 : (v' : G) ^ 4 = S.z := by
    have hw'4 : w' ^ 4 = t1Elt := Subtype.ext (by simpa [hw', t1Elt] using hw4)
    have : v' ^ 4 = S.zM := σ.injective (by
      rw [map_pow, hv', MulEquiv.apply_symm_apply, hconj4, hw'4, hcent, hσz])
    simpa using congrArg Subtype.val this
  have hVK : V ≤ centralizer ({(t : G)} : Set G) := inf_le_left
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 9) (by rw [hcard]; norm_num)
  obtain ⟨P, hP, hVP⟩ := exists_isSylowOf_le hVK hV2
  refine ⟨?_, hcard⟩
  by_cases hVPe : V = P
  · rw [hVPe]
    exact hP
  · obtain ⟨l, hlP, hlV, hlN⟩ :=
      exists_mem_normalizer_of_lt hP.isPGroup (lt_of_le_of_ne hVP hVPe)
    exfalso
    have hlz : l * S.z * l⁻¹ = S.z := by
      rcases hpow _ (hlN _ hv'V) with h | h
      · rw [conj_pow, hv'4] at h
        exfalso
        apply S.z_ne_one
        calc S.z = l⁻¹ * (l * S.z * l⁻¹) * l := by group
          _ = 1 := by rw [h]; group
      · rwa [conj_pow, hv'4] at h
    apply hlV
    refine ⟨hP.le hlP, mem_centralizer_singleton_iff.mpr ?_⟩
    calc l * S.z = l * S.z * l⁻¹ * l := by group
      _ = S.z * l := by rw [hlz]

theorem not_isConj_z_of_isConj_lambda4 (σ : S.M ≃* ↥(invE 1)) {t : S.M}
    (ht : IsConj (σ t) lambda4) : ¬ IsConj (t : G) S.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  obtain ⟨hsyl, hcard⟩ := sylow_of_isConj_lambda4 S σ ht
  have h1 := hsyl.card_eq
  have h2 : Nat.card (centralizer ({(t : G)} : Set G)) = 3317760 := by
    rw [card_centralizer_of_isConj hc]
    exact card_M S σ
  rw [h2, hcard, factorization_3317760] at h1
  norm_num at h1

theorem isConj_lambda3 (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* ↥(invE 1)) :
    IsConj ((σ.symm lambda3 : S.M) : G) S.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀, hne₀⟩ := hNWC
  have h5 : 5 ≤ Module.finrank (ZMod 2) S.Qt := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
    norm_num
  have hswap : ∀ u ∈ S.QG, orderOf u = 2 → IsConj S.z u := fun u hu hu2 =>
    CFSG.Sporadic.Co1Patterson.isConj_of_mem_QG_of_omega S h5 hΩ hg₀ hne₀ hu hu2
  have hσz := map_zM S σ
  have : (Q₁ : Subgroup ↥(invE 1)).Normal := Q₁_normal
  by_contra hne
  have hQ : ∀ y (hy : y ∈ S.M), orderOf y = 2 → IsConj S.z y → y ∈ S.QG := by
    intro y hy hy2 hyz
    set y' : S.M := ⟨y, hy⟩ with hy'
    have hy'2 : orderOf (σ y') = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hy2
    obtain ⟨i, hi, hc⟩ := exists_isConj_lambda (σ y') hy'2
    interval_cases i
    · have h1 : σ y' = t1Elt := eq_of_isConj_of_mem_center hc t1Elt_mem_center
      have h2 : y' = S.zM := σ.injective (by rw [h1, hσz])
      rw [show y = S.z from congrArg Subtype.val h2]
      exact S.z_mem_QG
    · exact mem_QG_of_map_mem S σ (mem_of_isConj_of_mem hc (qVec_mem_Q₁ (by norm_num)))
    · exfalso
      apply hne
      have hc' : IsConj (σ y') (σ (σ.symm lambda3)) := by
        rw [MulEquiv.apply_symm_apply]
        exact hc
      exact (hyz.trans (isConj_of_isConj_map S σ hc')).symm
    · exact absurd hyz.symm (not_isConj_z_of_isConj_lambda4 S σ hc)
  set x' : S.M := σ.symm lambda2 with hx'
  have hx'Q : (x' : G) ∈ S.QG := mem_QG_of_map_mem S σ (by
    rw [hx', MulEquiv.apply_symm_apply]
    exact qVec_mem_Q₁ (by norm_num))
  have hx'2 : orderOf (x' : G) = 2 := by
    rw [Subgroup.orderOf_coe, hx', MulEquiv.orderOf_eq]
    exact orderOf_lambdaElt (i := 1) (by norm_num)
  have hxz : IsConj S.z (x' : G) := hswap _ hx'Q hx'2
  set K := centralizer ({(x' : G)} : Set G) ⊓ centralizer ({S.z} : Set G) with hK
  have hKcard : Nat.card K = 61440 := by
    rw [hK, card_centralizer_inf S σ x', hx', MulEquiv.apply_symm_apply,
      card_centralizer_lambda2]
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 K
  have hTcard : Nat.card T = 4096 := by
    rw [hT.card_eq, hKcard, factorization_61440]
    norm_num
  have hCx : Nat.card (centralizer ({(x' : G)} : Set G)) = 3317760 := by
    rw [← card_centralizer_of_isConj hxz]
    exact card_M S σ
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_le (hT.le.trans inf_le_left) hT.isPGroup
  have hPcard : Nat.card P = 8192 := by
    rw [hP.card_eq, hCx, factorization_3317760]
    norm_num
  have hTP' : T < P := lt_of_le_of_ne hTP fun h => by
    rw [h, hPcard] at hTcard
    omega
  obtain ⟨l, hlP, hlT, hlN⟩ := exists_mem_normalizer_of_lt hP.isPGroup hTP'
  obtain ⟨huu, hvv, hux, hvx, huv⟩ := q4_q8_facts
  have tr : ∀ a b : ↥(invE 1), (a : Equiv.Perm (Fin 1782)) = b →
      ((σ.symm a : S.M) : G) = ((σ.symm b : S.M) : G) := fun a b h => by
    rw [Subtype.ext h]
  set u₀ : ↥(invE 1) := ⟨qVec 4, qVec_mem_invE 4⟩ with hu₀
  set v₀ : ↥(invE 1) := ⟨qVec 8, qVec_mem_invE 8⟩ with hv₀
  set u : G := ((σ.symm u₀ : S.M) : G) with hu
  set v : G := ((σ.symm v₀ : S.M) : G) with hv
  have hσt1 : σ.symm t1Elt = S.zM := by rw [← hσz, MulEquiv.symm_apply_apply]
  have huu' : u * u = 1 := by simpa [hu, map_mul] using tr (u₀ * u₀) 1 huu
  have hvv' : v * v = 1 := by simpa [hv, map_mul] using tr (v₀ * v₀) 1 hvv
  have hux' : u * x' = x' * u := by
    simpa [hu, hx', map_mul] using tr (u₀ * lambda2) (lambda2 * u₀) hux
  have hvx' : v * x' = x' * v := by
    simpa [hv, hx', map_mul] using tr (v₀ * lambda2) (lambda2 * v₀) hvx
  have huv' : u * v * u * v = S.z := by
    have h := tr (u₀ * v₀ * u₀ * v₀) t1Elt huv
    rw [hσt1] at h
    simpa [hu, hv, map_mul] using h
  have hz1 := S.z_ne_one
  have hu1 : u ≠ 1 := fun h => hz1 (by rw [← huv', h, one_mul, mul_one, hvv'])
  have hv1 : v ≠ 1 := fun h => hz1 (by rw [← huv', h, mul_one, mul_one, huu'])
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu') hu1
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv') hv1
  have huQ : u ∈ S.QG := mem_QG_of_map_mem S σ (by
    rw [MulEquiv.apply_symm_apply]
    exact qVec_mem_Q₁ (by norm_num))
  have hvQ : v ∈ S.QG := mem_QG_of_map_mem S σ (by
    rw [MulEquiv.apply_symm_apply]
    exact qVec_mem_Q₁ (by norm_num))
  have huK : u ∈ K := ⟨mem_centralizer_singleton_iff.mpr hux', (σ.symm u₀).2⟩
  have hvK : v ∈ K := ⟨mem_centralizer_singleton_iff.mpr hvx', (σ.symm v₀).2⟩
  have hQ2 : IsPGroup 2 S.QG := S.extraspecial.1.map S.M.subtype
  have hQN : ∀ k ∈ S.M, ∀ q ∈ S.QG, k * q * k⁻¹ ∈ S.QG := by
    intro k hk q hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨⟨k, hk⟩ * q' * ⟨k, hk⟩⁻¹, S.normal.conj_mem q' hq' ⟨k, hk⟩, rfl⟩
  set N : Subgroup K := (S.QG ⊓ K).subgroupOf K with hN
  have hNn : N.Normal := ⟨fun n hn k => by
    rw [hN, mem_subgroupOf] at hn ⊢
    refine ⟨?_, (k * n * k⁻¹).2⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hQN k (k.2.2) n hn.1⟩
  have hN2 : IsPGroup 2 N :=
    (hQ2.to_le inf_le_left).comap_of_injective K.subtype K.subtype_injective
  obtain ⟨T₀, hT₀⟩ := hT
  have hNT : N ≤ T₀ := hN2.le_sylow_of_normal T₀
  have hmemT : ∀ y ∈ S.QG, y ∈ K → y ∈ T := fun y hyQ hyK => by
    rw [← hT₀]
    exact ⟨⟨y, hyK⟩, hNT (by rw [hN, mem_subgroupOf]; exact ⟨hyQ, hyK⟩), rfl⟩
  have huT : u ∈ T := hmemT u huQ huK
  have hvT : v ∈ T := hmemT v hvQ hvK
  have hTK : T ≤ K := by
    rw [← hT₀]
    exact map_subtype_le _
  have hconjQ : ∀ y ∈ T, y ∈ S.QG → orderOf y = 2 → l * y * l⁻¹ ∈ S.QG := by
    intro y hyT hyQ hy2
    have h1 := hlN y hyT
    refine hQ _ (hTK h1).2 ?_ ((hswap y hyQ hy2).trans (isConj_iff.mpr ⟨l, rfl⟩))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy2
  have hluQ := hconjQ u huT huQ hu2
  have hlvQ := hconjQ v hvT hvQ hv2
  have hcommQ : ∀ a ∈ S.QG, ∀ b ∈ S.QG, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = S.z := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hc : ⁅(⟨a', ha'⟩ : S.Q), ⟨b', hb'⟩⁆ ∈ center S.Q := by
      rw [← S.extraspecial.2.1, _root_.commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    rcases S.mem_center_Q_iff.mp hc with h | h
    · left
      have := congrArg (fun q : S.Q => ((q : S.M) : G)) h
      simpa [commutatorElement_def] using this
    · right
      have := congrArg (fun q : S.Q => ((q : S.M) : G)) h
      simpa [commutatorElement_def, Setting.zQ] using this
  have hlz : l * S.z * l⁻¹ = S.z := by
    have hinvu : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu'
    have hinvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv'
    have e : l * u * l⁻¹ * (l * v * l⁻¹) * (l * u * l⁻¹)⁻¹ * (l * v * l⁻¹)⁻¹ =
        l * S.z * l⁻¹ := by
      rw [← huv']
      calc l * u * l⁻¹ * (l * v * l⁻¹) * (l * u * l⁻¹)⁻¹ * (l * v * l⁻¹)⁻¹ =
            l * (u * v * u⁻¹ * v⁻¹) * l⁻¹ := by group
        _ = l * (u * v * u * v) * l⁻¹ := by rw [hinvu, hinvv]
    rcases hcommQ _ hluQ _ hlvQ with h | h
    · rw [e] at h
      exfalso
      apply hz1
      calc S.z = l⁻¹ * (l * S.z * l⁻¹) * l := by group
        _ = 1 := by rw [h]; group
    · rwa [e] at h
  have hlK : l ∈ K := by
    refine ⟨hP.le hlP, mem_centralizer_singleton_iff.mpr ?_⟩
    calc l * S.z = l * S.z * l⁻¹ * l := by group
      _ = S.z * l := by rw [hlz]
  have hHP : T ⊔ zpowers l ≤ P := sup_le hTP (zpowers_le.mpr hlP)
  have hHK : T ⊔ zpowers l ≤ K := sup_le hTK (zpowers_le.mpr hlK)
  obtain ⟨Q', hQ', hHQ'⟩ := exists_isSylowOf_le hHK (hP.isPGroup.to_le hHP)
  have hQ'card : Nat.card Q' = 4096 := by
    rw [hQ'.card_eq, hKcard, factorization_61440]
    norm_num
  have hTQ' : T = Q' := Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hHQ')
    (by rw [hTcard, hQ'card])
  exact hlT (hTQ' ▸ hHQ' (mem_sup_right (mem_zpowers l)))

theorem not_isConj_iff (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* ↥(invE 1))
    (t : S.M) (ht : orderOf t = 2) :
    ¬ IsConj (t : G) S.z ↔ IsConj (σ t) lambda4 := by
  have : (Q₁ : Subgroup ↥(invE 1)).Normal := Q₁_normal
  refine ⟨fun hnc => ?_, not_isConj_z_of_isConj_lambda4 S σ⟩
  have ht2 : orderOf (σ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨i, hi, hc⟩ := exists_isConj_lambda (σ t) ht2
  interval_cases i
  · exfalso
    have h1 : σ t = t1Elt := eq_of_isConj_of_mem_center hc t1Elt_mem_center
    have h2 : t = S.zM := σ.injective (by rw [h1, map_zM])
    exact hnc (by rw [h2]; exact IsConj.refl _)
  · exfalso
    obtain ⟨g₀, hg₀, hne₀⟩ := hNWC
    have h5 : 5 ≤ Module.finrank (ZMod 2) S.Qt := by
      rw [S.finrank_Qt_eq_two_mul_width, hw]
      norm_num
    have htQ : (t : G) ∈ S.QG := mem_QG_of_map_mem S σ (mem_of_isConj_of_mem hc
      (qVec_mem_Q₁ (by norm_num)))
    exact hnc (CFSG.Sporadic.Co1Patterson.isConj_of_mem_QG_of_omega S h5 hΩ hg₀ hne₀ htQ
      (by rwa [Subgroup.orderOf_coe])).symm
  · exfalso
    have hc' : IsConj (σ t) (σ (σ.symm lambda3)) := by
      rw [MulEquiv.apply_symm_apply]
      exact hc
    exact hnc ((isConj_of_isConj_map S σ hc').trans (isConj_lambda3 S hw hΩ hNWC σ))
  · exact hc

theorem nonCentralSylow (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* ↥(invE 1)) :
    ∀ t ∈ centralizer ({S.z} : Set G), orderOf t = 2 → ¬ IsConj t S.z →
      IsSylowOf 2 (centralizer ({t} : Set G) ⊓ centralizer ({S.z} : Set G))
          (centralizer ({t} : Set G)) ∧
        Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({S.z} : Set G) : Subgroup G) = 512 := by
  intro t htM ht2 hnc
  have h := (not_isConj_iff S hw hΩ hNWC σ ⟨t, htM⟩ (by rwa [Subgroup.orderOf_mk])).mp hnc
  exact sylow_of_isConj_lambda4 S σ h

end Fusion

end CFSG.Sporadic.SuzRecog.LocalR
