module

public import CFSG.Sporadic.Recognition.LyonsAS4Aut
public import CFSG.Sporadic.Recognition.McLASThreeLocalCert
public import CFSG.Sporadic.Recognition.McLASCert

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG.Sporadic.Recognition.McLAS CFSG.Blueprint
open scoped commutatorElement

universe u

section Generic

variable {K : Type u} [Group K]

theorem card_centralizer_mulEquiv {K' : Type*} [Group K'] (e : K ≃* K') (y : K) :
    Nat.card ↥(centralizer ({e y} : Set K')) = Nat.card ↥(centralizer ({y} : Set K)) := by
  have h : centralizer ({e y} : Set K') = (centralizer ({y} : Set K)).map e.toMonoidHom := by
    ext g
    simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hg
      refine ⟨e.symm g, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    · rintro ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hc]
  rw [h, Subgroup.card_map_of_injective e.injective]

theorem exists_commutator_eq_of_commutator_eq_zpowers {R : Subgroup K} {x : K}
    (hx : orderOf x = 3) (h : ⁅R, R⁆ = zpowers x) : ∃ a ∈ R, ∃ b ∈ R, ⁅a, b⁆ = x := by
  by_contra hne
  push Not at hne
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hbot : ⁅R, R⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ zpowers x := h ▸ commutator_mem_commutator ha hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hzp : x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x ^ 2 := by
      have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx3
      rw [zpow_eq_zpow_emod k h3]
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h | h | h <;> rw [h] <;> simp
    rcases hzp with h1 | h1 | h1
    · rw [← hk, h1]; exact one_mem _
    · exact absurd (hk.symm.trans h1) (hne a ha b hb)
    · exfalso
      apply hne b hb a ha
      rw [← commutatorElement_inv, ← hk, h1]
      calc (x ^ 2)⁻¹ = (x ^ 3) * (x ^ 2)⁻¹ := by rw [hx3, one_mul]
        _ = x := by group
  rw [hbot] at h
  apply hx1
  have : x ∈ zpowers x := mem_zpowers x
  rw [← h] at this
  exact this

structure ThreeCore (y : K) (R : Subgroup K) : Prop where
  isPGroup : IsPGroup 3 R
  card : Nat.card ↥R = 243
  le_cent : R ≤ centralizer ({y} : Set K)
  normal : ∀ c ∈ centralizer ({y} : Set K), ∀ r ∈ R, c * r * c⁻¹ ∈ R
  max : ∀ J : Subgroup K, J ≤ centralizer ({y} : Set K) →
    (∀ c ∈ centralizer ({y} : Set K), ∀ j ∈ J, c * j * c⁻¹ ∈ J) → IsPGroup 3 J → J ≤ R
  comm : ⁅R, R⁆ = zpowers y

namespace ThreeCore

variable {y : K} {R : Subgroup K}

theorem map {K' : Type*} [Group K'] (φ : K ≃* K') (h : ThreeCore y R) :
    ThreeCore (φ y) (R.map φ.toMonoidHom) := by
  have hcent : ∀ c' : K', c' ∈ centralizer ({φ y} : Set K') ↔
      φ.symm c' ∈ centralizer ({y} : Set K) := by
    intro c'
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hc
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc
    · intro hc
      have := congrArg φ hc
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      exact this
  refine ⟨h.isPGroup.map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h.card
  · rintro _ ⟨r, hr, rfl⟩
    rw [hcent]
    simpa using h.le_cent hr
  · intro c' hc' r' hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    refine ⟨φ.symm c' * r * (φ.symm c')⁻¹, h.normal _ ((hcent c').1 hc') r hr, ?_⟩
    simp
  · intro J' hJ' hJn' hJ3'
    have hJ : J'.map φ.symm.toMonoidHom ≤ R := by
      refine h.max _ ?_ ?_ (hJ3'.map φ.symm.toMonoidHom)
      · rintro _ ⟨j, hj, rfl⟩
        have := hJ' hj
        rw [hcent] at this
        simpa using this
      · rintro c hc _ ⟨j, hj, rfl⟩
        have hc' : φ c ∈ centralizer ({φ y} : Set K') := by
          rw [hcent]; simpa using hc
        refine ⟨φ c * j * (φ c)⁻¹, hJn' _ hc' j hj, ?_⟩
        simp
    intro g hg
    refine ⟨φ.symm g, hJ ⟨g, hg, rfl⟩, ?_⟩
    simp
  · rw [← Subgroup.map_commutator, h.comm, MonoidHom.map_zpowers]
    rfl

theorem le_normalizer_of_conj_mem {C S : Subgroup K} (h : ∀ c ∈ C, ∀ k ∈ S, c * k * c⁻¹ ∈ S) :
    C ≤ normalizer (S : Set K) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro k
  refine ⟨h c hc k, fun hk => ?_⟩
  have := h c⁻¹ (C.inv_mem hc) _ hk
  simpa [mul_assoc] using this

theorem of_threeLocal {G : Type u} [Group G] {x : G} {R T A : Subgroup G}
    (h : ThreeLocal G x R T A) : ThreeCore x R := by
  have hx3 : x ^ 3 = 1 := by rw [← h.order_x]; exact pow_orderOf_eq_one x
  set N : Subgroup G := normalizer (zpowers x : Set G) with hN
  have hR : R = (CFSG.pCore 3 ↥N).map N.subtype := h.pCore_eq.symm
  have hcentN : centralizer ({x} : Set G) ≤ N := centralizer_le_normalizer_zpowers x
  have hRcent : R ≤ centralizer ({x} : Set G) := by
    intro r hr
    have hx : x ∈ R ⊓ centralizer (R : Set G) := by rw [h.center_R]; exact mem_zpowers x
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx.2 r hr)
  have hRnorm : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    rw [hR] at hr ⊢
    obtain ⟨r', hr', rfl⟩ := hr
    have hnorm : (CFSG.pCore 3 ↥N).Normal := CFSG.pCore_normal
    refine ⟨⟨g, hg⟩ * r' * ⟨g, hg⟩⁻¹, hnorm.conj_mem r' hr' ⟨g, hg⟩, ?_⟩
    simp
  refine ⟨IsPGroup.of_card (n := 5) (by rw [h.card_R]; norm_num), h.card_R, hRcent,
    fun c hc r hr => hRnorm c (hcentN hc) r hr, ?_, h.commutator_R⟩
  intro J hJC hJn hJ3
  have hcardlt : ¬ N ≤ centralizer ({x} : Set G) := by
    intro hle
    have heq : N = centralizer ({x} : Set G) := le_antisymm hle hcentN
    have h1 := h.card_normalizer
    have h2 := h.card_centralizer
    rw [← hN, heq] at h1
    omega
  obtain ⟨n, hnN, hnC⟩ := IsConcreteLE.not_le_iff_exists.1 hcardlt
  have hinv : n * x * n⁻¹ = x⁻¹ := by
    rcases McLAS.normalizer_zpowers_cases h.order_x hnN with h1 | h1
    · exact absurd (mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1)) hnC
    · exact h1
  have hinv' : n⁻¹ * x * n = x⁻¹ := by
    have h2 : n * x⁻¹ * n⁻¹ = x := by
      have := congrArg (fun z => z⁻¹) hinv
      simpa [mul_assoc] using this
    calc n⁻¹ * x * n = n⁻¹ * (n * x⁻¹ * n⁻¹) * n := by rw [h2]
      _ = x⁻¹ := by group
  have hnN' : n⁻¹ ∈ N := N.inv_mem hnN
  have hn2 : n * n ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : n * n * x * (n * n)⁻¹ = x := by
      calc n * n * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
        _ = n * x⁻¹ * n⁻¹ := by rw [hinv]
        _ = (n * x * n⁻¹)⁻¹ := by group
        _ = x := by rw [hinv, inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 this
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hnconj : ∀ c ∈ C, n * c * n⁻¹ ∈ C := fun c hc => conj_mem_centralizer hnN hc
  have hnconj' : ∀ c ∈ C, n⁻¹ * c * n ∈ C := fun c hc => by
    simpa using conj_mem_centralizer hnN' hc
  set Jn : Subgroup G := J.map (MulAut.conj n).toMonoidHom with hJn_def
  have hmemJn : ∀ g, g ∈ Jn ↔ n⁻¹ * g * n ∈ J := by
    intro g
    simp only [hJn_def, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa [mul_assoc] using hj
    · intro hg
      exact ⟨n⁻¹ * g * n, hg, by group⟩
  have hJnC : Jn ≤ C := by
    rintro _ ⟨j, hj, rfl⟩
    exact hnconj j (hJC hj)
  have hCnormJn : ∀ c ∈ C, ∀ k ∈ Jn, c * k * c⁻¹ ∈ Jn := by
    intro c hc k hk
    rw [hmemJn] at hk ⊢
    have h1 := hJn (n⁻¹ * c * n) (hnconj' c hc) _ hk
    have : n⁻¹ * (c * k * c⁻¹) * n = (n⁻¹ * c * n) * (n⁻¹ * k * n) * (n⁻¹ * c * n)⁻¹ := by group
    rw [this]
    exact h1
  have hJnorm : J ≤ normalizer (Jn : Set G) :=
    (le_normalizer_of_conj_mem (C := J) (S := Jn) fun c hc k hk => hCnormJn c (hJC hc) k hk)
  have hJnP : IsPGroup 3 Jn := hJ3.map (MulAut.conj n).toMonoidHom
  have hJ'P : IsPGroup 3 (J ⊔ Jn : Subgroup G) := hJ3.to_sup_of_normal_right' hJnP hJnorm
  have hJ'N : J ⊔ Jn ≤ N := sup_le (hJC.trans hcentN) (hJnC.trans hcentN)
  have hnorm' : ∀ g ∈ N, ∀ y ∈ J ⊔ Jn, g * y * g⁻¹ ∈ J ⊔ Jn := by
    intro g hg
    have hJle : J ≤ (J ⊔ Jn).comap (MulAut.conj g).toMonoidHom ∧
        Jn ≤ (J ⊔ Jn).comap (MulAut.conj g).toMonoidHom := by
      rcases McLAS.mem_centralizer_or_of_mem_normalizer (Q := ⊤) h.order_x (mem_top n) hinv
        (mem_inf.2 ⟨mem_top g, hg⟩) with h1 | h1
      · have hgC : g ∈ C := (mem_inf.1 h1).2
        refine ⟨fun j hj => ?_, fun k hk => ?_⟩
        · exact Subgroup.mem_sup_left (hJn g hgC j hj)
        · exact Subgroup.mem_sup_right (hCnormJn g hgC k hk)
      · have hcC : n⁻¹ * g ∈ C := (mem_inf.1 h1).2
        refine ⟨fun j hj => ?_, fun k hk => ?_⟩
        · have h2 : g * j * g⁻¹ = n * ((n⁻¹ * g) * j * (n⁻¹ * g)⁻¹) * n⁻¹ := by group
          have h3 : g * j * g⁻¹ ∈ Jn := by
            rw [hmemJn]
            have : n⁻¹ * (g * j * g⁻¹) * n = (n⁻¹ * g) * j * (n⁻¹ * g)⁻¹ := by group
            rw [this]
            exact hJn _ hcC j hj
          exact Subgroup.mem_sup_right h3
        · have hk' := (hmemJn k).1 hk
          have hnn : n * (n⁻¹ * g) * n ∈ C := by
            have : n * (n⁻¹ * g) * n = (n * (n⁻¹ * g) * n⁻¹) * (n * n) := by group
            rw [this]
            exact C.mul_mem (hnconj _ hcC) hn2
          have h3 : g * k * g⁻¹ ∈ J := by
            have : g * k * g⁻¹ = (n * (n⁻¹ * g) * n) * (n⁻¹ * k * n) * (n * (n⁻¹ * g) * n)⁻¹ := by
              group
            rw [this]
            exact hJn _ hnn _ hk'
          exact Subgroup.mem_sup_left h3
    intro y hy
    exact (sup_le hJle.1 hJle.2) hy
  have hnormal : ((J ⊔ Jn).subgroupOf N).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    simpa using hnorm' g.1 g.2 y hy
  have hP' : IsPGroup 3 ((J ⊔ Jn).subgroupOf N) :=
    hJ'P.of_equiv (subgroupOfEquivOfLe hJ'N).symm
  have hle : (J ⊔ Jn).subgroupOf N ≤ CFSG.pCore 3 ↥N := le_sSup ⟨hnormal, hP'⟩
  intro g hg
  rw [hR]
  refine ⟨⟨g, hJ'N (Subgroup.mem_sup_left hg)⟩, hle ?_, rfl⟩
  rw [mem_subgroupOf]
  exact Subgroup.mem_sup_left hg

end ThreeCore

end Generic

section McLSection

variable {K : Type u} [Group K]

theorem exists_two_classes_of_mulEquiv_aux {K' : Type*} [Group K'] (e : K ≃* K') {x₁ x₂ : K'}
    (o₁ : orderOf x₁ = 3) (o₂ : orderOf x₂ = 3)
    (c₁ : Nat.card ↥(centralizer ({x₁} : Set K')) = 29160)
    (c₂ : Nat.card ↥(centralizer ({x₂} : Set K')) = 972)
    (hall : ∀ y : K', orderOf y = 3 → IsConj y x₁ ∨ IsConj y x₂) :
    ∃ r₁ r₂ : K, orderOf r₁ = 3 ∧ orderOf r₂ = 3 ∧
      Nat.card ↥(centralizer ({r₁} : Set K)) = 29160 ∧
      Nat.card ↥(centralizer ({r₂} : Set K)) = 972 ∧
      ∀ y : K, orderOf y = 3 → IsConj y r₁ ∨ IsConj y r₂ := by
  refine ⟨e.symm x₁, e.symm x₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact o₁
  · rw [MulEquiv.orderOf_eq]; exact o₂
  · rw [← card_centralizer_mulEquiv e, MulEquiv.apply_symm_apply]; exact c₁
  · rw [← card_centralizer_mulEquiv e, MulEquiv.apply_symm_apply]; exact c₂
  · intro y hy
    have hy' : orderOf (e y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
    rcases hall (e y) hy' with h | h
    · left
      have := (e.symm.toMonoidHom).map_isConj h
      simpa using this
    · right
      have := (e.symm.toMonoidHom).map_isConj h
      simpa using this

theorem exists_two_classes_of_mulEquiv
    (e : K ≃* NativeSporadic.McL) :
    ∃ r₁ r₂ : K, orderOf r₁ = 3 ∧ orderOf r₂ = 3 ∧
      Nat.card ↥(centralizer ({r₁} : Set K)) = 29160 ∧
      Nat.card ↥(centralizer ({r₂} : Set K)) = 972 ∧
      ∀ y : K, orderOf y = 3 → IsConj y r₁ ∨ IsConj y r₂ := by
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  exact @exists_two_classes_of_mulEquiv_aux K _ NativeSporadic.McL inferInstance e x₁ x₂ o₁ o₂
    c₁ c₂ hall

theorem card_centralizer_eq_or
    (e : K ≃* NativeSporadic.McL) {y : K} (hy : orderOf y = 3) :
    Nat.card ↥(centralizer ({y} : Set K)) = 29160 ∨
      Nat.card ↥(centralizer ({y} : Set K)) = 972 := by
  obtain ⟨r₁, r₂, -, -, c₁, c₂, hall⟩ := exists_two_classes_of_mulEquiv e
  rcases hall y hy with h | h
  · left; rw [card_centralizer_eq_of_isConj h]; exact c₁
  · right; rw [card_centralizer_eq_of_isConj h]; exact c₂

theorem card_centralizer_eq_of_five_dvd
    (e : K ≃* NativeSporadic.McL) {y : K} (hy : orderOf y = 3)
    (h5 : 5 ∣ Nat.card ↥(centralizer ({y} : Set K))) :
    Nat.card ↥(centralizer ({y} : Set K)) = 29160 := by
  rcases card_centralizer_eq_or e hy with h | h
  · exact h
  · rw [h] at h5; exact absurd h5 (by norm_num)

theorem isConj_of_card_eq_aux {K' : Type*} [Group K'] {r₁ r₂ : K'}
    (c₂ : Nat.card ↥(centralizer ({r₂} : Set K')) = 972)
    (hall : ∀ y : K', orderOf y = 3 → IsConj y r₁ ∨ IsConj y r₂) {a b : K'}
    (ha : orderOf a = 3) (hb : orderOf b = 3)
    (ha' : Nat.card ↥(centralizer ({a} : Set K')) = 29160)
    (hb' : Nat.card ↥(centralizer ({b} : Set K')) = 29160) : IsConj a b := by
  have h1 : IsConj a r₁ := by
    rcases hall a ha with h | h
    · exact h
    · exfalso
      rw [card_centralizer_eq_of_isConj h, c₂] at ha'
      omega
  have h2 : IsConj b r₁ := by
    rcases hall b hb with h | h
    · exact h
    · exfalso
      rw [card_centralizer_eq_of_isConj h, c₂] at hb'
      omega
  exact h1.trans h2.symm

theorem exists_threeCore_aux {K' : Type*} [Group K'] (e : K ≃* K') {x : K'} {R T A : Subgroup K'}
    (hL : ThreeLocal K' x R T A) {r₁ r₂ : K'}
    (c₂ : Nat.card ↥(centralizer ({r₂} : Set K')) = 972)
    (hall : ∀ y : K', orderOf y = 3 → IsConj y r₁ ∨ IsConj y r₂) {y : K} (hy : orderOf y = 3)
    (hc : Nat.card ↥(centralizer ({y} : Set K)) = 29160) :
    ∃ R : Subgroup K, ThreeCore y R := by
  have hey : orderOf (e y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
  have hcey : Nat.card ↥(centralizer ({e y} : Set K')) = 29160 := by
    rw [card_centralizer_mulEquiv e]; exact hc
  have hxy : IsConj x (e y) :=
    isConj_of_card_eq_aux c₂ hall hL.order_x hey hL.card_centralizer hcey
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  have h1 := (ThreeCore.of_threeLocal hL).map (MulAut.conj g)
  have h2 := h1.map e.symm
  have h3 : e.symm ((MulAut.conj g) x) = y := by
    rw [MulAut.conj_apply, hg, MulEquiv.symm_apply_apply]
  rw [h3] at h2
  exact ⟨_, h2⟩

theorem exists_threeCore
    (e : K ≃* NativeSporadic.McL) {y : K} (hy : orderOf y = 3)
    (hc : Nat.card ↥(centralizer ({y} : Set K)) = 29160) :
    ∃ R : Subgroup K, ThreeCore y R := by
  obtain ⟨x, R, T, A, hL⟩ := mcl_threeLocal_of_certificate
  obtain ⟨x₁, x₂, o₁, o₂, c₁, c₂, -, hall⟩ := mcl_two_classes_order_three_of_certificate
  exact @exists_threeCore_aux K _ NativeSporadic.McL inferInstance e x R T A hL.toThreeLocal
    x₁ x₂ c₂ hall y hy hc

theorem exists_commutator_of_card_eq
    (e : K ≃* NativeSporadic.McL) {y : K} (hy : orderOf y = 3)
    (hc : Nat.card ↥(centralizer ({y} : Set K)) = 29160) :
    ∃ a b : K, a * y = y * a ∧ b * y = y * b ∧ ⁅a, b⁆ = y := by
  obtain ⟨R, hR⟩ := exists_threeCore e hy hc
  obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_eq_of_commutator_eq_zpowers hy hR.comm
  exact ⟨a, b, mem_centralizer_singleton_iff.1 (hR.le_cent ha),
    mem_centralizer_singleton_iff.1 (hR.le_cent hb), hab⟩

end McLSection


end CFSG.Sporadic.Recognition.LyonsSims
