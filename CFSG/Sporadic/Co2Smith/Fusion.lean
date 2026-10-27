module

public import CFSG.Sporadic.Co2Smith.G21
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u v

section Counts

variable {M : Type*} [Group M] {M' : Type*} [Group M']

@[expose] noncomputable def sqrtCnt (c x : M) : ℕ :=
  Nat.card {y : M // y * x = x * y ∧ y * y = c}

theorem sqrtCnt_mulEquiv (φ : M ≃* M') (c x : M) : sqrtCnt (φ c) (φ x) = sqrtCnt c x := by
  unfold sqrtCnt
  refine (Nat.card_congr (φ.toEquiv.subtypeEquiv fun y => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, φ.injective.eq_iff]

theorem sqrtCnt_conj (h c x : M) : sqrtCnt (h * c * h⁻¹) (h * x * h⁻¹) = sqrtCnt c x :=
  sqrtCnt_mulEquiv (MulAut.conj h) c x

@[expose] noncomputable def cnt3 (c a b : M) : ℕ :=
  Nat.card {y : M // y * a = a * y ∧ y * b = b * y ∧ y * y = c}

theorem cnt3_conj (g c a b : M) :
    cnt3 (g⁻¹ * c * g) (g⁻¹ * a * g) (g⁻¹ * b * g) = cnt3 c a b := by
  unfold cnt3
  refine (Nat.card_congr ((MulAut.conj g⁻¹).toEquiv.subtypeEquiv fun y => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> group <;> simp only [mul_assoc] at h1 h2 h3 ⊢
    · rw [← mul_assoc y a, h1, mul_assoc]
    · rw [← mul_assoc y b, h2, mul_assoc]
    · rw [← mul_assoc y y, h3]
  · rintro ⟨h1, h2, h3⟩
    have e1 : y * a = a * y := by
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    have e2 : y * b = b * y := by
      have := congrArg (fun w => g * w * g⁻¹) h2
      simpa [mul_assoc] using this
    have e3 : y * y = c := by
      have := congrArg (fun w => g * w * g⁻¹) h3
      simpa [mul_assoc] using this
    exact ⟨e1, e2, e3⟩

theorem cnt3_comm (c a b : M) : cnt3 c a b = cnt3 c b a := by
  unfold cnt3
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by tauto)

end Counts

section Fusion

variable {G : Type u} [Group G] {z : G}

theorem sqrtCnt_eq_cnt3 (c x : centralizer ({z} : Set G)) :
    sqrtCnt c x = cnt3 (c : G) z (x : G) := by
  unfold sqrtCnt cnt3
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1, mem_centralizer_singleton_iff.mp y.1.2,
        congrArg Subtype.val y.2.1, congrArg Subtype.val y.2.2⟩
      invFun := fun y => ⟨⟨y.1, mem_centralizer_singleton_iff.mpr y.2.1⟩,
        Subtype.ext y.2.2.1, Subtype.ext y.2.2.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }

theorem conj_mem_centralizer {g : G} (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    g * z * g⁻¹ ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff] at ht ⊢
  calc g * z * g⁻¹ * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * z * g * z) * g⁻¹ := by rw [← ht]
    _ = z * (g * z * g⁻¹) := by group

theorem sqrtCnt_swap {g : G} (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    sqrtCnt (zC z) (⟨_, ht⟩ : centralizer ({z} : Set G)) =
        sqrtCnt (⟨_, conj_mem_centralizer ht⟩ : centralizer ({z} : Set G))
          ⟨_, conj_mem_centralizer ht⟩ ∧
      sqrtCnt (⟨_, ht⟩ : centralizer ({z} : Set G)) ⟨_, ht⟩ =
        sqrtCnt (zC z) (⟨_, conj_mem_centralizer ht⟩ : centralizer ({z} : Set G)) := by
  simp only [sqrtCnt_eq_cnt3]
  have hz : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  constructor
  · show cnt3 z z (g⁻¹ * z * g) = cnt3 (g * z * g⁻¹) z (g * z * g⁻¹)
    conv_lhs => rw [show cnt3 z z (g⁻¹ * z * g) =
      cnt3 (g⁻¹ * (g * z * g⁻¹) * g) (g⁻¹ * (g * z * g⁻¹) * g) (g⁻¹ * z * g) by rw [← hz]]
    rw [cnt3_conj, cnt3_comm]
  · show cnt3 (g⁻¹ * z * g) z (g⁻¹ * z * g) = cnt3 z z (g * z * g⁻¹)
    conv_lhs => rw [show cnt3 (g⁻¹ * z * g) z (g⁻¹ * z * g) =
      cnt3 (g⁻¹ * z * g) (g⁻¹ * (g * z * g⁻¹) * g) (g⁻¹ * z * g) by rw [← hz]]
    rw [cnt3_conj, cnt3_comm]

theorem mul_self_conj_z (g : G) (hz : z * z = 1) : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
  calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [hz]; group

variable [Finite G]

theorem exists_conj_mem_ne
    (hG : SmithHyp G z) :
    ∃ g : G, g⁻¹ * z * g ∈ centralizer ({z} : Set G) ∧ g⁻¹ * z * g ≠ z := by
  have hz := hG.orderOf_eq
  obtain ⟨T⟩ : Nonempty (Sylow 2 (centralizer ({z} : Set G))) := inferInstance
  obtain ⟨P, hP⟩ := exists_sylow_eq_map hG.centralizer hz T
  have hPH : (P : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [hP]
    exact map_subtype_le _
  have hzP : z ∈ (P : Subgroup G) := by
    rw [hP]
    exact ⟨zC z, pCore_le_sylow' T (zC_mem_pCore hz), rfl⟩
  by_contra hne
  push Not at hne
  have hwc : ∀ g : G, g⁻¹ * ((⟨z, hzP⟩ : (P : Subgroup G)) : G) * g ∈ (P : Subgroup G) →
      g⁻¹ * ((⟨z, hzP⟩ : (P : Subgroup G)) : G) * g = (⟨z, hzP⟩ : (P : Subgroup G)) :=
    fun g hg => hne g (hPH hg)
  have hZ : (⟨z, hzP⟩ : (P : Subgroup G)) ∈ center (P : Subgroup G) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hPH y.2))
  have hzo : orderOf (⟨z, hzP⟩ : (P : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz
  obtain ⟨h1, -⟩ :=
    ComponentClassification.StandardRecognition.glauberman_zStar_central_sylow_involution_univ
      P ⟨z, hzP⟩ hZ hzo hwc
  have hcen : z ∈ center G := by
    rw [mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := h1 g
    rw [hG.oddCore_eq_bot, mem_bot] at hk
    subst hk
    rw [mul_one]
    exact mem_centralizer_singleton_iff.mp hc
  rw [hG.center_eq_bot, mem_bot] at hcen
  rw [hcen, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem false_of_classes
    {M : Type v} [Group M] (hG : SmithHyp G z)
    (φ : centralizer ({z} : Set G) ≃* M) (zM : M) (r : Fin 4 → M)
    (hzM : ∀ y ∈ CFSG.pCore 2 M, (∀ a ∈ CFSG.pCore 2 M, a * y = y * a) → y = 1 ∨ y = zM)
    (hinv : ∀ y : M, y * y = 1 → y = 1 ∨ y = zM ∨ ∃ i, ∃ h : M, h * y * h⁻¹ = r i)
    (hpair : ∀ i j, sqrtCnt zM (r i) = sqrtCnt (r j) (r j) →
      sqrtCnt (r i) (r i) = sqrtCnt zM (r j) → i = 0)
    (hr0 : r 0 ∈ CFSG.pCore 2 M) (hr : ∀ i, i ≠ 0 → r i ∉ CFSG.pCore 2 M)
    (hcomm : ∀ a ∈ CFSG.pCore 2 M, ∀ b ∈ CFSG.pCore 2 M,
      a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = zM)
    (hab : ∃ a ∈ CFSG.pCore 2 M, ∃ b ∈ CFSG.pCore 2 M, a * a = 1 ∧ b * b = 1 ∧
      a * r 0 = r 0 * a ∧ b * r 0 = r 0 * b ∧ a * b ≠ b * a) : False := by
  set H := centralizer ({z} : Set G)
  set E := CFSG.pCore 2 H
  have hz2 := hG.orderOf_eq
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hφz : φ (zC z) = zM := by
    have hmem : φ (zC z) ∈ CFSG.pCore 2 M := apply_mem_pCore_two φ (zC_mem_pCore hz2)
    have hcen : ∀ a ∈ CFSG.pCore 2 M, a * φ (zC z) = φ (zC z) * a := by
      intro a _
      have hc := mem_center_iff.mp (zC_mem_center z) (φ.symm a)
      have := congrArg φ hc
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
    rcases hzM _ hmem hcen with h | h
    · exact absurd (φ.injective (h.trans (map_one φ).symm)) fun e => hz1 (congrArg Subtype.val e)
    · exact h
  have hφz' : φ.symm zM = zC z := by rw [← hφz, MulEquiv.symm_apply_apply]
  have hcls : ∀ x : H, x * x = 1 → x = 1 ∨ x = zC z ∨
      ∃ i, ∃ h : H, h * x * h⁻¹ = φ.symm (r i) := by
    intro x hx
    rcases hinv (φ x) (by rw [← map_mul, hx, map_one]) with h | h | ⟨i, h, hh⟩
    · exact Or.inl (φ.injective (h.trans (map_one φ).symm))
    · exact Or.inr (Or.inl (φ.injective (h.trans hφz.symm)))
    · refine Or.inr (Or.inr ⟨i, φ.symm h, ?_⟩)
      rw [← hh, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hinvZ : ∀ i, sqrtCnt (zC z) (φ.symm (r i)) = sqrtCnt zM (r i) := by
    intro i
    rw [← hφz', sqrtCnt_mulEquiv]
  have hinvR : ∀ i, sqrtCnt (φ.symm (r i)) (φ.symm (r i)) = sqrtCnt (r i) (r i) :=
    fun i => sqrtCnt_mulEquiv _ _ _
  have hconjZ : ∀ (h x : H), sqrtCnt (zC z) (h * x * h⁻¹) = sqrtCnt (zC z) x := by
    intro h x
    have e : h * zC z * h⁻¹ = zC z := by
      rw [mem_center_iff.mp (zC_mem_center z) h, mul_inv_cancel_right]
    rw [← e, sqrtCnt_conj, e]
  have hconjR : ∀ (h x : H), sqrtCnt (h * x * h⁻¹) (h * x * h⁻¹) = sqrtCnt x x :=
    fun h x => sqrtCnt_conj h x x
  have hEn : E.Normal := CFSG.pCore_normal
  have hr0E : φ.symm (r 0) ∈ E := symm_apply_mem_pCore_two φ hr0
  have hmemE : ∀ (x h : H), h * x * h⁻¹ = φ.symm (r 0) → x ∈ E := by
    intro x h hh
    have := hEn.conj_mem _ hr0E h⁻¹
    rwa [← hh, show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  have hfus : ∀ g : G, ∀ ht : g⁻¹ * z * g ∈ H,
      (⟨_, ht⟩ : H) ∈ E ∧ (⟨_, conj_mem_centralizer ht⟩ : H) ∈ E := by
    intro g ht
    by_cases hte : g⁻¹ * z * g = z
    · have hse : g * z * g⁻¹ = z := by
        have := congrArg (fun w => g * w * g⁻¹) hte
        simpa [mul_assoc] using this.symm
      have h1 : (⟨_, ht⟩ : H) = zC z := Subtype.ext hte
      have h2 : (⟨_, conj_mem_centralizer ht⟩ : H) = zC z := Subtype.ext hse
      rw [h1, h2]
      exact ⟨zC_mem_pCore hz2, zC_mem_pCore hz2⟩
    · set t : H := ⟨_, ht⟩
      set u : H := ⟨_, conj_mem_centralizer ht⟩
      have htt : t * t = 1 := Subtype.ext (mul_self_conj_z g hzz)
      have huu : u * u = 1 := Subtype.ext (by
        show g * z * g⁻¹ * (g * z * g⁻¹) = 1
        simpa using mul_self_conj_z g⁻¹ hzz)
      have ht1 : t ≠ 1 := fun e => hz1 (by
        have := congrArg Subtype.val e
        simp only [t, OneMemClass.coe_one] at this
        have := congrArg (fun w => g * w * g⁻¹) this
        simpa [mul_assoc] using this)
      have htz : t ≠ zC z := fun e => hte (congrArg Subtype.val e)
      have hu1 : u ≠ 1 := fun e => hz1 (by
        have := congrArg Subtype.val e
        simp only [u, OneMemClass.coe_one] at this
        have := congrArg (fun w => g⁻¹ * w * g) this
        simpa [mul_assoc] using this)
      have huz : u ≠ zC z := fun e => hte (by
        have := congrArg (fun w => g⁻¹ * w * g) (congrArg Subtype.val e)
        simp only [u, zC] at this
        simpa [mul_assoc] using this.symm)
      obtain ⟨i, h, hh⟩ := ((hcls t htt).resolve_left ht1).resolve_left htz
      obtain ⟨j, k, hk⟩ := ((hcls u huu).resolve_left hu1).resolve_left huz
      obtain ⟨sw1, sw2⟩ := sqrtCnt_swap ht
      have e1 : sqrtCnt zM (r i) = sqrtCnt (r j) (r j) := by
        rw [← hinvZ, ← hinvR, ← hh, ← hk, hconjZ, hconjR]
        exact sw1
      have e2 : sqrtCnt (r i) (r i) = sqrtCnt zM (r j) := by
        rw [← hinvZ, ← hinvR, ← hh, ← hk, hconjZ, hconjR]
        exact sw2
      have hi := hpair i j e1 e2
      have hj := hpair j i e2.symm e1.symm
      subst hi
      subst hj
      exact ⟨hmemE t h hh, hmemE u k hk⟩
  obtain ⟨g, ht, hte⟩ := exists_conj_mem_ne hG
  obtain ⟨htE, hsE⟩ := hfus g ht
  set t : H := ⟨_, ht⟩
  have htt : t * t = 1 := Subtype.ext (mul_self_conj_z g hzz)
  have ht1 : t ≠ 1 := fun e => hz1 (by
    have := congrArg Subtype.val e
    simp only [t, OneMemClass.coe_one] at this
    have := congrArg (fun w => g * w * g⁻¹) this
    simpa [mul_assoc] using this)
  have htz : t ≠ zC z := fun e => hte (congrArg Subtype.val e)
  obtain ⟨i, h, hh⟩ := ((hcls t htt).resolve_left ht1).resolve_left htz
  have hi : i = 0 := by
    by_contra hi
    exact hr i hi (by
      have := apply_mem_pCore_two φ (hEn.conj_mem _ htE h)
      rwa [hh, MulEquiv.apply_symm_apply] at this)
  subst hi
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = zC z := by
    intro x hx y hy
    rcases hcomm _ (apply_mem_pCore_two φ hx) _ (apply_mem_pCore_two φ hy) with e | e
    · left
      apply φ.injective
      simpa only [map_mul, map_inv, map_one] using e
    · right
      apply φ.injective
      rw [hφz]
      simpa only [map_mul, map_inv] using e
  have hinvE : ∀ x ∈ E, x * x = 1 → x ≠ 1 → x ≠ zC z → ∃ k : G, (x : G) = k⁻¹ * z * k := by
    intro x hx hxx hx1 hxz
    obtain ⟨i', h', hh'⟩ := ((hcls x hxx).resolve_left hx1).resolve_left hxz
    have hi' : i' = 0 := by
      by_contra hi'
      exact hr i' hi' (by
        have := apply_mem_pCore_two φ (hEn.conj_mem _ hx h')
        rwa [hh', MulEquiv.apply_symm_apply] at this)
    subst hi'
    refine ⟨g * (h : G)⁻¹ * (h' : G), ?_⟩
    have e : x = h'⁻¹ * (h * t * h⁻¹) * h' := by rw [hh, ← hh']; group
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, t] at this
    rw [this]
    group
  obtain ⟨a, ha, b, hb, haa, hbb, har, hbr, hab'⟩ := hab
  set a' : H := h⁻¹ * φ.symm a * h
  set b' : H := h⁻¹ * φ.symm b * h
  have ha'E : a' ∈ E := by simpa using hEn.conj_mem _ (symm_apply_mem_pCore_two φ ha) h⁻¹
  have hb'E : b' ∈ E := by simpa using hEn.conj_mem _ (symm_apply_mem_pCore_two φ hb) h⁻¹
  have hsq : ∀ c : M, c * c = 1 → (h⁻¹ * φ.symm c * h) * (h⁻¹ * φ.symm c * h) = 1 := by
    intro c hc
    calc (h⁻¹ * φ.symm c * h) * (h⁻¹ * φ.symm c * h) = h⁻¹ * φ.symm (c * c) * h := by
          rw [map_mul]; group
      _ = 1 := by rw [hc, map_one]; group
  have haa' : a' * a' = 1 := hsq a haa
  have hbb' : b' * b' = 1 := hsq b hbb
  have et : t = h⁻¹ * φ.symm (r 0) * h := by rw [← hh]; group
  have hct : ∀ c : M, c * r 0 = r 0 * c → (h⁻¹ * φ.symm c * h) * t = t * (h⁻¹ * φ.symm c * h) := by
    intro c hc
    have e : φ.symm c * φ.symm (r 0) = φ.symm (r 0) * φ.symm c := by
      rw [← map_mul, ← map_mul, hc]
    calc (h⁻¹ * φ.symm c * h) * t = h⁻¹ * (φ.symm c * φ.symm (r 0)) * h := by rw [et]; group
      _ = h⁻¹ * (φ.symm (r 0) * φ.symm c) * h := by rw [e]
      _ = t * (h⁻¹ * φ.symm c * h) := by rw [et]; group
  have hat : a' * t = t * a' := hct a har
  have hbt : b' * t = t * b' := hct b hbr
  have hab'' : a' * b' ≠ b' * a' := by
    intro e
    apply hab'
    apply φ.symm.injective
    rw [map_mul, map_mul]
    calc φ.symm a * φ.symm b = h * (a' * b') * h⁻¹ := by simp only [a', b']; group
      _ = h * (b' * a') * h⁻¹ := by rw [e]
      _ = φ.symm b * φ.symm a := by simp only [a', b']; group
  have hcz : ∀ y : H, zC z * y = y * zC z := fun y => (mem_center_iff.mp (zC_mem_center z) y).symm
  have ha'1 : a' ≠ 1 := fun e => hab'' (by rw [e, one_mul, mul_one])
  have ha'z : a' ≠ zC z := fun e => hab'' (by rw [e]; exact hcz b')
  have hb'1 : b' ≠ 1 := fun e => hab'' (by rw [e, one_mul, mul_one])
  have hb'z : b' ≠ zC z := fun e => hab'' (by rw [e]; exact (hcz a').symm)
  obtain ⟨ka, hka⟩ := hinvE a' ha'E haa' ha'1 ha'z
  obtain ⟨kb, hkb⟩ := hinvE b' hb'E hbb' hb'1 hb'z
  have hconjH : ∀ (c : H) (k : G), (c : G) = k⁻¹ * z * k → c * t = t * c →
      (k * g⁻¹)⁻¹ * z * (k * g⁻¹) ∈ H ∧ (k * g⁻¹)⁻¹ * z * (k * g⁻¹) = g * c * g⁻¹ := by
    intro c k hk hc
    have e : (k * g⁻¹)⁻¹ * z * (k * g⁻¹) = g * c * g⁻¹ := by rw [hk]; group
    refine ⟨?_, e⟩
    rw [e, mem_centralizer_singleton_iff]
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, t] at this
    calc g * (c : G) * g⁻¹ * z = g * ((c : G) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [this]
      _ = z * (g * c * g⁻¹) := by group
  obtain ⟨hAH, hA⟩ := hconjH a' ka hka hat
  obtain ⟨hBH, hB⟩ := hconjH b' kb hkb hbt
  have hAE := (hfus _ hAH).1
  have hBE := (hfus _ hBH).1
  have hc1 : a' * b' * a'⁻¹ * b'⁻¹ = zC z := by
    refine (hcommE a' ha'E b' hb'E).resolve_left fun e => hab'' ?_
    calc a' * b' = a' * b' * a'⁻¹ * b'⁻¹ * (b' * a') := by group
      _ = b' * a' := by rw [e, one_mul]
  have hc1v : (a' : G) * b' * (a' : G)⁻¹ * (b' : G)⁻¹ = z := congrArg Subtype.val hc1
  have hval : ((⟨_, hAH⟩ : H) * ⟨_, hBH⟩ * (⟨_, hAH⟩ : H)⁻¹ * (⟨_, hBH⟩ : H)⁻¹ : H).val =
      g * z * g⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hA, hB]
    rw [← hc1v]
    group
  rcases hcommE _ hAE _ hBE with e | e
  · have := congrArg Subtype.val e
    rw [hval, OneMemClass.coe_one] at this
    exact hz1 (by
      have := congrArg (fun w => g⁻¹ * w * g) this
      simpa [mul_assoc] using this)
  · have := congrArg Subtype.val e
    rw [hval] at this
    exact hte (by
      have := congrArg (fun w => g⁻¹ * w * g) this
      simp only [zC] at this
      simpa [mul_assoc] using this.symm)

end Fusion

end CFSG.Sporadic.Co2Smith
