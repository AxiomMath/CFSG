module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2
public import CFSG.RankThree.PartOne.SEITZ4.SpConf
public import CFSG.RankThree.PartOne.SEITZ4.SpQ

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.CTP

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spT (a : Fin r ⊕ Fin r → K) (c : K) : StatedSp r K :=
  ⟨spTrans a c, spTrans_mem_statedSp a c⟩

theorem spMat_spT (a : Fin r ⊕ Fin r → K) (c : K) (x : Fin r ⊕ Fin r → K) :
    spMat (spT a c) *ᵥ x = x + (c * spForm r K x a) • a :=
  spTrans_mulVec a c x

theorem eq_zero_or_one_of_card_two {k : Subfield K} (hk : Nat.card k = 2) {c : K} (hc : c ∈ k) :
    c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  have h1 : (⟨1, k.one_mem⟩ : k) = y := huniq _ (fun h' => one_ne_zero (congrArg Subtype.val h'))
  have h2 : (⟨c, hc⟩ : k) = y := huniq _ (fun h' => h.1 (congrArg Subtype.val h'))
  exact h.2 (congrArg Subtype.val (h2.trans h1.symm))

section Char2

variable [CharP K 2]

theorem planeHom_apply {e u' : Fin r ⊕ Fin r → K} (hvw : spForm r K e u' = 1)
    (m : Matrix.SpecialLinearGroup (Fin 2) K) (c₁ c₂ : K) :
    spMat (planeHom hvw m) *ᵥ (c₁ • e + c₂ • u') =
      ((m : Matrix (Fin 2) (Fin 2) K) 0 0 * c₁ + (m : Matrix (Fin 2) (Fin 2) K) 0 1 * c₂) • e +
        ((m : Matrix (Fin 2) (Fin 2) K) 1 0 * c₁ + (m : Matrix (Fin 2) (Fin 2) K) 1 1 * c₂) •
          u' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu'e : spForm r K u' e = 1 := by rw [spForm_comm']; exact hvw
  have hee : spForm r K e e = 0 := spForm_self e
  have huu : spForm r K u' u' = 0 := spForm_self u'
  change planeMat e u' (m : Matrix (Fin 2) (Fin 2) K) *ᵥ (c₁ • e + c₂ • u') = _
  rw [planeMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hee, huu,
    hvw, hu'e, mul_zero, zero_add, add_zero, mul_one]
  match_scalars
  · linear_combination c₁ * h2
  · linear_combination c₂ * h2

theorem planeHom_fix {e u' : Fin r ⊕ Fin r → K} (hvw : spForm r K e u' = 1)
    (m : Matrix.SpecialLinearGroup (Fin 2) K) {x : Fin r ⊕ Fin r → K}
    (hxe : spForm r K x e = 0) (hxu : spForm r K x u' = 0) : spMat (planeHom hvw m) *ᵥ x = x := by
  change planeMat e u' (m : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x
  rw [planeMat_mulVec, hxe, hxu]
  simp

theorem planeHom_u2 {e u' : Fin r ⊕ Fin r → K} (hvw : spForm r K e u' = 1) (c : K) :
    planeHom hvw (u2 c) = spT e c :=
  Subtype.ext (planeHom_upper hvw (u2 c) c (u2_coe c))

theorem planeHom_l2 {e u' : Fin r ⊕ Fin r → K} (hvw : spForm r K e u' = 1) (c : K) :
    planeHom hvw (l2 c) = spT u' c :=
  Subtype.ext (planeHom_lower hvw (l2 c) c (l2_coe c))

noncomputable def liftSub (H : Subgroup (StatedSp r K)) (z e u' : Fin r ⊕ Fin r → K)
    (hvw : spForm r K e u' = 1) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {m | ∃ n ∈ H, spMat n *ᵥ z = z ∧ ∀ c₁ c₂ : K, ∃ t : K,
    spMat n *ᵥ (c₁ • e + c₂ • u') = spMat (planeHom hvw m) *ᵥ (c₁ • e + c₂ • u') + t • z}
  one_mem' := ⟨1, H.one_mem, by simp [spMat], fun c₁ c₂ => ⟨0, by simp [spMat]⟩⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨n₁, hn₁, hz₁, P₁⟩ ⟨n₂, hn₂, hz₂, P₂⟩
    refine ⟨n₁ * n₂, H.mul_mem hn₁ hn₂, by rw [spMat_mul_mulVec, hz₂, hz₁], fun c₁ c₂ => ?_⟩
    obtain ⟨t₂, ht₂⟩ := P₂ c₁ c₂
    set y₂ := spMat (planeHom hvw m₂) *ᵥ (c₁ • e + c₂ • u') with hy₂
    obtain ⟨c₁', c₂', hc'⟩ : ∃ c₁' c₂' : K, y₂ = c₁' • e + c₂' • u' := by
      rw [hy₂, planeHom_apply]
      exact ⟨_, _, rfl⟩
    obtain ⟨t₁, ht₁⟩ := P₁ c₁' c₂'
    refine ⟨t₁ + t₂, ?_⟩
    have e1 : spMat n₁ *ᵥ y₂ =
        spMat (planeHom hvw (m₁ * m₂)) *ᵥ (c₁ • e + c₂ • u') + t₁ • z := by
      rw [hc', ht₁, ← hc', hy₂, ← spMat_mul_mulVec, ← map_mul]
    rw [spMat_mul_mulVec, ht₂, mulVec_add, mulVec_smul, hz₁, e1, add_assoc, ← add_smul]
  inv_mem' := by
    rintro m ⟨n, hn, hz, P⟩
    refine ⟨n⁻¹, H.inv_mem hn, ?_, fun c₁ c₂ => ?_⟩
    · have := spMat_inv_mulVec_mulVec n z
      rwa [hz] at this
    · set y' := spMat (planeHom hvw m⁻¹) *ᵥ (c₁ • e + c₂ • u') with hy'
      obtain ⟨c₁', c₂', hc'⟩ : ∃ c₁' c₂' : K, y' = c₁' • e + c₂' • u' := by
        rw [hy', planeHom_apply]
        exact ⟨_, _, rfl⟩
      obtain ⟨t, ht⟩ := P c₁' c₂'
      have hP : spMat (planeHom hvw m) *ᵥ y' = c₁ • e + c₂ • u' := by
        rw [hy', ← spMat_mul_mulVec, ← map_mul, mul_inv_cancel, map_one]
        simp [spMat]
      rw [← hc', hP] at ht
      refine ⟨-t, ?_⟩
      have h1 : spMat n⁻¹ *ᵥ (spMat n *ᵥ y') = y' := spMat_inv_mulVec_mulVec n y'
      rw [ht, mulVec_add, mulVec_smul] at h1
      have hz' : spMat n⁻¹ *ᵥ z = z := by
        have := spMat_inv_mulVec_mulVec n z
        rwa [hz] at this
      rw [hz'] at h1
      rw [neg_smul]
      exact eq_add_neg_of_add_eq h1

theorem u2_one_mem_liftSub {H : Subgroup (StatedSp r K)} {z e u' : Fin r ⊕ Fin r → K}
    (hvw : spForm r K e u' = 1) (hTe : spT e 1 ∈ H) (hze : spForm r K z e = 0) :
    u2 (1 : K) ∈ liftSub H z e u' hvw := by
  refine ⟨spT e 1, hTe, ?_, fun c₁ c₂ => ⟨0, ?_⟩⟩
  · rw [spMat_spT, hze]
    simp
  · rw [planeHom_u2, zero_smul, add_zero]

theorem l2_sq_mem_liftSub {H : Subgroup (StatedSp r K)} {z e u' : Fin r ⊕ Fin r → K}
    (hvw : spForm r K e u' = 1) (c : K) (hT : spT (c • u') 1 ∈ H) (hzu : spForm r K z u' = 0) :
    l2 (c ^ 2) ∈ liftSub H z e u' hvw := by
  have hspT : spT (c • u') 1 = spT u' (c ^ 2) :=
    Subtype.ext (by rw [show ((spT (c • u') 1 : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      spTrans (c • u') 1 from rfl, spTrans_smul, mul_one]; rfl)
  refine ⟨spT (c • u') 1, hT, ?_, fun c₁ c₂ => ⟨0, ?_⟩⟩
  · rw [spMat_spT, map_smul, hzu]
    simp
  · rw [planeHom_l2, ← hspT, zero_smul, add_zero]

theorem u2_sq_mem_liftSub {H : Subgroup (StatedSp r K)} {z e u' w : Fin r ⊕ Fin r → K}
    (hvw : spForm r K e u' = 1) {β₁ β₂ : K} (hTw : spT w 1 ∈ H)
    (hzw : spForm r K z w = 0) (hw : w = β₁⁻¹ • z + (β₁⁻¹ * β₂) • e)
    (hew : spForm r K e w = 0) (hu'w : spForm r K u' w = β₁⁻¹ * β₂) :
    u2 ((β₂ * β₁⁻¹) ^ 2) ∈ liftSub H z e u' hvw := by
  have hee : spForm r K e e = 0 := spForm_self e
  have hu'e : spForm r K u' e = 1 := by rw [spForm_comm']; exact hvw
  refine ⟨spT w 1, hTw, ?_, fun c₁ c₂ => ⟨c₂ * β₁⁻¹ * β₁⁻¹ * β₂, ?_⟩⟩
  · rw [spMat_spT, hzw]
    simp
  · have hBw : spForm r K (c₁ • e + c₂ • u') w = c₂ * (β₁⁻¹ * β₂) := by
      rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
        LinearMap.smul_apply, hew, hu'w]
      simp
    have hBe : spForm r K (c₁ • e + c₂ • u') e = c₂ := by
      rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
        LinearMap.smul_apply, hee, hu'e]
      simp
    rw [planeHom_u2, spMat_spT, spMat_spT, hBw, hBe]
    conv_lhs => rw [hw]
    match_scalars <;> ring

structure F2Hyp (k : Subfield K) (H : Subgroup (StatedSp r K)) (e w u : Fin r ⊕ Fin r → K) :
    Prop where
  isRat_e : IsRat k e
  isRat_w : IsRat k w
  orth : spForm r K e w = 0
  trans_u : spT u 1 ∈ H
  beta1 : spForm r K e u ≠ 0
  beta2 : spForm r K w u ≠ 0
  beta12 : spForm r K w u ≠ spForm r K e u

theorem z_mem_rootSet [Finite K] {k : Subfield K}
    {H : Subgroup (StatedSp r K)} (hH : spSub r k ≤ H) (hk2 : Nat.card k = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) {e w u : Fin r ⊕ Fin r → K}
    (h : F2Hyp k H e w u) :
    (spForm r K w u • e + spForm r K e u • w) ∈ rootSet H := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set β₁ := spForm r K e u with hβ₁def
  set β₂ := spForm r K w u with hβ₂def
  have hβ₁ : β₁ ≠ 0 := h.beta1
  have hβ₂ : β₂ ≠ 0 := h.beta2
  have hβ₁₂ : β₂ ≠ β₁ := h.beta12
  set z : Fin r ⊕ Fin r → K := β₂ • e + β₁ • w with hz
  set u' : Fin r ⊕ Fin r → K := β₁⁻¹ • u with hu'
  have hvw : spForm r K e u' = 1 := by
    rw [hu', map_smul, smul_eq_mul, inv_mul_cancel₀ hβ₁]
  have hee : spForm r K e e = 0 := spForm_self e
  have hww : spForm r K w w = 0 := spForm_self w
  have hew : spForm r K e w = 0 := h.orth
  have hwe : spForm r K w e = 0 := by rw [spForm_comm']; exact hew
  have hue : spForm r K u e = β₁ := by rw [spForm_comm']
  have hze : spForm r K z e = 0 := by
    rw [hz, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, hee, hwe]
    simp
  have hzw : spForm r K z w = 0 := by
    rw [hz, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, hew, hww]
    simp
  have hzu : spForm r K z u = 0 := by
    rw [hz, map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, ← hβ₁def, ← hβ₂def]
    linear_combination (β₁ * β₂) * h2
  have hzu' : spForm r K z u' = 0 := by
    rw [hu', map_smul, hzu, smul_zero]
  have hw : w = β₁⁻¹ • z + (β₁⁻¹ * β₂) • e := by
    rw [hz]
    match_scalars <;> field_simp
    linear_combination (-β₂) * h2
  have hTe : spT e 1 ∈ H := hH (spTrans_mem_spSub k h.isRat_e k.one_mem)
  have hTw : spT w 1 ∈ H := hH (spTrans_mem_spSub k h.isRat_w k.one_mem)
  have hTew : spT (e + w) 1 ∈ H :=
    hH (spTrans_mem_spSub k (isRat_add h.isRat_e h.isRat_w) k.one_mem)
  have hu'u : β₁ • u' = u := by rw [hu', smul_smul, mul_inv_cancel₀ hβ₁, one_smul]
  have hTu : spT (β₁ • u') 1 ∈ H := by
    rw [hu'u]
    exact h.trans_u
  have hu'w : spForm r K u' w = β₁⁻¹ * β₂ := by
    rw [hu', map_smul, LinearMap.smul_apply, smul_eq_mul, spForm_comm' u w]
  have hγ : (β₂ * β₁⁻¹) ^ 2 ∉ k := by
    intro hmem
    have hk' : β₂ * β₁⁻¹ ∈ k := mem_subfield_of_sq_mem k hmem
    rcases eq_zero_or_one_of_card_two hk2 hk' with h0 | h1
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · exact hβ₂ h0
      · exact inv_ne_zero hβ₁ h0
    · exact hβ₁₂ (by field_simp at h1; exact h1)
  have hM : liftSub H z e u' hvw = ⊤ := by
    refine sl2_eq_top_of_root_groups hp hp2 hK (a₁ := 1) (a₂ := (β₂ * β₁⁻¹) ^ 2) (b₀ := β₁ ^ 2)
      one_ne_zero (by simpa using hγ) (pow_ne_zero 2 hβ₁) ?_
      (l2_sq_mem_liftSub hvw β₁ hTu hzu')
    intro c₁ hc₁ c₂ hc₂
    have hu1 : u2 (1 : K) ∈ liftSub H z e u' hvw := u2_one_mem_liftSub hvw hTe hze
    have huγ : u2 ((β₂ * β₁⁻¹) ^ 2) ∈ liftSub H z e u' hvw :=
      u2_sq_mem_liftSub hvw hTw hzw hw hew hu'w
    rcases eq_zero_or_one_of_card_two hk2 hc₁ with rfl | rfl <;>
      rcases eq_zero_or_one_of_card_two hk2 hc₂ with rfl | rfl
    · simp [u2_zero]
    · simpa using huγ
    · simpa using hu1
    · rw [show (1 : K) * 1 + 1 * (β₂ * β₁⁻¹) ^ 2 = 1 + (β₂ * β₁⁻¹) ^ 2 by ring, u2_add]
      exact (liftSub H z e u' hvw).mul_mem hu1 huγ
  set a : Fin r ⊕ Fin r → K := β₁⁻¹ • e with ha
  have hza : spForm r K z a = 0 := by rw [ha, map_smul, hze, smul_zero]
  have hSq : qSp z a 0 hza ∈ H := by
    have hq : qSp z a 0 hza = spT (e + w) 1 * spT e 1 * spT w 1 :=
      qSp_shortRoot (e := e) (w := w) (β₁ := β₁) (β₂ := β₂) hew hβ₁ hza
    rw [hq]
    exact H.mul_mem (H.mul_mem hTew hTe) hTw
  have key : ∀ (X Y : Fin r ⊕ Fin r → K) (hX : spForm r K z X = 0) (hY : spForm r K z Y = 0),
      X = Y → qSp z X 0 hX = qSp z Y 0 hY := by
    intro X Y hX hY hXY
    subst hXY
    rfl
  have hQ : ∀ m : Matrix.SpecialLinearGroup (Fin 2) K,
      ∃ hb : spForm r K z (spMat (planeHom hvw m) *ᵥ a) = 0,
        qSp z (spMat (planeHom hvw m) *ᵥ a) 0 hb ∈ H := by
    intro m
    have hm : m ∈ liftSub H z e u' hvw := hM ▸ Subgroup.mem_top m
    obtain ⟨n, hn, hnz, hP⟩ := hm
    obtain ⟨t, ht⟩ := hP β₁⁻¹ 0
    have ha' : β₁⁻¹ • e + (0 : K) • u' = a := by rw [ha, zero_smul, add_zero]
    rw [ha'] at ht
    have hna : spForm r K z (spMat n *ᵥ a) = 0 := by
      have := spForm_mulVec n.2 z a
      rw [show ((n : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z = z
        from hnz] at this
      rw [this]
      exact hza
    have hb : spForm r K z (spMat (planeHom hvw m) *ᵥ a) = 0 := by
      have hz' : spMat (planeHom hvw m) *ᵥ z = z := planeHom_fix hvw m hze hzu'
      have := spForm_mulVec (planeHom hvw m).2 z a
      rw [show ((planeHom hvw m : StatedSp r K) : GL (Fin r ⊕ Fin r) K).1 *ᵥ z = z from hz'] at this
      rw [show spMat (planeHom hvw m) *ᵥ a = _ from rfl, this]
      exact hza
    refine ⟨hb, ?_⟩
    have hconj : n * qSp z a 0 hza * n⁻¹ = qSp z (spMat n *ᵥ a) 0 hna :=
      conj_qSp n z a 0 hnz hza hna
    have hmem : n * qSp z a 0 hza * n⁻¹ ∈ H := H.mul_mem (H.mul_mem hn hSq) (H.inv_mem hn)
    rw [hconj] at hmem
    have hhb : spForm r K z (spMat (planeHom hvw m) *ᵥ a + t • z) = 0 := by
      rw [map_add, map_smul, hb, spForm_self, smul_zero, add_zero]
    have h1 := key _ _ hna hhb ht
    have h2' := qSp_add_smul z (spMat (planeHom hvw m) *ᵥ a) 0 t hb hhb
    rw [h1, h2'] at hmem
    exact hmem
  have hu'e : spForm r K u' e = 1 := by rw [spForm_comm']; exact hvw
  have hT : ∀ lam : K, spT z lam ∈ H := by
    intro lam
    by_cases hl : lam = 0
    · have : spT z (0 : K) = 1 := Subtype.ext (spTrans_zero z)
      rw [hl, this]
      exact H.one_mem
    · set d : K := lam * β₁ ^ 2 with hd
      have hd0 : d ≠ 0 := mul_ne_zero hl (pow_ne_zero 2 hβ₁)
      set μ : K := d * β₁⁻¹ with hμ
      set b₂ : Fin r ⊕ Fin r → K := μ • u' with hb₂
      have hb₂z : spForm r K z b₂ = 0 := by rw [hb₂, map_smul, hzu', smul_zero]
      have hab : spForm r K z (a + b₂) = 0 := by rw [map_add, hza, hb₂z, add_zero]
      have ha2 : a = β₁⁻¹ • e + (0 : K) • u' := by rw [ha, zero_smul, add_zero]
      have hP₃ : spMat (planeHom hvw (l2 d)) *ᵥ a = a + b₂ := by
        rw [ha2, planeHom_apply, l2_coe, ← ha2]
        simp [hb₂, hμ, ha]
      have hP₂ : spMat (planeHom hvw (u2 d⁻¹ * l2 d)) *ᵥ a = b₂ := by
        rw [ha2, planeHom_apply, Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two, hb₂, hμ, hd0, one_add_one_eq_two, h2]
      have hq₂ : qSp z b₂ 0 hb₂z ∈ H := by
        obtain ⟨hb, hm⟩ := hQ (u2 d⁻¹ * l2 d)
        rwa [key _ _ hb hb₂z hP₂] at hm
      have hq₃ : qSp z (a + b₂) 0 hab ∈ H := by
        obtain ⟨hb, hm⟩ := hQ (l2 d)
        rwa [key _ _ hb hab hP₃] at hm
      have h3 := qSp_three z a b₂ hza hb₂z hab
      have hmem := H.mul_mem (H.mul_mem hSq hq₂) hq₃
      rw [h3] at hmem
      have hBb : spForm r K b₂ a = lam := by
        rw [hb₂, ha, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, hu'e, hμ,
          hd]
        field_simp
      rw [hBb] at hmem
      exact hmem
  exact fun c => hT c
theorem eq_top_of_F2Hyp [Finite K] {k : Subfield K}
    {H : Subgroup (StatedSp r K)} (hH : spSub r k ≤ H) (hk2 : Nat.card k = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) {e w u : Fin r ⊕ Fin r → K}
    (h : F2Hyp k H e w u) : H = ⊤ := by
  have hz := z_mem_rootSet hH hk2 hp hp2 hK h
  set β₁ := spForm r K e u with hβ₁def
  set β₂ := spForm r K w u with hβ₂def
  have hβ₂ : β₂ ≠ 0 := h.beta2
  have hβ₁₂ : β₂ ≠ β₁ := h.beta12
  set z : Fin r ⊕ Fin r → K := β₂ • e + β₁ • w with hz'
  have he0 : e ≠ 0 := fun h0 => h.beta1 (by rw [h0, map_zero, LinearMap.zero_apply])
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp he0
  set s : Fin r ⊕ Fin r → K := Pi.single i₀.swap 1 with hs
  have hsr : IsRat k s := isRat_single k _
  have hBes : spForm r K e s = 1 := by
    rw [hs, spForm_single_right, Sum.swap_swap]
    rcases eq_zero_or_one_of_card_two hk2 (h.isRat_e i₀) with h0 | h1
    · exact absurd h0 (by simpa using hi₀)
    · exact h1
  have hBws : spForm r K w s = 0 ∨ spForm r K w s = 1 :=
    eq_zero_or_one_of_card_two hk2 (spForm_mem_of_isRat h.isRat_w hsr)
  set δ : K := spForm r K z s with hδdef
  have hδ : δ ≠ 0 := by
    have hδe : δ = β₂ * 1 + β₁ * spForm r K w s := by
      rw [hδdef, hz', map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
        LinearMap.smul_apply, hBes, smul_eq_mul, smul_eq_mul]
    rcases hBws with h0 | h1
    · rw [hδe, h0]
      simpa using hβ₂
    · rw [hδe, h1]
      intro h'
      apply hβ₁₂
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h' - β₁ * h2
  have hTs : spT s 1 ∈ H := hH (spTrans_mem_spSub k hsr k.one_mem)
  have hzz : spMat (spT s 1) *ᵥ z = z + δ • s := by
    rw [spMat_spT, one_mul]
  have hzs' : (z + δ • s) ∈ rootSet H := by
    rw [← hzz]
    exact mulVec_mem_rootSet hz hTs
  have hab : spForm r K z (z + δ • s) ≠ 0 := by
    rw [map_add, map_smul, spForm_self, zero_add, smul_eq_mul]
    exact mul_ne_zero hδ hδ
  have hδs : δ • s ∈ rootSet H := by
    have := add_smul_mem_rootSet hz hzs' hab 1
    rwa [one_smul, ← add_assoc, add_self_vec', zero_add] at this
  have hsm : s ∈ rootSet H := by
    have := smul_mem_rootSet hδs δ⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hδ, one_smul] at this
  exact eq_top_of_rootSet_eq_univ (rootSet_eq_univ hH hsm hsr (single_ne_zero _))

theorem eq_top_of_rank_one [Finite K] {k : Subfield K}
    {H : Subgroup (StatedSp r K)} (hH : spSub r k ≤ H) (hk2 : Nat.card k = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) {v : Fin r ⊕ Fin r → K}
    (hvr : IsRat k v) (hv0 : v ≠ 0) {b : K} (hb : b ∉ k) (hT : spT (b • v) 1 ∈ H) : H = ⊤ := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv0
  set s : Fin r ⊕ Fin r → K := Pi.single i₀.swap 1 with hs
  have hsr : IsRat k s := isRat_single k _
  have hvs : spForm r K v s = 1 := by
    rw [hs, spForm_single_right, Sum.swap_swap]
    rcases eq_zero_or_one_of_card_two hk2 (hvr i₀) with h0 | h1
    · exact absurd h0 (by simpa using hi₀)
    · exact h1
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := H.comap (planeHom hvs) with hM
  have hu1 : u2 (1 : K) ∈ M := by
    show planeHom hvs (u2 1) ∈ H
    rw [planeHom_u2]
    exact hH (spTrans_mem_spSub k hvr k.one_mem)
  have hub : u2 (b ^ 2) ∈ M := by
    show planeHom hvs (u2 (b ^ 2)) ∈ H
    rw [planeHom_u2]
    have : spT v (b ^ 2) = spT (b • v) 1 :=
      Subtype.ext (by
        rw [show ((spT (b • v) 1 : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
          spTrans (b • v) 1 from rfl, spTrans_smul, mul_one]
        rfl)
    rw [this]
    exact hT
  have hl1 : l2 (1 : K) ∈ M := by
    show planeHom hvs (l2 1) ∈ H
    rw [planeHom_l2]
    exact hH (spTrans_mem_spSub k hsr k.one_mem)
  have hMtop : M = ⊤ := by
    refine sl2_eq_top_of_root_groups hp hp2 hK (a₁ := 1) (a₂ := b ^ 2) (b₀ := 1) one_ne_zero
      (by simpa using fun h => hb (mem_subfield_of_sq_mem k h)) one_ne_zero ?_ hl1
    intro c₁ hc₁ c₂ hc₂
    rcases eq_zero_or_one_of_card_two hk2 hc₁ with rfl | rfl <;>
      rcases eq_zero_or_one_of_card_two hk2 hc₂ with rfl | rfl
    · simp [u2_zero]
    · simpa using hub
    · simpa using hu1
    · rw [show (1 : K) * 1 + 1 * b ^ 2 = 1 + b ^ 2 by ring, u2_add]
      exact M.mul_mem hu1 hub
  have hv : v ∈ rootSet H := fun c => by
    have hc : u2 c ∈ M := hMtop ▸ Subgroup.mem_top _
    have h' : planeHom hvs (u2 c) ∈ H := hc
    rwa [planeHom_u2] at h'
  exact eq_top_of_rootSet_eq_univ (rootSet_eq_univ hH hv hvr hv0)

theorem subfieldPairSp_of_card_two [Finite K] {r : ℕ} (hr : 2 ≤ r)
    (k : Subfield K) (hk2 : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = Nat.card k ^ p) (A : gsp r K)
    (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
      ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤ := by
  classical
  set G₀ := spSub r k with hG₀def
  set G₁ := G₀.map (conjSp r K A).toMonoidHom with hG₁def
  set H := Subgroup.closure ((G₀ : Set (StatedSp r K)) ∪ (G₁ : Set (StatedSp r K))) with hH
  have hG₀ : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hG₁ : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  obtain ⟨g, hg1, i, j, hij⟩ := exists_entry_not_mem k A hne
  have hgH : g ∈ H := hG₁ hg1
  set s' : Fin r ⊕ Fin r → K := Pi.single j 1 with hs'
  set u : Fin r ⊕ Fin r → K := spMat g *ᵥ s' with hu
  have hTu : spT u 1 ∈ H := by
    have e : g * spT s' 1 * g⁻¹ = spT u 1 :=
      Subtype.ext (conj_spTrans g.2 s' 1)
    rw [← e]
    exact H.mul_mem (H.mul_mem hgH (hG₀ (spTrans_mem_spSub k (isRat_single k _) k.one_mem)))
      (H.inv_mem hgH)
  have hui : u i ∉ k := by
    have : u i = ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j := by
      rw [hu, hs', Matrix.mulVec_single_one]
      rfl
    rw [this]
    exact hij
  have hp2 : p ≠ 2 := by omega
  by_cases hrank : ∃ i₁ j₁, u i₁ ≠ 0 ∧ u j₁ ≠ 0 ∧ u j₁ ≠ u i₁
  · obtain ⟨i₁, j₁, h1, h2, h3⟩ := hrank
    obtain ⟨e, w, he, hw, hew, hβ1, hβ2, hβ12⟩ := exists_orthogonal_pair k hr h1 h2 h3
    exact eq_top_of_F2Hyp hG₀ hk2 hp hp2 hK ⟨he, hw, hew, hTu, hβ1, hβ2, hβ12⟩
  · push Not at hrank
    have hi0 : u i ≠ 0 := fun h0 => hui (h0 ▸ k.zero_mem)
    set v : Fin r ⊕ Fin r → K := fun l => if u l = 0 then 0 else 1 with hv
    have hvr : IsRat k v := fun l => by
      simp only [hv]
      split_ifs
      · exact k.zero_mem
      · exact k.one_mem
    have hvi : v i = 1 := by simp [hv, hi0]
    have hv0 : v ≠ 0 := fun h0 => by simp [h0] at hvi
    have huv : u = u i • v := by
      funext l
      by_cases hl : u l = 0
      · simp [hv, hl]
      · simp [hv, hrank i l hi0 hl]
    exact eq_top_of_rank_one hG₀ hk2 hp hp2 hK hvr hv0 hui (by rw [← huv]; exact hTu)

end Char2

end CFSG.RankThree.PartOne.SEITZ4
