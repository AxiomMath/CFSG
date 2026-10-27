module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SMain
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section ShapeA

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.kerK_comm_conjSub {y : D} (hyA : y ∈ A) (hyT : y ∉ A ⊓ B) :
    ∀ k ∈ kerK B V, ∀ k' ∈ conjSub y (kerK B V), k * k' = k' * k := by
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := h.K_inf_conj_eq_bot hyA hyT
  have hKQ : kerK B V ≤ pCoreOf 2 A := h.K_le_QA
  have hK'Q : conjSub y (kerK B V) ≤ pCoreOf 2 A := h.conjSub_K_le_QA hyA
  have hQK : pCoreOf 2 A ≤ Subgroup.normalizer ((kerK B V : Subgroup D) : Set D) :=
    h.QA_le_normalizer_K
  have hQK' : pCoreOf 2 A ≤ Subgroup.normalizer ((conjSub y (kerK B V) : Subgroup D) : Set D) :=
    h.QA_le_normalizer_conjSub_K hyA
  intro k hk k' hk'
  have h1 : k' * k⁻¹ * k'⁻¹ ∈ kerK B V :=
    (Subgroup.mem_normalizer_iff.mp (hQK (hK'Q hk')) k⁻¹).mp ((kerK B V).inv_mem hk)
  have h2 : k * k' * k⁻¹ ∈ conjSub y (kerK B V) :=
    (Subgroup.mem_normalizer_iff.mp (hQK' (hKQ hk)) k').mp hk'
  have h3 : k * k' * k⁻¹ * k'⁻¹ ∈ kerK B V ⊓ conjSub y (kerK B V) := by
    refine ⟨?_, ?_⟩
    · have := (kerK B V).mul_mem hk h1
      have e : k * (k' * k⁻¹ * k'⁻¹) = k * k' * k⁻¹ * k'⁻¹ := by group
      rwa [e] at this
    · exact (conjSub y (kerK B V)).mul_mem h2 ((conjSub y (kerK B V)).inv_mem hk')
  rw [hint, Subgroup.mem_bot] at h3
  calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
    _ = k' * k := by rw [h3, one_mul]

theorem Hyp2.kerK_le_U : kerK B V ≤ conjClosure V B := by
  rw [h.kerK_eq_center_U]
  exact inf_le_left

theorem Hyp2.exists_cyclic_kerK (hT : Nat.card ↥(A ⊓ B) = 32) :
    ∃ w, w ∈ kerK B V ∧ w * w = z ∧ kerK B V = Subgroup.zpowers w := by
  by_contra hno
  obtain ⟨y, hyA, hyT⟩ := h.exists_y
  have hz1 : z * z = 1 := h.z_mul_z
  have hsq1 : ∀ w ∈ kerK B V, w * w = 1 := by
    intro w hw
    by_contra hw1
    apply hno
    have hwz : w * w = z := (h.mem_zpowers (h.sq_U w (h.kerK_le_U hw))).resolve_left hw1
    have hw2 : ¬ w ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hwz]; exact h.natural.z_ne
    have hw4 : w ^ 2 ^ (1 + 1) = 1 := by
      have e : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
      rw [e]
      calc w ^ 4 = (w * w) * (w * w) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := by rw [hwz, hz1]
    have hord : orderOf w = 2 ^ (1 + 1) := orderOf_eq_prime_pow hw2 hw4
    have hcard : Nat.card (Subgroup.zpowers w) = 4 := by
      rw [Nat.card_zpowers, hord]; norm_num
    refine ⟨w, hw, hwz, ?_⟩
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
      (by rw [hcard, h.card_kerK])).symm
  have hKK' := h.kerK_comm_conjSub hyA hyT
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := h.K_inf_conj_eq_bot hyA hyT
  have hcardK' : Nat.card ↥(conjSub y (kerK B V)) = 4 := by
    rw [card_conjSub]; exact h.card_kerK
  have hQA16 : Nat.card ↥(pCoreOf 2 A) = 16 := by
    have := h.card_T_QA
    omega
  have hKQ : kerK B V ≤ pCoreOf 2 A := h.K_le_QA
  have hK'Q : conjSub y (kerK B V) ≤ pCoreOf 2 A := h.conjSub_K_le_QA hyA
  have hr : ∀ r ∈ pCoreOf 2 A, ∃ k ∈ kerK B V, ∃ k' ∈ conjSub y (kerK B V), r = k * k' :=
    fun r hr => exists_mul_of_card_le hKQ hK'Q hint
      (by rw [hQA16, h.card_kerK, hcardK']) hr
  have hsq' : ∀ k' ∈ conjSub y (kerK B V), k' * k' = 1 := by
    intro k' hk'
    have h1 : y⁻¹ * k' * y ∈ kerK B V := mem_conjSub.mp hk'
    have h2 := hsq1 _ h1
    calc k' * k' = y * ((y⁻¹ * k' * y) * (y⁻¹ * k' * y)) * y⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hqq : ∀ q ∈ pCoreOf 2 A, q * q = 1 := by
    intro q hq
    obtain ⟨k, hk, k', hk', rfl⟩ := hr q hq
    calc k * k' * (k * k') = k * (k' * k) * k' := by group
      _ = k * (k * k') * k' := by rw [← hKK' k hk k' hk']
      _ = (k * k) * (k' * k') := by group
      _ = 1 := by rw [hsq1 k hk, hsq' k' hk', one_mul]
  have hcomm : ∀ q₁ ∈ pCoreOf 2 A, ∀ q₂ ∈ pCoreOf 2 A, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ h₁ q₂ h₂
    have h12 := hqq _ ((pCoreOf 2 A).mul_mem h₁ h₂)
    have e1 : q₁⁻¹ = q₁ := inv_eq_of_mul_eq_one_right (hqq q₁ h₁)
    have e2 : q₂⁻¹ = q₂ := inv_eq_of_mul_eq_one_right (hqq q₂ h₂)
    calc q₁ * q₂ = (q₁ * q₂)⁻¹ := (inv_eq_of_mul_eq_one_right h12).symm
      _ = q₂⁻¹ * q₁⁻¹ := mul_inv_rev _ _
      _ = q₂ * q₁ := by rw [e1, e2]
  have hle : pCoreOf 2 A ≤ V := fun q hq =>
    h.mem_V_of_center_QA ⟨hq, Subgroup.mem_centralizer_iff.mpr fun r hr => hcomm r hr q hq⟩
      (hqq q hq)
  have := Subgroup.card_le_of_le hle
  rw [hQA16, h.natural.card_eq] at this
  omega


omit h in
theorem card_multiplicative_zmod_four : Nat.card (Multiplicative (ZMod 4)) = 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 4))]
  exact Nat.card_zmod 4

theorem Hyp2.pCoreOf_left_mulEquiv (hT : Nat.card ↥(A ⊓ B) = 32) :
    Nonempty (↥(pCoreOf 2 A) ≃* Multiplicative (ZMod 4 × ZMod 4)) := by
  obtain ⟨w, hwK, hww, hKw⟩ := h.exists_cyclic_kerK hT
  obtain ⟨y, hyA, hyT⟩ := h.exists_y
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := h.K_inf_conj_eq_bot hyA hyT
  have hKQ : kerK B V ≤ pCoreOf 2 A := h.K_le_QA
  have hK'Q : conjSub y (kerK B V) ≤ pCoreOf 2 A := h.conjSub_K_le_QA hyA
  have hKK' := h.kerK_comm_conjSub hyA hyT
  have hcardK' : Nat.card ↥(conjSub y (kerK B V)) = 4 := by
    rw [card_conjSub]; exact h.card_kerK
  have hQA16 : Nat.card ↥(pCoreOf 2 A) = 16 := by
    have := h.card_T_QA
    omega
  let f : ↥(kerK B V) × ↥(conjSub y (kerK B V)) →* ↥(pCoreOf 2 A) :=
    (Subgroup.inclusion hKQ).noncommCoprod (Subgroup.inclusion hK'Q) (fun m n => by
      apply Subtype.ext
      exact hKK' m m.2 n n.2)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ hf
    have h1 : k * k' = 1 := congrArg Subtype.val hf
    have h2 : k ∈ kerK B V ⊓ conjSub y (kerK B V) := by
      refine ⟨hk, ?_⟩
      have : k = k'⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact (conjSub y (kerK B V)).inv_mem hk'
    rw [hint, Subgroup.mem_bot] at h2
    subst h2
    have : k' = 1 := by simpa using h1
    subst this
    rfl
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, hQA16]
    simp only [h.card_kerK, hcardK']
    norm_num
  have hcycK : IsCyclic ↥(kerK B V) := by rw [hKw]; infer_instance
  have hK'eq : conjSub y (kerK B V) = Subgroup.zpowers (y * w * y⁻¹) := by
    rw [hKw]
    unfold conjSub
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hcycK' : IsCyclic ↥(conjSub y (kerK B V)) := by rw [hK'eq]; infer_instance
  let e₁ : ↥(kerK B V) ≃* Multiplicative (ZMod 4) :=
    haveI := hcycK
    mulEquivOfCyclicCardEq (by rw [h.card_kerK, card_multiplicative_zmod_four])
  let e₂ : ↥(conjSub y (kerK B V)) ≃* Multiplicative (ZMod 4) :=
    haveI := hcycK'
    mulEquivOfCyclicCardEq (by rw [hcardK', card_multiplicative_zmod_four])
  exact ⟨(MulEquiv.ofBijective f hbij).symm.trans
    ((e₁.prodCongr e₂).trans (MulEquiv.prodMultiplicative (G := ZMod 4) (H := ZMod 4)).symm)⟩

end ShapeA


section Quat

variable {x a a₁ a₂ w : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.quat_ii (hwU : ∀ u ∈ conjClosure V B, w * u = u * w) (hww : w * w = z) :
    (a * w) * (a * w) = z := by
  calc (a * w) * (a * w) = a * (w * a) * w := by group
    _ = a * (a * w) * w := by rw [hwU a g.a_mem_U]
    _ = (a * a) * (w * w) := by group
    _ = z := by rw [g.a_sq, hww, one_mul]

theorem Gen.quat_jj (hwU : ∀ u ∈ conjClosure V B, w * u = u * w) (hww : w * w = z) :
    (a₁ * w) * (a₁ * w) = z := by
  calc (a₁ * w) * (a₁ * w) = a₁ * (w * a₁) * w := by group
    _ = a₁ * (a₁ * w) * w := by rw [hwU a₁ g.a₁_mem_U]
    _ = (a₁ * a₁) * (w * w) := by group
    _ = z := by rw [g.a₁_sq, hww, one_mul]

variable [Finite D] in
theorem Gen.quat_jij (hwU : ∀ u ∈ conjClosure V B, w * u = u * w) (hww : w * w = z) :
    (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = (a * w)⁻¹ := by
  have hwinv : w⁻¹ = w * z := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, hww, g.z_mul_z]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right g.a_sq
  have hwa : w * a = a * w := hwU a g.a_mem_U
  have hwa₁ : w * a₁ = a₁ * w := hwU a₁ g.a₁_mem_U
  have hzw : z * w = w * z := by
    have := hwU z g.hyp.z_mem_U
    exact this.symm
  have hconj : a₁ * a * a₁⁻¹ = z * a := conj_of_comm_eq (g.comm_symm g.comm01_eq)
  have hza : z * a = a * z := g.z_comm_a
  calc (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = (a₁ * a * a₁⁻¹) * (a₁ * w * a₁⁻¹) := by
        calc (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = a₁ * (w * a) * w * (w⁻¹ * a₁⁻¹) := by group
          _ = a₁ * (a * w) * w * (w⁻¹ * a₁⁻¹) := by rw [hwa]
          _ = (a₁ * a * a₁⁻¹) * (a₁ * w * a₁⁻¹) := by group
    _ = (z * a) * w := by
        rw [hconj]
        congr 1
        calc a₁ * w * a₁⁻¹ = (a₁ * w) * a₁⁻¹ := rfl
          _ = (w * a₁) * a₁⁻¹ := by rw [hwa₁]
          _ = w := by group
    _ = (a * w)⁻¹ := by
        rw [mul_inv_rev, hwinv, hainv]
        calc z * a * w = z * (a * w) := by group
          _ = z * (w * a) := by rw [hwa]
          _ = (z * w) * a := by group
          _ = (w * z) * a := by rw [hzw]

end Quat


section QuatEquiv

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.nonempty_kerK_mulEquiv (hT : Nat.card ↥(A ⊓ B) = 32) :
    Nonempty (↥(kerK B V) ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨w, hwK, hww, hKw⟩ := h.exists_cyclic_kerK hT
  have hcyc : IsCyclic ↥(kerK B V) := by rw [hKw]; infer_instance
  have := hcyc
  exact ⟨mulEquivOfCyclicCardEq (by rw [h.card_kerK, card_multiplicative_zmod_four])⟩

theorem Hyp2.isCentralProduct₂_of_card_inf_eq_32 (hT : Nat.card ↥(A ⊓ B) = 32) :
    IsCentralProduct₂ ↥(pCoreOf 2 B) (Multiplicative (ZMod 4)) (QuaternionGroup 2) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  obtain ⟨w, hwK, hww, hKw⟩ := h.exists_cyclic_kerK hT
  obtain ⟨e₁⟩ := h.nonempty_kerK_mulEquiv hT
  have hQB16 : Nat.card ↥(pCoreOf 2 B) = 16 := by
    have := h.card_T_QB
    omega
  have hUQ : conjClosure V B = pCoreOf 2 B :=
    Subgroup.eq_of_le_of_card_ge h.U_le (by rw [h.card_U, hQB16])
  have hwU : ∀ u ∈ conjClosure V B, w * u = u * w := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hwK.2 u hu).symm
  have hwUmem : w ∈ conjClosure V B := h.kerK_le_U hwK
  have hz1 : z ≠ 1 := h.natural.z_ne
  have hii : (a * w) * (a * w) = z := g.quat_ii hwU hww
  have hjj : (a₁ * w) * (a₁ * w) = z := g.quat_jj hwU hww
  have hjij : (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = (a * w)⁻¹ := g.quat_jij hwU hww
  have hiU : a * w ∈ conjClosure V B := (conjClosure V B).mul_mem g.a_mem_U hwUmem
  have hjU : a₁ * w ∈ conjClosure V B := (conjClosure V B).mul_mem g.a₁_mem_U hwUmem
  have hi2 : ¬ (a * w) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hii]; exact hz1
  have hi4 : (a * w) ^ 2 ^ (1 + 1) = 1 := by
    have e : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [e, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hii, h.z_mul_z]
  have hiord : orderOf (a * w) = 2 ^ (1 + 1) := orderOf_eq_prime_pow hi2 hi4
  have hZi : Nat.card (Subgroup.zpowers (a * w)) = 2 * 2 := by
    rw [Nat.card_zpowers, hiord]; norm_num
  have hgen : ∀ y : ↥(Subgroup.zpowers (a * w)),
      y ∈ Subgroup.zpowers (⟨a * w, Subgroup.mem_zpowers _⟩ : ↥(Subgroup.zpowers (a * w))) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨n, Subtype.ext (by simp)⟩
  let eZ := zmodMulEquivOfGenerator hgen hZi
  let coords : Multiplicative (ZMod (2 * 2)) →* D :=
    (Subgroup.zpowers (a * w)).subtype.comp eZ.toMonoidHom
  have hcoords_zpow : ∀ n : ℤ, coords (Multiplicative.ofAdd (n : ZMod (2 * 2))) = (a * w) ^ n := by
    intro n
    have := zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hZi n
    simp only [coords, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    change ((zmodMulEquivOfGenerator hgen hZi (Multiplicative.ofAdd (n : ZMod (2 * 2))) :
      ↥(Subgroup.zpowers (a * w))) : D) = _
    rw [this]
    simp
  have hcoords_mem : ∀ c, coords c ∈ Subgroup.zpowers (a * w) := fun c => (eZ c).2
  have hcinj : Function.Injective coords := Subtype.val_injective.comp eZ.injective
  have hJnot : a₁ * w ∉ coords.range := by
    rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    have hcomm : (a * w) * (a₁ * w) = (a₁ * w) * (a * w) := by
      rw [← hc, ← hn]
      exact ((Commute.refl (a * w)).zpow_right n).eq
    have h1 : (a₁ * w) * (a * w) * (a₁ * w)⁻¹ = a * w := by
      rw [← hcomm]; group
    rw [h1] at hjij
    have h2 : (a * w) * (a * w) = 1 := by
      calc (a * w) * (a * w) = (a * w) * (a * w)⁻¹⁻¹ := by rw [inv_inv]
        _ = (a * w)⁻¹ * (a * w)⁻¹⁻¹ := by rw [← hjij]
        _ = 1 := by rw [inv_inv]; group
    rw [hii] at h2
    exact hz1 h2
  have hsquare : (a₁ * w) ^ 2 = coords (Multiplicative.ofAdd (((2 : ℕ) : ZMod (2 * 2)))) := by
    have e1 := hcoords_zpow 2
    have e2 : (((2 : ℤ) : ZMod (2 * 2))) = ((2 : ℕ) : ZMod (2 * 2)) := by simp
    rw [e2] at e1
    rw [e1, pow_two, hjj, zpow_two, hii]
  have hinversion : ∀ c, (a₁ * w) * coords c * (a₁ * w)⁻¹ = (coords c)⁻¹ := by
    intro c
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    rw [← hn, ← conj_zpow, hjij, inv_zpow]
  let f : QuaternionGroup 2 →* D :=
    CFSG.DisconnectedInvolutionGraph.Helpers.quaternionCoordinateHom 2 coords (a₁ * w)
      hsquare hinversion
  have hty : ∀ p q : ZMod (2 * 2),
      coords (Multiplicative.ofAdd p) ≠ (a₁ * w) * coords (Multiplicative.ofAdd q) := by
    intro p q hpq
    apply hJnot
    have e : a₁ * w = coords (Multiplicative.ofAdd p) * (coords (Multiplicative.ofAdd q))⁻¹ := by
      rw [hpq]; group
    rw [e]
    exact coords.range.mul_mem ⟨_, rfl⟩ (coords.range.inv_mem ⟨_, rfl⟩)
  have hfinj : Function.Injective f := by
    intro p q hpq
    cases p with
    | a p =>
      cases q with
      | a q =>
        change coords (Multiplicative.ofAdd p) = coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.a (congrArg Multiplicative.toAdd (hcinj hpq))
      | xa q => exact (hty p q hpq).elim
    | xa p =>
      cases q with
      | a q => exact (hty q p hpq.symm).elim
      | xa q =>
        change (a₁ * w) * coords (Multiplicative.ofAdd p) =
          (a₁ * w) * coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.xa
          (congrArg Multiplicative.toAdd (hcinj (mul_left_cancel hpq)))
  have hIf : a * w ∈ f.range := by
    refine ⟨QuaternionGroup.a 1, ?_⟩
    change coords (Multiplicative.ofAdd (1 : ZMod (2 * 2))) = a * w
    have := hcoords_zpow 1
    simpa using this
  have hJf : a₁ * w ∈ f.range := by
    refine ⟨QuaternionGroup.xa 0, ?_⟩
    change (a₁ * w) * coords (Multiplicative.ofAdd (0 : ZMod (2 * 2))) = a₁ * w
    simp
  have hfU : f.range ≤ conjClosure V B := by
    rintro _ ⟨q, rfl⟩
    cases q with
    | a k =>
      change coords (Multiplicative.ofAdd k) ∈ conjClosure V B
      exact Subgroup.zpowers_le.mpr hiU (hcoords_mem _)
    | xa k =>
      change (a₁ * w) * coords (Multiplicative.ofAdd k) ∈ conjClosure V B
      exact (conjClosure V B).mul_mem hjU (Subgroup.zpowers_le.mpr hiU (hcoords_mem _))
  have hfcard : Nat.card f.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hKQ : kerK B V ≤ pCoreOf 2 B := inf_le_left
  have hBQ : f.range ≤ pCoreOf 2 B := hUQ ▸ hfU
  have hc₀ : a * a₁ * a₂ ∈ kerK B V := by
    rw [h.kerK_eq_center_U]; exact g.c_mem_center
  have hwinv : w⁻¹ ∈ kerK B V := (kerK B V).inv_mem hwK
  have hgens : ∀ S : Subgroup D, a * w ∈ S → a₁ * w ∈ S → w ∈ S → a * a₁ * a₂ ∈ S →
      conjClosure V B ≤ S := by
    intro S hiS hjS hwS hcS
    have haS : a ∈ S := by
      have e : a = (a * w) * w⁻¹ := by group
      rw [e]; exact S.mul_mem hiS (S.inv_mem hwS)
    have ha₁S : a₁ ∈ S := by
      have e : a₁ = (a₁ * w) * w⁻¹ := by group
      rw [e]; exact S.mul_mem hjS (S.inv_mem hwS)
    have hzS : z ∈ S := by rw [← hww]; exact S.mul_mem hwS hwS
    have ha₂S : a₂ ∈ S := by
      have e : a₂ = a₁⁻¹ * a⁻¹ * (a * a₁ * a₂) := by group
      rw [e]; exact S.mul_mem (S.mul_mem (S.inv_mem ha₁S) (S.inv_mem haS)) hcS
    rw [g.U_eq_closure, Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht | ht <;> rw [ht] <;> assumption
  have hKB : kerK B V ⊔ f.range = pCoreOf 2 B := by
    refine le_antisymm (sup_le hKQ hBQ) ?_
    rw [← hUQ]
    exact hgens _ (Subgroup.mem_sup_right hIf) (Subgroup.mem_sup_right hJf)
      (Subgroup.mem_sup_left hwK) (Subgroup.mem_sup_left hc₀)
  have hKnotle : ¬ kerK B V ≤ f.range := by
    intro hle
    have hUle := hgens f.range hIf hJf (hle hwK) (hle hc₀)
    have := Subgroup.card_le_of_le hUle
    rw [h.card_U, hfcard] at this
    omega
  have hzKB : z ∈ kerK B V ⊓ f.range :=
    ⟨h.center_U_le_K h.z_mem_center_U, by rw [← hii]; exact f.range.mul_mem hIf hIf⟩
  have hKB2 : Nat.card ↥(kerK B V ⊓ f.range) = 2 := by
    have hdvd : Nat.card ↥(kerK B V ⊓ f.range) ∣ Nat.card ↥(kerK B V) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h.card_kerK] at hdvd
    have hge : 2 ≤ Nat.card ↥(kerK B V ⊓ f.range) := by
      have hle : Subgroup.zpowers z ≤ kerK B V ⊓ f.range := Subgroup.zpowers_le.mpr hzKB
      have := Subgroup.card_le_of_le hle
      rwa [h.card_zpowers] at this
    have hne4 : Nat.card ↥(kerK B V ⊓ f.range) ≠ 4 := by
      intro h4
      apply hKnotle
      have e : kerK B V ⊓ f.range = kerK B V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, h.card_kerK])
      rw [← e]; exact inf_le_right
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hdvd
    generalize Nat.card ↥(kerK B V ⊓ f.range) = m at *
    interval_cases m <;> omega
  refine ⟨(kerK B V).subgroupOf (pCoreOf 2 B), f.range.subgroupOf (pCoreOf 2 B), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hKQ hBQ, hKB, Subgroup.subgroupOf_self]
  · intro a' ha' b' hb'
    apply Subtype.ext
    have haK : (a' : D) ∈ kerK B V := ha'
    have hbU : (b' : D) ∈ conjClosure V B := hfU hb'
    exact (Subgroup.mem_centralizer_iff.mp haK.2 _ hbU).symm
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hKQ).trans e₁⟩
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hBQ).trans (MonoidHom.ofInjective hfinj).symm⟩
  · have e : (kerK B V).subgroupOf (pCoreOf 2 B) ⊓ f.range.subgroupOf (pCoreOf 2 B) =
        (kerK B V ⊓ f.range).subgroupOf (pCoreOf 2 B) := (Subgroup.comap_inf _ _ _).symm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKQ)).toEquiv]
    exact hKB2

end QuatEquiv

end GoldAmL2S

end F6

end CFSG.Quasithin
