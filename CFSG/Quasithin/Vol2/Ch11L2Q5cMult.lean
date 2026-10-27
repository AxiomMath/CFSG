module

public import CFSG.Quasithin.Vol2.Ch11SecHInputs
public import CFSG.Quasithin.Vol2.Ch11L2Q5cMultForm
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SL2Borel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open scoped MatrixGroups commutatorElement Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL diagSL_conj unipSL_mul_self
  unipSL_zero unipHom unipHom_apply unipHom_injective card_SL_two_pow odd_four_pow_sub_one)

section Focal

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_pow_mem_of_coprime {H : Subgroup X} {z : X} {m : ℕ}
    (hm : Nat.Coprime m (orderOf z)) (hz : z ^ m ∈ H) : z ∈ H := by
  rcases Nat.lt_or_ge 1 (orderOf z) with h1 | h1
  · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm h1
    have hza : z = (z ^ m) ^ a := by
      rw [← pow_mul, ← pow_mod_orderOf, ha, pow_one]
    rw [hza]
    exact Subgroup.pow_mem _ hz a
  · have h0 := orderOf_pos z
    have h1' : orderOf z = 1 := by omega
    rw [orderOf_eq_one_iff.mp h1']
    exact H.one_mem

theorem mem_commutator_sylow_of_mem_center (hX : commutator X = ⊤) {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) {z : X} (hz : z ∈ Subgroup.center X) (hzP : z ∈ (P : Subgroup X)) :
    z ∈ ⁅(P : Subgroup X), (P : Subgroup X)⁆ := by
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have hc : z ^ k * g₀ = g₀ * z ^ k :=
      ((Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k)) g₀).symm
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow
    (Abelianization.of : (P : Subgroup X) →* Abelianization (P : Subgroup X)) z hkey
  have h2 : MonoidHom.transfer
      (Abelianization.of : (P : Subgroup X) →* Abelianization (P : Subgroup X)) z = 1 := by
    have hle : commutator X ≤ (MonoidHom.transfer
        (Abelianization.of : (P : Subgroup X) →* Abelianization (P : Subgroup X))).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [hX] at hle
    exact hle (Subgroup.mem_top z)
  rw [h2] at h1
  have hmem : (⟨z ^ (P : Subgroup X).index, MonoidHom.transfer_eq_pow_aux z hkey⟩ :
      (P : Subgroup X)) ∈ commutator (P : Subgroup X) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  have hmem' : z ^ (P : Subgroup X).index ∈ ⁅(P : Subgroup X), (P : Subgroup X)⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, hmem, rfl⟩
  refine mem_of_pow_mem_of_coprime ?_ hmem'
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨z, hzP⟩
  have hord : orderOf z ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hord
  rw [hj]
  exact Nat.Coprime.pow_right _
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr P.not_dvd_index).symm

end Focal

section OddSylow

variable {F : Type} [Field F]

theorem center_SL2_char_two_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ :=
  eq_bot_iff.mpr fun _ hz => Subgroup.mem_bot.mpr (CFSG.Quasithin.H13.eq_one_of_mem_center hz)

theorem isCyclic_of_isPGroup_odd [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    {Q : Subgroup SL(2, F)} (hQ : IsPGroup r Q) : IsCyclic Q := by
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have hcard : Nat.card SL(2, F) = 60 := by
      rw [card_SL_two_pow hF]
      norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    have hdvd : r ^ k ∣ 60 := by
      rw [← hk, ← hcard]
      exact Subgroup.card_subgroup_dvd_card Q
    apply isCyclic_of_card_dvd_prime (p := r)
    rw [hk]
    rcases k with _ | _ | k
    · simp
    · simp
    · exfalso
      have hr3 : 3 ≤ r := by
        have := hr.out.two_le
        omega
      have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans hdvd
      have h3 : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h2
      have h7 : r ≤ 7 := by nlinarith
      interval_cases r <;> norm_num at h2
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h7 : 7 ≤ Nat.card F := by
      rw [hF]
      calc 7 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    let ι : SL(2, F) ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
      ((QuotientGroup.quotientMulEquivOfEq center_SL2_char_two_eq_bot).trans
        QuotientGroup.quotientBot).symm
    have hQ' : IsPGroup r (Q.map ι.toMonoidHom) := hQ.map _
    obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
    have hcop : Nat.Coprime r (Nat.card F) := by
      rw [hF]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr.out Nat.prime_two).mpr hr2)
    have hRc : IsCyclic (R : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)) := by
      have h := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 r hr2
        hcop R
      exact h
    have hQc : IsCyclic ↥(Q.map ι.toMonoidHom) := Subgroup.isCyclic_of_le hR
    exact (MulEquiv.isCyclic (Q.equivMapOfInjective ι.toMonoidHom ι.injective)).mpr hQc

end OddSylow

section Kernel

variable {X : Type*} [Group X] [Finite X] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isPGroup_two_ker (hX : commutator X = ⊤) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (π : X →* SL(2, F)) (hZ : π.ker ≤ Subgroup.center X) :
    IsPGroup 2 π.ker := by
  have hodd : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ z ∈ π.ker, orderOf z = r → False := by
    intro r _ hr2 z hz hzr
    have hzc : z ∈ Subgroup.center X := hZ hz
    have hP : IsPGroup r (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzr, pow_one])
    obtain ⟨R, hR⟩ := hP.exists_le_sylow
    have hzR : z ∈ (R : Subgroup X) := hR (Subgroup.mem_zpowers z)
    have hcomm := mem_commutator_sylow_of_mem_center hX R hzc hzR
    let f := (π.comp (R : Subgroup X).subtype).rangeRestrict
    have : IsCyclic (π.comp (R : Subgroup X).subtype).range :=
      isCyclic_of_isPGroup_odd hn hF hr2
        (R.isPGroup'.of_surjective f (MonoidHom.rangeRestrict_surjective _))
    have hf : f.ker ≤ Subgroup.center (R : Subgroup X) := by
      intro x hx
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
      have hxc : (x : X) ∈ Subgroup.center X := hZ hx
      rw [Subgroup.mem_center_iff] at hxc ⊢
      intro y
      exact Subtype.ext (hxc y)
    have hab := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
    have hbot : ⁅(R : Subgroup X), (R : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    rw [hbot, Subgroup.mem_bot] at hcomm
    rw [hcomm, orderOf_one] at hzr
    exact (Fact.out : r.Prime).one_lt.ne hzr
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card π.ker) with ⟨k, hk⟩ |
      ⟨r, hr, hrdvd, hrodd⟩
  · exact IsPGroup.of_card hk
  · exfalso
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) r hrdvd
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.mpr even_two) hrodd
    exact hodd r hr2 z hz (by rw [← hzo, Subgroup.orderOf_mk])

end Kernel

section Comm

variable {X : Type*} [Group X]

theorem commutator_eq_of_ker {Y : Type*} [Group Y] (π : X →* Y)
    (hZ : π.ker ≤ Subgroup.center X) {a a' b b' : X} (ha : π a = π a') (hb : π b = π b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  have hz : a⁻¹ * a' ∈ Subgroup.center X := hZ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel])
  have hw : b⁻¹ * b' ∈ Subgroup.center X := hZ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel])
  set z := a⁻¹ * a' with hzdef
  set w := b⁻¹ * b' with hwdef
  have ha' : a' = a * z := by rw [hzdef, mul_inv_cancel_left]
  have hb' : b' = b * w := by rw [hwdef, mul_inv_cancel_left]
  have hz' : z * (b * w) * z⁻¹ = b * w := by
    rw [← Subgroup.mem_center_iff.mp hz (b * w), mul_inv_cancel_right]
  have hw' : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hw a⁻¹, mul_inv_cancel_right]
  have key : a' * b' * a'⁻¹ * b'⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    calc a' * b' * a'⁻¹ * b'⁻¹ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
          rw [ha', hb']; group
      _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [hz']; group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [hw']
  rw [commutatorElement_def, commutatorElement_def, key]

theorem commutatorElement_mul_left_of_central {a a' b : X}
    (h : ⁅a', b⁆ ∈ Subgroup.center X) : ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
  have hc := Subgroup.mem_center_iff.mp h a
  calc ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a', b⁆ * ⁅a, b⁆ := by rw [hc, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_central {a b b' : X}
    (h : ⁅a, b'⁆ ∈ Subgroup.center X) : ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have hc := Subgroup.mem_center_iff.mp h b
  calc ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, b⁆ * ⁅a, b'⁆ := by rw [hc, mul_inv_cancel_right]

theorem commutator_eq_bot_of_sq_eq_one {S : Subgroup X} (h : ∀ a ∈ S, a ^ 2 = 1) :
    ⁅S, S⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 := h (b * a) (mul_mem hb ha)
  have h2 := h a ha
  have h3 := h b hb
  rw [sq] at h1 h2 h3
  have e1 : b * a = (b * a)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [e1, mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]

end Comm

section Form

variable {X : Type*} [Group X] {F : Type} [Field F]

theorem unipSL_add (x y : F) : unipSL (x + y) = unipSL x * unipSL y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipSL_comm (x y : F) : unipSL x * unipSL y = unipSL y * unipSL x := by
  rw [← unipSL_add, ← unipSL_add, add_comm]

theorem mem_range_unipHom {g : SL(2, F)} :
    g ∈ (unipHom (F := F)).range ↔ ∃ x : F, g = unipSL x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd x, unipHom_apply x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.ofAdd x, by rw [unipHom_apply, toAdd_ofAdd]⟩

theorem exists_sq_eq_of_char_two [Finite F] [CharP F 2] (c : F) : ∃ μ : F, μ ^ 2 = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (fun μ : F => μ ^ 2) := fun a b hab => by
    have h1 : (a - b) ^ 2 = 0 := by
      rw [sub_pow_char, sub_eq_zero]
      exact hab
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)
  exact Finite.surjective_of_injective hinj c

variable (π : X →* SL(2, F)) (hπs : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center X)

@[expose] noncomputable def liftU (x : F) : X := Function.surjInv hπs (unipSL x)

theorem map_liftU (x : F) : π (liftU π hπs x) = unipSL x := Function.surjInv_eq hπs _

@[expose] noncomputable def commForm (x y : F) : X := ⁅liftU π hπs x, liftU π hπs y⁆

include hZ in
theorem commForm_mem_center (x y : F) : commForm π hπs x y ∈ Subgroup.center X := by
  apply hZ
  rw [MonoidHom.mem_ker, commForm, map_commutatorElement, map_liftU, map_liftU,
    commutatorElement_def, unipSL_comm x y, mul_inv_cancel_right, mul_inv_cancel]

include hZ in
theorem commForm_add_left (x x' y : F) :
    commForm π hπs (x + x') y = commForm π hπs x y * commForm π hπs x' y := by
  have h1 : commForm π hπs (x + x') y = ⁅liftU π hπs x * liftU π hπs x', liftU π hπs y⁆ :=
    commutator_eq_of_ker π hZ (by rw [map_liftU, map_mul, map_liftU, map_liftU, unipSL_add]) rfl
  rw [h1, commutatorElement_mul_left_of_central (commForm_mem_center π hπs hZ x' y)]
  exact Subgroup.mem_center_iff.mp (commForm_mem_center π hπs hZ x y) _

include hZ in
theorem commForm_add_right (x y y' : F) :
    commForm π hπs x (y + y') = commForm π hπs x y * commForm π hπs x y' := by
  have h1 : commForm π hπs x (y + y') = ⁅liftU π hπs x, liftU π hπs y * liftU π hπs y'⁆ :=
    commutator_eq_of_ker π hZ rfl (by rw [map_liftU, map_mul, map_liftU, map_liftU, unipSL_add])
  exact h1.trans (commutatorElement_mul_right_of_central (commForm_mem_center π hπs hZ x y'))

include hZ in
theorem commForm_zero_right (x : F) : commForm π hπs x 0 = 1 := by
  have h := commForm_add_right π hπs hZ x 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

include hZ in
theorem commForm_sq [CharP F 2] (x y : F) : commForm π hπs x y ^ 2 = 1 := by
  have hsq : liftU π hπs x * liftU π hπs x ∈ Subgroup.center X := hZ (by
    rw [MonoidHom.mem_ker, map_mul, map_liftU, unipSL_mul_self])
  have h1 : ⁅liftU π hπs x * liftU π hπs x, liftU π hπs y⁆ =
      ⁅liftU π hπs x, liftU π hπs y⁆ * ⁅liftU π hπs x, liftU π hπs y⁆ :=
    commutatorElement_mul_left_of_central (commForm_mem_center π hπs hZ x y)
  have h2 : ⁅liftU π hπs x * liftU π hπs x, liftU π hπs y⁆ = 1 := by
    rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hsq (liftU π hπs y),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [sq]
  exact h1.symm.trans h2

include hZ in
theorem commForm_smul [Finite F] [CharP F 2] (c x y : F) (hc : c ≠ 0) :
    commForm π hπs (c * x) (c * y) = commForm π hπs x y := by
  obtain ⟨μ, hμ⟩ := exists_sq_eq_of_char_two c
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hμ
    exact hc hμ.symm
  obtain ⟨h, hh⟩ := hπs (diagSL hμ0)
  have hconj : ∀ t : F, π (h * liftU π hπs t * h⁻¹) = unipSL (c * t) := fun t => by
    rw [map_mul, map_mul, map_inv, hh, map_liftU, diagSL_conj, hμ]
  have h1 : commForm π hπs (c * x) (c * y) =
      ⁅h * liftU π hπs x * h⁻¹, h * liftU π hπs y * h⁻¹⁆ :=
    commutator_eq_of_ker π hZ (by rw [map_liftU, hconj]) (by rw [map_liftU, hconj])
  have h2 : ⁅h * liftU π hπs x * h⁻¹, h * liftU π hπs y * h⁻¹⁆ =
      h * commForm π hπs x y * h⁻¹ := by
    rw [commForm]
    simp only [commutatorElement_def]
    group
  rw [h1, h2, Subgroup.mem_center_iff.mp (commForm_mem_center π hπs hZ x y) h,
    mul_inv_cancel_right]

include hZ in
theorem commutator_eq_commForm {a b : X} (ha : π a ∈ (unipHom (F := F)).range)
    (hb : π b ∈ (unipHom (F := F)).range) : ∃ x y : F, ⁅a, b⁆ = commForm π hπs x y := by
  obtain ⟨x, hx⟩ := mem_range_unipHom.mp ha
  obtain ⟨y, hy⟩ := mem_range_unipHom.mp hb
  exact ⟨x, y, commutator_eq_of_ker π hZ (by rw [hx, map_liftU]) (by rw [hy, map_liftU])⟩

end Form

section Main

variable {X : Type*} [Group X] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isPGroup_comap_unip {n : ℕ} (hF : Nat.card F = 2 ^ n) (π : X →* SL(2, F))
    (hπs : Function.Surjective π) (hk2 : IsPGroup 2 π.ker) :
    IsPGroup 2 ((unipHom (F := F)).range.comap π) ∧
      ¬ 2 ∣ ((unipHom (F := F)).range.comap π).index := by
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := mem_range_unipHom.mp (Subgroup.mem_comap.mp s.2)
    have hs2 : (s : X) ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hx, sq, unipSL_mul_self]
    obtain ⟨k, hk⟩ := hk2 ⟨_, hs2⟩
    have hk' : ((s : X) ^ 2) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k + 1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul]
    exact hk'
  · rw [Subgroup.index_comap_of_surjective _ hπs]
    have hU : Nat.card (unipHom (F := F)).range = 2 ^ n := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective unipHom_injective,
        Subgroup.card_top]
      exact hF
    have h := (unipHom (F := F)).range.card_mul_index
    rw [hU, card_SL_two_pow hF] at h
    have hi : (unipHom (F := F)).range.index = 4 ^ n - 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n) h
    rw [hi]
    intro h2
    exact (Nat.not_even_iff_odd.mpr (odd_four_pow_sub_one hn)) (even_iff_two_dvd.mpr h2)

theorem as_I_1_3_L2_holds : AS_I_1_3_L2 := by
  intro n hn F _ _ hF X _ _ hPf Z _ hZ ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hF
  have hX : commutator X = ⊤ := hPf.commutator_eq_top
  set π : X →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hπ
  have hπs : Function.Surjective π := fun y => by
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨x, rfl⟩
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e (QuotientGroup.mk x) = 1 := hx
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      exact h1
    · intro hx
      show e (QuotientGroup.mk x) = 1
      rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
  have hZπ : π.ker ≤ Subgroup.center X := by
    rw [hker]
    exact hZ
  have hk2 : IsPGroup 2 π.ker := isPGroup_two_ker hX hn hF π hZπ
  obtain ⟨hS2, hSi⟩ := isPGroup_comap_unip hF π hπs hk2
  set S : Subgroup X := (unipHom (F := F)).range.comap π with hSdef
  have hZS : ∀ z ∈ Z, z ∈ ⁅S, S⁆ := by
    intro z hz
    have hzk : z ∈ π.ker := by
      rw [hker]
      exact hz
    have hzS : z ∈ (hS2.toSylow hSi : Subgroup X) := by
      rw [IsPGroup.toSylow_coe]
      show π z ∈ (unipHom (F := F)).range
      rw [MonoidHom.mem_ker.mp hzk]
      exact Subgroup.one_mem _
    have h1 := mem_commutator_sylow_of_mem_center hX (hS2.toSylow hSi) (hZ hz) hzS
    rwa [IsPGroup.toSylow_coe] at h1
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    obtain rfl : n = 2 := by omega
    by_cases hZb : Z = ⊥
    · exact Or.inl hZb
    right
    refine ⟨rfl, ?_⟩
    let φ : Multiplicative F →* X :=
      { toFun := fun u => commForm π hπs (Multiplicative.toAdd u) 1
        map_one' := by
          show commForm π hπs 0 1 = 1
          have h := commForm_add_left π hπs hZπ 0 0 1
          rw [add_zero] at h
          exact mul_eq_left.mp h.symm
        map_mul' := fun u v => commForm_add_left π hπs hZπ _ _ 1 }
    have hφ1 : Multiplicative.ofAdd (1 : F) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      show commForm π hπs 1 1 = 1
      rw [commForm]
      exact commutatorElement_self _
    have hker2 : 1 < Nat.card φ.ker := by
      refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => ?_
      rw [h, Subgroup.mem_bot] at hφ1
      have h1 := congrArg Multiplicative.toAdd hφ1
      simp at h1
    have hrange : Nat.card φ.range ≤ 2 := by
      have h := Subgroup.card_ker_mul_card_range φ
      have hc : Nat.card (Multiplicative F) = 4 := by
        show Nat.card F = 4
        rw [hF]
        norm_num
      rw [hc] at h
      nlinarith
    have hcomm_le : ⁅S, S⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨x, y, hxy⟩ := commutator_eq_commForm π hπs hZπ (Subgroup.mem_comap.mp ha)
        (Subgroup.mem_comap.mp hb)
      rw [hxy]
      by_cases hy : y = 0
      · rw [hy, commForm_zero_right π hπs hZπ]
        exact Subgroup.one_mem _
      · refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (y⁻¹ * x), ?_⟩
        show commForm π hπs (y⁻¹ * x) 1 = commForm π hπs x y
        have h1 := commForm_smul π hπs hZπ y⁻¹ x y (inv_ne_zero hy)
        rwa [inv_mul_cancel₀ hy] at h1
    have hcardZ : Nat.card Z = 2 := by
      have h1 : Nat.card Z ≤ 2 :=
        (Subgroup.card_le_of_le fun z hz => hcomm_le (hZS z hz)).trans hrange
      have h2 : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZb
      omega
    refine ⟨hcardZ, ?_⟩
    have hZ2 : ∀ ζ ∈ Z, ζ ^ 2 = 1 := fun ζ hζ => by
      have h := pow_card_eq_one' (G := Z) (x := ⟨ζ, hζ⟩)
      rw [hcardZ] at h
      have h1 := congrArg Subtype.val h
      simpa using h1
    intro x hx2
    by_contra hxZ
    have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (show x ^ 2 ^ 1 = 1 by rw [pow_one]; exact hx2))
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P (hS2.toSylow hSi)
    have hxS : g * x * g⁻¹ ∈ S := by
      have h1 : x ∈ (P : Subgroup X) := hxP (Subgroup.mem_zpowers x)
      have h2 : MulAut.conj g • x ∈ MulAut.conj g • (P : Subgroup X) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ h1
      rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
        MulAut.conj_apply] at h2
      exact h2
    set x' := g * x * g⁻¹ with hx'
    have hx'2 : x' ^ 2 = 1 := by rw [hx', conj_pow, hx2, mul_one, mul_inv_cancel]
    have hx'Z : x' ∉ Z := fun h => hxZ (by
      have h1 := (inferInstance : Z.Normal).conj_mem x' h g⁻¹
      have e1 : g⁻¹ * x' * g⁻¹⁻¹ = x := by rw [hx']; group
      rwa [e1] at h1)
    obtain ⟨b, hb⟩ := mem_range_unipHom.mp (Subgroup.mem_comap.mp hxS)
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hx'Z
      rw [← hker, MonoidHom.mem_ker, hb, unipSL_zero]
    have hSexp : ∀ a ∈ S, a ^ 2 = 1 := by
      intro a ha
      obtain ⟨y, hy⟩ := mem_range_unipHom.mp (Subgroup.mem_comap.mp ha)
      by_cases hy0 : y = 0
      · have haZ : a ∈ Z := by
          rw [← hker, MonoidHom.mem_ker, hy, hy0, unipSL_zero]
        exact hZ2 a haZ
      · obtain ⟨μ, hμ⟩ := exists_sq_eq_of_char_two (y * b⁻¹)
        have hμ0 : μ ≠ 0 := by
          rintro rfl
          rw [zero_pow two_ne_zero] at hμ
          exact mul_ne_zero hy0 (inv_ne_zero hb0) hμ.symm
        obtain ⟨h, hh⟩ := hπs (diagSL hμ0)
        have hπa : π (h * x' * h⁻¹) = π a := by
          rw [map_mul, map_mul, map_inv, hh, hb, diagSL_conj, hμ, hy, mul_assoc,
            inv_mul_cancel₀ hb0, mul_one]
        have hζ : (h * x' * h⁻¹)⁻¹ * a ∈ Z := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
        have ha'2 : (h * x' * h⁻¹) ^ 2 = 1 := by
          rw [conj_pow, hx'2, mul_one, mul_inv_cancel]
        have hcomm : Commute (h * x' * h⁻¹) ((h * x' * h⁻¹)⁻¹ * a) :=
          Subgroup.mem_center_iff.mp (hZ hζ) _
        have e1 : a = (h * x' * h⁻¹) * ((h * x' * h⁻¹)⁻¹ * a) := by group
        rw [e1, hcomm.mul_pow, ha'2, hZ2 _ hζ, one_mul]
    have hSb : ⁅S, S⁆ = ⊥ := commutator_eq_bot_of_sq_eq_one hSexp
    apply hZb
    rw [eq_bot_iff]
    intro z hz
    have h1 := hZS z hz
    rwa [hSb] at h1
  ·
    left
    have h8 : 8 ≤ Nat.card F := by
      rw [hF]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have hβ := eq_one_of_invariant_biadditive h8 (commForm π hπs)
      (commForm_add_left π hπs hZπ) (commForm_add_right π hπs hZπ) (commForm_sq π hπs hZπ)
      (fun c x y hc => commForm_smul π hπs hZπ c x y hc)
    have hSb : ⁅S, S⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨x, y, hxy⟩ := commutator_eq_commForm π hπs hZπ (Subgroup.mem_comap.mp hb)
        (Subgroup.mem_comap.mp ha)
      rw [hβ, commutatorElement_eq_one_iff_mul_comm] at hxy
      exact hxy
    rw [eq_bot_iff]
    intro z hz
    have h1 := hZS z hz
    rwa [hSb] at h1

end Main

end CFSG.Quasithin.Vol2.Ch11.SecH
