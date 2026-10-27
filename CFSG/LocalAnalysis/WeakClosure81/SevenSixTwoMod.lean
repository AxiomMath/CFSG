module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Walter.W67.Section6.Util
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem s762M_exists_complement [Finite G] {I W : Subgroup G} (hI : IsElemAbelian 2 I)
    (hIW : I ≤ W) (hWI : W ≤ Subgroup.normalizer (I : Set G)) (hodd : Odd (I.relIndex W)) :
    ∃ S : Subgroup G, S ≤ W ∧ I ⊓ S = ⊥ ∧ I ⊔ S = W ∧
      Nat.Coprime (Nat.card S) (Nat.card I) ∧ ⁅I, W⁆ = ⁅I, S⁆ := by
  have habel : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := by
    intro x hx y hy
    letI := hI.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : I) ⟨y, hy⟩)
  obtain ⟨k, hk⟩ := hI.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card I) (I.relIndex W) := by
    rw [hk]
    rcases k.eq_zero_or_pos with hk0 | hkpos
    · subst hk0
      simp
    · rw [Nat.coprime_pow_left_iff hkpos]
      exact hodd.coprime_two_left
  obtain ⟨S, hSW, hIS, hIsup, hcard⟩ :=
    CFSG.Walter.W67.Sec6.exists_complement_in (C := I) (N := W) hIW hWI hcop
  have hric : I.relIndex W * Nat.card (I ⊓ W : Subgroup G) = Nat.card W :=
    Subgroup.relIndex_mul_card I W
  have hinf : (I ⊓ W : Subgroup G) = I := inf_eq_left.mpr hIW
  rw [hinf] at hric
  have hpos : 0 < Nat.card I := by
    haveI : Nonempty I := ⟨1⟩
    exact Nat.card_pos
  have hS_eq : Nat.card S = I.relIndex W := by
    refine Nat.mul_left_cancel hpos ?_
    calc Nat.card I * Nat.card S = Nat.card W := hcard
      _ = Nat.card I * I.relIndex W := by rw [← hric, Nat.mul_comm]
  have hSodd : Odd (Nat.card S) := by rw [hS_eq]; exact hodd
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card I) := by
    rw [hk]
    rcases k.eq_zero_or_pos with hk0 | hkpos
    · subst hk0
      simp
    · rw [Nat.coprime_pow_right_iff hkpos]
      exact hSodd.coprime_two_right
  refine ⟨S, hSW, hIS, hIsup, hcop', ?_⟩
  have hSI : S ≤ Subgroup.normalizer (I : Set G) := hSW.trans hWI
  have hle : ⁅I, S⁆ ≤ I := CFSG.Quasithin.E1.commutator_le_of_le_normalizer hSI
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl hSW)
  rw [← hIsup]
  refine Subgroup.commutator_le.mpr fun a ha w hw => ?_
  have hw' : w ∈ (I : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left I S hSI]
    exact hw
  obtain ⟨i, hi, s, hs, rfl⟩ := Set.mem_mul.mp hw'
  have hai : a * i = i * a := habel a ha i hi
  have hx : ⁅a, i * s⁆ = i * ⁅a, s⁆ * i⁻¹ := by
    rw [CFSG.Quasithin.E1.comm_mul_right]
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hai]
    group
  rw [hx]
  have hxmem : ⁅a, s⁆ ∈ ⁅I, S⁆ := Subgroup.commutator_mem_commutator ha hs
  have hxI : ⁅a, s⁆ ∈ I := hle hxmem
  have hconj : i * ⁅a, s⁆ * i⁻¹ = ⁅a, s⁆ := by
    rw [habel i hi _ hxI]
    group
  rw [hconj]
  exact hxmem

theorem commutator_mem_centralizer_of_normalizes {F : Subgroup G} {y v : G}
    (hy : y ∈ Subgroup.normalizer (F : Set G)) (hv : v ∈ Subgroup.centralizer (F : Set G)) :
    ⁅y, v⁆ ∈ Subgroup.centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfv : f * v = v * f := (Subgroup.mem_centralizer_iff.mp hv) f hf
  have hf' : y⁻¹ * f * y ∈ F := by
    have hy' : y⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ hy
    simpa using ((Subgroup.mem_normalizer_iff.mp hy') f).mp hf
  have hv_f' : v * (y⁻¹ * f * y) = (y⁻¹ * f * y) * v :=
    ((Subgroup.mem_centralizer_iff.mp hv) _ hf').symm
  have hconj : ⁅y, v⁆ * f * ⁅y, v⁆⁻¹ = f := by
    have hv_inv_f : v⁻¹ * f * v = f := by
      calc v⁻¹ * f * v = v⁻¹ * (f * v) := by group
        _ = v⁻¹ * (v * f) := by rw [hfv]
        _ = f := by group
    have h1 : y⁻¹ * v⁻¹ * f * v * y = y⁻¹ * f * y := by
      rw [show y⁻¹ * v⁻¹ * f * v * y = y⁻¹ * (v⁻¹ * f * v) * y from by group, hv_inv_f]
    rw [commutatorElement_def]
    calc y * v * y⁻¹ * v⁻¹ * f * (y * v * y⁻¹ * v⁻¹)⁻¹
        = y * v * (y⁻¹ * v⁻¹ * f * v * y) * v⁻¹ * y⁻¹ := by group
      _ = y * v * (y⁻¹ * f * y) * v⁻¹ * y⁻¹ := by rw [h1]
      _ = y * (v * (y⁻¹ * f * y) * v⁻¹) * y⁻¹ := by group
      _ = y * (y⁻¹ * f * y) * y⁻¹ := by rw [hv_f']; group
      _ = f := by group
  have hcomm : ⁅y, v⁆ * f = f * ⁅y, v⁆ :=
    mul_inv_eq_iff_eq_mul.mp hconj
  exact hcomm.symm

theorem commutator_inf_centralizer_eq_bot_of_odd_relIndex [Finite G] {I W : Subgroup G}
    (hI : IsElemAbelian 2 I) (hIW : I ≤ W) (hWI : W ≤ Subgroup.normalizer (I : Set G))
    (hodd : Odd (I.relIndex W)) :
    ⁅I, W⁆ ⊓ (I ⊓ Subgroup.centralizer (W : Set G)) = ⊥ := by
  have habel : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := by
    intro x hx y hy
    letI := hI.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : I) ⟨y, hy⟩)
  obtain ⟨S, hSW, hIS, hIsup, hcop, hcomm_eq⟩ :=
    s762M_exists_complement hI hIW hWI hodd
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxF, hxIC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxI, hxC⟩ := Subgroup.mem_inf.mp hxIC
  have hxS : x ∈ ⁅S, I⁆ := by
    rw [← Subgroup.commutator_comm I S, ← hcomm_eq]
    exact hxF
  have hfix : ∀ a ∈ S, a * x * a⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
    intro a ha
    have haW : a ∈ W := hSW ha
    have hax : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hxC) a haW
    refine Subgroup.mem_bot.mpr ?_
    rw [hax]
    group
  exact CFSG.LocalAnalysis.EvenBN.Common.mem_of_mem_commutator_sup_of_fixed
    (A := S) (Y := I) (Z := ⊥)
    bot_le
    (fun y hy y' hy' => by
      refine Subgroup.mem_bot.mpr ?_
      rw [habel y hy y' hy']
      group)
    (hSW.trans hWI)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    hcop
    (Subgroup.mem_sup_left hxS)
    hfix

theorem commutator_commutator_eq_of_odd_relIndex [Finite G] {I W : Subgroup G}
    (hI : IsElemAbelian 2 I) (hIW : I ≤ W) (hWI : W ≤ Subgroup.normalizer (I : Set G))
    (hodd : Odd (I.relIndex W)) : ⁅⁅I, W⁆, W⁆ = ⁅I, W⁆ := by
  obtain ⟨S, hSW, hIS, hIsup, hcop, hcomm_eq⟩ :=
    s762M_exists_complement hI hIW hWI hodd
  have hSI : S ≤ Subgroup.normalizer (I : Set G) := hSW.trans hWI
  have hle : ⁅⁅I, W⁆, W⁆ ≤ ⁅I, W⁆ :=
    CFSG.Quasithin.E1.commutator_le_of_le_normalizer (R := ⁅I, W⁆)
      (Subgroup.normalizer_commutator_ge_right I W)
  have hge : ⁅I, W⁆ ≤ ⁅⁅I, W⁆, W⁆ := by
    calc ⁅I, W⁆ = ⁅I, S⁆ := hcomm_eq
      _ ≤ ⁅⁅I, S⁆, S⁆ :=
        CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime I S hSI hcop
      _ ≤ ⁅⁅I, W⁆, W⁆ := Subgroup.commutator_mono (le_of_eq hcomm_eq.symm) hSW
  exact le_antisymm hle hge

theorem commutator_eq_bot_of_centralizes_commutator [Finite G] {I Y W : Subgroup G} {v : G}
    (hI : IsElemAbelian 2 I) (hIW : I ≤ W) (hWY : W ≤ Y)
    (hYI : Y ≤ Subgroup.normalizer (I : Set G)) (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hodd : Odd (I.relIndex W))
    (hvI : v ∈ Subgroup.normalizer (I : Set G)) (hvW : v ∈ Subgroup.normalizer (W : Set G))
    (hWv : W ≤ ⁅Y, Subgroup.zpowers v⁆ ⊔ I)
    (hcent : ∀ w ∈ W, ∀ z ∈ ⁅I, Subgroup.zpowers v⁆, w * z = z * w) :
    ⁅I, W⁆ = ⊥ := by
  have habel : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := by
    intro x hx y hy
    letI := hI.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : I) ⟨y, hy⟩)
  set F : Subgroup G := ⁅I, W⁆ with hF
  have hWI : W ≤ Subgroup.normalizer (I : Set G) := hWY.trans hYI
  have hFI : F ≤ I := by
    rw [hF]
    exact CFSG.Quasithin.E1.commutator_le_of_le_normalizer hWI
  have hYF : Y ≤ Subgroup.normalizer (F : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : I.map (MulAut.conj y) = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYI hy)
    have h2 : W.map (MulAut.conj y) = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYW hy)
    rw [hF, Subgroup.map_commutator, h1, h2]
  have hvF : v ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : I.map (MulAut.conj v) = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hvI
    have h2 : W.map (MulAut.conj v) = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hvW
    rw [hF, Subgroup.map_commutator, h1, h2]
  have hF_comm_v : ∀ f ∈ F, ⁅f, v⁆ = 1 := by
    intro f hf
    have hcommZ : ∀ z ∈ Subgroup.zpowers v, ⁅f, z⁆ = 1 := by
      intro z hz
      have hzv : z ∈ Subgroup.normalizer (F : Set G) := Subgroup.zpowers_le.mpr hvF hz
      have hmemF : ⁅f, z⁆ ∈ F :=
        CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hf hzv
      have hmemI : ⁅f, z⁆ ∈ I := hFI hmemF
      have hmemC : ⁅f, z⁆ ∈ Subgroup.centralizer (W : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact hcent w hw ⁅f, z⁆ (Subgroup.commutator_mem_commutator (hFI hf) hz)
      have hbot : ⁅f, z⁆ ∈ (⊥ : Subgroup G) := by
        have hmem : ⁅f, z⁆ ∈ F ⊓ (I ⊓ Subgroup.centralizer (W : Set G)) :=
          Subgroup.mem_inf.mpr ⟨hmemF, Subgroup.mem_inf.mpr ⟨hmemI, hmemC⟩⟩
        rw [hF, commutator_inf_centralizer_eq_bot_of_odd_relIndex hI hIW hWI hodd] at hmem
        exact hmem
      exact Subgroup.mem_bot.mp hbot
    exact hcommZ v (Subgroup.mem_zpowers v)
  have hvC : v ∈ Subgroup.centralizer (F : Set G) :=
    Subgroup.mem_centralizer_iff_commutator_eq_one.mpr hF_comm_v
  have hYvC : ⁅Y, Subgroup.zpowers v⁆ ≤ Subgroup.centralizer (F : Set G) := by
    refine Subgroup.commutator_le.mpr fun y hy z hz => ?_
    exact commutator_mem_centralizer_of_normalizes (hYF hy)
      (Subgroup.zpowers_le.mpr hvC hz)
  have hIC : I ≤ Subgroup.centralizer (F : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (habel i hi f (hFI hf)).symm
  have hWC : W ≤ Subgroup.centralizer (F : Set G) := hWv.trans (sup_le hYvC hIC)
  have hFCW : F ≤ Subgroup.centralizer (W : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp (hWC hw)) f hf).symm
  have hFW : ⁅F, W⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFCW
  have h33 := commutator_commutator_eq_of_odd_relIndex hI hIW hWI hodd
  calc ⁅I, W⁆ = ⁅⁅I, W⁆, W⁆ := h33.symm
    _ = ⁅F, W⁆ := by rw [← hF]
    _ = ⊥ := hFW

theorem le_of_isPGroup_of_odd_relIndex [Finite G] {I W : Subgroup G} (hW : IsPGroup 2 W)
    (hodd : Odd (I.relIndex W)) : W ≤ I := by
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hdvd : I.relIndex W ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card (H := I) (K := W)
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hjne
    have h2dvd : 2 ∣ 2 ^ j := by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjne
      exact ⟨2 ^ j', by rw [pow_succ, Nat.mul_comm]⟩
    have hnotdvd : ¬ 2 ∣ 2 ^ j := by
      have hoddj : Odd (2 ^ j) := by rw [← hjeq]; exact hodd
      exact (Nat.prime_two.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hoddj.coprime_two_right)
    exact hnotdvd h2dvd
  subst hj0
  have : I.relIndex W = 1 := by simpa using hjeq
  exact Subgroup.relIndex_eq_one.mp this

end CFSG.LocalAnalysis.WeakClosure81
