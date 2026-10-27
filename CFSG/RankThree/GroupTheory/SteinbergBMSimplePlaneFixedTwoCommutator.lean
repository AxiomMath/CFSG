module

public import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem map_actionCommutator_conj {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))
    (K' : Subgroup K) :
    letI : MulDistribMulAction X K := MulDistribMulAction.compHom K (Subgroup.inclusion hXK)
    (actionCommutator X K').map K.subtype = ⁅K'.map K.subtype, X⁆ := by
  let : MulDistribMulAction X K := MulDistribMulAction.compHom K (Subgroup.inclusion hXK)
  have hsmul : ∀ (x : X) (k : K), ((x • k : K) : G) = x * k * (x : G)⁻¹ := fun _ _ => rfl
  unfold actionCommutator
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  refine le_antisymm ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨_, ⟨k, hk, x, rfl⟩, rfl⟩
    have e : K.subtype (k⁻¹ * (x • k)) = ⁅(k : G)⁻¹, (x : G)⁆ := by
      rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact subset_closure ⟨_, (K'.map K.subtype).inv_mem (mem_map_of_mem K.subtype hk), x, x.2,
      rfl⟩
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, x, hx, rfl⟩
    have hmem : k⁻¹⁻¹ * ((⟨x, hx⟩ : X) • k⁻¹) ∈
        {y : K | ∃ h ∈ K', ∃ a : X, y = h⁻¹ * (a • h)} := ⟨k⁻¹, K'.inv_mem hk, ⟨x, hx⟩, rfl⟩
    refine subset_closure ⟨_, hmem, ?_⟩
    rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def]
    simp only [inv_inv, coe_inv]
    group

theorem le_normalizer_inf_centralizer {V K : Subgroup G} {b : G}
    (hKV : K ≤ normalizer (V : Set G)) (hKb : ∀ c ∈ K, c * b = b * c) :
    K ≤ normalizer ((V ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun c hc x hx => ⟨?_, ?_⟩
  · exact (mem_normalizer_iff.mp (hKV hc) x).mp hx.1
  · have hcb := hKb c hc
    have hxb : x * b = b * x := mem_centralizer_singleton_iff.mp hx.2
    refine mem_centralizer_singleton_iff.mpr ?_
    calc c * x * c⁻¹ * b = c * x * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = c * x * b * c⁻¹ := by
          rw [show c⁻¹ * b * c = b by rw [mul_assoc, ← hcb]; group]
      _ = c * b * x * c⁻¹ := by rw [mul_assoc c x b, hxb, ← mul_assoc]
      _ = b * (c * x * c⁻¹) := by rw [hcb]; group

theorem commutator_zpowers_ne_bot_of_isSimpleGroup {P W : Subgroup G} [IsSimpleGroup P]
    (hPW : P ≤ normalizer (W : Set G)) (hWP : ⁅W, P⁆ ≠ ⊥) {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1) :
    ⁅W, zpowers x⁆ ≠ ⊥ := by
  set K := (centralizer (W : Set G)).subgroupOf P with hK
  have hKn : K.Normal := by
    refine ⟨fun c hc y => ?_⟩
    rw [hK, mem_subgroupOf, mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : (y : G)⁻¹ * w * y ∈ W := by
      have := (mem_normalizer_iff.mp (hPW (P.inv_mem y.2)) w).mp hw
      rwa [inv_inv] at this
    have hc' := hc _ hw'
    simp only [coe_mul, coe_inv]
    calc w * (y * c * (y : G)⁻¹) = y * (((y : G)⁻¹ * w * y) * c) * (y : G)⁻¹ := by group
      _ = y * (c * ((y : G)⁻¹ * w * y)) * (y : G)⁻¹ := by rw [hc']
      _ = y * c * (y : G)⁻¹ * w := by group
  rcases hKn.eq_bot_or_eq_top with h | h
  · intro hx
    have hxC : x ∈ centralizer (W : Set G) := by
      have hWx := commutator_eq_bot_iff_le_centralizer.mp hx
      rw [mem_centralizer_iff]
      intro w hw
      exact (mem_centralizer_iff.mp (hWx hw) x (mem_zpowers x)).symm
    have : (⟨x, hxP⟩ : P) ∈ K := hxC
    rw [h, mem_bot] at this
    exact hx1 (congrArg Subtype.val this)
  · exfalso
    apply hWP
    rw [commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    have : (⟨y, hy⟩ : P) ∈ K := h ▸ mem_top _
    exact (mem_centralizer_iff.mp this w hw).symm

theorem characteristic_two_centralizing_simple_subgroup_plane_fixed_two_commutator [Finite G]
    (hG : CFSG.IsCharacteristicPType G 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A P B R : Subgroup G} {d : G} (hA : CFSG.IsElementaryAbelian p A) [IsSimpleGroup P]
    (hAP : A ≤ normalizer (P : Set G)) (hdP : d ∈ P) (hd : orderOf d = p) (hBA : B ≤ A)
    (hB : Nat.card B = p ^ 2) (hBP : ⁅B, P⁆ = ⊥) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hAR : A ≤ normalizer (R : Set G)) (hRP : ⁅R, P⁆ = ⊥) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      S ≤ centralizer (R : Set G) ⊓ centralizer ({b} : Set G) ∧ A ≤ normalizer (S : Set G) ∧
      P ≤ normalizer (S : Set G) ∧ ⁅S, P⁆ = S ∧ ⁅S, zpowers d⁆ ≠ ⊥ ∧
      A ≤ normalizer ((CFSG.inSubgroup (CFSG.pCore 2) (normalizer (R : Set G)) ⊓
        centralizer ({b} : Set G) : Subgroup G) : Set G) ∧
      P ≤ normalizer ((CFSG.inSubgroup (CFSG.pCore 2) (normalizer (R : Set G)) ⊓
        centralizer ({b} : Set G) : Subgroup G) : Set G) ∧
      S ≤ ⁅CFSG.inSubgroup (CFSG.pCore 2) (normalizer (R : Set G)) ⊓
        centralizer ({b} : Set G), P⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (R : Set G) with hHdef
  set V := CFSG.inSubgroup (CFSG.pCore 2) H with hVdef
  have hV2 : IsPGroup 2 V := (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype
  have hHV : H ≤ normalizer (V : Set G) := le_normalizer_inSubgroup_pCore 2 H
  have hPH : P ≤ H := by
    refine le_normalizer_of_forall_conj_mem fun y hy x hx => ?_
    have hxy := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hRP hx) y hy
    rw [hxy, mul_inv_cancel_right]
    exact hx
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd
    exact hp.one_lt.ne' hd.symm
  have hBPc : ∀ b ∈ B, ∀ y ∈ P, y * b = b * y := fun b hb y hy =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBP hb) y hy)
  have hBe : CFSG.IsElementaryAbelian p B := isElementaryAbelian_of_le hA hBA
  have hpV : ¬ p ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨b, hb, hb1, hUP⟩ : ∃ b ∈ B, b ≠ 1 ∧ ⁅V ⊓ centralizer ({b} : Set G), P⁆ ≠ ⊥ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hVP : V ≤ centralizer (P : Set G) :=
      le_of_forall_inf_centralizer_le hBe hB.ge hpV ((hBA.trans hAR).trans hHV)
        fun b hb hb1 => commutator_eq_bot_iff_le_centralizer.mp (hcon b hb hb1)
    have hdV : d ∈ V := mem_inSubgroup_pCore_of_isCharacteristicPType hG hR2 hR1 (hPH hdP)
      fun s hs => (mem_centralizer_iff.mp (hVP hs) d hdP).symm
    have hcop : Nat.Coprime 2 (Nat.card (zpowers d)) := by
      rw [Nat.card_zpowers, hd]
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact hd1 (eq_one_of_mem_isPGroup_of_coprime hV2 hcop hdV (mem_zpowers d))
  set U := V ⊓ centralizer ({b} : Set G) with hUdef
  have hbA : b ∈ A := hBA hb
  have hAU : A ≤ normalizer (U : Set G) := le_normalizer_inf_centralizer (hAR.trans hHV)
    fun c hc => congrArg Subtype.val (hA.is_comm.comm ⟨c, hc⟩ ⟨b, hbA⟩)
  have hPU : P ≤ normalizer (U : Set G) := le_normalizer_inf_centralizer (hPH.trans hHV)
    fun c hc => hBPc b hb c hc
  have hU2 : IsPGroup 2 U := hV2.to_le inf_le_left
  set X := zpowers d with hXdef
  have hXP : X ≤ P := zpowers_le.mpr hdP
  have hXU : X ≤ normalizer (U : Set G) := hXP.trans hPU
  set D := ⁅U, X⁆ with hDdef
  have hD1 : D ≠ ⊥ := commutator_zpowers_ne_bot_of_isSimpleGroup hPU hUP hdP hd1
  have hDD : ⁅D, X⁆ = D := by
    let : MulDistribMulAction X U := MulDistribMulAction.compHom U (Subgroup.inclusion hXU)
    have h2X : ¬ 2 ∣ Nat.card X := by
      rw [Nat.card_zpowers, hd]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
    have hfact := (coprime_pgroup_commutator_factorization (A := X) (Q := U) Nat.prime_two
      hU2 h2X).2
    have hD : (actionCommutator X (⊤ : Subgroup U)).map U.subtype = D := by
      rw [map_actionCommutator_conj hXU, ← MonoidHom.range_eq_map, range_subtype]
    rw [← hD, ← map_actionCommutator_conj hXU, hfact]
  obtain ⟨T, hT0, hTs⟩ : ∃ T : ℕ → Subgroup G, T 0 = U ∧ ∀ n, T (n + 1) = ⁅T n, P⁆ :=
    ⟨fun n => Nat.rec U (fun _ T => ⁅T, P⁆) n, rfl, fun _ => rfl⟩
  have hTP : ∀ n, P ≤ normalizer (T n : Set G) := by
    intro n
    cases n with
    | zero => rw [hT0]; exact hPU
    | succ n => rw [hTs]; exact normalizer_commutator_ge_right _ _
  have hTA : ∀ n, A ≤ normalizer (T n : Set G) := by
    intro n
    induction n with
    | zero => rw [hT0]; exact hAU
    | succ n ih =>
      rw [hTs]
      intro a ha
      rw [mem_normalizer_iff_map_conj_eq, map_commutator,
        (mem_normalizer_iff_map_conj_eq).mp (ih ha), (mem_normalizer_iff_map_conj_eq).mp (hAP ha)]
  have hTdesc : ∀ n, T (n + 1) ≤ T n := fun n => by
    rw [hTs]
    exact le_normalizer_iff_commutator_le_left.mp (hTP n)
  have hTU : ∀ n, T n ≤ U := by
    intro n
    induction n with
    | zero => rw [hT0]
    | succ n ih => exact (hTdesc n).trans ih
  have hDT : ∀ n, D ≤ T n := by
    intro n
    induction n with
    | zero => rw [hT0]; exact le_normalizer_iff_commutator_le_left.mp hXU
    | succ n ih =>
      rw [hTs, ← hDD]
      exact commutator_mono ih hXP
  obtain ⟨n, hn⟩ : ∃ n, T (n + 1) = T n := by
    by_contra hcon
    push Not at hcon
    have hlt : ∀ n, Nat.card (T n) + n ≤ Nat.card U := by
      intro n
      induction n with
      | zero => simp [hT0]
      | succ n ih =>
        have := card_lt_of_lt (lt_of_le_of_ne (hTdesc n) (hcon n))
        omega
    have := hlt (Nat.card U + 1)
    omega
  set S := T n with hSdef
  have hSP : ⁅S, P⁆ = S := by rw [hSdef, ← hTs, hn]
  have hS1 : S ≠ ⊥ := fun h => hD1 (le_bot_iff.mp (h ▸ hDT n))
  have hSUP : S ≤ ⁅U, P⁆ := hSP ▸ commutator_mono (hTU n) le_rfl
  have hUR : ⁅⁅U, P⁆, R⁆ = ⊥ := by
    have hRU : ⁅R, U⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp
      ((inf_le_left.trans (map_subtype_le _)) : U ≤ H)
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commutator_comm P R, hRP, commutator_bot_left]
    · exact le_bot_iff.mp ((commutator_mono hRU le_rfl).trans hRP.le)
  have hSR : S ≤ centralizer (R : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_mono hSUP le_rfl).trans hUR.le))
  refine ⟨b, hb, hb1, S, hS1, hU2.to_le (hTU n), le_inf hSR ((hTU n).trans inf_le_right),
    hTA n, hTP n, hSP, ?_, hAU, hPU, hSUP⟩
  exact commutator_zpowers_ne_bot_of_isSimpleGroup (hTP n) (by rw [hSP]; exact hS1) hdP hd1

end CFSG.RankThree.GroupTheory.SteinbergBM
