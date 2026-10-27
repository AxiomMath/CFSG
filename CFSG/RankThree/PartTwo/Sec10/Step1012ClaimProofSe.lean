module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsTwo

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

namespace Step1012ClaimProof


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem exists_w_of_isSylowOf (h107 : Item107) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G}
    (hS : IsSylowOf 2 S
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))))
    (hSA : A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) ∧
      w * a * w⁻¹ = a ∧ w * d * w⁻¹ = d ∧ w * c * w⁻¹ = c * d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨τ, hτT, hτa, hτc⟩ := Sec10XProof.exists_transvection h hdL hd3 hAcl
  obtain ⟨w₀, hw₀N, -, hw₀τ⟩ := Sec4.mem_autIn_iff.mp (h107 G A c L a R h d hdA hdL hτT)
  have hw₀ : ∀ x : A, w₀ * x * w₀⁻¹ = (τ x : G) := fun x => by
    rw [← hw₀τ, Sec4.normalizerMonoidHom_apply_coe]
  have hw₀a : w₀ * a * w₀⁻¹ = a := (hw₀ ⟨a, h.a_mem⟩).trans hτa
  have hw₀c : w₀ * c * w₀⁻¹ = c * d := (hw₀ ⟨c, h.mem_A⟩).trans hτc
  have hw₀d : w₀ * d * w₀⁻¹ = d := (hw₀ ⟨d, hdA⟩).trans (congrArg Subtype.val hτT.1)
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Θ := inSubgroup (aschbacherSolvableCore 3) Ca with hΘ
  have hAC : A ≤ Ca := Sec10XProof.le_centralizer_of_mem h h.a_mem
  have hAN : A ≤ Subgroup.normalizer (Θ : Set G) := hAC.trans (Sec6.le_normalizer_theta Ca)
  have hw₀C : w₀ ∈ Ca := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w₀ * a = w₀ * a * w₀⁻¹ * w₀ := by group
      _ = a * w₀ := by rw [hw₀a]
  have hw₀Θ : w₀ ∈ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta Ca hw₀C
  set ρ : A →* MulAut Θ := Θ.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (x : A) (y : Θ), ((ρ x y : Θ) : G) = (x : G) * y * (x : G)⁻¹ := fun x y =>
    Sec4.normalizerMonoidHom_apply_coe (hAN x.2) y
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := (Sec6.theta_solvable_and_not_dvd Ca).2
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Θ) := by
    rw [h.card_eq, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3)
  have hΘs : Group.IsSolvable Θ := (Sec6.theta_solvable_and_not_dvd Ca).1
  obtain ⟨Q, hQS⟩ := hS
  have hQinv' : ∀ x : A, ∀ y ∈ (Q : Subgroup Θ), ρ x y ∈ (Q : Subgroup Θ) := by
    intro x y hy
    have hyS : (y : G) ∈ S := hQS ▸ ⟨y, hy, rfl⟩
    have h1 : (x : G) * y * (x : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hSA x.2) y).mp hyS
    rw [← hQS] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hz' : z = ρ x y := Subtype.ext (by rw [hρapp]; exact hzeq)
    rw [← hz']
    exact hz
  set ρw : MulAut Θ := Θ.normalizerMonoidHom ⟨w₀, hw₀Θ⟩ with hρw
  have hρwapp : ∀ z : Θ, ((ρw z : Θ) : G) = w₀ * z * w₀⁻¹ := fun z =>
    Sec4.normalizerMonoidHom_apply_coe hw₀Θ z
  have hρwinv : ∀ z : Θ, ((ρw⁻¹ z : Θ) : G) = w₀⁻¹ * z * w₀ := fun z => by
    have h1 : ρw⁻¹ = Θ.normalizerMonoidHom ⟨w₀⁻¹, Subgroup.inv_mem _ hw₀Θ⟩ := by
      rw [hρw, ← map_inv]
      rfl
    rw [h1, Sec4.normalizerMonoidHom_apply_coe, inv_inv]
  set Q' : Sylow 2 Θ := ρw • Q with hQ'
  have hQ'mem : ∀ z : Θ, z ∈ (Q' : Subgroup Θ) ↔ ρw⁻¹ z ∈ (Q : Subgroup Θ) := fun z => by
    rw [hQ', Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hQ'inv : ∀ x : A, ∀ z ∈ (Q' : Subgroup Θ), ρ x z ∈ (Q' : Subgroup Θ) := by
    intro x z hz
    rw [hQ'mem] at hz ⊢
    have hx' : w₀⁻¹ * x * w₀ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw₀N) x).mp x.2
      simpa using this
    have hmem := hQinv' ⟨_, hx'⟩ _ hz
    convert hmem using 1
    apply Subtype.ext
    rw [hρwinv, hρapp, hρapp, hρwinv]
    group
  obtain ⟨y, hyfix, hyQ⟩ :=
    GroupTheory.SteinbergBK.solvable_coprime_invariant_sylow_conjugacy hΘs hcop ρ Q' Q hQ'inv
      hQinv'
  have hyC : (y : G) ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have h1 := congrArg Subtype.val (hyfix ⟨x, hx⟩)
      rw [hρapp] at h1
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h1]
  have hcomm : ∀ x ∈ A, (y : G)⁻¹ * x * y = x := fun x hx => by
    have h1 := Subgroup.mem_centralizer_iff.mp hyC x hx
    calc (y : G)⁻¹ * x * y = (y : G)⁻¹ * (x * y) := by group
      _ = (y : G)⁻¹ * (y * x) := by rw [h1]
      _ = x := by group
  set w := (y : G)⁻¹ * w₀ with hw
  have hwconj : ∀ g : G, w * g * w⁻¹ = (y : G)⁻¹ * (w₀ * g * w₀⁻¹) * y := fun g => by
    rw [hw]
    group
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hyC)) hw₀N
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hQS]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      have hsQ' : ρw s ∈ (Q' : Subgroup Θ) := by
        rw [hQ'mem, MulAut.inv_apply_self]
        exact hs
      have hmem : (MulAut.conj y⁻¹) (ρw s) ∈ (Q : Subgroup Θ) := by
        rw [← hyQ]
        exact ⟨_, hsQ', rfl⟩
      refine ⟨_, hmem, ?_⟩
      change ((MulAut.conj y⁻¹ (ρw s) : Θ) : G) = w * (s : G) * w⁻¹
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
        hρwapp, hwconj]
    · exact (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge
  · rw [hwconj, hw₀a, hcomm a h.a_mem]
  · rw [hwconj, hw₀d, hcomm d hdA]
  · rw [hwconj, hw₀c, hcomm (c * d) (A.mul_mem h.mem_A hdA)]

theorem le_theta_e (h1011 : Item1011Two) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {e : G} (he : e ∈ Subgroup.closure ({a, c} : Set G))
    (hec : e ∉ Subgroup.zpowers c) {X : Subgroup G}
    (hXU : X ≤ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)))
    (hXe : X ≤ Subgroup.centralizer ({e} : Set G))
    (hXa : ¬ X ≤ Subgroup.centralizer ({a} : Set G)) :
    sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
  obtain ⟨x, hxX, hxa⟩ : ∃ x ∈ X, x ∉ Subgroup.centralizer ({a} : Set G) := by
    by_contra hall
    push Not at hall
    exact hXa hall
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ Subgroup.one_mem _)
  have hxe : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hXe hxX)
  have hxc : ¬ Commute x c := by
    intro hxc
    obtain ⟨i, j, hij, hi⟩ := Sec10XProof.exists_eq_zpow_of_mem_closure h he hec
    rw [hij] at hxe
    have h2 : Commute x (a ^ i) := by
      have := hxe.mul_right (hxc.zpow_right (-j))
      rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at this
    have hii : (i * i) % 3 = 1 := by
      have : i % 3 = 1 ∨ i % 3 = 2 := by omega
      rcases this with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
    have h3 := h2.zpow_right i
    rw [← zpow_mul, Sec10XProof.zpow_eq_zpow_emod_three (h.pow_three h.a_mem), hii,
      zpow_one] at h3
    exact hxa (Subgroup.mem_centralizer_singleton_iff.mpr h3)
  have hxO : x ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) :=
    Sec10XProof.inf_centralizer_le_pCore_inf _ e ⟨hXU hxX, hXe hxX⟩
  have hcomm : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)), Subgroup.zpowers c⁆ ≠ ⊥ := by
    intro hbot
    have hmem := Subgroup.commutator_mem_commutator hxO (Subgroup.mem_zpowers c)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hxc hmem
  exact h1011 G A c L a R h d hdL e he he1 hcomm

theorem pow_two_eq_one (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSab : IsMulCommutative S) (hSA : A ≤ Subgroup.normalizer (S : Set G))
    (hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a)
    (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) {w : G}
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwd : w * d * w⁻¹ = d)
    (hwc : w * c * w⁻¹ = c * d) : ∀ s ∈ S, s ^ 2 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  obtain ⟨-, -, hUe, -⟩ := Sec10XSteps.sec10U_facts h
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hSab.1.comm ⟨s, hs⟩ ⟨t, ht⟩)
  let M : Subgroup G :=
    { carrier := {s | s ∈ S ∧ s ^ 2 = 1}
      one_mem' := ⟨S.one_mem, one_pow 2⟩
      mul_mem' := fun {s t} hs ht => ⟨S.mul_mem hs.1 ht.1, by
        rw [(Commute.mul_pow (hcomm s hs.1 t ht.1) 2), hs.2, ht.2, one_mul]⟩
      inv_mem' := fun {s} hs => ⟨S.inv_mem hs.1, by rw [inv_pow, hs.2, inv_one]⟩ }
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.mem_A
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hSM : S ≤ M := by
    refine Sec10XSteps.le_of_inf_centralizer_le (h.pow_three h.mem_A) (h.pow_three hdA)
      (h.comm h.mem_A hdA) (Sec10XProof.isElemAbelian_of_le h hcdA)
      (Sec10XSteps.card_closure_c_d h hdL hd3).ge hS2 (hcdA.trans hSA) hwS hwc hwd
      (fun x hx => ⟨(Subgroup.mem_normalizer_iff.mp hwS x).mp hx.1, by
        rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩) ?_ ?_
    · rw [hSc]
      intro u hu
      exact ⟨(hSc.ge hu).1, hUe.2 u hu⟩
    · rw [hSd]
      exact bot_le
  exact fun s hs => (hSM hs).2

end Step1012ClaimProof

end CFSG.RankThree.PartTwo.Sec10
