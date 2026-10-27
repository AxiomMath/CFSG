module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofSym
public import CFSG.RankThree.PGroups.CoprimeInvariantSylow
public import CFSG.GroupTheory.SteinbergBKCoprimeSylowConjugacy

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

namespace Sec10XProof

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem exists_transvection (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hd3 : orderOf d = 3) (hA : A = Subgroup.closure {c, a, d}) :
    ∃ τ ∈ Sec12.transvectionGroup A ⟨d, h.d_mem_A hdL⟩,
      ((τ ⟨a, h.a_mem⟩ : A) : G) = a ∧ ((τ ⟨c, h.mem_A⟩ : A) : G) = c * d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  set B₀ := Subgroup.closure ({a, d} : Set G) with hB₀
  have haB : a ∈ B₀ := Subgroup.subset_closure (by simp)
  have hdB : d ∈ B₀ := Subgroup.subset_closure (by simp)
  have hB₀A : B₀ ≤ A := by
    rw [hB₀, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.a_mem
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hB₀card : Nat.card B₀ = 9 := card_closure_a_d h hdL hd3
  have hcB₀ : c ∉ B₀ := by
    intro hc
    have hAB : A ≤ B₀ := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | hy
      · exact hc
      · exact haB
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hdB
    have hle := Subgroup.card_le_of_le hAB
    rw [h.card_eq, hB₀card] at hle
    norm_num at hle
  have hAcomm : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext (h.comm x.2 y.2)
  set B' := B₀.subgroupOf A with hB'
  have hB'n : B'.Normal := ⟨fun x hx g => by
    have hgx : g * x * g⁻¹ = x := by rw [hAcomm g x, mul_inv_cancel_right]
    rw [hgx]
    exact hx⟩
  set c' : A := ⟨c, h.mem_A⟩ with hc'
  set d' : A := ⟨d, hdA⟩ with hd'
  set a' : A := ⟨a, h.a_mem⟩ with ha'
  set q : A ⧸ B' := (c' : A ⧸ B') with hq
  have hQcard : Nat.card (A ⧸ B') = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup B'
    rw [card_subgroupOf_of_le hB₀A, hB₀card, h.card_eq] at h1
    omega
  have hq1 : q ≠ 1 := by
    intro hq1
    rw [hq, QuotientGroup.eq_one_iff] at hq1
    exact hcB₀ (Subgroup.mem_subgroupOf.mp hq1)
  have hq3 : orderOf q = 3 := by
    have hc3 : c' ^ 3 = 1 := Subtype.ext (by simpa using h.pow_three h.mem_A)
    have : q ^ 3 = 1 := by rw [hq, ← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
    exact orderOf_eq_prime this hq1
  have hgen : ∀ x : A ⧸ B', x ∈ Subgroup.zpowers q := by
    have heq : Subgroup.zpowers q = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hq3, hQcard])
    intro x
    rw [heq]
    exact Subgroup.mem_top x
  have hd'o : orderOf d' ∣ orderOf q := by
    rw [hq3, Subgroup.orderOf_mk, hd3]
  set ψ : A ⧸ B' →* A := monoidHomOfForallMemZpowers hgen hd'o with hψ
  have hψq : ψ q = d' := monoidHomOfForallMemZpowers_apply_gen hgen hd'o
  set χ : A →* A := ψ.comp (QuotientGroup.mk' B') with hχ
  have hχB : ∀ x : A, (x : G) ∈ B₀ → χ x = 1 := fun x hx => by
    have hx1 : (x : A ⧸ B') = 1 := (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hx1, map_one]
  have hχd : ∀ x : A, χ x ∈ Subgroup.zpowers d' := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen (x : A ⧸ B'))
    rw [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hk, map_zpow, hψq]
    exact Subgroup.zpow_mem_zpowers d' k
  have hχc : χ c' = d' := hψq
  let τ₀ : A →* A :=
    { toFun := fun x => x * χ x
      map_one' := by rw [map_one, mul_one]
      map_mul' := fun x y => by
        rw [map_mul]
        calc x * y * (χ x * χ y) = x * (y * χ x) * χ y := by group
          _ = x * (χ x * y) * χ y := by rw [hAcomm y (χ x)]
          _ = x * χ x * (y * χ y) := by group }
  have hτ₀ : ∀ x, τ₀ x = x * χ x := fun _ => rfl
  have hτinj : Function.Injective τ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hτ₀] at hx
    have hx' : x = (χ x)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hxd : x ∈ Subgroup.zpowers d' := hx' ▸ Subgroup.inv_mem _ (hχd x)
    have hxB : (x : G) ∈ B₀ := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxd
      simpa using Subgroup.zpow_mem _ hdB k
    rw [hχB x hxB, inv_one] at hx'
    rw [hx']
    exact Subgroup.one_mem _
  set τ : MulAut A := MulEquiv.ofBijective τ₀ hτinj.bijective_of_finite with hτ
  have hτapp : ∀ x, τ x = x * χ x := fun _ => rfl
  refine ⟨τ, ⟨?_, fun x => ?_⟩, ?_, ?_⟩
  · rw [hτapp, hχB d' hdB, mul_one]
  · rw [hτapp, hAcomm x (χ x), mul_inv_cancel_right]
    exact hχd x
  · rw [hτapp, hχB a' haB, mul_one]
  · rw [hτapp, hχc]
    rfl

theorem exists_w (h107 : Item107) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hU : sec10U L a ∈ fourGroupsMinus A)
    (hUθ : sec10U L a ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    ∃ S ∈ maxInvariantPiSubgroups
        (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
      sec10U L a ≤ S ∧ ∃ w ∈ Subgroup.normalizer (A : Set G),
        w ∈ Subgroup.normalizer (S : Set G) ∧ w * a * w⁻¹ = a ∧ w * d * w⁻¹ = d ∧
          w * c * w⁻¹ = c * d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨τ, hτT, hτa, hτc⟩ := exists_transvection h hdL hd3 hAcl
  obtain ⟨w₀, hw₀N, -, hw₀τ⟩ := Sec4.mem_autIn_iff.mp (h107 G A c L a R h d hdA hdL hτT)
  have hw₀ : ∀ x : A, w₀ * x * w₀⁻¹ = (τ x : G) := fun x => by
    rw [← hw₀τ, Sec4.normalizerMonoidHom_apply_coe]
  have hw₀a : w₀ * a * w₀⁻¹ = a := (hw₀ ⟨a, h.a_mem⟩).trans hτa
  have hw₀c : w₀ * c * w₀⁻¹ = c * d := (hw₀ ⟨c, h.mem_A⟩).trans hτc
  have hw₀d : w₀ * d * w₀⁻¹ = d := (hw₀ ⟨d, hdA⟩).trans (congrArg Subtype.val hτT.1)
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Θ := inSubgroup (aschbacherSolvableCore 3) Ca with hΘ
  have hAC : A ≤ Ca := le_centralizer_of_mem h h.a_mem
  have hAN : A ≤ Subgroup.normalizer (Θ : Set G) := hAC.trans (Sec6.le_normalizer_theta Ca)
  have hw₀C : w₀ ∈ Ca := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w₀ * a = w₀ * a * w₀⁻¹ * w₀ := by group
      _ = a * w₀ := by rw [hw₀a]
  have hw₀Θ : w₀ ∈ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta Ca hw₀C
  set ρ : A →* MulAut Θ := Θ.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (x : A) (y : Θ), ((ρ x y : Θ) : G) = (x : G) * y * (x : G)⁻¹ := fun x y =>
    Sec4.normalizerMonoidHom_apply_coe (hAN x.2) y
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective Ca.subtype_injective]
    exact not_three_dvd_card_theta Ca
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Θ) := by
    rw [h.card_eq, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3)
  have hΘs : Group.IsSolvable Θ := by
    have : Group.IsSolvable (aschbacherSolvableCore 3 Ca) :=
      (solvable_prime_complement_core_characterization (H := Ca) Nat.prime_three).1
    exact Group.isSolvable_of_surjective
      (f := ((aschbacherSolvableCore 3 Ca).equivMapOfInjective Ca.subtype
        Ca.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hAs : Group.IsSolvable A := Group.isSolvable_of_comm fun x y => Subtype.ext (h.comm x.2 y.2)
  set U := sec10U L a with hUdef
  obtain ⟨⟨⟨-, hU2, hUA⟩, -, -⟩, -⟩ := hU
  have hU2' : IsPGroup 2 U := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hU2
  set U' := U.subgroupOf Θ with hU'
  have hU'2 : IsPGroup 2 U' := hU2'.comap_subtype (K := Θ)
  have hU'inv : ∀ x : A, ∀ u ∈ U', ρ x u ∈ U' := fun x u hu => by
    rw [Subgroup.mem_subgroupOf, hρapp]
    exact (Subgroup.mem_normalizer_iff.mp (hUA x.2) u).mp (Subgroup.mem_subgroupOf.mp hu)
  obtain ⟨Q, hUQ, hQinv⟩ :=
    (PGroups.solvable_coprime_invariant_sylow_containment hcop ρ Nat.prime_two).1 U' hU'2 hU'inv
  have hQinv' : ∀ x : A, ∀ y ∈ (Q : Subgroup Θ), ρ x y ∈ (Q : Subgroup Θ) := fun x y hy => by
    rw [← hQinv x]
    exact ⟨y, hy, rfl⟩
  set S := (Q : Subgroup Θ).map Θ.subtype with hS
  have hSΘ : S ≤ Θ := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := Q.isPGroup'.map _
  have hSA : A ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ρ ⟨x, hx⟩ s, hQinv' ⟨x, hx⟩ s hs, hρapp ⟨x, hx⟩ s⟩
    · rintro ⟨s, hs, hsz⟩
      refine ⟨ρ ⟨x, hx⟩⁻¹ s, hQinv' _ s hs, ?_⟩
      have h1 := hρapp ⟨x, hx⟩⁻¹ s
      simp only [Subgroup.coe_subtype] at hsz ⊢
      rw [h1, hsz]
      simp only [Subgroup.coe_inv, inv_inv]
      group
  have hSmax : S ∈ maxInvariantPiSubgroups Θ A (piOf 2) := by
    rw [mem_maxInvariantPiSubgroups_iff]
    refine ⟨⟨hSΘ, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2, hSA⟩, fun Y hY hSY => ?_⟩
    obtain ⟨hYΘ, hY2, -⟩ := hY
    have hY2' : IsPGroup 2 Y := (isPiSubgroup_piOf_iff Nat.prime_two Y).mp hY2
    have hQY : (Q : Subgroup Θ) ≤ Y.subgroupOf Θ := fun z hz =>
      Subgroup.mem_subgroupOf.mpr (hSY ⟨z, hz, rfl⟩)
    have heq := Q.is_maximal' (hY2'.comap_subtype (K := Θ)) hQY
    refine le_antisymm (fun z hz => ?_) hSY
    have hzQ : (⟨z, hYΘ hz⟩ : Θ) ∈ (Q : Subgroup Θ) := heq ▸ Subgroup.mem_subgroupOf.mpr hz
    exact ⟨_, hzQ, rfl⟩
  have hUS : U ≤ S := fun u hu => ⟨⟨u, hUθ hu⟩, hUQ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
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
  refine ⟨S, hSmax, hUS, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hyC)) hw₀N
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
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

end Std

end Sec10XProof

end CFSG.RankThree.PartTwo.Sec10
