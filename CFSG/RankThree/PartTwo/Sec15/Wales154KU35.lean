module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.Models.PGL
import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
import CFSG.GH74.KGroups.L3EpsUniInv
import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
import CFSG.Quasithin.Vol2.KGFactAutSylowU35Syl
import CFSG.Quasithin.Background.F6W16Wreath
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG.Open

namespace KU35

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.KGroups.L3Eps.Uni

theorem pow_three_of_mem_scalars {F : Type} [Field F] (hU : UnitaryFieldData 5 1 F)
    {z : unitarySU 5 1 F 3} (hz : z ∈ unitaryScalars hU 3) : z ^ 3 = 1 := by
  have hcard : Nat.card (unitaryScalars hU 3) = 3 := by
    rw [card_unitaryScalars hU (by norm_num)]
    norm_num
  have h := pow_card_eq_one' (G := unitaryScalars hU 3) (x := ⟨z, hz⟩)
  rw [hcard] at h
  exact congrArg Subtype.val h

theorem no_commute_seven {Q : Type} [Group Q] (hQ : StatedClassicalModel Q .PSU 3 5 1)
    {t y : Q} (ht : orderOf t = 2) (hy : orderOf y = 7) : t * y ≠ y * t := by
  intro hty
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hconj⟩ := CFSG.RankThree.Classical.unitary_three_five_model Q hQ
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have hU : UnitaryFieldData 5 1 F := ⟨Nat.prime_five, le_rfl, by rw [hF]; norm_num⟩
  have hq : Odd (5 ^ 1) := by decide
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hU e₀
  have ht₀ : orderOf (θ (dU hq)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact theta_dU_sq hq θ) (theta_dU_ne_one hU hq hθ)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj t _ ht ht₀)
  have hx7 : orderOf (c * y * c⁻¹) = 7 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hxC : c * y * c⁻¹ ∈ Subgroup.centralizer ({θ (dU hq)} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * y * c⁻¹ * (c * t * c⁻¹) = c * (y * t) * c⁻¹ := by group
      _ = c * (t * y) * c⁻¹ := by rw [hty]
      _ = c * t * c⁻¹ * (c * y * c⁻¹) := by group
  obtain ⟨g, hg, hgd⟩ := cen_lift hU θ hθ.ker hθ.surj (two_ne_zero_of_odd_pow hU hq) hq hxC
  have hg21 : g ^ 21 = 1 := by
    have h7 : g ^ 7 ∈ unitaryScalars hU 3 := by
      rw [← hθ.ker, MonoidHom.mem_ker, map_pow, hg, ← hx7]
      exact pow_orderOf_eq_one _
    rw [show (21 : ℕ) = 7 * 3 by norm_num, pow_mul]
    exact pow_three_of_mem_scalars hU h7
  let G : Subgroup.centralizer ({dU hq} : Set (unitarySU 5 1 F 3)) :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.2 hgd⟩
  have hu24 : cenHomU hU hq G ^ 24 = 1 := by
    have hcard : Nat.card Fˣ = 24 := by
      have h := Nat.card_units (α := F)
      rw [hF] at h
      norm_num at h
      exact h
    rw [← hcard]
    exact pow_card_eq_one'
  have hG21 : G ^ 21 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg21)
  have hu21 : cenHomU hU hq G ^ 21 = 1 := by rw [← map_pow, hG21, map_one]
  have hu3 : cenHomU hU hq (G ^ 3) = 1 := by
    have h := pow_add (cenHomU hU hq G) 21 3
    rw [show (21 : ℕ) + 3 = 24 by norm_num, hu24, hu21, one_mul] at h
    rw [map_pow]
    exact h.symm
  obtain ⟨B, hB⟩ := mem_range_levU_of_cenHomU hU hq (G ^ 3) hu3
  have hmem : (c * y * c⁻¹) ^ 3 ∈ levS hq θ := by
    refine (mem_levS hq).2 ⟨B, ?_⟩
    rw [hB, Subgroup.coe_pow, map_pow]
    exact congrArg (· ^ 3) hg
  have hord : orderOf ((c * y * c⁻¹) ^ 3) = 7 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hx7]; norm_num), hx7]
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hord, card_levS hU hθ hq] at hdvd
  norm_num at hdvd

theorem card_involutions_le_five {Q : Type} [Group Q] [Finite Q]
    (hQ : StatedClassicalModel Q .PSU 3 5 1) {S : Subgroup Q} (hS : IsPGroup 2 S) :
    Nat.card {s : Q // s ∈ S ∧ orderOf s = 2} ≤ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have : Finite (StatedProj (StatedSU 3 (5 ^ 1) F)) := Finite.of_equiv Q e₀.toEquiv
  obtain ⟨T, ⟨eT⟩⟩ := CFSG.Quasithin.H13.KGAutSyl.u35SylowSemidihedral_holds F hF
  obtain ⟨T', hST'⟩ := (hS.map e₀.toMonoidHom).exists_le_sylow
  have e₁ : ↥(T' : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F))) ≃* SemidihedralGroup 4 :=
    (Sylow.equiv T' T).trans eT
  let ι : {s : Q // s ∈ S ∧ orderOf s = 2} →
      {x : ↥(T' : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F))) // orderOf x = 2} :=
    fun s => ⟨⟨e₀ s.1, hST' (Subgroup.mem_map_of_mem e₀.toMonoidHom s.2.1)⟩, by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq]
      exact s.2.2⟩
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply e₀.injective
    have h := congrArg (fun x : {x : ↥(T' : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F))) //
      orderOf x = 2} => ((x.1 : ↥(T' : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F)))) :
        StatedProj (StatedSU 3 (5 ^ 1) F))) hab
    exact h
  calc Nat.card {s : Q // s ∈ S ∧ orderOf s = 2}
      ≤ Nat.card {x : ↥(T' : Subgroup (StatedProj (StatedSU 3 (5 ^ 1) F))) // orderOf x = 2} :=
        Nat.card_le_card_of_injective ι hι
    _ = CFSG.Quasithin.F6.WreathRes.involutionCount (SemidihedralGroup 4) :=
        CFSG.Quasithin.F6.WreathRes.involutionCount_congr e₁
    _ = 5 := CFSG.Quasithin.F6.WreathRes.involutionCount_semidihedral_four

theorem seven_dvd_card_involutions {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q} {y : Q}
    (hy : y ^ 7 = 1) (hyS : y ∈ Subgroup.normalizer (S : Set Q))
    (hfree : ∀ s ∈ S, orderOf s = 2 → s * y ≠ y * s) :
    7 ∣ Nat.card {s : Q // s ∈ S ∧ orderOf s = 2} := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype {s : Q // s ∈ S ∧ orderOf s = 2} := Fintype.ofFinite _
  have hmem : ∀ s : {s : Q // s ∈ S ∧ orderOf s = 2},
      y * s * y⁻¹ ∈ S ∧ orderOf (y * s * y⁻¹) = 2 := fun s =>
    ⟨(Subgroup.mem_normalizer_iff.mp hyS s).mp s.2.1, by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact s.2.2⟩
  let f : Function.End {s : Q // s ∈ S ∧ orderOf s = 2} := fun s => ⟨y * s * y⁻¹, hmem s⟩
  have hpow : ∀ (n : ℕ) (s : {s : Q // s ∈ S ∧ orderOf s = 2}),
      (((f ^ n) s : {s : Q // s ∈ S ∧ orderOf s = 2}) : Q) = y ^ n * s * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s; simp; rfl
    | succ n ih =>
      intro s
      rw [pow_succ']
      change y * (((f ^ n) s : {s : Q // s ∈ S ∧ orderOf s = 2}) : Q) * y⁻¹ = _
      rw [ih]
      simp only [pow_succ']
      group
  have hf : f ^ 7 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hpow, hy]
    show _ = (s : Q)
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 7) (n := 1) hf
  have hfix : Fintype.card ↑(Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    have h1 : y * (s : Q) * y⁻¹ = s := congrArg Subtype.val hs
    apply hfree s s.2.1 s.2.2
    calc (s : Q) * y = y * s * y⁻¹ * y := by rw [h1]
      _ = y * s := by group
  rw [hfix] at hmod
  rw [Nat.card_eq_fintype_card]
  exact Nat.modEq_zero_iff_dvd.mp hmod

theorem not_fix_seven {Q : Type} [Group Q] [Finite Q] (hQ : StatedClassicalModel Q .PSU 3 5 1)
    {σ : MulAut Q} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : Q →* MulAut Q).range)
    {y : Q} (hy : orderOf y = 7) : σ y ≠ y := by
  intro hσy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hA : ∀ u : Q, orderOf u = 2 → u * y ≠ y * u := fun u hu => no_commute_seven hQ hu hy
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have hU : UnitaryFieldData 5 1 F := ⟨Nat.prime_five, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hU e₀
  obtain ⟨N, hGD, ⟨eN⟩⟩ := CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3.graphData_of_cover_psl2
    hU (by norm_num) (by norm_num) (by decide) hθ hσ hout
  have hN : Nat.card N = 60 := by
    rw [Nat.card_congr eN.toEquiv,
      CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_projective_two_field,
      hU.card_fixedField]
    norm_num
  have hyN : y ∈ Subgroup.normalizer (N : Set Q) := by
    have hσy' : σ y⁻¹ = y⁻¹ := by rw [map_inv, hσy]
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hGD.conj_mem y hσy n, fun hn => ?_⟩
    have h := hGD.conj_mem y⁻¹ hσy' _ hn
    rwa [show y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n by group] at h
  have hmod := CFSG.RankThree.PartTwo.Sec16.Res9A10.card_modEq_card_inf_centralizer
    (p := 7) (D := Subgroup.zpowers y) (V := N)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one]))
    (Subgroup.zpowers_le.mpr hyN)
  rw [hN] at hmod
  set C : Subgroup Q := N ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup Q) : Set Q)
    with hC
  have hCdvd : Nat.card C ∣ 60 := by
    rw [← hN]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : 2 ∣ Nat.card C := by
    have hle : Nat.card C ≤ 60 := Nat.le_of_dvd (by norm_num) hCdvd
    unfold Nat.ModEq at hmod
    generalize Nat.card C = m at hCdvd hmod hle ⊢
    interval_cases m <;> omega
  obtain ⟨⟨u, huC⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
  rw [Subgroup.orderOf_mk] at hu
  have huy : y * u = u * y :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huC).2 y (Subgroup.mem_zpowers y)
  exact hA u hu huy.symm

end KU35

theorem ks154U35A7 : KS154U35A7 := by
  intro _ Q _ hQ K h7 P hP hKP
  obtain ⟨e⟩ := hQ
  classical
  have hSt : StatedClassicalModel Q .PSU 3 5 1 :=
    CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU ⟨Fact.out, le_rfl, le_rfl, by decide⟩ e
  obtain ⟨hcard, -, ⟨t₀, ht₀⟩, -⟩ := CFSG.RankThree.Classical.unitary_three_five_model Q hSt
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨y, hyK⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 h7
  rw [Subgroup.orderOf_mk] at hy
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hZ : Subgroup.center Q = ⊥ := by
    have := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Q 3 5 1 hSt).2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have ht₀Z : t₀ ∈ Subgroup.center Q := by
        rw [h]
        exact Subgroup.mem_top t₀
      exact KU35.no_commute_seven hSt ht₀ hy (Subgroup.mem_center_iff.mp ht₀Z y).symm
  have hcZ : ∀ q : Q, c q = 1 → q = 1 := by
    intro q hq
    have hqZ : q ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun σ : MulAut Q => σ g) hq
      simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * q = q * g * q⁻¹ * q := by rw [h1]
        _ = q * g := by group
    rw [hZ, Subgroup.mem_bot] at hqZ
    exact hqZ
  set S : Subgroup Q := (P ⊓ c.range).comap c with hS
  have hS2 : IsPGroup 2 S := by
    rintro ⟨s, hs⟩
    rw [hS, Subgroup.mem_comap] at hs
    obtain ⟨n, hn⟩ := hP ⟨c s, (Subgroup.mem_inf.mp hs).1⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : c (s ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    simpa using hcZ _ h1
  have hKS : K ≤ Subgroup.normalizer (S : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk s hs
    rw [hS, Subgroup.mem_comap] at hs ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨k * s * k⁻¹, rfl⟩⟩
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKP k hk) (c s)).mp (Subgroup.mem_inf.mp hs).1
  have hSbot : S = ⊥ := by
    by_contra hne
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero]))
    obtain ⟨⟨s₀, hs₀S⟩, hs₀⟩ := exists_prime_orderOf_dvd_card' (G := S) 2
      (by rw [hm]; exact dvd_pow_self 2 hm0)
    rw [Subgroup.orderOf_mk] at hs₀
    have h5 := KU35.card_involutions_le_five hSt hS2
    have h7' := KU35.seven_dvd_card_involutions (S := S) (y := y)
      (by rw [← hy]; exact pow_orderOf_eq_one y) (hKS hyK)
      (fun s _ hs => KU35.no_commute_seven hSt hs hy)
    have hpos : 0 < Nat.card {s : Q // s ∈ S ∧ orderOf s = 2} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨s₀, hs₀S, hs₀⟩⟩, inferInstance⟩
    omega
  have hfix : ∀ σ ∈ P, ∀ k ∈ K, σ k = k := by
    intro σ hσ k hk
    have h1 : c (σ k * k⁻¹) ∈ P := by
      have h : c (σ k * k⁻¹) = σ * (c k * σ⁻¹ * (c k)⁻¹) := by
        ext z
        simp [hc, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]
      rw [h]
      exact P.mul_mem hσ ((Subgroup.mem_normalizer_iff.mp (hKP k hk) σ⁻¹).mp (P.inv_mem hσ))
    have h2 : σ k * k⁻¹ ∈ S := by
      rw [hS, Subgroup.mem_comap]
      exact Subgroup.mem_inf.mpr ⟨h1, ⟨σ k * k⁻¹, rfl⟩⟩
    rw [hSbot, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  by_contra hne
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero]))
  obtain ⟨⟨τ, hτP⟩, hτ⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    (by rw [hm]; exact dvd_pow_self 2 hm0)
  rw [Subgroup.orderOf_mk] at hτ
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτout : τ ∉ c.range := by
    rintro ⟨q, rfl⟩
    have hq : q ∈ S := by
      rw [hS, Subgroup.mem_comap]
      exact Subgroup.mem_inf.mpr ⟨hτP, ⟨q, rfl⟩⟩
    rw [hSbot, Subgroup.mem_bot] at hq
    rw [hq, map_one, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  exact KU35.not_fix_seven hSt hτ2 hτout hy (hfix τ hτP y hyK)

end CFSG.RankThree.PartTwo.Sec15.Wales154
