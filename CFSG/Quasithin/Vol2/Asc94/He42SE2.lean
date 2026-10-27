module

public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.A94.He42SE

open CFSG.Open

private theorem he42s2_eq_of_sq_eq_one_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {x y : C} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hxy
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx
    · exact hy
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hy1⟩), Finset.card_pair hxy]
  have := Finset.card_le_card hsub
  change _ ≤ (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card at this
  have h2 : (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card ≤ 2 := by
    convert hle using 2
  omega

private theorem he42s2_eq_of_sq_eq_one_quaternion {n : ℕ} [NeZero n] {x y : QuaternionGroup n}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have han : (QuaternionGroup.a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
    rw [← QuaternionGroup.a_one_pow]
    refine pow_ne_one_of_lt_orderOf (NeZero.ne n) ?_
    rw [QuaternionGroup.orderOf_a_one]
    have := NeZero.pos n
    omega
  have hmem : ∀ g : QuaternionGroup n, g ^ 2 = 1 → g ∈ Subgroup.zpowers (QuaternionGroup.a 1) := by
    intro g hg
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    · rw [QuaternionGroup.xa_sq] at hg
      exact absurd hg han
  have := he42s2_eq_of_sq_eq_one_cyclic (C := Subgroup.zpowers (QuaternionGroup.a (1 : ZMod (2 * n))))
    (x := ⟨x, hmem x hx⟩) (y := ⟨y, hmem y hy⟩) (Subtype.ext (by simpa using hx))
    (Subtype.ext (by simpa using hy)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

private theorem he42s2_eq_of_sq_eq_one_sylow {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsCyclic S ∨ ∃ r : ℕ, 3 ≤ r ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2))))
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  rcases hS with hcyc | ⟨r, -, ⟨e⟩⟩
  · haveI := hcyc
    exact congrArg Subtype.val
      (he42s2_eq_of_sq_eq_one_cyclic (C := S) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
        (Subtype.ext (by simpa using hx2)) (Subtype.ext (by simpa using hy2))
        (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h)))
  · haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have hx' : e ⟨x, hx⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨x, hx⟩ : S) ^ 2 = 1 from Subtype.ext (by simpa using hx2), map_one]
    have hy' : e ⟨y, hy⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨y, hy⟩ : S) ^ 2 = 1 from Subtype.ext (by simpa using hy2), map_one]
    have hx1' : e ⟨x, hx⟩ ≠ 1 := fun h =>
      hx1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    have hy1' : e ⟨y, hy⟩ ≠ 1 := fun h =>
      hy1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    exact congrArg Subtype.val
      (e.injective (he42s2_eq_of_sq_eq_one_quaternion hx' hy' hx1' hy1'))

theorem false_of_stronglyEmbedded {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (hH : fusionStronglyEmbedded H) (hsimple : IsSimpleGroup ↥H)
    (E : Subgroup X) (hEH : E ≤ H) (hEcard : Nat.card E = 4) (hEsq : ∀ e ∈ E, e * e = 1)
    (U W : Subgroup X) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUH : U ≤ H) (hWH : W ≤ H)
    (hWU : W ≤ Subgroup.normalizer (U : Set X)) (hW : ¬ Group.IsSolvable ↥W) : False := by
  rcases CFSG.Open.bender_strongly_embedded_normal_series X H hH with hcase |
    ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hB⟩
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 2) (hEcard.trans (by norm_num))
    obtain ⟨S, hES⟩ := hEp.exists_le_sylow
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hEcard]; norm_num)
    obtain ⟨z', hz'⟩ := exists_ne (1 : E)
    obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 :=
      ⟨z', z'.2, fun h => hz' (Subtype.ext h)⟩
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hEsq z hzE
    have hsq : ∀ y ∈ E, y ^ 2 = 1 := fun y hy => by rw [pow_two]; exact hEsq y hy
    have hEsub : E ≤ Subgroup.zpowers z := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact Subgroup.one_mem _
      · have hyz : y = z :=
          he42s2_eq_of_sq_eq_one_sylow (hcase S) (hES hy) (hES hzE) (hsq y hy) hz2 hy1 hz1
        rw [hyz]; exact Subgroup.mem_zpowers z
    have hcard := Subgroup.card_le_of_le hEsub
    rw [Nat.card_zpowers, hEcard] at hcard
    have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz2)
    omega
  ·
    haveI := hMn
    haveI := hNn
    haveI := hMNn
    haveI : (N.subgroupOf H).Normal := hNn.subgroupOf H
    haveI : (M.subgroupOf H).Normal := hMn.subgroupOf H
    have hHN : H ≤ N := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf H) with hbot | htop
      · exfalso
        let f : ↥H →* (X ⧸ N) := (QuotientGroup.mk' N).comp H.subtype
        have hf : Function.Injective f := by
          rw [injective_iff_map_eq_one]
          intro h hh
          have h1 : (h : X) ∈ N := (QuotientGroup.eq_one_iff _).1 hh
          have h2 : h ∈ N.subgroupOf H := Subgroup.mem_subgroupOf.2 h1
          rw [hbot, Subgroup.mem_bot] at h2
          exact h2
        have hdvd : Nat.card H ∣ Nat.card (X ⧸ N) := Subgroup.card_dvd_of_injective f hf
        rw [← Subgroup.index_eq_card] at hdvd
        have h2 : 2 ∣ N.index := (even_iff_two_dvd.mp hH.2.1).trans hdvd
        exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
      · exact Subgroup.subgroupOf_eq_top.1 htop
    have hMH : M.subgroupOf H = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf H) with hbot | htop
      · exact hbot
      · exfalso
        have hdvd : Nat.card (M.subgroupOf H) ∣ Nat.card M :=
          Subgroup.card_comap_dvd_of_injective M H.subtype H.subtype_injective
        rw [htop, Subgroup.card_top] at hdvd
        exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hModd hdvd)) hH.2.1
    let ψ : ↥H →* (↥N ⧸ M.subgroupOf N) :=
      (QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hHN)
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro h hh
      have h1 : Subgroup.inclusion hHN h ∈ M.subgroupOf N := (QuotientGroup.eq_one_iff _).1 hh
      have h2 : h ∈ M.subgroupOf H := h1
      rw [hMH, Subgroup.mem_bot] at h2
      exact h2
    have hUne : U.subgroupOf H ≠ ⊥ := by
      intro hbot
      apply hU
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      have h1 : (⟨u, hUH hu⟩ : ↥H) ∈ U.subgroupOf H := Subgroup.mem_subgroupOf.2 hu
      rw [hbot, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    have hÛne : (U.subgroupOf H).map ψ ≠ ⊥ := fun h =>
      hUne ((Subgroup.map_eq_bot_iff_of_injective (U.subgroupOf H) hψ).1 h)
    have hUH2 : IsPGroup 2 (U.subgroupOf H) :=
      hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
    have hÛ2 : IsPGroup 2 ((U.subgroupOf H).map ψ) := hUH2.map ψ
    have hkey : ∀ w ∈ W.subgroupOf H, ∀ u ∈ U.subgroupOf H, w * u * w⁻¹ ∈ U.subgroupOf H := by
      intro w hw u hu
      rw [Subgroup.mem_subgroupOf] at hw hu ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1 (hWU hw) (u : X)).1 hu
      simpa using h1
    have hWn : (W.subgroupOf H).map ψ ≤
        Subgroup.normalizer (((U.subgroupOf H).map ψ : Subgroup (↥N ⧸ M.subgroupOf N)) :
          Set (↥N ⧸ M.subgroupOf N)) := by
      rintro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
        exact Subgroup.mem_map.2 ⟨w * u * w⁻¹, hkey w hw u hu, by simp only [map_mul, map_inv]⟩
      · intro hy
        obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 hy
        refine Subgroup.mem_map.2
          ⟨w⁻¹ * u * w⁻¹⁻¹, hkey w⁻¹ (inv_mem hw) u hu, ?_⟩
        simp only [map_mul, map_inv, inv_inv]
        rw [hu']
        group
    have hsolv : Group.IsSolvable ↥((W.subgroupOf H).map ψ) :=
      CFSG.Quasithin.H13.Cor332.twoLocalsSolvable_of_fusionIsBenderGroup hB ((U.subgroupOf H).map ψ)
        ((W.subgroupOf H).map ψ) hÛne hÛ2 hWn
    haveI := hsolv
    have hWHsolv : Group.IsSolvable ↥(W.subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective (W.subgroupOf H) ψ hψ).toMonoidHom)
        (Subgroup.equivMapOfInjective (W.subgroupOf H) ψ hψ).injective
    haveI := hWHsolv
    exact hW (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hWH).symm.injective)

end CFSG.Quasithin.A94.He42SE
