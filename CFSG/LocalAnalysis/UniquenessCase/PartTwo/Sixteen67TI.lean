module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen65
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1667_centralizer_le_of_four_le_card (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {F : Subgroup G}
    (hFV : F ≤ V) (hF : 4 ≤ Nat.card F) :
    centralizer (F : Set G) ≤ D.M := by
  have hFpg : IsPGroup 2 F := hV.isPGroup.to_le hFV
  obtain ⟨H', hH'card⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := ↥F) (p := 2) (n := 2) (by norm_num) hFpg (by simpa using hF)
  let F' : Subgroup G := H'.map F.subtype
  have hF'F : F' ≤ F := Subgroup.map_subtype_le H'
  have hF'card : Nat.card F' = 4 := by
    change Nat.card (H'.map F.subtype) = 4
    rw [Subgroup.card_map_of_injective F.subtype_injective, hH'card]
    norm_num
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hF'F)).trans
    (s1665_centralizer_le_of_card_four D hSg h61 h1217 hS hs h0 (hF'F.trans hFV) hF'card)

private theorem mem_centralizer_sup {W₁ W₂ V : Subgroup G} (hsup : W₁ ⊔ W₂ = V) {a : G}
    (h₁ : a ∈ Subgroup.centralizer (W₁ : Set G))
    (h₂ : a ∈ Subgroup.centralizer (W₂ : Set G)) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : W₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₁ y hy
  have h2 : W₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₂ y hy
  have hV : V ≤ Subgroup.centralizer ({a} : Set G) := hsup ▸ sup_le h1 h2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := hV hv
  rwa [Subgroup.mem_centralizer_singleton_iff] at hv'

private theorem isKleinFour_of_card_four_of_sq {W : Subgroup G} (hcard : Nat.card W = 4)
    (hsq : ∀ x ∈ W, x ^ 2 = 1) : IsKleinFour ↥W where
  card_four := hcard
  exponent_two := by
    haveI : Fintype ↥W := Fintype.ofFinite ↥W
    haveI : Nontrivial ↥W := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
      norm_num
    rw [Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)]
    intro x hx
    refine orderOf_eq_prime ?_ hx
    apply Subtype.ext
    simpa using hsq (x : G) x.2

private theorem relIndex_centralizer_le_three_of_kleinFour {W R : Subgroup G}
    (hW : IsKleinFour ↥W) (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hR : IsPGroup 3 ↥R) :
    (Subgroup.centralizer (W : Set G)).relIndex R ≤ 3 := by
  haveI : IsKleinFour ↥W := hW
  let ψ : ↥R →* MulAut ↥W :=
    (Subgroup.normalizerMonoidHom (H := W)).comp (Subgroup.inclusion hRW)
  have hker : ψ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf R := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change Subgroup.normalizerMonoidHom (H := W) (Subgroup.inclusion hRW x) = 1 ↔
      (x : G) ∈ Subgroup.centralizer (W : Set G)
    rw [← MonoidHom.mem_ker (f := Subgroup.normalizerMonoidHom (H := W)),
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hrange : Nat.card ψ.range ≤ 3 := by
    have hr3 : IsPGroup 3 ↥ψ.range :=
      hR.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hd6 : Nat.card ψ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [CFSG.kleinFour_automorphism_card ↥W] at this
    obtain ⟨n, hn⟩ := hr3.exists_card_eq
    rw [hn] at hd6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h9 : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle6 : 3 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hd6
      norm_num at h9
      omega
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 3 := by norm_num
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact hrange

theorem s1667_exists_orderOf_three (D : Data G) (hSg : UC6S846.SigmaStd D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) :
    ∃ c ∈ D.M, c ∈ centralizer (V : Set G) ∧ orderOf c = 3 := by
  obtain ⟨x, hxM, hxn⟩ :=
    c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  let W₁ : Subgroup G := wSub V₀ V hV L
  let W₂ : Subgroup G := conjSubgroup W₁ x
  have hsup : W₁ ⊔ W₂ = V := s1667_sup_conj_eq D h1217 hS hs.1 hxM hxn
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    show wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) x = ⊥
    rw [s1667_inf_conj_eq D hS hs.1 hxM hxn, h0]
  have hW₁card : Nat.card W₁ = 4 := by
    have hV0 : Nat.card V₀ = 1 := by rw [h0, Subgroup.card_bot]
    have h := s1667_card_wSub D hS hs.1
    rw [hV0, mul_one] at h
    exact h
  have hW₂card : Nat.card W₂ = 4 := by
    change Nat.card (conjSubgroup (wSub V₀ V hV L) x) = 4
    rw [E3.card_conjSubgroup]
    exact hW₁card
  have hne : W₁ ≠ W₂ := by
    intro heq
    have hbot : W₁ = ⊥ := by
      have h1 : W₁ ⊓ W₂ = W₁ := by rw [← heq, inf_idem]
      rw [← h1, hinf]
    have h2 : Nat.card W₁ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have h3sig : 3 ∈ D.sig := by
    rw [hs.1.2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨E, hEM, hEea, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3)
    (by norm_num) (by rw [UC6.groupPRank_eq_pRank]; exact hSg.three_le 3 h3sig)
  have hodd : Odd (Nat.card E) := by rw [hEcard]; norm_num
  have hfix : ∀ a ∈ E, conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂ :=
    s1667_forall_conj_eq_of_odd (W₁ := W₁) (W₂ := W₂) (E := E) hne hodd
      (fun a ha => s1667_conj_cases D hS hs.1 hxM hxn (hEM ha))
  have hW₁V : W₁ ≤ V := preTil_le V₀ V hV (wTil V₀ V hV L)
  have hW₂V : W₂ ≤ V := by
    have hnormV : conjSubgroup V x = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr
        (hS.setting.hyp16.hyp125.pairFacts.le_normalizer hxM)
    calc W₂ = conjSubgroup W₁ x := rfl
      _ ≤ conjSubgroup V x := E3.conjSubgroup_mono_left x hW₁V
      _ = V := hnormV
  have hK₁ : IsKleinFour ↥W₁ :=
    isKleinFour_of_card_four_of_sq hW₁card (fun u hu => hV.2 u (hW₁V hu))
  have hK₂ : IsKleinFour ↥W₂ :=
    isKleinFour_of_card_four_of_sq hW₂card (fun u hu => hV.2 u (hW₂V hu))
  have hnorm₁ : E ≤ Subgroup.normalizer (W₁ : Set G) := fun e he =>
    conjSubgroup_eq_iff_mem_normalizer.mp (hfix e he).1
  have hnorm₂ : E ≤ Subgroup.normalizer (W₂ : Set G) := fun e he =>
    conjSubgroup_eq_iff_mem_normalizer.mp (hfix e he).2
  have hEpg : IsPGroup 3 ↥E := hEea.isPGroup
  have hrel₁ : (Subgroup.centralizer (W₁ : Set G)).relIndex E ≤ 3 :=
    relIndex_centralizer_le_three_of_kleinFour (W := W₁) (R := E) hK₁ hnorm₁ hEpg
  have hrel₂ : (Subgroup.centralizer (W₂ : Set G)).relIndex E ≤ 3 :=
    relIndex_centralizer_le_three_of_kleinFour (W := W₂) (R := E) hK₂ hnorm₂ hEpg
  let F : Subgroup G :=
    Subgroup.centralizer (W₁ : Set G) ⊓ Subgroup.centralizer (W₂ : Set G)
  have hFrel : F.relIndex E ≤ 9 := by
    calc F.relIndex E
        ≤ (Subgroup.centralizer (W₁ : Set G)).relIndex E *
          (Subgroup.centralizer (W₂ : Set G)).relIndex E := Subgroup.relIndex_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul hrel₁ hrel₂
      _ = 9 := by norm_num
  have hmul : Nat.card (E ⊓ F : Subgroup G) * F.relIndex E = 27 := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_comm, hEcard] at h
    rwa [mul_comm] at h
  have hge3 : 3 ≤ Nat.card (E ⊓ F : Subgroup G) := by
    by_contra hcon
    have hle2 : Nat.card (E ⊓ F : Subgroup G) ≤ 2 := by omega
    have hle : Nat.card (E ⊓ F : Subgroup G) * F.relIndex E ≤ 2 * 9 :=
      Nat.mul_le_mul hle2 hFrel
    omega
  have hneF : E ⊓ F ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (E ⊓ F : Subgroup G) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  obtain ⟨c, hc1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hneF
  have hcE : (c : G) ∈ E := (Subgroup.mem_inf.mp c.2).1
  have hcF : (c : G) ∈ F := (Subgroup.mem_inf.mp c.2).2
  have hcC₁ : (c : G) ∈ Subgroup.centralizer (W₁ : Set G) := (Subgroup.mem_inf.mp hcF).1
  have hcC₂ : (c : G) ∈ Subgroup.centralizer (W₂ : Set G) := (Subgroup.mem_inf.mp hcF).2
  have hc1 : (c : G) ≠ 1 := fun h => hc1' (Subtype.ext h)
  refine ⟨(c : G), hEM hcE, mem_centralizer_sup hsup hcC₁ hcC₂, ?_⟩
  exact orderOf_eq_prime (hEea.2 (c : G) hcE) hc1

theorem s1667_card_inf_conj_le (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {y : G} (hy : y ∉ D.M) :
    Nat.card (V ⊓ conjSubgroup V y : Subgroup G) ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  let F : Subgroup G := V ⊓ conjSubgroup V y
  have hleF : 2 < Nat.card F := hle
  have hFV : F ≤ V := inf_le_left
  have hFpg : IsPGroup 2 F := hV.isPGroup.to_le hFV
  have hF4 : 4 ≤ Nat.card F := by
    obtain ⟨n, hn⟩ := hFpg.exists_card_eq
    rw [hn] at hleF ⊢
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · exact absurd hleF (by norm_num)
        · exact absurd hleF (by norm_num)
      · exact h
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hCFM : Subgroup.centralizer (F : Set G) ≤ D.M :=
    s1667_centralizer_le_of_four_le_card D hSg h61 h1217 hS hs h0 hFV hF4
  have hF'eq : conjSubgroup F y⁻¹ = conjSubgroup V y⁻¹ ⊓ V := by
    change conjSubgroup (V ⊓ conjSubgroup V y) y⁻¹ = conjSubgroup V y⁻¹ ⊓ V
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv]
  have hF'V : conjSubgroup F y⁻¹ ≤ V := (le_of_eq hF'eq).trans inf_le_right
  have hF'card : 4 ≤ Nat.card (conjSubgroup F y⁻¹) := by
    rw [E3.card_conjSubgroup]
    exact hF4
  have hCF'M : Subgroup.centralizer (conjSubgroup F y⁻¹ : Set G) ≤ D.M :=
    s1667_centralizer_le_of_four_le_card D hSg h61 h1217 hS hs h0 hF'V hF'card
  obtain ⟨c, hcM, hcV, hcord⟩ := s1667_exists_orderOf_three D hSg h1217 hS hs h0
  have hcF : c ∈ Subgroup.centralizer (F : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hFV) hcV
  have hcyM : c ∈ conjSubgroup D.M y := by
    have h1 : c ∈ conjSubgroup (Subgroup.centralizer (conjSubgroup F y⁻¹ : Set G)) y := by
      rw [E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj]
      exact hcF
    exact E3.conjSubgroup_mono_left y hCF'M h1
  have hzle : Subgroup.zpowers c ≤ D.M ⊓ conjSubgroup D.M y :=
    Subgroup.zpowers_le.mpr ⟨hcM, hcyM⟩
  have hdvd : 3 ∣ Nat.card (D.M ⊓ conjSubgroup D.M y : Subgroup G) := by
    rw [← hcord, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hzle
  have hsp := sixteen_sixtyEight_k D hSg h1219 V₀ V L hV hS hs
  have hyi : y⁻¹ ∉ D.M := fun h => hy (by simpa using D.M.inv_mem h)
  exact hsp.2.2 y⁻¹ hyi (by simpa only [conjSubgroup] using hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
