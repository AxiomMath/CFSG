module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4L2

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

theorem not_surv1_of_pRank_three {G : Type} [Group G] [Finite G] {H K M : Subgroup G} {t : G}
    (hKc : K ∈ cComp H) (htH : t ∈ H) (hJ : kerIn M H = pCoreOf 2 H)
    (hne : cjSub t K ≠ K) (hsimp : IsSimpleGroup ↥(E2.star M H K))
    (hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card ↥(E2.star M H K))
    (hrank : CFSG.Open.pRank 3 H ≤ 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ2 : IsPGroup 2 ((kerIn M H).subgroupOf H) := by
    rw [hJ]
    exact isPGroup_pCoreOf_two H
  have hNX : kerIn M H ≤ H := by
    rw [hJ]
    exact Subgroup.map_subtype_le _
  have hJsolv : Group.IsSolvable ↥(kerIn M H) := by
    have hnil : Group.IsNilpotent ↥(pCoreOf 2 H) := by
      have hp : IsPGroup 2 ↥(pCoreOf 2 H) := by
        intro g
        obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨x, hx⟩
        refine ⟨k, Subtype.ext ?_⟩
        have hk' : x ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxg, ← map_pow, hk', map_one]
      exact hp.isNilpotent
    rw [hJ]
    exact inferInstance
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hbij := cComp_quotient_bijOn_of_le hNX (by infer_instance) hJsolv
  have hKt : cjSub t K ∈ cComp H := conjSub_mem_cComp_of_mem hKc htH
  have hinj : E2.star M H (cjSub t K) ≠ E2.star M H K := fun h => hne (hbij.injOn hKt hKc h)
  set A : Subgroup (E2.StarQuot M H) := E2.star M H K with hAdef
  set tbar : E2.StarQuot M H := QuotientGroup.mk' ((kerIn M H).subgroupOf H) ⟨t, htH⟩ with htbar
  set c : E2.StarQuot M H →* E2.StarQuot M H := (MulAut.conj tbar).toMonoidHom with hcdef
  have hc_inj : Function.Injective c := (MulAut.conj tbar).injective
  have hA : A ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) := hbij.mapsTo hKc
  have hB : E2.star M H (cjSub t K) = A.map c := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyG : ((y : H) : G) ∈ cjSub t K := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyG
      have hkH : k ∈ H := hKH hk
      have hy_eq : y = (⟨t, htH⟩ : H) * ⟨k, hkH⟩ * (⟨t, htH⟩ : H)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hky]
        rfl
      refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' _ ⟨k, hkH⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      · show tbar * QuotientGroup.mk' _ ⟨k, hkH⟩ * tbar⁻¹ = _
        rw [hy_eq, map_mul, map_mul, map_inv]
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨kH, hkH, rfl⟩ := Subgroup.mem_map.mp ha
      refine Subgroup.mem_map.mpr ⟨(⟨t, htH⟩ : H) * kH * (⟨t, htH⟩ : H)⁻¹, ?_, ?_⟩
      · apply Subgroup.mem_subgroupOf.mpr
        refine Subgroup.mem_map.mpr ⟨(kH : G), Subgroup.mem_subgroupOf.mp hkH, ?_⟩
        show t * (kH : G) * t⁻¹ = _
        simp [mul_assoc]
      · show QuotientGroup.mk' _ (⟨t, htH⟩ * kH * (⟨t, htH⟩ : H)⁻¹) = tbar * _ * tbar⁻¹
        rw [map_mul, map_mul, map_inv]
  have hBA : A ≠ A.map c := fun h => hinj (hB.trans h.symm)
  have hAsimp : IsSimpleGroup ↥A := hsimp
  have hAnc : ¬ IsMulCommutative ↥A := by
    intro hc
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (isMulCommutative_iff.mp hc a b)
  have hcen : Subgroup.center ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with h | h
    · exact h
    · exfalso
      apply hAnc
      refine isMulCommutative_iff.mpr fun a b => ?_
      have ha : a ∈ Subgroup.center ↥A := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have eA : ↥A ≃* ↥(A.map c) := Subgroup.equivMapOfInjective A c hc_inj
  have hBsimp : IsSimpleGroup ↥(A.map c) := eA.isSimpleGroup_congr.mp hAsimp
  have hBnc : ¬ IsMulCommutative ↥(A.map c) := fun hc => hAnc (by
    refine isMulCommutative_iff.mpr fun a b => ?_
    apply eA.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hc (eA a) (eA b))
  have hAq : CFSG.Open.IsQuasisimple ↥A := isQuasisimple_of_simple_nonabelian _ hAnc
  have hBq : CFSG.Open.IsQuasisimple ↥(A.map c) := isQuasisimple_of_simple_nonabelian _ hBnc
  have hBcC : A.map c ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) := by
    rw [← hB]
    exact hbij.mapsTo hKt
  have hAcomp : IsComponentOf A (⊤ : Subgroup (E2.StarQuot M H)) :=
    ⟨le_top, subnormal_of_mem_cComp hA, hAq⟩
  have hBcomp : IsComponentOf (A.map c) (⊤ : Subgroup (E2.StarQuot M H)) :=
    ⟨le_top, subnormal_of_mem_cComp hBcC, hBq⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A.map c, a * b = b * a := by
    have h1 := CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hAcomp
      (subnormal_of_mem_cComp hBcC)
    have h2 := CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hBcomp
      (subnormal_of_mem_cComp hA)
    intro a ha b hb
    have key : ⁅A, A.map c⁆ = ⊥ → a * b = b * a := fun h => by
      have hab : ⁅a, b⁆ ∈ ⁅A, A.map c⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
      exact hab
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (le_antisymm h1 h2) hBA
      · exact key (by rw [Subgroup.commutator_comm]; exact h2)
    · exact key h1
  have hinter : ∀ g ∈ A, g ∈ A.map c → g = 1 := by
    intro g hgA hgB
    have hcenter : (⟨g, hgA⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro a'
      apply Subtype.ext
      exact hcomm a' a'.2 g hgB
    rw [hcen] at hcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcenter)
  have h3A : 3 ∣ Nat.card ↥A := h3
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 3 h3A
  have hub_mem : (u : E2.StarQuot M H) ∈ A := u.2
  have hub_ord : orderOf (u : E2.StarQuot M H) = 3 := by
    rw [Subgroup.orderOf_coe, hu]
  have hyb_mem : c (u : E2.StarQuot M H) ∈ A.map c := Subgroup.mem_map_of_mem c hub_mem
  have hyb_ord : orderOf (c (u : E2.StarQuot M H)) = 3 := by
    rw [orderOf_injective c hc_inj, hub_ord]
  have hcomm' : (u : E2.StarQuot M H) * c (u : E2.StarQuot M H) =
      c (u : E2.StarQuot M H) * (u : E2.StarQuot M H) :=
    hcomm _ hub_mem _ hyb_mem
  have hind : ∀ i j : ℕ, (u : E2.StarQuot M H) ^ i * (c (u : E2.StarQuot M H)) ^ j = 1 →
      3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    have hA_i : (u : E2.StarQuot M H) ^ i ∈ A := A.pow_mem hub_mem i
    have hB_j : (c (u : E2.StarQuot M H)) ^ j ∈ A.map c := (A.map c).pow_mem hyb_mem j
    have h1 : (u : E2.StarQuot M H) ^ i = 1 := by
      apply hinter _ hA_i
      have e : (u : E2.StarQuot M H) ^ i = ((c (u : E2.StarQuot M H)) ^ j)⁻¹ :=
        eq_inv_of_mul_eq_one_left hij
      rw [e]
      exact (A.map c).inv_mem hB_j
    have h2 : (c (u : E2.StarQuot M H)) ^ j = 1 := by
      apply hinter _ _ hB_j
      have e : (c (u : E2.StarQuot M H)) ^ j = ((u : E2.StarQuot M H) ^ i)⁻¹ :=
        eq_inv_of_mul_eq_one_right hij
      rw [e]
      exact A.inv_mem (A.pow_mem hub_mem i)
    constructor
    · have h := orderOf_dvd_of_pow_eq_one h1
      rwa [hub_ord] at h
    · have h := orderOf_dvd_of_pow_eq_one h2
      rwa [hyb_ord] at h
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_elemAb9_of_commuting _ _ hub_ord hyb_ord hcomm' hind
  set Y : Subgroup H := (kerIn M H).subgroupOf H with hYdef
  set P : Subgroup H := E₀.comap (QuotientGroup.mk' Y) with hPdef
  have hYP : Y ≤ P := by
    intro y hy
    show QuotientGroup.mk' Y y ∈ E₀
    have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff (y : H)).mpr hy
    rw [h1]
    exact E₀.one_mem
  have hcomm_P : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Y := by
    intro p hp q hq
    have hpE : QuotientGroup.mk' Y p ∈ E₀ := hp
    have hqE : QuotientGroup.mk' Y q ∈ E₀ := hq
    have hc' : QuotientGroup.mk' Y p * QuotientGroup.mk' Y q =
        QuotientGroup.mk' Y q * QuotientGroup.mk' Y p :=
      congrArg Subtype.val (isMulCommutative_iff.mp hE₀.1 ⟨_, hpE⟩ ⟨_, hqE⟩)
    have h1 : QuotientGroup.mk' Y (p * q * p⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc']
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcube_P : ∀ p ∈ P, p ^ 3 ∈ Y := by
    intro p hp
    have hpE : QuotientGroup.mk' Y p ∈ E₀ := hp
    have h1 : QuotientGroup.mk' Y (p ^ 3) = 1 := by
      rw [map_pow, hE₀.2 _ hpE]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcard_P : Nat.card P = 9 * Nat.card Y := by
    rw [hPdef, card_comap_mk' Y E₀, hE₀9]
  obtain ⟨F, -, hF, hF9⟩ := exists_elemAb9_of_two_kernel P Y hJ2 hYP hcomm_P hcube_P hcard_P
  have hFH : F.map H.subtype ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF' : IsElemAbelian 3 (F.map H.subtype) := isElemAbelian_map 3 H.subtype hF
  have hF'9 : Nat.card (F.map H.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hF9]
  have h2 := two_le_pRank_three_of_elemAb9 hFH hF' hF'9
  omega

end CFSG.Quasithin.H13.L829N
