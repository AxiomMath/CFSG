module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.EmptyFaithful.S151CLY
public import CFSG.Quasithin.EmptyFaithful.S151CLPhi
public import CFSG.Quasithin.EmptyFaithful.S151ZI
public import CFSG.Quasithin.EmptyFaithful.ModBAlt6
public import CFSG.Quasithin.EmptyFaithful.S152VL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sq_mem_inner_of_alt_six {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 6))
    (x : MulAut S) : x ^ 2 ∈ inner S := by
  let f : S ≃* Unc25A6.X0 := e.trans Setup.X3Aut.psiEquiv.symm
  apply Unc25Small.mem_innerAut_of_congr f
  rw [map_pow]
  exact Unc25A6.sq_inner _

theorem odd_order_aut_eq_one_of_sq_inner {Γ : Type} [Group Γ]
    (hZ : ∀ c : Γ, (∀ y, c * y = y * c) → c = 1)
    (hsq : ∀ α : MulAut Γ, α ^ 2 ∈ (MulAut.conj : Γ →* MulAut Γ).range) (l : Γ)
    (hP : ∀ g : Γ, g * l = l * g → Odd (orderOf g) → g = 1) (α : MulAut Γ)
    (hα : Odd (orderOf α)) (hc : α * MulAut.conj l = MulAut.conj l * α) : α = 1 := by
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    apply hZ
    intro y
    have h := MulEquiv.ext_iff.1 hc1 y
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y * c := by rw [h]
  have hαN : α ∈ (MulAut.conj : Γ →* MulAut Γ).range := by
    obtain ⟨m, hm⟩ := hα
    have h3 : α = (α ^ 2) ^ (m + 1) := by
      have h4 : α ^ (2 * m + 2) = α := by
        have := pow_orderOf_eq_one α
        rw [hm] at this
        calc α ^ (2 * m + 2) = α ^ (2 * m + 1) * α := pow_succ _ _
          _ = α := by rw [this, one_mul]
      rw [← pow_mul, show 2 * (m + 1) = 2 * m + 2 by ring, h4]
    rw [h3]
    exact (MulAut.conj : Γ →* MulAut Γ).range.pow_mem (hsq α) _
  obtain ⟨g, rfl⟩ := hαN
  have hgl : g * l = l * g := by
    apply hinj
    rw [map_mul, map_mul]
    exact hc
  have hordg : orderOf g = orderOf (MulAut.conj g) := (orderOf_injective _ hinj g).symm
  rw [hP g hgl (hordg ▸ hα)]
  exact map_one _

section Centralize

variable {G : Type} [Group G]

theorem odd_centralizes_of_inner_involution_of_sq_inner {L : Subgroup G} {z l k : G}
    (hZ : Subgroup.center ↥L = ⊥)
    (hsq : ∀ α : MulAut ↥L, α ^ 2 ∈ (MulAut.conj : ↥L →* MulAut ↥L).range)
    (hl : l ∈ L) (hll : l * l = 1)
    (hP : ∀ g : ↥L, g * ⟨l, hl⟩ = ⟨l, hl⟩ * g → Odd (orderOf g) → g = 1)
    (hlz : ∀ x ∈ L, z⁻¹ * x * z = l * x * l) (hkN : k ∈ Subgroup.normalizer (L : Set G))
    (hkz : k * z = z * k) (hodd : Odd (orderOf k)) : ∀ x ∈ L, k * x = x * k := by
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  let lL : ↥L := ⟨l, hl⟩
  have hZ' : ∀ c : ↥L, (∀ y, c * y = y * c) → c = 1 := by
    intro c hc
    have hmem : c ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hc g).symm
    rw [hZ] at hmem
    exact Subgroup.mem_bot.1 hmem
  let kN : ↥(Subgroup.normalizer (L : Set G)) := ⟨k, hkN⟩
  let α : MulAut ↥L := L.normalizerMonoidHom kN
  have hα_apply : ∀ x : ↥L, ((α x : ↥L) : G) = k * (x : G) * k⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L kN x
  have hαodd : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf kN := orderOf_map_dvd L.normalizerMonoidHom kN
    have h2 : orderOf kN = orderOf k := Subgroup.orderOf_mk k hkN
    exact Odd.of_dvd_nat (h2 ▸ hodd) h1
  have hkzC : Commute k z := hkz
  have hzkC : Commute z k := hkz.symm
  have hc : α * MulAut.conj lL = MulAut.conj lL * α := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hxL : (x : G) ∈ L := x.2
    have hkxL : k * (x : G) * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hkN _).1 hxL
    have lhs : (((α * MulAut.conj lL) x : ↥L) : G) = k * (l * (x : G) * l⁻¹) * k⁻¹ := by
      rw [MulAut.mul_apply, hα_apply]
      simp [MulAut.conj_apply, lL]
    have rhs : (((MulAut.conj lL * α) x : ↥L) : G) = l * (k * (x : G) * k⁻¹) * l⁻¹ := by
      rw [MulAut.mul_apply]
      simp [MulAut.conj_apply, hα_apply, lL]
    rw [lhs, rhs]
    have h1 : l * (x : G) * l⁻¹ = z⁻¹ * (x : G) * z := by rw [hlz _ hxL, hlinv]
    have h2 : l * (k * (x : G) * k⁻¹) * l⁻¹ = z⁻¹ * (k * (x : G) * k⁻¹) * z := by
      rw [hlz _ hkxL, hlinv]
    rw [h1, h2]
    have hc1 : k * z⁻¹ = z⁻¹ * k := (Commute.inv_right hkzC).eq
    have hc2 : z * k⁻¹ = k⁻¹ * z := (Commute.inv_right hzkC).eq
    calc k * (z⁻¹ * (x : G) * z) * k⁻¹ = (k * z⁻¹) * (x : G) * (z * k⁻¹) := by group
      _ = (z⁻¹ * k) * (x : G) * (k⁻¹ * z) := by rw [hc1, hc2]
      _ = z⁻¹ * (k * (x : G) * k⁻¹) * z := by group
  have hα1 : α = 1 := odd_order_aut_eq_one_of_sq_inner hZ' hsq lL hP α hαodd hc
  intro x hx
  have h1 : ((α ⟨x, hx⟩ : ↥L) : G) = ((⟨x, hx⟩ : ↥L) : G) := by rw [hα1]; rfl
  rw [hα_apply] at h1
  have h2 : k * x * k⁻¹ = x := h1
  calc k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [h2]

end Centralize

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem compListNoA6_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : CompListNoA6 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx hA6
  obtain ⟨e⟩ := hA6
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLin : IsComponentIn L (g1_1516 Z₁) := DoubleA3.isComponentIn_iff_open.mpr hcomp
  have hLcomp : L ∈ cComp (g1_1516 Z₁) := Id2519.mem_cComp_of_isComponentIn hLin
  obtain ⟨hcard, hcent8⟩ := Unc25K1.card_centralizer_eight_of_A6 e
  have hsimple : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr e).mpr
    (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnp : ¬ IsPGroup 2 ↥L := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h
    rw [hcard] at hk
    rcases Nat.lt_or_ge k 9 with h9 | h9
    · interval_cases k <;> norm_num at hk
    · have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h9
      omega
  have hpc : CFSG.pCore 2 ↥L = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥L) with h | h
    · exact h
    · exfalso
      apply hnp
      have h2 := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
      rw [h] at h2
      exact IsPGroup.of_equiv h2 Subgroup.topEquiv
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hLcomp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLcomp)).mp hn)
    · exact absurd h2 (a6NotA38Type_holds G L
        ⟨e.toMonoidHom, e.surjective, by
          rw [hpc]; exact (MonoidHom.ker_eq_bot_iff _).2 e.injective⟩)
  have hOut : ∀ α : MulAut ↥L, α ^ 2 ∈ inner ↥L := fun α => sq_mem_inner_of_alt_six e α
  have hnab : ∃ a ∈ s1516 T Z₁, ∃ b ∈ s1516 T Z₁, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
    let SS : Sylow 2 ↥L := A4.toSylow hSyl
    have hsurj : Function.Surjective e.toMonoidHom := e.surjective
    refine ModB.alt6_sylow_not_comm (Sylow.mapSurjective hsurj SS) ?_
    intro a ha b hb
    rw [Sylow.coe_mapSurjective] at ha hb
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    have hs' : (s : G) ∈ s1516 T Z₁ := (Subgroup.mem_subgroupOf.mp hs).1
    have ht' : (t : G) ∈ s1516 T Z₁ := (Subgroup.mem_subgroupOf.mp ht).1
    have hst : s * t = t * s := Subtype.ext (hcon _ hs' _ ht')
    show e.toMonoidHom s * e.toMonoidHom t = e.toMonoidHom t * e.toMonoidHom s
    rw [← map_mul, ← map_mul, hst]
  obtain ⟨z, hzZ, hz1, l₀, hl₀, hinl⟩ := exists_inner_central_element hc hx.s_normal hSN hOut hnab
  have hyp := hc.h18.six z hzZ hz1
  obtain ⟨-, hcomm, -, -⟩ := hyp.component_action hLin
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    rw [alternatingGroup.center_eq_bot (by simp)] at hex
    exact Subgroup.mem_bot.2 (e.injective (by simpa using Subgroup.mem_bot.1 hex))
  have hL1 : L ≠ ⊥ := by
    intro hL
    rw [hL, Subgroup.card_bot] at hcard
    omega
  obtain ⟨l, hl, hl1, hll, hlz⟩ := S152V.inner_involution_data hZ
    (sq_eq_one_of_mem_omegaOneCenter T hzZ) hcomm hL1 ⟨l₀, hl₀, hinl⟩
  let lL : ↥L := ⟨l, hl⟩
  have hP : ∀ g : ↥L, g * lL = lL * g → Odd (orderOf g) → g = 1 := by
    intro g hg hodd
    have hlL2 : lL * lL = 1 := Subtype.ext hll
    have hlL1 : lL ≠ 1 := fun h => hl1 (congrArg Subtype.val h)
    have hcard8 := hcent8 lL hlL2 hlL1
    have hgC : g ∈ Subgroup.centralizer ({lL} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hg.symm
    have hdvd : orderOf g ∣ 8 := by
      have h1 := orderOf_dvd_natCard (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({lL} : Set ↥L)))
      rw [hcard8] at h1
      rwa [Subgroup.orderOf_mk] at h1
    obtain ⟨k, hk, hk8⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf g ∣ 2 ^ 3 by
      simpa using hdvd)
    have hk0 : k = 0 := by
      by_contra hk0
      obtain ⟨m, hm⟩ := hodd
      rw [hk8] at hm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [pow_succ] at hm
      omega
    rw [hk0, pow_zero] at hk8
    exact orderOf_eq_one_iff.1 hk8
  have hY1G : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      g1_1516 Z₁ := hc.h18.one.2.trans (mZ1516_le_g1 Mc Z₁)
  have hYC : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (L : Set G) := by
    refine (Subgroup.closure_le _).mpr fun k hk => ?_
    have hkY := mem_oTwoUpper_of_odd hk.1 hk.2
    have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
      oTwoUpper_le_normalizer_component h37 h38 hc hcomp hY1G
        (mem_oTwoUpper_of_odd hkY (by simpa using hk.2))
    have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hk.1 z hzZ).symm
    have hcommk := odd_centralizes_of_inner_involution_of_sq_inner hZ
      (fun α => sq_mem_inner_of_alt_six e α) hl hll hP hlz hkN hkz hk.2
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcommk x hx).symm
  have hLMc : L ≤ Mc := le_mc_of_le_centralizer_oTwoUpper hq
    (Subgroup.le_centralizer_iff.mp hYC)
  exact hc.hL.not_le fun x hx => ⟨hc.hL.mem.1 hx, hLMc hx⟩

end CFSG.Quasithin
