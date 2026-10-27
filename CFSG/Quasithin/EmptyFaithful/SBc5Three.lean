module

public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.T1515eA
import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.EmptyFaithful.R3c2Kernel
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq map_oPrimeResidualOf_top)
open scoped commutatorElement

@[expose] def Input32ThreeComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L → Clause32Two T M V₁ L →
      L ∈ cComp (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G))

namespace SBc5

section A318

variable {G : Type} [Group G] [Finite G]

theorem eq_oPrimeResidualOf_of_a318 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H L : Subgroup G} (hH : SQTKGroup ↥H) (hL : L ∈ cComp H)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : 2 ≤ CFSG.Open.pRank 3 L)
    (hn2 : ¬ A318Case2 (starImage 3 (L.subgroupOf H)))
    (hn3 : ¬ A318Case3Group ↥(starImage 3 (L.subgroupOf H))) :
    L = oPrimeResidualOf 3 H := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr' : 1 < CFSG.Open.pRank 3 (L.subgroupOf H) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num), ← R3c.pRank_three_eq_pCore_quotient L]
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr'
  have hLmap : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3g, -⟩
  · rw [← map_oPrimeResidualOf_top, ← h1, hLmap]
  · exact absurd h2 hn2
  · exact absurd h3g hn3

end A318

section Alt8

theorem eq_alt8_of_perfect_normal {K : Subgroup (Equiv.Perm (Fin 8))} (hn : K.Normal)
    (hperf : commutator ↥K = ⊤) (hbot : K ≠ ⊥) : K = alternatingGroup (Fin 8) := by
  have hle : K ≤ alternatingGroup (Fin 8) := by
    intro k hk
    have hker := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Equiv.Perm (Fin 8) →* ℤˣ).comp K.subtype)
    have hmem : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by rw [hperf]; trivial
    have := hker hmem
    simpa [Equiv.Perm.mem_alternatingGroup] using this
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) := hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

omit [Finite G] in
theorem starL_equiv_alt8 (hLI : L ≤ I) (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple ↥(Star153 T I L))
    (e : ↥(Star153 T I I) ≃* Equiv.Perm (Fin 8)) :
    Nonempty (↥(Star153 T I L) ≃* ↥(alternatingGroup (Fin 8))) := by
  have hAB : Star153 T I L ≤ Star153 T I I := InternalSec.autOn_le_autOn_of_le hLI
  set N : Subgroup ↥(Star153 T I I) := (Star153 T I L).subgroupOf (Star153 T I I) with hN
  set K : Subgroup (Equiv.Perm (Fin 8)) := N.map e.toMonoidHom with hK
  let eAK : ↥(Star153 T I L) ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hAB).symm.trans (e.subgroupMap N)
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨e.symm g * n * (e.symm g)⁻¹, ?_, by simp⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := InternalSec.autOn_normal_of (U := UI153 T I) hIL _ (e.symm g).2 _ hn
    simpa using this
  have hqK : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eAK hq
  have hperf : commutator ↥K = ⊤ := hqK.1.commutator_eq_top
  have hbot : K ≠ ⊥ := by
    intro hb
    obtain ⟨-, -, a, b, hab⟩ := hqK
    have hs : Subsingleton ↥K := by rw [hb]; infer_instance
    have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim x y]⟩
    exact hab (Subsingleton.elim _ _)
  exact ⟨eAK.trans (MulEquiv.subgroupCongr (eq_alt8_of_perfect_normal hKn hperf hbot))⟩

noncomputable def alt8EquivStatedSL :
    ↥(alternatingGroup (Fin 8)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
  CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm.trans
      (specialLinearGroupEquivStatedSL 4 (ZMod 2)))

theorem isPSL_two_of_statedSL {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) : IsPSL n 2 1 X :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hn e

end Alt8

section Surj

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

theorem mem_centralizer_UI_of_mem_pPrimeCore {I₁ : Subgroup G} (hLI : L ≤ I) (hLI₁ : L ≤ I₁)
    (hS : A318Exclusion ↥(Star153 T I L)) {x : G} (hx : x ∈ L)
    (hxN : (⟨x, hLI₁ hx⟩ : ↥I₁) ∈ CFSG.pPrimeCore 3 ↥I₁) :
    x ∈ Subgroup.centralizer (UI153 T I : Set G) := by
  have := hS.simple
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, hψ, hψ1⟩ := R3c2.exists_starSurj T I L hLI
  let N₀ : Subgroup ↥L := (CFSG.pPrimeCore 3 ↥I₁).comap (Subgroup.inclusion hLI₁)
  have hN₀ : N₀.Normal := Subgroup.Normal.comap inferInstance _
  have hM₀ : (N₀.map ψ).Normal := hN₀.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map ψ) with hb | ht
  · have h1 : ψ ⟨x, hx⟩ ∈ N₀.map ψ := Subgroup.mem_map_of_mem ψ hxN
    rw [hb, Subgroup.mem_bot] at h1
    exact (hψ1 ⟨x, hx⟩).1 h1
  · exfalso
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Star153 T I L)) 3 hS.three_dvd_card
    have hzM : z ∈ N₀.map ψ := ht ▸ Subgroup.mem_top z
    obtain ⟨n, hn, rfl⟩ := hzM
    have hn' : Subgroup.inclusion hLI₁ n ∈ CFSG.pPrimeCore 3 ↥I₁ := hn
    have h1 : orderOf (ψ n) ∣ orderOf n := orderOf_map_dvd ψ n
    have h2 : orderOf n = orderOf (Subgroup.inclusion hLI₁ n) :=
      (orderOf_injective _ (Subgroup.inclusion_injective hLI₁) n).symm
    have h3 : orderOf (⟨Subgroup.inclusion hLI₁ n, hn'⟩ : ↥(CFSG.pPrimeCore 3 ↥I₁)) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 ↥I₁) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    have h4 : 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥I₁) := by
      rw [hz] at h1
      exact h1.trans (h2 ▸ h3)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card h4

theorem exists_starImage_surj {I₁ : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I) (hLI₁ : L ≤ I₁)
    (hS : A318Exclusion ↥(Star153 T I L)) :
    ∃ ρ : ↥(starImage 3 (L.subgroupOf I₁)) →* ↥(Star153 T I L),
      Function.Surjective ρ ∧ ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y := by
  obtain ⟨ψ, hψ, hψ1⟩ := R3c2.exists_starSurj T I L hLI
  let π₁ : ↥(L.subgroupOf I₁) →* ↥(starImage 3 (L.subgroupOf I₁)) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I₁)).subgroupMap (L.subgroupOf I₁)
  have hπ₁ : Function.Surjective π₁ := MonoidHom.subgroupMap_surjective _ _
  let φ : ↥(L.subgroupOf I₁) →* ↥(Star153 T I L) :=
    ψ.comp (Subgroup.subgroupOfEquivOfLe hLI₁).toMonoidHom
  have hφ : ∀ y : ↥(L.subgroupOf I₁), φ y = 1 ↔ ((y : ↥I₁) : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
    fun y => hψ1 ⟨((y : ↥I₁) : G), y.2⟩
  have hle : π₁.ker ≤ φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I₁)) (y : ↥I₁) = 1 := by
      have := congrArg Subtype.val hy
      simpa [π₁] using this
    have hyN : (y : ↥I₁) ∈ CFSG.pPrimeCore 3 ↥I₁ := (QuotientGroup.eq_one_iff _).1 h1
    exact (hφ y).2 (mem_centralizer_UI_of_mem_pPrimeCore hLI hLI₁ hS y.2 hyN)
  let ρ : ↥(starImage 3 (L.subgroupOf I₁)) →* ↥(Star153 T I L) :=
    (MonoidHom.liftOfSurjective π₁ hπ₁) ⟨φ, hle⟩
  have hρ : ∀ y, ρ (π₁ y) = φ y := fun y => by
    simp [ρ]
  refine ⟨ρ, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := hψ z
    exact ⟨π₁ ⟨⟨x, hLI₁ x.2⟩, x.2⟩, by rw [hρ]; rfl⟩
  · intro y hy h3
    obtain ⟨y', rfl⟩ := hπ₁ y
    rw [hρ] at hy
    have hC := (hφ y').1 hy
    have hxL : ((y' : ↥I₁) : G) ∈ L := y'.2
    have hdvd : orderOf (π₁ y') ∣ orderOf y' := orderOf_map_dvd π₁ y'
    have hord : orderOf y' = orderOf ((y' : ↥I₁) : G) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    have h3x : 3 ∣ orderOf ((y' : ↥I₁) : G) := by
      rw [← hord]
      exact h3.trans hdvd
    have hne : orderOf ((y' : ↥I₁) : G) ≠ 0 := (isOfFinOrder_of_finite _).orderOf_pos.ne'
    have hx3 : orderOf (((y' : ↥I₁) : G) ^ (orderOf ((y' : ↥I₁) : G) / 3)) = 3 :=
      orderOf_pow_orderOf_div hne h3x
    exact R3c2.orderOf_ne_three_of_mem_centralizer_UI hI hF
      (Subgroup.pow_mem I (hLI hxL) _) (Subgroup.pow_mem _ hC _) hx3

theorem not_case2_starImage {I₁ : Subgroup G} (hS : A318Exclusion ↥(Star153 T I L))
    (ρ : ↥(starImage 3 (L.subgroupOf I₁)) →* ↥(Star153 T I L)) (hρ : Function.Surjective ρ) :
    ¬ A318Case2 (starImage 3 (L.subgroupOf I₁)) := by
  rintro ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩
  subst hq
  exact hS.noImage _ s r k hrp hk1 hPSL hmod ρ hρ

theorem not_case3Group_starImage {I₁ : Subgroup G} (hS : A318Exclusion ↥(Star153 T I L))
    (ρ : ↥(starImage 3 (L.subgroupOf I₁)) →* ↥(Star153 T I L)) (hρ : Function.Surjective ρ)
    (hker : ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y) :
    ¬ A318Case3Group ↥(starImage 3 (L.subgroupOf I₁)) := by
  intro h3
  obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3
  have hzc : ρ z ∈ Subgroup.center ↥(Star153 T I L) :=
    Subgroup.map_center_le_center hρ ⟨z, hzcen, rfl⟩
  rw [hS.center_eq_bot, Subgroup.mem_bot] at hzc
  exact hker z hzc (by rw [hz])

end Surj

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input32Three_of_comp (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hcomp : Input32ThreeComp) : Input32Three := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1 h2
  have hLc₁ := hcomp G T Mc M V₁ V₂ Yp I L t c h1 h2
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hyp.decomp
  obtain ⟨hLcJ, -, -, -, hStarQ, hLQ⟩ := c25.conc
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLcJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  obtain ⟨e⟩ := c.c31
  obtain ⟨eA⟩ := starL_equiv_alt8 hLI hIL hStarQ e
  have : Finite ↥(Star153 T I L) := Finite.of_equiv _ eA.symm.toEquiv
  have hPSL : IsPSL 4 2 1 ↥(Star153 T I L) :=
    isPSL_two_of_statedSL (by norm_num) (eA.trans alt8EquivStatedSL)
  have hS : A318Exclusion ↥(Star153 T I L) := hK.l42 _ hPSL
  have hr : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [R3c2.pRank_three_eq_star c25.ctx.inH c25.facts hLI]
    exact hS.rank
  have hLI₁ : L ≤ Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzL : z ∈ ZS153 T M V₁ ⊓ Subgroup.centralizer (L : Set G) := h2.1 ▸ hz
    exact (Subgroup.mem_centralizer_iff.mp hzL.2 l hl).symm
  have hZ₁V : ZS153 T M V₁ ⊓ V₁ ≤ VZ T M := inf_le_right.trans Dc.le₁
  have hZ₁I₁ : (ZS153 T M V₁ ⊓ V₁ : Subgroup G) ≤
      Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      B2F.isElemAbelian_comm hh.elemAbelian (hZ₁V hy) (hZ₁V hx)
  have hZ₁2 : IsPGroup 2 ↥(ZS153 T M V₁ ⊓ V₁) :=
    (B2F.isPGroup_of_isElemAbelian hh.elemAbelian).to_le hZ₁V
  have hZ₁N : Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hZ₁pc : ZS153 T M V₁ ⊓ V₁ ≤
      pCoreOf 2 (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hZ₁I₁ hZ₁N hZ₁2
  have hZ₁ne : ZS153 T M V₁ ⊓ V₁ ≠ ⊥ := by
    intro hb
    have := h2.2
    rw [hb, Subgroup.card_bot] at this
    omega
  have hO2 : pCoreOf 2 (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) ≠ ⊥ :=
    fun hb => hZ₁ne (le_bot_iff.mp (hb ▸ hZ₁pc))
  have hSQ : SQTKGroup ↥(Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hh.qtfe.qtke hh.qtfe.simple hh.qtfe.nonabelian hO2
  obtain ⟨ρ, hρ, hker⟩ := exists_starImage_surj (I₁ := Subgroup.centralizer
    ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G)) c25.ctx.inH c25.facts hLI hLI₁ hS
  exact eq_oPrimeResidualOf_of_a318 hF318 h36 h38 hSQ hLc₁ hLQ hr
    (not_case2_starImage hS ρ hρ) (not_case3Group_starImage hS ρ hρ hker)

end Main

end SBc5

end CFSG.Quasithin
