module

public import CFSG.Walter.W67.W1Prop24B
public import CFSG.Walter.W67.CentralExt
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Walter.SimpleCaseStronglyEmbedded
import CFSG.Walter.PSL2Facts.Even
import CFSG.Walter.Bender1970.S2.AutEven
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem mem_involutionCore_of_sq_eq_one {X : Type*} [Group X] {x : X} (hx : x ^ 2 = 1) :
    x ∈ involutionCore X := by
  by_cases h1 : x = 1
  · rw [h1]; exact one_mem _
  · exact Subgroup.subset_closure (show x ∈ involutionsSet X from ⟨h1, hx⟩)

theorem isMulCommutative_of_isCyclic_map {X X' : Type*} [Group X] [Group X'] (f : X →* X')
    (P : Subgroup X) (hker : ∀ z ∈ P, f z = 1 → ∀ y ∈ P, z * y = y * z)
    [IsCyclic (P.map f)] : IsMulCommutative P := by
  set φ := f.comp P.subtype
  have hR : φ.range = P.map f := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have : IsCyclic φ.range := by rw [hR]; infer_instance
  have hk : φ.rangeRestrict.ker ≤ Subgroup.center P := by
    intro z hz
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hker z z.2 hz y y.2).symm
  exact φ.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hk

theorem isCyclic_of_isPGroup_of_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ R : Sylow p X, IsCyclic (R : Subgroup X)) {H : Subgroup X} (hH : IsPGroup p H) :
    IsCyclic H := by
  obtain ⟨R, hR⟩ := hH.exists_le_sylow
  have := hcyc R
  exact Subgroup.isCyclic_of_le hR

theorem isMulCommutative_map {X X' : Type*} [Group X] [Group X'] (f : X →* X') (P : Subgroup X)
    [hP : IsMulCommutative P] : IsMulCommutative (P.map f) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
  apply Subtype.ext
  have := congrArg Subtype.val (hP.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  simp only [Subgroup.coe_mul] at this ⊢
  rw [← map_mul, ← map_mul, this]

theorem isSimpleBenderGroup_psl2_eight : IsSimpleBenderGroup PSL(2, GaloisField 2 3) :=
  IsSimpleBenderGroup.isPSL2 ⟨3, by norm_num, ⟨MulEquiv.refl _⟩⟩

theorem pPrimeCore_eq_bot_of_quotient_psl2_eight {X : Type*} [Group X] [Finite X]
    (hgen : involutionCore X = ⊤) (hc : CFSG.pPrimeCore 2 X ≤ Subgroup.center X)
    (e : X ⧸ CFSG.pPrimeCore 2 X ≃* PSL(2, GaloisField 2 3)) :
    CFSG.pPrimeCore 2 X = ⊥ ∧ commutator X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := CFSG.pPrimeCore 2 X
  have hZo : Odd (Nat.card Z) := odd_card_pPrimeCore X
  set π := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hB : IsSimpleBenderGroup (X ⧸ Z) := isSimpleBenderGroup_psl2_eight.map_mulEquiv e.symm
  have : IsSimpleGroup (X ⧸ Z) := hB.isSimple
  have hperf : commutator (X ⧸ Z) = ⊤ := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup (X ⧸ Z)) ⊤).eq_bot_or_eq_top with h1 | h1
    · exfalso
      apply hB.not_commutative
      intro x y
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      exact (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top y)) x (Subgroup.mem_top x))
    · rw [commutator_def]; exact h1
  have hZD : Z ⊓ commutator X = ⊥ := by
    refine inf_commutator_eq_bot hc fun p hp hpZ => ?_
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q⟩ : Nonempty (Sylow p X) := inferInstance
    refine ⟨this, Q, ?_⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hZo) (even_iff_two_dvd.mpr hpZ)
    have hcyc : ∀ R : Sylow p PSL(2, GaloisField 2 3),
        IsCyclic (R : Subgroup PSL(2, GaloisField 2 3)) := by
      have hK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
      intro R
      refine GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField 2 3)
        (p := 2) (f := 3) hK (by rw [hK]; norm_num) p hp2 ?_ R
      rw [hK]
      exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hQe : IsCyclic ((Q : Subgroup X).map π) := by
      have h1 : IsPGroup p (((Q : Subgroup X).map π).map e.toMonoidHom) :=
        (Q.isPGroup'.map π).map _
      have h2 := isCyclic_of_isPGroup_of_sylow hcyc h1
      exact (MulEquiv.isCyclic (((Q : Subgroup X).map π).equivMapOfInjective _
        e.injective)).mpr h2
    refine isMulCommutative_of_isCyclic_map π Q (fun z _ hz y _ => ?_)
    have hzZ : z ∈ Z := (QuotientGroup.eq_one_iff z).mp hz
    exact (Subgroup.mem_center_iff.mp (hc hzZ) y).symm
  have hsup : commutator X ⊔ Z = ⊤ := by
    have h1 : (commutator X).map π = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, ←
        commutator_def, hperf]
    have h2 := Subgroup.comap_map_eq π (commutator X)
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  have hinv : involutionCore X ≤ commutator X := by
    rw [involutionCore, Subgroup.closure_le]
    intro x hx
    have hx2 : x ^ 2 = 1 := hx.2
    have hZN : Z ≤ Subgroup.normalizer (commutator X : Set X) := by
      rw [Subgroup.normalizer_eq_top]; exact le_top
    obtain ⟨d, hd, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hZN).mp
      (hsup ▸ Subgroup.mem_top x)
    have hzc : ∀ y : X, y * z = z * y := Subgroup.mem_center_iff.mp (hc hz)
    have hz2 : z ^ 2 = 1 := by
      have h1 : d ^ 2 * z ^ 2 = 1 := by
        rw [← hx2, (show Commute d z from hzc d).mul_pow]
      have hmem : z ^ 2 ∈ Z ⊓ commutator X := by
        refine ⟨pow_mem hz 2, ?_⟩
        rw [eq_inv_of_mul_eq_one_right h1]
        exact (commutator X).inv_mem ((commutator X).pow_mem hd 2)
      rw [hZD] at hmem
      exact hmem
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have h2 : Odd (orderOf z) := Odd.of_dvd_nat hZo (Subgroup.orderOf_dvd_natCard Z hz)
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at h2; exact absurd h2 (by decide)
    rw [SetLike.mem_coe, hz1, mul_one]
    exact hd
  have htop : commutator X = ⊤ := top_le_iff.mp (hgen ▸ hinv)
  refine ⟨?_, htop⟩
  rw [← inf_top_eq (a := Z), ← htop, hZD]

theorem center_eq_bot_of_psl2_eight {X : Type*} [Group X] [Finite X]
    (e : X ≃* PSL(2, GaloisField 2 3)) : Subgroup.center X = ⊥ := by
  have hB := isSimpleBenderGroup_psl2_eight.map_mulEquiv e.symm
  have : IsSimpleGroup X := hB.isSimple
  rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    apply hB.not_commutative
    intro x y
    exact (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y) x)

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem S_le_involutionCore : (fr.S : Subgroup G) ≤ involutionCore G := fun _ hx =>
  mem_involutionCore_of_sq_eq_one (by rw [pow_two]; exact fr.mul_self_of_mem_S hx)

section Three

variable (hq : h.q = 3) (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
include hq hidx

theorem isStronglyEmbedded_normalizer
    (hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ≠ ⊤) :
    CFSG.BenderSuzuki.IsStronglyEmbedded
      (Subgroup.normalizer ((fr.S : Subgroup G) : Set G)) := by
  refine ⟨hN, ⟨h.J, Subgroup.le_normalizer fr.J_mem, h.J_ne_one,
    by rw [pow_two]; exact h.J_mul_J⟩, ?_⟩
  intro g hg x hxM hxg hx
  simp only [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxg
  obtain ⟨m, hm, hmx⟩ := hxg
  have hxS := fr.mem_S_of_sq_eq_one hxM hx.2
  have hgx : g * x * g⁻¹ = m := by
    rw [← hmx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hm2 : m ^ 2 = 1 := by rw [← hgx, conj_pow, hx.2, mul_one, mul_inv_cancel]
  have hmS := fr.mem_S_of_sq_eq_one hm hm2
  exact hg (fr.mem_normalizer_S_of_conj_mem hq hidx hxS hx.1 (hgx ▸ hmS))

include fr in
theorem involutionCore_le_centralizer_of_three :
    involutionCore G ≤ Subgroup.centralizer (CFSG.pPrimeCore 2 G : Set G) := by
  rw [involutionCore, Subgroup.closure_le]
  intro u hu
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.2 hu.1
  obtain ⟨g, hg⟩ := fr.exists_conj_eq_J hidx hu2
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro o ho
  have h1 : g * o * g⁻¹ ∈ fr.CS :=
    fr.pPrimeCore_le_CS_of_three hq hidx (CFSG.pPrimeCore_normal.conj_mem o ho g)
  have h2 := Subgroup.mem_centralizer_iff.mp h1 h.J fr.J_mem
  rw [← hg] at h2
  have h3 : g * (u * o) * g⁻¹ = g * (o * u) * g⁻¹ := by
    calc g * (u * o) * g⁻¹ = g * u * g⁻¹ * (g * o * g⁻¹) := by group
      _ = g * o * g⁻¹ * (g * u * g⁻¹) := h2
      _ = g * (o * u) * g⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h3)).symm

theorem nonempty_quotient_iso
    (hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ≠ ⊤) :
    Nonempty (involutionCore G ⧸ twoPrimeCore (involutionCore G) ≃*
      PSL(2, GaloisField 2 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := involutionCore G
  set OY := twoPrimeCore Y
  have hSY := fr.S_le_involutionCore
  have hSE : TheoremSEConclusion (Subgroup.normalizer ((fr.S : Subgroup G) : Set G)) :=
    theorem_SE _ (fr.isStronglyEmbedded_normalizer hq hidx hN)
  have hrank : TwoRankAtLeastTwo Y := by
    refine ⟨fr.T.subgroupOf Y, ?_, fun x => ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fr.T_le_S.trans hSY)).toEquiv]
      exact fr.card_T
    · apply Subtype.ext
      apply Subtype.ext
      have hx : ((x : Y) : G) ∈ fr.T := x.2
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_two]
      exact JT.mul_self_of_isKleinFour fr.isKleinFour_T hx
  have hB : TheoremSEBenderConclusion (Subgroup.normalizer ((fr.S : Subgroup G) : Set G)) :=
    (hSE : ¬ TwoRankAtLeastTwo Y ∨ _).resolve_left (not_not.mpr hrank)
  obtain ⟨hBender, -, -⟩ := hB
  set π := QuotientGroup.mk' OY
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective OY
  have hOY : Odd (Nat.card OY) := odd_card_pPrimeCore Y
  have hsylY := h.sylow_of_subgroup ⟨fr.S, hSY⟩
  have hab : HasAbelianSylowTwo (Y ⧸ OY) := by
    intro P
    obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 P
    have := (hsylY Q).1
    rw [Sylow.coe_mapSurjective]
    exact isMulCommutative_map π _
  have h8 : ∀ P : Sylow 2 (Y ⧸ OY), Nat.card (P : Subgroup (Y ⧸ OY)) = 8 := by
    intro P
    obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 P
    rw [Sylow.coe_mapSurjective]
    have h1 := card_eq_card_map_mul_card_inf_ker π (Q : Subgroup Y)
    rw [QuotientGroup.ker_mk'] at h1
    have h2 : (Q : Subgroup Y) ⊓ OY = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact eq_one_of_odd_of_isPGroup Q.isPGroup' hx.1
        (Odd.of_dvd_nat hOY (Subgroup.orderOf_dvd_natCard _ hx.2))
    rw [h2, Subgroup.card_bot, mul_one, (hsylY Q).2] at h1
    exact h1.symm
  rcases CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup hBender with
    ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨P⟩ : Nonempty (Sylow 2 (Y ⧸ OY)) := inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 n)) := inferInstance
    have hU := (psl2_even_sylow_two hn U).2
    have hP := h8 P
    rw [Sylow.card_eq_multiplicity] at hU hP
    rw [Nat.card_congr e.toEquiv, hU] at hP
    have hn3 : n = 3 := Nat.pow_right_injective (le_refl 2) (hP.trans (by norm_num))
    subst hn3
    exact ⟨e⟩
  · exfalso
    have : Finite (CFSG.Open.PSU3 2 f) := Finite.of_surjective e e.surjective
    have hB' := (CFSG.Open.bender_psu3_borel_full f hf).map_mulEquiv e.symm
    refine not_hasAbelianSylowTwo_of_fusionBenderBorel hB' ?_ (by norm_num) hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    have : Finite (CFSG.Open.Sz a) := Finite.of_surjective e e.surjective
    have hB' := (CFSG.Open.bender_suzuki_borel_full a ha).map_mulEquiv e.symm
    refine not_hasAbelianSylowTwo_of_fusionBenderBorel hB' ?_ le_rfl hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_yData_of_not_normal
    (hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ≠ ⊤) :
    fr.E ≤ CFSG.pPrimeCore 2 G ∧ Nat.card G = 1512 * Nat.card (CFSG.pPrimeCore 2 G) ∧
      ∃ Y : Subgroup G, fr.YData Y ∧ Nat.card Y = 504 ∧ commutator Y = ⊤ ∧
        Nonempty (Y ≃* PSL(2, GaloisField 2 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 G
  have hO : Odd (Nat.card O) := odd_card_pPrimeCore G
  set S : Subgroup G := (fr.S : Subgroup G)
  set Y := involutionCore G
  have hYn : Y.Normal := inferInstance
  have hSY : S ≤ Y := fr.S_le_involutionCore
  have hYC : Y ≤ Subgroup.centralizer (O : Set G) :=
    fr.involutionCore_le_centralizer_of_three hq hidx
  set OY := twoPrimeCore Y
  have hOYc : OY ≤ Subgroup.center Y := by
    have : OY.Characteristic := CFSG.pPrimeCore_characteristic
    have hn : (OY.map Y.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hle : OY.map Y.subtype ≤ O :=
      le_sSup ⟨hn, by
        rw [Subgroup.card_map_of_injective Y.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card⟩
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hzO : (z : G) ∈ O := hle ⟨z, hz, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hYC y.2) z hzO).symm
  obtain ⟨e⟩ := fr.nonempty_quotient_iso hq hidx hN
  obtain ⟨hOY, hperf⟩ := pPrimeCore_eq_bot_of_quotient_psl2_eight
    (involutionCore_involutionCore_eq_top G) hOYc e
  let eY : Y ≃* PSL(2, GaloisField 2 3) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOY.symm)).trans e
  have hYcard : Nat.card Y = 504 := by
    rw [Nat.card_congr eY.toEquiv, psl2_even_card (by norm_num)]
    norm_num
  have hYO : Y ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxY, hxO⟩
    have hWn : (O.subgroupOf Y).Normal := Subgroup.Normal.subgroupOf CFSG.pPrimeCore_normal Y
    have hW : O.subgroupOf Y ≤ OY := le_sSup ⟨hWn, by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        CFSG.pPrimeCore_coprime_card⟩
    have := hW (show (⟨x, hxY⟩ : Y) ∈ O.subgroupOf Y from hxO)
    have hOY' : OY = ⊥ := hOY
    rw [hOY', Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  set SY := S.subgroupOf Y
  have hSYcard : Nat.card SY = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, fr.card_S]
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 3)) := inferInstance
  have hU₀ := (psl2_even_sylow_two (by norm_num : 2 ≤ 3) U₀).2
  rw [Sylow.card_eq_multiplicity] at hU₀
  let U : Sylow 2 PSL(2, GaloisField 2 3) := Sylow.ofCard (SY.map eY.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective eY.injective, hSYcard, hU₀]
    norm_num)
  have hUeq : (U : Subgroup PSL(2, GaloisField 2 3)) = SY.map eY.toMonoidHom := rfl
  have hYN : Nat.card (Y ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) = 56 := by
    have hNU := psl2_even_card_normalizer_sylow_two (f := 3) (by norm_num) U
    rw [hUeq, ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective eY.injective,
      ← Subgroup.subgroupOf_normalizer_eq hSY, ← Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.subgroupOf_map_subtype] at hNU
    rw [inf_comm, hNU]
    norm_num
  have hEC : fr.E ≤ Subgroup.centralizer (Y : Set G) := by
    intro x hx
    set ψ := MulAut.congr eY (MulAut.conjNormal x : MulAut Y)
    have hodd : Odd (orderOf ψ) := by
      have h1 : orderOf ψ ∣ orderOf x :=
        orderOf_map_dvd ((MulAut.congr eY).toMonoidHom.comp (MulAut.conjNormal (H := Y))) x
      exact Odd.of_dvd_nat (odd_orderOf_of_mem_oddPart hx) h1
    have hfix : ∀ u ∈ (U : Subgroup PSL(2, GaloisField 2 3)), ψ u = u := by
      intro u hu
      rw [hUeq] at hu
      obtain ⟨s, hs, rfl⟩ := hu
      simp only [ψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hc := Subgroup.mem_centralizer_iff.mp (fr.E_le_CS hx) (s : G) hs
      rw [← hc, mul_inv_cancel_right]
    have hψ := psl2_even_mulAut_eq_one (by norm_num : 2 ≤ 3) ψ hodd U hfix
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut PSL(2, GaloisField 2 3) => φ (eY ⟨y, hy⟩)) hψ
    simp only [ψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (eY.injective h1)
    rw [MulAut.conjNormal_apply] at h2
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group
  have hCO : Subgroup.centralizer (Y : Set G) ≤ O := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Nat.coprime_two_left]
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have huY : (u : G) ∈ Y :=
      mem_involutionCore_of_sq_eq_one (by rw [← hu']; exact pow_orderOf_eq_one _)
    have hcen : (⟨u, huY⟩ : Y) ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp u.2 y y.2)
    rw [center_eq_bot_of_psl2_eight eY, Subgroup.mem_bot] at hcen
    have : (u : G) = 1 := congrArg Subtype.val hcen
    rw [this, orderOf_one] at hu'
    omega
  have hEO : fr.E ≤ O := hEC.trans hCO
  have hEeq : fr.E = O := le_antisymm hEO (fr.pPrimeCore_le_E_of_three hq hidx)
  have hCS : Nat.card fr.CS = 8 * Nat.card O := by
    obtain ⟨hsup, hdisj, hcomm⟩ := fr.isInternalDirectProduct_CS.1
    have hc : ∀ x ∈ S, ∀ y ∈ fr.E, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hcomm hx) y hy).symm
    obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
    rw [hsup, hdisj.eq_bot, Subgroup.card_bot, mul_one, fr.card_S, hEeq] at h1
    exact h1
  have hNcard : Nat.card (Subgroup.normalizer (S : Set G)) = 168 * Nat.card O := by
    have h2 := Subgroup.relIndex_mul_card (H := fr.CS) (K := Subgroup.normalizer (S : Set G))
    have h21 : fr.CS.relIndex (Subgroup.normalizer (S : Set G)) = 21 :=
      fr.index_CS_normalizer_S hidx
    rw [inf_eq_left.mpr (Subgroup.centralizer_le_normalizer _), h21, hCS] at h2
    rw [← h2]
    ring
  have hG : Nat.card G = 1512 * Nat.card O := by
    have hfr : Subgroup.normalizer (S : Set G) ⊔ Y = ⊤ := Sylow.normalizer_sup_eq_top' fr.S hSY
    have h1 := card_sup_mul_card_inf_of_normal Y (Subgroup.normalizer (S : Set G))
    rw [sup_comm, hfr, Subgroup.card_top, hYN, hYcard, hNcard] at h1
    omega
  refine ⟨hEO, hG, Y, ⟨hYn, hYO, hYC, hSY, ?_⟩, hYcard, hperf, ⟨eY⟩⟩
  rw [hYN]
  norm_num

end Three

end Frame

end CFSG.Walter.W67
