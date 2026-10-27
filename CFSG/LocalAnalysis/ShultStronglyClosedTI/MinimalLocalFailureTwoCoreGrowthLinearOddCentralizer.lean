module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearPartition
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

universe u

theorem even_field_binary_size {K : Type u} [Field K] [Finite K]
    (hK : Even (Nat.card K)) (hKge : 4 ≤ Nat.card K) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f := by
  let : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr
    (by simpa only [Nat.card_eq_fintype_card] using Nat.even_iff.mp hK)
  let : CharP K 2 := ringChar.of_eq hchar
  obtain ⟨f, _, hf⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (f : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hf
  refine ⟨f, ?_, hcard⟩
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
  simpa only [hcard, show (2 : ℕ) ^ 2 = 4 by norm_num] using hKge

theorem psl2_even_odd_element_full_centralizer
    {K : Type u} [Field K] [Finite K]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (x : PSL2MatrixGroup K) (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    IsCyclic (Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K))) ∧
      (Nat.card (Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K))) =
          Nat.card K - 1 ∨
        Nat.card (Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K))) =
          Nat.card K + 1) ∧
      ∀ a : PSL2MatrixGroup K, a * x * a⁻¹ = x⁻¹ →
        ∀ y : PSL2MatrixGroup K,
          y ∈ Subgroup.centralizer ({x} : Set (PSL2MatrixGroup K)) →
            a * y * a⁻¹ = y⁻¹ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (PSL2MatrixGroup K) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpart⟩ :=
    huppert_II_8_5_a_psl2_cover (p := 2) (f := f) hcard P
  have hKge : 4 ≤ Nat.card K := by
    rw [hcard]
    exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  have hKeven : Even (Nat.card K) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (by omega)
  have hminusodd : Odd (Nat.card K - 1) :=
    Nat.Even.sub_odd (by omega) hKeven odd_one
  have hplusodd : Odd (Nat.card K + 1) := hKeven.add_odd odd_one
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 :=
    hminusodd.coprime_two_right.gcd_eq_one
  rw [hgcd, Nat.div_one] at hUcard hScard
  have hUS : Nat.Coprime (Nat.card U) (Nat.card S) := by
    have h := hsplit_nonsplit_order_coprime (Nat.card K) (by omega)
    simpa only [hgcd, Nat.div_one, hUcard, hScard] using h
  have hcover : ∀ y : PSL2MatrixGroup K, y ≠ 1 →
      ∃ V : Subgroup (PSL2MatrixGroup K), y ∈ V ∧
        ((∃ g, V = (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = S.map (MulAut.conj g).toMonoidHom)) := by
    intro y hy
    exact (hpart y hy).exists
  obtain ⟨U0, wU, hU0cyclic, hU0card, hwUN, _hwUne, hwUsq,
    hwUinv, _hUjoincard, hU0N⟩ :=
      huppert_II_8_3_split_torus_reflection_data (p := 2) (f := f) hcard
  obtain ⟨S0, wS, hS0cyclic, hS0card, hwSN, _hwSne, hwSsq,
    hwSinv, _hSjoincard, hS0N⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (p := 2) (f := f) hcard
  rw [hgcd, Nat.div_one] at hU0card hS0card
  let : IsCyclic U0 := hU0cyclic
  let : IsCyclic S0 := hS0cyclic
  obtain ⟨gU, hgU⟩ := reference_torus_matches_partition
    (P : Subgroup (PSL2MatrixGroup K)) U S U0 P.isPGroup'
    (hU0card.trans hUcard.symm) (hUcard.symm ▸ hminusodd)
    (by rw [hUcard]; omega) hUS hcover
  have hreverse : ∀ y : PSL2MatrixGroup K, y ≠ 1 →
      ∃ V : Subgroup (PSL2MatrixGroup K), y ∈ V ∧
        ((∃ g, V = (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = S.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, V = U.map (MulAut.conj g).toMonoidHom)) := by
    intro y hy
    obtain ⟨V, hyV, hVP | hVU | hVS⟩ := hcover y hy
    · exact ⟨V, hyV, Or.inl hVP⟩
    · exact ⟨V, hyV, Or.inr (Or.inr hVU)⟩
    · exact ⟨V, hyV, Or.inr (Or.inl hVS)⟩
  obtain ⟨gS, hgS⟩ := reference_torus_matches_partition
    (P : Subgroup (PSL2MatrixGroup K)) S U S0 P.isPGroup'
    (hS0card.trans hScard.symm) (hScard.symm ▸ hplusodd)
    (by rw [hScard]; omega) hUS.symm hreverse
  obtain ⟨V, hxV, hVP | hVU | hVS⟩ := hcover x hx
  · obtain ⟨g, rfl⟩ := hVP
    have htwo := P.isPGroup'.map (MulAut.conj g).toMonoidHom
    let y : (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hxV⟩
    have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
    have hcop := htwo.orderOf_coprime hyodd.coprime_two_left y
    have hyone : y = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)
    exact False.elim (hx (congrArg Subtype.val hyone))
  · obtain ⟨g, rfl⟩ := hVU
    let eU : PSL2MatrixGroup K ≃* PSL2MatrixGroup K :=
      (MulAut.conj gU).symm.trans (MulAut.conj g)
    have hUmap : U0.map eU.toMonoidHom = U.map (MulAut.conj g).toMonoidHom := by
      have hU0back : U0.map (MulAut.conj gU).symm.toMonoidHom = U :=
        (Subgroup.map_symm_eq_iff_map_eq (K := U) (e := MulAut.conj gU)).mpr hgU.symm
      change U0.map ((MulAut.conj g).toMonoidHom.comp
        (MulAut.conj gU).symm.toMonoidHom) = _
      rw [← Subgroup.map_map, hU0back]
    have hxU0 : x ∈ U0.map eU.toMonoidHom := hUmap.symm ▸ hxV
    obtain ⟨hcyclic, hCcard, hwholeinv⟩ :=
      conjugate_reflection_torus_odd_centralizer U0 wU hwUN hwUsq hwUinv hU0N
        eU x hxU0 hx hxodd
    exact ⟨hcyclic, Or.inl (hCcard.trans hU0card), hwholeinv⟩
  · obtain ⟨g, rfl⟩ := hVS
    let eS : PSL2MatrixGroup K ≃* PSL2MatrixGroup K :=
      (MulAut.conj gS).symm.trans (MulAut.conj g)
    have hSmap : S0.map eS.toMonoidHom = S.map (MulAut.conj g).toMonoidHom := by
      have hS0back : S0.map (MulAut.conj gS).symm.toMonoidHom = S :=
        (Subgroup.map_symm_eq_iff_map_eq (K := S) (e := MulAut.conj gS)).mpr hgS.symm
      change S0.map ((MulAut.conj g).toMonoidHom.comp
        (MulAut.conj gS).symm.toMonoidHom) = _
      rw [← Subgroup.map_map, hS0back]
    have hxS0 : x ∈ S0.map eS.toMonoidHom := hSmap.symm ▸ hxV
    obtain ⟨hcyclic, hCcard, hwholeinv⟩ :=
      conjugate_reflection_torus_odd_centralizer S0 wS hwSN hwSsq hwSinv hS0N
        eS x hxS0 hx hxodd
    exact ⟨hcyclic, Or.inr (hCcard.trans hS0card), hwholeinv⟩

theorem linear_even_odd_element_centralizer
    (K : Type) [Field K] [Finite K]
    (hKeven : Even (Nat.card K)) (hKge : 4 ≤ Nat.card K)
    (x : CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K))
    (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    IsCyclic (Subgroup.centralizer ({x} :
      Set (CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K)))) ∧
      (Nat.card (Subgroup.centralizer ({x} :
          Set (CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K)))) = Nat.card K - 1 ∨
        Nat.card (Subgroup.centralizer ({x} :
          Set (CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K)))) = Nat.card K + 1) ∧
      ∀ a : CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K),
        orderOf a = 2 → a⁻¹ * x * a = x⁻¹ →
          ∀ y : CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K),
            y ∈ Subgroup.centralizer ({x} :
              Set (CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K))) →
                a⁻¹ * y * a = y⁻¹ := by
  obtain ⟨f, hf, hcard⟩ := even_field_binary_size hKeven hKge
  let e := CFSG.ShultStronglyClosedTI.glaSLQuotientEquivPSL (ι := Fin 2) (K := K)
  have hex : e x ≠ 1 := fun h => hx (e.map_eq_one_iff.mp h)
  have heodd : Odd (orderOf (e x)) :=
    (orderOf_injective e.toMonoidHom e.injective x).symm ▸ hxodd
  obtain ⟨hcyclic, hCcard, hwholeinv⟩ :=
    psl2_even_odd_element_full_centralizer f hf hcard (e x) hex heodd
  let c := elementCentralizerEquiv e x
  have hcardC := Nat.card_congr c.toEquiv
  refine ⟨c.isCyclic.mpr hcyclic, ?_, ?_⟩
  · rcases hCcard with hminus | hplus
    · exact Or.inl (hcardC.trans hminus)
    · exact Or.inr (hcardC.trans hplus)
  · intro a ha hax y hy
    have hai : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha
    have hax' : a * x * a⁻¹ = x⁻¹ := by simpa only [hai] using hax
    have heax : e a * e x * (e a)⁻¹ = (e x)⁻¹ := by
      simpa only [map_mul, map_inv] using congrArg e hax'
    have hey : e y ∈ Subgroup.centralizer ({e x} : Set (PSL2MatrixGroup K)) :=
      (c ⟨y, hy⟩).property
    have h := hwholeinv (e a) heax (e y) hey
    have hresult : a * y * a⁻¹ = y⁻¹ := e.injective
      (by simpa only [map_mul, map_inv] using h)
    simpa only [hai] using hresult

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
