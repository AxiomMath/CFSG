module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairGen
public import CFSG.LocalAnalysis.WeakClosure81.SuzukiGen
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.SignalizerFunctorTheorem.CatalogBridge
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSz)

private theorem w183fin_odd_orderOf_mul_of_odd_inf {G : Type*} [Group G] [Finite G]
    {M₁ M₂ : Subgroup G} {a b : G} (hodd : Odd (Nat.card ↥(M₁ ⊓ M₂)))
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha : Subgroup.centralizer ({a} : Set G) ≤ M₁)
    (hb : Subgroup.centralizer ({b} : Set G) ≤ M₂) :
    Odd (orderOf (a * b)) := by
  by_contra hodd'
  rw [Nat.not_odd_iff_even] at hodd'
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hodd'
  have hnpos : 0 < orderOf (a * b) := orderOf_pos _
  have hkpos : 0 < k := by omega
  let z : G := (a * b) ^ k
  have hz2 : z * z = 1 := by
    dsimp only [z]
    rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have hdvd : orderOf (a * b) ∣ k := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hz
    have hle : orderOf (a * b) ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hconj : ∀ c : G, c * c = 1 → c * (a * b) * c⁻¹ = (a * b)⁻¹ → c * z * c⁻¹ = z := by
    intro c hc hcab
    calc c * z * c⁻¹ = (c * (a * b) * c⁻¹) ^ k := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
      _ = ((a * b)⁻¹) ^ k := by rw [hcab]
      _ = z⁻¹ := by rw [inv_pow]
      _ = z := inv_eq_of_mul_eq_one_right hz2
  have haz : a * z * a⁻¹ = z := by
    refine hconj a ha2 ?_
    rw [mul_inv_rev, ha', hb']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha2, one_mul]
  have hbz : b * z * b⁻¹ = z := by
    refine hconj b hb2 ?_
    rw [mul_inv_rev, ha', hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb2, mul_one]
  have hzCa : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp haz).symm
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hbz).symm
  have hmem : z ∈ M₁ ⊓ M₂ := Subgroup.mem_inf.mpr ⟨ha hzCa, hb hzCb⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have h2dvd : 2 ∣ Nat.card ↥(M₁ ⊓ M₂) := by
    have := orderOf_dvd_natCard (⟨z, hmem⟩ : ↥(M₁ ⊓ M₂))
    rwa [Subgroup.orderOf_mk, hzord] at this
  exact absurd (hodd.of_dvd_nat h2dvd) (by decide)

variable {Q : Type} [Group Q] [Finite Q]

private theorem w183fin_sz8_sup_eq_top
    (e : Q ≃* Sz 1) {P P' : Sylow 2 Q} (hne : P ≠ P')
    {E F : Subgroup Q} (hE : E ≤ sylowCenter (P : Subgroup Q))
    (hF : F ≤ sylowCenter (P' : Subgroup Q)) (hE4 : 4 ≤ Nat.card E) (hF4 : 4 ≤ Nat.card F) :
    E ⊔ F = ⊤ := by
  have ha : 1 ≤ 1 := le_rfl
  have hB : fusionBenderBorel Q (2 ^ (2 * 1 + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha e
  set Y : Subgroup Q := E ⊔ F with hY
  have hZP2 : ∀ z ∈ E, z ^ 2 = 1 := by
    intro z hz; exact (benderBorel_sylowCenter hB P).2.1 z (hE hz)
  have hZP'2 : ∀ z ∈ F, z ^ 2 = 1 := by
    intro z hz; exact (benderBorel_sylowCenter hB P').2.1 z (hF hz)
  have hZPcomm : IsMulCommutative E := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxc : (x : Q) ∈ sylowCenter (P : Subgroup Q) := hE x.2
    have hyc : (y : Q) ∈ sylowCenter (P : Subgroup Q) := hE y.2
    exact Subtype.ext
      ((mem_sylowCenter.mp hxc).2 (y : Q) (mem_sylowCenter.mp hyc).1).symm
  have hZP'comm : IsMulCommutative F := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxc : (x : Q) ∈ sylowCenter (P' : Subgroup Q) := hF x.2
    have hyc : (y : Q) ∈ sylowCenter (P' : Subgroup Q) := hF y.2
    exact Subtype.ext
      ((mem_sylowCenter.mp hxc).2 (y : Q) (mem_sylowCenter.mp hyc).1).symm
  have hZPel : IsElemAbelian 2 E := ⟨hZPcomm, hZP2⟩
  have hZP'el : IsElemAbelian 2 F := ⟨hZP'comm, hZP'2⟩
  have hZPY : E ≤ Y := by rw [hY]; exact le_sup_left
  have hZP'Y : F ≤ Y := by rw [hY]; exact le_sup_right
  obtain ⟨kE, hkE⟩ := IsPGroup.iff_card.mp hZPel.isPGroup
  have hkE2 : 2 ≤ kE := by
    by_contra hlt
    have : 2 ^ kE ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set Zsub : Subgroup ↥Y := E.subgroupOf Y with hZsub
  have hZsubel : IsElemAbelian 2 Zsub := by rw [hZsub]; exact hZPel.subgroupOf Y
  have hZsubcard : Nat.card Zsub = 2 ^ kE := by
    have h : Nat.card Zsub = Nat.card E := by
      rw [hZsub]
      have hmap := Subgroup.card_map_of_injective (K := E.subgroupOf Y) Y.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZPY] at hmap
      exact hmap.symm
    rw [h, hkE]
  set N₀ : Subgroup Q := Subgroup.normalizer ((P : Subgroup Q) : Set Q) with hN₀
  have hSE : fusionStronglyEmbedded N₀ := by rw [hN₀]; exact (hB P).1
  have hnotY : ¬ Y ≤ N₀ := by
    intro hYN
    have hZP'leN : F ≤ N₀ := hZP'Y.trans hYN
    have hZP'leP : F ≤ (P : Subgroup Q) := by
      have hnorm : F ≤ Subgroup.normalizer (P : Subgroup Q) := by
        rw [← hN₀]; exact hZP'leN
      have hsup : IsPGroup 2 ↥(F ⊔ (P : Subgroup Q)) :=
        IsPGroup.to_sup_of_normal_right' hZP'el.isPGroup (P : Sylow 2 Q).isPGroup' hnorm
      calc F ≤ F ⊔ (P : Subgroup Q) := le_sup_left
        _ = (P : Subgroup Q) := (P : Sylow 2 Q).is_maximal' hsup le_sup_right
    have hFbot : F = ⊥ := by
      have hle : F ≤ (P : Subgroup Q) ⊓ (P' : Subgroup Q) :=
        le_inf hZP'leP ((hF.trans (sylowCenter_le _)))
      rw [inf_eq_bot_of_fusionBenderBorel hB hne] at hle
      exact le_bot_iff.mp hle
    have h1 : Nat.card F = 1 := by rw [hFbot, Subgroup.card_bot]
    omega
  have hEven : Even (Nat.card ↥(N₀ ⊓ Y)) := by
    have hZPY' : E ≤ N₀ ⊓ Y := by
      refine le_inf ?_ hZPY
      rw [hN₀]
      exact (hE.trans (sylowCenter_le (P : Subgroup Q))).trans Subgroup.le_normalizer
    have hdvd : Nat.card E ∣ Nat.card ↥(N₀ ⊓ Y) := Subgroup.card_dvd_of_le hZPY'
    have h2 : 2 ∣ Nat.card E := by rw [hkE]; exact dvd_pow_self 2 (by omega)
    exact even_iff_two_dvd.mpr (h2.trans hdvd)
  have hSEY : fusionStronglyEmbedded (N₀.subgroupOf Y) :=
    stronglyEmbedded_subgroupOf hSE Y hnotY hEven
  rcases CFSG.Open.Open.bender_strongly_embedded ↥Y (N₀.subgroupOf Y) hSEY with
    hcyc | ⟨M, N, hMnorm, hNnorm, hMNnorm, hMN, hModd, hNodd, hBender⟩
  · exfalso
    obtain ⟨S, hZsubS⟩ := IsPGroup.exists_le_sylow hZsubel.isPGroup
    have hnt : Nontrivial Zsub := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZsubcard]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    obtain ⟨x, hx1⟩ := exists_ne (1 : Zsub)
    have hx2 : (x : ↥Y) ^ 2 = 1 := hZsubel.2 (x : ↥Y) x.2
    have hxord : orderOf (x : ↥Y) = 2 :=
      orderOf_eq_prime hx2 (fun h => hx1 (Subtype.ext h))
    let z : ↥S := ⟨(x : ↥Y), hZsubS x.2⟩
    have hzord : orderOf z = 2 :=
      (Subgroup.orderOf_mk (x : ↥Y) (hZsubS x.2)).trans hxord
    have huniq : ∀ y : ↥S, orderOf y = 2 → y = z :=
      fun y hy => eq_of_orderOf_eq_two_of_cyclic_or_quaternion (hcyc S) hy hzord
    have hrankS : twoRank ↥S ≤ 1 :=
      CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution z hzord huniq
    have hrank_ge : kE ≤ twoRank ↥S := by
      have hEcard : Nat.card (Zsub.subgroupOf (S : Subgroup ↥Y)) = 2 ^ kE := by
        have hmap := Subgroup.card_map_of_injective
          (K := Zsub.subgroupOf (S : Subgroup ↥Y)) (S : Subgroup ↥Y).subtype_injective
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZsubS] at hmap
        rw [hmap.symm, hZsubcard]
      exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary ↥S
        (Zsub.subgroupOf (S : Subgroup ↥Y)) (hZsubel.subgroupOf (S : Subgroup ↥Y))
        kE hEcard
    omega
  · have hZsubMbot : Zsub ⊓ M = ⊥ := by
      have hdiv : Nat.card ↥(Zsub ⊓ M) ∣ 2 ^ kE := by
        rw [← hZsubcard]; exact Subgroup.card_dvd_of_le inf_le_left
      have hodd : Odd (Nat.card ↥(Zsub ⊓ M)) :=
        hModd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
      have hcop : Nat.Coprime (Nat.card ↥(Zsub ⊓ M)) (2 ^ kE) :=
        hodd.coprime_two_right.pow_right _
      exact (Subgroup.eq_bot_iff_card (H := Zsub ⊓ M)).mpr
        (Nat.Coprime.eq_one_of_dvd hcop hdiv)
    have hZN : Zsub ≤ N := by
      intro z hz
      by_contra hzN
      have hpow : (QuotientGroup.mk' N z) ^ 2 ^ 1 = 1 := by
        rw [pow_one, ← map_pow, hZsubel.2 z hz, map_one]
      have hodd_top : Odd (Nat.card ↥(⊤ : Subgroup (↥Y ⧸ N))) := by
        rw [Subgroup.card_top, ← Subgroup.index_eq_card]; exact hNodd
      have h1 := eq_one_of_mem_odd_subgroup_of_pow_two_pow (N := (⊤ : Subgroup (↥Y ⧸ N)))
        hodd_top (c := QuotientGroup.mk' N z) trivial hpow
      exact hzN ((QuotientGroup.eq_one_iff z).mp h1)
    have hcardQ : Nat.card Q = Nat.card (Sz 1) := Nat.card_congr e.toEquiv
    have h3Q : ¬ 3 ∣ Nat.card Q := by
      rw [hcardQ]
      exact not_three_dvd_card_sz 1
    have hNMdvd : Nat.card (N ⧸ M.subgroupOf N) ∣ Nat.card Q :=
      (Subgroup.card_quotient_dvd_card (M.subgroupOf N)).trans
        ((Subgroup.card_subgroup_dvd_card N).trans (Subgroup.card_subgroup_dvd_card Y))
    have hBenderSz : ∃ b : ℕ, 1 ≤ b ∧ Nonempty ((N ⧸ M.subgroupOf N) ≃* Sz b) := by
      rcases hBender with ⟨f0, hf0, ⟨ePSL⟩⟩ | ⟨f0, hf0, ⟨ePSU⟩⟩ | ⟨b, hb, ⟨eSz⟩⟩
      · exfalso
        have h3 : 3 ∣ Nat.card (N ⧸ M.subgroupOf N) := by
          rw [Nat.card_congr ePSL.toEquiv]
          exact three_dvd_card_psl2_two_pow (by omega)
        exact h3Q (h3.trans hNMdvd)
      · exfalso
        have h3 : 3 ∣ Nat.card (N ⧸ M.subgroupOf N) := by
          rw [Nat.card_congr ePSU.toEquiv]
          exact three_dvd_card_psu3 (by omega)
        exact h3Q (h3.trans hNMdvd)
      · exact ⟨b, hb, ⟨eSz⟩⟩
    obtain ⟨b, hb, ⟨eSz⟩⟩ := hBenderSz
    have hab : 1 = b := by
      have hba : b ≤ 1 := by
        apply card_sz_le_imp_le
        have hNMleY : Nat.card (N ⧸ M.subgroupOf N) ≤ Nat.card ↥Y :=
          (Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_quotient_dvd_card (M.subgroupOf N))).trans
            (Subgroup.card_le_card_group (H := N))
        have hYleQ : Nat.card ↥Y ≤ Nat.card Q := Subgroup.card_le_card_group (H := Y)
        calc Nat.card (Sz b) = Nat.card (N ⧸ M.subgroupOf N) :=
              (Nat.card_congr eSz.toEquiv).symm
          _ ≤ Nat.card ↥Y := hNMleY
          _ ≤ Nat.card Q := hYleQ
          _ = Nat.card (Sz 1) := hcardQ
      omega
    have hcardN : Nat.card (N ⧸ M.subgroupOf N) = Nat.card Q := by
      have h1 : Nat.card (N ⧸ M.subgroupOf N) = Nat.card (Sz b) :=
        Nat.card_congr eSz.toEquiv
      have h2 : Nat.card (Sz b) = Nat.card (Sz 1) := by rw [← hab]
      exact h1.trans (h2.trans hcardQ.symm)
    have hYcard : Nat.card ↥Y = Nat.card Q := by
      apply le_antisymm (Subgroup.card_le_card_group (H := Y))
      calc Nat.card Q = Nat.card (N ⧸ M.subgroupOf N) := hcardN.symm
        _ ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_quotient_dvd_card (M.subgroupOf N))
        _ ≤ Nat.card ↥Y := Subgroup.card_le_card_group (H := N)
    exact Subgroup.eq_top_of_card_eq (H := Y) hYcard

private theorem w183fin_finPairGenSz8_gen :
    ∀ (Y : Type) [Group Y], IsSz Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    ∀ E F : Subgroup Y, E ≤ P₁ → F ≤ P₂ → 4 ≤ Nat.card E → 4 ≤ Nat.card F → E ⊔ F = ⊤ := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne E F hE hF hE4 hF4
  obtain ⟨a, ha, h3, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hY
  have ha1 : a = 1 := by omega
  subst ha1
  haveI : Finite Y := Finite.of_equiv (Sz 1) e.symm.toEquiv
  obtain ⟨P, hP⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e h₁
    (by rw [c₁]; norm_num)
  obtain ⟨P', hP'⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e h₂
    (by rw [c₂]; norm_num)
  have hPP' : P ≠ P' := by
    intro h
    exact hne (by rw [hP, hP', h])
  exact w183fin_sz8_sup_eq_top e hPP' (hE.trans hP.le) (hF.trans hP'.le) hE4 hF4

private theorem w183fin_finPairGenSz8_odd :
    ∀ (Y : Type) [Group Y], IsSz Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    ∀ a ∈ P₁, ∀ b ∈ P₂, a ≠ 1 → b ≠ 1 → Odd (orderOf (a * b)) := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne a ha b hb ha1 hb1
  obtain ⟨a', ha', h3, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hY
  have ha1' : a' = 1 := by omega
  subst ha1'
  haveI : Finite Y := Finite.of_equiv (Sz 1) e.symm.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha' e h₁
    (by rw [c₁]; norm_num)
  obtain ⟨P', hP'⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha' e h₂
    (by rw [c₂]; norm_num)
  have hPP' : P ≠ P' := by
    intro h
    exact hne (by rw [hP, hP', h])
  have hB : fusionBenderBorel Y (2 ^ (2 * 1 + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha' e
  have haP : a ∈ (P : Subgroup Y) := by
    have := ha
    rw [hP] at this
    exact this.1
  have hbP : b ∈ (P' : Subgroup Y) := by
    have := hb
    rw [hP'] at this
    exact this.1
  have ha2 : a * a = 1 := by
    have := h₁.2 a ha
    rwa [pow_two] at this
  have hb2 : b * b = 1 := by
    have := h₂.2 b hb
    rwa [pow_two] at this
  have haord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hbord : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hCa := centralizer_le_normalizer_of_stronglyEmbedded (hB P).1 haP haord
  have hCb := centralizer_le_normalizer_of_stronglyEmbedded (hB P').1 hbP hbord
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P P'
  have hgN : g ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y) := by
    intro hgN
    exact hPP' (by rw [← hg]; exact (Sylow.smul_eq_iff_mem_normalizer.mpr hgN).symm)
  have hN' : Subgroup.normalizer ((P' : Subgroup Y) : Set Y) =
      (Subgroup.normalizer ((P : Subgroup Y) : Set Y)).map (MulAut.conj g).toMonoidHom := by
    have hP'g : (P' : Subgroup Y) = (P : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    rw [hP'g]
    exact (Subgroup.map_equiv_normalizer_eq (P : Subgroup Y) (MulAut.conj g)).symm
  have hodd := (hB P).1.2.2 g⁻¹ (fun h => hgN (by simpa using h))
  rw [inv_inv, ← hN'] at hodd
  exact w183fin_odd_orderOf_mul_of_odd_inf hodd ha2 hb2 hCa hCb

theorem finPairGenSz8_holds :
    FinPairGenSz8 := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne
  exact ⟨w183fin_finPairGenSz8_gen Y hY P₁ P₂ h₁ h₂ c₁ c₂ hne,
    w183fin_finPairGenSz8_odd Y hY P₁ P₂ h₁ h₂ c₁ c₂ hne⟩

end CFSG.LocalAnalysis.WeakClosure81

end
