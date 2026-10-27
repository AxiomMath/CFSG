module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.OddTranspositions.PartThree.EightNine.Tools
public import CFSG.OddTranspositions.PartThree.EightEight.Triangles
public import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
public import CFSG.OddTranspositions.PartThree.EightSeven
public import CFSG.OddTranspositions.TheoremTwo.AalphaNonempty
public import CFSG.OddTranspositions.FiveThreeQZ
public import CFSG.OddTranspositions.PartThree.EightOne.Quotient
public import CFSG.OddTranspositions.SixTenPetersen
public import CFSG.OddTranspositions.PartFour.LineTransport
import CFSG.Mathlib.GroupTheory.MulConjMemNormal
public import CFSG.StronglyEmbedded.PSL2Facts

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}


namespace MainHyp

variable {hC : HypothesisC D}

private abbrev H (hC : HypothesisC D) : Subgroup G := Halpha D hC.alpha

private abbrev Q (hC : HypothesisC D) : Subgroup (H hC) := CFSG.pCore 2 (H hC)

private abbrev K (hC : HypothesisC D) : Subgroup (H hC) := EightOne.twoOddCore (H hC)

private def KOrbit (hC : HypothesisC D) (v : H hC) : Set (H hC) :=
  {x | ∃ k : H hC, k ∈ K hC ∧ x = k * v * k⁻¹}

private theorem normal_K (hC : HypothesisC D) : (K hC).Normal :=
  (CFSG.oddCore_normal (H hC ⧸ Q hC)).comap (QuotientGroup.mk' (Q hC))

private theorem mul_mem_K_of_mem_KOrbit (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) {s w : H hC} (hs : s ∈ KOrbit hC vH) (hw : w ∈ KOrbit hC vH) :
    s * w ∈ K hC := by
  have hK := normal_K hC
  obtain ⟨k₁, hk₁, rfl⟩ := hs
  obtain ⟨k₂, hk₂, rfl⟩ := hw
  have ha : vH * (k₁ * vH * k₁⁻¹) ∈ K hC :=
    CFSG.GroupTheory.mul_mul_conj_mem_of_normal (hN := hK) hk₁ hv2
  have hb : vH * (k₂ * vH * k₂⁻¹) ∈ K hC :=
    CFSG.GroupTheory.mul_mul_conj_mem_of_normal (hN := hK) hk₂ hv2
  have hs' : k₁ * vH * k₁⁻¹ = vH * (vH * (k₁ * vH * k₁⁻¹)) := by
    rw [← mul_assoc, hv2, one_mul]
  have hw' : k₂ * vH * k₂⁻¹ = vH * (vH * (k₂ * vH * k₂⁻¹)) := by
    rw [← mul_assoc, hv2, one_mul]
  rw [hs', hw']
  have hid : vH * (vH * (k₁ * vH * k₁⁻¹)) * (vH * (vH * (k₂ * vH * k₂⁻¹)))
      = (vH * (vH * (k₁ * vH * k₁⁻¹)) * vH⁻¹) * (vH * (k₂ * vH * k₂⁻¹)) := by
    rw [inv_eq_of_mul_eq_one_right hv2]; group
  rw [hid]
  exact Subgroup.mul_mem _ (hK.conj_mem _ ha vH) hb

private theorem mul_self_eq_one_of_mem_KOrbit (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) {s : H hC} (hs : s ∈ KOrbit hC vH) : s * s = 1 := by
  obtain ⟨k, -, rfl⟩ := hs
  calc (k * vH * k⁻¹) * (k * vH * k⁻¹) = k * (vH * vH) * k⁻¹ := by group
    _ = 1 := by rw [hv2, mul_one, mul_inv_cancel]

private theorem mul_mem_Q_of_mem_KOrbit (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) {s w : H hC} (hs : s ∈ KOrbit hC vH) (hw : w ∈ KOrbit hC vH)
    (hcomm : Commute s w) : s * w ∈ Q hC := by
  have hKmem : s * w ∈ K hC := mul_mem_K_of_mem_KOrbit hC hv2 hs hw
  have hss : s * s = 1 := mul_self_eq_one_of_mem_KOrbit hC hv2 hs
  have hww : w * w = 1 := mul_self_eq_one_of_mem_KOrbit hC hv2 hw
  have hsq : (s * w) * (s * w) = 1 := by
    calc (s * w) * (s * w) = s * (w * s) * w := by group
      _ = s * (s * w) * w := by rw [← hcomm.eq]
      _ = (s * s) * (w * w) := by group
      _ = 1 := by rw [hss, hww, mul_one]
  have hmemO : QuotientGroup.mk' (Q hC) (s * w) ∈ CFSG.oddCore (H hC ⧸ Q hC) :=
    Subgroup.mem_comap.mp hKmem
  have htwo : QuotientGroup.mk' (Q hC) (s * w) * QuotientGroup.mk' (Q hC) (s * w) = 1 := by
    rw [← map_mul]; exact congrArg _ hsq
  have hodd : Odd (orderOf (QuotientGroup.mk' (Q hC) (s * w))) :=
    Odd.of_dvd_nat (EightOne.odd_card_oddCore (X := H hC ⧸ Q hC))
      (Subgroup.orderOf_dvd_natCard _ hmemO)
  have h1 : QuotientGroup.mk' (Q hC) (s * w) = 1 := by
    have h2 : orderOf (QuotientGroup.mk' (Q hC) (s * w)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr ⟨1, by norm_num⟩) hodd
  exact (QuotientGroup.eq_one_iff (s * w)).mp h1

private theorem mul_not_mem_Q_of_mem_KOrbit (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) (hvD : (vH : G) ∈ D) {s : H hC} (hs : s ∈ KOrbit hC vH)
    (hns : ¬ Commute vH s) : vH * s ∉ Q hC := by
  intro hmem
  obtain ⟨k, hk, rfl⟩ := hs
  have hsD : ((k * vH * k⁻¹ : H hC) : G) ∈ D := hC.setup.normal (k : G) (vH : G) hvD
  have hnsG : ¬ Commute (vH : G) ((k * vH * k⁻¹ : H hC) : G) :=
    fun hc => hns (Subtype.ext hc.eq)
  have hoddG : Odd (orderOf ((vH : G) * ((k * vH * k⁻¹ : H hC) : G))) :=
    hC.setup.oddT.odd_of_not_commute hvD hsD hnsG
  have hoddH : Odd (orderOf (vH * (k * vH * k⁻¹))) := by
    rw [← Subgroup.orderOf_coe (vH * (k * vH * k⁻¹))]
    exact hoddG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ :=
    (CFSG.pCore_isPGroup (p := 2) (G := H hC)).exists_orderOf_eq_pow
      (⟨vH * (k * vH * k⁻¹), hmem⟩ : Q hC)
  have hn' : orderOf (vH * (k * vH * k⁻¹)) = 2 ^ n := by
    have h := hn
    rw [← Subgroup.orderOf_coe (⟨vH * (k * vH * k⁻¹), hmem⟩ : Q hC)] at h
    exact h
  have h1 : orderOf (vH * (k * vH * k⁻¹)) = 1 := by
    obtain ⟨m, hm⟩ := hoddH
    rcases n with _ | n
    · simpa using hn'
    · exfalso
      rw [hn'] at hm
      have heven : Even (2 ^ (n + 1)) := by
        rw [Nat.even_pow]
        exact ⟨even_two, by omega⟩
      exact (Nat.not_odd_iff_even.mpr heven) ⟨m, hm⟩
  have hs1 : vH * (k * vH * k⁻¹) = 1 := orderOf_eq_one_iff.mp h1
  apply hns
  have hseq : k * vH * k⁻¹ = vH := by
    have h := mul_eq_one_iff_eq_inv.mp hs1
    rw [mul_inv_rev, mul_inv_rev, inv_inv] at h
    rw [inv_eq_of_mul_eq_one_right hv2] at h
    simpa [mul_assoc] using h.symm
  rw [hseq]

private theorem commute_map_mk_of_commute_conj (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) {k : H hC} (hk : k ∈ K hC)
    (hc : Commute vH (k * vH * k⁻¹)) :
    Commute (QuotientGroup.mk' (Q hC) vH) (QuotientGroup.mk' (Q hC) k) := by
  have hvK : vH ∈ KOrbit hC vH := ⟨1, (K hC).one_mem, by rw [one_mul, inv_one, mul_one]⟩
  have hprod : vH * (k * vH * k⁻¹) ∈ Q hC :=
    mul_mem_Q_of_mem_KOrbit hC hv2 hvK ⟨k, hk, rfl⟩ hc
  have hq : QuotientGroup.mk' (Q hC) (vH * (k * vH * k⁻¹)) = 1 :=
    (QuotientGroup.eq_one_iff (vH * (k * vH * k⁻¹))).mpr hprod
  have hV2 : QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) vH = 1 := by
    rw [← map_mul]; exact congrArg _ hv2
  simp only [map_mul, map_inv] at hq
  have hVK : QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) k *
      QuotientGroup.mk' (Q hC) vH = QuotientGroup.mk' (Q hC) k := by
    have h := congrArg (· * QuotientGroup.mk' (Q hC) k) hq
    simp only [one_mul] at h
    convert h using 1 <;> group
  show QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) k =
    QuotientGroup.mk' (Q hC) k * QuotientGroup.mk' (Q hC) vH
  calc QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) k
      = (QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) k) *
          (QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) vH) := by
        rw [hV2, mul_one]
    _ = (QuotientGroup.mk' (Q hC) vH * QuotientGroup.mk' (Q hC) k *
          QuotientGroup.mk' (Q hC) vH) * QuotientGroup.mk' (Q hC) vH := by group
    _ = QuotientGroup.mk' (Q hC) k * QuotientGroup.mk' (Q hC) vH := by rw [hVK]

private theorem closure_image_DalphaStar_eq_top (hC : HypothesisC D) :
    Subgroup.closure ((fun x : H hC => QuotientGroup.mk' (Q hC) x) ''
      {x : H hC | (x : G) ∈ DalphaStar D hC.alpha}) = ⊤ := by
  have hS : Subgroup.closure {x : H hC | (x : G) ∈ DalphaStar D hC.alpha} = ⊤ := by
    have himg : (H hC).subtype '' {x : H hC | (x : G) ∈ DalphaStar D hC.alpha}
        = DalphaStar D hC.alpha := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy; exact ⟨⟨y, Subgroup.subset_closure hy⟩, hy, rfl⟩
    have hmap : Subgroup.map (H hC).subtype
        (Subgroup.closure {x : H hC | (x : G) ∈ DalphaStar D hC.alpha}) = H hC := by
      rw [MonoidHom.map_closure, himg]
      rfl
    have h := Subgroup.comap_map_eq_self_of_injective (f := (H hC).subtype)
      (fun x y hxy => Subtype.ext hxy)
      (Subgroup.closure {x : H hC | (x : G) ∈ DalphaStar D hC.alpha})
    rw [hmap] at h
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_self] at h
    exact h.symm
  rw [← MonoidHom.map_closure, hS]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (Q hC))

private theorem conj_mem_centralizer_oddCore (hC : HypothesisC D) {vH : H hC}
    (hv : (vH : G) ∈ DalphaStar D hC.alpha)
    (hcommK : ∀ k : H hC, k ∈ K hC →
      Commute (QuotientGroup.mk' (Q hC) vH) (QuotientGroup.mk' (Q hC) k))
    {x : H hC} (hx : (x : G) ∈ DalphaStar D hC.alpha) :
    QuotientGroup.mk' (Q hC) x ∈ Subgroup.centralizer
      (CFSG.oddCore (H hC ⧸ Q hC) : Set (H hC ⧸ Q hC)) := by
  have hmapKO : Subgroup.map (QuotientGroup.mk' (Q hC)) (K hC) =
      CFSG.oddCore (H hC ⧸ Q hC) := by
    rw [show K hC = (CFSG.oddCore (H hC ⧸ Q hC)).comap (QuotientGroup.mk' (Q hC)) from rfl]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (Q hC)) _
  have hVcent : QuotientGroup.mk' (Q hC) vH ∈
      Subgroup.centralizer (CFSG.oddCore (H hC ⧸ Q hC) : Set (H hC ⧸ Q hC)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (hmapKO.symm ▸ hn)
    exact (hcommK k hk).symm.eq
  obtain ⟨h, hh, hxeq⟩ := hC.Halpha_transitive (vH : G) hv (x : G) hx
  have hxH : (⟨h, hh⟩ : H hC) * vH * ⟨h, hh⟩⁻¹ = x := by
    apply Subtype.ext
    simpa using hxeq
  have hconj := (inferInstance :
    (Subgroup.centralizer (CFSG.oddCore (H hC ⧸ Q hC) : Set (H hC ⧸ Q hC))).Normal).conj_mem
    (QuotientGroup.mk' (Q hC) vH) hVcent (QuotientGroup.mk' (Q hC) ⟨h, hh⟩)
  rw [← hxH]
  simpa only [map_mul, map_inv] using hconj

private theorem exists_not_commute_conj (h : MainHyp hC) {v : G}
    (hv : v ∈ DalphaStar D hC.alpha) :
    ∃ k : H hC, k ∈ K hC ∧ ¬ Commute v ((k : G) * v * (k : G)⁻¹) := by
  by_contra hconj
  push Not at hconj
  have hvD : v ∈ D := DalphaStar_subset hC.isBlock_alpha hv
  have hvH : v ∈ H hC := Subgroup.subset_closure hv
  set vH : H hC := ⟨v, hvH⟩ with hvHdef
  have hv2 : vH * vH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hvD)
  have hcommK : ∀ k : H hC, k ∈ K hC →
      Commute (QuotientGroup.mk' (Q hC) vH) (QuotientGroup.mk' (Q hC) k) := by
    intro k hk
    exact commute_map_mk_of_commute_conj hC hv2 hk (Subtype.ext (hconj k hk).eq)
  have hgen := closure_image_DalphaStar_eq_top hC
  have hOtop : CFSG.oddCore (H hC ⧸ Q hC) ≤ Subgroup.center (H hC ⧸ Q hC) := by
    refine Subgroup.centralizer_eq_top_iff_subset.mp ?_
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).mpr
      (by rintro d ⟨x, hx, rfl⟩; exact conj_mem_centralizer_oddCore hC hv hcommK hx)
  exact h.not_central hOtop

private theorem mem_closure_of_not_commute (hC : HypothesisC D) {s w : G}
    (hs : s ∈ D) (hw : w ∈ D) (hns : ¬ Commute s w) :
    w ∈ Subgroup.closure ({s, w * s * w⁻¹} : Set G) := by
  have hodd : Odd (orderOf (s * w)) := hC.setup.oddT.odd_of_not_commute hs hw hns
  have hs2 : s * s = 1 := hC.setup.oddT.mul_self_eq_one hs
  have hw2 : w * w = 1 := hC.setup.oddT.mul_self_eq_one hw
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hsq : (s * w) ^ 2 = s * (w * s * w⁻¹) := by
    rw [pow_two, hw_inv]; group
  have hsq_mem : (s * w) ^ 2 ∈ Subgroup.closure ({s, w * s * w⁻¹} : Set G) := by
    rw [hsq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hs_mem : s ∈ Subgroup.closure ({s, w * s * w⁻¹} : Set G) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨m, hm⟩ := hodd
  have hpow : s * w = ((s * w) ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h2 : 2 * (m + 1) = orderOf (s * w) + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hsw_mem : s * w ∈ Subgroup.closure ({s, w * s * w⁻¹} : Set G) := by
    rw [hpow]
    exact Subgroup.pow_mem _ hsq_mem (m + 1)
  have hw_eq : w = s * (s * w) := by rw [← mul_assoc, hs2, one_mul]
  have := Subgroup.mul_mem (Subgroup.closure ({s, w * s * w⁻¹} : Set G)) hs_mem hsw_mem
  rwa [← hw_eq] at this

private theorem closure_union_ne_top (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) :
    Subgroup.closure (β ∪ DalphaStar D β) ≠ ⊤ := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have hXnorm : Subgroup.closure (β ∪ DalphaStar D β) ≤ Subgroup.normalizer β := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · exact mem_normalizer_of_mem_block hβblock hy
    · obtain ⟨γ, hγ, hyγ⟩ := hy
      have hcent : y ∈ Subgroup.centralizer (β : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact ((mem_Dalpha_iff.mp hγ).2.2.2 z hz y hyγ).eq
      exact Subgroup.centralizer_le_normalizer β hcent
  intro htop
  have hDβ : D ⊆ β := by
    intro d hd
    obtain ⟨v, hvβ⟩ := hβblock.nonempty
    obtain ⟨c, hc⟩ := isConj_iff.mp (hC.setup.isConj (hβ.2.1 hvβ) hd)
    have hall : (c : G) ∈ Subgroup.normalizer β := by
      rw [htop] at hXnorm
      exact hXnorm (Subgroup.mem_top (c : G))
    have himg : cimg (c : G) β = β :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hall
    have hmem : (c : G) * v * (c : G)⁻¹ ∈ β := by
      rw [← himg]
      exact ⟨v, hvβ, rfl⟩
    rwa [hc] at hmem
  exact hβblock.ne_univ (Set.Subset.antisymm hβ.2.1 hDβ)

private theorem closure_union_inter_D_subset_perp (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) :
    ((Subgroup.closure (β ∪ DalphaStar D β) : Subgroup G) : Set G) ∩ D ⊆
      β ∪ DalphaStar D β := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  set hC' : HypothesisC D := hC.conj g with hC'def
  set X : Subgroup G := Subgroup.closure (β ∪ DalphaStar D β) with hXdef
  have hXD : X = Subgroup.closure ((X : Set G) ∩ D) := by
    apply le_antisymm
    · rw [show X = Subgroup.closure (β ∪ DalphaStar D β) from rfl, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Or.inl hx), hβ.2.1 hx⟩
      · exact Subgroup.subset_closure
          ⟨Subgroup.subset_closure (Or.inr hx), DalphaStar_subset hβblock hx⟩
    · exact (Subgroup.closure_le _).mpr Set.inter_subset_left
  have hα' : hC'.alpha = β := by
    rw [HypothesisC.conj_alpha]
    exact hg.symm
  have hdX : hC'.d ∈ X := by
    have hdβ : hC'.d ∈ β := by
      rw [HypothesisC.conj_d, hg]
      exact ⟨hC.d, hC.d_mem_alpha, rfl⟩
    exact Subgroup.subset_closure (Or.inl hdβ)
  have hEeq : hC'.E = DalphaStar D β := by
    rw [show hC'.E = cimg g hC.E from rfl, ← hC.DalphaStar_alpha,
      ← DalphaStar_cimg hC.setup.normal g hC.alpha, hg]
  have hEX : hC'.E ⊆ (X : Set G) := by
    rw [hEeq]
    intro y hy
    exact Subgroup.subset_closure (Or.inr hy)
  have h := inter_D_subset_perp hC' hXD hdX hEX (closure_union_ne_top hC hβ)
  rwa [hα'] at h

private theorem mem_Dalpha_of_mem_Dalpha_of_mem_closure (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D β) {w : G}
    (hwX : w ∈ Subgroup.closure β) (hwγ : w ∈ γ)
    {δ : Set G} (hδ : δ ∈ Dalpha D β) (hδne : δ ≠ γ) : δ ∈ Dalpha D γ := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have hγα : γ ∈ blockClass hC.alpha := by
    rw [← blockClass_eq_of_mem hβ.1]; exact hγ.1
  have hδα : δ ∈ blockClass hC.alpha := by
    rw [← blockClass_eq_of_mem hβ.1]; exact hδ.1
  obtain ⟨y, hy⟩ := nonempty_of_mem_blockClass hβblock.nonempty hδ.1
  have hycomm : ∀ a ∈ β, Commute a y := fun a ha => (mem_Dalpha_iff.mp hδ).2.2.2 a ha y hy
  have hcent : w ∈ Subgroup.centralizer ({y} : Set G) := by
    have hle : Subgroup.closure β ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hycomm a ha).eq
    exact hle hwX
  have hwy : Commute w y := Subgroup.mem_centralizer_singleton_iff.mp hcent
  exact mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
    hγα hδα hδne.symm hwγ hy hwy

private theorem perp_subset_of_mem_Dalpha_of_mem_closure (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D β) {w : G}
    (hwX : w ∈ Subgroup.closure β) (hwγ : w ∈ γ) :
    perp D β ⊆ perp D γ := by
  have hβγ : β ∈ Dalpha D γ := Dalpha_symm hγ hβ.2.1
  intro δ hδ
  rcases mem_perp_iff.mp hδ with hδD | rfl
  · by_cases hδγ : δ = γ
    · rw [hδγ]; exact mem_perp_iff.mpr (Or.inr rfl)
    · exact mem_perp_iff.mpr (Or.inl
        (mem_Dalpha_of_mem_Dalpha_of_mem_closure hC hβ hγ hwX hwγ hδD hδγ))
  · exact mem_perp_iff.mpr (Or.inl hβγ)

private theorem mem_block_of_mem_closure_of_mem_Dalpha (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D β) {w : G} (hwD : w ∈ D)
    (hwX : w ∈ Subgroup.closure β) (hwγ : w ∈ γ) : w ∈ β := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have hsub := perp_subset_of_mem_Dalpha_of_mem_closure hC hβ hγ hwX hwγ
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hγ.1
  have hcard : (perp D γ).ncard ≤ (perp D β).ncard := by
    rw [hk, ncard_perp_conj hC.setup.normal]
  have hperpeq : perp D β = perp D γ :=
    Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hγV : γ ∈ Valpha D β := mem_Valpha_iff.mpr ⟨hγ.1, hperpeq.symm⟩
  have hmax : CFSG.Timmesfeld.Bridge.IsMaxBlock D β :=
    EightEight.isMaxBlock_of_mem_blockClass hC hβ.1
  have hproper : Valpha D β ≠ blockClass β := by
    intro hV
    obtain ⟨δ, hδ⟩ := Aalpha_nonempty hC.setup hβblock
    have hδV : δ ∈ Valpha D β := by rw [hV]; exact hδ.1
    have hδp : δ ∈ perp D β := by
      rw [← (mem_Valpha_iff.mp hδV).2]
      exact mem_perp_iff.mpr (Or.inr rfl)
    exact (mem_Aalpha_iff.mp hδ).2 hδp
  have hsingle : Valpha D β = {β} :=
    Valpha_eq_singleton_of_isMaxBlock_of_ne hC.setup.normal hmax hproper
  have hγeq : γ = β := by simpa [hsingle] using hγV
  exact hγeq ▸ hwγ

private theorem closure_inter_D_subset (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) :
    ((Subgroup.closure β : Subgroup G) : Set G) ∩ D ⊆ β := by
  have h68 := closure_union_inter_D_subset_perp hC hβ
  rintro w ⟨hwX, hwD⟩
  have hwX' : w ∈ (Subgroup.closure (β ∪ DalphaStar D β) : Subgroup G) :=
    Subgroup.closure_mono (Set.subset_union_left) hwX
  rcases h68 ⟨hwX', hwD⟩ with hwβ | hwStar
  · exact hwβ
  · obtain ⟨γ, hγ, hwγ⟩ := hwStar
    exact mem_block_of_mem_closure_of_mem_Dalpha hC hβ hγ hwD hwX hwγ


private theorem not_commute_conj_of_mem_KOrbit (hC : HypothesisC D) {vH : H hC}
    (hv2 : vH * vH = 1) (hvD : (vH : G) ∈ D)
    {s w : H hC} (hs : s ∈ KOrbit hC vH) (hw : w ∈ KOrbit hC vH)
    (hns : ¬ Commute vH s) (hcomm : Commute vH w) :
    ¬ Commute s w := by
  intro hc
  have hvK : vH ∈ KOrbit hC vH := ⟨1, (K hC).one_mem, by rw [one_mul, inv_one, mul_one]⟩
  have h1 : s * w ∈ Q hC := mul_mem_Q_of_mem_KOrbit hC hv2 hs hw hc
  have h2 : w * vH ∈ Q hC := mul_mem_Q_of_mem_KOrbit hC hv2 hw hvK hcomm.symm
  have hw2 : w * w = 1 := mul_self_eq_one_of_mem_KOrbit hC hv2 hw
  have h3 : s * vH ∈ Q hC := by
    have hid : (s * w) * (w * vH) = s * vH := by
      calc (s * w) * (w * vH) = s * (w * w) * vH := by group
        _ = s * vH := by rw [hw2, mul_one]
    rw [← hid]
    exact Subgroup.mul_mem _ h1 h2
  have hnot : vH * s ∉ Q hC := mul_not_mem_Q_of_mem_KOrbit hC hv2 hvD hs hns
  have hs2 : s * s = 1 := mul_self_eq_one_of_mem_KOrbit hC hv2 hs
  apply hnot
  rw [show vH * s = (s * vH)⁻¹ by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hs2]]
  exact (Q hC).inv_mem h3

private theorem conj_orbit_mem_block (hC : HypothesisC D) {β : Set G}
    {vH : H hC} (hv2 : vH * vH = 1) (hvD : (vH : G) ∈ D)
    {k₀ : H hC} (hk₀ : k₀ ∈ K hC) (hnc₀H : ¬ Commute vH (k₀ * vH * k₀⁻¹))
    (hSAH : ∀ k : H hC, k ∈ K hC → ¬ Commute vH (k * vH * k⁻¹) →
      ((k * vH * k⁻¹ : H hC) : G) ∈ β)
    {w : H hC} (hwOrbit : w ∈ KOrbit hC vH) (hcomm : Commute vH w) :
    ((w * (k₀ * vH * k₀⁻¹) * w⁻¹ : H hC) : G) ∈ β := by
  have hs₀Orbit : k₀ * vH * k₀⁻¹ ∈ KOrbit hC vH := ⟨k₀, hk₀, rfl⟩
  have hns : ¬ Commute (k₀ * vH * k₀⁻¹) w :=
    not_commute_conj_of_mem_KOrbit hC hv2 hvD hs₀Orbit hwOrbit hnc₀H hcomm
  have hw2 : w * w = 1 := mul_self_eq_one_of_mem_KOrbit hC hv2 hwOrbit
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h3 : w * vH * w⁻¹ = vH := by
    rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hk' : w * k₀ * w⁻¹ ∈ K hC := (normal_K hC).conj_mem k₀ hk₀ w
  have hns' : ¬ Commute vH (w * (k₀ * vH * k₀⁻¹) * w⁻¹) := by
    intro hc
    apply hnc₀H
    have h1 : Commute (w * vH * w⁻¹)
        (w * (w * (k₀ * vH * k₀⁻¹) * w⁻¹) * w⁻¹) := hc.conj w
    have h2 : w * (w * (k₀ * vH * k₀⁻¹) * w⁻¹) * w⁻¹ = k₀ * vH * k₀⁻¹ := by
      rw [hw_inv]
      calc w * (w * (k₀ * vH * k₀⁻¹) * w) * w
          = (w * w) * (k₀ * vH * k₀⁻¹) * (w * w) := by group
        _ = k₀ * vH * k₀⁻¹ := by rw [hw2, one_mul, mul_one]
    rw [h3, h2] at h1
    exact h1
  have heq : (w * k₀ * w⁻¹) * vH * (w * k₀ * w⁻¹)⁻¹
      = w * (k₀ * vH * k₀⁻¹) * w⁻¹ := by
    calc (w * k₀ * w⁻¹) * vH * (w * k₀ * w⁻¹)⁻¹
        = (w * k₀ * w⁻¹) * (w * vH * w⁻¹) * (w * k₀ * w⁻¹)⁻¹ := by rw [h3]
      _ = w * (k₀ * vH * k₀⁻¹) * w⁻¹ := by group
  have hnc' : ¬ Commute vH ((w * k₀ * w⁻¹) * vH * (w * k₀ * w⁻¹)⁻¹) := by
    rw [heq]
    exact hns'
  have h := hSAH (w * k₀ * w⁻¹) hk' hnc'
  rwa [heq] at h

private theorem mem_block_of_commute_conj (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {vH : H hC}
    (hv2 : vH * vH = 1) (hvD : (vH : G) ∈ D)
    {k₀ : H hC} (hk₀ : k₀ ∈ K hC) (hnc₀H : ¬ Commute vH (k₀ * vH * k₀⁻¹))
    (hSAH : ∀ k : H hC, k ∈ K hC → ¬ Commute vH (k * vH * k⁻¹) →
      ((k * vH * k⁻¹ : H hC) : G) ∈ β)
    (hs₀β : ((k₀ * vH * k₀⁻¹ : H hC) : G) ∈ β)
    {w : H hC} (hwOrbit : w ∈ KOrbit hC vH) (hcomm : Commute vH w) :
    ((w : H hC) : G) ∈ β := by
  have hs'β : ((w * (k₀ * vH * k₀⁻¹) * w⁻¹ : H hC) : G) ∈ β :=
    conj_orbit_mem_block hC hv2 hvD hk₀ hnc₀H hSAH hwOrbit hcomm
  have hns : ¬ Commute (k₀ * vH * k₀⁻¹) w :=
    not_commute_conj_of_mem_KOrbit hC hv2 hvD ⟨k₀, hk₀, rfl⟩ hwOrbit hnc₀H hcomm
  have hs₀D : ((k₀ * vH * k₀⁻¹ : H hC) : G) ∈ D :=
    hC.setup.normal (k₀ : G) (vH : G) hvD
  obtain ⟨kw, hkw, hw_eq⟩ := hwOrbit
  have hwD : ((w : H hC) : G) ∈ D := by
    rw [hw_eq]
    exact hC.setup.normal (kw : G) (vH : G) hvD
  have hnsG : ¬ Commute ((k₀ * vH * k₀⁻¹ : H hC) : G) ((w : H hC) : G) :=
    fun hc => hns (Subtype.ext hc.eq)
  have hcl := mem_closure_of_not_commute hC hs₀D hwD hnsG
  have hsub : Subgroup.closure
      ({((k₀ * vH * k₀⁻¹ : H hC) : G),
        (w : G) * ((k₀ * vH * k₀⁻¹ : H hC) : G) * (w : G)⁻¹} : Set G)
      ≤ Subgroup.closure (β : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure hs₀β
    · simpa using Subgroup.subset_closure hs'β
  exact closure_inter_D_subset hC hβ ⟨hsub hcl, hwD⟩

private theorem mem_block_of_forall_not_commute_mem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β)
    (hk₀ : ∃ k₀ : H hC, k₀ ∈ K hC ∧ ¬ Commute v ((k₀ : G) * v * (k₀ : G)⁻¹))
    (hSA : ∀ k : H hC, k ∈ K hC → ¬ Commute v ((k : G) * v * (k : G)⁻¹) →
      (k : G) * v * (k : G)⁻¹ ∈ β) :
    ∀ k : H hC, k ∈ K hC → (k : G) * v * (k : G)⁻¹ ∈ β := by
  obtain ⟨k₀, hk₀, hnc₀⟩ := hk₀
  have hvD : v ∈ D := hβ.2.1 hv
  have hvStar : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hvH : v ∈ H hC := Subgroup.subset_closure hvStar
  set vH : H hC := ⟨v, hvH⟩ with hvHdef
  have hv2 : vH * vH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hvD)
  have hnc₀H : ¬ Commute vH (k₀ * vH * k₀⁻¹) :=
    fun hc => hnc₀ (by simpa using hc.map (H hC).subtype)
  have hSAH : ∀ k : H hC, k ∈ K hC → ¬ Commute vH (k * vH * k⁻¹) →
      ((k * vH * k⁻¹ : H hC) : G) ∈ β := by
    intro k hk hnc
    exact hSA k hk (fun hc => hnc (Subtype.ext hc.eq))
  have hs₀β : ((k₀ * vH * k₀⁻¹ : H hC) : G) ∈ β := hSAH k₀ hk₀ hnc₀H
  intro k hk
  set w : H hC := k * vH * k⁻¹ with hwdef
  have hwOrbit : w ∈ KOrbit hC vH := ⟨k, hk, hwdef⟩
  by_cases hnc : ¬ Commute vH w
  · exact hSA k hk (fun hc => hnc (Subtype.ext hc.eq))
  · push Not at hnc
    by_cases hwv : w = vH
    · change ((w : H hC) : G) ∈ β
      rw [hwv]
      exact hv
    · exact mem_block_of_commute_conj hC hβ hv2 hvD hk₀ hnc₀H hSAH hs₀β hwOrbit hnc

private theorem conj_mem_of_mem_K_of_forall_mem_block (hC : HypothesisC D) {vH : H hC}
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hvβ : (vH : G) ∈ β)
    (hSβ : ∀ k : H hC, k ∈ K hC → (k : G) * (vH : G) * (k : G)⁻¹ ∈ β)
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) {c : G} (hc : c ∈ γ)
    {k : H hC} (hk : k ∈ K hC) :
    (k : G) * c * (k : G)⁻¹ ∈ γ := by
  have hvStar : (vH : G) ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hvβ
  have hcStar : c ∈ DalphaStar D hC.alpha := ⟨γ, hγ, hc⟩
  obtain ⟨h, hh, hvc⟩ := hC.Halpha_transitive (vH : G) hvStar c hcStar
  set hH : H hC := ⟨h, hh⟩ with hHdef
  have hk' : hH⁻¹ * k * hH ∈ K hC := by
    simpa using (normal_K hC).conj_mem k hk hH⁻¹
  have hmemβ : ((hH⁻¹ * k * hH : H hC) : G) * (vH : G) * ((hH⁻¹ * k * hH : H hC) : G)⁻¹
      ∈ β := hSβ (hH⁻¹ * k * hH) hk'
  have hmem' : h⁻¹ * ((k : G) * c * (k : G)⁻¹) * h ∈ β := by
    have h1 : ((hH⁻¹ * k * hH : H hC) : G) * (vH : G) *
        ((hH⁻¹ * k * hH : H hC) : G)⁻¹ = h⁻¹ * ((k : G) * c * (k : G)⁻¹) * h := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hHdef]
      rw [← hvc]
      group
    rwa [h1] at hmemβ
  have hwimg : (k : G) * c * (k : G)⁻¹ ∈ cimg h β :=
    ⟨h⁻¹ * ((k : G) * c * (k : G)⁻¹) * h, hmem', by group⟩
  have hcimg : c ∈ cimg h β := ⟨(vH : G), hvβ, hvc⟩
  have hclass : cimg h β ∈ blockClass hC.alpha := by
    rw [← blockClass_eq_of_mem hβ.1]
    exact mem_blockClass_iff.mpr ⟨h, rfl⟩
  have heq : cimg h β = γ :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass hγ.1 ⟨c, hcimg, hc⟩
  rwa [heq] at hwimg

private theorem conj_perp_eq_of_forall_mem_block (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {vH : H hC} (hvβ : (vH : G) ∈ β)
    {k₀ : H hC} (hk₀ : k₀ ∈ K hC) (hv2 : vH * vH = 1)
    (hSβ : ∀ k : H hC, k ∈ K hC → (k : G) * (vH : G) * (k : G)⁻¹ ∈ β) :
    ∀ γ ∈ perp D hC.alpha, cimg ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) γ = γ := by
  have htK : vH * (k₀ * vH * k₀⁻¹) ∈ K hC :=
    CFSG.GroupTheory.mul_mul_conj_mem_of_normal (hN := normal_K hC) hk₀ hv2
  have hHcent : H hC ≤ Subgroup.centralizer (hC.alpha : Set G) := by
    rw [show H hC = Halpha D hC.alpha from rfl, Halpha, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Nine.commute_of_mem_alpha_of_mem_DalphaStar hC ha hx).eq
  intro γ hγ
  rcases mem_perp_iff.mp hγ with hγD | rfl
  · have hsub : cimg ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) γ ⊆ γ := by
      rintro y ⟨c, hc, rfl⟩
      exact conj_mem_of_mem_K_of_forall_mem_block (vH := vH) hC hβ hvβ hSβ hγD hc htK
    have hsub' : cimg ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G)⁻¹ γ ⊆ γ := by
      rintro y ⟨c, hc, rfl⟩
      exact conj_mem_of_mem_K_of_forall_mem_block (vH := vH) hC hβ hvβ hSβ hγD hc
        ((K hC).inv_mem htK)
    refine Set.Subset.antisymm hsub ?_
    intro y hy
    have h1 : ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G)⁻¹ * y *
        ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) ∈ γ := hsub' ⟨y, hy, by group⟩
    exact ⟨_, h1, by group⟩
  · have htH : ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) ∈ H hC :=
      (vH * (k₀ * vH * k₀⁻¹)).2
    have hcent := hHcent htH
    rw [Subgroup.mem_centralizer_iff] at hcent
    have hfix : ∀ a ∈ hC.alpha, ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) * a *
        ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G)⁻¹ = a := by
      intro a ha
      have h1 : a * ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) =
          ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) * a := hcent a ha
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    calc cimg ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) hC.alpha = id '' hC.alpha :=
          Set.image_congr hfix
      _ = hC.alpha := Set.image_id' hC.alpha

private theorem actsTriviallyOnBlocks_of_forall_mem_block (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {vH : H hC} (hvβ : (vH : G) ∈ β)
    {k₀ : H hC} (hk₀ : k₀ ∈ K hC) (hv2 : vH * vH = 1)
    (hSβ : ∀ k : H hC, k ∈ K hC → (k : G) * (vH : G) * (k : G)⁻¹ ∈ β) :
    ActsTriviallyOnBlocks hC.alpha ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have hbβ : ((k₀ * vH * k₀⁻¹ : H hC) : G) ∈ β := hSβ k₀ hk₀
  have ht : ∀ y ∈ DalphaStar D β, Commute ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) y := by
    intro y hy
    obtain ⟨γ, hγ, hyγ⟩ := hy
    have hvy : Commute (vH : G) y := (mem_Dalpha_iff.mp hγ).2.2.2 (vH : G) hvβ y hyγ
    have hby : Commute ((k₀ * vH * k₀⁻¹ : H hC) : G) y :=
      (mem_Dalpha_iff.mp hγ).2.2.2 ((k₀ * vH * k₀⁻¹ : H hC) : G) hbβ y hyγ
    exact hvy.mul_left hby
  have htβ : cimg ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) β = β := by
    have hvN : (vH : G) ∈ Subgroup.normalizer β := mem_normalizer_of_mem_block hβblock hvβ
    have hbN : ((k₀ * vH * k₀⁻¹ : H hC) : G) ∈ Subgroup.normalizer β :=
      mem_normalizer_of_mem_block hβblock hbβ
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.mul_mem _ hvN hbN)
  exact actsTriviallyOnBlocks_of_perp_of_theorem8_7 theorem8_7_holds hC h.rad h.not_o4 hβ ht
    htβ (conj_perp_eq_of_forall_mem_block hC hβ hvβ hk₀ hv2 hSβ)

theorem exists_conj_not_commute (h : MainHyp hC) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v : G} (hv : v ∈ β) :
    ∃ k ∈ EightOne.twoOddCore (Halpha D hC.alpha),
      ¬ Commute v ((k : G) * v * (k : G)⁻¹) ∧ (k : G) * v * (k : G)⁻¹ ∉ β := by
  have hvD : v ∈ D := hβ.2.1 hv
  have hvStar : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hvH : v ∈ H hC := Subgroup.subset_closure hvStar
  set vH : H hC := ⟨v, hvH⟩ with hvHdef
  have hv2 : vH * vH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hvD)
  obtain ⟨k₀, hk₀, hnc₀⟩ := exists_not_commute_conj h hvStar
  by_contra hgoal
  push Not at hgoal
  have hSA : ∀ k : H hC, k ∈ K hC → ¬ Commute v ((k : G) * v * (k : G)⁻¹) →
      (k : G) * v * (k : G)⁻¹ ∈ β := fun k hk hnc => hgoal k hk hnc
  have hall : ∀ k : H hC, k ∈ K hC → (k : G) * v * (k : G)⁻¹ ∈ β :=
    mem_block_of_forall_not_commute_mem hC hβ hv ⟨k₀, hk₀, hnc₀⟩ hSA
  have hSβ : ∀ k : H hC, k ∈ K hC → (k : G) * (vH : G) * (k : G)⁻¹ ∈ β :=
    fun k hk => hall k hk
  set b : G := ((k₀ * vH * k₀⁻¹ : H hC) : G) with hbdef
  set t : G := ((vH * (k₀ * vH * k₀⁻¹) : H hC) : G) with htdef
  have ht_eq : t = v * b := rfl
  have htriv : ActsTriviallyOnBlocks hC.alpha t :=
    actsTriviallyOnBlocks_of_forall_mem_block h hβ hv hk₀ hv2 hSβ
  rcases sixSix_dichotomy_of_rad hC h.rad with hW | hF
  · exact h.not_wreath hW
  · have ht1 : t = 1 := hF t htriv
    have hb_eq : b = v := by
      have h : v * b = 1 := ht_eq ▸ ht1
      have h2 : v⁻¹ = b := by rw [mul_eq_one_iff_eq_inv.mp h, inv_inv]
      rw [hC.setup.oddT.inv_eq hvD] at h2
      exact h2.symm
    exact hnc₀ (by change Commute v b; rw [hb_eq])

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
