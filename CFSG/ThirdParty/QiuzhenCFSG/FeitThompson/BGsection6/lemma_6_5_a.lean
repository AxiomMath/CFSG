module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct commutatorElement

/-! # Lemma 6.5 infrastructure from BG Section 6 -/

public theorem CFSG.lemma_6_5_conjBy_mul
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    H.conjBy (a * b) = (H.conjBy b).conjBy a := by
  simpa using Subgroup.conjBy_mul H a b

public theorem CFSG.lemma_6_5_conjBy_eq_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (G := G) H) :
    H.conjBy g = H := by
  simpa using conjBy_eq_of_mem_normalizer_local (H := H) hg

theorem CFSG.lemma_6_5_mem_normalizer_of_conjBy_eq
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (G := G) H := by
  simpa using mem_normalizer_of_conjBy_eq_local (H := H) hg


theorem CFSG.lemma_6_5_conjBy_inv_mul_cancel
    {G : Type*} [Group G] (H : Subgroup G) {a b : G}
    (h : H.conjBy a = H.conjBy b) :
    H.conjBy (a⁻¹ * b) = H := by
  simpa using Subgroup.conjBy_inv_mul_cancel H h

public theorem CFSG.lemma_6_5_centralizerIn_le_normalizer
    {G : Type*} [Group G] (K H : Subgroup G) :
    subgroupCentralizerIn K H ≤ Subgroup.normalizer (G := G) H := by
  intro x hx
  exact centralizer_le_normalizer H hx.2

public theorem CFSG.lemma_6_5_derived_le_sup_commutator
    {G : Type*} [Group G] [Finite G] {K U : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) :
    derivedSubgroup G ≤ K ⊔ ⁅U, U⁆ := by
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ K ⊔ ⁅U, U⁆
  rw [Subgroup.commutator_le]
  intro p hp q hq
  have hp_sup : p ∈ K ⊔ U := by simp [hKU]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := U) (x := p)).1 hp_sup with
    ⟨k₁, hk₁K, u₁, hu₁U, hk₁u₁⟩
  have hq_sup : q ∈ K ⊔ U := by simp [hKU]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := U) (x := q)).1 hq_sup with
    ⟨k₂, hk₂K, u₂, hu₂U, hk₂u₂⟩
  let c : G := ⁅u₁, u₂⁆
  have hcUU : c ∈ ⁅U, U⁆ := by
    exact Subgroup.commutator_mem_commutator (H₁ := U) (H₂ := U) hu₁U hu₂U
  have hk₁eq : (((k₁ * u₁ : G) : G) : G ⧸ K) = (u₁ : G ⧸ K) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hk₁K
  have hk₂eq : (((k₂ * u₂ : G) : G) : G ⧸ K) = (u₂ : G ⧸ K) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hk₂K
  have hmap_eq : QuotientGroup.mk' K ⁅p, q⁆ = QuotientGroup.mk' K c := by
    calc
      QuotientGroup.mk' K ⁅p, q⁆
          = ⁅((p : G) : G ⧸ K), ((q : G) : G ⧸ K)⁆ := by
              exact
                (map_commutatorElement (f := QuotientGroup.mk' K) (g₁ := p) (g₂ := q))
      _ = ⁅(((k₁ * u₁ : G) : G) : G ⧸ K), (((k₂ * u₂ : G) : G) : G ⧸ K)⁆ := by
            rw [← hk₁u₁, ← hk₂u₂]
      _ = ⁅(u₁ : G ⧸ K), (u₂ : G ⧸ K)⁆ := by rw [hk₁eq, hk₂eq]
      _ = QuotientGroup.mk' K c := by
            exact
              (map_commutatorElement (f := QuotientGroup.mk' K) (g₁ := u₁) (g₂ := u₂)).symm
  let k₀ : G := ⁅p, q⁆ * c⁻¹
  have hk₀K : k₀ ∈ K := by
    apply (QuotientGroup.eq_one_iff (N := K) (x := k₀)).mp
    calc
      QuotientGroup.mk' K k₀ = QuotientGroup.mk' K ⁅p, q⁆ * (QuotientGroup.mk' K c)⁻¹ := by
        simp only [k₀, map_mul, map_inv]
      _ = QuotientGroup.mk' K c * (QuotientGroup.mk' K c)⁻¹ := by rw [hmap_eq]
      _ = 1 := by simp
  have hrepr : ⁅p, q⁆ = k₀ * c := by
    dsimp [k₀]
    simp [mul_assoc]
  rw [hrepr]
  exact (K ⊔ ⁅U, U⁆).mul_mem (Subgroup.mem_sup_left hk₀K) (Subgroup.mem_sup_right hcUU)

public theorem CFSG.lemma_6_5_c_core
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {K U H : Subgroup G} [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (g : G) (hconj : H.conjBy g ≤ U) :
    ∃ c ∈ subgroupCentralizerIn K H, ∃ u ∈ U, g = u * c := by
  classical
  have hHK_bot : H ⊓ K = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hg_sup : g ∈ U ⊔ K := by
    simp [hKU, sup_comm]
  obtain ⟨u₀, hu₀U, k, hkK, huk⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := U) (t := K) (x := g)).1 hg_sup
  have hHk_le_U : H.conjBy k ≤ U := by
    rw [← huk] at hconj
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨h, hhH, rfl⟩
    have hxg : u₀ * (k * h * k⁻¹) * u₀⁻¹ ∈ U := by
      have hx_conj : u₀ * (k * h * k⁻¹) * u₀⁻¹ ∈ H.conjBy (u₀ * k) := by
        refine Subgroup.mem_map.mpr ?_
        exact ⟨h, hhH, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact hconj hx_conj
    have hu₀Inv : u₀⁻¹ ∈ U := U.inv_mem hu₀U
    have hback : u₀⁻¹ * (u₀ * (k * h * k⁻¹) * u₀⁻¹) * u₀ ∈ U :=
      U.mul_mem (U.mul_mem hu₀Inv hxg) hu₀U
    simpa [Subgroup.conjBy, MulAut.conj_apply, mul_assoc] using hback
  obtain ⟨w, hwK, hwU, hw_conj⟩ :
      ∃ w : G, w ∈ K ∧ w ∈ U ∧ H.conjBy w = H.conjBy k := by
    let L : Subgroup G := (H ⊔ K) ⊓ U
    let N : Subgroup G := K ⊓ U
    have hH_le_L : H ≤ L := by
      intro x hx
      exact ⟨Subgroup.mem_sup_left hx, hHU hx⟩
    have hN_le_L : N ≤ L := by
      intro x hx
      exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
    have hHk_le_H_sup_K : H.conjBy k ≤ H ⊔ K := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨h, hhH, rfl⟩
      have hkInvK : k⁻¹ ∈ K := K.inv_mem hkK
      exact (H ⊔ K).mul_mem
        ((H ⊔ K).mul_mem (Subgroup.mem_sup_right hkK) (Subgroup.mem_sup_left hhH))
        (Subgroup.mem_sup_right hkInvK)
    have hH_le_Hk_sup_K : H ≤ H.conjBy k ⊔ K := by
      intro h hhH
      have hkInvK : k⁻¹ ∈ K := K.inv_mem hkK
      have hhconj : k * h * k⁻¹ ∈ H.conjBy k := by
        exact Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
      have hmid : k⁻¹ * (k * h * k⁻¹) ∈ H.conjBy k ⊔ K := by
        exact (H.conjBy k ⊔ K).mul_mem (Subgroup.mem_sup_right hkInvK)
          (Subgroup.mem_sup_left hhconj)
      have hhEq : h = (k⁻¹ * (k * h * k⁻¹)) * k := by
        group
      rw [hhEq]
      exact (H.conjBy k ⊔ K).mul_mem hmid (Subgroup.mem_sup_right hkK)
    have hHK_eq_hHkK : H ⊔ K = H.conjBy k ⊔ K := by
      apply le_antisymm
      · exact sup_le hH_le_Hk_sup_K le_sup_right
      · exact sup_le hHk_le_H_sup_K le_sup_right
    have hN_sup_H : N ⊔ H = L := by
      apply le_antisymm
      · exact sup_le hN_le_L hH_le_L
      · intro x hxL
        rcases (Subgroup.mem_sup_of_normal_right (s := H) (t := K) (x := x)).1 hxL.1 with
          ⟨h, hhH, k', hk'K, hhkx⟩
        have hhU : h ∈ U := hHU hhH
        have hk'U : k' ∈ U := by
          have : k' = h⁻¹ * x := by
            calc
              k' = h⁻¹ * (h * k') := by group
              _ = h⁻¹ * x := by rw [hhkx]
          rw [this]
          exact U.mul_mem (U.inv_mem hhU) hxL.2
        rw [← hhkx]
        exact (N ⊔ H).mul_mem (Subgroup.mem_sup_right hhH) (Subgroup.mem_sup_left ⟨hk'K, hk'U⟩)
    have hHk_le_L : H.conjBy k ≤ L := by
      intro x hx
      exact ⟨hHk_le_H_sup_K hx, hHk_le_U hx⟩
    have hN_sup_Hk : N ⊔ H.conjBy k = L := by
      apply le_antisymm
      · exact sup_le hN_le_L hHk_le_L
      · intro x hxL
        have hxL' : x ∈ (H.conjBy k ⊔ K) ⊓ U := by
          simpa [L, hHK_eq_hHkK] using hxL
        rcases (Subgroup.mem_sup_of_normal_right (s := H.conjBy k) (t := K) (x := x)).1 hxL'.1 with
          ⟨h, hhHk, k', hk'K, hhkx⟩
        have hhU : h ∈ U := hHk_le_U hhHk
        have hk'U : k' ∈ U := by
          have : k' = h⁻¹ * x := by
            calc
              k' = h⁻¹ * (h * k') := by group
              _ = h⁻¹ * x := by rw [hhkx]
          rw [this]
          exact U.mul_mem (U.inv_mem hhU) hxL'.2
        rw [← hhkx]
        exact (N ⊔ H.conjBy k).mul_mem
          (Subgroup.mem_sup_right hhHk) (Subgroup.mem_sup_left ⟨hk'K, hk'U⟩)
    let Nsub : Subgroup L := N.subgroupOf L
    let Hsub : Subgroup L := H.subgroupOf L
    let Hksub : Subgroup L := (H.conjBy k).subgroupOf L
    have hNsub_eq_Ksub : Nsub = K.subgroupOf L := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, x.2.2⟩
    have : Nsub.Normal := by
      have hKsubNormal : (K.subgroupOf L).Normal := by
        simpa using
          (Subgroup.Normal.subgroupOf (H := K) (K := L) (inferInstance : K.Normal))
      simpa [Nsub, hNsub_eq_Ksub] using hKsubNormal
    have hdisjHK : Disjoint H K := by
      rw [Subgroup.disjoint_def]
      intro x hxH hxK
      exact Subgroup.mem_bot.mp (by
        simpa [hHK_bot] using (show x ∈ H ⊓ K from ⟨hxH, hxK⟩))
    have hdisj_N_H : Disjoint Nsub Hsub := by
      rw [Subgroup.disjoint_def]
      intro x hxN hxH
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hdisjHK) hxH hxN.1
    have hcard_Hk : Nat.card (H.conjBy k) = Nat.card H := by
      simpa [Subgroup.conjBy] using
        (Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj k).toMonoidHom)
          (hf := EquivLike.injective (MulAut.conj k)))
    have hHkK_bot : H.conjBy k ⊓ K = ⊥ := by
      have hcopHk : Nat.Coprime (Nat.card (H.conjBy k)) (Nat.card K) := by
        rw [hcard_Hk]
        exact hcop
      exact (Subgroup.disjoint_of_coprime_natCard hcopHk).eq_bot
    have hdisjHkK : Disjoint (H.conjBy k) K := by
      rw [Subgroup.disjoint_def]
      intro x hxHk hxK
      simpa [hHkK_bot] using (show x ∈ H.conjBy k ⊓ K from ⟨hxHk, hxK⟩)
    have hdisj_N_Hk : Disjoint Nsub Hksub := by
      rw [Subgroup.disjoint_def]
      intro x hxN hxHk
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hdisjHkK) hxHk hxN.1
    have hsup_H : Nsub ⊔ Hsub = ⊤ := by
      calc
        Nsub ⊔ Hsub = (N ⊔ H).subgroupOf L := by
          symm
          exact Subgroup.subgroupOf_sup (A := N) (A' := H) (B := L) hN_le_L hH_le_L
        _ = L.subgroupOf L := by rw [hN_sup_H]
        _ = ⊤ := by simp
    have hsup_Hk : Nsub ⊔ Hksub = ⊤ := by
      calc
        Nsub ⊔ Hksub = (N ⊔ H.conjBy k).subgroupOf L := by
          symm
          exact Subgroup.subgroupOf_sup (A := N) (A' := H.conjBy k) (B := L) hN_le_L hHk_le_L
        _ = L.subgroupOf L := by rw [hN_sup_Hk]
        _ = ⊤ := by simp
    have hmul_univ_H : ((Nsub : Set L) * (Hsub : Set L)) = Set.univ := by
      calc
        ((Nsub : Set L) * (Hsub : Set L)) = (↑(Nsub ⊔ Hsub) : Set L) := by
          simpa using (Subgroup.normal_mul Nsub Hsub).symm
        _ = Set.univ := by simp [hsup_H]
    have hmul_univ_Hk : ((Nsub : Set L) * (Hksub : Set L)) = Set.univ := by
      calc
        ((Nsub : Set L) * (Hksub : Set L)) = (↑(Nsub ⊔ Hksub) : Set L) := by
          simpa using (Subgroup.normal_mul Nsub Hksub).symm
        _ = Set.univ := by simp [hsup_Hk]
    have hcomp_H : Nsub.IsComplement' Hsub :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_N_H hmul_univ_H
    have hcomp_Hk : Nsub.IsComplement' Hksub :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_N_Hk hmul_univ_Hk
    have hcop_N_H : Nat.Coprime (Nat.card N) (Nat.card H) := by
      exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le (show N ≤ K from inf_le_left)) hcop.symm
    have hcop_cards_sub : Nat.Coprime (Nat.card Nsub) (Nat.card Hsub) := by
      simpa [Nsub, Hsub, natCard_subgroupOf_eq N L hN_le_L, natCard_subgroupOf_eq H L hH_le_L] using
        hcop_N_H
    have hcop_index_sub : Nat.Coprime (Nat.card Nsub) Nsub.index := by
      simpa [hcomp_H.symm.index_eq_card, Hsub, natCard_subgroupOf_eq H L hH_le_L] using
        hcop_cards_sub
    let π : Set Nat.Primes := { p | p.val ∣ Nat.card H }
    have hhall_H : IsHallSubgroup π Hsub := by
      refine isHallSubgroup_of (G := L) (π := π) (H := Hsub) ?_ ?_
      · intro p hp_dvd
        change p.val ∣ Nat.card H
        simpa [Hsub, natCard_subgroupOf_eq H L hH_le_L] using hp_dvd
      · intro p hp_in hp_dvd_idx
        have hp_dvd_Nsub : p.val ∣ Nat.card Nsub := by
          simpa [hcomp_H.index_eq_card] using hp_dvd_idx
        have hp_dvd_N : p.val ∣ Nat.card N := by
          simpa [Nsub, natCard_subgroupOf_eq N L hN_le_L] using hp_dvd_Nsub
        have hp_dvd_K : p.val ∣ Nat.card K :=
          dvd_trans hp_dvd_N (Subgroup.card_dvd_of_le (show N ≤ K from inf_le_left))
        exact (Nat.not_coprime_of_dvd_of_dvd p.2.one_lt hp_in hp_dvd_K) hcop
    have hcard_Hksub : Nat.card Hksub = Nat.card H := by
      calc
        Nat.card Hksub = Nat.card (H.conjBy k) := by
          exact natCard_subgroupOf_eq (H.conjBy k) L hHk_le_L
        _ = Nat.card H := hcard_Hk
    have hhall_Hk : IsHallSubgroup π Hksub := by
      refine isHallSubgroup_of (G := L) (π := π) (H := Hksub) ?_ ?_
      · intro p hp_dvd
        change p.val ∣ Nat.card H
        rwa [hcard_Hksub] at hp_dvd
      · intro p hp_in hp_dvd_idx
        have hp_dvd_Nsub : p.val ∣ Nat.card Nsub := by
          simpa [hcomp_Hk.index_eq_card] using hp_dvd_idx
        have hp_dvd_N : p.val ∣ Nat.card N := by
          simpa [Nsub, natCard_subgroupOf_eq N L hN_le_L] using hp_dvd_Nsub
        have hp_dvd_K : p.val ∣ Nat.card K :=
          dvd_trans hp_dvd_N (Subgroup.card_dvd_of_le (show N ≤ K from inf_le_left))
        exact (Nat.not_coprime_of_dvd_of_dvd p.2.one_lt hp_in hp_dvd_K) hcop
    have hL_solv : Group.IsSolvable L := by infer_instance
    obtain ⟨w0, hw0⟩ :=
      exists_conj_eq_of_isHallSubgroup_of_solvable (G := L) hL_solv hhall_H hhall_Hk
    have hw0_sup : w0 ∈ Nsub ⊔ Hsub := by
      simp [hsup_H]
    obtain ⟨n, hnNsub, h, hhHsub, hnh_eq⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Nsub) (t := Hsub) (x := w0)).1 hw0_sup
    have hhN : h ∈ Subgroup.normalizer (G := L) Hsub := Subgroup.le_normalizer hhHsub
    have hh_conj : Hsub.conjBy h = Hsub := lemma_6_5_conjBy_eq_of_mem_normalizer (H := Hsub) hhN
    have hn : Hksub = Hsub.map (MulAut.conj n).toMonoidHom := by
      calc
        Hksub = Hsub.map (MulAut.conj w0).toMonoidHom := hw0
        _ = Hsub.map (MulAut.conj (n * h)).toMonoidHom := by rw [hnh_eq]
        _ = Hsub.conjBy (n * h) := rfl
        _ = (Hsub.conjBy h).conjBy n := lemma_6_5_conjBy_mul Hsub n h
        _ = Hsub.conjBy n := by rw [hh_conj]
        _ = Hsub.map (MulAut.conj n).toMonoidHom := rfl
    have hHsub_map : Hsub.map L.subtype = H := by
      calc
        Hsub.map L.subtype = H ⊓ L := by simp [Hsub]
        _ = H := inf_eq_left.mpr hH_le_L
    have hHksub_map : Hksub.map L.subtype = H.conjBy k := by
      calc
        Hksub.map L.subtype = H.conjBy k ⊓ L := by
          simp [Hksub]
        _ = H.conjBy k := inf_eq_left.mpr hHk_le_L
    have hmap_hn := congrArg (fun S : Subgroup L => S.map L.subtype) hn
    have hw_conj' : H.conjBy k = H.map (MulAut.conj (n : G)).toMonoidHom := by
      calc
        H.conjBy k = Hksub.map L.subtype := by symm; exact hHksub_map
        _ = (Hsub.map (MulAut.conj n).toMonoidHom).map L.subtype := hmap_hn
        _ = H.map (MulAut.conj (n : G)).toMonoidHom := by
          simpa [Hsub] using
            (map_subgroupOf_map_conj_eq (K0 := L) (K := H) hH_le_L (n := n))
    refine ⟨(n : G), ?_, ?_, ?_⟩
    · have hnN : (n : G) ∈ N := hnNsub
      exact hnN.1
    · have hnN : (n : G) ∈ N := hnNsub
      exact hnN.2
    · simpa [Subgroup.conjBy] using hw_conj'.symm
  have hcentral_seed : w⁻¹ * k ∈ subgroupCentralizerIn K H := by
    let c : G := w⁻¹ * k
    have hcK : c ∈ K := K.mul_mem (K.inv_mem hwK) hkK
    refine ⟨hcK, ?_⟩
    change c ∈ Subgroup.centralizer (H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hhH
    have hc_conj : H.conjBy c = H := by
      simpa [c] using lemma_6_5_conjBy_inv_mul_cancel H hw_conj
    have hcN : c ∈ Subgroup.normalizer (G := G) H :=
      lemma_6_5_mem_normalizer_of_conjBy_eq hc_conj
    have hchH : c * h * c⁻¹ ∈ H :=
      ((Subgroup.mem_normalizer_iff).1 hcN h).1 hhH
    have hcommH : c * h * c⁻¹ * h⁻¹ ∈ H :=
      H.mul_mem hchH (H.inv_mem hhH)
    have hcInvK : c⁻¹ ∈ K := K.inv_mem hcK
    have hhcInvK : h * c⁻¹ * h⁻¹ ∈ K :=
      (inferInstance : K.Normal).conj_mem c⁻¹ hcInvK h
    have hcommK : c * h * c⁻¹ * h⁻¹ ∈ K := by
      have hmul : c * (h * c⁻¹ * h⁻¹) ∈ K := K.mul_mem hcK hhcInvK
      simpa [mul_assoc] using hmul
    have hcommBot : c * h * c⁻¹ * h⁻¹ ∈ (⊥ : Subgroup G) := by
      simpa [hHK_bot] using (show c * h * c⁻¹ * h⁻¹ ∈ H ⊓ K from ⟨hcommH, hcommK⟩)
    have hcommOne : c * h * c⁻¹ * h⁻¹ = 1 := Subgroup.mem_bot.mp hcommBot
    have hcomm : c * h = h * c := by
      calc
        c * h = (c * h * c⁻¹ * h⁻¹) * h * c := by group
        _ = h * c := by rw [hcommOne]; simp
    exact hcomm.symm
  obtain ⟨c, hcC, u, huU, hguc⟩ :
      ∃ c ∈ subgroupCentralizerIn K H, ∃ u ∈ U, g = u * c := by
    refine ⟨w⁻¹ * k, hcentral_seed, u₀ * w, U.mul_mem hu₀U hwU, ?_⟩
    calc
      g = u₀ * k := huk.symm
      _ = (u₀ * w) * (w⁻¹ * k) := by group
  exact ⟨c, hcC, u, huU, hguc⟩

/-! # Lemma 6.5(a) from BG Section 6 -/

public theorem CFSG.lemma_6_5_a
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {K U H : Subgroup G} [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    (H ⊓ derivedSubgroup G = H ⊓ ⁅U, U⁆) := by
  classical
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H := hx.1
    have hxD : x ∈ derivedSubgroup G := hx.2
    have hxU : x ∈ U := hHU hxH
    have hHK_bot : H ⊓ K = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hD_le_K_sup_UU : derivedSubgroup G ≤ K ⊔ ⁅U, U⁆ := by
      exact lemma_6_5_derived_le_sup_commutator hKU
    have hxKUU : x ∈ K ⊔ ⁅U, U⁆ := hD_le_K_sup_UU hxD
    have hx_mod_comm : x ∈ ⁅U, U⁆ := by
      let UUsub : Subgroup U := derivedSubgroup U
      let xU : U := ⟨x, hxU⟩
      let xbar : U ⧸ UUsub := QuotientGroup.mk' UUsub xU
      have hUUsub_eq : UUsub = commutator U := by
        simp [UUsub]
      let qH : H →* U ⧸ UUsub :=
        (QuotientGroup.mk' UUsub).comp (Subgroup.inclusion hHU)
      have horderH : orderOf xbar ∣ Nat.card H := by
        change orderOf (qH ⟨x, hxH⟩) ∣ Nat.card H
        exact dvd_trans (orderOf_map_dvd (ψ := qH) (⟨x, hxH⟩ : H))
          (orderOf_dvd_natCard (⟨x, hxH⟩ : H))
      rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := ⁅U, U⁆) (x := x)).1 hxKUU with
        ⟨k, hkK, y, hyUU, hkyx⟩
      have hyU : y ∈ U := (Subgroup.commutator_le_self U) hyUU
      have hyUUsub : (⟨y, hyU⟩ : U) ∈ UUsub := by
        have hyMap : y ∈ UUsub.map U.subtype := by
          rw [hUUsub_eq, Subgroup.map_subtype_commutator]
          exact hyUU
        exact (Subgroup.mem_map_iff_mem U.subtype_injective).mp hyMap
      have hkU : k ∈ U := by
        have : k = x * y⁻¹ := by
          calc
            k = (k * y) * y⁻¹ := by simp [mul_assoc]
            _ = x * y⁻¹ := by rw [hkyx]
        rw [this]
        exact U.mul_mem hxU (U.inv_mem hyU)
      have hxU_eq : ((⟨k, hkU⟩ : U) * ⟨y, hyU⟩) = xU := by
        apply Subtype.ext
        exact hkyx
      let qKU : ↥(K ⊓ U) →* U ⧸ UUsub :=
        (QuotientGroup.mk' UUsub).comp (Subgroup.inclusion (by
          intro z hz
          exact hz.2))
      have hxbarK : xbar = qKU ⟨k, ⟨hkK, hkU⟩⟩ := by
        have hybar : QuotientGroup.mk' UUsub ⟨y, hyU⟩ = 1 :=
          (QuotientGroup.eq_one_iff (N := UUsub) (x := ⟨y, hyU⟩)).2 hyUUsub
        dsimp [xbar, qKU]
        calc
          QuotientGroup.mk' UUsub xU = QuotientGroup.mk' UUsub (((⟨k, hkU⟩ : U) * ⟨y, hyU⟩)) := by
            rw [← hxU_eq]
          _ = QuotientGroup.mk' UUsub ⟨k, hkU⟩ * QuotientGroup.mk' UUsub ⟨y, hyU⟩ := by
            simpa using
              (map_mul (QuotientGroup.mk' UUsub) (⟨k, hkU⟩ : U) ⟨y, hyU⟩)
          _ = QuotientGroup.mk' UUsub ⟨k, hkU⟩ := by simp [hybar]
          _ = qKU ⟨k, ⟨hkK, hkU⟩⟩ := by rfl
      have horderK : orderOf xbar ∣ Nat.card K := by
        rw [hxbarK]
        exact dvd_trans (orderOf_map_dvd (ψ := qKU) (⟨k, ⟨hkK, hkU⟩⟩ : ↥(K ⊓ U)))
          (dvd_trans (orderOf_dvd_natCard (⟨k, ⟨hkK, hkU⟩⟩ : ↥(K ⊓ U)))
            (Subgroup.card_dvd_of_le (show K ⊓ U ≤ K from inf_le_left)))
      have horder1 : orderOf xbar = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop horderH horderK
      have hxbar1 : xbar = 1 := orderOf_eq_one_iff.mp horder1
      have hxUUsub : xU ∈ UUsub := (QuotientGroup.eq_one_iff (N := UUsub) (x := xU)).mp hxbar1
      have hxmap : x ∈ UUsub.map U.subtype := by
        exact Subgroup.mem_map.mpr ⟨xU, hxUUsub, rfl⟩
      rw [hUUsub_eq, Subgroup.map_subtype_commutator] at hxmap
      exact hxmap
    exact ⟨hxH, hx_mod_comm⟩
  · intro x hx
    have hUU_le_D : ⁅U, U⁆ ≤ derivedSubgroup G := by
      simpa [derivedSeries_one] using
        (Subgroup.commutator_mono (H₁ := U) (H₂ := U)
          (K₁ := (⊤ : Subgroup G)) (K₂ := (⊤ : Subgroup G)) le_top le_top)
    exact ⟨hx.1, hUU_le_D hx.2⟩
