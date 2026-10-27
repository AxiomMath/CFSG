module

public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingIntersections
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbedding

public section

namespace CFSG.Open

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

noncomputable section

theorem fusionStronglyEmbedded.of_native
    {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : CFSG.BenderSuzuki.IsStronglyEmbedded B) : fusionStronglyEmbedded B := by
  refine ⟨hB.ne_top, hB.card_even, ?_⟩
  intro g hg
  simpa only [rightConjugate, Subgroup.conjBy] using
    hB.inf_rightConjugate_card_odd hg

theorem fusionStronglyEmbedded.map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {B : Subgroup G} (hB : fusionStronglyEmbedded B) (e : G ≃* H) :
    fusionStronglyEmbedded (B.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hB.1
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      using hB.2.1
  · intro g hg
    have hpre : e.symm g ∉ B := by
      intro h
      apply hg
      simpa using Subgroup.mem_map_of_mem e.toMonoidHom h
    have hconj :
        (B.map (MulAut.conj (e.symm g)⁻¹).toMonoidHom).map e.toMonoidHom =
          (B.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    have hinf :
        (B ⊓ B.map (MulAut.conj (e.symm g)⁻¹).toMonoidHom).map e.toMonoidHom =
          B.map e.toMonoidHom ⊓
            (B.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ e.injective, hconj]
    rw [← hinf, Subgroup.card_map_of_injective e.injective]
    exact hB.2.2 (e.symm g) hpre

theorem center_pow_two_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : ∀ z ∈ Subgroup.center G, z ^ 2 = 1) :
    ∀ z ∈ Subgroup.center H, z ^ 2 = 1 := by
  intro z hz
  have hpre : e.symm z ∈ Subgroup.center G := by
    rw [← Subgroup.map_center_eq e.symm]
    exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hz
  simpa using congrArg e (hG (e.symm z) hpre)

@[expose] def fusionBenderSubgroupData
    {G : Type*} [Group G] (R : Subgroup G) (q k : ℕ) : Prop :=
  fusionStronglyEmbedded (Subgroup.normalizer (R : Set G)) ∧
    (∃ D : Subgroup G, IsCyclic D ∧ Odd (Nat.card D) ∧ R ⊓ D = ⊥ ∧
      R ⊔ D = Subgroup.normalizer (R : Set G)) ∧
    (∀ z ∈ Subgroup.center R, z ^ 2 = 1) ∧
    Nat.card (Subgroup.center R) = q ∧ Nat.card R = q ^ k

theorem fusionBenderSubgroupData.map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {R : Subgroup G} {q k : ℕ} (hR : fusionBenderSubgroupData R q k)
    (e : G ≃* H) : fusionBenderSubgroupData (R.map e.toMonoidHom) q k := by
  rcases hR with ⟨hSE, ⟨D, hcyc, hodd, hinf, hsup⟩, hpow, hZcard, hRcard⟩
  have hN := Subgroup.map_equiv_normalizer_eq R e
  let eR := e.subgroupMap R
  let eD := e.subgroupMap D
  let : IsCyclic D := hcyc
  refine ⟨hN ▸ hSE.map_mulEquiv e, ⟨D.map e.toMonoidHom,
    isCyclic_of_surjective eD eD.surjective, ?_, ?_, ?_⟩,
    center_pow_two_of_mulEquiv eR hpow, ?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      using hodd
  · rw [← Subgroup.map_inf _ _ _ e.injective, hinf, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, hsup, hN]
  · exact (Nat.card_congr (Subgroup.centerCongr eR).symm.toEquiv).trans hZcard
  · exact (Nat.card_congr eR.symm.toEquiv).trans hRcard

theorem fusionBenderBorel_of_one_sylow
    {G : Type*} [Group G] [Finite G] {q k : ℕ} (S : Sylow 2 G)
    (hS : fusionBenderSubgroupData (S : Subgroup G) q k) :
    fusionBenderBorel G q k := by
  intro Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hmap : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = Q := by
    change (g • S : Sylow 2 G).toSubgroup = Q.toSubgroup
    rw [hg]
  change fusionBenderSubgroupData (Q : Subgroup G) q k
  have h := hS.map_mulEquiv (MulAut.conj g)
  rw [hmap] at h
  exact h

theorem fusionBenderBorel.map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {q k : ℕ} (hG : fusionBenderBorel G q k) (e : G ≃* H) :
    fusionBenderBorel H q k := by
  intro Q
  let S := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hmap : (S : Subgroup G).map e.toMonoidHom = Q := by
    simp [S, Subgroup.map_map]
  have hS : fusionBenderSubgroupData (S : Subgroup G) q k := hG S
  change fusionBenderSubgroupData (Q : Subgroup H) q k
  have h := hS.map_mulEquiv e
  rw [hmap] at h
  exact h

theorem involution_mem_sylow_of_normalizer_eq_stabilizer
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    (S : Sylow 2 G) (a : Ω)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G a)
    {x : G} (hx : x ∈ MulAction.stabilizer G a) (hI : IsInvolution x) :
    x ∈ (S : Subgroup G) := by
  let B := MulAction.stabilizer G a
  have hSB : (S : Subgroup G) ≤ B := by
    change (S : Subgroup G) ≤ MulAction.stabilizer G a
    rw [← hN]
    exact Subgroup.le_normalizer
  let P : Sylow 2 B := S.subtype hSB
  let : (P : Subgroup B).Normal := by
    change ((S : Subgroup G).subgroupOf B).Normal
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr
    exact hN.ge
  let : Unique (Sylow 2 B) := P.unique_of_normal inferInstance
  let y : B := ⟨x, hx⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_involution
    (CFSG.BenderSuzuki.IsInvolution.subtype hI hx)).exists_le_sylow
  have hyQ : y ∈ (Q : Subgroup B) := hQ (Subgroup.mem_zpowers y)
  have hQP : Q = P := Subsingleton.elim _ _
  rw [hQP] at hyQ
  exact hyQ

theorem fusionStronglyEmbedded_of_sylow_regular_compl
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    (S : Sylow 2 G) (a : Ω)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G a)
    (hmove : ∃ g : G, g • a ≠ a)
    (heven : Even (Nat.card (S : Subgroup G)))
    (hreg : ∀ b c : Ω, b ≠ a → c ≠ a →
      ∃! s : S, (s : G) • b = c) :
    fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  rw [hN]
  apply fusionStronglyEmbedded.of_native
  refine ⟨?_, ?_, ?_⟩
  · rintro htop
    obtain ⟨g, hg⟩ := hmove
    exact hg (MulAction.mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top g))
  · obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card'
      (G := (S : Subgroup G)) 2 (even_iff_two_dvd.mp heven)
    have hI : IsInvolution x := by
      exact ⟨(orderOf_eq_prime_iff.mp hxorder).2,
        (orderOf_eq_prime_iff.mp hxorder).1⟩
    refine ⟨(x : G), ?_,
      CFSG.BenderSuzuki.IsInvolution.map_of_injective hI
        (S : Subgroup G).subtype (S : Subgroup G).subtype_injective⟩
    rw [← hN]
    exact Subgroup.le_normalizer x.property
  · intro g hg x hxB hxconj hxI
    have hxS := involution_mem_sylow_of_normalizer_eq_stabilizer S a hN hxB hxI
    have hgmove : g⁻¹ • a ≠ a := by
      intro h
      apply hg
      simpa only [inv_inv] using (MulAction.stabilizer G a).inv_mem
        (MulAction.mem_stabilizer_iff.mpr h)
    have hxfix : x • (g⁻¹ • a) = g⁻¹ • a := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_smul, mul_smul, smul_inv_smul]
      exact congrArg (fun b => g⁻¹ • b) (MulAction.mem_stabilizer_iff.mp hy)
    obtain ⟨s, hs, huniq⟩ := hreg (g⁻¹ • a) (g⁻¹ • a) hgmove hgmove
    have hx1 : (⟨x, hxS⟩ : S) = 1 :=
      (huniq ⟨x, hxS⟩ hxfix).trans (huniq 1 (by simp)).symm
    exact hxI.ne_one (congrArg Subtype.val hx1)

end

end CFSG.Open
