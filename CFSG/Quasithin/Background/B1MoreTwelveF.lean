module

public import CFSG.Quasithin.Background.B1MoreTwelveE

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section Blocks

variable {V : Type*} [CommGroup V]

structure TwelveBlocks (T K : Subgroup (MulAut V))
    (𝓗 : Finset (Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))))) : Prop where
  blocks : IsTransvectionBlocks (ffJ (autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K))))) 𝓗
  offenders : ∀ A : Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))),
    IsFFStarOffender (autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K)))) A →
      ∃ a : Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))) →
          Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))),
        (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
          (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H

variable [Finite V] {T K : Subgroup (MulAut V)}

local notation "𝐔" => fixV (pCoreOf 2 (T ⊔ K))

theorem TwelveHyp.exists_twelveBlocks (h : TwelveHyp T K) :
    ∃ 𝓗 : Finset (Subgroup (MulAut ↥𝐔)), TwelveBlocks T K 𝓗 := by
  obtain ⟨𝓗, hb, hoff⟩ := exists_blocks (B1.sq_eq_one_sub h.sq 𝐔) h.isSolvable_autSub
    h.normal_two_autSub
  exact ⟨𝓗, ⟨hb, hoff⟩⟩

theorem TwelveHyp.comm_of_resHom_comm (h : TwelveHyp T K) {a b : MulAut V}
    (ha : a ∈ conjClosure K T) (hb : b ∈ conjClosure K T) (has : a ∈ stabSub 𝐔)
    (hbs : b ∈ stabSub 𝐔)
    (hcomm : resHom 𝐔 ⟨a, has⟩ * resHom 𝐔 ⟨b, hbs⟩ = resHom 𝐔 ⟨b, hbs⟩ * resHom 𝐔 ⟨a, has⟩) :
    a * b = b * a := by
  have hc : ⁅a, b⁆ ∈ conjClosure K T :=
    (conjClosure K T).mul_mem ((conjClosure K T).mul_mem ((conjClosure K T).mul_mem ha hb)
      ((conjClosure K T).inv_mem ha)) ((conjClosure K T).inv_mem hb)
  have hcs : ⁅a, b⁆ ∈ stabSub 𝐔 :=
    (stabSub 𝐔).mul_mem ((stabSub 𝐔).mul_mem ((stabSub 𝐔).mul_mem has hbs)
      ((stabSub 𝐔).inv_mem has)) ((stabSub 𝐔).inv_mem hbs)
  have h1 : resHom 𝐔 ⟨⁅a, b⁆, hcs⟩ = 1 := by
    have e : resHom 𝐔 ⟨⁅a, b⁆, hcs⟩ = ⁅resHom 𝐔 ⟨a, has⟩, resHom 𝐔 ⟨b, hbs⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [e, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have h2 : ⁅a, b⁆ ∈ centSub 𝐔 := by
    have : (⟨⁅a, b⁆, hcs⟩ : stabSub 𝐔) ∈ (resHom 𝐔).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at this
    exact this
  exact commutatorElement_eq_one_iff_mul_comm.1 (h.eq_one_of_mem_centSub hc h2)

theorem TwelveHyp.le_of_autSub_le (h : TwelveHyp T K) {K' K'' : Subgroup (MulAut V)}
    (hK' : K' ≤ conjClosure K T) (hK'' : K'' ≤ conjClosure K T)
    (hle : autSub K' 𝐔 ≤ autSub K'' 𝐔) : K' ≤ K'' := by
  intro x hx
  have hxs : x ∈ stabSub 𝐔 := (hK'.trans (conjClosure_le_sup.trans h.le_stabSub)) hx
  obtain ⟨g, hgK'', hg⟩ := mem_autSub.1 (hle (mem_autSub.2 ⟨⟨x, hxs⟩, hx, rfl⟩))
  have hgx : (g : MulAut V)⁻¹ * x ∈ centSub 𝐔 := by
    have h0 : resHom 𝐔 (g⁻¹ * ⟨x, hxs⟩) = 1 := by
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have h1 : (g⁻¹ * ⟨x, hxs⟩ : stabSub 𝐔) ∈ (resHom 𝐔).ker := h0
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hgK0 : (g : MulAut V) ∈ conjClosure K T := hK'' hgK''
  have hmem : (g : MulAut V)⁻¹ * x ∈ conjClosure K T :=
    (conjClosure K T).mul_mem ((conjClosure K T).inv_mem hgK0) (hK' hx)
  have h1 := h.eq_one_of_mem_centSub hmem hgx
  have hxg : x = g := by
    calc x = (g : MulAut V) * ((g : MulAut V)⁻¹ * x) := by group
      _ = g := by rw [h1, mul_one]
  rw [hxg]
  exact hgK''

omit [Finite V] in
theorem TwelveHyp.odd_mem_autSub (h : TwelveHyp T K) {y : MulAut ↥𝐔}
    (hy : y ∈ autSub (T ⊔ K) 𝐔) (ho : Odd (orderOf y)) :
    y ∈ autSub (conjClosure K T) 𝐔 := by
  obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
  have hg' : (g : MulAut V) ∈ conjClosure K T ⊔ T := sup_le_conjClosure_sup hgH
  obtain ⟨k, hk, t, ht, hgkt⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_conjClosure K T)).1 hg'
  have hks : k ∈ stabSub 𝐔 := (conjClosure_le_sup.trans h.le_stabSub) hk
  have hts : t ∈ stabSub 𝐔 := (le_sup_left.trans h.le_stabSub) ht
  have hgeq : g = ⟨k, hks⟩ * ⟨t, hts⟩ := Subtype.ext hgkt
  have hn : resHom 𝐔 ⟨k, hks⟩ ∈ autSub (conjClosure K T) 𝐔 := mem_autSub.2 ⟨⟨k, hks⟩, hk, rfl⟩
  have hta : resHom 𝐔 ⟨t, hts⟩ ∈
      Subgroup.normalizer ((autSub (conjClosure K T) 𝐔 : Subgroup (MulAut ↥𝐔)) : Set (MulAut ↥𝐔)) := by
    have : autSub T 𝐔 ≤
        Subgroup.normalizer ((autSub (conjClosure K T) 𝐔 : Subgroup (MulAut ↥𝐔)) : Set (MulAut ↥𝐔)) :=
      le_normalizer_of_conj fun φ hφ ψ hψ => autSub_conj_mem
        (fun x hx y hy => B19Aux.conj_mem_of_le_normalizer (le_normalizer_conjClosure K T) hx hy)
        hφ hψ
    exact this (mem_autSub.2 ⟨⟨t, hts⟩, ht, rfl⟩)
  obtain ⟨j, hj⟩ := h.two ⟨t, ht⟩
  have htj : resHom 𝐔 ⟨t, hts⟩ ^ 2 ^ j = 1 := by
    have : (⟨t, hts⟩ : stabSub 𝐔) ^ 2 ^ j = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hj)
    rw [← map_pow, this, map_one]
  have hprod : resHom 𝐔 g = resHom 𝐔 ⟨k, hks⟩ * resHom 𝐔 ⟨t, hts⟩ := by
    rw [hgeq, map_mul]
  rw [hprod] at ho ⊢
  exact mul_mem_of_odd_orderOf hn hta htj ho


theorem TwelveHyp.exists_blk_eq (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) {G : Subgroup (MulAut ↥𝐔)} (hG : G ∈ 𝓗) :
    ∃ K' ∈ conjSetUnder T K, blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) = G := by
  have hdata : ∀ {K' : Subgroup (MulAut V)}, K' ∈ conjSetUnder T K →
      blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ∈ 𝓗 ∧
        autSub K' 𝐔 = oddCoreOfSub (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔)) ∧
        blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ≤ autSub (twelveM T K) 𝐔 :=
    fun hK' => h.exists_blockOf hB.blocks hB.offenders hK'
  have hle : oddCoreOfSub G ≤ ⨆ i : conjSetUnder T K,
      oddCoreOfSub (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔)) := by
    intro y hy
    obtain ⟨hyG, hy3⟩ := (hB.blocks.mem_oddCoreOfSub_iff_of_mem hG).1 hy
    have hyX : y ∈ autSub (T ⊔ K) 𝐔 := B6.ffJ_le _ (hB.blocks.le_J hG hyG)
    have hodd : Odd (orderOf y) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3)
    have hyK0 := h.odd_mem_autSub hyX hodd
    have hsub : autSub (conjClosure K T) 𝐔 ≤ ⨆ i : conjSetUnder T K, autSub i.1 𝐔 := by
      refine autSub_le_of_le_preimageAut (H₀ := T ⊔ K) ?_
      rw [conjClosure_eq_iSup]
      refine iSup_le fun i g hgi => ?_
      have hiH : i.1 ≤ T ⊔ K :=
        (le_conjClosure_of_mem_conjSetUnder i.2).trans conjClosure_le_sup
      have hgs : g ∈ stabSub 𝐔 := h.le_stabSub (hiH hgi)
      exact mem_preimageAut.2 ⟨hiH hgi, hgs,
        Subgroup.mem_iSup_of_mem i (mem_autSub.2 ⟨⟨g, hgs⟩, hgi, rfl⟩)⟩
    have hy' := hsub hyK0
    have heq : (⨆ i : conjSetUnder T K, autSub i.1 𝐔) = ⨆ i : conjSetUnder T K,
        oddCoreOfSub (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔)) :=
      iSup_congr fun i => (hdata i.2).2.1
    rwa [heq] at hy'
  obtain ⟨i, hi⟩ := hB.blocks.exists_eq_of_oddCoreOfSub_le_iSup hG
    (fun i : conjSetUnder T K => blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔))
    (fun i => (hdata i.2).1) hle
  exact ⟨i.1, i.2, hi⟩

theorem TwelveHyp.autSub_twelveM_eq (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) :
    autSub (twelveM T K) 𝐔 = ffJ (autSub (T ⊔ K) 𝐔) := by
  apply le_antisymm
  · refine autSub_le_of_le_preimageAut (H₀ := T ⊔ K) ?_
    unfold twelveM
    refine sup_le ?_ ?_
    · intro g hg
      have hgH : g ∈ T ⊔ K := (le_sup_left : T ≤ T ⊔ K) ((B6.ffJ_le T) hg)
      have hgs := h.le_stabSub hgH
      exact mem_preimageAut.2 ⟨hgH, hgs, h.autSub_ffJ_le (mem_autSub.2 ⟨⟨g, hgs⟩, hg, rfl⟩)⟩
    · rw [conjClosure_eq_iSup]
      refine iSup_le fun i g hgi => ?_
      have hiH : i.1 ≤ T ⊔ K :=
        (le_conjClosure_of_mem_conjSetUnder i.2).trans conjClosure_le_sup
      have hgs : g ∈ stabSub 𝐔 := h.le_stabSub (hiH hgi)
      exact mem_preimageAut.2 ⟨hiH hgi, hgs,
        h.autSub_le_ffJ i.2 (mem_autSub.2 ⟨⟨g, hgs⟩, hgi, rfl⟩)⟩
  · rw [← hB.blocks.iSup_eq]
    refine iSup₂_le fun G hG => ?_
    obtain ⟨K', hK', hblk⟩ := h.exists_blk_eq hB hG
    rw [← hblk]
    exact (h.exists_blockOf hB.blocks hB.offenders hK').2.2

theorem TwelveHyp.blk_injective (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) {K' K'' : Subgroup (MulAut V)} (hK' : K' ∈ conjSetUnder T K)
    (hK'' : K'' ∈ conjSetUnder T K)
    (hblk : blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) =
      blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K'' 𝐔)) : K' = K'' := by
  have h1 : autSub K' 𝐔 = autSub K'' 𝐔 := by
    rw [(h.exists_blockOf hB.blocks hB.offenders hK').2.1,
      (h.exists_blockOf hB.blocks hB.offenders hK'').2.1, hblk]
  exact le_antisymm
    (h.le_of_autSub_le (le_conjClosure_of_mem_conjSetUnder hK') (le_conjClosure_of_mem_conjSetUnder hK'') h1.le)
    (h.le_of_autSub_le (le_conjClosure_of_mem_conjSetUnder hK'') (le_conjClosure_of_mem_conjSetUnder hK') h1.ge)

theorem TwelveHyp.isInnerDirectProduct (h : TwelveHyp T K) :
    IsInnerDirectProduct (fun K' : conjSetUnder T K => (K' : Subgroup (MulAut V)))
      (conjClosure K T) := by
  obtain ⟨𝓗, hB⟩ := h.exists_twelveBlocks
  have hdata : ∀ {K' : Subgroup (MulAut V)}, K' ∈ conjSetUnder T K →
      blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ∈ 𝓗 ∧
        autSub K' 𝐔 = oddCoreOfSub (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔)) ∧
        blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub K' 𝐔) ≤ autSub (twelveM T K) 𝐔 :=
    fun hK' => h.exists_blockOf hB.blocks hB.offenders hK'
  have hKH : ∀ i : conjSetUnder T K, (i : Subgroup (MulAut V)) ≤ T ⊔ K := fun i =>
    (le_conjClosure_of_mem_conjSetUnder i.2).trans conjClosure_le_sup
  have hmem : ∀ (i : conjSetUnder T K) {a : MulAut V} (ha : a ∈ (i : Subgroup (MulAut V)))
      (has : a ∈ stabSub 𝐔), resHom 𝐔 ⟨a, has⟩ ∈
        blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔) := fun i a ha has =>
    oddCoreOfSub_le _ ((hdata i.2).2.1 ▸ mem_autSub.2 ⟨⟨a, has⟩, ha, rfl⟩)
  refine ⟨?_, ?_, conjClosure_eq_iSup.symm⟩
  · intro i j hij a ha b hb
    have hbl : blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔) ≠
        blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub j.1 𝐔) := fun e =>
      hij (Subtype.ext (h.blk_injective hB i.2 j.2 e))
    have has : a ∈ stabSub 𝐔 := h.le_stabSub (hKH i ha)
    have hbs : b ∈ stabSub 𝐔 := h.le_stabSub (hKH j hb)
    exact h.comm_of_resHom_comm (le_conjClosure_of_mem_conjSetUnder i.2 ha)
      (le_conjClosure_of_mem_conjSetUnder j.2 hb) has hbs
      (hB.blocks.comm _ (hdata i.2).1 _ (hdata j.2).1 hbl _ (hmem i ha has) _ (hmem j hb hbs))
  · unfold iSupIndep
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxs
    have hxK0 : x ∈ conjClosure K T := le_conjClosure_of_mem_conjSetUnder i.2 hxi
    have hxst : x ∈ stabSub 𝐔 := h.le_stabSub (hKH i hxi)
    have hRle : (⨆ j : conjSetUnder T K, ⨆ (_ : j ≠ i), (j : Subgroup (MulAut V))) ≤
        preimageAut (T ⊔ K) 𝐔 (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ blockOf (ffJ (autSub (T ⊔ K) 𝐔))
          (autSub i.1 𝐔)), H') := by
      refine iSup₂_le fun j hji g hgj => ?_
      have hgs : g ∈ stabSub 𝐔 := h.le_stabSub (hKH j hgj)
      refine mem_preimageAut.2 ⟨hKH j hgj, hgs, ?_⟩
      have hne : blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub j.1 𝐔) ≠
          blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔) := fun e =>
        hji (Subtype.ext (h.blk_injective hB j.2 i.2 e))
      exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut ↥𝐔)) (_ : H' ∈ 𝓗) =>
        ⨆ (_ : H' ≠ blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔)), H')
        (blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub j.1 𝐔)) (hdata j.2).1
        (le_iSup (fun _ : blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub j.1 𝐔) ≠
          blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔) =>
          blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub j.1 𝐔)) hne) (hmem j hgj hgs)
    obtain ⟨-, hxs', hxR⟩ := mem_preimageAut.1 (hRle hxs)
    have hbot : resHom 𝐔 ⟨x, hxs'⟩ ∈ blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔) ⊓
        ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ blockOf (ffJ (autSub (T ⊔ K) 𝐔)) (autSub i.1 𝐔)), H' :=
      ⟨hmem i hxi hxs', hxR⟩
    rw [hB.blocks.inf_biSup_ne_eq_bot (hdata i.2).1, Subgroup.mem_bot] at hbot
    have hxc : x ∈ centSub 𝐔 := by
      have : (⟨x, hxs'⟩ : stabSub 𝐔) ∈ (resHom 𝐔).ker := hbot
      rw [ker_resHom, Subgroup.mem_subgroupOf] at this
      exact this
    exact h.eq_one_of_mem_centSub hxK0 hxc

omit [Finite V] in
theorem TwelveHyp.ffJ_le_normalizer_conjClosure (h : TwelveHyp T K) :
    ffJ T ≤ Subgroup.normalizer (conjClosure K T : Set (MulAut V)) := by
  refine le_normalizer_of_conj fun a ha x hx => ?_
  have hle : conjClosure K T ≤ (conjClosure K T).comap (MulAut.conj a).toMonoidHom := by
    refine conjClosure_le fun t ht z hz => ?_
    have hK' : K.map (MulAut.conj t).toMonoidHom ∈ conjSetUnder T K := ⟨t, ht, rfl⟩
    have hmem : t * z * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have := conj_mem_of_commutator_eq (h.comm_of_mem hK') ha hmem
    exact le_conjClosure_of_mem_conjSetUnder hK' this
  exact hle hx

omit [Finite V] in
theorem TwelveHyp.mem_normalizer_twelveM (h : TwelveHyp T K) {t m : MulAut V} (ht : t ∈ T)
    (hm : m ∈ twelveM T K) : t * m * t⁻¹ ∈ twelveM T K := by
  unfold twelveM at hm ⊢
  rw [sup_comm] at hm ⊢
  exact conj_mem_sup_of_conj_mem h.ffJ_le_normalizer_conjClosure
    (fun y hy => B19Aux.conj_mem_of_le_normalizer (le_normalizer_conjClosure K T) ht hy)
    (fun z hz => (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ T ht) z).mp hz) m hm

end Blocks

end B1Red

end CFSG.Quasithin
