module

public import CFSG.Quasithin.Background.AutSubConj
public import CFSG.Quasithin.Background.B1MoreTwelveG

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

section Statement

variable {V : Type*} [CommGroup V]

@[expose] def B112Conclusion (T K : Subgroup (MulAut V)) : Prop :=
  IsInnerDirectProduct (fun K' : conjSetUnder T K => (K' : Subgroup (MulAut V)))
      (conjClosure K T) ∧
    (∀ t ∈ T, ∀ m ∈ twelveM T K, t * m * t⁻¹ ∈ twelveM T K) ∧
    (∀ t ∈ T, ∀ i : conjSetUnder T K, ∃ j : conjSetUnder T K,
      j.1 = i.1.map (MulAut.conj t).toMonoidHom) ∧
    (∀ i j : conjSetUnder T K, ∃ t ∈ T, j.1 = i.1.map (MulAut.conj t).toMonoidHom) ∧
    ∃ Mb : conjSetUnder T K → Subgroup (SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K))),
      IsInnerDirectProduct Mb ⊤ ∧
      (∀ i, Nonempty (↥(Mb i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
      (∀ i, secImg (twelveM T K) (pCoreOf 2 (twelveM T K)) i.1 = oddCoreOfSub (Mb i)) ∧
      ∀ t ∈ T, ∀ i j : conjSetUnder T K, j.1 = i.1.map (MulAut.conj t).toMonoidHom →
        ∀ x y : ↥(twelveM T K), (y : MulAut V) = t * x * t⁻¹ →
          (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x ∈ Mb i ↔
            secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y ∈ Mb j)

end Statement

namespace B1Red

section Conj

variable {V : Type*} [CommGroup V]

set_option linter.unusedVariables false in
theorem autSub_map_conj {U : Subgroup V} {Y : Subgroup (MulAut V)} (hY : Y ≤ stabSub U)
    {t : MulAut V} (ht : t ∈ stabSub U) :
    autSub (Y.map (MulAut.conj t).toMonoidHom) U =
      (autSub Y U).map (MulAut.conj (resHom U ⟨t, ht⟩)).toMonoidHom :=
  CFSG.Quasithin.StabLat.autSub_map_conj_eq ht

theorem conj_mem_map_conj_iff {Ω : Type*} [Group Ω] (S : Subgroup Ω) (g z : Ω) :
    g * z * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom ↔ z ∈ S := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = z := by
      have h1 : g * w * g⁻¹ = g * z * g⁻¹ := by simpa [MulAut.conj_apply] using hwz
      exact mul_left_cancel (mul_right_cancel h1)
    rw [← this]
    exact hw
  · intro hz
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩

end Conj

section Final

variable {V : Type*} [CommGroup V] [Finite V] {T K : Subgroup (MulAut V)}

local notation "𝐔" => fixV (pCoreOf 2 (T ⊔ K))

@[expose] def twelveBlk (T K K' : Subgroup (MulAut V)) :
    Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))) :=
  blockOf (ffJ (autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K)))))
    (autSub K' (fixV (pCoreOf 2 (T ⊔ K))))

theorem TwelveHyp.twelveBlk_data (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗)
    {K' : Subgroup (MulAut V)} (hK' : K' ∈ conjSetUnder T K) :
    twelveBlk T K K' ∈ 𝓗 ∧ autSub K' 𝐔 = oddCoreOfSub (twelveBlk T K K') ∧
      twelveBlk T K K' ≤ autSub (twelveM T K) 𝐔 :=
  h.exists_blockOf hB.blocks hB.offenders hK'

theorem TwelveHyp.twelveBlk_comm (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗)
    {i j : conjSetUnder T K} (hij : i ≠ j) :
    ∀ a ∈ twelveBlk T K i.1, ∀ b ∈ twelveBlk T K j.1, a * b = b * a := fun a ha b hb =>
  hB.blocks.comm _ (h.twelveBlk_data hB i.2).1 _ (h.twelveBlk_data hB j.2).1
    (fun e => hij (Subtype.ext (h.blk_injective hB i.2 j.2 e))) a ha b hb

theorem TwelveHyp.twelveBlk_iSupIndep (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) :
    iSupIndep (fun i : conjSetUnder T K => twelveBlk T K i.1) := by
  unfold iSupIndep
  intro i
  rw [Subgroup.disjoint_def]
  intro x hxi hxs
  have hRle : (⨆ j : conjSetUnder T K, ⨆ (_ : j ≠ i), twelveBlk T K j.1) ≤
      ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ twelveBlk T K i.1), H' := by
    refine iSup₂_le fun j hji => ?_
    have hne : twelveBlk T K j.1 ≠ twelveBlk T K i.1 := fun e =>
      hji (Subtype.ext (h.blk_injective hB j.2 i.2 e))
    exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut ↥𝐔)) (_ : H' ∈ 𝓗) =>
      ⨆ (_ : H' ≠ twelveBlk T K i.1), H') (twelveBlk T K j.1) (h.twelveBlk_data hB j.2).1
      (le_iSup (fun _ : twelveBlk T K j.1 ≠ twelveBlk T K i.1 => twelveBlk T K j.1) hne)
  have hmem : x ∈ twelveBlk T K i.1 ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ twelveBlk T K i.1), H' :=
    ⟨hxi, hRle hxs⟩
  rw [hB.blocks.inf_biSup_ne_eq_bot (h.twelveBlk_data hB i.2).1, Subgroup.mem_bot] at hmem
  exact hmem

theorem TwelveHyp.iSup_twelveBlk (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) :
    ⨆ i : conjSetUnder T K, twelveBlk T K i.1 = ffJ (autSub (T ⊔ K) 𝐔) := by
  apply le_antisymm
  · exact iSup_le fun i => hB.blocks.le_J (h.twelveBlk_data hB i.2).1
  · rw [← hB.blocks.iSup_eq]
    refine iSup₂_le fun G hG => ?_
    obtain ⟨K', hK', hblk⟩ := h.exists_blk_eq hB hG
    rw [← hblk]
    exact le_iSup (fun i : conjSetUnder T K => twelveBlk T K i.1) ⟨K', hK'⟩

omit [Finite V] in
theorem TwelveHyp.twelveBlk_conj (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ≤ T ⊔ K) {t : MulAut V} (ht : t ∈ T) (hts : t ∈ stabSub 𝐔) :
    twelveBlk T K (K'.map (MulAut.conj t).toMonoidHom) =
      (twelveBlk T K K').map (MulAut.conj (resHom 𝐔 ⟨t, hts⟩)).toMonoidHom := by
  unfold twelveBlk
  rw [autSub_map_conj (hK'.trans h.le_stabSub) hts]
  have hxX : resHom 𝐔 ⟨t, hts⟩ ∈ autSub (T ⊔ K) 𝐔 :=
    mem_autSub.2 ⟨⟨t, hts⟩, (le_sup_left : T ≤ T ⊔ K) ht, rfl⟩
  refine blockOf_map_conj (fun j hj => ?_) (fun j hj => ?_)
  · exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ hxX) j).mp hj
  · have := (Subgroup.mem_normalizer_iff.mp
      (B6.le_normalizer_ffJ _ ((autSub (T ⊔ K) 𝐔).inv_mem hxX)) j).mp hj
    simpa using this

theorem TwelveHyp.nonempty_comap (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗)
    {E : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)) →* MulAut ↥𝐔}
    (hEinj : Function.Injective E) (hErange : E.range = ffJ (autSub (T ⊔ K) 𝐔))
    (i : conjSetUnder T K) :
    Nonempty (↥((twelveBlk T K i.1).comap E) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  have hV' : ∀ w : ↥𝐔, w ^ 2 = 1 := B1.sq_eq_one_sub h.sq 𝐔
  obtain ⟨e₁⟩ := nonempty_comap_mulEquiv E hEinj (twelveBlk T K i.1)
    (by rw [hErange]; exact hB.blocks.le_J (h.twelveBlk_data hB i.2).1)
  obtain ⟨e₂⟩ := hB.blocks.nonempty_mulEquiv_sl2 hV' (h.twelveBlk_data hB i.2).1
  exact ⟨e₁.trans e₂⟩

theorem TwelveHyp.secImg_eq (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗)
    {E : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)) →* MulAut ↥𝐔}
    (hEinj : Function.Injective E)
    (hEmk : ∀ x : ↥(twelveM T K),
      E (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x) = twelveRes T K x)
    (hErange : E.range = ffJ (autSub (T ⊔ K) 𝐔)) (i : conjSetUnder T K) :
    secImg (twelveM T K) (pCoreOf 2 (twelveM T K)) i.1 =
      oddCoreOfSub ((twelveBlk T K i.1).comap E) := by
  have hKM : i.1 ≤ twelveM T K :=
    (le_conjClosure_of_mem_conjSetUnder i.2).trans (le_sup_right : conjClosure K T ≤ twelveM T K)
  have hcard : Nat.card ↥((twelveBlk T K i.1).comap E) = 6 := by
    obtain ⟨e⟩ := nonempty_comap_mulEquiv E hEinj (twelveBlk T K i.1)
      (by rw [hErange]; exact hB.blocks.le_J (h.twelveBlk_data hB i.2).1)
    rw [Nat.card_congr e.toEquiv]
    exact hB.blocks.card_eq _ (h.twelveBlk_data hB i.2).1
  ext y
  rw [mem_oddCoreOfSub_iff_of_card_six hcard, Subgroup.mem_comap]
  have hE3 : y ^ 3 = 1 ↔ E y ^ 3 = 1 := by
    rw [← map_pow]
    exact ⟨fun h1 => by rw [h1, map_one], fun h1 => hEinj (by rw [h1, map_one])⟩
  rw [hE3, mem_secImg]
  constructor
  · rintro ⟨x, hxK, rfl⟩
    have hEx : E (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x) ∈ autSub i.1 𝐔 := by
      rw [hEmk, twelveRes_apply]
      exact mem_autSub.2 ⟨⟨(x : MulAut V), twelveM_le_stab x.2⟩, hxK, rfl⟩
    rw [(h.twelveBlk_data hB i.2).2.1,
      hB.blocks.mem_oddCoreOfSub_iff_of_mem (h.twelveBlk_data hB i.2).1] at hEx
    exact hEx
  · rintro ⟨hyB, hy3⟩
    have hyO : E y ∈ autSub i.1 𝐔 := by
      rw [(h.twelveBlk_data hB i.2).2.1,
        hB.blocks.mem_oddCoreOfSub_iff_of_mem (h.twelveBlk_data hB i.2).1]
      exact ⟨hyB, hy3⟩
    obtain ⟨g, hgK, hg⟩ := mem_autSub.1 hyO
    refine ⟨⟨(g : MulAut V), hKM hgK⟩, hgK, hEinj ?_⟩
    rw [hEmk, twelveRes_apply]
    exact hg

omit [Finite V] in
theorem TwelveHyp.equivariance (h : TwelveHyp T K)
    {E : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)) →* MulAut ↥𝐔}
    (hEmk : ∀ x : ↥(twelveM T K),
      E (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x) = twelveRes T K x) :
    ∀ t ∈ T, ∀ i j : conjSetUnder T K, j.1 = i.1.map (MulAut.conj t).toMonoidHom →
      ∀ x y : ↥(twelveM T K), (y : MulAut V) = t * x * t⁻¹ →
        (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x ∈ (twelveBlk T K i.1).comap E ↔
          secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y ∈ (twelveBlk T K j.1).comap E) := by
  intro t ht i j hij x y hxy
  have hts : t ∈ stabSub 𝐔 := h.le_stabSub ((le_sup_left : T ≤ T ⊔ K) ht)
  have hEq : twelveRes T K y =
      resHom 𝐔 ⟨t, hts⟩ * twelveRes T K x * (resHom 𝐔 ⟨t, hts⟩)⁻¹ := by
    rw [twelveRes_apply, twelveRes_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxy
  have hblk : twelveBlk T K j.1 =
      (twelveBlk T K i.1).map (MulAut.conj (resHom 𝐔 ⟨t, hts⟩)).toMonoidHom := by
    rw [hij]
    exact h.twelveBlk_conj ((le_conjClosure_of_mem_conjSetUnder i.2).trans conjClosure_le_sup) ht hts
  rw [Subgroup.mem_comap, Subgroup.mem_comap, hEmk, hEmk, hEq, hblk]
  exact (conj_mem_map_conj_iff (twelveBlk T K i.1) (resHom 𝐔 ⟨t, hts⟩) (twelveRes T K x)).symm

theorem TwelveHyp.conclusion (h : TwelveHyp T K) : B112Conclusion T K := by
  obtain ⟨𝓗, hB⟩ := h.exists_twelveBlocks
  obtain ⟨E, hEinj, hEmk, hErange⟩ := h.exists_embedding hB
  have hsup : ⨆ i : conjSetUnder T K, twelveBlk T K i.1 = E.range := by
    rw [h.iSup_twelveBlk hB, hErange]
  have hIDP : IsInnerDirectProduct (fun i : conjSetUnder T K => (twelveBlk T K i.1).comap E) ⊤ :=
    isInnerDirectProduct_comap_top E hEinj (fun i : conjSetUnder T K => twelveBlk T K i.1)
      (fun i j hij => h.twelveBlk_comm hB hij) (h.twelveBlk_iSupIndep hB) hsup
  have hnon := fun i : conjSetUnder T K => h.nonempty_comap hB hEinj hErange i
  have hsec := fun i : conjSetUnder T K => h.secImg_eq hB hEinj hEmk hErange i
  have heq := h.equivariance hEmk
  exact ⟨h.isInnerDirectProduct, fun t ht m hm => h.mem_normalizer_twelveM ht hm,
    fun t ht i => ⟨⟨_, map_conj_mem_conjSetUnder i.2 ht⟩, rfl⟩,
    fun i j => by
      obtain ⟨s, hs, hsi⟩ := i.2
      obtain ⟨u, hu, hui⟩ := j.2
      refine ⟨u * s⁻¹, T.mul_mem hu (T.inv_mem hs), ?_⟩
      rw [hui, hsi, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc],
    fun i => (twelveBlk T K i.1).comap E, hIDP, hnon, hsec, heq⟩

end Final

end B1Red

theorem B1_12 {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G T K : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G)
    (hK3 : Nat.card ↥K = 3) (hKJ : ⁅K, ffJ T⁆ = K)
    (hsub : CFSG.Open.IsSubnormal K (T ⊔ K)) : B112Conclusion T K :=
  B1Red.TwelveHyp.conclusion ⟨hV, hT.2.1, hK3, hKJ, hsub⟩

end CFSG.Quasithin
