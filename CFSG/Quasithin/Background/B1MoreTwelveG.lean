module

public import CFSG.Quasithin.Background.B1MoreTwelveF

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section Abstract

variable {A Γ ι : Type*} [Group A] [Group Γ]

theorem isInnerDirectProduct_comap_top (E : A →* Γ) (hE : Function.Injective E)
    (G : ι → Subgroup Γ) (hcomm : ∀ i j, i ≠ j → ∀ a ∈ G i, ∀ b ∈ G j, a * b = b * a)
    (hind : iSupIndep G) (hsup : ⨆ i, G i = E.range) :
    IsInnerDirectProduct (fun i => (G i).comap E) ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    apply hE
    rw [map_mul, map_mul]
    exact hcomm i j hij _ ha _ hb
  · unfold iSupIndep
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxs
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (G j).comap E) ≤ (⨆ j, ⨆ (_ : j ≠ i), G j).comap E :=
      iSup₂_le fun j hji => (Subgroup.comap_mono (le_iSup₂_of_le j hji le_rfl))
    have hxE : E x ∈ ⨆ j, ⨆ (_ : j ≠ i), G j := hle hxs
    have h1 : E x = 1 := Subgroup.disjoint_def.1 (hind i) (Subgroup.mem_comap.1 hxi) hxE
    exact hE (by rw [h1, map_one])
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : E x ∈ ⨆ i, G i := by rw [hsup]; exact ⟨x, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := Subgroup.iSup_induction G (C := fun y => ∃ x' ∈ ⨆ i, (G i).comap E,
      E x' = y) hx
      (fun i y hy => by
        obtain ⟨a, ha⟩ : y ∈ E.range := hsup ▸ (le_iSup G i) hy
        exact ⟨a, Subgroup.mem_iSup_of_mem i (by rw [Subgroup.mem_comap, ha]; exact hy), ha⟩)
      ⟨1, Subgroup.one_mem _, map_one E⟩
      (fun y z ⟨a, ha, hay⟩ ⟨b, hb, hbz⟩ => ⟨a * b, Subgroup.mul_mem _ ha hb, by
        rw [map_mul, hay, hbz]⟩)
    have : x = x' := hE hxx'.symm
    rw [this]
    exact hx'

theorem nonempty_comap_mulEquiv (E : A →* Γ) (hE : Function.Injective E) (S : Subgroup Γ)
    (hS : S ≤ E.range) : Nonempty (↥(S.comap E) ≃* ↥S) := by
  let f : ↥(S.comap E) →* ↥S := (E.comp (S.comap E).subtype).codRestrict S fun x => x.2
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : E (x : A) = E (y : A) := congrArg Subtype.val hxy
      exact Subtype.ext (hE h1)
    · intro s
      obtain ⟨a, ha⟩ : (s : Γ) ∈ E.range := hS s.2
      exact ⟨⟨a, by rw [Subgroup.mem_comap, ha]; exact s.2⟩, Subtype.ext ha⟩
  exact ⟨MulEquiv.ofBijective f hf⟩

end Abstract

section ModuleM

variable {V : Type*} [CommGroup V] [Finite V] {T K : Subgroup (MulAut V)}

local notation "𝐔" => fixV (pCoreOf 2 (T ⊔ K))

omit [Finite V] in
theorem twelveM_le_sup : twelveM T K ≤ T ⊔ K :=
  sup_le ((B6.ffJ_le T).trans le_sup_left) conjClosure_le_sup

omit [Finite V] in
theorem twelveM_le_stab : twelveM T K ≤ stabSub 𝐔 :=
  twelveM_le_sup.trans (le_stabSub_fixV_pCoreOf (T ⊔ K))

@[expose] def twelveRes (T K : Subgroup (MulAut V)) :
    ↥(twelveM T K) →* MulAut ↥(fixV (pCoreOf 2 (T ⊔ K))) :=
  (resHom (fixV (pCoreOf 2 (T ⊔ K)))).comp (Subgroup.inclusion twelveM_le_stab)

omit [Finite V] in
theorem twelveRes_apply (x : ↥(twelveM T K)) :
    twelveRes T K x = resHom 𝐔 ⟨(x : MulAut V), twelveM_le_stab x.2⟩ := rfl

theorem inf_pCoreOf_le_pCoreOf {M H : Subgroup (MulAut V)} (hMH : M ≤ H) :
    M ⊓ pCoreOf 2 H ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((M ⊓ pCoreOf 2 H).subgroupOf M).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun d m hd hm => ?_
    exact ⟨M.mul_mem (M.mul_mem hm hd.1) (M.inv_mem hm), conj_mem_pCoreOf_gen (hMH hm) hd.2⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hn
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)

theorem TwelveHyp.ker_twelveRes (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) :
    (twelveRes T K).ker = (pCoreOf 2 (twelveM T K)).subgroupOf (twelveM T K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hxc : (x : MulAut V) ∈ centSub 𝐔 := by
      have h0 : (⟨(x : MulAut V), twelveM_le_stab x.2⟩ : stabSub 𝐔) ∈ (resHom 𝐔).ker := hx
      rw [ker_resHom, Subgroup.mem_subgroupOf] at h0
      exact h0
    have hxQ : (x : MulAut V) ∈ pCoreOf 2 (T ⊔ K) := by
      rw [← h.ker_eq]
      exact ⟨twelveM_le_sup x.2, hxc⟩
    exact inf_pCoreOf_le_pCoreOf twelveM_le_sup ⟨x.2, hxQ⟩
  · intro hxN
    have hJX : ffJ (autSub (T ⊔ K) 𝐔) ≤ autSub (T ⊔ K) 𝐔 := B6.ffJ_le _
    have hJn : ∀ g ∈ autSub (T ⊔ K) 𝐔, ∀ j ∈ ffJ (autSub (T ⊔ K) 𝐔),
        g * j * g⁻¹ ∈ ffJ (autSub (T ⊔ K) 𝐔) := fun g hg j hj =>
      (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ hg) j).mp hj
    have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX hJn h.normal_two_autSub
    have hQmJ : autSub (pCoreOf 2 (twelveM T K)) 𝐔 ≤ ffJ (autSub (T ⊔ K) 𝐔) :=
      (autSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 (twelveM T K)) 𝐔).trans
        (h.autSub_twelveM_eq hB).le
    have hQmn : ((autSub (pCoreOf 2 (twelveM T K)) 𝐔).subgroupOf
        (ffJ (autSub (T ⊔ K) 𝐔))).Normal := by
      refine (Subgroup.normal_subgroupOf_iff hQmJ).2 fun q j hq hj => ?_
      have hjM : j ∈ autSub (twelveM T K) 𝐔 := (h.autSub_twelveM_eq hB).symm ▸ hj
      exact autSub_conj_mem (X := twelveM T K) (Y := pCoreOf 2 (twelveM T K))
        (fun a ha b hb => conj_mem_pCoreOf_gen ha hb) hjM hq
    have hQm2 : IsPGroup 2 ↥(autSub (pCoreOf 2 (twelveM T K)) 𝐔) := by
      intro y
      obtain ⟨g, hgN, hg⟩ := mem_autSub.1 y.2
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (twelveM T K))
        ⟨(g : MulAut V), hgN⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      have hk' : (g : MulAut V) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hgk : g ^ 2 ^ k = 1 := Subtype.ext hk'
      show (y : MulAut ↥𝐔) ^ 2 ^ k = 1
      rw [← hg, ← map_pow, hgk, map_one]
    have hbot := hOJ _ hQmJ hQmn hQm2
    have hmem : resHom 𝐔 ⟨(x : MulAut V), twelveM_le_stab x.2⟩ ∈
        autSub (pCoreOf 2 (twelveM T K)) 𝐔 :=
      mem_autSub.2 ⟨⟨(x : MulAut V), twelveM_le_stab x.2⟩, hxN, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem

theorem TwelveHyp.exists_embedding (h : TwelveHyp T K) {𝓗 : Finset (Subgroup (MulAut ↥𝐔))}
    (hB : TwelveBlocks T K 𝓗) :
    ∃ E : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)) →* MulAut ↥𝐔,
      Function.Injective E ∧
        (∀ x : ↥(twelveM T K), E (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x) = twelveRes T K x) ∧
        E.range = ffJ (autSub (T ⊔ K) 𝐔) := by
  have hker := h.ker_twelveRes hB
  let E : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)) →* MulAut ↥𝐔 :=
    QuotientGroup.lift ((pCoreOf 2 (twelveM T K)).subgroupOf (twelveM T K)) (twelveRes T K)
      (le_of_eq hker.symm)
  have hEmk : ∀ x : ↥(twelveM T K),
      E (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) x) = twelveRes T K x := fun x => rfl
  refine ⟨E, ?_, hEmk, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : twelveRes T K x = 1 := by rw [← hEmk]; exact hq
    have : x ∈ (twelveRes T K).ker := hx
    rw [hker] at this
    exact (QuotientGroup.eq_one_iff x).2 this
  · rw [← h.autSub_twelveM_eq hB]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [show E (QuotientGroup.mk x) = twelveRes T K x from rfl, twelveRes_apply]
      exact mem_autSub.2 ⟨⟨(x : MulAut V), twelveM_le_stab x.2⟩, x.2, rfl⟩
    · intro hy
      obtain ⟨g, hgM, rfl⟩ := mem_autSub.1 hy
      exact ⟨secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) ⟨(g : MulAut V), hgM⟩, hEmk _⟩

end ModuleM

end B1Red

end CFSG.Quasithin
