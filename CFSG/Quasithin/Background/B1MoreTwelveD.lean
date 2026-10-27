module

public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreTwelveA
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

section Defs

variable {V : Type*} [CommGroup V]

@[expose] def conjSetUnder (T K : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {K' | ∃ t ∈ T, K' = K.map (MulAut.conj t).toMonoidHom}

@[expose] def twelveM (T K : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ffJ T ⊔ conjClosure K T

end Defs

namespace B1Red

section Hyp

variable {V : Type*} [CommGroup V]

structure TwelveHyp (T K : Subgroup (MulAut V)) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  two : IsPGroup 2 T
  card : Nat.card ↥K = 3
  comm : ⁅K, ffJ T⁆ = K
  sub : IsSubnormal K (T ⊔ K)

theorem map_conj_eq_self_of_mem_normalizer {Ω : Type*} [Group Ω] {J : Subgroup Ω} {t : Ω}
    (ht : t ∈ Subgroup.normalizer (J : Set Ω)) : J.map (MulAut.conj t).toMonoidHom = J := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ht x).mp hx
  · intro hy
    refine ⟨t⁻¹ * y * t, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (J : Set Ω)).inv_mem ht) y).mp hy
    simpa using this

variable {T K : Subgroup (MulAut V)}

theorem le_conjClosure_of_mem_conjSetUnder {K' : Subgroup (MulAut V)}
    (hK' : K' ∈ conjSetUnder T K) : K' ≤ conjClosure K T := by
  obtain ⟨t, ht, rfl⟩ := hK'
  rintro _ ⟨z, hz, rfl⟩
  simpa [MulAut.conj_apply] using mem_conjClosure ht hz

theorem self_mem_conjSetUnder (hT : (1 : MulAut V) ∈ T) : K ∈ conjSetUnder T K := by
  refine ⟨1, hT, ?_⟩
  ext y
  simp [Subgroup.mem_map]

theorem map_conj_mem_conjSetUnder {K' : Subgroup (MulAut V)} (hK' : K' ∈ conjSetUnder T K)
    {t : MulAut V} (ht : t ∈ T) : K'.map (MulAut.conj t).toMonoidHom ∈ conjSetUnder T K := by
  obtain ⟨s, hs, rfl⟩ := hK'
  refine ⟨t * s, T.mul_mem ht hs, ?_⟩
  rw [Subgroup.map_map]
  congr 1

theorem conjClosure_eq_iSup : conjClosure K T = ⨆ K' : conjSetUnder T K, (K' : Subgroup (MulAut V)) := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have hmem : K.map (MulAut.conj h).toMonoidHom ∈ conjSetUnder T K := ⟨h, hh, rfl⟩
    exact le_iSup (fun K' : conjSetUnder T K => (K' : Subgroup (MulAut V))) ⟨_, hmem⟩
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · exact iSup_le fun K' => le_conjClosure_of_mem_conjSetUnder K'.2

theorem TwelveHyp.card_of_mem (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ∈ conjSetUnder T K) : Nat.card ↥K' = 3 := by
  obtain ⟨t, ht, rfl⟩ := hK'
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, h.card]

theorem TwelveHyp.comm_of_mem (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ∈ conjSetUnder T K) : ⁅K', ffJ T⁆ = K' := by
  obtain ⟨t, ht, rfl⟩ := hK'
  have hn : t ∈ Subgroup.normalizer (ffJ T : Set (MulAut V)) := B6.le_normalizer_ffJ T ht
  calc ⁅K.map (MulAut.conj t).toMonoidHom, ffJ T⁆
      = ⁅K.map (MulAut.conj t).toMonoidHom, (ffJ T).map (MulAut.conj t).toMonoidHom⁆ := by
        rw [map_conj_eq_self_of_mem_normalizer hn]
    _ = (⁅K, ffJ T⁆).map (MulAut.conj t).toMonoidHom := (Subgroup.map_commutator _ _ _).symm
    _ = K.map (MulAut.conj t).toMonoidHom := by rw [h.comm]

theorem TwelveHyp.le_stabSub (_h : TwelveHyp T K) :
    T ⊔ K ≤ stabSub (fixV (pCoreOf 2 (T ⊔ K))) :=
  le_stabSub_fixV_pCoreOf (T ⊔ K)

theorem autSub_le_of_le_preimageAut {H₀ Y : Subgroup (MulAut V)} {U : Subgroup V}
    {S : Subgroup (MulAut ↥U)} (hY : Y ≤ preimageAut H₀ U S) : autSub Y U ≤ S := by
  intro ψ hψ
  obtain ⟨g, hgY, rfl⟩ := mem_autSub.1 hψ
  obtain ⟨-, hg, hmem⟩ := mem_preimageAut.1 (hY hgY)
  exact hmem

variable [Finite V]

theorem TwelveHyp.ker_eq (h : TwelveHyp T K) :
    (T ⊔ K) ⊓ centSub (fixV (pCoreOf 2 (T ⊔ K))) = pCoreOf 2 (T ⊔ K) :=
  kernel_eq_pCoreOf h.sq (fun _ hx ho => odd_mem_conjClosure h.two hx ho)
    (commute_conjClosure_pCoreOf h.card h.sub)

theorem TwelveHyp.eq_one_of_mem_centSub (h : TwelveHyp T K) {x : MulAut V}
    (hx : x ∈ conjClosure K T) (hc : x ∈ centSub (fixV (pCoreOf 2 (T ⊔ K)))) : x = 1 := by
  have hxQ : x ∈ pCoreOf 2 (T ⊔ K) := by
    rw [← h.ker_eq]
    exact ⟨conjClosure_le_sup hx, hc⟩
  have := conjClosure_inf_pCoreOf h.card h.sub
  have hmem : x ∈ conjClosure K T ⊓ pCoreOf 2 (T ⊔ K) := ⟨hx, hxQ⟩
  rwa [this, Subgroup.mem_bot] at hmem

theorem TwelveHyp.inf_centSub_eq_bot (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ≤ conjClosure K T) : K' ⊓ centSub (fixV (pCoreOf 2 (T ⊔ K))) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hx => h.eq_one_of_mem_centSub (hK' hx.1) hx.2

theorem TwelveHyp.card_autSub (h : TwelveHyp T K) {K' : Subgroup (MulAut V)}
    (hK' : K' ≤ conjClosure K T) :
    Nat.card ↥(autSub K' (fixV (pCoreOf 2 (T ⊔ K)))) = Nat.card ↥K' := by
  have h1 := card_autSub_mul (U := fixV (pCoreOf 2 (T ⊔ K)))
    (hK'.trans (conjClosure_le_sup.trans h.le_stabSub))
  rw [h.inf_centSub_eq_bot hK', Subgroup.card_bot, mul_one] at h1
  exact h1

theorem TwelveHyp.isSolvable_autSub (h : TwelveHyp T K) :
    Group.IsSolvable ↥(autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K)))) := by
  have hS : Group.IsSolvable ↥(T ⊔ K) := isSolvable_sup h.two h.card h.sub
  rw [autSub_eq_range h.le_stabSub]
  exact Group.isSolvable_of_surjective
    (((resHom (fixV (pCoreOf 2 (T ⊔ K)))).comp (Subgroup.inclusion h.le_stabSub)).rangeRestrict_surjective)

theorem TwelveHyp.normal_two_autSub (h : TwelveHyp T K) :
    ∀ Q : Subgroup (MulAut ↥(fixV (pCoreOf 2 (T ⊔ K)))),
      Q ≤ autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K))) → (Q.subgroupOf
        (autSub (T ⊔ K) (fixV (pCoreOf 2 (T ⊔ K))))).Normal → IsPGroup 2 Q → Q = ⊥ :=
  normal_two_subgroups_trivial_of_pCoreOf_eq_bot (pCoreOf_autSub_eq_bot h.ker_eq)

end Hyp

end B1Red

end CFSG.Quasithin
