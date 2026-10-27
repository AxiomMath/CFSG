module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.F918N0
import CFSG.Quasithin.Background.InternalSecIrr
import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.F918P1
import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin

open CFSG.Open

section Generic

private theorem n7_mul_pow_mem {G : Type*} [Group G] {K : Subgroup G} {k σ : G} (hk : k ∈ K)
    (hσ : σ ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) : ∃ k' ∈ K, (k * σ) ^ n = k' * σ ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', hn⟩ := ih
    have hσn : σ ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hσ n
    have hc : σ ^ n * k * (σ ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hσn k).mp hk
    refine ⟨k' * (σ ^ n * k * (σ ^ n)⁻¹), K.mul_mem hk' hc, ?_⟩
    rw [pow_succ, hn]
    group

private theorem n7_pCoreOf_eq_bot_of_irr {P : Type} [CommGroup P] [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    {G K : Subgroup (MulAut P)} (hKG : K ≤ G) (hn : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hq : CFSG.IsQuasisimple ↥K) (hirr : XMod.IsIrrSec ↥K (⊥ : Subgroup P) ⊤) :
    pCoreOf 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqo := B1Red.isQuasisimple_to_open hq
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hQle : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hnot : ¬ K ≤ pCoreOf 2 G := by
    intro hle
    have hnil := (hQ2.to_le hle).isNilpotent
    have : Group.IsPerfect ↥K := ⟨hqo.1⟩
    have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
    exact Group.IsPerfect.not_isNilpotent ↥K hnil
  have hcomm := B1Red.commute_of_normal_not_le hqo
    (fun n hn' l hl => hn n (hQle hn') l hl)
    (fun l hl n hn' => B1Red.conj_mem_pCoreOf (hKG hl) hn') hnot
  have hodd : Odd (Nat.card ↥(XMod.eqvAut ↥K P)) :=
    InternalSec.odd_card_eqvAut_of_irr hP hirr (InternalSec.exists_noncomm_of_isQuasisimple hq)
  rw [eq_bot_iff]
  intro q hq'
  have hqe : q ∈ XMod.eqvAut ↥K P := by
    intro a p
    exact congrArg (fun f : MulAut P => f p) (hcomm q hq' a a.2)
  obtain ⟨k, hk⟩ := hQ2 ⟨q, hq'⟩
  have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥K P)) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥K P)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_natCard _)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (orderOf_eq_one_iff.1 hord))

end Generic

section Restrict

variable {X : Type} [CommGroup X]

theorem n7_map_eq_of_mem_stabSub {U : Subgroup X} {g : MulAut X} (hg : g ∈ stabSub U) :
    U.map g.toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (hg u).2 hu
  · intro hx
    exact ⟨g.symm x, (hg (g.symm x)).1 (by simpa using hx), by simp⟩

private theorem n7_mem_stabSub_of_map_eq {U : Subgroup X} {g : MulAut X} (hg : U.map g.toMonoidHom = U) :
    g ∈ stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hg

private theorem n7_autSub_normal {Y L : Subgroup (MulAut X)} {U : Subgroup X}
    (hN : Y ⊓ stabSub U ≤ Subgroup.normalizer (L : Set (MulAut X))) :
    ∀ x ∈ autSub Y U, ∀ k ∈ autSub L U, x * k * x⁻¹ ∈ autSub L U := by
  intro x hx k hk
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hk
  have hgN : (g : MulAut X) ∈ Subgroup.normalizer (L : Set (MulAut X)) := hN ⟨hg, g.2⟩
  refine mem_autSub.mpr ⟨g * l * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hgN (l : MulAut X)).mp hl

private theorem n7_autSub_two {L S : Subgroup (MulAut X)} {U : Subgroup X}
    (hSL : S ≤ Subgroup.normalizer (L : Set (MulAut X))) (hLs : L ≤ stabSub U) (hSs : S ≤ stabSub U)
    (hS2 : IsPGroup 2 ↥S) :
    ∀ x ∈ autSub (L ⊔ S) U, ∃ e : ℕ, x ^ 2 ^ e ∈ autSub L U := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  have hg' : (g : MulAut X) ∈ ((L ⊔ S : Subgroup (MulAut X)) : Set (MulAut X)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L S hSL] at hg'
  obtain ⟨l, hl, s, hs, hls⟩ := hg'
  have hsX : resHom U ⟨s, hSs hs⟩ ∈ autSub S U := mem_autSub.mpr ⟨⟨s, hSs hs⟩, hs, rfl⟩
  have hnS : ∀ x ∈ autSub S U, ∀ k ∈ autSub L U, x * k * x⁻¹ ∈ autSub L U :=
    n7_autSub_normal (inf_le_left.trans hSL)
  have hσN : resHom U ⟨s, hSs hs⟩ ∈
      Subgroup.normalizer ((autSub L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hnS _ hsX k hk
    · intro hk
      have h2 := hnS _ ((autSub S U).inv_mem hsX) _ hk
      have e2 : (resHom U ⟨s, hSs hs⟩)⁻¹ * (resHom U ⟨s, hSs hs⟩ * k * (resHom U ⟨s, hSs hs⟩)⁻¹) *
          ((resHom U ⟨s, hSs hs⟩)⁻¹)⁻¹ = k := by group
      rw [e2] at h2
      exact h2
  obtain ⟨e, he⟩ : ∃ e : ℕ, s ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hS2 ⟨s, hs⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hσe : (resHom U ⟨s, hSs hs⟩) ^ 2 ^ e = 1 := by
    rw [← map_pow, show (⟨s, hSs hs⟩ : ↥(stabSub U)) ^ 2 ^ e = 1 from Subtype.ext (by simpa using he),
      map_one]
  have hκ : resHom U ⟨l, hLs hl⟩ ∈ autSub L U := mem_autSub.mpr ⟨⟨l, hLs hl⟩, hl, rfl⟩
  have hgls : g = ⟨l, hLs hl⟩ * ⟨s, hSs hs⟩ := Subtype.ext hls.symm
  obtain ⟨k', hk', hpow⟩ := n7_mul_pow_mem hκ hσN (2 ^ e)
  refine ⟨e, ?_⟩
  rw [hgls, map_mul, hpow, hσe, mul_one]
  exact hk'

private theorem n7_isQuasisimple_autSub {L : Subgroup (MulAut X)} {U : Subgroup X} (hLs : L ≤ stabSub U)
    (hq : CFSG.IsQuasisimple ↥L) (hne : ∃ l ∈ L, ∃ u ∈ U, l u ≠ u) :
    CFSG.IsQuasisimple ↥(autSub L U) := by
  obtain ⟨l, hl, u, hu, hlu⟩ := hne
  let ψ : ↥L →* ↥(autSub L U) :=
    ((resHom U).comp (Subgroup.inclusion hLs)).codRestrict (autSub L U)
      (fun l => mem_autSub.2 ⟨Subgroup.inclusion hLs l, l.2, rfl⟩)
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := ψ) hq ?_ ⟨⟨l, hl⟩, fun h1 => hlu ?_⟩
  · intro φ
    obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 φ.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgφ⟩
  · have h2 : resHom U ⟨l, hLs hl⟩ = 1 := congrArg Subtype.val h1
    exact congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : X)) h2

private theorem n7_isIrrSec_autSub {L : Subgroup (MulAut X)} {U : Subgroup X} (hLs : L ≤ stabSub U)
    (hirr : XMod.IsIrr ↥L U) : XMod.IsIrrSec ↥(autSub L U) (⊥ : Subgroup ↥U) ⊤ := by
  obtain ⟨-, hlt, hJ⟩ := hirr
  refine ⟨?_, fun J hJinv _ _ => ?_⟩
  · obtain ⟨u, hu, hu1⟩ := IsConcreteLE.exists_of_lt hlt
    refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨bot_le, ⟨u, hu⟩, trivial, fun h1 => hu1 ?_⟩
    rw [Subgroup.mem_bot] at h1 ⊢
    exact congrArg Subtype.val h1
  · have hinv : XMod.IsInv ↥L (J.map U.subtype) := by
      rintro ⟨a, ha⟩ _ ⟨w, hw, rfl⟩
      exact ⟨resHom U ⟨a, hLs ha⟩ w,
        hJinv ⟨resHom U ⟨a, hLs ha⟩, mem_autSub.mpr ⟨⟨a, hLs ha⟩, ha, rfl⟩⟩ w hw, rfl⟩
    rcases hJ (J.map U.subtype) hinv bot_le (Subgroup.map_subtype_le J) with h1 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp h1
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : X) ∈ J.map U.subtype := by rw [h1]; exact u.2
      exact (Subgroup.mem_map_iff_mem (x := u) U.subtype_injective).mp hu

end Restrict

section Final

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

private theorem n7_Lb_le_stabSub (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) : Lb ≤ stabSub Vb := by
  subst hML
  intro g hg u
  refine ⟨fun hu => ?_, fun hu => h.irr.1 ⟨g, hg⟩ u hu⟩
  have h1 := h.irr.1 ⟨g, hg⟩⁻¹ _ hu
  change (g⁻¹ : MulAut X) (g u) ∈ Vb at h1
  simpa using h1

private theorem n7_Tb_le_normalizer (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    Tb ≤ Subgroup.normalizer (Lb : Set (MulAut X)) := by
  have h1 := le_normalizer_conjClosure Lb Tb
  rwa [← h.Mp_eq, hML] at h1

theorem z35_not_le_stab (h : Z35 Mb Tb Lb Vb) : ¬ Tb ≤ stabSub Vb := by
  intro hle
  have h1 : orbSup Tb Vb = Vb := orbSup_eq_of_stab fun t ht => hle ht
  rw [h.gen] at h1
  exact h.lt.ne h1.symm

theorem z35_b4Hyp (hA21 : AsA21SQTKSection) (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    B4Hyp (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) := by
  have hLs : Lb ≤ stabSub Vb := n7_Lb_le_stabSub h hML
  have hNn : Tb ⊓ stabSub Vb ≤ Subgroup.normalizer (Lb : Set (MulAut X)) :=
    inf_le_left.trans (n7_Tb_le_normalizer h hML)
  have hYn : (Lb ⊔ (Tb ⊓ stabSub Vb)) ⊓ stabSub Vb ≤ Subgroup.normalizer (Lb : Set (MulAut X)) :=
    inf_le_left.trans (sup_le Subgroup.le_normalizer hNn)
  have hN2 : IsPGroup 2 ↥(Tb ⊓ stabSub Vb) :=
    h.sylow.2.1.to_le (inf_le_left : Tb ⊓ stabSub Vb ≤ Tb)
  have hexp : ∀ w : ↥Vb, w ^ 2 = 1 := fun w => Subtype.ext (by simp [h.exp])
  have hle : autSub Lb Vb ≤ autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb := autSub_mono le_sup_left Vb
  have hn := n7_autSub_normal hYn
  have htwo := n7_autSub_two hNn hLs inf_le_right hN2
  have hne : ∃ l ∈ Lb, ∃ v ∈ Vb, l v ≠ v := by
    obtain ⟨l, hl, v, hv, hlv⟩ := h.nontriv 1 Tb.one_mem
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
    exact ⟨l', hl', v, hv, by simpa using hlv⟩
  have hq : CFSG.IsQuasisimple ↥(autSub Lb Vb) := n7_isQuasisimple_autSub hLs h.quasi hne
  have hirr : XMod.IsIrrSec ↥(autSub Lb Vb) (⊥ : Subgroup ↥Vb) ⊤ :=
    n7_isIrrSec_autSub hLs (hML ▸ h.irr)
  have hO2 := n7_pCoreOf_eq_bot_of_irr hexp hle hn hq hirr
  have hF := InternalSec.quasithinGenFitting_eq_of_two_pow hle hn (B1Red.isQuasisimple_to_open hq) htwo hO2
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := h.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hLX : Lb ≤ Mb ⊔ Tb := hML ▸ le_sup_left
  have hSL : SQTKGroup ↥Lb := B69.sqtk_subgroup hA21 hS φ hφ hLX h.quasi
  have hSL1 : SQTKGroup ↥(autSub Lb Vb) := B69.sqtk_autSub hA21 hLs hSL hq
  exact ⟨InternalSec.sqtkGroup_of_two_pow hle hn htwo hSL1, hF.symm, hq, hirr⟩

theorem z35_b42 (hB42 : AsB42) (hA21 : AsA21SQTKSection) (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    {A : Subgroup (MulAut X)} (hAT : A ≤ Tb) (hAV : A ≤ stabSub Vb) (hAe : IsElemAbelian2 A)
    (hAne : A ≠ ⊥)
    (hfaith : ∀ a ∈ A, (∀ w ∈ Vb, a w = w) → a = 1)
    (hr : Nat.card ↥Vb ≤ Nat.card A * Nat.card ↥(Vb ⊓ fixV A)) :
    ∃ A' : Subgroup (MulAut X), A' ≤ A ∧
      IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub A' Vb) ∧
      B42Conclusion (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A' Vb) := by
  have hexp : ∀ w : ↥Vb, w ^ 2 = 1 := fun w => Subtype.ext (by simp [h.exp])
  have hAY : A ≤ Lb ⊔ (Tb ⊓ stabSub Vb) := le_sup_of_le_right (le_inf hAT hAV)
  have hfc : A ⊓ centSub Vb = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, hac⟩
    exact Subgroup.mem_bot.2 (hfaith a ha hac)
  have hcomm : commSub Vb A ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2 (hfaith a ha fun w hw => (commSub_eq_bot_iff.mp hbot) hw a ha)
  have hA2 : IsA2 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub A Vb) :=
    IsA2.autSub ⟨hAY, hAne, hAe⟩ hAV hcomm
  have hcardA : Nat.card ↥(autSub A Vb) = Nat.card A := by
    have h1 := card_autSub_mul hAV
    rwa [hfc, Subgroup.card_bot, mul_one] at h1
  have hcardF : Nat.card ↥(fixV (autSub A Vb)) = Nat.card ↥(Vb ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAV, Subgroup.card_map_of_injective Vb.subtype_injective]
  have h0 : Nat.card ↥Vb + 0 ≤ Nat.card ↥(autSub A Vb) * Nat.card ↥(fixV (autSub A Vb)) := by
    rw [hcardA, hcardF, add_zero]
    exact hr
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 h0
  obtain ⟨A', hA'A, hA'B⟩ := exists_le_of_le_autSub hBA
  refine ⟨A', hA'A, ?_, ?_⟩
  · rw [hA'B]
    exact hB
  · rw [hA'B]
    exact hB42 ↥Vb hexp _ _ (z35_b4Hyp hA21 h hML) B hB

theorem z35_four (h : Z35 Mb Tb Lb Vb) (hidx : (Tb ⊓ stabSub Vb).relIndex Tb ≤ 2) :
    (∃ t ∈ Tb, t ∉ stabSub Vb) ∧
      ∀ t ∈ Tb, t ∉ stabSub Vb →
        (∀ s ∈ Tb, s ∈ stabSub Vb ∨ t⁻¹ * s ∈ stabSub Vb) ∧
          IsIntDirect Vb (Vb.map t.toMonoidHom) ⊤ := by
  have hns := z35_not_le_stab h
  refine ⟨?_, fun t ht htn => ?_⟩
  · by_contra hcon
    push Not at hcon
    exact hns hcon
  have hne1 : (Tb ⊓ stabSub Vb).relIndex Tb ≠ 1 := by
    intro h1
    exact hns ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  have hne0 : (Tb ⊓ stabSub Vb).relIndex Tb ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx2 : ((Tb ⊓ stabSub Vb).subgroupOf Tb).index = 2 := by
    show (Tb ⊓ stabSub Vb).relIndex Tb = 2
    omega
  have hmemN : ∀ s : ↥Tb, s ∈ (Tb ⊓ stabSub Vb).subgroupOf Tb ↔ (s : MulAut X) ∈ stabSub Vb := by
    intro s
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hs => hs.2, fun hs => ⟨s.2, hs⟩⟩
  have hcos : ∀ s ∈ Tb, s ∈ stabSub Vb ∨ t⁻¹ * s ∈ stabSub Vb := by
    intro s hs
    by_cases hsV : s ∈ stabSub Vb
    · exact Or.inl hsV
    · right
      have key := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨t, ht⟩ : ↥Tb)⁻¹)
        (b := ⟨s, hs⟩)).mpr ?_
      · exact (hmemN _).mp key
      · rw [hmemN, hmemN]
        constructor
        · intro hti
          exact absurd (by simpa using (stabSub Vb).inv_mem hti) htn
        · intro hs'
          exact absurd hs' hsV
  refine ⟨hcos, ?_, ?_⟩
  · rw [eq_top_iff, ← h.gen]
    refine orbSup_le fun s hs => ?_
    rcases hcos s hs with hsV | hsV
    · rw [n7_map_eq_of_mem_stabSub hsV]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨(t⁻¹ * s) v, (hsV v).2 hv, ?_⟩
      simp [MulAut.mul_apply]
  · have hmem1 : Vb ∈ {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} :=
      ⟨1, Tb.one_mem, (n7_map_eq_of_mem_stabSub ((stabSub Vb).one_mem)).symm⟩
    have hmemt : Vb.map t.toMonoidHom ∈ {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} :=
      ⟨t, ht, rfl⟩
    have hne : Vb ≠ Vb.map t.toMonoidHom := fun he => htn (n7_mem_stabSub_of_map_eq he.symm)
    exact disjoint_iff.mp (h.indep.pairwiseDisjoint hmem1 hmemt hne)

end Final

end CFSG.Quasithin
