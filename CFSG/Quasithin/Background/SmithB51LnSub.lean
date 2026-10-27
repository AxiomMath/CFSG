module

public import CFSG.Quasithin.Background.SmithB51LnB42
public import CFSG.Quasithin.Background.SmithB51LnRealB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix

theorem not_b51Case1ii {V' : Type} [CommGroup V'] [Finite V'] {G' L' : Subgroup (MulAut V')} {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : ↥L' ≃* ↥(StatedSL n (ZMod 2))) : ¬ B51Case1ii G' L' := by
  rintro ⟨-, m, K, hKf, hKfin, hK, I, π, -, -, hreal, -, -⟩
  have hπ := hreal 0
  have hbij : Function.Bijective π := ⟨realizesVia_injective (FFModel.nat_faithful _) hπ, hπ.1⟩
  exact not_equiv_sl3 hK hn ⟨(MulEquiv.ofBijective π hbij).trans e⟩

section SecBot

variable {V : Type} [CommGroup V]

@[expose] def secIota (U : Subgroup V) : Sec U ⊥ →* V :=
  QuotientGroup.lift ((⊥ : Subgroup V).subgroupOf U) U.subtype (fun x hx => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
    exact hx)

theorem secIota_mk (U : Subgroup V) (u : ↥U) :
    secIota U (QuotientGroup.mk u) = (u : V) := rfl

theorem secIota_injective (U : Subgroup V) : Function.Injective (secIota U) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
  rw [secIota_mk] at hs
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
  exact hs

theorem secPre_bot_eq_map (U : Subgroup V) (X : Subgroup (Sec U ⊥)) :
    secPre U ⊥ X = X.map (secIota U) := by
  ext v
  rw [mem_secPre, Subgroup.mem_map]
  constructor
  · rintro ⟨hv, hX⟩
    exact ⟨_, hX, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨u.2, hs⟩

theorem map_secIota_top (U : Subgroup V) : (⊤ : Subgroup (Sec U ⊥)).map (secIota U) = U := by
  rw [← secPre_bot_eq_map, secPre_top]

theorem mk_secBot_fixed {L : Subgroup (MulAut V)} {U : Subgroup V} (hLU : L ≤ stabSub U)
    (u : ↥U) : (QuotientGroup.mk u : Sec U ⊥) ∈ fixV (autSec L U ⊥) ↔ (u : V) ∈ fixV L := by
  have hLbot : L ≤ stabSub (⊥ : Subgroup V) := fun a _ v => by
    simp only [Subgroup.mem_bot]
    constructor
    · intro h
      exact a.injective (h.trans (map_one a).symm)
    · intro h
      rw [h, map_one]
  rw [mk_mem_fixV_autSec_iff hLU hLbot]
  constructor
  · intro h l hl
    have := h l hl
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  · intro h l hl
    rw [h l hl, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem commV_autSec_bot_eq_top {L : Subgroup (MulAut V)} {U : Subgroup V} (hLU : L ≤ stabSub U)
    (hcomm : commSub U L = U) : commV (autSec L U ⊥) = ⊤ := by
  have hLbot : L ≤ stabSub (⊥ : Subgroup V) := fun a _ v => by
    simp only [Subgroup.mem_bot]
    constructor
    · intro h
      exact a.injective (h.trans (map_one a).symm)
    · intro h
      rw [h, map_one]
  rw [eq_top_iff]
  intro s _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
  have hu : (u : V) ∈ commSub U L := by rw [hcomm]; exact u.2
  let q : Subgroup V := (commV (autSec L U ⊥)).map (secIota U)
  have hle : commSub U L ≤ q := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hxs : secHom L hLU hLbot ⟨x, hx⟩ ∈ autSec L U ⊥ := by
      rw [← range_secHom L hLU hLbot]; exact ⟨_, rfl⟩
    refine ⟨_, Subgroup.subset_closure ⟨_, hxs, QuotientGroup.mk ⟨w, hw⟩, rfl⟩, ?_⟩
    rw [map_mul, map_inv, secHom_mk, secIota_mk, secIota_mk]
  obtain ⟨s', hs', hs'u⟩ := hle hu
  have : s' = QuotientGroup.mk u := secIota_injective U (by rw [hs'u, secIota_mk])
  rw [← this]
  exact hs'

theorem mem_irrPlus_of_sec {L : Subgroup (MulAut V)} {U : Subgroup V} (hLU : L ≤ stabSub U)
    (hcomm : commSub U L = U)
    (h : commV (autSec L U ⊥) ∈ IrrPlus (autSec L U ⊥) (⊤ : Subgroup (Sec U ⊥))) :
    U ∈ IrrPlus L (⊤ : Subgroup V) := by
  obtain ⟨-, -, hlt', hirr'⟩ := mem_irrPlus_top_iff.1 h
  have hLbot : L ≤ stabSub (⊥ : Subgroup V) := fun a _ v => by
    simp only [Subgroup.mem_bot]
    constructor
    · intro h
      exact a.injective (h.trans (map_one a).symm)
    · intro h
      rw [h, map_one]
  have hcommV : commV (autSec L U ⊥) = ⊤ := commV_autSec_bot_eq_top hLU hcomm
  rw [hcommV] at hlt' hirr'
  refine mem_irrPlus_top_iff.2 ⟨fun x hx w hw => (hLU hx w).2 hw, hcomm, ?_, ?_⟩
  ·
    rw [top_inf_eq] at hlt'
    obtain ⟨s, -, hs⟩ := IsConcreteLE.exists_of_lt hlt'
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    refine lt_of_le_of_ne inf_le_left fun heq => hs ?_
    rw [mk_secBot_fixed hLU]
    have : (u : V) ∈ U ⊓ fixV L := by rw [heq]; exact u.2
    exact this.2
  · intro J hJ hJ1 hJ2
    set J' : Subgroup (Sec U ⊥) := (J.subgroupOf U).map (QuotientGroup.mk' _) with hJ'
    have hJ'inv : ∀ x ∈ autSec L U ⊥, ∀ s ∈ J', x s ∈ J' := by
      intro x hx s hs
      rw [← range_secHom L hLU hLbot] at hx
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hs
      refine ⟨⟨(l : MulAut V) j, (hLU l.2 j).2 j.2⟩, ?_, ?_⟩
      · have hj' : (j : V) ∈ J := hj
        show (l : MulAut V) j ∈ J
        exact hJ _ l.2 _ hj'
      · rfl
    have hfixJ' : ⊤ ⊓ fixV (autSec L U ⊥) ≤ J' := by
      intro s hs
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
      have hs' : (QuotientGroup.mk u : Sec U ⊥) ∈ fixV (autSec L U ⊥) := hs.2
      rw [mk_secBot_fixed hLU] at hs'
      exact ⟨u, show (u : V) ∈ J from hJ1 ⟨u.2, hs'⟩, rfl⟩
    rcases hirr' J' hJ'inv hfixJ' le_top with h1 | h1
    · left
      refine le_antisymm (fun j hj => ⟨hJ2 hj, ?_⟩) hJ1
      have hmem : (QuotientGroup.mk ⟨j, hJ2 hj⟩ : Sec U ⊥) ∈ J' :=
        ⟨⟨j, hJ2 hj⟩, show j ∈ J from hj, rfl⟩
      rw [h1] at hmem
      exact (mk_secBot_fixed hLU _).1 hmem.2
    · right
      refine le_antisymm hJ2 fun u hu => ?_
      have hmem : (QuotientGroup.mk ⟨u, hu⟩ : Sec U ⊥) ∈ J' := by rw [h1]; trivial
      obtain ⟨j, hj, hju⟩ := hmem
      have : j = ⟨u, hu⟩ := by
        have h2 := congrArg (secIota U) hju
        exact Subtype.ext h2
      have hj' : (j : V) ∈ J := hj
      rw [this] at hj'
      exact hj'

end SecBot

section Transport

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}

theorem stabSub_bot_le (L : Subgroup (MulAut V)) : L ≤ stabSub (⊥ : Subgroup V) := fun a _ v => by
  simp only [Subgroup.mem_bot]
  constructor
  · intro h
    exact a.injective (h.trans (map_one a).symm)
  · intro h
    rw [h, map_one]

variable (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec U ⊥ = ⊥)
include hLU hfaith

theorem realM_of_secBot {n : ℕ} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    {X : Subgroup (Sec U ⊥)} {π' : ↥(StatedSL n (ZMod 2)) →* ↥(autSec L U ⊥)}
    (h : RealM (autSec L U ⊥) X ⊥ π' M) :
    RealM L (X.map (secIota U)) ⊥
      ((B5.secEquiv L hLU (stabSub_bot_le L) hfaith).symm.toMonoidHom.comp π') M := by
  have := RealM.ofSec hLU (stabSub_bot_le L) hfaith h
  rwa [secPre_bot_eq_map, secPre_bot (bot_le : (⊥ : Subgroup V) ≤ U)] at this

theorem sumNatDual_of_sec {m : ℕ} (hcomm : commV (autSec L U ⊥) = ⊤)
    (h : SumNatDual (autSec L U ⊥) (commV (autSec L U ⊥)) m) : SumNatDual L U m := by
  obtain ⟨hm, π', U₁, U₂, ⟨hsup, hinf⟩, h1, h2⟩ := h
  refine ⟨hm, _, U₁.map (secIota U), U₂.map (secIota U), ⟨?_, ?_⟩,
    realM_mat_iff.1 (realM_of_secBot hLU hfaith (realM_mat_iff.2 h1)),
    realM_dmat_iff.1 (realM_of_secBot hLU hfaith (realM_dmat_iff.2 h2))⟩
  · rw [← Subgroup.map_sup, hsup, hcomm, map_secIota_top]
  · rw [← Subgroup.map_inf _ _ _ (secIota_injective U), hinf, Subgroup.map_bot]

theorem directSumOfCopies_of_sec {m k : ℕ} (hcomm : commV (autSec L U ⊥) = ⊤)
    (h : DirectSumOfCopies (autSec L U ⊥) (commV (autSec L U ⊥)) ⊥
      (FFModel.nat (StatedSL m (ZMod 2))) k) :
    DirectSumOfCopies L U ⊥ (FFModel.nat (StatedSL m (ZMod 2))) k := by
  obtain ⟨I, π', -, hind, hsum, hreal⟩ := h
  refine ⟨fun i => (I i).map (secIota U), _, fun i => bot_le, fun i => ?_, ?_,
    fun i => realM_mat_iff.1 (realM_of_secBot hLU hfaith (realM_mat_iff.2 (hreal i)))⟩
  · have h1 := hind i
    rw [bot_sup_eq] at h1 ⊢
    have h2 : (⨆ (j : Fin k) (_ : j ≠ i), (I j).map (secIota U)) =
        (⨆ (j : Fin k) (_ : j ≠ i), I j).map (secIota U) := by
      rw [Subgroup.map_iSup]
      congr 1
      ext j
      rw [Subgroup.map_iSup]
    rw [h2, ← Subgroup.map_inf _ _ _ (secIota_injective U), h1, Subgroup.map_bot]
  · rw [bot_sup_eq] at hsum ⊢
    rw [← Subgroup.map_iSup, hsum, hcomm, map_secIota_top]

end Transport

section CaseLt

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem commV_ne_bot (h : B51Hyp G L) : commV L ≠ ⊥ := by
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open (quasi_L h))
  intro h0
  rw [commV_eq_commSub, commSub_eq_bot_iff] at h0
  obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
  apply hl
  apply Subtype.ext
  ext v
  exact h0 (Subgroup.mem_top v) l l.2

theorem case_lt (hA21 : AsA21SQTKSection) (hIH : B51Part1Below (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hlt : commV L ≠ ⊤) :
    (∃ m, B51Case1iii G L m) ∨ B51Case1iv G L := by
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) eL
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV (normal_L h) (fun g hg => G.inv_mem hg)
  have hLU : L ≤ stabSub (commV L) := (le_G h).trans hGU
  have hcommU : commSub (commV L) L = commV L :=
    commSub_commV_eq (commutator_L_perfect (quasi_L h))
  have hUne := commV_ne_bot h
  have hcard : Nat.card (Sec (commV L) ⊥) < Nat.card V := by
    have h1 := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ commV L)
    rw [Subgroup.card_bot, mul_one] at h1
    rw [h1]
    by_contra hge
    exact hlt (Subgroup.eq_top_of_le_card _ (not_lt.1 hge))
  have hcommV : commV (autSec L (commV L) ⊥) = ⊤ := commV_autSec_bot_eq_top hLU hcommU
  have ctx : ∀ A, IsFFStarOffender G A → SecCtx G L A (commV L) ⊥ := fun A hA =>
    ⟨hA.1, hA.2.2.1, hA.2.1, bot_le, sup_le hLU (hA.1.trans hGU), stabSub_bot_le _,
      by rw [hcommU]; exact fun h0 => hUne (le_bot_iff.1 h0)⟩
  have key : ∀ A, IsFFStarOffender G A → autSec A (commV L) ⊥ ≤ autSec L (commV L) ⊥ ∧
      ((∃ m, SumNatDual (autSec L (commV L) ⊥) (commV (autSec L (commV L) ⊥)) m) ∨
        (∃ m, (m = 4 ∨ m = 5) ∧ ∃ k, 1 ≤ k ∧ k ≤ m - 1 ∧
          DirectSumOfCopies (autSec L (commV L) ⊥) (commV (autSec L (commV L) ⊥)) ⊥
            (FFModel.nat (StatedSL m (ZMod 2))) k)) := by
    intro A hA
    have c := ctx A hA
    have hA' : IsFFStarOffender (L ⊔ A) A := ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
    have hB := isFFStarOffender_autSec_bot hA' c.hMW (sec_A_inf_centSec h c)
    have hY := b51Hyp_secY h c hA21 hB
    obtain ⟨-, hcase⟩ := hIH (Sec (commV L) ⊥) hcard (CFSG.Quasithin.sq_eq_one_sec hV _ _) _ _ hY
    have hfL := faithful_secL h c hZ
    have eL' : ↥(autSec L (commV L) ⊥) ≃* ↥(StatedSL n (ZMod 2)) :=
      (B5.secEquiv L hLU (stabSub_bot_le L) hfL).symm.trans eL
    rcases hcase with hi | hii | ⟨m, hGeq, hsum⟩ | ⟨hGeq, m, hm, k, hk1, hk2, hdir⟩
    · exact absurd (mem_irrPlus_of_sec hLU hcommU hi.1) hU
    · exact absurd hii (not_b51Case1ii hn eL')
    · exact ⟨le_sup_right.trans hGeq.le, Or.inl ⟨m, hsum⟩⟩
    · exact ⟨le_sup_right.trans hGeq.le, Or.inr ⟨m, hm, k, hk1, hk2, hdir⟩⟩
  have hAL : ∀ A, IsFFStarOffender G A → A ≤ L := by
    intro A hA
    have c := ctx A hA
    exact le_of_autSec_le c.hMW c.hMU (faithful_sec h c hZ) le_sup_left le_sup_right (key A hA).1
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  have hGL : G = L := eq_of_offenders_le h hT (fun A hA _ => hAL A hA)
  obtain ⟨A, hA⟩ := exists_offender h
  have hfL := faithful_secL h (ctx A hA) hZ
  rcases (key A hA).2 with ⟨m, hsum⟩ | ⟨m, hm, k, hk1, hk2, hdir⟩
  · exact Or.inl ⟨m, hGL, sumNatDual_of_sec hLU hfL hcommV hsum⟩
  · exact Or.inr ⟨hGL, m, hm, k, hk1, hk2, directSumOfCopies_of_sec hLU hfL hcommV hdir⟩

end CaseLt

end CFSG.Quasithin.B5.Ln
