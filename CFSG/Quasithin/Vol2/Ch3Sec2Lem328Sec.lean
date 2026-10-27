module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Basic
public import CFSG.Quasithin.Background.B5IrrA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem quasithinGenFitting_eq_of_two_pow {Ω : Type*} [Group Ω] [Finite Ω] {Y L : Subgroup Ω}
    (hLY : L ≤ Y) (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hL : CFSG.Open.IsQuasisimple ↥L)
    (h2 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ L) (hO2 : pCoreOf 2 Y = ⊥) :
    quasithinGenFitting Y = L := by
  apply le_antisymm
  · unfold quasithinGenFitting
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNY, hNn, hNnil⟩ x hx
      have hn' : ∀ y ∈ Y, ∀ z ∈ N, y * z * y⁻¹ ∈ N := by
        intro y hy z hz
        have := hNn.conj_mem ⟨z, hNY hz⟩ (by rw [Subgroup.mem_subgroupOf]; exact hz) ⟨y, hy⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hodd := B1Red.odd_orderOf_of_nilpotent_normal hNY hn' hO2 x hx
      obtain ⟨k, hk⟩ := h2 x (hNY hx)
      exact B1Red.mem_of_two_pow_mem_of_odd hk hodd
    · rintro K ⟨hKY, -, hKq⟩ k hk
      have hperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
      exact oTwoUpper_le_of_pow_mem h2 (B1Red.perfect_le_oTwoUpper' hKY hperf hk)
  · refine le_sup_of_le_right (le_sSup ⟨hLY, ?_, hL⟩)
    refine IsSubnormal.step hLY ?_ (IsSubnormal.refl _)
    exact (Subgroup.normal_subgroupOf_iff hLY).2 fun l y hl hy => hn y hy l hl

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_isSylowTwoOf_ge {H P : Subgroup (MulAut V)} (hPH : P ≤ H) (hP : IsPGroup 2 ↥P) :
    ∃ S : Subgroup (MulAut V), IsSylowTwoOf S H ∧ P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 ↥(P.subgroupOf H) := hP.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩,
    fun x hx => ⟨⟨x, hPH hx⟩, hQ hx, rfl⟩⟩
  have : ((Q : Subgroup ↥H).map H.subtype).subgroupOf H = (Q : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [this]
  exact Q.not_dvd_index

structure Sec328 (L S : Subgroup (MulAut V)) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  quasi : CFSG.IsQuasisimple ↥L
  sqtk : SQTKGroup ↥L
  irr : commV L ∈ IrrPlus L ⊤
  top : commV L = ⊤
  two : IsPGroup 2 ↥S
  norm : S ≤ Subgroup.normalizer (L : Set (MulAut V))

namespace Sec328

variable {L S : Subgroup (MulAut V)} (h : Sec328 L S)
include h

theorem eq_one {x : MulAut V} (hx : ∀ l ∈ L, l * x = x * l) {k : ℕ} (hxk : x ^ 2 ^ k = 1) :
    x = 1 := by
  have hV : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact h.sq v⟩
  obtain ⟨-, -, hlt, hirr⟩ := B5.irr_data h.irr
  rw [h.top, top_inf_eq] at hlt hirr
  refine eq_one_of_le_centralizer hV h.top hlt (fun J hJ hfJ => ?_) hx hxk
  exact hirr J hJ hfJ le_top

theorem odd_orderOf {x : MulAut V} (hx : ∀ l ∈ L, l * x = x * l) : Odd (orderOf x) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  set y := x ^ (orderOf x / 2) with hy
  have hy2 : orderOf y = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (even_iff_two_dvd.1 hev)
  have hyc : ∀ l ∈ L, l * y = y * l := fun l hl => (Commute.pow_right (hx l hl) _).eq
  have hy1 : y ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hy2 ▸ pow_orderOf_eq_one y
  rw [h.eq_one hyc hy1, orderOf_one] at hy2
  omega

theorem sup_le_normalizer : L ⊔ S ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  sup_le Subgroup.le_normalizer h.norm

theorem conj_mem {m l : MulAut V} (hm : m ∈ L ⊔ S) (hl : l ∈ L) : m * l * m⁻¹ ∈ L :=
  B19Aux.conj_mem_of_le_normalizer h.sup_le_normalizer hm hl

theorem sup_inf_centralizer_le :
    (L ⊔ S) ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := fun _ hx =>
  B1Red.mem_of_odd_orderOf_of_mem_sup h.two h.norm hx.1
    (h.odd_orderOf fun l hl => Subgroup.mem_centralizer_iff.1 hx.2 l hl)

theorem two_pow_mem : ∀ m ∈ L ⊔ S, ∃ k : ℕ, m ^ 2 ^ k ∈ L := by
  intro m hm
  obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer h.norm).1 hm
  obtain ⟨j, hj⟩ := h.two ⟨t, ht⟩
  have htj : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨x', hx', hx⟩ := A4.exists_pow_mul_eq hl (h.norm ht) (2 ^ j)
  rw [htj, mul_one] at hx
  exact ⟨j, hx ▸ hx'⟩

theorem normal_subgroupOf : (L.subgroupOf (L ⊔ S)).Normal :=
  (Subgroup.normal_subgroupOf_iff le_sup_left).2 fun _ _ hl hm => h.conj_mem hm hl

theorem quot_isPGroup [(L.subgroupOf (L ⊔ S)).Normal] :
    IsPGroup 2 (↥(L ⊔ S) ⧸ L.subgroupOf (L ⊔ S)) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := h.two_pow_mem (m : MulAut V) m.2
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hk

theorem not_le_of_isPGroup {R : Subgroup (MulAut V)} (hR : IsPGroup 2 ↥R) : ¬ L ≤ R := by
  intro hle
  have hnil := (hR.to_le hle).isNilpotent
  have : Group.IsPerfect ↥L := h.quasi.1
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open h.quasi)
  exact Group.IsPerfect.not_isNilpotent ↥L hnil

theorem pCoreOf_eq_bot : pCoreOf 2 (L ⊔ S) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ S)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ S)
  have hRM : pCoreOf 2 (L ⊔ S) ≤ L ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ S)
  have hcomm := B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open h.quasi)
    (fun n hn l hl => h.conj_mem (hRM hn) hl)
    (fun l hl n hn => B1Red.conj_mem_pCoreOf_prime 2 (Subgroup.mem_sup_left hl) hn)
    (h.not_le_of_isPGroup hR2)
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact Subgroup.mem_bot.2 (h.eq_one (fun l hl => (hcomm r hr l hl).symm) hk')

theorem genFitting_eq : quasithinGenFitting (L ⊔ S) = L :=
  quasithinGenFitting_eq_of_two_pow le_sup_left (fun _ hm _ hl => h.conj_mem hm hl)
    (B1Red.isQuasisimple_to_open h.quasi) h.two_pow_mem h.pCoreOf_eq_bot

theorem sqtk_sup : SQTKGroup ↥(L ⊔ S) := by
  have := h.normal_subgroupOf
  have hq := h.quot_isPGroup
  let e : ↥(L.subgroupOf (L ⊔ S)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hLm : SQTKGroup ↥(L.subgroupOf (L ⊔ S)) := by
    refine ⟨fun p hp hp2 => ?_, h.sqtk.2.of_mulEquiv e⟩
    show CFSG.Open.pRank p (⊤ : Subgroup ↥(L.subgroupOf (L ⊔ S))) ≤ 2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact h.sqtk.1 p hp hp2
  exact ⟨B5.sqt_of_two_quotient _ hq hLm.1, B5.kGroup_of_two_quotient _ hq hLm.2⟩

theorem le_stabSub_commV : L ⊔ S ≤ stabSub (commV L) :=
  B5.le_stabSub_commV (fun _ hg _ hl => h.conj_mem hg hl) (fun _ hg => (L ⊔ S).inv_mem hg)

theorem le_stabSub_fixV : L ⊔ S ≤ stabSub (fixV L ⊓ commV L) :=
  B5.le_stabSub_fixV_inf_commV (fun _ hg _ hl => h.conj_mem hg hl)
    (fun _ hg => (L ⊔ S).inv_mem hg)

theorem not_le_centSec : ¬ L ≤ centSec (commV L) (fixV L ⊓ commV L) := by
  intro hle
  obtain ⟨-, hcomm, hlt, -⟩ := B5.irr_data h.irr
  have h1 : commSub (commV L) L ≤ fixV L ⊓ commV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (hle hx).2 w hw
  rw [hcomm] at h1
  exact absurd (lt_of_lt_of_le hlt (h1.trans (inf_comm _ _).le)) (lt_irrefl _)

theorem sup_inf_centSec_eq_bot : (L ⊔ S) ⊓ centSec (commV L) (fixV L ⊓ commV L) = ⊥ := by
  set N := (L ⊔ S) ⊓ centSec (commV L) (fixV L ⊓ commV L) with hN
  have hMW := h.le_stabSub_commV
  have hMU := h.le_stabSub_fixV
  have hnot : ¬ L ≤ N := fun hle => h.not_le_centSec (hle.trans inf_le_right)
  have hcomm := B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open h.quasi) (N := N)
    (fun n hn l hl => h.conj_mem hn.1 hl)
    (fun l hl n hn => ⟨(L ⊔ S).mul_mem ((L ⊔ S).mul_mem (Subgroup.mem_sup_left hl) hn.1)
        ((L ⊔ S).inv_mem (Subgroup.mem_sup_left hl)),
      conj_mem_centSec (hMW (Subgroup.mem_sup_left hl)) (hMU (Subgroup.mem_sup_left hl)) hn.2⟩)
    hnot
  rw [eq_bot_iff]
  intro n hn
  have hnc : ∀ l ∈ L, l * n = n * l := fun l hl => (hcomm n hn l hl).symm
  have hnL : n ∈ L := h.sup_inf_centralizer_le ⟨hn.1, Subgroup.mem_centralizer_iff.2 hnc⟩
  have hsq : ∀ w ∈ commV L, (n * n) w = w :=
    B5.sq_trivial_of_stab h.sq hn.2.2 (fun c hc => hc.1 n hnL)
  have hn2 : n ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact MulEquiv.ext fun w => hsq w (by rw [h.top]; trivial)
  exact Subgroup.mem_bot.2 (h.eq_one hnc hn2)

theorem inf_centSec_eq_bot : L ⊓ centSec (commV L) (fixV L ⊓ commV L) = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right _ le_sup_left).trans h.sup_inf_centSec_eq_bot.le)

theorem b4Hyp :
    B4Hyp (autSec (L ⊔ S) (commV L) (fixV L ⊓ commV L))
      (autSec L (commV L) (fixV L ⊓ commV L)) := by
  obtain ⟨-, -, hlt, hirr⟩ := B5.irr_data h.irr
  have hMW := h.le_stabSub_commV
  have hMU := h.le_stabSub_fixV
  have hfM := h.sup_inf_centSec_eq_bot
  refine ⟨B5.sqtk_autSec hMW hMU hfM h.sqtk_sup, ?_,
    B5.isQuasisimple_autSec (le_sup_left.trans hMW) (le_sup_left.trans hMU)
      h.inf_centSec_eq_bot h.quasi, ?_⟩
  · exact (B5.genFitting_autSec le_sup_left hMW hMU hfM h.genFitting_eq).symm
  · rw [inf_comm] at hlt hirr
    exact B5.isIrrSec_autSec hlt hirr (le_sup_left.trans hMW) (le_sup_left.trans hMU)

theorem exists_sec_offender
    (hS : IsSylowTwoOf S (Subgroup.normalizer (L : Set (MulAut V))))
    (hFF : IsFFModule (Subgroup.normalizer (L : Set (MulAut V)))) :
    ∃ A, IsFFStarOffender (Subgroup.normalizer (L : Set (MulAut V))) A ∧ A ≤ S ∧
      ∃ B, B ≤ autSec A (commV L) (fixV L ⊓ commV L) ∧
        IsFFStarOffender (autSec (L ⊔ S) (commV L) (fixV L ⊓ commV L)) B := by
  obtain ⟨A₀, hA₀⟩ := ((B1_4_5 h.sq _).out 1 2).1 hFF
  obtain ⟨x, -, hA', hA'S⟩ := B5.exists_offender_le_sylow hS hA₀
  have hAM : IsFFStarOffender (L ⊔ S) (B1.conjAut x⁻¹ A₀) :=
    ⟨hA'S.trans le_sup_right, hA'.2.1, hA'.2.2.1, hA'.2.2.2⟩
  obtain ⟨-, hcomm, hlt, -⟩ := B5.irr_data h.irr
  have hSnot : ¬ commSub (commV L) (quasithinGenFitting (L ⊔ S)) ≤ fixV L ⊓ commV L := by
    rw [h.genFitting_eq, hcomm]
    intro hle
    have h1 : fixV L ⊓ commV L = commV L := le_antisymm inf_le_right hle
    rw [inf_comm, h1] at hlt
    exact lt_irrefl _ hlt
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ S)) := by
    rw [h.genFitting_eq]
    exact h.quasi
  obtain ⟨-, ⟨B, hBA, hB⟩, -⟩ := B1_5_8 h.sq hAM (W := commV L) (U := fixV L ⊓ commV L)
    inf_le_right h.le_stabSub_commV h.le_stabSub_fixV hq h.pCoreOf_eq_bot hSnot
  exact ⟨_, hA', hA'S, B, hBA, hB⟩

theorem b42 (hB42 : AsB42) (hS : IsSylowTwoOf S (Subgroup.normalizer (L : Set (MulAut V))))
    (hFF : IsFFModule (Subgroup.normalizer (L : Set (MulAut V)))) :
    ∃ B, IsFFStarOffender (autSec (L ⊔ S) (commV L) (fixV L ⊓ commV L)) B ∧
      B42Conclusion (autSec (L ⊔ S) (commV L) (fixV L ⊓ commV L))
        (autSec L (commV L) (fixV L ⊓ commV L)) B := by
  obtain ⟨-, -, -, B, -, hB⟩ := h.exists_sec_offender hS hFF
  exact ⟨B, hB, hB42 _ (sq_eq_one_sec h.sq _ _) _ _ h.b4Hyp B hB⟩

end Sec328

end CFSG.Quasithin.H13
