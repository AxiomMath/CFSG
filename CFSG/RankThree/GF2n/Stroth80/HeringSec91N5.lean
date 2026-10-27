module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91A
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91N5Grp
public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_psi91 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = Nat.card Z ∧
      ∃ ψ : ↥(Rt M (LB M Q B) t) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K),
        Function.Surjective ψ ∧ ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
  obtain ⟨K, fK, finK, hK, φ, hφr, hφk, -⟩ := hs.plus4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  let ψ : ↥(Rt M (LB M Q B) t) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    e.toMonoidHom.comp ((MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict)
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp ((MulEquiv.subgroupCongr hφr).surjective.comp
      (MonoidHom.rangeRestrict_surjective φ))
  have hψker : ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    rw [← hφk]
    ext g
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      have h1 := e.injective (h.trans (map_one e).symm)
      have h2 := (MulEquiv.subgroupCongr hφr).injective
        (h1.trans (map_one (MulEquiv.subgroupCongr hφr)).symm)
      have := congrArg Subtype.val h2
      simpa using this
    · intro h
      have h1 : (φ.rangeRestrict g) = 1 := Subtype.ext (by simpa using h)
      rw [h1]
      simp
  exact ⟨K, fK, finK, inferInstance, hK, ψ, hψsurj, hψker⟩

end HS9

theorem sec9NGeFive_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Sec9NGeFiveStatement := by
  intro G _ _ M Q Z B hc n t hs
  by_contra hlt
  push Not at hlt
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := by omega
  have h35' := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have h35 := h35'.2.1
  have hn4 : 4 ≤ n := by
    have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun v hv =>
      ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
        hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
    have hle := Subgroup.card_le_of_le hVW
    rw [hs.card_V, hs.card_W h34] at hle
    have := (Nat.pow_le_pow_iff_right hq2).mp hle
    omega
  have hn : n = 4 := by omega
  subst hn
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc 4 t hs
  have hrR := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨hprod, hcomm, hNN⟩ := sec9_N51 h34 h311a hNC hs hr
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLAR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQLA : Q ≤ LB M Q (conjSubgroup r B) := sec39_Q_le_LB
  have hQN : Q ≤ hc.CN t := sec9_Q_le_CN hc ht
  obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk⟩ := HS9.exists_psi91 hs
  haveI := hch
  have hQT : Q ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) := le_inf hQL hQLA
  have hTR : ∀ g ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B),
      g * x * g⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro g hg x hx
    have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem (hQT (hcomm g hg x hx)) hx
  have hT'N : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ hc.CN t := by
    intro x hx
    have hxR : x ∈ Rt M (LB M Q B) t := hLR hx.1
    have hxz : ψ ⟨x, hxR⟩ ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro p
      obtain ⟨s, rfl⟩ := hψs p
      have hQs : ⁅(s : G), x⁆ ∈ Q := hcomm s s.2 x hx
      have h1 : ψ ⁅s, (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t))⁆ = 1 := by
        have : ⁅s, (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t))⁆ ∈ ψ.ker := by
          rw [hψk, Subgroup.mem_subgroupOf]
          exact hQN hQs
        exact this
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [Subgroup.center_prod, center_statedSL_two_eq_bot, Subgroup.bot_prod_bot,
      Subgroup.mem_bot] at hxz
    have : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ ψ.ker := hxz
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this
  have hLcard : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ 3 := by
    simpa using h35'.2.2.1
  have hrel := HS9.relIndex_LB_CN h34 hs
  have hXcard : Nat.card ↥(LB M Q B ⊓ hc.CN t) = Nat.card Q * Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
    rw [hrel, hLcard, inf_comm] at h1
    refine Nat.eq_of_mul_eq_mul_left (pow_pos hqpos 2) ?_
    rw [h1]
    ring
  have hNnorm : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hrR hx
  have hYconj : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr hNnorm]
  have hYcard : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hYconj]
    exact card_conjSubgroup r _
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hQT
  have hj2 : 2 ≤ j := by
    by_contra hj'
    push Not at hj'
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · exfalso
        have := Nat.card_pos (α := ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)))
        rw [hj, h0, mul_zero] at this
        omega
      · exact h0
    have hj1 : j = 1 := by omega
    have hle : Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) ≤ Nat.card Q := by
      rw [hj, hj1, mul_one]
    have heq := Subgroup.eq_of_le_of_card_ge hQT hle
    have htI : t ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
      ⟨ht, by rw [hLA]; exact hc.mem_conjSubgroup_LB_of_mem_Rt ht hrR⟩
    rw [← heq] at htI
    exact hs5.notQ htI
  obtain ⟨T, hT⟩ := exists_centLB hc t
  have hT'T : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ T := fun x hx =>
    (hT x).mpr ⟨hx.1, fun g hg => hcomm g hg x hx⟩
  have hTcard := h311bCard G M Q Z B hc 4 hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht hs5.notQ
    (sec9_Rt_ne_LB h34 hs) (sec9_not_SLNat hs) T hT
  have hT'card : Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) ≤
      Nat.card Q * Nat.card Z := (Subgroup.card_le_of_le hT'T).trans hTcard
  have hXY_le : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ LB M Q B ⊓ hc.CN t :=
    le_inf inf_le_left hT'N
  have hXYinf : (LB M Q B ⊓ hc.CN t) ⊓ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    ext x
    constructor
    · rintro ⟨⟨hxL, -⟩, ⟨hxLA, -⟩⟩
      exact ⟨hxL, hxLA⟩
    · intro hx
      exact ⟨⟨hx.1, hT'N hx⟩, ⟨hx.2, hT'N hx⟩⟩
  have hXYsup : (LB M Q B ⊓ hc.CN t) ⊔ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) = hc.CN t := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    exact Subgroup.mul_mem_sup ha hb
  have hNY : (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ≤
      Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine Subgroup.commutator_le.mpr fun b hb a ha => ?_
    exact hXY_le (hNN (Subgroup.commutator_mem_commutator hb.2 ha.2))
  have hcnt : Nat.card ↥(hc.CN t) * Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) := by
    have := card_sup_mul_card_inf_of_le_normalizer hNY
    rwa [hXYsup, hXYinf] at this
  have hsq : ∀ x ∈ hc.CN t, x ^ 2 ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have ha2 : a ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB ha.1
    have hb2 : b ^ 2 ∈ Q := hcr.sq_mem_Q_of_mem_LB hb.1
    have hcom : ⁅b, a⁆ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
      hNN (Subgroup.commutator_mem_commutator hb.2 ha.2)
    have hconj := hTR a (hNR ha.2) _ hcom
    have e : (a * b) ^ 2 = (a * ⁅b, a⁆ * a⁻¹) * a ^ 2 * b ^ 2 := by
      simp only [commutatorElement_def, pow_two]; group
    rw [e]
    exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem
      ((LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem hconj (hQT ha2)) (hQT hb2)
  obtain ⟨e, kk, hZ2, -⟩ := hc.hyp.cp
  have hKe : Nat.card K = 2 ^ e := hK.trans hZ2
  have h4K : 4 ≤ Nat.card K := by rw [hK]; exact hq4
  have he : 2 ≤ e := by
    by_contra he'
    push Not at he'
    have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hKe] at this
    omega
  let N₀ : Subgroup ↥(Rt M (LB M Q B) t) := (hc.CN t).subgroupOf (Rt M (LB M Q B) t)
  let T₀ : Subgroup ↥(Rt M (LB M Q B) t) :=
    (LB M Q B ⊓ LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)
  haveI hN₀ : N₀.Normal := ⟨fun x hx g => hc.CN_conj_mem ht g.2 hx⟩
  haveI hT₀ : T₀.Normal := ⟨fun x hx g => hTR g g.2 x hx⟩
  have hT₀N₀ : T₀ ≤ N₀ := fun x hx => hT'N hx
  have hNN₀ : ∀ a ∈ N₀, ∀ b ∈ N₀, ⁅a, b⁆ ∈ T₀ := fun a ha b hb =>
    hNN (Subgroup.commutator_mem_commutator ha hb)
  have hN2₀ : ∀ x ∈ N₀, x ^ 2 ∈ T₀ := fun x hx => hsq x hx
  have hker : ∀ g, ψ g = 1 → g ∈ N₀ := fun g hg => by
    have : g ∈ ψ.ker := hg
    rwa [hψk] at this
  have hT'R : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := fun x hx => hLR hx.1
  have hN₀card : Nat.card ↥N₀ = Nat.card ↥(hc.CN t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  have hT₀card : Nat.card ↥T₀ = Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'R).toEquiv
  have hidx0 : T₀.relIndex N₀ * Nat.card ↥T₀ = Nat.card ↥N₀ := by
    have h1 := Subgroup.relIndex_mul_card (H := T₀) (K := N₀)
    rwa [inf_of_le_left hT₀N₀] at h1
  have hXq : Nat.card (HS9.Xq N₀ T₀) = T₀.relIndex N₀ := (Subgroup.index_eq_card _).symm
  have hNcard : Nat.card ↥(hc.CN t) = T₀.relIndex N₀ * (Nat.card Q * j) := by
    rw [← hN₀card, ← hidx0, hT₀card, hj]
  have hmain : T₀.relIndex N₀ * j ^ 2 = Nat.card Z ^ 2 := by
    have h1 := hcnt
    rw [hNcard, hj, hYcard, hXcard] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left (mul_pos hQpos hQpos) ?_
    calc Nat.card Q * Nat.card Q * (T₀.relIndex N₀ * j ^ 2)
        = T₀.relIndex N₀ * (Nat.card Q * j) * (Nat.card Q * j) := by ring
      _ = (Nat.card Q * Nat.card Z) * (Nat.card Q * Nat.card Z) := h1
      _ = Nat.card Q * Nat.card Q * Nat.card Z ^ 2 := by ring
  have hdvd : T₀.relIndex N₀ ∣ 2 ^ (2 * e) :=
    ⟨j ^ 2, by rw [pow_mul', ← hZ2, ← hmain]⟩
  obtain ⟨d, hd, hidxd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hd2 : d + 2 ≤ 2 * e := by
    have h4 : 4 ≤ j ^ 2 := by nlinarith
    have h5 : 2 ^ d * 4 ≤ 2 ^ (2 * e) := by
      calc 2 ^ d * 4 = T₀.relIndex N₀ * 4 := by rw [hidxd]
        _ ≤ T₀.relIndex N₀ * j ^ 2 := Nat.mul_le_mul_left _ h4
        _ = Nat.card Z ^ 2 := hmain
        _ = 2 ^ (2 * e) := by rw [hZ2, pow_mul']
    have h6 : 2 ^ (d + 2) ≤ 2 ^ (2 * e) := by rw [pow_add]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h6
  have hX : Nat.card (HS9.Xq N₀ T₀) = 2 ^ d := by rw [hXq]; exact hidxd
  haveI hsimple : IsSimpleGroup ↥(StatedSL 2 K) :=
    isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl h4K)
  have hall := HS9.comm_mem_of_small (S := ↥(StatedSL 2 K)) N₀ T₀ hNN₀ hN2₀ ψ hψs hker hX
    (HS9.hsmall_statedSL K hKe he hd2)
  have hrc : ∀ x ∈ hc.CN t, ⁅r, x⁆ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := fun x hx =>
    hall ⟨r, hrR⟩ ⟨x, hNR hx⟩ hx
  have hYle : (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ≤
      LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro y hy
    have hy' := hy
    rw [hYconj, mem_conjSubgroup] at hy'
    have hcr' := hrc _ hy'.2
    have e : y = ⁅r, r⁻¹ * y * r⁆ * (r⁻¹ * y * r) := by
      simp only [commutatorElement_def]; group
    have hyX : y ∈ LB M Q B ⊓ hc.CN t := by
      rw [e]
      exact (LB M Q B ⊓ hc.CN t).mul_mem (hXY_le hcr') hy'
    have : y ∈ (LB M Q B ⊓ hc.CN t) ⊓ (LB M Q (conjSubgroup r B) ⊓ hc.CN t) := ⟨hyX, hy⟩
    rwa [hXYinf] at this
  have hT'Y : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ LB M Q (conjSubgroup r B) ⊓ hc.CN t :=
    le_inf inf_le_right hT'N
  have hYT : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) :=
    le_antisymm (Subgroup.card_le_of_le hYle) (Subgroup.card_le_of_le hT'Y)
  have hNT : Nat.card ↥(hc.CN t) = Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) := by
    have hX_T : Nat.card ↥(LB M Q B ⊓ hc.CN t) =
        Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) := hYcard.symm.trans hYT
    rw [hX_T, hYT] at hcnt
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcnt
  have := hs.large_t
  omega

end CFSG.RankThree.GF2n.Stroth80
