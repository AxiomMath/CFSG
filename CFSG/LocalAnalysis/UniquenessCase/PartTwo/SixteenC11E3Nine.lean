module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Aux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3AutL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAENatFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3NineF
public import CFSG.Quasithin.EmptyFaithful.F918C15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_nine_v1Sub {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h9 : Case168_9 D V₀ V hV L) : v1Sub D.M V₀ V hV L = V₀ := by
  by_cases hV0 : V₀ = ⊥
  · subst V₀
    refine s1611e3_v1Sub_eq_bot_of_fix D hV ?_
    intro w hw hfix
    obtain ⟨-, -, -, hsum, -⟩ := h9
    have hN : NatSum3 (lBar ⊥ V hV L) (wTil ⊥ V hV L) :=
      s16c167_natSum3_of_sumOfNat hsum
    have hmem : w ∈ wTil ⊥ V hV L ⊓ fixV (lBar ⊥ V hV L) :=
      ⟨hw, mem_fixV.2 hfix⟩
    rw [s16ae_natSum3_inf_fixV_eq_bot hN, Subgroup.mem_bot] at hmem
    exact hmem
  · exact v1Sub_of_ne_bot D.M V₀ V hV L hV0

theorem s1611e3_mem_stabSub_commSub_top {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {z : MulAut W} (hz : ∀ l ∈ L, z * l = l * z) :
    z ∈ stabSub (commSub (⊤ : Subgroup W) L) := by
  have hLmap : L.map (MulAut.conj z).toMonoidHom = L := by
    ext l
    constructor
    · rintro ⟨a, ha, rfl⟩
      change z * a * z⁻¹ ∈ L
      have h1 : z * a * z⁻¹ = a := by rw [hz a ha]; group
      rw [h1]
      exact ha
    · intro hl
      refine ⟨z⁻¹ * l * z, ?_, ?_⟩
      · rw [mul_assoc, ← hz l hl, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hl
      · show z * (z⁻¹ * l * z) * z⁻¹ = l
        group
  have hmap : (commSub (⊤ : Subgroup W) L).map z.toMonoidHom = commSub ⊤ L := by
    rw [← s15_Infra_commSub_top_map_conj L z, hLmap]
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : z u ∈ (commSub (⊤ : Subgroup W) L).map z.toMonoidHom := by rw [hmap]; exact hu
    obtain ⟨a, ha, hza⟩ := Subgroup.mem_map.1 h1
    have h2 : a = u := z.injective hza
    rw [← h2]
    exact ha
  · intro hu
    have h1 : z u ∈ (commSub (⊤ : Subgroup W) L).map z.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rwa [hmap] at h1

theorem s1611e3_isL3_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) : IsL3 X 1 :=
  Or.inl ⟨by decide, h⟩

theorem s1611e3_nine_center_comm {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    {x : MulAut (Vtil V₀ V hV)} (hxM : x ∈ Mbar D.M V₀ V hV) (hx2 : x * x = 1)
    (hxL : ∀ a ∈ lBar V₀ V hV L, x * a = a * x) :
    ∀ z : ↥(Fstar (Mbar D.M V₀ V hV)),
      z ∈ Subgroup.center ↥(Fstar (Mbar D.M V₀ V hV)) → x * (z : _) = (z : _) * x := by
  obtain ⟨⟨e⟩, hL3, hs15, hsum, -⟩ := h9
  obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hLPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  have hSC := s16c167_isPSL_simpleCentreless hLPSL
  have hperf := s16c167_isPSL_isPerfect hLPSL
  have hout := s16c167_isPSL_outer_solvable hLPSL
  have hOutF : Group.IsSolvable (Outer ↥(Fstar (Mbar D.M V₀ V hV))) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hc.setting.hyp151.le
  have hLF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hselfF hOutF hperf
  set Zc : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (Subgroup.center ↥(Fstar (Mbar D.M V₀ V hV))).map (Fstar (Mbar D.M V₀ V hV)).subtype
    with hZcdef
  have hZcM : Zc ≤ Mbar D.M V₀ V hV := (Subgroup.map_subtype_le _).trans hFX
  have hZccard : Nat.card ↥Zc = 7 := by
    rw [hZcdef, Subgroup.card_map_of_injective (f := (Fstar (Mbar D.M V₀ V hV)).subtype)
      (Fstar (Mbar D.M V₀ V hV)).subtype_injective]
    exact s1611e3_nine_center_card hL3 e
  have hZcn : (Zc.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZcM]
    intro z m hz hm
    rw [hZcdef] at hz ⊢
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.mem_map.2 ⟨⟨m * (w : MulAut (Vtil V₀ V hV)) * m⁻¹, hFn m hm w w.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : m⁻¹ * (g : MulAut (Vtil V₀ V hV)) * m⁻¹⁻¹ ∈ Fstar (Mbar D.M V₀ V hV) :=
      hFn m⁻¹ ((Mbar D.M V₀ V hV).inv_mem hm) g g.2
    have hc := Subgroup.mem_center_iff.mp hw ⟨_, hg⟩
    have hc' : (m⁻¹ * (g : MulAut (Vtil V₀ V hV)) * m⁻¹⁻¹) *
        (w : MulAut (Vtil V₀ V hV)) =
        (w : MulAut (Vtil V₀ V hV)) * (m⁻¹ * (g : MulAut (Vtil V₀ V hV)) * m⁻¹⁻¹) :=
      congrArg Subtype.val hc
    apply Subtype.ext
    show (g : MulAut (Vtil V₀ V hV)) * (m * (w : MulAut (Vtil V₀ V hV)) * m⁻¹) =
      (m * (w : MulAut (Vtil V₀ V hV)) * m⁻¹) * (g : MulAut (Vtil V₀ V hV))
    calc (g : MulAut (Vtil V₀ V hV)) * (m * (w : MulAut (Vtil V₀ V hV)) * m⁻¹)
        = m * ((m⁻¹ * (g : MulAut (Vtil V₀ V hV)) * m⁻¹⁻¹) *
            (w : MulAut (Vtil V₀ V hV))) * m⁻¹ := by group
      _ = m * ((w : MulAut (Vtil V₀ V hV)) *
            (m⁻¹ * (g : MulAut (Vtil V₀ V hV)) * m⁻¹⁻¹)) * m⁻¹ := by rw [hc']
      _ = (m * (w : MulAut (Vtil V₀ V hV)) * m⁻¹) * (g : MulAut (Vtil V₀ V hV)) := by group
  have hZcfix : fixV Zc = ⊥ :=
    s16c1610_fixV_eq_bot D h.hx h.h61 h.h127 h.h1214 hc.setting.hyp16.hyp125 hZcM hZcn
      (by intro h0; rw [h0, Subgroup.card_bot] at hZccard; omega)
      (by rw [hZccard]; norm_num)
  have hwcomm : ∀ w ∈ Zc, ∀ l ∈ lBar V₀ V hV L, w * l = l * w := by
    intro w hw l hl
    rw [hZcdef] at hw
    obtain ⟨w₀, hw₀, hww⟩ := Subgroup.mem_map.1 hw
    rw [← hww]
    have h := Subgroup.mem_center_iff.mp hw₀ ⟨l, hLF hl⟩
    have h2 : (Fstar (Mbar D.M V₀ V hV)).subtype (⟨l, hLF hl⟩ * w₀) =
        (Fstar (Mbar D.M V₀ V hV)).subtype (w₀ * ⟨l, hLF hl⟩) := congrArg _ h
    rw [map_mul, map_mul] at h2
    exact h2.symm
  have hmain : ∀ w ∈ Zc, x * w = w * x := by
    intro w hw
    by_cases hw1 : w = 1
    · subst hw1; rw [mul_one, one_mul]
    set J : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hJdef
    have hwL : ∀ l ∈ lBar V₀ V hV L, w * l = l * w := hwcomm w hw
    have hword : orderOf w = 7 := by
      have hdvd : orderOf w ∣ 7 := by
        have h := orderOf_dvd_natCard (⟨w, hw⟩ : Zc)
        rw [← Subgroup.orderOf_coe (⟨w, hw⟩ : Zc), hZccard] at h
        exact h
      rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hw1
      · exact hh
    have hzgen : Subgroup.zpowers w = Zc := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw)
      rw [Nat.card_zpowers, hword, hZccard]
    have hwJ : w ∈ stabSub (wTil V₀ V hV L) :=
      s1611e3_mem_stabSub_commSub_top (L := lBar V₀ V hV L) hwL
    have hxJ : x ∈ stabSub (wTil V₀ V hV L) :=
      s1611e3_mem_stabSub_commSub_top (L := lBar V₀ V hV L) hxL
    have hJsq : ∀ v : ↥J, v ^ 2 = 1 := fun v => Subtype.ext (s15_Infra_vtil_sq_eq_one V₀ V hV v)
    have hJodd : Odd (rk ↥J) := by
      have hrk : rk ↥J = 9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
      rw [hrk]; norm_num
    have hfixw : ∀ v : ↥J, (resHom J ⟨w, hwJ⟩) v = v → v = 1 := by
      intro v hv
      have hzv : w (v : Vtil V₀ V hV) = v := by
        have hc := congrArg (fun u : ↥J => (u : Vtil V₀ V hV)) hv
        simpa [resHom_apply] using hc
      have hmem : (v : Vtil V₀ V hV) ∈ fixV (Subgroup.zpowers w) :=
        mem_fixV_zpowers_iff_apply.2 hzv
      rw [hzgen, hZcfix, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hword7 : w ^ 7 = 1 := by rw [← hword]; exact pow_orderOf_eq_one w
    have hz7 : (resHom J ⟨w, hwJ⟩) ^ 7 = 1 := by
      rw [← map_pow, show (⟨w, hwJ⟩ : stabSub J) ^ 7 = 1 from Subtype.ext (by
        simpa using hword7), map_one]
    have hx2' : (resHom J ⟨x, hxJ⟩) ^ (2 ^ 1) = 1 := by
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← map_pow,
        show (⟨x, hxJ⟩ : stabSub J) ^ 2 = 1 from Subtype.ext (by
          simpa [pow_two] using hx2), map_one]
    have hxw : x * w * x⁻¹ ∈ Zc := by
      rw [hZcdef] at hw ⊢
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
      refine Subgroup.mem_map.2 ⟨⟨x * (w₀ : MulAut (Vtil V₀ V hV)) * x⁻¹, hFn x hxM w₀ w₀.2⟩,
        ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : x⁻¹ * (g : MulAut (Vtil V₀ V hV)) * x⁻¹⁻¹ ∈ Fstar (Mbar D.M V₀ V hV) :=
        hFn x⁻¹ ((Mbar D.M V₀ V hV).inv_mem hxM) g g.2
      have hc := Subgroup.mem_center_iff.mp hw₀ ⟨_, hg⟩
      have hc' : (x⁻¹ * (g : MulAut (Vtil V₀ V hV)) * x⁻¹⁻¹) *
          (w₀ : MulAut (Vtil V₀ V hV)) =
          (w₀ : MulAut (Vtil V₀ V hV)) * (x⁻¹ * (g : MulAut (Vtil V₀ V hV)) * x⁻¹⁻¹) :=
        congrArg Subtype.val hc
      apply Subtype.ext
      show (g : MulAut (Vtil V₀ V hV)) * (x * (w₀ : MulAut (Vtil V₀ V hV)) * x⁻¹) =
        (x * (w₀ : MulAut (Vtil V₀ V hV)) * x⁻¹) * (g : MulAut (Vtil V₀ V hV))
      calc (g : MulAut (Vtil V₀ V hV)) * (x * (w₀ : MulAut (Vtil V₀ V hV)) * x⁻¹)
          = x * ((x⁻¹ * (g : MulAut (Vtil V₀ V hV)) * x⁻¹⁻¹) *
              (w₀ : MulAut (Vtil V₀ V hV))) * x⁻¹ := by group
        _ = x * ((w₀ : MulAut (Vtil V₀ V hV)) *
              (x⁻¹ * (g : MulAut (Vtil V₀ V hV)) * x⁻¹⁻¹)) * x⁻¹ := by rw [hc']
        _ = (x * (w₀ : MulAut (Vtil V₀ V hV)) * x⁻¹) * (g : MulAut (Vtil V₀ V hV)) := by group
    have hn : resHom J ⟨x, hxJ⟩ * resHom J ⟨w, hwJ⟩ * (resHom J ⟨x, hxJ⟩)⁻¹ ∈
        Subgroup.zpowers (resHom J ⟨w, hwJ⟩) := by
      rw [← hzgen] at hxw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxw
      have heq : resHom J ⟨x, hxJ⟩ * resHom J ⟨w, hwJ⟩ * (resHom J ⟨x, hxJ⟩)⁻¹ =
          (resHom J ⟨w, hwJ⟩) ^ k := by
        rw [← map_inv (f := resHom J) (⟨x, hxJ⟩), ← map_mul, ← map_mul]
        have harg : (⟨x, hxJ⟩ * ⟨w, hwJ⟩ * (⟨x, hxJ⟩)⁻¹ : stabSub J) = ⟨w, hwJ⟩ ^ k := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
          exact hk.symm
        rw [harg]
        exact map_zpow (resHom J) ⟨w, hwJ⟩ k
      rw [heq]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    have hrescomm : resHom J ⟨x, hxJ⟩ * resHom J ⟨w, hwJ⟩ =
        resHom J ⟨w, hwJ⟩ * resHom J ⟨x, hxJ⟩ := by
      by_cases hx1 : resHom J ⟨x, hxJ⟩ = 1
      · rw [hx1, one_mul, mul_one]
      · rcases s16t_a_conj_eq_or_inv hz7 hn hx2' with hh | hh
        · exact mul_inv_eq_iff_eq_mul.mp hh
        · exact (s16t_a_false_of_inverted hJsq hJodd hz7 hfixw hh).elim
    have hpt : ∀ u ∈ J, x (w u) = w (x u) := by
      intro u hu
      have h2 := congrArg (fun φ : MulAut ↥J => ((φ ⟨u, hu⟩ : ↥J) : Vtil V₀ V hV)) hrescomm
      simpa [MulAut.mul_apply, resHom_apply] using h2
    have hagree : ∀ v ∈ J, (x * w * x⁻¹) v = w v := by
      intro v hv
      have hxJinv : x⁻¹ ∈ stabSub (wTil V₀ V hV L) := (stabSub (wTil V₀ V hV L)).inv_mem hxJ
      have hv' : x⁻¹ v ∈ J := (mem_stabSub.1 hxJinv v).2 hv
      have h2 := hpt (x⁻¹ v) hv'
      simpa [MulAut.mul_apply] using h2
    have hww : x * w * x⁻¹ * w⁻¹ = 1 := by
      by_contra hne
      have hwZ : x * w * x⁻¹ * w⁻¹ ∈ Zc := Zc.mul_mem hxw (Zc.inv_mem hw)
      have hword : orderOf (x * w * x⁻¹ * w⁻¹) = 7 := by
        have hdvd : orderOf (x * w * x⁻¹ * w⁻¹) ∣ 7 := by
          have h := orderOf_dvd_natCard (⟨_, hwZ⟩ : Zc)
          rw [← Subgroup.orderOf_coe (⟨_, hwZ⟩ : Zc), hZccard] at h
          exact h
        rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with hh | hh
        · exact absurd (orderOf_eq_one_iff.mp hh) hne
        · exact hh
      have hgen : Subgroup.zpowers (x * w * x⁻¹ * w⁻¹) = Zc := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwZ)
        rw [Nat.card_zpowers, hword, hZccard]
      have hJle : J ≤ fixV (Subgroup.zpowers (x * w * x⁻¹ * w⁻¹)) := by
        intro v hv
        rw [mem_fixV_zpowers_iff_apply]
        have hwJinv : w⁻¹ ∈ stabSub (wTil V₀ V hV L) :=
          (stabSub (wTil V₀ V hV L)).inv_mem hwJ
        have hv' : w⁻¹ v ∈ J := (mem_stabSub.1 hwJinv v).2 hv
        have h := hagree (w⁻¹ v) hv'
        simpa [MulAut.mul_apply] using h
      rw [hgen, hZcfix] at hJle
      have hJbot : J = ⊥ := le_bot_iff.mp hJle
      have hrk : rk ↥J = 9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
      rw [hJbot, rk_bot] at hrk
      omega
    have h1 : x * w * x⁻¹ = w := mul_inv_eq_one.mp hww
    exact mul_inv_eq_iff_eq_mul.mp h1
  intro z hz
  have hzZ : (z : MulAut (Vtil V₀ V hV)) ∈ Zc := by
    rw [hZcdef]
    exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  exact hmain z hzZ

theorem s1611e3_nine_faith_of_comm {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    {g : MulAut (Vtil V₀ V hV)} (hg : s16n9b_case9Two (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g)
    {x : MulAut (Vtil V₀ V hV)} (hxM : x ∈ Mbar D.M V₀ V hV) (hx2 : x * x = 1)
    (hxL : ∀ a ∈ lBar V₀ V hV L, x * a = a * x)
    (hxL' : ∀ a ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom, x * a = a * x)
    (hxZ : ∀ z : ↥(Fstar (Mbar D.M V₀ V hV)),
      z ∈ Subgroup.center ↥(Fstar (Mbar D.M V₀ V hV)) → x * (z : _) = (z : _) * x) :
    x = 1 := by
  obtain ⟨⟨e⟩, hL3, -, -, -⟩ := h9
  have hLPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  have hL'3 : IsL3 ↥((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom) 1 :=
    s1611e3_isL3_of_isPSL (isPSL_conjAutSub g hLPSL)
  obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hSC := s16c167_isPSL_simpleCentreless hLPSL
  have hperf := s16c167_isPSL_isPerfect hLPSL
  have hout := s16c167_isPSL_outer_solvable hLPSL
  have hOutF : Group.IsSolvable (Outer ↥(Fstar (Mbar D.M V₀ V hV))) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hc.setting.hyp151.le
  have hLF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hselfF hOutF hperf
  have hBmap : (Fstar (Mbar D.M V₀ V hV)).map (MulAut.conj g).toMonoidHom =
      Fstar (Mbar D.M V₀ V hV) := by
    apply le_antisymm
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact hFn g hg.mem y hy
    · intro x hx
      refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g,
        hFn g⁻¹ ((Mbar D.M V₀ V hV).inv_mem hg.mem) x hx, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  have hL'F : (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≤
      Fstar (Mbar D.M V₀ V hV) := by
    intro x hx
    have h2 : x ∈ (Fstar (Mbar D.M V₀ V hV)).map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono hLF hx
    rwa [hBmap] at h2
  have hcommAB : ∀ a ∈ lBar V₀ V hV L,
      ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom, a * b = b * a := by
    intro a ha b hb
    have hle := commutator_eq_bot_iff_le_centralizer.mp hg.comm
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  exact s1611e3_nine_abstract_faith hL3 e hselfF hLF hL'F hL3 hL'3 hcommAB hg.ne.symm
    hxM hx2 hxL hxL' hxZ

theorem s1611e3_nine_card_le_four_of_acttriv {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h9 : Case168_9 D V₀ V hV L) {g : MulAut (Vtil V₀ V hV)}
    (hg : s16n9b_case9Two (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : E ≤ Mbar D.M V₀ V hV)
    (hab : IsElemAbelian2 E)
    (hENL : E ≤ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hENB : E ≤ Subgroup.normalizer
      ((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom : Set (MulAut (Vtil V₀ V hV))))
    (hcentL : ∀ x ∈ E, ∀ a ∈ lBar V₀ V hV L, x * a = a * x) :
    Nat.card ↥E ≤ 4 := by
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := h9.2.1
  have hLPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  set B : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom with hBdef
  have hENB' : E ≤ Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))) := hENB
  have hB3 : IsL3 ↥B 1 := s1611e3_isL3_of_isPSL (isPSL_conjAutSub g hLPSL)
  let ψ : E →* MulAut ↥B :=
    B.normalizerMonoidHom.comp (Subgroup.inclusion hENB')
  have hψker : ∀ x : E, ψ x = 1 → x = 1 := by
    intro x hx
    have hxN : (⟨(x : MulAut (Vtil V₀ V hV)), hENB' x.2⟩ :
        ↥(Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))))) ∈
        MonoidHom.ker B.normalizerMonoidHom := by
      rw [MonoidHom.mem_ker]
      exact hx
    rw [Subgroup.normalizerMonoidHom_ker (H := B), Subgroup.mem_subgroupOf] at hxN
    have hxB : (x : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) := hxN
    have hxL' : ∀ a ∈ B,
        (x : MulAut (Vtil V₀ V hV)) * a = a * (x : MulAut (Vtil V₀ V hV)) := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hxB a ha).symm
    have hx2 : (x : MulAut (Vtil V₀ V hV)) * (x : MulAut (Vtil V₀ V hV)) = 1 := by
      simpa [pow_two] using hab.2 x x.2
    have hxZ := s1611e3_nine_center_comm h hc h9 (hE x.2) hx2 (hcentL x x.2)
    exact Subtype.ext (s1611e3_nine_faith_of_comm h hc h9 hg (hE x.2) hx2 (hcentL x x.2) hxL' hxZ)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ψ (x * y⁻¹) = 1 := by rw [map_mul, hxy, map_inv, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hψker (x * y⁻¹) h1
    exact mul_inv_eq_one.mp h2
  have hEimg : IsElemAbelian 2 ψ.range := by
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun y hy => ?_⟩
    · apply Subtype.ext
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      have h1 : ((a : ψ.range) : MulAut ↥B) = ψ x := hx.symm
      have h2 : ((b : ψ.range) : MulAut ↥B) = ψ z := hz.symm
      have hxz : x * z = z * x := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hab.1 x x.2 z z.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, h2, ← map_mul, ← map_mul, hxz]
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
      rw [← hx, ← map_pow]
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hab.2 x x.2
      rw [hx2, map_one]
  have h4 := s1611e3_card_le_four_mulAut_l3 hB3 hEimg
  rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv] at h4
  exact h4

theorem s1611e3_nine_card_le_four_of_acttriv_sym {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h9 : Case168_9 D V₀ V hV L) {g : MulAut (Vtil V₀ V hV)}
    (hg : s16n9b_case9Two (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : E ≤ Mbar D.M V₀ V hV)
    (hab : IsElemAbelian2 E)
    (hENL : E ≤ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hcentB : ∀ x ∈ E, ∀ a ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom,
      x * a = a * x) :
    Nat.card ↥E ≤ 4 := by
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := h9.2.1
  have hLPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  set B : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom with hBdef
  let ψ : E →* MulAut ↥(lBar V₀ V hV L) :=
    (lBar V₀ V hV L).normalizerMonoidHom.comp (Subgroup.inclusion hENL)
  have hψker : ∀ x : E, ψ x = 1 → x = 1 := by
    intro x hx
    have hxN : (⟨(x : MulAut (Vtil V₀ V hV)), hENL x.2⟩ :
        ↥(Subgroup.normalizer ((lBar V₀ V hV L) : Set (MulAut (Vtil V₀ V hV))))) ∈
        MonoidHom.ker (lBar V₀ V hV L).normalizerMonoidHom := by
      rw [MonoidHom.mem_ker]
      exact hx
    rw [Subgroup.normalizerMonoidHom_ker (H := lBar V₀ V hV L), Subgroup.mem_subgroupOf] at hxN
    have hxL : (x : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer ((lBar V₀ V hV L) : Set (MulAut (Vtil V₀ V hV))) := hxN
    have hxLc : ∀ a ∈ lBar V₀ V hV L,
        (x : MulAut (Vtil V₀ V hV)) * a = a * (x : MulAut (Vtil V₀ V hV)) := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hxL a ha).symm
    have hx2 : (x : MulAut (Vtil V₀ V hV)) * (x : MulAut (Vtil V₀ V hV)) = 1 := by
      simpa [pow_two] using hab.2 x x.2
    have hxZ := s1611e3_nine_center_comm h hc h9 (hE x.2) hx2 hxLc
    have hxL' : ∀ a ∈ B,
        (x : MulAut (Vtil V₀ V hV)) * a = a * (x : MulAut (Vtil V₀ V hV)) := hcentB x x.2
    exact Subtype.ext (s1611e3_nine_faith_of_comm h hc h9 hg (hE x.2) hx2 hxLc hxL' hxZ)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ψ (x * y⁻¹) = 1 := by rw [map_mul, hxy, map_inv, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hψker (x * y⁻¹) h1)
  have hEimg : IsElemAbelian 2 ψ.range := by
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun y hy => ?_⟩
    · apply Subtype.ext
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      have h1 : ((a : ψ.range) : MulAut ↥(lBar V₀ V hV L)) = ψ x := hx.symm
      have h2 : ((b : ψ.range) : MulAut ↥(lBar V₀ V hV L)) = ψ z := hz.symm
      have hxz : x * z = z * x := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hab.1 x x.2 z z.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, h2, ← map_mul, ← map_mul, hxz]
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
      rw [← hx, ← map_pow]
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hab.2 x x.2
      rw [hx2, map_one]
  have h4 := s1611e3_card_le_four_mulAut_l3 hL3 hEimg
  rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv] at h4
  exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
