module

public import CFSG.RankThree.GF2n.Tim79aCase1End
public import CFSG.RankThree.GF2n.Tim79aCentralizer
public import CFSG.RankThree.GF2n.Tim79aIdentNormalizer

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isBenderGroup_and_VZ_eq_of_sec23Two [Finite G] {V H : Subgroup G} (h2 : Sec23Two V H) :
    IsBenderGroup (XbarZ V H) ∧
      ∃ S : Sylow 2 (XbarZ V H), VZ V H = sylowCenter (S : Subgroup (XbarZ V H)) := by
  rcases h2 with ⟨f, hf, -, ⟨e⟩, S, hS⟩ | ⟨n, hn, -, ⟨e⟩, S, hS⟩ | ⟨f, hf, -, ⟨e⟩, S, hS⟩
  · exact ⟨.isPSL2 f hf e, S, hS.symm.trans (sylowCenter_eq_of_psl2 hf e S).symm⟩
  · exact ⟨.isSuzuki n hn e, S, hS.trans (map_center_eq S)⟩
  · exact ⟨.isPSU3 f hf e, S, hS.trans (map_center_eq S)⟩

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem exists_mul_cPbar_of_sq_mem (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hBG : IsBenderGroup (XbarZ V H)) {S : Sylow 2 (XbarZ V H)}
    (hVS : VZ V H = sylowCenter (S : Subgroup (XbarZ V H))) {y : G} (hyP : y ∈ P)
    (hyX : y ∈ xOf V H) (hyy : y * y ∈ wOf V H) :
    ∃ v ∈ V, ∃ c ∈ cPbar V H P, y = v * c := by
  have hyH : y ∈ H := hc.PleH hyP
  set yH : ↥H := ⟨y, hyH⟩
  set r : Xbar V H := ⟨piBar V H yH, mem_barOf_iff.mpr ⟨yH, hyX, rfl⟩⟩
  have hrR : r ∈ Rbar V H P := mem_Rbar.mpr (mem_barOf_iff.mpr ⟨yH, hyP, rfl⟩)
  have hrr : r * r = 1 := by
    apply Subtype.ext
    show piBar V H yH * piBar V H yH = 1
    rw [← map_mul]
    exact (piBar_eq_one_iff _).2 hyy
  have hRS : Rtilde V H P ≤ (S : Subgroup (XbarZ V H)) :=
    hc.le_sylow_of_isPGroup hd hBG hVS.le hc.isPGroup_Rtilde hc.VZ_le_Rtilde
  have hπS : projZ V H r ∈ (S : Subgroup (XbarZ V H)) := hRS ⟨r, hrR, rfl⟩
  have hπZ : projZ V H r ∈ VZ V H := by
    rw [hVS]
    refine mem_sylowCenter.mpr ⟨hπS, fun t ht => ?_⟩
    exact (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hBG S hπS
      (by rw [← map_mul, hrr, map_one]) t ht).eq.symm
  obtain ⟨u, hu, hur⟩ := hπZ
  have hz : u⁻¹ * r ∈ Subgroup.center (Xbar V H) := by
    have h1 : projZ V H (u⁻¹ * r) = 1 := by
      rw [map_mul, map_inv, hur]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨u', hu'V, hu'u⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hu)
  have hcP : (u' : G)⁻¹ * y ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hu'V)) hyP
  have hcX : (u' : G)⁻¹ * y ∈ cX V H := by
    show (u' : G)⁻¹ * y ∈ H ∧ ∀ x ∈ xOf V H, ⁅(u' : G)⁻¹ * y, x⁆ ∈ wOf V H
    refine ⟨H.mul_mem (H.inv_mem u'.2) hyH, fun x hx => ?_⟩
    have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
    have hzc := Subgroup.mem_center_iff.mp hz
      ⟨piBar V H ⟨x, hxH⟩, mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩⟩
    have hzc' : piBar V H ⟨x, hxH⟩ * ((u : Hbar V H)⁻¹ * piBar V H yH) =
        ((u : Hbar V H)⁻¹ * piBar V H yH) * piBar V H ⟨x, hxH⟩ := congrArg Subtype.val hzc
    have h1 : piBar V H ⁅u'⁻¹ * yH, (⟨x, hxH⟩ : ↥H)⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_inv, hu'u, commutatorElement_eq_one_iff_mul_comm]
      exact hzc'.symm
    exact (piBar_eq_one_iff _).1 h1
  exact ⟨(u' : G), hu'V, (u' : G)⁻¹ * y, Subgroup.mem_inf.mpr ⟨hcP, hcX⟩, by group⟩

theorem exists_xOf_mul_cPbar (hc : MinCex M V Q P H) (hX : xOf V H ⊔ cPbar V H P = H) {x : G}
    (hx : x ∈ P) : ∃ y ∈ xOf V H, ∃ c ∈ cPbar V H P, x = y * c := by
  have hle : cPbar V H P ≤ Subgroup.normalizer (xOf V H : Set G) :=
    fun c hcC => H_le_normalizer_xOf V H (hc.PleH (Subgroup.mem_inf.mp hcC).1)
  have hxs : x ∈ xOf V H ⊔ cPbar V H P := by
    rw [hX]
    exact hc.PleH hx
  exact exists_mul_of_mem_sup hle hxs

theorem sq_mem_wOf_of_mul_self_eq_one (hc : MinCex M V Q P H) {x y c : G} (hy : y ∈ xOf V H)
    (hcC : c ∈ cPbar V H P) (hxyc : x = y * c) (hxx : x * x = 1) : y * y ∈ wOf V H := by
  have hcy : ⁅c, y⁆ ∈ wOf V H := ((Subgroup.mem_inf.mp hcC).2).2 y hy
  have hcc : c * c = 1 := hc.cPbar_sq_eq_one hcC
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have h1 : y * c * (y * c) = 1 := by rw [← hxyc]; exact hxx
  have hyinv : c * y * c = y⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc c * y * c * y = c * (y * c * (y * c)) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have e : y * y = ⁅c, y⁆⁻¹ := by
    calc y * y = y * (c * c) * y * (c * c) := by rw [hcc]; group
      _ = y * c * (c * y * c) * c := by group
      _ = y * c * y⁻¹ * c⁻¹ := by rw [hyinv, hcinv]
      _ = ⁅c, y⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact (wOf V H).inv_mem hcy

variable (hc : MinCex M V Q P H) (hd : Sec23Data V H) (hBG : IsBenderGroup (XbarZ V H))
  {S : Sylow 2 (XbarZ V H)} (hVS : VZ V H = sylowCenter (S : Subgroup (XbarZ V H)))
include hc hd hBG hVS

theorem dec_of_sq_mem {x y c : G} (hx : x ∈ P) (hy : y ∈ xOf V H) (hcC : c ∈ cPbar V H P)
    (hxyc : x = y * c) (hyy : y * y ∈ wOf V H) :
    ∃ v ∈ V, ∃ c' ∈ cPbar V H P, x = v * c' := by
  have hyP : y ∈ P := by
    have e : y = x * c⁻¹ := by rw [hxyc]; group
    rw [e]
    exact P.mul_mem hx (P.inv_mem (Subgroup.mem_inf.mp hcC).1)
  obtain ⟨v, hv, c', hc', hyvc⟩ := hc.exists_mul_cPbar_of_sq_mem hd hBG hVS hyP hy hyy
  exact ⟨v, hv, c' * c, (cPbar V H P).mul_mem hc' hcC, by rw [hxyc, hyvc]; group⟩

theorem dec_of_inv (hX : xOf V H ⊔ cPbar V H P = H) :
    ∀ t ∈ P, t * t = 1 → ∃ v ∈ V, ∃ c ∈ cPbar V H P, t = v * c := by
  intro t ht htt
  obtain ⟨y, hy, c, hcC, hyc⟩ := hc.exists_xOf_mul_cPbar hX ht
  exact hc.dec_of_sq_mem hd hBG hVS ht hy hcC hyc
    (hc.sq_mem_wOf_of_mul_self_eq_one hy hcC hyc htt)

end MinCex

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem pCap_wOf_le_V_of_inv (hc : MinCex M V Q P H)
    (hinv : ∀ t ∈ P, t * t = 1 → ∃ v ∈ V, ∃ c ∈ cPbar V H P, t = v * c) :
    P ⊓ wOf V H ≤ V := by
  set L : Subgroup G := Subgroup.closure {t | t ∈ P ∧ t * t = 1}
  have hLP : L ≤ P := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hVC : IsElemAbelian 2 (V ⊔ cPbar V H P) :=
    IsElemAbelian.sup_of_commute hc.elemAb hc.isElemAbelian_cPbar
      (fun a ha b hb => hc.commute_of_mem_P (Subgroup.mem_inf.mp hb).1 ha)
  have hLVC : L ≤ V ⊔ cPbar V H P := (Subgroup.closure_le _).2 fun t ht => by
    obtain ⟨v, hv, c, hcC, rfl⟩ := hinv t ht.1 ht.2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hcC)
  have hVL : V ≤ L := fun v hv =>
    Subgroup.subset_closure ⟨hc.V_le_P hv, hc.elemAb.mul_self_eq_one hv⟩
  have hEL : P ⊓ wOf V H ≤ L := fun e he =>
    Subgroup.subset_closure ⟨(Subgroup.mem_inf.1 he).1,
      hc.wOf_isElemAbelian.mul_self_eq_one (Subgroup.mem_inf.1 he).2⟩
  have hLc : IsMulCommutative L :=
    ⟨⟨fun x y => Subtype.ext (hVC.comm (hLVC x.2) (hLVC y.2))⟩⟩
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hLM : L ≤ M := fun l hl => hQM (hc.P_le_Q (hLP hl))
  have hconj : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    induction hl using Subgroup.closure_induction with
    | mem t ht =>
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hc.M_le_normalizer_P hm) t).1 ht.1
      · calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
          _ = 1 := by rw [ht.2]; group
    | one => simpa using L.one_mem
    | mul a b _ _ iha ihb =>
      have e : m * (a * b) * m⁻¹ = m * a * m⁻¹ * (m * b * m⁻¹) := by group
      rw [e]
      exact L.mul_mem iha ihb
    | inv a _ iha =>
      have e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [e]
      exact L.inv_mem iha
  have hML : M ≤ Subgroup.normalizer (L : Set G) := fun m hm =>
    Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj m hm x, fun hx => by
      simpa [mul_assoc] using hconj m⁻¹ (M.inv_mem hm) _ hx⟩
  exact fun e he => hc.maxAb.2 ⟨hLM, hML, hLc⟩ hVL (hEL he)

theorem mem_P_of_commute_of_dec (hc : MinCex M V Q P H) {g : G}
    (hg : ∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H)
    (hdec : (P ⊓ wOf V H) ⊔ (conjSubgroup g V ⊓ wOf V H) = wOf V H) :
    ∀ v ∈ V, v ∉ wOf V H → ∀ w ∈ wOf V H, v * w = w * v → w ∈ P := by
  have hne : conjSubgroup g V ≠ V := by
    intro h
    obtain ⟨u, hu, w, hw, hnc⟩ := hg
    rw [h] at hw
    apply hnc
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc.elemAb.comm hu hw)]
    exact (wOf V H).one_mem
  have hVB : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hc.ti hne
  have hnorm : ∀ v ∈ V, v ∉ wOf V H →
      v ∉ Subgroup.normalizer (conjSubgroup g V : Set G) := by
    intro v hv hvW hvN
    apply hvW
    have hle : wOf V H ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [← hdec]
      refine sup_le (fun e he => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc.commute_of_mem_P (Subgroup.mem_inf.mp he).1 hv).symm
      · obtain ⟨hbB, hbW⟩ := Subgroup.mem_inf.mp hb
        have hbN : b ∈ Subgroup.normalizer (V : Set G) := by
          rw [hc.normalizer_eq]
          exact hc.pCoreH_le_M (wOf_le_pCore V H hbW)
        have h1 : v * b * v⁻¹ * b⁻¹ ∈ conjSubgroup g V :=
          (conjSubgroup g V).mul_mem ((Subgroup.mem_normalizer_iff.mp hvN b).mp hbB)
            ((conjSubgroup g V).inv_mem hbB)
        have h2 : v * b * v⁻¹ * b⁻¹ ∈ V := by
          have h3 : b * v⁻¹ * b⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.mp hbN v⁻¹).mp (V.inv_mem hv)
          have h4 := V.mul_mem hv h3
          rwa [show v * (b * v⁻¹ * b⁻¹) = v * b * v⁻¹ * b⁻¹ by group] at h4
        have h5 : v * b * v⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup g V := ⟨h2, h1⟩
        rw [hVB, Subgroup.mem_bot] at h5
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc b * v = v * b * v⁻¹ * b⁻¹ * (b * v) := by rw [h5, one_mul]
          _ = v * b := by group
    exact hc.mem_wOf_of_centralizes_gen hv fun w hw =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm
  intro v hv hvW w hw hvw
  have hBN : conjSubgroup g V ⊓ wOf V H ≤
      Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) :=
    le_normalizer_of_comm fun x hx y hy => hc.wOf_isElemAbelian.comm hx.2 hy.2
  have hw' : w ∈ (P ⊓ wOf V H) ⊔ (conjSubgroup g V ⊓ wOf V H) := by
    rw [hdec]
    exact hw
  obtain ⟨e, he, b, hb, rfl⟩ := exists_mul_of_mem_sup hBN hw'
  have heP : e ∈ P := (Subgroup.mem_inf.mp he).1
  have hve : v * e = e * v := hc.commute_of_mem_P heP hv
  have hvb : v * b = b * v := by
    apply mul_left_cancel (a := e)
    calc e * (v * b) = (e * v) * b := by rw [mul_assoc]
      _ = (v * e) * b := by rw [hve]
      _ = v * (e * b) := by rw [mul_assoc]
      _ = (e * b) * v := hvw
      _ = e * (b * v) := by rw [mul_assoc]
  have hb1 : b = 1 := by
    by_contra hb1
    exact hnorm v hv hvW (Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g)
      (Subgroup.mem_inf.mp hb).1 hb1 hvb)
  rw [hb1, mul_one]
  exact heP

theorem sq_mem_wOf_of_pCap_le (hc : MinCex M V Q P H) (hPW : P ⊓ wOf V H ≤ V)
    (hA6 : ∀ v ∈ V, v ∉ wOf V H → ∀ w ∈ wOf V H, v * w = w * v → w ∈ P) :
    ∀ x ∈ P, x * x ∈ wOf V H := by
  intro x hxP
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hc.isPGroup_P⟩
  have hsqF : (⟨x, hxP⟩ : P) ^ 2 ∈ frattini ↥P :=
    CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) _
  have hxV : x * x ∈ V := hc.frattini_P_le ⟨_, hsqF, by simp [pow_two]⟩
  by_contra hxW
  have hC : wOf V H ⊓ Subgroup.centralizer ({x} : Set G) =
      wOf V H ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by
    ext w
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hw => ⟨fun h => ?_, fun h => ?_⟩
    · exact Commute.pow_right (show Commute w x from h) 2
    · have hwP : w ∈ P := hA6 (x * x) hxV hxW w hw (by rw [← pow_two]; exact h.symm)
      exact hc.commute_of_mem_P hxP (hPW (Subgroup.mem_inf.2 ⟨hwP, hw⟩))
  obtain ⟨k, hk⟩ := hc.isPGroup_P ⟨x, hxP⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcent := Tim78.tim78_2_1 hc.wOf_isElemAbelian.1
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian)
    (H_le_normalizer_wOf V H (hc.PleH hxP)) ⟨k, hxk⟩ hC
  have hxC : x ∈ cPbar V H P := by
    rw [hc.cPbar_eq_inf_centralizer]
    exact Subgroup.mem_inf.mpr ⟨hxP, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hcent hw)⟩
  exact hxW (by rw [hc.cPbar_sq_eq_one hxC]; exact (wOf V H).one_mem)

end MinCex

theorem false_of_sec23Two_of_sec25Concl [Finite G] {M V Q P H : Subgroup G}
    (hs : Sec23Setup M V Q P H) (h2 : Sec23Two V H) (h5 : Sec25Concl V H P) : False := by
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hd : Sec23Data V H := hs.data
  obtain ⟨hBG, S, hVS⟩ := isBenderGroup_and_VZ_eq_of_sec23Two h2
  obtain ⟨h5ab, hX, -⟩ := h5
  have hPW := hc.pCap_wOf_le_V_of_inv (hc.dec_of_inv hd hBG hVS hX)
  obtain ⟨g, hgX, hg⟩ := hc.exists_noncomm_conj hd
  have hA6 := hc.mem_P_of_commute_of_dec hg (h5ab g hgX hg).2.1
  have hsq := hc.sq_mem_wOf_of_pCap_le hPW hA6
  refine hc.false_of_dec fun x hx => ?_
  obtain ⟨y, hy, c, hcC, hyc⟩ := hc.exists_xOf_mul_cPbar hX hx
  have hyP : y ∈ P := by
    have e : y = x * c⁻¹ := by rw [hyc]; group
    rw [e]
    exact P.mul_mem hx (P.inv_mem (Subgroup.mem_inf.mp hcC).1)
  exact hc.dec_of_sq_mem hd hBG hVS hx hy hcC hyc (hsq y hyP)

end CFSG.RankThree.GF2n.Tim79a
