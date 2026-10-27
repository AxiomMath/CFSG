module

public import CFSG.RankThree.GF2n.Tim81.Sec6.S65Min
public import CFSG.Timmesfeld.Bridge.OddTranspBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515F
import CFSG.RankThree.GF2n.Tim78S410Core
import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}
variable {U B : Subgroup G} {α β : G}

theorem Sec6Hyp.commute_of_mk (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    {x y : ↥U} (hx : (x : G) ∈ EU V U) (hy : (y : G) ∈ EU V U)
    (hc : Commute (x : UBar U) (y : UBar U)) : Commute (x : G) y := by
  have hroot := hS.sec5.toRootHyp
  obtain ⟨hxD, A, hA, -, hxA⟩ := hx
  obtain ⟨hyD, C, hC, -, hyC⟩ := hy
  have hx2G : (x : G) * (x : G) = 1 := hroot.mul_self_of_mem hA hxA
  have hy2G : (y : G) * (y : G) = 1 := hroot.mul_self_of_mem hC hyC
  have hx2 : x * x = 1 := Subtype.ext (by simpa using hx2G)
  have hy2 : y * y = 1 := Subtype.ext (by simpa using hy2G)
  have hinv : (x * y : ↥U)⁻¹ = y * x := by
    rw [mul_inv_rev, show x⁻¹ = x from inv_eq_of_mul_eq_one_right hx2,
      show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy2]
  have hsq_center : (x * y) ^ 2 ∈ Subgroup.center ↥U := by
    rw [← QuotientGroup.eq_one_iff]
    have hz : ((x * y : ↥U) : UBar U)⁻¹ = ((y * x : ↥U) : UBar U) := by
      rw [← QuotientGroup.mk_inv]
      exact congrArg (fun z : ↥U => (z : UBar U)) hinv
    have h : ((x * y : ↥U) : UBar U) = ((y * x : ↥U) : UBar U) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc.eq
    have heq : ((x * y : ↥U) : UBar U) = ((x * y : ↥U) : UBar U)⁻¹ :=
      h.trans hz.symm
    show (((x * y : ↥U) : UBar U)) ^ 2 = 1
    rw [pow_two]
    nth_rewrite 2 [heq]
    exact mul_inv_cancel _
  have hzZU : ((x : G) * (y : G)) ^ 2 ∈ ZU U := by
    have h := mem_center_iff_mem_ZU.mp hsq_center
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h
  set z : G := ((x : G) * (y : G)) ^ 2 with hzdef
  have hzmem : z ∈ ZU U := hzZU
  have hzx : (x : G) * z * (x : G)⁻¹ = z⁻¹ := by
    have hyx : (y : G) * (x : G) = ((x : G) * (y : G))⁻¹ := by
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      calc (x : G) * (y : G) * ((y : G) * (x : G)) =
          (x : G) * ((y : G) * (y : G)) * (x : G) := by group
        _ = 1 := by rw [hy2G, mul_one, hx2G]
    calc (x : G) * z * (x : G)⁻¹ = ((x : G) * ((x : G) * (y : G)) * (x : G)⁻¹) ^ 2 := by
          rw [hzdef, conj_pow]
      _ = ((y : G) * (x : G)) ^ 2 := by
          rw [show (x : G) * ((x : G) * (y : G)) * (x : G)⁻¹ = (y : G) * (x : G) by
            rw [← mul_assoc, hx2G, one_mul,
              show (x : G)⁻¹ = x from inv_eq_of_mul_eq_one_right hx2G]]
      _ = (((x : G) * (y : G))⁻¹) ^ 2 := by rw [hyx]
      _ = (((x : G) * (y : G)) ^ 2)⁻¹ := by rw [inv_pow]
      _ = z⁻¹ := by rw [hzdef]
  have hcommzx : Commute z (x : G) :=
    (Subgroup.mem_centralizer_iff.mp hzmem.2 (x : G) x.2).symm
  have hcomm_conj : (x : G) * z * (x : G)⁻¹ = z := by
    calc (x : G) * z * (x : G)⁻¹ = z * (x : G) * (x : G)⁻¹ := by rw [← hcommzx.eq]
      _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hz : z * z = 1 := by
    have h : z = z⁻¹ := by
      rw [← hzx, hcomm_conj]
    exact mul_eq_one_iff_eq_inv.mpr h
  have hpow : ((x : G) * (y : G)) ^ (2 ^ 2) = 1 := by
    have h4 : ((x : G) * (y : G)) ^ 4 = (((x : G) * (y : G)) ^ 2) ^ 2 := by
      rw [← pow_mul]
    norm_num
    rw [h4, ← hzdef, pow_two]
    exact hz
  exact hS.commute_of_pow_two_pow h64 hxD hyD hpow

private theorem eu_involution (hS : Sec6Hyp M V) {x : G} (hx : x ∈ EU V U) : x * x = 1 := by
  obtain ⟨-, A, hA, -, hxA⟩ := hx
  exact hS.sec5.toRootHyp.mul_self_of_mem hA hxA

private theorem eu_mem_U {x : G} (hx : x ∈ EU V U) : x ∈ U := by
  obtain ⟨-, A, -, hAU, hxA⟩ := hx
  exact hAU hxA

private theorem ebar_mk_mem {u : ↥U} (hu : (u : G) ∈ EU V U) : (u : UBar U) ∈ EBar V U :=
  ⟨u, hu, rfl⟩

private theorem ebar_orderOf_two (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {d : UBar U} (hd : d ∈ EBar V U) : orderOf d = 2 := by
  obtain ⟨u, hu, rfl⟩ := hd
  have hu2 : u * u = 1 := Subtype.ext (by simpa using eu_involution hS hu)
  have hd2 : (u : UBar U) * (u : UBar U) = 1 := by
    rw [← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
  have hd1 : (u : UBar U) ≠ 1 := by
    intro h
    have hc : u ∈ Subgroup.center ↥U := (QuotientGroup.eq_one_iff u).mp h
    exact hm.not_mem_classD hS h64 (mem_center_iff_mem_ZU.mp hc) hu.1
  exact orderOf_eq_prime (by simpa [pow_two] using hd2) hd1

private theorem ebar_oddT (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    Asc72.IsOddTransp (EBar V U) := by
  constructor
  · intro d hd
    exact ebar_orderOf_two hS h64 hm hd
  · intro d hd e he
    obtain ⟨u, hu, rfl⟩ := hd
    obtain ⟨v, hv, rfl⟩ := he
    have hdvd : orderOf ((u : UBar U) * (v : UBar U)) ∣
        orderOf ((u : G) * (v : G)) := by
      have h1 : (u : UBar U) * (v : UBar U) = ((u * v : ↥U) : UBar U) := by
        rw [QuotientGroup.mk_mul]
      rw [h1]
      have h2 := orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center ↥U)) (u * v)
      simpa only [QuotientGroup.mk'_apply, Subgroup.orderOf_coe, ← Subgroup.coe_mul] using h2
    by_cases hb : BadPair (u : G) (v : G)
    · obtain ⟨r, hr, -, ho⟩ := hS.exists_odd_of_bad h64 hu.1 hv.1 hb
      have hz := hm.pow_mem_ZU hS hu hv hb hr ho
      have hpow : (((u * v : ↥U) ^ r : ↥U) : UBar U) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact mem_center_iff_mem_ZU.mpr
          (by simpa only [Subgroup.coe_pow, Subgroup.coe_mul] using hz)
      have hde : ((u : UBar U) * (v : UBar U)) ^ r = 1 := by
        rw [show (u : UBar U) * (v : UBar U) = ((u * v : ↥U) : UBar U) by
          rw [QuotientGroup.mk_mul]]
        rw [← QuotientGroup.mk_pow]
        exact hpow
      exact Or.inr (hr.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hde))
    · rw [BadPair] at hb
      push Not at hb
      rcases hb with h2 | hodd
      · exact Or.inl (hdvd.trans h2)
      · exact Or.inr (hodd.of_dvd_nat hdvd)

private theorem eu_conj_mem {w : ↥U} (hw : (w : G) ∈ EU V U)
    (u : ↥U) : ((u * w * u⁻¹ : ↥U) : G) ∈ EU V U := by
  obtain ⟨hwD, A, hA, hAU, hwA⟩ := hw
  have hu : (u : G) ∈ U := u.2
  have hD : (u : G) * (w : G) * (u : G)⁻¹ ∈ Tim78.classD V := Tim78.mem_classD_conj hwD _
  refine ⟨hD, conjSubgroup (u : G) A,
    Tim79a.conjSubgroup_mem_omegaOf_of_mem hA (Subgroup.mem_top (u : G)), ?_, ?_⟩
  · intro z hz
    rw [mem_conjSubgroup] at hz
    have hzU : (u : G)⁻¹ * z * (u : G) ∈ U := hAU hz
    have hz' : z = (u : G) * ((u : G)⁻¹ * z * (u : G)) * (u : G)⁻¹ := by group
    rw [hz']
    exact U.mul_mem (U.mul_mem hu hzU) (U.inv_mem hu)
  · refine mem_conjSubgroup.mpr ?_
    rw [show (u : G)⁻¹ * ↑(u * w * u⁻¹) * (u : G) = (w : G) by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group]
    exact hwA

private theorem ebar_conj_mem {z : UBar U} (hz : z ∈ EBar V U)
    (k : UBar U) : k * z * k⁻¹ ∈ EBar V U := by
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨u * w * u⁻¹, eu_conj_mem hw u, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

private theorem ebar_isConj_of_not_commute
    (hoddT : Asc72.IsOddTransp (EBar V U)) {x y : UBar U}
    (hx : x ∈ EBar V U) (hy : y ∈ EBar V U) (hnc : ¬ Commute x y) : IsConj x y := by
  have ho : Odd (orderOf (x * y)) := hoddT.odd_of_not_commute hx hy hnc
  have hx2 : x * x = 1 := hoddT.mul_self_eq_one hx
  have hy2 : y * y = 1 := hoddT.mul_self_eq_one hy
  obtain ⟨g, -, hg⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hx2 hy2 ho
  exact isConj_iff.mpr ⟨g, hg⟩

private theorem ebar_V_B_not_commute (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {v b : ↥U} (hvV : (v : G) ∈ V) (hv1 : v ≠ 1)
    (hbB : (b : G) ∈ B) (hb1 : b ≠ 1) : ¬ Commute (v : UBar U) (b : UBar U) := by
  intro hc
  have hvEU : (v : G) ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hvV
      (by intro h; exact hv1 (Subtype.ext h)), V, mem_omegaSet_self V, hm.le.1, hvV⟩
  have hbEU : (b : G) ∈ EU V U :=
    ⟨mem_classD_of_mem hm.memB hbB (by intro h; exact hb1 (Subtype.ext h)),
      B, hm.memB, hm.le.2.1, hbB⟩
  have hcomm : Commute (v : G) (b : G) := Sec6Hyp.commute_of_mk hS h64 hvEU hbEU hc
  have hVB := hS.sec5.toRootHyp.commute_of_commute_mem (mem_omegaSet_self V) hm.memB
    hvV hbB (by intro h; exact hv1 (Subtype.ext h)) (by intro h; exact hb1 (Subtype.ext h)) hcomm
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  have hα2 : α * α = 1 := hS.sec5.toRootHyp.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hβ2 : β * β = 1 := hS.sec5.toRootHyp.mul_self_of_mem hm.memB hm.memβ
  have hαβ : Commute α β := hVB α hm.memα β hm.memβ
  have hprod : (α * β) * (α * β) = 1 := by
    calc (α * β) * (α * β) = α * (β * α) * β := by group
      _ = α * (α * β) * β := by rw [hαβ.eq]
      _ = (α * α) * (β * β) := by group
      _ = 1 := by rw [hα2, hβ2, one_mul]
  exact hm.bad (Or.inl (orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hprod)))

private theorem ebar_exists_not_commute (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {x : UBar U} (hx : x ∈ EBar V U) :
    (∃ v : ↥U, (v : G) ∈ V ∧ v ≠ 1 ∧ ¬ Commute x (v : UBar U)) ∨
    (∃ b : ↥U, (b : G) ∈ B ∧ b ≠ 1 ∧ ¬ Commute x (b : UBar U)) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, rfl⟩ := hx
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hVcomm : ∀ v ∈ V, v ≠ 1 → Commute (u : G) v := by
    intro v hvV hv1
    have hvU : (⟨v, hm.le.1 hvV⟩ : ↥U) ≠ 1 := by
      intro h
      exact hv1 (congrArg Subtype.val h)
    have hvEU : v ∈ EU V U :=
      ⟨mem_classD_of_mem (mem_omegaSet_self V) hvV hv1, V, mem_omegaSet_self V,
        hm.le.1, hvV⟩
    exact Sec6Hyp.commute_of_mk hS h64 hu hvEU (hcon.1 ⟨v, hm.le.1 hvV⟩ hvV hvU)
  have hBcomm : ∀ b ∈ B, b ≠ 1 → Commute (u : G) b := by
    intro b hbB hb1
    have hbU : (⟨b, hm.le.2.1 hbB⟩ : ↥U) ≠ 1 := by
      intro h
      exact hb1 (congrArg Subtype.val h)
    have hbEU : b ∈ EU V U :=
      ⟨mem_classD_of_mem hm.memB hbB hb1, B, hm.memB, hm.le.2.1, hbB⟩
    exact Sec6Hyp.commute_of_mk hS h64 hu hbEU (hcon.2 ⟨b, hm.le.2.1 hbB⟩ hbB hbU)
  have hVc : V ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, one_mul]
    · exact (hVcomm z hz hz1).eq
  have hBc : B ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, one_mul]
    · exact (hBcomm z hz hz1).eq
  have hUc : U ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
    intro z hz
    have hz' : z ∈ V ⊔ B := by rwa [hm.eq_sup] at hz
    exact (sup_le hVc hBc) hz' 
  have huCen : (u : G) ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hUc hz) (u : G) (Set.mem_singleton _)).symm
  exact hm.not_mem_classD hS h64 ⟨u.2, huCen⟩ hu.1

private theorem MinBad.ebar_class (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) :
    ∃ d₀ : UBar U, EBar V U = {g | IsConj d₀ g} := by
  classical
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  have hαD : α ∈ Tim78.classD V := mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1
  have hβD : β ∈ Tim78.classD V := mem_classD_of_mem hm.memB hm.memβ hβ1
  let au : ↥U := ⟨α, hm.le.2.2.1⟩
  let bu : ↥U := ⟨β, hm.le.2.2.2⟩
  have hαEU : α ∈ EU V U := ⟨hαD, V, mem_omegaSet_self V, hm.le.1, hm.memα⟩
  have hβEU : β ∈ EU V U := ⟨hβD, B, hm.memB, hm.le.2.1, hm.memβ⟩
  have hαbar : (au : UBar U) ∈ EBar V U := ⟨au, hαEU, rfl⟩
  have hβbar : (bu : UBar U) ∈ EBar V U := ⟨bu, hβEU, rfl⟩
  have hoddT := ebar_oddT hS h64 hm
  refine ⟨(au : UBar U), ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨u, huEU, rfl⟩ := hy
    have hxbar : (u : UBar U) ∈ EBar V U := ebar_mk_mem huEU
    rcases ebar_exists_not_commute hS h64 hm hxbar with ⟨v, hvV, hv1, hnc⟩ |
      ⟨b, hbB, hb1, hnc⟩
    · have hvbar : (v : UBar U) ∈ EBar V U := by
        refine ebar_mk_mem ?_
        exact ⟨mem_classD_of_mem (mem_omegaSet_self V) hvV
          (by intro h; exact hv1 (Subtype.ext h)), V, mem_omegaSet_self V, hm.le.1, hvV⟩
      have h1 := ebar_isConj_of_not_commute hoddT hxbar hvbar hnc
      have hvβ : IsConj (v : UBar U) (bu : UBar U) :=
        ebar_isConj_of_not_commute hoddT hvbar hβbar
          (ebar_V_B_not_commute hS h64 hm hvV hv1 hm.memβ
            (by intro h; exact hβ1 (congrArg Subtype.val h)))
      have hβα : IsConj (bu : UBar U) (au : UBar U) :=
        ebar_isConj_of_not_commute hoddT hβbar hαbar (by
          intro h
          exact (ebar_V_B_not_commute hS h64 hm hm.memα
            (by intro h1; exact hα1 (congrArg Subtype.val h1)) hm.memβ
            (by intro h1; exact hβ1 (congrArg Subtype.val h1))) h.symm)
      exact (h1.trans (hvβ.trans hβα)).symm
    · have hbbar : (b : UBar U) ∈ EBar V U := by
        refine ebar_mk_mem ?_
        exact ⟨mem_classD_of_mem hm.memB hbB
          (by intro h; exact hb1 (Subtype.ext h)), B, hm.memB, hm.le.2.1, hbB⟩
      have h1 := ebar_isConj_of_not_commute hoddT hxbar hbbar hnc
      have hbα : IsConj (b : UBar U) (au : UBar U) :=
        ebar_isConj_of_not_commute hoddT hbbar hαbar (by
          intro h
          exact (ebar_V_B_not_commute hS h64 hm hm.memα
            (by intro h1; exact hα1 (congrArg Subtype.val h1)) hbB hb1) h.symm)
      exact (h1.trans hbα).symm
  · intro hconj
    obtain ⟨k, hk⟩ := isConj_iff.mp hconj
    rw [← hk]
    exact ebar_conj_mem hαbar k

theorem MinBad.setup (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    Asc72.Setup (UBar U) (EBar V U) := by
  refine ⟨hm.ebar_class hS h64, ebar_oddT hS h64 hm, ?_⟩
  let EUU : Set ↥U := {u | (u : G) ∈ EU V U}
  have hEUU : Subgroup.closure EUU = ⊤ := by
    have hmap : (Subgroup.closure EUU).map U.subtype = U := by
      rw [MonoidHom.map_closure]
      have himg : U.subtype '' EUU = EU V U := by
        ext x
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact hu
        · intro hx
          exact ⟨⟨x, eu_mem_U hx⟩, hx, rfl⟩
      rw [himg, hm.closure_EU]
    have htop : (⊤ : Subgroup ↥U).map U.subtype = U := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    exact Subgroup.map_subtype_inj.mp (by rw [hmap, htop])
  have himg : (QuotientGroup.mk' (Subgroup.center ↥U)) '' EUU = EBar V U := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ebar_mk_mem hu
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  have hmap := MonoidHom.map_closure (QuotientGroup.mk' (Subgroup.center ↥U)) EUU
  rw [hEUU, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), himg] at hmap
  exact hmap.symm

theorem MinBad.exists_conj (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β)
    {x y : G} (hx : x ∈ EU V U) (hy : y ∈ EU V U) :
    ∃ u ∈ U, ∃ ζ ∈ ZU U, y = u * x * u⁻¹ * ζ := by
  classical
  have hsetup := hm.setup hS h64
  let xU : ↥U := ⟨x, eu_mem_U hx⟩
  let yU : ↥U := ⟨y, eu_mem_U hy⟩
  have hxbar : (xU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [xU] using hx)
  have hybar : (yU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [yU] using hy)
  obtain ⟨k, hk⟩ := isConj_iff.mp (hsetup.isConj hxbar hybar)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective k
  let w : ↥U := u * xU * u⁻¹
  have hw : (w : UBar U) = (yU : UBar U) := hk
  let ζ : ↥U := w⁻¹ * yU
  have hζ : ζ ∈ Subgroup.center ↥U := (QuotientGroup.eq).mp hw
  refine ⟨(u : G), u.2, (ζ : G), mem_center_iff_mem_ZU.mp hζ, ?_⟩
  have hwζ : (w * ζ : ↥U) = yU := by
    rw [show w * ζ = w * (w⁻¹ * yU) from rfl, mul_inv_cancel_left]
  calc y = (yU : G) := rfl
    _ = ((w * ζ : ↥U) : G) := by rw [hwζ]
    _ = (w : G) * (ζ : G) := by rw [Subgroup.coe_mul]
    _ = (u : G) * x * (u : G)⁻¹ * (ζ : G) := by
      simp only [w, xU, Subgroup.coe_mul, Subgroup.coe_inv]

private theorem MinBad.exists_central_mul_mem (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {x : G} (hx : x ∈ EU V U) :
    ∃ ζ : G, ζ ∈ ZU U ∧ ζ * ζ = 1 ∧ ζ ≠ 1 ∧ x * ζ ∈ EU V U := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hαEU : α ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1, V, mem_omegaSet_self V,
      hm.le.1, hm.memα⟩
  obtain ⟨H, h₀, y₀, z₀, ht⟩ := hm.exists_twin hS h64
  obtain ⟨u, huU, ζ₁, hζ₁, hxeq⟩ := hm.exists_conj hS h64 hαEU hx
  let uU : ↥U := ⟨u, huU⟩
  let αU : ↥U := ⟨α, hm.le.2.2.1⟩
  let a : G := (u : G) * α * (u : G)⁻¹
  have haU : a ∈ U := by
    simpa only [a] using U.mul_mem (U.mul_mem huU hm.le.2.2.1) (U.inv_mem huU)
  have haEU : a ∈ EU V U := by
    simpa only [a, uU, αU, Subgroup.coe_mul, Subgroup.coe_inv] using
      eu_conj_mem (w := αU) (by simpa only [αU] using hαEU) uU
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have ha2 : a * a = 1 := by
    calc a * a = (u : G) * (α * α) * (u : G)⁻¹ := by simp only [a]; group
      _ = 1 := by rw [hα2]; group
  have hcomm_aζ : Commute a ζ₁ :=
    Subgroup.mem_centralizer_iff.mp hζ₁.2 a haU
  have hprod : (a * ζ₁) * (a * ζ₁) = 1 := by
    rw [← hxeq]
    exact eu_involution hS hx
  have hζ₁sq : ζ₁ * ζ₁ = 1 := by
    have hconj : (a * ζ₁) * (a * ζ₁) = (a * a) * (ζ₁ * ζ₁) := by
      calc (a * ζ₁) * (a * ζ₁) = a * (ζ₁ * a) * ζ₁ := by group
        _ = a * (a * ζ₁) * ζ₁ := by rw [hcomm_aζ.eq]
        _ = (a * a) * (ζ₁ * ζ₁) := by group
    rw [hconj, ha2, one_mul] at hprod
    exact hprod
  by_cases hζ₁ne : ζ₁ = 1
  · have hx_eq_a : x = a := by rw [hxeq, hζ₁ne, mul_one]
    have hαz₀EU : α * z₀ ∈ EU V U := by
      have hA' : conjSubgroup y₀ V ∈ omegaSet V := by
        obtain ⟨g, hg, -⟩ := ht.sigma
        exact Tim79a.mem_omegaOf.mpr ⟨g, Subgroup.mem_top g, hg⟩
      have hne : α * z₀ ≠ 1 := by
        intro h
        apply ht.not_mem
        have hz : z₀ = α := by
          calc z₀ = α * (α * z₀) := by rw [← mul_assoc, hα2, one_mul]
            _ = α := by rw [h, mul_one]
        rw [hz]
        exact hm.memα
      exact ⟨mem_classD_of_mem hA' ht.mem hne, conjSubgroup y₀ V, hA', ht.le, ht.mem⟩
    have hzu : Commute z₀ (u : G) :=
      (Subgroup.mem_centralizer_iff.mp ht.mem_ZU.2 (u : G) huU).symm
    have hzuinv : Commute z₀ (u : G)⁻¹ := hzu.inv_right
    have haz : a * z₀ = (u : G) * (α * z₀) * (u : G)⁻¹ := by
      simp only [a]
      calc (u : G) * α * (u : G)⁻¹ * z₀ = (u : G) * α * ((u : G)⁻¹ * z₀) := by group
        _ = (u : G) * α * (z₀ * (u : G)⁻¹) := by rw [← hzuinv.eq]
        _ = (u : G) * (α * z₀) * (u : G)⁻¹ := by group
    let αz₀U : ↥U := ⟨α * z₀, eu_mem_U hαz₀EU⟩
    have hαz₀Ueu : (αz₀U : G) ∈ EU V U := by simpa only [αz₀U] using hαz₀EU
    have hconjEU : ((uU * αz₀U * uU⁻¹ : ↥U) : G) ∈ EU V U :=
      eu_conj_mem hαz₀Ueu uU
    have hcoe : ((uU * αz₀U * uU⁻¹ : ↥U) : G) =
        (u : G) * (α * z₀) * (u : G)⁻¹ := by
      simp only [uU, αz₀U, Subgroup.coe_mul, Subgroup.coe_inv]
    have hz₀1 : z₀ ≠ 1 := fun h => ht.not_mem (by rw [h]; exact V.one_mem)
    refine ⟨z₀, ht.mem_ZU, ht.sq, hz₀1, ?_⟩
    rw [hx_eq_a, haz, ← hcoe]
    exact hconjEU
  · refine ⟨ζ₁, hζ₁, hζ₁sq, hζ₁ne, ?_⟩
    have hxζ : x * ζ₁ = a := by
      rw [hxeq]
      calc (u : G) * α * (u : G)⁻¹ * ζ₁ * ζ₁ = (u : G) * α * (u : G)⁻¹ * (ζ₁ * ζ₁) := by
            group
        _ = (u : G) * α * (u : G)⁻¹ := by rw [hζ₁sq, mul_one]
        _ = a := rfl
    rw [hxζ]
    exact haEU

theorem MinBad.commute_of_commute (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {e x y : G} (he : e ∈ EU V U) (hx : x ∈ EU V U)
    (hy : y ∈ EU V U) (hex : Commute e x) (hey : Commute e y) : Commute x y := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hfalse : ∀ {x y : G}, x ∈ EU V U → y ∈ EU V U → BadPair x y →
      Commute e x → Commute e y → False := by
    intro x y hx' hy' hb hex' hey'
    obtain ⟨hxD, A, hA, -, hxA⟩ := hx'
    obtain ⟨hyD, C, hC, -, hyC⟩ := hy'
    obtain ⟨heD, E, hE, -, heE⟩ := he
    have hAE : ∀ z ∈ E, ∀ w ∈ A, Commute z w :=
      hroot.commute_of_commute_mem hE hA heE hxA (classD_ne_one heD) (classD_ne_one hxD) hex'
    have hCE : ∀ z ∈ E, ∀ w ∈ C, Commute z w :=
      hroot.commute_of_commute_mem hE hC heE hyC (classD_ne_one heD) (classD_ne_one hyD) hey'
    exact hS.not_bad_of_common h64 hA hC hE hAE hCE hxA hyC hb
  by_cases hbad : BadPair x y
  · exact (hfalse hx hy hbad hex hey).elim
  · rw [BadPair] at hbad
    push Not at hbad
    rcases hbad with hdvd | hodd
    · have hx2 : x * x = 1 := eu_involution hS hx
      have hy2 : y * y = 1 := eu_involution hS hy
      exact (commute_iff_mul_sq_eq_one hx2 hy2).mpr (orderOf_dvd_iff_pow_eq_one.mp hdvd)
    · by_cases hp1 : orderOf (x * y) = 1
      · have hxy1 : x * y = 1 := orderOf_eq_one_iff.mp hp1
        have hy2 : y * y = 1 := eu_involution hS hy
        have hxy : x = y := by
          calc x = x * (y * y) := by rw [hy2, mul_one]
            _ = (x * y) * y := by group
            _ = y := by rw [hxy1, one_mul]
        rw [hxy]
      · obtain ⟨ζ, hζ, hζ2, hζne, hxζEU⟩ := hm.exists_central_mul_mem hS h64 hx
        have hζord : orderOf ζ = 2 :=
          orderOf_eq_prime (by simpa [pow_two] using hζ2) hζne
        have hxU : x ∈ U := eu_mem_U hx
        have heU : e ∈ U := eu_mem_U he
        have hxyU : x * y ∈ U := U.mul_mem hxU (eu_mem_U hy)
        have hζx : Commute x ζ := Subgroup.mem_centralizer_iff.mp hζ.2 x hxU
        have hζe : Commute e ζ := Subgroup.mem_centralizer_iff.mp hζ.2 e heU
        have hζxy : Commute ζ (x * y) :=
          (Subgroup.mem_centralizer_iff.mp hζ.2 (x * y) hxyU).symm
        have hexζ : Commute e (x * ζ) := hex.mul_right hζe
        have hxy_eq : (x * ζ) * y = ζ * (x * y) := by
          calc (x * ζ) * y = (ζ * x) * y := by rw [hζx.eq]
            _ = ζ * (x * y) := by group
        have hord : orderOf ((x * ζ) * y) = 2 * orderOf (x * y) := by
          have hcop : Nat.Coprime (orderOf ζ) (orderOf (x * y)) := by
            rw [hζord]
            exact hodd.coprime_two_left
          rw [hxy_eq, hζxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hζord]
        have hbadζ : BadPair (x * ζ) y := by
          rw [BadPair, not_or, hord]
          constructor
          · intro hd
            have hle : 2 * orderOf (x * y) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
            have hpos : 0 < orderOf (x * y) := orderOf_pos _
            omega
          · exact Nat.not_odd_iff_even.mpr (even_two_mul _)
        exact (hfalse hxζEU hy hbadζ hexζ hey).elim

theorem MinBad.meetsSq (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    OddTransp.MeetsSq (EBar V U) := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  letI : Fintype ↥V := Fintype.ofFinite _
  letI : Fintype {v : ↥V // v ≠ 1} := Fintype.ofFinite _
  letI : Fintype {v : ↥V // v = 1} := Fintype.ofFinite _
  have hcard : 1 < Fintype.card {v : ↥V // v ≠ 1} := by
    have hcompl := Fintype.card_subtype_compl (α := ↥V) (p := fun v => v = 1)
    have hone : Fintype.card {v : ↥V // v = 1} = 1 := Fintype.card_subtype_eq 1
    have hVcard : 4 ≤ Fintype.card ↥V := by
      simpa only [Nat.card_eq_fintype_card] using hroot.four_le_card
    rw [hone] at hcompl
    have hb : Fintype.card {v : ↥V // v ≠ 1} = Fintype.card ↥V - 1 := hcompl
    omega
  let aV : {v : ↥V // v ≠ 1} :=
    ⟨⟨α, hm.memα⟩, by intro h; exact hα1 (congrArg Subtype.val h)⟩
  obtain ⟨v', hv'ne⟩ : ∃ v' : {v : ↥V // v ≠ 1}, v' ≠ aV :=
    Fintype.exists_ne_of_one_lt_card hcard aV
  let v : G := (v'.1 : G)
  have hvV : v ∈ V := v'.1.2
  have hv1 : v ≠ 1 := fun h => v'.2 (Subtype.ext h)
  have hvα : v ≠ α := by
    intro h
    exact hv'ne (Subtype.ext (Subtype.ext h))
  let αU : ↥U := ⟨α, hm.le.2.2.1⟩
  let vU : ↥U := ⟨v, hm.le.1 hvV⟩
  have hαEU : α ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1, V, mem_omegaSet_self V,
      hm.le.1, hm.memα⟩
  have hvEU : v ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hvV hv1, V, mem_omegaSet_self V,
      hm.le.1, hvV⟩
  have hαbar : (αU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [αU] using hαEU)
  have hvbar : (vU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [vU] using hvEU)
  have hαv : Commute α v :=
    (Subgroup.commute_subtype_iff (⟨α, hm.memα⟩) (⟨v, hvV⟩)).mpr
      (hroot.toHyp.elem.1.is_comm.comm _ _)
  have hcommU : Commute αU vU := (Subgroup.commute_subtype_iff αU vU).mp hαv
  have hcomm : Commute (αU : UBar U) (vU : UBar U) :=
    hcommU.map (QuotientGroup.mk' (Subgroup.center ↥U))
  have hαv_ne1 : α * v ≠ 1 := by
    intro h
    apply hvα
    calc v = α * (α * v) := by rw [← mul_assoc, hα2, one_mul]
      _ = α := by rw [h, mul_one]
  have hprodEU : α * v ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) (V.mul_mem hm.memα hvV) hαv_ne1,
      V, mem_omegaSet_self V, hm.le.1, V.mul_mem hm.memα hvV⟩
  have hprod : (αU : UBar U) * (vU : UBar U) ∈ EBar V U := by
    have hprodU : ((αU * vU : ↥U) : G) ∈ EU V U := by
      simpa only [αU, vU, Subgroup.coe_mul] using hprodEU
    have h := ebar_mk_mem hprodU
    rwa [QuotientGroup.mk_mul] at h
  have hne : (αU : UBar U) ≠ (vU : UBar U) := by
    intro heq
    have hαU2 : αU * αU = 1 :=
      Subtype.ext (by simpa only [αU, Subgroup.coe_mul, Subgroup.coe_one] using hα2)
    have hprod1 : ((αU * vU : ↥U) : UBar U) = 1 := by
      rw [QuotientGroup.mk_mul]
      calc (αU : UBar U) * (vU : UBar U) = (αU : UBar U) * (αU : UBar U) := by rw [← heq]
        _ = ((αU * αU : ↥U) : UBar U) := by rw [QuotientGroup.mk_mul]
        _ = 1 := by rw [hαU2, QuotientGroup.mk_one]
    have hcen : αU * vU ∈ Subgroup.center ↥U := (QuotientGroup.eq_one_iff _).mp hprod1
    have hzu := mem_center_iff_mem_ZU.mp hcen
    have hmem : α * v ∈ V ⊓ ZU U := by
      refine ⟨V.mul_mem hm.memα hvV, ?_⟩
      show α * v ∈ ZU U
      simpa only [αU, vU, Subgroup.coe_mul] using hzu
    rw [hm.inf_ZU hS h64] at hmem
    exact hαv_ne1 (Subgroup.mem_bot.mp hmem)
  exact ⟨(αU : UBar U), hαbar, (vU : UBar U), hvbar, hne, hcomm, hprod⟩

theorem MinBad.disconnected (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) : Connectivity.Disconnected (EBar V U) := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hβ1 : β ≠ 1 := hm.beta_ne_one hS
  let αU : ↥U := ⟨α, hm.le.2.2.1⟩
  let βU : ↥U := ⟨β, hm.le.2.2.2⟩
  have hαEU : α ∈ EU V U :=
    ⟨mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1, V, mem_omegaSet_self V,
      hm.le.1, hm.memα⟩
  have hβEU : β ∈ EU V U :=
    ⟨mem_classD_of_mem hm.memB hm.memβ hβ1, B, hm.memB, hm.le.2.1, hm.memβ⟩
  have hαbar : (αU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [αU] using hαEU)
  have hβbar : (βU : UBar U) ∈ EBar V U := ebar_mk_mem (by simpa only [βU] using hβEU)
  have hreach : ∀ {x y : UBar U}, x ∈ EBar V U → y ∈ EBar V U →
      Connectivity.Reach (EBar V U) x y → Commute x y := by
    intro x y hx hy h
    induction h with
    | refl => exact Commute.refl x
    | tail hxy hyz ih =>
      rename_i y z
      obtain ⟨hyD, hzD, hyzcomm⟩ := hyz
      obtain ⟨ux, huxEU, huxEq⟩ := hx
      obtain ⟨uy, huyEU, huyEq⟩ := hyD
      obtain ⟨uz, huzEU, huzEq⟩ := hzD
      have hxyG : Commute (ux : G) (uy : G) :=
        Sec6Hyp.commute_of_mk hS h64 huxEU huyEU (by
          simpa only [huxEq, huyEq] using ih ⟨uy, huyEU, huyEq⟩)
      have hyzG : Commute (uy : G) (uz : G) :=
        Sec6Hyp.commute_of_mk hS h64 huyEU huzEU (by
          simpa only [huyEq, huzEq] using hyzcomm)
      have hxzG : Commute (ux : G) (uz : G) :=
        hm.commute_of_commute hS h64 huyEU huxEU huzEU hxyG.symm hyzG
      have hxzU : Commute ux uz := (Subgroup.commute_subtype_iff ux uz).mp hxzG
      simpa only [QuotientGroup.mk'_apply, huxEq, huzEq] using
        hxzU.map (QuotientGroup.mk' (Subgroup.center ↥U))
  refine ⟨(αU : UBar U), hαbar, (βU : UBar U), hβbar, ?_⟩
  intro hR
  exact (ebar_V_B_not_commute hS h64 hm (v := αU) (b := βU) hm.memα
    (by intro h; exact hα1 (congrArg Subtype.val h)) hm.memβ
    (by intro h; exact hβ1 (congrArg Subtype.val h)))
    (hreach hαbar hβbar hR)

theorem MinBad.center_eq_bot (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β) :
    Subgroup.center (UBar U) = ⊥ := by
  have hsetup := hm.setup hS h64
  have hsq := hm.meetsSq hS h64
  have hcomm : commutator (UBar U) = ⊤ := OddTransp.commutator_eq_top hsetup hsq
  exact
    CFSG.LocalAnalysis.RankThreeUC.S15.R1515F.center_quotient_center_eq_bot_of_isPerfect_quotient
      (D := ↥U) ⟨hcomm⟩


end CFSG.RankThree.GF2n.Tim81
