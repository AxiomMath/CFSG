module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47K1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Card
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Perp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Quad
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_conj_mem_pCoreOf {K : Subgroup G} {k : G} (hk : k ∈ K) {o : G}
    (ho : o ∈ pCoreOf 2 K) : k * o * k⁻¹ ∈ pCoreOf 2 K := by
  have h := s16c1_conjSubgroup_pCoreOf_self K (K.inv_mem hk)
  rw [← h, mem_conjSubgroup_iff]
  have e : k⁻¹ * (k * o * k⁻¹) * k⁻¹⁻¹ = o := by group
  rw [e]
  exact ho

theorem s16c1_G47_le_centralizer {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V) :
    V ≤ centralizer ({z} : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact IsElemAbelian.comm hV hz hv

theorem s16c1_G47_comm_mem_uOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    {r : G} (hrQ : r ∈ pCoreOf 2 (centralizer ({z} : Set G)))
    (hrN : r ∈ normalizer (V : Set G)) {w : G} (hw : w ∈ V) :
    r * w * r⁻¹ * w⁻¹ ∈ uOne V z := by
  have hwH : w ∈ centralizer ({z} : Set G) := s16c1_G47_le_centralizer hV hz hw
  have h1 : r * w * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hrN w).1 hw
  have h2 : w * r⁻¹ * w⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) :=
    s16c1_G47_conj_mem_pCoreOf hwH ((pCoreOf 2 (centralizer ({z} : Set G))).inv_mem hrQ)
  refine Subgroup.mem_inf.2 ⟨V.mul_mem h1 (V.inv_mem hw), ?_⟩
  have e : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 (centralizer ({z} : Set G))).mul_mem hrQ h2

theorem s16c1_G47_pCore_le_of_card_two (D : Data G) (hkit : OmegaKit) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : IntMod V hV} (ctx : G47Ctx D V₀ V L hV x)
    (hU4 : IsU4 (Bar2 L) 1) {X : Subgroup G} (hXL : X ≤ L)
    (hcard : Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) ≤ 2) :
    X ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ pCoreOf 2 L := by
  classical
  have hS := ctx.sect
  have hc := ctx.caseOne
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS ctx.setup
  have hzU : x.val ∈ uOne V x.val :=
    s16c1_zpowers_le_uOne hV x.val_mem (Subgroup.mem_zpowers x.val)
  have hzmem : mkTil V₀ V hV x ∈ imgTil V₀ V hV (uOne V x.val) :=
    (mem_imgTil V₀ V hV _ _).2 ⟨x, hzU, rfl⟩
  have hpos : 1 < Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    rw [hbot] at hzmem
    exact hz1 (Subgroup.mem_bot.1 hzmem)
  have hcard2 : Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) = 2 := by omega
  obtain ⟨c0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(imgTil V₀ V hV (uOne V x.val)))).1 hcard2
  have hUz : ∀ u ∈ imgTil V₀ V hV (uOne V x.val), u = 1 ∨ u = mkTil V₀ V hV x := by
    intro u hu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · right
      have h1 : (⟨u, hu⟩ : ↥(imgTil V₀ V hV (uOne V x.val))) = c0 :=
        huniq _ (fun h => hu1 (congrArg Subtype.val h))
      have h2 : (⟨mkTil V₀ V hV x, hzmem⟩ : ↥(imgTil V₀ V hV (uOne V x.val))) = c0 :=
        huniq _ (fun h => hz1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  intro r hr
  obtain ⟨hrX, hrQ⟩ := Subgroup.mem_inf.1 hr
  have hrL : r ∈ L := hXL hrX
  have hrs : r ∈ stabTil V₀ V := s16c1_le_stabTil D hS hrL
  have hrN : r ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V hrs
  have hfix : ∀ q : Vtil V₀ V hV, actTil V₀ V hV ⟨r, hrs⟩ q = q ∨
      actTil V₀ V hV ⟨r, hrs⟩ q = q * mkTil V₀ V hV x := by
    intro q
    obtain ⟨w, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [actTil_mk]
    set w' : IntMod V hV := actStab V₀ V hV ⟨r, hrs⟩ w with hw'
    have hu : (w' * w⁻¹).val ∈ uOne V x.val := by
      rw [IntMod.val_mul, IntMod.val_inv, hw', actStab_apply_val]
      exact s16c1_G47_comm_mem_uOne hV x.val_mem hrQ hrN w.val_mem
    have hmem : mkTil V₀ V hV (w' * w⁻¹) ∈ imgTil V₀ V hV (uOne V x.val) :=
      (mem_imgTil V₀ V hV _ _).2 ⟨_, hu, rfl⟩
    have hsplit : mkTil V₀ V hV w' = mkTil V₀ V hV (w' * w⁻¹) * mkTil V₀ V hV w := by
      rw [← map_mul, inv_mul_cancel_right]
    rcases hUz _ hmem with h | h
    · left
      rw [hsplit, h, one_mul]
    · right
      rw [hsplit, h, mul_comm]
  have hmemBar : actTil V₀ V hV ⟨r, hrs⟩ ∈ lBar V₀ V hV L :=
    actTil_mem_barSub V₀ V hV hrL hrs
  have hone : actTil V₀ V hV ⟨r, hrs⟩ = 1 :=
    (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2 _ hmemBar _ hz1 hfix
  exact (s16c1_actTil_eq_one_iff D hS hc hU4 ⟨r, hrs⟩ hrL).1 hone

theorem s16c1_G47_imgTil_large (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D V₀ V L hV x) (hU4 : IsU4 (Bar2 L) 1) (h46 : Concl1646 L x.val) :
    64 ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) := by
  classical
  by_contra hlt
  push Not at hlt
  have hS := ctx.sect
  have hc := ctx.caseOne
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS ctx.setup
  obtain ⟨Q, hQ, hQi⟩ := (h41 V₀ V L hV hS hc).1
  have hQz : Q (mkTil V₀ V hV x) = 0 := ctx.sing Q hQ hQi
  have h960 : Nat.card ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960 :=
    s16c1_card_of_isE16A5 (((h41 V₀ V L hV hS hc).2 Q hQ hQi).1 _ hz1 hQz)
  have hbar := s16c1_barSub_xInf_eq_ptCent (s16c1_le_stabTil D hS) x ctx.e16 h960
  have hstab : StableUnder (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x))
      (imgTil V₀ V hV (uOne V x.val)) := by
    intro φ hφ q hq
    rw [← hbar] at hφ
    exact s16c1_stable_imgTil_uOne x L φ (barSub_mono V₀ V hV (perfectCore_le _) hφ) q hq
  have hIrr := (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.1 _ hz1 h960 _ hstab
  have hle2 : Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) ≤ 2 := by
    rcases hIrr with h | h | h | h <;> omega
  have hXL : xInf L x.val ≤ L := (perfectCore_le _).trans inf_le_right
  have hXH : xInf L x.val ≤ centralizer ({x.val} : Set G) := (perfectCore_le _).trans inf_le_left
  have hcore := s16c1_G47_pCore_le_of_card_two D hkit ctx hU4 hXL hle2
  have hcmp := s16c1_G47_card_starImg_le hXL hXH hcore
  have h960' : Nat.card ↥(starImg L (xInf L x.val)) = 960 := by
    rw [← s16c1_card_barSub_eq_card_starImg D hS hc hU4 hXL]
    exact s16c1_card_of_isE16A5 ctx.e16
  have h120 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) = 120 :=
    (s16c1_sl2five_facts h46.2.2.1).1
  omega

theorem s16c1_G47_perp_le_imgTil_uOne (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D V₀ V L hV x)
    (hU : 64 ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val)))
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar V₀ V hV L)) :
    ∀ y : Vtil V₀ V hV, polarQ Q (mkTil V₀ V hV x) y = 0 →
      y ∈ imgTil V₀ V hV (uOne V x.val) := by
  obtain ⟨hS, hc, hx, hsing, -, he16, -, -⟩ := ctx
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS hx
  have hQz : Q (mkTil V₀ V hV x) = 0 := hsing Q hQ hQi
  have h960 : Nat.card ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960 :=
    s16c1_card_of_isE16A5 (((h41 V₀ V L hV hS hc).2 Q hQ hQi).1 _ hz1 hQz)
  have hbar := s16c1_barSub_xInf_eq_ptCent (s16c1_le_stabTil D hS) x he16 h960
  have hstab : StableUnder (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x))
      (imgTil V₀ V hV (uOne V x.val)) := by
    intro φ hφ q hq
    rw [← hbar] at hφ
    exact s16c1_stable_imgTil_uOne x L φ (barSub_mono V₀ V hV (perfectCore_le _) hφ) q hq
  have hW64 : Nat.card (Vtil V₀ V hV) = 64 := by
    have h := Sixteen21.card_vTil_of_case1 (V₀ := V₀) hV hc
    simpa using h
  have hIrr := (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.1 _ hz1 h960
  refine s16c1_perp_le_of_stable hQ.1
    (fun w => by rw [← pow_two]; exact s15_Infra_vtil_sq_eq_one V₀ V hV w) hW64
    (C := ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) (fun h hh w => hQi h hh.1 w) hz1 ?_
    hIrr hstab hU
  intro φ hφ
  simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.mp hφ.2

theorem s16c1_G47_cTilde_of_cent_uOne (D : Data G) (hkit : OmegaKit) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (h41 : R16_41 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (ctx : G47Ctx D V₀ V L hV x)
    (hU : 64 ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val))) {m : G} (hmM : m ∈ D.M)
    (hm : ∀ u ∈ uOne V x.val, m * u * m⁻¹ = u) : m ∈ F11.CTilde D.M V₀ V := by
  have hS := ctx.sect
  have hc := ctx.caseOne
  obtain ⟨Q, hQ, hQi⟩ := (h41 V₀ V L hV hS hc).1
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS ctx.setup
  have hQz : Q (mkTil V₀ V hV x) = 0 := ctx.sing Q hQ hQi
  have hms : m ∈ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀ hmM
  have hσN : actTil V₀ V hV ⟨m, hms⟩ ∈
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    s16c1_Mbar_le_normalizer hkitB hS hc (actTil_mem_barSub V₀ V hV hmM hms)
  have hσQ : ∀ w, Q (actTil V₀ V hV ⟨m, hms⟩ w) = Q w :=
    (hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.1 Q hQ hQi _ hσN
  have hperp := s16c1_G47_perp_le_imgTil_uOne D hkit h41 ctx hU hQ hQi
  have hfix : ∀ y : Vtil V₀ V hV, polarQ Q (mkTil V₀ V hV x) y = 0 →
      actTil V₀ V hV ⟨m, hms⟩ y = y := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_imgTil V₀ V hV _ y).1 (hperp y hy)
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact hm u.val hu
  have hone : actTil V₀ V hV ⟨m, hms⟩ = 1 :=
    s16c1_no_singular_transvection hQ.1
      (fun w => by rw [← pow_two]; exact s15_Infra_vtil_sq_eq_one V₀ V hV w) _ hσQ hz1 hQz hfix
  have htriv : ∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ V₀ :=
    (actTil_eq_one_iff V₀ V hV ⟨m, hms⟩).1 hone
  exact (CFSG.LocalAnalysis.WeakClosure81.mem_cTilde_iff_centralizes hV hP.le_normalizer
    hP.le_normalizer₀).2 ⟨hmM, htriv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
