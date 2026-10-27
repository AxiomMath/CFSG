module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8CentF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.InvertingElements
public import CFSG.GroupTheory.CoprimeCovering

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def cartanL1 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (FL : Subgroup G) : Subgroup G :=
  c.L ⊓ Subgroup.centralizer (FL : Set G)

private noncomputable def cartanN0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (FL : Subgroup G) : Subgroup G :=
  cartanL1 c FL ⊓ CFSG.Open.pCoreOf 2 c.L

private theorem eq_of_bar2_eq_of_inf_pCore_bot {L DL : Subgroup G} (hDLleL : DL ≤ L)
    (hdisj : DL ⊓ CFSG.Open.pCoreOf 2 L = ⊥) {a b : G} (ha : a ∈ DL) (hb : b ∈ DL)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, hDLleL ha⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨b, hDLleL hb⟩) : a = b := by
  have h' : (QuotientGroup.mk (⟨a, hDLleL ha⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      QuotientGroup.mk ⟨b, hDLleL hb⟩ := h
  have hdiv : (⟨a, hDLleL ha⟩ : ↥L) / ⟨b, hDLleL hb⟩ ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_iff_div_mem).mp h'
  have hmemcore : a * b⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    have hmap := Subgroup.mem_map_of_mem L.subtype hdiv
    have hcoe : L.subtype ((⟨a, hDLleL ha⟩ : ↥L) / ⟨b, hDLleL hb⟩) = a * b⁻¹ := by
      simp [div_eq_mul_inv]
    rw [hcoe] at hmap
    exact hmap
  have hmemDL : a * b⁻¹ ∈ DL := DL.mul_mem ha (DL.inv_mem hb)
  have hbot : a * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hdisj]
    exact ⟨hmemDL, hmemcore⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)

private theorem mem_normalizer_of_decomp {v : G} {F DL FL : Subgroup G}
    (hDLF : DL ≤ F) (hFLF : FL ≤ F)
    (hdecomp : ∀ x ∈ F, ∃ d ∈ DL, ∃ e ∈ FL, x = d * e)
    (hinv : ∀ d ∈ DL, v * d * v⁻¹ = d⁻¹)
    (hcent : ∀ e ∈ FL, v * e * v⁻¹ = e) :
    v ∈ Subgroup.normalizer (F : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y hy
    obtain ⟨x, hxF, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨d, hd, e, he, rfl⟩ := hdecomp x hxF
    change v * (d * e) * v⁻¹ ∈ F
    rw [show v * (d * e) * v⁻¹ = (v * d * v⁻¹) * (v * e * v⁻¹) by group,
      hinv d hd, hcent e he]
    exact F.mul_mem (hDLF (DL.inv_mem hd)) (hFLF he)
  · rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]

private theorem inf_cartan_eq_bot (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    DL ⊓ (D.T ⊓ c.L) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let TL : Subgroup G := D.T ⊓ c.L
  have hT2 : IsPGroup 2 TL :=
    IsPGroup.to_inf_left (p := 2) (H := D.T) (K := c.L)
      (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG)
  have hDLodd : Odd (Nat.card DL) := by
    rw [hDLcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hcopTL : Nat.Coprime (Nat.card TL) (Nat.card DL) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk, hDLcard]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hDLcard ▸ hDLodd))
  rw [show DL ⊓ (D.T ⊓ c.L) = DL ⊓ TL from rfl, inf_comm]
  exact Subgroup.inf_eq_bot_of_coprime hcopTL

private theorem cartan_image_disj (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    DL ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ := by
  have hDLinfTL := inf_cartan_eq_bot D Ch c h3 hDLcard
  apply le_antisymm _ bot_le
  intro x hx
  have hxTL : x ∈ D.T ⊓ c.L :=
    ⟨(Ctx23L.pCoreOf_L_le_T D Ch c) hx.2,
      CFSG.LieType.BorelTits.pCoreOf_le 2 c.L hx.2⟩
  have hxbot : x ∈ DL ⊓ (D.T ⊓ c.L) := ⟨hx.1, hxTL⟩
  rw [hDLinfTL] at hxbot
  exact hxbot

private theorem cartan_image_card (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    Nat.card ((DL.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))) =
      2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
  have hDLleL : DL ≤ c.L := hDLleB.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)
  have hdisj := cartan_image_disj D Ch c h3 hDLcard
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hker : (DL.subgroupOf c.L) ⊓ q.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    apply le_antisymm _ bot_le
    intro x hx
    have hxDL : (x : G) ∈ DL := Subgroup.mem_subgroupOf.mp hx.1
    have hxcore : (x : G) ∈ CFSG.Open.pCoreOf 2 c.L :=
      (CFSG.mem_openPCoreOf_iff x).mpr hx.2
    have hmem : (x : G) ∈ DL ⊓ CFSG.Open.pCoreOf 2 c.L := ⟨hxDL, hxcore⟩
    rw [hdisj] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot q hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDLleL).toEquiv, hDLcard]

private theorem cartan_image_data (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∃ (S : Sylow 2 (Bar2 c.L)) (H : Subgroup (Bar2 c.L)),
      (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
        ((D.T ⊓ c.L).subgroupOf c.L) ∧
      H = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) (DL.subgroupOf c.L) ∧
      H ≤ Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) ∧
      Nat.card H = 2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
  classical
  let H : Subgroup (Bar2 c.L) :=
    (DL.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
  obtain ⟨S, hS⟩ := Ctx23L.sylowImage_L D Ch c
  have hHle : H ≤ Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) := by
    rintro _ ⟨d, hd, rfl⟩
    exact borelOf_mem_normalizer_sylow (D := D) (Ch := Ch) c hS
      (hDLleB (Subgroup.mem_subgroupOf.mp hd))
  exact ⟨S, H, hS, rfl, hHle, cartan_image_card D Ch c h3 hDLleB hDLcard⟩

private theorem cartan_action_preserves_sylow (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {F : Subgroup G} (hFNT : F ≤ Subgroup.normalizer (D.T : Set G))
    (hFNL : F ≤ Subgroup.normalizer (c.L : Set G)) (f : ↥F)
    {S : Sylow 2 (Bar2 c.L)}
    (hS : (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      ((D.T ⊓ c.L).subgroupOf c.L)) :
    ∀ x ∈ (S : Subgroup (Bar2 c.L)),
      UC6S846.rhoL c.L ⟨f, hFNL f.2⟩ x ∈ (S : Subgroup (Bar2 c.L)) := by
  intro x hx
  have hfNL : (f : G) ∈ Subgroup.normalizer (c.L : Set G) := hFNL f.2
  have hfTL : (f : G) ∈ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) :=
    CFSG.ABGLocalTools.mem_normalizer_inf (hFNT f.2) hfNL
  have hθmap : Subgroup.map
      (UC6S846.rhoL c.L ⟨f, hFNL f.2⟩).toMonoidHom (S : Subgroup (Bar2 c.L)) =
      (S : Subgroup (Bar2 c.L)) := by
    rw [hS]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
      (L := c.L) (U := D.T ⊓ c.L) ⟨f, hFNL f.2⟩ hfTL
  rw [← hθmap]
  exact Subgroup.mem_map_of_mem (UC6S846.rhoL c.L ⟨f, hFNL f.2⟩).toMonoidHom hx

private theorem cartan_action_fixes_image (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {DL F : Subgroup G} (hDLF : DL ≤ F)
    (hFcomm : IsMulCommutative F) (hFNL : F ≤ Subgroup.normalizer (c.L : Set G))
    (f : ↥F) {H : Subgroup (Bar2 c.L)}
    (hHdef : H = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L)) :
    ∀ h ∈ H, UC6S846.rhoL c.L ⟨f, hFNL f.2⟩ h = h := by
  intro h hh
  have hfNL : (f : G) ∈ Subgroup.normalizer (c.L : Set G) := hFNL f.2
  rw [hHdef] at hh
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
  have hdL : (d : G) ∈ c.L := d.2
  have hdDL : (d : G) ∈ DL := Subgroup.mem_subgroupOf.mp hd
  have hdF : (d : G) ∈ F := hDLF hdDL
  have hfd : (f : G) * (d : G) = (d : G) * (f : G) :=
    congrArg Subtype.val (hFcomm.is_comm.comm f ⟨(d : G), hdF⟩)
  have hfeq : (⟨(f : G) * (d : G) * (f : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hfNL (d : G)).mp hdL⟩ : ↥c.L) = d := by
    apply Subtype.ext
    change (f : G) * (d : G) * (f : G)⁻¹ = (d : G)
    rw [hfd]
    group
  change UC6S846.rhoL c.L ⟨(f : G), hFNL f.2⟩
      (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) d) =
    QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) d
  rw [rhoL_apply_mk hfNL d, hfeq]

private theorem mem_centralizer_of_conj_eq_of_fixes {X : Type} [Group X]
    {H : Subgroup X} {θ : MulAut X} (hfix : ∀ h ∈ H, θ h = h) {y : X}
    (hy : MulAut.conj y = θ) : y ∈ Subgroup.centralizer (H : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hyh : y * h * y⁻¹ = h := by
    rw [← MulAut.conj_apply, hy]
    exact hfix h hh
  calc h * y = (y * h * y⁻¹) * y := by rw [hyh]
    _ = y * h := by group

private theorem cartan_action_odd {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {F : Subgroup G} (hFodd : Odd (Nat.card F))
    (hFNL : F ≤ Subgroup.normalizer (c.L : Set G)) (f : ↥F) :
    Odd (orderOf (UC6S846.rhoL c.L ⟨f, hFNL f.2⟩)) := by
  have hfodd : Odd (orderOf (f : G)) := by
    have h := Odd.of_dvd_nat hFodd (orderOf_dvd_natCard f)
    exact (Subgroup.orderOf_coe f).symm ▸ h
  have h1 : orderOf (UC6S846.rhoL c.L ⟨f, hFNL f.2⟩) ∣ orderOf
      (⟨(f : G), hFNL f.2⟩ : ↥(Subgroup.normalizer (c.L : Set G))) :=
    orderOf_map_dvd (UC6S846.rhoL c.L) ⟨(f : G), hFNL f.2⟩
  have h2 : Odd (orderOf
      (⟨(f : G), hFNL f.2⟩ : ↥(Subgroup.normalizer (c.L : Set G)))) := by
    have h3 : Odd (orderOf
        ((⟨(f : G), hFNL f.2⟩ : ↥(Subgroup.normalizer (c.L : Set G))) : G)) := by
      simpa using hfodd
    exact Subgroup.orderOf_coe (⟨(f : G), hFNL f.2⟩ :
      ↥(Subgroup.normalizer (c.L : Set G))) ▸ h3
  exact Odd.of_dvd_nat h2 h1

private theorem exists_cartan_inner_action (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F)
    (hFNL : F ≤ Subgroup.normalizer (c.L : Set G))
    (hFNT : F ≤ Subgroup.normalizer (D.T : Set G)) (f : ↥F) :
    ∃ y ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) (DL.subgroupOf c.L),
      UC6S846.rhoL c.L ⟨f, hFNL f.2⟩ = MulAut.conj y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL2, -⟩ := h23 h1930 c
  have hL2' : IsL2 (Bar2 c.L) (CFSG.Open.pRank 2 D.Z) := by simpa using hL2
  obtain ⟨S, H, hS, hHdef, hHle, hHcard⟩ :=
    cartan_image_data D Ch c h3 hDLleB hDLcard
  let θ : MulAut (Bar2 c.L) := UC6S846.rhoL c.L ⟨f, hFNL f.2⟩
  have hpres : ∀ x ∈ (S : Subgroup (Bar2 c.L)), θ x ∈ (S : Subgroup (Bar2 c.L)) :=
    cartan_action_preserves_sylow D Ch c hFNT hFNL f hS
  have hθodd : Odd (orderOf θ) := cartan_action_odd hFodd hFNL f
  have hfixH : ∀ h ∈ H, θ h = h :=
    cartan_action_fixes_image D Ch c hDLF hFcomm hFNL f hHdef
  have hfixmod : ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (Bar2 c.L)) := by
    intro h hh
    rw [hfixH h hh, mul_inv_cancel]
    exact (S : Subgroup (Bar2 c.L)).one_mem
  obtain ⟨y, hy⟩ := kL2OddAutInner_holds (Bar2 c.L) 0
    (CFSG.Open.pRank 2 D.Z) (by simpa using hL2')
    S θ hθodd hpres H hHle hHcard hfixmod
  have hcent := (kL2TorusSelfCent_holds (Bar2 c.L) (CFSG.Open.pRank 2 D.Z)
    hL2' S H hHle hHcard).2
  have hyH : y ∈ H := hcent (mem_centralizer_of_conj_eq_of_fixes hfixH hy)
  rw [hHdef] at hyH
  exact ⟨y, hyH, hy.symm⟩

private theorem exists_cartan_image_eq (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F)
    (hFNL : F ≤ Subgroup.normalizer (c.L : Set G))
    (hFNT : F ≤ Subgroup.normalizer (D.T : Set G))
    (φ : ↥F →* MulAut (Bar2 c.L))
    (hφ : ∀ f : ↥F, φ f = UC6S846.rhoL c.L ⟨f, hFNL f.2⟩) (f : ↥F) :
    ∃ d : G, ∃ hd : d ∈ DL, φ f = φ ⟨d, hDLF hd⟩ := by
  obtain ⟨y, hyH, hy⟩ :=
    exists_cartan_inner_action D Ch h23 h1930 c h3 hDLleB hDLcard hDLF hFodd
      hFcomm hFNL hFNT f
  obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hyH
  let dG : G := (d : G)
  have hdF : dG ∈ F := hDLF (Subgroup.mem_subgroupOf.mp hd)
  refine ⟨dG, Subgroup.mem_subgroupOf.mp hd, ?_⟩
  rw [hφ f, hφ ⟨dG, hdF⟩]
  calc UC6S846.rhoL c.L ⟨f, hFNL f.2⟩ = MulAut.conj y := hy
    _ = MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) d) := by rw [← hdy]
    _ = UC6S846.rhoL c.L ⟨dG, hFNL hdF⟩ :=
      (UC6S846.rhoL_inner c.L dG d.2).symm

private theorem exists_cartan_decomp (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F)
    (hFNL : F ≤ Subgroup.normalizer (c.L : Set G))
    (hFNT : F ≤ Subgroup.normalizer (D.T : Set G))
    (φ : ↥F →* MulAut (Bar2 c.L))
    (hφ : ∀ f : ↥F, φ f = UC6S846.rhoL c.L ⟨f, hFNL f.2⟩) (f : ↥F) :
    ∃ d : G, ∃ hd : d ∈ DL,
      (f : G) * d⁻¹ ∈ φ.ker.map F.subtype := by
  obtain ⟨d, hd, heq⟩ :=
    exists_cartan_image_eq D Ch h23 h1930 c h3 hDLleB hDLcard hDLF hFodd hFcomm
      hFNL hFNT φ hφ f
  have hdF : d ∈ F := hDLF hd
  refine ⟨d, hd, ?_⟩
  have hmem : φ (f * ⟨d, hdF⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact Subgroup.mem_map_of_mem F.subtype (MonoidHom.mem_ker.mpr hmem)

private theorem cartan_kernel_commutator {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {F : Subgroup G} (hFNL : F ≤ Subgroup.normalizer (c.L : Set G))
    (φ : ↥F →* MulAut (Bar2 c.L))
    (hφ : ∀ f : ↥F, φ f = UC6S846.rhoL c.L ⟨f, hFNL f.2⟩)
    {r : G} (hr : r ∈ φ.ker.map F.subtype) {x : G} (hx : x ∈ c.L) :
    ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L := by
  obtain ⟨rF, hrF, rfl⟩ := Subgroup.mem_map.mp hr
  have hφr : φ rF = 1 := MonoidHom.mem_ker.mp hrF
  rw [hφ rF] at hφr
  have hfix : UC6S846.rhoL c.L ⟨(rF : G), hFNL rF.2⟩
      (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨x, hx⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨x, hx⟩ := by
    rw [hφr]
    rfl
  have hmem : (rF : G) * x * (rF : G)⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
    (UC6S846.rhoL_fix_iff c.L ⟨(rF : G), hFNL rF.2⟩ ⟨x, hx⟩).mp hfix
  have hmem' : F.subtype rF * x * (F.subtype rF)⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
    simpa using hmem
  rw [commutatorElement_def]
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    (CFSG.Open.pCoreOf 2 c.L).inv_mem hmem'

private theorem exists_cartan_kernel (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F)
    (hFN : F ≤ c.N) (hFNT : F ≤ Subgroup.normalizer (D.T : Set G)) :
    ∃ FL : Subgroup G, FL ≤ F ∧
      (∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L) ∧
      (∀ f ∈ F, ∃ d ∈ DL, ∃ e ∈ FL, f = d * e) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL2, -⟩ := h23 h1930 c
  let n := CFSG.Open.pRank 2 D.Z
  have hL2' : IsL2 (Bar2 c.L) n := by simpa [n] using hL2
  have hLleN : c.L ≤ c.N := le_sup_left.trans (Ctx23L.sup_le_N D Ch c)
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleN).mp
      (Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c)
  have hFNL : F ≤ Subgroup.normalizer (c.L : Set G) := hFN.trans hNL
  let φ : ↥F →* MulAut (Bar2 c.L) :=
    (UC6S846.rhoL c.L).comp (Subgroup.inclusion hFNL)
  let FL : Subgroup G := φ.ker.map F.subtype
  have hFLleF : FL ≤ F := Subgroup.map_subtype_le _
  have hFLcomm : ∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L :=
    fun r hr x hx => cartan_kernel_commutator c hFNL φ (fun _ => rfl) hr hx
  have hsplit : ∀ f ∈ F, ∃ d ∈ DL, ∃ e ∈ FL, f = d * e := by
    intro f hfF
    obtain ⟨d, hd, hmem⟩ :=
      exists_cartan_decomp D Ch h23 h1930 c h3 hDLleB hDLcard hDLF hFodd hFcomm
        hFNL hFNT φ (fun _ => rfl) ⟨f, hfF⟩
    have hdF : d ∈ F := hDLF hd
    let e : G := f * d⁻¹
    have hfd : f * d = d * f :=
      congrArg Subtype.val (hFcomm.is_comm.comm ⟨f, hfF⟩ ⟨d, hdF⟩)
    have hcomm : d * e = f := by
      calc d * e = d * (f * d⁻¹) := by rw [show e = f * d⁻¹ from rfl]
        _ = (d * f) * d⁻¹ := by group
        _ = (f * d) * d⁻¹ := by rw [← hfd]
        _ = f := by group
    exact ⟨d, hd, e, hmem, hcomm.symm⟩
  exact ⟨FL, hFLleF, hFLcomm, hsplit⟩

private theorem exists_centralizing_translate (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {F FL : Subgroup G} (hFLF : FL ≤ F)
    (hFodd : Odd (Nat.card F)) (hFN : F ≤ c.N)
    (hFLcomm : ∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L)
    {x : G} (hx : x ∈ c.L) :
    ∃ n ∈ CFSG.Open.pCoreOf 2 c.L,
      x * n ∈ c.L ⊓ Subgroup.centralizer (FL : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := CFSG.Open.pCoreOf 2 c.L
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hPn : (P.subgroupOf c.L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleL).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L)
  have hLleN : c.L ≤ c.N := le_sup_left.trans (Ctx23L.sup_le_N D Ch c)
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleN).mp
      (Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c)
  have hFLn : FL ≤ Subgroup.normalizer (P : Set G) :=
    ((hFLF.trans hFN).trans hNL).trans (UC6S846.normalizer_le_normalizer_pCoreOf c.L)
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hsolv : Group.IsSolvable ↥P := inferInstance
  have hFLodd : Odd (Nat.card FL) := hFodd.of_dvd_nat (Subgroup.card_dvd_of_le hFLF)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card FL) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hFLodd)
  exact CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem
    hPleL hPn hFLn hsolv hcop hx (fun r hr => hFLcomm r hr x hx)

private theorem exists_covering_subgroup (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {F FL : Subgroup G} (hFLF : FL ≤ F)
    (hFodd : Odd (Nat.card F)) (hFN : F ≤ c.N)
    (hFLcomm : ∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L) :
    c.L ≤ (c.L ⊓ Subgroup.centralizer (FL : Set G)) ⊔ CFSG.Open.pCoreOf 2 c.L := by
  intro x hx
  obtain ⟨n, hnP, hxn⟩ :=
    exists_centralizing_translate D Ch h4 h23 h208 h1930 c hFLF hFodd hFN hFLcomm hx
  have hxeq : x = (x * n) * n⁻¹ := by group
  rw [hxeq]
  exact Subgroup.mul_mem_sup (show x * n ∈ c.L ⊓ Subgroup.centralizer (FL : Set G) from
    ⟨hxn.1, hxn.2⟩) ((CFSG.Open.pCoreOf 2 c.L).inv_mem hnP)

private theorem cartan_le_l1 (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {DL F FL : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F) (hFLleF : FL ≤ F) :
    DL ≤ c.L ∧ DL ≤ cartanL1 c FL := by
  have hDLleL : DL ≤ c.L := hDLleB.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)
  refine ⟨hDLleL, ?_⟩
  intro d hd
  refine ⟨hDLleL hd, ?_⟩
  change d ∈ Subgroup.centralizer (FL : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (congrArg Subtype.val
    (hFcomm.is_comm.comm ⟨d, hDLF hd⟩ ⟨e, hFLleF he⟩)).symm

private theorem lift_w0_sq_mem_cartanN0 {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {FL : Subgroup G} {w : Bar2 c.L} (hw2 : w * w = 1)
    {w0 : G} (hw0L : w0 ∈ c.L) (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G))
    (hw0q : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w) :
    w0 ^ 2 ∈ cartanN0 c FL := by
  let P := CFSG.Open.pCoreOf 2 c.L
  let L1 := cartanL1 c FL
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hw02L : w0 ^ 2 ∈ c.L := by
    simpa only [pow_two] using c.L.mul_mem hw0L hw0L
  have hw02P : w0 ^ 2 ∈ P := by
    have hq2 : q ⟨w0 ^ 2, hw02L⟩ = 1 := by
      rw [show (⟨w0 ^ 2, hw02L⟩ : ↥c.L) = ⟨w0, hw0L⟩ ^ 2 by rfl]
      rw [map_pow, hw0q, pow_two, hw2]
    exact (CFSG.mem_openPCoreOf_iff ⟨w0 ^ 2, hw02L⟩).mpr
      ((QuotientGroup.eq_one_iff _).mp hq2)
  have hw02L1 : w0 ^ 2 ∈ L1 := by
    simpa only [pow_two] using L1.mul_mem hw0L1 hw0L1
  exact ⟨hw02L1, hw02P⟩

private theorem lift_w0_normalizes_cartanN0 (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {DL F FL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F) (hFLleF : FL ≤ F)
    {w0 : G} (hw0L : w0 ∈ c.L) (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G)) :
    w0 ∈ Subgroup.normalizer (cartanN0 c FL : Set G) ∧
      DL ≤ Subgroup.normalizer (cartanN0 c FL : Set G) := by
  let P := CFSG.Open.pCoreOf 2 c.L
  let L1 := cartanL1 c FL
  let N0 := cartanN0 c FL
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hDLleL1 : DL ≤ L1 := (cartan_le_l1 D Ch c hDLleB hDLF hFcomm hFLleF).2
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hL1NP : L1 ≤ Subgroup.normalizer (P : Set G) :=
    ((inf_le_left : L1 ≤ c.L).trans (Subgroup.le_normalizer (H := c.L))).trans
      (UC6S846.normalizer_le_normalizer_pCoreOf c.L)
  have hw0NP : w0 ∈ Subgroup.normalizer (P : Set G) := hL1NP hw0L1
  have hw0N0 : w0 ∈ Subgroup.normalizer (N0 : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (show w0 ∈ Subgroup.normalizer (L1 : Set G) ⊓
          Subgroup.normalizer (P : Set G) from
        ⟨Subgroup.le_normalizer hw0L1, hw0NP⟩)
  have hDLNP : DL ≤ Subgroup.normalizer (P : Set G) :=
    ((cartan_le_l1 D Ch c hDLleB hDLF hFcomm hFLleF).1.trans
      (Subgroup.le_normalizer (H := c.L))).trans
      (UC6S846.normalizer_le_normalizer_pCoreOf c.L)
  have hDLN0 : DL ≤ Subgroup.normalizer (N0 : Set G) :=
    (le_inf (fun d hd => Subgroup.le_normalizer (hDLleL1 hd)) hDLNP).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hw0N0, hDLN0⟩

private theorem exists_lift_involution (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F FL : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F)
    (hFLleF : FL ≤ F) (hFodd : Odd (Nat.card F)) (hFN : F ≤ c.N)
    (hFLcomm : ∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L)
    {w : Bar2 c.L} (hw2 : w * w = 1) :
    ∃ (w0 : G) (hw0L : w0 ∈ c.L) (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G)),
      (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w) ∧
      w0 ^ 2 ∈ cartanN0 c FL ∧ w0 ∈ Subgroup.normalizer (cartanN0 c FL : Set G) ∧
      DL ≤ Subgroup.normalizer (cartanN0 c FL : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := CFSG.Open.pCoreOf 2 c.L
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  obtain ⟨xL, hxLq⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) w
  obtain ⟨n, hnP, hxn⟩ :=
    exists_centralizing_translate D Ch h4 h23 h208 h1930 c hFLleF hFodd hFN hFLcomm xL.2
  let w0 : G := (xL : G) * n
  have hw0L : w0 ∈ c.L := hxn.1
  have hw0C : w0 ∈ Subgroup.centralizer (FL : Set G) := hxn.2
  have hnq : q ⟨n, hPleL hnP⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff ⟨n, hPleL hnP⟩).mp hnP)
  have hw0q : q ⟨w0, hw0L⟩ = q xL := by
    rw [show (⟨w0, hw0L⟩ : ↥c.L) = xL * ⟨n, hPleL hnP⟩ by rfl]
    rw [map_mul, hnq, mul_one]
  have hw02N0 : w0 ^ 2 ∈ cartanN0 c FL :=
    lift_w0_sq_mem_cartanN0 hw2 hw0L hw0C (hw0q.trans hxLq)
  obtain ⟨hw0N0, hDLN0⟩ :=
    lift_w0_normalizes_cartanN0 D Ch c hDLleB hDLF hFcomm hFLleF hw0L hw0C
  exact ⟨w0, hw0L, hw0C, hw0q.trans hxLq, hw02N0, hw0N0, hDLN0⟩

private theorem conj_lift_mul_mem_cartanN0 (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {DL F FL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F) (hFLleF : FL ≤ F)
    {w : Bar2 c.L} {w0 : G} (hw0L : w0 ∈ c.L)
    (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G))
    (hw0q : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w)
    (hwinv : ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹)
    {d : G} (hd : d ∈ DL) : (w0 * d * w0⁻¹) * d ∈ cartanN0 c FL := by
  let L1 := cartanL1 c FL
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  obtain ⟨hDLleL, hDLleL1⟩ := cartan_le_l1 D Ch c hDLleB hDLF hFcomm hFLleF
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hdL : d ∈ c.L := hDLleL hd
  have hdL1 : d ∈ L1 := hDLleL1 hd
  have hdqH : q ⟨d, hdL⟩ ∈ Subgroup.map q (DL.subgroupOf c.L) :=
    Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hd)
  have hconjq : q ⟨w0 * d * w0⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hw0L) d).mp hdL⟩ =
      (q ⟨d, hdL⟩)⁻¹ := by
    rw [show (⟨w0 * d * w0⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hw0L) d).mp hdL⟩ : ↥c.L) =
        ⟨w0, hw0L⟩ * ⟨d, hdL⟩ * ⟨w0, hw0L⟩⁻¹ by rfl]
    rw [map_mul, map_mul, map_inv, hw0q]
    exact hwinv _ hdqH
  have hprodL : (w0 * d * w0⁻¹) * d ∈ c.L :=
    c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hw0L hdL) (c.L.inv_mem hw0L)) hdL
  have hprodq : q ⟨(w0 * d * w0⁻¹) * d, hprodL⟩ = 1 := by
    rw [show (⟨(w0 * d * w0⁻¹) * d, hprodL⟩ : ↥c.L) =
        ⟨w0 * d * w0⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hw0L) d).mp hdL⟩ *
          ⟨d, hdL⟩ by rfl]
    rw [map_mul, hconjq, inv_mul_cancel]
  have hkP : (w0 * d * w0⁻¹) * d ∈ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.mem_openPCoreOf_iff ⟨(w0 * d * w0⁻¹) * d, hprodL⟩).mpr
      ((QuotientGroup.eq_one_iff _).mp hprodq)
  have hkL1 : (w0 * d * w0⁻¹) * d ∈ L1 :=
    L1.mul_mem (L1.mul_mem (L1.mul_mem hw0L1 hdL1) (L1.inv_mem hw0L1)) hdL1
  exact ⟨hkL1, hkP⟩

private theorem conj_lift_maps_cartan (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {DL F FL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F) (hFLleF : FL ≤ F)
    {w : Bar2 c.L} {w0 : G} (hw0L : w0 ∈ c.L)
    (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G))
    (hw0q : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w)
    (hwinv : ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹) :
    Subgroup.map (MulAut.conj w0).toMonoidHom DL ≤ DL ⊔ cartanN0 c FL := by
  let N0 := cartanN0 c FL
  rintro y ⟨d, hd, rfl⟩
  change w0 * d * w0⁻¹ ∈ DL ⊔ N0
  have hk0 := conj_lift_mul_mem_cartanN0 D Ch c hDLleB hDLF hFcomm hFLleF
    hw0L hw0C hw0q hwinv hd
  have heq : w0 * d * w0⁻¹ = ((w0 * d * w0⁻¹) * d) * d⁻¹ := by group
  rw [heq]
  have hmem : ((w0 * d * w0⁻¹) * d) * d⁻¹ ∈ N0 ⊔ DL :=
    Subgroup.mul_mem_sup hk0 (DL.inv_mem hd)
  rwa [sup_comm] at hmem

private theorem lift_normalizes_cartan_join (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F FL : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F) (hFLleF : FL ≤ F)
    {w : Bar2 c.L} {w0 : G} (hw0L : w0 ∈ c.L)
    (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G))
    (hw0q : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w)
    (hwinv : ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹)
    (hw0N0 : w0 ∈ Subgroup.normalizer (cartanN0 c FL : Set G)) :
    w0 ∈ Subgroup.normalizer ((DL ⊔ cartanN0 c FL : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := CFSG.Open.pCoreOf 2 c.L
  let L1 := cartanL1 c FL
  let N0 := cartanN0 c FL
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hmapDL := conj_lift_maps_cartan D Ch c hDLleB hDLF hFcomm hFLleF hw0L hw0C hw0q hwinv
  have hmapN0 : Subgroup.map (MulAut.conj w0).toMonoidHom N0 ≤ DL ⊔ N0 := by
    rintro y ⟨x, hx, rfl⟩
    change w0 * x * w0⁻¹ ∈ DL ⊔ N0
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hw0N0 x).mp hx)
  have hmap_le : Subgroup.map (MulAut.conj w0).toMonoidHom (DL ⊔ N0) ≤ DL ⊔ N0 := by
    rw [Subgroup.map_sup]
    exact sup_le hmapDL hmapN0
  have hmap_eq : Subgroup.map (MulAut.conj w0).toMonoidHom (DL ⊔ N0) = DL ⊔ N0 :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj w0).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq

private theorem corrected_weyl_same_image {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {FL : Subgroup G} {v w0 : G}
    (hvN : v⁻¹ * w0 ∈ cartanN0 c FL) (hw0L : w0 ∈ c.L)
    (hvL1 : v ∈ cartanL1 c FL) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨v, hvL1.1⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ := by
  have hPleL : CFSG.Open.pCoreOf 2 c.L ≤ c.L :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hn0q : q ⟨v⁻¹ * w0, hPleL hvN.2⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr
      ((CFSG.mem_openPCoreOf_iff ⟨v⁻¹ * w0, hPleL hvN.2⟩).mp hvN.2)
  rw [show (⟨v, hvL1.1⟩ : ↥c.L) =
      ⟨w0, hw0L⟩ * (⟨v⁻¹ * w0, hPleL hvN.2⟩)⁻¹ by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group]
  rw [map_mul, map_inv, hn0q, inv_one, mul_one]

private theorem corrected_weyl_inverts (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL FL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    {v w0 : G} {w : Bar2 c.L} (hw0L : w0 ∈ c.L)
    (hw0q : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩ = w) (hvL : v ∈ c.L)
    (hvq : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨v, hvL⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨w0, hw0L⟩)
    (hvnormDL : v ∈ Subgroup.normalizer (DL : Set G))
    (hwinv : ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹) :
    ∀ d ∈ DL, v * d * v⁻¹ = d⁻¹ := by
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  intro d hd
  have hDLleL : DL ≤ c.L := hDLleB.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)
  have hdL : d ∈ c.L := hDLleL hd
  have hvdDL : v * d * v⁻¹ ∈ DL := (Subgroup.mem_normalizer_iff.mp hvnormDL d).mp hd
  have hdqH : q ⟨d, hdL⟩ ∈ Subgroup.map q (DL.subgroupOf c.L) :=
    Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hd)
  have hleft : q ⟨v * d * v⁻¹, hDLleL hvdDL⟩ = (q ⟨d, hdL⟩)⁻¹ := by
    rw [show (⟨v * d * v⁻¹, hDLleL hvdDL⟩ : ↥c.L) =
        ⟨v, hvL⟩ * ⟨d, hdL⟩ * ⟨v, hvL⟩⁻¹ by rfl]
    rw [map_mul, map_mul, map_inv, hvq, hw0q]
    exact hwinv _ hdqH
  have hright : q ⟨d⁻¹, hDLleL (DL.inv_mem hd)⟩ = (q ⟨d, hdL⟩)⁻¹ := by
    rw [show (⟨d⁻¹, hDLleL (DL.inv_mem hd)⟩ : ↥c.L) = (⟨d, hdL⟩ : ↥c.L)⁻¹ by rfl]
    exact map_inv q _
  exact eq_of_bar2_eq_of_inf_pCore_bot hDLleL (cartan_image_disj D Ch c h3 hDLcard)
    hvdDL (DL.inv_mem hd) (hleft.trans hright.symm)

private theorem mem_cartanL1_of_mul_mem_cartanN0 {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {FL : Subgroup G} {v w0 : G}
    (hw0L : w0 ∈ c.L) (hw0C : w0 ∈ Subgroup.centralizer (FL : Set G))
    (hvN : v⁻¹ * w0 ∈ cartanN0 c FL) : v ∈ cartanL1 c FL := by
  let L1 := cartanL1 c FL
  let P := CFSG.Open.pCoreOf 2 c.L
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hveq : v = w0 * (v⁻¹ * w0)⁻¹ := by group
  rw [hveq]
  exact L1.mul_mem hw0L1 (L1.inv_mem hvN.1)

private theorem conj_eq_self_of_mem_cartanL1 {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {FL : Subgroup G} {v : G} (hv : v ∈ cartanL1 c FL) :
    ∀ e ∈ FL, v * e * v⁻¹ = e := by
  intro e he
  have hcomm : v * e = e * v := (Subgroup.mem_centralizer_iff.mp hv.2 e he).symm
  rw [hcomm, mul_inv_cancel_right]

private theorem exists_corrected_weyl (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {DL F FL : Subgroup G} (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFcomm : IsMulCommutative F)
    (hFLleF : FL ≤ F) (hFodd : Odd (Nat.card F)) (hFN : F ≤ c.N)
    (hFLcomm : ∀ r ∈ FL, ∀ x ∈ c.L, ⁅x, r⁆ ∈ CFSG.Open.pCoreOf 2 c.L)
    {w : Bar2 c.L} (hw2 : w * w = 1)
    (hwinv : ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹) :
    ∃ v : G, v ∈ c.L ⊓ Subgroup.centralizer (FL : Set G) ∧
      (∃ k : ℕ, orderOf v = 2 ^ k) ∧
      (∀ d ∈ DL, v * d * v⁻¹ = d⁻¹) ∧
      (∀ e ∈ FL, v * e * v⁻¹ = e) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := CFSG.Open.pCoreOf 2 c.L
  let L1 : Subgroup G := c.L ⊓ Subgroup.centralizer (FL : Set G)
  let N0 : Subgroup G := L1 ⊓ P
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hPleL : P ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  obtain ⟨w0, hw0L, hw0C, hw0q, hw02N0, hw0N0, hDLN0⟩ :=
    exists_lift_involution D Ch h4 h23 h208 h1930 c h3 hDLleB hDLcard hDLF hFcomm
      hFLleF hFodd hFN hFLcomm hw2
  have hw0L1 : w0 ∈ L1 := ⟨hw0L, hw0C⟩
  have hwHN : w0 ∈ Subgroup.normalizer ((DL ⊔ N0 : Subgroup G) : Set G) :=
    lift_normalizes_cartan_join D Ch h23 h1930 c h3 hDLleB hDLcard hDLF hFcomm
      hFLleF hw0L hw0C hw0q hwinv hw0N0
  have hN02 : IsPGroup 2 N0 := IsPGroup.to_inf_right (p := 2) (H := L1) (K := P) hP2
  have hDLodd : Odd (Nat.card DL) := by
    rw [hDLcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  obtain ⟨v, hvN, hvnormDL, hvord⟩ :=
    CFSG.GroupTheory.exists_isPGroup_two_mem_normalizer_of_sq_mem hN02 hDLodd
      hDLN0 hw0N0 hwHN hw02N0
  have hvL1 : v ∈ L1 := mem_cartanL1_of_mul_mem_cartanN0 hw0L hw0C hvN
  have hvL : v ∈ c.L := hvL1.1
  have hvq : q ⟨v, hvL⟩ = q ⟨w0, hw0L⟩ :=
    corrected_weyl_same_image hvN hw0L hvL1
  have hvinv : ∀ d ∈ DL, v * d * v⁻¹ = d⁻¹ :=
    corrected_weyl_inverts D Ch c h3 (FL := FL) hDLleB hDLcard hw0L hw0q hvL hvq
      hvnormDL hwinv
  have hvcent : ∀ e ∈ FL, v * e * v⁻¹ = e :=
    conj_eq_self_of_mem_cartanL1 hvL1
  exact ⟨v, hvL1, hvord, hvinv, hvcent⟩

private theorem exists_involution_inverting_cartan (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∃ w : Bar2 c.L, w * w = 1 ∧
      ∀ h ∈ Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
          (DL.subgroupOf c.L), w * h * w⁻¹ = h⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL2, -⟩ := h23 h1930 c
  let n := CFSG.Open.pRank 2 D.Z
  have hL2' : IsL2 (Bar2 c.L) n := by simpa [n] using hL2
  obtain ⟨S, H, hS, hHdef, hHle, hHcard⟩ :=
    cartan_image_data D Ch c h3 hDLleB hDLcard
  obtain ⟨hcyc, -⟩ := kL2TorusSelfCent_holds (Bar2 c.L) n hL2' S H hHle
    (by simpa [n] using hHcard)
  have hL2Ev : IsL2Ev (Bar2 c.L) n := hL2'.isL2Ev
  obtain ⟨x0, hx0⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hcyc
  obtain ⟨w, hw2, hwx⟩ := exists_mul_self_conj_eq_inv_of_isL2Ev hL2Ev x0
  refine ⟨w, hw2, ?_⟩
  intro h hh
  have hhH : h ∈ H := by rw [hHdef]; exact hh
  have hhpow : h ∈ Subgroup.zpowers x0 := by rw [hx0]; exact hhH
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hhpow
  calc w * x0 ^ i * w⁻¹ = (MulAut.conj w) (x0 ^ i) := by rw [MulAut.conj_apply]
    _ = ((MulAut.conj w) x0) ^ i := by rw [map_zpow]
    _ = (x0⁻¹) ^ i := by rw [MulAut.conj_apply, hwx]
    _ = (x0 ^ i)⁻¹ := by rw [inv_zpow]

private theorem exists_nontrivial_mem_cartan (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL : Subgroup G}
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∃ b ∈ DL, b ≠ 1 := by
  have hcardgt : 1 < Nat.card DL := by
    rw [hDLcard]
    have hpow : 8 ≤ 2 ^ CFSG.Open.pRank 2 D.Z := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := pow_le_pow_right₀ (by norm_num) h3
    omega
  have hDLne : DL ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card DL = 1 := by rw [hbot]; simp
    omega
  haveI : Nontrivial ↥DL := (Subgroup.nontrivial_iff_ne_bot DL).mpr hDLne
  exact Subgroup.exists_ne_one_of_nontrivial DL

private theorem not_mem_M_of_inverts_cartan (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL F : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFM : F ≤ D.M) (hFodd : Odd (Nat.card F))
    {v : G} (hvM : v ∈ D.M) (hvord : ∃ k : ℕ, orderOf v = 2 ^ k)
    (hvinv : ∀ d ∈ DL, v * d * v⁻¹ = d⁻¹) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    have h4c := h4 h1930 c
    simpa [h4c.1] using h4c.2.2
  obtain ⟨k, hk⟩ := hvord
  have hvZ : v ∈ Subgroup.centralizer (D.Z : Set G) :=
    D.mem_centralizer_Z_of_two_element hZM hvM hk
  obtain ⟨b, hb, hb1⟩ := exists_nontrivial_mem_cartan D Ch c h3 hDLcard
  have hbF : b ∈ F := hDLF hb
  have hbM : b ∈ D.M := hFM hbF
  have hbodd : Odd (orderOf b) := by
    have h := Odd.of_dvd_nat hFodd (orderOf_dvd_natCard (⟨b, hbF⟩ : ↥F))
    exact (Subgroup.orderOf_coe (⟨b, hbF⟩ : ↥F)).symm ▸ h
  have hbZ : b ∈ Subgroup.normalizer (D.Z : Set G) := hZM hbM
  have hbC : b ∈ Subgroup.centralizer (D.Z : Set G) :=
    CFSG.GroupTheory.mem_centralizer_of_inverted hbodd (hvinv b hb)
      (fun a ha => (Subgroup.mem_centralizer_iff.mp hvZ a ha).symm) hbZ
  have hbL : b ∈ c.L := (hDLleB.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)) hb
  have hN1 := Ctx23L.L_inf_centralizer_Z_eq D Ch h4 h23 h1930 c
  have hbTL : b ∈ D.T ⊓ c.L := by
    rw [← hN1]
    exact ⟨hbL, hbC⟩
  have hDLinfTL := inf_cartan_eq_bot D Ch c h3 hDLcard
  have hbot : b ∈ (⊥ : Subgroup G) := by
    rw [← hDLinfTL]
    exact ⟨hb, hbTL⟩
  exact hb1 (Subgroup.mem_bot.mp hbot)

theorem Ctx23L.exists_weyl_normalizing_F (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {DL F : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hDLF : DL ≤ F) (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F)
    (hFN : F ≤ c.N) (hFM : F ≤ D.M)
    (hFNT : F ≤ Subgroup.normalizer (D.T : Set G)) :
    ∃ v ∈ c.L, v ∉ D.M ∧ v ∈ Subgroup.normalizer (F : Set G) := by
  classical
  obtain ⟨FL, hFLleF, hFLcomm, hFdec⟩ :=
    exists_cartan_kernel D Ch h4 h23 h208 h1930 c h3 hDLleB hDLcard
      hDLF hFodd hFcomm hFN hFNT
  obtain ⟨w, hw2, hwinv⟩ :=
    exists_involution_inverting_cartan D Ch h23 h1930 c h3 hDLleB hDLcard
  obtain ⟨v, hvL1, hvord, hvinv, hvcent⟩ :=
    exists_corrected_weyl D Ch h4 h23 h208 h1930 c h3 hDLleB hDLcard
      hDLF hFcomm hFLleF hFodd hFN hFLcomm hw2 hwinv
  have hvF : v ∈ Subgroup.normalizer (F : Set G) :=
    mem_normalizer_of_decomp hDLF hFLleF hFdec hvinv hvcent
  have hvnotM : v ∉ D.M := fun hvM =>
    not_mem_M_of_inverts_cartan D Ch h4 h23 h1930 c h3 hDLleB hDLcard
      hDLF hFM hFodd hvM hvord hvinv
  exact ⟨v, hvL1.1, hvnotM, hvF⟩

theorem cartanCentralizerStep_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h847 : R847ThinCZ D) :
    CartanCentralizerStep D Ch :=
  cartanCentralizerStep_of_weyl D Ch h4 h23 h847
    fun h1930 c h3 _ _ hDLleB hDLcard _ hDLF hFodd hFcomm hFN hFM hFNT =>
      Ctx23L.exists_weyl_normalizing_F D Ch h4 h23 h208 h1930 c h3 hDLleB hDLcard hDLF hFodd
        hFcomm hFN hFM hFNT

theorem d2337_of_r847 (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h208 : S20_8 D) (hPush : Push2329 D Ch) (h847 : R847ThinCZ D) :
    D2337 D Ch :=
  d2337_of D Ch (cartanCentralizerStep_of D Ch h4 h23 h208 h847) h4 h23 h208 hPush

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
