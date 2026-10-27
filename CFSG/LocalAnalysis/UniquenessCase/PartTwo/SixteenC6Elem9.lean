module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Cover
import CFSG.ClassicalGroups.Symplectic.Sp4ElemAbelianPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusNonsingStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c6_elemAbelian_statedSp {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 3) :
    ∃ E : Subgroup ↥(StatedSp 2 F), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ :=
    CFSG.ClassicalGroups.Symplectic.Sp4.exists_isElemAbelian_card_sq_of_dvd_card_add_one
      (K := F) (p := 3) (by norm_num) (by rw [hF]; norm_num)
  exact ⟨E, hE, by rw [hcard]; norm_num⟩

theorem s16c6_exists_elem9
    (D : Data G) (hstd : S168e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L)
    (c : S16c6Coords V₀ V L hV) {w : G} (hw : w ∈ V) (hns : c.NonSingular w hw) :
    ∃ K E : Subgroup G, K ∈ calC D.M ∧ K ≤ D.M ∧ E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ e ∈ E, e * w * e⁻¹ * w⁻¹ ∈ V₀ := by
  classical
  obtain ⟨K, hKcalC, -, hbar, hsimple⟩ := s16c6_exists_cover D hstd hS hc
  have hKM : K ≤ D.M := hKcalC.1.le
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp16.hyp125.pairFacts.le_normalizer
      hS.setting.hyp16.hyp125.pairFacts.le_normalizer₀
  have hKstab : K ≤ stabTil V₀ V := hKM.trans hMstab
  haveI hsimpleI : IsSimpleGroup (Bar2 K) := hsimple
  let π : ↥K →* ↥(barSub V₀ V hV K) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hKstab)).codRestrict (barSub V₀ V hV K)
      (fun x => actTil_mem_barSub V₀ V hV x.2 (hKstab x.2))
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨g, hgK, hgy⟩ := (mem_barSub V₀ V hV K y).1 y.2
    refine ⟨⟨(g : G), hgK⟩, ?_⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨(g : G), hKstab hgK⟩ = (y : MulAut (Vtil V₀ V hV))
    have hg_eq : (⟨(g : G), hKstab hgK⟩ : stabTil V₀ V) = g := Subtype.ext rfl
    rw [hg_eq, hgy]
  have hO2bar : barSub V₀ V hV (pCoreOf 2 K) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hKcalC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hS.setting.hyp16.hyp125)
  have hO2le : pCore 2 ↥K ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    have hxP : (x : G) ∈ pCoreOf 2 K := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hKstab x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 K) :=
      actTil_mem_barSub V₀ V hV hxP (hKstab x.2)
    rw [hO2bar, Subgroup.mem_bot] at h1
    change actTil V₀ V hV ⟨(x : G), hKstab x.2⟩ = 1
    exact h1
  have hN : π.ker = CFSG.pCore 2 ↥K := by
    refine le_antisymm ?_ hO2le
    have hmapN : (π.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
      Subgroup.Normal.map (H := π.ker) inferInstance _
        (QuotientGroup.mk'_surjective _)
    rcases Subgroup.Normal.eq_bot_or_eq_top
        (π.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hbot | htop
    · intro x hx
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈
          π.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have hNtop : π.ker = ⊤ := by
        have hker_mk : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker = CFSG.pCore 2 ↥K :=
          QuotientGroup.ker_mk' _
        have hle : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker ≤ π.ker := by
          rw [hker_mk]; exact hO2le
        have h := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K)) hle
        rw [htop, Subgroup.comap_top] at h
        exact h.symm
      have hbar_bot : barSub V₀ V hV K = ⊥ := by
        refine eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 ?_
        obtain ⟨x, hx⟩ := hπsurj ⟨y, hy⟩
        have hxN : x ∈ π.ker := hNtop ▸ Subgroup.mem_top x
        rw [MonoidHom.mem_ker] at hxN
        have h1 : (⟨y, hy⟩ : ↥(barSub V₀ V hV K)) = 1 := hx ▸ hxN
        exact Subtype.ext_iff.mp h1
      exact (by rw [hbar] at hbar_bot; exact hS.ne_bot hbar_bot)
  have hN2 : IsPGroup 2 π.ker := by
    rw [hN]; exact CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  obtain ⟨E, hEelem, hEcard⟩ := s16c6_elemAbelian_statedSp c.card_eq
  obtain ⟨e⟩ := S18.exists_vecStab_OmegaMinus6_nonsing_equiv
    (n := 3) (F := c.F) (b := c.b) (c := c.c) (by norm_num) c.card_eq c.irr hns
  let Ω := StatedOmega (StatedQuadMinus 3 c.F c.b c.c)
  let Vw : Subgroup ↥Ω := KTabC.vecStab Ω.subtype (c.vec w hw)
  let Ê₁ : Subgroup ↥Vw := E.map e.symm.toMonoidHom
  let Ê : Subgroup ↥Ω := Ê₁.map Vw.subtype
  have hÊle : Ê ≤ Vw := Subgroup.map_subtype_le _
  have hÊelem : IsElemAbelian 3 Ê :=
    CFSG.SectionRank.isElemAbelian_map
      (CFSG.SectionRank.isElemAbelian_map hEelem e.symm.toMonoidHom) Vw.subtype
  have hÊcard : Nat.card Ê = 9 := by
    rw [show Ê = (E.map e.symm.toMonoidHom).map Vw.subtype from rfl,
      Subgroup.card_map_of_injective Vw.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hEcard]
  let Φ : ↥(barSub V₀ V hV K) ≃* ↥Ω := (MulEquiv.subgroupCongr hbar).trans c.ε
  let Êb : Subgroup ↥(barSub V₀ V hV K) := Ê.map Φ.symm.toMonoidHom
  have hÊbcard : Nat.card Êb = 9 := by
    rw [show Êb = Ê.map Φ.symm.toMonoidHom from rfl,
      Subgroup.card_map_of_injective Φ.symm.injective, hÊcard]
  have hÊbelem : IsElemAbelian 3 Êb :=
    CFSG.SectionRank.isElemAbelian_map hÊelem Φ.symm.toMonoidHom
  let φ : ↥(Êb.comap π) →* ↥(barSub V₀ V hV K) := π.comp (Êb.comap π).subtype
  have hφrange : φ.range = Êb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.map_comap_eq_self_of_surjective hπsurj]
  have hcardφ := Subgroup.card_ker_mul_card_range φ
  rw [hφrange, hÊbcard] at hcardφ
  have h9 : 9 ∣ Nat.card ↥(Êb.comap π) := by
    rw [← hcardφ]
    exact dvd_mul_left 9 (Nat.card φ.ker)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S, hScard, -, hSle⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (by norm_num) (n := 2)
      (H := ⊥) (L := Êb.comap π) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]; exact h9) bot_le
  have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 2) (by rw [hScard])
  have hSsub3 : IsPGroup 3 (S.subgroupOf (Êb.comap π)) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv, hScard]
  have hφker2 : IsPGroup 2 φ.ker := by
    have hcomap : φ.ker = π.ker.comap (Êb.comap π).subtype := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      rfl
    rw [hcomap]
    exact IsPGroup.comap_of_injective hN2 (Êb.comap π).subtype
      (Êb.comap π).subtype_injective
  have hSdisj : Disjoint (S.subgroupOf (Êb.comap π)) φ.ker :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hSsub3 hφker2
  let ψ : ↥(S.subgroupOf (Êb.comap π)) →* ↥Êb :=
    (φ.comp (S.subgroupOf (Êb.comap π)).subtype).codRestrict Êb
      (fun s => by
        have h : φ ((S.subgroupOf (Êb.comap π)).subtype s) ∈ φ.range :=
          MonoidHom.mem_range.mpr ⟨(S.subgroupOf (Êb.comap π)).subtype s, rfl⟩
        rwa [hφrange] at h)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hs1 : ψ s = 1 := hs
    have hsφ : (S.subgroupOf (Êb.comap π)).subtype s ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hs1
    have hsbot : (S.subgroupOf (Êb.comap π)).subtype s ∈
        (⊥ : Subgroup ↥(Êb.comap π)) := by
      rw [← hSdisj.eq_bot]
      exact ⟨s.2, hsφ⟩
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.mp hsbot))
  have hSsubelem : IsElemAbelian 3 (S.subgroupOf (Êb.comap π)) := by
    haveI := hÊbelem.1
    have hcomm : ∀ a b : ↥(S.subgroupOf (Êb.comap π)),
        ψ a * ψ b = ψ b * ψ a := fun a b => mul_comm' _ _
    have hpow : ∀ a : ↥(S.subgroupOf (Êb.comap π)), (ψ a) ^ 3 = 1 :=
      fun a => Subtype.ext (by simpa using hÊbelem.2 (ψ a) (ψ a).2)
    have hres := CFSG.SectionRank.comm_pow_of_injective (p := 3) hψinj hcomm hpow
    exact ⟨⟨⟨hres.1⟩⟩, fun x hx => by
      simpa using congrArg Subtype.val (hres.2 ⟨x, hx⟩)⟩
  have hSelem : IsElemAbelian 3 S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSle]
    exact CFSG.SectionRank.isElemAbelian_map hSsubelem (Êb.comap π).subtype
  refine ⟨K, S.map K.subtype, hKcalC, hKM, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hSelem K.subtype
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hScard]; norm_num
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hkπ : π k ∈ Êb := hSle hk
    have hΦmem : Φ (π k) ∈ Ê := by
      obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp
        (show π k ∈ Ê.map Φ.symm.toMonoidHom from hkπ)
      have hyq' : y = Φ (π k) := by
        have := congrArg Φ hyq
        simpa using this
      rwa [hyq'] at hy
    let l : ↥(lBar V₀ V hV L) := MulEquiv.subgroupCongr hbar (π k)
    have hl : (l : MulAut (Vtil V₀ V hV)) = actTil V₀ V hV ⟨k, hKstab k.2⟩ := by
      rw [show l = MulEquiv.subgroupCongr hbar (π k) from rfl,
        MulEquiv.subgroupCongr_apply]
      rfl
    have hfixΩ : Matrix.mulVec (((c.ε l : ↥Ω) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) c.F) (c.vec w hw) = c.vec w hw :=
      KTabC.mem_vecStab.mp (hÊle hΦmem)
    have hcoords := c.coords l
      ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩
    rw [hl, show Multiplicative.toAdd
        (c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩) =
        c.vec w hw from rfl, hfixΩ] at hcoords
    have hofAdd : Multiplicative.ofAdd (c.vec w hw) =
        c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩ := by
      rw [show c.vec w hw = Multiplicative.toAdd
        (c.ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _⟩) from rfl]
      exact ofAdd_toAdd _
    rw [hofAdd] at hcoords
    have hmkTil : actTil V₀ V hV ⟨k, hKstab k.2⟩
        (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) :=
      Subtype.ext_iff.mp (c.ψ.injective hcoords)
    have hmk2 : mkTil V₀ V hV
        (actStab V₀ V hV ⟨k, hKstab k.2⟩ (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by
      rw [← actTil_mk V₀ V hV ⟨k, hKstab k.2⟩ (IntMod.mk hV ⟨w, hw⟩)]
      exact hmkTil
    have hmk3 := (mkTil_eq_iff V₀ V hV _ (IntMod.mk hV ⟨w, hw⟩)).1 hmk2
    rw [actStab_apply_val] at hmk3
    simpa [IntMod.mk, IntMod.val] using hmk3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
