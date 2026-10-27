module

public import CFSG.Quasithin.Background.FFC10B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem component_le_twoResidual {X L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    L ≤ twoResidual X := by
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hcomm : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hLperf
  have hperf : Group.IsPerfect ↥(L.subgroupOf X) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hL.1, hcomm]
  have h1 : L.subgroupOf X ≤ twoResidual (⊤ : Subgroup ↥X) := B6.perfect_le_twoResidual
  rw [B6.twoResidual_top_eq_subgroupOf] at h1
  intro l hl
  have := h1 (Subgroup.mem_subgroupOf.2 hl : (⟨l, hL.1 hl⟩ : ↥X) ∈ L.subgroupOf X)
  exact Subgroup.mem_subgroupOf.1 this

theorem map_mem_commV_of_offender (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4)
    {X B L : Subgroup (MulAut V)} (hB : IsFFStarOffender X B) (hL : CFSG.Open.IsComponentOf L X) :
    ∀ b ∈ B, ∀ w ∈ commV L, b w ∈ commV L := by
  have hBnorm : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := hP4 V hV X B hB L hL
  intro b hb w hw
  have h1 := map_mem_commV_conj b w hw
  have h2 : B6.conjSub b L = L := by
    ext x
    rw [B6.mem_conjSub]
    have := Subgroup.mem_normalizer_iff.1 (hBnorm (B.inv_mem hb)) x
    simpa using this.symm
  rwa [h2] at h1

theorem exists_blk_prod (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X T M B N : Subgroup (MulAut V)}
    (hctx : ShapeCtx X T M)
    (hact : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X →
      ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L)
    (hblkN : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X → blk X L ≤ N)
    (hB : IsFFStarOffender X B) {b : MulAut V} (hb : b ∈ B) (S : Finset (Subgroup (MulAut V)))
    (hS : ∀ L ∈ S, CFSG.Open.IsComponentOf L X) :
    ∃ h ∈ N, (∀ L ∈ S, ∀ w ∈ commV L, h w = b w) ∧
      ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X → L ∉ S → ∀ w ∈ commV L, h w = w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, N.one_mem, fun L hL => absurd hL (Finset.notMem_empty L), fun L _ _ w _ => rfl⟩
  | insert L₀ S hL₀ ih =>
    have hL₀c : CFSG.Open.IsComponentOf L₀ X := hS L₀ (Finset.mem_insert_self _ _)
    obtain ⟨h₁, hh₀, hh₁, hh₂⟩ := ih fun L hL => hS L (Finset.mem_insert_of_mem hL)
    obtain ⟨y, hy, hyw⟩ := exists_act_blk hV hP4 hctx (hact L₀ hL₀c) hB hL₀c b hb
    refine ⟨y * h₁, N.mul_mem (hblkN L₀ hL₀c hy) hh₀, fun L hL w hw => ?_, fun L hL hLn w hw => ?_⟩
    · rcases Finset.mem_insert.1 hL with rfl | hLS
      · show y (h₁ w) = b w
        rw [hh₂ L hL₀c hL₀ w hw]
        exact hyw w hw
      · have hLc : CFSG.Open.IsComponentOf L X := hS L hL
        have hne : L₀ ≠ L := fun e => hL₀ (e ▸ hLS)
        show y (h₁ w) = b w
        rw [hh₁ L hLS w hw]
        exact blk_le_centSub hV hP4 hctx hL₀c hLc (hact L hLc) hne hy (b w)
          (map_mem_commV_of_offender hV hP4 hB hLc b hb w hw)
    · have hne : L₀ ≠ L := fun e => hLn (e ▸ Finset.mem_insert_self _ _)
      have hLS : L ∉ S := fun h => hLn (Finset.mem_insert_of_mem h)
      show y (h₁ w) = w
      rw [hh₂ L hL hLS w hw]
      exact blk_le_centSub hV hP4 hctx hL₀c hL (hact L hL) hne hy w hw

theorem asB69GenByMin_of (hP4 : AsB15Part4) (hComp : AsB69Component) : AsB69GenByMin := by
  intro V _ _ hV X T M hsq h hO2 hFF hns
  have hctx : ShapeCtx X T M := shapeCtx_of_component hComp hV hsq h hO2 hFF hns
  have hact := exists_active hV hP4 h hO2 hFF hns
  have hst : IsStableFF X {A | IsFFStarMin X A} := B1_7 hV hFF
  set N : Subgroup (MulAut V) := ffJP {A | IsFFStarMin X A} X with hNdef
  have hNX : N ≤ X := iSup₂_le fun A _ => iSup_le fun hAX => hAX
  have hNn : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (fun x hx => B1Red.ffJP_conj_mem hst hg hx)
      (fun x hx => by simpa using B1Red.ffJP_conj_mem hst (X.inv_mem hg) hx)
  have hPN : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → A ≤ N := fun A hA =>
    B19.le_ffJP hA hA.1.1
  have hblkN : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X → blk X L ≤ N := by
    intro L hL
    obtain ⟨A₀, hA₀, hLA₀⟩ := hact L hL
    refine blk_le_iff.2 ⟨?_, fun A hA _ => hPN A hA⟩
    rw [← hLA₀]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ N := B1Red.ffJP_conj_mem hst (hL.1 hl) (hPN A₀ hA₀ ha)
    exact N.mul_mem h1 (N.inv_mem (hPN A₀ hA₀ ha))
  obtain ⟨A₀, hA₀⟩ := hst.1
  have hres : twoResidual X ≤ N := by
    rcases h.le_kerIn_or_twoResidual_le hNX hNn with hJ | hK
    · exfalso
      have hA₀2 : IsPGroup 2 A₀ := fun x => ⟨1, by
        apply Subtype.ext
        simpa using hA₀.1.2.2.1.2 _ x.2⟩
      have := h.le_pCoreOf_of_isPGroup_of_le_kerIn hA₀2 ((hPN A₀ hA₀).trans hJ)
      rw [hO2] at this
      exact hA₀.1.2.1 (le_bot_iff.1 this)
    · exact hK
  set R : Subgroup (MulAut V) := X ⊓ centSub (vSigma X) with hRdef
  have hXst : X ≤ stabSub (vSigma X) := B1.le_stabSub_of_invariant (vSigma_invariant X)
  have hRn : X ≤ Subgroup.normalizer (R : Set (MulAut V)) := fun g hg =>
    B6.mem_normalizer_of_forall_mem
      (fun x hx => ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg), conj_mem_centSub (hXst hg) hx.2⟩)
      (fun x hx => ⟨X.mul_mem (X.mul_mem (X.inv_mem hg) hx.1) hg, by
        simpa using conj_mem_centSub (hXst (X.inv_mem hg)) hx.2⟩)
  have hRN : R ≤ N := by
    refine le_trans ?_ hres
    rcases h.le_kerIn_or_twoResidual_le inf_le_left hRn with hJ | hK
    ·
      intro r hr
      have hrJ : r ∈ kerIn M X := hJ hr
      have hrX : r ∈ X := hr.1
      obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf r) (orderOf_pos r).ne'
      have hm0 : m ≠ 0 := hm.pos.ne'
      have hodd : Odd (orderOf r) := by
        have hord2 : orderOf (r ^ m) = 2 ^ a := by
          rw [orderOf_pow_of_dvd hm0 ⟨2 ^ a, by rw [hord, mul_comm]⟩, hord,
            Nat.mul_div_cancel _ hm.pos]
        have h2grp : IsPGroup 2 (Subgroup.zpowers (r ^ m)) :=
          IsPGroup.of_card (by rw [Nat.card_zpowers, hord2])
        have hzJ : Subgroup.zpowers (r ^ m) ≤ kerIn M X := Subgroup.zpowers_le.2 ((kerIn M X).pow_mem hrJ m)
        have hz := h.le_pCoreOf_of_isPGroup_of_le_kerIn h2grp hzJ
        rw [hO2] at hz
        have h1 : r ^ m = 1 := Subgroup.mem_bot.1 (hz (Subgroup.mem_zpowers _))
        exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X r hrX
      exact B6.mem_of_pow_mem_of_coprime hk (Nat.Coprime.pow_right k (Odd.coprime_two_right hodd))
    · exfalso
      obtain ⟨L, hL, hLA⟩ := exists_component_of_nonsolvable hV hP4 h hO2 hns hA₀
      have hW : commV L ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hV hctx hA₀ hL hLA
      have hlt := (mem_irrPlus_top_iff.1 hW).2.2.1
      have hLR : L ≤ R := (component_le_twoResidual hL).trans hK
      refine absurd ?_ (not_le_of_gt hlt)
      intro w hw
      refine ⟨hw, fun l hl => ?_⟩
      exact (hLR hl).2 w (commV_le_vSigma hL hw)
  refine iSup₂_le fun B hB => ?_
  intro b hb
  have hfin : {L : Subgroup (MulAut V) | CFSG.Open.IsComponentOf L X}.Finite := Set.toFinite _
  obtain ⟨hh, hhN, hh1, -⟩ := exists_blk_prod hV hP4 hctx hact hblkN hB hb hfin.toFinset
    (fun L hL => hfin.mem_toFinset.1 hL)
  have hcR : hh⁻¹ * b ∈ R := by
    refine ⟨X.mul_mem (X.inv_mem (hNX hhN)) (hB.1 hb), fun u hu => ?_⟩
    have hle : vSigma X ≤ MonoidHom.eqLocus ((hh⁻¹ * b : MulAut V) : V →* V) (MonoidHom.id V) := by
      refine iSup₂_le fun L hL w hw => ?_
      have e : b w = hh w := (hh1 L (hfin.mem_toFinset.2 hL) w hw).symm
      show hh⁻¹ (b w) = w
      rw [e]
      simp
    exact hle hu
  have := N.mul_mem hhN (hRN hcR)
  simpa using this

end B69

end CFSG.Quasithin
