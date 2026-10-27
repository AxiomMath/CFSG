module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Bad
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47StarCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_a_mem_eTwo (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)))
    {a : G} (haV₀ : a ∈ V₀) (ha1 : a ≠ 1)
    (hW : ∀ y ∈ V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)), y = 1 ∨ y = a) :
    a ∈ eTwo D V₀ x.val := by
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hne : V₀ ≠ ⊥ := by
    intro hb
    rw [hb] at haV₀
    exact ha1 (Subgroup.mem_bot.1 haV₀)
  have hSM : D.T ⊓ centralizer ({x.val} : Set G) ≤ D.M := inf_le_left.trans D.sylowM.le
  obtain ⟨b, hbV₀, hb1, hbS⟩ := s16c1_G47_fixed_nontrivial hSyl.2.1
    (hSM.trans hP.le_normalizer₀) hP.elemAbelian₀.isPGroup hne
  have hbC : b ∈ V₀ ⊓ centralizer
      ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨hbV₀, Subgroup.mem_centralizer_iff.2 hbS⟩
  have hbQ := s16c1_cent_V0_le_pCore D hS hx hSyl hbC
  have hba : b = a := (hW b (Subgroup.mem_inf.2 ⟨hbV₀, hbQ⟩)).resolve_left hb1
  rw [← hba]
  exact s16c1_G47_le_hConjClosure x.val _ hbC

theorem s16c1_G47_exists_action {H E : Subgroup G} (hHE : H ≤ normalizer (E : Set G))
    (hQ : E ≤ centralizer (pCoreOf 2 H : Set G)) :
    ∃ ρ : Bar2 H →* MulAut ↥E, ∀ (h : ↥H) (e : ↥E),
      ((ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) e : ↥E) : G) = (h : G) * (e : G) * (h : G)⁻¹ := by
  haveI : Subgroup.Normalizes H E := ⟨hHE⟩
  let ρH : ↥H →* MulAut ↥E := MulDistribMulAction.toMulAut ↥H ↥E
  have hker : CFSG.pCore 2 ↥H ≤ ρH.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun e => ?_
    apply Subtype.ext
    have hqQ : (q : G) ∈ pCoreOf 2 H := Subgroup.mem_map.2 ⟨q, hq, rfl⟩
    have hcomm : (q : G) * (e : G) = (e : G) * (q : G) :=
      Subgroup.mem_centralizer_iff.1 (hQ e.2) (q : G) hqQ
    show (q : G) * (e : G) * (q : G)⁻¹ = (e : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  exact ⟨QuotientGroup.lift _ ρH hker, fun h e => rfl⟩

theorem s16c1_G47_false_odd (D : Data G) (hkit : OmegaKit) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (h41 : R16_41 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x) (hU4 : IsU4 (Bar2 L) 1) (h46 : Concl1646 L x.val)
    (hch : Chosen1647 D V₀ V x.val) (hnle : ¬ V₀ ≤ pCoreOf 2 (centralizer ({x.val} : Set G)))
    (hodd : EqTimesOdd (starImg (centralizer ({x.val} : Set G)) (xInf L x.val))
      (starImg (centralizer ({x.val} : Set G)) (yGen L x.val))) : False := by
  classical
  have hS := ctx.sect
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hX := h46.2.2.1
  have hSt := G47Star.of_ctx hsp hL ctx hX
  have hVH : V ≤ centralizer ({x.val} : Set G) := s16c1_G47_le_centralizer hV x.val_mem
  have hVs4 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) V) ≤ 4 := by
    have h : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) V) *
        Nat.card ↥(uOne V x.val) = Nat.card ↥V := s16c1_G47_card_starImg_mul hVH
    have h4 := s16c1_G47_card_V_le_four D hkit h41 ctx hU4 h46
    have hpos : 0 < Nat.card ↥(uOne V x.val) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (by rw [h]; exact h4) hpos
  have hVX := s16c1_G47_comm_of_card_le_four hX hSt.conj_X hVs4
  obtain ⟨a, haV₀, ha1, haQ, hCa, hW⟩ := s16c1_G47_a_data D hS ctx.setup ctx.sylow hnle
  have haE : a ∈ eTwo D V₀ x.val := s16c1_G47_a_mem_eTwo D hS ctx.setup ctx.sylow haV₀ ha1 hW
  have hC := s16c1_cent_V0_le_pCore D hS ctx.setup ctx.sylow
  have hEQ : eTwo D V₀ x.val ≤ pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    s16c1_eTwo_le_pCoreOf D hC
  have hEcent : eTwo D V₀ x.val ≤
      centralizer (pCoreOf 2 (centralizer ({x.val} : Set G)) : Set G) :=
    s16c1_eTwo_le_centralizer D ctx.sylow
  obtain ⟨-, hEsq⟩ := s16c1_phi_eTwo D hP.elemAbelian₀ ctx.sylow hC
  have hEC := s16c1_G47_eTwo_le_cTilde D hkit hkitB hkitC h41 ctx
    (s16c1_G47_imgTil_large D hkit h41 ctx hU4 h46)
  have hVE := s16c1_comm_V_eTwo_le_uTwo D hV x.val_mem hP.le_normalizer hP.le_normalizer₀ hEC
  have hEinv : ∀ h ∈ centralizer ({x.val} : Set G),
      conjSubgroup (eTwo D V₀ x.val) h = eTwo D V₀ x.val := fun h hh => by
    simpa only [eTwo] using s16c1_conjSubgroup_hConjClosure (z := x.val)
      (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G)) hh
  have hHE : centralizer ({x.val} : Set G) ≤ normalizer (eTwo D V₀ x.val : Set G) :=
    fun h hh => (conjSubgroup_eq_iff_mem_normalizer (A := eTwo D V₀ x.val) (g := h)).1
      (hEinv h hh)
  obtain ⟨ρ, hρ⟩ := s16c1_G47_exists_action hHE hEcent
  have hE : ∀ e : ↥(eTwo D V₀ x.val), e * e = 1 := fun e =>
    Subtype.ext (by simpa [pow_two] using hEsq (e : G) e.2)
  have hEab : ∀ e₁ ∈ eTwo D V₀ x.val, ∀ e₂ ∈ eTwo D V₀ x.val, e₁ * e₂ = e₂ * e₁ :=
    fun e₁ h₁ e₂ h₂ => (Subgroup.mem_centralizer_iff.1 (hEcent h₁) e₂ (hEQ h₂)).symm
  have hT : ∀ v ∈ starImg (centralizer ({x.val} : Set G)) V, ∀ e : ↥(eTwo D V₀ x.val),
      ρ v e = e ∨ ρ v e = e * ⟨a, haE⟩ := by
    intro v hv e
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.1 hw
    have hcomm : ⁅(w : G), (e : G)⁆ ∈ uTwo D V₀ x.val :=
      hVE (Subgroup.commutator_mem_commutator hwV e.2)
    have hcQ : ⁅(w : G), (e : G)⁆ ∈ V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)) :=
      Subgroup.mem_inf.2 ⟨hcomm.1, hEQ hcomm.2⟩
    have hconj : ((ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w) e :
        ↥(eTwo D V₀ x.val)) : G) = (w : G) * (e : G) * (w : G)⁻¹ := hρ w e
    rcases hW _ hcQ with h1 | h1
    · left
      apply Subtype.ext
      rw [hconj]
      rw [commutatorElement_def] at h1
      exact mul_inv_eq_one.1 h1
    · right
      apply Subtype.ext
      rw [hconj]
      rw [commutatorElement_def] at h1
      have h2 : (w : G) * (e : G) * (w : G)⁻¹ = a * (e : G) := mul_inv_eq_iff_eq_mul.1 h1
      rw [h2]
      exact hEab a haE e e.2
  have hstab : ∀ r : Bar2 (centralizer ({x.val} : Set G)), ρ r ⟨a, haE⟩ = ⟨a, haE⟩ →
      ∀ v ∈ starImg (centralizer ({x.val} : Set G)) V,
        r * v * r⁻¹ ∈ starImg (centralizer ({x.val} : Set G)) V := by
    intro r hr v hv
    obtain ⟨w, rfl⟩ :=
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) r
    have hwa : (w : G) * a * (w : G)⁻¹ = a := by
      have h1 := congrArg Subtype.val hr
      rw [hρ w ⟨a, haE⟩] at h1
      exact h1
    have hwM : (w : G) ∈ D.M := s16c1_G47_stab_mem_M D hS haV₀ ha1 hwa
    have hB : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w ∈
        starImg (centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G) ⊓ D.M) :=
      Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨w.2, hwM⟩), rfl⟩
    exact hSt.conj_B _ hB v hv
  have hα : ∃ v ∈ starImg (centralizer ({x.val} : Set G)) V, ρ v ≠ 1 := by
    obtain ⟨w, hwV, e, heE, hne⟩ := s16c1_G47_alpha (L := L) D haE hCa hch
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) ⟨w, hVH hwV⟩,
      Subgroup.mem_map.2 ⟨⟨w, hVH hwV⟩, Subgroup.mem_subgroupOf.2 hwV, rfl⟩, fun h1 => hne ?_⟩
    have h2 := congrArg
      (fun f : MulAut ↥(eTwo D V₀ x.val) => ((f ⟨e, heE⟩ : ↥(eTwo D V₀ x.val)) : G)) h1
    simp only [MulAut.one_apply] at h2
    rw [hρ ⟨w, hVH hwV⟩ ⟨e, heE⟩] at h2
    exact h2
  exact s16c1_G47_odd_false hSt.pCore_bot hSt.pRank_le hSt.normal_Y hSt.le_XY hX hodd hSt.split
    hSt.conj_B hSt.pgroup hSt.sq hVX hE ρ (a := ⟨a, haE⟩)
    (fun h => ha1 (congrArg Subtype.val h)) hT hstab hα

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
