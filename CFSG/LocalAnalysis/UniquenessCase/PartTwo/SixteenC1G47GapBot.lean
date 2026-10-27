module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Wrap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapQ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Schur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47QuotAct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Plane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private abbrev QE (V : Subgroup G) (z : G) : Type :=
  ↥(eOne V z) ⧸ (Subgroup.zpowers z).subgroupOf (eOne V z)

theorem s16c1_G47_gap_bot (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M) (ctx : G47Ctx D ⊥ V L hV x)
    (h46 : Concl1646 L x.val) (h47 : Concl1647 V x.val) (h47a : Concl1647a D ⊥ V x.val) :
    False := by
  classical
  obtain ⟨-, hcore, -, ⟨hEE, hEsq⟩, hVE⟩ := h47a.1 rfl
  have hS := ctx.sect
  have hz : x.val ∈ V := x.val_mem
  have hX := h46.2.2.1
  have hSt := G47Star.of_ctx hsp hL ctx hX
  have hVH : V ≤ centralizer ({x.val} : Set G) := s16c1_G47_le_centralizer hV hz
  have hV64 : Nat.card ↥V = 64 := s16c1_card_V_of_case D ctx.caseOne
  have hU32 : Nat.card ↥(uOne V x.val) = 32 := s16c1_card_uOne hV hz hV64 h47
  have hMV : D.M ≤ normalizer (V : Set G) := hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hP : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ normalizer (V : Set G) :=
    (s16c1_pCoreOf_le_M D ctx.sylow).trans hMV
  have hZU : Subgroup.zpowers x.val ≤ uOne V x.val := s16c1_zpowers_le_uOne hV hz
  have hUE : uOne V x.val ≤ eOne V x.val := s16c1_uOne_le_eOne V x.val
  have hEQ : eOne V x.val ≤ pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    s16c1_eOne_le_pCoreOf V x.val
  have hEH : eOne V x.val ≤ centralizer ({x.val} : Set G) :=
    hEQ.trans (Subgroup.map_subtype_le _)
  have hZE : Subgroup.zpowers x.val ≤ eOne V x.val := hZU.trans hUE
  have hEinv : ∀ h ∈ centralizer ({x.val} : Set G),
      conjSubgroup (eOne V x.val) h = eOne V x.val := fun h hh => by
    simpa only [eOne] using s16c1_conjSubgroup_hConjClosure (z := x.val) (uOne V x.val) hh
  have hHE : centralizer ({x.val} : Set G) ≤ normalizer (eOne V x.val : Set G) :=
    fun h hh => (conjSubgroup_eq_iff_mem_normalizer (A := eOne V x.val) (g := h)).1 (hEinv h hh)
  have hconjE : ∀ h ∈ centralizer ({x.val} : Set G), ∀ e ∈ eOne V x.val,
      h * e * h⁻¹ ∈ eOne V x.val := fun h hh e he =>
    (Subgroup.mem_normalizer_iff.1 (hHE hh) e).1 he
  have hZc : ∀ h ∈ centralizer ({x.val} : Set G), ∀ c ∈ Subgroup.zpowers x.val,
      h * c = c * h := fun h hh c hc =>
    mul_inv_eq_iff_eq_mul.1 (s16c1_G47_conj_zpowers_fix hh hc)
  haveI hZnorm : ((Subgroup.zpowers x.val).subgroupOf (eOne V x.val)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZE]
    intro e he
    exact (conjSubgroup_eq_iff_mem_normalizer (A := Subgroup.zpowers x.val) (g := e)).1
      (s16c1_G47_conj_zpowers (hEH he))
  have hUQ := s16c1_G47_comm_UQ D hkit h41 ctx h47
  have hEQc := s16c1_G47_comm_EQ hUQ
  obtain ⟨ρ, hρ⟩ := s16c1_G47_quot_action (H := centralizer ({x.val} : Set G))
    (E := eOne V x.val) (Z := Subgroup.zpowers x.val) hHE hZE hZc
    (fun q hq e he => hEQc (q : G) (Subgroup.mem_map.2 ⟨q, hq, rfl⟩) e he)
  have hρ' : ∀ (h : ↥(centralizer ({x.val} : Set G))) (e : ↥(eOne V x.val)),
      ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) h)
          (QuotientGroup.mk e) =
        (QuotientGroup.mk (⟨(h : G) * (e : G) * (h : G)⁻¹, hconjE h h.2 e e.2⟩ :
          ↥(eOne V x.val)) : QE V x.val) :=
    fun h e => hρ h e _ rfl
  have hρd : ∀ (w : ↥(centralizer ({x.val} : Set G))) (e : ↥(eOne V x.val)),
      ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w)
          (QuotientGroup.mk e) * QuotientGroup.mk e =
        (QuotientGroup.mk (⟨(w : G) * (e : G) * (w : G)⁻¹ * (e : G),
          (eOne V x.val).mul_mem (hconjE w w.2 e e.2) e.2⟩ : ↥(eOne V x.val)) : QE V x.val) := by
    intro w e
    rw [hρ' w e, ← QuotientGroup.mk_mul]
    rfl
  have hmk1 : ∀ e : ↥(eOne V x.val),
      (QuotientGroup.mk e : QE V x.val) = 1 ↔ (e : G) ∈ Subgroup.zpowers x.val := fun e =>
    (QuotientGroup.eq_one_iff e).trans Subgroup.mem_subgroupOf
  have hF : ∀ ē : QE V x.val, ē * ē = 1 := by
    intro ē
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective ē
    rw [← QuotientGroup.mk_mul, hmk1]
    have h := hEsq (e : G) e.2
    rw [pow_two] at h
    exact h
  have hz1 : x.val ≠ 1 := ctx.setup.ne_one
  have hcardZ : Nat.card ↥(Subgroup.zpowers x.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV.2 x.val hz) hz1
  obtain ⟨D₀, hD₀def⟩ : ∃ D₀ : Subgroup (QE V x.val), D₀ =
      ((uOne V x.val).subgroupOf (eOne V x.val)).map
        (QuotientGroup.mk' ((Subgroup.zpowers x.val).subgroupOf (eOne V x.val))) := ⟨_, rfl⟩
  have hD₀iff : ∀ e : ↥(eOne V x.val), (QuotientGroup.mk e : QE V x.val) ∈ D₀ ↔
      (e : G) ∈ uOne V x.val := by
    intro e
    rw [hD₀def]
    exact ⟨fun h => s16c1_G47_mem_of_mk_mem hUE hZU h,
      fun h => ⟨e, Subgroup.mem_subgroupOf.2 h, rfl⟩⟩
  have hD₀card : Nat.card ↥D₀ = 16 := by
    have h := s16c1_G47_card_image hUE hZU
    rw [hcardZ, hU32] at h
    have h' : Nat.card ↥D₀ * 2 = 32 := by
      rw [hD₀def]
      exact h
    omega
  have hdval : ∀ (w : ↥(centralizer ({x.val} : Set G))) (e : ↥(eOne V x.val)), (w : G) ∈ V →
      (w : G) * (e : G) * (w : G)⁻¹ * (e : G) ∈ uOne V x.val := fun w e hwV =>
    s16c1_G47_d_mem hV hz hP hwV e.2 (hEsq (e : G) e.2)
  have hVstar : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V,
      ∃ w : ↥(centralizer ({x.val} : Set G)), (w : G) ∈ V ∧
        QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w = u := by
    intro u hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu
    exact ⟨w, Subgroup.mem_subgroupOf.1 hw, hwu⟩
  have hVw : ∀ w : ↥(centralizer ({x.val} : Set G)), (w : G) ∈ V →
      QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w ≠ 1 →
        ∀ v ∈ V, v ∈ uOne V x.val ∨ (w : G)⁻¹ * v ∈ uOne V x.val := by
    intro w hwV hw1 v hv
    have hu : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) w ∈
        starImg (centralizer ({x.val} : Set G)) V :=
      Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 hwV, rfl⟩
    have hv' : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
        ⟨v, hVH hv⟩ ∈ starImg (centralizer ({x.val} : Set G)) V :=
      Subgroup.mem_map.2 ⟨⟨v, hVH hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rcases s16c1_G47_two_elems h47.1 hu hw1 _ hv' with h1 | h1
    · left
      refine Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_map.2 ⟨⟨v, hVH hv⟩, ?_, rfl⟩⟩
      exact (QuotientGroup.eq_one_iff _).1 h1
    · right
      refine Subgroup.mem_inf.2 ⟨V.mul_mem (V.inv_mem hwV) hv,
        Subgroup.mem_map.2 ⟨w⁻¹ * ⟨v, hVH hv⟩, ?_, rfl⟩⟩
      exact QuotientGroup.eq.1 h1.symm
  have hstabM : ∀ h : ↥(centralizer ({x.val} : Set G)), (h : G) ∈ D.M →
      ∀ f ∈ D₀, ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) h) f ∈
        D₀ := by
    intro h hM f hf
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective f
    rw [hD₀iff] at hf
    rw [hρ' h a, hD₀iff]
    have hconj := s16c1_conjSubgroup_uOne_eq h.2 (hMV hM)
    exact mem_conjSubgroup_iff.1 (by rw [hconj]; exact hf)
  have hXHL := s16c1_G47_xInf_le L x.val
  have hXH : xInf L x.val ≤ centralizer ({x.val} : Set G) := hXHL.trans inf_le_left
  have hXM : xInf L x.val ≤ D.M := (hXHL.trans inf_le_right).trans hL.1.le
  have hXperf : Group.IsPerfect ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) :=
    Group.isPerfect_def.mpr (s16c1_sl2five_facts hX).2.1
  have hDX : ∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), ∀ d ∈ D₀,
      ρ y d ∈ D₀ := by
    intro y hy d hd
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
    exact hstabM g (hXM (Subgroup.mem_subgroupOf.1 hg)) d hd
  have hirr : ∀ S : Subgroup (QE V x.val), S ≤ D₀ →
      (∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), ∀ s ∈ S, ρ y s ∈ S) →
        S = ⊥ ∨ S = D₀ := by
    intro S hSD hSst
    let S' : Subgroup G :=
      (S.comap (QuotientGroup.mk' ((Subgroup.zpowers x.val).subgroupOf (eOne V x.val)))).map
        (eOne V x.val).subtype
    have hS'mem : ∀ a : G, a ∈ S' ↔
        ∃ e : ↥(eOne V x.val), (QuotientGroup.mk e : QE V x.val) ∈ S ∧ (e : G) = a := by
      intro a
      constructor
      · intro ha
        obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 ha
        exact ⟨e, he, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact Subgroup.mem_map.2 ⟨e, he, rfl⟩
    have hZS' : Subgroup.zpowers x.val ≤ S' := by
      intro a ha
      refine (hS'mem a).2 ⟨⟨a, hZE ha⟩, ?_, rfl⟩
      rw [(hmk1 ⟨a, hZE ha⟩).2 ha]
      exact S.one_mem
    have hS'U : S' ≤ uOne V x.val := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := (hS'mem a).1 ha
      exact (hD₀iff e).1 (hSD he)
    have hS'st : ∀ g ∈ xInf L x.val, ∀ n ∈ S', g * n * g⁻¹ ∈ S' := by
      intro g hg n hn
      obtain ⟨e, he, rfl⟩ := (hS'mem n).1 hn
      have hgH : g ∈ centralizer ({x.val} : Set G) := hXH hg
      refine (hS'mem _).2 ⟨⟨g * e * g⁻¹, hconjE g hgH e e.2⟩, ?_, rfl⟩
      have hy : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
          ⟨g, hgH⟩ ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val) :=
        Subgroup.mem_map.2 ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
      have h1 := hSst _ hy _ he
      rwa [hρ' ⟨g, hgH⟩ e] at h1
    have hIrr := s16c1_G47_irr_card D hkit h41 ctx (hS'U.trans inf_le_left) hS'st
    have hlo : 2 ≤ Nat.card ↥S' := by
      have h := Subgroup.card_le_of_le hZS'
      rwa [hcardZ] at h
    have hhi : Nat.card ↥S' ≤ 32 := by
      have h := Subgroup.card_le_of_le hS'U
      rwa [hU32] at h
    rcases hIrr with h | h | h | h
    · omega
    · left
      have hEq : Subgroup.zpowers x.val = S' :=
        Subgroup.eq_of_le_of_card_ge hZS' (by rw [hcardZ, h])
      refine (Subgroup.eq_bot_iff_forall S).2 fun s hs => ?_
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective s
      have h1 : (e : G) ∈ S' := (hS'mem _).2 ⟨e, hs, rfl⟩
      rw [← hEq] at h1
      exact (hmk1 e).2 h1
    · right
      have hEq : S' = uOne V x.val := Subgroup.eq_of_le_of_card_ge hS'U (by rw [h, hU32])
      refine le_antisymm hSD fun f hf => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective f
      have ha : (a : G) ∈ uOne V x.val := (hD₀iff a).1 hf
      rw [← hEq] at ha
      obtain ⟨e, he, hea⟩ := (hS'mem _).1 ha
      have hea' : e = a := Subtype.ext hea
      rw [← hea']
      exact he
    · omega
  refine s16c1_G47_wrap hsp hL ctx h46 h47 hF ρ ?_ ?_ ?_
  ·
    intro u hu hu1
    obtain ⟨w, hwV, rfl⟩ := hVstar u hu
    by_contra hall
    push Not at hall
    have hcomm : ∀ e ∈ eOne V x.val, ⁅(w : G), e⁆ ∈ Subgroup.zpowers x.val := by
      intro e he
      have h1 := hall (QuotientGroup.mk ⟨e, he⟩)
      rw [hρd w ⟨e, he⟩, hmk1] at h1
      have h1' : (w : G) * e * (w : G)⁻¹ * e ∈ Subgroup.zpowers x.val := h1
      have e1 : ⁅(w : G), e⁆ = ((w : G) * e * (w : G)⁻¹ * e) * (e ^ 2)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact (Subgroup.zpowers x.val).mul_mem h1' ((Subgroup.zpowers x.val).inv_mem (hEsq e he))
    have hVEz : ⁅V, eOne V x.val⁆ ≤ Subgroup.zpowers x.val :=
      s16c1_G47_comm_V_of_w hEE w.2 (hVw w hwV hu1) hcomm
    have hUz : uOne V x.val ≤ Subgroup.zpowers x.val :=
      hVE.symm.le.trans (sup_le hVEz le_rfl)
    have h2 := Subgroup.card_le_of_le hUz
    rw [hU32, hcardZ] at h2
    omega
  ·
    intro u hu hu1 r hr e e' hee'
    obtain ⟨w, hwV, rfl⟩ := hVstar u hu
    obtain ⟨h, rfl⟩ :=
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) r
    obtain ⟨e₁, rfl⟩ := QuotientGroup.mk_surjective e
    obtain ⟨e₂, rfl⟩ := QuotientGroup.mk_surjective e'
    have hb : (w : G) * (e₁ : G) * (w : G)⁻¹ * (e₁ : G) ∈ uOne V x.val := hdval w e₁ hwV
    have hb' : (w : G) * (e₂ : G) * (w : G)⁻¹ * (e₂ : G) ∈ uOne V x.val := hdval w e₂ hwV
    rw [hρd w e₁, hρd w e₂, hρ' h] at hee'
    rw [hρd w e₁]
    have hhb : (h : G) * ((w : G) * (e₁ : G) * (w : G)⁻¹ * (e₁ : G)) * (h : G)⁻¹ ∈
        uOne V x.val := by
      have h1 := (hD₀iff _).1 (hee' ▸ (hD₀iff ⟨(w : G) * (e₂ : G) * (w : G)⁻¹ * (e₂ : G),
        (eOne V x.val).mul_mem (hconjE w w.2 e₂ e₂.2) e₂.2⟩).2 hb')
      exact h1
    by_cases hM : (h : G) ∈ D.M
    · exfalso
      have hB : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) h ∈
          starImg (centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G) ⊓ D.M) :=
        Subgroup.mem_map.2 ⟨h, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h.2, hM⟩), rfl⟩
      exact hr (s16c1_G47_conj_eq_of_two hu1 (s16c1_G47_two_elems h47.1 hu hu1)
        (hSt.conj_B _ hB _ hu))
    · have hle : uOne V x.val ⊓ conjSubgroup (uOne V x.val) (h : G) ≤ Subgroup.zpowers x.val := by
        by_contra hnle
        exact hM (hcore (h : G) h.2 hnle)
      exact (hmk1 _).2 (hle (Subgroup.mem_inf.2 ⟨hb, mem_conjSubgroup_iff.2 hhb⟩))
  ·
    intro u hu hu1 c q hq h5 hcq hcu hcX e
    obtain ⟨w, hwV, rfl⟩ := hVstar u hu
    obtain ⟨e₁, rfl⟩ := QuotientGroup.mk_surjective e
    rw [hρd w e₁]
    have hdD : (QuotientGroup.mk (⟨(w : G) * (e₁ : G) * (w : G)⁻¹ * (e₁ : G),
        (eOne V x.val).mul_mem (hconjE w w.2 e₁ e₁.2) e₁.2⟩ : ↥(eOne V x.val)) : QE V x.val) ∈ D₀ :=
      (hD₀iff _).2 (hdval w e₁ hwV)
    have hcB := s16c1_G47_cent_le_B hsp hL ctx hX c hcX
    have hcD : ∀ d ∈ D₀, ρ c d ∈ D₀ := by
      intro d hd
      obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hcB
      rw [← hyc]
      exact hstabM y (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).2 d hd
    exact s16c1_G47_schur16 ρ hF hD₀card hXperf hDX hirr hq h5
      (hcq ▸ pow_orderOf_eq_one c) hcX hcD _ hdD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
