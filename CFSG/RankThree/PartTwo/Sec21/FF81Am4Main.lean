module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Rig
public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Glue
import CFSG.RankThree.PartTwo.Sec21.FF81Am4Supp

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

namespace Am4

theorem sl2_mem_closure (A : SL(2, ZMod 2)) :
    A ∈ Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) := by
  have key : ∀ c : ZMod 2, (sl2Upper c = 1 ∨ sl2Upper c = sl2Upper 1) ∧
      (sl2Lower c = 1 ∨ sl2Lower c = sl2Lower 1) := by decide
  have hle : Subgroup.closure (Set.range (sl2Upper (k := ZMod 2)) ∪ Set.range sl2Lower) ≤
      Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rcases (key c).1 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.subset_closure (by simp)
    · rcases (key c).2 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.subset_closure (by simp)
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A)

theorem commute_of_gens {X : Type*} [Group X] (f f' : SL(2, ZMod 2) →* X)
    (h : ∀ a ∈ ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)),
      ∀ b ∈ ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)), f a * f' b = f' b * f a) :
    ∀ A B, f A * f' B = f' B * f A := by
  have step1 : ∀ A : SL(2, ZMod 2), ∀ b ∈ ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)),
      f A * f' b = f' b * f A := by
    intro A b hb
    have : Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) ≤
        (Subgroup.centralizer {f' b}).comap f := by
      rw [Subgroup.closure_le]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h a ha b hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this (sl2_mem_closure A))
  intro A B
  have : Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) ≤
      (Subgroup.centralizer {f A}).comap f' := by
    rw [Subgroup.closure_le]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (step1 A b hb).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this (sl2_mem_closure B))).symm

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}
  {fL : K3 →* G} {g : G}

theorem Setup.rel_a (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (A : SL(2, ZMod 2)) :
    fL (ι₁ A) = thetaM fL g (ι₀ A) := by
  rw [thetaM_apply, ← embS_shortBlock A, hs.hg.S, embS'_shortBlock A]

theorem ι₀_mem_supp (B : SL(2, ZMod 2)) :
    ι₀ B ∈ suppGroup (coords (0 : Fin 3) ∪ coords (1 : Fin 3)) :=
  isSupp_shortBlock (show (0 : Fin 3) ≠ 1 by decide) B

theorem ι₁_mem_supp (A : SL(2, ZMod 2)) :
    ι₁ A ∈ suppGroup (coords (1 : Fin 3) ∪ coords (2 : Fin 3)) :=
  isSupp_shortBlock (show (1 : Fin 3) ≠ 2 by decide) A

theorem nsElt_two_mem_supp :
    nsElt (K := ZMod 2) (n := 3) 2 ∈ suppGroup (coords (1 : Fin 3) ∪ coords (2 : Fin 3)) :=
  suppGroup_mono Set.subset_union_right (isSupp_longBlock (2 : Fin 3) zThreeSL)

theorem Setup.commute_thetaM_init (hs : Setup b L B b₁ b₂ b₃ t₀ fL g)
    (T : ThetaData t₀ fL) {x : K3} (hx : x ∈ P3)
    (hxs : x ∈ suppGroup (coords (1 : Fin 3) ∪ coords (2 : Fin 3))) (B' : SL(2, ZMod 2)) :
    thetaM fL g x * fL (ι₀ B') = fL (ι₀ B') * thetaM fL g x := by
  have hc : shiftHom ⟨x, hx⟩ * initHom (ι₀ B') = initHom (ι₀ B') * shiftHom ⟨x, hx⟩ :=
    Subtype.ext (commute_shiftEmb_initEmb hxs (ι₀_mem_supp B')).eq
  rw [hs.agree T ⟨x, hx⟩, Phi2_apply, ← T.init, ← map_mul, ← map_mul, hc]

theorem Setup.thetaM_nsElt_two (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    thetaM fL g (nsElt 2) = b := by
  rw [thetaM_apply, hs.e2, hs.hg.c1]

theorem Setup.rel_b
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) (A B' : SL(2, ZMod 2)) :
    thetaM fL g (ι₁ A) * fL (ι₀ B') = fL (ι₀ B') * thetaM fL g (ι₁ A) := by
  have hb := hs.hD.h4.basis
  refine commute_of_gens ((thetaM fL g).comp ι₁) (fL.comp ι₀) ?_ A B'
  intro a ha b' hb'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  show thetaM fL g (ι₁ a) * fL (ι₀ b') = fL (ι₀ b') * thetaM fL g (ι₁ a)
  rcases ha with rfl | rfl
  ·
    set n : K3 := nsElt 2 with hn
    set c : K3 := n⁻¹ * ι₁ (sl2Upper 1) * n with hc
    have hcP : c ∈ P3 :=
      Subgroup.mem_centralizer_singleton_iff.mpr commute_a_upper_conj.eq
    have hcs : c ∈ suppGroup (coords (1 : Fin 3) ∪ coords (2 : Fin 3)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ nsElt_two_mem_supp)
        (ι₁_mem_supp _)) nsElt_two_mem_supp
    have hy : fL (ι₀ b') ∈ L := hs.fL_mem _
    have hbc : Commute b (fL (ι₀ b')) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hb.hyp.hLC hy)).symm
    have hcy := hs.commute_thetaM_init T hcP hcs b'
    have hx : ι₁ (sl2Upper 1) = n * c * n⁻¹ := by rw [hc]; group
    rw [hx, map_mul, map_mul, map_inv, hn, hs.thetaM_nsElt_two]
    calc b * thetaM fL g c * b⁻¹ * fL (ι₀ b') =
        b * thetaM fL g c * (b⁻¹ * fL (ι₀ b')) := by group
      _ = b * thetaM fL g c * (fL (ι₀ b') * b⁻¹) := by rw [hbc.inv_left.eq]
      _ = b * (thetaM fL g c * fL (ι₀ b')) * b⁻¹ := by group
      _ = b * (fL (ι₀ b') * thetaM fL g c) * b⁻¹ := by rw [hcy]
      _ = (b * fL (ι₀ b')) * thetaM fL g c * b⁻¹ := by group
      _ = (fL (ι₀ b') * b) * thetaM fL g c * b⁻¹ := by rw [hbc.eq]
      _ = fL (ι₀ b') * (b * thetaM fL g c * b⁻¹) := by group
  · exact hs.commute_thetaM_init T
      (Subgroup.mem_centralizer_singleton_iff.mpr commute_a_lower.eq) (ι₁_mem_supp _) b'

theorem Setup.thetaM_ι₂_mem (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (A : SL(2, ZMod 2)) :
    thetaM fL g (ι₂ A) ∈ CenS L := by
  have hb := hs.hD.h4.basis
  have hbC : b ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hb.hyp.hLC hl)
  have ht0 : t₀ ∈ CenS L := hs.hD.h4.ht₀L
  have hle : Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) ≤
      (CenS L).comap ((thetaM fL g).comp ι₂) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · show thetaM fL g (ι₂ (sl2Upper 1)) ∈ CenS L
      rw [ι₂_sl2Upper, hs.thetaM_tM]; exact ht0
    · show thetaM fL g (ι₂ (sl2Lower 1)) ∈ CenS L
      rw [ι₂_sl2Lower, map_mul, map_mul, map_inv, hs.thetaM_tM, hs.thetaM_nsElt_two]
      exact (CenS L).mul_mem ((CenS L).mul_mem hbC ht0) ((CenS L).inv_mem hbC)
  exact hle (sl2_mem_closure A)

theorem Setup.rel_c (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (A : SL(2, ZMod 2)) (x : K3) :
    thetaM fL g (ι₂ A) * fL x = fL x * thetaM fL g (ι₂ A) :=
  (Subgroup.mem_centralizer_iff.mp (hs.thetaM_ι₂_mem A) (fL x) (hs.fL_mem x)).symm

theorem range_hom_K3 {X : Type*} [Group X] (f : K3 →* X) :
    f.range = (f.comp ι₀).range ⊔ (f.comp ι₁).range ⊔ (f.comp ι₂).range := by
  rw [MonoidHom.range_eq_map, ← iSup_nodes_eq_top, Subgroup.map_sup, Subgroup.map_sup,
    ← MonoidHom.range_comp, ← MonoidHom.range_comp, ← MonoidHom.range_comp]

noncomputable abbrev nodes (fL : K3 →* G) (g : G) : Subgroup G :=
  (fL.comp ι₀).range ⊔ (fL.comp ι₁).range ⊔ ((thetaM fL g).comp ι₁).range ⊔
    ((thetaM fL g).comp ι₂).range

theorem Setup.thetaM_range_le (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    (thetaM fL g).range ≤ nodes fL g := by
  have h0 : (thetaM fL g).comp ι₀ = fL.comp ι₁ :=
    MonoidHom.ext fun A => (hs.rel_a A).symm
  rw [range_hom_K3, h0]
  have h1 : (fL.comp ι₁).range ≤ nodes fL g :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have h2 : ((thetaM fL g).comp ι₁).range ≤ nodes fL g := le_sup_of_le_left le_sup_right
  have h3 : ((thetaM fL g).comp ι₂).range ≤ nodes fL g := le_sup_right
  exact sup_le (sup_le h1 h2) h3

theorem Setup.fL_tM_mem (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) :
    fL tM ∈ (thetaM fL g).range := by
  have hu : longBlock (ZMod 2) 3 1 (sl2Upper 1) ∈ S3 :=
    longBlock_mem_complSp (by decide : (1 : Fin 3) ≠ 2) (sl2Upper 1)
  have hshift : shiftHom ⟨longBlock (ZMod 2) 3 1 (sl2Upper 1), S3_le_P3 hu⟩ = initHom tM :=
    Subtype.ext (by
      show shiftEmb (longBlock (ZMod 2) 3 1 (sl2Upper 1)) = initEmb tM
      rw [shiftEmb_longBlock, tM, initEmb_longBlock]; rfl)
  refine ⟨longBlock (ZMod 2) 3 1 (sl2Upper 1), ?_⟩
  rw [hs.agree_S T hu, Phi2_apply, hshift, T.init]

theorem Setup.L_le_nodes
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) : L ≤ nodes fL g := by
  have hM := hs.thetaM_range_le
  rw [← hs.range, range_hom_K3 fL]
  have h0 : (fL.comp ι₀).range ≤ nodes fL g :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have h1 : (fL.comp ι₁).range ≤ nodes fL g :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hb₁ : b₁ ∈ nodes fL g := hM ⟨nsElt 1, by rw [thetaM_apply, hs.e1, hs.hg.c2]⟩
  have hfT : fL tM ∈ nodes fL g := hM (hs.fL_tM_mem T)
  have h2 : (fL.comp ι₂).range ≤ nodes fL g := by
    have hle : Subgroup.closure ({sl2Upper 1, sl2Lower 1} : Set SL(2, ZMod 2)) ≤
        (nodes fL g).comap (fL.comp ι₂) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · show fL (ι₂ (sl2Upper 1)) ∈ nodes fL g
        rw [ι₂_sl2Upper]; exact hfT
      · show fL (ι₂ (sl2Lower 1)) ∈ nodes fL g
        rw [ι₂_sl2Lower, map_mul, map_mul, map_inv, hs.e2]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁ hfT) (Subgroup.inv_mem _ hb₁)
    rintro y ⟨A, rfl⟩
    exact hle (sl2_mem_closure A)
  exact sup_le (sup_le h0 h1) h2

theorem Setup.T_le_nodes
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) : Op 2 (Cen t₀) ≤ nodes fL g := by
  have hD := hs.hD
  have hB := hD.h4.basis
  have hL := hs.L_le_nodes T
  have hM := hs.thetaM_range_le
  have hRp : ∀ r ∈ Rp t₀ b₃, r ∈ nodes fL g := by
    intro r hr
    rw [← hs.map_Qsub] at hr
    obtain ⟨x, -, hx⟩ := hr
    exact hM ⟨x, hx⟩
  refine hD.h4.le_of_le_le hD.h42 ?_ (fun r hr => hRp r hr)
  intro r hr
  obtain ⟨n, hnL, -, hn2, -⟩ := hB.monoL
  have hnC : n ∈ Cen t₀ := hD.h4.L_le_cen hnL
  have hmem : n * r * n⁻¹ ∈ Rp t₀ b₃ := by
    refine ⟨op_two_conj hnC hr.1, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hrb : r * b₂ = b₂ * r := Subgroup.mem_centralizer_singleton_iff.mp hr.2
    rw [← hn2]
    calc n * r * n⁻¹ * (n * b₂ * n⁻¹) = n * (r * b₂) * n⁻¹ := by group
      _ = n * (b₂ * r) * n⁻¹ := by rw [hrb]
      _ = n * b₂ * n⁻¹ * (n * r * n⁻¹) := by group
  have hr' : n * r * n⁻¹ ∈ nodes fL g := hRp _ hmem
  have : r = n⁻¹ * (n * r * n⁻¹) * n := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL hnL)) hr') (hL hnL)

theorem Setup.range_thetaM_le_OUpp (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    (thetaM fL g).range ≤ OUpp 2 (Cen b₃) := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Subgroup.closure {w : K3 | w * w = 1} := by
    rw [closure_sq_eq_top_K3]; exact Subgroup.mem_top x
  have hle : Subgroup.closure {w : K3 | w * w = 1} ≤ (OUpp 2 (Cen b₃)).comap (thetaM fL g) := by
    rw [Subgroup.closure_le]
    intro w hw
    have hw2 : thetaM fL g w * thetaM fL g w = 1 := by
      rw [← map_mul]; rw [Set.mem_setOf_eq] at hw; rw [hw, map_one]
    exact ⟨⟨thetaM fL g w, hs.thetaM_mem_cen w⟩,
      Subgroup.subset_normalClosure ⟨1, Subtype.ext (by
        show thetaM fL g w ^ (2 ^ 1) = 1
        rw [pow_one, sq]; exact hw2)⟩, rfl⟩
  exact hle hx

theorem Setup.OUpp_le_range (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) :
    OUpp 2 (Cen b₃) ≤ (thetaM fL g).range := by
  have hb := hs.hD.h4.basis
  rintro y ⟨⟨y', hy'⟩, hyn, rfl⟩
  have hnorm : ((thetaM fL g).range.subgroupOf (Cen b₃)).Normal := by
    refine ⟨fun m hm z => ?_⟩
    obtain ⟨zz, hzz⟩ := z
    obtain ⟨mm, hmm⟩ := m
    obtain ⟨x, hx⟩ : mm ∈ (thetaM fL g).range := hm
    have hz : zz * b₃ = b₃ * zz := Subgroup.mem_centralizer_singleton_iff.mp hzz
    have h0 : g * b * g⁻¹ = b₃ := hs.hg.c0
    have hzc : g⁻¹ * zz * g ∈ Cen b := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc g⁻¹ * zz * g * b = g⁻¹ * (zz * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (b₃ * zz) * g := by rw [h0, hz]
        _ = g⁻¹ * ((g * b * g⁻¹) * zz) * g := by rw [h0]
        _ = b * (g⁻¹ * zz * g) := by group
    have hnL : (g⁻¹ * zz * g) * fL x * (g⁻¹ * zz * g)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hb.hyp.hLN hzc) (fL x)).mp (hs.fL_mem x)
    rw [← hs.range] at hnL
    obtain ⟨x', hx'⟩ := hnL
    show zz * mm * zz⁻¹ ∈ (thetaM fL g).range
    refine ⟨x', ?_⟩
    rw [thetaM_apply, hx', ← hx, thetaM_apply]
    group
  have hsub : {gg : ↥(Cen b₃) | ∃ k : ℕ, gg ^ (2 ^ k) = 1} ⊆
      ((thetaM fL g).range.subgroupOf (Cen b₃) : Set ↥(Cen b₃)) := by
    rintro ⟨r, hr⟩ ⟨k, hk⟩
    obtain ⟨x, hx⟩ := hs.exists_thetaM_eq hr (k := k) (by simpa using congrArg Subtype.val hk)
    exact ⟨x, hx⟩
  exact Subgroup.normalClosure_le_normal hsub hyn

theorem Setup.generate
    (hs : Setup b L B b₁ b₂ b₃ t₀ fL g) (T : ThetaData t₀ fL) : nodes fL g = Y4 b₃ t₀ := by
  have hD := hs.hD
  apply le_antisymm
  · have hL : L ≤ Y4 b₃ t₀ := hD.h4.L_le_cen.trans (show Cen t₀ ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃) from
      le_sup_left)
    have hM : (thetaM fL g).range ≤ Y4 b₃ t₀ :=
      hs.range_thetaM_le_OUpp.trans (show OUpp 2 (Cen b₃) ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃) from
        le_sup_right)
    have h0 : (fL.comp ι₀).range ≤ Y4 b₃ t₀ := by
      rintro _ ⟨x, rfl⟩; exact hL (hs.fL_mem _)
    have h1 : (fL.comp ι₁).range ≤ Y4 b₃ t₀ := by
      rintro _ ⟨x, rfl⟩; exact hL (hs.fL_mem _)
    have h2 : ((thetaM fL g).comp ι₁).range ≤ Y4 b₃ t₀ := by
      rintro _ ⟨x, rfl⟩; exact hM ⟨_, rfl⟩
    have h3 : ((thetaM fL g).comp ι₂).range ≤ Y4 b₃ t₀ := by
      rintro _ ⟨x, rfl⟩; exact hM ⟨_, rfl⟩
    exact sup_le (sup_le (sup_le h0 h1) h2) h3
  · refine sup_le (fun x hx => ?_) (hs.OUpp_le_range.trans hs.thetaM_range_le)
    have hx' : x ∈ setMul (Op 2 (Cen t₀)) L := by rw [hD.h43.1]; exact hx
    obtain ⟨u, hu, l, hl, rfl⟩ := hx'
    exact Subgroup.mul_mem _ (hs.T_le_nodes T hu) (hs.L_le_nodes T hl)

end Am4

section CT4M


theorem ff81_4_amalgam' :
    KF_Sp6O7 → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G)
      (b₁ b₂ b₃ t₀ : G), FF81Sec4 b L B b₁ b₂ b₃ t₀ → FF81Conc4_2 b₂ b₃ → FF81Conc4_3 L t₀ →
      Opp 3 (Cen b) = ⊥ → HasLeviAmalgam Sp8 ↥(Y4 b₃ t₀) := by
  intro hKF G _ _ b L B b₁ b₂ b₃ t₀ h4 h42 h43 hO3
  have hD : Am4.Data b L B b₁ b₂ b₃ t₀ := ⟨h4, h42, h43, hO3⟩
  obtain ⟨g₀, c1, c2, c3, c0⟩ := hD.exists_cycle
  obtain ⟨fL, hinj, hrange, e0, e1, e2⟩ := hD.exists_std
  have hS : Am4.StdData b L b₁ b₂ b₃ fL g₀ := ⟨hinj, hrange, e0, e1, e2, c1, c2, c3, c0⟩
  obtain ⟨g, hg⟩ := hS.exists_g hD
  have hB := h4.basis
  obtain ⟨Θ, ht, hSv⟩ := hKF G L t₀ h4.ht₀ h4.L_le_cen hB.hyp.model h43.1 h43.2.1 h43.2.2
  obtain ⟨T⟩ := Am4.exists_thetaData h4.L_le_cen hinj hrange Θ ht hSv
  have hs : Am4.Setup b L B b₁ b₂ b₃ t₀ fL g := ⟨hD, hinj, hrange, e0, e1, e2, hg⟩
  have hLY : L ≤ Y4 b₃ t₀ := h4.L_le_cen.trans (show Cen t₀ ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃) from
    le_sup_left)
  have hMY : (Am4.thetaM fL g).range ≤ Y4 b₃ t₀ :=
    hs.range_thetaM_le_OUpp.trans
      (show OUpp 2 (Cen b₃) ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃) from le_sup_right)
  exact hasLeviAmalgam_of_glue_sub (Y4 b₃ t₀) fL (Am4.thetaM fL g)
    (fun x => hLY (hs.fL_mem x)) (fun x => hMY ⟨x, rfl⟩) hinj hs.thetaM_injective hs.rel_a
    (hs.rel_b T) (fun A B' => hs.rel_c A (Am4.ι₀ B')) (fun A B' => hs.rel_c A (Am4.ι₁ B'))
    (hs.generate T)

end CT4M

end CFSG.RankThree.PartTwo.Sec21.FF81
