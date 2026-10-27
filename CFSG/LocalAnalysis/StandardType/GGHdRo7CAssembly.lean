module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
import CFSG.LocalAnalysis.StandardType.GGMaxRankLinear
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm
import CFSG.LocalAnalysis.StandardType.GGHdRo7CNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7CRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CGen
import CFSG.LocalAnalysis.StandardType.GGHdRo7CFullWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CSignX
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLStab
import CFSG.LocalAnalysis.StandardType.GGResIO2bExcl
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_join_of_leaves : C2JoinLeaf :=
  have hG := c2_gen_holds
  have hF := c2_fullWeyl_holds
  fun p _ hp n hn V _ _ b AL Q S hAL hS hQ hsw => by
    obtain ⟨F, hFa, hsup⟩ := hG p hp n hn V b AL Q S hAL hS hQ hsw
    exact ⟨F, hFa, hsup, hF p hp n hn V b F hFa⟩

theorem c2_lin_of_leaves (hN : C2NormalizerLeaf) (hR : C2ReflLeaf) (hJ : C2JoinLeaf)
    {p : ℕ}
    [Fact p.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {b : Module.Basis (Fin (n + 1)) (ZMod p) V} {AL Q A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : C2LinData p n V b AL Q A) : ZS.LinWeyl p (AL ⊔ Q) := by
  have hX := c2_signx_holds
  obtain ⟨hp, hn, hAL, hALA, hQA, hStab, hNoT, ⟨S, hS, hQS, hconn⟩, hAJ, hnle⟩ := hD
  have hcls : ∀ s ∈ S, s ∈ Q ∧ GGLinRefl s ∧
      (C2SP p b s ∨ C2SignX p b s ∨ C2Swap p b s) := fun s hs =>
    ⟨(hS s hs).1, (hS s hs).2, hR p hp n hn V b A (fun a ha => hALA ((hAL a).mpr ha))
      (fun a ha h => hN p hp n hn V b a (hStab a ha h) h) hNoT s
      (hQA (hS s hs).1) (hS s hs).2⟩
  by_cases hsw : ∃ s ∈ S, C2Swap p b s
  · obtain ⟨F, hF, hsup, hW⟩ := hJ p hp n hn V b AL Q S hAL hcls hQS hsw
    rw [hsup]
    exact hW
  · exact (hX p hp n hn V b AL Q S hAL hcls hQS hconn hsw hnle hAJ).elim

theorem weyl_of_xDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatum p Bs X) : GGWeylReflectionGroup p (ggAutomizer X Bs) := by
  obtain ⟨Λ, _, _, M, C, V, _, _, ι, φ, h, α, hM, hC, hlin, hrefl, hpair, ⟨f, hf⟩, hgen⟩ := h
  exact ⟨Λ, M, hM, f, fun i => by rw [hf i]; exact hrefl i⟩

theorem c2_L_join_of_leaves (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hN : C2NormalizerLeaf)
    (hR : C2ReflLeaf) (hJoin : C2JoinLeaf) (hModel : C2LModelLeaf)
    (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf) (hAJ : C2AJLeaf) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      GGResRowAt ggRowCorank2C p J L →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hStab := c2_lstab_holds
  intro G _ _ p B Bs x L D J y K hH _ hrow
  have hp3 : p = 3 := by
    obtain ⟨-, -, -, -, -, -, h3, -⟩ := hrow
    exact h3
  by_cases hle : ggAutomizer K Bs ≤ ggAutomizer L Bs
  · rw [sup_eq_left.mpr hle]
    rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
    · exact weyl_of_xDatum hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  · obtain ⟨n, V, _, _, ι, b, hx, -, hn, hxb, hAL⟩ := hModel G p B Bs x L D J y K hH hrow
    have hDK : GGResXDatum p Bs K := by
      rcases (hX G p B Bs x L D J y K hH).2 with hD | h7
      · exact hD
      · exfalso
        obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
        omega
    obtain ⟨S, hS, hQ, hconn⟩ := hXD G p Bs K hDK V ι
    obtain ⟨hJne, hJle⟩ := hAJ hX hJ hRig hLB G p B Bs x L D J y K hH hrow
    have hstab := hStab G p B Bs x L D J y K hH hrow n V ι b hx hp3 hn hxb hAL
    have hDat : C2LinData p n V b ((ggAutomizer L Bs).map (ggLin (p := p) ι))
        ((ggAutomizer K Bs).map (ggLin (p := p) ι)) ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
      { hp := hp3
        hn := hn
        hAL := hAL
        hALA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
        hQA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
        hStab := hstab
        hNoT := hNoTV G p Bs hH.2.2.2.1 V ι
        hQgen := ⟨S, hS, hQ, hconn⟩
        hJ := by
          obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJne
          exact ⟨ggLin (p := p) ι (a : MulAut ↥Bs), Subgroup.mem_map_of_mem _ (hJle a.2).2,
            Subgroup.mem_map_of_mem _ (hJle a.2).1, fun h => ha1 (Subtype.ext
              (ggLin_injective (p := p) ι (by simpa using h)))⟩
        hnle := fun h => hle (fun a ha => by
          have := h (Subgroup.mem_map_of_mem (ggLin (p := p) ι) ha)
          obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp this
          exact (ggLin_injective (p := p) ι haa) ▸ ha') }
    have hW := c2_lin_of_leaves hN hR hJoin hDat
    exact ggRC_weylReflGroup_of_linWeyl ι _ (by rw [Subgroup.map_sup]; exact hW)

theorem c2_K_empty_of_leaves (hTCJ : GGTCJKnown) (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hN : C2NormalizerLeaf)
    (hR : C2ReflLeaf) (hContra : C2KContraLeaf) (hKModel : C2KModelLeaf)
    (hKStab : C2KStabLeaf) (hLOrder : C2LOrderLeaf) (hLFix : C2LFixGenLeaf)
    (hNoTV : NoTVLeaf) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      GGResRowAt ggRowCorank2C p J K → False := by
  intro G _ _ p B Bs x L D J y K hH _ hrow
  obtain ⟨n, V, _, _, ι, b, hy, hx, hp3, hn, hyb, hAK, c, hxc⟩ :=
    hKModel hRig hLB G p B Bs x L D J y K hH hrow
  have hDL : GGResXDatum p Bs L := by
    rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  obtain ⟨hfix, hgen⟩ := hLFix G p B Bs x L D J y K hH hDL V ι hx
  have hstab := hKStab G p B Bs x L D J y K hH hrow n V ι b hy hp3 hn hyb hAK
  have hord := hLOrder hTCJ hX hJ hRig hLB G p B Bs x L D J y K hH hrow n V ι b hy hp3 hn hyb hAK
  refine hContra hN hR p hp3 n hn V b ((ggAutomizer K Bs).map (ggLin (p := p) ι))
    ((ggAutomizer L Bs).map (ggLin (p := p) ι)) ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) c hAK
    (Subgroup.map_mono (ggAutomizer_mono Bs le_top))
    (Subgroup.map_mono (ggAutomizer_mono Bs le_top)) hstab (hNoTV G p Bs hH.2.2.2.1 V ι) ?_ hgen ?_
  · intro a ha
    have h := hfix a ha
    rwa [hxc] at h
  · rw [Subgroup.card_map_of_injective (ggLin_injective (p := p) ι)]
    exact hord

theorem ggResCorank2CInput_of_leaves (hTCJ : GGTCJKnown) (hX : GGResXDichotomyInput)
    (hJ : GGTBJInputR) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hN : C2NormalizerLeaf)
    (hR : C2ReflLeaf)
    (hContra : C2KContraLeaf) (hModel : C2LModelLeaf) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf)
    (hAJ : C2AJLeaf) (hKModel : C2KModelLeaf) (hKStab : C2KStabLeaf) (hLOrder : C2LOrderLeaf)
    (hLFix : C2LFixGenLeaf) : GGResCorank2CInput := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hrow
  rcases hrow with hL | hK
  · exact c2_L_join_of_leaves hX hJ hRig hLB hN hR c2_join_of_leaves hModel
      hNoTV hXD hAJ G p B Bs x L D J y K hH hL
  · exact (c2_K_empty_of_leaves hTCJ hX hJ hRig hLB hN hR hContra hKModel hKStab hLOrder hLFix hNoTV
      G p B Bs x L D J y K hH hK).elim

private theorem zmod_three_neg_one_add_neg_one : (-1 : ZMod 3) + (-1) = 1 := by decide

private theorem false_of_gen_le_three
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs L : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {V₀ : Type} [AddCommGroup V₀] [Module (ZMod p) V₀]
    (ι : Additive ↥Bs ≃+ V) (ι₀ : Additive ↥Bs ≃+ V₀)
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hALmodel : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    {Τ : Type} [Fintype Τ] (hcard : Fintype.card Τ ≤ 3)
    (r : Τ → (V₀ ≃ₗ[ZMod p] V₀)) (hh : Τ → V₀) (α : Τ → Module.Dual (ZMod p) V₀)
    (hr : ∀ t v, r t v = v - α t v • hh t)
    (hα : ∀ t, α t (hh t) = 2)
    (hgen : (ggAutomizer L Bs).map (ggLin (p := p) ι₀) =
      Subgroup.closure (Set.range r)) : False := by
  subst p
  classical
  have : Finite V₀ := Finite.of_equiv _ ι₀.toEquiv
  have : FiniteDimensional (ZMod 3) V₀ := Module.Finite.of_finite
  let A' : Subgroup (V₀ ≃ₗ[ZMod 3] V₀) := (ggAutomizer L Bs).map (ggLin (p := 3) ι₀)
  have hspan : CFSG.LinearAlgebra.movedSpan A' =
      Submodule.span (ZMod 3) (Set.range hh) := by
    rw [show A' = Subgroup.closure (Set.range r) from hgen]
    exact ggMaxRank_movedSpan_eq (p := 3) (by norm_num) r hh α hr hα
  have hfin_le : Module.finrank (ZMod 3) (CFSG.LinearAlgebra.movedSpan A') ≤ 3 := by
    rw [hspan]
    have hspan_eq : Submodule.span (ZMod 3) (Set.range hh) =
        Submodule.span (ZMod 3) ((Finset.univ.image hh : Finset V₀) : Set V₀) := by
      congr 1
      ext v
      simp
    rw [hspan_eq]
    have h1 : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) ((Finset.univ.image hh : Finset V₀) : Set V₀)) ≤
        (Finset.univ.image hh).card := finrank_span_finset_le_card (R := ZMod 3) _
    have h2 : (Finset.univ.image hh).card ≤ 3 := by
      calc (Finset.univ.image hh).card ≤ (Finset.univ : Finset Τ).card := Finset.card_image_le
        _ = Fintype.card Τ := Finset.card_univ
        _ ≤ 3 := hcard
    omega
  let e : V₀ ≃ₗ[ZMod 3] V :=
    LinearEquiv.ofBijective ((ι₀.symm.trans ι).toAddMonoidHom.toZModLinearMap 3)
      (ι₀.symm.trans ι).bijective
  have he_coe : ∀ w : V₀, e w = ι (ι₀.symm w) := fun w => rfl
  have he : ∀ (φ : MulAut ↥Bs) (w : V₀),
      e (ggLin (p := 3) ι₀ φ w) = ggLin (p := 3) ι φ (e w) := by
    intro φ w
    rw [ggLin_apply, ggLin_apply, he_coe]
    simp only [he_coe, AddEquiv.symm_apply_apply]
  have hmem : ∀ j : Fin n, e.symm (b j.succ) ∈ CFSG.LinearAlgebra.movedSpan A' := by
    intro j
    let s : V ≃ₗ[ZMod 3] V := CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ
    have hsp : C2SP 3 b s := by
      refine ⟨1, fun i => if i = j.succ then -1 else 1, ?_, ?_, ?_, ?_⟩
      · simp
      · dsimp only
        rw [if_neg (Ne.symm (Fin.succ_ne_zero j))]
      · intro i
        dsimp only
        by_cases h : i = j.succ <;> simp [h]
      · intro i
        rw [Equiv.Perm.one_apply]
        dsimp only
        by_cases h : i = j.succ
        · rw [h, if_pos rfl, CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
          simp
        · rw [if_neg h, CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne b h]
          simp
    obtain ⟨ψ, hψ, hψs⟩ := Subgroup.mem_map.mp ((hALmodel s).mpr hsp)
    let a : V₀ ≃ₗ[ZMod 3] V₀ := ggLin (p := 3) ι₀ ψ
    have ha : a ∈ A' := Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩
    have hmove : a (e.symm (b j.succ)) - e.symm (b j.succ) = e.symm (b j.succ) := by
      have h1 : e (a (e.symm (b j.succ))) = -b j.succ := by
        rw [he ψ (e.symm (b j.succ)), LinearEquiv.apply_symm_apply, hψs,
          CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
      have h2 : a (e.symm (b j.succ)) = -e.symm (b j.succ) := by
        have h := congrArg e.symm h1
        rw [map_neg, LinearEquiv.symm_apply_apply] at h
        exact h
      rw [h2]
      have hchar : (-e.symm (b j.succ)) - e.symm (b j.succ) = e.symm (b j.succ) := by
        have h3 : (-1 : ZMod 3) + (-1) = 1 := zmod_three_neg_one_add_neg_one
        calc -e.symm (b j.succ) - e.symm (b j.succ)
            = (-1 : ZMod 3) • e.symm (b j.succ) + (-1 : ZMod 3) • e.symm (b j.succ) := by
              simp only [neg_one_smul, sub_eq_add_neg]
          _ = ((-1 : ZMod 3) + (-1 : ZMod 3)) • e.symm (b j.succ) := by rw [add_smul]
          _ = (1 : ZMod 3) • e.symm (b j.succ) := by rw [h3]
          _ = e.symm (b j.succ) := one_smul _ _
      exact hchar
    exact Submodule.subset_span ⟨a, ha, e.symm (b j.succ), hmove.symm⟩
  have hLI : LinearIndependent (ZMod 3) (fun j : Fin n => e.symm (b j.succ)) := by
    have hb : LinearIndependent (ZMod 3) (fun i : Fin (n + 1) => e.symm (b i)) :=
      b.linearIndependent.map' e.symm.toLinearMap (LinearEquiv.ker e.symm)
    exact hb.comp Fin.succ (Fin.succ_injective n)
  have hspan_le : Submodule.span (ZMod 3) (Set.range (fun j : Fin n => e.symm (b j.succ))) ≤
      CFSG.LinearAlgebra.movedSpan A' := by
    rw [Submodule.span_le]
    rintro w ⟨j, rfl⟩
    exact hmem j
  have hfin_ge : n ≤ Module.finrank (ZMod 3) (CFSG.LinearAlgebra.movedSpan A') := by
    have hspanfin : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range (fun j : Fin n => e.symm (b j.succ)))) = n := by
      rw [finrank_span_eq_card hLI, Fintype.card_fin]
    calc n = Module.finrank (ZMod 3)
          (Submodule.span (ZMod 3) (Set.range (fun j : Fin n => e.symm (b j.succ)))) :=
          hspanfin.symm
      _ ≤ Module.finrank (ZMod 3) (CFSG.LinearAlgebra.movedSpan A') :=
          Submodule.finrank_mono hspan_le
  omega

private theorem common_reflection_of_le3_left
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs L J K : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hALmodel : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    (hD : GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny) :
    ∃ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧ a ≠ 1 := by
  subst p
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V₀, i5, i6, ι₀, φ, h, α,
    hS2, hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have hScard := hS3
  have hΛa3 := hA3
  have hne : Nonempty {i : Λ // i ∉ S} := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hS : ∀ i, i ∈ S := fun i => by
      by_contra hi
      exact hempty.false ⟨i, hi⟩
    have hcardΛ : Fintype.card Λ ≤ 3 := by
      have hSu : S = Finset.univ := Finset.eq_univ_of_forall hS
      rw [← Finset.card_univ, ← hSu]
      exact hScard
    let r : Λ → (V₀ ≃ₗ[ZMod 3] V₀) := fun i => ggLin (p := 3) ι₀ (φ (Sum.inl i))
    let h' : Λ → V₀ := fun i => h (Sum.inl i)
    let α' : Λ → Module.Dual (ZMod 3) V₀ := fun i => α (Sum.inl i)
    have hr : ∀ t v, r t v = v - α' t v • h' t := fun t v => hlin (Sum.inl t) v
    have hα : ∀ t, α' t (h' t) = 2 := fun t => by
      have hp := hpairL t t
      rw [hCLL.1 t] at hp
      simpa using hp
    have hgen : (ggAutomizer L Bs).map (ggLin (p := 3) ι₀) =
        Subgroup.closure (Set.range r) := by
      rw [hclosL, MonoidHom.map_closure]
      congr 1
      ext s
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨φ (Sum.inl i), ⟨i, rfl⟩, rfl⟩
    exact false_of_gen_le_three (p := 3) rfl (L := L) hn ι ι₀ b hALmodel hcardΛ r h' α' hr hα hgen
  obtain ⟨j⟩ := hne
  refine ⟨ggLin (p := 3) ι (φ (Sum.inl j.1)), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map]
    refine ⟨φ (Sum.inl j.1), ?_, rfl⟩
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
  · rw [Subgroup.mem_map]
    exact ⟨φ (Sum.inl j.1), by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨j.1, rfl⟩, rfl⟩
  · intro hzero
    exact ggIsReflection_ne_one (hrefl (Sum.inl j.1)) (ggLin_injective (p := 3) ι (by simpa only [map_one] using hzero))

private theorem common_reflection_of_le3_right
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs L J K : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hALmodel : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    (hD : GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny) :
    ∃ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧ a ≠ 1 := by
  subst p
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V₀, i5, i6, ι₀, φ, h, α,
    hS2, hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have hΛa3 := hA3
  have hne : Nonempty {i : Λ // i ∉ S} := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hzero : Fintype.card {i : Λ // i ∉ S} = 0 :=
      Fintype.card_eq_zero_iff.mpr hempty
    have hΛa3' : Fintype.card Λa ≤ 3 := by
      simpa [Nat.card_eq_fintype_card] using hΛa3
    have hcard : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) ≤ 3 := by
      rw [Fintype.card_sum, hzero, Nat.zero_add]
      exact hΛa3'
    let r : ({i : Λ // i ∉ S} ⊕ Λa) → (V₀ ≃ₗ[ZMod 3] V₀) :=
      fun o => ggLin (p := 3) ι₀ (φ (o.map Subtype.val id))
    let h' : ({i : Λ // i ∉ S} ⊕ Λa) → V₀ := fun o => h (o.map Subtype.val id)
    let α' : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod 3) V₀ :=
      fun o => α (o.map Subtype.val id)
    have hr : ∀ t v, r t v = v - α' t v • h' t :=
      fun t v => hlin (t.map Subtype.val id) v
    have hα : ∀ t, α' t (h' t) = 2 := fun t => by
      have hp := hpairK t t
      rw [hCKK.1 t] at hp
      simpa using hp
    have hgen : (ggAutomizer L Bs).map (ggLin (p := 3) ι₀) =
        Subgroup.closure (Set.range r) := by
      have hclosK' : ggAutomizer L Bs = Subgroup.closure
          (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
        rw [hclosK, Sum.range_eq]
        rfl
      rw [hclosK', MonoidHom.map_closure]
      congr 1
      ext s
      constructor
      · rintro ⟨x, ⟨o, rfl⟩, rfl⟩
        exact ⟨o, rfl⟩
      · rintro ⟨o, rfl⟩
        exact ⟨φ (o.map Subtype.val id), ⟨o, rfl⟩, rfl⟩
    exact false_of_gen_le_three (p := 3) rfl (L := L) hn ι ι₀ b hALmodel hcard r h' α' hr hα hgen
  obtain ⟨j⟩ := hne
  refine ⟨ggLin (p := 3) ι (φ (Sum.inl j.1)), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map]
    refine ⟨φ (Sum.inl j.1), ?_, rfl⟩
    rw [hclosL]
    exact Subgroup.subset_closure ⟨j.1, rfl⟩
  · rw [Subgroup.mem_map]
    exact ⟨φ (Sum.inl j.1), by
      rw [hclosK]
      exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩), rfl⟩
  · intro hzero
    exact ggIsReflection_ne_one (hrefl (Sum.inl j.1)) (ggLin_injective (p := 3) ι (by simpa only [map_one] using hzero))

theorem ggResLeviLE3_join_of_signedModel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hx : x ∈ Bs) (hn : 5 ≤ n)
    (hxb : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = b 0)
    (hALmodel : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hD23 : GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  by_cases hle : ggAutomizer K Bs ≤ ggAutomizer L Bs
  · rw [sup_eq_left.mpr hle]
    rcases hD23 with hD | hD
    · exact weyl_of_xDatum (ggResXDatum_left_of_leviLE3 hD)
    · exact weyl_of_xDatum (ggResXDatum_right_of_leviLE3 hD)
  · have hDK : GGResXDatum p Bs K := by
      rcases hD23 with hD | hD
      · exact ggResXDatum_right_of_leviLE3 hD
      · exact ggResXDatum_left_of_leviLE3 hD
    obtain ⟨S, hS, hQS, hconn⟩ := xDatumGraph_holds G p Bs K hDK V ι
    have hJ : ∃ a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι),
        a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧ a ≠ 1 := by
      rcases hD23 with hD | hD
      · exact common_reflection_of_le3_left hp3 hn ι b hALmodel hD
      · exact common_reflection_of_le3_right hp3 hn ι b hALmodel hD
    have hstab := hdRo7CLStab_main hH hnc ι b hx hxb hALmodel
    have hDat : C2LinData p n V b ((ggAutomizer L Bs).map (ggLin (p := p) ι))
        ((ggAutomizer K Bs).map (ggLin (p := p) ι)) ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
      { hp := hp3
        hn := hn
        hAL := hALmodel
        hALA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
        hQA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
        hStab := hstab
        hNoT := noTV_holds G p Bs hH.2.2.2.1 V ι
        hQgen := ⟨S, hS, hQS, hconn⟩
        hJ := hJ
        hnle := fun h => hle
          ((Subgroup.map_le_map_iff_of_injective (ggLin_injective (p := p) ι)).mp h) }
    have hW := c2_lin_of_leaves c2_normalizer_holds c2_refl_holds
      c2_join_of_leaves hDat
    exact ggRC_weylReflGroup_of_linWeyl ι (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
      (by rw [Subgroup.map_sup]; exact hW)

theorem ggResLeviExact2_join_of_signedModel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (hx : x ∈ Bs) (hn : 5 ≤ n)
    (hxb : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = b 0)
    (hALmodel : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hD2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  apply ggResLeviLE3_join_of_signedModel hH hp3 ι b hx hn hxb hALmodel hnc
  rcases hD2 with hD | hD
  · exact Or.inl
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K ggSelAny ggTypAny).mpr (Or.inl hD))
  · exact Or.inr
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs K J L ggSelAny ggTypAny).mpr (Or.inl hD))

end CFSG.StandardType.HdRo7C
