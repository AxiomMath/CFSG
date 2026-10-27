module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Fitting

theorem s15_semiBot_fittingOf_map_conj {V : Type*} [CommGroup V] [Finite V]
    (H : Subgroup (MulAut V)) (φ : MulAut V) :
    fittingOf (H.map (MulAut.conj φ).toMonoidHom) =
      (fittingOf H).map (MulAut.conj φ).toMonoidHom := by
  set f : MulAut V →* MulAut V := (MulAut.conj φ).toMonoidHom with hf
  set B : Subgroup (MulAut V) := H.map f with hB
  let e : ↥H ≃* ↥B := Subgroup.equivMapOfInjective H f (MulAut.conj φ).injective
  have hmap : B.subtype.comp e.toMonoidHom = f.comp H.subtype := by
    ext x
    rfl
  calc fittingOf B = (CFSG.fittingSubgroup ↥B).map B.subtype := rfl
    _ = ((CFSG.fittingSubgroup ↥H).map e.toMonoidHom).map B.subtype := by
      rw [← CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e]
    _ = (CFSG.fittingSubgroup ↥H).map (B.subtype.comp e.toMonoidHom) := by
      rw [Subgroup.map_map]
    _ = (CFSG.fittingSubgroup ↥H).map (f.comp H.subtype) := by rw [hmap]
    _ = ((CFSG.fittingSubgroup ↥H).map H.subtype).map f := by rw [Subgroup.map_map]
    _ = (fittingOf H).map f := rfl

end Fitting

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_semiBot_map_pCore_subtype_normal {A : Type*} [Group A] {H N : Subgroup A}
    (hHN : H ≤ N) (hHn : (H.subgroupOf N).Normal) :
    (((CFSG.pCore 2 ↥H).map H.subtype).subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff
    ((Subgroup.map_subtype_le (H := H) (CFSG.pCore 2 ↥H)).trans hHN)]
  intro q n hq hn
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
  let α : ↥H ≃* ↥H := {
    toFun := fun y => ⟨n * (y : A) * n⁻¹,
      (Subgroup.normal_subgroupOf_iff hHN).1 hHn y.1 n y.2 hn⟩
    invFun := fun y => ⟨n⁻¹ * (y : A) * n, by
      have h := (Subgroup.normal_subgroupOf_iff hHN).1 hHn y.1 n⁻¹ y.2 (N.inv_mem hn)
      simpa using h⟩
    left_inv := by intro y; ext; group
    right_inv := by intro y; ext; group
    map_mul' := by
      intro a b
      ext
      change n * ((a * b : ↥H) : A) * n⁻¹ =
        (n * (a : A) * n⁻¹) * (n * (b : A) * n⁻¹)
      rw [Subgroup.coe_mul]
      group }
  have hαx : α x ∈ CFSG.pCore 2 ↥H := by
    rw [← (Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥H)) α)]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact Subgroup.mem_map.mpr ⟨α x, hαx, by simp [α]⟩

theorem s15_semiBot_odd_card_fitting (h : Hyp151 D V₀ V L) :
    Odd (Nat.card ↥(fittingOf (barSub V₀ V h.isElemAbelian L))) := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := fittingOf Lb
  have hFL : F ≤ Lb := fittingOf_le Lb
  have hFn : (F.subgroupOf Lb).Normal :=
    (Subgroup.normal_subgroupOf_iff hFL).mpr fun x l hx hl => conj_mem_fittingOf hl hx
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥F := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  haveI : Group.IsNilpotent ↥F := fittingOf_nilpotent Lb
  obtain ⟨H2, hH2card, hH2norm⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := ↥F) h2
  have hH2p : IsPGroup 2 ↥H2 := IsPGroup.of_card (p := 2) (n := 1) (by rw [hH2card]; norm_num)
  have hH2le : H2 ≤ CFSG.pCore 2 ↥F := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hH2norm, hH2p⟩
  have hH2ne : H2 ≠ ⊥ := by
    intro hbot
    have : Nat.card ↥H2 = 1 := by rw [hbot]; simp
    omega
  have hpCore_ne : CFSG.pCore 2 ↥F ≠ ⊥ := fun hbot =>
    hH2ne (le_bot_iff.mp (hH2le.trans (le_of_eq hbot)))
  have hQne : (CFSG.pCore 2 ↥F).map F.subtype ≠ ⊥ := fun hbot =>
    hpCore_ne ((Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).1 hbot)
  have hQle : (CFSG.pCore 2 ↥F).map F.subtype ≤ Lb :=
    (Subgroup.map_subtype_le (H := F) (CFSG.pCore 2 ↥F)).trans hFL
  have hQn : (((CFSG.pCore 2 ↥F).map F.subtype).subgroupOf Lb).Normal :=
    s15_semiBot_map_pCore_subtype_normal hFL hFn
  have hQp : IsPGroup 2 ↥((CFSG.pCore 2 ↥F).map F.subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥F)) F.subtype
  have hQpn : IsPGroup 2 ↥(((CFSG.pCore 2 ↥F).map F.subtype).subgroupOf Lb) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
  have hcore := s15_Three_twoCore_barSub h
    (((CFSG.pCore 2 ↥F).map F.subtype).subgroupOf Lb) hQn hQpn
  have hQbot : (CFSG.pCore 2 ↥F).map F.subtype = ⊥ := by
    have hmap := congrArg (fun S : Subgroup ↥Lb => S.map Lb.subtype) hcore
    rw [Subgroup.map_bot, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQle] at hmap
    exact hmap
  exact hQne hQbot

theorem s15_semiBot_odd_card_iSup_fitting (h : Hyp151 D V₀ V L) :
    Odd (Nat.card ↥(⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      (fittingOf (barSub V₀ V h.isElemAbelian L)).map (MulAut.conj φ).toMonoidHom)) := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := fittingOf Lb
  have hoddF : Odd (Nat.card ↥F) := s15_semiBot_odd_card_fitting h
  have hcard : ∀ φ : MulAut (Vtil V₀ V hV),
      Nat.card ↥(F.map (MulAut.conj φ).toMonoidHom) = Nat.card ↥F :=
    fun φ => Subgroup.card_map_of_injective (MulAut.conj φ).injective
  have hodd : ∀ φ : ↥(Mbar D.M V₀ V hV),
      Odd (Nat.card ↥(F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom)) :=
    fun φ => by rw [hcard]; exact hoddF
  have hcomm : ∀ φ ψ : ↥(Mbar D.M V₀ V hV),
      F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom ≠
        F.map (MulAut.conj (ψ : MulAut (Vtil V₀ V hV))).toMonoidHom →
      ∀ x ∈ F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom,
      ∀ y ∈ F.map (MulAut.conj (ψ : MulAut (Vtil V₀ V hV))).toMonoidHom, Commute x y := by
    intro φ ψ hne x hx y hy
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M (φ : MulAut (Vtil V₀ V hV))).1 φ.2
    obtain ⟨g', hg'M, hg'ψ⟩ := (mem_barSub V₀ V hV D.M (ψ : MulAut (Vtil V₀ V hV))).1 ψ.2
    have hm : (g : G)⁻¹ ∈ D.M := D.M.inv_mem hgM
    have hm' : (g' : G)⁻¹ ∈ D.M := D.M.inv_mem hg'M
    have hbarφ : Lb.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L (g : G)⁻¹) := by
      rw [← hgφ, s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L]
      have hact : actTil V₀ V hV ⟨(g : G)⁻¹, hMs hm⟩ = (actTil V₀ V hV g)⁻¹ := by
        rw [show (⟨(g : G)⁻¹, hMs hm⟩ : stabTil V₀ V) = g⁻¹ from rfl, map_inv]
      rw [hact, inv_inv]
    have hbarψ : Lb.map (MulAut.conj (ψ : MulAut (Vtil V₀ V hV))).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L (g' : G)⁻¹) := by
      rw [← hg'ψ, s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm') L]
      have hact : actTil V₀ V hV ⟨(g' : G)⁻¹, hMs hm'⟩ = (actTil V₀ V hV g')⁻¹ := by
        rw [show (⟨(g' : G)⁻¹, hMs hm'⟩ : stabTil V₀ V) = g'⁻¹ from rfl, map_inv]
      rw [hact, inv_inv]
    have hne' : (g' : G)⁻¹ * ((g : G)⁻¹)⁻¹ ∉ nBar D.M V₀ V hV L := by
      intro hmem
      apply hne
      have heq : barSub V₀ V hV (conjSubgroup L (g' : G)⁻¹) =
          barSub V₀ V hV (conjSubgroup L (g : G)⁻¹) :=
        (s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV hm hm').1 hmem
      rw [← s15_semiBot_fittingOf_map_conj Lb (φ : MulAut (Vtil V₀ V hV)),
        ← s15_semiBot_fittingOf_map_conj Lb (ψ : MulAut (Vtil V₀ V hV)),
        hbarφ, hbarψ, heq]
    have hc := (s15_Kbar_commute_conj h hm hm' hne').1
    have hx' : x ∈ barSub V₀ V hV (conjSubgroup L (g : G)⁻¹) := by
      rw [← hbarφ]
      refine fittingOf_le _ ?_
      rw [s15_semiBot_fittingOf_map_conj Lb (φ : MulAut (Vtil V₀ V hV))]
      exact hx
    have hy' : y ∈ barSub V₀ V hV (conjSubgroup L (g' : G)⁻¹) := by
      rw [← hbarψ]
      refine fittingOf_le _ ?_
      rw [s15_semiBot_fittingOf_map_conj Lb (ψ : MulAut (Vtil V₀ V hV))]
      exact hy
    have hmem : ⁅x, y⁆ ∈ ⁅barSub V₀ V hV (conjSubgroup L (g : G)⁻¹),
        barSub V₀ V hV (conjSubgroup L (g' : G)⁻¹)⁆ :=
      Subgroup.commutator_mem_commutator hx' hy'
    rw [hc, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  have hmain := s15_Lin_odd_card_iSup (A := MulAut (Vtil V₀ V hV))
    (K := fun φ : ↥(Mbar D.M V₀ V hV) =>
      F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom) hodd hcomm
  have heq : (⨆ φ : ↥(Mbar D.M V₀ V hV),
        F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom) =
      ⨆ φ ∈ Mbar D.M V₀ V hV, F.map (MulAut.conj φ).toMonoidHom :=
    iSup_subtype'' (Mbar D.M V₀ V hV : Set (MulAut (Vtil V₀ V hV)))
      (fun φ => F.map (MulAut.conj φ).toMonoidHom)
  rw [heq] at hmain
  simpa [F, Lb] using hmain

theorem s15_semiBot_commSub_top_iSup_fitting (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hF : fittingOf (barSub V₀ V h.isElemAbelian L) ≠ ⊥) :
    commSub ⊤ (⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      (fittingOf (barSub V₀ V h.isElemAbelian L)).map (MulAut.conj φ).toMonoidHom) = ⊤ := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := fittingOf Lb
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ φ ∈ Mb, F.map (MulAut.conj φ).toMonoidHom
  have hFL : F ≤ Lb := fittingOf_le Lb
  have hFM : F ≤ Mb := hFL.trans (barSub_mono V₀ V hV h.le)
  have hFX : F ≤ X := by
    have h1 : (1 : MulAut (Vtil V₀ V hV)) ∈ Mb := Mb.one_mem
    have hK1 : F.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom = F := by
      rw [map_one MulAut.conj]
      exact Subgroup.map_id F
    calc F = F.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom := hK1.symm
      _ ≤ X := le_iSup₂_of_le (f := fun φ (_ : φ ∈ Mb) =>
          F.map (MulAut.conj φ).toMonoidHom) (1 : MulAut (Vtil V₀ V hV)) h1 le_rfl
  have hXne : X ≠ ⊥ := fun hbot => hF (le_bot_iff.mp (hFX.trans (le_of_eq hbot)))
  have hXM : X ≤ Mb := by
    refine iSup₂_le fun φ hφ => ?_
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hx
    exact Mb.mul_mem (Mb.mul_mem hφ (hFM hf)) (Mb.inv_mem hφ)
  have hXn : (X.subgroupOf Mb).Normal := by
    have h := s15_semiBot_iSup_map_conj_normal (K := F) (B := Mb) hFM
    have heq : (⨆ φ : ↥Mb, F.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom) =
        ⨆ φ ∈ Mb, F.map (MulAut.conj φ).toMonoidHom :=
      iSup_subtype'' (Mb : Set (MulAut (Vtil V₀ V hV)))
        (fun φ => F.map (MulAut.conj φ).toMonoidHom)
    rw [heq] at h
    exact h
  have hgen : ⨆ I ∈ irrSet X, I = ⊤ :=
    h1217 V₀ V h.hyp125 X hXne hXM hXn (Or.inl (s15_semiBot_odd_card_iSup_fitting h))
  have hmain : commSub ⊤ X = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup (Vtil V₀ V hV)) = ⨆ I ∈ irrSet X, I := hgen.symm
      _ ≤ commSub ⊤ X := iSup₂_le fun I hI => by
          rw [← hI.1]
          exact commSub_mono le_top le_rfl
  simpa [X, Mb, F, Lb] using hmain

theorem s15_semiBot_commSub_wTil_fitting (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hF : fittingOf (barSub V₀ V h.isElemAbelian L) ≠ ⊥) :
    commSub (wTil V₀ V h.isElemAbelian L) (fittingOf (barSub V₀ V h.isElemAbelian L)) =
      wTil V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := fittingOf Lb
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let N : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Mb ⊓ normalizer (Lb : Set (MulAut (Vtil V₀ V hV)))
  have hspan : commSub ⊤ (⨆ φ ∈ Mb, F.map (MulAut.conj φ).toMonoidHom) = ⊤ :=
    s15_semiBot_commSub_top_iSup_fitting h1217 h hF
  have hwt := s15_semiBot_wTil_eq_iSup_of_span h (Y := F) (fittingOf_le Lb) hspan
  have hEq : ∀ n : MulAut (Vtil V₀ V hV), n ∈ N →
      F.map (MulAut.conj n).toMonoidHom = F := by
    intro n hn
    have hnL : Lb.map (MulAut.conj n).toMonoidHom = Lb :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 hn.2
    rw [← s15_semiBot_fittingOf_map_conj Lb n, hnL]
  have hsup : (⨆ n ∈ N, commSub ⊤ (F.map (MulAut.conj n).toMonoidHom)) = commSub ⊤ F := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun n hn => ?_
      rw [hEq n hn]
    · have h1N : (1 : MulAut (Vtil V₀ V hV)) ∈ N := ⟨Mb.one_mem, Subgroup.one_mem _⟩
      have h := le_iSup₂_of_le (f := fun n (_ : n ∈ N) =>
          commSub ⊤ (F.map (MulAut.conj n).toMonoidHom))
        (1 : MulAut (Vtil V₀ V hV)) h1N le_rfl
      rwa [hEq 1 h1N] at h
  have hwtF : wTil V₀ V hV L = commSub ⊤ F := by
    rw [hwt, hsup]
  have hcop := CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_commSub_eq
    (s15_Infra_vtil_sq_eq_one V₀ V hV) (Y := F) (s15_semiBot_odd_card_fitting h)
  rw [hwtF]
  simpa [F, Lb] using hcop

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
