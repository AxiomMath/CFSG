module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Tor

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {L : Type} [Field L]

@[expose] def secTuple (μ : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  fun _ => μ

@[expose] def secElt (μ : Lˣ) : ModGL TwistTag.D4.tag L :=
  rootDiagUnit TwistTag.D4.tag (secTuple μ) * diagramMap TwistTag.D4 L

theorem rootChar_secTuple (μ : Lˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (secTuple μ) v = μ ^ height v := by
  rw [rootChar, height]
  exact Finset.prod_zpow_eq_zpow_sum _ _ _

theorem secTuple_perm (μ : Lˣ) :
    (fun i => secTuple μ (TwistTag.D4.perm.symm i)) = secTuple μ :=
  rfl

theorem diagramMap_commute_secTuple (μ : Lˣ) :
    rootDiagUnit TwistTag.D4.tag (secTuple μ) * diagramMap TwistTag.D4 L =
      diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag (secTuple μ) := by
  rw [diagramMap_mul_rootDiagUnit, secTuple_perm]

theorem secElt_conj_eq (μ : Lˣ) (g : ModGL TwistTag.D4.tag L) :
    secElt μ * g * (secElt μ)⁻¹ = rootDiagUnit TwistTag.D4.tag (secTuple μ) *
      twistHom TwistTag.D4 L (RingHom.id L) g * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ := by
  rw [twistHom_id_eq, secElt]
  group

theorem secElt_conj_pinnedX (h2 : (2 : L) = 0) (μ : Lˣ) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (x : L) :
    secElt μ * pinnedX TwistTag.D4.tag L γ x * (secElt μ)⁻¹ =
      pinnedX TwistTag.D4.tag L (permLattice TwistTag.D4.perm γ)
        (((μ ^ height γ : Lˣ) : L) * x) := by
  rw [secElt_conj_eq, twistHom_id_pinnedX h2 hγ x,
    rootDiagUnit_conj_pinnedX _ (hγ.permLattice TwistTag.D4.cartan_perm), rootChar_secTuple,
    CFSG.LieType.Chevalley.height_permLattice]

theorem secElt_conj_rootDiagUnit (μ : Lˣ) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    secElt μ * rootDiagUnit TwistTag.D4.tag a * (secElt μ)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm.symm i)) := by
  have hP : diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag a *
      (diagramMap TwistTag.D4 L)⁻¹ =
        rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm.symm i)) := by
    rw [diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]
  calc secElt μ * rootDiagUnit TwistTag.D4.tag a * (secElt μ)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (secTuple μ) * (diagramMap TwistTag.D4 L *
        rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) *
          (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ := by rw [secElt]; group
    _ = _ := by
      rw [hP, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
      congr 1
      funext i
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_comm (secTuple μ i), mul_inv_cancel_right]

theorem weylTuple_inv (w : WeylGroup TwistTag.D4.tag) (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    weylTuple w b⁻¹ = (weylTuple w b)⁻¹ := by
  funext i
  simp only [weylTuple, rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem secElt_conj_canonicalRep (μ : Lˣ) {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTwist TwistTag.D4 w = w) :
    secElt μ * canonicalRep (coxeterSystem TwistTag.D4.tag) L w * (secElt μ)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (secTuple μ * (weylTuple w (secTuple μ))⁻¹) *
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
  have hP : twistHom TwistTag.D4 L (RingHom.id L) n = n := by
    rw [hn, twistHom_canonicalRep, hw]
  have hconj : n * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple w (secTuple μ))⁻¹ := by
    rw [rootDiagUnit_inv, canonicalRep_conj_rootDiagUnit, weylTuple_inv]
  rw [secElt_conj_eq, hP, rootDiagUnit_mul]
  calc rootDiagUnit TwistTag.D4.tag (secTuple μ) * n *
        (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ =
      rootDiagUnit TwistTag.D4.tag (secTuple μ) *
        (n * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ * n⁻¹) * n := by group
    _ = _ := by rw [hconj]

theorem rootDiagUnit_conj_mem_posUnipotent (a : Fin TwistTag.D4.tag.rank → Lˣ)
    {u : ModGL TwistTag.D4.tag L} (hu : u ∈ posUnipotent TwistTag.D4.tag L) :
    rootDiagUnit TwistTag.D4.tag a * u * (rootDiagUnit TwistTag.D4.tag a)⁻¹ ∈
      posUnipotent TwistTag.D4.tag L := by
  have h := ((chevalley_root_character_and_field_conjugation TwistTag.D4.tag L).2.2.2.1 a).2.1
  rw [← h]
  exact ⟨u, hu, rfl⟩

theorem secElt_conj_mem_posUnipotent (μ : Lˣ) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ posUnipotent TwistTag.D4.tag L) :
    secElt μ * u * (secElt μ)⁻¹ ∈ posUnipotent TwistTag.D4.tag L := by
  rw [secElt_conj_eq]
  exact rootDiagUnit_conj_mem_posUnipotent _
    (twistHom_mem_posUnipotent (RingHom.id L).surjective hu)

theorem rootDiagUnit_conj_mem_rootSpan (a : Fin TwistTag.D4.tag.rank → Lˣ)
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α)
    {u : ModGL TwistTag.D4.tag L} (hu : u ∈ rootSpan TwistTag.D4.tag L S) :
    rootDiagUnit TwistTag.D4.tag a * u * (rootDiagUnit TwistTag.D4.tag a)⁻¹ ∈
      rootSpan TwistTag.D4.tag L S := by
  have h : (rootSpan TwistTag.D4.tag L S).map
      (MulAut.conj (rootDiagUnit TwistTag.D4.tag a)).toMonoidHom = rootSpan TwistTag.D4.tag L S :=
    map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a (hS α hα)
  rw [← h]
  exact ⟨u, hu, rfl⟩

theorem secElt_conj_mem_rootSpan_inversionSet (μ : Lˣ) {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTwist TwistTag.D4 w = w) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ rootSpan TwistTag.D4.tag L (inversionSet w)) :
    secElt μ * u * (secElt μ)⁻¹ ∈ rootSpan TwistTag.D4.tag L (inversionSet w) := by
  rw [secElt_conj_eq]
  exact rootDiagUnit_conj_mem_rootSpan _ (fun α hα => hα.1)
    (twistHom_mem_rootSpan_inversionSet (RingHom.id L).surjective hw hu)

theorem secElt_conj_mem_torusGroup (μ : Lˣ) {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ torusGroup TwistTag.D4.tag L) :
    secElt μ * h * (secElt μ)⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  rw [secElt_conj_eq]
  have hT := twistHom_mem_torusGroup' (RingHom.id L).surjective hh
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have e : rootDiagUnit TwistTag.D4.tag (secTuple μ) * twistHom TwistTag.D4 L (RingHom.id L) h *
      (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ = twistHom TwistTag.D4 L (RingHom.id L) h := by
    rw [ha', rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm (secTuple μ) a',
      mul_assoc, mul_inv_cancel, mul_one]
  rw [e]
  exact hT

theorem secTuple_eq_twoTuple {μ : Lˣ} (hμ3 : μ ^ 3 = 1) : secTuple μ = twoTuple (μ ^ 2) := by
  have h1 : (μ ^ 2)⁻¹ = μ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hμ3]
  have h2 : (μ ^ 2) ^ 2 = μ := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hμ3, one_mul]
  funext i
  fin_cases i <;> simp [secTuple, twoTuple, h1, h2] <;> rfl

theorem rootDiagUnit_secTuple_mem_torusGroup {μ : Lˣ} (hμ3 : μ ^ 3 = 1) :
    rootDiagUnit TwistTag.D4.tag (secTuple μ) ∈ torusGroup TwistTag.D4.tag L := by
  rw [secTuple_eq_twoTuple hμ3, ← torusElt_two_eq]
  exact Subgroup.subset_closure ⟨(2, μ ^ 2), rfl⟩

theorem secElt_conj_mem_bruhatCell {μ : Lˣ} (hμ3 : μ ^ 3 = 1) {w : WeylGroup TwistTag.D4.tag}
    {x : ModGL TwistTag.D4.tag L} (hx : x ∈ bruhatCell TwistTag.D4.tag L w) :
    secElt μ * x * (secElt μ)⁻¹ ∈ bruhatCell TwistTag.D4.tag L (weylTwist TwistTag.D4 w) := by
  rw [secElt_conj_eq]
  obtain ⟨b, hb, b', hb', he⟩ :=
    mem_bruhatCell.1 (twistHom_mem_bruhatCell (RingHom.id L).surjective hx)
  have hdB : rootDiagUnit TwistTag.D4.tag (secTuple μ) ∈ borelGroup TwistTag.D4.tag L :=
    torusGroup_le_borelGroup (rootDiagUnit_secTuple_mem_torusGroup hμ3)
  refine mem_bruhatCell.2 ⟨rootDiagUnit TwistTag.D4.tag (secTuple μ) * b, mul_mem hdB hb,
    b' * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹, mul_mem hb' (inv_mem hdB), ?_⟩
  rw [← he]
  group

theorem rootDiagUnit_secFactor_mem_torusGroup {μ : Lˣ} (hμ3 : μ ^ 3 = 1)
    (w : WeylGroup TwistTag.D4.tag) :
    rootDiagUnit TwistTag.D4.tag (secTuple μ * (weylTuple w (secTuple μ))⁻¹) ∈
      torusGroup TwistTag.D4.tag L := by
  have hb := rootDiagUnit_secTuple_mem_torusGroup (L := L) hμ3
  rw [rootDiagUnit_mul, ← rootDiagUnit_inv, ← canonicalRep_conj_rootDiagUnit]
  exact mul_mem hb
    (inv_mem ((Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) _).1 hb))

theorem exists_sec_fixed_factor {μ : Lˣ} (hμ3 : μ ^ 3 = 1) {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ adjointGroup TwistTag.D4.tag L) (hfix : secElt μ * g * (secElt μ)⁻¹ = g) :
    ∃ w : WeylGroup TwistTag.D4.tag, weylTwist TwistTag.D4 w = w ∧
      ∃ v ∈ posUnipotent TwistTag.D4.tag L, ∃ h ∈ torusGroup TwistTag.D4.tag L,
      ∃ u ∈ posUnipotent TwistTag.D4.tag L,
        secElt μ * v * (secElt μ)⁻¹ = v ∧
        secElt μ * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) * (secElt μ)⁻¹ =
          h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧
        secElt μ * u * (secElt μ)⁻¹ = u ∧
        g = v * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) * u := by
  have hU : g ∈ ⋃ w, bruhatCell TwistTag.D4.tag L w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hgw⟩ := Set.mem_iUnion.1 hU
  have hδ : weylTwist TwistTag.D4 w = w := bruhatCell_injective (bruhatCell_eq_of_mem
    (hfix ▸ secElt_conj_mem_bruhatCell hμ3 hgw) hgw)
  refine ⟨w, hδ, ?_⟩
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := L) w).2.2 hgw
  simp only at hb hu hfix ⊢
  obtain ⟨-, -, -, -, -, hUH, -, huniq', -⟩ :=
    triangular_borel_structure.{0, 0} TwistTag.D4.tag L
  have hb' : b ∈ (posUnipotent TwistTag.D4.tag L : Set (ModGL TwistTag.D4.tag L)) *
      (torusGroup TwistTag.D4.tag L : Set (ModGL TwistTag.D4.tag L)) := by
    rw [← hUH]
    exact hb
  obtain ⟨v, hv, h, hh, rfl⟩ := hb'
  have huU : u ∈ posUnipotent TwistTag.D4.tag L :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos (w := w) h) hu
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
  set A := secElt μ with hA
  set f := secTuple μ * (weylTuple w (secTuple μ))⁻¹ with hf
  have hθn : A * n * A⁻¹ = rootDiagUnit TwistTag.D4.tag f * n := secElt_conj_canonicalRep μ hδ
  have hθv : A * v * A⁻¹ ∈ posUnipotent TwistTag.D4.tag L := secElt_conj_mem_posUnipotent μ hv
  have hθh : A * h * A⁻¹ ∈ torusGroup TwistTag.D4.tag L := secElt_conj_mem_torusGroup μ hh
  have hθu : A * u * A⁻¹ ∈ rootSpan TwistTag.D4.tag L (inversionSet w) :=
    secElt_conj_mem_rootSpan_inversionSet μ hδ hu
  have hdf : rootDiagUnit TwistTag.D4.tag f ∈ torusGroup TwistTag.D4.tag L :=
    rootDiagUnit_secFactor_mem_torusGroup hμ3 w
  have hθhf : A * h * A⁻¹ * rootDiagUnit TwistTag.D4.tag f ∈ torusGroup TwistTag.D4.tag L :=
    mul_mem hθh hdf
  have hθg : A * (v * h * n * u) * A⁻¹ =
      (A * v * A⁻¹ * (A * h * A⁻¹ * rootDiagUnit TwistTag.D4.tag f)) * n * (A * u * A⁻¹) := by
    calc A * (v * h * n * u) * A⁻¹ =
        (A * v * A⁻¹) * (A * h * A⁻¹) * (A * n * A⁻¹) * (A * u * A⁻¹) := by group
      _ = _ := by rw [hθn]; group
  rw [hθg] at hfix
  have hBθ : A * v * A⁻¹ * (A * h * A⁻¹ * rootDiagUnit TwistTag.D4.tag f) ∈
      borelGroup TwistTag.D4.tag L :=
    mul_mem (Subgroup.mem_sup_right hθv) (torusGroup_le_borelGroup hθhf)
  have hinj := (bijOn_bruhatCell (K := L) w).2.1 (Set.mk_mem_prod hBθ hθu)
    (Set.mk_mem_prod hb hu) hfix
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨h1, h2⟩ := hinj
  obtain ⟨hv', hh'⟩ := huniq' _ hθhf _ hh _ hθv _ hv h1
  refine ⟨v, hv, h, hh, u, huU, hv', ?_, h2, by group⟩
  calc A * (h * n) * A⁻¹ = (A * h * A⁻¹) * (A * n * A⁻¹) := by group
    _ = (A * h * A⁻¹ * rootDiagUnit TwistTag.D4.tag f) * n := by rw [hθn]; group
    _ = h * n := by rw [hh']

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
