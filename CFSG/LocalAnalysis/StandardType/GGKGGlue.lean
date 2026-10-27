module

public import CFSG.LocalAnalysis.StandardType.GGKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.StandardType.TCJ

private theorem kgg_ne_one {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (e : MulAut L') (he : e ≠ 1) (φ : MulAut R)
    (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) : φ ≠ 1 := by
  intro hφ1
  have hmem : ∀ l : L', e l * l⁻¹ ∈ Subgroup.center L' := by
    intro l
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ l, hφ1]
    simp
  let f : L' →* Subgroup.center L' :=
    { toFun := fun l => ⟨e l * l⁻¹, hmem l⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun l l' => by
        apply Subtype.ext
        have hb : l⁻¹ * (e l' * l'⁻¹) = (e l' * l'⁻¹) * l⁻¹ :=
          (Subgroup.mem_center_iff.1 (hmem l')) l⁻¹
        change e (l * l') * (l * l')⁻¹ = (e l * l⁻¹) * (e l' * l'⁻¹)
        rw [map_mul, mul_inv_rev]
        calc (e l * e l') * (l'⁻¹ * l⁻¹)
            = e l * ((e l' * l'⁻¹) * l⁻¹) := by group
          _ = e l * (l⁻¹ * (e l' * l'⁻¹)) := by rw [← hb]
          _ = (e l * l⁻¹) * (e l' * l'⁻¹) := by group }
  have hle : commutator L' ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf] at hle
  have hf1 : ∀ l : L', f l = 1 := fun l => hle (Subgroup.mem_top l)
  apply he
  ext l
  have h2 : e l * l⁻¹ = 1 := congrArg Subtype.val (hf1 l)
  calc e l = e l * l⁻¹ * l := by group
    _ = 1 * l := by rw [h2]
    _ = l := by simp

theorem ggPumpCLabelKnown_of_kgSimple
    (h : KGSimple) : GGPumpCLabelKnown := by
  intro p hp hp2 lab hlab
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hqP => ⟨hqP.1, ?_⟩) (ggTCJ_datum_marking hlab Q hQ)
  intro L' _ _ ψ hψ hker hperf e he1 hep hφe J k f hJ hk3 hlabJ
  let φ : MulAut R := hφe.choose
  have hφI : φ ∈ I := hφe.choose_spec.1
  have hφind : ∀ l : L', φ (ψ l) = ψ (e l) := hφe.choose_spec.2
  have hna : ∃ a b : R, a * b ≠ b * a := by
    by_contra hnab
    push Not at hnab
    haveI : IsMulCommutative R := isMulCommutative_iff.mpr hnab
    have hRcomm : commutator R = ⊥ := (commutator_eq_bot_iff R).mpr inferInstance
    have hmap : (commutator L').map ψ = ⊥ := by
      have h1 : (commutator L').map ψ = commutator R := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top_of_surjective _ hψ, commutator_def]
      rw [h1, hRcomm]
    have hle : commutator L' ≤ ψ.ker := by
      intro x hx
      have hx' : ψ x ∈ (commutator L').map ψ := ⟨x, hx, rfl⟩
      rw [hmap] at hx'
      exact hx'
    have hcenter : commutator L' ≤ Subgroup.center L' := hle.trans hker
    have hZtop : Subgroup.center L' = ⊤ := top_le_iff.mp (hperf ▸ hcenter)
    have hcommL' : commutator L' = ⊥ :=
      (commutator_eq_bot_iff L').mpr (isMulCommutative_iff.mpr fun a b =>
        (Subgroup.mem_center_iff.mp (hZtop.symm ▸ Subgroup.mem_top a) b).symm)
    have htopbot : (⊤ : Subgroup L') = ⊥ := by rw [← hperf, hcommL']
    haveI : Subsingleton L' := ⟨fun a b => by
      have ha : a = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top b)
      rw [ha, hb]⟩
    haveI : Subsingleton J := ⟨fun a b =>
      Subtype.ext (Subsingleton.elim (a : L') (b : L'))⟩
    haveI : Subsingleton (J ⧸ Subgroup.center J) := inferInstance
    haveI : Nontrivial (J ⧸ Subgroup.center J) := hJ.2.2.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (J ⧸ Subgroup.center J)
    exact hab (Subsingleton.elim a b)
  haveI : Finite R := hqP.2.1
  haveI : IsSimpleGroup R := (hqP.2.2 hna).1
  have hRinn : InnDiagKind R lab φ := (hqP.2.2 hna).2 φ hφI
  have hRcenter : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((e ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφind l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφp : φ ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have hev : (e ^ p) l = l := by simpa using congrArg (fun f : MulAut L' => f l) hep
    rw [hpow p l, hev]
    rfl
  have hφne : φ ≠ 1 := kgg_ne_one ψ hker hperf e he1 φ hφind
  have hdescent := ggTCJ_descent ψ hψ hker e φ hφind J hJ
  have hlabJ' : GGHasLabel ⟨.C, k, f⟩ ((J.map ψ) ⧸ Subgroup.center (J.map ψ)) :=
    ggHasLabel_of_mulEquiv hdescent.2.some hlabJ
  show KGLabConcl lab k f
  exact h p hp hp2 R lab φ (J.map ψ) trivial hlab hRcenter hRinn hφp hφne hdescent.1
    k f hk3 hlabJ'

end CFSG.StandardType.KG

end
