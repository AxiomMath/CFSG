module

public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaDefs

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem ggTCJEnnolaKnown_of_simple
    (h : TCJEnnolaSimple) : GGTCJEnnolaKnown := by
  intro p hp hp2 lab hlab
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hqP => ⟨hqP.1, ?_⟩) (ggTCJ_datum_marking hlab Q hQ)
  intro hrow L' _ _ ψ hψ hker hperf e he hφe J hJ
  intro labJ₀ hlabJ₀ hhasJ₀
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
  have hRsimple : IsSimpleGroup R := (hqP.2.2 hna).1
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
    have hev : (e ^ p) l = l := by simpa using congrArg (fun f : MulAut L' => f l) he
    rw [hpow p l, hev]
    rfl
  have hlabel : GGHasLabel labJ₀ ((J.map ψ) ⧸ Subgroup.center (J.map ψ)) :=
    ggHasLabel_of_mulEquiv (ggTCJ_descent ψ hψ hker e φ hφind J hJ).2.some hhasJ₀
  obtain ⟨labJ, hlabJ, hhas, hdvd, hnotD2⟩ :=
    h p hp hp2 R lab φ (J.map ψ) hlab hrow hRcenter hRinn hφp
      (ggTCJ_descent ψ hψ hker e φ hφind J hJ).1 labJ₀ hlabJ₀ hlabel
  exact ⟨labJ, hlabJ,
    ggHasLabel_of_mulEquiv (ggTCJ_descent ψ hψ hker e φ hφind J hJ).2.some.symm hhas,
    hdvd, hnotD2⟩

end CFSG.StandardType.TCJ

end
