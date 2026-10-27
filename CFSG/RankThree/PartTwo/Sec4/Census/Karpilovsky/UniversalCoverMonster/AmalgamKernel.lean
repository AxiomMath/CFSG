module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.SectionExtension
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.SectionDecomp
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamSplitting

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.Monster.GMS CFSG.AGLEmbedding

theorem kernelTrivialAt_of_amalgamCells {V : Type*} {Γ : SimpleGraph V} {X : Type} [Group X]
    [Finite X] [MulAction X V] (D : TitsData Γ X Bool) {p : ℕ} [hpp : Fact p.Prime]
    (hp2 : p ≠ 2) (Z : Subgroup X) (hZ : D.Xt true ≤ Z)
    (hXv : PerfectCoreCell p D.Xv) (hZc : PerfectCoreCell p Z)
    (hK : PerfectCoreOf p (D.Xv ⊓ D.Xe)) (hJ : PerfectCoreOf p (D.Xv ⊓ Z))
    (hKe : ∀ g ∈ D.Xe, ∀ k ∈ D.Xv ⊓ D.Xe, g * k * g⁻¹ ∈ D.Xv ⊓ D.Xe)
    (hKe_idx : Nat.Coprime ((D.Xv ⊓ D.Xe).relIndex D.Xe) p)
    (hKt : D.Xv ⊓ D.Xe ≤ D.Xt false)
    (hKt_norm : ∀ g ∈ D.Xt false, ∀ k ∈ D.Xv ⊓ D.Xe, g * k * g⁻¹ ∈ D.Xv ⊓ D.Xe)
    (hKt_ext : Nat.Coprime ((D.Xv ⊓ D.Xe).relIndex (D.Xt false)) p ∨
      ∀ g ∈ D.Xt false, ∃ k ∈ D.Xv ⊓ D.Xe, ∃ w ∈ D.Xt false ⊓ Z, g = k * w)
    (hKt_sq₁ : ∀ g ∈ D.Xv ⊓ D.Xt false, g ^ 2 ∈ D.Xv ⊓ D.Xe)
    (hKt_sq₂ : ∀ g ∈ D.Xe ⊓ D.Xt false, g ^ 2 ∈ D.Xv ⊓ D.Xe)
    (hKz : (D.Xv ⊓ D.Xe) ⊓ Z ≤ D.Xt true)
    (hKz_sq : ∀ g ∈ D.Xe ⊓ D.Xt true, g ^ 2 ∈ (D.Xv ⊓ D.Xe) ⊓ Z) :
    KernelTrivialAt X p := by
  intro E _ _ _ π hπ hC hp
  set K := D.Xv ⊓ D.Xe with hKdef
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpp.out).2 (Ne.symm hp2)
  obtain ⟨σv, hσv⟩ := exists_section_of_cell π hπ hC hp hXv
  obtain ⟨σz, hσz⟩ := exists_section_of_cell π hπ hC hp hZc
  have hKv : K ≤ D.Xv := inf_le_left
  have hKe' : K ≤ D.Xe := inf_le_right
  let σK : K →* E := σv.comp (Subgroup.inclusion hKv)
  have hσK : ∀ k, π (σK k) = k := fun k => hσv _
  have hKu : ∀ τ : K →* E, (∀ k, π (τ k) = k) → τ = σK := by
    obtain ⟨L, hLK, hLn, hL, hcop⟩ := hK
    intro τ hτ
    exact sectionDiff_eq_one π hC hp hLK hLn hL hcop τ σK hτ hσK
  have hvz : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ Z), σv ⟨a, ha⟩ = σz ⟨a, hb⟩ := by
    intro a ha hb
    obtain ⟨L, hLJ, hLn, hL, hcop⟩ := hJ
    have := sectionDiff_eq_one π hC hp hLJ hLn hL hcop (σv.comp (Subgroup.inclusion inf_le_left))
      (σz.comp (Subgroup.inclusion inf_le_right)) (fun x => hσv _) (fun x => hσz _)
    exact congrArg (fun f : (D.Xv ⊓ Z : Subgroup X) →* E => f ⟨a, ha, hb⟩) this
  obtain ⟨σe, hσe, hσeK⟩ := exists_section_extend π hπ hC hp hKe' hKe hKe_idx σK hσK hKu
  obtain ⟨σt0, hσt0, hσt0K⟩ : ∃ σ : D.Xt false →* E, (∀ x, π (σ x) = x) ∧
      ∀ k : K, σ (Subgroup.inclusion hKt k) = σK k := by
    rcases hKt_ext with hidx | hdec
    · exact exists_section_extend π hπ hC hp hKt hKt_norm hidx σK hσK hKu
    · let σW : (D.Xt false ⊓ Z : Subgroup X) →* E := σz.comp (Subgroup.inclusion inf_le_right)
      obtain ⟨σ, hσ, hσK'⟩ := exists_section_of_decomp π (N := D.Xt false) (K := K)
        (W := D.Xt false ⊓ Z) hKt (fun w hw k hk => hKt_norm w hw.1 k hk) hdec σK hσK hKu σW
        (fun w => hσz _) (fun x hxK hxW => by
          have := hvz x (hKv hxK) hxW.2
          exact this)
      exact ⟨σ, hσ, fun k => hσK' k k.2⟩
  let σt1 : D.Xt true →* E := σz.comp (Subgroup.inclusion hZ)
  have hσt1 : ∀ x, π (σt1 x) = x := fun x => hσz _
  let σt : ∀ j : Bool, D.Xt j →* E := fun j => Bool.rec (motive := fun j => D.Xt j →* E) σt0 σt1 j
  have hσt : ∀ j x, π (σt j x) = x := by
    intro j; cases j
    · exact hσt0
    · exact hσt1
  have hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), σv ⟨a, ha⟩ = σe ⟨a, hb⟩ := by
    intro a ha hb
    exact (hσeK ⟨a, ha, hb⟩).symm
  have hvt0 : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt false), σv ⟨a, ha⟩ = σt0 ⟨a, hb⟩ := by
    intro a ha hb
    have hNI : K ≤ D.Xv ⊓ D.Xt false := le_inf hKv hKt
    have := section_agree_of_pow_mem π hcop2 hC hp hNI hKt_sq₁
      (σv.comp (Subgroup.inclusion inf_le_left)) (σt0.comp (Subgroup.inclusion inf_le_right))
      (fun x => hσv _) (fun x => hσt0 _) (fun n hn => by
        have h1 : σv ⟨n, hKv hn⟩ = σK ⟨n, hn⟩ := rfl
        have h2 := hσt0K ⟨n, hn⟩
        exact h1.trans h2.symm)
    exact congrArg (fun f : (D.Xv ⊓ D.Xt false : Subgroup X) →* E => f ⟨a, ha, hb⟩) this
  have het0 : ∀ a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt false), σe ⟨a, ha⟩ = σt0 ⟨a, hb⟩ := by
    intro a ha hb
    have hNI : K ≤ D.Xe ⊓ D.Xt false := le_inf hKe' hKt
    have := section_agree_of_pow_mem π hcop2 hC hp hNI hKt_sq₂
      (σe.comp (Subgroup.inclusion inf_le_left)) (σt0.comp (Subgroup.inclusion inf_le_right))
      (fun x => hσe _) (fun x => hσt0 _) (fun n hn => by
        have h1 := hσeK ⟨n, hn⟩
        have h2 := hσt0K ⟨n, hn⟩
        exact h1.trans h2.symm)
    exact congrArg (fun f : (D.Xe ⊓ D.Xt false : Subgroup X) →* E => f ⟨a, ha, hb⟩) this
  have het1 : ∀ a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt true), σe ⟨a, ha⟩ = σt1 ⟨a, hb⟩ := by
    intro a ha hb
    have hNI : K ⊓ Z ≤ D.Xe ⊓ D.Xt true := le_inf (inf_le_left.trans hKe') hKz
    have := section_agree_of_pow_mem π hcop2 hC hp hNI hKz_sq
      (σe.comp (Subgroup.inclusion inf_le_left)) (σt1.comp (Subgroup.inclusion inf_le_right))
      (fun x => hσe _) (fun x => hσt1 _) (fun n hn => by
        have h1 := hσeK ⟨n, hn.1⟩
        have h2 : σK ⟨n, hn.1⟩ = σz ⟨n, hn.2⟩ := hvz n (hKv hn.1) hn.2
        exact h1.trans h2)
    exact congrArg (fun f : (D.Xe ⊓ D.Xt true : Subgroup X) →* E => f ⟨a, ha, hb⟩) this
  obtain ⟨s, hs⟩ := exists_section_of_titsData D π σv σe σt hσv hσe hσt hve
    (fun j a ha hb => by
      cases j
      · exact hvt0 a ha hb
      · exact (hvz a ha (hZ hb)))
    (fun j a ha hb => by
      cases j
      · exact het0 a ha hb
      · exact het1 a ha hb)
  exact ker_eq_bot_of_section π hC s hs

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
