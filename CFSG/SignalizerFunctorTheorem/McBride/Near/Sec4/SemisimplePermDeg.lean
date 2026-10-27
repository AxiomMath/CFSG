module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PrimitiveProduct
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegSplit
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open CFSG.SignalizerFunctorTheorem.McBride CFSG.SignalizerFunctorTheorem.Nonsolvable

universe u v

theorem sum_permDeg_le_permDeg_pi_aux (n : ℕ) :
    ∀ (ι : Type u) [Fintype ι] (G : ι → Type v) [∀ i, Group (G i)] [∀ i, Finite (G i)]
      [∀ i, IsSimpleGroup (G i)], (∀ i, ¬ IsMulCommutative (G i)) → Fintype.card ι = n →
      ∑ i, permDeg (G i) ≤ permDeg (∀ i, G i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ G _ _ _ hnc hn
    classical
    have hsub : ProperSubproducts G := by
      intro p _ hp hnp
      obtain ⟨j, hj⟩ := hnp
      have hlt : Fintype.card {i // p i} < n := hn ▸ Fintype.card_subtype_lt hj
      exact ih _ hlt {i // p i} (fun i => G i) (fun i => hnc i) rfl
    rcases Nat.lt_or_ge (Fintype.card ι) 2 with h2 | h2
    · have h01 : Fintype.card ι = 0 ∨ Fintype.card ι = 1 := by omega
      rcases h01 with h0 | h1
      · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
        simp
      · obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp h1
        have := hu
        rw [Fintype.sum_unique]
        exact (permDeg_congr (MulEquiv.piUnique G)).symm.le
    · obtain ⟨f, hf⟩ := exists_injective_permDeg (H := ∀ i, G i)
      let _ : MulAction (∀ i, G i) (Fin (permDeg (∀ i, G i))) := MulAction.compHom _ f
      have hsmul : ∀ (q : ∀ i, G i) (ω : Fin (permDeg (∀ i, G i))), q • ω = f q ω :=
        fun _ _ => rfl
      have hfaith : ∀ q : ∀ i, G i, (∀ ω : Fin (permDeg (∀ i, G i)), q • ω = ω) → q = 1 := by
        intro q hq
        apply hf
        rw [map_one]
        refine Equiv.ext fun ω => ?_
        simpa [hsmul] using hq ω
      have hΩ : Nat.card (Fin (permDeg (∀ i, G i))) = permDeg (∀ i, G i) := by simp
      suffices h : ∑ i, permDeg (G i) ≤ Nat.card (Fin (permDeg (∀ i, G i))) by
        rwa [hΩ] at h
      by_cases hpt : MulAction.IsPretransitive (∀ i, G i) (Fin (permDeg (∀ i, G i)))
      · obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
        have hnt : Nontrivial (G i₀) := nontrivial_of_not_isMulCommutative (hnc i₀)
        obtain ⟨g, hg⟩ : ∃ g : G i₀, g ≠ 1 := exists_ne 1
        have hq1 : (Pi.mulSingle i₀ g : ∀ i, G i) ≠ 1 := fun h => hg (by simpa using congrFun h i₀)
        have hne : Nonempty (Fin (permDeg (∀ i, G i))) := by
          by_contra hne
          rw [not_nonempty_iff] at hne
          exact hq1 (hfaith _ fun ω => isEmptyElim ω)
        obtain ⟨a⟩ := hne
        by_cases hM : IsCoatom (MulAction.stabilizer (∀ i, G i) a)
        · exact sum_permDeg_le_of_isCoatom hnc hfaith a hM h2
        · have hMtop : MulAction.stabilizer (∀ i, G i) a ≠ ⊤ := by
            intro h
            refine hq1 (hfaith _ fun ω => ?_)
            obtain ⟨q, rfl⟩ := MulAction.exists_smul_eq (∀ i, G i) a ω
            have hmem : q⁻¹ * Pi.mulSingle i₀ g * q ∈ MulAction.stabilizer (∀ i, G i) a :=
              h ▸ Subgroup.mem_top _
            rw [MulAction.mem_stabilizer_iff] at hmem
            calc (Pi.mulSingle i₀ g : ∀ i, G i) • q • a
                = q • (q⁻¹ * Pi.mulSingle i₀ g * q) • a := by
                  simp only [mul_smul, smul_inv_smul]
              _ = q • a := by rw [hmem]
          obtain ⟨M, hlt, hMne⟩ : ∃ M, MulAction.stabilizer (∀ i, G i) a < M ∧ M ≠ ⊤ := by
            by_contra hno
            push Not at hno
            exact hM ⟨hMtop, fun M hM' => hno M hM'⟩
          exact sum_permDeg_le_of_lt_stabilizer hnc hsub hfaith hΩ.le a hlt hMne
      · exact sum_permDeg_le_of_not_pretransitive hnc hsub hfaith hΩ.le hpt

theorem sum_permDeg_le_permDeg_pi {ι : Type u} [Fintype ι] (G : ι → Type v)
    [∀ i, Group (G i)] [∀ i, Finite (G i)] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) : ∑ i, permDeg (G i) ≤ permDeg (∀ i, G i) :=
  sum_permDeg_le_permDeg_pi_aux _ ι G hnc rfl

theorem lcalOf_eq_simpleComponents_top {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsSemisimple (⊤ : Subgroup Q)) :
    lcalOf Q = simpleComponents (⊤ : Subgroup Q) := by
  ext J
  constructor
  · rintro ⟨hsub, hs, hnc⟩
    have hJ : J ∈ lcal (⊤ : Subgroup Q) :=
      mem_lcal_iff.mpr ⟨le_top, hsub.subgroupOf, hs, hnc⟩
    rwa [hQ.lcal_eq] at hJ
  · exact mem_lcalOf_of_mem_simpleComponents_top

theorem permDeg_eq_sum_lcalOf {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsSemisimple (⊤ : Subgroup Q)) :
    permDeg Q = ∑ᶠ (J : Subgroup Q) (_ : J ∈ lcalOf Q), permDeg J := by
  classical
  set S := simpleComponents (⊤ : Subgroup Q) with hSdef
  have hSfin : S.Finite := Set.toFinite S
  have : Fintype S := hSfin.fintype
  have hdp : IsDirectProduct S (⊤ : Subgroup Q) := hQ
  let e : (∀ J : S, ↥(J : Subgroup Q)) ≃* ↥(⊤ : Subgroup Q) := hdp.equiv
  have e2 : Q ≃* (∀ J : S, ↥(J : Subgroup Q)) := Subgroup.topEquiv.symm.trans e.symm
  have hperm : permDeg Q = permDeg (∀ J : S, ↥(J : Subgroup Q)) := permDeg_congr e2
  have hsimple : ∀ J : S, IsSimpleGroup ↥(J : Subgroup Q) := fun J => J.2.2.2.1
  have hnc : ∀ J : S, ¬ IsMulCommutative ↥(J : Subgroup Q) := by
    intro J hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := J.2.2.2.2
    exact hxy (congrArg Subtype.val ((isMulCommutative_iff.mp hJ) ⟨x, hx⟩ ⟨y, hy⟩))
  have hle : permDeg (∀ J : S, ↥(J : Subgroup Q)) ≤ ∑ J : S, permDeg ↥(J : Subgroup Q) :=
    permDeg_pi_le _
  have hge : ∑ J : S, permDeg ↥(J : Subgroup Q) ≤ permDeg (∀ J : S, ↥(J : Subgroup Q)) :=
    sum_permDeg_le_permDeg_pi _ hnc
  rw [lcalOf_eq_simpleComponents_top hQ, ← finsum_subtype_eq_finsum_cond
    (f := fun J : Subgroup Q => permDeg ↥J) (fun J => J ∈ S), finsum_eq_sum_of_fintype, hperm]
  exact le_antisymm hle hge

end CFSG.SignalizerFunctorTheorem.McBride.Near
