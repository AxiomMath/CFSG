module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectOrth
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthMinus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

private theorem isSolvable_perm_fin_three : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  haveI : IsZGroup (Equiv.Perm (Fin 3)) := IsZGroup.of_squarefree (by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 3 = 2 * 3 from rfl]
    exact (Nat.squarefree_mul (by norm_num)).2
      ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)
  infer_instance

private theorem noFactor_of_isTrialityOddTransp {P : (T : Type) → [Group T] → Prop}
    (hNonab : ∀ (T : Type) [Group T], P T → ∃ a b : T, a * b ≠ b * a)
    (hOrth : ∀ (Y : Type) [Group Y] (m n : ℕ), IsOrthGp Y m n →
      ∀ (T : Type) [Group T], P T → ¬ E1.IsCompositionFactor Y T)
    {Y : Type} [Group Y] [Finite Y] {s : Y} (h : IsTrialityOddTransp Y s)
    (T : Type) [Group T] (hT : P T) : ¬ E1.IsCompositionFactor Y T := by
  intro hcf
  obtain ⟨ε, hε⟩ := h
  obtain ⟨a, b, hab⟩ := hNonab T hT
  rcases isCompositionFactor_of_normal ε.ker hcf with hK | hQ
  · set L : Subgroup Y := ε.ker ⊔ Subgroup.zpowers s with hLdef
    have hle : ε.ker ≤ L := le_sup_left
    have hK' : E1.IsCompositionFactor ↥(ε.ker.subgroupOf L) T :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hle).symm).1 hK
    have hL : E1.IsCompositionFactor ↥L T := kbr_isCompositionFactor_of_normal_subgroup _ hK'
    rcases isCompositionFactor_of_normal (Subgroup.center ↥L) hL with hZ | hQ'
    · exact hab (isCompositionFactor_commute
        (fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x.1)) hZ a b)
    · obtain ⟨f, F, hF, hFin, hcard, e, -⟩ := hε.orth
      exact hOrth (↥L ⧸ Subgroup.center ↥L) 8 f
        (Or.inl ⟨4, by norm_num, rfl, F, hF, hFin, hcard, ⟨e⟩⟩) T hT hQ'
  · have hcf3 : E1.IsCompositionFactor (Equiv.Perm (Fin 3)) T :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (QuotientGroup.quotientKerEquivOfSurjective ε hε.surjective)).1 hQ
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      isSolvable_perm_fin_three hcf3 a b)

theorem not_compFactor_of_isTrialityOddTransp (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] {s : X}
    (h : IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s))
    {T : Type} [Group T] (hT : CFSG.Quasithin.F6.IsL2 5 2 T ∨ LieModel T .PSp 2 5 1) :
    ¬ E1.IsCompositionFactor X T := by
  intro hcf
  rcases isCompositionFactor_of_normal (Subgroup.center X) hcf with hZ | hQ
  · have hcomm := isCompositionFactor_commute
      (fun x y : ↥(Subgroup.center X) => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x.1)) hZ
    rcases hT with hL2 | hPSp
    · haveI := Socle185Shape.finite (Or.inl ⟨5, 2, by norm_num, by norm_num, by norm_num, hL2⟩ :
        Socle185Shape T)
      obtain ⟨a, b, hab⟩ := Socle185Shape.exists_not_commute (Or.inl
        ⟨5, 2, by norm_num, by norm_num, by norm_num, hL2⟩ : Socle185Shape T)
      exact hab (hcomm a b)
    · obtain ⟨a, b, hab⟩ := Psp45Shape.exists_not_commute hO hPSp
      exact hab (hcomm a b)
  · rcases hT with hL2 | hPSp
    · have hShape : Socle185Shape T := Or.inl ⟨5, 2, by norm_num, by norm_num, by norm_num, hL2⟩
      exact noFactor_of_isTrialityOddTransp (P := Socle185Shape)
        (fun S _ hS => by
          haveI := Socle185Shape.finite hS
          exact Socle185Shape.exists_not_commute hS)
        (fun Y _ m n h => noSocle185Factor_of_isOrthGp hO h) h T hShape hQ
    · exact noFactor_of_isTrialityOddTransp (P := Psp45Shape)
        (fun S _ hS => Psp45Shape.exists_not_commute hO hS)
        (fun Y _ m n h => noPsp45Factor_of_isOrthGp hO h) h T hPSp hQ

end CFSG.LocalAnalysis.WeakClosure81
