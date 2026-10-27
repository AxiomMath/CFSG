module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.StandardType

theorem perm_solvable_quotient_card_le_two {N : ℕ} (hN : 5 ≤ N) {Q : Type*} [Group Q]
    (f : Equiv.Perm (Fin N) →* Q) (hf : Function.Surjective f) (hQ : IsSolvable Q) :
    Nat.card Q ≤ 2 := by
  have hX : 5 ≤ Cardinal.mk (Fin N) := by
    rw [Cardinal.mk_fin]
    exact_mod_cast hN
  by_cases hK : f.ker = ⊥
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hK
    haveI : Group.IsSolvable Q := hQ
    have hP : IsSolvable (Equiv.Perm (Fin N)) :=
      Group.isSolvable_of_isSolvable_injective (f := f) hinj
    exact absurd hP (Equiv.Perm.not_isSolvable (Fin N) hX)
  · have hnt : Nontrivial f.ker := (Subgroup.nontrivial_iff_ne_bot f.ker).mpr hK
    have hα : 5 ≤ Nat.card (Fin N) := by rw [Nat.card_fin]; exact hN
    have hA : alternatingGroup (Fin N) ≤ f.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal (N := f.ker) hα hnt
    haveI : Nontrivial (Fin N) := (Fin.nontrivial_iff_two_le).mpr (by omega)
    have hindex : f.ker.index ≤ 2 := by
      have hle : f.ker.index ≤ (alternatingGroup (Fin N)).index :=
        Subgroup.index_antitone hA
      rwa [alternatingGroup.index_eq_two] at hle
    have hiso : Equiv.Perm (Fin N) ⧸ f.ker ≃* Q :=
      QuotientGroup.quotientKerEquivOfSurjective f hf
    have hcard : Nat.card Q = f.ker.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr hiso.symm.toEquiv
    exact hcard.trans_le hindex

theorem ggSolvQuotLeTwo_of_surj {G : Type} [Group G] {X C : Subgroup G} {W : Type*} [Group W]
    (hW : ∀ (Q : Type) [Group Q] (f : W →* Q), Function.Surjective f → IsSolvable Q →
      Nat.card Q ≤ 2)
    (ρ : X →* W) (hρ : Function.Surjective ρ) (hk : ρ.ker ≤ C.subgroupOf X) :
    GGSolvQuotLeTwo X C := by
  intro N hN hCN hsolv
  have hker : ρ.ker ≤ N.comap (MonoidHom.id X) := by
    rw [Subgroup.comap_id]
    exact hk.trans hCN
  let q : X ⧸ ρ.ker →* X ⧸ N := QuotientGroup.map ρ.ker N (MonoidHom.id X) hker
  have hq : Function.Surjective q := by
    dsimp only [q]
    exact QuotientGroup.map_surjective_of_surjective ρ.ker N (MonoidHom.id X)
      (by simpa using QuotientGroup.mk_surjective) hker
  let e : X ⧸ ρ.ker ≃* W := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  let f : W →* X ⧸ N := q.comp e.symm.toMonoidHom
  have hf : Function.Surjective f := by
    dsimp only [f]
    exact hq.comp (MulEquiv.surjective e.symm)
  exact hW (X ⧸ N) f hf hsolv

end CFSG.StandardType
