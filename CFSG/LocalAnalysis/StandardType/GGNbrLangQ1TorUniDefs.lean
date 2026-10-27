module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


@[expose] def ToralUni (R : Type) [Group R] (E : Subgroup (MulAut R)) : Prop :=
  ∀ (d m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 →
    ∀ θ : R ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)),
      IsMulCommutative ((E.map (MulAut.congr θ).toMonoidHom).comap
        (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m))))

private theorem l02qtu_map_congr_refl {R : Type} [Group R] (E : Subgroup (MulAut R)) :
    E.map (MulAut.congr (MulEquiv.refl R)).toMonoidHom = E := by
  ext a
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

theorem toralUni_commute_datum {d m : ℕ} {K : Type} [inst : Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))}
    (h : ToralUni _ E) :
    IsMulCommutative (E.comap (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)))) := by
  have h1 := h d m K inst ‹Finite K› hK (MulEquiv.refl _)
  rwa [l02qtu_map_congr_refl] at h1

@[expose] def UniOdd (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1)

theorem uniOdd_of_unitaryTorsion {p : ℕ} {lab : LargeEvenLabel} (h : UnitaryTorsion p lab) :
    UniOdd p lab :=
  ⟨h.1, h.2.1⟩

theorem uniOdd_of_pgu6 {p : ℕ} {lab : LargeEvenLabel} (h : PGU6 p lab) : UniOdd p lab := by
  obtain ⟨ht, hr, hp, hd⟩ := h
  subst hp
  refine ⟨ht, Nat.dvd_gcd ?_ hd⟩
  rw [hr]
  norm_num

theorem q1RToralTransfer_mono
    {Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop}
    {S S' : ℕ → LargeEvenLabel → Prop} {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : Q1RToralTransfer Toral S Rel) :
    Q1RToralTransfer Toral S' Rel :=
  fun p hp hp2 lab hlab hS' => h p hp hp2 lab hlab (hS p lab hS')

theorem exists_unitaryInvolution {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) :
    ∃ τ : K ≃+* K, (∀ x, τ (τ x) = x) ∧ ∀ x, τ x = x ^ 2 ^ m := by
  have h := unitaryFieldData_of_card hm hK
  let τ : K ≃+* K := RingEquiv.ofBijective h.bar
    ⟨h.bar.injective, fun y => ⟨h.bar y, h.bar_bar y⟩⟩
  exact ⟨τ, fun x => h.bar_bar x, fun x => h.bar_apply x⟩

end CFSG.StandardType
