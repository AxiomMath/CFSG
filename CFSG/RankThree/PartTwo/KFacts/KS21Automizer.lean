module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58
public import CFSG.RankThree.PartTwo.KFacts.KS21L44
public import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly.RankThreeEven (projSU projSL)

theorem card_normalizer_le_of_injective {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    {p : ℕ} [Fact p.Prime] [CharP k p] {n : ℕ} (hn : 1 ≤ n) (ρ : X →* GL (Fin n) k)
    (hρ : Function.Injective ρ) (A : Subgroup X) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAp : Nat.Coprime (Nat.card A) p) :
    Nat.card (Subgroup.normalizer (A : Set X)) ≤
      n.factorial * Nat.card (Subgroup.centralizer (A : Set X)) := by
  classical
  let ρ' : X →* LinearMap.GeneralLinearGroup k (Fin n → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ
  have hρ' : Function.Injective ρ' := Matrix.GeneralLinearGroup.toLin.injective.comp hρ
  set A' := A.map ρ' with hA'def
  have : Finite A' := Finite.of_surjective (ρ'.subgroupMap A) (ρ'.subgroupMap_surjective A)
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    rw [← map_mul, ← map_mul, hA r hr r' hr']
  have hA'p : Nat.Coprime (Nat.card A') p := by
    rw [hA'def, Subgroup.card_map_of_injective hρ']
    exact hAp
  have hfin : Module.finrank k (Fin n → k) = n := Module.finrank_fin_fun _
  obtain ⟨r, -, hrn, f, hf, -⟩ :=
    CFSG.LinearAlgebra.abelian_coprime_matrix_automizer_permutation_embedding (p := p)
      (by rw [hfin]; exact hn) A' hA'comm hA'p
  rw [hfin] at hrn
  set N := Subgroup.normalizer (A : Set X) with hNdef
  have hnorm : ∀ x : N, ρ' x ∈
      Subgroup.normalizer (A' : Set (LinearMap.GeneralLinearGroup k (Fin n → k))) := by
    intro x
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨(x : X) * b * (x : X)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp x.2 b).mp hb
  let φ := (ρ'.comp N.subtype).codRestrict _ hnorm
  let χ := f.comp ((QuotientGroup.mk' _).comp φ)
  have hker : ∀ x ∈ χ.ker, (x : X) ∈ Subgroup.centralizer (A : Set X) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' _) (φ x) = 1 := hf (by rw [map_one]; exact hx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx'
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ρ' a * ρ' x = ρ' x * ρ' a := Subgroup.mem_centralizer_iff.mp hx' _ ⟨a, ha, rfl⟩
    apply hρ'
    rw [map_mul, map_mul]
    exact h1
  have hcardker : Nat.card χ.ker ≤ Nat.card (Subgroup.centralizer (A : Set X)) :=
    Nat.card_le_card_of_injective (fun x => ⟨((x : N) : X), hker x x.2⟩)
      (fun x y h => by
        have h' : ((x : N) : X) = ((y : N) : X) :=
          congrArg (fun z : Subgroup.centralizer (A : Set X) => (z : X)) h
        exact Subtype.ext (Subtype.ext h'))
  have hcardrange : Nat.card χ.range ≤ n.factorial := by
    calc Nat.card χ.range ≤ Nat.card (Equiv.Perm (Fin r)) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = r.factorial := by rw [Nat.card_perm, Nat.card_fin]
      _ ≤ n.factorial := Nat.factorial_le hrn
  calc Nat.card N = Nat.card (N ⧸ χ.ker) * Nat.card χ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card χ.range * Nat.card χ.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
    _ ≤ n.factorial * Nat.card (Subgroup.centralizer (A : Set X)) :=
        Nat.mul_le_mul hcardrange hcardker

theorem terminalAutomizer : TerminalAutomizer := by
  intro X _ _ A hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun ⟨e⟩ hcard => ?_, fun ⟨e⟩ hcard => ?_⟩
  · have hcop : Nat.Coprime (Nat.card A) 2 := by rw [hcard]; norm_num
    have h := card_normalizer_le_of_injective (k := U58.K) (p := 2) (n := 5) (by norm_num)
      ((U58.SUI.subtype.comp U58.equivSUI.toMonoidHom).comp e.toMonoidHom)
      (Subtype.val_injective.comp (U58.equivSUI.injective.comp e.injective)) A hcomm hcop
    have h120 : Nat.factorial 5 = 120 := rfl
    rwa [h120] at h
  · have hcop : Nat.Coprime (Nat.card A) 2 := by rw [hcard]; norm_num
    have h := card_normalizer_le_of_injective (k := L44.F4) (p := 2) (n := 4) (by norm_num)
      ((Matrix.SpecialLinearGroup.toGL.comp L44.equivSL.toMonoidHom).comp e.toMonoidHom)
      (Matrix.SpecialLinearGroup.toGL_injective.comp (L44.equivSL.injective.comp e.injective))
      A hcomm hcop
    have h24 : Nat.factorial 4 = 24 := rfl
    rwa [h24] at h

end CFSG.RankThree.PartTwo.KFacts.KS21
