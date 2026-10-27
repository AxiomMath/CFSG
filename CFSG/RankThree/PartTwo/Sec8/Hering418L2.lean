module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Engine
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Open (IsElemAbelian)

namespace Hering418L2

variable {K : Type} [Field K]

theorem card_le_three_of_pgl2 [Finite K] (h3 : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K)
    (E : Subgroup (PGL2 K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (PGL2 K) :=
    Finite.of_surjective _ (Matrix.ProjGenLinGroup.mk_surjective (n := Fin 2) (R := K))
  set φ : PSL2 K →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL with hφdef
  have hφ : Function.Injective φ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hEr : E ≤ φ.range := fun e he => by
    obtain ⟨x, hx⟩ := KFacts.exists_toPGL_eq_of_pow_three (hexp e he)
    exact ⟨x, hx⟩
  set E' : Subgroup (PSL2 K) := E.comap φ with hE'
  have hcard : Nat.card E' = Nat.card E := by
    have h : Nat.card (E'.map φ) = Nat.card E' := Subgroup.card_map_of_injective hφ
    rw [hE', Subgroup.map_comap_eq_self hEr] at h
    exact h.symm
  have hE'p : IsPGroup 3 E' := fun g => ⟨1, Subtype.ext (by
    apply hφ
    simpa using hexp (φ g.1) (g.2))⟩
  obtain ⟨Q, hQ⟩ := hE'p.exists_le_sylow
  have hQc : IsCyclic Q := KFacts.isCyclic_sylow_three_psl2 h3 h4 Q
  have hsub : IsCyclic (E'.subgroupOf Q) := Subgroup.isCyclic _
  have hexp' : ∀ x : E'.subgroupOf Q, x ^ 3 = 1 := by
    intro x
    have hx : ((x : Q) : PSL2 K) ∈ E' := x.2
    have h1 : φ ((x : Q) : PSL2 K) ∈ E := hx
    have h2 : (((x : Q) : PSL2 K)) ^ 3 = 1 :=
      hφ (by rw [map_pow, map_one]; exact hexp _ h1)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h2
  have hdvd : Nat.card (E'.subgroupOf Q) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp'
  have hc2 : Nat.card (E'.subgroupOf Q) = Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

variable [Finite K]

theorem card_le_nine_of_mulAut_PSL2 (h3 : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K)
    (B : Subgroup (MulAut (PSL2 K))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K
  have hcycK := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K
    (by rw [Nat.card_eq_fintype_card, hK])).2
  set N := (pglAction K).range
  set C := (psl2FieldAut K).range
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psl2FieldAut K).rangeRestrict
      (psl2FieldAut K).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (PSL2 K))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, (KFacts.psl2FieldAut_mul_pglAction_mul_inv σ g).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨g, σ, hgσ⟩ := KFacts.exists_pglAction_mul_psl2FieldAut b
    exact ⟨pglAction K g, ⟨g, rfl⟩, psl2FieldAut K σ, ⟨σ, rfl⟩, hgσ⟩
  set E := (B ⊓ N).comap (pglAction K)
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) (KFacts.pglAction_injective (K := K))
    rw [Subgroup.map_comap_eq_self inf_le_right] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3' : Nat.card (B ⊓ N : Subgroup _) ≤ 3 := by
    rw [← hcardE]
    refine card_le_three_of_pgl2 h3 h4 E (fun x hx y hy => KFacts.pglAction_injective ?_)
      (fun x hx => KFacts.pglAction_injective ?_)
    · rw [map_mul, map_mul]
      exact hBc _ (Subgroup.mem_comap.mp hx).1 _ (Subgroup.mem_comap.mp hy).1
    · rw [map_pow, map_one]
      exact hB.2 _ (Subgroup.mem_comap.mp hx).1
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  omega

end Hering418L2

end CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GorensteinWalter

section One


@[expose] def IsLTwoOddNeThree (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 1 ≤ e ∧
    Nonempty (X ≃* projSL 2 (GaloisField p e))

theorem kF418ModelOn_L2 : KF418ModelOn (fun X _ => IsLTwoOddNeThree X) := by
  refine kF418ModelOn_of_bound ?_
  intro X _ _ ⟨p, e, hpf, hp2, hp3, he, ⟨φ⟩⟩
  set F := GaloisField p e with hF
  have hFcard : Nat.card F = p ^ e := GaloisField.card p e (by omega)
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F p]
    exact hp3
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    have hp5 : 5 ≤ p := by
      have := hpf.out.two_le
      have h5 : p ≠ 4 := fun h => by rw [h] at hpf; exact absurd hpf.out (by norm_num)
      omega
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  let ψ : X ≃* PSL2 F := φ.trans (Sec4.projSLEquivPSLn 2 F)
  refine ⟨⊤, le_top, fun σ _ => Subgroup.mem_top σ, ?_⟩
  intro F' hF' _
  have hle := Sec4.Hering418L2.card_le_nine_of_mulAut_PSL2 hchar h4
    (F'.map (MulAut.congr ψ).toMonoidHom) (hF'.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr ψ).injective] at hle

end One

end CFSG.RankThree.PartTwo.Sec8.Hering418
