module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Transfer
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofSub

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSp)

theorem item4_31_of_le (h431 : Sec4.Ronan431.Item4_31List42) {Γ : Type} [Group Γ] [Finite Γ]
    (C : Subgroup Γ) (hC3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3)
    (hCθ : aschbacherSolvableCore 3 ↥C = ⊥) {A L K : Subgroup Γ} {c : Γ} (hAC : A ≤ C)
    (hLC : L ≤ C) (hA : Late.IsE27 A) (hcA : c ∈ A) (hc1 : c ≠ 1) (hLq : IsQuasisimple ↥L)
    (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hL42 : Sec4.Census.List42 (↥(L.subgroupOf C) ⧸ Subgroup.center ↥(L.subgroupOf C)))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {c})
    (hKs : IsSimpleGroup ↥K) (hKnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (hK6 : Nonempty (↥K ≃* alternatingGroup (Fin 6))) :
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥L ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (↥L ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥L ≃* projSp 2 (GaloisField 2 3)) := by
  have hcC : c ∈ C := hAC hcA
  have hKC : K ≤ C := (hKL.trans inf_le_left).trans hLC
  set c' : ↥C := ⟨c, hcC⟩
  set L' : Subgroup ↥C := L.subgroupOf C
  set A' : Subgroup ↥C := A.subgroupOf C
  set K' : Subgroup ↥C := K.subgroupOf C
  set M : Subgroup ↥C := L' ⊓ Subgroup.centralizer ({c'} : Set ↥C)
  have hK'M : K' ≤ M := by
    intro x hx
    have hx' : (x : Γ) ∈ L ⊓ Subgroup.centralizer {c} := hKL hx
    refine ⟨hx'.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  set K₀ : Subgroup ↥M := K'.subgroupOf M
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hK'M).trans (Subgroup.subgroupOfEquivOfLe hKC)
  have hA' : Late.IsE27 A' := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
    · have h := congrArg Subtype.val
        (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
      simpa using h
    · simpa using hA.1.2 _ hx
    · rw [← hA.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hc'A : c' ∈ A' := hcA
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hLn
  have hL' : IsComponent L' := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq,
    hL'n.isSubnormal⟩
  have hKq : IsQuasisimple ↥K := by
    have := hKs
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hKnc).1
  have hfmem : ∀ m : ↥M, ((m : ↥C) : Γ) ∈ L ⊓ Subgroup.centralizer {c} := by
    intro m
    refine ⟨m.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp m.2.2)
  let f : ↥M →* ↥(L ⊓ Subgroup.centralizer {c}) :=
    MonoidHom.codRestrict (C.subtype.comp M.subtype) (L ⊓ Subgroup.centralizer {c}) hfmem
  have hK₀eq : K₀ = (K.subgroupOf (L ⊓ Subgroup.centralizer {c})).comap f := by
    ext m
    exact Iff.rfl
  have hK₀ : IsComponent K₀ := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq,
    hK₀eq ▸ hKsub.comap f⟩
  have hK₀s : IsSimpleGroup ↥K₀ := MulEquiv.isSimpleGroup eK
  have hK₀nc : ∃ a b : ↥K₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnc
    exact ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩
  have hO2 : CFSG.pCore 2 ↥K₀ = ⊥ := Main148.pCore_two_eq_bot_of_isSimpleGroup hK₀s hK₀nc
  let eQ : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).trans eK
  have hK₀6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨φ⟩ := hK6
    exact ⟨eQ.trans φ⟩
  rcases h431 ↥C hC3 hCθ A' hA' c' hc'A hc'1 L' hL' hL42 K₀ hK₀ hK₀6 with
    ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl ⟨eL.symm.trans φ⟩
  · exact Or.inr (Or.inl ⟨eL.symm.trans φ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eL.symm.trans φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eL.symm.trans φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eL.symm.trans φ⟩)))

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
