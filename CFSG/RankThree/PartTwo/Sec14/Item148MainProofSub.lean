module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

namespace Main148

theorem pCore_two_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [Finite X] (hX : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (CFSG.pCore_normal (p := 2) (G := X)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 X := by
      intro x
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨x, h ▸ Subgroup.mem_top x⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Nontrivial X := hX.toNontrivial
    have hZ : Nontrivial (Subgroup.center X) := hp.center_nontrivial
    rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ hc
    · obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top a : a ∈ Subgroup.center X)
        b).symm

theorem isoLThreePi_congr {X X' : Type} [Group X] [Group X'] {p e : ℕ} [Fact p.Prime]
    (φ : X ≃* X') (h : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi X' p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩

theorem item4_29_of_le
    (h429 : Sec4.Item4_29)
    {Γ : Type} [Group Γ] [Finite Γ] (C : Subgroup Γ) (hC4 : SectionFourHyp ↥C)
    (hCθ : aschbacherSolvableCore 3 ↥C = ⊥) (hCE : partTwoE ↥C = partTwoF ↥C)
    {A L K : Subgroup Γ} {c : Γ} (hAC : A ≤ C) (hLC : L ≤ C) (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hLq : IsQuasisimple ↥L) (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {c}) (hKs : IsSimpleGroup ↥K)
    (hKnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (htype : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi ↥K p e) ∨
      Nonempty (↥K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K ≃* Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥K ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥K ≃* Blueprint.NativeSporadic.J2))
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K : Set Γ)) :
    K = L ∨
      (Nonempty (↥K ≃* alternatingGroup (Fin 7)) ∧
        Nonempty (↥L ≃* alternatingGroup (Fin 10))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi ↥K 2 n ∧ Sec4.IsoLThreePi ↥L 2 (3 * n) ∧
        KFacts.InducesStdKind L c .field) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi ↥K 2 n ∧
        Blueprint.ChevalleyExceptionalModel ↥L .trialityD4 2 n ∧
        KFacts.InducesStdKind L c .graphField) := by
  have hcC : c ∈ C := hAC hcA
  have hKC : K ≤ C := (hKL.trans inf_le_left).trans hLC
  set c' : ↥C := ⟨c, hcC⟩ with hc'def
  set L' : Subgroup ↥C := L.subgroupOf C with hL'def
  set A' : Subgroup ↥C := A.subgroupOf C with hA'def
  set K' : Subgroup ↥C := K.subgroupOf C with hK'def
  set M : Subgroup ↥C := L' ⊓ Subgroup.centralizer ({c'} : Set ↥C) with hMdef
  have hK'M : K' ≤ M := by
    intro x hx
    have hx' : (x : Γ) ∈ L ⊓ Subgroup.centralizer {c} := hKL hx
    refine ⟨hx'.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  set K₀ : Subgroup ↥M := K'.subgroupOf M with hK₀def
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K := (Subgroup.subgroupOfEquivOfLe hK'M).trans (Subgroup.subgroupOfEquivOfLe hKC)
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
  have hK'eq : K' = K₀.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hK'M).symm
  have hK₀s : IsSimpleGroup ↥K₀ := MulEquiv.isSimpleGroup eK
  have hK₀nc : ∃ a b : ↥K₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnc
    exact ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩
  have hO2 : CFSG.pCore 2 ↥K₀ = ⊥ := pCore_two_eq_bot_of_isSimpleGroup hK₀s hK₀nc
  let eQ : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).trans eK
  have htype' : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
        Sec4.IsoLThreePi (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) p e) ∨
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* Blueprint.NativeSporadic.J2) := by
    rcases htype with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl ⟨p, e, hp, he, isoLThreePi_congr eQ.symm hiso⟩
    · exact Or.inr (Or.inl ⟨eQ.trans φ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨eQ.trans φ⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eQ.trans φ⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eQ.trans φ⟩)))
  have hcent' : Subgroup.zpowers c' = A' ⊓ Subgroup.centralizer (K' : Set ↥C) := by
    ext x
    have hx : x ∈ Subgroup.zpowers c' ↔ (x : Γ) ∈ Subgroup.zpowers c := by
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, by simp [hc'def]⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa [hc'def] using hn)⟩
    rw [hx, hcent, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    refine and_congr Iff.rfl ⟨fun h k hk => Subtype.ext (h (k : Γ) hk), fun h k hk => ?_⟩
    exact congrArg Subtype.val (h ⟨k, hKC hk⟩ hk)
  rcases h429 ↥C hC4 hCθ hCE A' hA' c' hc'A hc'1 L' hL' K₀ hK₀ K' hK'eq htype' hcent' with
    h1 | ⟨⟨φ⟩, ⟨ψ⟩⟩ | ⟨n, hn, hK2, hL2, hind⟩ | ⟨n, hn, hK2, hLD, hind⟩
  · left
    have h' := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left hKC, inf_of_le_left hLC] at h'
  · exact Or.inr (Or.inl ⟨⟨eK.symm.trans φ⟩, ⟨eL.symm.trans ψ⟩⟩)
  · have hind' := Sec13.inducesStdKind_sub C L' hind
    rw [Subgroup.map_subgroupOf_eq_of_le hLC] at hind'
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, isoLThreePi_congr eK hK2, isoLThreePi_congr eL hL2,
      hind'⟩))
  · have hind' := Sec13.inducesStdKind_sub C L' hind
    rw [Subgroup.map_subgroupOf_eq_of_le hLC] at hind'
    exact Or.inr (Or.inr (Or.inr ⟨n, hn, isoLThreePi_congr eK hK2,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL.symm hLD, hind'⟩))

end Main148

end CFSG.RankThree.PartTwo.Sec14
