module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofSub
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def TypeEps148 (X : Type) [Group X] : Prop :=
  ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
    ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
      (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (X ≃* projSU 3 p f)))

@[expose] def Item4_29EpsOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → aschbacherSolvableCore 3 G = ⊥ →
    partTwoE G = partTwoF G → ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 →
    ∀ L : Subgroup G, IsComponent L → L.Normal → ¬ L ≤ Subgroup.centralizer {c} →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      TypeEps148 (K ⧸ CFSG.pCore 2 K) →
      Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G) → False

section Certificates

@[expose] def Item4_29Eps : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → aschbacherSolvableCore 3 G = ⊥ →
    partTwoE G = partTwoF G → ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 →
    ∀ L : Subgroup G, IsComponent L → L.Normal →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      TypeEps148 (K ⧸ CFSG.pCore 2 K) →
      Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G) →
      K' = L ∨
      (Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ Nonempty (L ≃* alternatingGroup (Fin 10))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi K 2 n ∧ Sec4.IsoLThreePi L 2 (3 * n) ∧
        KFacts.InducesStdKind L c .field) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi K 2 n ∧
        Blueprint.ChevalleyExceptionalModel L .trialityD4 2 n ∧
        KFacts.InducesStdKind L c .graphField)

end Certificates

namespace Res148

theorem eq_of_isComponent_of_le_centralizer {G : Type*} [Group G] {L : Subgroup G} {c : G}
    (hL : IsComponent L) (hLc : L ≤ Subgroup.centralizer {c})
    (K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)) (hK : IsComponent K) :
    K.map (L ⊓ Subgroup.centralizer {c}).subtype = L := by
  have hML : L ⊓ Subgroup.centralizer {c} ≤ L := inf_le_left
  have hLM : L ≤ L ⊓ Subgroup.centralizer {c} := le_inf le_rfl hLc
  have hK'M : K.map (L ⊓ Subgroup.centralizer {c}).subtype ≤ L ⊓ Subgroup.centralizer {c} :=
    Subgroup.map_subtype_le K
  have eK : ↥K ≃* ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) :=
    K.equivMapOfInjective _ (Subgroup.subtype_injective _)
  have hK'q : IsQuasisimple ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'1 : Nontrivial ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) := by
    have : Nontrivial (↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) ⧸
        Subgroup.center ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype)) :=
      hK'q.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype))).nontrivial
  have hsub : ((K.map (L ⊓ Subgroup.centralizer {c}).subtype).subgroupOf L).IsSubnormal := by
    have hsurj : Function.Surjective (Subgroup.inclusion hML) := by
      intro x
      exact ⟨⟨x, hLM x.2⟩, rfl⟩
    have h := hK.2.map hsurj
    have heq : K.map (Subgroup.inclusion hML) =
        (K.map (L ⊓ Subgroup.centralizer {c}).subtype).subgroupOf L := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y, hy, Subtype.ext hyx⟩
    rwa [heq] at h
  exact Main148.eq_of_le_of_isSubnormal_of_isQuasisimple (hK'M.trans hML) hL.1 hK'q.1 hK'1 hsub

end Res148

open Res148

section Certificates

theorem item4_29Eps_of_outer (h : Item4_29EpsOuter) : Item4_29Eps := by
  intro G _ _ hG hθ hE A hA c hc hc1 L hL hLn K hK K' hK' htype hcent
  by_cases hLc : L ≤ Subgroup.centralizer {c}
  · left
    rw [hK']
    exact eq_of_isComponent_of_le_centralizer hL hLc K hK
  · exact (h G hG hθ hE A hA c hc hc1 L hL hLn hLc K hK K' hK' htype hcent).elim

end Certificates

namespace Res148

variable {G : Type} [Group G] [Finite G]

theorem item4_29Eps_of_le
    (h429 : Item4_29Eps)
    {Γ : Type} [Group Γ] [Finite Γ] (C : Subgroup Γ) (hC4 : SectionFourHyp ↥C)
    (hCθ : aschbacherSolvableCore 3 ↥C = ⊥) (hCE : partTwoE ↥C = partTwoF ↥C)
    {A L K : Subgroup Γ} {c : Γ} (hAC : A ≤ C) (hLC : L ≤ C) (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hLq : IsQuasisimple ↥L) (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {c}) (hKs : IsSimpleGroup ↥K)
    (hKnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (htype : TypeEps148 ↥K)
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
  have hO2 : CFSG.pCore 2 ↥K₀ = ⊥ := Main148.pCore_two_eq_bot_of_isSimpleGroup hK₀s hK₀nc
  let eQ : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).trans eK
  have htype' : TypeEps148 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    obtain ⟨p, f, hp, hp3, hf, ⟨hq, ⟨φ⟩⟩ | ⟨hq, hq2, ⟨φ⟩⟩⟩ := htype
    · exact ⟨p, f, hp, hp3, hf, Or.inl ⟨hq, ⟨eQ.trans φ⟩⟩⟩
    · exact ⟨p, f, hp, hp3, hf, Or.inr ⟨hq, hq2, ⟨eQ.trans φ⟩⟩⟩
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
  rcases h429 ↥C hC4 hCθ hCE A' hA' c' hc'A hc'1 L' hL' hL'n K₀ hK₀ K' hK'eq htype' hcent' with
    h1 | ⟨⟨φ⟩, ⟨ψ⟩⟩ | ⟨n, hn, hK2, hL2, hind⟩ | ⟨n, hn, hK2, hLD, hind⟩
  · left
    have h' := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left hKC, inf_of_le_left hLC] at h'
  · exact Or.inr (Or.inl ⟨⟨eK.symm.trans φ⟩, ⟨eL.symm.trans ψ⟩⟩)
  · have hind' := Sec13.inducesStdKind_sub C L' hind
    rw [Subgroup.map_subgroupOf_eq_of_le hLC] at hind'
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, Main148.isoLThreePi_congr eK hK2,
      Main148.isoLThreePi_congr eL hL2, hind'⟩))
  · have hind' := Sec13.inducesStdKind_sub C L' hind
    rw [Subgroup.map_subgroupOf_eq_of_le hLC] at hind'
    exact Or.inr (Or.inr (Or.inr ⟨n, hn, Main148.isoLThreePi_congr eK hK2,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL.symm hLD, hind'⟩))

end Res148

section Certificates

theorem step148Lift429Eps_of_item4_29Eps (h429 : Item4_29Eps) (h41 : Sec4.Item4_1LargePrime) :
    Step148Lift429Eps := by
  intro G _ _ A c L h Y hY hs e he he1 K hK hAK hsec hE J hJ hKJ hAJ
  let := ker148_normal hY.2
  have hT : Hyp429In148 := hyp429In148_of h41
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hKYe : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := hKJ.trans hJM
  have hKe : K ≤ Subgroup.centralizer {e} := hKYe.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  obtain ⟨p, f, hp, hp3, hf, hcase⟩ := hE
  obtain ⟨hKαs, hKαnc, h3K⟩ := Main148.isSimpleGroup_of_eps hKαp hf hcase
  have htype : TypeEps148 ↥(img148 A Y K) := ⟨p, f, hp, hp3, hf, hcase⟩
  have h3J : 3 ∣ Nat.card J := (h3K.trans (Main148.card_img148_dvd hKM)).trans
    (Subgroup.card_dvd_of_le hKJ)
  obtain ⟨hJq, hJθ⟩ := Main148.img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hT G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact Main148.aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hAC : img148 A Y A ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_right
  have hLC : img148 A Y J ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_left
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hcent := img148_inf_centralizer_eq (A := A) (Y := Y) (J := K) hKM he hKe hsec rfl
  have hCJ := Main148.img148_inf_centralizer_alpha148 hY.2 hJM hAJ he (hA3 e he)
  have hKL : img148 A Y K ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} := by
    rw [hCJ]
    exact img148_mono (le_inf hKJ hKe)
  have hKsubJ : (K.subgroupOf (J ⊓ Subgroup.centralizer {e})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hK).2.2.1
    have hle : J ⊓ Subgroup.centralizer {e} ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle)
    have heq : (K.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set G))).comap
        (Subgroup.inclusion hle) = K.subgroupOf (J ⊓ Subgroup.centralizer {e}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hKsub : ((img148 A Y K).subgroupOf
      (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he})).IsSubnormal := by
    rw [hCJ]
    exact Main148.isSubnormal_img148 (le_inf hKJ hKe) (inf_le_left.trans hJM) hKsubJ
  rcases item4_29Eps_of_le h429 (img148 A Y (J ⊔ A)) hC4 hCθ hCE hAC hLC (img148_isE27 hA)
      (alpha148_mem_img148 he) (Main148.alpha148_ne_one he he1 (hA3 e he)) hJq hLn hKL hKαs
      hKαnc hKsub htype hcent.symm with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

theorem step148Lift429_of_item4_29EpsOuter
    (h429 : Sec4.Item4_29)
    (h41 : Sec4.Item4_1LargePrime) (h : Item4_29EpsOuter) : Step148Lift429 :=
  step148Lift429_of_item4_1 h429 h41 (step148Lift429Eps_of_item4_29Eps (item4_29Eps_of_outer h) h41)

end Certificates

end CFSG.RankThree.PartTwo.Sec14
