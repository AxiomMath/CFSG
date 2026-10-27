module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofFamily
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Statement


@[expose] def D4ThreeASL3Model : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ v ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, v ^ 3 = 1 → v ≠ 1 →
      ∃ (L : Type) (_ : Field L) (ρ : Subgroup.centralizer
          ({v} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →*
          Matrix.SpecialLinearGroup (Fin 3) L),
        Item1118Res2Proof.IsSL3Model ρ

end Statement

namespace Item1118Res2Proof

section Transport

variable {Z C : Type} [Group Z] [Group C] {L : Type} [Field L]

theorem isSL3Model_comap (e : Z ≃* C) {v : Z}
    {ρ₀ : Subgroup.centralizer ({e v} : Set C) →* Matrix.SpecialLinearGroup (Fin 3) L}
    (h : IsSL3Model ρ₀) :
    ∃ ρ : Subgroup.centralizer ({v} : Set Z) →* Matrix.SpecialLinearGroup (Fin 3) L,
      IsSL3Model ρ := by
  have hmem : ∀ x : Subgroup.centralizer ({v} : Set Z),
      (e.toMonoidHom.comp (Subgroup.centralizer ({v} : Set Z)).subtype) x ∈
        Subgroup.centralizer ({e v} : Set C) := fun x => by
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change e x * e v = e v * e x
    rw [← map_mul, ← map_mul, hx]
  set eC : Subgroup.centralizer ({v} : Set Z) →* Subgroup.centralizer ({e v} : Set C) :=
    (e.toMonoidHom.comp (Subgroup.centralizer ({v} : Set Z)).subtype).codRestrict _ hmem
    with heC
  have heCv : eC ⟨v, self_mem_centralizer v⟩ = ⟨e v, self_mem_centralizer (e v)⟩ := rfl
  have heCinj : Function.Injective eC := fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab))
  obtain ⟨hc, hne, hzp, hker⟩ := h
  refine ⟨ρ₀.comp eC, ?_, ?_, fun x hx3 hx => ?_, fun x y hx => ?_⟩
  · rw [MonoidHom.comp_apply, heCv]
    exact hc
  · rw [MonoidHom.comp_apply, heCv]
    exact hne
  · have hx3' : ∃ k : ℕ, eC x ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hx3
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp (eC x) hx3' hx)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
    rw [map_zpow]
    exact hk
  · apply heCinj
    rw [map_mul, map_mul]
    exact hker (eC x) (eC y) hx

end Transport

section D4


theorem sl3Model1118For_d4_of (hM : D4ThreeASL3Model) :
    SL3Model1118For fun X _ => ∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) := by
  intro Z _ _ hZ z v J hz3 hJ hJT hvJ hv3 hv1
  have hZ' : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) := by
    obtain ⟨X, _, ⟨q, hq, hq2, hf⟩, he⟩ := hZ
    exact ⟨X, inferInstance, ⟨q, hq, by rw [hq2]; decide, hf⟩, he⟩
  obtain ⟨K, _, _, q, σ, hK, hσ, h3, -, hz3', -, e, -, h⟩ :=
    KS11Lie4Proof.exists_d4_threeB KS11Lie6Proof.d4ThreeConj_holds
      KS11Lie6Proof.d4ThreeACent_holds KS11Lie6Proof.d4ThreeBCent_holds hZ' hz3 hJ hJT
  have hJS := h.eq hJ
  have hevS : e v ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
    have : v ∈ (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom := hJS ▸ hvJ
    exact this
  have hev3 : e v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have hev1 : e v ≠ 1 := fun h1 => hv1 (e.injective (h1.trans (map_one e).symm))
  obtain ⟨L, _, ρ₀, hρ₀⟩ := hM K q σ hK hσ h3 (e v) hevS hev3 hev1
  obtain ⟨ρ, hρ⟩ := isSL3Model_comap e hρ₀
  exact ⟨hz3', L, inferInstance, ρ, hρ⟩

end D4

end Item1118Res2Proof

section KFacts


theorem invElt1118D4Even_of (hM : D4ThreeASL3Model) : InvElt1118D4Even :=
  Item1118Res2Proof.invElt1118For_of_sl3Model (Item1118Res2Proof.sl3Model1118For_d4_of hM)

theorem comm1119D4Even_of (hM : D4ThreeASL3Model) : Comm1119D4Even :=
  Item1118Res2Proof.comm1119For_of_sl3Model (Item1118Res2Proof.sl3Model1118For_d4_of hM)

end KFacts

end CFSG.RankThree.PartTwo.Sec11
