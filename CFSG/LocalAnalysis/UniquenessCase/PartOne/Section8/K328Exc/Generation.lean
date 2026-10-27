module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ResidualHandback
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Seitz.TrialityEven.Assembly
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4ThreeProved
public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
public import CFSG.LocalAnalysis.ComponentClassification.ONanTauCetiPartitionEven
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc

open CFSG.Open CFSG.Blueprint CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
  TauCeti

@[expose] def K328ExcLieModel (K : Type) [Group K] : Prop :=
  LieModel K .G2 0 2 2 ∨ LieModel K .trialityD4 0 2 2 ∨ LieModel K .G2 0 2 3 ∨
    LieModel K .trialityD4 0 2 3 ∨ LieModel K .twistedF4 0 2 3

@[expose] def IsK328ExcIndex (d : LieTypeIndex) : Prop :=
  (∃ q : PrimePower, d = .G2 q ∧ q.p = 2 ∧ (q.exponent = 2 ∨ q.exponent = 3)) ∨
  (∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2 ∧ (q.exponent = 2 ∨ q.exponent = 3)) ∨
  d = .reeF4 1

theorem exists_ne_comm_of_simple_of_card_nine {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (E : Subgroup K) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    ∃ a b : K, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [this, Subgroup.card_bot] at hc
    norm_num at hc
  have hno : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hab g n, mul_inv_cancel_right]; exact hn⟩
  have htop : Subgroup.zpowers x = ⊤ := by
    rcases hno.eq_bot_or_eq_top with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hx1
    · exact h
  have hord : orderOf x = 3 := orderOf_eq_prime (hE.2 x hxE) hx1
  have hcardK : Nat.card K = 3 := by
    rw [← Subgroup.card_top (G := K), ← htop, Nat.card_zpowers, hord]
  have := Subgroup.card_le_card_group E
  omega

theorem exists_index_of_k328ExcLieModel
    {K : Type} [Group K] (hK : K328ExcLieModel K) :
    ∃ d : ValidLieTypeIndex, IsK328ExcIndex d.1 ∧ IsSimpleGroup (Cat d) ∧
      Nonempty (K ≃* Cat d) := by
  have chev : ∀ {t : StatedLieTag} {f : ℕ}, t ∈ chevalleyExceptionalTags →
      LieModel K t 0 2 f → ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t 2 f ∧
        Nonempty (K ≃* d.Group) := fun ht h =>
    CFSG.TauCetiBridge.exists_index_of_chevalley_even ht (h.chevalleyExceptionalModel ht)
  rcases hK with h | h | h | h | h
  · obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := chev (by decide) h
    cases d <;> simp only [CFSG.Models.NamesTag] at hn
    case G2 q =>
      exact ⟨⟨_, hv⟩, Or.inl ⟨q, rfl, hn.1, Or.inl hn.2⟩,
        (finite_isSimpleGroup_cat_G2 hv).2, ⟨e⟩⟩
  · obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := chev (by decide) h
    cases d <;> simp only [CFSG.Models.NamesTag] at hn
    case trialityD4 q =>
      exact ⟨⟨_, hv⟩, Or.inr (Or.inl ⟨q, rfl, hn.1, Or.inl hn.2⟩),
        (finite_isSimpleGroup_cat_trialityD4 hv).2, ⟨e⟩⟩
  · obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := chev (by decide) h
    cases d <;> simp only [CFSG.Models.NamesTag] at hn
    case G2 q =>
      exact ⟨⟨_, hv⟩, Or.inl ⟨q, rfl, hn.1, Or.inr hn.2⟩,
        (finite_isSimpleGroup_cat_G2 hv).2, ⟨e⟩⟩
  · obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := chev (by decide) h
    cases d <;> simp only [CFSG.Models.NamesTag] at hn
    case trialityD4 q =>
      exact ⟨⟨_, hv⟩, Or.inr (Or.inl ⟨q, rfl, hn.1, Or.inr hn.2⟩),
        (finite_isSimpleGroup_cat_trialityD4 hv).2, ⟨e⟩⟩
  · obtain ⟨-, hR⟩ := h.reeTitsModel (by decide)
    obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := CFSG.TauCetiBridge.exists_index_of_reeTits_even (by decide) hR
    cases d <;> simp only [CFSG.Models.NamesTag] at hn
    case reeF4 m =>
      obtain rfl : m = 1 := by omega
      exact ⟨⟨_, hv⟩, Or.inr (Or.inr rfl), (finite_isSimpleGroup_cat_reeF4 hv).2, ⟨e⟩⟩

theorem planeGen_of_isK328ExcIndex
    (d : ValidLieTypeIndex) (hd : IsK328ExcIndex d.1)
    (E : Subgroup (MulAut (Cat d))) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hin : InnerPlane d 3 E) : PlaneGen E := by
  obtain ⟨d, hv⟩ := d
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  rcases hd with ⟨q, rfl, hp2, hexp⟩ | ⟨q, rfl, hp2, hexp⟩ | rfl
  · have hpd : (3 : ℕ) ≠ (LieTypeIndex.G2 q).characteristic := by simp [hp2]
    have hex : ¬ IsD2SeitzException 3 (LieTypeIndex.G2 q) := by simp [IsD2SeitzException]
    have hncl : ¬ IsClassicalIndex (LieTypeIndex.G2 q) := by simp [IsClassicalIndex]
    by_cases hN : NormalizesRSubgroup ⟨_, hv⟩ E
    · exact seitzExcParabolic ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc ⟨hin, hncl, hN⟩
    have hrank : RankLE2 3 (Cat ⟨LieTypeIndex.G2 q, hv⟩) :=
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv
        (by rw [hp2]; norm_num)
    have hcard : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def q, hp2]
    rcases hexp with he | he
    · refine CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.seitzExcAnisotropicG2ThreeMinus_proved
        ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc ⟨hin, ⟨q, rfl⟩, ⟨rfl, q, rfl, ?_⟩, hrank, hN⟩
      rw [hcard, he]; norm_num
    · refine CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.seitzExcAnisotropicG2ThreePlus_proved
        ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc ⟨⟨hin, hncl, hrank, hN⟩, rfl, q, rfl, ?_⟩
      rw [hcard, he]; norm_num
  · have hpd : (3 : ℕ) ≠ (LieTypeIndex.trialityD4 q).characteristic := by simp [hp2]
    have hex : ¬ IsD2SeitzException 3 (LieTypeIndex.trialityD4 q) := by
      simp [IsD2SeitzException]
    have hncl : ¬ IsClassicalIndex (LieTypeIndex.trialityD4 q) := by simp [IsClassicalIndex]
    by_cases hN : NormalizesRSubgroup ⟨_, hv⟩ E
    · exact seitzExcParabolic ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc ⟨hin, hncl, hN⟩
    have hrank : RankLE2 3 (Cat ⟨LieTypeIndex.trialityD4 q, hv⟩) :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv
        (by rw [hp2]; norm_num)
    exact CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThreeGe_proved
      ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc
      ⟨hin, ⟨q, rfl⟩, ⟨rfl, q, rfl, hp2, by omega⟩, hrank, hN⟩
  · have hpd : (3 : ℕ) ≠ (LieTypeIndex.reeF4 1).characteristic := by simp
    have hex : ¬ IsD2SeitzException 3 (LieTypeIndex.reeF4 1) := by simp [IsD2SeitzException]
    have hncl : ¬ IsClassicalIndex (LieTypeIndex.reeF4 1) := by simp [IsClassicalIndex]
    by_cases hN : NormalizesRSubgroup ⟨_, hv⟩ E
    · exact seitzExcParabolic ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc ⟨hin, hncl, hN⟩
    have hrank : RankLE2 3 (Cat ⟨LieTypeIndex.reeF4 1, hv⟩) :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv
    exact seitzExcAnisotropicReeF4Three_holds ⟨_, hv⟩ 3 h3 h32 hpd hex E hE hc
      ⟨hin, ⟨1, rfl⟩, rfl, hrank, hN⟩

theorem closure_commute_eq_top
    {K : Type} [Group K] [Finite K] (hK : K328ExcLieModel K)
    (E : Subgroup K) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  obtain ⟨d, hd, hsd, ⟨e⟩⟩ := exists_index_of_k328ExcLieModel hK
  have hs : IsSimpleGroup K := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple hs (exists_ne_comm_of_simple_of_card_nine hs E hE hc)
  let ψ : K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hψel : IsElemAbelian 3 (E.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE ψ
  have hgen : PlaneGen (E.map ψ) :=
    planeGen_of_isK328ExcIndex d hd (E.map ψ) hψel
      (by rw [Subgroup.card_map_of_injective hψ, hc]; norm_num) (InnerPlane.map_congr_conj e E 3)
  have hle : (⊤ : Subgroup (Cat d)) ≤
      (Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
    rw [← hgen, planeClosure, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, Subgroup.subset_closure ⟨x, hx, hx1, ?_⟩, by simp⟩
    have h1 : ψ x c = e (x * e.symm c * x⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1] at hεc
    have h2 : x * e.symm c * x⁻¹ = e.symm c := by
      apply e.injective
      rw [hεc]
      simp
    calc e.symm c * x = x * e.symm c * x⁻¹ * x := by rw [h2]
      _ = x * e.symm c := by group
  rw [eq_top_iff]
  intro k _
  obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
  rw [show k = k' from e.injective hkk.symm]
  exact hk'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc
