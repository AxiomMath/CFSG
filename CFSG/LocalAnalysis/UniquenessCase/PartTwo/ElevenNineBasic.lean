module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.GroupTheory.SylowNormalElements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem hyp11_ctilde (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) ∧
      pCoreOf 2 D.M ≤ F11.CTilde D.M V₀ V ∧ F11.CTilde D.M V₀ V ≤ D.M := by
  obtain ⟨hV, -, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  exact ⟨ElevenFourteen.le_normalizer_ctilde hV.2.2.1 hMV₀, uc22p22qh_pCore_le_ctilde D hH,
    uc22p22q_ctilde_le⟩

theorem gamma_le_of_stronglyEmbedded (D : Data G) {p : ℕ} (hp : p.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {X : Subgroup G} (hXM : X ≤ D.M)
    (hX : IsPGroup p X) : rankThreeGamma 1 p X ≤ D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine sSup_le ?_
  rintro N ⟨Q, hQX, hQ1, rfl⟩
  have hQ : Q ≠ ⊥ := by
    rintro rfl
    obtain ⟨E, hE, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊥ : Subgroup G)
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    have h0 : CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
      by_contra hne
      have := Nat.one_lt_pow hne hp.one_lt
      omega
    omega
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le hsp hQ (hX.to_le hQX)
    (hQX.trans hXM)

theorem exists_sylow_normalizer {r : ℕ} (hr : r.Prime) {M Y P : Subgroup G} (hYM : Y ≤ M)
    (hYn : M ≤ normalizer (Y : Set G)) (hP : CFSG.ABGLocalTools.IsSylowOf r P Y) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R M ∧ P ≤ R ∧ R ≤ normalizer (P : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hPM : P ≤ M := hP.le.trans hYM
  obtain ⟨R, hR, hPR⟩ : ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R M ∧ P ≤ R := by
    have hP' : IsPGroup r (P.subgroupOf M) := hP.isPGroup.comap_subtype
    obtain ⟨S, hS⟩ := hP'.exists_le_sylow
    refine ⟨(S : Subgroup M).map M.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
    exact ⟨⟨x, hPM hx⟩, hS (show (⟨x, hPM hx⟩ : M) ∈ P.subgroupOf M from hx), rfl⟩
  refine ⟨R, hR, hPR, ?_⟩
  have h1 : R ⊓ Y = P := hP.eq_of_le (le_inf hPR hP.le) inf_le_right hR.isPGroup.to_inf_left
  have h2 := CFSG.GroupTheory.isSylowOf_le_normalizer_inf hYM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hYn) hR
  have h2' : R ≤ normalizer ((R ⊓ Y : Subgroup G) : Set G) := h2
  rwa [h1] at h2'

theorem permutes_of_le_sup_pCore {M T Y P : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hYM : Y ≤ M) (hYn : M ≤ normalizer (Y : Set G)) (hPY : P ≤ Y)
    (hYP : Y ≤ P ⊔ pCoreOf 2 M) : Permutes P T := by
  have hPM : P ≤ M := hPY.trans hYM
  have hTM : T ≤ M := hT.le
  have hOn : M ≤ normalizer (pCoreOf 2 M : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro n
    refine ⟨fun hn => uc22p21c_conj_mem_pCoreOf_self hk hn, fun hn => ?_⟩
    have := uc22p21c_conj_mem_pCoreOf_self (M.inv_mem hk) hn
    simpa [mul_assoc] using this
  have hOT : pCoreOf 2 M ≤ T :=
    uc22p22na_le_sylow_of_normal hT (uc22p21c_pCoreOf_le M) hOn (uc22p21c_isPGroup_pCoreOf M)
  have hmul : ((P ⊔ pCoreOf 2 M : Subgroup G) : Set G) = (P : Set G) * (pCoreOf 2 M : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hPM.trans hOn)
  have hdec : ∀ y ∈ Y, ∃ p' ∈ P, ∃ o ∈ pCoreOf 2 M, y = p' * o := by
    intro y hy
    have := hYP hy
    rw [← SetLike.mem_coe, hmul] at this
    obtain ⟨p', hp', o, ho, rfl⟩ := this
    exact ⟨p', hp', o, ho, rfl⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, t, ht, rfl⟩
    have hy : t⁻¹ * p * t ∈ Y := by
      have := (mem_normalizer_iff.1 (hYn (hTM (T.inv_mem ht))) p).1 (hPY hp)
      simpa using this
    obtain ⟨p', hp', o, ho, hyo⟩ := hdec _ hy
    have ho' : p' * o * p'⁻¹ ∈ pCoreOf 2 M :=
      uc22p21c_conj_mem_pCoreOf_self (hPM hp') ho
    refine ⟨t * (p' * o * p'⁻¹), T.mul_mem ht (hOT ho'), p', hp', ?_⟩
    calc t * (p' * o * p'⁻¹) * p' = t * (p' * o) := by group
      _ = t * (t⁻¹ * p * t) := by rw [hyo]
      _ = p * t := by group
  · rintro _ ⟨t, ht, p, hp, rfl⟩
    have hy : t * p * t⁻¹ ∈ Y := by
      have := (mem_normalizer_iff.1 (hYn (hTM ht)) p).1 (hPY hp)
      simpa using this
    obtain ⟨p', hp', o, ho, hyo⟩ := hdec _ hy
    refine ⟨p', hp', o * t, T.mul_mem (hOT ho) ht, ?_⟩
    calc p' * (o * t) = (p' * o) * t := by group
      _ = (t * p * t⁻¹) * t := by rw [hyo]
      _ = t * p := by group

theorem le_centralizer_of_perfect_of_sub {L V₀ V : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hV₀ : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) (hLV₀ : L ≤ centralizer (V₀ : Set G))
    (hLV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ * v⁻¹ ∈ V₀) : L ≤ centralizer (V : Set G) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcomm : ∀ a b : ↥L, ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) =
      ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := fun a b =>
    hV₀ _ (hLV _ a.2 v hv) _ (hLV _ b.2 v hv)
  let f : ↥L →* G := MonoidHom.mk' (fun a => (a : G) * v * (a : G)⁻¹ * v⁻¹) fun a b => by
    have h1 : (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹ =
        (b : G) * v * (b : G)⁻¹ * v⁻¹ :=
      mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 (hLV₀ a.2) _ (hLV _ b.2 v hv)).symm
    calc ((a * b : ↥L) : G) * v * ((a * b : ↥L) : G)⁻¹ * v⁻¹
        = ((a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹) *
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by simp only [Subgroup.coe_mul]; group
      _ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by rw [h1]
      _ = ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) := (hcomm a b).symm
  have hrange : ⁅f.range, f.range⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_commute.2 (hcomm a b)
  have htop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hperf]
  have hf1 : f.range = ⊥ := by
    have h := congrArg (Subgroup.map f) htop
    rw [Subgroup.map_commutator, Subgroup.map_top, hrange] at h
    exact h.symm
  have h0 : f ⟨l, hl⟩ ∈ f.range := ⟨_, rfl⟩
  rw [hf1, Subgroup.mem_bot] at h0
  have h1 : l * v * l⁻¹ * v⁻¹ = 1 := h0
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem normal_iSup_conj {Γ : Type*} [Group Γ] (H : Subgroup Γ) :
    (⨆ g : Γ, H.map (MulAut.conj g).toMonoidHom).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have key : (⨆ h : Γ, H.map (MulAut.conj h).toMonoidHom) ≤
      (⨆ h : Γ, H.map (MulAut.conj h).toMonoidHom).comap (MulAut.conj g).toMonoidHom := by
    refine iSup_le fun h => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle : H.map (MulAut.conj (g * h)).toMonoidHom ≤
        ⨆ h : Γ, H.map (MulAut.conj h).toMonoidHom :=
      le_iSup (fun h : Γ => H.map (MulAut.conj h).toMonoidHom) (g * h)
    exact hle ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  exact key hn

theorem le_normalizer_of_normal_barImage11 {M V₀ V X : Subgroup G}
    [((F11.CTilde M V₀ V).subgroupOf M).Normal] (hCX : F11.CTilde M V₀ V ≤ X) (hXM : X ≤ M)
    (hN : (F11.barImage11 M V₀ V X).Normal) : M ≤ normalizer (X : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro m hm x hx
    have hxM : x ∈ M := hXM hx
    have h1 : (QuotientGroup.mk ⟨x, hxM⟩ : F11.MBar11 M V₀ V) ∈ F11.barImage11 M V₀ V X :=
      ⟨⟨x, hxM⟩, hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hN.conj_mem _ h1 (QuotientGroup.mk ⟨m, hm⟩)
    have hyeq' : (QuotientGroup.mk y : F11.MBar11 M V₀ V) =
        QuotientGroup.mk (⟨m, hm⟩ * ⟨x, hxM⟩ * ⟨m, hm⟩⁻¹ : ↥M) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hyeq
    have h2 : ((y⁻¹ * (⟨m, hm⟩ * ⟨x, hxM⟩ * ⟨m, hm⟩⁻¹ : ↥M) : ↥M) : G) ∈
        F11.CTilde M V₀ V := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hyeq')
    have h3 : m * x * m⁻¹ = (y : G) *
        ((y⁻¹ * (⟨m, hm⟩ * ⟨x, hxM⟩ * ⟨m, hm⟩⁻¹ : ↥M) : ↥M) : G) := by
      simp [mul_assoc]
    rw [h3]
    exact X.mul_mem hy (hCX h2)
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key m hm x hx, fun hx => ?_⟩
  simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hx

theorem card_le_four_or_eight_le (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    Nat.card V₀ ≤ 4 ∨ 8 ≤ Nat.card V₀ := by
  obtain ⟨-, -, -, hV₀⟩ := uc22p22q_hyp11_unpack D hH
  have hp : IsPGroup 2 ↥V₀ := by
    rcases hV₀ with rfl | ⟨hV₀, -, -⟩
    · exact IsPGroup.of_card (n := 0) (by simp)
    · exact uc22p22e_isPGroup_of_elem hV₀.2.2.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  rw [hk]
  rcases Nat.lt_or_ge k 3 with h | h
  · left
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  · right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h

theorem not_uniqueMax_of_eight_le (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V)
    (h8 : 8 ≤ Nat.card V₀) :
    ¬ UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G)) := by
  intro hU
  obtain ⟨-, -, -, hV₀⟩ := uc22p22q_hyp11_unpack D hH
  rcases hV₀ with rfl | ⟨hV₀, -, -⟩
  · simp at h8
  · exact (hH.2.2 h8).1 ⟨hV₀, hU⟩

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
