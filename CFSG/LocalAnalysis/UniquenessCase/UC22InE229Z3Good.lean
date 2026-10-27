module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZR1
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3ConclusionPlus Gls3StronglyThreeEmbeddedPlus)
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem mem_smul_sylow_iff {p : ℕ} {X : Type*} [Group X] (P : Sylow p X) (g x : X) :
    x ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (P : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h : g⁻¹ * ((MulAut.conj g) • s) * g = s := by
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rwa [h]
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply]
    group

theorem forall_sylow_of_self_centralizing {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (P : Sylow p X) (hc : Nat.card (P : Subgroup X) = p ^ 2)
    (hC : centralizer ((P : Subgroup X) : Set X) ≤ P) (R : Sylow p X) :
    Nat.card (R : Subgroup X) = p ^ 2 ∧ centralizer ((R : Subgroup X) : Set X) ≤ R := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P R
  refine ⟨?_, fun c hc' => ?_⟩
  · rw [Sylow.card_eq_multiplicity (g • P), ← Sylow.card_eq_multiplicity P]
    exact hc
  · rw [mem_smul_sylow_iff]
    refine hC (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    have h := Subgroup.mem_centralizer_iff.1 hc' (g * x * g⁻¹)
      ((mem_smul_sylow_iff P g _).2 (by rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]; exact hx))
    calc x * (g⁻¹ * c * g) = g⁻¹ * (g * x * g⁻¹ * c) * g := by group
      _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * c * g * x := by group

theorem dihedral_nine_no_commute :
    ∀ g h : DihedralGroup 9, g ^ 2 = 1 → g ≠ 1 → h ^ 3 = 1 → h ≠ 1 → g * h = h * g → False := by
  decide

theorem false_of_commute_of_dihedral_nine {X : Type*} [Group X] {Γ : Subgroup X}
    (φ : ↥Γ ≃* DihedralGroup 9) {g h : X} (hg : g ∈ Γ) (hh : h ∈ Γ) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) (hgh : g * h = h * g) : False := by
  refine dihedral_nine_no_commute (φ ⟨g, hg⟩) (φ ⟨h, hh⟩) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, EmbeddingLike.map_eq_one_iff]
    exact Subtype.ext (by simpa using hg2)
  · rw [Ne, EmbeddingLike.map_eq_one_iff]
    exact fun h' => hg1 (by simpa using congrArg Subtype.val h')
  · rw [← map_pow, EmbeddingLike.map_eq_one_iff]
    exact Subtype.ext (by simpa using hh3)
  · rw [Ne, EmbeddingLike.map_eq_one_iff]
    exact fun h' => hh1 (by simpa using congrArg Subtype.val h')
  · rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (by simpa using hgh))

theorem goodZ3_of_l28Row {X : Type} [Group X] [Finite X] {N K Γ : Subgroup X} [K.Normal]
    (P : Sylow 3 X) (hidx : K.index = 3) (hNK : N ⊓ K = Γ)
    (hD : Nonempty (↥Γ ≃* DihedralGroup 9)) (hP27 : Nat.card (P : Subgroup X) = 27)
    (hPnc : ¬ ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) :
    InvolutionCentralizerHasPElementOutside 3 N ∧ AbelianPSubgroupLeFStar 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hD
  refine ⟨fun A hAN hA hAc t htN ht2 htA => ?_, fun B hBN hB hBab hBc => ?_⟩
  · exfalso
    have htt : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have htK : t ∈ K := by
      have h := K.pow_index_mem t
      rwa [hidx, show t ^ 3 = t by rw [pow_succ, htt, one_mul]] at h
    have hrel : (K.subgroupOf A).index ∣ 3 := by
      have h := Subgroup.relIndex_dvd_index_of_normal (H := K) (K := A)
      rw [hidx] at h
      exact h
    have hne : K.subgroupOf A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.index_bot, hAc] at hrel
      norm_num at hrel
    obtain ⟨x, hxK, hx1⟩ := (Subgroup.bot_or_exists_ne_one (K.subgroupOf A)).resolve_left hne
    have hxK' : (x : X) ∈ K := Subgroup.mem_subgroupOf.1 hxK
    have hx1' : (x : X) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have htΓ : t ∈ Γ := by rw [← hNK]; exact ⟨htN, htK⟩
    have hxΓ : (x : X) ∈ Γ := by rw [← hNK]; exact ⟨hAN x.2, hxK'⟩
    exact false_of_commute_of_dihedral_nine φ htΓ hxΓ htt ht1 (hA.2 _ x.2) hx1'
      (htA _ x.2).symm
  · exfalso
    obtain ⟨R, hBR⟩ := hB.exists_le_sylow
    have hR27 : Nat.card (R : Subgroup X) = 27 := by
      rw [Sylow.card_eq_multiplicity R, ← Sylow.card_eq_multiplicity P]
      exact hP27
    have hBR' : B = R :=
      Subgroup.eq_of_le_of_card_ge hBR (by rw [hR27]; simpa using hBc)
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P R
    refine hPnc fun a ha b hb => ?_
    have h1 : g * a * g⁻¹ ∈ B := by
      rw [hBR']
      exact (mem_smul_sylow_iff P g _).2
        (by rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]; exact ha)
    have h2 : g * b * g⁻¹ ∈ B := by
      rw [hBR']
      exact (mem_smul_sylow_iff P g _).2
        (by rw [show g⁻¹ * (g * b * g⁻¹) * g = b by group]; exact hb)
    have h := hBab _ h1 _ h2
    calc a * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [h]
      _ = b * a := by group

theorem goodZ3_of_m11Row {X : Type} [Group X] [Finite X] {N S : Subgroup X} (P : Sylow 3 X)
    (hE : IsElemAbelian 3 (P : Subgroup X)) (hP9 : Nat.card (P : Subgroup X) = 9)
    (hsup : (P : Subgroup X) ⊔ S = normalizer ((P : Subgroup X) : Set X))
    (hSC : S ⊓ centralizer ((P : Subgroup X) : Set X) = ⊥) :
    InvolutionCentralizerHasPElementOutside 3 N ∧ AbelianPSubgroupLeFStar 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsMulCommutative ↥(P : Subgroup X) := hE.1
  have hPC : (P : Subgroup X) ≤ centralizer ((P : Subgroup X) : Set X) :=
    Subgroup.le_centralizer (P : Subgroup X)
  have hSn : S ≤ normalizer ((P : Subgroup X) : Set X) := le_sup_right.trans hsup.le
  have hCP : centralizer ((P : Subgroup X) : Set X) ≤ P := by
    intro c hc
    have hcΓ : c ∈ (P : Subgroup X) ⊔ S := by
      rw [hsup]
      exact Subgroup.centralizer_le_normalizer _ hc
    obtain ⟨x, hx, s, hs, rfl⟩ := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hSn).1 hcΓ
    have hsC : x⁻¹ * (x * s) ∈ centralizer ((P : Subgroup X) : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPC hx)) hc
    rw [inv_mul_cancel_left] at hsC
    have hs1 : s ∈ S ⊓ centralizer ((P : Subgroup X) : Set X) := ⟨hs, hsC⟩
    rw [hSC, Subgroup.mem_bot] at hs1
    rwa [hs1, mul_one]
  exact goodZ_of_sylow (by norm_num)
    (forall_sylow_of_self_centralizing P (by rw [hP9]; norm_num) hCP) N

theorem goodZ3_of_rows {p : ℕ} (hp3 : p = 3) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (P : Sylow p X)
    (hrows : Gls3ConclusionPlus X (CFSG.generalizedFitting X) (P : Subgroup X))
    (hNK : N ⊓ CFSG.generalizedFitting X = CFSG.generalizedFitting X ⊓
      normalizer (((P : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X))
    (hNoRee : ∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting X) (.reeG2 m)) :
    AbelianPSubgroupLeFStar p N ∧
      (InvolutionCentralizerHasPElementOutside p N ∨
        IsoLie ↥(CFSG.generalizedFitting X) (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hrows⟩ := hrows
  obtain ⟨-, -, hKn, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  haveI := hKn
  have hgood : InvolutionCentralizerHasPElementOutside 3 N ∧ AbelianPSubgroupLeFStar 3 N →
      AbelianPSubgroupLeFStar 3 N ∧ (InvolutionCentralizerHasPElementOutside 3 N ∨
        IsoLie ↥(CFSG.generalizedFitting X) (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) :=
    fun h => ⟨h.2, Or.inl h.1⟩
  rcases hrows with ⟨q, hq3, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨q, hq3, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨m, hI, -⟩ |
      ⟨-, hidx, -, -, hΓ, hD, hP27, hPnc⟩ | ⟨⟨φ, -⟩, -⟩ | ⟨hI, ⟨k, hk⟩, -⟩ |
      ⟨-, hK, hE, hQ9, hΓ, S, -, hsup, -, -, hSC, -⟩
  ·
    obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
      (show IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ from ⟨q, rfl, hq3, rfl⟩)
    exact hgood (goodZ_psl2GF (by norm_num) q.exponent_pos hO hN (e.trans f))
  ·
    exact hgood (goodZ_unitary (p := 3) (d := ⟨.twistedA 2 q, hv⟩) (by norm_num)
      ⟨q, hq3, rfl⟩ hO hN e)
  · exact absurd hI (hNoRee m)
  ·
    exact hgood (goodZ3_of_l28Row P hidx (hNK.trans hΓ.symm) hD hP27 hPnc)
  ·
    have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 2) = 9 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
      norm_num
    obtain ⟨f⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
    exact hgood (goodZ_psl2GF (p := 3) (n := 2) (by norm_num) (by norm_num) hO hN
      (φ.trans f.symm))
  ·
    refine ⟨abelianPSubgroupLeFStar_of_forall_mem fun z _ hz => ?_,
      (Classical.em (InvolutionCentralizerHasPElementOutside 3 N)).imp id fun _ => hI⟩
    obtain ⟨a, ha⟩ := hz.exists_card_eq
    have hord : orderOf z = 3 ^ a := by rw [← Nat.card_zpowers, ha]
    have hcop : Nat.Coprime (2 ^ k) (orderOf z) := by
      rw [hord]
      exact Nat.Coprime.pow k a (by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have h := (CFSG.generalizedFitting X).pow_index_mem z
    rw [hk] at h
    rw [← hm]
    exact Subgroup.pow_mem _ h m
  ·
    rw [hK] at hE hQ9 hSC hsup hΓ
    simp only [inf_top_eq, top_inf_eq] at hE hQ9 hSC hsup hΓ
    exact hgood (goodZ3_of_m11Row P hE hQ9 (hsup.trans hΓ) hSC)

namespace Sec7Core4

variable {G : Type} [Group G] [Finite G]

theorem goodZ3_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Config k H) :
    AbelianPSubgroupLeFStar k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∧
      (InvolutionCentralizerHasPElementOutside k.p
          (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∨
        IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
          (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow k.p ↥(H ⊓ k.M)) := inferInstance
  obtain ⟨P', -, hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH
    (P := (P₀ : Subgroup ↥(H ⊓ k.M)).map (H ⊓ k.M).subtype) ⟨P₀, rfl⟩
  obtain ⟨hrows, hNoRee, -⟩ := k.rows3_of_config hG3 hRee hp3 hH P'
  exact goodZ3_of_rows hp3 (CFSG.pPrimeCore_quotient_eq_bot k.prime)
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) P' hrows
    (k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P' hP'N).1 hNoRee

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
