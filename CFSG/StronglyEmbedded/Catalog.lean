module

public import CFSG.Assembly.InCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
import CFSG.StronglyEmbedded.Catalog.TypeA
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.StronglyEmbedded.Catalog.Unitary
import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import Certificates.Certificate43
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.BenderSuzuki

open TauCeti _root_.CFSG.BenderSuzuki.MatrixGroups

theorem nonempty_mulEquiv_alternatingGroup_five {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 60) : Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

private theorem not_isMulCommutative_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative H := by
  rintro ⟨hc⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (e.injective (by rw [map_mul, map_mul]; exact hc.comm _ _))

theorem inCatalog_of_isSimpleBenderGroup {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (h : IsSimpleBenderGroup X) :
    Assembly.InCatalog X := by
  rcases h with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, E, hEfield, hEfinite, J, hform, hEcard, hfixed, ⟨e⟩⟩⟩
  · have := e.symm.isSimpleGroup
    have hP := not_isMulCommutative_of_mulEquiv e hnonab
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · have hcard : Nat.card X = 60 := by
        rw [Nat.card_congr e.toEquiv, lemma114_psl2Binary_card_formula 2 (by norm_num)]
        norm_num
      obtain ⟨e5⟩ := nonempty_mulEquiv_alternatingGroup_five hcard
      exact ⟨.alternating 5 le_rfl, ⟨e5⟩⟩
    · let q : PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
      have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
      have h9 : 2 ^ n ≠ 9 := fun h => by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [pow_succ] at h
        omega
      have hv : (LieTypeIndex.A 1 q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        simp only [q, PrimePower.card_def]
        generalize 2 ^ n = N at *
        omega
      exact ⟨.lie ⟨_, hv⟩, ⟨e.trans (Catalog.groupEquivPSL 1 q hv hP).symm⟩⟩
  · have hv : (LieTypeIndex.suzuki m).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simpa using hm
    exact ⟨.lie ⟨_, hv⟩, ⟨e.trans (Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩
  · let := hEfield
    let := hEfinite
    obtain ⟨u⟩ := CFSG.BenderSuzuki.projectiveSpecialUnitary_equiv_PSU3Model J n hn hform hEcard hfixed
    let e' := e.trans u
    have := e'.symm.isSimpleGroup
    have hP := not_isMulCommutative_of_mulEquiv e' hnonab
    have h4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    have hv : (LieTypeIndex.twistedA 2 ⟨2, n, Nat.prime_two, by omega⟩).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def]
      generalize 2 ^ n = N at *
      simp
      omega
    exact ⟨.lie ⟨_, hv⟩, ⟨e'.trans (Catalog.groupEquivPSU3Model (by omega) hv hP).symm⟩⟩

end CFSG.BenderSuzuki
