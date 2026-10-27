module

public import CFSG.Quasithin.Vol2.Ch4Sec1Lem412
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

structure Hyp4_2_1 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  T_le : T ≤ M
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  L_le : L ≤ M
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem exists_isSylowTwoOf_le_of_sup_eq {M C I P : Subgroup G} (hIM : I ≤ M)
    (hIC : I ≤ Subgroup.normalizer (C : Set G)) (hCI : C ⊔ I = M) (hP : IsSylowTwoOf P C)
    (hPI : P ≤ I) : ∃ S, IsSylowTwoOf S M ∧ S ≤ I := by
  obtain ⟨S, hS, hPS⟩ := exists_isSylowTwoOf_ge hPI hP.2.1
  refine ⟨S, ⟨hS.1.trans hIM, hS.2.1, ?_⟩, hS.1⟩
  have hCM : C ≤ M := le_sup_left.trans hCI.le
  have h1 : C.relIndex (I ⊔ C) = C.relIndex I := relIndex_sup_eq_of_le_normalizer' hIC
  rw [sup_comm, hCI] at h1
  have h2 := Subgroup.relIndex_mul_card C M
  have h3 := Subgroup.relIndex_mul_card C I
  have h4 := Subgroup.relIndex_mul_card I M
  have h5 := Subgroup.relIndex_mul_card (I ⊓ C) C
  rw [inf_eq_left.mpr hCM] at h2
  rw [inf_eq_left.mpr hIM] at h4
  rw [inf_assoc, inf_idem] at h5
  have hpos : 0 < Nat.card ↥(C ⊓ I) := Nat.card_pos
  have hpos' : 0 < C.relIndex I := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := ↥I)).ne' h3.symm
  have hIdx : I.relIndex M = (I ⊓ C).relIndex C := by
    have e1 : I.relIndex M * (C.relIndex I * Nat.card ↥(C ⊓ I)) =
        C.relIndex I * Nat.card ↥C := by rw [h3, h4, ← h2, h1]
    have e2 : (I ⊓ C).relIndex C * Nat.card ↥(C ⊓ I) = Nat.card ↥C := by
      rw [inf_comm I C] at h5 ⊢
      exact h5
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [e2]
    refine Nat.eq_of_mul_eq_mul_left hpos' ?_
    rw [← e1]
    ring
  have hodd : ¬ 2 ∣ (I ⊓ C).relIndex C := by
    have h6 := Subgroup.relIndex_mul_relIndex P (I ⊓ C) C (le_inf hPI hP.1) inf_le_right
    intro h2d
    exact hP.2.2 (show 2 ∣ P.relIndex C from h6 ▸ Dvd.dvd.mul_left h2d _)
  have h7 := Subgroup.relIndex_mul_relIndex S I M hS.1 hIM
  intro h2d
  change 2 ∣ S.relIndex M at h2d
  rw [← h7] at h2d
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2d with h | h
  · exact hS.2.2 h
  · exact hodd (hIdx ▸ h)

namespace Hyp4_2_1

variable (h : Hyp4_2_1 G T M L)
include h

theorem perfect : ⁅L, L⁆ = L := h.maximal.1.2.1.2.1

theorem sup_le : L ⊔ T ≤ M := _root_.sup_le h.L_le h.T_le

theorem inH : InH (L ⊔ T) M := ⟨h.sup_le, pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1⟩

theorem mem_cComp (h37 : A37ForSQTK) (h39 : A39ForSQTK) : L ∈ cComp M :=
  lemma_1_2_7_one h.qtke h.simple h.nonabelian h37 h39 h.sylow h.maximal h.inH

theorem isUniqueM_sup (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    IsUniqueM (L ⊔ T) M ∧ Subgroup.normalizer (conjClosure L T : Set G) = M := by
  have hU := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow h.maximal
  have he : M = Subgroup.normalizer (conjClosure L T : Set G) :=
    hU.2 M ⟨h.maxTwoLocal, h.sup_le⟩
  exact ⟨he ▸ hU, he.symm⟩

theorem le_normalizer_conjClosure (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    M ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  (h.isUniqueM_sup h37 h38 h39).2.ge

theorem conjClosure_le : conjClosure L T ≤ M :=
  CFSG.Quasithin.conjClosure_le fun _ ht _ hl =>
    M.mul_mem (M.mul_mem (h.T_le ht) (h.L_le hl)) (M.inv_mem (h.T_le ht))

theorem oTwoUpper_conjClosure : oTwoUpper (conjClosure L T) = conjClosure L T :=
  (eq_oTwoUpper_of_perfect (perfect_conjClosure h.perfect)).symm

end Hyp4_2_1

theorem lemma_4_2_2 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp4_2_1 G T M L) : Hyp4_1_1 G T M (conjClosure L T) := by
  set Mp := conjClosure L T with hMp
  have hnorm : M ≤ Subgroup.normalizer (Mp : Set G) := h.le_normalizer_conjClosure h37 h38 h39
  have hU := (h.isUniqueM_sup h37 h38 h39).1
  refine ⟨h.simple, h.nonabelian, h.qtke, h.sylow, h.maxTwoLocal, h.T_le,
    h.oTwoUpper_conjClosure, h.conjClosure_le, hnorm, fun I hIM hI hCI => ?_⟩
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  have hTsyl : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (Mp : Set G)) := by
    rw [inf_eq_left.mpr hnorm]
    exact isSylowTwoOf_of_le h.sylow h.T_le
  have hTC : IsSylowTwoOf (T ⊓ C) C := isSylowTwoOf_inf_centralizerSection hTsyl
  obtain ⟨S, hS, hSI⟩ := exists_isSylowTwoOf_le_of_sup_eq hIM
    (hIM.trans (le_normalizer_centralizerSection' hnorm)) hCI hTC (le_sup_right.trans hI)
  obtain ⟨m, hm, hmS⟩ := exists_conj_of_isSylowTwoOf (isSylowTwoOf_of_le h.sylow h.T_le) hS
  have hU' : IsUniqueM (I.map (MulAut.conj m⁻¹).toMonoidHom) M := by
    refine isUniqueM_mono hU (_root_.sup_le ?_ ?_)
      ((map_conj_mono hIM m⁻¹).trans
        (map_conj_le_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hm))))
    · intro l hl
      rw [mem_map_conj_iff, inv_inv]
      have hlMp : m * l * m⁻¹ ∈ Mp :=
        (Subgroup.mem_normalizer_iff.mp (hnorm hm) l).mp (le_conjClosure L T hl)
      exact (le_sup_left.trans hI) hlMp
    · intro t ht
      rw [mem_map_conj_iff, inv_inv]
      exact hSI ((hmS _).mpr (by simpa [mul_assoc] using ht))
  have := isUniqueM_map_conj hU' hm
  rwa [map_conj_map_conj_inv] at this

end CFSG.Quasithin.H13.Ch4
