module

public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec11.Statements
public import CFSG.RankThree.PartTwo.Sec12.Item124
public import CFSG.RankThree.PartTwo.Sec11.Wreath
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.RankThree.PartTwo.Sec8.Transfer
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_sup_of_subset_mul {P M N : Subgroup G}
    (hMP : M ≤ Subgroup.normalizer (P : Set G)) (hN : (N : Set G) ⊆ (P : Set G) * (M : Set G)) :
    ⁅P, N⁆ ≤ ⁅P, P⁆ ⊔ ⁅M, P⁆ := by
  rw [Subgroup.commutator_le]
  intro q hq y hy
  obtain ⟨p, hp, m, hm, rfl⟩ := hN hy
  have hw : q * m * q⁻¹ * m⁻¹ ∈ P := by
    have : m * q⁻¹ * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hMP hm) q⁻¹).mp (P.inv_mem hq)
    have h' := P.mul_mem hq this
    simpa [mul_assoc] using h'
  have hwM : q * m * q⁻¹ * m⁻¹ ∈ ⁅M, P⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hq hm
  have e : ⁅q, p * m⁆ = ⁅q, p⁆ * (⁅p, q * m * q⁻¹ * m⁻¹⁆ * (q * m * q⁻¹ * m⁻¹)) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq hp))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hp hw))
      (Subgroup.mem_sup_right hwM))

theorem commutator_le_of_le_normalizer {P M : Subgroup G}
    (hMP : M ≤ Subgroup.normalizer (P : Set G)) : ⁅M, P⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro m hm q hq
  have : m * q * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hMP hm) q).mp hq
  simp only [commutatorElement_def]
  exact P.mul_mem this (P.inv_mem hq)

theorem rank3II_11_14_of [Finite G] (P : Sylow 3 G) {H : Subgroup G} (hG : oResidual 3 G = ⊤)
    (hN : (Subgroup.normalizer ((P : Subgroup G) : Set G) : Set G) ⊆
      ((P : Subgroup G) : Set G) *
        ((H ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    (∃ (K : Subgroup (P : Subgroup G)) (_ : K.Normal), Nonempty ((P : Subgroup G) ⧸ K ≃* W33)) ∨
      (P : Subgroup G) = ⁅(P : Subgroup G), (P : Subgroup G)⁆ ⊔
        ⁅H ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G), (P : Subgroup G)⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((P : Subgroup G) ⧸ K ≃* W33)
  · right
    have hY := CFSG.RankThree.Transfer.yoshida_eq_commutator_normalizer_of_oResidual_eq_top P hW hG
    have hM : H ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((P : Subgroup G) : Set G) := inf_le_right
    apply le_antisymm
    · conv_lhs => rw [hY]
      exact commutator_le_sup_of_subset_mul hM hN
    · exact sup_le (commutator_le_of_le_normalizer Subgroup.le_normalizer)
        (commutator_le_of_le_normalizer hM)
  · left
    push Not at hW
    obtain ⟨K, hK, hne⟩ := hW
    exact ⟨K, hK, hne⟩

theorem rank3II_11_31_of [Finite G] (P : Sylow 3 G) (hG : oResidual 3 G = ⊤)
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal], IsEmpty ((P : Subgroup G) ⧸ K ≃* W33)) :
    (P : Subgroup G) = ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.RankThree.Transfer.yoshida_eq_commutator_normalizer_of_oResidual_eq_top P hW hG

theorem false_of_inverts {P : Subgroup G} {a u : G} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hPP : a ∈ ⁅P, P⁆) (hau : u * a * u⁻¹ = a)
    (hinv : ∀ y ∈ ⁅P, Subgroup.zpowers u⁆, u * y * u⁻¹ = y⁻¹)
    (habel : ⁅P, P⁆ ≤ ⁅P, Subgroup.zpowers u⁆) : False := by
  have h1 : a = a⁻¹ := hau.symm.trans (hinv a (habel hPP))
  have h2 : a ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel a
  apply ha1
  have : a ^ 3 = a ^ 2 * a := pow_succ a 2
  rw [ha3, h2, one_mul] at this
  exact this.symm

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem subset_mul_normalizer_of_transitive [Finite G] {P D : Subgroup G} {c d : G}
    (hND : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hNd : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hcD : c ∈ D) (hcd : Subgroup.zpowers c ≠ Subgroup.zpowers d)
    (htrans : ∀ F : Subgroup G, F ≤ D → Nat.card F = Nat.card (Subgroup.zpowers c) →
      F ≠ Subgroup.zpowers d → ∃ p ∈ P, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom) :
    (Subgroup.normalizer (P : Set G) : Set G) ⊆ (P : Set G) *
      ((Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (P : Set G) :
        Subgroup G) : Set G) := by
  intro y hy
  set F := (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom with hF
  have hFD : F ≤ D := by
    rw [hF, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact (Subgroup.mem_normalizer_iff.mp (hND hy) c).mp hcD
  have hFc : Nat.card F = Nat.card (Subgroup.zpowers c) :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hFd : F ≠ Subgroup.zpowers d := by
    intro h
    apply hcd
    have hyd : y⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := inv_mem (hNd hy)
    have e1 : F.map (MulAut.conj y⁻¹).toMonoidHom = Subgroup.zpowers c := by
      rw [hF, map_conj_map_conj, inv_mul_cancel, map_one]
      ext x
      simp
    rw [← e1, h]
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hyd z).mp hz
    · intro hx
      refine ⟨y * x * y⁻¹, ?_, by simp [mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyd) x).mp hx
      simpa using this
  obtain ⟨p, hp, hpF⟩ := htrans F hFD hFc hFd
  have hpN : p ∈ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer hp
  refine ⟨p, hp, p⁻¹ * y, ⟨?_, (Subgroup.normalizer (P : Set G)).mul_mem (inv_mem hpN) hy⟩,
    by group⟩
  have h1 : (Subgroup.zpowers c).map (MulAut.conj (p⁻¹ * y)).toMonoidHom = Subgroup.zpowers c := by
    rw [← map_conj_map_conj, ← hF, hpF, map_conj_map_conj, inv_mul_cancel, map_one]
    ext x
    simp
  have h2 : (Subgroup.zpowers c).map (MulAut.conj (p⁻¹ * y)⁻¹).toMonoidHom =
      Subgroup.zpowers c := by
    conv_lhs => rw [← h1]
    rw [map_conj_map_conj, inv_mul_cancel, map_one]
    ext x
    simp
  exact Sec12.mem_normalizer_of_map_conj_eq h1 h2

theorem isSylowOf_top_of_subset_mul [Finite G] {P R H : Subgroup G} (hP3 : IsPGroup 3 P)
    (hRP : R ≤ P) (hR : CFSG.ABGLocalTools.IsSylowOf 3 R H)
    (hN : (Subgroup.normalizer (P : Set G) : Set G) ⊆
      (P : Set G) * ((H ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (P : Set G)
  have hPN : P ≤ N := Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := N)).exists_le_sylow
  set S := (Q : Subgroup N).map N.subtype with hS
  have hPS : P ≤ S := fun x hx => ⟨⟨x, hPN hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map N.subtype
  have hSP : S ≤ P := by
    intro y hy
    obtain ⟨p, hp, n, hn, rfl⟩ := hN (hSN hy)
    have hnS : n ∈ S := by
      have := S.mul_mem (S.inv_mem (hPS hp)) hy
      simpa using this
    have hT : S ⊓ (H ⊓ N) = R :=
      (hR.eq_of_le (le_inf (hRP.trans hPS) (le_inf hR.le (hRP.trans hPN)))
        (inf_le_right.trans inf_le_left) (hS3.to_le inf_le_left))
    have hnR : n ∈ R := hT ▸ ⟨hnS, hn⟩
    exact P.mul_mem hp (hRP hnR)
  have hPS' : P = S := le_antisymm hPS hSP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P N := by
    rw [hPS']
    exact ⟨Q, rfl⟩
  exact Sec12.isSylowOf_of_normalizer_le hPsyl le_top (inf_le_right)

@[expose] noncomputable def sylowOfIsSylowOf [Finite G] {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) : Sylow 3 G :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard P (by
    rw [hP.card_eq, Subgroup.card_top])

theorem coe_sylowOfIsSylowOf [Finite G] {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) : (sylowOfIsSylowOf hP : Subgroup G) = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sylow.coe_ofCard P (by rw [hP.card_eq, Subgroup.card_top])

@[expose] def sec11P {G : Type*} [Group G] (R : Subgroup G) (g : G) : Subgroup G :=
  R ⊔ Subgroup.zpowers g

theorem Sec11Data.zpowers_ne {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) : Subgroup.zpowers c ≠ Subgroup.zpowers d := by
  intro hcd
  have hexpA : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hcommA : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdA : d ∈ A := by
    have hd : d ∈ A ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.mem_inf.mp hd).1
  have hcd' : c ∈ Subgroup.zpowers d := by
    rw [← hcd]
    exact Subgroup.mem_zpowers c
  have haK : a ∈ Subgroup.closure ({a, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdK : d ∈ Subgroup.closure ({a, d} : Set G) := Subgroup.subset_closure (by simp)
  have hle : A ≤ Subgroup.closure ({a, d} : Set G) := by
    have hA := h.closure_eq
    intro y hy
    rw [hA] at hy
    refine (Subgroup.closure_le _).mpr ?_ hy
    rintro z (rfl | rfl | rfl)
    · exact (Subgroup.zpowers_le.mpr hdK) hcd'
    · exact haK
    · exact hdK
  have h9 := card_closure_pair_le_nine (hcommA a h.a_mem d hdA) (hexpA a h.a_mem) (hexpA d hdA)
  have hcard := Subgroup.card_le_of_le hle
  rw [h.card_eq] at hcard
  exact absurd (hcard.trans h9) (by norm_num)

theorem Sec11Data.isPGroup_sec11P {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) : IsPGroup 3 (sec11P R g) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h.pow_eq_one
  have hg3 : IsPGroup 3 (Subgroup.zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr h.g_mem_normalizer
  have := hg3.to_sup_of_normal_right' h.isSylowOf.isPGroup hgN
  rw [sup_comm] at this
  exact this

theorem rank3II_11_14 {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom) :
    (∃ (K : Subgroup (sec11P R g)) (_ : K.Normal), Nonempty (sec11P R g ⧸ K ≃* W33)) ∨
      sec11P R g = ⁅sec11P R g, sec11P R g⁆ ⊔
        ⁅Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G), sec11P R g⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcD : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hN := subset_mul_normalizer_of_transitive hcdN hNd hcD h.zpowers_ne htrans
  have hS := isSylowOf_top_of_subset_mul h.isPGroup_sec11P le_sup_left h.isSylowOf hN
  have hG := h.toTheoremFourHyp.oResidual_eq_top 3
  exact rank3II_11_14_of (sylowOfIsSylowOf hS) hG hN

theorem rank3II_11_31 {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 (sec11P R g) ⊤)
    (hW : ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33)) :
    sec11P R g = ⁅sec11P R g, Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G)⁆ :=
  rank3II_11_31_of (sylowOfIsSylowOf hS) (h.toTheoremFourHyp.oResidual_eq_top 3) hW

structure Sec11Final (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) (d x s r g : G) : Prop
    extends Sec11Data G A c L a R Y d x s r g where
  zpowers_s_eq : Subgroup.zpowers s = Subgroup.zpowers c
  closure_eq_closure : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  orderOf_x : orderOf x = 9
  commutator_eq : ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a, d}
  not_field : ¬ KFacts.InducesStdKind Y c .field
  g_comm : g * a = a * g

@[expose] def Sec11DataExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y →
      ∃ (a' : G) (Y' : Subgroup G) (d x s r g : G), Sec11Data G A c L a' R Y' d x s r g

@[expose] def Item1128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      ∃ (a' : G) (Y' : Subgroup G) (x' s' r' g' : G), Sec11Final G A c L a' R Y' d x' s' r' g'

@[expose] def Item1132 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Final G A c L a R Y d x s r g →
      ∃ u ∈ Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        (∃ k : ℕ, u ^ 2 ^ k = 1) ∧
          sec11P R g ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.closure {a, g}

@[expose] def Item1133 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Final G A c L a R Y d x s r g →
      ∀ u ∈ Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        (∃ k : ℕ, u ^ 2 ^ k = 1) →
        sec11P R g ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.closure {a, g} →
          (∀ y ∈ ⁅sec11P R g, Subgroup.zpowers u⁆, u * y * u⁻¹ = y⁻¹) ∧
            ⁅sec11P R g, sec11P R g⁆ ≤ ⁅sec11P R g, Subgroup.zpowers u⁆

theorem sec11Never_of (hex : Sec11DataExists) (h1128 : Item1128) (h1132 : Item1132)
    (h1133 : Item1133) : Sec11Never := by
  intro G _ _ A c L a R Y hstd
  obtain ⟨a₀, Y₀, d, x, s, r, g, hdata⟩ := hex G A c L a R Y hstd
  obtain ⟨a', Y', x', s', r', g', hf⟩ := h1128 G A c L a₀ R Y₀ d x s r g hdata
  obtain ⟨u, hu, hu2, hCu⟩ := h1132 G A c L a' R Y' d x' s' r' g' hf
  obtain ⟨hinv, habel⟩ := h1133 G A c L a' R Y' d x' s' r' g' hf u hu hu2 hCu
  have haP : a' ∈ ⁅sec11P R g', sec11P R g'⁆ := by
    rw [hf.commutator_eq]
    exact Subgroup.subset_closure (by simp)
  have hau : u * a' * u⁻¹ = a' := by
    have : a' ∈ sec11P R g' ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hCu]
      exact Subgroup.subset_closure (by simp)
    have hc := Subgroup.mem_centralizer_singleton_iff.mp this.2
    rw [← hc, mul_inv_cancel_right]
  exact false_of_inverts hf.a_ne_one (hf.mem_partTwoF.1.2 a' hf.a_mem) haP hau hinv habel

end CFSG.RankThree.PartTwo.Sec11
