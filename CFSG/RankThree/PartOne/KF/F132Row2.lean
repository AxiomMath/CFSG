module

public import CFSG.RankThree.PartOne.KLAY.Frames
public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132AtEx
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.KLAY.G2

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KLAY

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem sec12TwoGeneric_of_exceptional (hECS : CFSG.RankThree.PartOne.ExceptionalCenterSmallPrimes)
    (hF : Sec12Facts G p A c L E) (hrep : ExceptionalRep (L ⧸ Subgroup.center L)) :
    Sec12TwoGeneric p c L E := by
  rcases hF.two with hG | hS
  · exact hG
  · exfalso
    have hp5 := hS.p_eq
    apply hECS L hS.quasisimple hrep p (by rw [hp5]; norm_num) (by omega)
    rw [hS.center_card, hp5]

theorem exists_r2frame_of {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hpq : p ∣ 2 ^ f - 1)
    (hmod : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .G2 0 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧ CharP K 2 ∧
      ∃ ε : ↥L →* AdjointQuotient .G2 K, IsCentralPQuot p ε ∧
        (∀ t ∈ Tp p K, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = g2Q K t) ∧
        ∀ x : F, ∃ t ∈ Tp p K, ε (Subgroup.inclusion h.F_le x) = g2Q K t := by
  classical
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hexc
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f)
        (by rw [Fintype.card_eq_nat_card]; exact hK)
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e hcop
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (g2Q K) (isCentralPQuot_g2Q p K) _ hε₀
      (fun t ht => Tp_exp t ht) (fun s hs t ht => Tp_comm s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp hp h5 hpK X hexp) h.F_le h.F_exp h.F_comm h.maximal
    exact ⟨K, hKf, hKfin, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

theorem layerRow2_of_core (h : Sec12Hyp G p A c L E)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c)
    (hEA' : E = A) (hcore : Table123Core p L (A ⊓ L) (E ⊓ L)) (hf1 : 1 ≤ f)
    (hpq : p ∣ 2 ^ f - 1)
    (hmod : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .G2 0 2 f) :
    ∃ (b : G) (K : Subgroup G), LayerCore p A L b K ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 f := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, hKf, hKfin, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r2frame_of hcore hpq hmod
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  have hq : IsCentralPQuot p (g2Q K) := isCentralPQuot_g2Q p K
  obtain ⟨bM, hbMT, hbMp, hbM1, hKq, hKz, hTK, ⟨U, hU, hU2, hTU, hnc⟩, k, hkf, hkfin, hk,
    ⟨eqv₂⟩⟩ := g2_side (p := p) hp h5 hf1 hK hpq ⟨ζ, hζ⟩
  obtain ⟨x, hx⟩ := hFT₁ bM hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = g2Q K bM := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : g2Q K bM = g2Q K 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbM1 (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp p K).map (g2Q K) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hEeq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem hLc hA ε (g2Q K) hε hq hxA hxL hbMp hbb
    (T₀ := Tp p K) (U := U) (fun t ht => Tp_exp t ht) hAT hKq hKz hTK hU hU2 hTU hnc
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  refine ⟨⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, k, hkf, hkfin, hk, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · exact ⟨eqv.trans (eqv₂.trans (projectiveSpecialLinearGroupEquivStatedProj 2 k))⟩

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KF132 CFSG.Blueprint

theorem kf132AtEx_row2
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hECS : ExceptionalCenterSmallPrimes) : KF132AtEx 2 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hrep : ExceptionalRep (L ⧸ Subgroup.center L) := by
    rcases hmod with ⟨hcl, -⟩ | ⟨-, ht, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
    · exact absurd hcl (by decide)
    · exact Or.inl ⟨.G2, 2, f, ht, hexc⟩
    · exact absurd hrt (by decide)
    · exact absurd ht (by decide)
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_exceptional hECS hF hrep
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨b, K, hd, hKmod⟩ := layerRow2_of_core h h.L_le_centralizer hG.E_eq hEA hcore hf1 hpq hmod
  obtain ⟨t, htL, hrefl, -, hKF, -⟩ := exists_reflection_of_core hGA h hEA hcL hd hf3 hKmod
  exact ⟨t, ⟨hrefl, L, hF13.inZeroStar, htL⟩, htL, f, f, ⟨hf1, hpq, hmod⟩, rfl, hKF⟩

end CFSG.RankThree.PartOne.S13K
