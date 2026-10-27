module

public import CFSG.Quasithin.Background.E2TwoProofFactor
import CFSG.Foundations.KCoreClosure
public import CFSG.Quasithin.Vol2.E2SevenStatement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem isKGroupCat_of_solvable {Y : Type} [Group Y] [Finite Y] (hY : Group.IsSolvable Y) :
    CFSG.SectionRank.IsKGroupCat Y :=
  CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple hY

theorem sqtkGroup_top {X : Type} [Group X] [Finite X] (hS : SQTKGroup X) :
    SQTKGroup ↥(⊤ : Subgroup X) := by
  refine ⟨fun p hp hp2 => ?_, hS.2.of_mulEquiv Subgroup.topEquiv⟩
  show CFSG.Open.pRank p (⊤ : Subgroup ↥(⊤ : Subgroup X)) ≤ 2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt Subgroup.topEquiv]
  exact hS.1 p hp hp2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem Hyp28.not_pCoreOf_subgroupOf_le (h : Hyp28 H T M V) :
    ¬ pCoreOf 2 (M.subgroupOf H) ≤ CFSG.Open.pCore 2 ↥H := by
  intro hle
  apply h.not_le_pCoreOf
  intro v hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvH : v ∈ H := h.le_H hv
  have hMH : M ≤ H := h.minParabolic.maximal.1.le
  have hPM : pCoreOf 2 M ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans hMH
  have hK : (pCoreOf 2 M).subgroupOf H ≤ pCoreOf 2 (M.subgroupOf H) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.subgroupOf_mono H (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv
        (Subgroup.subgroupOfEquivOfLe hPM).symm)
    intro m hm
    have hm' : (m : G) ∈ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (Subgroup.mem_subgroupOf.mp hm)
    rw [Subgroup.mem_normalizer_iff] at hm' ⊢
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hm' x
  have hy : (⟨v, hvH⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H :=
    hle (hK (Subgroup.mem_subgroupOf.mpr (h.le_pCoreOf hv)))
  exact Subgroup.mem_map.mpr ⟨⟨v, hvH⟩, hy, rfl⟩

theorem index_frattini_dvd {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hcases : Nonempty (P ≃* Multiplicative (ZMod p)) ∨ IsElemAbelianOfRank p 2 P ∨
      IsPOnePlusTwo p P) :
    (frattini P).index ∣ p ^ 2 := by
  rcases hcases with he | he | ⟨hex, hc, -⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card P = p := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Subgroup.index_dvd_card _).trans (hc ▸ dvd_pow_self p two_ne_zero)
  · obtain ⟨e⟩ := he
    have hc : Nat.card P = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    exact hc ▸ Subgroup.index_dvd_card _
  · have : Fact p.Prime := ⟨hp⟩
    have : Fact (IsPGroup p P) := ⟨IsPGroup.of_card hc⟩
    have hne : frattini P ≠ ⊥ := by
      intro hbot
      have hcomm : _root_.commutator P ≤ ⊥ :=
        hbot ▸ CFSG.commutator_le_frattini_of_isPGroup (R := P) (p := p)
      have hZ : Subgroup.center P = ⊤ := by
        refine Subgroup.eq_top_iff' _ |>.mpr fun z => Subgroup.mem_center_iff.mpr fun g => ?_
        have h1 := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
          (Subgroup.mem_top z))
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      have h1 := hex.center_order_p
      rw [hZ, Subgroup.card_top, hc] at h1
      have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      rw [pow_one] at h2
      omega
    have hidx : (frattini P).index ∣ p ^ 3 := hc ▸ Subgroup.index_dvd_card _
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow hp).mp hidx
    have hi3 : i ≠ 3 := by
      rintro rfl
      apply hne
      have h1 := (frattini P).card_mul_index
      rw [hie, hc] at h1
      have h2 : Nat.card (frattini P) = 1 := by
        have hp3 : 0 < p ^ 3 := pow_pos hp.pos 3
        nlinarith [Nat.card_pos (α := frattini P)]
      exact Subgroup.card_eq_one.mp h2
    rw [hie]
    exact pow_dvd_pow p (by omega)

theorem pow_le_sq_of_dvd {r p k : ℕ} (hr : r.Prime) (hp : p.Prime) (h : r ^ k ∣ p ^ 2) :
    r ^ k ≤ r ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero]
    exact Nat.one_le_pow _ _ hr.pos
  · have hrp : r = p := by
      have : r ∣ p ^ 2 := (dvd_pow_self r hk0.ne').trans h
      exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow this)
    subst hrp
    exact Nat.le_of_dvd (pow_pos hr.pos 2) h

theorem pRank_star_le_of_solvable (h : Hyp28 H T M V) (hsolv : Group.IsSolvable ↥H) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : CFSG.Open.pRank r (⊤ : Subgroup (StarQuot M H)) ≤ 2 := by
  have hmp := h.minParabolic.subgroupOf
  have hφs : Function.Surjective (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨p, hp, -, hcases⟩ := E2_1 hmp h.sqtk.1 hsolv (Or.inl h.not_pCoreOf_subgroupOf_le)
  obtain ⟨p', hp', hp2', hO2p2, hJbar, -, -⟩ := hmp.solvable_structure hsolv
  have h2P : ∀ y : ↥H ⧸ CFSG.Open.pCore 2 ↥H, ∃ k : ℕ,
      y ^ 2 ^ k ∈ CFSG.Open.pCore p' (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p ↥H p')).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) =
      CFSG.Open.pCore p' (↥H ⧸ CFSG.Open.pCore 2 ↥H) :=
    E2.twoResidual_eq_pCore hp' hp2' h2P
  rw [← hKP] at hJbar
  have hcard : Nat.card (StarQuot M H) =
      (frattini ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)))).index *
        (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))).index := by
    rw [← Subgroup.index_map_subtype, ← hJbar, Subgroup.index_map_eq _ hφs, kerIn_subgroupOf_top]
    · rfl
    · rw [QuotientGroup.ker_mk']
      exact hmp.pCore_le_kerIn
  have : (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))).Normal :=
    E2P.Factor.twoResidual_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
    (E2P.isPGroup_quotient_twoResidual (Y := ↥H ⧸ CFSG.Open.pCore 2 ↥H))
  have ha' : (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))).index = 2 ^ a := ha
  have hΦ := index_frattini_dvd hp hcases
  refine CFSG.SectionRank.pRank_le hr.one_lt fun E _ hE => ?_
  have : Fact r.Prime := ⟨hr⟩
  have hEp : IsPGroup r E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have h1 : r ^ k ∣ (frattini ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)))).index *
      2 ^ a := by
    rw [← hk, ← ha', ← hcard]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (r ^ k) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  rw [hk]
  exact pow_le_sq_of_dvd hr hp ((hcop.dvd_of_dvd_mul_right h1).trans hΦ)

theorem Hyp28.sqtkGroup_star (hA21 : AsA21SQTKSection) (h : Hyp28 H T M V) :
    SQTKGroup ↥(⊤ : Subgroup (StarQuot M H)) := by
  by_cases hsolv : Group.IsSolvable ↥H
  · have hsolv' : Group.IsSolvable (StarQuot M H) := by
      have := hsolv
      exact Group.isSolvable_of_surjective (E2P.starMap_surjective M H)
    refine sqtkGroup_top (X := StarQuot M H) ⟨fun r hr hr2 => ?_, isKGroupCat_of_solvable hsolv'⟩
    exact pRank_star_le_of_solvable h hsolv hr hr2
  · exact sqtkGroup_top (E2P.sqtkGroup_star hA21 h.minParabolic h.sqtk hsolv)

end E2

theorem ASInputs.as_E_2_9_starSQTK_of (hA21 : AsA21SQTKSection) : ASInputs.AS_E_2_9_starSQTK :=
  fun _ _ _ _ _ _ _ h => h.sqtkGroup_star hA21

end CFSG.Quasithin
