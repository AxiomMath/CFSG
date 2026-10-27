module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.Open.BenderStronglyEmbedded
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.SourceSuzukiTransport
public import CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2LayerSylow
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection
public import CFSG.Blueprint.SourceGeckCorrespondence

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {Q : Type} [Group Q] [Finite Q] {a : ℕ}

theorem mem_centralizer_conj_iff {P : Subgroup Q} {g h : Q}
    (hg : ∀ q : Q, q ∈ P ↔ g * q * g⁻¹ ∈ P) :
    h ∈ Subgroup.centralizer (P : Set Q) ↔
      g * h * g⁻¹ ∈ Subgroup.centralizer (P : Set Q) := by
  constructor
  · intro hh
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro p hp
    have hp' : g⁻¹ * p * g ∈ P := by
      refine (hg (g⁻¹ * p * g)).mpr ?_
      have : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
      rwa [this]
    have hc := (Subgroup.mem_centralizer_iff.mp hh) (g⁻¹ * p * g) hp'
    calc p * (g * h * g⁻¹) = (g * (g⁻¹ * p * g) * g⁻¹) * (g * h * g⁻¹) := by group
      _ = g * ((g⁻¹ * p * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * p * g)) * g⁻¹ := by rw [hc]
      _ = (g * h * g⁻¹) * (g * (g⁻¹ * p * g) * g⁻¹) := by group
      _ = (g * h * g⁻¹) * p := by group
  · intro hh
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro p hp
    have hp' : g * p * g⁻¹ ∈ P := (hg p).mp hp
    have hc := (Subgroup.mem_centralizer_iff.mp hh) (g * p * g⁻¹) hp'
    calc p * h = g⁻¹ * ((g * p * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * p * g⁻¹)) * g := by rw [hc]
      _ = h * p := by group

theorem card_le_of_isElemAbelian_of_fusionBenderBorel {L : Type} [Group L] [Finite L]
    {q k : ℕ} (hB : fusionBenderBorel L q k) (hq : 2 ≤ q) {A : Subgroup L}
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ q := by
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hA.isPGroup
  have hle : A ≤ sylowCenter (S : Subgroup L) := by
    intro x hx
    exact ⟨hAS hx, mem_centralizer_of_fusionBenderBorel hB hq S (hAS hx) (hA.2 x hx)⟩
  calc Nat.card A ≤ Nat.card (sylowCenter (S : Subgroup L)) := Subgroup.card_le_of_le hle
    _ = q := (benderBorel_sylowCenter hB S).2.2.1

theorem szOrder_strictMono {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) :
    x ^ 2 * (x ^ 2 + 1) * (x - 1) < y ^ 2 * (y ^ 2 + 1) * (y - 1) := by
  have h1 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by norm_num)
  have h2 : x ^ 2 + 1 ≤ y ^ 2 + 1 := by omega
  have h3 : x - 1 ≤ y - 1 := by omega
  have h4 : (x ^ 2 + 1) * (x - 1) ≤ (y ^ 2 + 1) * (y - 1) := Nat.mul_le_mul h2 h3
  have h5 : 0 < (y ^ 2 + 1) * (y - 1) := by
    have : 0 < y - 1 := by omega
    positivity
  calc x ^ 2 * (x ^ 2 + 1) * (x - 1) = x ^ 2 * ((x ^ 2 + 1) * (x - 1)) := by ring
    _ < y ^ 2 * ((y ^ 2 + 1) * (y - 1)) := Nat.mul_lt_mul_of_lt_of_le h1 h4 h5
    _ = y ^ 2 * (y ^ 2 + 1) * (y - 1) := by ring

theorem card_sz_le_imp_le {b c : ℕ}
    (h : Nat.card (Sz b) ≤ Nat.card (Sz c)) : b ≤ c := by
  by_contra hbc
  have hcb : c < b := by omega
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz,
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz] at h
  have hlt : (2 : ℕ) ^ (2 * c + 1) < 2 ^ (2 * b + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2c : 2 ≤ (2 : ℕ) ^ (2 * c + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstrict := szOrder_strictMono h2c hlt
  omega

theorem eq_of_orderOf_eq_two_of_cyclic_or_quaternion {P : Type} [Group P] [Finite P]
    (h : IsCyclic P ∨ ∃ r : ℕ, 3 ≤ r ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (r - 2))))
    {x y : P} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  rcases h with hc | ⟨r, -, ⟨e⟩⟩
  · exact CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution.eq_of_orderOf_eq_two_of_isCyclic
      hx hy
  · haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    exact CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution.eq_of_orderOf_eq_two_of_quaternion
      e hx hy

theorem exists_mulEquiv_sz_of_isSz {X : Type} [Group X] {r : ℕ}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz X r) :
    ∃ a : ℕ, 1 ≤ a ∧ r = 2 * a + 1 ∧ Nonempty (X ≃* Sz a) := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz CFSG.Blueprint.LieModel at h
  rcases h with h | h | h | ⟨-, -, hSuz⟩
  · exact absurd h.1 (by decide)
  · exact absurd h.2.1 (by decide)
  · exact absurd h.2.1 (by decide)
  · unfold CFSG.Blueprint.SuzukiModel at hSuz
    obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hKcard, ⟨eX⟩⟩ := hSuz
    letI : Field K := hKfld
    letI : Finite K := hKfin
    have hcard : Nat.card K = Nat.card (GaloisField 2 (2 * a + 1)) := by
      rw [GaloisField.card 2 (2 * a + 1) (by omega)]
      rw [hf] at hKcard
      exact hKcard
    obtain ⟨φ⟩ := CFSG.Blueprint.EvenSource.nonempty_ringEquiv_of_card_eq K
      (GaloisField 2 (2 * a + 1)) hcard
    exact ⟨a, ha, hf, ⟨eX.trans ((CFSG.Blueprint.EvenSource.suzukiGroupMapEquiv a φ).trans
      (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup
        a).some.symm)⟩⟩

theorem twoRank_eq_of_mulEquiv_sz (ha : 1 ≤ a) (e : Q ≃* Sz a) :
    twoRank Q = 2 * a + 1 := by
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  obtain ⟨e'⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  exact CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_eq_of_mulEquiv hK (e.trans e')

theorem exists_sylow_eq_inf_centralizer_of_isElemAbelian (ha : 1 ≤ a) (e : Q ≃* Sz a)
    {A : Subgroup Q} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 2 ^ (2 * a + 1)) :
    ∃ P : Sylow 2 Q, A = (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) := by
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha e
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA.isPGroup
  refine ⟨P, ?_⟩
  have hAle : A ≤ (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) := by
    intro x hx
    exact ⟨hAP hx, mem_centralizer_of_fusionBenderBorel hB hq P (hAP hx) (hA.2 x hx)⟩
  have hZcard : Nat.card ↥((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)) =
      2 ^ (2 * a + 1) :=
    (benderBorel_sylowCenter hB P).2.2.1
  apply Subgroup.eq_of_le_of_card_ge hAle
  omega

theorem normalizer_inf_centralizer_eq_of_mulEquiv_sz (ha : 1 ≤ a) (e : Q ≃* Sz a)
    (P : Sylow 2 Q) :
    normalizer (((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) : Subgroup Q) : Set Q) =
      normalizer ((P : Subgroup Q) : Set Q) := by
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha e
  have hZcard : Nat.card ↥((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)) =
      2 ^ (2 * a + 1) :=
    (benderBorel_sylowCenter hB P).2.2.1
  apply le_antisymm
  · intro g hg
    by_cases hge : P = g • P
    · exact Sylow.smul_eq_iff_mem_normalizer.mp hge.symm
    · exfalso
      have hgZ : ((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)).map
          (MulAut.conj g).toMonoidHom =
          (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      have hZle : (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) ≤
          (P : Subgroup Q) ⊓ ((g • P : Sylow 2 Q) : Subgroup Q) := by
        refine le_inf inf_le_left ?_
        calc (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)
            = ((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)).map
                (MulAut.conj g).toMonoidHom := hgZ.symm
          _ ≤ (P : Subgroup Q).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono inf_le_left
          _ = ((g • P : Sylow 2 Q) : Subgroup Q) := by
              rw [Sylow.coe_subgroup_smul]
              rfl
      have hZle_bot : (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) ≤ ⊥ := by
        rw [← inf_eq_bot_of_fusionBenderBorel hB hge]
        exact hZle
      have hZne : (P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q) ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card ↥((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)) = 1 := by
          rw [hbot, Subgroup.card_bot]
        rw [hZcard] at h1
        omega
      exact hZne (le_bot_iff.mp hZle_bot)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hhP, hhC⟩
      exact ⟨(hg h).mp hhP, (mem_centralizer_conj_iff hg).mp hhC⟩
    · rintro ⟨hhP, hhC⟩
      exact ⟨(hg h).mpr hhP, (mem_centralizer_conj_iff hg).mpr hhC⟩

theorem inf_centralizer_sup_inf_centralizer_eq_top
    (ha : 1 ≤ a) (e : Q ≃* Sz a) {P P' : Sylow 2 Q}
    (hne : P ≠ P') :
    ((P : Subgroup Q) ⊓ centralizer ((P : Subgroup Q) : Set Q)) ⊔
      ((P' : Subgroup Q) ⊓ centralizer ((P' : Subgroup Q) : Set Q)) = ⊤ := by
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha e
  change sylowCenter (P : Subgroup Q) ⊔ sylowCenter (P' : Subgroup Q) = ⊤
  set ZP : Subgroup Q := sylowCenter (P : Subgroup Q) with hZP
  set ZP' : Subgroup Q := sylowCenter (P' : Subgroup Q) with hZP'
  set Y : Subgroup Q := ZP ⊔ ZP' with hY
  have hZPcard : Nat.card ZP = 2 ^ (2 * a + 1) := by
    rw [hZP]; exact (benderBorel_sylowCenter hB P).2.2.1
  have hZP'card : Nat.card ZP' = 2 ^ (2 * a + 1) := by
    rw [hZP']; exact (benderBorel_sylowCenter hB P').2.2.1
  have hZP2 : ∀ z ∈ ZP, z ^ 2 = 1 := by
    intro z hz; rw [hZP] at hz; exact (benderBorel_sylowCenter hB P).2.1 z hz
  have hZP'2 : ∀ z ∈ ZP', z ^ 2 = 1 := by
    intro z hz; rw [hZP'] at hz; exact (benderBorel_sylowCenter hB P').2.1 z hz
  have hZPcomm : IsMulCommutative ZP := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxc : (x : Q) ∈ sylowCenter (P : Subgroup Q) := by rw [← hZP]; exact x.2
    have hyc : (y : Q) ∈ sylowCenter (P : Subgroup Q) := by rw [← hZP]; exact y.2
    exact Subtype.ext
      ((mem_sylowCenter.mp hxc).2 (y : Q) (mem_sylowCenter.mp hyc).1).symm
  have hZP'comm : IsMulCommutative ZP' := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxc : (x : Q) ∈ sylowCenter (P' : Subgroup Q) := by rw [← hZP']; exact x.2
    have hyc : (y : Q) ∈ sylowCenter (P' : Subgroup Q) := by rw [← hZP']; exact y.2
    exact Subtype.ext
      ((mem_sylowCenter.mp hxc).2 (y : Q) (mem_sylowCenter.mp hyc).1).symm
  have hZPel : IsElemAbelian 2 ZP := ⟨hZPcomm, hZP2⟩
  have hZP'el : IsElemAbelian 2 ZP' := ⟨hZP'comm, hZP'2⟩
  have hZPY : ZP ≤ Y := by rw [hY]; exact le_sup_left
  have hZP'Y : ZP' ≤ Y := by rw [hY]; exact le_sup_right
  set Zsub : Subgroup ↥Y := ZP.subgroupOf Y with hZsub
  have hZsubel : IsElemAbelian 2 Zsub := by rw [hZsub]; exact hZPel.subgroupOf Y
  have hZsubcard : Nat.card Zsub = 2 ^ (2 * a + 1) := by
    have h : Nat.card Zsub = Nat.card ZP := by
      rw [hZsub]
      have hmap := Subgroup.card_map_of_injective (K := ZP.subgroupOf Y) Y.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZPY] at hmap
      exact hmap.symm
    rw [h, hZPcard]
  set N₀ : Subgroup Q := Subgroup.normalizer ((P : Subgroup Q) : Set Q) with hN₀
  have hSE : fusionStronglyEmbedded N₀ := by rw [hN₀]; exact (hB P).1
  have hnotY : ¬ Y ≤ N₀ := by
    intro hYN
    have hZP'leN : ZP' ≤ N₀ := hZP'Y.trans hYN
    have hZP'leP : ZP' ≤ (P : Subgroup Q) := by
      have hnorm : ZP' ≤ Subgroup.normalizer (P : Subgroup Q) := by
        rw [← hN₀]; exact hZP'leN
      have hsup : IsPGroup 2 ↥(ZP' ⊔ (P : Subgroup Q)) :=
        IsPGroup.to_sup_of_normal_right' hZP'el.isPGroup (P : Sylow 2 Q).isPGroup' hnorm
      calc ZP' ≤ ZP' ⊔ (P : Subgroup Q) := le_sup_left
        _ = (P : Subgroup Q) := (P : Sylow 2 Q).is_maximal' hsup le_sup_right
    have hZP'bot : ZP' = ⊥ := by
      have hle : ZP' ≤ (P : Subgroup Q) ⊓ (P' : Subgroup Q) :=
        le_inf hZP'leP (by rw [hZP']; exact inf_le_left)
      rw [inf_eq_bot_of_fusionBenderBorel hB hne] at hle
      exact le_bot_iff.mp hle
    have hZP'ne : ZP' ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ZP' = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hZP'card] at h1
      omega
    exact hZP'ne hZP'bot
  have hEven : Even (Nat.card ↥(N₀ ⊓ Y)) := by
    have hZPY' : ZP ≤ N₀ ⊓ Y := by
      refine le_inf ?_ hZPY
      rw [hN₀, hZP]
      exact (sylowCenter_le (P : Subgroup Q)).trans Subgroup.le_normalizer
    have hdvd : Nat.card ZP ∣ Nat.card ↥(N₀ ⊓ Y) := Subgroup.card_dvd_of_le hZPY'
    have h2 : 2 ∣ Nat.card ZP := by rw [hZPcard]; exact dvd_pow_self 2 (by omega)
    exact even_iff_two_dvd.mpr (h2.trans hdvd)
  have hSEY : fusionStronglyEmbedded (N₀.subgroupOf Y) :=
    stronglyEmbedded_subgroupOf hSE Y hnotY hEven
  rcases CFSG.Open.Open.bender_strongly_embedded ↥Y (N₀.subgroupOf Y) hSEY with
    hcyc | ⟨M, N, hMnorm, hNnorm, hMNnorm, hMN, hModd, hNodd, hBender⟩
  · exfalso
    obtain ⟨S, hZsubS⟩ := IsPGroup.exists_le_sylow hZsubel.isPGroup
    have hnt : Nontrivial Zsub := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZsubcard]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    obtain ⟨x, hx1⟩ := exists_ne (1 : Zsub)
    have hx2 : (x : ↥Y) ^ 2 = 1 := hZsubel.2 (x : ↥Y) x.2
    have hxord : orderOf (x : ↥Y) = 2 :=
      orderOf_eq_prime hx2 (fun h => hx1 (Subtype.ext h))
    let z : ↥S := ⟨(x : ↥Y), hZsubS x.2⟩
    have hzord : orderOf z = 2 :=
      (Subgroup.orderOf_mk (x : ↥Y) (hZsubS x.2)).trans hxord
    have huniq : ∀ y : ↥S, orderOf y = 2 → y = z :=
      fun y hy => eq_of_orderOf_eq_two_of_cyclic_or_quaternion (hcyc S) hy hzord
    have hrankS : twoRank ↥S ≤ 1 :=
      CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution z hzord huniq
    have hrank_ge : 2 * a + 1 ≤ twoRank ↥S := by
      have hEcard : Nat.card (Zsub.subgroupOf (S : Subgroup ↥Y)) = 2 ^ (2 * a + 1) := by
        have hmap := Subgroup.card_map_of_injective
          (K := Zsub.subgroupOf (S : Subgroup ↥Y)) (S : Subgroup ↥Y).subtype_injective
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZsubS] at hmap
        rw [hmap.symm, hZsubcard]
      exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary ↥S
        (Zsub.subgroupOf (S : Subgroup ↥Y)) (hZsubel.subgroupOf (S : Subgroup ↥Y))
        (2 * a + 1) hEcard
    omega
  · have hZsubMbot : Zsub ⊓ M = ⊥ := by
      have hdiv : Nat.card ↥(Zsub ⊓ M) ∣ 2 ^ (2 * a + 1) := by
        rw [← hZsubcard]; exact Subgroup.card_dvd_of_le inf_le_left
      have hodd : Odd (Nat.card ↥(Zsub ⊓ M)) :=
        hModd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
      have hcop : Nat.Coprime (Nat.card ↥(Zsub ⊓ M)) (2 ^ (2 * a + 1)) :=
        hodd.coprime_two_right.pow_right _
      exact (Subgroup.eq_bot_iff_card (H := Zsub ⊓ M)).mpr
        (Nat.Coprime.eq_one_of_dvd hcop hdiv)
    have hZN : Zsub ≤ N := by
      intro z hz
      by_contra hzN
      have hpow : (QuotientGroup.mk' N z) ^ 2 ^ 1 = 1 := by
        rw [pow_one, ← map_pow, hZsubel.2 z hz, map_one]
      have hodd_top : Odd (Nat.card ↥(⊤ : Subgroup (↥Y ⧸ N))) := by
        rw [Subgroup.card_top, ← Subgroup.index_eq_card]; exact hNodd
      have h1 := eq_one_of_mem_odd_subgroup_of_pow_two_pow (N := (⊤ : Subgroup (↥Y ⧸ N)))
        hodd_top (c := QuotientGroup.mk' N z) trivial hpow
      exact hzN ((QuotientGroup.eq_one_iff z).mp h1)
    let f : Zsub →* N ⧸ M.subgroupOf N :=
      (QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hZN)
    have hf_inj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxM : (x : ↥Y) ∈ M := by
        have hx' : ((Subgroup.inclusion hZN x : N) : N ⧸ M.subgroupOf N) = 1 := hx
        have hmem := (QuotientGroup.eq_one_iff (Subgroup.inclusion hZN x)).mp hx'
        simpa [Subgroup.mem_subgroupOf] using hmem
      have hxbot : (x : ↥Y) ∈ Zsub ⊓ M := ⟨x.2, hxM⟩
      rw [hZsubMbot] at hxbot
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    let Aq : Subgroup (N ⧸ M.subgroupOf N) := f.range
    have hAqcard : Nat.card Aq = 2 ^ (2 * a + 1) := by
      have h := Nat.card_congr (MonoidHom.ofInjective hf_inj).toEquiv
      change Nat.card f.range = 2 ^ (2 * a + 1)
      rw [← h, hZsubcard]
    have hAqel : IsElemAbelian 2 Aq := by
      change IsElemAbelian 2 f.range
      refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
      · obtain ⟨u', hu'⟩ := MonoidHom.mem_range.mp u.2
        obtain ⟨v', hv'⟩ := MonoidHom.mem_range.mp v.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← hu', ← hv', ← map_mul, ← map_mul, mul_comm' u' v']
      · obtain ⟨u', hu'⟩ := MonoidHom.mem_range.mp hu
        rw [← hu', ← map_pow]
        have hu2 : u' ^ 2 = 1 := Subtype.ext (hZsubel.2 (u' : ↥Y) u'.2)
        rw [hu2, map_one]
    have hcardQ : Nat.card Q = Nat.card (Sz a) := Nat.card_congr e.toEquiv
    have h3Q : ¬ 3 ∣ Nat.card Q := by
      rw [hcardQ]
      exact not_three_dvd_card_sz a
    have hNMdvd : Nat.card (N ⧸ M.subgroupOf N) ∣ Nat.card Q :=
      (Subgroup.card_quotient_dvd_card (M.subgroupOf N)).trans
        ((Subgroup.card_subgroup_dvd_card N).trans (Subgroup.card_subgroup_dvd_card Y))
    have hBenderSz : ∃ b : ℕ, 1 ≤ b ∧ Nonempty ((N ⧸ M.subgroupOf N) ≃* Sz b) := by
      rcases hBender with ⟨f0, hf0, ⟨ePSL⟩⟩ | ⟨f0, hf0, ⟨ePSU⟩⟩ | ⟨b, hb, ⟨eSz⟩⟩
      · exfalso
        have h3 : 3 ∣ Nat.card (N ⧸ M.subgroupOf N) := by
          rw [Nat.card_congr ePSL.toEquiv]
          exact three_dvd_card_psl2_two_pow (by omega)
        exact h3Q (h3.trans hNMdvd)
      · exfalso
        have h3 : 3 ∣ Nat.card (N ⧸ M.subgroupOf N) := by
          rw [Nat.card_congr ePSU.toEquiv]
          exact three_dvd_card_psu3 (by omega)
        exact h3Q (h3.trans hNMdvd)
      · exact ⟨b, hb, ⟨eSz⟩⟩
    obtain ⟨b, hb, ⟨eSz⟩⟩ := hBenderSz
    have hq_le_qb : 2 ^ (2 * a + 1) ≤ 2 ^ (2 * b + 1) := by
      have hBq : fusionBenderBorel (N ⧸ M.subgroupOf N) (2 ^ (2 * b + 1)) 2 :=
        fusionBenderBorel_of_mulEquiv_sz hb eSz
      have hle := card_le_of_isElemAbelian_of_fusionBenderBorel hBq (by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hAqel
      rwa [hAqcard] at hle
    have hab : a = b := by
      have hle1 : 2 * a + 1 ≤ 2 * b + 1 :=
        (Nat.pow_le_pow_iff_right (by norm_num)).mp hq_le_qb
      have hba : b ≤ a := by
        apply card_sz_le_imp_le
        have hNMleY : Nat.card (N ⧸ M.subgroupOf N) ≤ Nat.card ↥Y :=
          (Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_quotient_dvd_card (M.subgroupOf N))).trans
            (Subgroup.card_le_card_group (H := N))
        have hYleQ : Nat.card ↥Y ≤ Nat.card Q := Subgroup.card_le_card_group (H := Y)
        calc Nat.card (Sz b) = Nat.card (N ⧸ M.subgroupOf N) :=
              (Nat.card_congr eSz.toEquiv).symm
          _ ≤ Nat.card ↥Y := hNMleY
          _ ≤ Nat.card Q := hYleQ
          _ = Nat.card (Sz a) := hcardQ
      omega
    have hcardN : Nat.card (N ⧸ M.subgroupOf N) = Nat.card Q := by
      have h1 : Nat.card (N ⧸ M.subgroupOf N) = Nat.card (Sz b) :=
        Nat.card_congr eSz.toEquiv
      have h2 : Nat.card (Sz b) = Nat.card (Sz a) := by rw [hab]
      exact h1.trans (h2.trans hcardQ.symm)
    have hYcard : Nat.card ↥Y = Nat.card Q := by
      apply le_antisymm (Subgroup.card_le_card_group (H := Y))
      calc Nat.card Q = Nat.card (N ⧸ M.subgroupOf N) := hcardN.symm
        _ ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_quotient_dvd_card (M.subgroupOf N))
        _ ≤ Nat.card ↥Y := Subgroup.card_le_card_group (H := N)
    exact Subgroup.eq_top_of_card_eq (H := Y) hYcard

theorem exists_smul_eq_and_smul_eq_of_mulEquiv_sz (ha : 1 ≤ a) (e : Q ≃* Sz a)
    {P P' : Sylow 2 Q} (hne : P ≠ P') : ∃ z : Q, z • P = P' ∧ z • P' = P := by
  have hB : fusionBenderBorel Q (2 ^ (2 * a + 1)) 2 := fusionBenderBorel_of_mulEquiv_sz ha e
  have hcard := card_sylow_of_mulEquiv_sz ha e P'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P P'
  by_cases hcase : g • P' = P
  · exact ⟨g, hg, hcase⟩
  · have hSne : g • P' ≠ P' := by
      intro h
      have hP : g • P = g • P' := by rw [hg, h]
      have : P = P' := by
        have := congrArg (fun x => g⁻¹ • x) hP
        simpa using this
      exact hne this
    obtain ⟨r, hrP', hrsmul⟩ := exists_mem_smul_eq_of_fusionBenderBorel hB hcard hSne hne
    refine ⟨r * g, ?_, ?_⟩
    · rw [mul_smul, hg]
      exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hrP')
    · rw [mul_smul, hrsmul]

end CFSG.LocalAnalysis.WeakClosure81
