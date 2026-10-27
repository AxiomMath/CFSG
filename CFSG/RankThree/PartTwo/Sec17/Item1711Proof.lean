module

public import CFSG.RankThree.PartTwo.Sec17.Item1712ProofRoute
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def k1711 (A : Subgroup G) (b : G) : Subgroup G :=
  oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

end Defs

@[expose] noncomputable def Step1711KM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) →
        k1711 A b ≤ (k1711 A b ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ pPrimeCoreOf 3 (k1711 A b)

@[expose] noncomputable def Step1711Fit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    ∀ U ∈ fourGroups A, U = ⁅U, Subgroup.zpowers a⁆ →
      U ∈ collectionIn (scriptQ A (lB A))
        (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
          Subgroup.centralizer ({b} : Set G)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ⁅k1711 A b, U⁆ ≤ pPrimeCoreOf 3 (k1711 A b) →
        ∃ Z : Subgroup G, Odd (Nat.card Z) ∧ U ≤ Subgroup.normalizer (Z : Set G) ∧
          ⁅Z, U⁆ ≠ ⊥ ∧
          Z ≤ ⨆ (u : G) (_ : u ∈ U) (_ : u ≠ 1),
            Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G) ∧
          Z ⊓ Subgroup.centralizer ({a} : Set G) ≤
            delta A (lB A) (Subgroup.centralizer ({a} : Set G))

namespace Proof1711

variable {G : Type} [Group G] [Finite G]

theorem centralizer_ne_top (hG : TheoremFourHyp G) {b : G} (hb : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hG.isSimpleGroup
  have hbZ : b ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h1
  · rw [h0, Subgroup.mem_bot] at hbZ
    exact hb hbZ
  · obtain ⟨x, y, hxy⟩ := hG.nonabelian
    have hy : y ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top y
    exact hxy (Subgroup.mem_center_iff.mp hy x)

theorem commutator_le_pPrimeCoreOf {K M U : Subgroup G} (hUM : U ≤ CFSG.Open.pCoreOf 2 M)
    (hUK : U ≤ Subgroup.normalizer (K : Set G))
    (hKM : K ≤ (K ⊓ M) ⊔ pPrimeCoreOf 3 K) : ⁅K, U⁆ ≤ pPrimeCoreOf 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 K with hO
  set H := K ⊓ M with hH
  set P := CFSG.Open.pCoreOf 2 M with hP
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hUO : U ≤ Subgroup.normalizer (O : Set G) :=
    hUK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hHK : H ≤ K := inf_le_left
  have hCK : ⁅H, U⁆ ≤ K := (Subgroup.commutator_mono hHK le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hUK)
  have hCP : ⁅H, U⁆ ≤ P := by
    have hMP : M ≤ Subgroup.normalizer (P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    have h1 : ⁅P, M⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hMP
    rw [Subgroup.commutator_comm] at h1
    exact (Subgroup.commutator_mono inf_le_right hUM).trans h1
  set N := ⁅H, U⁆ ⊔ O with hN
  have hNK : N ≤ K := sup_le hCK (pPrimeCoreOf_le 3 K)
  have hCO : ⁅H, U⁆ ≤ Subgroup.normalizer (O : Set G) := hCK.trans hKO
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    have hdvd := card_sup_dvd_card_mul hCO
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP2.to_le hCP)
    have hc1 : Nat.Coprime 3 (Nat.card (⁅H, U⁆ : Subgroup G)) := by
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    exact Nat.Coprime.coprime_dvd_right hdvd
      (Nat.Coprime.mul_right hc1 (coprime_card_pPrimeCoreOf 3 K))
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup (Subgroup.normalizer_commutator_ge_left H U) (hHK.trans hKO)
  have hON : O ≤ Subgroup.normalizer (N : Set G) :=
    (le_sup_right : O ≤ N).trans Subgroup.le_normalizer
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := hKM.trans (sup_le hHN hON)
  have hNO : N ≤ O := le_pPrimeCoreOf hNK hKN hN3
  have hCO' : ⁅H, U⁆ ≤ O := le_sup_left.trans hNO
  rw [Subgroup.commutator_le]
  intro k hk u hu
  have hk' : k ∈ ((O ⊔ H : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hKM hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O H (hHK.trans hKO)] at hk'
  obtain ⟨o, ho, m, hm, rfl⟩ := hk'
  have hkey : ⁅o * m, u⁆ = o * ⁅m, u⁆ * (u * o⁻¹ * u⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hkey]
  refine mul_mem (mul_mem ho (hCO' (Subgroup.commutator_mem_commutator hm hu))) ?_
  exact (Subgroup.mem_normalizer_iff.mp (hUO hu) _).mp (inv_mem ho)

theorem k1711_eq_bot_of_not_dvd {A : Subgroup G} {b : G}
    (h3 : ¬ 3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))) :
    k1711 A b = ⊥ := by
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  rw [k1711, oPrimeResidualOf_eq_closure, Subgroup.closure_eq_bot_iff]
  rintro x ⟨hxD, k, hk⟩
  have hdvd : orderOf (⟨x, hxD⟩ : D) ∣ Nat.gcd (3 ^ k) (Nat.card D) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk)))
      (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact congrArg Subtype.val hdvd

theorem inf_eq_bot_of_odd {Z P : Subgroup G} (hZ : Odd (Nat.card Z)) (hP : IsPGroup 2 P) :
    Z ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_le (inf_le_right : Z ⊓ P ≤ P))
  have hdvd : Nat.card (Z ⊓ P : Subgroup G) ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_left
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra hn0
    have h2 : 2 ∣ Nat.card Z := (dvd_pow_self 2 hn0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h2)
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.mp hn

omit [Finite G] in
theorem inf_centralizer_conj_le {Z : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (Z : Set G)) (a : G) :
    Z ⊓ Subgroup.centralizer ({u * a * u⁻¹} : Set G) ≤
      (Z ⊓ Subgroup.centralizer ({a} : Set G)).map (MulAut.conj u).toMonoidHom := by
  intro x hx
  refine ⟨u⁻¹ * x * u, ⟨?_, ?_⟩, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hu) x).mp hx.1
    simpa using this
  · change u⁻¹ * x * u ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    calc u⁻¹ * x * u * a = u⁻¹ * (x * (u * a * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * a * u⁻¹) * x) * u := by rw [h]
      _ = a * (u⁻¹ * x * u) := by group
  · change u * (u⁻¹ * x * u) * u⁻¹ = x
    group

end Proof1711

section Item1711

variable {G : Type} [Group G] [Finite G]

theorem rank3II_17_11_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h179 : Item179 A (lB A)) (hKM : Step1711KM) (hFit : Step1711Fit) : Item1711 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y₀' hY₀' a ha ha1 Y hY hΔaY b hb hb1 U hU hUa hUQ
  obtain rfl : Y₀' = Y₀ := h.eq_of_mem_y0Star hY₀'
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  have hDtop : D ≠ ⊤ := by
    intro htop
    apply Proof1711.centralizer_ne_top h.toTheoremFourHyp hb1
    rw [eq_top_iff, ← htop]
    exact delta_le _
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  refine ⟨⟨⟨hDtop, hAD⟩, fun hO2 => ?_⟩, (delta_delta _).symm⟩
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := (mem_fourGroups_iff.mp hU).1
  have hUA : ⁅U, A⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hAU
  have hUm : U ∈ fourGroupsMinus A :=
    ⟨hU, le_antisymm (hUa.le.trans (Subgroup.commutator_mono le_rfl
      (Subgroup.zpowers_le.mpr ha))) hUA⟩
  have hUY : U ≤ CFSG.Open.pCoreOf 2 Y :=
    (h179 Y₀' hY₀').2 U hUm ⟨hUQ.1, hUQ.2.trans inf_le_left⟩ Y hY
  have hUD : U ≤ D := le_delta hUQ.1 (hUQ.2.trans inf_le_right)
  by_cases hDM : D ≤ Subgroup.normalizer (Y₀' : Set G)
  · have hUO : U ≤ CFSG.Open.pCoreOf 2 D := (le_inf (hUQ.2.trans inf_le_left) hUD).trans
      (inf_le_pCoreOf_of_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        (hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
    rw [hO2, le_bot_iff] at hUO
    have h4 := (mem_fourGroups_iff.mp hU).2.2
    rw [hUO, Subgroup.card_bot] at h4
    omega
  have hKM' : k1711 A b ≤ (k1711 A b ⊓ Subgroup.normalizer (Y₀' : Set G)) ⊔
      pPrimeCoreOf 3 (k1711 A b) := by
    by_cases h3 : 3 ∣ Nat.card D
    · exact hKM G A c L Y₀' h b hb hb1 hO2 hDM h3
    · rw [Proof1711.k1711_eq_bot_of_not_dvd h3]
      exact bot_le
  have hUK : U ≤ Subgroup.normalizer (k1711 A b : Set G) :=
    hUD.trans (le_normalizer_oPrimeResidualOf Subgroup.le_normalizer)
  have hcomm : ⁅k1711 A b, U⁆ ≤ pPrimeCoreOf 3 (k1711 A b) :=
    Proof1711.commutator_le_pPrimeCoreOf (hUQ.2.trans inf_le_left) hUK hKM'
  obtain ⟨Z, hZodd, hUZ, hZU, hZgen, hZa⟩ :=
    hFit G A c L Y₀' h a ha ha1 b hb hb1 U hU hUa hUQ hO2 hDM hcomm
  have hUYle : U ≤ Y := hUY.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hZY : Z ≤ Y := by
    refine hZgen.trans (iSup_le fun u => iSup_le fun hu => iSup_le fun _ => ?_)
    refine (Proof1711.inf_centralizer_conj_le (hUZ hu) a).trans ?_
    calc (Z ⊓ Subgroup.centralizer ({a} : Set G)).map (MulAut.conj u).toMonoidHom
        ≤ Y.map (MulAut.conj u).toMonoidHom := Subgroup.map_mono (hZa.trans hΔaY)
      _ = Y := Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hUYle hu))
  apply hZU
  have hZUZ : ⁅Z, U⁆ ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp hUZ
  have hZUO : ⁅Z, U⁆ ≤ CFSG.Open.pCoreOf 2 Y := by
    have hYO : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
    have h1 : ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hYO
    rw [Subgroup.commutator_comm] at h1
    exact (Subgroup.commutator_mono hZY hUY).trans h1
  exact le_bot_iff.mp ((le_inf hZUZ hZUO).trans
    (Proof1711.inf_eq_bot_of_odd hZodd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)).le)

theorem item1711S17_of (h179 : Item179S17) (hKM : Step1711KM) (hFit : Step1711Fit) :
    Item1711S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_11_of h (h179 G A c L Y₀ h) hKM hFit

end Item1711

end CFSG.RankThree.PartTwo.Sec17
