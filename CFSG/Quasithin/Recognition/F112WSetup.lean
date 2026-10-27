module

public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.F1Weak

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F112W

variable {G : Type*} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem relIndex_sup_eq_relIndex_inf {N B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (N : Set G)) : B.relIndex (N ⊔ B) = (N ⊓ B).relIndex N := by
  have h1 : (B ⊓ N).relIndex B * B.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
  have h2 : (B ⊓ N).relIndex N * N.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left
  have h3 : N.relIndex (N ⊔ B) = (B ⊓ N).relIndex B := by
    rw [sup_comm, F1.relIndex_sup_eq_of_le_normalizer hB]
    exact (Subgroup.inf_relIndex_left B N).symm
  have h4 : 0 < (B ⊓ N).relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((B ⊓ N).subgroupOf B)))
  have h5 : B.relIndex (N ⊔ B) = (B ⊓ N).relIndex N := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h1, ← h2, h3, mul_comm]
  rw [h5, inf_comm]

theorem isSylowTwoOf_sup {N B T : Subgroup G} (hB : B ≤ Subgroup.normalizer (N : Set G))
    (hT : IsSylowTwoOf T B) (hN : ¬ 2 ∣ (N ⊓ B).relIndex N) : IsSylowTwoOf T (N ⊔ B) := by
  refine F7.isSylowTwoOf_of_relIndex (hT.1.trans le_sup_right) hT.2.1 ?_
  rw [← Subgroup.relIndex_mul_relIndex T B (N ⊔ B) hT.1 le_sup_right,
    relIndex_sup_eq_relIndex_inf hB]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
  · exact F7.isSylowTwoOf_odd_relIndex hT hd
  · exact hN hd

omit [Finite G] in
theorem isSylowTwoOf_borelOf_left (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ L1) (borelOf L1 S) :=
  F7.isSylowTwoOf_mono_right h.hyp.h1.sylow (F1.sylow_le_borelOf L1 S) (F1.borelOf_le L1 S)

omit [Finite G] in
theorem isSylowTwoOf_borelOf_right (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ L2) (borelOf L2 S) :=
  isSylowTwoOf_borelOf_left h.symm

omit [Finite G] in
theorem not_two_dvd_relIndex_borelOf (h : Hyp111R L1 L2 S) :
    ¬ 2 ∣ (borelOf L1 S).relIndex L1 := by
  intro hd
  apply F7.isSylowTwoOf_odd_relIndex h.hyp.h1.sylow
  rw [← Subgroup.relIndex_mul_relIndex (S ⊓ L1) (borelOf L1 S) L1 (F1.sylow_le_borelOf L1 S)
    (F1.borelOf_le L1 S)]
  exact hd.mul_left _

theorem isSylowTwoOf_bigB (h : Hyp111R L1 L2 S) : IsSylowTwoOf S (bigB L1 L2 S) := by
  have hB2N1 : borelOf L2 S ≤ Subgroup.normalizer ((borelOf L1 S : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer_borelOf h
  have hB2S1 : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer_sylow h
  have hB1S2 : borelOf L1 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer_sylow h.symm
  have hB1S1 : borelOf L1 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer L1 S
  have hB2S2 : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer L2 S
  have hB1K : borelOf L1 S ≤ Subgroup.normalizer (((S ⊓ L1) ⊔ (S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hB1S1 hB1S2
  have hB2K : borelOf L2 S ≤ Subgroup.normalizer (((S ⊓ L1) ⊔ (S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hB2S1 hB2S2
  have hS1B1 : S ⊓ L1 ≤ borelOf L1 S := F1.sylow_le_borelOf L1 S
  have hS2B2 : S ⊓ L2 ≤ borelOf L2 S := F1.sylow_le_borelOf L2 S
  set K : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hKdef
  set M : Subgroup G := borelOf L1 S ⊔ K with hMdef
  set N : Subgroup G := borelOf L1 S ⊔ borelOf L2 S with hNdef
  have hKS : K ≤ S := sup_le inf_le_left inf_le_left
  have hKN : K ≤ N :=
    sup_le (hS1B1.trans le_sup_left) (hS2B2.trans le_sup_right)
  have hMN : M ≤ N := sup_le le_sup_left hKN
  have hKM : K ≤ M := le_sup_right
  have hB2M : borelOf L2 S ≤ Subgroup.normalizer (M : Set G) := F1.le_normalizer_sup hB2N1 hB2K
  have hNM : N = borelOf L2 S ⊔ M := by
    apply le_antisymm
    · exact sup_le (le_sup_left.trans le_sup_right) (le_sup_left)
    · exact sup_le le_sup_right hMN
  have hKM_odd : ¬ 2 ∣ K.relIndex M := by
    rw [hMdef, F1.relIndex_sup_eq_of_le_normalizer hB1K]
    have h1 : K.relIndex (borelOf L1 S) = (K ⊓ borelOf L1 S).relIndex (borelOf L1 S) :=
      (Subgroup.inf_relIndex_right K (borelOf L1 S)).symm
    rw [h1]
    intro hd
    refine F7.isSylowTwoOf_odd_relIndex (isSylowTwoOf_borelOf_left h) ?_
    have hS1 : S ⊓ L1 ≤ K ⊓ borelOf L1 S := le_inf le_sup_left hS1B1
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left _ hS1)
  have hMN_odd : ¬ 2 ∣ M.relIndex N := by
    rw [hNM, F1.relIndex_sup_eq_of_le_normalizer hB2M]
    have h1 : M.relIndex (borelOf L2 S) = (M ⊓ borelOf L2 S).relIndex (borelOf L2 S) :=
      (Subgroup.inf_relIndex_right M (borelOf L2 S)).symm
    rw [h1]
    intro hd
    refine F7.isSylowTwoOf_odd_relIndex (isSylowTwoOf_borelOf_right h) ?_
    have hS2 : S ⊓ L2 ≤ M ⊓ borelOf L2 S := le_inf (le_sup_right.trans hKM) hS2B2
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left _ hS2)
  have hKN_odd : ¬ 2 ∣ K.relIndex N := by
    rw [← Subgroup.relIndex_mul_relIndex K M N hKM hMN]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
    · exact hKM_odd hd
    · exact hMN_odd hd
  have hKsyl : IsSylowTwoOf K N :=
    F7.isSylowTwoOf_of_relIndex hKN (h.hyp.h1.pgroup.to_le hKS) hKN_odd
  have hSN : S ≤ Subgroup.normalizer (N : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_borelOf h.hyp.h1.normalizes)
      (F1.le_normalizer_borelOf h.hyp.h2.normalizes)
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  obtain ⟨S', hS', hSS'⟩ := F1.exists_isSylowTwoOf_ge hSB h.hyp.h1.pgroup
  have hle : S' ≤ S := by
    intro x hx
    have hxB : x ∈ N ⊔ S := hS'.1 hx
    obtain ⟨n, hn, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSN).mp hxB
    have hnS' : n ∈ S' := by
      have := S'.mul_mem hx (S'.inv_mem (hSS' hs))
      simpa using this
    have hKS' : K ≤ S' ⊓ N := le_inf (hKS.trans hSS') hKN
    have hKeq : K = S' ⊓ N :=
      F1.eq_of_isSylowTwoOf_le hKsyl inf_le_right (hS'.2.1.to_le inf_le_left) hKS'
    have hnK : n ∈ K := by
      rw [hKeq]
      exact ⟨hnS', hn⟩
    exact S.mul_mem (hKS hnK) hs
  have heq : S' = S := le_antisymm hle hSS'
  rw [heq] at hS'
  exact hS'

theorem isSylowTwoOf_parabolic (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := by
  refine isSylowTwoOf_sup (F1.bigB_le_normalizer_left h).1 (isSylowTwoOf_bigB h) ?_
  rw [F1.inf_bigB_eq_borelOf h]
  exact not_two_dvd_relIndex_borelOf h

theorem isSylowTwoOf_parabolic' (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) := by
  have := isSylowTwoOf_parabolic h.symm
  rwa [bigB_comm] at this

omit [Finite G] in
theorem parabolic_sup_parabolic' (L1 L2 S : Subgroup G) :
    (L2 ⊔ bigB L1 L2 S) ⊔ (L1 ⊔ bigB L1 L2 S) = L1 ⊔ L2 ⊔ S := by
  rw [sup_comm (L2 ⊔ bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S)]
  exact F1.parabolic_sup_parabolic L1 L2 S

theorem amalgamHyp_alpha (h : Hyp111R L1 L2 S) :
    AmalgamHyp (L1 ⊔ L2 ⊔ S) (L2 ⊔ bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S) S where
  gen := (parabolic_sup_parabolic' L1 L2 S).symm
  charTwo := by
    have := F1.parabolic_charTwo h.symm
    rwa [bigB_comm] at this
  sylow₁ := isSylowTwoOf_parabolic' h
  sylow₂ := isSylowTwoOf_parabolic h
  o2_trivial := h.hyp.o2

theorem amalgamHyp_beta (h : Hyp111R L1 L2 S) :
    AmalgamHyp (L1 ⊔ L2 ⊔ S) (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) S where
  gen := (F1.parabolic_sup_parabolic L1 L2 S).symm
  charTwo := F1.parabolic_charTwo h
  sylow₁ := isSylowTwoOf_parabolic h
  sylow₂ := isSylowTwoOf_parabolic' h
  o2_trivial := h.hyp.o2

omit [Finite G] in
theorem charTwo_beta (h : Hyp111R L1 L2 S) : CharTwo (L1 ⊔ bigB L1 L2 S) :=
  F1.parabolic_charTwo h

theorem coreIn_eq_bot_of_amalgamHyp {G₀ G₁ G₂ T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T) :
    coreIn (G₁ ⊓ G₂) G₀ = ⊥ := by
  set Y : Subgroup G := coreIn (G₁ ⊓ G₂) G₀ with hY
  have hYG0 : G₀ ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_coreIn _ _
  have hYB : Y ≤ G₁ ⊓ G₂ := coreIn_le_right _ _
  have hYP1 : Y ≤ G₁ := hYB.trans inf_le_left
  have hO2 : pCoreOf 2 Y = ⊥ := by
    have h1 : pCoreOf 2 Y ≤ pCoreOf 2 G₀ :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans (coreIn_le_left _ _))
        (le_normalizer_pCoreOf_of_le_normalizer hYG0) (pCoreOf_isPGroup 2 Y)
    rw [hyp.o2_trivial] at h1
    exact le_bot_iff.mp h1
  have hinf : pCoreOf 2 G₁ ⊓ Y ≤ ⊥ := by
    have := pCoreOf_inf_le hYP1
    rwa [hO2] at this
  have hcomm : ⁅Y, pCoreOf 2 G₁⁆ = ⊥ := by
    refine le_bot_iff.mp (le_trans (commutator_le_inf_of_normalizes ?_ ?_)
      (by rw [inf_comm]; exact hinf))
    · exact hYP1.trans (le_normalizer_pCoreOf 2 G₁)
    · exact ((pCoreOf_le 2 G₁).trans hyp.le₁).trans hYG0
  have hcent : Y ≤ Subgroup.centralizer (pCoreOf 2 G₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hYQ : Y ≤ pCoreOf 2 G₁ := fun x hx => hyp.charTwo ⟨hYP1 hx, hcent hx⟩
  exact le_bot_iff.mp ((le_inf hYQ le_rfl).trans hinf)

theorem perm3_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem perm3_conj_card : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 →
    3 ≤ (insert (1 : Equiv.Perm (Fin 3))
      (Finset.univ.image fun ρ : Equiv.Perm (Fin 3) => ρ⁻¹ * σ * ρ)).card := by
  decide

theorem perm3_order (τ : Equiv.Perm (Fin 3)) (hτ : ∃ k : ℕ, τ ^ (2 ^ k) = 1) : τ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hτ
  have h1 : orderOf τ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf τ ∣ 6 := by
    have := orderOf_dvd_natCard (G := Equiv.Perm (Fin 3)) τ
    rwa [perm3_card] at this
  have h3 : orderOf τ ∣ 2 := by
    have h4 : orderOf τ ∣ Nat.gcd (2 ^ k) 6 := Nat.dvd_gcd h1 h2
    have hg : Nat.gcd (2 ^ k) 6 ∣ 2 := by
      rcases k with _ | k
      · simp
      · rw [pow_succ]
        have e : Nat.gcd (2 ^ k * 2) 6 = 2 * Nat.gcd (2 ^ k) 3 := by
          rw [mul_comm (2 ^ k) 2, show (6 : ℕ) = 2 * 3 by norm_num, Nat.gcd_mul_left]
        rw [e]
        have e3 : Nat.gcd (2 ^ k) 3 = 1 := by
          apply Nat.Coprime.pow_left
          norm_num
        rw [e3]
    exact h4.trans hg
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem perm3_false {H : Subgroup (Equiv.Perm (Fin 3))} (hH : H ≠ ⊤)
    {τ σ : Equiv.Perm (Fin 3)} (hτ : τ ∈ H) (hτ1 : τ ≠ 1) (hτ2 : τ ^ 2 = 1) (hσ : σ ≠ 1)
    (hconj : ∀ ρ : Equiv.Perm (Fin 3), ρ⁻¹ * σ * ρ ∈ H) : False := by
  have hord : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
  have hdvd : Nat.card H ∣ 6 := perm3_card ▸ Subgroup.card_subgroup_dvd_card H
  have h2 : 2 ∣ Nat.card H := hord ▸ Subgroup.orderOf_dvd_natCard H hτ
  have hne6 : Nat.card H ≠ 6 := fun h => hH (Subgroup.eq_top_of_card_eq H (h.trans perm3_card.symm))
  have hle : (insert (1 : Equiv.Perm (Fin 3))
      (Finset.univ.image fun ρ : Equiv.Perm (Fin 3) => ρ⁻¹ * σ * ρ)).card ≤ Nat.card H := by
    classical
    have hsub : (insert (1 : Equiv.Perm (Fin 3))
        (Finset.univ.image fun ρ : Equiv.Perm (Fin 3) => ρ⁻¹ * σ * ρ)) ⊆
          Finset.univ.filter (· ∈ H) := by
      intro g hg
      rw [Finset.mem_insert, Finset.mem_image] at hg
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hg with rfl | ⟨ρ, -, rfl⟩
      · exact H.one_mem
      · exact hconj ρ
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h3 := perm3_conj_card σ hσ
  have h6 : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card H = c at *
  interval_cases c <;> omega

omit [Finite G] in
theorem centralizer_conjClosure_le_pCoreOf {L Z R : Subgroup G}
    (hperm : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) (hR : IsSylowTwoOf R L)
    (hRZ : R ≤ Subgroup.normalizer (Z : Set G))
    (hZO : pCoreOf 2 L ≤ Subgroup.centralizer (Z : Set G))
    (hZn : ¬ L ≤ Subgroup.normalizer (Z : Set G)) :
    L ⊓ Subgroup.centralizer (conjClosure Z L : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨e⟩ := hperm
  let φ : ↥L →* Equiv.Perm (Fin 3) :=
    (e : oTwoQuot ↥L →* Equiv.Perm (Fin 3)).comp (QuotientGroup.mk' (pCore 2 ↥L))
  have hφsurj : Function.Surjective φ := fun p => by
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hφker : ∀ x : ↥L, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
    intro x
    have hx : φ x = e (QuotientGroup.mk x) := rfl
    rw [hx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
  set N : Subgroup G := L ⊓ Subgroup.normalizer (Z : Set G) with hN
  set Nl : Subgroup ↥L := N.subgroupOf L with hNl
  set Hb : Subgroup (Equiv.Perm (Fin 3)) := Nl.map φ with hHb
  have hOn : ∀ y : G, y ∈ pCoreOf 2 L → y ∈ Subgroup.normalizer (Z : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (hZO hy)
  have hHbtop : Hb ≠ ⊤ := by
    intro htop
    apply hZn
    intro l hl
    have hmem : φ ⟨l, hl⟩ ∈ Hb := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hmem
    have hker1 : φ (⟨l, hl⟩ * n⁻¹) = 1 := by
      rw [map_mul, map_inv, hnl, mul_inv_cancel]
    have hO : l * (n : G)⁻¹ ∈ pCoreOf 2 L := (hφker _).mp hker1
    have hnN : (n : G) ∈ Subgroup.normalizer (Z : Set G) := (Subgroup.mem_subgroupOf.mp hn).2
    have e1 : l = (l * (n : G)⁻¹) * (n : G) := by group
    rw [e1]
    exact (Subgroup.normalizer (Z : Set G)).mul_mem (hOn _ hO) hnN
  have hex : ∃ r ∈ R, r ∉ pCoreOf 2 L := by
    by_contra hcon
    push Not at hcon
    have hRO : R ≤ pCoreOf 2 L := hcon
    have h1 : (pCoreOf 2 L).relIndex L ∣ R.relIndex L := Subgroup.relIndex_dvd_of_le_left L hRO
    have h2 : (pCoreOf 2 L).relIndex L = 6 := by
      have h3 : (pCoreOf 2 L).subgroupOf L = pCore 2 ↥L := by
        unfold pCoreOf Subgroup.subgroupOf
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      show ((pCoreOf 2 L).subgroupOf L).index = 6
      rw [h3, Subgroup.index, ← perm3_card]
      exact Nat.card_congr e.toEquiv
    rw [h2] at h1
    exact F7.isSylowTwoOf_odd_relIndex hR ((by norm_num : (2 : ℕ) ∣ 6).trans h1)
  intro x hx
  obtain ⟨hxL, hxV⟩ := hx
  by_contra hxO
  obtain ⟨r, hrR, hrO⟩ := hex
  have hrL : r ∈ L := hR.1 hrR
  have hτH : φ ⟨r, hrL⟩ ∈ Hb :=
    ⟨⟨r, hrL⟩, Subgroup.mem_subgroupOf.mpr ⟨hrL, hRZ hrR⟩, rfl⟩
  have hτ1 : φ ⟨r, hrL⟩ ≠ 1 := fun h => hrO ((hφker _).mp h)
  have hτ2 : φ ⟨r, hrL⟩ ^ 2 = 1 := by
    apply perm3_order
    obtain ⟨k, hk⟩ := hR.2.1 ⟨r, hrR⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨r, hrL⟩ : ↥L) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hσ : φ ⟨x, hxL⟩ ≠ 1 := fun h => hxO ((hφker _).mp h)
  refine perm3_false hHbtop hτH hτ1 hτ2 hσ fun ρ => ?_
  obtain ⟨l, rfl⟩ := hφsurj ρ
  have hmem : l⁻¹ * ⟨x, hxL⟩ * l ∈ Nl := by
    rw [hNl, Subgroup.mem_subgroupOf]
    refine ⟨(l⁻¹ * ⟨x, hxL⟩ * l).2, ?_⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hcomm := Subgroup.mem_centralizer_iff.mp hxV (l * z * (l : G)⁻¹) (mem_conjClosure l.2 hz)
    show z * ((l : G)⁻¹ * x * l) = (l : G)⁻¹ * x * l * z
    calc z * ((l : G)⁻¹ * x * l) = (l : G)⁻¹ * ((l * z * (l : G)⁻¹) * x) * l := by group
      _ = (l : G)⁻¹ * (x * (l * z * (l : G)⁻¹)) * l := by rw [hcomm]
      _ = (l : G)⁻¹ * x * l * z := by group
  exact ⟨_, hmem, by simp [map_mul, map_inv]⟩

theorem inf_eq_pCoreOf_of_quotient {P C N T : Subgroup G} (hT : IsSylowTwoOf T P)
    (hCP : C ≤ P) (hC : P ≤ Subgroup.normalizer (C : Set G))
    (hN : P ≤ Subgroup.normalizer (N : Set G))
    (hX : P ≤ Subgroup.normalizer ((T ⊔ N : Subgroup G) : Set G))
    (hCN : IsPGroup 2 ↥(C ⊓ N)) : T ⊓ C = pCoreOf 2 C := by
  have hsyl : IsSylowTwoOf (T ⊓ C) C := isSylowTwoOf_inf_normal hT hCP (hT.1.trans hC)
  set Y : Subgroup G := C ⊓ (T ⊔ N) with hY
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hT.1.trans hN
  have hY2 : IsPGroup 2 ↥Y := by
    intro y
    obtain ⟨y, hy⟩ := y
    obtain ⟨hyC, hyX⟩ := hy
    obtain ⟨t, ht, n, hn, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hTN).mp hyX
    have key : ∀ j : ℕ, ∃ m ∈ N, (t * n) ^ j = t ^ j * m := by
      intro j
      induction j with
      | zero => exact ⟨1, N.one_mem, by simp⟩
      | succ j ih =>
        obtain ⟨m, hm, hj⟩ := ih
        refine ⟨t⁻¹ * m * t * n, ?_, ?_⟩
        · refine N.mul_mem ?_ hn
          have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem ht)) m).mp hm
          simpa using this
        · rw [pow_succ, hj]
          group
    obtain ⟨k, hk⟩ := hT.2.1 ⟨t, ht⟩
    have htk : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, hm, hmk⟩ := key (2 ^ k)
    rw [htk, one_mul] at hmk
    have hmC : (t * n) ^ (2 ^ k) ∈ C ⊓ N := by
      refine ⟨C.pow_mem hyC _, ?_⟩
      rw [hmk]
      exact hm
    obtain ⟨j, hj⟩ := hCN ⟨(t * n) ^ (2 ^ k), hmC⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hYC : Y ≤ C := inf_le_left
  have hCY : C ≤ Subgroup.normalizer (Y : Set G) := fun c hc =>
    mem_normalizer_inf (hC (hCP hc)) (hX (hCP hc))
  have hTY : T ⊓ C ≤ Y := le_inf inf_le_right (inf_le_left.trans le_sup_left)
  have hEq : T ⊓ C = Y := F1.eq_of_isSylowTwoOf_le hsyl hYC hY2 hTY
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ hsyl.2.1
    rw [hEq]
    exact hCY
  · exact isSylowTwoOf_pCoreOf_le hsyl

theorem amalgamHypV_alpha (h : Hyp111R L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {Z : Subgroup G} (hZS : Z ≤ quasithinOmegaOneCenter S)
    (hperm : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hZn : ¬ L2 ≤ Subgroup.normalizer (Z : Set G)) :
    AmalgamHypV (L1 ⊔ L2 ⊔ S) (L2 ⊔ bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S) S
      (conjClosure Z (L2 ⊔ bigB L1 L2 S)) := by
  have hA := amalgamHyp_alpha h
  set P : Subgroup G := L2 ⊔ bigB L1 L2 S with hP
  have hSP : IsSylowTwoOf S P := hA.sylow₁
  have hF : P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P := hA.charTwo
  have hZc : Z ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
    refine hZS.trans ?_
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hZcent : S ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp (hZc.trans inf_le_right)
  have hO2L : pCoreOf 2 L2 ≤ S := by
    refine (isSylowTwoOf_pCoreOf_le h.hyp.h2.sylow).trans inf_le_left
  have hZO : pCoreOf 2 L2 ≤ Subgroup.centralizer (Z : Set G) := hO2L.trans hZcent
  have hSL2 : S ⊓ L2 ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans (hZcent.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨hVle, hVel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hSP.1 hSP.2.1
    (F7.isSylowTwoOf_odd_relIndex hSP) hF hZS
  have hred : IsTwoReducedIn P (conjClosure Z P) :=
    isTwoReducedIn_conjClosure_of_sylowIn hSP.1 hSP.2.1 (F7.isSylowTwoOf_odd_relIndex hSP) hF hZS
  have hPN : P ≤ Subgroup.normalizer ((conjClosure Z P : Subgroup G) : Set G) := hred.2.1
  have hCV : L2 ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ≤ pCoreOf 2 L2 := by
    refine le_trans ?_ (centralizer_conjClosure_le_pCoreOf hperm h.hyp.h2.sylow hSL2 hZO hZn)
    exact inf_le_inf_left L2 (Subgroup.centralizer_le (conjClosure_mono le_rfl le_sup_left))
  have hO2PL : pCoreOf 2 L2 ≤ pCoreOf 2 P := by
    have := F1.pCoreOf_le_pCoreOf_parabolic h.symm
    rwa [bigB_comm] at this
  have hPL2 : P ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h).2
  have hPN' : P ≤ Subgroup.normalizer ((pCoreOf 2 P ⊔ L2 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (le_normalizer_pCoreOf 2 P) hPL2
  have hX : P ≤ Subgroup.normalizer ((S ⊔ (pCoreOf 2 P ⊔ L2) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_right.trans le_sup_right :
        L2 ≤ S ⊔ (pCoreOf 2 P ⊔ L2)).trans Subgroup.le_normalizer
    · exact F1.le_normalizer_sup hSB (le_sup_right.trans hPN')
  have hQV : pCoreOf 2 P ≤ Subgroup.centralizer (conjClosure Z P : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVle hv).2 q hq).symm
  have hCN : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ⊓
      (pCoreOf 2 P ⊔ L2)) := by
    refine (pCoreOf_isPGroup 2 P).to_le ?_
    intro x hx
    obtain ⟨⟨hxP, hxC⟩, hxN⟩ := hx
    obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
      ((pCoreOf_le 2 P).trans hPL2)).mp hxN
    have hlC : l ∈ Subgroup.centralizer (conjClosure Z P : Set G) := by
      have := (Subgroup.centralizer (conjClosure Z P : Set G)).mul_mem
        ((Subgroup.centralizer _).inv_mem (hQV hq)) hxC
      simpa using this
    have hlL : l ∈ pCoreOf 2 L2 := hCV ⟨hl, hlC⟩
    exact (pCoreOf 2 P).mul_mem hq (hO2PL hlL)
  have hCP : P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) ≤ P := inf_le_left
  have hCnorm : P ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (conjClosure Z P : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hPN.trans (normalizer_le_normalizer_centralizer _))
  have hT := inf_eq_pCoreOf_of_quotient hSP hCP hCnorm hPN' hX hCN
  refine { toAmalgamHyp := hA, reduced := hred, cT := ?_ }
  rw [← hT, ← inf_assoc, inf_eq_left.mpr hSP.1]

end F112W

end CFSG.Quasithin
