module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.GoldschmidtF112SzB5Orb
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L : Subgroup G}

private theorem T_card_and_relIndex (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    Nat.card ↥T = 2 * Nat.card ↥(pCoreOf 2 L) ∧ T.relIndex L = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA.vS3
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card ↥(pCoreOf 2 L) := by
    have h : Nat.card ↥(pCoreOf 2 L) = Nat.card ↥(pCore 2 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  have h6 : Nat.card (oTwoQuot ↥L) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 L)
  have hL : Nat.card ↥L = 2 ^ (a + 1) * 3 := by
    rw [hcard, h6, ha, pow_succ]
    ring
  have hfac : (Nat.card ↥L).factorization 2 = a + 1 := by
    rw [hL, Nat.factorization_mul (by positivity) (by norm_num : (3 : ℕ) ≠ 0),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 3), add_zero]
  have hSyl : IsSylowTwoOf T L :=
    isSylowTwoOf_mono_right hA.hyp.sylow₂ (hA.inf_eq ▸ inf_le_left) hA.le
  obtain ⟨Sy, hSy⟩ := isSylowTwoOf_exists_sylow hSyl
  have hcardSy : Nat.card (Sy : Subgroup ↥L) = Nat.card ↥T := by
    rw [hSy]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv
  have hT : Nat.card ↥T = 2 * Nat.card ↥(pCoreOf 2 L) := by
    rw [← hcardSy, Sylow.card_eq_multiplicity, hfac, ha, pow_succ]
    ring
  refine ⟨hT, ?_⟩
  have hcardL : Nat.card ↥L = 3 * Nat.card ↥T := by
    rw [hL, hT, ha, pow_succ]
    ring
  have hTL : T ≤ L := hA.inf_eq ▸ inf_le_left
  have hmul := Subgroup.relIndex_mul_card T L
  rw [inf_eq_left.mpr hTL] at hmul
  rw [hcardL] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

theorem AmalgamS3.T_le_L (hA : AmalgamS3 G₀ G₁ G₂ T L) : T ≤ L :=
  hA.inf_eq ▸ inf_le_left

theorem AmalgamS3.isSylowTwoOf_L (hA : AmalgamS3 G₀ G₁ G₂ T L) : IsSylowTwoOf T L :=
  isSylowTwoOf_mono_right hA.hyp.sylow₂ (hA.T_le_L) hA.le

theorem AmalgamS3.pCoreOf_le_T (hA : AmalgamS3 G₀ G₁ G₂ T L) : pCoreOf 2 G₂ ≤ T :=
  hA.pCoreOf_eq ▸ isSylowTwoOf_pCoreOf_le (hA.isSylowTwoOf_L)

theorem AmalgamS3.relIndex_pCoreOf_T (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    (pCoreOf 2 G₂).relIndex T = 2 := by
  rw [show pCoreOf 2 G₂ = pCoreOf 2 L from hA.pCoreOf_eq.symm]
  have hQT : pCoreOf 2 L ≤ T := isSylowTwoOf_pCoreOf_le (hA.isSylowTwoOf_L)
  have hmul := Subgroup.relIndex_mul_card (pCoreOf 2 L) T
  rw [inf_eq_left.mpr hQT] at hmul
  rw [(T_card_and_relIndex hA).1] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul

theorem AmalgamS3.relIndex_inf_G₂ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    (G₁ ⊓ G₂).relIndex G₂ = 3 := by
  have hTrel : T.relIndex L = 3 := (T_card_and_relIndex hA).2
  have hsup : (G₁ ⊓ G₂) ⊔ L = G₂ := by rw [sup_comm, hA.sup_eq]
  have hnorm : G₁ ⊓ G₂ ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans hA.le_normalizer
  have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := G₁ ⊓ G₂) (K := L) hnorm).1
  rw [hsup] at h
  rw [h]
  have hinf : (G₁ ⊓ G₂) ⊓ L = T := by
    rw [← hA.inf_eq]
    ext x
    constructor
    · rintro ⟨⟨hx1, _⟩, hxL⟩
      exact ⟨hxL, hx1⟩
    · rintro ⟨hxL, hx1⟩
      have hxT : x ∈ T := hA.inf_eq ▸ ⟨hxL, hx1⟩
      exact ⟨⟨hx1, (hA.hyp.T_le hxT).2⟩, hxL⟩
  rw [hinf, hTrel]

theorem AmalgamS3.inf_le_normalizer_T (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    G₁ ⊓ G₂ ≤ Subgroup.normalizer (T : Set G) := by
  have hL : G₁ ⊓ G₂ ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans hA.le_normalizer
  have hG₁ : G₁ ⊓ G₂ ≤ Subgroup.normalizer (G₁ : Set G) :=
    inf_le_left.trans Subgroup.le_normalizer
  have h := le_normalizer_inf hL hG₁
  rwa [hA.inf_eq] at h

theorem AmalgamS3.inf_normalizer_T (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    G₂ ⊓ Subgroup.normalizer (T : Set G) = G₁ ⊓ G₂ := by
  set N := G₂ ⊓ Subgroup.normalizer (T : Set G) with hNdef
  have hle1 : G₁ ⊓ G₂ ≤ N := le_inf inf_le_right hA.inf_le_normalizer_T
  have hle2 : N ≤ G₂ := inf_le_left
  have hrel : (G₁ ⊓ G₂).relIndex N * N.relIndex G₂ = (G₁ ⊓ G₂).relIndex G₂ :=
    Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) N G₂ hle1 hle2
  rw [hA.relIndex_inf_G₂] at hrel
  refine le_antisymm ?_ hle1
  have hi : (G₁ ⊓ G₂).relIndex N ∣ 3 := ⟨N.relIndex G₂, hrel.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hi with hi1 | hi3
  · exact Subgroup.relIndex_eq_one.mp hi1
  · exfalso
    have hj1 : N.relIndex G₂ = 1 := by
      rw [hi3] at hrel
      omega
    have hNG₂ : G₂ ≤ N := Subgroup.relIndex_eq_one.mp hj1
    have hEq : N = G₂ := le_antisymm hle2 hNG₂
    have hNG₂norm : G₂ ≤ Subgroup.normalizer (T : Set G) := by
      have hNnorm : N ≤ Subgroup.normalizer (T : Set G) := inf_le_right
      rwa [hEq] at hNnorm
    have hTQ : T ≤ pCoreOf 2 G₂ :=
      le_pCoreOf_of_le_normalizer 2 hA.hyp.sylow₂.1 hNG₂norm hA.hyp.sylow₂.2.1
    have hQT : pCoreOf 2 G₂ ≤ T := hA.pCoreOf_le_T
    have heqT : T = pCoreOf 2 G₂ := le_antisymm hTQ hQT
    have h2 := hA.relIndex_pCoreOf_T
    rw [← heqT, Subgroup.relIndex_self] at h2
    exact absurd h2 (by norm_num)

theorem AmalgamS3.le_L_of_isPGroup (hA : AmalgamS3 G₀ G₁ G₂ T L) {P : Subgroup G}
    (hP : P ≤ G₂) (h2 : IsPGroup 2 P) : P ≤ L := by
  obtain ⟨x, hxG₂, hPx⟩ := isSylowTwoOf_exists_conj_le hA.hyp.sylow₂ hP h2
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hA.le_normalizer hxG₂
  have hxL : conjSub x L = L := conjSub_eq_of_mem_normalizer hxN
  rw [← hxL]
  exact hPx.trans (conjSub_mono x hA.T_le_L)

private theorem pCoreOf_le_conjSub_T (hA : AmalgamS3 G₀ G₁ G₂ T L) {g : G} (hg : g ∈ G₂) :
    pCoreOf 2 G₂ ≤ conjSub g T := by
  have hQ : conjSub g (pCoreOf 2 G₂) = pCoreOf 2 G₂ := by
    rw [← pCoreOf_conjSub, conjSub_eq_of_mem hg]
  rw [← hQ]
  exact conjSub_mono g hA.pCoreOf_le_T

private theorem conjSub_T_le_G₂ (hA : AmalgamS3 G₀ G₁ G₂ T L) {g : G} (hg : g ∈ G₂) :
    conjSub g T ≤ G₂ := by
  have h : conjSub g T ≤ conjSub g G₂ := conjSub_mono g hA.hyp.sylow₂.1
  rwa [conjSub_eq_of_mem hg] at h

private theorem relIndex_pCoreOf_conjSub_T (hA : AmalgamS3 G₀ G₁ G₂ T L) {g : G}
    (hg : g ∈ G₂) : (pCoreOf 2 G₂).relIndex (conjSub g T) = 2 := by
  have hQ : conjSub g (pCoreOf 2 G₂) = pCoreOf 2 G₂ := by
    rw [← pCoreOf_conjSub, conjSub_eq_of_mem hg]
  rw [← hQ]
  have hmap : (conjSub g (pCoreOf 2 G₂)).relIndex (conjSub g T) =
      (pCoreOf 2 G₂).relIndex T :=
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _
      (MulEquiv.injective (MulAut.conj g))
  rw [hmap]
  exact hA.relIndex_pCoreOf_T

theorem AmalgamS3.conjSub_inf_conjSub (hA : AmalgamS3 G₀ G₁ G₂ T L) {k k' : G} (hk : k ∈ G₂)
    (hk' : k' ∈ G₂) (hne : conjSub k T ≠ conjSub k' T) :
    conjSub k T ⊓ conjSub k' T = pCoreOf 2 G₂ := by
  have hQle : pCoreOf 2 G₂ ≤ conjSub k T ⊓ conjSub k' T :=
    le_inf (pCoreOf_le_conjSub_T hA hk) (pCoreOf_le_conjSub_T hA hk')
  let I : Subgroup G := conjSub k T ⊓ conjSub k' T
  have hQleI : pCoreOf 2 G₂ ≤ I := hQle
  have hrel : (pCoreOf 2 G₂).relIndex I * I.relIndex (conjSub k T) =
      (pCoreOf 2 G₂).relIndex (conjSub k T) :=
    Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₂) I (conjSub k T) hQleI inf_le_left
  rw [relIndex_pCoreOf_conjSub_T hA hk] at hrel
  have hi_dvd : (pCoreOf 2 G₂).relIndex I ∣ 2 := ⟨I.relIndex (conjSub k T), hrel.symm⟩
  by_cases hi1 : (pCoreOf 2 G₂).relIndex I = 1
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp hi1) hQle
  · exfalso
    rcases (Nat.dvd_prime Nat.prime_two).mp hi_dvd with hi1' | hi2
    · exact hi1 hi1'
    · have hj1 : I.relIndex (conjSub k T) = 1 := by
        rw [hi2] at hrel
        omega
      have hTkleI : conjSub k T ≤ I := Subgroup.relIndex_eq_one.mp hj1
      have hTkleTk' : conjSub k T ≤ conjSub k' T := hTkleI.trans inf_le_right
      have hcard : Nat.card (conjSub k T) = Nat.card (conjSub k' T) := by
        rw [CosetGeom.card_conjSub k T, CosetGeom.card_conjSub k' T]
      have heq : conjSub k T = conjSub k' T :=
        Subgroup.eq_of_le_of_card_ge hTkleTk' (le_of_eq hcard.symm)
      exact hne heq

private theorem ncard_nbrs_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    (nbrs (γ₁ G₀ G₁ G₂)).ncard = 3 := by
  have hE : stab (γ₁ G₀ G₁ G₂) ≤ G₀ := stab_le _
  have horb : MulAction.orbit ↥((stab (γ₁ G₀ G₁ G₂)).comap G₀.subtype)
      (γ₀ G₀ G₁ G₂) = nbrs (γ₁ G₀ G₁ G₂) := by
    ext w
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      have h1 : g • γ₁ G₀ G₁ G₂ = γ₁ G₀ G₁ G₂ := smul_eq_of_mem_stab hg
      have h2 := (smul_adj g).mpr
        (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm
      rwa [h1] at h2
    · intro hw
      obtain ⟨g, hg, hgw⟩ := stab_transitive_on_nbrs
        (show γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) from
          (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm) hw
      exact ⟨⟨g, hg⟩, hgw⟩
  rw [← horb, F112SzB5.ncard_orbit_comap hE (γ₀ G₀ G₁ G₂), stab_γ₀ hA.hyp.le₁,
    stab_γ₁ hA.hyp.le₂]
  rw [← Subgroup.inf_relIndex_right G₁ G₂]
  exact hA.relIndex_inf_G₂

private theorem neighbour_repr (hA : AmalgamS3 G₀ G₁ G₂ T L) {ε : CosetGeom G₀ G₁ G₂}
    (hε : ε ∈ nbrs (γ₁ G₀ G₁ G₂)) :
    ∃ k : ↥G₀, (k : G) ∈ G₂ ∧ ε = k • (γ₀ G₀ G₁ G₂) := by
  obtain ⟨k, hk, hkε⟩ := stab_transitive_on_nbrs
    (show γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) from
      (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm) hε
  refine ⟨k, ?_, hkε.symm⟩
  rwa [stab_γ₁ hA.hyp.le₂] at hk

private theorem inf_stab_eq_conjSub (hA : AmalgamS3 G₀ G₁ G₂ T L) {k : ↥G₀}
    (hk : (k : G) ∈ G₂) :
    stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂) = conjSub (k : G) (G₁ ⊓ G₂) := by
  rw [stab_γ₁ hA.hyp.le₂, stab_smul, stab_γ₀ hA.hyp.le₁]
  have hkG₂ : conjSub (k : G) G₂ = G₂ := conjSub_eq_of_mem hk
  calc G₂ ⊓ conjSub (k : G) G₁
      = conjSub (k : G) G₂ ⊓ conjSub (k : G) G₁ := by rw [hkG₂]
    _ = conjSub (k : G) (G₂ ⊓ G₁) := (conjSub_inf _ _ _).symm
    _ = conjSub (k : G) (G₁ ⊓ G₂) := by rw [inf_comm]

private theorem le_conjSub_T_of_isPGroup (hA : AmalgamS3 G₀ G₁ G₂ T L) {k : ↥G₀}
    (hk : (k : G) ∈ G₂) {P : Subgroup G}
    (hP : P ≤ stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂)) (h2 : IsPGroup 2 P) :
    P ≤ conjSub (k : G) T := by
  have hE : stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂) =
      conjSub (k : G) (G₁ ⊓ G₂) := inf_stab_eq_conjSub hA hk
  have hSyl : IsSylowTwoOf (conjSub (k : G) T)
      (stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂)) := by
    rw [hE]
    exact isSylowTwoOf_conj hA.hyp.sylow_inf (k : G)
  have hNorm : stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂) ≤
      Subgroup.normalizer (conjSub (k : G) T : Set G) := by
    rw [hE]
    exact conjSub_le_normalizer (g := (k : G)) hA.inf_le_normalizer_T
  obtain ⟨x, hxE, hPx⟩ := isSylowTwoOf_exists_conj_le hSyl hP h2
  have hxN : x ∈ Subgroup.normalizer (conjSub (k : G) T : Set G) := hNorm hxE
  have hx : conjSub x (conjSub (k : G) T) = conjSub (k : G) T :=
    conjSub_eq_of_mem_normalizer hxN
  rwa [hx] at hPx

private theorem exists_two_elt_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) {k : ↥G₀}
    (hk : (k : G) ∈ G₂) :
    ∃ t ∈ stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂),
      (∃ n : ℕ, t ^ 2 ^ n = 1) ∧ t ∉ pCoreOf 2 G₂ := by
  have hle : pCoreOf 2 G₂ ≤ conjSub (k : G) T := pCoreOf_le_conjSub_T hA hk
  have hne : ¬ conjSub (k : G) T ≤ pCoreOf 2 G₂ := by
    intro hle'
    have heq : conjSub (k : G) T = pCoreOf 2 G₂ := le_antisymm hle' hle
    have h2 := relIndex_pCoreOf_conjSub_T hA hk
    rw [← heq, Subgroup.relIndex_self] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨t, htTk, htQ⟩ := Set.not_subset.mp hne
  refine ⟨t, ?_, ?_, htQ⟩
  · rw [inf_stab_eq_conjSub hA hk]
    exact (conjSub_mono (k : G) hA.hyp.T_le) htTk
  · obtain ⟨n, hn⟩ :=
      (isPGroup_conjSub (g := (k : G)) (H := T) hA.hyp.sylow₂.2.1) ⟨t, htTk⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

private theorem nbrs_eq_triple (hA : AmalgamS3 G₀ G₁ G₂ T L)
    {a b c : CosetGeom G₀ G₁ G₂} (ha : a ∈ nbrs (γ₁ G₀ G₁ G₂))
    (hb : b ∈ nbrs (γ₁ G₀ G₁ G₂)) (hc : c ∈ nbrs (γ₁ G₀ G₁ G₂))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    nbrs (γ₁ G₀ G₁ G₂) = {a, b, c} := by
  have hsub : ({a, b, c} : Set (CosetGeom G₀ G₁ G₂)) ⊆ nbrs (γ₁ G₀ G₁ G₂) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have h3 : ({a, b, c} : Set (CosetGeom G₀ G₁ G₂)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hle : (nbrs (γ₁ G₀ G₁ G₂)).ncard ≤ ({a, b, c} : Set _).ncard := by
    have h := ncard_nbrs_γ₁ hA
    omega
  exact (Set.eq_of_subset_of_ncard_le hsub hle).symm

private theorem exists_third_nbrs (hA : AmalgamS3 G₀ G₁ G₂ T L)
    {ε ε' : CosetGeom G₀ G₁ G₂} (hne : ε ≠ ε') :
    ∃ ε'' ∈ nbrs (γ₁ G₀ G₁ G₂), ε'' ≠ ε ∧ ε'' ≠ ε' := by
  have hpair : ({ε, ε'} : Set (CosetGeom G₀ G₁ G₂)).ncard = 2 := Set.ncard_pair hne
  have hlt : ({ε, ε'} : Set (CosetGeom G₀ G₁ G₂)).ncard <
      (nbrs (γ₁ G₀ G₁ G₂)).ncard := by
    have h := ncard_nbrs_γ₁ hA
    omega
  obtain ⟨ε'', hε''mem, hε''not⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  refine ⟨ε'', hε''mem, ?_, ?_⟩
  · intro h
    exact hε''not (by simp [h])
  · intro h
    exact hε''not (by simp [h])

private theorem smul_ne_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    ∀ f : ↥G₀, (f : G) ∈ stab (γ₁ G₀ G₁ G₂) →
      (∃ n : ℕ, (f : G) ^ 2 ^ n = 1) → (f : G) ∉ pCoreOf 2 G₂ →
      ∀ ε ∈ nbrs (γ₁ G₀ G₁ G₂), f • ε = ε →
      ∀ ε' ∈ nbrs (γ₁ G₀ G₁ G₂), ε' ≠ ε → f • ε' ≠ ε' := by
  intro f hf hf2 hfQ ε hε hfix ε' hε' hne hfix'
  obtain ⟨k, hk, rfl⟩ := neighbour_repr hA hε
  obtain ⟨k', hk', rfl⟩ := neighbour_repr hA hε'
  have hfzp : IsPGroup 2 (Subgroup.zpowers (f : G)) := by
    obtain ⟨n, hn⟩ := hf2
    have hd : orderOf (f : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine IsPGroup.of_card (n := m) ?_
    rw [Nat.card_zpowers, hm]
  have hfInf : Subgroup.zpowers (f : G) ≤
      stab (γ₁ G₀ G₁ G₂) ⊓ stab (k • γ₀ G₀ G₁ G₂) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hf, mem_stab_of_smul_eq hfix⟩
  have hfTk : (f : G) ∈ conjSub (k : G) T :=
    le_conjSub_T_of_isPGroup hA hk hfInf hfzp (Subgroup.mem_zpowers (f : G))
  have hfInf' : Subgroup.zpowers (f : G) ≤
      stab (γ₁ G₀ G₁ G₂) ⊓ stab (k' • γ₀ G₀ G₁ G₂) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hf, mem_stab_of_smul_eq hfix'⟩
  have hfTk' : (f : G) ∈ conjSub (k' : G) T :=
    le_conjSub_T_of_isPGroup hA hk' hfInf' hfzp (Subgroup.mem_zpowers (f : G))
  have hTkne : conjSub (k : G) T ≠ conjSub (k' : G) T := by
    intro heq
    have hkk'G₂ : (k : G)⁻¹ * (k' : G) ∈ G₂ := G₂.mul_mem (G₂.inv_mem hk) hk'
    have hconj : conjSub ((k : G)⁻¹ * (k' : G)) T = T := by
      rw [conjSub_mul, ← heq, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hN : (k : G)⁻¹ * (k' : G) ∈ Subgroup.normalizer (T : Set G) :=
      mem_normalizer_of_conjSub_eq hconj
    have hinf : (k : G)⁻¹ * (k' : G) ∈ G₁ ⊓ G₂ := by
      rw [← hA.inf_normalizer_T]
      exact ⟨hkk'G₂, hN⟩
    have hmemStab : (((k⁻¹ * k' : ↥G₀)) : G) ∈ stab (γ₀ G₀ G₁ G₂) := by
      rw [stab_γ₀ hA.hyp.le₁]
      simpa using hinf.1
    have hsmul : (k⁻¹ * k') • (γ₀ G₀ G₁ G₂) = γ₀ G₀ G₁ G₂ :=
      smul_eq_of_mem_stab hmemStab
    have hk'k : k' • (γ₀ G₀ G₁ G₂) = k • (γ₀ G₀ G₁ G₂) := by
      calc k' • γ₀ G₀ G₁ G₂ = (k * (k⁻¹ * k')) • γ₀ G₀ G₁ G₂ := by group
        _ = k • ((k⁻¹ * k') • γ₀ G₀ G₁ G₂) := mul_smul k (k⁻¹ * k') (γ₀ G₀ G₁ G₂)
        _ = k • γ₀ G₀ G₁ G₂ := by rw [hsmul]
    exact hne hk'k
  have hfQ' : (f : G) ∈ pCoreOf 2 G₂ := by
    have hmem : (f : G) ∈ conjSub (k : G) T ⊓ conjSub (k' : G) T := ⟨hfTk, hfTk'⟩
    rwa [hA.conjSub_inf_conjSub hk hk' hTkne] at hmem
  exact hfQ hfQ'

private theorem exists_swap_fix_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) {k : ↥G₀}
    (hk : (k : G) ∈ G₂) {ε₁ ε₂ : CosetGeom G₀ G₁ G₂}
    (h₁ : ε₁ ∈ nbrs (γ₁ G₀ G₁ G₂)) (h₂ : ε₂ ∈ nbrs (γ₁ G₀ G₁ G₂))
    (hne1 : ε₁ ≠ k • γ₀ G₀ G₁ G₂) (hne2 : ε₂ ≠ k • γ₀ G₀ G₁ G₂) (h12 : ε₁ ≠ ε₂) :
    ∃ g : ↥G₀, (g : G) ∈ stab (γ₁ G₀ G₁ G₂) ∧
      g • (k • γ₀ G₀ G₁ G₂) = k • γ₀ G₀ G₁ G₂ ∧
      g • ε₁ = ε₂ ∧ g • ε₂ = ε₁ := by
  obtain ⟨t, ht, ht2, htQ⟩ := exists_two_elt_γ₁ hA hk
  have htG₂ : t ∈ G₂ := by
    have h := ht.1
    rwa [stab_γ₁ hA.hyp.le₂] at h
  let t₀ : ↥G₀ := ⟨t, hA.hyp.le₂ htG₂⟩
  have ht₀stab : (t₀ : G) ∈ stab (γ₁ G₀ G₁ G₂) := by
    rw [stab_γ₁ hA.hyp.le₂]
    exact htG₂
  have ht₀γ₁ : t₀ • (γ₁ G₀ G₁ G₂) = γ₁ G₀ G₁ G₂ := smul_eq_of_mem_stab ht₀stab
  have htfix : t₀ • (k • γ₀ G₀ G₁ G₂) = k • γ₀ G₀ G₁ G₂ := by
    apply smul_eq_of_mem_stab
    exact ht.2
  have hkstab : (k : G) ∈ stab (γ₁ G₀ G₁ G₂) := by
    rwa [stab_γ₁ hA.hyp.le₂]
  have hkγ₁ : k • (γ₁ G₀ G₁ G₂) = γ₁ G₀ G₁ G₂ := smul_eq_of_mem_stab hkstab
  have hε₀mem : k • γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    rw [← hkγ₁]
    exact (smul_adj k).mpr
      (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm
  have htriple : nbrs (γ₁ G₀ G₁ G₂) = {k • γ₀ G₀ G₁ G₂, ε₁, ε₂} :=
    nbrs_eq_triple hA hε₀mem h₁ h₂ (Ne.symm hne1) (Ne.symm hne2) h12
  have htε₁_mem : t₀ • ε₁ ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    rw [← ht₀γ₁]
    exact (smul_adj t₀).mpr h₁
  have htε₁_ne_self : t₀ • ε₁ ≠ ε₁ :=
    smul_ne_γ₁ hA t₀ ht₀stab (by simpa using ht2) (by simpa using htQ)
      (k • γ₀ G₀ G₁ G₂) hε₀mem htfix ε₁ h₁ hne1
  have htε₁_ne_other : t₀ • ε₁ ≠ k • γ₀ G₀ G₁ G₂ := by
    intro h
    exact hne1 (smul_left_cancel t₀ (h.trans htfix.symm))
  have htε₁ : t₀ • ε₁ = ε₂ := by
    have hmem : t₀ • ε₁ ∈ ({k • γ₀ G₀ G₁ G₂, ε₁, ε₂} : Set _) := by
      rw [← htriple]
      exact htε₁_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h htε₁_ne_other
    · exact absurd h htε₁_ne_self
    · exact h
  have htε₂_mem : t₀ • ε₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    rw [← ht₀γ₁]
    exact (smul_adj t₀).mpr h₂
  have htε₂_ne_self : t₀ • ε₂ ≠ ε₂ :=
    smul_ne_γ₁ hA t₀ ht₀stab (by simpa using ht2) (by simpa using htQ)
      (k • γ₀ G₀ G₁ G₂) hε₀mem htfix ε₂ h₂ hne2
  have htε₂_ne_other : t₀ • ε₂ ≠ k • γ₀ G₀ G₁ G₂ := by
    intro h
    exact hne2 (smul_left_cancel t₀ (h.trans htfix.symm))
  have htε₂ : t₀ • ε₂ = ε₁ := by
    have hmem : t₀ • ε₂ ∈ ({k • γ₀ G₀ G₁ G₂, ε₁, ε₂} : Set _) := by
      rw [← htriple]
      exact htε₂_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h htε₂_ne_other
    · exact h
    · exact absurd h htε₂_ne_self
  exact ⟨t₀, ht₀stab, htfix, htε₁, htε₂⟩

private theorem exists_swap_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    ∀ ε₁ ∈ nbrs (γ₁ G₀ G₁ G₂), ∀ ε₂ ∈ nbrs (γ₁ G₀ G₁ G₂), ε₁ ≠ ε₂ →
      ∃ g : ↥G₀, (g : G) ∈ stab (γ₁ G₀ G₁ G₂) ∧ g • ε₁ = ε₂ ∧ g • ε₂ = ε₁ := by
  intro ε₁ h₁ ε₂ h₂ h12
  obtain ⟨ε, hε, hεne1, hεne2⟩ := exists_third_nbrs hA h12
  obtain ⟨k, hk, hkε⟩ := neighbour_repr hA hε
  obtain ⟨g, hgstab, -, hg1, hg2⟩ :=
    exists_swap_fix_γ₁ hA hk h₁ h₂
      (by rw [← hkε]; exact Ne.symm hεne1)
      (by rw [← hkε]; exact Ne.symm hεne2) h12
  exact ⟨g, hgstab, hg1, hg2⟩

private theorem transitive_of_normal_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    ∀ N : Subgroup G, N ≤ stab (γ₁ G₀ G₁ G₂) →
      stab (γ₁ G₀ G₁ G₂) ≤ Subgroup.normalizer (N : Set G) →
      (∃ f ∈ N, (∃ n : ℕ, f ^ 2 ^ n = 1) ∧ f ∉ pCoreOf 2 G₂) →
      ∀ ε ∈ nbrs (γ₁ G₀ G₁ G₂), ∀ ε' ∈ nbrs (γ₁ G₀ G₁ G₂),
        ∃ g : ↥G₀, (g : G) ∈ N ∧ g • ε = ε' := by
  intro N hN hNnorm ⟨f, hfN, hf2, hfQ⟩ ε hε ε' hε'
  classical
  by_cases hεε' : ε = ε'
  · exact ⟨1, N.one_mem, by simp [hεε']⟩
  have hfG₂ : f ∈ G₂ := by
    have h := hN hfN
    rwa [stab_γ₁ hA.hyp.le₂] at h
  have hfzp : IsPGroup 2 (Subgroup.zpowers f) := by
    obtain ⟨n, hn⟩ := hf2
    have hd : orderOf f ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine IsPGroup.of_card (n := m) ?_
    rw [Nat.card_zpowers, hm]
  obtain ⟨x, hxG₂, hxle⟩ := isSylowTwoOf_exists_conj_le hA.hyp.sylow₂
    (Subgroup.zpowers_le.mpr hfG₂) hfzp
  let f₀ : ↥G₀ := ⟨f, hA.hyp.le₂ hfG₂⟩
  let x₀ : ↥G₀ := ⟨x, hA.hyp.le₂ hxG₂⟩
  have hTxStab : conjSub x T ≤ stab (x₀ • γ₀ G₀ G₁ G₂) := by
    rw [stab_smul, stab_γ₀ hA.hyp.le₁]
    exact conjSub_mono x (hA.hyp.T_le.trans inf_le_left)
  have hfε₀ : f₀ • (x₀ • γ₀ G₀ G₁ G₂) = x₀ • γ₀ G₀ G₁ G₂ := by
    apply smul_eq_of_mem_stab
    exact hTxStab (hxle (Subgroup.mem_zpowers f))
  have hx₀stab : (x₀ : G) ∈ stab (γ₁ G₀ G₁ G₂) := by
    rw [stab_γ₁ hA.hyp.le₂]
    exact hxG₂
  have hx₀γ₁ : x₀ • (γ₁ G₀ G₁ G₂) = γ₁ G₀ G₁ G₂ := smul_eq_of_mem_stab hx₀stab
  have hε₀mem : x₀ • γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    rw [← hx₀γ₁]
    exact (smul_adj x₀).mpr
      (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm
  obtain ⟨ε'', hε''mem, hε''ne1, hε''ne2⟩ := exists_third_nbrs hA hεε'
  obtain ⟨g, hgstab, hgε₀⟩ := stab_transitive_on_nbrs hε₀mem hε''mem
  have hgG₂ : (g : G) ∈ G₂ := by
    have h := hgstab
    rwa [stab_γ₁ hA.hyp.le₂] at h
  let h : ↥G₀ := g * f₀ * g⁻¹
  have hhN : (h : G) ∈ N := by
    have hgn : (g : G) ∈ Subgroup.normalizer (N : Set G) := hNnorm hgstab
    have hconj := (Subgroup.mem_normalizer_iff.mp hgn f).mp hfN
    simpa [h, f₀] using hconj
  have hhstab : (h : G) ∈ stab (γ₁ G₀ G₁ G₂) := hN hhN
  have hh2 : ∃ n : ℕ, (h : G) ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hf2
    refine ⟨n, ?_⟩
    have hcoe : (h : G) = (g : G) * f * (g : G)⁻¹ := rfl
    rw [hcoe, conj_pow, hn, mul_one, mul_inv_cancel]
  have hhQ : (h : G) ∉ pCoreOf 2 G₂ := by
    intro hmem
    apply hfQ
    have hg'inv : (g : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 G₂ : Set G) :=
      (le_normalizer_pCoreOf 2 G₂) (G₂.inv_mem hgG₂)
    have hQinv : conjSub (g : G)⁻¹ (pCoreOf 2 G₂) = pCoreOf 2 G₂ :=
      conjSub_eq_of_mem_normalizer hg'inv
    have hconj : f ∈ conjSub (g : G)⁻¹ (pCoreOf 2 G₂) := by
      rw [mem_conjSub]
      simpa [h, mul_assoc] using hmem
    rwa [hQinv] at hconj
  have hhfix : h • ε'' = ε'' := by
    rw [← hgε₀]
    calc h • (g • (x₀ • γ₀ G₀ G₁ G₂))
        = (g * f₀ * g⁻¹) • (g • (x₀ • γ₀ G₀ G₁ G₂)) := rfl
      _ = g • (f₀ • (g⁻¹ • (g • (x₀ • γ₀ G₀ G₁ G₂)))) := by
            rw [mul_smul, mul_smul]
      _ = g • (f₀ • (x₀ • γ₀ G₀ G₁ G₂)) := by rw [inv_smul_smul]
      _ = g • (x₀ • γ₀ G₀ G₁ G₂) := by rw [hfε₀]
  have hmoves : h • ε ≠ ε :=
    smul_ne_γ₁ hA h hhstab hh2 hhQ ε'' hε''mem hhfix ε hε (Ne.symm hε''ne1)
  have hmoves' : h • ε' ≠ ε' :=
    smul_ne_γ₁ hA h hhstab hh2 hhQ ε'' hε''mem hhfix ε' hε' (Ne.symm hε''ne2)
  have htriple : nbrs (γ₁ G₀ G₁ G₂) = {ε, ε', ε''} :=
    nbrs_eq_triple hA hε hε' hε''mem hεε' (Ne.symm hε''ne1) (Ne.symm hε''ne2)
  have hhγ₁ : h • (γ₁ G₀ G₁ G₂) = γ₁ G₀ G₁ G₂ := smul_eq_of_mem_stab hhstab
  have hhε_mem : h • ε ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    rw [← hhγ₁]
    exact (smul_adj h).mpr hε
  have hmem : h • ε ∈ ({ε, ε', ε''} : Set _) := by
    rw [← htriple]
    exact hhε_mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hhε : h • ε = ε' := by
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 hmoves
    · exact h1
    · exact absurd (smul_left_cancel h (h1.trans hhfix.symm)) (Ne.symm hε''ne1)
  exact ⟨h, hhN, hhε⟩

private theorem le_pCoreOf_of_le_ballStab_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) {P : Subgroup G}
    (hP : P ≤ ballStab 1 (γ₁ G₀ G₁ G₂)) (h2 : IsPGroup 2 P) :
    P ≤ pCoreOf 2 (stab (γ₁ G₀ G₁ G₂)) := by
  rw [stab_γ₁ hA.hyp.le₂]
  have hK : ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ :=
    (ballStab_one_γ₁ hA.hyp.gen).1
  have hP' : P ≤ coreIn (G₁ ⊓ G₂) G₂ := hK ▸ hP
  have hPG₂ : P ≤ G₂ := hP'.trans (coreIn_le_left _ _)
  have hPL : P ≤ L := hA.le_L_of_isPGroup hPG₂ h2
  have hPK₁ : P ≤ G₁ := hP'.trans ((coreIn_le_right _ _).trans inf_le_left)
  have hKG₁ : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₁ := by
    rw [hK]
    exact (coreIn_le_right _ _).trans inf_le_left
  have hKLT : ballStab 1 (γ₁ G₀ G₁ G₂) ⊓ L ≤ T := by
    rw [← hA.inf_eq]
    exact le_inf inf_le_right (inf_le_left.trans hKG₁)
  have hnorm : G₂ ≤
      Subgroup.normalizer ((ballStab 1 (γ₁ G₀ G₁ G₂) ⊓ L : Subgroup G) : Set G) := by
    refine le_normalizer_inf ?_ hA.le_normalizer
    rw [hK]
    exact le_normalizer_coreIn _ _
  have h2' : IsPGroup 2 ↥(ballStab 1 (γ₁ G₀ G₁ G₂) ⊓ L) :=
    hA.hyp.sylow₂.2.1.to_le hKLT
  have hKLQ : ballStab 1 (γ₁ G₀ G₁ G₂) ⊓ L ≤ pCoreOf 2 G₂ :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans hA.le) hnorm h2'
  exact (le_inf hP hPL).trans hKLQ

theorem AmalgamS3.s3Point_γ₁ (hA : AmalgamS3 G₀ G₁ G₂ T L) :
    S3Point G₀ G₁ G₂ (γ₁ G₀ G₁ G₂) where
  charTwo := by
    simpa [stab_γ₁ hA.hyp.le₂] using hA.charTwo₂
  ncard_nbrs := ncard_nbrs_γ₁ hA
  le_pCoreOf_of_le_ballStab := by
    intro P hP h2
    simpa [stab_γ₁ hA.hyp.le₂] using le_pCoreOf_of_le_ballStab_γ₁ hA hP h2
  relIndex_le_two := by
    intro ε hε P hP h2
    rw [stab_γ₁ hA.hyp.le₂]
    obtain ⟨k, hk, rfl⟩ := neighbour_repr hA hε
    have hPTk : P ≤ conjSub (k : G) T := le_conjSub_T_of_isPGroup hA hk hP h2
    have hTkG₂ : conjSub (k : G) T ≤ G₂ := conjSub_T_le_G₂ hA hk
    have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set G) :=
      hPTk.trans (hTkG₂.trans (le_normalizer_pCoreOf 2 G₂))
    have hQleTk : pCoreOf 2 G₂ ≤ conjSub (k : G) T := pCoreOf_le_conjSub_T hA hk
    have hsup : P ⊔ pCoreOf 2 G₂ ≤ conjSub (k : G) T := sup_le hPTk hQleTk
    have hEq := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := P) (K := pCoreOf 2 G₂) hPN).2
    rw [← hEq]
    refine (Subgroup.relIndex_le_of_le_right hsup Subgroup.index_ne_zero_of_finite).trans ?_
    rw [relIndex_pCoreOf_conjSub_T hA hk]
  exists_two_elt := by
    intro ε hε
    obtain ⟨k, hk, rfl⟩ := neighbour_repr hA hε
    obtain ⟨t, ht, ht2, htQ⟩ := exists_two_elt_γ₁ hA hk
    exact ⟨t, ht, ht2, by simpa [stab_γ₁ hA.hyp.le₂] using htQ⟩
  smul_ne := by
    intro f hf hf2 hfQ ε hε hfix ε' hε' hne
    exact smul_ne_γ₁ hA f hf hf2 (by simpa [stab_γ₁ hA.hyp.le₂] using hfQ) ε hε hfix ε' hε' hne
  exists_swap := exists_swap_γ₁ hA
  exists_swap_fix := by
    intro ε hε ε₁ h₁ ε₂ h₂ h1 h2 h12
    obtain ⟨k, hk, rfl⟩ := neighbour_repr hA hε
    exact exists_swap_fix_γ₁ hA hk h₁ h₂ h1 h2 h12
  transitive_of_normal := by
    intro N hN hNnorm hf ε hε ε' hε'
    obtain ⟨f, hfN, hf2, hfQ⟩ := hf
    exact transitive_of_normal_γ₁ hA N hN hNnorm ⟨f, hfN, hf2, by
      simpa [stab_γ₁ hA.hyp.le₂] using hfQ⟩ ε hε ε' hε'

end CFSG.Quasithin.F112Crit.APrime

end

