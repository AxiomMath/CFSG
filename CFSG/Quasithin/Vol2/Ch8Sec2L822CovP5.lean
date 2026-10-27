module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP1
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

theorem perm5_normal_eq_bot_cv (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (h : N ⊓ alternatingGroup (Fin 5) = ⊥) : N = ⊥ := by
  by_contra hne
  obtain ⟨τ, htN, hτ1⟩ : ∃ τ : Equiv.Perm (Fin 5), τ ∈ N ∧ τ ≠ 1 := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  have hsq : ∀ u : Equiv.Perm (Fin 5), u * u ∈ alternatingGroup (Fin 5) := fun u =>
    Equiv.Perm.mem_alternatingGroup.2 (by rw [map_mul, ← sq, Int.units_sq])
  have htt : τ * τ = 1 := by
    have hmem : τ * τ ∈ N ⊓ alternatingGroup (Fin 5) := ⟨N.mul_mem htN htN, hsq τ⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right htt
  have hcomm : ∀ σ : Equiv.Perm (Fin 5), σ * τ = τ * σ := by
    intro σ
    have hc : σ * τ * σ⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance τ htN σ
    have hsg : Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ := by
      rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ),
        mul_inv_cancel_right]
    have hmem : τ * (σ * τ * σ⁻¹) ∈ N ⊓ alternatingGroup (Fin 5) := by
      refine ⟨N.mul_mem htN hc, Equiv.Perm.mem_alternatingGroup.2 ?_⟩
      rw [map_mul, hsg, ← sq, Int.units_sq]
    rw [h, Subgroup.mem_bot] at hmem
    have hX : σ * τ * σ⁻¹ = τ := by
      rw [eq_inv_of_mul_eq_one_right hmem, hinv]
    exact mul_inv_eq_iff_eq_mul.1 hX
  have hcen : ∀ u : Equiv.Perm (Fin 5),
      u * List.formPerm [0, 1, 2, 3, 4] = List.formPerm [0, 1, 2, 3, 4] * u →
        u * Equiv.swap 0 1 = Equiv.swap 0 1 * u → u = 1 := by
    decide +kernel
  exact hτ1 (hcen τ (hcomm _).symm (hcomm _).symm)

theorem perm5_alt_le_of_normal_ne_bot_cv (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hN : N ≠ ⊥) : alternatingGroup (Fin 5) ≤ N := by
  by_contra hle
  haveI : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with hb | ht
  · exact hN (perm5_normal_eq_bot_cv N (disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 hb)))
  · exact hle (Subgroup.subgroupOf_eq_top.1 ht)

theorem perm5_normal_eq_bot_of_odd_cv (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hodd : ¬ 2 ∣ Nat.card N) : N = ⊥ := by
  by_contra hne
  have hle := perm5_alt_le_of_normal_ne_bot_cv N hne
  have hdA : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hd2 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ^ 2 = 1 := by decide
  have hd1 : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 ≠ 1 := by decide
  let x : N := ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3, hle hdA⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext hd2
  have hx1 : x ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  exact hodd (by rw [← hord]; exact orderOf_dvd_natCard x)

theorem perm5_normal_eq_bot_of_pgroup_cv (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k = 1) : N = ⊥ := by
  by_contra hne
  have hle := perm5_alt_le_of_normal_ne_bot_cv N hne
  have hc3 : (List.formPerm [0, 1, 2] : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  obtain ⟨k, hk⟩ := hN2 _ (hle hc3)
  have h3 : (List.formPerm [0, 1, 2] : Equiv.Perm (Fin 5)) ^ 3 = 1 := by decide
  have h1 : (List.formPerm [0, 1, 2] : Equiv.Perm (Fin 5)) ≠ 1 := by decide
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have hg := pow_gcd_eq_one.2 ⟨h3, hk⟩
  rw [hcop, pow_one] at hg
  exact h1 hg

theorem perm5_commutator_alt_ne_bot_cv :
    ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ ≠ ⊥ := by
  intro hbot
  have ha : (List.formPerm [0, 1, 2] : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hb : (List.formPerm [0, 1, 3] : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  revert hmem
  decide

theorem le_ker_of_odd_index_cv {X : Type} [Group X] [Finite X] (θ : X →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ) {J S : Subgroup X} [hJ : J.Normal] (hSJ : S ≤ J)
    (hSk : S ≤ θ.ker) {m : ℕ} (hm : Nat.card J = Nat.card S * m) (hodd : ¬ 2 ∣ m) :
    J ≤ θ.ker := by
  have hrange : (θ.comp J.subtype).range = J.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card J = Nat.card (θ.comp J.subtype).ker * Nat.card (J.map θ) := by
    rw [← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hSf : S.subgroupOf J ≤ (θ.comp J.subtype).ker := by
    intro x hx
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 (hSk (Subgroup.mem_subgroupOf.1 hx)))
  have hdvd : Nat.card (S.subgroupOf J) ∣ Nat.card (θ.comp J.subtype).ker :=
    Subgroup.card_dvd_of_le hSf
  have hSc : Nat.card (S.subgroupOf J) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  rw [hSc] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hmk : m = k * Nat.card (J.map θ) := by
    apply Nat.eq_of_mul_eq_mul_left hSpos
    rw [← hm, hcard, hk]
    ring
  have hnodd : ¬ 2 ∣ Nat.card (J.map θ) := fun h2 =>
    hodd (by rw [hmk]; exact Dvd.dvd.mul_left h2 k)
  haveI : (J.map θ).Normal := hJ.map θ hθ
  have hbot : J.map θ = ⊥ := perm5_normal_eq_bot_of_odd_cv (J.map θ) hnodd
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmem : θ x ∈ J.map θ := Subgroup.mem_map_of_mem θ hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem le_ker_of_pgroup_normal_cv {X : Type} [Group X] (θ : X →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ) {S : Subgroup X} [hS : S.Normal]
    (hS2 : ∀ x ∈ S, ∃ k : ℕ, x ^ 2 ^ k = 1) : S ≤ θ.ker := by
  haveI : (S.map θ).Normal := hS.map θ hθ
  have hbot : S.map θ = ⊥ := by
    refine perm5_normal_eq_bot_of_pgroup_cv (S.map θ) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hS2 x hx
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmem : θ x ∈ S.map θ := Subgroup.mem_map_of_mem θ hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem kerIn_subgroupOf_le_ker_cv {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (hmp : CFSG.Quasithin.MinParabolic H T M) (θ : ↥H →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ) :
    (CFSG.Quasithin.kerIn M H).subgroupOf H ≤ θ.ker := by
  haveI hSn : ((CFSG.Open.pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  haveI hJn : ((CFSG.Quasithin.kerIn M H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmp.kerIn_le_H).2
      (CFSG.Quasithin.le_normalizer_kerIn M H)
  have hS2 : ∀ x ∈ (CFSG.Open.pCoreOf 2 H).subgroupOf H, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hSk : (CFSG.Open.pCoreOf 2 H).subgroupOf H ≤ θ.ker :=
    le_ker_of_pgroup_normal_cv θ hθ hS2
  have hSJ : (CFSG.Open.pCoreOf 2 H).subgroupOf H ≤ (CFSG.Quasithin.kerIn M H).subgroupOf H :=
    Subgroup.subgroupOf_mono H hmp.pCoreOf_le_kerIn
  have hm : Nat.card ((CFSG.Quasithin.kerIn M H).subgroupOf H) =
      Nat.card ((CFSG.Open.pCoreOf 2 H).subgroupOf H) *
        ((CFSG.Open.pCoreOf 2 H).subgroupOf (CFSG.Quasithin.kerIn M H)).index := by
    have e1 : Nat.card ((CFSG.Quasithin.kerIn M H).subgroupOf H) =
        Nat.card (CFSG.Quasithin.kerIn M H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmp.kerIn_le_H).toEquiv
    have e2 : Nat.card ((CFSG.Open.pCoreOf 2 H).subgroupOf H) = Nat.card (CFSG.Open.pCoreOf 2 H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).toEquiv
    have e3 : Nat.card ((CFSG.Open.pCoreOf 2 H).subgroupOf (CFSG.Quasithin.kerIn M H)) =
        Nat.card (CFSG.Open.pCoreOf 2 H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmp.pCoreOf_le_kerIn).toEquiv
    have e4 : Nat.card ((CFSG.Open.pCoreOf 2 H).subgroupOf (CFSG.Quasithin.kerIn M H)) *
        ((CFSG.Open.pCoreOf 2 H).subgroupOf (CFSG.Quasithin.kerIn M H)).index =
          Nat.card (CFSG.Quasithin.kerIn M H) :=
      Subgroup.card_mul_index _
    rw [e1, e2, ← e3]
    exact e4.symm
  exact le_ker_of_odd_index_cv θ hθ hSJ hSk hm hmp.isSylowTwoOf_pCoreOf_kerIn.2.2

theorem conj_mem_commutator_cv {G : Type} [Group G] {K : Subgroup G} {h : G}
    (hK : ∀ a ∈ K, h * a * h⁻¹ ∈ K) (x : G) (hx : x ∈ ⁅K, K⁆) : h * x * h⁻¹ ∈ ⁅K, K⁆ := by
  have hle : ⁅K, K⁆ ≤ (⁅K, K⁆).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    change h * ⁅a, b⁆ * h⁻¹ ∈ ⁅K, K⁆
    have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hK a ha) (hK b hb)
  exact hle hx

theorem isPerfect_twoResidual_of_perm5_cv {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (hmp : CFSG.Quasithin.MinParabolic H T M) (θ : ↥H →* Equiv.Perm (Fin 5))
    (hθ : Function.Surjective θ)
    (hA5 : ((CFSG.Quasithin.twoResidual H).subgroupOf H).map θ = alternatingGroup (Fin 5)) :
    Group.IsPerfect ↥(CFSG.Quasithin.twoResidual H) := by
  set K : Subgroup G := CFSG.Quasithin.twoResidual H with hKdef
  have hKH : K ≤ H := CFSG.Quasithin.twoResidual_le H
  have hYK : ⁅K, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have hYH : ⁅K, K⁆ ≤ H := hYK.trans hKH
  have hYn : H ≤ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_commutator_cv
        (fun a ha => (Subgroup.mem_normalizer_iff.1 (CFSG.Quasithin.le_normalizer_twoResidual H hh) a).1 ha)
        x hx
    · intro hx
      have hinv : h⁻¹ ∈ H := H.inv_mem hh
      have hK' : ∀ a ∈ K, h⁻¹ * a * h⁻¹⁻¹ ∈ K := fun a ha =>
        (Subgroup.mem_normalizer_iff.1 (CFSG.Quasithin.le_normalizer_twoResidual H hinv) a).1 ha
      have h1 := conj_mem_commutator_cv hK' (h * x * h⁻¹) hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at h1
  rcases hmp.le_kerIn_or_twoResidual_le hYH hYn with hY | hKY
  ·
    exfalso
    have hcomm_le : ⁅K.subgroupOf H, K.subgroupOf H⁆ ≤ (CFSG.Quasithin.kerIn M H).subgroupOf H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_subgroupOf]
      have e : (((⁅a, b⁆ : ↥H)) : G) = ⁅(a : G), (b : G)⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      exact hY (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 ha)
        (Subgroup.mem_subgroupOf.1 hb))
    have h1 : Subgroup.map θ ⁅K.subgroupOf H, K.subgroupOf H⁆ ≤ ⊥ :=
      Subgroup.map_le_iff_le_comap.2 (hcomm_le.trans (kerIn_subgroupOf_le_ker_cv hmp θ hθ))
    have h2 : ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ =
        Subgroup.map θ ⁅K.subgroupOf H, K.subgroupOf H⁆ := by
      rw [Subgroup.map_commutator, hA5]
    exact perm5_commutator_alt_ne_bot_cv (by rw [h2]; exact le_bot_iff.1 h1)
  · exact Subgroup.isPerfect_iff.2 (le_antisymm hYK hKY)

end CFSG.Quasithin.H13
