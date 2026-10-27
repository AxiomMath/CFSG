module

public import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open scoped commutatorElement

theorem eq_top_of_commute_sup {J : Type} [Group J] {p : ℕ} {θ N : Subgroup J}
    (hgen : Subgroup.closure {x : J | ∃ k : ℕ, orderOf x = p ^ k} = ⊤)
    (hθ : ∀ t ∈ θ, Nat.Coprime p (orderOf t)) [N.Normal] (hsup : N ⊔ θ = ⊤)
    (hcomm : ∀ n ∈ N, ∀ t ∈ θ, n * t = t * n) : N = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
  obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  have hpow : (n * t) ^ (p ^ k) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hc : Commute n t := hcomm n hn t ht
  rw [hc.mul_pow] at hpow
  have h1 : t ^ (p ^ k) = (n ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hpow
  have h2 : t ^ (p ^ k) ∈ N := by
    rw [h1]
    exact N.inv_mem (N.pow_mem hn _)
  have hcop : Nat.Coprime (p ^ k) (orderOf t) := Nat.Coprime.pow_left k (hθ t ht)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h3 : t ∈ N := by
    rw [← hm]
    exact N.pow_mem h2 m
  exact N.mul_mem hn h3

theorem exists_noncomm_of_psu_four_model {Q : Type} [Group Q] {f : ℕ}
    (h : StatedClassicalModel Q .PSU 4 2 f) : ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h'
    have := congrArg Prod.fst h'
    simp at this
  obtain ⟨hqs, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := f) hK (by norm_num) hne
  obtain ⟨a, b, hab⟩ := hqs.2.2
  let φ : (StatedSU 4 (2 ^ f) K ⧸ Subgroup.center (StatedSU 4 (2 ^ f) K)) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e.symm
  exact ⟨φ a, φ b, fun h' => hab (φ.injective (by rw [map_mul, map_mul]; exact h'))⟩

theorem theta_eq_bot_of_commute
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] {p : ℕ} (hp : p.Prime) {f : ℕ} (hf : 2 ≤ f)
    (hgen : Subgroup.closure {x : J | ∃ k : ℕ, orderOf x = p ^ k} = ⊤)
    (hmodel : StatedClassicalModel (J ⧸ aschbacherSolvableCore p J) .PSU 4 2 f)
    {c : J} (hcp : orderOf c = p)
    (hcent : ∀ v ∈ aschbacherSolvableCore p J, v * c = c * v) :
    aschbacherSolvableCore p J = ⊥ := by
  set θ := aschbacherSolvableCore p J with hθdef
  have hθn : θ.Normal := aschbacherSolvableCore_normal p J
  obtain ⟨-, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := J) hp
  have hθord : ∀ t ∈ θ, Nat.Coprime p (orderOf t) := by
    intro t ht
    have h1 : orderOf t ∣ Nat.card θ := by
      have := orderOf_dvd_natCard (⟨t, ht⟩ : θ)
      rwa [Subgroup.orderOf_mk] at this
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hθp (hd.trans h1)
  have hQs : IsSimpleGroup (J ⧸ θ) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 2 f hmodel).2
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_psu_four_model hmodel
  have hcθ : c ∉ θ := by
    intro hc
    have := hθord c hc
    rw [hcp, Nat.coprime_self] at this
    exact hp.ne_one this
  have hsup : ∀ H : Subgroup J, H.Normal → ¬ H ≤ θ → H ⊔ θ = ⊤ := by
    intro H hH hHθ
    have hmapn : (H.map (QuotientGroup.mk' θ)).Normal :=
      hH.map _ (QuotientGroup.mk'_surjective θ)
    rcases hQs.eq_bot_or_eq_top_of_normal (H.map (QuotientGroup.mk' θ)) with h0 | h1
    · exfalso
      apply hHθ
      intro x hx
      have : QuotientGroup.mk' θ x ∈ H.map (QuotientGroup.mk' θ) := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    · have := Subgroup.comap_map_eq (QuotientGroup.mk' θ) H
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
  have hSn : (Subgroup.centralizer (θ : Set J)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro t ht
    have h1 : g⁻¹ * t * g ∈ θ := by
      have := hθn.conj_mem t ht g⁻¹
      simpa using this
    have h2 := hx _ h1
    calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
      _ = g * x * g⁻¹ * t := by group
  have hN : Subgroup.normalClosure ({c} : Set J) ≤ Subgroup.centralizer (θ : Set J) := by
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact Subgroup.mem_centralizer_iff.2 fun t ht => hcent t ht
  have hNcomm : ∀ n ∈ Subgroup.normalClosure ({c} : Set J), ∀ t ∈ θ, n * t = t * n := by
    intro n hn t ht
    exact ((Subgroup.mem_centralizer_iff.1 (hN hn)) t ht).symm
  have hNtop : Subgroup.normalClosure ({c} : Set J) = ⊤ := by
    refine eq_top_of_commute_sup hgen hθord ?_ hNcomm
    exact hsup _ inferInstance fun hle => hcθ (hle (Subgroup.subset_normalClosure rfl))
  have hθZ : θ ≤ Subgroup.center J := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    exact hNcomm g (hNtop ▸ Subgroup.mem_top g) t ht
  have hperf : commutator J = ⊤ := by
    have hnot : ¬ commutator J ≤ θ := by
      intro hle
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have h2 : ((QuotientGroup.mk' θ) ⁅x, y⁆ : J ⧸ θ) = 1 :=
        (QuotientGroup.eq_one_iff _).2
          (hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)))
      rw [map_commutatorElement] at h2
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
    refine eq_top_of_commute_sup hgen hθord (hsup _ inferInstance hnot) ?_
    intro n _ t ht
    exact ((Subgroup.mem_center_iff.1 (hθZ ht)) n)
  have hZθ : Subgroup.center J = θ := by
    refine le_antisymm ?_ hθZ
    by_contra hnle
    have h1 := hsup (Subgroup.center J) inferInstance hnle
    have h2 : Subgroup.center J = ⊤ := by
      rw [← top_le_iff, ← h1]
      exact sup_le le_rfl hθZ
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Subgroup.center J := h2 ▸ Subgroup.mem_top x
    rw [Subgroup.mem_center_iff] at hx
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (hx y).symm]
  let φ : (J ⧸ Subgroup.center J) ≃* (J ⧸ θ) := QuotientGroup.quotientMulEquivOfEq hZθ
  have hqs : CFSG.IsQuasisimple J := by
    refine ⟨⟨hperf⟩, φ.isSimpleGroup, ?_⟩
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩
  have hmodel' : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 4 2 f :=
    Equivariance.statedClassicalModel_of_mulEquiv φ.symm hmodel
  have hcen := psuFourEvenCenterTrivial_of_multipliers hGA J f hf hqs hmodel'
  rw [← hZθ]
  exact hcen

end CFSG.RankThree.PartOne.K1327
