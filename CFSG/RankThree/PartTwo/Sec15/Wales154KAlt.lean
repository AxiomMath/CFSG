module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec15.Wales154KSmall

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Equiv Equiv.Perm Subgroup

private theorem exists_mulAut_mulEquiv_perm {Q : Type} [Group Q] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (φ : Q ≃* alternatingGroup (Fin n)) :
    ∃ θ : MulAut Q ≃* Perm (Fin n),
      (∀ α : MulAut Q, ∀ q : Q,
        θ α * (φ q : Perm (Fin n)) * (θ α)⁻¹ = (φ (α q) : Perm (Fin n))) ∧
      ∀ q : Q, θ (MulAut.conj q) = (φ q : Perm (Fin n)) := by
  set c : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6) with hc
  have hcapp : ∀ (σ : Perm (Fin n)) (x : alternatingGroup (Fin n)),
      ((c σ x : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * x * σ⁻¹ := by
    intro σ x
    rw [hc, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]
  refine ⟨(MulAut.congr φ).trans c.symm, fun α q => ?_, fun q => ?_⟩
  · have h1 : c (((MulAut.congr φ).trans c.symm) α) = MulAut.congr φ α := by simp
    have h2 := congrArg (fun β : MulAut (alternatingGroup (Fin n)) =>
      ((β (φ q) : alternatingGroup (Fin n)) : Perm (Fin n))) h1
    simp only [hcapp] at h2
    rw [h2]
    simp
  · apply c.injective
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    ext x
    rw [hcapp]
    simp

private theorem pow_dvd_card_of_le {G : Type*} [Group G] [Finite G] {p k : ℕ} [hp : Fact p.Prime]
    (hG : IsPGroup p G) (h : p ^ k ≤ Nat.card G) : p ^ k ∣ Nat.card G := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  rw [hn] at h ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp h)

private theorem eq_bot_of_orderOf_eq_seven {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    {y : Perm (Fin 7)} (hyN : y ∈ normalizer (P : Set (Perm (Fin 7)))) (hy : orderOf y = 7) :
    P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 7) (by simp)
  have hcyc : y.IsCycle := isCycle_of_prime_order' (by rw [hy]; norm_num)
    (by rw [hy, Fintype.card_fin]; norm_num)
  have hsupp : y.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hy, Fintype.card_fin]
  have hfix : ∀ i : Fin 7, ∀ p ∈ P, p i = i := by
    intro i p hp
    obtain ⟨m, rfl⟩ := hcyc.exists_pow_eq (mem_support.mp (hsupp ▸ Finset.mem_univ j))
      (mem_support.mp (hsupp ▸ Finset.mem_univ i))
    have hq : (y ^ m)⁻¹ * p * y ^ m ∈ P := (mem_normalizer_iff''.mp (pow_mem hyN m) p).mp hp
    have h1 : ((y ^ m)⁻¹ * p * y ^ m) j = j := hj ⟨_, hq⟩
    rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h1
    exact h1
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  ext i
  simp [hfix i p hp]

theorem ks154A7Seven : KS154A7Seven := by
  intro Q _ hQ K h7 P hP hKP
  obtain ⟨φ⟩ := hQ
  obtain ⟨θ, -, hθc⟩ := exists_mulAut_mulEquiv_perm (n := 7) (by norm_num) (by norm_num) φ
  have : Finite Q := Finite.of_equiv _ φ.symm.toEquiv
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨k, hkK⟩, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 h7
  rw [Subgroup.orderOf_mk] at hk
  have hy : orderOf (φ k : Perm (Fin 7)) = 7 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hk]
  have hyN : (φ k : Perm (Fin 7)) ∈
      normalizer ((P.map θ.toMonoidHom : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨MulAut.conj k, hKP k hkK, hθc k⟩
  have h := eq_bot_of_orderOf_eq_seven (hP.map θ.toMonoidHom) hyN hy
  exact (Subgroup.map_eq_bot_iff_of_injective P (f := θ.toMonoidHom) θ.injective).mp h

private theorem card_centralizer_of_orderOf_eq_five {x : Perm (Fin 7)} (hx : orderOf x = 5) :
    Nat.card (centralizer ({x} : Set (Perm (Fin 7)))) = 10 := by
  have hcyc : x.IsCycle := isCycle_of_prime_order' (by rw [hx]; norm_num)
    (by rw [hx, Fintype.card_fin]; norm_num)
  have hsupp : x.support.card = 5 := by rw [← hcyc.orderOf, hx]
  rw [nat_card_centralizer, hcyc.cycleType, hsupp]
  simp [Fintype.card_fin, Nat.factorial]

private theorem eq_one_of_mem_normalizer_of_card_eq_five {S : Subgroup (Perm (Fin 7))}
    (hS : Nat.card S = 5) {t : Perm (Fin 7)} (ht : t ∈ normalizer (S : Set (Perm (Fin 7))))
    {m : ℕ} (htm : t ^ 3 ^ m = 1) : t = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic S := isCyclic_of_prime_card hS
  set ψ := S.normalizerMonoidHom ⟨t, ht⟩ with hψ
  have hψ4 : orderOf ψ ∣ 4 := by
    have h := orderOf_dvd_natCard ψ
    rwa [IsCyclic.card_mulAut, hS, Nat.totient_prime (by norm_num)] at h
  have hψ3 : orderOf ψ ∣ 3 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨t, ht⟩ : normalizer (S : Set (Perm (Fin 7)))) ^ 3 ^ m = 1 := Subtype.ext htm
    rw [hψ, ← map_pow, h1, map_one]
  have hψ1 : ψ = 1 := by
    have h := Nat.dvd_gcd hψ4 hψ3
    rw [(Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 4 3)).gcd_eq_one] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : S)
  have hx5 : orderOf (x : Perm (Fin 7)) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hS ▸ pow_card_eq_one') hx1
  have htx : t ∈ centralizer ({(x : Perm (Fin 7))} : Set (Perm (Fin 7))) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg (fun σ : MulAut S => ((σ x : S) : Perm (Fin 7))) hψ1
    simp only [hψ, MulAut.one_apply, normalizerMonoidHom_apply_apply_coe] at h1
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h1]
  have h10 : orderOf t ∣ 10 :=
    card_centralizer_of_orderOf_eq_five hx5 ▸ Subgroup.orderOf_dvd_natCard _ htx
  have h := Nat.dvd_gcd h10 (orderOf_dvd_of_pow_eq_one htm)
  rw [(Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 10 3)).gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

open scoped Pointwise in
private theorem false_of_le_normalizer {K E : Subgroup (Perm (Fin 7))} (h5 : 5 ∣ Nat.card K)
    (h9 : ¬ 9 ∣ Nat.card K) (hE : IsPGroup 3 E) (h9E : 9 ≤ Nat.card E)
    (hEN : E ≤ normalizer (K : Set (Perm (Fin 7)))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := normalizer (K : Set (Perm (Fin 7)))
  set E₀ : Subgroup N := E.subgroupOf N
  have hE₀card : Nat.card E₀ = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have h9E' : 9 ∣ Nat.card E := pow_dvd_card_of_le (p := 3) (k := 2) hE (by simpa using h9E)
  obtain ⟨S, g, hgS, hg1⟩ : ∃ S : Sylow 5 K, ∃ g ∈ MulAction.stabilizer E₀ S, g ≠ 1 := by
    by_contra hfree
    push Not at hfree
    have hbot : ∀ S : Sylow 5 K, MulAction.stabilizer E₀ S = ⊥ := fun S =>
      (Subgroup.eq_bot_iff_forall _).mpr (hfree S)
    have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hbot)
    rw [Nat.card_prod] at hcard
    have hdvd : Nat.card E₀ ∣ Nat.card (Sylow 5 K) := Dvd.intro_left _ hcard.symm
    have hdvdK : Nat.card (Sylow 5 K) ∣ Nat.card K :=
      (Sylow.card_dvd_index (default : Sylow 5 K)).trans (Subgroup.index_dvd_card _)
    exact h9 (h9E'.trans (hE₀card ▸ hdvd.trans hdvdK))
  set t : Perm (Fin 7) := ((g : N) : Perm (Fin 7))
  have htE : t ∈ E := Subgroup.mem_subgroupOf.mp g.2
  set S' : Subgroup (Perm (Fin 7)) := (S : Subgroup K).map K.subtype with hS'
  have htS : t ∈ normalizer (S' : Set (Perm (Fin 7))) := by
    apply mem_normalizer_fintype
    rintro _ ⟨s, hs, rfl⟩
    have h3 : (g : N) • (S : Subgroup K) = (S : Subgroup K) :=
      congrArg (fun T : Sylow 5 K => (T : Subgroup K)) hgS
    have h1 : (g : N) • s ∈ (S : Subgroup K) := by
      rw [← h3]
      exact Subgroup.smul_mem_pointwise_smul s _ _ hs
    exact ⟨(g : N) • s, h1, rfl⟩
  have hScard : Nat.card (S : Subgroup K) = 5 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have h1 : 5 ∣ Nat.card (S : Subgroup K) := S.dvd_card_of_dvd_card h5
    have h7 : Nat.card (Perm (Fin 7)) = 5040 := by rw [Nat.card_perm, Nat.card_fin]; rfl
    have h2 : Nat.card (S : Subgroup K) ∣ 5040 := h7 ▸
      (Subgroup.card_subgroup_dvd_card (S : Subgroup K)).trans (Subgroup.card_subgroup_dvd_card K)
    rw [hn] at h1 h2 ⊢
    rcases n with _ | _ | n
    · norm_num at h1
    · rfl
    · exfalso
      have h3 := (pow_dvd_pow 5 (by omega : 2 ≤ n + 2)).trans h2
      norm_num at h3
  have hS'card : Nat.card S' = 5 := by
    rw [hS', Subgroup.card_map_of_injective K.subtype_injective]
    exact hScard
  obtain ⟨m, hm⟩ := hE ⟨t, htE⟩
  have htm : t ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  exact hg1 (Subtype.ext (Subtype.ext (eq_one_of_mem_normalizer_of_card_eq_five hS'card htS htm)))

theorem ks154A7E9 : KS154A7E9 := by
  intro Q _ hQ K h5 h9 E hE h9E hEK
  obtain ⟨φ⟩ := hQ
  obtain ⟨θ, hθ, -⟩ := exists_mulAut_mulEquiv_perm (n := 7) (by norm_num) (by norm_num) φ
  set ι : Q →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hK : Nat.card (K.map ι) = Nat.card K := Subgroup.card_map_of_injective hιinj
  have hE' : Nat.card (E.map θ.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective θ.injective
  refine false_of_le_normalizer (K := K.map ι) (E := E.map θ.toMonoidHom) (hK ▸ h5) (hK ▸ h9)
    (hE.map _) (hE' ▸ h9E) ?_
  rw [le_normalizer_iff]
  rintro _ ⟨e, he, rfl⟩ _ ⟨k, hk, rfl⟩
  exact ⟨e k, hEK e he k hk, (hθ e k).symm⟩

private theorem mem_alternatingGroup_of_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {m : ℕ} (hσ : σ ^ 3 ^ m = 1) : σ ∈ alternatingGroup α := by
  rw [mem_alternatingGroup]
  have hs : sign σ ^ 3 ^ m = 1 := by rw [← map_pow, hσ, map_one]
  rcases Int.units_eq_one_or (sign σ) with h | h
  · exact h
  · rw [h, Odd.neg_one_pow (Odd.pow (by decide))] at hs
    exact absurd hs (by decide)

theorem ks154A10Aut : KS154A10Aut := by
  intro Q _ hQ K h7 E hE h27 _ P hP hKP hEP
  obtain ⟨φ⟩ := hQ
  obtain ⟨θ, -, hθc⟩ := exists_mulAut_mulEquiv_perm (n := 10) (by norm_num) (by norm_num) φ
  set ι : Q →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp φ.toMonoidHom
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  set K' : Subgroup (Perm (Fin 10)) := K.map ι with hK'
  set E' : Subgroup (Perm (Fin 10)) := E.map θ.toMonoidHom
  set P' : Subgroup (Perm (Fin 10)) := P.map θ.toMonoidHom
  have hN : (normalizer (P : Set (MulAut Q))).map θ.toMonoidHom =
      normalizer (P' : Set (Perm (Fin 10))) := Subgroup.map_equiv_normalizer_eq P θ
  have hKA : K' ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨k, -, rfl⟩
    exact (φ k).2
  have hEA : E' ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨m, hm⟩ := hE ⟨e, he⟩
    apply mem_alternatingGroup_of_pow_three (m := m)
    have h := congrArg (fun x : E => θ (x : MulAut Q)) hm
    simpa using h
  have hKN : K' ≤ normalizer (P' : Set (Perm (Fin 10))) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← hN]
    exact ⟨MulAut.conj k, hKP k hk, hθc k⟩
  have hEN : E' ≤ normalizer (P' : Set (Perm (Fin 10))) := by
    rw [← hN]
    exact Subgroup.map_mono hEP
  have h7' : 7 ∣ Nat.card (K' ⊔ E' : Subgroup (Perm (Fin 10))) := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le le_sup_left)
    rwa [hK', Subgroup.card_map_of_injective hιinj]
  have h27' : 27 ∣ Nat.card (K' ⊔ E' : Subgroup (Perm (Fin 10))) := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le le_sup_right)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective θ.injective
    exact pow_dvd_card_of_le (p := 3) (k := 3) (hE.map θ.toMonoidHom) (by rw [hcard]; simpa)
  have h189 : 189 ∣ Nat.card (K' ⊔ E' : Subgroup (Perm (Fin 10))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 27) h7' h27'
  have h := ks154A10 (K' ⊔ E') (sup_le hKA hEA) h189 P' (hP.map θ.toMonoidHom) (sup_le hKN hEN)
  exact (Subgroup.map_eq_bot_iff_of_injective P (f := θ.toMonoidHom) θ.injective).mp h

end CFSG.RankThree.PartTwo.Sec15.Wales154
