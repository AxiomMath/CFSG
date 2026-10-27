module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Kernel
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSymplecticGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
import CFSG.Permutation.SylowTwoNormalizer.Sym
import CFSG.GroupTheory.QuaternionAutPrime
import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open scoped MatrixGroups

theorem normSylowAt_of_odd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ y ∈ normalizer (S : Set X),
      Odd (orderOf y) → y ^ p ∈ centralizer (S : Set X) → y ∈ centralizer (S : Set X)) :
    NormSylowAt X p := by
  intro S hS y hyN hyp
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set y' : X := y ^ 2 ^ a with hy'def
  have hdvd : 2 ^ a ∣ orderOf y := ⟨m, hn⟩
  have hga : orderOf y' = m := by
    rw [hy'def, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hy'N : y' ∈ normalizer (S : Set X) := pow_mem hyN _
  have hy'p : y' ^ p = (y ^ p) ^ 2 ^ a := by
    rw [hy'def, ← pow_mul, Nat.mul_comm, pow_mul]
  have hy'C : y' ∈ centralizer (S : Set X) :=
    h S hS y' hy'N (by rw [hga]; exact hm) (by rw [hy'p]; exact pow_mem hyp _)
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2))
  have hu : ((2 ^ a : ℕ) : ℤ) * (Nat.gcdA (2 ^ a) p : ℤ) +
      (p : ℤ) * (Nat.gcdB (2 ^ a) p : ℤ) = 1 := by
    have h1 := Nat.gcd_eq_gcd_ab (2 ^ a) p
    rw [hcop.gcd_eq_one, Nat.cast_one] at h1
    exact h1.symm
  have h1 : y' ^ (Nat.gcdA (2 ^ a) p : ℤ) =
      y ^ (((2 ^ a : ℕ) : ℤ) * (Nat.gcdA (2 ^ a) p : ℤ)) := by
    rw [hy'def, ← zpow_natCast,
      (zpow_mul y ((2 ^ a : ℕ) : ℤ) (Nat.gcdA (2 ^ a) p : ℤ)).symm]
  have h2 : (y ^ p) ^ (Nat.gcdB (2 ^ a) p : ℤ) =
      y ^ ((p : ℤ) * (Nat.gcdB (2 ^ a) p : ℤ)) := by
    rw [← zpow_natCast, (zpow_mul y (p : ℤ) (Nat.gcdB (2 ^ a) p : ℤ)).symm]
  have hy : y = y' ^ (Nat.gcdA (2 ^ a) p : ℤ) * (y ^ p) ^ (Nat.gcdB (2 ^ a) p : ℤ) := by
    rw [h1, h2, ← zpow_add, hu, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem hy'C _) (zpow_mem hyp _)

theorem mem_normalizer_of_conjSetStab_perm {X : Type} [Group X] [Finite X]
    {Δ : Set (Subgroup X)} (S : Sylow 2 X) (hS : (S : Subgroup X) ≤ conjSetStab Δ)
    {α : Type} [Finite α] (e : (conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm α)
    {y : X} (hyΔ : y ∈ conjSetStab Δ) (hyS : y ∈ normalizer ((S : Subgroup X) : Set X))
    (hy : Odd (orderOf y)) : ∀ J ∈ Δ, y ∈ normalizer (J : Set X) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥(conjSetStab Δ) →* Equiv.Perm ↥Δ := conjPermHom (le_refl (conjSetStab Δ))
  let φ : ↥(conjSetStab Δ) →* ρ.range := ρ.rangeRestrict
  let ψ : ↥(conjSetStab Δ) →* Equiv.Perm α := e.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := e.surjective.comp ρ.rangeRestrict_surjective
  let S' : Sylow 2 ↥(conjSetStab Δ) := S.subtype hS
  let R : Sylow 2 (Equiv.Perm α) := S'.mapSurjective (f := ψ) hψ
  let ty : ↥(conjSetStab Δ) := ⟨y, hyΔ⟩
  have hS'coe : (S' : Subgroup ↥(conjSetStab Δ)) =
      (S : Subgroup X).subgroupOf (conjSetStab Δ) := Sylow.coe_subtype S hS
  have htyN : ty ∈ normalizer (S' : Set ↥(conjSetStab Δ)) := by
    have hset : (S' : Set ↥(conjSetStab Δ)) =
        (((S : Subgroup X).subgroupOf (conjSetStab Δ) : Subgroup ↥(conjSetStab Δ)) :
          Set ↥(conjSetStab Δ)) :=
      congrArg (fun H : Subgroup ↥(conjSetStab Δ) => (H : Set ↥(conjSetStab Δ))) hS'coe
    rw [hset, Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      have h := (Subgroup.mem_normalizer_iff.mp hyS (s : X)).mp hs
      simpa [ty] using h
    · intro hs
      have h : y * (s : X) * y⁻¹ ∈ (S : Subgroup X) := by simpa [ty] using hs
      exact (Subgroup.mem_normalizer_iff.mp hyS (s : X)).mpr h
  have hτN : ψ ty ∈ normalizer (R : Set (Equiv.Perm α)) := by
    have hRcoe : (R : Subgroup (Equiv.Perm α)) = (S' : Subgroup ↥(conjSetStab Δ)).map ψ :=
      Sylow.coe_mapSurjective hψ S'
    have hset : (R : Set (Equiv.Perm α)) =
        (((S' : Subgroup ↥(conjSetStab Δ)).map ψ : Subgroup (Equiv.Perm α)) :
          Set (Equiv.Perm α)) :=
      congrArg (fun H : Subgroup (Equiv.Perm α) => (H : Set (Equiv.Perm α))) hRcoe
    rw [hset]
    exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ htyN)
  have hτodd : Odd (orderOf (ψ ty)) := by
    have h1 : orderOf (ψ ty) ∣ orderOf ty := orderOf_map_dvd ψ ty
    have h2 : orderOf ty = orderOf y := Subgroup.orderOf_mk y hyΔ
    rw [h2] at h1
    exact Odd.of_dvd_nat hy h1
  have hτ1 : ψ ty = 1 :=
    CFSG.Permutation.SylowTwoNormalizer.eq_one_of_mem_normalizer R.isPGroup' R.not_dvd_index
      hτodd hτN
  have hφ1 : φ ty = 1 := by
    apply e.injective
    rw [map_one]
    exact hτ1
  have hρ1 : ρ ty = 1 := by
    have h := congrArg Subtype.val hφ1
    simpa [φ] using h
  exact (CFSG.ComponentClassification.AS81.Sec2.conjPermHom_eq_one_iff
    (le_refl (conjSetStab Δ)) ty).mp hρ1

theorem commute_of_odd_orderOf_of_map_commute {G X : Type} [Group G] [Group X] (ψ : G →* X)
    (hkerC : ψ.ker ≤ center G) (hker2 : ∀ z ∈ ψ.ker, z * z = 1) {g b : G}
    (hg : Odd (orderOf g)) (h : Commute (ψ g) (ψ b)) : Commute g b := by
  set c : G := g * b * g⁻¹ * b⁻¹ with hcdef
  have hψc : ψ c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, h.eq]
    group
  have hcKer : c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]; exact hψc
  have hcCenter : c ∈ center G := hkerC hcKer
  have hcC : ∀ z : G, z * c = c * z := fun z => Subgroup.mem_center_iff.mp hcCenter z
  have hc2 : c * c = 1 := hker2 c hcKer
  have hgb : g * b * g⁻¹ = c * b := by
    rw [hcdef]; group
  have hcg : Commute g c := hcC g
  have hpow : ∀ j : ℕ, g ^ j * b * (g ^ j)⁻¹ = c ^ j * b := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hcj : g * c ^ j * g⁻¹ = c ^ j := by
          have h1 : g * c ^ j = c ^ j * g := (hcg.pow_right j).eq
          rw [h1]; group
        calc g ^ (j + 1) * b * (g ^ (j + 1))⁻¹
            = g * (g ^ j * b * (g ^ j)⁻¹) * g⁻¹ := by group
          _ = g * (c ^ j * b) * g⁻¹ := by rw [ih]
          _ = (g * c ^ j * g⁻¹) * (g * b * g⁻¹) := by group
          _ = c ^ j * (c * b) := by rw [hcj, hgb]
          _ = c ^ (j + 1) * b := by rw [pow_succ']; group
  have hgm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hcm : c ^ orderOf g = 1 := by
    have h1 : b = c ^ orderOf g * b := by
      have h2 := hpow (orderOf g)
      rw [hgm, one_mul] at h2
      simpa using h2
    exact mul_right_cancel (by rw [one_mul]; exact h1.symm)
  obtain ⟨k, hk⟩ := hg
  have hc1 : c = 1 := by
    have h : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact hcm
    have h2 : c ^ (2 * k + 1) = (c * c) ^ k * c := by rw [pow_succ, pow_mul, sq]
    rw [h2, hc2, one_pow, one_mul] at h
    exact h
  have hfix : g * b * g⁻¹ = b := by rw [hgb, hc1, one_mul]
  show g * b = b * g
  calc g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [hfix]

theorem mem_centralizer_of_isSylowOf_sl2 {X F : Type} [Group X] [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {K Q : Subgroup X} (e : K ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) {y : X} (hyQ : y ∈ normalizer (Q : Set X))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hyp : y ^ p ∈ centralizer (Q : Set X)) :
    y ∈ centralizer (Q : Set X) := by
  have : Finite ↥K := Finite.of_equiv (SL(2, F)) e.symm.toEquiv
  obtain ⟨Q₀, hQ₀⟩ := hQ
  obtain ⟨k, hk, ⟨eQ₀⟩⟩ := CFSG.ClassicalInvolution.Asc77.exists_quaternion_equiv_sylow hF e Q₀
  let eQ : ↥Q ≃* QuaternionGroup (2 ^ k) :=
    ((MulEquiv.subgroupCongr hQ₀.symm).trans
      (Subgroup.equivMapOfInjective Q₀ K.subtype K.subtype_injective).symm).trans eQ₀
  have hmap : Q.map (MulAut.conj y).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyQ
  let σ : MulAut ↥Q :=
    (MulEquiv.subgroupMap (MulAut.conj y) Q).trans (MulEquiv.subgroupCongr hmap)
  have hσcoe : ∀ s : ↥Q, ((σ s : ↥Q) : X) = y * (s : X) * y⁻¹ := by
    intro s
    have h := MulEquiv.coe_subgroupMap_apply (MulAut.conj y) Q s
    have h2 := MulEquiv.subgroupCongr_apply hmap ((MulEquiv.subgroupMap (MulAut.conj y) Q) s)
    calc (((MulEquiv.subgroupCongr hmap) ((MulEquiv.subgroupMap (MulAut.conj y) Q) s) : ↥Q) : X)
        = (((MulEquiv.subgroupMap (MulAut.conj y) Q) s :
            ↥(Q.map (MulAut.conj y).toMonoidHom)) : X) := h2
      _ = (MulAut.conj y) (s : X) := h
      _ = y * (s : X) * y⁻¹ := MulAut.conj_apply y (s : X)
  have hσpow : ∀ j : ℕ, ∀ s : ↥Q,
      (((σ ^ j) s : ↥Q) : X) = y ^ j * (s : X) * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro s; simp
    | succ j ih =>
        intro s
        have h1 : ((σ ^ (j + 1)) s : ↥Q) = σ ((σ ^ j) s) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [h1, hσcoe, ih, pow_succ']
        group
  have hσp : σ ^ p = 1 := by
    refine MulEquiv.ext fun s => ?_
    apply Subtype.ext
    rw [hσpow p s]
    have hcomm : (s : X) * y ^ p = y ^ p * (s : X) :=
      (Subgroup.mem_centralizer_iff.mp hyp) s s.2
    rw [← hcomm]
    group
    rfl
  have hσ1 : σ = 1 := by
    by_cases hk1 : k = 1
    · have h2k : 2 ^ k = 2 := by rw [hk1, pow_one]
      rw [h2k] at eQ
      have hσ'p : (MulAut.congr eQ σ) ^ p = 1 := by
        rw [← map_pow, hσp, map_one]
      have h := CFSG.GroupTheory.mulAut_quaternion_eq_one_of_pow_eq_one hp hp5 hσ'p
      exact (MulAut.congr eQ).injective (by rw [h, map_one])
    · have hk2 : 2 ≤ k := by omega
      refine CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22.mulAut_eq_one_of_odd_of_equiv hk2 eQ σ ?_
      exact Odd.of_dvd_nat (hp.odd_of_ne_two (by omega)) (orderOf_dvd_of_pow_eq_one hσp)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxfix : σ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hσ1]; rfl
  have h := hσcoe ⟨x, hx⟩
  rw [hxfix] at h
  have hxeq : x = y * x * y⁻¹ := by simpa using h
  calc x * y = (y * x * y⁻¹) * y := by
        conv_lhs => rw [hxeq]
    _ = y * x := by group

open CFSG.ClassicalInvolution.Models.SymplecticPairs in
theorem eq_one_of_odd_of_commute_longBlock_sylow {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {n : ℕ} (Q : Fin n → Sylow 2 SL(2, F)) {g : CFSG.Open.StatedSp n F}
    (hg : Odd (orderOf g))
    (hc : ∀ k, ∀ A ∈ (Q k : Subgroup SL(2, F)), Commute g (longBlock F n k A)) : g = 1 := by
  classical
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hF
  have hsupp : ∀ k : Fin n, g ∈ suppGroup (coords k)ᶜ := by
    intro k
    have hneg : (-1 : SL(2, F)) ∈ (Q k : Subgroup SL(2, F)) :=
      CFSG.ClassicalInvolution.G2D4Models.neg_one_mem_sylow hF (Q k)
    have hcomm : Commute g (longInv F n k) := hc k (-1) hneg
    obtain ⟨a, ha, b, hb, hgab⟩ := exists_mul_of_commute_longInv h2 k hcomm.eq
    have haRange : a ∈ (longBlock F n k).range := ha
    have hbSub : b ∈ suppGroup (coords k)ᶜ := by
      rwa [complGroup_longInv h2 k] at hb
    obtain ⟨A, rfl⟩ := haRange
    have hLmem : ∀ B : SL(2, F), longBlock F n k B ∈ suppGroup (coords k) := by
      intro B
      rw [← range_longBlock]
      exact ⟨B, rfl⟩
    have hAcomm : ∀ B ∈ (Q k : Subgroup SL(2, F)),
        Commute (longBlock F n k A) (longBlock F n k B) := by
      intro B hB
      have hgL : Commute g (longBlock F n k B) := hc k B hB
      have hbL : Commute b (longBlock F n k B) :=
        (commute_suppGroup_compl (hLmem B) hbSub).symm
      have haeq : longBlock F n k A = g * b⁻¹ := by rw [hgab]; group
      rw [haeq]
      exact hgL.mul_left hbL.inv_left
    have hAcent : A ∈ Subgroup.center SL(2, F) := by
      refine CFSG.GH74.GLS.LU.Local.SL2.cent_sylow_le_center hF (Q k) (x := A) ?_
      intro B hB
      have h1 := hAcomm B hB
      exact longBlock_injective k (by rw [map_mul, map_mul]; exact h1.eq)
    have hA2 : A * A = 1 := by
      rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff A).mp hAcent with rfl | rfl
      · simp
      · show (-1 : SL(2, F)) * (-1) = 1
        simp
    have hcommab : Commute (longBlock F n k A) b :=
      commute_suppGroup_compl (hLmem A) hbSub
    have hgpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    have hLA2 : longBlock F n k A ^ 2 = 1 := by
      rw [← map_pow, show A ^ 2 = 1 by rw [sq, hA2], map_one]
    have hapow : longBlock F n k A ^ orderOf g = longBlock F n k A := by
      obtain ⟨t, ht⟩ := hg
      calc longBlock F n k A ^ orderOf g
          = ((longBlock F n k A) ^ 2) ^ t * longBlock F n k A := by
              rw [ht, pow_succ, pow_mul, sq]
        _ = longBlock F n k A := by rw [hLA2, one_pow, one_mul]
    have hbpow : b ^ orderOf g ∈ suppGroup (coords k)ᶜ := Subgroup.pow_mem _ hbSub _
    have haeq2 : longBlock F n k A = (b ^ orderOf g)⁻¹ := by
      have h1 : longBlock F n k A * b ^ orderOf g = 1 := by
        rw [← hapow, ← hcommab.mul_pow, ← hgab, hgpow]
      exact eq_inv_of_mul_eq_one_left h1
    have haone : longBlock F n k A = 1 := by
      have hmem : longBlock F n k A ∈ suppGroup (coords k) ⊓ suppGroup (coords k)ᶜ := by
        refine ⟨hLmem A, ?_⟩
        rw [haeq2]
        exact Subgroup.inv_mem _ hbpow
      exact Subgroup.disjoint_def.mp (disjoint_suppGroup_compl (coords k)) hmem.1 hmem.2
    have hgb : g = b := by rw [hgab, haone, one_mul]
    rwa [hgb]
  have hmat : CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g = 1 := by
    ext r t
    rcases r with k | k
    · exact (mem_suppGroup.mp (hsupp k)) _ _ (fun h => h.1 (inl_mem_coords k))
    · exact (mem_suppGroup.mp (hsupp k)) _ _ (fun h => h.1 (inr_mem_coords k))
  exact CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective (by rw [hmat, map_one])

private lemma exists_sylow_sl2_of_isSylowOf {F : Type} [Field F] {X : Type} [Group X] [Finite X]
    {J Q : Subgroup X} (e : ↥J ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q J) :
    ∃ Q' : Sylow 2 SL(2, F), ∀ A ∈ (Q' : Subgroup SL(2, F)),
      ∃ z : ↥J, (z : X) ∈ Q ∧ e.toMonoidHom z = A := by
  obtain ⟨T, hT⟩ := hQ
  let Q' : Sylow 2 SL(2, F) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ'coe : (Q' : Subgroup SL(2, F)) = (T : Subgroup ↥J).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  refine ⟨Q', fun A hA => ?_⟩
  rw [hQ'coe] at hA
  obtain ⟨z, hzT, hzA⟩ := Subgroup.mem_map.mp hA
  exact ⟨z, hT ▸ Subgroup.mem_map_of_mem J.subtype hzT, hzA⟩

private lemma longRootSp2_map_mulEquiv_sl2 {F : Type} [Field F] [Finite F] {X : Type}
    [Group X] {n : ℕ} (hn : 2 ≤ n) (ψ : CFSG.Open.StatedSp n F →* X)
    (hker : ψ.ker ≤ Subgroup.center (CFSG.Open.StatedSp n F)) (k : Fin n) :
    ∃ e : ↥((CFSG.ClassicalInvolution.Models.SymplecticPairs.longRootSp2 F n k).map ψ) ≃*
        SL(2, F),
      ∀ z, (ψ.comp (longBlock F n k)) (e.toMonoidHom z) = (z : X) := by
  have hι : Function.Injective (ψ.comp (longBlock F n k)) := by
    have h := CFSG.ClassicalInvolution.Models.SymplecticPairs.injective_comp_conj_longBlock
      hn ψ hker 1 k
    simpa using h
  have hrange : (ψ.comp (longBlock F n k)).range =
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longRootSp2 F n k).map ψ := by
    rw [MonoidHom.range_comp]
    rfl
  refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hι).symm, ?_⟩
  intro z
  have h := MonoidHom.ofInjective_apply (f := ψ.comp (longBlock F n k)) hι
    (x := (MonoidHom.ofInjective hι).symm
      ((MulEquiv.subgroupCongr hrange.symm) z))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans (MulEquiv.subgroupCongr_apply hrange.symm z)


theorem normSylowAt_psp {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {n r f : ℕ}
    (hr2 : r ≠ 2) (hadm : CFSG.Open.StatedLieAdmissible .PSp n r f)
    (hX : CFSG.Blueprint.LieModel X .PSp n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowAt X p := by
  have hpr : r.Prime := hadm.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Fact r.Prime := ⟨hpr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField r f
  have hFcard : Nat.card F = r ^ f := GaloisField.card r f (by omega)
  have hFodd : Odd (Nat.card F) := by
    rw [hFcard]
    exact (hpr.odd_of_ne_two hr2).pow
  refine normSylowAt_of_odd hp (by omega) ?_
  intro S hS y hyN hyodd hyp
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let P : Sylow 2 X := hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hPcoe : (P : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  have hyNP : y ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyN
  have hypP : y ^ p ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) := hPcoe.symm ▸ hyp
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSp n r f hpr hr2 (by trivial) hadm X hX
  let ψ : CFSG.Open.StatedSp n F →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ Subgroup.center (CFSG.Open.StatedSp n F) := hker0
  obtain ⟨c, hfull⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.exists_full_coordinate_frame_funSet_psp
      (p := r) hr2 hadm hX ψ hψ hker P
  let ψc : CFSG.Open.StatedSp n F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (CFSG.Open.StatedSp n F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  let Δ : Set (Subgroup X) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X)
  have hfull' : Δ = Set.range (fun k : Fin n =>
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longRootSp2 F n k).map ψc) := by
    simpa [Δ, ψc, Subgroup.map_map] using hfull
  have hconj : ∀ (g : X) {K : Subgroup X},
      fundPred (r ^ f) (⊤ : Subgroup X) K →
      fundPred (r ^ f) (⊤ : Subgroup X) (K.map (MulAut.conj g).toMonoidHom) :=
    fun g K h => CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv
      (MulAut.conj g) h
  have hSΔ : (P : Subgroup X) ≤ conjSetStab Δ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F14.sylow_le_conjSetStab_funSet hconj P
  have hyΔ : y ∈ conjSetStab Δ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F14.le_conjSetStab_of_mapsTo_conj
      (H := Subgroup.normalizer ((P : Subgroup X) : Set X))
      (fun g hg K hK =>
        CFSG.LocalAnalysis.UniquenessCase.UC22.F14.mem_funSet_map_conj_of_mem_normalizer
          hconj hg hK) hyNP
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.nonempty_equiv_perm_funSet_psp
    (p := r) hr2 hadm hX P
  have hfix : ∀ J ∈ Δ, y ∈ Subgroup.normalizer (J : Set X) :=
    mem_normalizer_of_conjSetStab_perm P hSΔ e hyΔ hyNP hyodd
  let J : Fin n → Subgroup X := fun k =>
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.longRootSp2 F n k).map ψc
  have hJΔ : ∀ k, J k ∈ Δ := by
    intro k
    rw [hfull']
    exact ⟨k, rfl⟩
  let eJ : ∀ k, ↥(J k) ≃* SL(2, F) := fun k =>
    Classical.choose (longRootSp2_map_mulEquiv_sl2 hn2 ψc hkerC k)
  have heJ : ∀ k (z : ↥(J k)), (ψc.comp (longBlock F n k)) ((eJ k).toMonoidHom z) = (z : X) :=
    fun k => Classical.choose_spec (longRootSp2_map_mulEquiv_sl2 hn2 ψc hkerC k)
  have hQex : ∀ k, ∃ Q' : Sylow 2 SL(2, F), ∀ A ∈ (Q' : Subgroup SL(2, F)),
      ∃ z : ↥(J k), (z : X) ∈ (P : Subgroup X) ⊓ J k ∧ (eJ k).toMonoidHom z = A :=
    fun k => exists_sylow_sl2_of_isSylowOf (eJ k) (hJΔ k).2
  choose Q hQ using hQex
  have hQmem : ∀ k (A : SL(2, F)), A ∈ (Q k : Subgroup SL(2, F)) →
      (ψc.comp (longBlock F n k)) A ∈ (P : Subgroup X) ⊓ J k := by
    intro k A hA
    obtain ⟨z, hz, hzA⟩ := hQ k A hA
    rw [← hzA, heJ k z]
    exact hz
  have hyC : ∀ k, y ∈ Subgroup.centralizer (((P : Subgroup X) ⊓ J k : Subgroup X) : Set X) := by
    intro k
    refine mem_centralizer_of_isSylowOf_sl2 hFodd (K := J k) (Q := (P : Subgroup X) ⊓ J k) (eJ k)
      (hJΔ k).2 ?_ hp hp5 ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hyNP, hfix (J k) (hJΔ k)⟩)
    · exact Subgroup.centralizer_le (inf_le_left : (P : Subgroup X) ⊓ J k ≤ P) hypP
  obtain ⟨yt, hψyt, hytodd⟩ :=
    CFSG.ClassicalInvolution.Q3.exists_odd_orderOf_lift ψc hψc hyodd
  have hker2 : ∀ z ∈ ψc.ker, z * z = 1 := fun z hz =>
    CFSG.ClassicalInvolution.Models.SymplecticPairs.mul_self_eq_one_of_mem_center
      (by omega) (hkerC hz)
  have hc : ∀ k, ∀ A ∈ (Q k : Subgroup SL(2, F)),
      Commute yt (longBlock F n k A) := by
    intro k A hA
    have hmem : (ψc.comp (longBlock F n k)) A ∈ (P : Subgroup X) ⊓ J k := hQmem k A hA
    have hcomm : Commute (ψc yt) ((ψc.comp (longBlock F n k)) A) := by
      rw [hψyt]
      exact (Subgroup.mem_centralizer_iff.mp (hyC k) ((ψc.comp (longBlock F n k)) A) hmem).symm
    exact commute_of_odd_orderOf_of_map_commute ψc hkerC hker2 hytodd hcomm
  have htriv : yt = 1 := eq_one_of_odd_of_commute_longBlock_sylow hFodd Q hytodd hc
  have hy1 : y = 1 := by rw [← hψyt, htriv, map_one]
  have hyCP : y ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    rw [hy1]
    exact Subgroup.one_mem _
  exact hPcoe ▸ hyCP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
