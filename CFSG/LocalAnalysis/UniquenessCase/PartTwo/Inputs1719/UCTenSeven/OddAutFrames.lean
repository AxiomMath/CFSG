module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
import CFSG.Permutation.SylowTwoNormalizer.Sym
import CFSG.GroupTheory.QuaternionAutPrime
import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open scoped MatrixGroups

private lemma mulAut_zpow_apply_eq_self {X : Type} [Group X] {β : MulAut X} {x : X}
    (hβ : β x = x) : ∀ z : ℤ, (β ^ z) x = x := by
  have hpow : ∀ n : ℕ, (β ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hβ, ih]
  have hinv : ∀ γ : MulAut X, γ x = x → (γ⁻¹) x = x := by
    intro γ hγ
    have h := congrArg (fun y => (γ⁻¹) y) hγ
    simpa using h.symm
  intro z
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg z
  · rw [hn]; simpa using hpow n
  · rw [hn, zpow_neg, zpow_natCast]
    exact hinv _ (hpow n)

theorem normSylowIn_of_odd {X : Type} [Group X] [Finite X] {D : Subgroup (MulAut X)} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ α ∈ D, Odd (orderOf α) →
      S.map α.toMonoidHom = S → (∀ x ∈ S, (α ^ p) x = x) → ∀ x ∈ S, α x = x) :
    NormSylowIn X D p := by
  intro S hS α hαD hαS hαp x hx
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos α).ne'
  set α' : MulAut X := α ^ 2 ^ a with hα'def
  have hdvd : 2 ^ a ∣ orderOf α := ⟨m, hn⟩
  have hga : orderOf α' = m := by
    rw [hα'def, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hα'D : α' ∈ D := D.pow_mem hαD _
  have hS' : S.map ((α : MulAut X) : X →* X) = S := hαS
  have hmap : ∀ k : ℕ, S.map ((α ^ k : MulAut X) : X →* X) = S := by
    intro k
    induction k with
    | zero => ext y; simp
    | succ k ih =>
        rw [show ((α ^ (k + 1) : MulAut X) : X →* X) =
          ((α ^ k : MulAut X) : X →* X).comp (α : X →* X) from rfl,
          ← Subgroup.map_map, hS', ih]
  have hα'S : S.map α'.toMonoidHom = S := by
    rw [hα'def]
    simpa using hmap (2 ^ a)
  have hα'p : ∀ y ∈ S, (α' ^ p) y = y := by
    have hαp_pow : ∀ k : ℕ, ∀ y ∈ S, ((α ^ p) ^ k) y = y := by
      intro k
      induction k with
      | zero => intro y hy; simp
      | succ k ih =>
          intro y hy
          rw [pow_succ, MulAut.mul_apply, hαp y hy, ih y hy]
    have hpoweq : α' ^ p = (α ^ p) ^ 2 ^ a := by
      rw [hα'def, ← pow_mul, ← pow_mul, Nat.mul_comm]
    intro y hy
    rw [hpoweq]
    exact hαp_pow _ y hy
  have hα'fix : ∀ y ∈ S, α' y = y :=
    h S hS α' hα'D (by rw [hga]; exact hm) hα'S hα'p
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2))
  have hu : ((2 ^ a : ℕ) : ℤ) * (Nat.gcdA (2 ^ a) p : ℤ) +
      (p : ℤ) * (Nat.gcdB (2 ^ a) p : ℤ) = 1 := by
    have h1 := Nat.gcd_eq_gcd_ab (2 ^ a) p
    rw [hcop.gcd_eq_one, Nat.cast_one] at h1
    exact h1.symm
  have h1 : α' ^ (Nat.gcdA (2 ^ a) p : ℤ) =
      α ^ (((2 ^ a : ℕ) : ℤ) * (Nat.gcdA (2 ^ a) p : ℤ)) := by
    rw [hα'def, ← zpow_natCast,
      (zpow_mul α ((2 ^ a : ℕ) : ℤ) (Nat.gcdA (2 ^ a) p : ℤ)).symm]
  have h2 : (α ^ p) ^ (Nat.gcdB (2 ^ a) p : ℤ) =
      α ^ ((p : ℤ) * (Nat.gcdB (2 ^ a) p : ℤ)) := by
    rw [← zpow_natCast, (zpow_mul α (p : ℤ) (Nat.gcdB (2 ^ a) p : ℤ)).symm]
  have hαeq : α = α' ^ (Nat.gcdA (2 ^ a) p : ℤ) *
      (α ^ p) ^ (Nat.gcdB (2 ^ a) p : ℤ) := by
    rw [h1, h2, ← zpow_add, hu, zpow_one]
  rw [hαeq, MulAut.mul_apply,
    mulAut_zpow_apply_eq_self (hαp x hx),
    mulAut_zpow_apply_eq_self (hα'fix x hx)]

private lemma subgroup_map_inv_map_conj_map {X : Type} [Group X] (K : Subgroup X) (s : X)
    (θ : MulAut X) :
    (((K.map ((θ⁻¹ : MulAut X) : X →* X)).map (MulAut.conj s).toMonoidHom)).map
        ((θ : MulAut X) : X →* X) = K.map (MulAut.conj (θ s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_eq_of_odd_of_conjSetStab_perm {X : Type} [Group X] [Finite X]
    {Δ : Set (Subgroup X)} (S : Sylow 2 X) (hS : (S : Subgroup X) ≤ conjSetStab Δ)
    {α : Type} [Finite α] (e : (conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm α)
    (hcard : Nat.card Δ = Nat.card α) (θ : MulAut X)
    (hθΔ : ∀ J ∈ Δ, J.map θ.toMonoidHom ∈ Δ)
    (hθS : (S : Subgroup X).map θ.toMonoidHom = S) (hθ : Odd (orderOf θ)) :
    ∀ J ∈ Δ, J.map θ.toMonoidHom = J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥Δ := Fintype.ofFinite ↥Δ
  have : Fintype α := Fintype.ofFinite α
  let f : ↥Δ → ↥Δ := fun J => ⟨J.1.map θ.toMonoidHom, hθΔ J.1 J.2⟩
  have hf : Function.Injective f := by
    intro J K hJK
    apply Subtype.ext
    exact Subgroup.map_injective (f := θ.toMonoidHom) θ.injective (congrArg Subtype.val hJK)
  let π : Equiv.Perm ↥Δ :=
    Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  have hπcoe : ∀ J : ↥Δ, ((π J : ↥Δ) : Subgroup X) =
      (J : Subgroup X).map ((θ : MulAut X) : X →* X) := by
    intro J
    rw [show π J = f J from Equiv.ofBijective_apply f _ J]
    rfl
  have hπpow : ∀ k : ℕ, ∀ J : ↥Δ,
      (((π ^ k) J : ↥Δ) : Subgroup X) = (J : Subgroup X).map ((θ ^ k : MulAut X) : X →* X) := by
    intro k
    induction k with
    | zero =>
        intro J
        rw [pow_zero, pow_zero]
        ext x
        simp
    | succ k ih =>
        intro J
        have hstep : ((π ^ (k + 1)) J : ↥Δ) = (π ^ k) (π J) := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hstep, ih, hπcoe J, Subgroup.map_map]
        rfl
  have hπord : Odd (orderOf π) := by
    have htop : π ^ orderOf θ = 1 := by
      refine Equiv.ext fun J => ?_
      apply Subtype.ext
      rw [hπpow (orderOf θ) J, pow_orderOf_eq_one]
      ext x
      simp
    exact Odd.of_dvd_nat hθ (orderOf_dvd_of_pow_eq_one htop)
  let ρ : ↥(conjSetStab Δ) →* Equiv.Perm ↥Δ := conjPermHom (le_refl (conjSetStab Δ))
  have hRcard : Nat.card ρ.range = Nat.card (Equiv.Perm ↥Δ) := by
    have h1 : Nat.card ρ.range = Nat.card (Equiv.Perm α) := Nat.card_congr e.toEquiv
    rw [h1]
    have hfc : Fintype.card α = Fintype.card ↥Δ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard.symm
    exact Nat.card_congr (Equiv.permCongr (Fintype.equivOfCardEq hfc))
  have hRtop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq ρ.range hRcard
  have hρsurj : Function.Surjective ρ := fun y =>
    MonoidHom.mem_range.mp (by rw [hRtop]; exact Subgroup.mem_top y)
  let S' : Sylow 2 ↥(conjSetStab Δ) := S.subtype hS
  let R' : Sylow 2 (Equiv.Perm ↥Δ) := S'.mapSurjective (f := ρ) hρsurj
  have hR'coe : (R' : Subgroup (Equiv.Perm ↥Δ)) = (S' : Subgroup ↥(conjSetStab Δ)).map ρ :=
    Sylow.coe_mapSurjective hρsurj S'
  have hS'coe : (S' : Subgroup ↥(conjSetStab Δ)) =
      (S : Subgroup X).subgroupOf (conjSetStab Δ) := Sylow.coe_subtype S hS
  have hθS' : (S : Subgroup X).map ((θ : MulAut X) : X →* X) = S := hθS
  have hθsmem : ∀ (s : X), s ∈ S → θ s ∈ S := by
    intro s hs
    have h : θ s ∈ (S : Subgroup X).map ((θ : MulAut X) : X →* X) :=
      Subgroup.mem_map_of_mem ((θ : MulAut X) : X →* X) hs
    rwa [hθS'] at h
  have hρapply : ∀ (n : ↥(conjSetStab Δ)) (K : ↥Δ),
      ((ρ n K : ↥Δ) : Subgroup X) =
        (K : Subgroup X).map (MulAut.conj (n : X)).toMonoidHom := by
    intro n K
    rw [show ρ n K = conjPermHom (le_refl (conjSetStab Δ)) n K from rfl,
      CFSG.ComponentClassification.AS81.Sec2.conjPermHom_apply]
    rw [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
  have hπinvcoe : ∀ J : ↥Δ, ((π⁻¹ J : ↥Δ) : Subgroup X) =
      (J : Subgroup X).map ((θ⁻¹ : MulAut X) : X →* X) := by
    have hcomp1 : ((θ : MulAut X) : X →* X).comp ((θ⁻¹ : MulAut X) : X →* X) =
        MonoidHom.id X := by
      ext x
      simp
    intro J
    apply Subgroup.map_injective (f := ((θ : MulAut X) : X →* X)) θ.injective
    have hlhs : (((π⁻¹ J : ↥Δ)) : Subgroup X).map ((θ : MulAut X) : X →* X) =
        (J : Subgroup X) := by
      have h := hπcoe (π⁻¹ J)
      rw [show π (π⁻¹ J) = J from Equiv.apply_symm_apply π J] at h
      exact h.symm
    rw [hlhs, Subgroup.map_map, hcomp1]
    ext x
    simp
  have hconjρ : ∀ (s : X) (hs : s ∈ S),
      π * ρ ⟨s, hS hs⟩ * π⁻¹ = ρ ⟨θ s, hS (hθsmem s hs)⟩ := by
    intro s hs
    refine Equiv.ext fun J => ?_
    apply Subtype.ext
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπcoe, hρapply, hπinvcoe, hρapply]
    exact subgroup_map_inv_map_conj_map (J : Subgroup X) s θ
  have hmemR' : ∀ (s : X) (hs : s ∈ S),
      ρ ⟨s, hS hs⟩ ∈ (R' : Subgroup (Equiv.Perm ↥Δ)) := by
    intro s hs
    rw [hR'coe, hS'coe]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hs)
  have hle : (R' : Subgroup (Equiv.Perm ↥Δ)).map (MulAut.conj π).toMonoidHom ≤ R' := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    rw [hR'coe] at hx ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have htm : (t : X) ∈ S := by
      rw [hS'coe, Subgroup.mem_subgroupOf] at ht
      exact ht
    rw [show t = (⟨(t : X), hS htm⟩ : ↥(conjSetStab Δ)) from Subtype.ext rfl]
    refine Subgroup.mem_map.mpr ⟨⟨θ (t : X), hS (hθsmem (t : X) htm)⟩,
      Subgroup.mem_subgroupOf.mpr (hθsmem (t : X) htm), ?_⟩
    simpa [MulAut.conj_apply] using (hconjρ (t : X) htm).symm
  have heq : (R' : Subgroup (Equiv.Perm ↥Δ)).map (MulAut.conj π).toMonoidHom = R' := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj π).injective]
  have hπN : π ∈ normalizer ((R' : Subgroup (Equiv.Perm ↥Δ)) : Set (Equiv.Perm ↥Δ)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hπ1 : π = 1 :=
    CFSG.Permutation.SylowTwoNormalizer.eq_one_of_mem_normalizer R'.isPGroup'
      R'.not_dvd_index hπord hπN
  intro J hJ
  have h := hπcoe ⟨J, hJ⟩
  rw [hπ1] at h
  simpa using h.symm

theorem fixes_of_isSylowOf_sl2 {X F : Type} [Group X] [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {K Q : Subgroup X} (e : K ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) (θ : MulAut X) (hθQ : Q.map θ.toMonoidHom = Q)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hθp : ∀ x ∈ Q, (θ ^ p) x = x) :
    ∀ x ∈ Q, θ x = x := by
  have : Finite ↥K := Finite.of_equiv (SL(2, F)) e.symm.toEquiv
  obtain ⟨Q₀, hQ₀⟩ := hQ
  obtain ⟨k, hk, ⟨eQ₀⟩⟩ := CFSG.ClassicalInvolution.Asc77.exists_quaternion_equiv_sylow hF e Q₀
  let eQ : ↥Q ≃* QuaternionGroup (2 ^ k) :=
    ((MulEquiv.subgroupCongr hQ₀.symm).trans
      (Subgroup.equivMapOfInjective Q₀ K.subtype K.subtype_injective).symm).trans eQ₀
  let σ : MulAut ↥Q :=
    (MulEquiv.subgroupMap θ Q).trans (MulEquiv.subgroupCongr hθQ)
  have hσcoe : ∀ s : ↥Q, ((σ s : ↥Q) : X) = θ (s : X) := by
    intro s
    have h := MulEquiv.coe_subgroupMap_apply θ Q s
    have h2 := MulEquiv.subgroupCongr_apply hθQ ((MulEquiv.subgroupMap θ Q) s)
    calc (((MulEquiv.subgroupCongr hθQ) ((MulEquiv.subgroupMap θ Q) s) : ↥Q) : X)
        = (((MulEquiv.subgroupMap θ Q) s : ↥(Q.map θ.toMonoidHom)) : X) := h2
      _ = θ (s : X) := h
  have hσpow : ∀ j : ℕ, ∀ s : ↥Q, (((σ ^ j) s : ↥Q) : X) = (θ ^ j) (s : X) := by
    intro j
    induction j with
    | zero => intro s; simp
    | succ j ih =>
        intro s
        have hσstep : ((σ ^ (j + 1)) s : ↥Q) = σ ((σ ^ j) s) := by
          rw [pow_succ', MulAut.mul_apply]
        have hθstep : (θ ^ (j + 1)) (s : X) = θ ((θ ^ j) (s : X)) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [hσstep, hθstep, hσcoe, ih]
  have hσp : σ ^ p = 1 := by
    refine MulEquiv.ext fun s => ?_
    apply Subtype.ext
    rw [hσpow p s, hθp (s : X) s.2]
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
  intro x hx
  have hxfix : σ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hσ1]; rfl
  have h := hσcoe ⟨x, hx⟩
  rw [hxfix] at h
  exact h.symm

theorem commute_of_odd_of_pow_two_pow_of_mem_center {G : Type} [Group G] {g b : G}
    (hg : Odd (orderOf g)) {k : ℕ} (hb : b ^ 2 ^ k = 1)
    (hc : g * b * g⁻¹ * b⁻¹ ∈ center G) : Commute g b := by
  set c : G := g * b * g⁻¹ * b⁻¹ with hcdef
  have hcC : ∀ z : G, z * c = c * z := fun z => Subgroup.mem_center_iff.mp hc z
  have hgb : g * b * g⁻¹ = c * b := by rw [hcdef]; group
  have hcg : Commute g c := hcC g
  have hcb : Commute c b := (hcC b).symm
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
          _ = c ^ (j + 1) * b := by rw [pow_succ]; group
  have hcm : c ^ orderOf g = 1 := by
    have h1 : c ^ orderOf g * b = b := by
      have h2 := hpow (orderOf g)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h2
      exact h2.symm
    exact mul_right_cancel (by rw [h1, one_mul] : c ^ orderOf g * b = 1 * b)
  have hc2k : c ^ 2 ^ k = 1 := by
    have h1 : (c * b) ^ 2 ^ k = c ^ 2 ^ k * b ^ 2 ^ k := hcb.mul_pow _
    rw [hb, mul_one] at h1
    have h2 : (c * b) ^ 2 ^ k = 1 := by
      rw [← hgb, conj_pow, hb]
      group
    rw [h2] at h1
    exact h1.symm
  have hdvd1 : orderOf c ∣ orderOf g := orderOf_dvd_of_pow_eq_one hcm
  have hdvd2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2k
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hg hdvd1
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd2)
  have hfix : g * b * g⁻¹ = b := by rw [hgb, hc1, one_mul]
  show g * b = b * g
  calc g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [hfix]

theorem fixes_of_odd_of_mul_inv_mem {X : Type} [Group X] {P N : Subgroup X}
    (hP : IsPGroup 2 P) (hNP : N ≤ P) (θ : MulAut X) (hθ : Odd (orderOf θ))
    (hN : ∀ x ∈ N, θ x = x) (hPN : ∀ s ∈ P, θ s * s⁻¹ ∈ N) : ∀ s ∈ P, θ s = s := by
  intro s hs
  set n : X := θ s * s⁻¹ with hndef
  have hnN : n ∈ N := hPN s hs
  have hnP : n ∈ P := hNP hnN
  have hnθ : θ n = n := hN n hnN
  have hθs : θ s = n * s := by rw [hndef]; group
  have hnfix : ∀ j : ℕ, (θ ^ j) n = n := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hnθ, ih]
  have hpow : ∀ j : ℕ, (θ ^ j) s = n ^ j * s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, MulAut.mul_apply, hθs, map_mul, hnfix j, ih, pow_succ]
        group
  have h1 : s = n ^ orderOf θ * s := by
    have h2 := hpow (orderOf θ)
    rwa [pow_orderOf_eq_one, MulAut.one_apply] at h2
  have hn1 : n ^ orderOf θ = 1 := by
    have h := congrArg (fun y => y * s⁻¹) h1
    simpa using h.symm
  have hdvd : orderOf n ∣ orderOf θ := orderOf_dvd_of_pow_eq_one hn1
  have hnodd : Odd (orderOf n) := Odd.of_dvd_nat hθ hdvd
  obtain ⟨m, hm⟩ := hP ⟨n, hnP⟩
  have hdvd2 : orderOf n ∣ 2 ^ m := by
    have h := orderOf_dvd_of_pow_eq_one hm
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime (orderOf n) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hnodd)
  have hone : orderOf n = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd2
  have hn1' : n = 1 := orderOf_eq_one_iff.mp hone
  rw [hθs, hn1', one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
