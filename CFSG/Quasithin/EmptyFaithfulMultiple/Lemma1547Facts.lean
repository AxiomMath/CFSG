module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section FourGroup

variable {W : Type*} [Group W]

theorem mem_of_card_eq_four {U : Subgroup W} (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    {u₀ x : W} (hu₀U : u₀ ∈ U) (hxU : x ∈ U) (hu₀ : u₀ ≠ 1) (hx : x ≠ 1) (hxu₀ : x ≠ u₀) :
    ∀ y ∈ U, y = 1 ∨ y = u₀ ∨ y = x ∨ y = x * u₀ := by
  classical
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype U := Fintype.ofFinite U
  have hinv : u₀⁻¹ = u₀ := by
    have h := hU2 u₀ hu₀U
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have h1 : x * u₀ ≠ 1 := by
    intro h
    apply hxu₀
    rw [← hinv]
    exact eq_inv_of_mul_eq_one_left h
  have h2 : x * u₀ ≠ u₀ := fun h => hx (by simpa using h)
  have h3 : x * u₀ ≠ x := fun h => hu₀ (by simpa using h)
  let s : Finset U := {⟨1, U.one_mem⟩, ⟨u₀, hu₀U⟩, ⟨x, hxU⟩, ⟨x * u₀, U.mul_mem hxU hu₀U⟩}
  have hs : s.card = 4 := by
    simp only [s]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · simpa [Subtype.ext_iff] using h3.symm
    · simp [Subtype.ext_iff, hxu₀.symm, h2.symm]
    · simp [Subtype.ext_iff, hu₀.symm, hx.symm, h1.symm]
  have huniv : s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hs, ← Nat.card_eq_fintype_card, hU4]
  intro y hy
  have hmem : (⟨y, hy⟩ : U) ∈ s := by rw [huniv]; exact Finset.mem_univ _
  simp only [s, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
  exact hmem

theorem exists_ne_of_card_eq_four {U : Subgroup W} (hU4 : Nat.card U = 4) (u₀ : W) :
    ∃ x ∈ U, x ≠ 1 ∧ x ≠ u₀ := by
  classical
  by_contra h
  push Not at h
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  let f : U → Bool := fun y => decide ((y : W) = 1)
  have hf : Function.Injective f := by
    intro y y' hyy'
    have hiff : (y : W) = 1 ↔ (y' : W) = 1 := decide_eq_decide.mp hyy'
    apply Subtype.ext
    by_cases hy : (y : W) = 1
    · rw [hy, hiff.mp hy]
    · rw [h y y.2 hy, h y' y'.2 (fun h' => hy (hiff.mpr h'))]
  have := Nat.card_le_card_of_injective f hf
  rw [hU4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
  omega

theorem mulAut_fix_of_card_eq_four {U : Subgroup W} (hU4 : Nat.card U = 4)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (a : MulAut W) (haU : ∀ u ∈ U, a u ∈ U) {u₀ : W} (hu₀U : u₀ ∈ U)
    (hu₀ : u₀ ≠ 1) (hau₀ : a u₀ = u₀) {k : ℕ} (hk : Odd k) (hak : a ^ k = 1) :
    ∀ u ∈ U, a u = u := by
  obtain ⟨x, hxU, hx1, hxu₀⟩ := exists_ne_of_card_eq_four hU4 u₀
  have hcases := mem_of_card_eq_four hU4 hU2 hu₀U hxU hu₀ hx1 hxu₀
  have hax : a x = x := by
    rcases hcases (a x) (haU x hxU) with h | h | h | h
    · exact absurd ((MulEquiv.map_eq_one_iff a).1 h) hx1
    · exact absurd (a.injective (h.trans hau₀.symm)) hxu₀
    · exact h
    · exfalso
      have hsq : (a ^ 2) x = x := by
        rw [pow_two, MulAut.mul_apply, h, map_mul, h, hau₀, mul_assoc, ← pow_two,
          hU2 u₀ hu₀U, mul_one]
      have hiter : ∀ n : ℕ, ((a ^ 2) ^ n) x = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hsq, ih]
      obtain ⟨j, rfl⟩ := hk
      have hodd : (a ^ (2 * j + 1)) x = x * u₀ := by
        rw [pow_succ, MulAut.mul_apply, h, map_mul, pow_mul, hiter, ← pow_mul]
        have hu : (a ^ (2 * j)) u₀ = u₀ := by
          have hiter' : ∀ n : ℕ, (a ^ n) u₀ = u₀ := by
            intro n
            induction n with
            | zero => rfl
            | succ n ih => rw [pow_succ, MulAut.mul_apply, hau₀, ih]
          exact hiter' _
        rw [hu]
      rw [hak, MulAut.one_apply] at hodd
      exact hu₀ (by simpa using hodd.symm)
  intro y hy
  rcases hcases y hy with rfl | rfl | rfl | rfl
  · exact map_one a
  · exact hau₀
  · exact hax
  · rw [map_mul, hax, hau₀]

end FourGroup

section Rank

theorem card_mulAut_le_six {U : Type*} [Group U] [Finite U] (hU4 : Nat.card U = 4) :
    Nat.card (MulAut U) ≤ 6 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  let f : MulAut U → Equiv.Perm {u : U // u ≠ 1} := fun a =>
    Equiv.Perm.subtypePerm a.toEquiv (fun u => MulEquiv.map_ne_one_iff a)
  have hf : Function.Injective f := by
    intro a b hab
    ext u
    by_cases hu : u = 1
    · rw [hu, map_one, map_one]
    · have := congrArg (fun π => ((π ⟨u, hu⟩ : {u : U // u ≠ 1}) : U)) hab
      simpa [f] using this
  have h3 : Nat.card {u : U // u ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hU4]
  calc Nat.card (MulAut U) ≤ Nat.card (Equiv.Perm {u : U // u ≠ 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = 6 := by rw [Nat.card_perm, h3]; rfl

theorem card_le_three_of_isPGroup_three {U : Type*} [Group U] [Finite U] (hU4 : Nat.card U = 4)
    {R : Subgroup (MulAut U)} (hR : IsPGroup 3 R) : Nat.card R ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Nat.card R ≤ 6 := (Subgroup.card_le_card_group R).trans (card_mulAut_le_six hU4)
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn] at hle ⊢
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have : 9 ≤ 3 ^ (n + 1 + 1) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

variable {G : Type*} [Group G]

omit [Group G] in
theorem conjAct_eq_one_of_mem_centralizer [Group G] {V : Subgroup G}
    {g : Subgroup.normalizer (V : Set G)} (hg : (g : G) ∈ Subgroup.centralizer (V : Set G)) :
    conjAct V g = 1 := by
  ext v
  change (V.normalizerMonoidHom (Subgroup.inclusion le_rfl g) v : G) = v
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  change (g : G) * v * (g : G)⁻¹ = v
  rw [(Subgroup.mem_centralizer_iff.mp hg v v.2).symm, mul_inv_cancel_right]

theorem relIndex_le_three_of_card_eq_four [Finite G] {U H : Subgroup G} (hU4 : Nat.card U = 4)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (h3 : ∀ h ∈ H, ∃ k : ℕ, h ^ 3 ^ k ∈ Subgroup.centralizer (U : Set G)) :
    (H ⊓ Subgroup.centralizer (U : Set G)).relIndex H ≤ 3 := by
  rw [← card_autOn_eq_relIndex hHU]
  apply card_le_three_of_isPGroup_three hU4
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hφ
  obtain ⟨k, hk⟩ := h3 g (Subgroup.mem_subgroupOf.mp hg)
  refine ⟨k, Subtype.ext ?_⟩
  change (conjAct U g) ^ 3 ^ k = 1
  rw [← map_pow]
  exact conjAct_eq_one_of_mem_centralizer (by simpa using hk)

end Rank

section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem exists_ne_one_commute_of_le_normalizer {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hU : IsPGroup 2 U) (hUne : U ≠ ⊥) (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ t ∈ T, t * u = u * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : T →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hTU)
  let : MulAction T U := MulAction.compHom U φ
  have hdvd : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hUne
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : U) ∈ MulAction.fixedPoints T U := fun t => map_one (φ t)
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun t ht => ?_⟩
  have hbt : ((φ ⟨t, ht⟩ b : U) : G) = b := congrArg Subtype.val (hb ⟨t, ht⟩)
  change (U.normalizerMonoidHom (Subgroup.inclusion hTU ⟨t, ht⟩) b : G) = b at hbt
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hbt
  change t * b * t⁻¹ = b at hbt
  calc t * (b : G) = t * b * t⁻¹ * t := by group
    _ = b * t := by rw [hbt]

end Fixed

section Subnormal

theorem mem_of_isSubnormal_of_odd {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y}
    (hH : H.IsSubnormal) (hidx : ∃ k : ℕ, H.index = 2 ^ k) {g : Y} (hg : Odd (orderOf g)) :
    g ∈ H := by
  revert hidx
  induction hH with
  | top => exact fun _ => Subgroup.mem_top g
  | step H K hle hK hN ih =>
    rintro ⟨k, hk⟩
    have hpow : ∀ n : ℕ, n ∣ 2 ^ k → ∃ j : ℕ, n = 2 ^ j := fun n hn => by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
      exact ⟨j, hj⟩
    have hgK : g ∈ K := ih (hpow _ (hk ▸ Subgroup.index_dvd_of_le hle))
    obtain ⟨j, hj⟩ := hpow _ (hk ▸ Subgroup.relIndex_dvd_index_of_le hle)
    let q : K ⧸ H.subgroupOf K := ((⟨g, hgK⟩ : K) : K ⧸ H.subgroupOf K)
    have hq1 : q ^ 2 ^ j = 1 := by
      have hcard : Nat.card (K ⧸ H.subgroupOf K) = 2 ^ j := by
        rw [← Subgroup.index_eq_card]
        exact hj
      rw [← hcard]
      exact pow_card_eq_one'
    have hq2 : q ^ orderOf g = 1 := by
      have : (⟨g, hgK⟩ : K) ^ orderOf g = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      change ((⟨g, hgK⟩ : K) : K ⧸ H.subgroupOf K) ^ orderOf g = 1
      rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ j) (orderOf g) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
    have hq : q = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)

end Subnormal

section Index

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_sup_eq_relIndex {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = H.relIndex K := by
  have hK1 : K.relIndex (H ⊔ K) = K.relIndex H := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hHK
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK).toEquiv.symm
  have e1 := Subgroup.relIndex_mul_card H (H ⊔ K)
  have e2 := Subgroup.relIndex_mul_card K (H ⊔ K)
  have e3 := Subgroup.relIndex_mul_card H K
  have e4 := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.mpr (le_sup_left : H ≤ H ⊔ K)] at e1
  rw [inf_eq_left.mpr (le_sup_right : K ≤ H ⊔ K), hK1] at e2
  rw [inf_comm] at e4
  have hpos : 0 < Nat.card H := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc H.relIndex (H ⊔ K) * Nat.card H = K.relIndex H * Nat.card K := by rw [e1, e2]
    _ = K.relIndex H * (H.relIndex K * Nat.card ↥(H ⊓ K)) := by rw [e3]
    _ = H.relIndex K * (K.relIndex H * Nat.card ↥(H ⊓ K)) := by ring
    _ = H.relIndex K * Nat.card H := by rw [e4]

end Index

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
