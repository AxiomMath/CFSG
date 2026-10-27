module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Res2

theorem apply_apply_eq_of_card_three {Q : Type*} [Group Q] (hQ : Nat.card Q = 3) (φ : Q →* Q)
    (hφ : Function.Injective φ) (x : Q) : φ (φ x) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  have h3 : ∀ y : Q, y ^ (3 : ℤ) = 1 := fun y => by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← hQ]
    exact pow_card_eq_one'
  obtain ⟨m, hm⟩ := φ.map_cyclic
  have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  ·
    exfalso
    have htriv : ∀ y : Q, φ y = 1 := fun y => by
      rw [hm, zpow_eq_zpow_emod m (h3 y), h0, zpow_zero]
    have : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial, hQ]
      norm_num
    obtain ⟨y, hy⟩ := exists_ne (1 : Q)
    exact hy (hφ ((htriv y).trans (map_one φ).symm))
  · rw [hm, hm, ← zpow_mul, zpow_eq_zpow_emod (m * m) (h3 x), Int.mul_emod, h1]
    norm_num
  · rw [hm, hm, ← zpow_mul, zpow_eq_zpow_emod (m * m) (h3 x), Int.mul_emod, h2]
    norm_num

theorem sq_eq_one_of_pow_four {D : Type*} [Group D] (hD9 : Nat.card D = 9)
    (hcomm : ∀ x y : D, x * y = y * x) {d : D} (hd3 : orderOf d = 3) {σ : MulAut D}
    (hσ : σ d ∈ Subgroup.zpowers d) (h4 : σ ^ 4 = 1) : σ ^ 2 = 1 := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD9]; norm_num)
  set H := Subgroup.zpowers d with hHdef
  have hH3 : Nat.card H = 3 := by rw [hHdef, Nat.card_zpowers, hd3]
  have hHn : H.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hσH : ∀ h ∈ H, σ h ∈ H := by
    rintro _ ⟨k, rfl⟩
    change σ (d ^ k) ∈ H
    rw [map_zpow]
    exact Subgroup.zpow_mem _ hσ k
  let φ : H →* H := (σ.toMonoidHom.comp H.subtype).codRestrict H fun h => hσH h h.2
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (σ.injective (congrArg Subtype.val hab))
  have hσσH : ∀ h ∈ H, σ (σ h) = h := fun h hh =>
    congrArg Subtype.val (apply_apply_eq_of_card_three hH3 φ hφinj ⟨h, hh⟩)
  let ψ : D ⧸ H →* D ⧸ H := QuotientGroup.map H H σ.toMonoidHom fun h hh => hσH h hh
  have hQ3 : Nat.card (D ⧸ H) = 3 := by
    have h := H.card_eq_card_quotient_mul_card_subgroup
    rw [hD9, hH3] at h
    omega
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : σ x ∈ H := (QuotientGroup.eq_one_iff _).mp hq
      have h1 : σ (σ (σ x)) = σ x := hσσH _ hx
      have h2 : σ (σ x) = x := σ.injective h1
      rw [QuotientGroup.eq_one_iff, ← h2]
      exact hσH _ hx
  have hσσQ : ∀ x : D, x⁻¹ * σ (σ x) ∈ H := fun x => by
    have h := apply_apply_eq_of_card_three hQ3 ψ hψinj (x : D ⧸ H)
    exact QuotientGroup.eq.mp h.symm
  have hsq : ∀ x : D, (σ ^ 2) x = σ (σ x) := fun x => by
    rw [pow_two, MulAut.mul_apply]
  refine MulEquiv.ext fun x => ?_
  rw [hsq, MulAut.one_apply]
  set h := x⁻¹ * σ (σ x) with hh
  have hhH : h ∈ H := hσσQ x
  have hx' : σ (σ x) = x * h := by rw [hh, mul_inv_cancel_left]
  have h4x : σ (σ (σ (σ x))) = x * h * h := by
    rw [hx', map_mul, map_mul, hx', hσσH h hhH]
  have h4' : σ (σ (σ (σ x))) = x := by
    have := congrArg (fun τ : MulAut D => τ x) h4
    simp only [MulAut.one_apply] at this
    rwa [show (4 : ℕ) = 2 + 2 from rfl, pow_add, MulAut.mul_apply, hsq, hsq] at this
  have hh2 : h * h = 1 := by
    have := h4x.symm.trans h4'
    rw [mul_assoc] at this
    exact mul_eq_left.mp this
  have hh3 : h ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hhH
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hd3,
      pow_orderOf_eq_one, one_zpow]
  have h1 : h = 1 := by
    calc h = h ^ 3 * (h * h)⁻¹ := by group
      _ = 1 := by rw [hh3, hh2]; group
  rw [hx', h1, mul_one]

variable {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X} {K : Subgroup X}

theorem autIn_apply_d_mem (h : InnerConfig424 X D c d K) {σ : MulAut D}
    (hσ : σ ∈ autIn (⊤ : Subgroup X) D) :
    σ ⟨d, h.d_mem⟩ ∈ Subgroup.zpowers (⟨d, h.d_mem⟩ : D) := by
  obtain ⟨g, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
  have hgd := h.normalizer_le hN
  have h1 : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp hgd d).mp (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := h1
  change d ^ k = g * d * g⁻¹ at hk
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_zpow]
  rw [Sec4.normalizerMonoidHom_apply_coe]
  exact hk

theorem sq_eq_one_of_mem_autIn (h : InnerConfig424 X D c d K) {σ : MulAut D}
    (hσ : σ ∈ autIn (⊤ : Subgroup X) D) (h4 : σ ^ 4 = 1) : σ ^ 2 = 1 := by
  have hDe := h.maximal.prop
  have hd1 : d ≠ 1 := fun hd => h.d_not_mem (hd ▸ Subgroup.one_mem _)
  have hd3 : orderOf (⟨d, h.d_mem⟩ : D) = 3 :=
    orderOf_eq_prime (Subtype.ext (hDe.2 d h.d_mem)) fun h1 => hd1 (congrArg Subtype.val h1)
  exact sq_eq_one_of_pow_four h.card_eq (fun x y => hDe.1.is_comm.comm x y) hd3
    (autIn_apply_d_mem h hσ) h4

theorem false_of_pow_four (h : InnerConfig424 X D c d K)
    (hσ : ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1) : False := by
  obtain ⟨σ, hσ, h4, h2⟩ := hσ
  exact h2 (sq_eq_one_of_mem_autIn h hσ h4)

omit [Finite X] in
theorem exists_pow_four_of_mulEquiv {M : Type*} [Group M] (f : autIn (⊤ : Subgroup X) D ≃* M)
    {m : M} (h4 : m ^ 4 = 1) (h2 : m ^ 2 ≠ 1) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  refine ⟨(f.symm m : MulAut D), (f.symm m).2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, h4, map_one, Subgroup.coe_one]
  · intro h
    apply h2
    have h' : f.symm (m ^ 2) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
    simpa using congrArg f h'

omit [Finite X] in
theorem exists_pow_four_of_conj {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y)
    (hY : (Nat.card Y).factorization 3 = 2) {F : Subgroup Y} (hF : Nat.card F = 9)
    {ρ : MulAut F} (hρ : ρ ∈ autIn (⊤ : Subgroup Y) F) (h4 : ρ ^ 4 = 1) (h2 : ρ ^ 2 ≠ 1)
    (hD9 : Nat.card D = 9) : ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  have hD9' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  obtain ⟨g, hg⟩ := Res423Two.exists_map_conj_eq_of_card_nine hY hD9' hF
  have f2 := Sporadic.autInTopCongr (MulAut.conj g) (D.map e.toMonoidHom)
  rw [show (D.map e.toMonoidHom).map (MulAut.conj g : Y ≃* Y).toMonoidHom = F from hg] at f2
  have f := (Sporadic.autInTopCongr e D).trans f2
  refine exists_pow_four_of_mulEquiv f (m := ⟨ρ, hρ⟩) ?_ ?_
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)
  · intro h
    exact h2 (by simpa using congrArg Subtype.val h)

theorem not_isSolvable_centralizer (h : InnerConfig424 X D c d K) :
    ¬ Group.IsSolvable (Subgroup.centralizer ({c} : Set X)) := by
  intro hs
  have hKC : K ≤ Subgroup.centralizer ({c} : Set X) :=
    (mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn).1
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKC)
      (Subgroup.inclusion_injective hKC)
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn h.mem_thetaComponentsIn
  have hKn : Nontrivial K := by
    obtain ⟨x, y, hxy⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial
      (Item424Proof.isQuasisimple_of_mem_thetaComponentsIn h.mem_thetaComponentsIn)).exists_pair_ne
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x', y', fun hx => hxy (by rw [hx])⟩⟩
  exact Group.IsPerfect.not_isSolvable K hKs

theorem isSolvable_of_card_eq_two_mul_pow_three {H : Type*} [Group H] [Finite H] {k : ℕ}
    (hH : Nat.card H = 2 * 3 ^ k) : Group.IsSolvable H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := k)
    (by rw [hH]; exact Dvd.intro_left 2 rfl)
  have hidx : P.index = 2 := by
    have h := P.card_mul_index
    rw [hH, hP] at h
    have h3 : 0 < 3 ^ k := by positivity
    have : 3 ^ k * P.index = 3 ^ k * 2 := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left h3 this
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPp : IsPGroup 3 P := IsPGroup.of_card hP
  have : Group.IsNilpotent P := hPp.isNilpotent
  have hQ : Group.IsSolvable (H ⧸ P) := by
    have h2 : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index, hidx]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (H ⧸ P) := isCyclic_of_prime_card h2
    exact Group.isSolvable_of_comm fun a b => hcyc.isMulCommutative.is_comm.comm a b
  exact Group.isSolvable_of_ker_le_range P.subtype (QuotientGroup.mk' P)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem census424_of_not_nine_dvd (hX : ¬ 9 ∣ Nat.card X) : Census424 X := by
  intro D c d K h
  exact (hX (h.card_eq ▸ Subgroup.card_subgroup_dvd_card D)).elim

end Item424Res2

end CFSG.RankThree.PartTwo.Sec4
