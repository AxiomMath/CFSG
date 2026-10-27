module

public import CFSG.Quasithin.Vol2.KGFact4413L3Y

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem index_upperTriangular_three :
    (upperTriangular 3 F).index = Nat.card (Sylow 2 (SpecialLinearGroup (Fin 3) F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  rw [Sylow.card_eq_index_normalizer P, ← normalizer_unitriangular, ← hP]
  rfl

theorem not_dvd_index_normalizer_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card F - 1) :
    ¬ p ∣ (Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F))).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2, projUpperTriangular, Subgroup.index_map_eq _
    (proj_surjective 3 F) (by rw [ker_proj]; exact scalars_le_upperTriangular 3 F),
    index_upperTriangular_three]
  exact (RankThree.PartOne.K159.borelFactsGrp_specialLinear hp hpq (by norm_num) hp3).2.1

theorem pow_eq_one_of_mem_projUpperTriangular {d : projectiveSL 3 F}
    (hd : d ∈ projUpperTriangular 3 F) (hodd : Odd (orderOf d)) : d ^ (Nat.card F - 1) = 1 := by
  have hd' : d ∈ ((dL3 F ⊔ projUnitriangular 3 F : Subgroup _) : Set (projectiveSL 3 F)) :=
    projUpperTriangular_le hd
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ dL3_le_normalizer] at hd'
  obtain ⟨d₀, hd₀, u, hu, rfl⟩ := hd'
  have hstep : ∀ m : ℕ, ∃ v ∈ projUnitriangular 3 F, (d₀ * u) ^ m = d₀ ^ m * v := by
    intro m
    induction m with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨v, hv, hve⟩ := ih
      have hN := dL3_le_normalizer (F := F) (Subgroup.inv_mem _ hd₀)
      refine ⟨d₀⁻¹ * v * d₀ * u, Subgroup.mul_mem _ ?_ hu, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hN v).mp hv
        simpa using this
      · rw [pow_succ, hve, pow_succ]
        group
  obtain ⟨v, hv, hve⟩ := hstep (Nat.card F - 1)
  rw [pow_eq_one_of_mem_dL3 hd₀, one_mul] at hve
  rw [hve]
  obtain ⟨m, hm⟩ := isPGroup_projUnitriangular_three (F := F) ⟨v, hv⟩
  have hm' : v ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hvo : Odd (orderOf v) := by
    rw [← hve]
    exact hodd.of_dvd_nat (orderOf_pow_dvd _)
  exact eq_one_of_odd_of_pow_two_pow hvo hm'

end Model

theorem not_dvd_index_of_isPSL3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsPSL 3 2 n Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ n - 1) : ¬ p ∣ (Subgroup.normalizer (U : Set Y)).index := by
  obtain ⟨F, _, _, _, ψ, hF, hψU, -, -⟩ := even_rank_two_residual_linear hY hU
  have hNU : (Subgroup.normalizer (U : Set Y)).map ψ.toMonoidHom =
      Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hψU]
  rw [← Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective, hNU]
  exact not_dvd_index_normalizer_three hp hp3 (hF ▸ hpq)

theorem pow_eq_one_of_isPSL3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsPSL 3 2 n Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {d : Y} (hd : d ∈ Subgroup.normalizer (U : Set Y))
    (hodd : Odd (orderOf d)) : d ^ (2 ^ n - 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, ψ, hF, hψU, -, -⟩ := even_rank_two_residual_linear hY hU
  have hNU : (Subgroup.normalizer (U : Set Y)).map ψ.toMonoidHom = projUpperTriangular 3 F := by
    rw [Subgroup.map_equiv_normalizer_eq, hψU, normalizer_projUnitriangular 2]
  have h1 : ψ d ∈ projUpperTriangular 3 F := hNU ▸ Subgroup.mem_map_of_mem _ hd
  have h2 : Odd (orderOf (ψ d)) := by rwa [MulEquiv.orderOf_eq]
  have h3 := pow_eq_one_of_mem_projUpperTriangular h1 h2
  rw [hF, ← map_pow, MulEquiv.map_eq_one_iff] at h3
  exact h3

variable {X Y : Type} [Group X] [Group Y] [Finite X]

theorem exists_mem_normalizer_of_cover_psl3 {n : ℕ} (hY : IsPSL 3 2 n Y)
    (hperf : commutator X = ⊤) (φ : X →* Y) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker)) {S D A : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hDN : D ≤ Subgroup.normalizer (S : Set X))
    (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hAD : A ≤ D) (hA : ∀ a ∈ A, a ^ p = 1) (𝒜 : Set (MulAut Y))
    (h𝒜U : ∀ α ∈ 𝒜, (S.map φ).map α.toMonoidHom = S.map φ)
    (h𝒜P : ∀ P : Subgroup Y, IsCoatom P → Subgroup.normalizer ((S.map φ : Subgroup Y) : Set Y) ≤ P →
      ∃ α ∈ 𝒜, P.map α.toMonoidHom ≠ P)
    (h𝒜A : ∀ α ∈ 𝒜, ∀ a ∈ A.map φ, α a ∈ A.map φ ⊔ S.map φ) :
    ∃ x : X, x ∉ Subgroup.normalizer (S : Set X) ∧ x ∈ Subgroup.normalizer (A : Set X) := by
  classical
  have : Finite Y := Finite.of_surjective φ hφ
  have hS2 : IsPGroup 2 S := hS.2.1
  set S' := S.map φ with hS'def
  have hNmap : ∀ x : X, φ x ∈ Subgroup.normalizer (S' : Set Y) ↔
      x ∈ Subgroup.normalizer (S : Set X) := fun x =>
    ⟨fun h => E2.TorusCover.mem_normalizer_of_map hker hodd hS2 h,
      fun h => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ h)⟩
  have hidx : (Subgroup.normalizer (S : Set X)).index =
      (Subgroup.normalizer (S' : Set Y)).index := by
    have he : Subgroup.normalizer (S : Set X) = (Subgroup.normalizer (S' : Set Y)).comap φ := by
      ext x
      exact (hNmap x).symm
    rw [he, Subgroup.index_comap_of_surjective _ hφ]
  have hS'syl : IsSylowTwoOf S' ⊤ := isSylowTwoOf_map hφ hS
  set A' := A.map φ with hA'def
  have hAodd : Odd (Nat.card A) := by
    have h1 := (odd_card_of_complement hS hDN hDS).of_dvd_nat (Subgroup.card_dvd_of_le hAD)
    exact h1
  have hA'N : A' ≤ Subgroup.normalizer (S' : Set Y) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hNmap a).mpr (hDN (hAD ha))
  have hA'odd : Odd (Nat.card A') := hAodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  obtain ⟨x', hx'N, hx'A⟩ := exists_mem_normalizer_of_isPSL3 hY hS'syl 𝒜 h𝒜U h𝒜P hA'N hA'odd
    h𝒜A
  obtain ⟨x, rfl⟩ := hφ x'
  refine ⟨x, fun h => hx'N ((hNmap x).mpr h), A4.mem_normalizer_of_conj_mem fun a ha => ?_⟩
  have haD := hAD ha
  have hap := hA a ha
  by_cases hpq : p ∣ 2 ^ n - 1
  ·
    have hZp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := by
      intro z hzk hzp
      have hzc := hker hzk
      have h2 := commutator_normalizer_le hDN hND hDab
        (pow_index_mem_commutator hperf hzc (Subgroup.normalizer (S : Set X)))
      have hzo : Odd (orderOf z) := by
        have := orderOf_dvd_natCard (⟨z, hzk⟩ : φ.ker)
        rw [Subgroup.orderOf_mk] at this
        exact hodd.of_dvd_nat this
      obtain ⟨m, hm⟩ := hS2 ⟨_, h2⟩
      have hm' : (z ^ (Subgroup.normalizer (S : Set X)).index) ^ 2 ^ m = 1 :=
        congrArg Subtype.val hm
      have h3 : z ^ (Subgroup.normalizer (S : Set X)).index = 1 :=
        eq_one_of_odd_of_pow_two_pow (hzo.of_dvd_nat (orderOf_pow_dvd _)) hm'
      have hcop : Nat.Coprime p (Subgroup.normalizer (S : Set X)).index := by
        rw [Nat.Prime.coprime_iff_not_dvd hp, hidx]
        exact not_dvd_index_of_isPSL3 hY hS'syl hp hp3 hpq
      have h4 : orderOf z ∣ Nat.gcd p (Subgroup.normalizer (S : Set X)).index :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one h3)
      rw [hcop, Nat.dvd_one] at h4
      exact orderOf_eq_one_iff.1 h4
    have h1 : φ (x * a * x⁻¹) ∈ A' := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hx'A (φ a)).mp ⟨a, ha, rfl⟩
    obtain ⟨a₁, ha₁, he⟩ := h1
    set z := a₁⁻¹ * (x * a * x⁻¹) with hzdef
    have hzk : z ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, he, inv_mul_cancel]
    have hxaD : x * a * x⁻¹ ∈ D := by
      have hφ' : φ (x * a * x⁻¹) ∈ D.map φ := ⟨a₁, hAD ha₁, he⟩
      obtain ⟨d, hd, hde⟩ := hφ'
      have hk : d⁻¹ * (x * a * x⁻¹) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hde, inv_mul_cancel]
      have hZD : φ.ker ≤ D := by
        intro y hy
        have hyN : y ∈ Subgroup.normalizer (S : Set X) := by
          rw [Subgroup.mem_normalizer_iff]
          intro s
          rw [E2.TorusCover.conj_central (hker hy)]
        have hy' : y ∈ ((D ⊔ S : Subgroup X) : Set X) := hND hyN
        rw [Subgroup.coe_mul_of_left_le_normalizer_right D S hDN] at hy'
        obtain ⟨d', hd', s, hs, rfl⟩ := hy'
        have hsk : s ∈ D := by
          have hyo : Odd (orderOf (d' * s)) := by
            have := orderOf_dvd_natCard (⟨d' * s, hy⟩ : φ.ker)
            rw [Subgroup.orderOf_mk] at this
            exact hodd.of_dvd_nat this
          have hcomm : Commute d' s := by
            have hc : ∀ g : X, g * (d' * s) = (d' * s) * g := Subgroup.mem_center_iff.1 (hker hy)
            have h1 : d' * (d' * s) = (d' * s) * d' := hc d'
            show d' * s = s * d'
            have : d' * d' * s = d' * s * d' := by rw [mul_assoc, h1]
            exact mul_left_cancel (a := d') (by rw [← mul_assoc, this, mul_assoc])
          obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
          have hm' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
          have hdo : Odd (orderOf d') := odd_orderOf_of_complement hS hDN hDS hd'
          have hpow : (d' * s) ^ orderOf d' = s ^ orderOf d' := by
            rw [hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
          have hs1 : s ^ orderOf d' = 1 := by
            rw [← hpow]
            refine eq_one_of_odd_of_pow_two_pow (m := m) (hyo.of_dvd_nat (orderOf_pow_dvd _)) ?_
            rw [hpow, ← pow_mul, mul_comm, pow_mul, hm', one_pow]
          have hso : orderOf s ∣ Nat.gcd (orderOf d') (2 ^ m) :=
            Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs1) (orderOf_dvd_of_pow_eq_one hm')
          rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hdo)),
            Nat.dvd_one, orderOf_eq_one_iff] at hso
          rw [hso]
          exact D.one_mem
        exact D.mul_mem hd' hsk
      have := D.mul_mem hd (hZD hk)
      simpa using this
    have hzp : z ^ p = 1 := by
      have hc : Commute a₁⁻¹ (x * a * x⁻¹) :=
        hDab _ (D.inv_mem (hAD ha₁)) _ hxaD
      rw [hzdef, hc.mul_pow, inv_pow, hA a₁ ha₁, inv_one, one_mul, conj_pow, hap, mul_one,
        mul_inv_cancel]
    have hz1 := hZp z hzk hzp
    have : x * a * x⁻¹ = a₁ := by
      have h := hz1
      rw [hzdef, inv_mul_eq_one] at h
      exact h.symm
    rw [this]
    exact ha₁
  ·
    have ha'1 : φ a = 1 := by
      have hN : φ a ∈ Subgroup.normalizer (S' : Set Y) := hA'N ⟨a, ha, rfl⟩
      have ho : Odd (orderOf (φ a)) :=
        (odd_orderOf_of_complement hS hDN hDS haD).of_dvd_nat (orderOf_map_dvd φ a)
      have h1 := pow_eq_one_of_isPSL3 hY hS'syl hN ho
      have hcop : Nat.Coprime p (2 ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
      have h4 : orderOf (φ a) ∣ Nat.gcd p (2 ^ n - 1) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hap, map_one]))
          (orderOf_dvd_of_pow_eq_one h1)
      rw [hcop, Nat.dvd_one] at h4
      exact orderOf_eq_one_iff.1 h4
    have hak : a ∈ φ.ker := ha'1
    rw [E2.TorusCover.conj_of_central (hker hak) x]
    exact ha

end CFSG.Quasithin.H13.KG4413
