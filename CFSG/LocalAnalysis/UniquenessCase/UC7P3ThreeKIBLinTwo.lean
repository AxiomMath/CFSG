module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem fixedFreeFive_of_param {q : ℕ} {A L : Type*} [CommGroup A] [Group L] [Finite L]
    (hA : IsPGroup q A) {a₀ : A} (ha₀ : a₀ ≠ 1) (ψ : A →* L) (hψ : Function.Injective ψ)
    (c : L) (α : A → A) (hc : ∀ a, c * ψ a * c⁻¹ = ψ (α a))
    (hfree : ∀ k : ℕ, 0 < k → k < 5 → ∀ a, α^[k] a = a → a = 1) :
    SEFive.FixedFreeFive q L := by
  have hpow : ∀ (k : ℕ) (a : A), c ^ k * ψ a * (c ^ k)⁻¹ = ψ (α^[k] a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', ← hc, ← ih a, pow_succ']
      group
  have hmap : ψ.range.map (MulAut.conj c).toMonoidHom = ψ.range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨α a, by simpa [MulAut.conj_apply] using (hc a).symm⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hN : c ∈ Subgroup.normalizer (ψ.range : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (MulAut.conj c) x ∈ ψ.range.map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmap] at hx'
      simpa [MulAut.conj_apply] using hx'
    · intro hx
      have hx' : (MulAut.conj c) x ∈ ψ.range.map (MulAut.conj c).toMonoidHom := by
        rw [hmap]
        simpa [MulAut.conj_apply] using hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
      have hyx : y = x := (MulAut.conj c).injective hxy
      simpa [hyx] using hy
  refine ⟨ψ.range, hA.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective, ?_, ?_, c, hN, ?_⟩
  · intro h
    have h₀ : ψ a₀ ∈ ψ.range := ⟨a₀, rfl⟩
    rw [h, Subgroup.mem_bot] at h₀
    exact ha₀ (hψ (h₀.trans (map_one ψ).symm))
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro k hk0 hk5 _ ⟨a, rfl⟩ hfix
    rw [hpow] at hfix
    rw [hfree k hk0 hk5 a (hψ hfix), map_one]

theorem coverActsTriviallyOnSmall_of_mulEquiv {p : ℕ} {L L' : Type*} [Group L] [Group L']
    (e : L ≃* L') (h : CoverActsTriviallyOnSmall p L) : CoverActsTriviallyOnSmall p L' := by
  intro J _ _ hJ φ hφ hcop hsol ℓ hℓ hℓ2 hℓp V _ _ hVcomm hVpow hVcard ρ
  have hker : ((e.symm : L' →* L).comp φ).ker = φ.ker := MonoidHom.ker_mulEquiv_comp φ e.symm
  exact h J hJ ((e.symm : L' →* L).comp φ) (e.symm.surjective.comp hφ) (hker ▸ hcop)
    (hker ▸ hsol) ℓ hℓ hℓ2 hℓp V hVcomm hVpow hVcard ρ

theorem fixedFreeFive_psl2GF_of_not_dvd {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (h : ∀ k : ℕ, 0 < k → k < 5 → ¬ p ^ n - 1 ∣ 2 * k) :
    SEFive.FixedFreeFive p (PSL2GF p n) := by
  classical
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField p n)ˣ)
  have hμk : ∀ k : ℕ, 0 < k → k < 5 → (μ : GaloisField p n) ^ (2 * k) ≠ 1 := by
    intro k hk0 hk5 h1
    have hd : orderOf μ ∣ 2 * k := orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h1))
    rw [hμ, Nat.card_units, hcard] at hd
    exact h k hk0 hk5 hd
  have hit : ∀ (k : ℕ) (a : Multiplicative (GaloisField p n)),
      (fun a : Multiplicative (GaloisField p n) =>
        Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a))^[k] a =
      Multiplicative.ofAdd ((μ : GaloisField p n) ^ (2 * k) * Multiplicative.toAdd a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      simp only [Function.iterate_succ_apply', ih, toAdd_ofAdd]
      congr 1
      ring
  refine fixedFreeFive_of_param (A := Multiplicative (GaloisField p n))
    (IsPGroup.of_card (n := n) hcard) (a₀ := Multiplicative.ofAdd 1) ?_
    (unipMonoidHom (GaloisField p n)) ?_ (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag μ))
    (fun a => Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) ?_ ?_
  · rw [Ne, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq]
    exact one_ne_zero
  · refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    rw [unipMonoidHom_apply, CFSG.PSL2Table.mk_eq_one_iff] at ha
    refine toAdd_eq_zero.mp ?_
    rcases ha with ha | ha
    · simpa using congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n) =>
        (A : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1) ha
    · simpa using congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n) =>
        (A : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 1) ha
  · intro a
    simp only [unipMonoidHom_apply, toAdd_ofAdd]
    rw [← map_inv, ← map_mul, ← map_mul, CFSG.PSL2Table.diag_conj_unip]
  · intro k hk0 hk5 a ha
    rw [hit] at ha
    have hX : (μ : GaloisField p n) ^ (2 * k) * Multiplicative.toAdd a =
        Multiplicative.toAdd a := by
      simpa using congrArg Multiplicative.toAdd ha
    have hsub : ((μ : GaloisField p n) ^ (2 * k) - 1) * Multiplicative.toAdd a = 0 := by
      rw [sub_mul, one_mul, hX, sub_self]
    exact toAdd_eq_zero.mp
      ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (hμk k hk0 hk5)))

theorem coverActsTriviallyOnSmall_of_isoLie_linTwo {L : Type} [Group L] [IsSimpleGroup L]
    {q : TauCeti.PrimePower} (hq3 : q.p = 3) (hI : IsoLie L (.A 1 q)) :
    CoverActsTriviallyOnSmall 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hd : IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, hq3, rfl⟩
  obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have h9 := card_ne_nine_of_isLinTwoIndex hd
  have h4 : 4 ≤ 3 ^ q.exponent := by
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h4 := hr.2 rfl
    rwa [TauCeti.PrimePower.card_def, hq3] at h4
  have ha : 3 ≤ q.exponent := by
    rcases Nat.lt_or_ge q.exponent 3 with hlt | hge
    · exfalso
      rcases (by omega : q.exponent = 0 ∨ q.exponent = 1 ∨ q.exponent = 2) with h0 | h0 | h0 <;>
        rw [h0] at h4 h9 <;> revert h4 h9 <;> norm_num
    · exact hge
  have h27 : 27 ≤ 3 ^ q.exponent :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) ha
  have hFF := fixedFreeFive_psl2GF_of_not_dvd (p := 3) (n := q.exponent) (by omega)
    fun k hk0 hk5 hdvd => by
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 3) (Or.inr rfl)
    (hFF.of_mulEquiv (e.trans f).symm)

theorem coverActsTriviallyOnSmall_of_isoLie_l28 {L : Type} [Group L] [IsSimpleGroup L]
    (hI : IsoLie L (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩)) :
    CoverActsTriviallyOnSmall 3 L := by
  obtain ⟨hv, ⟨e⟩⟩ := hI
  obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3)
    (d := ⟨.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩, hv⟩) ⟨_, rfl, rfl, rfl⟩
  have hFF := fixedFreeFive_psl2GF_of_not_dvd (p := 2) (n := 3) (by norm_num)
    fun k hk0 hk5 => by interval_cases k <;> decide
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 2) (Or.inl rfl)
    (hFF.of_mulEquiv (e.trans f).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
