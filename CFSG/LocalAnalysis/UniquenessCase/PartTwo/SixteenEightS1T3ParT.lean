module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParTRep
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_parab_of_model (h : ThreeNat A L T) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {I : Subgroup W} (hTI : StableUnder T I)
    (hR : (FFModel.nat Γ).Realizes L I (I ⊓ fixV L)) {a : ℕ}
    (hM : ∀ X : Subgroup (Matrix.GeneralLinearGroup ι K), IsPGroup 2 ↥X →
      X ≤ Subgroup.normalizer (Γ : Set (Matrix.GeneralLinearGroup ι K)) → T3ParabIn Γ X a) :
    T3ParabIn L T a := by
  classical
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥Γ →* ↥L := π₀
  have hπ : (FFModel.nat Γ).RealizesVia L I (I ⊓ fixV L) π := hπ₀
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ) hπ
  have hsurj : Function.Surjective π := hπ.1
  have hTL : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := h.sylow.le.trans h.normal
  have hTZ : StableUnder T (I ⊓ fixV L) := by
    intro x hx u hu
    obtain ⟨huI, huZ⟩ := hu
    refine ⟨hTI x hx u huI, mem_fixV.2 ?_⟩
    intro l hl
    have hconj : x⁻¹ * l * x ∈ L := by
      have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) := hTL hx
      have h := (Subgroup.mem_normalizer_iff.1 hxN (x⁻¹ * l * x)).2
      rw [show x * (x⁻¹ * l * x) * x⁻¹ = l by group] at h
      exact h hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.1 huZ _ hconj]
  obtain ⟨τ, hτ1, hτ2⟩ := s16t3_exists_rep_of_normalizes hK hπ hTI hTZ hTL
  let X' : Subgroup (Matrix.GeneralLinearGroup ι K) := τ.range
  have hX'p : IsPGroup 2 ↥X' :=
    h.sylow.isPGroup.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  have hXN : X' ≤ Subgroup.normalizer (Γ : Set (Matrix.GeneralLinearGroup ι K)) := by
    intro x' hx'
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hx'
    rw [Subgroup.mem_normalizer_iff]
    intro γ
    constructor
    · intro hγ
      exact (hτ1 x ⟨γ, hγ⟩).1
    · intro hγ
      have h := (hτ1 x⁻¹ ⟨τ x * γ * (τ x)⁻¹, hγ⟩).1
      have hxinv : τ x⁻¹ = (τ x)⁻¹ := map_inv τ x
      rw [hxinv] at h
      have h2 : (τ x)⁻¹ * (τ x * γ * (τ x)⁻¹) * ((τ x)⁻¹)⁻¹ = γ := by group
      rwa [h2] at h
  obtain ⟨P₀, hP₀le, hP₀norm, hP₀inf, hP₀card, hP₀exp⟩ := hM X' hX'p hXN
  set P : Subgroup (MulAut W) := ((P₀.subgroupOf Γ).map π).map L.subtype with hP
  have mem_P : ∀ p : MulAut W, p ∈ P ↔ ∃ γ : ↥Γ,
      (γ : Matrix.GeneralLinearGroup ι K) ∈ P₀ ∧ ((π γ : ↥L) : MulAut W) = p := by
    intro p
    rw [hP]
    constructor
    · intro hp
      obtain ⟨y, hy, hyP⟩ := (Subgroup.mem_map.1 hp)
      obtain ⟨γ, hγ, hγy⟩ := (Subgroup.mem_map.1 hy)
      rw [Subgroup.mem_subgroupOf] at hγ
      refine ⟨γ, hγ, ?_⟩
      have : ((π γ : ↥L) : MulAut W) = (y : MulAut W) := congrArg Subtype.val hγy
      exact this.trans hyP
    · rintro ⟨γ, hγ, rfl⟩
      refine Subgroup.mem_map.2 ⟨(π γ : ↥L), ?_, rfl⟩
      exact Subgroup.mem_map.2 ⟨γ, Subgroup.mem_subgroupOf.2 hγ, rfl⟩
  have hPle : P ≤ L := by
    rw [hP]
    exact Subgroup.map_subtype_le _
  have hPnorm : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P := by
    intro t ht p hp
    obtain ⟨γ, hγP₀, rfl⟩ := (mem_P p).1 hp
    obtain ⟨hγΓ, hπeq⟩ := hτ1 ⟨t, ht⟩ γ
    refine (mem_P _).2 ⟨⟨τ ⟨t, ht⟩ * (γ : Matrix.GeneralLinearGroup ι K) * (τ ⟨t, ht⟩)⁻¹,
      hγΓ⟩, ?_, ?_⟩
    · exact hP₀norm (τ ⟨t, ht⟩) (MonoidHom.mem_range.2 ⟨⟨t, ht⟩, rfl⟩)
        (γ : Matrix.GeneralLinearGroup ι K) hγP₀
    · simpa using hπeq
  have hPinf : T ⊓ L ≤ P := by
    intro t ht
    obtain ⟨htT, htL⟩ := Subgroup.mem_inf.1 ht
    obtain ⟨γ, hγ⟩ := hsurj ⟨t, htL⟩
    have hγval : ((π γ : ↥L) : MulAut W) = t := congrArg Subtype.val hγ
    have hτt : τ ⟨t, htT⟩ = (γ : Matrix.GeneralLinearGroup ι K) :=
      hτ2 ⟨t, htT⟩ γ hγval.symm
    refine (mem_P t).2 ⟨γ, ?_, hγval⟩
    have hX'γ : (γ : Matrix.GeneralLinearGroup ι K) ∈ X' := by
      rw [← hτt]
      exact MonoidHom.mem_range.2 ⟨⟨t, htT⟩, rfl⟩
    exact hP₀inf ⟨hX'γ, γ.2⟩
  have hPcard : Nat.card ↥P = 3 ^ a * 2 ^ (Nat.card ↥L).factorization 2 := by
    have h1 : Nat.card ↥P = Nat.card ↥((P₀.subgroupOf Γ).map π) := by
      rw [hP]
      exact Subgroup.card_map_of_injective L.subtype_injective
    have h2 : Nat.card ↥((P₀.subgroupOf Γ).map π) = Nat.card ↥(P₀.subgroupOf Γ) :=
      Subgroup.card_map_of_injective hinj
    have h3 : Nat.card ↥(P₀.subgroupOf Γ) = Nat.card ↥P₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀le).toEquiv
    have hΓL : Nat.card ↥Γ = Nat.card ↥L :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩)
    rw [h1, h2, h3, hP₀card, hΓL]
  have hPexp : ∀ p ∈ P, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1 := by
    intro p hp m hm
    obtain ⟨γ, hγP₀, rfl⟩ := (mem_P p).1 hp
    have hγm : γ ^ 3 ^ m = 1 := by
      apply hinj
      rw [map_pow, map_one]
      apply Subtype.ext
      simpa using hm
    have hγm' : (γ : Matrix.GeneralLinearGroup ι K) ^ 3 ^ m = 1 := by
      simpa using congrArg Subtype.val hγm
    have hγ3' : (γ : Matrix.GeneralLinearGroup ι K) ^ 3 = 1 :=
      hP₀exp (γ : Matrix.GeneralLinearGroup ι K) hγP₀ m hγm'
    have hγ3 : γ ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hγ3'
    have h3 : (π (γ ^ 3) : ↥L) = 1 := by rw [hγ3, map_one]
    have := congrArg Subtype.val h3
    simpa [map_pow] using this
  exact ⟨P, hPle, hPnorm, hPinf, hPcard, hPexp⟩

theorem ThreeNat.exists_parab_of_parabIn (h : ThreeNat A L T) {a : ℕ} (hP : T3ParabIn L T a) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ a * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := hP
  have hS := (h.sylow.inf_of_le_normalizer h.le h.normal).card_eq
  exact ⟨P, h1, h2, h3, by rw [h4, hS], h5⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
