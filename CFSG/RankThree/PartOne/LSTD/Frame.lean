module

public import CFSG.RankThree.PartOne.LSTD.Center
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.KF.R12Unitary
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.ToralQuotAut

public section

namespace CFSG.RankThree.PartOne.LSTD

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G]

theorem exists_r12frame [Finite G] {L A₀ F : Subgroup G} (h : Table123Core 5 L A₀ F) {f : ℕ}
    (hf1 : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h25 : ¬ 25 ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : UnitaryFieldData 2 f K) (_ : ∃ ζ : Kˣ,
      IsPrimitiveRoot ζ 5) (ε : ↥L →* StatedProj (unitarySU 2 f K 5)), IsCentralPQuot 5 ε ∧
      (∀ t ∈ torusBar K f, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = t) ∧
      ∀ x : F, ∃ t ∈ torusBar K f, ε (Subgroup.inclusion h.F_le x) = t := by
  classical
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  obtain ⟨ζ, hζ'⟩ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 :=
    ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  have hcop : Nat.Coprime 5 (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h.center_pPrime
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ↥L →* StatedProj (unitarySU 2 f K 5), IsCentralPQuot 5 ε₀ :=
    ⟨_, isCentralPQuot_center e hcop⟩
  have hTexp : ∀ t ∈ torusBar K f, t ^ 5 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow]
    have : t ^ 5 = 1 := by
      apply Subtype.ext
      obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
      rw [Subgroup.coe_pow, ← hd, diagU_pow, show d ^ 5 = 1 from funext hd1, diagU_one]
      rfl
    rw [this, map_one]
  have hTcomm : ∀ s ∈ torusBar K f, ∀ t ∈ torusBar K f, s * t = t * s := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    show (s : GL (Fin 5) K) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm]
  obtain ⟨S₀, hS₀L, hS₀ne, hS₀2, hAS₀, hS₀comm⟩ := h.A₀_invariant
  have hA₀pow : ∀ g ∈ A₀, g ^ 5 = 1 := fun g hg => by
    have := h.A₀_elem
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(A₀.subgroupOf L) →* StatedProj (unitarySU 2 f K 5),
      ∀ x, ρ x = ε₀ (x : ↥L) := ⟨ε₀.comp (A₀.subgroupOf L).subtype, fun x => rfl⟩
  have hAinj : Function.Injective ρ := by
    intro x y hxy
    have hx5 : ((x : ↥L)) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp x.2))
    have hy5 : ((y : ↥L)) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp y.2))
    rw [hρ, hρ] at hxy
    exact Subtype.ext (hε₀.eq_of_map_eq hx5 hy5 hxy)
  have hAcard : Nat.card ρ.range = 25 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A₀_le).toEquiv, h.A₀_card]
    norm_num
  have hSb_ne : (S₀.subgroupOf L).map ε₀ ≠ ⊥ := by
    intro hbot
    apply hS₀ne
    have hcent : ∀ s ∈ S₀, ∀ a ∈ A₀, s * a = a * s := by
      intro s hs a ha
      have h1 : ε₀ ⟨s, hS₀L hs⟩ = 1 := by
        have : ε₀ ⟨s, hS₀L hs⟩ ∈ (S₀.subgroupOf L).map ε₀ :=
          ⟨⟨s, hS₀L hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        rw [hbot] at this
        exact this
      have h3 := hε₀.central (show (⟨s, hS₀L hs⟩ : ↥L) ∈ ε₀.ker from h1)
      have := Subgroup.mem_center_iff.mp h3 ⟨a, h.A₀_le ha⟩
      exact (congrArg Subtype.val this).symm
    refine hS₀comm.trans (eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun s hs a ha => ?_))
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent s hs a ha)
  have hSb2 : IsPGroup 2 ((S₀.subgroupOf L).map ε₀) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨k, hk⟩ := hS₀2 ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hy' : y ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [Subgroup.coe_pow, ← hyx, ← map_pow, hy', map_one]
    rfl
  have hAS : ∀ a ∈ ρ.range, ∀ s ∈ (S₀.subgroupOf L).map ε₀,
      a * s * a⁻¹ ∈ (S₀.subgroupOf L).map ε₀ := by
    rintro _ ⟨a₀, rfl⟩ _ ⟨s₀, hs₀, rfl⟩
    refine ⟨(a₀ : ↥L) * s₀ * (a₀ : ↥L)⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
      by rw [hρ, map_mul, map_mul, map_inv]⟩
    have ha₀ := Subgroup.mem_subgroupOf.mp a₀.2
    have hs₀' := Subgroup.mem_subgroupOf.mp hs₀
    exact (Subgroup.mem_normalizer_iff.mp (hAS₀ ha₀) _).mp hs₀'
  have hDiag : ∀ X : Subgroup (StatedProj (unitarySU 2 f K 5)), (∀ x ∈ X, x ^ 5 = 1) →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      (∀ (a : G) (ha : a ∈ A₀),
        ε₀ (Subgroup.inclusion (h.A₀_le_F.trans h.F_le) ⟨a, ha⟩) ∈ X) →
      ∃ α : MulAut (StatedProj (unitarySU 2 f K 5)), ∀ x ∈ X, α x ∈ torusBar K f := by
    intro X hXe hXc hAX
    refine toral_conj_of_contains hU h5 h25 X ρ.range ((S₀.subgroupOf L).map ε₀) ?_ hAcard hXe
      hXc hSb_ne hSb2 hAS
    rintro _ ⟨y, rfl⟩
    rw [hρ]
    exact hAX (y : G) (Subgroup.mem_subgroupOf.mp y.2)
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot_aut ε₀ hε₀ hTexp hTcomm h.F_le h.A₀_le_F hDiag
    h.F_exp h.F_comm h.maximal
  exact ⟨K, hKf, hKfin, hU, ⟨ζ, hζ'⟩, ε, hε, hFT₁, hFT₂⟩

theorem exists_r12iso [Finite G] {L A₀ F : Subgroup G} (h : Table123Core 5 L A₀ F)
    (hGA : CFSG.Open.GriessAllModelsStatement) {f : ℕ}
    (hf1 : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h25 : ¬ 25 ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : UnitaryFieldData 2 f K) (_ : ∃ ζ : Kˣ,
      IsPrimitiveRoot ζ 5) (ε : ↥L ≃* StatedProj (unitarySU 2 f K 5)),
      ∀ x : ↥L, (x : G) ∈ F ↔ ε x ∈ torusBar K f := by
  classical
  obtain ⟨K, hKf, hKfin, hU, hζ, ε₁, hε₁, hFT₁, hFT₂⟩ := exists_r12frame h hf1 h5 h25 hmod
  have hZ : Subgroup.center ↥L = ⊥ :=
    psuFive_center_trivial hGA h5 h.quasisimple.1 h.center_pPrime hmod
  have hker : ε₁.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := hε₁.central hx
    rw [hZ] at this
    exact this
  have hinj : Function.Injective ε₁ := (MonoidHom.ker_eq_bot_iff ε₁).mp hker
  let ε : ↥L ≃* StatedProj (unitarySU 2 f K 5) :=
    MulEquiv.ofBijective ε₁ ⟨hinj, hε₁.surjective⟩
  refine ⟨K, hKf, hKfin, hU, hζ, ε, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := hFT₂ ⟨(x : G), hx⟩
    have : (Subgroup.inclusion h.F_le ⟨(x : G), hx⟩ : ↥L) = x := rfl
    rw [this] at hxt
    exact hxt ▸ ht
  · intro hx
    obtain ⟨y, hy⟩ := hFT₁ _ hx
    have : Subgroup.inclusion h.F_le y = x := hinj hy
    rw [← this]
    exact y.2

end CFSG.RankThree.PartOne.LSTD
