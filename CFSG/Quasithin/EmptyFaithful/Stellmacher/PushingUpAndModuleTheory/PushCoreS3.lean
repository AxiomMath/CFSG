module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreNat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCorePU0
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Perm3

theorem perm3_pow_three_of_sign (σ : Equiv.Perm (Fin 3)) (h : Equiv.Perm.sign σ = 1) :
    σ ^ 3 = 1 := by
  revert σ; decide

theorem perm3_involution_of_pow_three_ne (σ : Equiv.Perm (Fin 3)) (h : σ ^ 3 ≠ 1) :
    σ * σ = 1 := by
  revert σ h; decide

theorem perm3_conj_ne (t c : Equiv.Perm (Fin 3)) (ht : t * t = 1) (ht1 : t ≠ 1) (hc : c ^ 3 = 1)
    (hc1 : c ≠ 1) : c * t * c⁻¹ ≠ t := by
  revert t c ht ht1 hc hc1; decide

theorem perm3_words (t u : Equiv.Perm (Fin 3)) (ht : t * t = 1) (hu : u * u = 1) (ht1 : t ≠ 1)
    (hu1 : u ≠ 1) (htu : t ≠ u) (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = t ∨ σ = u ∨ σ = t * u ∨ σ = u * t ∨ σ = t * u * t := by
  revert t u ht hu ht1 hu1 htu σ; decide

theorem perm3_eq_one_of_pow {σ : Equiv.Perm (Fin 3)} (h3 : σ ^ 3 = 1) {k : ℕ}
    (h2 : σ ^ 2 ^ k = 1) : σ = 1 := by
  have h3' : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2' : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ h3') with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at h2'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2'
    omega

theorem perm3_eq_one_or_involution {σ : Equiv.Perm (Fin 3)} {k : ℕ} (h2 : σ ^ 2 ^ k = 1) :
    σ = 1 ∨ σ * σ = 1 := by
  by_cases h3 : σ ^ 3 = 1
  · exact Or.inl (perm3_eq_one_of_pow h3 h2)
  · exact Or.inr (perm3_involution_of_pow_three_ne σ h3)

def cyc3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cyc3_pow_three : cyc3 ^ 3 = 1 := by unfold cyc3; decide

theorem cyc3_ne_one : cyc3 ≠ 1 := by unfold cyc3; decide

end Perm3


section Quotient

variable {G : Type*} [Group G] {X S Z : Subgroup G}

noncomputable def toS3 (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) : ↥X →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))

theorem toS3_surjective (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) : Function.Surjective (toS3 e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem toS3_eq_one_iff (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G} (hx : x ∈ X) :
    toS3 e ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X := by
  have h1 : toS3 e ⟨x, hx⟩ = 1 ↔ (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : OTwoQuot X) = 1 :=
    e.map_eq_one_iff
  rw [h1, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy

theorem toS3_pow_two_pow_eq_one (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G}
    (hx : x ∈ S) : ∃ k : ℕ, (toS3 e ⟨x, h.le_self hx⟩) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have : (⟨x, h.le_self hx⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
  rw [this, map_one]

theorem sign_toS3_of_mem_pResidualOf [Finite G] (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G}
    (hx : x ∈ pResidualOf 2 X) :
    ∃ hX : x ∈ X, Equiv.Perm.sign (toS3 e ⟨x, hX⟩) = 1 := by
  rw [← oTwoUpper_eq_pResidualOf] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine ⟨hx.1, ?_⟩
    set σ := toS3 e ⟨x, hx.1⟩ with hσ
    have h1 : σ ^ orderOf x = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨x, hx.1⟩ : ↥X) ^ orderOf x = 1 := Subtype.ext (by simp)
      rw [this, map_one]
    have h2 : Equiv.Perm.sign σ ^ orderOf x = 1 := by
      rw [← map_pow, h1, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · exfalso
      rw [h, Odd.neg_one_pow hx.2] at h2
      exact absurd h2 (by decide)
  | one =>
    refine ⟨X.one_mem, ?_⟩
    have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
    rw [this, map_one, map_one]
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hx⟩ := hx
    obtain ⟨hyX, hy⟩ := hy
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    have : (⟨x * y, X.mul_mem hxX hyX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ := rfl
    rw [this, map_mul, map_mul, hx, hy, mul_one]
  | inv x _ hx =>
    obtain ⟨hxX, hx⟩ := hx
    refine ⟨X.inv_mem hxX, ?_⟩
    have : (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X) = (⟨x, hxX⟩)⁻¹ := rfl
    rw [this, map_inv, map_inv, hx, inv_one]

theorem pResidualOf_inf_le_core [Finite G] (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    pResidualOf 2 X ⊓ S ≤ pCoreOf 2 X := by
  intro x ⟨hxL, hxS⟩
  obtain ⟨hX, hsgn⟩ := sign_toS3_of_mem_pResidualOf e hxL
  obtain ⟨k, hk⟩ := toS3_pow_two_pow_eq_one h e hxS
  have : toS3 e ⟨x, hX⟩ = 1 := perm3_eq_one_of_pow (perm3_pow_three_of_sign _ hsgn) hk
  exact (toS3_eq_one_iff e hX).mp this

theorem exists_three_elt [Finite G] (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    ∃ d ∈ pResidualOf 2 X, ∃ hd : d ∈ X, toS3 e ⟨d, hd⟩ ≠ 1 ∧ toS3 e ⟨d, hd⟩ ^ 3 = 1 := by
  obtain ⟨x, hx⟩ := toS3_surjective e cyc3
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf X x.2
  refine ⟨(x : G) ^ 2 ^ k, hk, X.pow_mem x.2 _, ?_, ?_⟩
  · have : (⟨(x : G) ^ 2 ^ k, X.pow_mem x.2 _⟩ : ↥X) = x ^ 2 ^ k := rfl
    rw [this, map_pow, hx]
    intro h1
    exact cyc3_ne_one (perm3_eq_one_of_pow cyc3_pow_three h1)
  · have : (⟨(x : G) ^ 2 ^ k, X.pow_mem x.2 _⟩ : ↥X) = x ^ 2 ^ k := rfl
    rw [this, map_pow, hx, ← pow_mul, mul_comm, pow_mul, cyc3_pow_three, one_pow]

theorem relIndex_core_eq_six (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    (pCoreOf 2 X).relIndex X = 6 := by
  have h1 : (pCoreOf 2 X).relIndex X = (CFSG.Open.pCore 2 ↥X).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf pCoreOf
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  rw [h1, Subgroup.index_eq_card, show Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) =
    Nat.card (Equiv.Perm (Fin 3)) from Nat.card_congr e.toEquiv, Nat.card_perm]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem relIndex_core_sylow [Finite G] (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    (pCoreOf 2 X).relIndex S = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) S X h.core_le h.le_self
  rw [relIndex_core_eq_six e] at h1
  have hodd : ¬ 2 ∣ S.relIndex X := h.sylow.2.2
  obtain ⟨n, hn⟩ := h.sylow.2.1.index ((pCoreOf 2 X).subgroupOf S)
  have hn' : (pCoreOf 2 X).relIndex S = 2 ^ n := hn
  rw [hn'] at h1 ⊢
  rcases n with _ | _ | n
  · exfalso; apply hodd; rw [pow_zero, one_mul] at h1; rw [h1]; norm_num
  · rfl
  · exfalso
    have : 6 = 4 * (2 ^ n * S.relIndex X) := by rw [← h1]; ring
    omega

end Quotient


section Counts

variable {G : Type*} [Group G] [Finite G] {X S Z : Subgroup G}

theorem four_le_relIndex_centralizer {Z : Subgroup G} (hZ2 : IsPGroup 2 Z)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {d : G}
    (hdZ : d ∈ Subgroup.normalizer (Z : Set G)) (hd3 : ∀ z ∈ Z, d ^ 3 * z * (d ^ 3)⁻¹ = z)
    {z0 : G} (hz0 : z0 ∈ Z) (hmove : d * z0 * d⁻¹ ≠ z0) :
    4 ≤ (Z ⊓ Subgroup.centralizer ({d} : Set G)).relIndex Z := by
  set C := Z ⊓ Subgroup.centralizer ({d} : Set G) with hC
  have hmem : ∀ z ∈ Z, z ∈ C ↔ d * z = z * d := by
    intro z hz
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp [hz]
  obtain ⟨y0, hy0def⟩ : ∃ y0, y0 = d * z0 * d⁻¹ := ⟨_, rfl⟩
  have hy0Z : y0 ∈ Z := by
    rw [hy0def]; exact (Subgroup.mem_normalizer_iff.mp hdZ z0).mp hz0
  have hz0C : z0 ∉ C := by
    intro h1
    apply hmove
    rw [(hmem z0 hz0).mp h1]; group
  have hy0C : y0 ∉ C := by
    intro h1
    have h2 := (hmem y0 hy0Z).mp h1
    apply hmove
    have h3 : d * (d * z0 * d⁻¹) = (d * z0 * d⁻¹) * d := by rw [← hy0def]; exact h2
    have h4 : d * (d * z0 * d⁻¹) = d * z0 := by rw [h3]; group
    exact mul_left_cancel h4
  obtain ⟨n, hn⟩ := hZ2.index (C.subgroupOf Z)
  have hidx : C.relIndex Z = 2 ^ n := hn
  rw [hidx]
  rcases n with _ | _ | n
  · exfalso
    have : C.relIndex Z = 1 := hidx
    rw [Subgroup.relIndex_eq_one] at this
    exact hz0C (this hz0)
  · exfalso
    have h2 : (C.subgroupOf Z).index = 2 := by simpa using hn
    have hiff := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨z0, hz0⟩) (b := ⟨y0, hy0Z⟩)
    have hz0C' : (⟨z0, hz0⟩ : ↥Z) ∉ C.subgroupOf Z := hz0C
    have hy0C' : (⟨y0, hy0Z⟩ : ↥Z) ∉ C.subgroupOf Z := hy0C
    have hprod : (⟨z0, hz0⟩ * ⟨y0, hy0Z⟩ : ↥Z) ∈ C.subgroupOf Z :=
      hiff.mpr (iff_of_false hz0C' hy0C')
    have hprod' : z0 * y0 ∈ C := Subgroup.mem_subgroupOf.mp hprod
    have hdz := (hmem (z0 * y0) (Z.mul_mem hz0 hy0Z)).mp hprod'
    have hy1Z : d * y0 * d⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hdZ y0).mp hy0Z
    have e1 : y0 * (d * y0 * d⁻¹) = z0 * y0 := by
      calc y0 * (d * y0 * d⁻¹) = d * (z0 * y0) * d⁻¹ := by rw [hy0def]; group
        _ = z0 * y0 := by rw [hdz]; group
    have e2 : z0 * y0 = y0 * z0 := hZc z0 hz0 y0 hy0Z
    have hy1 : d * y0 * d⁻¹ = z0 := mul_left_cancel (e1.trans e2)
    apply hmove
    calc d * z0 * d⁻¹ = d * (d * y0 * d⁻¹) * d⁻¹ := by rw [hy1]
      _ = d ^ 3 * z0 * (d ^ 3)⁻¹ := by
        rw [hy0def, show d ^ 3 = d * d * d by rw [pow_succ, pow_two]]; group
      _ = z0 := hd3 z0 hz0
  · have : 2 ^ (n + 2) = 4 * 2 ^ n := by ring
    rw [this]
    have : 0 < 2 ^ n := by positivity
    omega

theorem offender_s3_aux (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAQ : ¬ A ≤ pCoreOf 2 X) :
    (A ⊓ pCoreOf 2 X).relIndex A = 2 ∧ S ≤ A ⊔ pCoreOf 2 X := by
  set Q := pCoreOf 2 X with hQ
  have hQS : Q ≤ S := h.core_le
  have hAS : A ≤ S := hA.1
  have hAn : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAS.trans (h.le_self.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have h1 : (A ⊓ Q).relIndex A = Q.relIndex (Q ⊔ A) := by
    rw [inf_comm, relIndex_sup_eq_relIndex_inf_right hAn]
  have h2 := Subgroup.relIndex_mul_relIndex Q (Q ⊔ A) S le_sup_left (sup_le hQS hAS)
  rw [relIndex_core_sylow h e] at h2
  have hne : Q.relIndex (Q ⊔ A) ≠ 1 := by
    intro h3
    rw [Subgroup.relIndex_eq_one] at h3
    exact hAQ (le_sup_right.trans h3)
  have hdvd : Q.relIndex (Q ⊔ A) ∣ 2 := Dvd.intro _ h2
  have hpos := relIndex_pos Q (Q ⊔ A)
  have h22 : Q.relIndex (Q ⊔ A) = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  refine ⟨by rw [h1, h22], ?_⟩
  rw [h22] at h2
  have h3 : (Q ⊔ A).relIndex S = 1 := by omega
  rw [Subgroup.relIndex_eq_one] at h3
  rw [sup_comm]
  exact h3

theorem natCounts_offender_le (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (A ⊓ pCoreOf 2 X).relIndex A ≤ 2 := fun _ hA hAQ =>
  (offender_s3_aux h e hA hAQ).1.le

theorem natCounts_offender_ge (h : PushHyp X S Z) :
    ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      2 ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := by
  intro A hA hAQ
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have haX : a ∈ X := h.le_self (hA.1 haA)
  have haC : a ∉ Subgroup.centralizer (Z : Set G) := fun hc => haQ (h.mem_core_of_centralizes haX hc)
  rw [Subgroup.mem_centralizer_iff] at haC
  push Not at haC
  obtain ⟨z, hz, hza⟩ := haC
  have hne : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    have := h1 hz
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at this
    exact hza (this.2 a haA).symm
  have := relIndex_pos (Z ⊓ Subgroup.centralizer (A : Set G)) Z
  omega

theorem natCounts_generated (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X := by
  obtain ⟨d, hdL, hdX, hd1, hd3⟩ := exists_three_elt e
  refine ⟨d, hdL, ?_⟩
  obtain ⟨a, haJ, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hJ
  have haS : a ∈ S := thompsonJ_le_self S haJ
  have haX : a ∈ X := h.le_self haS
  set t := toS3 e ⟨a, haX⟩ with ht
  have ht1 : t ≠ 1 := fun h1 => haQ ((toS3_eq_one_iff e haX).mp h1)
  obtain ⟨k, hk⟩ := toS3_pow_two_pow_eq_one h e haS
  have htt : t * t = 1 := (perm3_eq_one_or_involution hk).resolve_left ht1
  set c := toS3 e ⟨d, hdX⟩ with hc
  have hdad : d * a * d⁻¹ ∈ X := X.mul_mem (X.mul_mem hdX haX) (X.inv_mem hdX)
  set u := toS3 e ⟨d * a * d⁻¹, hdad⟩ with hu
  have huc : u = c * t * c⁻¹ := by
    have : (⟨d * a * d⁻¹, hdad⟩ : ↥X) = ⟨d, hdX⟩ * ⟨a, haX⟩ * ⟨d, hdX⟩⁻¹ := rfl
    rw [hu, this, map_mul, map_mul, map_inv]
  have huu : u * u = 1 := by
    rw [huc]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hu1 : u ≠ 1 := by
    intro h1
    apply ht1
    rw [huc] at h1
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  have htu : t ≠ u := fun h' => perm3_conj_ne t c htt ht1 hd3 hd1 (huc ▸ h'.symm)
  set I₂ := thompsonJ S ⊔ cj d (thompsonJ S) with hI₂
  set K : Subgroup (Equiv.Perm (Fin 3)) := (I₂.subgroupOf X).map (toS3 e) with hK
  have htK : t ∈ K := ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left haJ), rfl⟩
  have huK : u ∈ K := by
    refine ⟨⟨d * a * d⁻¹, hdad⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ?_), rfl⟩
    rw [mem_cj]
    simpa [mul_assoc] using haJ
  have hKall : ∀ σ, σ ∈ K := by
    intro σ
    rcases perm3_words t u htt huu ht1 hu1 htu σ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact K.one_mem
    · exact htK
    · exact huK
    · exact K.mul_mem htK huK
    · exact K.mul_mem huK htK
    · exact K.mul_mem (K.mul_mem htK huK) htK
  intro l hl
  have hlX : l ∈ X := pResidualOf_le_self X hl
  obtain ⟨y, hy, hyl⟩ := hKall (toS3 e ⟨l, hlX⟩)
  have hyX : (y : G)⁻¹ * l ∈ X := X.mul_mem (X.inv_mem y.2) hlX
  have hq : (y : G)⁻¹ * l ∈ pCoreOf 2 X := by
    rw [← toS3_eq_one_iff e hyX]
    have : (⟨(y : G)⁻¹ * l, hyX⟩ : ↥X) = y⁻¹ * ⟨l, hlX⟩ := rfl
    rw [this, map_mul, map_inv, hyl, inv_mul_cancel]
  have hl' : l = (y : G) * ((y : G)⁻¹ * l) := by group
  rw [hl']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) hq

theorem natCounts_index_ge (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    2 ^ 2 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z := by
  obtain ⟨d, hdL, hdX, hd1, hd3⟩ := exists_three_elt e
  have hZ2 : IsPGroup 2 Z := h.sylow.2.1.to_le h.Z_le
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hdZ : d ∈ Subgroup.normalizer (Z : Set G) := h.normal hdX
  have hd3Q : d ^ 3 ∈ pCoreOf 2 X := by
    have hd3X : d ^ 3 ∈ X := X.pow_mem hdX 3
    rw [← toS3_eq_one_iff e hd3X]
    have : (⟨d ^ 3, hd3X⟩ : ↥X) = ⟨d, hdX⟩ ^ 3 := rfl
    rw [this, map_pow, hd3]
  have hd3' : ∀ z ∈ Z, d ^ 3 * z * (d ^ 3)⁻¹ = z := by
    intro z hz
    have := h.core_le_centralizer hd3Q z hz
    calc d ^ 3 * z * (d ^ 3)⁻¹ = (d ^ 3 * z) * (d ^ 3)⁻¹ := rfl
      _ = (z * d ^ 3) * (d ^ 3)⁻¹ := by rw [← this]
      _ = z := by group
  have hdC : d ∉ Subgroup.centralizer (Z : Set G) := fun hc =>
    hd1 ((toS3_eq_one_iff e hdX).mpr (h.mem_core_of_centralizes hdX hc))
  rw [Subgroup.mem_centralizer_iff] at hdC
  push Not at hdC
  obtain ⟨z0, hz0, hz0d⟩ := hdC
  have hmove : d * z0 * d⁻¹ ≠ z0 := by
    intro h1
    apply hz0d
    calc z0 * d = (d * z0 * d⁻¹) * d := by rw [h1]
      _ = d * z0 := by group
  have h4 := four_le_relIndex_centralizer hZ2 hZc hdZ hd3' hz0 hmove
  have hle : Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) ≤
      Z ⊓ Subgroup.centralizer ({d} : Set G) := by
    refine inf_le_inf_left Z (Subgroup.centralizer_le ?_)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hdL
  have := relIndex_le_of_le Z hle
  omega

theorem natCounts_of_s3 (h : PushHyp X S Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) : NatCounts X S Z 2 where
  offender_le := natCounts_offender_le h e
  offender_ge := natCounts_offender_ge h
  thompsonJ_le := fun A hA hAQ =>
    (thompsonJ_le_self S).trans (offender_s3_aux h e hA hAQ).2
  residual_inf_le := fun A _ _ s hs =>
    ⟨1, A.one_mem, s, pResidualOf_inf_le_core h e hs, by simp, fun z _ _ => by simp⟩
  generated := natCounts_generated h e hJ
  index_ge := natCounts_index_ge h e

theorem pu1_s3 (h : PushHyp X S Z) (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)))
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    pResidualOf 2 X ⊓ S ≤ baum S ∧ IsSylowTwoOf (baum S) (conjClosure (baum S) X) ∧
      (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z = 4 := by
  obtain ⟨e⟩ := he
  have := pu1_of_counts h hJ (natCounts_of_s3 h e hJ)
  simpa using this

theorem pu1_s3_of_noCharNormal (h : PushHyp X S Z)
    (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) (hS : S ≠ ⊥)
    (hnc : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ X ≤ Subgroup.normalizer (C : Set G)) :
    pResidualOf 2 X ⊓ S ≤ baum S ∧ IsSylowTwoOf (baum S) (conjClosure (baum S) X) ∧
      (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z = 4 :=
  pu1_s3 h he (not_le_core_of_noCharNormal h hS hnc)

end Counts

end CFSG.Quasithin.F53Push
