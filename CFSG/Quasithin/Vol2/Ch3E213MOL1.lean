module

public import CFSG.Quasithin.Vol2.Ch3E213MOS4

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

variable {K : Type} [Group K] [Finite K]

theorem exists_outer_inv (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {M₀ V₀ : Subgroup (MulAut K)} {z : K} (hz : orderOf z = 2)
    (hD : M₀ ⊓ innAut K = (Subgroup.centralizer ({z} : Set K)).map MulAut.conj)
    (hQ : ∀ Q : Subgroup K, Q ≤ Subgroup.centralizer ({z} : Set K) → IsPGroup 2 Q →
      Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (Q : Set K) →
      Q ≤ Subgroup.zpowers z)
    (hVM : V₀ ≤ pCoreOf 2 M₀) (hsq : ∀ v ∈ V₀, v * v = 1) (hV4 : 4 ≤ Nat.card V₀) :
    ∃ v ∈ V₀, orderOf v = 2 ∧ v ∉ innAut K ∧
      ∀ x ∈ Subgroup.centralizer ({z} : Set K), v x * x⁻¹ ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set K) with hC
  set Q : Subgroup K := (pCoreOf 2 M₀).comap MulAut.conj with hQdef
  have hQM : ∀ x ∈ Q, MulAut.conj x ∈ M₀ := fun x hx =>
    CFSG.LieType.BorelTits.pCoreOf_le 2 M₀ hx
  have hQC : Q ≤ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hD ▸ (⟨hQM x hx, ⟨x, rfl⟩⟩ : MulAut.conj x ∈ M₀ ⊓ innAut K) :
      MulAut.conj x ∈ C.map MulAut.conj)
    rw [← hinj hyx]
    exact hy
  have hQ2 : IsPGroup 2 Q := by
    intro x
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀
      ⟨MulAut.conj (x : K), x.2⟩
    refine ⟨n, Subtype.ext (hinj ?_)⟩
    have h1 : MulAut.conj ((x : K) ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    show MulAut.conj ((x : K) ^ 2 ^ n) = MulAut.conj 1
    rw [h1, map_one]
  have hQn : C ≤ Subgroup.normalizer (Q : Set K) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyM : MulAut.conj y ∈ M₀ :=
      (hD.symm ▸ (⟨y, hy, rfl⟩ : MulAut.conj y ∈ C.map MulAut.conj) :
        MulAut.conj y ∈ M₀ ⊓ innAut K).1
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀ hyM) (MulAut.conj x)
    show MulAut.conj x ∈ pCoreOf 2 M₀ ↔ MulAut.conj (y * x * y⁻¹) ∈ pCoreOf 2 M₀
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hQz := hQ Q hQC hQ2 hQn
  have hVI : V₀ ⊓ innAut K ≤ (Subgroup.zpowers z).map MulAut.conj := by
    rintro _ ⟨hvV, ⟨x, rfl⟩⟩
    exact ⟨x, hQz (hVM hvV), rfl⟩
  have hcard : Nat.card ↥(V₀ ⊓ innAut K) ≤ 2 := by
    refine (Subgroup.card_le_of_le hVI).trans ?_
    rw [Subgroup.card_map_of_injective hinj, Nat.card_zpowers, hz]
  have hnle : ¬ V₀ ≤ innAut K := by
    intro hle
    have : V₀ ⊓ innAut K = V₀ := inf_eq_left.mpr hle
    rw [this] at hcard
    omega
  obtain ⟨v, hv, hvI⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hv1 : v ≠ 1 := fun h => hvI (h ▸ (innAut K).one_mem)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq v hv) hv1
  refine ⟨v, hv, hv2, hvI, fun x hx => hQz ?_⟩
  have hxM : MulAut.conj x ∈ M₀ :=
    (hD.symm ▸ (⟨x, hx, rfl⟩ : MulAut.conj x ∈ C.map MulAut.conj) :
      MulAut.conj x ∈ M₀ ⊓ innAut K).1
  have hvP := hVM hv
  have h1 : v * MulAut.conj x * v⁻¹ * (MulAut.conj x)⁻¹ ∈ pCoreOf 2 M₀ := by
    have h2 : MulAut.conj x * v⁻¹ * (MulAut.conj x)⁻¹ ∈ pCoreOf 2 M₀ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀ hxM)
        v⁻¹).mp ((pCoreOf 2 M₀).inv_mem hvP)
    have h3 := (pCoreOf 2 M₀).mul_mem hvP h2
    simpa only [mul_assoc] using h3
  have h4 : v * MulAut.conj x * v⁻¹ * (MulAut.conj x)⁻¹ = MulAut.conj (v x * x⁻¹) := by
    rw [OS.mul_conj_mul_inv, map_mul, map_inv]
  rw [h4] at h1
  exact h1

end CFSG.Quasithin.Ch3E213M.OL
