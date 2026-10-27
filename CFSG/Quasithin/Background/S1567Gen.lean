module

public import CFSG.Quasithin.EmptyFaithful.T1531In68b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S1567

variable {G : Type} [Group G]

theorem conj_mem_of_relIndex_three {A N : Subgroup G} (hAN : A ≤ N) (h3 : A.relIndex N = 3) {x : G}
    (hx : x ∈ A) (hc : Nat.Coprime (orderOf x) 6) {g : G} (hg : g ∈ N) : g * x * g⁻¹ ∈ A := by
  set A' : Subgroup ↥N := A.subgroupOf N with hA'
  have hidx : A'.index = 3 := h3
  have hfin : Finite (↥N ⧸ A') := by
    have : A'.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (↥N ⧸ A') = 3 := by rw [← Subgroup.index]; exact hidx
  set φ : ↥N →* Equiv.Perm (↥N ⧸ A') := MulAction.toPermHom ↥N (↥N ⧸ A') with hφ
  have hperm : Nat.card (Equiv.Perm (↥N ⧸ A')) = 6 := by
    rw [Nat.card_perm, hcard]
    rfl
  set x' : ↥N := ⟨x, hAN hx⟩ with hx'
  have hord : orderOf x' = orderOf x := (Subgroup.orderOf_coe x').symm
  have h1 : orderOf (φ x') ∣ orderOf x' := orderOf_map_dvd φ x'
  have h2 : orderOf (φ x') ∣ 6 := hperm ▸ orderOf_dvd_natCard (φ x')
  have h3' : orderOf (φ x') = 1 := by
    have hcop : Nat.Coprime (orderOf (φ x')) 6 :=
      Nat.Coprime.of_dvd_left (hord ▸ h1) hc
    exact Nat.Coprime.eq_one_of_dvd hcop h2
  have hker : x' ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h3'
  have hcore : x' ∈ A'.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
    exact hker
  have := (Subgroup.normalCore_normal A').conj_mem x' hcore ⟨g, hg⟩
  have h5 := Subgroup.normalCore_le A' this
  exact h5

theorem eq_bot_of_normalized_by_max_two_local [Finite G] {M K D : Subgroup G}
    (hM : quasithinIsMaxTwoLocal M)
    (hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hKM : ¬ K ≤ M) (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G))
    (hgen : D ≤ Subgroup.closure {x | x ∈ D ∧ Odd (orderOf x)}) : D = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hO : pCoreOf 2 D = ⊥
  · have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
    have hDO : D ⊓ pCoreOf 2 M ≤ pCoreOf 2 D := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (pCoreOf_isPGroup 2 M).to_inf_right
      intro d hd
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hd, hMO (hDM hd)⟩
    have hDC : D ≤ pCoreOf 2 M := by
      intro d hd
      refine hF ⟨hDM hd, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hqM : q ∈ M := (pCoreOf_le 2 M) hq
      have hdM : d ∈ M := hDM hd
      have hc1 : q * d * q⁻¹ * d⁻¹ ∈ D :=
        D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMD hqM) d).mp hd) (D.inv_mem hd)
      have hc2 : q * d * q⁻¹ * d⁻¹ ∈ pCoreOf 2 M := by
        have h1 : d * q⁻¹ * d⁻¹ ∈ pCoreOf 2 M :=
          (Subgroup.mem_normalizer_iff.mp (hMO hdM) q⁻¹).mp ((pCoreOf 2 M).inv_mem hq)
        have := (pCoreOf 2 M).mul_mem hq h1
        simpa [mul_assoc] using this
      have hbot : q * d * q⁻¹ * d⁻¹ ∈ (⊥ : Subgroup G) := hO ▸ hDO ⟨hc1, hc2⟩
      have h1 : q * d * q⁻¹ * d⁻¹ = 1 := hbot
      have h2 : q * d * q⁻¹ = d := mul_inv_eq_one.mp h1
      calc q * d = (q * d * q⁻¹) * q := by group
        _ = d * q := by rw [h2]
    have hD2 : IsPGroup 2 ↥D := (pCoreOf_isPGroup 2 M).to_le hDC
    refine le_bot_iff.mp (hgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_))
    obtain ⟨hxD, hxo⟩ := hx
    obtain ⟨k, hk⟩ := hD2 ⟨x, hxD⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j = 0 := by
      by_contra hne
      have : 2 ∣ orderOf x := by
        rw [hjo]
        exact dvd_pow_self 2 hne
      exact (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr this)
    rw [hj0, pow_zero] at hjo
    exact orderOf_eq_one_iff.mp hjo
  · have hP2 : IsPGroup 2 (pCoreOf 2 D) := pCoreOf_isPGroup 2 D
    have hN : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 D : Set G)) := ⟨pCoreOf 2 D, hO, hP2, rfl⟩
    have hMN : M ≤ Subgroup.normalizer (pCoreOf 2 D : Set G) :=
      hMD.trans (normalizer_le_normalizer_pCoreOf 2 D)
    have hKN : K ≤ Subgroup.normalizer (pCoreOf 2 D : Set G) :=
      hKD.trans (normalizer_le_normalizer_pCoreOf 2 D)
    exact absurd (hM.2 _ hN hMN ▸ hKN) hKM

theorem frattini_two [Finite G] {X Y P : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hP : IsSylowTwoOf P X) {y : G} (hy : y ∈ Y) :
    ∃ x ∈ X, ∃ n ∈ Y ⊓ Subgroup.normalizer (P : Set G), y = x * n := by
  have h1 : IsSylowTwoOf (conjSubgroup P y⁻¹) (conjSubgroup X y⁻¹) :=
    isSylowTwoOf_conjSubgroup' hP y⁻¹
  have h2 : conjSubgroup X y⁻¹ = X := conjSubgroup_eq_iff_mem_normalizer.mpr (hYX (Y.inv_mem hy))
  rw [h2] at h1
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hP h1
  refine ⟨h, hh, h⁻¹ * y, ⟨Y.mul_mem (Y.inv_mem (hXY hh)) hy, ?_⟩, by group⟩
  show h⁻¹ * y ∈ Subgroup.normalizer (P : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h3 := hconj (y * z * y⁻¹)
  rw [mem_conjSubgroup_iff] at h3
  have e1 : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
  have e2 : h⁻¹ * (y * z * y⁻¹) * h = h⁻¹ * y * z * (h⁻¹ * y)⁻¹ := by group
  rw [e1, e2] at h3
  exact h3

theorem relIndex_inf_eq_relIndex_sup [Finite G] {A N : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) : (A ⊓ N).relIndex N = A.relIndex (A ⊔ N) := by
  have h1 : Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) = Nat.card ↥N * Nat.card ↥A := by
    have := S143.card_sup_mul_card_inf_of_le_normalizer hA
    rw [sup_comm, inf_comm]
    exact this
  have h2 : (A ⊓ N).relIndex N * Nat.card ↥(A ⊓ N ⊓ N) = Nat.card ↥N :=
    Subgroup.relIndex_mul_card _ _
  have h3 : A.relIndex (A ⊔ N) * Nat.card ↥(A ⊓ (A ⊔ N)) = Nat.card ↥(A ⊔ N) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_assoc, inf_idem] at h2
  rw [inf_eq_left.mpr le_sup_left] at h3
  have hA0 : 0 < Nat.card ↥A := Nat.card_pos
  have hi0 : 0 < Nat.card ↥(A ⊓ N) := Nat.card_pos
  have h4 : A.relIndex (A ⊔ N) * (Nat.card ↥A * Nat.card ↥(A ⊓ N)) =
      (A ⊓ N).relIndex N * (Nat.card ↥A * Nat.card ↥(A ⊓ N)) := by
    calc A.relIndex (A ⊔ N) * (Nat.card ↥A * Nat.card ↥(A ⊓ N))
        = (A.relIndex (A ⊔ N) * Nat.card ↥A) * Nat.card ↥(A ⊓ N) := by ring
      _ = Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ N) := by rw [h3]
      _ = Nat.card ↥N * Nat.card ↥A := h1
      _ = ((A ⊓ N).relIndex N * Nat.card ↥(A ⊓ N)) * Nat.card ↥A := by rw [h2]
      _ = (A ⊓ N).relIndex N * (Nat.card ↥A * Nat.card ↥(A ⊓ N)) := by ring
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hA0 hi0) h4).symm

theorem relIndex_oTwoUpper_eq_two_pow [Finite G] (H : Subgroup G) :
    ∃ k : ℕ, (oTwoUpper H).relIndex H = 2 ^ k := by
  have hN : ((oTwoUpper H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
      (le_normalizer_oTwoUpper H)
  have hp : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, hk⟩

theorem sup_eq_of_relIndex_two_pow_of_odd {A D X : Subgroup G} (hAX : A ≤ X) (hDX : D ≤ X)
    (hA : ∃ k : ℕ, A.relIndex X = 2 ^ k) (hD : Odd (D.relIndex X)) : A ⊔ D = X := by
  have hsup : A ⊔ D ≤ X := sup_le hAX hDX
  have h1 : (A ⊔ D).relIndex X ∣ A.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_left
  have h2 : (A ⊔ D).relIndex X ∣ D.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_right
  obtain ⟨k, hk⟩ := hA
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd : Odd ((A ⊔ D).relIndex X) := hD.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hsup hj

theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem not_nonempty_oTwoQuot_equiv_perm_three {X : Subgroup G} (hX : X = oTwoUpper X) :
    ¬ Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  set φ : ↥X →* Equiv.Perm (Fin 3) := (e : OTwoQuot X →* Equiv.Perm (Fin 3)).comp
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  set ψ : ↥X →* ℤˣ := Equiv.Perm.sign.comp φ with hψ
  have hodd : ∀ (x : G) (hx : x ∈ X), Odd (orderOf x) → (⟨x, hx⟩ : ↥X) ∈ ψ.ker := by
    intro x hx ho
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (ψ ⟨x, hx⟩) ∣ orderOf (⟨x, hx⟩ : ↥X) := orderOf_map_dvd ψ _
    have h2 : orderOf (⟨x, hx⟩ : ↥X) = orderOf x := (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥X)).symm
    have h3 : orderOf (ψ ⟨x, hx⟩) ∣ 2 := by
      have := orderOf_dvd_natCard (ψ ⟨x, hx⟩)
      simpa using this
    have hodd' : Odd (orderOf (ψ ⟨x, hx⟩)) := (h2 ▸ ho).of_dvd_nat h1
    have h4 : orderOf (ψ ⟨x, hx⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') even_two
    exact orderOf_eq_one_iff.mp h4
  have hker : ∀ (x : G) (hx : x ∈ X), (⟨x, hx⟩ : ↥X) ∈ ψ.ker := by
    intro x hx
    have hx' : x ∈ oTwoUpper X := hX ▸ hx
    have hle : oTwoUpper X ≤ ψ.ker.map X.subtype := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      exact ⟨⟨y, hy.1⟩, hodd y hy.1 hy.2, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hle hx'
    have : z = ⟨x, hx⟩ := Subtype.ext hzx
    exact this ▸ hz
  obtain ⟨z, hz⟩ := hφs (Equiv.swap 0 1)
  have h1 : ψ z = 1 := hker z z.2
  have h2 : ψ z = -1 := by
    rw [hψ, MonoidHom.comp_apply, hz]
    exact Equiv.Perm.sign_swap (by decide)
  rw [h1] at h2
  exact absurd h2 (by decide)


end S1567

end CFSG.Quasithin
