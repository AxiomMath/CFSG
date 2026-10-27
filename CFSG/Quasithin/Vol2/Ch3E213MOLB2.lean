module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB1
public import CFSG.Quasithin.Vol2.Ch3E213MOLA6

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem exists_zOf_of_classical {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {z : K} {L : Subgroup K} (hL : IsClassicalSL2 F L z)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set K), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ Subgroup.zpowers z)
    (hS : ∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ a ∈ L, ∀ b ∈ L, a * b ≠ b * a →
      y * a = a * y → y * b = b * y → y ∈ Subgroup.centralizer (L : Set K))
    (hconj : ∀ t : K, orderOf t = 2 → ∃ g : K, t = g * z * g⁻¹) (S : Sylow 2 K) :
    ∃ g : K, E2P.zOf (S : Subgroup K) = Subgroup.zpowers (g * z * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htZ, ht2⟩ : ∃ t ∈ E2P.zOf (S : Subgroup K), orderOf t = 2 := by
    have hdvd : 2 ∣ Nat.card K := by
      rw [← hL.orderOf_eq_two]
      exact orderOf_dvd_natCard z
    have : Nontrivial (S : Subgroup K) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (S.ne_bot_of_dvd_card hdvd)
    have : Nontrivial (Subgroup.center (S : Subgroup K)) := S.isPGroup'.center_nontrivial
    have h2Z : 2 ∣ Nat.card (Subgroup.center (S : Subgroup K)) := by
      rcases (S.isPGroup'.to_subgroup (Subgroup.center _)).card_eq_or_dvd with h | h
      · exact absurd h Finite.one_lt_card.ne'
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
    refine ⟨((c : S) : K), ?_, ?_⟩
    · change ((c : S) : K) ∈ (S : Subgroup K) ⊓ Subgroup.centralizer ((S : Subgroup K) : Set K)
      refine Subgroup.mem_inf.mpr ⟨(c : S).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨s, hs⟩)
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  obtain ⟨g, hg⟩ := hconj t ht2
  have hφz : (MulAut.conj g) z = t := by rw [MulAut.conj_apply, hg]
  have hL' : IsClassicalSL2 F (L.map (MulAut.conj g).toMonoidHom) t := by
    have h1 := hL.conj g
    rwa [← hg] at h1
  have hC' := OLA.centralizer_two_map (MulAut.conj g) hC
  rw [hφz] at hC'
  have hS' := OLA.commute_two_map (MulAut.conj g) hS
  rw [hφz] at hS'
  refine ⟨g, ?_⟩
  rw [← hg]
  exact OLA.zOf_eq_zpowers hodd hL' hC' hS' S htZ

theorem mem_zpowers_of_mem_centralizer {x : SL(3, GaloisField 3 1)}
    (hx : x ∈ Subgroup.centralizer
      (Models.rootSL2 (GaloisField 3 1) (n := 3) (by norm_num) : Set SL(3, GaloisField 3 1))) :
    x = 1 ∨ x = Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) := by
  obtain ⟨h01, h02, h10, h12, h20, h21, h0011⟩ := isBlockScalar_of_mem_centralizer hx
  set X := ((x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) with hX
  have hdet : X 0 0 * X 0 0 * X 2 2 = 1 := by
    have h1 := x.2
    rw [Matrix.det_fin_three, ← hX, h01, h02, h10, h12, h20, h21, ← h0011] at h1
    linear_combination h1
  have hl0 : X 0 0 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  have hl2 := sq_eq_one_of_ne_zero hl0
  have hm : X 2 2 = 1 := by rw [hl2, one_mul] at hdet; exact hdet
  rcases eq_zero_or_one_or_neg_one (X 0 0) with h | h | h
  · exact absurd h hl0
  · left
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one, ← hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ← h0011, h, hm]
  · right
    apply Subtype.ext
    rw [coe_rootInv_three, ← hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ← h0011, h, hm]

theorem exists_zOf_sl3 {K : Type} [Group K] [Finite K] (ι : SL(3, GaloisField 3 1) ≃* K)
    (S : Sylow 2 K) : ∃ g : SL(3, GaloisField 3 1), E2P.zOf (S : Subgroup K) =
      Subgroup.zpowers (ι (g * Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) * g⁻¹)) := by
  set θ : SL(3, GaloisField 3 1) →* K := ι.toMonoidHom with hθdef
  have hθ : Function.Surjective θ := ι.surjective
  have hker : θ.ker ≤ Subgroup.center SL(3, GaloisField 3 1) := by
    intro x hx
    have h1 : x = 1 := ι.injective (by rw [map_one]; exact hx)
    rw [h1]
    exact Subgroup.one_mem _
  have hL : IsClassicalSL2 (GaloisField 3 1)
      ((Models.rootSL2 (GaloisField 3 1) (n := 3) (by norm_num)).map θ)
      (θ (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num))) :=
    IsLongRootImage.isClassicalSL2 odd_card_gf3 (le_refl 3) hθ hker (Or.inl (by norm_num))
      ⟨_, _, Models.isLongRootSL2_standard (K := GaloisField 3 1) (by norm_num : 2 ≤ 3), rfl,
        rfl⟩
  have hC : ∀ c ∈ Subgroup.centralizer
      (((Models.rootSL2 (GaloisField 3 1) (n := 3) (by norm_num)).map θ : Subgroup K) : Set K),
      ∀ k : ℕ, c ^ 2 ^ k = 1 →
        c ∈ Subgroup.zpowers (θ (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num))) := by
    intro c hc _ _
    obtain ⟨x, rfl⟩ := hθ c
    have hx : x ∈ Subgroup.centralizer
        (Models.rootSL2 (GaloisField 3 1) (n := 3) (by norm_num) : Set _) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro r hr
      exact ι.injective (by
        have h1 := hc (θ r) ⟨r, hr, rfl⟩
        simpa [hθdef] using h1)
    rcases mem_zpowers_of_mem_centralizer hx with h | h
    · rw [h, map_one]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  obtain ⟨g, hg⟩ := exists_zOf_of_classical odd_card_gf3 hL hC
    (OLA.lin_commute_two odd_card_gf3 θ hθ hker) (OLA.lin_conj_inv odd_card_gf3 θ hθ hker) S
  obtain ⟨g₀, rfl⟩ := hθ g
  refine ⟨g₀, ?_⟩
  rw [hg]
  simp [hθdef, map_mul, map_inv]

end CFSG.Quasithin.Ch3E213M.OLB
