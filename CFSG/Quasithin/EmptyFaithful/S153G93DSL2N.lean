module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace SL2N

open CFSG.Open CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W] {G₀ K S : Subgroup (MulAut W)} {a : MulAut W} {z : W}

omit [Finite W] in
theorem mem_normalizer_of_aN (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (ha2 : a ^ 2 = 1) :
    a ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => haN l hl, fun hl => ?_⟩
  have hinv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact ha2
  have h1 := haN _ hl
  have e : a * (a * l * a⁻¹) * a⁻¹ = l := by
    rw [hinv]
    have : a * a = 1 := by rw [← pow_two]; exact ha2
    calc a * (a * l * a) * a = (a * a) * l * (a * a) := by group
      _ = l := by rw [this]; group
  rwa [e] at h1

theorem le_normalizer_of_ctx1 (h : Ctx1 W G₀ K a S z) :
    G₀ ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  rw [h.G₀eq]
  refine sup_le (fun k hk => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk), fun hl => by
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hl) hk
      simpa [mul_assoc] using this⟩
  · rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_aN h.aN h.a2

theorem false_of_ctx1 (h : Ctx1 W G₀ K a S z) {n : ℕ} (hn : BinaryNaturalSL K ⊤ ⊥ 2 n) :
    False := by
  obtain ⟨F, _, _, hF, hreal⟩ := hn
  obtain ⟨e, -, h2⟩ := H.exists_transport_natural hreal h.K_le (le_normalizer_of_ctx1 h)
  have ha'N : H.congrHom e a ∈ H.natNorm (StatedSL 2 F) := h2 ⟨a, h.a_mem, rfl⟩
  have ha'2 : H.congrHom e a ^ 2 = 1 := by rw [← map_pow, h.a2, map_one]
  have ha'1 : H.congrHom e a ≠ 1 := fun h1 =>
    h.a1 (H.congrHom_injective e (by rw [h1, map_one]))
  have hrk : rkIdx (fixV (Subgroup.zpowers (H.congrHom e a))) = 2 := by
    have h1 := H.rkIdx_fixV_map_congrHom e (Subgroup.zpowers a)
    rw [MonoidHom.map_zpowers] at h1
    rw [h1]
    exact rkIdx_fixV_eq_two h.rk
  have hcardW : Nat.card W = 2 ^ (2 * n) := by
    rw [Nat.card_congr e.toEquiv, H.card_stdMod, hF, Fintype.card_fin, ← pow_mul, mul_comm]
  have hn3 : 3 ≤ n := by
    have h6 := h.big
    rw [hcardW] at h6
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h6
    omega
  have hΓ : H.HasScalarCommutant (StatedSL 2 F) := H.hasScalarCommutant_statedSL (by norm_num)
  have hsl : H.IsSemilinear (H.congrHom e a) (H.fieldAut hΓ ⟨H.congrHom e a, ha'N⟩) :=
    H.isSemilinear_fieldAut hΓ ⟨H.congrHom e a, ha'N⟩
  by_cases hσ : H.fieldAut hΓ ⟨H.congrHom e a, ha'N⟩ = RingEquiv.refl F
  · rw [hσ] at hsl
    have := H.le_rkIdx_fixV_of_linear hF hsl ha'1
    omega
  · obtain ⟨-, h3⟩ := H.rkIdx_fixV_of_semilinear_two (by omega) hF hsl hσ ha'2
    simp only [Fintype.card_fin] at h3
    omega

theorem oneSL2_holds : OneSL2 := fun _ _ _ _ _ _ _ _ h ⟨_, hn⟩ => false_of_ctx1 h hn

end SL2N

end S153G93D

end CFSG.Quasithin
