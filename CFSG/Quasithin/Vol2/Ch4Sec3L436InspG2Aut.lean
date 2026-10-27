module

public import CFSG.Quasithin.Vol2.RootDataG2
public import CFSG.RankThree.PartTwo.KFacts.AutG2

public section

namespace CFSG.Quasithin.H13.Ch4.G2A

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.NQCat
  CFSG.Quasithin.H13.RootData.G2
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped Pointwise

theorem aut_eq_one_of_fixes
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (φ : MulAut ↥(adjointGroup Tag.G2 K))
    (hφ : ∀ x : ↥(adjointGroup Tag.G2 K),
      (x : ModGL Tag.G2 K) ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}) → φ x = x) :
    φ = 1 := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 := four_le_card hK hf
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨g, σ, hgσ⟩ := (CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4).1 φ
  have hact := (CFSG.RankThree.PartTwo.KFacts.forall_eq_iff_eq_conj_mul_g2FieldHom φ g σ).mpr hgσ
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hUP := posUnipotent_le_perfectCore hK hf
  set ψ : ModGL Tag.G2 K →* ModGL Tag.G2 K := Units.map (entrywiseHom σ.toRingHom) with hψ
  have hfixU : ∀ u ∈ posUnipotent Tag.G2 K,
      (g : ModGL Tag.G2 K) * ψ u * (g : ModGL Tag.G2 K)⁻¹ = u := by
    intro u hu
    have h1 := hact ⟨u, hUC hu⟩
    rw [hφ ⟨u, hUC hu⟩ (hUP hu)] at h1
    exact h1.symm
  have hψU := map_entrywise_posUnipotent (K := K) σ
  have hψU1 : ∀ u ∈ posUnipotent Tag.G2 K, ψ u ∈ posUnipotent Tag.G2 K := fun u hu => by
    rw [← hψU]
    exact Subgroup.mem_map_of_mem _ hu
  have hgN : (g : ModGL Tag.G2 K) ∈
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : h ∈ (posUnipotent Tag.G2 K).map ψ := by rw [hψU]; exact hh
      obtain ⟨u, hu, rfl⟩ := hh'
      rw [hfixU u hu]
      exact hu
    · intro hh
      have h1 := hfixU _ hh
      have h2 : ψ ((g : ModGL Tag.G2 K) * h * (g : ModGL Tag.G2 K)⁻¹) = h := by
        have := congrArg (fun y => (g : ModGL Tag.G2 K)⁻¹ * y * (g : ModGL Tag.G2 K)) h1
        simpa [mul_assoc] using this
      rw [← h2]
      exact hψU1 _ hh
  have hgB : (g : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
    rw [← (borel_self_normalizers Tag.G2 K).1]
    exact ⟨g.2, hgN⟩
  have hgB' : (g : ModGL Tag.G2 K) ∈ (SetLike.coe (torusGroup Tag.G2 K) *
      SetLike.coe (posUnipotent Tag.G2 K) : Set (ModGL Tag.G2 K)) := by
    rw [← (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.1]
    exact hgB
  obtain ⟨t, ht, u, hu, htu⟩ := Set.mem_mul.mp hgB'
  obtain ⟨l, hl⟩ := torus_conj_gX_rC ht
  have hc : ∀ s : K, gX rC s = gX rC ((l : K) * σ s) := by
    intro s
    have h1 := hfixU (gX rC s) (LieCentral.G2.gX_mem_posUnipotent (by simp) s)
    have h2 : ψ (gX rC s) = gX rC (σ s) := Units.ext (entrywise_pinnedX σ.toRingHom rC s)
    rw [h2, ← htu] at h1
    have hcomm : u * gX rC (σ s) * u⁻¹ = gX rC (σ s) := by
      have h3 := Subgroup.mem_centralizer_iff.mp (LieCentral.G2.gX_rC_mem_centralizer (σ s)) u hu
      rw [h3, mul_inv_cancel_right]
    calc gX rC s = t * u * gX rC (σ s) * (t * u)⁻¹ := h1.symm
      _ = t * (u * gX rC (σ s) * u⁻¹) * t⁻¹ := by group
      _ = t * gX rC (σ s) * t⁻¹ := by rw [hcomm]
      _ = gX rC ((l : K) * σ s) := hl _
  have hl1 : (l : K) = 1 := by
    have h := hc 1
    rw [map_one, mul_one] at h
    exact (pinnedX_injective Tag.G2 K rC h).symm
  have hσ : σ = 1 := by
    ext s
    have h := hc s
    rw [hl1, one_mul] at h
    exact (pinnedX_injective Tag.G2 K rC h).symm
  subst hσ
  rw [map_one, mul_one] at hgσ
  have hgcent : ∀ y : ↥(adjointGroup Tag.G2 K),
      (y : ModGL Tag.G2 K) ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}) →
      (y : ModGL Tag.G2 K) * g = g * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hφ y hy)
    rw [hgσ, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (y : ModGL Tag.G2 K) * g = g * y * (g : ModGL Tag.G2 K)⁻¹ * g := by rw [h1]
      _ = g * y := by group
  obtain ⟨d, hg⟩ := exists_eq_gX_rC_of_centralizer g.2 fun y hy => hgcent ⟨y, hUC hy⟩ (hUP hy)
  have hPC : perfectCore (parabolicSubgroup Tag.G2 K {i0}) ≤ adjointGroup Tag.G2 K :=
    (CFSG.Quasithin.perfectCore_le _).trans (parabolicSubgroup_le_adjointGroup _ _ _)
  have hn := hgcent ⟨weylElt Tag.G2 K i0 1, hPC (weyl_mem_perfectCore_zero hK4)⟩
    (weyl_mem_perfectCore_zero hK4)
  rw [hg] at hn
  have hd : d = 0 := eq_zero_of_commute_weyl hn
  subst hd
  rw [gX_zero] at hg
  have hg1 : g = 1 := Subtype.ext hg
  rw [hgσ, hg1, map_one]

end CFSG.Quasithin.H13.Ch4.G2A
