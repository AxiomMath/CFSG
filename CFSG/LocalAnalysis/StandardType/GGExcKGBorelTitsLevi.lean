module

public import CFSG.LocalAnalysis.StandardType.GGExcKGRankKnown
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankProp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwoLocalLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

section ExcCertBTLevi

theorem ggExcKGBorelTits_of_leviRank (hlev : E8LeviRankLE3)
    (n f : ℕ) (G : Type) [Group G] [Finite G] (ψ : (ggU .E8 n f).K →* G)
    (hset : GGKnownSetting .E8 n f ψ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf ((2 : ZMod p) ^ f) ∈ ({3, 4, 6} : Set ℕ))
    (E : Subgroup G) (hEn : E ≤ Subgroup.normalizer (ψ.range : Set G)) (hE : IsElemAbelian p E)
    (hcard : p ^ 4 ≤ Nat.card E) (hdiag : ∀ b ∈ E, GGPsiInnerDiag (ggU .E8 n f).D ψ b)
    (T : Subgroup G) (hTn : T ≤ Subgroup.normalizer (ψ.range : Set G)) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    E ≤ Subgroup.centralizer (T : Set G) := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le
  have hEr : E ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_E8 G n f ψ ψ.range
      ⟨⟨hadm, hrk⟩, ⟨rfl, hker⟩, hcomm, hlie⟩ b (hEn hb) (hdiag b hb)
    rw [hcent, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hT0 : T ⊓ ψ.range = ⊥ := by
    by_contra hne
    let U : Subgroup (ggU .E8 n f).K := (T ⊓ ψ.range).comap ψ
    have hUne : U ≠ ⊥ := by
      intro hUbot
      apply hne
      rw [eq_bot_iff]
      intro t ht
      obtain ⟨k, hk⟩ := ht.2
      have hkU : k ∈ U := by
        show ψ k ∈ T ⊓ ψ.range
        rw [hk]; exact ht
      rw [hUbot, Subgroup.mem_bot] at hkU
      rw [Subgroup.mem_bot, ← hk, hkU, map_one]
    have hU2 : IsPGroup 2 U :=
      (hT2.to_le (inf_le_left : T ⊓ ψ.range ≤ T)).comap_of_injective ψ hinj
    obtain ⟨hE', hcardE'⟩ := kgr_pullback_adjoint .E8 n f G ψ p E hEr hinj hE
    have hE'n : E.comap ψ ≤ Subgroup.normalizer (U : Set (ggU .E8 n f).K) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have he' : ψ e ∈ E := Subgroup.mem_comap.1 he
      have h1 := Subgroup.mem_normalizer_iff.1 (hET he') (ψ u)
      have h2 := Subgroup.mem_normalizer_iff.1 (hEn he') (ψ u)
      show ψ u ∈ T ⊓ ψ.range ↔ ψ (e * u * e⁻¹) ∈ T ⊓ ψ.range
      rw [map_mul, map_mul, map_inv, Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr h1 h2
    have hc : (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = (2 : ZMod p) ^ f := by
      rw [hq]; push_cast; rfl
    have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
      intro hdvd
      rw [hq] at hdvd
      have h0 : (((2 ^ f - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      rw [Nat.cast_sub Nat.one_le_two_pow] at h0
      push_cast at h0
      rw [sub_eq_zero.1 h0, orderOf_one] at hord
      simp at hord
    have key : Nat.card (E.comap ψ) ≤ p ^ 3 := CFSG.LocalAnalysis.GLTheoremA.twoLocal_card_le_of_levi'
      (τ := Tag.E8) (K := GaloisField 2 f) (k := 3) hp hp2 hpq
      (fun J hJ F hF hFel =>
        hlev (GaloisField 2 f) p hp hp2 (by rw [hc]; exact hord) J hJ F hF hFel)
      hUne hU2 hE'n hE'
    have h34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hc1 : t⁻¹ * (e * t * e⁻¹) ∈ T :=
    T.mul_mem (T.inv_mem ht) ((Subgroup.mem_normalizer_iff.1 (hET he) t).1 ht)
  have hc2 : t⁻¹ * (e * t * e⁻¹) ∈ ψ.range := by
    have h3 : t⁻¹ * e * t ∈ ψ.range := by
      have := (Subgroup.mem_normalizer_iff.1 (hTn (T.inv_mem ht)) e).1 (hEr he)
      simpa using this
    have h' : t⁻¹ * (e * t * e⁻¹) = (t⁻¹ * e * t) * e⁻¹ := by group
    rw [h']
    exact ψ.range.mul_mem h3 (ψ.range.inv_mem (hEr he))
  have h0 : t⁻¹ * (e * t * e⁻¹) ∈ T ⊓ ψ.range := ⟨hc1, hc2⟩
  rw [hT0, Subgroup.mem_bot] at h0
  have h2 : t = e * t * e⁻¹ := inv_mul_eq_one.1 h0
  calc t * e = e * t * e⁻¹ * e := by rw [← h2]
    _ = e * t := by group

end ExcCertBTLevi

end CFSG.StandardType
