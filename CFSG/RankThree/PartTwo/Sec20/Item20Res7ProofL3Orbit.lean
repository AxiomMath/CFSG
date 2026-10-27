module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofIndex
public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Aut
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Module

namespace Res7

section Lin

variable {F : Type*} [Field F]

theorem exists_conj_projStabilizer {n : ℕ} {W W' : Submodule F (Fin n → F)}
    (h : finrank F W = finrank F W') :
    ∃ x : projectiveSL n F, projStabilizer W' =
      (projStabilizer W).map (MulAut.conj x : projectiveSL n F →* projectiveSL n F) := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  obtain ⟨g', hg'⟩ := exists_map_flagSpace_eq W'
  rw [← h] at hg'
  refine ⟨proj n F g' * (proj n F g)⁻¹, ?_⟩
  rw [← hg, ← hg', ← projStabilizer_map_conj, ← projStabilizer_map_conj, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_of_three [Finite F] [CharP F 2]
    {X₁ X₂ X₃ : Subgroup (projectiveSL 3 F)}
    (h₁ : X₁ ∈ maximalParabolics (projectiveSL 3 F) 2)
    (h₂ : X₂ ∈ maximalParabolics (projectiveSL 3 F) 2)
    (h₃ : X₃ ∈ maximalParabolics (projectiveSL 3 F) 2) :
    (∃ x : projectiveSL 3 F,
        X₂ = X₁.map (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F)) ∨
      (∃ x : projectiveSL 3 F,
        X₃ = X₁.map (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F)) ∨
      ∃ x : projectiveSL 3 F,
        X₃ = X₂.map (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMP, -, -⟩ := maximal_parabolics (K := F) (n := 3) 2 (by norm_num)
  rw [hMP] at h₁ h₂ h₃
  obtain ⟨W₁, ⟨h01, ht1⟩, rfl⟩ := h₁
  obtain ⟨W₂, ⟨h02, ht2⟩, rfl⟩ := h₂
  obtain ⟨W₃, ⟨h03, ht3⟩, rfl⟩ := h₃
  obtain ⟨a1, b1⟩ := one_le_finrank_and_lt h01 ht1
  obtain ⟨a2, b2⟩ := one_le_finrank_and_lt h02 ht2
  obtain ⟨a3, b3⟩ := one_le_finrank_and_lt h03 ht3
  by_cases e12 : finrank F W₁ = finrank F W₂
  · exact Or.inl (exists_conj_projStabilizer e12)
  by_cases e13 : finrank F W₁ = finrank F W₃
  · exact Or.inr (Or.inl (exists_conj_projStabilizer e13))
  have e23 : finrank F W₂ = finrank F W₃ := by omega
  exact Or.inr (Or.inr (exists_conj_projStabilizer e23))

end Lin

theorem eq_map_conj_of_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) {X Y : Subgroup A}
    {x : B} (h : Y.map e.toMonoidHom = (X.map e.toMonoidHom).map (MulAut.conj x : B →* B)) :
    Y = X.map (MulAut.conj (e.symm x)).toMonoidHom := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

section Grp

variable {G : Type} [Group G]

theorem map_conj_one (S : Subgroup G) : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  ext x
  simp

theorem map_conj_map_conj (S : Subgroup G) (a b : G) :
    (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      S.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    _root_.mul_inv_rev, mul_assoc]

theorem relIndex_le_two_of [Finite G] {H M : Subgroup G}
    (h : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, a⁻¹ * b ∈ H ∨ a⁻¹ * c ∈ H ∨ b⁻¹ * c ∈ H) :
    H.relIndex M ≤ 2 := by
  classical
  rw [Subgroup.relIndex, Subgroup.index]
  by_contra hlt
  push Not at hlt
  have : Fintype (M ⧸ H.subgroupOf M) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hlt
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  rcases h a a.2 b b.2 c c.2 with h1 | h1 | h1
  · exact hxy (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))
  · exact hxz (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))
  · exact hyz (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using h1)))

theorem map_conj_img {K Q : Subgroup G} (hQK : Q ≤ K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ((Q.map (MulAut.conj g).toMonoidHom).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
      ((Q.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).map
        (Res6.quotAut K (K.normalizerMonoidHom ⟨g, hg⟩)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    refine ⟨QuotientGroup.mk' _ ⟨q, hQK hq⟩,
      ⟨⟨q, hQK hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, Res6.quotAut_apply_mk,
      QuotientGroup.mk'_apply]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, ← hqx]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    refine ⟨K.normalizerMonoidHom ⟨g, hg⟩ x, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Sec4.normalizerMonoidHom_apply_coe]
      exact ⟨x, hx, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        Res6.quotAut_apply_mk]

theorem quotAut_of_mem {K : Subgroup G} {k : G} (hk : k ∈ K) :
    Res6.quotAut K (K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩) =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hk⟩) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) z
  rw [QuotientGroup.mk'_apply, Res6.quotAut_apply_mk, MulAut.conj_apply, QuotientGroup.mk'_apply,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1

theorem eq_of_img_eq {K A B : Subgroup G} (hOA : CFSG.Open.pCoreOf 2 K ≤ A) (hAK : A ≤ K)
    (hOB : CFSG.Open.pCoreOf 2 K ≤ B) (hBK : B ≤ K)
    (h : (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
      (B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) : A = B := by
  have hA : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ A.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hOA ((Sec18.mem_pCore_iff_mem_pCoreOf _).mp hx))
  have hB : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ B.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hOB ((Sec18.mem_pCore_iff_mem_pCoreOf _).mp hx))
  have h1 : A.subgroupOf K = B.subgroupOf K := by
    rw [← Subgroup.comap_map_eq_self hA, h, Subgroup.comap_map_eq_self hB]
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_of_le_left hAK, inf_of_le_left hBK] at h2

end Grp

end Res7

theorem kFactL3ParabolicOrbit_holds : KFactL3ParabolicOrbit := by
  intro G _ _ M K P n hKM hMK ⟨e₀⟩ hOP hPK hpar
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set ψ : K ⧸ CFSG.pCore 2 K ≃* projectiveSL 3 F :=
    e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 F) with hψ
  set N₀ := M ⊓ Subgroup.normalizer (P : Set G) with hN₀
  set H := K ⊔ N₀ with hH
  have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hPgK : ∀ g ∈ M, P.map (MulAut.conj g).toMonoidHom ≤ K := by
    intro g hg
    rw [← Late.map_conj_eq_of_mem_normalizer (hMK hg)]
    exact Subgroup.map_mono hPK
  have hOPg : ∀ g ∈ M, CFSG.Open.pCoreOf 2 K ≤ P.map (MulAut.conj g).toMonoidHom := by
    intro g hg
    rw [← Late.map_conj_eq_of_mem_normalizer (hMO hg)]
    exact Subgroup.map_mono hOP
  have hpar_g : ∀ g ∈ M, Sec18.IsMaxParabolicRankTwo
      (((P.map (MulAut.conj g).toMonoidHom).subgroupOf K).map π) := by
    intro g hg
    rw [Res7.map_conj_img hPK (hMK hg)]
    exact Res7.isMaxParabolicRankTwo_map _ hpar
  have hmem : ∀ g ∈ M, (((P.map (MulAut.conj g).toMonoidHom).subgroupOf K).map π).map
      ψ.toMonoidHom ∈ maximalParabolics (projectiveSL 3 F) 2 := by
    intro g hg
    obtain ⟨hc, T, hT⟩ := Res7.isMaxParabolicRankTwo_map ψ (hpar_g g hg)
    exact ⟨hc, _, ⟨T, rfl⟩, hT⟩
  have hkey : ∀ a ∈ M, ∀ b ∈ M, ∀ y : K ⧸ CFSG.pCore 2 K,
      ((P.map (MulAut.conj b).toMonoidHom).subgroupOf K).map π =
        (((P.map (MulAut.conj a).toMonoidHom).subgroupOf K).map π).map
          (MulAut.conj y).toMonoidHom → a⁻¹ * b ∈ H := by
    intro a ha b hb y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) y
    have hka : (k : G) * a ∈ M := M.mul_mem (hKM k.2) ha
    have hy' : ((P.map (MulAut.conj b).toMonoidHom).subgroupOf K).map π =
        ((P.map (MulAut.conj ((k : G) * a)).toMonoidHom).subgroupOf K).map π := by
      rw [hy, Res7.map_conj_img hPK (hMK hka), Res7.map_conj_img hPK (hMK ha), Subgroup.map_map]
      congr 1
      rw [← Res7.quotAut_of_mem k.2]
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← MulAut.mul_apply, ← map_mul, ← map_mul]
      rfl
    have heq := Res7.eq_of_img_eq (hOPg b hb) (hPgK b hb) (hOPg _ hka) (hPgK _ hka) hy'
    have hN : ((k : G) * a)⁻¹ * b ∈ N₀ := by
      refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.inv_mem hka) hb, ?_⟩
      have hP' : P.map (MulAut.conj (((k : G) * a)⁻¹ * b)).toMonoidHom = P := by
        rw [← Res7.map_conj_map_conj, heq, Res7.map_conj_map_conj, inv_mul_cancel,
          Res7.map_conj_one]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hP'
    have hk' : a⁻¹ * (k : G) * a ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hMK (M.inv_mem ha)) k).mp k.2
      simpa [mul_assoc] using this
    have e1 : a⁻¹ * b = (a⁻¹ * (k : G) * a) * (((k : G) * a)⁻¹ * b) := by group
    rw [e1]
    exact H.mul_mem (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right hN)
  have h3 : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, a⁻¹ * b ∈ H ∨ a⁻¹ * c ∈ H ∨ b⁻¹ * c ∈ H := by
    intro a ha b hb c hc
    rcases Res7.exists_conj_of_three (hmem a ha) (hmem b hb) (hmem c hc) with
      ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl (hkey a ha b hb _ (Res7.eq_map_conj_of_map ψ hx))
    · exact Or.inr (Or.inl (hkey a ha c hc _ (Res7.eq_map_conj_of_map ψ hx)))
    · exact Or.inr (Or.inr (hkey b hb c hc _ (Res7.eq_map_conj_of_map ψ hx)))
  have hHM2 : H.relIndex M ≤ 2 := Res7.relIndex_le_two_of h3
  have hN₀K : N₀ ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans hMK
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN₀K
  have hr1 := Subgroup.relIndex_mul_card N₀ H
  rw [inf_of_le_left (le_sup_right : N₀ ≤ H)] at hr1
  have hr2 := Subgroup.relIndex_mul_card (K ⊓ N₀) K
  rw [inf_of_le_left inf_le_left] at hr2
  have hidx : N₀.relIndex H = (K ⊓ N₀).relIndex K := by
    have hpos : 0 < Nat.card N₀ * Nat.card (K ⊓ N₀ : Subgroup G) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc N₀.relIndex H * (Nat.card N₀ * Nat.card (K ⊓ N₀ : Subgroup G))
        = Nat.card H * Nat.card (K ⊓ N₀ : Subgroup G) := by rw [← hr1]; ring
      _ = Nat.card K * Nat.card N₀ := hcard
      _ = (K ⊓ N₀).relIndex K * (Nat.card N₀ * Nat.card (K ⊓ N₀ : Subgroup G)) := by
        rw [← hr2]; ring
  have hPN₀ : P ≤ K ⊓ N₀ := le_inf hPK (le_inf (hPK.trans hKM) Subgroup.le_normalizer)
  have hdvd : (K ⊓ N₀).relIndex K ∣ P.relIndex K := Subgroup.relIndex_dvd_of_le_left K hPN₀
  have hPodd : ¬ 2 ∣ P.relIndex K := by
    obtain ⟨-, T, hT⟩ := hpar
    have hTP : (T : Subgroup _) ≤ (P.subgroupOf K).map π := Subgroup.le_normalizer.trans hT
    have hker : π.ker ≤ P.subgroupOf K := by
      rw [hπ, QuotientGroup.ker_mk']
      exact fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hOP ((Sec18.mem_pCore_iff_mem_pCoreOf _).mp hx))
    have h1 : ((P.subgroupOf K).map π).index = (P.subgroupOf K).index :=
      Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker
    rw [Subgroup.relIndex, ← h1]
    intro h2
    exact T.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hTP))
  have hodd : ¬ 2 ∣ N₀.relIndex H := by
    rw [hidx]
    exact fun h => hPodd (h.trans hdvd)
  have hmul := Subgroup.relIndex_mul_relIndex N₀ H M le_sup_right (sup_le hKM inf_le_left)
  have hHM0 : H.relIndex M ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  intro h4
  rw [← hmul] at h4
  have hcop : Nat.Coprime 4 (N₀.relIndex H) := by
    have : Nat.Coprime 2 (N₀.relIndex H) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    exact Nat.Coprime.pow_left 2 this
  have h4' : 4 ∣ H.relIndex M := hcop.dvd_of_dvd_mul_left h4
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hHM0) h4'
  omega

end CFSG.RankThree.PartTwo.Sec20
