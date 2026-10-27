module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.Open.Defs
public import Mathlib.GroupTheory.Perm.ViaEmbedding
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Extension
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.Permutation.Embedding
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

section General

variable {f : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)}

private theorem oaQ_coords_normPerm_last {G : Type} [Group G]
    {Bs X : Subgroup G} {n r p : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : ∀ b : ↥Bs, (b : G) ∈ X → eta b (π (Fin.last r)) = 1)
    (σ : Equiv.Perm (Fin r))
    (hσ : κ (normPerm E hr σ) ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    eta (ggConjAut Bs hσ b) (π (Fin.last r)) = eta b (π (Fin.last r)) := by
  classical
  let τ : (Fin r → Multiplicative (ZMod p)) →* normOmega E r :=
    normPlaneTorus E (by omega : 2 ≤ r) hpq χ
  let u : Fin r → Multiplicative (ZMod p) := fun i => eta b (π i.castSucc)
  let t : G := κ (τ u)
  let v : Fin r → Multiplicative (ZMod p) := fun i => u (σ⁻¹ i)
  let tv : G := κ (τ v)
  have htBs : t ∈ Bs := hframe.normPlaneTorus_mem_Bs_of_dvd (by omega) hpq hSC u
  have htvBs : tv ∈ Bs := hframe.normPlaneTorus_mem_Bs_of_dvd (by omega) hpq hSC v
  have hconj := hframe.conj_normPerm_eq_of_dvd hr hpq hSC σ b
  have hsub : ggConjAut Bs hσ b = b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩ := by
    ext
    simpa [t, tv, u, v, ggConjAut_apply] using hconj
  have htX : t ∈ X := by
    rw [← hframe.2.1]
    exact ⟨_, rfl⟩
  have htvX : tv ∈ X := by
    rw [← hframe.2.1]
    exact ⟨_, rfl⟩
  have htlast : eta ⟨t, htBs⟩ (π (Fin.last r)) = 1 := hX ⟨t, htBs⟩ htX
  have hvlast : eta ⟨tv, htvBs⟩ (π (Fin.last r)) = 1 := hX ⟨tv, htvBs⟩ htvX
  calc eta (ggConjAut Bs hσ b) (π (Fin.last r))
      = eta (b * (⟨t, htBs⟩ : ↥Bs)⁻¹ * ⟨tv, htvBs⟩) (π (Fin.last r)) := by rw [hsub]
    _ = eta b (π (Fin.last r)) * (eta ⟨t, htBs⟩ (π (Fin.last r)))⁻¹ *
          eta ⟨tv, htvBs⟩ (π (Fin.last r)) := by
          simp [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
    _ = eta b (π (Fin.last r)) := by simp [htlast, hvlast]

theorem GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last_of_dvd {G : Type} [Group G]
    {Bs X : Subgroup G} {n r p : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : ∀ b : Bs, (b : G) ∈ X → eta b (π (Fin.last r)) = 1) (σ : Equiv.Perm (Fin r))
    (hσ : κ (normPerm E hr σ) ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut.congr eta (ggConjAut Bs hσ) =
      SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
        ((Fin.castSuccEmb (n := r)).trans π.toEmbedding) σ) := by
  classical
  let ι : Fin r ↪ Fin n := (Fin.castSuccEmb (n := r)).trans π.toEmbedding
  apply MulEquiv.ext
  intro v
  obtain ⟨b, rfl⟩ := eta.surjective v
  have hcongr : (MulAut.congr eta (ggConjAut Bs hσ)) (eta b) =
      eta (ggConjAut Bs hσ b) := by
    funext j
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  funext j
  obtain ⟨k, rfl⟩ := π.surjective j
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · rw [hcongr, hframe.coords_normPerm_of_dvd hr hpq hSC σ b i]
    rw [SpCoord.permAut_apply]
    have hinv : (Equiv.Perm.viaEmbeddingHom ι σ)⁻¹ =
        Equiv.Perm.viaEmbeddingHom ι σ⁻¹ := by rw [map_inv]
    rw [hinv, Equiv.Perm.viaEmbeddingHom_apply]
    change eta b (π (σ⁻¹ i).castSucc) =
      eta b ((Equiv.Perm.viaEmbedding σ⁻¹ ι) (ι i))
    rw [Equiv.Perm.viaEmbedding_apply]
    rfl
  · rw [hcongr,
      oaQ_coords_normPerm_last (hframe := hframe) (hr := hr) (hpq := hpq) (hSC := hSC)
        (hX := hX) (σ := σ) (hσ := hσ) (b := b)]
    rw [SpCoord.permAut_apply]
    have hnot : π (Fin.last r) ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      simp [ι] at hi
    have hinv : (Equiv.Perm.viaEmbeddingHom ι σ)⁻¹ =
        Equiv.Perm.viaEmbeddingHom ι σ⁻¹ := by rw [map_inv]
    rw [hinv, Equiv.Perm.viaEmbeddingHom_apply]
    change eta b (π (Fin.last r)) =
      eta b ((Equiv.Perm.viaEmbedding σ⁻¹ ι) (π (Fin.last r)))
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem (e := σ⁻¹) (ι := ι)
      (x := π (Fin.last r)) hnot]

theorem GGSecFiveBPermOmKFrame.exists_normOmega_hom_of_permHom_of_dvd {G : Type} [Group G]
    [Finite G] {Bs L X : Subgroup G} {x : G} {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k)
    (hpq : p ∣ 2 ^ f + 1)
    {eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod p))} {π : Fin (k + 4) ≃ Fin (k + 4)}
    {κ₁ κ₂ : normOmega E (k + 3) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    {t : Equiv.Perm (Fin (k + 4)) →* G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hx : x ∈ Bs) (hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (h₂ : GGSecFiveBPermOmKFrame E Bs X eta ((finRotate (k + 4)).trans π) κ₂ χ)
    (hX : ∀ b : Bs, (b : G) ∈ X → eta b (π 0) = 1)
    (ht₁ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
      κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)))
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
      κ₂.comp (normPerm E (by omega : 3 ≤ k + 3))) :
    ∃ Ψ : normOmega E (k + 4) →* G, Function.Injective Ψ ∧
      (∀ a, Ψ (normOmegaCast E (Nat.le_succ (k + 3)) a) = κ₁ a) ∧
      (∀ σ, Ψ (normPerm E (by omega : 3 ≤ k + 4) σ) = t σ) ∧ Ψ.range = L ⊔ t.range := by
  classical
  let σ : Equiv.Perm (Fin (k + 3)) :=
    Equiv.swap (⟨k, by omega⟩ : Fin (k + 3)) (Fin.last (k + 2))
  have h1 : Fin.succEmb (k + 3) (⟨k, by omega⟩ : Fin (k + 3)) =
      (⟨k + 3 - 2, by omega⟩ : Fin (k + 4)) := by
    change Fin.succ (⟨k, by omega⟩ : Fin (k + 3)) =
      (⟨k + 3 - 2, by omega⟩ : Fin (k + 4))
    rw [Fin.succ_mk]
    congr 1
  have h2 : Fin.succEmb (k + 3) (Fin.last (k + 2)) = Fin.last (k + 3) := by
    refine Fin.ext ?_
    rw [Fin.coe_succEmb, Fin.val_succ, Fin.val_last, Fin.val_last]
  have hs : Equiv.swap (⟨k + 3 - 2, by omega⟩ : Fin (k + 4)) (Fin.last (k + 3)) =
      Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3)) σ := by
    rw [show σ = Equiv.swap (⟨k, by omega⟩ : Fin (k + 3)) (Fin.last (k + 2)) from rfl,
      CFSG.Permutation.viaEmbeddingHom_swap, h1, h2]
  let g : G := κ₂ (normPerm E (by omega : 3 ≤ k + 3) σ)
  have hts : t (Equiv.swap (⟨k + 3 - 2, by omega⟩ : Fin (k + 4)) (Fin.last (k + 3))) =
      g := by
    have h := DFunLike.congr_fun ht₂ σ
    simp only [MonoidHom.comp_apply] at h
    rw [← hs] at h
    exact h
  have hX₂ : ∀ b : ↥Bs, (b : G) ∈ X →
      eta b (((finRotate (k + 4)).trans π) (Fin.last (k + 3))) = 1 := by
    intro b hb
    rw [Equiv.trans_apply, finRotate_last]
    exact hX b hb
  let e : Fin (k + 3) ↪ Fin (k + 4) :=
    (Fin.castSuccEmb (n := k + 3)).trans ((finRotate (k + 4)).trans π).toEmbedding
  let τ : Equiv.Perm (Fin (k + 4)) := Equiv.Perm.viaEmbeddingHom e σ
  have hg : g ∈ Subgroup.normalizer (Bs : Set G) :=
    h₂.normPerm_mem_normalizer_of_dvd (by omega) hpq hSC σ
  have hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ :=
    GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last_of_dvd (E := E) h₂ (by omega) hpq hSC
      hX₂ σ hg
  have he : ∀ i : Fin (k + 3), e i = π i.succ := by
    intro i
    simp [e]
  have h0not : (π 0 : Fin (k + 4)) ∉ Set.range e := by
    rintro ⟨i, hi⟩
    rw [he i] at hi
    exact Fin.succ_ne_zero i (π.injective hi)
  have hτ0 : τ (π 0) = π 0 := by
    change Equiv.Perm.viaEmbeddingHom e σ (π 0) = π 0
    rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem (e := σ) (ι := e) (x := π 0) h0not]
  have he0 : e (⟨0, by omega⟩ : Fin (k + 3)) = π ⟨1, by omega⟩ := by
    simpa using he ⟨0, by omega⟩
  have hσ0 : σ (⟨0, by omega⟩ : Fin (k + 3)) = ⟨0, by omega⟩ := by
    rw [show σ = Equiv.swap (⟨k, by omega⟩ : Fin (k + 3)) (Fin.last (k + 2)) from rfl]
    exact Equiv.swap_apply_of_ne_of_ne
      (by
        intro h
        have hval : (0 : ℕ) = k := by simpa using congrArg Fin.val h
        omega)
      (by
        intro h
        have hval : (0 : ℕ) = k + 2 := by simpa using congrArg Fin.val h
        omega)
  have hτ1 : τ (π ⟨1, by omega⟩) = π ⟨1, by omega⟩ := by
    calc τ (π ⟨1, by omega⟩) = τ (e ⟨0, by omega⟩) := by rw [he0]
      _ = e (σ ⟨0, by omega⟩) := by
          change Equiv.Perm.viaEmbeddingHom e σ (e ⟨0, by omega⟩) =
            e (σ ⟨0, by omega⟩)
          rw [Equiv.Perm.viaEmbeddingHom_apply]
          exact Equiv.Perm.viaEmbedding_apply σ e ⟨0, by omega⟩
      _ = e ⟨0, by omega⟩ := by rw [hσ0]
      _ = π ⟨1, by omega⟩ := he0
  have hτS : τ '' ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4))) =
      ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4))) := by
    rw [Set.image_pair, hτ0, hτ1]
  have h01 : (⟨0, by omega⟩ : Fin (k + 3)) ≠ ⟨1, by omega⟩ := by
    intro h
    have hval : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  have hS : ((fun i : Fin (k + 3) => π i.castSucc) ''
      (↑({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (k + 3))) : Set (Fin (k + 3)))) =
      ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4))) := by
    rw [Finset.coe_pair, Set.image_pair]
    rfl
  have hblock : (anchorBlock E (by omega : 2 ≤ k + 3)).map κ₁ =
      ggBlockComm Bs eta ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4))) := by
    rw [anchorBlock_eq_normBlock (E := E) (m := k + 3) (by omega)]
    rw [← GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock (hBs := hSC) (hyB := hx)
      (hX := hLc) (hκ := h₁) (S := ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (k + 3))))
      (by rw [Finset.card_pair h01]) (by rw [Finset.card_pair h01]; omega)]
    exact congrArg (ggBlockComm Bs eta) hS
  have hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ k + 3)).map κ₁,
      t (Equiv.swap (⟨k + 3 - 2, by omega⟩ : Fin (k + 4)) (Fin.last (k + 3))) * y *
        (t (Equiv.swap (⟨k + 3 - 2, by omega⟩ : Fin (k + 4)) (Fin.last (k + 3))))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ k + 3)).map κ₁ := by
    intro y hy
    rw [hblock] at hy ⊢
    have hmap := ggBlockComm_map_conj (eta := eta) hg hτ
      ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4)))
    rw [hτS] at hmap
    have hmem : (MulAut.conj g).toMonoidHom y ∈
        (ggBlockComm Bs eta ({π 0, π ⟨1, by omega⟩} : Set (Fin (k + 4)))).map
          (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rw [hmap] at hmem
    rw [hts]
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hmem
  obtain ⟨Ψ, hΨinj, hΨcast, hΨperm, hΨrange⟩ :=
    exists_normOmega_hom_of_perm E (m := k + 3) (by omega) t κ₁ h₁.1 ht₁ hT2
  exact ⟨Ψ, hΨinj, hΨcast, hΨperm, by rw [hΨrange, h₁.2.1]⟩

end General

section QTwo

variable {E : QuadExt F K (unitaryInvolution K 2 1)}

theorem GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last {G : Type} [Group G]
    {Bs X : Subgroup G} {n r : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {π : Fin (r + 1) ≃ Fin n} {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) (hr : 3 ≤ r)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hX : ∀ b : Bs, (b : G) ∈ X → eta b (π (Fin.last r)) = 1) (σ : Equiv.Perm (Fin r))
    (hσ : κ (normPerm E hr σ) ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut.congr eta (ggConjAut Bs hσ) =
      SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
        ((Fin.castSuccEmb (n := r)).trans π.toEmbedding) σ) :=
  hframe.congr_normPerm_of_coord_last_of_dvd hr (by decide : 3 ∣ 2 ^ 1 + 1) hSC hX σ hσ

theorem GGSecFiveBPermOmKFrame.exists_normOmega_hom_of_permHom {G : Type} [Group G] [Finite G]
    {Bs L X : Subgroup G} {x : G} {k : ℕ} (hk : 1 ≤ k)
    {eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod 3))} {π : Fin (k + 4) ≃ Fin (k + 4)}
    {κ₁ κ₂ : normOmega E (k + 3) →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    {t : Equiv.Perm (Fin (k + 4)) →* G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hx : x ∈ Bs) (hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (h₂ : GGSecFiveBPermOmKFrame E Bs X eta ((finRotate (k + 4)).trans π) κ₂ χ)
    (hX : ∀ b : Bs, (b : G) ∈ X → eta b (π 0) = 1)
    (ht₁ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
      κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)))
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
      κ₂.comp (normPerm E (by omega : 3 ≤ k + 3))) :
    ∃ Ψ : normOmega E (k + 4) →* G, Function.Injective Ψ ∧
      (∀ a, Ψ (normOmegaCast E (Nat.le_succ (k + 3)) a) = κ₁ a) ∧
      (∀ σ, Ψ (normPerm E (by omega : 3 ≤ k + 4) σ) = t σ) ∧ Ψ.range = L ⊔ t.range :=
  GGSecFiveBPermOmKFrame.exists_normOmega_hom_of_permHom_of_dvd hk (by decide : 3 ∣ 2 ^ 1 + 1)
    hSC h₁ hx hLc h₂ hX ht₁ ht₂

end QTwo

end CFSG.StandardType

end
