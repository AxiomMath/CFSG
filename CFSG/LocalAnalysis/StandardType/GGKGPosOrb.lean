module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagPair
public import CFSG.LocalAnalysis.StandardType.GGA2Conj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Orb

theorem ggSecFiveOrbInput_of_kgPos (hKG : GGSecFiveKGPosInput) : GGSecFiveOrbInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 i j hij
  classical
  obtain ⟨t, n, f, ψ, hadm, h3t, _hker, _hrange, ht, _hdvd, hTB⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 L (Or.inl rfl) hL
  obtain ⟨ε, hεrefl, -⟩ := hTB
  obtain ⟨a, b, hab3, -⟩ := ggTag_adjStdPair ht hadm h3t
  let M' : CoxeterMatrix (Fin (ggU t n f).D.rank) := coxeterMatrix (ggU t n f).D.isFiniteType
  let ra : MulAut ↥Bs := ((ε (M'.simple a) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  let rb : MulAut ↥Bs := ((ε (M'.simple b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hra_mem : ra ∈ ggAutomizer L Bs := (ε (M'.simple a)).2
  have hrb_mem : rb ∈ ggAutomizer L Bs := (ε (M'.simple b)).2
  have hra_refl : GGIsReflection p ra := hεrefl a
  have hrb_refl : GGIsReflection p rb := hεrefl b
  have hra_A : ra ∈ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hra_mem
  have hrb_A : rb ∈ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrb_mem
  obtain ⟨w₁, i₁, hw₁⟩ :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 hra_A hra_refl
  obtain ⟨w₂, i₂, hw₂⟩ :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 hrb_A hrb_refl
  let t₁ : M.Group := w₁ * M.simple i₁ * w₁⁻¹
  let t₂ : M.Group := w₂ * M.simple i₂ * w₂⁻¹
  have hra_e : ra = ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₁
  have hrb_e : rb = ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₂
  have hne : t₁ ≠ t₂ := by
    intro ht12
    have hεeq : ε (M'.simple a) = ε (M'.simple b) := by
      apply Subtype.coe_injective
      calc ((ε (M'.simple a) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
          = ra := rfl
        _ = ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hra_e
        _ = ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [ht12]
        _ = rb := hrb_e.symm
        _ = ((ε (M'.simple b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := rfl
    have hsimple : M'.simple a = M'.simple b := ε.injective hεeq
    have hsimple' : M'.toCoxeterSystem.simple a = M'.toCoxeterSystem.simple b := by
      simpa [CoxeterMatrix.toCoxeterSystem_simple] using hsimple
    have hab : a = b := CoxeterSystem.simple_injective M'.toCoxeterSystem hsimple'
    rw [hab] at hab3
    rw [M'.diagonal] at hab3
    exact absurd hab3 (by norm_num)
  have horder : orderOf (M'.simple a * M'.simple b) = M'.M a b := by
    have h := CoxeterSystem.orderOf_simple_mul_simple M'.toCoxeterSystem a b
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using h
  have hst : (M'.simple a * M'.simple b) ^ 3 = 1 := by
    have h3o : orderOf (M'.simple a * M'.simple b) = 3 := horder.trans hab3
    rw [← h3o]
    exact pow_orderOf_eq_one _
  have hra_rb : (ra * rb) ^ 3 = 1 := by
    have hmul : ra * rb =
        ((ε (M'.simple a * M'.simple b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
      show ((ε (M'.simple a) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
          ((ε (M'.simple b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
        ((ε (M'.simple a * M'.simple b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
      exact (congrArg Subtype.val (map_mul ε (M'.simple a) (M'.simple b))).symm
    have h2 : (ra * rb) ^ 3 =
        ((ε ((M'.simple a * M'.simple b) ^ 3) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
      rw [hmul]
      exact (congrArg Subtype.val (map_pow ε (M'.simple a * M'.simple b) 3)).symm
    rw [h2, hst, map_one]
    rfl
  have hord : (t₁ * t₂) ^ 3 = 1 := by
    have hra_rb_e : ra * rb =
        ((e (t₁ * t₂) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
      rw [hra_e, hrb_e]
      exact (congrArg Subtype.val (map_mul e t₁ t₂)).symm
    have h1 : ((e ((t₁ * t₂) ^ 3) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = 1 := by
      have h2 : (ra * rb) ^ 3 =
          ((e ((t₁ * t₂) ^ 3) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        rw [hra_rb_e]
        exact (congrArg Subtype.val (map_pow e (t₁ * t₂) 3)).symm
      rw [← h2]
      exact hra_rb
    have h3' : e ((t₁ * t₂) ^ 3) = 1 := Subtype.coe_injective (by simpa using h1)
    exact e.injective (by rw [h3', map_one])
  obtain ⟨w, hw1, hw2⟩ :=
    ggA2_conj hpres.1 h3 ⟨w₁, i₁, rfl⟩ ⟨w₂, i₂, rfl⟩ hne hord hij
  refine ⟨w, L, Or.inl rfl, ?_, ?_⟩
  · have h : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw1]
    rw [h, ← hra_e]
    exact hra_mem
  · have h : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw2]
    rw [h, ← hrb_e]
    exact hrb_mem

end Orb

end CFSG.StandardType
