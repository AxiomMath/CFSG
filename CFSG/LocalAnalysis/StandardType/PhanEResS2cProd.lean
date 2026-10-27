module

public import CFSG.LocalAnalysis.StandardType.PhanEResS2c

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem pls2p_mem_refSet_flagAct_iff {n : ℕ} {d : List ℕ} {e : GL (Fin n) K}
    (he : StabV n d e) (x : FlagK K n) :
    flagAct e x ∈ refSet K n d ↔ x ∈ refSet K n d := by
  have himg := flagMap_image_refSet (glLin e) he
  constructor
  · intro hx
    have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K n d := by
      rw [himg]; exact hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzx' : z = x := flagMap_injective (glLin e) hzx
    rwa [hzx'] at hz
  · intro hx
    have hx' : flagMap (glLin e) x ∈ flagMap (glLin e) '' refSet K n d :=
      Set.mem_image_of_mem _ hx
    rwa [himg] at hx'

private theorem pls2p_flagPsi'_eq (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} {d : List ℕ}
    (hd : IsCut n d) (pol : Bool) (pl : List Bool)
    (hpl : ∀ b, b + 1 < d.length → 2 ≤ blockSize d b → pl.getD b false = pol)
    {x : FlagK K n} (hx : x ∈ refSet K n d) :
    flagPsi' K f hK n d pl x = flagPsi hK hd (List.replicate (d.length - 1) pol) x := by
  rw [flagPsi', dif_pos hd]
  exact flagPsi_eq_of_pol_eq hK hd pl (List.replicate (d.length - 1) pol)
    (fun b hb h2 => by
      rw [hpl b hb h2]
      simp [List.getD_replicate, show b < d.length - 1 from by omega]) hx

theorem exists_chart_prod {I C : Type} (X : ChamberSystem I C) (hK : Nat.card K = (2 ^ f) ^ 2)
    {m₁ m₂ : ℕ} {d₁ d₂ : List ℕ} (hd₁ : IsCut (m₁ + 1) d₁) (hd₂ : IsCut (m₂ + 1) d₂)
    (S : Set C) (ψ : C → C) (Θ₀ : ChamberIso X ((flagSys K m₁).prod (flagSys K m₂)))
    (N₁ : GL (Fin (m₁ + 1)) K) (N₂ : GL (Fin (m₂ + 1)) K)
    (hN₁ : StabV (m₁ + 1) d₁ N₁) (hN₂ : StabV (m₂ + 1) d₂ N₂)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈ refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c) (pol₁ pol₂ : Bool)
    (P₁ : SpecialLinearGroup (Fin (m₁ + 1)) K) (P₂ : SpecialLinearGroup (Fin (m₂ + 1)) K)
    (hP₁ : (P₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) K) =
      if pol₁ then (revBlocks K (m₁ + 1) d₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) K) else 1)
    (hP₂ : (P₂ : Matrix (Fin (m₂ + 1)) (Fin (m₂ + 1)) K) =
      if pol₂ then (revBlocks K (m₂ + 1) d₂ : Matrix (Fin (m₂ + 1)) (Fin (m₂ + 1)) K) else 1)
    (hψ : ∀ A₁ ∈ blockSL K m₁ d₁, ∀ A₂ ∈ blockSL K m₂ d₂, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag K (m₁ + 1)),
        flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K (m₂ + 1))) →
        Θ₀.Φ (ψ c) =
          (flagAct N₁ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol₁ P₁ A₁))
              (stdFlag K (m₁ + 1))),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol₂ P₂ A₂))
              (stdFlag K (m₂ + 1)))))
    (pl₁ pl₂ : List Bool)
    (hpl₁ : ∀ b, b + 1 < d₁.length → 2 ≤ blockSize d₁ b → pl₁.getD b false = pol₁)
    (hpl₂ : ∀ b, b + 1 < d₂.length → 2 ≤ blockSize d₂ b → pl₂.getD b false = pol₂) :
    ∃ Θ : ChamberIso X ((flagSys K m₁).prod (flagSys K m₂)),
      (∀ c, c ∈ S ↔ Θ.Φ c ∈ refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = Prod.map (flagPsi' K f hK (m₁ + 1) d₁ pl₁)
        (flagPsi' K f hK (m₂ + 1) d₂ pl₂) (Θ.Φ c) := by
  have hkey : ∀ c ∈ S, Θ₀.Φ (ψ c) =
      (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
          (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) (Θ₀.Φ c).1),
        flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
          (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) (Θ₀.Φ c).2)) := by
    intro c hc
    have hy := (hS c).mp hc
    obtain ⟨hy₁, hy₂⟩ := Set.mem_prod.mp hy
    obtain ⟨A₁, hA₁, hA₁x⟩ := exists_blockSL_of_mem_refSet hd₁ hy₁
    obtain ⟨A₂, hA₂, hA₂x⟩ := exists_blockSL_of_mem_refSet hd₂ hy₂
    have hpair : Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL A₁) (stdFlag K (m₁ + 1)),
        flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K (m₂ + 1))) := Prod.ext hA₁x hA₂x
    have hψc := hψ A₁ hA₁ A₂ hA₂ c hc hpair
    rw [hψc, hA₁x, hA₂x]
    exact Prod.ext (flagAct_kapMat_stdFlag hK hd₁ N₁ pol₁ P₁ hP₁ hA₁)
      (flagAct_kapMat_stdFlag hK hd₂ N₂ pol₂ P₂ hP₂ hA₂)
  have hinv_pair : ∀ p ∈ refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂,
      (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
          (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁)
            (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
              (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) p.1))),
        flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
          (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂)
            (flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
              (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) p.2)))) = p := by
    intro p hp
    let c : C := Θ₀.Φ.symm p
    have hcΦ : Θ₀.Φ c = p := Θ₀.Φ.apply_symm_apply p
    have hcS : c ∈ S := (hS c).mpr (by rw [hcΦ]; exact hp)
    have h1 := hkey c hcS
    have h2 := hkey (ψ c) (hψS c hcS)
    rw [hψψ c hcS, h1, hcΦ] at h2
    exact h2.symm
  have hinv₁ : ∀ x ∈ refSet K (m₁ + 1) d₁,
      flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
        (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁)
          (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
            (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) x))) = x := by
    intro x hx
    have h := hinv_pair (x, stdFlag K (m₂ + 1))
      (Set.mem_prod.mpr ⟨hx, stdFlag_mem_refSet hd₂⟩)
    exact congrArg Prod.fst h
  have hinv₂ : ∀ x ∈ refSet K (m₂ + 1) d₂,
      flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
        (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂)
          (flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
            (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) x))) = x := by
    intro x hx
    have h := hinv_pair (stdFlag K (m₁ + 1), x)
      (Set.mem_prod.mpr ⟨stdFlag_mem_refSet hd₁, hx⟩)
    exact congrArg Prod.snd h
  obtain ⟨e₁, he₁, heq₁⟩ := exists_normalForm_flagPsi hK hd₁
    (List.replicate (d₁.length - 1) pol₁) (stabV_pathMat hd₁ hN₁ pol₁) hinv₁
  obtain ⟨e₂, he₂, heq₂⟩ := exists_normalForm_flagPsi hK hd₂
    (List.replicate (d₂.length - 1) pol₂) (stabV_pathMat hd₂ hN₂ pol₂) hinv₂
  let Θ : ChamberIso X ((flagSys K m₁).prod (flagSys K m₂)) :=
    Θ₀.trans ((flagMapIso (glLin e₁)).prodCongr (flagMapIso (glLin e₂)))
  have hΘ : ∀ c, Θ.Φ c = (flagAct e₁ (Θ₀.Φ c).1, flagAct e₂ (Θ₀.Φ c).2) := fun _ => rfl
  refine ⟨Θ, ?_, ?_⟩
  · intro c
    rw [hS c, hΘ c]
    simp only [Set.mem_prod]
    exact and_congr (pls2p_mem_refSet_flagAct_iff he₁ _).symm
      (pls2p_mem_refSet_flagAct_iff he₂ _).symm
  · intro c hc
    have hy := (hS c).mp hc
    obtain ⟨hy₁, hy₂⟩ := Set.mem_prod.mp hy
    have h1 := hkey c hc
    have hc1 : (Θ₀.Φ (ψ c)).1 = flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
        (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) (Θ₀.Φ c).1) := by rw [h1]
    have hc2 : (Θ₀.Φ (ψ c)).2 = flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
        (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) (Θ₀.Φ c).2) := by rw [h1]
    rw [hΘ (ψ c), hc1, hc2, hΘ c]
    simp only [Prod.map_apply']
    refine Prod.ext ?_ ?_
    · have hxmem : flagAct e₁ (Θ₀.Φ c).1 ∈ refSet K (m₁ + 1) d₁ :=
        (pls2p_mem_refSet_flagAct_iff he₁ _).mpr hy₁
      have hn := heq₁ (flagAct e₁ (Θ₀.Φ c).1) hxmem
      rw [flagAct_inv_flagAct] at hn
      rw [pls2p_flagPsi'_eq hK hd₁ pol₁ pl₁ hpl₁ hxmem]
      exact hn
    · have hxmem : flagAct e₂ (Θ₀.Φ c).2 ∈ refSet K (m₂ + 1) d₂ :=
        (pls2p_mem_refSet_flagAct_iff he₂ _).mpr hy₂
      have hn := heq₂ (flagAct e₂ (Θ₀.Φ c).2) hxmem
      rw [flagAct_inv_flagAct] at hn
      rw [pls2p_flagPsi'_eq hK hd₂ pol₂ pl₂ hpl₂ hxmem]
      exact hn

theorem exists_chart_prod3 {I C : Type} (X : ChamberSystem I C) (hK : Nat.card K = (2 ^ f) ^ 2)
    {m₁ m₂ m₃ : ℕ} {d₁ d₂ d₃ : List ℕ} (hd₁ : IsCut (m₁ + 1) d₁) (hd₂ : IsCut (m₂ + 1) d₂)
    (hd₃ : IsCut (m₃ + 1) d₃) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X (((flagSys K m₁).prod (flagSys K m₂)).prod (flagSys K m₃)))
    (N₁ : GL (Fin (m₁ + 1)) K) (N₂ : GL (Fin (m₂ + 1)) K) (N₃ : GL (Fin (m₃ + 1)) K)
    (hN₁ : StabV (m₁ + 1) d₁ N₁) (hN₂ : StabV (m₂ + 1) d₂ N₂) (hN₃ : StabV (m₃ + 1) d₃ N₃)
    (hS : ∀ c, c ∈ S ↔ Θ₀.Φ c ∈
      (refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂) ×ˢ refSet K (m₃ + 1) d₃)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c) (pol₁ pol₂ pol₃ : Bool)
    (P₁ : SpecialLinearGroup (Fin (m₁ + 1)) K) (P₂ : SpecialLinearGroup (Fin (m₂ + 1)) K)
    (P₃ : SpecialLinearGroup (Fin (m₃ + 1)) K)
    (hP₁ : (P₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) K) =
      if pol₁ then (revBlocks K (m₁ + 1) d₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) K) else 1)
    (hP₂ : (P₂ : Matrix (Fin (m₂ + 1)) (Fin (m₂ + 1)) K) =
      if pol₂ then (revBlocks K (m₂ + 1) d₂ : Matrix (Fin (m₂ + 1)) (Fin (m₂ + 1)) K) else 1)
    (hP₃ : (P₃ : Matrix (Fin (m₃ + 1)) (Fin (m₃ + 1)) K) =
      if pol₃ then (revBlocks K (m₃ + 1) d₃ : Matrix (Fin (m₃ + 1)) (Fin (m₃ + 1)) K) else 1)
    (hψ : ∀ A₁ ∈ blockSL K m₁ d₁, ∀ A₂ ∈ blockSL K m₂ d₂, ∀ A₃ ∈ blockSL K m₃ d₃, ∀ c ∈ S,
      Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL A₁) (stdFlag K (m₁ + 1)),
        flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K (m₂ + 1))),
          flagAct (SpecialLinearGroup.toGL A₃) (stdFlag K (m₃ + 1))) →
        Θ₀.Φ (ψ c) =
          ((flagAct N₁ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol₁ P₁ A₁))
              (stdFlag K (m₁ + 1))),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol₂ P₂ A₂))
              (stdFlag K (m₂ + 1)))),
            flagAct N₃ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) pol₃ P₃ A₃))
              (stdFlag K (m₃ + 1)))))
    (pl₁ pl₂ pl₃ : List Bool)
    (hpl₁ : ∀ b, b + 1 < d₁.length → 2 ≤ blockSize d₁ b → pl₁.getD b false = pol₁)
    (hpl₂ : ∀ b, b + 1 < d₂.length → 2 ≤ blockSize d₂ b → pl₂.getD b false = pol₂)
    (hpl₃ : ∀ b, b + 1 < d₃.length → 2 ≤ blockSize d₃ b → pl₃.getD b false = pol₃) :
    ∃ Θ : ChamberIso X (((flagSys K m₁).prod (flagSys K m₂)).prod (flagSys K m₃)),
      (∀ c, c ∈ S ↔ Θ.Φ c ∈
        (refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂) ×ˢ refSet K (m₃ + 1) d₃) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = Prod.map (Prod.map (flagPsi' K f hK (m₁ + 1) d₁ pl₁)
        (flagPsi' K f hK (m₂ + 1) d₂ pl₂)) (flagPsi' K f hK (m₃ + 1) d₃ pl₃) (Θ.Φ c) := by
  have hkey : ∀ c ∈ S, Θ₀.Φ (ψ c) =
      ((flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
          (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) (Θ₀.Φ c).1.1),
        flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
          (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) (Θ₀.Φ c).1.2)),
        flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
          (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃) (Θ₀.Φ c).2)) := by
    intro c hc
    have hy := (hS c).mp hc
    obtain ⟨hy₁₂, hy₃⟩ := Set.mem_prod.mp hy
    obtain ⟨hy₁, hy₂⟩ := Set.mem_prod.mp hy₁₂
    obtain ⟨A₁, hA₁, hA₁x⟩ := exists_blockSL_of_mem_refSet hd₁ hy₁
    obtain ⟨A₂, hA₂, hA₂x⟩ := exists_blockSL_of_mem_refSet hd₂ hy₂
    obtain ⟨A₃, hA₃, hA₃x⟩ := exists_blockSL_of_mem_refSet hd₃ hy₃
    have hpair : Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL A₁) (stdFlag K (m₁ + 1)),
        flagAct (SpecialLinearGroup.toGL A₂) (stdFlag K (m₂ + 1))),
          flagAct (SpecialLinearGroup.toGL A₃) (stdFlag K (m₃ + 1))) :=
      Prod.ext (Prod.ext hA₁x hA₂x) hA₃x
    have hψc := hψ A₁ hA₁ A₂ hA₂ A₃ hA₃ c hc hpair
    rw [hψc, hA₁x, hA₂x, hA₃x]
    exact Prod.ext (Prod.ext (flagAct_kapMat_stdFlag hK hd₁ N₁ pol₁ P₁ hP₁ hA₁)
      (flagAct_kapMat_stdFlag hK hd₂ N₂ pol₂ P₂ hP₂ hA₂))
      (flagAct_kapMat_stdFlag hK hd₃ N₃ pol₃ P₃ hP₃ hA₃)
  have hinv_pair : ∀ p ∈ (refSet K (m₁ + 1) d₁ ×ˢ refSet K (m₂ + 1) d₂) ×ˢ
      refSet K (m₃ + 1) d₃,
      ((flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
          (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁)
            (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
              (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) p.1.1))),
        flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
          (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂)
            (flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
              (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) p.1.2)))),
        flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
          (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃)
            (flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
              (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃) p.2)))) = p := by
    intro p hp
    let c : C := Θ₀.Φ.symm p
    have hcΦ : Θ₀.Φ c = p := Θ₀.Φ.apply_symm_apply p
    have hcS : c ∈ S := (hS c).mpr (by rw [hcΦ]; exact hp)
    have h1 := hkey c hcS
    have h2 := hkey (ψ c) (hψS c hcS)
    rw [hψψ c hcS, h1, hcΦ] at h2
    exact h2.symm
  have hinv₁ : ∀ x ∈ refSet K (m₁ + 1) d₁,
      flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
        (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁)
          (flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
            (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) x))) = x := by
    intro x hx
    have h := hinv_pair ((x, stdFlag K (m₂ + 1)), stdFlag K (m₃ + 1))
      (Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨hx, stdFlag_mem_refSet hd₂⟩,
        stdFlag_mem_refSet hd₃⟩)
    exact congrArg (fun p => p.1.1) h
  have hinv₂ : ∀ x ∈ refSet K (m₂ + 1) d₂,
      flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
        (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂)
          (flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
            (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) x))) = x := by
    intro x hx
    have h := hinv_pair ((stdFlag K (m₁ + 1), x), stdFlag K (m₃ + 1))
      (Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨stdFlag_mem_refSet hd₁, hx⟩,
        stdFlag_mem_refSet hd₃⟩)
    exact congrArg (fun p => p.1.2) h
  have hinv₃ : ∀ x ∈ refSet K (m₃ + 1) d₃,
      flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
        (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃)
          (flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
            (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃) x))) = x := by
    intro x hx
    have h := hinv_pair ((stdFlag K (m₁ + 1), stdFlag K (m₂ + 1)), x)
      (Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨stdFlag_mem_refSet hd₁,
        stdFlag_mem_refSet hd₂⟩, hx⟩)
    exact congrArg Prod.snd h
  obtain ⟨e₁, he₁, heq₁⟩ := exists_normalForm_flagPsi hK hd₁
    (List.replicate (d₁.length - 1) pol₁) (stabV_pathMat hd₁ hN₁ pol₁) hinv₁
  obtain ⟨e₂, he₂, heq₂⟩ := exists_normalForm_flagPsi hK hd₂
    (List.replicate (d₂.length - 1) pol₂) (stabV_pathMat hd₂ hN₂ pol₂) hinv₂
  obtain ⟨e₃, he₃, heq₃⟩ := exists_normalForm_flagPsi hK hd₃
    (List.replicate (d₃.length - 1) pol₃) (stabV_pathMat hd₃ hN₃ pol₃) hinv₃
  let Θ : ChamberIso X (((flagSys K m₁).prod (flagSys K m₂)).prod (flagSys K m₃)) :=
    Θ₀.trans (((flagMapIso (glLin e₁)).prodCongr (flagMapIso (glLin e₂))).prodCongr
      (flagMapIso (glLin e₃)))
  have hΘ : ∀ c, Θ.Φ c =
      ((flagAct e₁ (Θ₀.Φ c).1.1, flagAct e₂ (Θ₀.Φ c).1.2), flagAct e₃ (Θ₀.Φ c).2) :=
    fun _ => rfl
  refine ⟨Θ, ?_, ?_⟩
  · intro c
    rw [hS c, hΘ c]
    simp only [Set.mem_prod]
    exact and_congr (and_congr (pls2p_mem_refSet_flagAct_iff he₁ _).symm
      (pls2p_mem_refSet_flagAct_iff he₂ _).symm)
      (pls2p_mem_refSet_flagAct_iff he₃ _).symm
  · intro c hc
    have hy := (hS c).mp hc
    obtain ⟨hy₁₂, hy₃⟩ := Set.mem_prod.mp hy
    obtain ⟨hy₁, hy₂⟩ := Set.mem_prod.mp hy₁₂
    have h1 := hkey c hc
    have hc1 : (Θ₀.Φ (ψ c)).1.1 = flagAct (pathMat K (m₁ + 1) d₁ N₁ pol₁)
        (flagPsi hK hd₁ (List.replicate (d₁.length - 1) pol₁) (Θ₀.Φ c).1.1) := by rw [h1]
    have hc2 : (Θ₀.Φ (ψ c)).1.2 = flagAct (pathMat K (m₂ + 1) d₂ N₂ pol₂)
        (flagPsi hK hd₂ (List.replicate (d₂.length - 1) pol₂) (Θ₀.Φ c).1.2) := by rw [h1]
    have hc3 : (Θ₀.Φ (ψ c)).2 = flagAct (pathMat K (m₃ + 1) d₃ N₃ pol₃)
        (flagPsi hK hd₃ (List.replicate (d₃.length - 1) pol₃) (Θ₀.Φ c).2) := by rw [h1]
    rw [hΘ (ψ c), hc1, hc2, hc3, hΘ c]
    simp only [Prod.map_apply']
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · have hxmem : flagAct e₁ (Θ₀.Φ c).1.1 ∈ refSet K (m₁ + 1) d₁ :=
        (pls2p_mem_refSet_flagAct_iff he₁ _).mpr hy₁
      have hn := heq₁ (flagAct e₁ (Θ₀.Φ c).1.1) hxmem
      rw [flagAct_inv_flagAct] at hn
      rw [pls2p_flagPsi'_eq hK hd₁ pol₁ pl₁ hpl₁ hxmem]
      exact hn
    · have hxmem : flagAct e₂ (Θ₀.Φ c).1.2 ∈ refSet K (m₂ + 1) d₂ :=
        (pls2p_mem_refSet_flagAct_iff he₂ _).mpr hy₂
      have hn := heq₂ (flagAct e₂ (Θ₀.Φ c).1.2) hxmem
      rw [flagAct_inv_flagAct] at hn
      rw [pls2p_flagPsi'_eq hK hd₂ pol₂ pl₂ hpl₂ hxmem]
      exact hn
    · have hxmem : flagAct e₃ (Θ₀.Φ c).2 ∈ refSet K (m₃ + 1) d₃ :=
        (pls2p_mem_refSet_flagAct_iff he₃ _).mpr hy₃
      have hn := heq₃ (flagAct e₃ (Θ₀.Φ c).2) hxmem
      rw [flagAct_inv_flagAct] at hn
      rw [pls2p_flagPsi'_eq hK hd₃ pol₃ pl₃ hpl₃ hxmem]
      exact hn

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
