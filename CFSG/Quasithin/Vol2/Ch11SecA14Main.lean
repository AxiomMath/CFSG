module

public import CFSG.Quasithin.Vol2.Ch11SecA14
public import CFSG.Quasithin.Vol2.Ch11SecA14Gen
public import CFSG.Quasithin.Vol2.Ch11SecAVi2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_normalizer_L_of_perm (h1113 : Stmt11_1_3) (hD : FactDeltaSp4) (hD' : FactDeltaG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n)
    {U₁ U₂ U₃ : Subgroup G} (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂)
    (hU₃ : IsVi T L I n 3 U₃) {g : G}
    (hg : ∀ x ∈ LOf L U₁, ∃ y ∈ LOf L U₁, (U₂.map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = U₂.map (MulAut.conj y).toMonoidHom) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [← iSup_lOf_eq hD hD' h1102 h hk hU₁ hU₂ hU₃]
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun x hx => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨y, hy, hxy⟩ := hg x hx
  obtain ⟨hc1, hc2, -⟩ := stmt11_1_3_conj h1113 h hU₂ (lOf_le L U₁ hx)
  obtain ⟨-, -, hc3⟩ := stmt11_1_3_conj h1113 h hU₂ (lOf_le L U₁ hy)
  have hK := isCComponent_map_equiv (MulAut.conj g) hc1
  rw [map_conj_normalizer, hxy] at hK
  have hKC : ¬ (LOf L (U₂.map (MulAut.conj x).toMonoidHom)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((U₂.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
    rw [← hxy, ← map_conj_centralizer]
    intro hle
    exact hc2 ((Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle)
  rw [hc3 _ hK hKC]
  exact le_iSup₂_of_le y hy le_rfl

theorem exists_conj_of_mem_normalizer (hF : NatFacts) (hD : FactDeltaSp4) (hD' : FactDeltaG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n)
    {U₁ U₂ U₃ : Subgroup G} (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂)
    (hU₃ : IsVi T L I n 3 U₃) (hL13 : LOf L U₁ ≤ Subgroup.normalizer (U₃ : Set G)) {g : G}
    (hg1 : g ∈ Subgroup.normalizer (U₁ : Set G)) (hg3 : g ∈ Subgroup.normalizer (U₃ : Set G))
    (hgL : g ∈ Subgroup.normalizer (LOf L U₁ : Set G)) :
    ∃ y ∈ LOf L U₁, U₂.map (MulAut.conj g).toMonoidHom = U₂.map (MulAut.conj y).toMonoidHom := by
  have h12 := IsVi.mono₁₂ hF h1102 h hU₁ hU₂
  have h23 := IsVi.mono₂₃ hF h1102 h hU₂ hU₃
  have hS := isSylowTwoOf_inf_lOf (U := U₁) h (IsVi.le_normalizer hU₁)
  set R := (T ⊓ LOf L U₁).map (MulAut.conj g).toMonoidHom
  have hR : QuasithinUnique.IsSylowTwoOf R (LOf L U₁) := by
    refine ⟨?_, hS.2.1.map _, ?_⟩
    · rw [← map_conj_eq_of_mem_normalizer hgL]
      exact Subgroup.map_mono hS.1
    · have := hS.2.2
      rwa [← Subgroup.relIndex, ← Subgroup.relIndex_map_map_of_injective
        (f := (MulAut.conj g).toMonoidHom) _ _ (MulAut.conj g).injective,
        map_conj_eq_of_mem_normalizer hgL] at this
  obtain ⟨y, hy, hyR⟩ := A4.exists_conj_of_isSylowTwoOf hS hR
  have hyN : y ∈ Subgroup.normalizer (LOf L U₁ : Set G) := Subgroup.le_normalizer hy
  have hy1 : y⁻¹ ∈ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.inv_mem _ ((iInf_le (derivedSeriesOf _) 0).trans inf_le_right hy)
  have hy3 : y⁻¹ ∈ Subgroup.normalizer (U₃ : Set G) := Subgroup.inv_mem _ (hL13 hy)
  set U := U₂.map (MulAut.conj (y⁻¹ * g)).toMonoidHom
  have hU1 : U₁ ≤ U := by
    rw [← map_conj_eq_of_mem_normalizer (Subgroup.mul_mem _ hy1 hg1)]
    exact Subgroup.map_mono h12
  have hU3 : U ≤ U₃ := by
    rw [← map_conj_eq_of_mem_normalizer (Subgroup.mul_mem _ hy3 hg3)]
    exact Subgroup.map_mono h23
  have hidx : U₁.relIndex U = 2 ^ n := by
    rw [← map_conj_eq_of_mem_normalizer (Subgroup.mul_mem _ hy1 hg1),
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (y⁻¹ * g)).toMonoidHom) _ _
        (MulAut.conj _).injective]
    have e1 := IsVi.relIndex_eq hU₁
    have e2 := IsVi.relIndex_eq hU₂
    have e3 := Subgroup.relIndex_mul_relIndex _ _ _ (IsVi.cV_le hU₁) h12
    rw [e1, e2, show n * 2 = n * 1 + n by ring, pow_add, mul_one] at e3
    exact Nat.eq_of_mul_eq_mul_left (by positivity) e3
  have hT : T ⊓ LOf L U₁ ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    rw [mem_normalizer_map_conj]
    have hR' : y * t * y⁻¹ ∈ R := (hyR _).mpr (by simpa [mul_assoc] using ht)
    rw [mem_map_conj] at hR'
    have hs : g⁻¹ * (y * t * y⁻¹) * g ∈ Subgroup.normalizer (U₂ : Set G) :=
      IsVi.le_normalizer hU₂ (Subgroup.mem_inf.mp hR').1
    convert hs using 1
    group
  have heq := eq_V₂_of_between hD hD' h1102 h hk hU₁ hU₂ hU₃ hU1 hU3 hidx hT
  refine ⟨y, hy, ?_⟩
  have e : U.map (MulAut.conj y).toMonoidHom = U₂.map (MulAut.conj g).toMonoidHom := by
    simp only [U]
    rw [map_conj_mul, show y * (y⁻¹ * g) = g by group]
  rw [← e, heq]

theorem stmt11_1_4_of (h331 : Stmt3_3_1) (hF : NatFacts) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3) (hD : FactDeltaSp4) (hD' : FactDeltaG2) :
    Stmt11_1_4 := by
  intro G _ _ T L I n V₁ V₃ h hV₁ hV₃
  by_cases hk : KindSL3 L (fsuV T I) n
  · have hV₃eq : V₃ = fsuV T I := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hk
    have hN := normalizer_fsuV_le h331 h
    rw [hV₃eq]
    exact ⟨fun g hg => hN hg.1, fun g hg => hN (Subgroup.mem_inf.mp hg).1⟩
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  have hN13 := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).2 hk
  have hL1M : LOf L V₁ ≤ Subgroup.normalizer (L : Set G) :=
    (lOf_le L V₁).trans Subgroup.le_normalizer
  have hL1N1 : LOf L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (iInf_le (derivedSeriesOf _) 0).trans inf_le_right
  have hL1N3 : LOf L V₁ ≤ Subgroup.normalizer (V₃ : Set G) := by
    intro x hx
    have : x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) :=
      Subgroup.mem_inf.mpr ⟨hL1M hx, hL1N1 hx⟩
    rw [← hN13] at this
    exact (Subgroup.mem_inf.mp this).2
  have h12 := IsVi.mono₁₂ hF h1102 h hV₁ hV₂
  have h23 := IsVi.mono₂₃ hF h1102 h hV₂ hV₃
  constructor
  ·
    intro g hg
    obtain ⟨hg3, -, hgc⟩ := hg
    refine mem_normalizer_L_of_perm h1113 hD hD' h1102 h hk hV₁ hV₂ hV₃ fun x hx => ⟨x, hx, ?_⟩
    apply map_conj_eq_of_mem_normalizer
    refine mem_normalizer_of_map_le ?_
    rintro _ ⟨u, hu, rfl⟩
    have hu3 : u ∈ V₃ := by
      rw [← map_conj_eq_of_mem_normalizer (hL1N3 hx)]
      exact Subgroup.map_mono h23 hu
    have h1 : V₁ ≤ V₂.map (MulAut.conj x).toMonoidHom := by
      rw [← map_conj_eq_of_mem_normalizer (hL1N1 hx)]
      exact Subgroup.map_mono h12
    have e : (MulAut.conj g).toMonoidHom u = (g * u * g⁻¹ * u⁻¹) * u := by
      simp [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (h1 (hgc u hu3)) hu
  ·
    intro g hg
    obtain ⟨hg3, hgL⟩ := Subgroup.mem_inf.mp hg
    have hpc : (pCoreOf 2 (LOf L V₁)).map (MulAut.conj g).toMonoidHom = pCoreOf 2 (LOf L V₁) := by
      have := Ch10.SecA.pCoreOf_conjugate (LOf L V₁) g⁻¹
      simp only [CFSG.conjugate, inv_inv] at this
      rw [← this, map_conj_eq_of_mem_normalizer hgL]
    have hO : g ∈ Subgroup.normalizer (pCoreOf 2 (LOf L V₁) : Set G) :=
      mem_normalizer_of_map_le (le_of_eq hpc)
    have hg1 : g ∈ Subgroup.normalizer (V₁ : Set G) := by
      refine mem_normalizer_of_map_le ?_
      rintro _ ⟨u, hu, rfl⟩
      have hu3 : u ∈ V₃ := h23 (h12 hu)
      have hgu3 : g * u * g⁻¹ ∈ V₃ := (Subgroup.mem_normalizer_iff.mp hg3 u).mp hu3
      have hfix := (centralizer_pCoreOf_lOf hD hD' h1102 h hk hV₁ hV₂ hV₃ hu3).mpr hu
      have : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := by simp
      rw [this, ← centralizer_pCoreOf_lOf hD hD' h1102 h hk hV₁ hV₂ hV₃ hgu3]
      intro z hz
      have hz' : g⁻¹ * z * g ∈ pCoreOf 2 (LOf L V₁) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hO) z).mp hz
        simpa using this
      have e := hfix _ hz'
      calc z * (g * u * g⁻¹) * z⁻¹ = g * ((g⁻¹ * z * g) * u * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by
            group
        _ = g * u * g⁻¹ := by rw [e]
    obtain ⟨y, hy, hgy⟩ :=
      exists_conj_of_mem_normalizer hF hD hD' h1102 h hk hV₁ hV₂ hV₃ hL1N3 hg1 hg3 hgL
    refine mem_normalizer_L_of_perm h1113 hD hD' h1102 h hk hV₁ hV₂ hV₃ fun x hx =>
      ⟨g * x * g⁻¹ * y, Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hgL x).mp hx) hy,
        ?_⟩
    rw [map_conj_mul, show g * x = (g * x * g⁻¹) * g by group, ← map_conj_mul, hgy,
      map_conj_mul]
    simp only [mul_inv_cancel_right]

end CFSG.Quasithin.Vol2.Ch11.SecA
