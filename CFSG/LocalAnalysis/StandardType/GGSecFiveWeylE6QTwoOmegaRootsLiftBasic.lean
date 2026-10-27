module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRoots

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem ne_smul_of_not_mem_zpowers (ι : Additive ↥Bs ≃+ V) {x y : ↥Bs}
    (hy : y ∉ Subgroup.zpowers x) (a : ZMod 3) :
    ι (Additive.ofMul y) ≠ a • ι (Additive.ofMul x) := by
  intro h
  apply hy
  have h' : ι (Additive.ofMul y) = ι (Additive.ofMul (x ^ a.val)) := by
    calc ι (Additive.ofMul y) = a • ι (Additive.ofMul x) := h
      _ = (a.val : ZMod 3) • ι (Additive.ofMul x) := by rw [ZMod.natCast_zmod_val]
      _ = a.val • ι (Additive.ofMul x) := by rw [Nat.cast_smul_eq_nsmul]
      _ = ι (Additive.ofMul (x ^ a.val)) := by rw [ofMul_pow, map_nsmul]
  have hy' : y = x ^ a.val := Additive.ofMul.injective (ι.injective h')
  rw [hy']
  exact Subgroup.npow_mem_zpowers x a.val

theorem mem_zpowers_of_eq_smul (ι : Additive ↥Bs ≃+ V) {b y : ↥Bs} {a : ZMod 3}
    (hb : ι (Additive.ofMul b) = a • ι (Additive.ofMul y)) : b ∈ Subgroup.zpowers y := by
  have h' : ι (Additive.ofMul b) = ι (Additive.ofMul (y ^ a.val)) := by
    calc ι (Additive.ofMul b) = a • ι (Additive.ofMul y) := hb
      _ = (a.val : ZMod 3) • ι (Additive.ofMul y) := by rw [ZMod.natCast_zmod_val]
      _ = a.val • ι (Additive.ofMul y) := by rw [Nat.cast_smul_eq_nsmul]
      _ = ι (Additive.ofMul (y ^ a.val)) := by rw [ofMul_pow, map_nsmul]
  have hb' : b = y ^ a.val := Additive.ofMul.injective (ι.injective h')
  rw [hb']
  exact Subgroup.npow_mem_zpowers y a.val

theorem exists_eq_smul_add_smul (hBs : IsElemAbelian 3 Bs) (ι : Additive ↥Bs ≃+ V)
    {D : Subgroup G} (hDBs : D ≤ Bs) (hD : Nat.card D = 9) {x y z : ↥Bs} (hxD : (x : G) ∈ D)
    (hyD : (y : G) ∈ D) (hzD : (z : G) ∈ D) (hx : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ a b : ZMod 3,
      ι (Additive.ofMul z) = a • ι (Additive.ofMul x) + b • ι (Additive.ofMul y) := by
  classical
  have hX0 : ι (Additive.ofMul x) ≠ 0 := by
    intro h
    apply hx
    have h1 : ι (Additive.ofMul x) = ι 0 := by rwa [map_zero]
    exact Additive.ofMul.injective (ι.injective h1)
  have hYnot : ι (Additive.ofMul y) ∉ Submodule.span (ZMod 3) {ι (Additive.ofMul x)} := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact hyx (mem_zpowers_of_eq_smul ι (b := y) (y := x) (a := a) ha.symm)
  have hind : LinearIndependent (ZMod 3) ![ι (Additive.ofMul x), ι (Additive.ofMul y)] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at h
      rcases smul_eq_zero.mp h with h0 | h0
      · exact ⟨h0, rfl⟩
      · exact absurd h0 hX0
    · exfalso
      have hbY : b • ι (Additive.ofMul y) = -(a • ι (Additive.ofMul x)) := by
        have h' := h
        rw [add_comm] at h'
        exact eq_neg_of_add_eq_zero_left h' 
      have hY' : ι (Additive.ofMul y) = (b⁻¹ * -a) • ι (Additive.ofMul x) := by
        calc ι (Additive.ofMul y) = b⁻¹ • (b • ι (Additive.ofMul y)) := by
              rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = b⁻¹ • (-(a • ι (Additive.ofMul x))) := by rw [hbY]
          _ = (b⁻¹ * -a) • ι (Additive.ofMul x) := by
              rw [← neg_smul, smul_smul]
              rfl
      exact hYnot (Submodule.mem_span_singleton.mpr ⟨b⁻¹ * -a, hY'.symm⟩)
  let P : Submodule (ZMod 3) V := ggLinImage (p := 3) ι D
  have hPcard : Nat.card ↥P = 9 := by
    rw [show Nat.card ↥P = Nat.card ↥(ggLinImage (p := 3) ι D) from rfl,
      card_ggLinImage, inf_eq_right.mpr hDBs, hD]
  have hPfin : finrank (ZMod 3) ↥P = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ↥P)
    rw [Nat.card_zmod, hPcard] at h
    exact (Nat.pow_right_injective (a := 3) (by norm_num)
      ((show (9 : ℕ) = 3 ^ 2 by norm_num).symm.trans h)).symm
  have hXmem : ι (Additive.ofMul x) ∈ P := (ofMul_mem_ggLinImage ι D x).mpr hxD
  have hYmem : ι (Additive.ofMul y) ∈ P := (ofMul_mem_ggLinImage ι D y).mpr hyD
  have hZmem : ι (Additive.ofMul z) ∈ P := (ofMul_mem_ggLinImage ι D z).mpr hzD
  have hspanle : Submodule.span (ZMod 3) {ι (Additive.ofMul x), ι (Additive.ofMul y)} ≤ P := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with rfl | rfl
    · exact hXmem
    · exact hYmem
  have hrange : Set.range ![ι (Additive.ofMul x), ι (Additive.ofMul y)] =
      {ι (Additive.ofMul x), ι (Additive.ofMul y)} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    tauto
  have hspanfin : finrank (ZMod 3)
      ↥(Submodule.span (ZMod 3) {ι (Additive.ofMul x), ι (Additive.ofMul y)}) = 2 := by
    have h := finrank_span_eq_card hind
    rw [hrange] at h
    simpa using h
  have hspan_eq : Submodule.span (ZMod 3) {ι (Additive.ofMul x), ι (Additive.ofMul y)} = P :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by rw [hspanfin, hPfin])
  rw [← hspan_eq] at hZmem
  rw [Submodule.mem_span_pair] at hZmem
  obtain ⟨a, b, hab⟩ := hZmem
  exact ⟨a, b, hab.symm⟩

theorem six_le_ncard_rootRefl_of_six_le
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (ι : Additive ↥Bs ≃+ V) {A K : Subgroup (MulAut ↥Bs)}
    (hmap : A.map (ggLin (p := 3) ι) = e6Weyl hα) (hKA : K ≤ A) {x y : ↥Bs}
    {R : Set (MulAut ↥Bs)} (hR : ∀ r ∈ R, r ∈ K ∧ GGIsReflection 3 r ∧ r x = x ∧ r y = y)
    (h6 : 6 ≤ Set.ncard R) :
    6 ≤ Set.ncard {r : V ≃ₗ[ZMod 3] V | r ∈ K.map (ggLin (p := 3) ι) ∧ ∃ v : V,
      ∃ hv : B v v = 2, B v (ι (Additive.ofMul x)) = 0 ∧ B v (ι (Additive.ofMul y)) = 0 ∧
        r = rootRefl (B := B) v hv} := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective ((↑) : (V ≃ₗ[ZMod 3] V) → V → V) DFunLike.coe_injective
  let T : Set (V ≃ₗ[ZMod 3] V) := {r : V ≃ₗ[ZMod 3] V | r ∈ K.map (ggLin (p := 3) ι) ∧
    ∃ v : V, ∃ hv : B v v = 2, B v (ι (Additive.ofMul x)) = 0 ∧
      B v (ι (Additive.ofMul y)) = 0 ∧ r = rootRefl (B := B) v hv}
  have hmaps : ∀ r ∈ R, ggLin (p := 3) ι r ∈ T := by
    intro r hr
    obtain ⟨hrK, hrRefl, hrx, hry⟩ := hR r hr
    have hrmem : ggLin (p := 3) ι r ∈ e6Weyl hα := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ (hKA hrK)
    obtain ⟨v, hv, hveq⟩ := exists_root_of_ggIsReflection hP hV hB hα ι hrRefl hrmem
    have hx0 : B v (ι (Additive.ofMul x)) = 0 := by
      have hfix : rootRefl (B := B) v hv (ι (Additive.ofMul x)) = ι (Additive.ofMul x) := by
        rw [← hveq, ggLin_apply_ofMul, hrx]
      exact (rootRefl_fix_iff hv _).mp hfix
    have hy0 : B v (ι (Additive.ofMul y)) = 0 := by
      have hfix : rootRefl (B := B) v hv (ι (Additive.ofMul y)) = ι (Additive.ofMul y) := by
        rw [← hveq, ggLin_apply_ofMul, hry]
      exact (rootRefl_fix_iff hv _).mp hfix
    exact ⟨Subgroup.mem_map_of_mem _ hrK, v, hv, hx0, hy0, hveq⟩
  have hle := Set.ncard_le_ncard_of_injOn (ggLin (p := 3) ι) hmaps
    (fun a _ b _ hab => ggLin_injective (p := 3) ι hab) (Set.toFinite T)
  exact h6.trans hle

theorem dich_map (hα : ∀ i, α i (h i) = 2) (ι : Additive ↥Bs ≃+ V)
    {A K : Subgroup (MulAut ↥Bs)} (hmap : A.map (ggLin (p := 3) ι) = e6Weyl hα) {y : ↥Bs}
    (hN : ∀ ψ ∈ A, ψ y = y → (∀ a ∈ K, ψ * a * ψ⁻¹ ∈ K) ∨
      ∀ a ∈ K, ∀ b ∈ K, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) :
    ∀ ψ ∈ e6Weyl hα, ψ (ι (Additive.ofMul y)) = ι (Additive.ofMul y) →
      (∀ a ∈ K.map (ggLin (p := 3) ι), ψ * a * ψ⁻¹ ∈ K.map (ggLin (p := 3) ι)) ∨
        ∀ a ∈ K.map (ggLin (p := 3) ι), ∀ b ∈ K.map (ggLin (p := 3) ι),
          a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a := by
  intro ψ hψ hfix
  rw [← hmap] at hψ
  obtain ⟨φ, hφA, rfl⟩ := Subgroup.mem_map.mp hψ
  have hφy : φ y = y := (ggLin_fix_iff ι φ y).mpr hfix
  rcases hN φ hφA hφy with hN1 | hN2
  · left
    intro a ha
    obtain ⟨a₀, ha₀K, rfl⟩ := Subgroup.mem_map.mp ha
    have h : φ * a₀ * φ⁻¹ ∈ K := hN1 a₀ ha₀K
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem (ggLin (p := 3) ι) h
  · right
    intro a ha b hb
    obtain ⟨a₀, ha₀K, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀K, rfl⟩ := Subgroup.mem_map.mp hb
    have h : a₀ * (φ * b₀ * φ⁻¹) = φ * b₀ * φ⁻¹ * a₀ := hN2 a₀ ha₀K b₀ hb₀K
    simpa only [map_mul, map_inv] using congrArg (ggLin (p := 3) ι) h

theorem map_le_closure_rootRefl_of_fix
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (ι : Additive ↥Bs ≃+ V) {A K : Subgroup (MulAut ↥Bs)}
    (hmap : A.map (ggLin (p := 3) ι) = e6Weyl hα) (hKA : K ≤ A) (hKr : GGReflGenerated 3 K)
    {x : ↥Bs} (hKx : ∀ φ ∈ K, φ x = x) :
    K.map (ggLin (p := 3) ι) ≤ Subgroup.closure {r : V ≃ₗ[ZMod 3] V | ∃ u : V,
      ∃ hu : B u u = 2, B u (ι (Additive.ofMul x)) = 0 ∧ r = rootRefl (B := B) u hu} := by
  have hgen : ∀ φ ∈ K, ggLin (p := 3) ι φ ∈ e6Weyl hα := by
    intro φ hφ
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (hKA hφ)
  rw [GGReflGenerated] at hKr
  rw [hKr, MonoidHom.map_closure, Subgroup.closure_le]
  rintro r ⟨φ, ⟨hφK, hφr⟩, rfl⟩
  obtain ⟨v, hv, hveq⟩ := exists_root_of_ggIsReflection hP hV hB hα ι hφr (hgen φ hφK)
  have hx0 : B v (ι (Additive.ofMul x)) = 0 := by
    have hfix : rootRefl (B := B) v hv (ι (Additive.ofMul x)) = ι (Additive.ofMul x) := by
      rw [← hveq, ggLin_apply_ofMul, hKx φ hφK]
    exact (rootRefl_fix_iff hv _).mp hfix
  exact Subgroup.subset_closure ⟨v, hv, hx0, hveq⟩

end CFSG.StandardType.E6QTwo

end
