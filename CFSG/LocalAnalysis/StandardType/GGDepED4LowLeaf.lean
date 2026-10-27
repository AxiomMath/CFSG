module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowLeafClose
public import CFSG.LocalAnalysis.StandardType.GGPZE6Input

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4Low_leaf (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G] {p k : ℕ}
    [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp3 : p = 3) {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {X : Subgroup G}
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hXΛ : LargeEvenInLambda2 labX) (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hCard : Nat.card ↥Bs = 3 ^ 6)
    (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank) (hRG : GGReflGenerated p (ggAutomizer J Bs))
    (hcells : GGDepED4LowCells)
    (hcfg : (X = L ∧ GGDepED4LowCfg p k Bs L J K x y) ∨
      (X = K ∧ GGDepED4LowCfg p k Bs K J L y x)) : False := by
  classical
  subst hp3
  have hDcl : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hDea : IsElemAbelian 3 D := hH.1.2.2.1.2.1
  have hDcard : Nat.card D = 3 ^ 2 := hH.1.2.2.1.2.2.1
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hy_not_zx : y ∉ Subgroup.zpowers x := by
    intro hy
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_zpowers x
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact hy
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ 3 := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : Nat.Prime 3).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 x hxD))
    have : 3 ^ 2 ≤ 3 := by simpa [hDcard] using h1
    nlinarith [(Fact.out : Nat.Prime 3).two_le]
  have hx_not_zy : x ∉ Subgroup.zpowers y := by
    intro hx
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers y := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact hx
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact Subgroup.mem_zpowers y
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ 3 := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : Nat.Prime 3).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 y hyD))
    have : 3 ^ 2 ≤ 3 := by simpa [hDcard] using h1
    nlinarith [(Fact.out : Nat.Prime 3).two_le]
  have hx_ne1 : x ≠ 1 := by
    intro hx1
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers y := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz, hx1]; exact Subgroup.one_mem _
        · simp only [Set.mem_singleton_iff] at hz; rw [hz]; exact Subgroup.mem_zpowers y
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ 3 := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : Nat.Prime 3).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 y hyD))
    have : 3 ^ 2 ≤ 3 := by simpa [hDcard] using h1
    nlinarith [(Fact.out : Nat.Prime 3).two_le]
  have hy_ne1 : y ≠ 1 := by
    intro hy1
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_zpowers x
        · simp only [Set.mem_singleton_iff] at hz; rw [hz, hy1]; exact Subgroup.one_mem _
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ 3 := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : Nat.Prime 3).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 x hxD))
    have : 3 ^ 2 ≤ 3 := by simpa [hDcard] using h1
    nlinarith [(Fact.out : Nat.Prime 3).two_le]
  have hxord : orderOf x = 3 := orderOf_eq_prime (hDea.2 x hxD) hx_ne1
  have hyord : orderOf y = 3 := orderOf_eq_prime (hDea.2 y hyD) hy_ne1
  have hpow_x : ∀ c : ZMod 3, c ≠ 0 → x ^ c.val ∉ Subgroup.zpowers y :=
    ggTWLowLeaf_pow_not_zpowers hy_not_zx hxord hyord
  have hpow_y : ∀ c : ZMod 3, c ≠ 0 → y ^ c.val ∉ Subgroup.zpowers x :=
    ggTWLowLeaf_pow_not_zpowers hx_not_zy hyord hxord
  have hzDxy : ∀ c : ZMod 3, x * y ^ c.val ∈ D := by
    intro c; rw [hDcl]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hzDyx : ∀ c : ZMod 3, y * x ^ c.val ∈ D := by
    intro c; rw [hDcl]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hzx_xy : ∀ c : ZMod 3, c ≠ 0 → x * y ^ c.val ∉ Subgroup.zpowers x := by
    intro c hc hmem
    apply hpow_y c hc
    have h : x⁻¹ * (x * y ^ c.val) ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) hmem
    simpa [mul_assoc] using h
  have hzy_xy : ∀ c : ZMod 3, c ≠ 0 → x * y ^ c.val ∉ Subgroup.zpowers y := by
    intro c hc hmem
    apply hx_not_zy
    have h : (x * y ^ c.val) * (y ^ c.val)⁻¹ ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ hmem (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
    simpa [mul_assoc] using h
  have hzx_yx : ∀ c : ZMod 3, c ≠ 0 → y * x ^ c.val ∉ Subgroup.zpowers x := by
    intro c hc hmem
    apply hy_not_zx
    have h : (y * x ^ c.val) * (x ^ c.val)⁻¹ ∈ Subgroup.zpowers x :=
      Subgroup.mul_mem _ hmem (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
    simpa [mul_assoc] using h
  have hzy_yx : ∀ c : ZMod 3, c ≠ 0 → y * x ^ c.val ∉ Subgroup.zpowers y := by
    intro c hc hmem
    apply hpow_x c hc
    have h : y⁻¹ * (y * x ^ c.val) ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) hmem
    simpa [mul_assoc] using h
  rcases hcfg with ⟨hXL, hcfg⟩ | ⟨hXK, hcfg⟩
  · obtain ⟨Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α,
      xV, yV, hx, hy, hxV, hyV, hcore, hdim, hHL, hyVne, hyJ, hya, hHK⟩ := hcfg
    letI := iΛ1; letI := iΛ2; letI := iΛa1; letI := iΛa2; letI := iV1; letI := iV2
    obtain ⟨hb1, hb2, hcardk, hWMK, hCK, hk2, hφlin, hF, hpairK, hnt, hxa, hgenA, hgenJ⟩ := hcore
    let r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V := fun o => ggLin (p := 3) ι (φ o)
    have hr : ∀ o w, r o w = w - α o w • h o := fun o w => hφlin o w
    have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure (Set.range r) := by
      have hrg : Set.range r = (ggLin (p := 3) ι) '' Set.range φ := by
        ext u; constructor
        · rintro ⟨o, rfl⟩; exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
      rw [hgenA, MonoidHom.map_closure, ← hrg]
    have hAJ : (ggAutomizer J Bs).map (ggLin (p := 3) ι) = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) := by
      have hrgJ : Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) =
          (ggLin (p := 3) ι) '' Set.range
            (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) := by
        ext u; constructor
        · rintro ⟨j, rfl⟩; exact ⟨φ (Sum.inl j.1), ⟨j, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
      rw [hgenJ, MonoidHom.map_closure, ← hrgJ]
    rcases hk with rfl | rfl
    · have hres := ggDepELLeaf_close_one hPZ hb1 hb2 hcardk hWMK hCK hr hF hdim hpairK hnt
        (hHL rfl) hxa hyVne hyJ hya (hHK rfl) hH (Or.inl hXL) hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG ι hA
        hAJ ⟨x, hx⟩ ⟨y, hy⟩ hxV hyV hzDxy hzx_xy hzy_xy
      exact hcells.1 hres
    · have hres := ggDepELLeaf_close_two hPZ hb1 hb2 hcardk hWMK hCK (hk2 rfl) hr hF hdim hpairK
        hnt hxa hyVne hyJ hya hH (Or.inl hXL) hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG
        ι hA hAJ ⟨x, hx⟩ ⟨y, hy⟩ hxV hyV hzDxy hzx_xy hzy_xy
      exact hcells.2 hres
  · obtain ⟨Λ, iΛ1, iΛ2, b₁, b₂, Λa, iΛa1, iΛa2, MK, CK, V, iV1, iV2, ι, e, φ, h, α,
      xV, yV, hy, hx, hyV, hxV, hcore, hdim, hHL, hyVne, hyJ, hya, hHK⟩ := hcfg
    letI := iΛ1; letI := iΛ2; letI := iΛa1; letI := iΛa2; letI := iV1; letI := iV2
    obtain ⟨hb1, hb2, hcardk, hWMK, hCK, hk2, hφlin, hF, hpairK, hnt, hxa, hgenA, hgenJ⟩ := hcore
    let r : Λ ⊕ Λa → V ≃ₗ[ZMod 3] V := fun o => ggLin (p := 3) ι (φ o)
    have hr : ∀ o w, r o w = w - α o w • h o := fun o w => hφlin o w
    have hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure (Set.range r) := by
      have hrg : Set.range r = (ggLin (p := 3) ι) '' Set.range φ := by
        ext u; constructor
        · rintro ⟨o, rfl⟩; exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
      rw [sup_comm (ggAutomizer L Bs) (ggAutomizer K Bs), hgenA, MonoidHom.map_closure, ← hrg]
    have hAJ : (ggAutomizer J Bs).map (ggLin (p := 3) ι) = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) := by
      have hrgJ : Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => r (Sum.inl j.1)) =
          (ggLin (p := 3) ι) '' Set.range
            (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) := by
        ext u; constructor
        · rintro ⟨j, rfl⟩; exact ⟨φ (Sum.inl j.1), ⟨j, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
      rw [hgenJ, MonoidHom.map_closure, ← hrgJ]
    rcases hk with rfl | rfl
    · have hres := ggDepELLeaf_close_one hPZ hb1 hb2 hcardk hWMK hCK hr hF hdim hpairK hnt
        (hHL rfl) hxa hyVne hyJ hya (hHK rfl) hH (Or.inr hXK) hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG ι hA
        hAJ ⟨y, hy⟩ ⟨x, hx⟩ hyV hxV hzDyx hzx_yx hzy_yx
      exact hcells.1 hres
    · have hres := ggDepELLeaf_close_two hPZ hb1 hb2 hcardk hWMK hCK (hk2 rfl) hr hF hdim hpairK
        hnt hxa hyVne hyJ hya hH (Or.inr hXK) hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG
        ι hA hAJ ⟨y, hy⟩ ⟨x, hx⟩ hyV hxV hzDyx hzx_yx hzy_yx
      exact hcells.2 hres

end CFSG.StandardType

end
