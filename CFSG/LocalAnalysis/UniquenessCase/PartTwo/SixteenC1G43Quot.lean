module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Dih
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G43_quot_aux {V W : Subgroup G} {g : G} {K L : Subgroup G}
    (hW : W = conjSubgroup V g) (hL : L = V ⊔ W) [(K.subgroupOf L).Normal]
    {v w : G} (hv : v ∈ V) (hw : w ∈ W) (hvK : v ∉ K) (hwK : w ∉ K)
    (hvsq : v * v = 1) (hwsq : w * w = 1)
    (hVcos : ∀ x ∈ V, x ∉ K → v⁻¹ * x ∈ K)
    (hWcos : ∀ x ∈ W, x ∉ K → w⁻¹ * x ∈ K)
    (hR : ∀ l ∈ V ⊔ W, ∀ l' ∈ V ⊔ W, ∀ ε ε' : G,
      (ε = 1 ∨ ε = g) → (ε' = 1 ∨ ε' = g) →
      ∀ a b : G, a ∈ conjSubgroup V (ε * l) → b ∈ conjSubgroup V (ε' * l') →
        a ∉ K → b ∉ K → ⁅a, b⁆ ∈ K →
          a⁻¹ * b ∈ K ∧ conjSubgroup V (ε * l) = conjSubgroup V (ε' * l')) :
    ∃ m : ℕ, Odd m ∧
      Nonempty ((↥L ⧸ K.subgroupOf L) ≃* DihedralGroup m) ∧
      CFSG.Open.twoRank (↥L ⧸ K.subgroupOf L) = 1 ∧
      ∃ l ∈ L, W = conjSubgroup V l := by
  have hVL : V ≤ L := by rw [hL]; exact le_sup_left
  have hWL : W ≤ L := by rw [hL]; exact le_sup_right
  let vL : ↥L := ⟨v, hVL hv⟩
  let wL : ↥L := ⟨w, hWL hw⟩
  let s : (↥L ⧸ K.subgroupOf L) := QuotientGroup.mk' (K.subgroupOf L) vL
  let t : (↥L ⧸ K.subgroupOf L) := QuotientGroup.mk' (K.subgroupOf L) wL
  have hmk1 : ∀ x : ↥L, QuotientGroup.mk' (K.subgroupOf L) x = 1 ↔ (x : G) ∈ K := by
    intro x
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmk2 : ∀ x y : ↥L, QuotientGroup.mk' (K.subgroupOf L) x =
      QuotientGroup.mk' (K.subgroupOf L) y ↔ (x : G)⁻¹ * (y : G) ∈ K := by
    intro x y
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
  have hvL2 : vL * vL = 1 := Subtype.ext hvsq
  have hwL2 : wL * wL = 1 := Subtype.ext hwsq
  have hssq : s * s = 1 := by
    show QuotientGroup.mk' (K.subgroupOf L) vL * QuotientGroup.mk' (K.subgroupOf L) vL = 1
    rw [← map_mul, hvL2, map_one]
  have httsq : t * t = 1 := by
    show QuotientGroup.mk' (K.subgroupOf L) wL * QuotientGroup.mk' (K.subgroupOf L) wL = 1
    rw [← map_mul, hwL2, map_one]
  have hs1 : s ≠ 1 := fun h => hvK ((hmk1 vL).1 h)
  have ht1 : t ≠ 1 := fun h => hwK ((hmk1 wL).1 h)
  have comm_mem : ∀ {x y : G}, x ∈ L → y ∈ L → ⁅x, y⁆ ∈ L := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
  have hgen : Subgroup.closure ({s, t} : Set (↥L ⧸ K.subgroupOf L)) = ⊤ := by
    let C : Subgroup (↥L ⧸ K.subgroupOf L) :=
      Subgroup.closure ({s, t} : Set (↥L ⧸ K.subgroupOf L))
    have hVH : V.subgroupOf L ≤ C.comap (QuotientGroup.mk' (K.subgroupOf L)) := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hxV : (x : G) ∈ V := Subgroup.mem_subgroupOf.1 hx
      by_cases hxK : (x : G) ∈ K
      · rw [(hmk1 x).2 hxK]
        exact C.one_mem
      · have hco : v⁻¹ * (x : G) ∈ K := hVcos (x : G) hxV hxK
        have h1 : QuotientGroup.mk' (K.subgroupOf L) (vL⁻¹ * x) = 1 :=
          (hmk1 _).2 (by simpa [vL] using hco)
        have h2 : QuotientGroup.mk' (K.subgroupOf L) (vL⁻¹ * x) =
            (QuotientGroup.mk' (K.subgroupOf L) vL)⁻¹ *
              QuotientGroup.mk' (K.subgroupOf L) x := by
          rw [map_mul, map_inv]
        have h3 : (QuotientGroup.mk' (K.subgroupOf L) vL)⁻¹ *
            QuotientGroup.mk' (K.subgroupOf L) x = 1 := by rw [← h2]; exact h1
        have hpx : QuotientGroup.mk' (K.subgroupOf L) x = s :=
          (inv_mul_eq_one.mp h3).symm
        rw [hpx]
        exact Subgroup.subset_closure (by simp)
    have hWH : W.subgroupOf L ≤ C.comap (QuotientGroup.mk' (K.subgroupOf L)) := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hxW : (x : G) ∈ W := Subgroup.mem_subgroupOf.1 hx
      by_cases hxK : (x : G) ∈ K
      · rw [(hmk1 x).2 hxK]
        exact C.one_mem
      · have hco : w⁻¹ * (x : G) ∈ K := hWcos (x : G) hxW hxK
        have h1 : QuotientGroup.mk' (K.subgroupOf L) (wL⁻¹ * x) = 1 :=
          (hmk1 _).2 (by simpa [wL] using hco)
        have h2 : QuotientGroup.mk' (K.subgroupOf L) (wL⁻¹ * x) =
            (QuotientGroup.mk' (K.subgroupOf L) wL)⁻¹ *
              QuotientGroup.mk' (K.subgroupOf L) x := by
          rw [map_mul, map_inv]
        have h3 : (QuotientGroup.mk' (K.subgroupOf L) wL)⁻¹ *
            QuotientGroup.mk' (K.subgroupOf L) x = 1 := by rw [← h2]; exact h1
        have hpx : QuotientGroup.mk' (K.subgroupOf L) x = t :=
          (inv_mul_eq_one.mp h3).symm
        rw [hpx]
        exact Subgroup.subset_closure (by simp)
    have hsup : V.subgroupOf L ⊔ W.subgroupOf L = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hVL hWL]
      rw [hL.symm]
      exact Subgroup.subgroupOf_self L
    have htop : C.comap (QuotientGroup.mk' (K.subgroupOf L)) = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le hVH hWH
    have hmap := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (K.subgroupOf L)) C
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective
      (K.subgroupOf L))] at hmap
    exact hmap.symm
  have lift : ∀ (x : ↥L ⧸ K.subgroupOf L), (IsConj s x ∨ IsConj t x) →
      ∃ (l : G) (hl : l ∈ L) (ε : G), (ε = 1 ∨ ε = g) ∧
        ∃ (a : G) (ha : a ∈ L), a ∈ conjSubgroup V (ε * l) ∧ a ∉ K ∧
          x = QuotientGroup.mk' (K.subgroupOf L) ⟨a, ha⟩ := by
    intro x hx
    have hxne_of : ∀ {u : ↥L ⧸ K.subgroupOf L}, IsConj s u → u ≠ 1 := by
      intro u hu h
      rw [h] at hu
      exact hs1 (isConj_one_left.mp hu)
    have hxne_of' : ∀ {u : ↥L ⧸ K.subgroupOf L}, IsConj t u → u ≠ 1 := by
      intro u hu h
      rw [h] at hu
      exact ht1 (isConj_one_left.mp hu)
    rcases hx with hx | hx
    · obtain ⟨c, hc⟩ := isConj_iff.1 hx
      obtain ⟨c', hc'⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) c
      have hxne : x ≠ 1 := hxne_of hx
      have haL : (c' : G) * v * (c' : G)⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem c'.2 (hVL hv)) (L.inv_mem c'.2)
      have hx_eq : x = QuotientGroup.mk' (K.subgroupOf L)
          ⟨(c' : G) * v * (c' : G)⁻¹, haL⟩ := by
        have h1 : QuotientGroup.mk' (K.subgroupOf L) (c' * vL * c'⁻¹) =
            QuotientGroup.mk' (K.subgroupOf L) c' *
              QuotientGroup.mk' (K.subgroupOf L) vL *
              (QuotientGroup.mk' (K.subgroupOf L) c')⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        have h2 : x = QuotientGroup.mk' (K.subgroupOf L) (c' * vL * c'⁻¹) := by
          rw [← hc, ← hc', h1]
        rw [h2, show c' * vL * c'⁻¹ =
          (⟨(c' : G) * v * (c' : G)⁻¹, haL⟩ : ↥L) from Subtype.ext rfl]
      refine ⟨(c' : G)⁻¹, L.inv_mem c'.2, 1, Or.inl rfl, ?_⟩
      refine ⟨(c' : G) * v * (c' : G)⁻¹, haL, ?_, ?_, hx_eq⟩
      · rw [one_mul, mem_conjSubgroup_iff]
        have e : (c' : G)⁻¹ * ((c' : G) * v * (c' : G)⁻¹) *
            ((c' : G)⁻¹)⁻¹ = v := by group
        rw [e]; exact hv
      · intro haK
        exact hxne (by rw [hx_eq]; exact (hmk1 _).2 haK)
    · obtain ⟨c, hc⟩ := isConj_iff.1 hx
      obtain ⟨c', hc'⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) c
      have hxne : x ≠ 1 := hxne_of' hx
      have haL : (c' : G) * w * (c' : G)⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem c'.2 (hWL hw)) (L.inv_mem c'.2)
      have hx_eq : x = QuotientGroup.mk' (K.subgroupOf L)
          ⟨(c' : G) * w * (c' : G)⁻¹, haL⟩ := by
        have h1 : QuotientGroup.mk' (K.subgroupOf L) (c' * wL * c'⁻¹) =
            QuotientGroup.mk' (K.subgroupOf L) c' *
              QuotientGroup.mk' (K.subgroupOf L) wL *
              (QuotientGroup.mk' (K.subgroupOf L) c')⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        have h2 : x = QuotientGroup.mk' (K.subgroupOf L) (c' * wL * c'⁻¹) := by
          rw [← hc, ← hc', h1]
        rw [h2, show c' * wL * c'⁻¹ =
          (⟨(c' : G) * w * (c' : G)⁻¹, haL⟩ : ↥L) from Subtype.ext rfl]
      refine ⟨(c' : G)⁻¹, L.inv_mem c'.2, g, Or.inr rfl, ?_⟩
      refine ⟨(c' : G) * w * (c' : G)⁻¹, haL, ?_, ?_, hx_eq⟩
      · rw [mem_conjSubgroup_iff]
        have e : (g * (c' : G)⁻¹) * ((c' : G) * w * (c' : G)⁻¹) *
            (g * (c' : G)⁻¹)⁻¹ = g * w * g⁻¹ := by group
        rw [e]
        have hwg : g * w * g⁻¹ ∈ V := by
          apply mem_conjSubgroup_iff.1
          rwa [← hW]
        exact hwg
      · intro haK
        exact hxne (by rw [hx_eq]; exact (hmk1 _).2 haK)
  have hrig : ∀ x y : ↥L ⧸ K.subgroupOf L,
      (IsConj s x ∨ IsConj t x) → (IsConj s y ∨ IsConj t y) →
        x * y = y * x → x = y := by
    intro x y hx hy hcomm
    obtain ⟨l₁, hl₁, ε₁, hε₁, a, haL, haConj, haK, hx_eq⟩ := lift x hx
    obtain ⟨l₂, hl₂, ε₂, hε₂, b, hbL, hbConj, hbK, hy_eq⟩ := lift y hy
    have hmemLab : ⁅a, b⁆ ∈ L := comm_mem haL hbL
    have hab : ⁅a, b⁆ ∈ K := by
      have h1 : (⟨⁅a, b⁆, hmemLab⟩ : ↥L) =
          ⁅(⟨a, haL⟩ : ↥L), (⟨b, hbL⟩ : ↥L)⁆ := Subtype.ext rfl
      have h2 : QuotientGroup.mk' (K.subgroupOf L) (⟨⁅a, b⁆, hmemLab⟩ : ↥L) = 1 := by
        rw [h1, map_commutatorElement]
        rw [← hx_eq, ← hy_eq]
        exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
      exact (hmk1 _).1 h2
    have hres := hR l₁ (le_of_eq hL hl₁) l₂ (le_of_eq hL hl₂) ε₁ ε₂ hε₁ hε₂ a b
      haConj hbConj haK hbK hab
    have hmkeq : QuotientGroup.mk' (K.subgroupOf L) (⟨a, haL⟩ : ↥L) =
        QuotientGroup.mk' (K.subgroupOf L) (⟨b, hbL⟩ : ↥L) := by
      rw [hmk2]
      simpa using hres.1
    rw [hx_eq, hy_eq]
    exact hmkeq
  obtain ⟨m, hm, he, hconj⟩ := s16c1G43_dih hssq httsq hs1 ht1 hgen hrig
  refine ⟨m, hm, he, ?_, ?_⟩
  · exact s16c1G43_twoRank_dihedral hm he.some
  · obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    obtain ⟨c', hc'⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) c
    refine ⟨(c' : G)⁻¹, L.inv_mem c'.2, ?_⟩
    have haL : (c' : G) * v * (c' : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem c'.2 (hVL hv)) (L.inv_mem c'.2)
    have haeq : QuotientGroup.mk' (K.subgroupOf L)
        (⟨(c' : G) * v * (c' : G)⁻¹, haL⟩ : ↥L) = t := by
      have h1 : QuotientGroup.mk' (K.subgroupOf L) (c' * vL * c'⁻¹) =
          QuotientGroup.mk' (K.subgroupOf L) c' *
            QuotientGroup.mk' (K.subgroupOf L) vL *
            (QuotientGroup.mk' (K.subgroupOf L) c')⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have h2 : t = QuotientGroup.mk' (K.subgroupOf L) (c' * vL * c'⁻¹) := by
        rw [← hc, ← hc', h1]
      rw [h2]
      exact (congrArg (QuotientGroup.mk' (K.subgroupOf L))
        (show c' * vL * c'⁻¹ =
          (⟨(c' : G) * v * (c' : G)⁻¹, haL⟩ : ↥L) from Subtype.ext rfl)).symm
    have haConj : (c' : G) * v * (c' : G)⁻¹ ∈ conjSubgroup V (1 * (c' : G)⁻¹) := by
      rw [one_mul, mem_conjSubgroup_iff]
      have e : (c' : G)⁻¹ * ((c' : G) * v * (c' : G)⁻¹) * ((c' : G)⁻¹)⁻¹ = v := by
        group
      rw [e]; exact hv
    have hbConj : w ∈ conjSubgroup V (g * 1) := by
      rw [mul_one, ← hW]
      exact hw
    have haK : (c' : G) * v * (c' : G)⁻¹ ∉ K := by
      intro h
      exact ht1 (by rw [← haeq]; exact (hmk1 _).2 h)
    have hmemLab : ⁅(c' : G) * v * (c' : G)⁻¹, w⁆ ∈ L := comm_mem haL (hWL hw)
    have hab : ⁅(c' : G) * v * (c' : G)⁻¹, w⁆ ∈ K := by
      have h1 : (⟨⁅(c' : G) * v * (c' : G)⁻¹, w⁆, hmemLab⟩ : ↥L) =
          ⁅(⟨(c' : G) * v * (c' : G)⁻¹, haL⟩ : ↥L), (⟨w, hWL hw⟩ : ↥L)⁆ :=
        Subtype.ext rfl
      have h2 : QuotientGroup.mk' (K.subgroupOf L)
          (⟨⁅(c' : G) * v * (c' : G)⁻¹, w⁆, hmemLab⟩ : ↥L) = 1 := by
        rw [h1, map_commutatorElement]
        have hwt : QuotientGroup.mk' (K.subgroupOf L) (⟨w, hWL hw⟩ : ↥L) = t := rfl
        rw [haeq, hwt, commutatorElement_self]
      exact (hmk1 _).1 h2
    have hRapp := hR ((c' : G)⁻¹) (le_of_eq hL (L.inv_mem c'.2)) 1
      (le_of_eq hL (one_mem L)) 1 g
      (Or.inl rfl) (Or.inr rfl) ((c' : G) * v * (c' : G)⁻¹) w haConj hbConj haK hwK hab
    rw [hW]
    have h := hRapp.2
    simp only [one_mul, mul_one] at h
    exact h.symm

theorem s16c1G43_quot {V : Subgroup G} {g : G} {K : Subgroup G}
    [(K.subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    {v w : G} (hv : v ∈ V) (hw : w ∈ conjSubgroup V g) (hvK : v ∉ K) (hwK : w ∉ K)
    (hvsq : v * v = 1) (hwsq : w * w = 1)
    (hVcos : ∀ x ∈ V, x ∉ K → v⁻¹ * x ∈ K)
    (hWcos : ∀ x ∈ conjSubgroup V g, x ∉ K → w⁻¹ * x ∈ K)
    (hR : ∀ l ∈ V ⊔ conjSubgroup V g, ∀ l' ∈ V ⊔ conjSubgroup V g, ∀ ε ε' : G,
      (ε = 1 ∨ ε = g) → (ε' = 1 ∨ ε' = g) →
      ∀ a b : G, a ∈ conjSubgroup V (ε * l) → b ∈ conjSubgroup V (ε' * l') →
        a ∉ K → b ∉ K → ⁅a, b⁆ ∈ K →
          a⁻¹ * b ∈ K ∧ conjSubgroup V (ε * l) = conjSubgroup V (ε' * l')) :
    ∃ m : ℕ, Odd m ∧
      Nonempty ((↥(V ⊔ conjSubgroup V g) ⧸ K.subgroupOf (V ⊔ conjSubgroup V g)) ≃*
        DihedralGroup m) ∧
      CFSG.Open.twoRank (↥(V ⊔ conjSubgroup V g) ⧸ K.subgroupOf (V ⊔ conjSubgroup V g)) = 1 ∧
      ∃ l ∈ V ⊔ conjSubgroup V g, conjSubgroup V g = conjSubgroup V l := by
  exact s16c1G43_quot_aux (V := V) (W := conjSubgroup V g) (g := g) (K := K)
    (L := V ⊔ conjSubgroup V g) rfl rfl hv hw hvK hwK hvsq hwsq hVcos hWcos hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
