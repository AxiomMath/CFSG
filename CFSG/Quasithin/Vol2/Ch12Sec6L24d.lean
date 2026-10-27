module

public import CFSG.Quasithin.Vol2.Ch12Sec6L24c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L19 S126L19a S126L20a Equiv CFSG.LieType.BorelTits
open CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

namespace S126L24

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem inHz_G1 (h1222 : Stmt12_2_2) (h1221 : Lemma12_6_21) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    InHz T L F.V1 (Subgroup.normalizer (F.V1 : Set G)) := by
  have hyp := hH.hyp
  obtain ⟨hVT, -, -, -⟩ := S126L20.facts h1222 hH
  have hcard : Nat.card F.V1 = 2 := (S126L23d.part2 h1222 F hH hZ).2
  obtain ⟨-, -, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  obtain ⟨zv, hzv⟩ := F.β_surj e0123
  have hz1 : (zv : G) ∈ F.V1 := (mem_preV zv.2).2 (hzv ▸ e0123_mem_W1)
  have hzne : (zv : G) ≠ 1 := by
    intro h
    apply e0123_ne_one
    rw [← hzv, show zv = 1 from Subtype.ext h, map_one]
  have hz4 : F.Wt4 (zv : G) := ⟨zv.2, by rw [hzv]; exact hasWt_e0123⟩
  have hC := h1221 G T L V F hH (zv : G) hzne hz4
  have hNC := normalizer_eq_centralizer_of_card_eq_two hcard
  refine ⟨⟨hXV1, fun hbot => ?_⟩, fun hle => hC ?_, hNC.le⟩
  · have hle := le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : F.V1 ≤ Subgroup.normalizer (F.V1 : Set G)) le_rfl
      (hyp.sylow.1.to_le ((preV_le F W1).trans hVT))
    rw [hbot] at hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard, Subgroup.card_bot] at h1
    omega
  · refine le_trans ?_ hle
    intro x hx
    rw [hNC, Subgroup.mem_centralizer_iff]
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, one_mul, mul_one]
    · rw [S126L23d.eq_of_card_two hcard hw hz1 hw1 hzne]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hx).symm

theorem le_pCoreOf_normalizer_closure (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hV5O : F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G))) {y : D8} (hy4 : HasWt 4 y)
    (hy4' : HasWt 4 (y * e0123)) :
    V ≤ pCoreOf 2 (Subgroup.normalizer
      (preV F (Subgroup.closure {e0123, y}) : Set G)) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  set S : Subgroup D8 := Subgroup.closure {e0123, y} with hS
  set X := preV F S with hX
  have hXV : X ≤ V := preV_le F S
  have hW1S : W1 ≤ S := fun w hw => by
    rcases mem_W1 hw with rfl | rfl
    · exact S.one_mem
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hV1X : F.V1 ≤ X := Subgroup.map_mono (Subgroup.comap_mono hW1S)
  obtain ⟨σ, hσA, hσσ, hσe, hσy, z, hz5, hzσ⟩ := exists_swap hy4 hy4'
  obtain ⟨l, hl⟩ := psi_surjective F hH ⟨σ, hσA⟩
  have hlσ : ActsAs F (l : G) σ := by
    have := actsAs_psi F hH l
    rw [hl] at this
    exact this
  have hlV : (l : G) ∈ Subgroup.normalizer (V : Set G) := hLV l.2
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hSσ : ∀ w ∈ S, dAct σ w ∈ S := by
    intro w hw
    have hmap : S.map (dAct σ) ≤ S := by
      rw [hS, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl
      · rw [hσe]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [hσy]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
    exact hmap ⟨w, hw, rfl⟩
  have hlX : (l : G) ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_preV hlV hlσ hSσ (by rw [hσinv]; exact hSσ)
  obtain ⟨v₀, hv₀⟩ := F.β_surj z
  have hv₀5 : (v₀ : G) ∈ F.V5 := (mem_preV v₀.2).2 (hv₀ ▸ hz5)
  set w₀ : ↥V := ⟨l * v₀ * l⁻¹, conj_mem hlV v₀⟩ with hw₀def
  have hw₀ : F.β w₀ ∉ W5 := by
    rw [hlσ v₀ w₀ rfl, hv₀]
    exact hzσ
  have hCX1 : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (F.V1 : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV1X hx)
  have hV5C : F.V5 ≤ Subgroup.centralizer (X : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun x hx => S126L1b.comm_of_mem (hXV hx) (preV_le F W5 hv)
  have hY : pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ⊓ Subgroup.centralizer (X : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer (X : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (A1a.le_normalizer_inf (hCX1.trans (le_normalizer_pCoreOf 2 _))
        Subgroup.le_normalizer)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  have hCP : pCoreOf 2 (Subgroup.centralizer (X : Set G)) ≤
      pCoreOf 2 (Subgroup.normalizer (X : Set G)) :=
    le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _))
      ((F7.normalizer_le_normalizer_centralizer X).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  have hV5P : F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (X : Set G)) := fun v hv =>
    hCP (hY ⟨hV5O hv, hV5C hv⟩)
  have hw₀P : (w₀ : G) ∈ pCoreOf 2 (Subgroup.normalizer (X : Set G)) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hlX) v₀).1 (hV5P hv₀5)
  intro v hv
  by_cases hv5 : v ∈ F.V5
  · exact hV5P hv5
  · have hβv : F.β ⟨v, hv⟩ ∉ W5 := fun h => hv5 ((mem_preV hv).2 h)
    have hm : F.β (⟨v, hv⟩ * w₀⁻¹) ∈ W5 := by
      rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two index_W5]
      exact iff_of_false hβv fun h => hw₀ ((W5.inv_mem_iff).1 h)
    have h5 : ((⟨v, hv⟩ * w₀⁻¹ : ↥V) : G) ∈ F.V5 := (mem_preV _).2 hm
    have e : v = ((⟨v, hv⟩ * w₀⁻¹ : ↥V) : G) * w₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ (hV5P h5) hw₀P

theorem part3 (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hV5O : F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G))) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (F.V2 : Set G)) := by
  have h := le_pCoreOf_normalizer_closure F hH hV5O hasWt_e0145 hasWt_e0145_mul
  rw [← W2_eq] at h
  exact h

theorem part5 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hV5O : F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G))) :
    ∀ g : G, F.V1 < V ⊓ conjSubgroup V g → IsPGroup 2 ↥(V ⊔ conjSubgroup V g) := by
  intro g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  obtain ⟨hVT, -, -, -⟩ := S126L20.facts h1222 hH
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hVg2 : IsPGroup 2 (conjSubgroup V g) := hV2.map _
  by_cases hgV : g ∈ Subgroup.normalizer (V : Set G)
  · rw [conjSubgroup_eq_iff_mem_normalizer.2 hgV, sup_idem]
    exact hV2
  obtain ⟨u, hu, hu1⟩ := IsConcreteLE.exists_of_lt hg
  obtain ⟨zv, hzv⟩ := F.β_surj e0123
  have hz1 : (zv : G) ∈ F.V1 := (mem_preV zv.2).2 (hzv ▸ e0123_mem_W1)
  have hu1' : u ≠ 1 := fun h => hu1 (h ▸ F.V1.one_mem)
  have hzu : u * zv ∈ V ⊓ conjSubgroup V g := (V ⊓ conjSubgroup V g).mul_mem hu (hg.le hz1)
  have hzu1 : u * zv ≠ 1 := fun h => hu1 (by
    rw [eq_inv_of_mul_eq_one_left h]
    exact F.V1.inv_mem hz1)
  obtain ⟨hu4V, hu4⟩ := S126L20.wt4_of_mem_inter h331 h1222 h1262 F hH hfus hgV hu hu1'
  obtain ⟨huz4V, huz4⟩ := S126L20.wt4_of_mem_inter h331 h1222 h1262 F hH hfus hgV hzu hzu1
  have hβuz : F.β ⟨u * zv, huz4V⟩ = F.β ⟨u, hu4V⟩ * e0123 := by
    rw [← hzv, ← map_mul]
    rfl
  rw [hβuz] at huz4
  have hP := le_pCoreOf_normalizer_closure F hH hV5O hu4 huz4
  have hinj := beta_injective F hZ
  have hXA : preV F (Subgroup.closure {e0123, F.β ⟨u, hu4V⟩}) ≤ V ⊓ conjSubgroup V g := by
    have h1 : Subgroup.closure {e0123, F.β ⟨u, hu4V⟩} ≤
        ((V ⊓ conjSubgroup V g).comap V.subtype).map F.β := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨zv, hg.le hz1, hzv⟩
      · exact ⟨⟨u, hu4V⟩, hu, rfl⟩
    have h2 := Subgroup.map_mono (f := V.subtype) (Subgroup.comap_mono (f := F.β) h1)
    exact le_trans h2 (le_of_eq (preV_map hinj inf_le_left))
  have hVgN : conjSubgroup V g ≤ Subgroup.normalizer
      (preV F (Subgroup.closure {e0123, F.β ⟨u, hu4V⟩}) : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx =>
      S126L20c.conj_comm (hXA hx).2 hy)
  set P := pCoreOf 2 (Subgroup.normalizer
    (preV F (Subgroup.closure {e0123, F.β ⟨u, hu4V⟩}) : Set G)) with hPdef
  have hPn : conjSubgroup V g ≤ Subgroup.normalizer (P : Set G) :=
    hVgN.trans (le_normalizer_pCoreOf 2 _)
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 _
  have h2 : IsPGroup 2 ↥(conjSubgroup V g ⊔ P) := IsPGroup.to_sup_of_normal_right' hVg2 hP2 hPn
  exact h2.to_le (sup_le (hP.trans le_sup_right) le_sup_left)

end S126L24

open S126L24 in
theorem lemma12_6_24_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (h1221 : Lemma12_6_21) : Lemma12_6_24 := by
  intro G _ _ T L V _ F hH hZ
  have hfus := (h1219 G T L V F hH).1
  have hF91 : ∀ H, InHz T L F.V1 H → HypF91 T V L F.V1 F.V5 H := fun H hHz =>
    hypF91 h331 h1222 h3228 h1262 F hH hfus hZ hHz
  have hV5O : F.V5 ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) :=
    (le_conjClosure _ _).trans (hF91 _ (inHz_G1 h1222 h1221 F hH hZ)).F92_1.1
  exact ⟨part1 h1222 F hH hZ, hV5O, part3 F hH hV5O, part4 h331 h1222 h1262 F hH hfus hZ,
    part5 h331 h1222 h1262 F hH hfus hZ hV5O, part6 h331 h1222 h1262 F hH hfus hZ,
    fun H hHz => ⟨(hF91 H hHz).F92_1.1, hF91 H hHz, (hF91 H hHz).F92_3.1⟩⟩

theorem lemma12_6_25_of (h1224 : Lemma12_6_24) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
      (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
        ∀ H : Subgroup G, InHz T L F.V1 H →
          (IsMulCommutative ↥(conjClosure F.V5 H) ↔ V ≤ pCoreOf 2 H) ∧
          (V ≤ pCoreOf 2 H ↔ V ≤ Subgroup.centralizer (conjClosure F.V5 H : Set G)) ∧
          (V ≤ Subgroup.centralizer (conjClosure F.V5 H : Set G) ↔
            IsMulCommutative ↥(conjClosure V H)) := by
  intro G _ _ T L V _ F hH hZ H hHz
  obtain ⟨-, -, -, -, -, ⟨-, -, h65, -⟩, h7⟩ := h1224 G T L V F hH hZ
  obtain ⟨-, hF, -⟩ := h7 H hHz
  have hC : (H ⊓ Subgroup.centralizer (F.V5 : Set G)) ⊓ (H ⊓ Subgroup.normalizer (V : Set G)) =
      H ⊓ Subgroup.centralizer (V : Set G) := by
    rw [h65]
    exact le_antisymm inf_le_left
      (le_inf le_rfl (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)))
  have h93 := hF.F93
  have h94 := hF.F94_3 hC
  have key : ∀ Z : Subgroup G, (∀ z ∈ Z, z ^ 2 = 1) →
      (IsMulCommutative ↥(conjClosure Z H) ↔ IsElemAbelian 2 (conjClosure Z H)) := by
    intro Z hZ2
    refine ⟨fun hc => ?_, fun h => h.1⟩
    refine F7.isElemAbelian_closure _ (fun x hx y hy => ?_) ?_
    · have hx' : x ∈ conjClosure Z H := Subgroup.subset_closure hx
      have hy' : y ∈ conjClosure Z H := Subgroup.subset_closure hy
      have := hc
      exact congrArg Subtype.val (mul_comm' (⟨x, hx'⟩ : ↥(conjClosure Z H)) ⟨y, hy'⟩)
    · rintro _ ⟨k, -, z, hz, rfl⟩
      have e : (k * z * k⁻¹) ^ 2 = k * z ^ 2 * k⁻¹ := conj_pow
      rw [e, hZ2 z hz]
      group
  have hsq5 : ∀ v ∈ F.V5, v ^ 2 = 1 := fun v hv => hF.elemAbelian_Vp.2 v hv
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => hF.elemAbelian.2 v hv
  refine ⟨?_, ?_, ?_⟩
  · exact (key _ hsq5).trans (h94.out 1 2).symm
  · exact (h93.out 1 2).trans ⟨fun h => h.trans inf_le_right, fun h => le_inf hF.V_le_H h⟩
  · constructor
    · intro h
      exact (key _ hsq).2 ((h94.out 1 3).1 ((h93.out 1 2).2 (le_inf hF.V_le_H h)))
    · intro h
      have h1 : V ≤ H ⊓ Subgroup.centralizer (conjClosure F.V5 H : Set G) :=
        (h93.out 1 2).1 ((h94.out 1 3).2 ((key _ hsq).1 h))
      exact h1.trans inf_le_right

end CFSG.Quasithin.H13
