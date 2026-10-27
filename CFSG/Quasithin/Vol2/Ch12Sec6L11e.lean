module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11d
public import CFSG.Quasithin.Vol2.Ch12Sec6L11c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def Stmt12_6_11_f : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : S126.Frame126 T L V) (v : G) (Kv S : Subgroup G), S126T2.Ctx1262 F v Kv S →
      S126T2.Lv L v = Kv → ¬ thompsonJ (S126T2.Tv T v) ≤ S126T2.Qv T V →
        S126T2.Gv v ≤ Subgroup.normalizer (S126T2.Vv L V v : Set G)

namespace S126T2

theorem pv_comp_inv (σ : Equiv.Perm (Fin 8)) (a b : Fin 8) :
    (fun i => B5FinS8.pv a b (σ⁻¹ i)) = B5FinS8.pv (σ a) (σ b) := by
  have h := congrArg Multiplicative.toAdd (B5FinS8.permAct_pv σ a b)
  rw [toAdd_ofAdd] at h
  rw [← h]
  funext i
  rw [permAct_apply, toAdd_ofAdd]

theorem vSix_comp_inv {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ A6s) :
    (fun i => vSix (σ⁻¹ i)) = vSix := by
  obtain ⟨hσ0, hσ1, -⟩ := mem_A6s.1 hσ
  funext i
  have hiff : σ⁻¹ i ∈ six ↔ i ∈ six := by
    rw [mem_six_iff, mem_six_iff, Ne, Ne, Ne, Ne, Equiv.Perm.inv_eq_iff_eq,
      Equiv.Perm.inv_eq_iff_eq, hσ0, hσ1]
  rw [vSix_apply, vSix_apply]
  exact if_congr hiff rfl rfl

theorem mem_six_perm {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ A6s) {i : Fin 8} (hi : i ∈ six) :
    σ i ∈ six := by
  obtain ⟨hσ0, hσ1, -⟩ := mem_A6s.1 hσ
  obtain ⟨hi0, hi1⟩ := (mem_six_iff i).1 hi
  refine (mem_six_iff _).2 ⟨fun h => hi0 ?_, fun h => hi1 ?_⟩
  · rw [← hσ0] at h; exact σ.injective h
  · rw [← hσ1] at h; exact σ.injective h

theorem quads_comp_inv {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ A6s) {x : Fin 8 → ZMod 2}
    (hx : x ∈ quads) : (fun i => x (σ⁻¹ i)) ∈ quads := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := (mem_duads_iff _).1 hd
  have e : (fun i => (B5FinS8.pv a b + vSix) (σ⁻¹ i)) =
      B5FinS8.pv (σ a) (σ b) + vSix := by
    funext i
    have h1 := congrFun (pv_comp_inv σ a b) i
    have h2 := congrFun (vSix_comp_inv hσ) i
    simp only [Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2]
  rw [e]
  exact Finset.mem_image.2 ⟨_, pv_mem_duads (mem_six_perm hσ ha) (mem_six_perm hσ hb)
    (fun h => hab (σ.injective h)), rfl⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_mem_Delta_coordV (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {x : Fin 8 → ZMod 2}
    (hx : x ∈ duads) : ∃ y ∈ Delta F v, coordV F y = x := by
  obtain ⟨i, j, hi, hj, hij, rfl⟩ := (mem_duads_iff _).1 hx
  obtain ⟨y, hyΔ, hyV, hβy⟩ := exists_mem_Delta h1222 F hH hv hβ hi hj hij
  have hpe : pe i j ∈ core01 := mem_core01.2 (by
    rw [S126L20a.toAdd_pe]
    exact pv_zero_of_two_le i j (two_le_of_mem_six i hi) (two_le_of_mem_six j hj))
  exact ⟨y, hyΔ, by rw [coordV_eq hyV hpe hβy, S126L20a.toAdd_pe]⟩

theorem perm_Delta_of_normalizer (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {g : G} (hgV : g ∈ Subgroup.normalizer (Vv L V v : Set G))
    (hgL : g ∈ Subgroup.normalizer (Lv L v : Set G)) :
    ∀ u ∈ Delta F v, g * u * g⁻¹ ∈ Delta F v := by
  classical
  intro u hu
  obtain ⟨huv, huD⟩ := (mem_Delta_iff h1222 hH hv hβ).1 hu
  set w := g * u * g⁻¹ with hw
  have hwv : w ∈ Vv L V v := (Subgroup.mem_normalizer_iff.1 hgV u).1 huv
  have hconj : ∀ y ∈ Delta F v, ∃ l' : ↥L, (l' : G) ∈ Lv L v ∧
      g * y * g⁻¹ = (l' : G) * w * (l' : G)⁻¹ := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := exists_Lv_conj_eq h1222 hH hv hβ hu hy
    have hl' : g * l * g⁻¹ ∈ Lv L v := (Subgroup.mem_normalizer_iff.1 hgL l).1 hl
    refine ⟨⟨_, Lv_le_L L v hl'⟩, hl', ?_⟩
    simp only [hw]
    group
  rcases coordV_cases h1222 hH hv hβ hwv with h0 | hD | hQ | h6
  ·
    exfalso
    have hw1 : w = 1 := coordV_injOn h1222 hH hv hβ hwv (Vv L V v).one_mem
      (h0.trans (coordV_one h1222 hH hv hβ).symm)
    have hu1 : u = 1 := by
      have : u = g⁻¹ * w * g := by rw [hw]; group
      rw [this, hw1]
      group
    rw [hu1, coordV_one h1222 hH hv hβ] at huD
    exact absurd huD (by decide)
  · exact (mem_Delta_iff h1222 hH hv hβ).2 ⟨hwv, hD⟩
  ·
    exfalso
    set A : Set G := {y | y ∈ Delta F v ∧ u * y ∈ Delta F v} with hA
    set B : Set G := {y | y ∈ Vv L V v ∧ coordV F y ∈ quads ∧ coordV F (w * y) ∈ quads} with hB
    have hA8 : 8 ≤ A.ncard := by
      have hs : (↑(duads.filter fun x => coordV F u + x ∈ duads) : Set (Fin 8 → ZMod 2)).ncard =
          8 := by
        rw [Set.ncard_coe_finset]
        exact card_duads_nbhd _ huD
      rw [← hs]
      let f : (Fin 8 → ZMod 2) → G := fun x =>
        if h : ∃ y ∈ Delta F v, coordV F y = x then h.choose else 1
      have hf : ∀ x ∈ duads, f x ∈ Delta F v ∧ coordV F (f x) = x := by
        intro x hx
        have h := exists_mem_Delta_coordV h1222 hH hv hβ hx
        simp only [f, dite_eq_left h]
        exact h.choose_spec
      refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) (fun x hx x' hx' hxx => ?_)
        (Set.toFinite _)
      · rw [Finset.coe_filter] at hx
        obtain ⟨hfx, hcx⟩ := hf x hx.1
        refine ⟨hfx, (mem_Delta_iff h1222 hH hv hβ).2 ⟨(Vv L V v).mul_mem huv
          ((mem_Delta_iff h1222 hH hv hβ).1 hfx).1, ?_⟩⟩
        rw [coordV_mul h1222 hH hv hβ huv ((mem_Delta_iff h1222 hH hv hβ).1 hfx).1, hcx]
        exact hx.2
      · rw [Finset.coe_filter] at hx hx'
        rw [← (hf x hx.1).2, ← (hf x' hx'.1).2, hxx]
    have hAB : A.ncard ≤ B.ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun y => g * y * g⁻¹) (fun y hy => ?_)
        (fun y _ y' _ h => ?_) (Set.toFinite _)
      · obtain ⟨hyΔ, huyΔ⟩ := hy
        have hyv := ((mem_Delta_iff h1222 hH hv hβ).1 hyΔ).1
        refine ⟨(Subgroup.mem_normalizer_iff.1 hgV y).1 hyv, ?_, ?_⟩
        · obtain ⟨l', hl', he⟩ := hconj y hyΔ
          rw [he, coordV_conj h1222 hH hv hβ hl' hwv]
          exact quads_comp_inv (psiP_mem_A6s h1222 F hH hv hβ
            (show l' ∈ (Lv L v).subgroupOf L from hl')) hQ
        · obtain ⟨l', hl', he⟩ := hconj (u * y) huyΔ
          have e : w * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by rw [hw]; group
          rw [e, he, coordV_conj h1222 hH hv hβ hl' hwv]
          exact quads_comp_inv (psiP_mem_A6s h1222 F hH hv hβ
            (show l' ∈ (Lv L v).subgroupOf L from hl')) hQ
      · simpa using h
    have hB6 : B.ncard ≤ 6 := by
      have ht : (↑(quads.filter fun x => coordV F w + x ∈ quads) : Set (Fin 8 → ZMod 2)).ncard =
          6 := by
        rw [Set.ncard_coe_finset]
        exact card_quads_nbhd _ hQ
      rw [← ht]
      refine Set.ncard_le_ncard_of_injOn (coordV F) (fun y hy => ?_) (fun y hy y' hy' h => ?_)
        (Set.toFinite _)
      · rw [Finset.coe_filter]
        refine ⟨hy.2.1, ?_⟩
        rw [← coordV_mul h1222 hH hv hβ hwv hy.1]
        exact hy.2.2
      · exact coordV_injOn h1222 hH hv hβ hy.1 hy'.1 h
    omega
  ·
    exfalso
    have hfixw : ∀ l ∈ Lv L v, l * w * l⁻¹ = w := by
      intro l hl
      have hlw : l * w * l⁻¹ ∈ Vv L V v :=
        (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) w).1 hwv
      refine coordV_injOn h1222 hH hv hβ hlw hwv ?_
      rw [show l = ((⟨l, Lv_le_L L v hl⟩ : ↥L) : G) from rfl,
        coordV_conj h1222 hH hv hβ (l := ⟨l, Lv_le_L L v hl⟩) hl hwv, h6]
      exact vSix_comp_inv (psiP_mem_A6s h1222 F hH hv hβ
        (show (⟨l, Lv_le_L L v hl⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hl))
    have hfixu : ∀ l ∈ Lv L v, l * u * l⁻¹ = u := by
      intro l hl
      have hl' : g * l * g⁻¹ ∈ Lv L v := (Subgroup.mem_normalizer_iff.1 hgL l).1 hl
      have h := hfixw _ hl'
      have e : l * u * l⁻¹ = g⁻¹ * ((g * l * g⁻¹) * w * (g * l * g⁻¹)⁻¹) * g := by
        rw [hw]; group
      rw [e, h, hw]
      group
    obtain ⟨u₁, hu₁, hc₁⟩ := exists_mem_Delta_coordV h1222 hH hv hβ
      (pv_mem_duads (i := 2) (j := 3) (by decide) (by decide) (by decide))
    obtain ⟨u₂, hu₂, hc₂⟩ := exists_mem_Delta_coordV h1222 hH hv hβ
      (pv_mem_duads (i := 4) (j := 5) (by decide) (by decide) (by decide))
    obtain ⟨l₁, hl₁, he₁⟩ := exists_Lv_conj_eq h1222 hH hv hβ hu hu₁
    obtain ⟨l₂, hl₂, he₂⟩ := exists_Lv_conj_eq h1222 hH hv hβ hu hu₂
    rw [hfixu l₁ hl₁] at he₁
    rw [hfixu l₂ hl₂] at he₂
    have h : B5FinS8.pv 2 3 = B5FinS8.pv 4 5 := by rw [← hc₁, ← hc₂, ← he₁, ← he₂]
    exact absurd h (by decide)

end S126T2

theorem lemma12_6_11_of (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (hD3 : Lemma12_6_6_9) (h11f : Stmt12_6_11_f) : Lemma12_6_11 := by
  intro G _ _ T L V _ F v Kv S hC
  have hlt : S126T2.Lv L v < Kv := by
    refine lt_of_le_of_ne hC.lv_le fun hLK => ?_
    by_cases hJ : thompsonJ (S126T2.Tv T v) ≤ S126T2.Qv T V
    · exact S126T2.false_of_le_Q h1222 h56 hD3 hC hLK hJ
    · have hN := h11f G T L V F v Kv S hC hLK hJ
      have hGL : S126T2.Gv v ≤ Subgroup.normalizer (S126T2.Lv L v : Set G) := hLK ▸ hC.normal
      exact hC.not_le fun g hg => S126T2.mem_M_of_perm_Delta h1222 hC hLK
        (S126T2.perm_Delta_of_normalizer h1222 hC.hyp hC.mem hC.coord (hN hg) (hGL hg))
  exact ⟨hlt, S126T2.not_le_M_of_lt h1222 h1228 hC hlt⟩

end CFSG.Quasithin.H13
