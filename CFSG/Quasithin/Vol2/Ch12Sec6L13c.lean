module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13b
public import CFSG.Quasithin.Vol2.Ch12Sec6L11e

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def Stmt12_6_13_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : S126.Frame126 T L V) (v : G) (Kv S : Subgroup G), S126T2.Ctx1262 F v Kv S →
      centralizerSection S (S126T2.Lv L v) (pCoreOf 2 (S126T2.Lv L v)) ≤
        Subgroup.normalizer (S126T2.Vv L V v : Set G)

namespace S126T2

theorem quad_eq_add : ∀ x ∈ quads, ∃ d₁ ∈ duads, ∃ d₂ ∈ duads, x = d₁ + d₂ := by
  decide +kernel

theorem fixed23 : ∀ i j : Fin 8, i ∈ six → j ∈ six → i ≠ j →
    B5FinS8.pv (cy 4 5 6 i) (cy 4 5 6 j) = B5FinS8.pv i j →
    B5FinS8.pv (cy 5 6 7 i) (cy 5 6 7 j) = B5FinS8.pv i j → B5FinS8.pv i j = B5FinS8.pv 2 3 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem Vv_le_closure_Delta (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    Vv L V v ≤ Subgroup.closure (Delta F v) := by
  intro y hy
  have hD : ∀ d ∈ duads, ∃ u ∈ Delta F v, u ∈ Vv L V v ∧ coordV F u = d := fun d hd => by
    obtain ⟨u, hu, hc⟩ := exists_mem_Delta_coordV h1222 hH hv hβ hd
    exact ⟨u, hu, ((mem_Delta_iff h1222 hH hv hβ).1 hu).1, hc⟩
  rcases coordV_cases h1222 hH hv hβ hy with h0 | hd | hq | h6
  · have h1 : y = 1 := coordV_injOn h1222 hH hv hβ hy (Vv L V v).one_mem
      (h0.trans (coordV_one h1222 hH hv hβ).symm)
    rw [h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ((mem_Delta_iff h1222 hH hv hβ).2 ⟨hy, hd⟩)
  · obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := quad_eq_add _ hq
    obtain ⟨u₁, hu₁, hv₁, hc₁⟩ := hD d₁ hd₁
    obtain ⟨u₂, hu₂, hv₂, hc₂⟩ := hD d₂ hd₂
    have h1 : y = u₁ * u₂ := coordV_injOn h1222 hH hv hβ hy ((Vv L V v).mul_mem hv₁ hv₂)
      (by rw [coordV_mul h1222 hH hv hβ hv₁ hv₂, hc₁, hc₂, he])
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hu₁) (Subgroup.subset_closure hu₂)
  · obtain ⟨u₁, hu₁, hv₁, hc₁⟩ := hD _ (pv_mem_duads (i := 2) (j := 3) (by decide) (by decide)
      (by decide))
    obtain ⟨u₂, hu₂, hv₂, hc₂⟩ := hD _ (pv_mem_duads (i := 4) (j := 5) (by decide) (by decide)
      (by decide))
    obtain ⟨u₃, hu₃, hv₃, hc₃⟩ := hD _ (pv_mem_duads (i := 6) (j := 7) (by decide) (by decide)
      (by decide))
    have h12 := (Vv L V v).mul_mem hv₁ hv₂
    have h1 : y = u₁ * u₂ * u₃ := coordV_injOn h1222 hH hv hβ hy ((Vv L V v).mul_mem h12 hv₃)
      (by rw [coordV_mul h1222 hH hv hβ h12 hv₃, coordV_mul h1222 hH hv hβ hv₁ hv₂, hc₁, hc₂,
        hc₃, h6]; rfl)
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hu₁)
      (Subgroup.subset_closure hu₂)) (Subgroup.subset_closure hu₃)

theorem mem_centralizer_Vv (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {S : Subgroup G} {x : G}
    (hx : x ∈ centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)))
    (hxV : x ∈ Subgroup.normalizer (Vv L V v : Set G)) :
    x ∈ Subgroup.centralizer (Vv L V v : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hxL, -, hxc⟩ := hx
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hOV := pCoreOf_Lv_le h1222 F hH hv hβ
  have hxl : ∀ l ∈ Lv L v, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (Lv L v) := by
    intro l hl
    have h1 := hxc l⁻¹ ((Lv L v).inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (Lv L v) hl) _).1 h1
    have e : l * (l⁻¹ * x * l⁻¹⁻¹ * x⁻¹) * l⁻¹ = x * l * x⁻¹ * l⁻¹ := by group
    rwa [e] at h2
  have hcomm : ∀ l ∈ Lv L v, ∀ y ∈ Vv L V v,
      x * (l * y * l⁻¹) * x⁻¹ = l * (x * y * x⁻¹) * l⁻¹ := by
    intro l hl y hy
    have ho := hOV (hxl l hl)
    have hw : x * y * x⁻¹ ∈ V := Vv_le_V hH v ((Subgroup.mem_normalizer_iff.1 hxV y).1 hy)
    have hlw : l * (x * y * x⁻¹) * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV (Lv_le_L L v hl)) _).1 hw
    have h1 : x * l * x⁻¹ * l⁻¹ * (l * (x * y * x⁻¹) * l⁻¹) =
        l * (x * y * x⁻¹) * l⁻¹ * (x * l * x⁻¹ * l⁻¹) :=
      (Subgroup.mem_centralizer_iff.1 ho _ hlw).symm
    calc x * (l * y * l⁻¹) * x⁻¹ =
        x * l * x⁻¹ * l⁻¹ * (l * (x * y * x⁻¹) * l⁻¹) * (x * l * x⁻¹ * l⁻¹)⁻¹ := by group
      _ = l * (x * y * x⁻¹) * l⁻¹ := by rw [h1]; group
  obtain ⟨u₀, hu₀, hc₀⟩ := exists_mem_Delta_coordV h1222 hH hv hβ
    (pv_mem_duads (i := 2) (j := 3) (by decide) (by decide) (by decide))
  have hu₀v := ((mem_Delta_iff h1222 hH hv hβ).1 hu₀).1
  have hwΔ := perm_Delta_of_normalizer h1222 hH hv hβ hxV hxL u₀ hu₀
  have hwv := ((mem_Delta_iff h1222 hH hv hβ).1 hwΔ).1
  obtain ⟨i, j, hi, hj, hij, hwij⟩ := (mem_duads_iff _).1 ((mem_Delta_iff h1222 hH hv hβ).1 hwΔ).2
  have key : ∀ σ ∈ A6s, σ 2 = 2 → σ 3 = 3 →
      B5FinS8.pv (σ i) (σ j) = B5FinS8.pv i j := by
    intro σ hσ h2 h3
    obtain ⟨l, hl, hlσ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ σ hσ
    have hlu : (l : G) * u₀ * (l : G)⁻¹ = u₀ := by
      refine coordV_injOn h1222 hH hv hβ
        ((Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) u₀).1 hu₀v) hu₀v ?_
      rw [coordV_conj h1222 hH hv hβ hl hu₀v, hc₀, hlσ, pv_comp_inv, h2, h3]
    have hlw : (l : G) * (x * u₀ * x⁻¹) * (l : G)⁻¹ = x * u₀ * x⁻¹ := by
      rw [← hcomm l hl u₀ hu₀v, hlu]
    have h := coordV_conj h1222 hH hv hβ hl hwv
    rw [hlw, hwij, hlσ, pv_comp_inv] at h
    exact h.symm
  have h456 := key (cy 4 5 6) (cy_mem (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by decide) (by decide)
  have h567 := key (cy 5 6 7) (cy_mem (by decide) (by decide) (by decide) (by decide)
    (by decide)) (by decide) (by decide)
  have hw₀ : x * u₀ * x⁻¹ = u₀ := coordV_injOn h1222 hH hv hβ hwv hu₀v
    (by rw [hwij, hc₀]; exact fixed23 i j hi hj hij h456 h567)
  have hΔ : ∀ u ∈ Delta F v, x * u * x⁻¹ = u := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := exists_Lv_conj_eq h1222 hH hv hβ hu₀ hu
    rw [hcomm l hl u₀ hu₀v, hw₀]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyc : y ∈ Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le _).2 (fun u hu => ?_) (Vv_le_closure_Delta h1222 hH hv hβ hy)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hΔ u hu
    calc u * x = x * u * x⁻¹ * x := by rw [h1]
      _ = x * u := by group
  exact Subgroup.mem_centralizer_singleton_iff.1 hyc

theorem Vv_le_comm_Usec (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) (h3 : Stmt12_6_13_three) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hD6 : ¬ CFSG.IsQuasisimple ↥Kv) :
    Vv L V v ≤ ⁅Usec Kv S, Kv⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  set R := centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)) with hR
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hOS : pCoreOf 2 (Lv L v) ≤ S := by
    have hOH : pCoreOf 2 (Lv L v) ≤ Gv v ⊓ Subgroup.normalizer (Lv L v : Set G) :=
      le_inf ((pCoreOf_le 2 _).trans (Lv_le_Gv L v))
        ((pCoreOf_le 2 _).trans Subgroup.le_normalizer)
    refine (A4.le_of_normal_of_isSylowTwoOf hC.sylowN hOH ?_ (pCoreOf_isPGroup 2 _)).trans
      inf_le_left
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (inf_le_right.trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hOR : pCoreOf 2 (Lv L v) ≤ R := by
    intro o ho
    have hoL : o ∈ Lv L v := pCoreOf_le 2 _ ho
    refine ⟨hOS ho, Subgroup.le_normalizer hoL, Subgroup.le_normalizer ho, fun l hl => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (Lv L v) hl) o).1 ho
    exact (pCoreOf 2 (Lv L v)).mul_mem h1 ((pCoreOf 2 (Lv L v)).inv_mem ho)
  have hVΩ : Vv L V v ≤ omegaOneCenterOf R := by
    intro u hu
    refine Subgroup.subset_closure ⟨⟨hOR (Vv_le_pCoreOf h1222 hH hv hu), ?_⟩,
      hVe.2 u (Vv_le_V hH v hu)⟩
    show u ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrC := mem_centralizer_Vv h1222 hH hv hβ hr (h3 G T L V F v Kv S hC hr)
    exact (Subgroup.mem_centralizer_iff.1 hrC u hu).symm
  calc Vv L V v ≤ ⁅Vv L V v, Lv L v⁆ := Vv_le_comm h1222 hH hv
    _ ≤ VYR (Lv L v) R := Subgroup.commutator_mono hVΩ le_rfl
    _ ≤ VYR Kv (pCoreOf 2 (Kv ⊔ S)) := a4_10_2 (a410Hyp h1222 h36 hD2 hC hD6)
    _ = ⁅Usec Kv S, Kv⁆ := rfl

end S126T2

theorem lemma12_6_13_of (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) (hD6 : Lemma12_6_12) (h3 : Stmt12_6_13_three) : Lemma12_6_13 := by
  intro G _ _ T L V _ F v Kv S hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hD6 G T L V F v Kv S hC
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hsub : IsSubnormal Kv (Kv ⊔ S) :=
    A4.subnormal_of_normal le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hSK))
  refine ⟨⟨A4.charTwo_sup (S126T2.charTwo_Kv h1222 h36 hC hq) hSK hC.sylow.2.1,
    S126T2.pCoreOf_eq_centralizer h1222 h36 hD2 hC hq⟩, ?_,
    S126T2.Vv_le_comm_Usec h1222 h36 hD2 h3 hC hq⟩
  have heq : (pCoreOf 2 (Kv ⊔ S)).subgroupOf Kv = CFSG.pCore 2 ↥Kv := by
    apply le_antisymm
    · intro z hz
      have hle : Kv ⊓ pCoreOf 2 (Kv ⊔ S) ≤ pCoreOf 2 Kv :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun k hk => A4.mem_normalizer_inf (Subgroup.le_normalizer hk)
            (le_normalizer_pCoreOf 2 (Kv ⊔ S) ((le_sup_left : Kv ≤ Kv ⊔ S) hk)))
          ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
      exact (S126T2.mem_pCoreOf_iff z).1 (hle ⟨z.2, hz⟩)
    · intro z hz
      exact A4.pCoreOf_le_of_subnormal 2 hsub ((S126T2.mem_pCoreOf_iff z).2 hz)
  rw [heq]
  exact ⟨inferInstance, S126T2.isSimple_Kv h1222 h36 hC⟩

end CFSG.Quasithin.H13
