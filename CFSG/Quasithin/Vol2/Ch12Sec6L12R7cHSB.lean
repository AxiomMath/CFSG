module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12R5Sing
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R7aGeom
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R7bHSA
public import CFSG.Quasithin.Vol2.Ch12Sec6T2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def psiV {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) : ↥V →* MulAut (↥Kv ⧸ Subgroup.center ↥Kv) :=
  (autBarHom Kv).comp (Subgroup.inclusion (V_le_normalizer_Kv hC))

theorem hs_branch_B (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hHS : FactHSE16Outer) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hq : CFSG.IsQuasisimple ↥Kv)
    (hcent : Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) ≤
      (Subgroup.center ↥Kv).map Kv.subtype)
    (eH : Nonempty (↥Kv ⧸ Subgroup.center ↥Kv ≃* NativeSporadic.HS))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hKG : Kv ≤ Gv v := le_of_mem_cComp hC.cComp
  have hLK : Lv L v ≤ Kv := hC.lv_le
  have hD := a6LocalData_of_ctx h1222 h36 hC hq hcent
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  obtain ⟨U, hU20, hUwt, hUnot, hUq⟩ := exists_twenty h1222 hH hv hβ hZ
  set ψ := psiV hC with hψdef
  have hfixE : ∀ u : ↥V, ∀ e ∈ Ebar L V v Kv, ψ u e = e := fun u e he =>
    autBarHom_fix_Ebar hH hC u u.2 e he
  have hfib : ∀ u u' : ↥V, ψ u = ψ u' → ((u : G))⁻¹ * u' ∈ Subgroup.centralizer (Kv : Set G) := by
    intro u u' h
    have h1 : ψ (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    exact mem_centralizer_of_autBarHom_eq_one Kv hK _ h1
  have hE2 : Nat.card ↥(Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G)) = 2 :=
    card_Vv_inf h1222 hH hv hβ
  have hfin : (((Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) : Subgroup G) : Set G)).Finite :=
    Set.toFinite _
  have hcardE2 : hfin.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card, ← Nat.card_coe_set_eq]
    exact hE2
  have hbound : ∀ a ∈ U.image ψ, (U.filter fun u => ψ u = a).card ≤ 2 := by
    intro a ha
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.1 ha
    rw [← hcardE2]
    refine Finset.card_le_card_of_injOn (fun u : ↥V => ((u₀ : G))⁻¹ * u) ?_ ?_
    · intro u hu
      obtain ⟨huU, hψu⟩ := Finset.mem_filter.1 hu
      simp only [Set.Finite.mem_toFinset, SetLike.mem_coe]
      refine ⟨hUq u₀ hu₀ u huU, ?_⟩
      exact Subgroup.centralizer_le hLK (hfib u₀ u hψu.symm)
    · intro u hu u' hu' h
      exact Subtype.ext (mul_left_cancel h)
  have hA7 : 7 ≤ (U.image ψ).card := by
    have := Finset.card_le_mul_card_image U 2 hbound
    omega
  have hnotinner : ∀ u ∈ U, ∀ e ∈ Ebar L V v Kv, ψ u ≠ MulAut.conj e := by
    intro u hu e he hψe
    obtain ⟨a', ha', rfl⟩ := he
    have ha'N : (a' : G) ∈ Subgroup.normalizer (Kv : Set G) := Subgroup.le_normalizer a'.2
    have h1 : autBarHom Kv ⟨(a' : G), ha'N⟩ = MulAut.conj (QuotientGroup.mk a') :=
      autBarHom_of_mem Kv ⟨(a' : G), ha'N⟩ a'.2
    have h2 : ψ u = autBarHom Kv ⟨(a' : G), ha'N⟩ := by rw [h1]; exact hψe
    have haV : (a' : G) ∈ V := Vv_le_V hH v ha'
    have huN : (u : G) ∈ Subgroup.normalizer (Kv : Set G) := V_le_normalizer_Kv hC u.2
    have h3 : autBarHom Kv (⟨(a' : G), ha'N⟩⁻¹ * ⟨(u : G), huN⟩) = 1 := by
      rw [map_mul, map_inv, ← h2]
      exact inv_mul_cancel _
    have h4 := mem_centralizer_of_autBarHom_eq_one Kv hK _ h3
    have hyV : (a' : G)⁻¹ * u ∈ V := V.mul_mem (V.inv_mem haV) u.2
    have hyL : (a' : G)⁻¹ * u ∈ Subgroup.centralizer (Lv L v : Set G) :=
      Subgroup.centralizer_le hLK h4
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (F.β ⟨(a' : G)⁻¹ * u, hyV⟩)
    have hc01 := coord01_of_mem_centralizer h1222 F hH hv hβ hyV hyL hc.symm
    obtain ⟨c', hc', hcc'⟩ := exists_mk_core01_of_coord_eq hc01
    have hyVv : (a' : G)⁻¹ * u ∈ Vv L V v :=
      mem_Vv_of_beta_eq h1222 hH hv hβ hZ hyV hc' (by rw [← hcc', hc])
    have huVv : (u : G) ∈ Vv L V v := by
      have := (Vv L V v).mul_mem ha' hyVv
      simpa using this
    exact hUnot u hu huVv
  obtain ⟨α, hαA, hαs, hαc⟩ := hHS _ eH _ _ _ hD (U.image ψ) hA7 (by
    intro α hα
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hα
    exact ⟨fun e he => hfixE u e he, fun e he => hnotinner u hu e he⟩)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hαA
  have hCT := charTwo_centralizer_singular h1222 hH hZ u.2 (hUwt u hu)
  have hv1 : v ≠ 1 := by
    intro h
    have h1 : F.β ⟨v, hv⟩ = 1 := by
      rw [show (⟨v, hv⟩ : ↥V) = 1 from Subtype.ext h, map_one]
    exact ne_one_of_nonsing nonsing_e01 (hβ.symm.trans h1)
  have hv2 : v ^ 2 = 1 := hVe.2 v hv
  have hCT' := charTwo_inf_centralizer_of_comm hCT (S126L1b.comm_of_mem u.2 hv) hv2 hv1 hKG
    hC.normal
  have hnp : ¬ IsPGroup 2 ↥(perfectCore (autCentralizer (ψ u))) := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hαc] at hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  exact false_of_charTwo_centralizer ⟨(u : G), V_le_normalizer_Kv hC u.2⟩ hαs hnp hCT'

end S126T2

end CFSG.Quasithin.H13
