module

public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.EmptyFaithful.S146zYFSJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem desc_j2
    (G : Type) [Group G] [Finite G] (L T B : Subgroup G)
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (hne : B ≠ L)
    (hJ : IsSporadic .J2 ↥L)
    (hext : IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y)) :
    ∃ z : G, IsTwoCentralInvolution L z ∧ B = L ⊓ Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hJ
  have : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLc : Nat.card ↥L = 604800 := (Nat.card_congr eL.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hTL := hT.1
  obtain ⟨V, hVn, ⟨hVx, hVc⟩, hA⟩ := hext
  have hBc : Nat.card B = 1920 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [A314.card_isAlt_five hA, hVc] at h1
    norm_num at h1
    exact h1
  have hTc : Nat.card T = 128 := by
    have h1 := CFSG.QuasithinUnique.A5.G3.card_eq_of_odd_index (U := T.subgroupOf L) (k := 7)
      (m := 4725) (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm) hT.2.2
      (hLc.trans (by norm_num)) (by decide)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv] at h1
    exact h1.trans (by norm_num)
  have hX := sup_ne_of_isSimpleGroup hB hBL hne hLs
  have hXT : T.subgroupOf L ≤ (B ⊔ T).subgroupOf L := Subgroup.subgroupOf_mono L le_sup_right
  have hXc : Nat.card ↥(B ⊔ T) = 1920 := by
    have hd := card_dvd_sup B T
    rw [hBc] at hd
    rcases CFSG.Quasithin.S146zY.j2_overgroups ⟨eL⟩ (isSylowTwoOf_top_subgroupOf hT) hXT with
      htop | h | h | h | h
    · exact absurd (le_antisymm (sup_le hBL hTL) (Subgroup.subgroupOf_eq_top.mp htop)) hX
    all_goals rw [card_sup_subgroupOf hBL hTL] at h
    all_goals rw [h] at hd ⊢
    · exact absurd hd (by decide)
    · exact absurd hd (by decide)
    · exact absurd hd (by decide)
    · norm_num
  have hBX : B = B ⊔ T := Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [hXc, hBc]))
  have hTB : T ≤ B := hBX ▸ le_sup_right
  have : CFSG.IsExtraspecial 2 ↥V := hVx
  have hZ2 : Nat.card (Subgroup.center V) = 2 := CFSG.IsExtraspecial.center_order_p 2 ↥V
  obtain ⟨w, hw1, hwu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center V)).mp hZ2
  set z : G := (((w : V) : B) : G) with hzdef
  have hzB : z ∈ B := ((w : V) : B).2
  have hzc : ∀ b ∈ B, b * z = z * b := by
    intro b hb
    have h1 := conj_mem_center_of_normal (⟨b, hb⟩ : B) w.2
    have hne1 : (⟨_, h1⟩ : Subgroup.center V) ≠ 1 := by
      intro h2
      apply hw1
      have h3 : (⟨b, hb⟩ : B) * ((w : V) : B) * (⟨b, hb⟩ : B)⁻¹ = 1 := by
        have := congrArg (fun u : Subgroup.center V => ((u : V) : B)) h2
        simpa using this
      have h4 : ((w : V) : B) = 1 := by
        calc ((w : V) : B) = (⟨b, hb⟩ : B)⁻¹ * ((⟨b, hb⟩ : B) * ((w : V) : B) *
              (⟨b, hb⟩ : B)⁻¹) * ⟨b, hb⟩ := by group
          _ = 1 := by rw [h3]; group
      exact Subtype.ext (Subtype.ext (by simpa using h4))
    have h5 := hwu _ hne1
    have h6 := congrArg (fun u : Subgroup.center V => (((u : V) : B) : G)) h5
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h6
    calc b * z = b * z * b⁻¹ * b := by group
      _ = z * b := by rw [h6]
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf w = 2 := by
      have := orderOf_dvd_natCard w
      rw [hZ2] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h1]
  have hzT : z ∈ T := by
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 5) (hVc.trans (by norm_num))
    have hTi : ¬ 2 ∣ (T.subgroupOf B).index := by
      have h1 := Subgroup.card_mul_index (T.subgroupOf B)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, hTc, hBc] at h1
      have h2 : (T.subgroupOf B).index = 15 := by omega
      rw [h2]
      decide
    have hT2 : IsPGroup 2 (T.subgroupOf B) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTB).symm
    have hVT := hV2.le_sylow_of_normal (hT2.toSylow hTi)
    exact Subgroup.mem_subgroupOf.mp (hVT (w : V).2)
  refine ⟨z, ⟨hBL hzB, hz2, T, hT, hzT, fun s hs => (hzc s (hTB hs))⟩, ?_⟩
  have hle : B ≤ L ⊓ Subgroup.centralizer ({z} : Set G) := fun b hb =>
    ⟨hBL hb, Subgroup.mem_centralizer_singleton_iff.mpr (hzc b hb)⟩
  have hTC : T.subgroupOf L ≤ (L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L :=
    Subgroup.subgroupOf_mono L (hTB.trans hle)
  have hCL : Nat.card ↥((L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L) =
      Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  refine eq_inf_centralizer_of_card hle ?_
  rcases CFSG.Quasithin.S146zY.j2_overgroups ⟨eL⟩ (isSylowTwoOf_top_subgroupOf hT) hTC with
    htop | h | h | h | h
  ·
    exfalso
    have hzL : (⟨z, hBL hzB⟩ : L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h0 : g ∈ (L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf L := by
        rw [htop]
        exact Subgroup.mem_top g
      have h1 : (g : G) ∈ L ⊓ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_subgroupOf.mp h0
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h1.2)
    have hc : Subgroup.center ↥L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hc | hc
      · exact hc
      · exfalso
        have : IsMulCommutative ↥L := Subgroup.center_eq_top_iff.mp hc
        have hp := Group.is_simple_iff_prime_card.mp hLs
        rw [hLc] at hp
        rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> omega
    rw [hc, Subgroup.mem_bot] at hzL
    have : z = 1 := congrArg Subtype.val hzL
    rw [this, orderOf_one] at hz2
    omega
  all_goals rw [← hCL, h, hBc]
  all_goals norm_num

end CFSG.Quasithin.H13.NQCat.A314D
