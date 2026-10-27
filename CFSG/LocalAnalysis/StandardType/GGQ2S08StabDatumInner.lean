module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CenterThree
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08x1c_centralizer_three_mem_zpowers {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G)) (hcx : c * x = x * c) (h3 : c ^ 3 = 1) :
    c ∈ Subgroup.zpowers x := by
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hS.1.1.tableB_facts
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hBs.2 x hxB
  have hcomm : ∀ a ∈ ({x, c} : Set G), ∀ b ∈ ({x, c} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · simp only [Set.mem_singleton_iff] at hb; subst hb; exact hcx.symm
    · simp only [Set.mem_singleton_iff] at ha; subst ha; exact hcx
    · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  let E : Subgroup G := Subgroup.closure ({x, c} : Set G)
  have hP1 : ∀ a ∈ E, ∀ y ∈ ({x, c} : Set G), a * y = y * a := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem z hz => intro y hy; exact hcomm z hz y hy
    | one => intro y hy; simp
    | mul a b ha hb iha ihb =>
      intro y hy
      rw [mul_assoc, ihb y hy, ← mul_assoc, iha y hy, mul_assoc]
    | inv a ha iha =>
      intro y hy
      have h := iha y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [h]
        _ = y * a⁻¹ := by group
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem z hz => exact hP1 a ha z hz
    | one => simp
    | mul b1 b2 hb1 hb2 ih1 ih2 =>
      rw [← mul_assoc, ih1, mul_assoc, ih2, mul_assoc]
    | inv b hb ihb =>
      have h := ihb
      calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
        _ = b⁻¹ * (a * b) * b⁻¹ := by rw [← h]
        _ = b⁻¹ * a := by group
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact hx3
      · simp only [Set.mem_singleton_iff] at hy; subst hy; exact h3
    | one => exact one_pow _
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := hEc a ha b hb
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  haveI : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hEc a.1 a.2 b.1 b.2)⟩⟩
  have hEel : CFSG.Open.IsElemAbelian 3 E := ⟨this, hE3⟩
  have hxE : x ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hcE : c ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hx1 : x ≠ 1 := hSS.2.2.1
  have hcyc := hSS.2.2.2.2
  have hEL := inf_centralizer_eq_zpowers_of_elemAbelian hp hEel hxE hx1 hLx hcyc
  rw [← hEL]
  exact ⟨hcE, hc⟩

private theorem ggQ2s08x1c_center_eq_one_of_not_mem {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxL : x ∉ L) (z : ↥L) (hz : z ∈ Subgroup.center ↥L) (h3 : z ^ 3 = 1) : z = 1 := by
  by_contra hz1
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hS.1.1.tableB_facts
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hzG : (z : G) ∈ Subgroup.zpowers x := ggQ2s08_center_three_mem hS z hz h3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hx3 : x ^ 3 = 1 := hBs.2 x hxB
  have hx1 : x ≠ 1 := hSS.2.2.1
  have hz3 : (z : G) ^ 3 = 1 := by
    have := congrArg Subtype.val h3
    simpa using this
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzord : orderOf (z : G) = 3 := orderOf_eq_prime hz3 hzG1
  have hz_le : Subgroup.zpowers (z : G) ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hzG
  have heq : Subgroup.zpowers (z : G) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hz_le
      (by rw [Nat.card_zpowers, hxord, Nat.card_zpowers, hzord])
  have hxmem : x ∈ Subgroup.zpowers (z : G) := heq ▸ Subgroup.mem_zpowers x
  exact hxL (Subgroup.zpowers_le.mpr z.2 hxmem)

theorem ggQ2s08x1p_inner_of_not_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) :
    ∀ b ∈ Bs, (∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), (b : G) = l * c) →
      (b : G) ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
  intro b hb hbc
  obtain ⟨l, hl, c, hc, hbc⟩ := hbc
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hS.1.1.tableB_facts
  have hb3 : b ^ 3 = 1 := hBs.2 b hb
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  have hcomm_lc : Commute l c := hlc
  have hbc3 : (l * c) ^ 3 = 1 := by rw [← hbc]; exact hb3
  have h1 : l ^ 3 * c ^ 3 = 1 := by
    rw [← hcomm_lc.mul_pow 3]; exact hbc3
  have hz_eq : l ^ 3 = (c⁻¹) ^ 3 := by
    rw [eq_inv_of_mul_eq_one_left h1, inv_pow]
  have hzL : l ^ 3 ∈ L := L.pow_mem hl 3
  have hzcent : l ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
    rw [hz_eq]
    exact (Subgroup.centralizer (L : Set G)).pow_mem (Subgroup.inv_mem _ hc) 3
  let zL : ↥L := ⟨l ^ 3, hzL⟩
  have hzLcenter : zL ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzcent (y : G) y.2)
  have hcx : c * x = x * c := by
    have hlx : l⁻¹ * x = x * l⁻¹ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
      calc l⁻¹ * x = l⁻¹ * (x * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * x) * l⁻¹ := by rw [h]
        _ = x * l⁻¹ := by group
    have hbx : b * x = x * b := by
      have h := hBs.1.is_comm.comm (⟨b, hb⟩ : ↥Bs) (⟨x, hxB⟩ : ↥Bs)
      exact congrArg Subtype.val h
    have hc_eq : c = l⁻¹ * b := by rw [hbc]; group
    rw [hc_eq]
    calc (l⁻¹ * b) * x = l⁻¹ * (b * x) := by group
      _ = l⁻¹ * (x * b) := by rw [hbx]
      _ = (l⁻¹ * x) * b := by group
      _ = (x * l⁻¹) * b := by rw [hlx]
      _ = x * (l⁻¹ * b) := by group
  set m : ℕ := orderOf (l ^ 3 : G) with hm
  have hmpos : 0 < m := by rw [hm]; exact orderOf_pos (l ^ 3 : G)
  have h3m : ¬ 3 ∣ m := by
    intro hdiv
    have hk3 : 3 * (m / 3) = m := Nat.mul_div_cancel' hdiv
    let wL : ↥L := zL ^ (m / 3)
    have hwcenter : wL ∈ Subgroup.center ↥L := Subgroup.pow_mem _ hzLcenter (m / 3)
    have hw3 : wL ^ 3 = 1 := by
      apply Subtype.ext
      have hpow : (l ^ 3 : G) ^ ((m / 3) * 3) = 1 := by
        rw [Nat.mul_comm (m / 3) 3, hk3, hm]
        exact pow_orderOf_eq_one (l ^ 3 : G)
      simpa [wL, zL, pow_mul] using hpow
    have hw1 : wL = 1 := ggQ2s08x1c_center_eq_one_of_not_mem hS hxL wL hwcenter hw3
    have hk1 : (l ^ 3 : G) ^ (m / 3) = 1 := by
      have := congrArg Subtype.val hw1
      simpa [wL, zL] using this
    have hdvd : m ∣ m / 3 := orderOf_dvd_iff_pow_eq_one.mpr hk1
    have hkpos : 0 < m / 3 := by omega
    have hle : m ≤ m / 3 := Nat.le_of_dvd hkpos hdvd
    omega
  have hmmod : m % 3 = 1 ∨ m % 3 = 2 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : m % 3 ≠ 0 := fun h => h3m (Nat.dvd_of_mod_eq_zero h)
    omega
  have hmm : (m * m) % 3 = 1 := by
    rcases hmmod with h | h <;> rw [Nat.mul_mod, h] <;> norm_num
  have hbmm : b ^ (m * m) = b := by
    have hsplit : m * m = 3 * (m * m / 3) + 1 := by
      have := Nat.div_add_mod (m * m) 3
      omega
    rw [hsplit, pow_add, pow_mul, hb3, one_pow, one_mul, pow_one]
  have hcxm : c ^ m * x = x * c ^ m := (show Commute c x from hcx).pow_left m
  have hbm3 : (b ^ m) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 3, pow_mul, hb3, one_pow]
  have hbm_lcm : b ^ m = l ^ m * c ^ m := by
    simpa [hbc] using hcomm_lc.mul_pow m
  have hlm3 : (l ^ m) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 3, pow_mul, hm]
    exact pow_orderOf_eq_one (l ^ 3 : G)
  have hc3 : (c ^ m) ^ 3 = 1 := by
    have hcomm_lcm : Commute (l ^ m) (c ^ m) := (hcomm_lc.pow_left m).pow_right m
    have h1' : (b ^ m) ^ 3 = (l ^ m) ^ 3 * (c ^ m) ^ 3 := by
      rw [hbm_lcm, hcomm_lcm.mul_pow]
    rw [h1', hlm3, one_mul] at hbm3
    exact hbm3
  have hcm : c ^ m ∈ Subgroup.zpowers x :=
    ggQ2s08x1c_centralizer_three_mem_zpowers hS (Subgroup.pow_mem _ hc m) hcxm hc3
  have hcm_bs : c ^ m ∈ Bs := Subgroup.zpowers_le.mpr hxB hcm
  have hbm_bs : b ^ m ∈ Bs := Bs.pow_mem hb m
  have hlm_eq : l ^ m = b ^ m * (c ^ m)⁻¹ := by
    rw [hbm_lcm]; group
  have hlm_bs : l ^ m ∈ Bs := by
    rw [hlm_eq]
    exact Bs.mul_mem hbm_bs (Subgroup.inv_mem Bs hcm_bs)
  have hlm_mem : l ^ m ∈ Bs ⊓ L :=
    Subgroup.mem_inf.mpr ⟨hlm_bs, L.pow_mem hl m⟩
  have hbm_mem : b ^ m ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
    rw [hbm_lcm]
    exact Subgroup.mul_mem_sup hlm_mem hcm
  have hb_eq : b = (b ^ m) ^ m := by
    rw [← pow_mul]
    exact hbmm.symm
  rw [hb_eq]
  exact Subgroup.pow_mem _ hbm_mem m

theorem ggQ2s08x1p_inner_of_cover {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    (hcov : M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} = ⊤) :
    ∀ b ∈ Bs, (b : G) ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
  intro b hb
  have hBs : IsElemAbelian 3 Bs := hS.1.1.tableB_facts.2.1
  set K : Subgroup G := (Bs ⊓ L) ⊔ Subgroup.zpowers x with hK
  let K' : Subgroup ↥Bs := K.subgroupOf Bs
  set S : Submodule (ZMod 3) M.V :=
    AddSubgroup.toZModSubmodule 3
      ((Subgroup.toAddSubgroup K').map M.model.toAddMonoidHom) with hSdef
  have hcoroot : ∀ i : M.Λ, M.coroot i ∈ S := by
    intro i
    rw [hSdef]
    change M.coroot i ∈ (Subgroup.toAddSubgroup K').map M.model.toAddMonoidHom
    rw [AddSubgroup.mem_map]
    refine ⟨Additive.ofMul (ggQ2s08x1_h M i), ?_, ?_⟩
    · show Additive.toMul (Additive.ofMul (ggQ2s08x1_h M i)) ∈ K'
      rw [toMul_ofMul, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left
        (Subgroup.mem_inf.mpr ⟨(ggQ2s08x1_h M i).2, ggQ2s08x1_h_mem_L hS hBsN M i⟩)
    · exact ggQ2s08x1_h_model M i
  have hxV : M.xV ∈ S := by
    rw [hSdef]
    change M.xV ∈ (Subgroup.toAddSubgroup K').map M.model.toAddMonoidHom
    rw [AddSubgroup.mem_map]
    refine ⟨Additive.ofMul (⟨x, M.hx⟩ : ↥Bs), ?_, ?_⟩
    · show Additive.toMul (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) ∈ K'
      rw [toMul_ofMul, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · rfl
  have hcoSpan : M.coSpan ≤ S := by
    rw [GGQ2LDatum.coSpan, Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact hcoroot i
  have hxspan : Submodule.span (ZMod 3) {M.xV} ≤ S := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact hxV
  have htop : S = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hcov]
    exact sup_le hcoSpan hxspan
  have hbS : M.model (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈ S := by
    rw [htop]
    exact Submodule.mem_top
  rw [hSdef] at hbS
  change M.model (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈
    (Subgroup.toAddSubgroup K').map M.model.toAddMonoidHom at hbS
  rw [AddSubgroup.mem_map] at hbS
  obtain ⟨y, hy, hyeq⟩ := hbS
  have hyK' : Additive.toMul y ∈ K' := hy
  rw [Subgroup.mem_subgroupOf] at hyK'
  have hy' : y = Additive.ofMul (⟨b, hb⟩ : ↥Bs) := M.model.injective hyeq
  rw [hy', toMul_ofMul] at hyK'
  exact hyK'

end CFSG.StandardType

end
