module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocVz
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique

set_option linter.unusedSectionVars false

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem comm_zg_tg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    zg hK * tg hK = tg hK * zg hK := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zg, coe_tg]
  exact (commute_invE ha hK (invE_invF_mem hK).2.2.2.1).symm

theorem Vg_le_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Vg K a ≤ Subgroup.centralizer ({tg hK} : Set (Gm K a)) := by
  intro v hv
  have hv' : (v : ModGL F4.tag K) ∈ S1 K a := hv
  rw [mem_centralizer_tg hK]
  exact (S1_le_centralizer_invF ha hK hv').2

theorem Vg_comm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ Vg K a, ∀ y ∈ Vg K a, x * y = y * x := by
  intro x hx y hy
  have hx' : (x : ModGL F4.tag K) ∈ S1 K a := hx
  have hy' : (y : ModGL F4.tag K) ∈ S1 K a := hy
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact S1_comm ha hK hx' hy'

theorem Vg_sq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ Vg K a, x ^ 2 = 1 := by
  intro x hx
  have hx' : (x : ModGL F4.tag K) ∈ S1 K a := hx
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact S1_sq ha hK hx'

theorem zg_mem_Vg (hK : Nat.card K = 2 ^ (2 * a + 1)) : zg hK ∈ Vg K a := by
  show ((zg hK : Gm K a) : ModGL F4.tag K) ∈ S1 K a
  rw [coe_zg]
  exact invE_mem_S1

theorem Vg_ne_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) : Vg K a ≠ ⊥ := by
  intro h
  have hz := zg_mem_Vg (a := a) hK
  rw [h, Subgroup.mem_bot] at hz
  have h2 := congrArg Subtype.val hz
  rw [coe_zg, Subgroup.coe_one] at h2
  exact invE_ne_one hK h2

theorem Vg_conj_zg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ v ∈ Vg K a, v ≠ 1 →
      ∃ x ∈ Subgroup.centralizer ({tg hK} : Set (Gm K a)), v = x * zg hK * x⁻¹ := by
  intro v hv hv1
  have hv' : (v : ModGL F4.tag K) ∈ S1 K a := hv
  have hne : (v : ModGL F4.tag K) ≠ 1 := fun h => hv1 (Subtype.ext (by rw [h, Subgroup.coe_one]))
  obtain ⟨x, hxN, hx⟩ := exists_conj_invE_leviN ha hK hv' hne
  refine ⟨⟨x, leviN_le_reeGamma hK .i3 hxN⟩, ?_, Subtype.ext ?_⟩
  · rw [mem_centralizer_tg hK]
    exact (leviN_three_le_centralizer_invF ha hK hxN).2
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zg]
    exact hx

theorem Lg_le_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Lg K a ≤ Subgroup.centralizer ({tg hK} : Set (Gm K a)) := by
  intro l hl
  have hl' : (l : ModGL F4.tag K) ∈ leviN K a .i3 := hl
  rw [mem_centralizer_tg hK]
  exact (leviN_three_le_centralizer_invF ha hK hl').2

theorem not_isSolvable_Lg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ Group.IsSolvable ↥(Lg K a) := by
  intro h
  obtain ⟨hs, x, y, hxy⟩ := isSimpleGroup_leviN ha hK .i3
  have e := Subgroup.subgroupOfEquivOfLe (leviN_le_reeGamma (K := K) (a := a) hK .i3)
  have h' : Group.IsSolvable ↥((leviN K a .i3).subgroupOf (F4.reeGamma K a)) := h
  have : Group.IsSolvable ↥(leviN K a .i3) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := ↥(leviN K a .i3))).2 this x y)

theorem isSolvable_Lg_inf_centralizer_Vg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Group.IsSolvable ↥(Lg K a ⊓ Subgroup.centralizer (Vg K a : Set (Gm K a))) := by
  have key : ∀ x : Gm K a, x ∈ Lg K a ⊓ Subgroup.centralizer (Vg K a : Set (Gm K a)) →
      x = 1 := by
    intro x hx
    have hxL : (x : ModGL F4.tag K) ∈ leviN K a .i3 := hx.1
    have hxC : (x : ModGL F4.tag K) ∈ Subgroup.centralizer (S1 K a : Set (ModGL F4.tag K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have huΓ : u ∈ F4.reeGamma K a :=
        reeFixedPosUnipotent_le_reeGamma (t := F4) (K := K) (a := a)
          (rootJoin_le_sylowP hK _ hu)
      have hu' : (⟨u, huΓ⟩ : Gm K a) ∈ Vg K a := hu
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx.2 ⟨u, huΓ⟩ hu')
    have hx1 : (x : ModGL F4.tag K) ∈ (⊥ : Subgroup (ModGL F4.tag K)) := by
      rw [← leviN_three_inf_centralizer_S1 ha hK]
      exact Subgroup.mem_inf.2 ⟨hxL, hxC⟩
    exact Subtype.ext (Subgroup.mem_bot.1 hx1)
  refine Group.isSolvable_of_comm (fun x y => ?_)
  have hx := key x.1 x.2
  have hy := key y.1 y.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, one_mul]

theorem f4_stdLoc (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Quasithin.H13.F431.Lift.StdLoc (Gm K a) (Ug K a) (zg hK) (tg hK) (Vg K a) (Lg K a) :=
  ⟨comm_zg_tg ha hK, sylow_tg ha hK, Vg_le_centralizer ha hK, Vg_comm ha hK, Vg_sq ha hK,
    Vg_ne_bot hK, stabilizes_Vg ha hK, Vg_conj_zg ha hK, Lg_le_centralizer ha hK,
    not_isSolvable_Lg ha hK, isSolvable_Lg_inf_centralizer_Vg ha hK⟩

end Model

end CFSG.Quasithin.H13.F431.TwoF4
