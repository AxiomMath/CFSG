module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocV
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Rel

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fuel comm_famL₂)
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem normal_centralizer_subgroupOf_of_normalizes {G : Type*} [Group G] {X V : Subgroup G}
    (hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) :
    ((Subgroup.centralizer (V : Set G)).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have hv' : (g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹ ∈ V := hVn _ (X.inv_mem g.2) v hv
  have h := hn _ hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc v * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹)) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * v := by group

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem comm_rootElt3_rootElt11 (hK : Nat.card K = 2 ^ (2 * a + 1)) (s t : K) :
    ⁅rootElt K a .i3 s, rootElt K a .i11 t⁆ = rootElt K a .i12 (s * t) := by
  have := comm_famL₂ hK (n := fuel) (i := 0) (j := 6) (by norm_num) (by norm_num)
    (p := [[0]]) (q := [[1]]) (by decide) (by decide) (l := [(8, [[0, 1]])]) (by decide)
    (by decide +kernel) s t
  have h2 : ⁅fam a K 0 s, fam a K 6 t⁆ = fam a K 8 (s * t) := by
    simpa [polyEval, monoEval, coordVal] using this
  exact h2

theorem conj_rootElt3_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c g i : K) :
    rootElt K a .i3 c * (rootElt K a .i11 g * rootElt K a .i12 i) * (rootElt K a .i3 c)⁻¹ =
      rootElt K a .i11 g * rootElt K a .i12 (i + c * g) := by
  have hAF : rootElt K a .i3 c * rootElt K a .i11 g * (rootElt K a .i3 c)⁻¹ =
      rootElt K a .i11 g * rootElt K a .i12 (c * g) := by
    have e1 : rootElt K a .i3 c * rootElt K a .i11 g * (rootElt K a .i3 c)⁻¹ =
        ⁅rootElt K a .i3 c, rootElt K a .i11 g⁆ * rootElt K a .i11 g := by
      rw [commutatorElement_def]
      group
    rw [e1, comm_rootElt3_rootElt11 hK]
    exact (commute_rootElt12 ha hK (rootElt11_mem_sylowP hK g) (c * g)).symm
  have hAH : rootElt K a .i3 c * rootElt K a .i12 i * (rootElt K a .i3 c)⁻¹ =
      rootElt K a .i12 i := by
    rw [commute_rootElt12 ha hK (rootElt3_mem_sylowP hK c) i]
    group
  have e : rootElt K a .i3 c * (rootElt K a .i11 g * rootElt K a .i12 i) *
      (rootElt K a .i3 c)⁻¹ = (rootElt K a .i3 c * rootElt K a .i11 g * (rootElt K a .i3 c)⁻¹) *
        (rootElt K a .i3 c * rootElt K a .i12 i * (rootElt K a .i3 c)⁻¹) := by group
  rw [e, hAF, hAH, mul_assoc, ← rootElt_add hK (i := .i12) (by decide), add_comm]

theorem rootElt3_mem_leviN (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    rootElt K a .i3 c ∈ leviN K a .i3 :=
  rootV_le_leviN hK .i3 (rootElt_mem_rootV (K := K) (a := a) .i3 c)

theorem exists_conj_invE_leviN (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ModGL F4.tag K} (hu : u ∈ S1 K a) (hu1 : u ≠ 1) :
    ∃ x ∈ leviN K a .i3, u = x * invE K a * x⁻¹ := by
  obtain ⟨g, i, rfl⟩ := exists_eq_of_mem_S1 hK hu
  have hs : weylS K ∈ leviN K a .i3 := weylS_mem_leviN
  have he : invE K a = rootElt K a .i11 0 * rootElt K a .i12 1 := by
    rw [rootElt_zero, one_mul]
    rfl
  have h11 : (1 : K) + 1 = 0 := add_self_eq_zero_f4 1
  have e1 := conj_weylS_S1 ha hK 0 1
  by_cases hg : g = 0
  · subst hg
    have hi : i ≠ 0 := fun h => hu1 (by rw [h, rootElt_zero, rootElt_zero, one_mul])
    refine ⟨weylS K * rootElt K a .i3 i⁻¹ * weylS K * rootElt K a .i3 i * weylS K,
      mul_mem (mul_mem (mul_mem (mul_mem hs (rootElt3_mem_leviN hK _)) hs)
        (rootElt3_mem_leviN hK _)) hs, ?_⟩
    have e2 : rootElt K a .i3 i * (rootElt K a .i11 1 * rootElt K a .i12 0) *
        (rootElt K a .i3 i)⁻¹ = rootElt K a .i11 1 * rootElt K a .i12 i := by
      rw [conj_rootElt3_S1 ha hK i 1 0, zero_add, mul_one]
    have e3 := conj_weylS_S1 ha hK 1 i
    have e4 : rootElt K a .i3 i⁻¹ * (rootElt K a .i11 i * rootElt K a .i12 1) *
        (rootElt K a .i3 i⁻¹)⁻¹ = rootElt K a .i11 i * rootElt K a .i12 0 := by
      rw [conj_rootElt3_S1 ha hK i⁻¹ i 1, inv_mul_cancel₀ hi, h11]
    have e5 := conj_weylS_S1 ha hK i 0
    rw [he]
    calc rootElt K a .i11 0 * rootElt K a .i12 i
        = weylS K * (rootElt K a .i11 i * rootElt K a .i12 0) * (weylS K)⁻¹ := by
          rw [e5]
      _ = weylS K * (rootElt K a .i3 i⁻¹ * (rootElt K a .i11 i * rootElt K a .i12 1) *
          (rootElt K a .i3 i⁻¹)⁻¹) * (weylS K)⁻¹ := by rw [e4]
      _ = weylS K * (rootElt K a .i3 i⁻¹ * (weylS K * (rootElt K a .i11 1 *
          rootElt K a .i12 i) * (weylS K)⁻¹) * (rootElt K a .i3 i⁻¹)⁻¹) * (weylS K)⁻¹ := by
          rw [e3]
      _ = weylS K * (rootElt K a .i3 i⁻¹ * (weylS K * (rootElt K a .i3 i *
          (rootElt K a .i11 1 * rootElt K a .i12 0) * (rootElt K a .i3 i)⁻¹) * (weylS K)⁻¹) *
          (rootElt K a .i3 i⁻¹)⁻¹) * (weylS K)⁻¹ := by rw [e2]
      _ = _ := by rw [← e1]; group
  · set c := (i + 1) / g with hcdef
    have hc : c * g = i + 1 := div_mul_cancel₀ _ hg
    refine ⟨rootElt K a .i3 c * weylS K * rootElt K a .i3 g * weylS K,
      mul_mem (mul_mem (mul_mem (rootElt3_mem_leviN hK _) hs) (rootElt3_mem_leviN hK _)) hs, ?_⟩
    have e2 : rootElt K a .i3 g * (rootElt K a .i11 1 * rootElt K a .i12 0) *
        (rootElt K a .i3 g)⁻¹ = rootElt K a .i11 1 * rootElt K a .i12 g := by
      rw [conj_rootElt3_S1 ha hK g 1 0, zero_add, mul_one]
    have e3 := conj_weylS_S1 ha hK 1 g
    have hi' : (1 : K) + c * g = i := by
      rw [hc]
      calc (1 : K) + (i + 1) = i + (1 + 1) := by ring
        _ = i := by rw [h11, add_zero]
    have e4 : rootElt K a .i3 c * (rootElt K a .i11 g * rootElt K a .i12 1) *
        (rootElt K a .i3 c)⁻¹ = rootElt K a .i11 g * rootElt K a .i12 i := by
      rw [conj_rootElt3_S1 ha hK c g 1, hi']
    rw [he]
    calc rootElt K a .i11 g * rootElt K a .i12 i
        = rootElt K a .i3 c * (rootElt K a .i11 g * rootElt K a .i12 1) *
          (rootElt K a .i3 c)⁻¹ := e4.symm
      _ = rootElt K a .i3 c * (weylS K * (rootElt K a .i11 1 * rootElt K a .i12 g) *
          (weylS K)⁻¹) * (rootElt K a .i3 c)⁻¹ := by rw [e3]
      _ = rootElt K a .i3 c * (weylS K * (rootElt K a .i3 g *
          (rootElt K a .i11 1 * rootElt K a .i12 0) * (rootElt K a .i3 g)⁻¹) *
          (weylS K)⁻¹) * (rootElt K a .i3 c)⁻¹ := by rw [e2]
      _ = _ := by rw [← e1]; group

theorem rootElt_one_ne_of_ne (hK : Nat.card K = 2 ^ (2 * a + 1)) {i j : Idx} (hij : i ≠ j) :
    rootElt K a i 1 ≠ rootElt K a j 1 := by
  intro h
  rw [rootElt_eq_sylowVec, rootElt_eq_sylowVec] at h
  have h' := congrFun ((bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h) i.coord
  rw [Pi.single_eq_same, Pi.single_apply, ite_eq_right (fun hc => hij
    (by rw [← Idx.ofCoord_coord i, hc, Idx.ofCoord_coord]))] at h'
  exact one_ne_zero h'

theorem leviN_three_inf_centralizer_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i3 ⊓ Subgroup.centralizer (S1 K a : Set (ModGL F4.tag K)) = ⊥ := by
  obtain ⟨hsimp, -⟩ := isSimpleGroup_leviN ha hK .i3
  have hnorm := normal_centralizer_subgroupOf_of_normalizes (X := leviN K a .i3) (V := S1 K a)
    (fun x hx v hv => (Subgroup.mem_normalizer_iff.1 (leviN_three_le_normalizer_S1 ha hK hx) v).1
      hv)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Subgroup.centralizer (S1 K a : Set (ModGL F4.tag K))).subgroupOf (leviN K a .i3)) with h | h
  · refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (⟨x, hx.1⟩ : leviN K a .i3) ∈
        (Subgroup.centralizer (S1 K a : Set (ModGL F4.tag K))).subgroupOf (leviN K a .i3) := hx.2
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  · exfalso
    have hs : (⟨weylS K, weylS_mem_leviN⟩ : leviN K a .i3) ∈
        (Subgroup.centralizer (S1 K a : Set (ModGL F4.tag K))).subgroupOf (leviN K a .i3) :=
      h ▸ Subgroup.mem_top _
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hs) (invE K a)
      (invE_mem_S1)
    have e1 := conj_weylS_S1 ha hK 0 1
    rw [rootElt_zero, rootElt_zero, one_mul, mul_one] at e1
    have e2 : weylS K * rootElt K a .i12 1 * (weylS K)⁻¹ = rootElt K a .i12 1 := by
      calc weylS K * rootElt K a .i12 1 * (weylS K)⁻¹ = (weylS K * invE K a) * (weylS K)⁻¹ := rfl
        _ = (invE K a * weylS K) * (weylS K)⁻¹ := by rw [← hc]
        _ = invE K a := by group
    exact rootElt_one_ne_of_ne hK (by decide : Idx.i11 ≠ Idx.i12) (e1.symm.trans e2)

end Model

end CFSG.Quasithin.H13.F431.TwoF4
