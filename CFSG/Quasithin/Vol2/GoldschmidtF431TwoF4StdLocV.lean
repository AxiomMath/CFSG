module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocSyl
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLeviWeyl

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique

set_option linter.unusedSectionVars false

section Model


section Defs

variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

@[expose] def Vg : Subgroup (Gm K a) := (S1 K a).subgroupOf (F4.reeGamma K a)

@[expose] def Lg : Subgroup (Gm K a) := (leviN K a .i3).subgroupOf (F4.reeGamma K a)

end Defs

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem add_self_eq_zero_f4 (g : K) : g + g = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact CharTwo.add_self_eq_zero g

theorem rootElt11_mem_sylowP (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : K) :
    rootElt K a .i11 g ∈ F4.reeFixedPosUnipotent K a :=
  rootV_le_sylowP hK .i11 (rootElt_mem_rootV _ _)

theorem rootElt3_mem_sylowP (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : K) :
    rootElt K a .i3 g ∈ F4.reeFixedPosUnipotent K a :=
  rootV_le_sylowP hK .i3 (rootElt_mem_rootV _ _)

theorem commute_rootElt12 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (c : K) :
    u * rootElt K a .i12 c = rootElt K a .i12 c * u := by
  have h := commute_centralZ ha hK hu c
  rw [← sylowH_zero_eq_centralZ] at h
  exact h

theorem exists_eq_of_mem_S1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ S1 K a) : ∃ g i : K, u = rootElt K a .i11 g * rootElt K a .i12 i := by
  have hu' : u ∈ (S1 K a : Set (ModGL F4.tag K)) := hu
  rw [(S1_spec hK).2.1] at hu'
  obtain ⟨x, hx, rfl⟩ := hu'
  refine ⟨x 6, x 8, ?_⟩
  rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 2 (by decide),
    hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 7 (by decide), hx 9 (by decide),
    hx 10 (by decide), hx 11 (by decide)]
  simp only [rootElt_zero, one_mul, mul_one]

theorem rootElt11_mem_S1 (g : K) : rootElt K a .i11 g ∈ S1 K a :=
  rootV_le_rootJoin (by decide) (rootElt_mem_rootV (K := K) (a := a) .i11 g)

theorem rootElt12_mem_S1 (i : K) : rootElt K a .i12 i ∈ S1 K a :=
  rootV_le_rootJoin (by decide) (rootElt_mem_rootV (K := K) (a := a) .i12 i)

theorem mul_mem_S1 (g i : K) : rootElt K a .i11 g * rootElt K a .i12 i ∈ S1 K a :=
  mul_mem (rootElt11_mem_S1 g) (rootElt12_mem_S1 i)

theorem S1_mul (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (g i g' i' : K) :
    (rootElt K a .i11 g * rootElt K a .i12 i) * (rootElt K a .i11 g' * rootElt K a .i12 i') =
      rootElt K a .i11 (g + g') * rootElt K a .i12 (i + i') := by
  rw [rootElt_add hK (i := .i11) (by decide), rootElt_add hK (i := .i12) (by decide)]
  have h := commute_rootElt12 ha hK (rootElt11_mem_sylowP hK g') i
  calc rootElt K a .i11 g * rootElt K a .i12 i *
        (rootElt K a .i11 g' * rootElt K a .i12 i')
      = rootElt K a .i11 g * (rootElt K a .i12 i * rootElt K a .i11 g') *
          rootElt K a .i12 i' := by group
    _ = rootElt K a .i11 g * (rootElt K a .i11 g' * rootElt K a .i12 i) *
          rootElt K a .i12 i' := by rw [h]
    _ = _ := by group

theorem S1_comm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u v : ModGL F4.tag K}
    (hu : u ∈ S1 K a) (hv : v ∈ S1 K a) : u * v = v * u := by
  obtain ⟨g, i, rfl⟩ := exists_eq_of_mem_S1 hK hu
  obtain ⟨g', i', rfl⟩ := exists_eq_of_mem_S1 hK hv
  rw [S1_mul ha hK, S1_mul ha hK, add_comm g, add_comm i]

theorem S1_sq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ S1 K a) : u ^ 2 = 1 := by
  obtain ⟨g, i, rfl⟩ := exists_eq_of_mem_S1 hK hu
  rw [pow_two, S1_mul ha hK, add_self_eq_zero_f4, add_self_eq_zero_f4, rootElt_zero, rootElt_zero,
    one_mul]

theorem invE_mem_S1 : invE K a ∈ S1 K a := rootElt12_mem_S1 1

theorem invE_ne_one (hK : Nat.card K = 2 ^ (2 * a + 1)) : invE K a ≠ 1 := by
  intro h
  have h2 := (invE_invF_mem (a := a) hK).2.2.2.2.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem S1_le_centralizer_invF (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S1 K a ≤ F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} :=
  (S1_le_S2_le_S3_le_S4_le_radS hK).1.trans ((S1_le_S2_le_S3_le_S4_le_radS hK).2.1.trans
    ((S1_le_S2_le_S3_le_S4_le_radS hK).2.2.1.trans (S4_le_centralizer_invF ha hK)))

theorem sylowP_le_normalizer_S1 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ≤ Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) :=
  (S1_spec hK).2.2.2

theorem conj_weylS_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (g i : K) :
    weylS K * (rootElt K a .i11 g * rootElt K a .i12 i) * (weylS K)⁻¹ =
      rootElt K a .i11 i * rootElt K a .i12 g := by
  have h1 := weylS_conj_rootElt (K := K) (a := a) (i := .i11) (by decide) g
  have h2 := weylS_conj_rootElt (K := K) (a := a) (i := .i12) (by decide) i
  have e : weylS K * (rootElt K a .i11 g * rootElt K a .i12 i) * (weylS K)⁻¹ =
      (weylS K * rootElt K a .i11 g * (weylS K)⁻¹) *
        (weylS K * rootElt K a .i12 i * (weylS K)⁻¹) := by group
  rw [e, h1, h2]
  exact (commute_rootElt12 ha hK (rootElt11_mem_sylowP hK i) g).symm

theorem weylS_mem_normalizer_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylS K ∈ Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) := by
  have hs : (weylS K)⁻¹ = weylS K := inv_eq_of_mul_eq_one_right weylS_mul_self
  have key : ∀ x ∈ S1 K a, weylS K * x * (weylS K)⁻¹ ∈ S1 K a := by
    intro x hx
    obtain ⟨g, i, rfl⟩ := exists_eq_of_mem_S1 hK hx
    rw [conj_weylS_S1 ha hK]
    exact mul_mem_S1 _ _
  exact mem_normalizer_of_conj_mem key fun x hx => by rw [hs]; simpa [hs] using key x hx

theorem leviN_three_le_normalizer_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i3 ≤ Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) := by
  rw [leviN_three_eq_closure ha hK, Subgroup.closure_le]
  rintro x (hx | hx)
  · exact sylowP_le_normalizer_S1 hK (rootV_le_sylowP hK .i3 hx)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact weylS_mem_normalizer_S1 ha hK

theorem centralizer_invF_le_normalizer_S1 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} ≤
      Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) := by
  rw [(reeGamma_inf_centralizer_invE_invF ha hK).2.2.1]
  exact sup_le ((rootJoin_le_sylowP hK _).trans (sylowP_le_normalizer_S1 hK))
    (leviN_three_le_normalizer_S1 ha hK)

end Model

end CFSG.Quasithin.H13.F431.TwoF4
