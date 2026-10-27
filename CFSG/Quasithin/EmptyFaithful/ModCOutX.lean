module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin.ModC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem out_contradiction {T M H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hTu : T ⊓ I = tU T u)
    {x : G} (hxU : x ∈ conjClosure (VZ T M) H) (hx1 : x ≠ 1) (hxu : x * u ≠ 1)
    (hxT : ∀ g ∈ tU T u, g * x * g⁻¹ = x)
    {J : Subgroup G} (hJI : J ≤ I) (hJx : ∀ j ∈ J, j * x * j⁻¹ = x)
    (hJM : ¬ J ≤ M) (hJG : ¬ J ≤ mcOf T) : False := by
  classical
  have S : Setting146 G T M := c.setting
  have hH : IsHTM T M H := c.hH
  have hu : IsInvU T M H u := c.hu
  have hI : IsIStar T M u I := c.hI
  have hIu : I ≤ Subgroup.centralizer ({u} : Set G) := c.cent hTu
  have hZ2 : ∀ a ∈ quasithinOmegaOneCenter T, a * a = 1 := fun a ha => by
    rw [← sq]; exact S146T.Z_sq ha
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have huU : u ∈ conjClosure (VZ T M) H := hu.mem
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH huU
  have hxG : x ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hxU
  obtain ⟨t₀, ht₀T0, ht₀n, ht₀⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (S.relIndex_tU_tZero hH hu)
  have ht₀T : t₀ ∈ T := S146T.tZero_le T u ht₀T0
  have hT0eq : tZero T u = pCoreOf 2 H ⊔ tU T u := S.tZero_eq_sup_pCoreOf hH hu
  have hTuH : tU T u ≤ H := (inf_le_left.trans hH.1.1)
  have hTuN : tU T u ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hTuH.trans (le_normalizer_pCoreOf 2 H)
  have ht₀mem : t₀ ∈ ((pCoreOf 2 H ⊔ tU T u : Subgroup G) : Set G) := hT0eq ▸ ht₀T0
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTuN] at ht₀mem
  obtain ⟨q, hq, s, hs, hqs⟩ := ht₀mem
  have hc : ∀ y ∈ conjClosure (VZ T M) H, (∀ g ∈ tU T u, g * y * g⁻¹ = y) →
      ⁅t₀, y⁆ ∈ quasithinOmegaOneCenter T := by
    intro y hy hyT
    have hs1 : ⁅s, y⁆ = 1 := by
      have := hyT s hs
      simp only [commutatorElement_def]
      rw [this]; group
    rw [← hqs, S146T.comm_mul_left, hs1]
    have : q * (1 : G) * q⁻¹ = 1 := by group
    rw [this, one_mul]
    exact S.comm_mem_Z hH hy hq
  have huT : ∀ g ∈ tU T u, g * u * g⁻¹ = u := fun g hg => by
    have := (S146T.mem_tU_iff.mp hg).2
    rw [commutatorElement_def] at this
    calc g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
      _ = u := by rw [this, one_mul]
  have hcu : ⁅t₀, u⁆ ∈ quasithinOmegaOneCenter T := hc u huU huT
  have hcu1 : ⁅t₀, u⁆ ≠ 1 := fun h => ht₀n (S146T.mem_tU_iff.mpr ⟨ht₀T, h⟩)
  have hcx : ⁅t₀, x⁆ ∈ quasithinOmegaOneCenter T := hc x hxU hxT
  have hJu : ∀ j ∈ J, j * u * j⁻¹ = u := fun j hj => by
    have h := Subgroup.mem_centralizer_iff.mp (hIu (hJI hj)) u rfl
    calc j * u * j⁻¹ = (u * j) * j⁻¹ := by rw [h]
      _ = u := by group
  obtain ⟨v, hvU, hv1, hvT, hvt, hvJ⟩ : ∃ v ∈ conjClosure (VZ T M) H, v ≠ 1 ∧
      (∀ g ∈ tU T u, g * v * g⁻¹ = v) ∧ t₀ * v * t₀⁻¹ = v ∧ (∀ j ∈ J, j * v * j⁻¹ = v) := by
    by_cases hcx1 : ⁅t₀, x⁆ = 1
    · refine ⟨x, hxU, hx1, hxT, ?_, hJx⟩
      have h := S146T.comm_eq_one_iff.mp hcx1
      calc t₀ * x * t₀⁻¹ = (x * t₀) * t₀⁻¹ := by rw [h]
        _ = x := by group
    · refine ⟨x * u, (conjClosure (VZ T M) H).mul_mem hxU huU, hxu, fun g hg => ?_, ?_, fun j hj => ?_⟩
      · calc g * (x * u) * g⁻¹ = (g * x * g⁻¹) * (g * u * g⁻¹) := by group
          _ = x * u := by rw [hxT g hg, huT g hg]
      · have heq : ⁅t₀, x⁆ = ⁅t₀, u⁆ := S.Z_eq_of_iff hcx hcu ⟨fun h => absurd h hcx1, fun h => absurd h hcu1⟩
        have hxc : x * ⁅t₀, u⁆ = ⁅t₀, u⁆ * x := S146T.comm_Z hxG hcu
        have h1 : ⁅t₀, x * u⁆ = 1 := by
          rw [S146T.comm_mul_right]
          have : x * ⁅t₀, u⁆ * x⁻¹ = ⁅t₀, u⁆ := by rw [hxc]; group
          rw [this, heq]
          exact hZ2 _ hcu
        have h := S146T.comm_eq_one_iff.mp h1
        calc t₀ * (x * u) * t₀⁻¹ = ((x * u) * t₀) * t₀⁻¹ := by rw [h]
          _ = x * u := by group
      · calc j * (x * u) * j⁻¹ = (j * x * j⁻¹) * (j * u * j⁻¹) := by group
          _ = x * u := by rw [hJx j hj, hJu j hj]
  have hvT0 : ∀ b ∈ tZero T u, b * v * b⁻¹ = v := by
    intro b hb
    rcases ht₀ b hb with h | h
    · have h1 := hvT _ h
      calc b * v * b⁻¹ = b * (t₀ * v * t₀⁻¹) * b⁻¹ := by rw [hvt]
        _ = (b * t₀) * v * (b * t₀)⁻¹ := by group
        _ = v := h1
    · exact hvT b h
  have hv2 : v * v = 1 := by rw [← sq]; exact hUab.2 v hvU
  let X : Subgroup G := Subgroup.centralizer ({v} : Set G)
  have hmemX : ∀ g : G, g * v * g⁻¹ = v → g ∈ X := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      calc v * g = (g * v * g⁻¹) * g := by rw [hg]
        _ = g * v := by group
  have hT0X : tZero T u ≤ X := fun b hb => hmemX b (hvT0 b hb)
  have hJX : J ≤ X := fun j hj => hmemX j (hvJ j hj)
  have hvX : v ∈ pCoreOf 2 X := by
    have hv2' : v ^ 2 = 1 := hUab.2 v hvU
    have hz : Subgroup.zpowers v ≤ pCoreOf 2 X := by
      refine le_pCoreOf_of_le_normalizer ?_ ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hmemX v (by group)
      · have h1 : X = Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
          show Subgroup.centralizer ({v} : Set G) = _
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        rw [h1]
        exact Subgroup.centralizer_le_normalizer _
      · intro ⟨h, hh⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        refine ⟨1, Subtype.ext ?_⟩
        show (v ^ k) ^ 2 ^ 1 = 1
        rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv2', one_zpow]
    exact hz (Subgroup.mem_zpowers v)
  have hIX : IsI T M u X := by
    refine ⟨⟨(tU_le_tZero T u).trans hT0X, ?_⟩, fun h => hJG (hJX.trans h), fun h => hJM (hJX.trans h)⟩
    intro hbot
    rw [hbot] at hvX
    exact hv1 (Subgroup.mem_bot.mp hvX)
  have hTIX : T ⊓ I ≤ X := by
    rw [hTu]
    exact (tU_le_tZero T u).trans hT0X
  have hlt : T ⊓ I < T ⊓ X := by
    refine lt_of_le_of_ne (le_inf inf_le_left hTIX) fun h => ht₀n ?_
    have h1 : t₀ ∈ T ⊓ X := ⟨ht₀T, hT0X ht₀T0⟩
    rw [← h, hTu] at h1
    exact h1
  exact hI.2 X hIX hlt

end CFSG.Quasithin.ModC
