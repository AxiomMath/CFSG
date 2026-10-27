module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecD31D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem eq_of_mem_of_card_eq_two {M : Type*} [Group M] {Z : Subgroup M} (hZ : Nat.card Z = 2)
    {a b : M} (ha : a ∈ Z) (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have : Fintype Z := Fintype.ofFinite Z
  have hS : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  have h1 := Finset.card_le_univ ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z)
  rw [hS, Fintype.card_eq_nat_card, hZ] at h1
  omega

@[expose] def l3T : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

theorem l3T_invol : L3.IsInvol l3T := by decide +kernel

theorem l3T_act_e0 : L3.act l3T ![1, 0, 0] = ![1, 0, 0] := by decide +kernel

theorem l3T_cim : L3.cim l3T = {0, ![0, 1, 0]} := by decide +kernel

theorem l3_e0_ne : (![1, 0, 0] : L3.Vec) ≠ 0 := by decide

theorem l3_e1_ne : (![0, 1, 0] : L3.Vec) ≠ 0 := by decide

theorem l3_e0_not_mem : (![1, 0, 0] : L3.Vec) ∉ ({0, ![0, 1, 0]} : Finset L3.Vec) := by decide

theorem l3_card_vec : Nat.card L3.Vec = 8 := by
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_fixV_of_l3 (hcard : Nat.card W = 2 ^ 4) {X : Subgroup (MulAut W)}
    (D : L3Data X ⊤ (fixV X)) : Nat.card (fixV X) = 2 := by
  have h1 := D.card_U
  rw [Subgroup.card_top, hcard] at h1
  omega

theorem exists_mem_apply_eq_of_l3 (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {X : Subgroup (MulAut W)} (hnat : BinaryNaturalSL X ⊤ (fixV X) 3 1) (hcomm : commV X = ⊤)
    {u w : W} (hu : u ∉ fixV X) (hw : w ∉ fixV X) : ∃ x ∈ X, x u = w := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card W = 16 := by rw [hcard]; norm_num
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcomm h16
  have hZ2 := card_fixV_of_l3 hcard D
  let β : W → L3.Vec := fun v => Multiplicative.toAdd (D.β ⟨v, Subgroup.mem_top v⟩)
  have hβ0 : ∀ v, β v = 0 ↔ v ∈ fixV X := fun v => by
    rw [← D.ker_β ⟨v, Subgroup.mem_top v⟩]
    exact toAdd_eq_zero
  have hβρ : ∀ γ v, β (D.rho γ v) = L3.act γ (β v) := fun γ v => by
    show Multiplicative.toAdd (D.β ⟨D.rho γ v, Subgroup.mem_top _⟩) = _
    rw [D.β_rho γ v (Subgroup.mem_top v) (Subgroup.mem_top _)]
    rfl
  have hβeq : ∀ v v', β v = β v' → v * v'⁻¹ ∈ fixV X := fun v v' h => by
    have h1 : D.β ⟨v, Subgroup.mem_top v⟩ = D.β ⟨v', Subgroup.mem_top v'⟩ :=
      Multiplicative.toAdd.injective h
    refine (D.ker_β ⟨v * v'⁻¹, Subgroup.mem_top _⟩).1 ?_
    show D.β (⟨v, Subgroup.mem_top v⟩ * (⟨v', Subgroup.mem_top v'⟩)⁻¹) = 1
    rw [map_mul, map_inv, h1]
    exact mul_inv_cancel _
  have hu0 : β u ≠ 0 := fun h => hu ((hβ0 u).1 h)
  have hw0 : β w ≠ 0 := fun h => hw ((hβ0 w).1 h)
  obtain ⟨γ, hγ⟩ := L3.act_trans (β u) (β w) hu0 hw0
  have hc : D.rho γ u * w⁻¹ ∈ fixV X := hβeq _ _ (by rw [hβρ, hγ])
  by_cases heq : D.rho γ u = w
  · exact ⟨D.rho γ, D.rho_mem γ, heq⟩
  have hc1 : D.rho γ u * w⁻¹ ≠ 1 := fun h => heq (mul_inv_eq_one.1 h)
  obtain ⟨g, hg⟩ := L3.act_trans ![1, 0, 0] (β w) l3_e0_ne hw0
  have hw₀ : β (D.rho g⁻¹ w) = ![1, 0, 0] := by
    rw [hβρ, ← hg, L3.act_inv_act]
  have hfix := fixV_rho_two D hW h16 rfl rfl hind l3T_invol l3_e1_ne l3T_cim
  have hnf : D.rho l3T (D.rho g⁻¹ w) ≠ D.rho g⁻¹ w := by
    intro h
    have hmem : D.rho g⁻¹ w ∈ fixV (Subgroup.zpowers (D.rho l3T)) := by
      intro x hx
      have hle : Subgroup.zpowers (D.rho l3T) ≤
          MulAction.stabilizer (MulAut W) (D.rho g⁻¹ w) := Subgroup.zpowers_le.2 h
      exact hle hx
    rw [hfix, D.mem_pre] at hmem
    obtain ⟨_, hmem'⟩ := hmem
    apply l3_e0_not_mem
    rw [← hw₀]
    exact hmem'
  have hd : D.rho l3T (D.rho g⁻¹ w) * (D.rho g⁻¹ w)⁻¹ ∈ fixV X :=
    hβeq _ _ (by rw [hβρ, hw₀, l3T_act_e0])
  have hd1 : D.rho l3T (D.rho g⁻¹ w) * (D.rho g⁻¹ w)⁻¹ ≠ 1 := fun h => hnf (mul_inv_eq_one.1 h)
  have hcd := eq_of_mem_of_card_eq_two hZ2 hc hd hc1 hd1
  have hcfix : ∀ y ∈ X, y (D.rho γ u * w⁻¹) = D.rho γ u * w⁻¹ := fun y hy => hc y hy
  have h1 : D.rho γ u = w * (D.rho γ u * w⁻¹) := by
    rw [mul_comm w, inv_mul_cancel_right]
  have h2 : D.rho l3T (D.rho g⁻¹ w) = D.rho g⁻¹ w * (D.rho γ u * w⁻¹) := by
    rw [hcd, mul_comm (D.rho g⁻¹ w), inv_mul_cancel_right]
  have h3 : (D.rho γ u * w⁻¹) * (D.rho γ u * w⁻¹) = 1 := by
    rw [← pow_two]
    exact hW _
  refine ⟨D.rho (g * l3T * g⁻¹ * γ), D.rho_mem _, ?_⟩
  calc D.rho (g * l3T * g⁻¹ * γ) u = D.rho g (D.rho l3T (D.rho g⁻¹ (D.rho γ u))) := by
        simp only [map_mul, MulAut.mul_apply]
    _ = D.rho g (D.rho l3T (D.rho g⁻¹ w * (D.rho γ u * w⁻¹))) := by
        conv_lhs => rw [h1]
        rw [map_mul (D.rho g⁻¹ : MulAut W), hcfix _ (D.rho_mem _)]
    _ = D.rho g (D.rho g⁻¹ w * (D.rho γ u * w⁻¹) * (D.rho γ u * w⁻¹)) := by
        rw [map_mul (D.rho l3T : MulAut W), h2, hcfix _ (D.rho_mem _)]
    _ = w := by
        rw [mul_assoc, h3, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          MulAut.one_apply]

omit [Finite W] in
theorem exists_card_four_of_l3 (hcard : Nat.card W = 2 ^ 4) {X : Subgroup (MulAut W)}
    (hnat : BinaryNaturalSL X ⊤ (fixV X) 3 1) {S : Subgroup (MulAut W)} (hSX : S ≤ X)
    (hS : IsPGroup 2 S) :
    ∃ E : Subgroup W, Nat.card E = 4 ∧ fixV X ≤ E ∧ ∀ s ∈ S, ∀ e ∈ E, s e ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := hnat.toL3Coord
  have hZ2 := card_fixV_of_l3 hcard D
  have hS' : IsPGroup 2 (S.comap D.rho) := hS.comap_of_injective D.rho D.rho_injective
  let act : MulAction (S.comap D.rho) L3.Vec :=
    { smul := fun s v => L3.act s v
      one_smul := fun v => L3.act_one v
      mul_smul := fun s t v => L3.act_mul s t v }
  have h0 : (0 : L3.Vec) ∈ MulAction.fixedPoints (S.comap D.rho) L3.Vec :=
    fun s => L3.act_zero s
  obtain ⟨c, hc, hc0⟩ := hS'.exists_fixed_point_of_prime_dvd_card_of_fixed_point L3.Vec
    (by rw [l3_card_vec]; norm_num) h0
  refine ⟨D.pre (Zc c), ?_, D.Z_le_pre _, ?_⟩
  · have h1 := D.card_pre (Zc c)
    rw [hZ2, card_Zc (Ne.symm hc0)] at h1
    omega
  · intro s hs e he
    obtain ⟨γ, rfl⟩ := D.exists_rho (hSX hs)
    have hγ : γ ∈ S.comap D.rho := hs
    rw [D.mem_pre] at he ⊢
    obtain ⟨_, he⟩ := he
    refine ⟨Subgroup.mem_top _, ?_⟩
    rw [D.β_rho γ e (Subgroup.mem_top e) (Subgroup.mem_top _)]
    have he' : Multiplicative.toAdd (D.β ⟨e, Subgroup.mem_top e⟩) ∈
        ({0, c} : Finset L3.Vec) := he
    show Multiplicative.toAdd (Multiplicative.ofAdd (L3.act γ
      (Multiplicative.toAdd (D.β ⟨e, Subgroup.mem_top e⟩)))) ∈ ({0, c} : Finset L3.Vec)
    rw [toAdd_ofAdd]
    rcases Finset.mem_insert.1 he' with h | h
    · rw [h, L3.act_zero]
      exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton.1 h]
      have hcγ : L3.act γ c = c := hc ⟨γ, hγ⟩
      rw [hcγ]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

omit [Finite W] in
theorem orbitIn_eq_of_mem {H : Subgroup (MulAut W)} {v w' : W} (h : w' ∈ Orbit.orbitIn H v) :
    Orbit.orbitIn H w' = Orbit.orbitIn H v := by
  obtain ⟨h₀, hh₀, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * h₀, H.mul_mem hk hh₀, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * h₀⁻¹, H.mul_mem hk (H.inv_mem hh₀), ?_⟩
    show k (h₀⁻¹ (h₀ v)) = k v
    rw [MulAut.inv_apply_self]

@[expose] def G2WeylNormalizerOrbits : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)), G2WeylDerived H →
    ∀ x : MulAut W, (∀ h, h ∈ H ↔ x * h * x⁻¹ ∈ H) → ∀ w : W, x w ∈ Orbit.orbitIn H w

theorem exists_fixed_of_g2Weyl (hOrb : OrbitG2Weyl) (hNorm : G2WeylNormalizerOrbits)
    {H : Subgroup (MulAut W)} (hH : G2WeylDerived H) {z : W} (hz1 : z ≠ 1) (hzH : z ∈ fixV H)
    {u₁ : W} (hu₁ : u₁ ≠ 1) (hu₁z : u₁ ≠ z) {S : Subgroup (MulAut W)} (hS : IsPGroup 2 S)
    (hSN : ∀ s ∈ S, ∀ h, h ∈ H ↔ s * h * s⁻¹ ∈ H) :
    ∃ u : W, u ≠ 1 ∧ u ≠ z ∧ ∀ s ∈ S, s u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hlen, -⟩ := hOrb W H z hz1 hzH hH
  have h63 : Nat.card (Orbit.orbitIn H u₁) = 63 := by
    simpa using hlen u₁ hu₁ hu₁z
  have hSO : ∀ s ∈ S, ∀ w ∈ Orbit.orbitIn H u₁, s w ∈ Orbit.orbitIn H u₁ := by
    intro s hs w hw
    have h1 := hNorm W H hH s (hSN s hs) w
    rwa [orbitIn_eq_of_mem hw] at h1
  let act : MulAction S (Orbit.orbitIn H u₁) :=
    { smul := fun s w => ⟨(s : MulAut W) w, hSO s s.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun s t w => Subtype.ext rfl }
  obtain ⟨⟨u, hu⟩, hfix⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card
    (Orbit.orbitIn H u₁) (by rw [h63]; decide)
  obtain ⟨h, hh, h1⟩ := hu
  refine ⟨u, ?_, ?_, fun s hs => congrArg Subtype.val (hfix ⟨s, hs⟩)⟩
  · rintro rfl
    exact hu₁ ((MulEquiv.map_eq_one_iff (h : MulAut W)).1 h1)
  · intro huz
    apply hu₁z
    have h2 : (h⁻¹ : MulAut W) z = z := hzH _ (H.inv_mem hh)
    calc u₁ = (h⁻¹ : MulAut W) (h u₁) := by rw [MulAut.inv_apply_self]
      _ = (h⁻¹ : MulAut W) z := by rw [h1, huz]
      _ = z := h2

end CFSG.Quasithin.H13
