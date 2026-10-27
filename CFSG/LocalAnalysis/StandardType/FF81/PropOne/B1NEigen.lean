module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NCore
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aTauT1
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Dihedral.BrauerSuzuki.Helpers
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aInvSubspaces
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aMonomial
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne.B1Normal

open scoped IsMulCommutative

private theorem isElemAb_sup_zpowers {W : Type} [Group W] [Finite W]
    [IsElementaryAbelian 3 W] {x y : W} (hx : x ≠ 1) (hy : y ≠ 1)
    (hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 2
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hpow3 : ∀ z : W, z ^ 3 = 1 := fun z =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 W) z
  have hEea : IsElementaryAbelian 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro z
        apply Subtype.ext
        exact hpow3 (z : W) }
  refine ⟨hEea, ?_⟩
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (Subgroup.zpowers y)
    (fun a _ c _ => mul_comm' a c)
  have hordx : orderOf x = 3 := orderOf_eq_prime (hpow3 x) hx
  have hordy : orderOf y = 3 := orderOf_eq_prime (hpow3 y) hy
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hordx]
  have hcardy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hordy]
  rw [hinf, Subgroup.card_bot, hcardx, hcardy, mul_one] at hcard
  rw [hcard]
  norm_num

theorem eigen_data {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    {sX tX : MulAut ↥(GGFF.Bt b z)}
    (hsX : (sX bG = bG ∧ ∀ i : Fin 3, sX (zsG i) = (zsG i)⁻¹) ∨
      (sX bG = bG⁻¹ ∧ ∀ i : Fin 3, sX (zsG i) = zsG i))
    (htX : tX bG = bG ∧ tX (zsG 0) = (zsG 0)⁻¹ ∧ tX (zsG 1) = zsG 1 ∧ tX (zsG 2) = zsG 2) :
    ((∀ x : ↥(GGFF.Bt b z), x⁻¹ * sX x = 1 ↔ x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z))) ∨
      (∀ x : ↥(GGFF.Bt b z), x * sX x = 1 ↔ x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z)))) ∧
    CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 2
      (Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)) ∧
    ((∀ x : ↥(GGFF.Bt b z), x⁻¹ * (sX * tX) x = 1 ↔
        x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)) ∨
      (∀ x : ↥(GGFF.Bt b z), x * (sX * tX) x = 1 ↔
        x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0))) := by
  let B := ↥(GGFF.Bt b z)
  have hBab : IsElementaryAbelian 3 B := (isElemAb_Bt h).1
  have hpow3 : ∀ x : B, x ^ 3 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 B) x
  let instCommGroup : CommGroup B := { (inferInstance : Group B) with
    mul_comm := fun a b => mul_comm' a b }
  have hbG_ne : (bG (b := b) (z := z) : B) ≠ 1 := by
    intro h1
    have hb1 : b = 1 := congrArg (fun x : B => (x : G)) h1
    have hord : orderOf b = 3 := h.hypA.ord
    rw [hb1, orderOf_one] at hord
    omega
  have hzsG0_ne : (zsG (b := b) (z := z) 0 : B) ≠ 1 := by
    intro h1
    have hzs1 : GGFF.zs z 0 = 1 := congrArg (fun x : B => (x : G)) h1
    exact h.settingCore.model.z_ne_one 0 (by simpa [GGFF.zs] using hzs1)
  have hsup : Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
      Subgroup.closure ({zsG (b := b) (z := z) 0, zsG 1, zsG 2} : Set B) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_four_gens (b := b) (z := z)]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hsup' : (Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
        Subgroup.zpowers (zsG (b := b) (z := z) 0)) ⊔
      Subgroup.closure ({zsG (b := b) (z := z) 1, zsG 2} : Set B) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_four_gens (b := b) (z := z)]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hEclosure : Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
      Subgroup.zpowers (zsG (b := b) (z := z) 0) =
      Subgroup.closure ({bG (b := b) (z := z), zsG (b := b) (z := z) 0} : Set B) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  have hinf : Subgroup.zpowers (bG (b := b) (z := z) : B) ⊓
      Subgroup.zpowers (zsG (b := b) (z := z) 0) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx0
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx1
    have hval : b ^ k = (GGFF.zs z 0) ^ m := by
      have h1 : ((bG (b := b) (z := z) : B) ^ k : G) = (x : G) := congrArg Subtype.val hk
      have h2 : (((zsG (b := b) (z := z) 0 : B) ^ m : B) : G) = (x : G) :=
        congrArg Subtype.val hm
      exact h1.trans h2.symm
    have hmem : b ^ k ∈ GGFF.tor (GGFF.zs z) := by
      rw [hval]
      exact (GGFF.tor (GGFF.zs z)).zpow_mem (Subgroup.subset_closure (by simp)) m
    have hb1 : b ^ k = 1 :=
      h.settingCore.zpow_eq_one_of_mem (GGFF.SettingCore.tor_le z hmem)
    have hx1' : (bG (b := b) (z := z) : B) ^ k = 1 := by
      apply Subtype.ext
      change b ^ k = (1 : G)
      exact hb1
    rw [← hk, hx1']
  have hE : CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 2
      (Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
        Subgroup.zpowers (zsG (b := b) (z := z) 0)) :=
    isElemAb_sup_zpowers hbG_ne hzsG0_ne hinf
  rcases hsX with ⟨hsXb, hsXi⟩ | ⟨hsXb, hsXi⟩
  · refine ⟨Or.inl ?_, hE, Or.inl ?_⟩
    · have hu₀ : ∀ x ∈ (Subgroup.zpowers (bG (b := b) (z := z) : B) : Subgroup B),
          sX x = x := by
        rw [Subgroup.zpowers_eq_closure]
        exact map_fix_of_closure (fun s hs => by
          rw [Set.mem_singleton_iff] at hs
          rw [hs, hsXb])
      have hu₁ : ∀ x ∈ Subgroup.closure ({zsG (b := b) (z := z) 0, zsG 1, zsG 2} : Set B),
          sX x = x⁻¹ :=
        map_inv_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl | rfl
          · exact hsXi 0
          · exact hsXi 1
          · exact hsXi 2)
      intro x
      rw [inv_mul_eq_one, eq_comm]
      exact (fix_of_fixes_inverts hpow3 hsup hu₀ hu₁) x
    · have hfix_bG : (sX * tX) (bG (b := b) (z := z) : B) = bG := by
        rw [MulAut.mul_apply, htX.1, hsXb]
      have hfix_z0 : (sX * tX) (zsG (b := b) (z := z) 0) = zsG 0 := by
        rw [MulAut.mul_apply, htX.2.1, map_inv, hsXi 0, inv_inv]
      have hinv_z1 : (sX * tX) (zsG (b := b) (z := z) 1) = (zsG 1)⁻¹ := by
        rw [MulAut.mul_apply, htX.2.2.1, hsXi 1]
      have hinv_z2 : (sX * tX) (zsG (b := b) (z := z) 2) = (zsG 2)⁻¹ := by
        rw [MulAut.mul_apply, htX.2.2.2, hsXi 2]
      have hu₀ : ∀ x ∈ (Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
            Subgroup.zpowers (zsG (b := b) (z := z) 0) : Subgroup B),
          (sX * tX) x = x := by
        rw [hEclosure]
        exact map_fix_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl
          · exact hfix_bG
          · exact hfix_z0)
      have hu₁ : ∀ x ∈ Subgroup.closure ({zsG (b := b) (z := z) 1, zsG 2} : Set B),
          (sX * tX) x = x⁻¹ :=
        map_inv_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl
          · exact hinv_z1
          · exact hinv_z2)
      intro x
      rw [inv_mul_eq_one, eq_comm]
      exact (fix_of_fixes_inverts hpow3 hsup' hu₀ hu₁) x
  · refine ⟨Or.inr ?_, hE, Or.inr ?_⟩
    · have hu₀ : ∀ x ∈ (Subgroup.zpowers (bG (b := b) (z := z) : B) : Subgroup B),
          sX x = x⁻¹ := by
        rw [Subgroup.zpowers_eq_closure]
        exact map_inv_of_closure (fun s hs => by
          rw [Set.mem_singleton_iff] at hs
          rw [hs, hsXb])
      have hu₁ : ∀ x ∈ Subgroup.closure ({zsG (b := b) (z := z) 0, zsG 1, zsG 2} : Set B),
          sX x = x :=
        map_fix_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl | rfl
          · exact hsXi 0
          · exact hsXi 1
          · exact hsXi 2)
      intro x
      rw [mul_eq_one_iff_inv_eq, eq_comm]
      exact (inv_of_fixes_inverts hpow3 hsup hu₀ hu₁) x
    · have hinv_bG : (sX * tX) (bG (b := b) (z := z) : B) = (bG)⁻¹ := by
        rw [MulAut.mul_apply, htX.1, hsXb]
      have hinv_z0 : (sX * tX) (zsG (b := b) (z := z) 0) = (zsG 0)⁻¹ := by
        rw [MulAut.mul_apply, htX.2.1, map_inv, hsXi 0]
      have hfix_z1 : (sX * tX) (zsG (b := b) (z := z) 1) = zsG 1 := by
        rw [MulAut.mul_apply, htX.2.2.1, hsXi 1]
      have hfix_z2 : (sX * tX) (zsG (b := b) (z := z) 2) = zsG 2 := by
        rw [MulAut.mul_apply, htX.2.2.2, hsXi 2]
      have hu₀ : ∀ x ∈ (Subgroup.zpowers (bG (b := b) (z := z) : B) ⊔
            Subgroup.zpowers (zsG (b := b) (z := z) 0) : Subgroup B),
          (sX * tX) x = x⁻¹ := by
        rw [hEclosure]
        exact map_inv_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl
          · exact hinv_bG
          · exact hinv_z0)
      have hu₁ : ∀ x ∈ Subgroup.closure ({zsG (b := b) (z := z) 1, zsG 2} : Set B),
          (sX * tX) x = x :=
        map_fix_of_closure (fun s hs => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl
          · exact hfix_z1
          · exact hfix_z2)
      intro x
      rw [mul_eq_one_iff_inv_eq, eq_comm]
      exact (inv_of_fixes_inverts hpow3 hsup' hu₀ hu₁) x

end CFSG.StandardType.FF81.PropOne.B1Normal

end
