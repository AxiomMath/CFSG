module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame
import CFSG.GroupTheory.FixedPointFreeModCentral
import CFSG.Quasithin.Recognition.St84.G24Tools

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.GroupTheory
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open Certificates.A5GL42 (aN bN)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

private theorem card_Q2_of_frame [Finite G] (F : G24Frame2 L1 L2 S) :
    Nat.card ↥(dsQ L2 L1 S) = 2 ^ 10 := by
  let Q : Subgroup G := dsQ L2 L1 S
  let K : Subgroup ↥Q := F.W.subgroupOf Q
  have hWQ : F.W ≤ Q := fun x hx => ((F.mem_W x).mp hx).1
  have hK : K = F.FN.φ.ker := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (F.FN.ker e).symm
  haveI : K.Normal := hK ▸ MonoidHom.normal_ker F.FN.φ
  let e := QuotientGroup.quotientKerEquivOfSurjective F.FN.φ F.FN.surj
  have hquot : Nat.card (↥Q ⧸ K) = 16 := by
    have hcard := Nat.card_congr e.toEquiv
    have h16 : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
        Fintype.card_fin, ZMod.card]
      norm_num
    rw [hK, hcard, h16]
  have hKW : Nat.card ↥K = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv]
    exact F.card_W
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [hquot, hKW] at h
  exact h

private theorem G24Frame2.Mk_mul_glMat (F : G24Frame2 L1 L2 S) {g : G}
    (gP : ↥(L2 ⊔ bigB L1 L2 S)) (hg : (gP : G) = g) (hkg : F.k * g = g * F.k) :
    F.Mk * glMat (F.FN.M gP) = glMat (F.FN.M gP) * F.Mk := by
  have hkgP : F.kP * gP = gP * F.kP := by
    apply Subtype.ext
    change F.k * (gP : G) = (gP : G) * F.k
    rw [hg]
    exact hkg
  calc F.Mk * glMat (F.FN.M gP)
      = glMat (F.FN.M F.kP) * glMat (F.FN.M gP) := rfl
    _ = glMat (F.FN.M F.kP * F.FN.M gP) := by rw [← Units.val_mul]
    _ = glMat (F.FN.M (F.kP * gP)) := by rw [← map_mul]
    _ = glMat (F.FN.M (gP * F.kP)) := by rw [hkgP]
    _ = glMat (F.FN.M gP * F.FN.M F.kP) := by rw [map_mul]
    _ = glMat (F.FN.M gP) * F.Mk := rfl

private theorem G24Frame2.Mk_pow_three (F : G24Frame2 L1 L2 S) : F.Mk ^ 3 = 1 := by
  have hkP3 : F.kP ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, G24Frame2.coe_kP]
    exact (by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k)
  have h : F.FN.M F.kP ^ 3 = 1 := by rw [← map_pow, hkP3, map_one]
  simpa [G24Frame2.Mk, Units.val_pow_eq_pow_val] using congrArg Units.val h

private theorem G24Frame2.fixedMod_eq_W [Finite G] (F : G24Frame2 L1 L2 S) :
    fixedModSubgroup (dsQ L2 L1 S) F.W F.k F.Q2_le_normalizer_W = F.W := by
  let Q : Subgroup G := dsQ L2 L1 S
  let X : Subgroup G := fixedModSubgroup Q F.W F.k F.Q2_le_normalizer_W
  have hmemX : ∀ x, x ∈ X ↔ x ∈ Q ∧ F.k * x * F.k⁻¹ * x⁻¹ ∈ F.W := fun x =>
    CFSG.GroupTheory.mem_fixedModSubgroup
  have hXQ : X ≤ Q := fun x hx => (hmemX x).mp hx |>.1
  have hWX : F.W ≤ X := by
    intro w hw
    refine (hmemX w).mpr ⟨((F.mem_W w).mp hw).1, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W w).mp hw
    exact F.W.mul_mem h (F.W.inv_mem hw)
  have hX2 : IsPGroup 2 X := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := 10) ?_
    have hd := Subgroup.card_dvd_of_le hXQ
    rw [card_Q2_of_frame F] at hd
    exact hd
  have hkNX : F.k ∈ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨hxQ, hxW⟩ := (hmemX x).mp hx
    refine (hmemX _).mpr ⟨?_, ?_⟩
    · have hcomm := F.comm_k x (dsQ_le_P_right L1 L2 S hxQ)
      have e : F.k * x * F.k⁻¹ = ⁅F.k, x⁆ * x := by
        rw [commutatorElement_def]; group
      rw [e]
      exact Q.mul_mem hcomm hxQ
    · have hb : F.k * (F.k * x * F.k⁻¹ * x⁻¹) * F.k⁻¹ ∈ F.W :=
        (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W _).mp hxW
      rw [show F.k * (F.k * x * F.k⁻¹) * F.k⁻¹ * (F.k * x * F.k⁻¹)⁻¹ =
          F.k * (F.k * x * F.k⁻¹ * x⁻¹) * F.k⁻¹ from by group]
      exact hb
  have hZn : ∀ q ∈ X, ∀ z ∈ F.W, q * z * q⁻¹ ∈ F.W := fun q hq z hz =>
    (Subgroup.mem_normalizer_iff.mp (F.Q2_le_normalizer_W (hXQ hq)) z).mp hz
  have htriv : ∀ x ∈ X, F.k * x * F.k⁻¹ * x⁻¹ ∈ F.W := fun x hx => (hmemX x).mp hx |>.2
  have hdec := CFSG.Quasithin.St84.exists_mul_mem_centralizer_of_acts_trivially
    (Q := X) (Z := F.W) (k := F.k) hWX hX2 F.orderOf_k hkNX
    F.k_le_normalizer_W hZn htriv
  have hXW : X ≤ F.W := by
    intro x hx
    obtain ⟨z, hz, a, ha, rfl⟩ := hdec x hx
    have haZ : a ∈ centerOf Q := by
      change a ∈ centerOf (dsQ L2 L1 S)
      rw [← F.inf_centralizer]
      exact ⟨((hmemX a).mp ha.1).1, ha.2⟩
    exact F.W.mul_mem hz (F.Z2_le_W haZ)
  exact le_antisymm hXW hWX

private theorem G24Frame2.Mk_fixed [Finite G] (F : G24Frame2 L1 L2 S) :
    ∀ v : Fin 4 → ZMod 2, F.Mk *ᵥ v = v → v = 0 := by
  intro v hv
  let Q : Subgroup G := dsQ L2 L1 S
  have hQ2P2 := dsQ_le_P_right L1 L2 S
  obtain ⟨e, he⟩ := F.FN.surj (Multiplicative.ofAdd v)
  have hcomm := F.comm_k (e : G) (hQ2P2 e.2)
  have hconjQ : F.k * (e : G) * F.k⁻¹ ∈ Q := by
    have ee : F.k * (e : G) * F.k⁻¹ = ⁅F.k, (e : G)⁆ * (e : G) := by
      rw [commutatorElement_def]; group
    rw [ee]
    exact Q.mul_mem hcomm e.2
  let e' : ↥Q := ⟨F.k * (e : G) * F.k⁻¹, hconjQ⟩
  have hact := F.FN.act F.kP e e' rfl
  have hφe : Multiplicative.toAdd (F.FN.φ e) = v := by rw [he]; rfl
  have hMk : F.Mk = glMat (F.FN.M F.kP) := rfl
  have hφe' : Multiplicative.toAdd (F.FN.φ e') = v := by
    have h := hact.symm
    rw [hφe, ← hMk] at h
    rwa [hv] at h
  have hmem : ((e' * e⁻¹ : ↥Q) : G) ∈ F.W := by
    apply (F.FN.ker (e' * e⁻¹)).mp
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hφe', hφe]
    abel
  have hxmem : (e : G) ∈ fixedModSubgroup Q F.W F.k F.Q2_le_normalizer_W := by
    refine CFSG.GroupTheory.mem_fixedModSubgroup.mpr ⟨e.2, ?_⟩
    have hc : ((e' * e⁻¹ : ↥Q) : G) = F.k * (e : G) * F.k⁻¹ * (e : G)⁻¹ := rfl
    rw [← hc]
    exact hmem
  rw [F.fixedMod_eq_W] at hxmem
  have hφ1 : F.FN.φ e = 1 := (F.FN.ker e).mpr hxmem
  rw [hφ1] at hφe
  exact hφe.symm

theorem G24Frame2.Mk_spec [Finite G] (F : G24Frame2 L1 L2 S) :
    F.Mk * aN = aN * F.Mk ∧ F.Mk * bN = bN * F.Mk ∧ F.Mk ^ 3 = 1 ∧
      ∀ v : Fin 4 → ZMod 2, F.Mk *ᵥ v = v → v = 0 := by
  have hka : F.k * F.a = F.a * F.k := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (F.A_le F.a_mem.1).2
    exact h.symm
  have hkb : F.k * F.b = F.b * F.k := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (F.A_le F.b_mem.1).2
    exact h.symm
  let aP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨F.a, (F.A_le F.a_mem.1).1⟩
  let bP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨F.b, (F.A_le F.b_mem.1).1⟩
  have haN : glMat (F.FN.M aP) = aN := F.FN_a aP rfl
  have hbN : glMat (F.FN.M bP) = bN := F.FN_b bP rfl
  refine ⟨?_, ?_, F.Mk_pow_three, F.Mk_fixed⟩
  · rw [← haN]
    exact F.Mk_mul_glMat aP rfl hka
  · rw [← hbN]
    exact F.Mk_mul_glMat bP rfl hkb

theorem G24Frame2.Mk_inv (F : G24Frame2 L1 L2 S) : F.inv.Mk = F.Mk ^ 2 := by
  have h3 : F.Mk ^ 3 = 1 := F.Mk_pow_three
  have hx : F.inv.Mk * F.Mk = 1 := by
    have hk : F.inv.kP = F.kP⁻¹ := Subtype.ext rfl
    show glMat (F.FN.M (F.kP⁻¹)) * glMat (F.FN.M F.kP) = 1
    rw [map_inv]
    exact ElemFrame.glMat_inv_mul (F.FN.M F.kP)
  have hp : F.Mk ^ 3 = F.Mk * F.Mk ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ']
  calc F.inv.Mk = F.inv.Mk * 1 := (mul_one _).symm
    _ = F.inv.Mk * F.Mk ^ 3 := by rw [h3]
    _ = F.inv.Mk * (F.Mk * F.Mk ^ 2) := by rw [hp]
    _ = (F.inv.Mk * F.Mk) * F.Mk ^ 2 := by rw [mul_assoc]
    _ = F.Mk ^ 2 := by rw [hx, one_mul]

theorem G24Frame2.exists_u [Finite G] (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) :
    ∃ u ∈ F.W, u ∉ centerOf (dsQ L2 L1 S) := by
  by_contra h
  push Not at h
  have hle : F.W ≤ centerOf (dsQ L2 L1 S) := fun u hu => h u hu
  have hcard := Subgroup.card_le_of_le hle
  rw [F.card_W, hD.card_centerOf_dsQ_right] at hcard
  norm_num at hcard

theorem G24Frame2.mem_Z2_of_fixed_on_W [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {w : G} (hw : w ∈ F.W)
    (hfix : F.k * w * F.k⁻¹ * w⁻¹ ∈ centerOf (dsQ L2 L1 S)) :
    w ∈ centerOf (dsQ L2 L1 S) := by
  let W := F.W
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  have hWZ : W ≤ Subgroup.normalizer (Z2 : Set G) := fun x hx =>
    P_le_normalizer_centerOf_dsQ_right L1 L2 S
      (dsQ_le_P_right L1 L2 S (((F.mem_W x).mp hx).1))
  have hcent : ∀ z ∈ Z2, ∀ x ∈ dsQ L2 L1 S, z * x = x * z :=
    (F.special_data hD).2.2.2.1
  have hW2 : IsPGroup 2 ↥W :=
    IsPGroup.of_card (n := 6) (by rw [show Nat.card ↥W = 2 ^ 6 from F.card_W])
  let X : Subgroup G := fixedModSubgroup W Z2 F.k hWZ
  have hmemX : ∀ x, x ∈ X ↔ x ∈ W ∧ F.k * x * F.k⁻¹ * x⁻¹ ∈ Z2 := fun x =>
    CFSG.GroupTheory.mem_fixedModSubgroup
  have hXW : X ≤ W := fun x hx => (hmemX x).mp hx |>.1
  have hZ2X : Z2 ≤ X := by
    intro z hz
    have hzW : z ∈ W := F.Z2_le_W hz
    have hcomm := F.cent_Z z hz
    have hkz : F.k * z * F.k⁻¹ = z := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    refine (hmemX z).mpr ⟨hzW, ?_⟩
    rw [hkz, mul_inv_cancel]
    exact Z2.one_mem
  have hX2 : IsPGroup 2 ↥X := hW2.to_le hXW
  have hkNX : F.k ∈ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨hxW, hxZ⟩ := (hmemX x).mp hx
    refine (hmemX _).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W x).mp hxW
    · have hb : F.k * (F.k * x * F.k⁻¹ * x⁻¹) * F.k⁻¹ ∈ Z2 :=
        (Subgroup.mem_normalizer_iff.mp F.k_mem_normalizer_Z2 _).mp hxZ
      rw [show F.k * (F.k * x * F.k⁻¹) * F.k⁻¹ * (F.k * x * F.k⁻¹)⁻¹ =
          F.k * (F.k * x * F.k⁻¹ * x⁻¹) * F.k⁻¹ from by group]
      exact hb
  have hZn : ∀ q ∈ X, ∀ z ∈ Z2, q * z * q⁻¹ ∈ Z2 := by
    intro q hq z hz
    have hqW : q ∈ W := hXW hq
    have hqQ : q ∈ dsQ L2 L1 S := ((F.mem_W q).mp hqW).1
    rw [G24Vertex2.conj_eq_of_mem_centerOf hz hqQ]
    exact hz
  have htriv : ∀ x ∈ X, F.k * x * F.k⁻¹ * x⁻¹ ∈ Z2 := fun x hx => (hmemX x).mp hx |>.2
  have hdec := CFSG.Quasithin.St84.exists_mul_mem_centralizer_of_acts_trivially
    (Q := X) (Z := Z2) (k := F.k) hZ2X hX2 F.orderOf_k hkNX
    F.k_mem_normalizer_Z2 hZn htriv
  have hXZ : X ≤ Z2 := by
    intro x hx
    obtain ⟨z, hz, a, ha, rfl⟩ := hdec x hx
    have haW : a ∈ W := hXW ha.1
    have haQ : a ∈ dsQ L2 L1 S := ((F.mem_W a).mp haW).1
    have haZ : a ∈ Z2 := by
      change a ∈ centerOf (dsQ L2 L1 S)
      rw [← F.inf_centralizer]
      exact ⟨haQ, ha.2⟩
    exact Z2.mul_mem hz haZ
  exact hXZ ((hmemX w).mpr ⟨hw, hfix⟩)

end CFSG.Quasithin.F112R.St84
