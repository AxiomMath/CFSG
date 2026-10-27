module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import CFSG.CGT.Stroth77.Arch76Lemma2Coord
import CFSG.Quasithin.Background.RonanF57Unitary
import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearPm

public section

namespace CFSG.StandardType.FrameRoute.GlueSwap

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.CGT.Stroth77.Arch76 CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.Quasithin.RonanF57 (unitaryFieldData_of_card)

lemma pow_val_eq_iff {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (a b : ZMod 3) : ζ ^ a.val = ζ ^ b.val ↔ a = b := by
  rw [pow_eq_pow_iff_modEq, hζ]
  constructor
  · intro h
    apply ZMod.val_injective 3
    have hmod : a.val % 3 = b.val % 3 := h
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at hmod
  · rintro rfl
    rfl

lemma prod_pow_val {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (m : ℕ) (v : Fin m → ZMod 3) :
    ∏ i, ζ ^ (v i).val = ζ ^ (∑ i, v i).val := by
  have h3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  induction m with
  | zero => simp [ZMod.val_zero]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, ih (fun i => v i.succ), pow_val_add h3]

noncomputable def coordinateSumRoot {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) (b : G) : ZMod 3 :=
  if 3 ∣ m then 0 else (∑ i, u b i) * (m : ZMod 3)⁻¹

lemma coordinateSumRoot_spec {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {b : G} (hb : b ∈ Bs) : (m : ZMod 3) * coordinateSumRoot hdet b = ∑ i, u b i := by
  by_cases h3 : 3 ∣ m
  · have hm0 : (m : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff m 3).mpr h3
    have hsum : ∑ i, u b i = 0 := hdet.resolve_left (not_not.mpr h3) b hb
    simp [coordinateSumRoot, h3, hm0, hsum]
  · have hm0 : (m : ZMod 3) ≠ 0 := fun h => h3 ((ZMod.natCast_eq_zero_iff m 3).mp h)
    simp only [coordinateSumRoot, if_neg h3]
    rw [← mul_assoc, mul_comm (m : ZMod 3) (∑ i, u b i), mul_assoc,
      mul_inv_cancel₀ hm0, mul_one]

@[expose] noncomputable def correctedDiag {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F]
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {ζ : Fˣ} (b : G) : Fin m → Fˣ :=
  fun i => ζ ^ (u b i - coordinateSumRoot hdet b).val

lemma correctedDiag_prod {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {b : G} (hb : b ∈ Bs) : ∏ i, correctedDiag hdet (ζ := ζ) b i = 1 := by
  simp only [correctedDiag]
  rw [prod_pow_val hζ m (fun i => u b i - coordinateSumRoot hdet b)]
  have hsum : ∑ i, (u b i - coordinateSumRoot hdet b) = 0 := by
    calc ∑ i, (u b i - coordinateSumRoot hdet b)
        = (∑ i, u b i) - ∑ _i : Fin m, coordinateSumRoot hdet b :=
          Finset.sum_sub_distrib (fun i => u b i) (fun _ : Fin m => coordinateSumRoot hdet b)
      _ = 0 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            coordinateSumRoot_spec hdet hb, sub_self]
  rw [hsum, ZMod.val_zero, pow_zero]

lemma pow_pow_three_eq_one {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (n : ℕ) : (ζ ^ n) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul,
    show ζ ^ 3 = 1 by rw [← hζ]; exact pow_orderOf_eq_one ζ, one_pow]

lemma diagGL_mem_unitarySU {F : Type} [Field F] {m : ℕ} (hF : Nat.card F = 4)
    {d : Fin m → Fˣ} (hd : ∏ i, d i = 1) :
    TauCeti.diagGL d ∈ unitarySU 2 1 F m := by
  have hU := unitaryFieldData_of_card hF
  have hnorm : ∀ k, hU.norm ((d k : Fˣ) : F) = 1 := by
    intro k
    rw [UnitaryFieldData.norm, hU.bar_apply]
    have h3 : ((d k : Fˣ) : F) ^ 3 = 1 := by
      simpa using congrArg (fun u : Fˣ => (u : F)) (units_pow_three_eq_one_of_card_four hF (d k))
    calc ((d k : Fˣ) : F) * ((d k : Fˣ) : F) ^ 2 = ((d k : Fˣ) : F) ^ 3 := by ring
      _ = 1 := h3
  rw [mem_unitarySU_iff hU]
  refine ⟨?_, ?_⟩
  · rw [TauCeti.diagGL_coe, Matrix.det_diagonal]
    simpa using congrArg (fun u : Fˣ => (u : F)) hd
  · simpa [TauCeti.diagGL_coe] using
      CFSG.SeitzReduction.UnitaryPilot.unitary_diagonal hU hnorm

lemma correctedDiag_mem_unitarySU {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hF : Nat.card F = 4) (hζ : orderOf ζ = 3)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {b : G} (hb : b ∈ Bs) :
    TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) ∈ unitarySU 2 1 F m :=
  diagGL_mem_unitarySU hF (correctedDiag_prod hζ hdet hb)

lemma diagGL_eq_scalar_mul_correctedDiag {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) (b : G) :
    TauCeti.diagGL (fun i => ζ ^ (u b i).val) =
      Matrix.GeneralLinearGroup.scalar (Fin m) (ζ ^ (coordinateSumRoot hdet b).val) *
        TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) := by
  have h3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have h : (fun _ : Fin m => ζ ^ (coordinateSumRoot hdet b).val) * correctedDiag hdet (ζ := ζ) b =
      fun i => ζ ^ (u b i).val := by
    funext i
    simp only [Pi.mul_apply, correctedDiag]
    rw [mul_comm, ← pow_val_add h3]
    congr 1
    ring_nf
  rw [← TauCeti.diagGL_const, ← map_mul, h]

lemma conj_scalar_eq {F : Type} [Field F] {m : ℕ}
    (U V s : GL (Fin m) F) (c : F)
    (h : (((U * s * U⁻¹)⁻¹ * (V * s * V⁻¹) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = Matrix.scalar (Fin m) c) :
    (((s⁻¹ * (U⁻¹ * V) * s : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) =
      Matrix.scalar (Fin m) c *
        (((U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F))) := by
  let W : GL (Fin m) F := s⁻¹ * (U⁻¹ * V) * s
  change ((W : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = _
  have hW : (U * s * U⁻¹)⁻¹ * (V * s * V⁻¹) = U * W * V⁻¹ := by
    dsimp [W]; group
  rw [hW] at h
  have hWeq : W = U⁻¹ * (U * W * V⁻¹) * V := by group
  have hcoe : ((U * W * V⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.scalar (Fin m) c := by simpa using h
  calc ((W : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
      = ((U⁻¹ * (U * W * V⁻¹) * V : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) :=
          congrArg (fun x : GL (Fin m) F => ((x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) hWeq
    _ = (U⁻¹ : Matrix (Fin m) (Fin m) F) *
          ((U * W * V⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          (V : Matrix (Fin m) (Fin m) F) := by simp
    _ = (U⁻¹ : Matrix (Fin m) (Fin m) F) * Matrix.scalar (Fin m) c *
          (V : Matrix (Fin m) (Fin m) F) := by rw [hcoe]
    _ = Matrix.scalar (Fin m) c *
          ((U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F)) := by
          rw [Matrix.mul_assoc, Matrix.scalar_commute c (fun _ => Commute.all c _),
            ← Matrix.mul_assoc, ← Matrix.scalar_commute c (fun _ => Commute.all c _)]

lemma conj_mul_of_central {G : Type} [Group G] {z : G}
    (hz : ∀ y : G, z * y = y * z) (x y : G) :
    (z * x) * y * (z * x)⁻¹ = x * y * x⁻¹ := by
  calc (z * x) * y * (z * x)⁻¹
      = z * (x * y * x⁻¹) * z⁻¹ := by group
    _ = (x * y * x⁻¹) * z * z⁻¹ := by rw [hz (x * y * x⁻¹)]
    _ = x * y * x⁻¹ := by group

@[expose] noncomputable def conjSU {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hF : Nat.card F = 4) (hζ : orderOf ζ = 3)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {b : G} (hb : b ∈ Bs)
    (s : ↥(unitarySU 2 1 F m)) : ↥(unitarySU 2 1 F m) :=
  ⟨TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) * s *
      (TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b))⁻¹,
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ (correctedDiag_mem_unitarySU hF hζ hdet hb) s.2)
      (Subgroup.inv_mem _ (correctedDiag_mem_unitarySU hF hζ hdet hb))⟩

lemma conjSU_coe {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hF : Nat.card F = 4) (hζ : orderOf ζ = 3)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {b : G} (hb : b ∈ Bs)
    (s : ↥(unitarySU 2 1 F m)) :
    (conjSU hF hζ hdet hb s : GL (Fin m) F) =
      TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ := by
  have hD := diagGL_eq_scalar_mul_correctedDiag (ζ := ζ) hζ hdet b
  have hcent : ∀ x : GL (Fin m) F,
      Matrix.GeneralLinearGroup.scalar (Fin m) (ζ ^ (coordinateSumRoot hdet b).val) * x =
        x * Matrix.GeneralLinearGroup.scalar (Fin m) (ζ ^ (coordinateSumRoot hdet b).val) :=
    fun x => Matrix.GeneralLinearGroup.scalar_commute _ x
  change TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) * s *
      (TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b))⁻¹ = _
  rw [hD, conj_mul_of_central hcent]

lemma correctedDiag_pow_three {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) (b : G)
    (i : Fin m) : (correctedDiag hdet (ζ := ζ) b i) ^ 3 = 1 := by
  simpa [correctedDiag] using pow_pow_three_eq_one hζ (u b i - coordinateSumRoot hdet b).val

lemma permSU_coe {F : Type} [Field F] {m : ℕ}
    (h : UnitaryFieldData 2 1 F) (σ : Equiv.Perm (Fin m)) :
    ((CFSG.SeitzReduction.UnitaryPilot.permSU h σ : unitarySU 2 1 F m) : GL (Fin m) F) =
      TauCeti.permutationGL (k := F) σ⁻¹ := by
  apply Units.ext
  rw [CFSG.SeitzReduction.UnitaryPilot.coe_permSU, TauCeti.permutationGL_coe, inv_inv]

lemma permSU_conj_diagGL {F : Type} [Field F] {m : ℕ}
    (h : UnitaryFieldData 2 1 F) (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ) :
    ((CFSG.SeitzReduction.UnitaryPilot.permSU h σ : unitarySU 2 1 F m) : GL (Fin m) F) *
        TauCeti.diagGL d *
        (((CFSG.SeitzReduction.UnitaryPilot.permSU h σ : unitarySU 2 1 F m) :
          GL (Fin m) F))⁻¹ =
      TauCeti.diagGL (d ∘ ⇑σ) := by
  rw [permSU_coe h σ, TauCeti.permutationGL_mul_diagGL_mul_inv (σ := σ⁻¹)]
  apply congrArg TauCeti.diagGL
  funext i
  simp

lemma permSU_swap_mul_self {F : Type} [Field F] {m : ℕ}
    (h : UnitaryFieldData 2 1 F) {a c : Fin m} :
    CFSG.SeitzReduction.UnitaryPilot.permSU h (Equiv.swap a c) *
        CFSG.SeitzReduction.UnitaryPilot.permSU h (Equiv.swap a c) = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, permSU_coe h, ← map_mul,
    show (Equiv.swap a c)⁻¹ * (Equiv.swap a c)⁻¹ = 1 by
      rw [Equiv.swap_inv, Equiv.swap_mul_self],
    map_one]
  rfl

@[expose] noncomputable def correctedDiagSU {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hF : Nat.card F = 4) (hζ : orderOf ζ = 3)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) (b : G) (hb : b ∈ Bs) :
    ↥(unitarySU 2 1 F m) :=
  ⟨TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b), correctedDiag_mem_unitarySU hF hζ hdet hb⟩

lemma conjSU_phi {G : Type} [Group G] {Bs : Subgroup G}
    {L : Subgroup G} {F : Type} [Field F] {m : ℕ}
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} {u : G → Fin m → ZMod 3}
    (hF : Nat.card F = 4) (hζ : orderOf ζ = 3)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    {b : G} (hb : b ∈ Bs) (s : ↥(unitarySU 2 1 F m)) :
    ((φ (conjSU hF hζ hdet hb s) : ↥L) : G) = b⁻¹ * ((φ s : ↥L) : G) * b :=
  hw b hb s _ (conjSU_coe hF hζ hdet hb s)

lemma diag_phi_mem_Bs {G : Type} [Group G] {B Bs : Subgroup G}
    {L : Subgroup G} (hBs : GGBstar 3 B Bs) {F : Type} [Field F] {m : ℕ}
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    {d : Fin m → Fˣ} (hd3 : ∀ i, d i ^ 3 = 1)
    {t : ↥(unitarySU 2 1 F m)} (ht : (t : GL (Fin m) F) = TauCeti.diagGL d) :
    ((φ t : ↥L) : G) ∈ Bs := by
  have hcent : ((φ t : ↥L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcommD : TauCeti.diagGL (fun i => ζ ^ (u b i).val) * TauCeti.diagGL d =
        TauCeti.diagGL d * TauCeti.diagGL (fun i => ζ ^ (u b i).val) := by
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      rw [Pi.mul_apply, Pi.mul_apply, mul_comm]
    have hEq : (t : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * t *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ := by
      rw [ht, hcommD, mul_assoc, mul_inv_cancel, mul_one]
    have h := hw b hb t t hEq
    calc b * ((φ t : ↥L) : G)
        = b * (b⁻¹ * ((φ t : ↥L) : G) * b) := congrArg (fun x => b * x) h
      _ = ((φ t : ↥L) : G) * b := by group
  have hpow : ((φ t : ↥L) : G) ^ 3 = 1 := by
    have ht3 : t ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ht]
      rw [show (TauCeti.diagGL d) ^ 3 = TauCeti.diagGL (d ^ 3) from
        (map_pow TauCeti.diagGL d 3).symm]
      rw [show d ^ 3 = 1 by funext i; simp [hd3 i]]
      exact map_one _
    have hφ3 : ((φ (t ^ 3) : ↥L) : G) = ((φ t : ↥L) : G) ^ 3 := by
      rw [map_pow]
      rfl
    rw [← hφ3, ht3, map_one]
    rfl
  exact hBs.2.2.2 _ hcent hpow

lemma exists_zpow_mul_diag {G : Type} [Group G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hBs : GGBstar 3 B Bs) (hxBs : x ∈ Bs)
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] {m : ℕ} (hF : Nat.card F = 4)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} (hφs : Function.Surjective φ)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {b : G} (hb : b ∈ Bs) :
    ∃ j : ℤ, b = x ^ j * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹ := by
  have hmem : ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) ∈ Bs :=
    diag_phi_mem_Bs hBs hw (fun i => correctedDiag_pow_three hζ hdet b i) rfl
  have hcent : b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) ∈
      Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨s, hs⟩ := hφs ⟨l, hl⟩
    have hgs : ((φ s : ↥L) : G) = l := congrArg (fun x : ↥L => (x : G)) hs
    rw [← hgs]
    have hφconj : ((φ (conjSU hF hζ hdet hb s) : ↥L) : G) =
        ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) * ((φ s : ↥L) : G) *
          ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹ := by
      rw [show conjSU hF hζ hdet hb s =
          correctedDiagSU hF hζ hdet b hb * s * (correctedDiagSU hF hζ hdet b hb)⁻¹ by
        apply Subtype.ext
        rfl]
      simp [map_mul, map_inv]
    have h1 : ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) * ((φ s : ↥L) : G) *
        ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹ =
        b⁻¹ * ((φ s : ↥L) : G) * b := by
      rw [← hφconj, conjSU_phi hF hζ hdet hw hb s]
    have h2 : (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) * ((φ s : ↥L) : G) *
        (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G))⁻¹ = ((φ s : ↥L) : G) := by
      calc (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) * ((φ s : ↥L) : G) *
            (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G))⁻¹
          = b * (((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) * ((φ s : ↥L) : G) *
              ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹) * b⁻¹ := by group
        _ = b * (b⁻¹ * ((φ s : ↥L) : G) * b) * b⁻¹ := by rw [h1]
        _ = ((φ s : ↥L) : G) := by group
    have h3 : (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) * ((φ s : ↥L) : G) =
        ((φ s : ↥L) : G) * (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) := by
      calc (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) * ((φ s : ↥L) : G)
          = (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) * ((φ s : ↥L) : G) *
              (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G))⁻¹ *
              (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) := by group
        _ = ((φ s : ↥L) : G) * (b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)) := by
              rw [h2]
    exact h3.symm
  have hmem2 : b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) ∈ Bs :=
    Subgroup.mul_mem Bs hb hmem
  have hinf : b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) ∈
      Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hmem2, hcent⟩
  rw [hker] at hinf
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hinf
  refine ⟨j, ?_⟩
  calc b = b * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G) *
        ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹ := by group
    _ = x ^ j * ((φ (correctedDiagSU hF hζ hdet b hb) : ↥L) : G)⁻¹ := by rw [hj]

end CFSG.StandardType.FrameRoute.GlueSwap

end
