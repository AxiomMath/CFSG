module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.ModelSylow
public import CFSG.Quasithin.Background.F6SQTK
import CFSG.GH74.GLS.SP.Local.SPLPGL2Cartan
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit

public noncomputable section

attribute [local instance] Set.addCommMonoid Set.distribMulActionSet

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open Subgroup
open CFSG.GorensteinWalter CFSG.GH74.GLS.SP.Local.PGL2Cartan
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

section FieldOrbit

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
  [Algebra (ZMod p) K]

omit [Finite K] [CharP K p] in
private theorem exists_dual_ker (H : AddSubgroup K) (hH : H.index = p) :
    ∃ f : K →ₗ[ZMod p] ZMod p, (∀ x, f x = 0 ↔ x ∈ H) ∧ f ≠ 0 := by
  obtain ⟨l, hl⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_hom_of_index_eq_prime H hH
  let f : K →ₗ[ZMod p] ZMod p :=
    @AddMonoidHom.toZModLinearMap p K (ZMod p) inferInstance inferInstance inferInstance
      Semiring.toModule l
  have hf : ∀ x, f x = 0 ↔ x ∈ H := by
    intro x
    change l x = 0 ↔ x ∈ H
    exact hl x
  refine ⟨f, hf, ?_⟩
  intro hf0
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← hf x, hf0]
    rfl
  rw [htop, AddSubgroup.index_top] at hH
  exact (Fact.out : p.Prime).ne_one hH.symm

omit [CharP K p] in
private theorem exists_smul_eq_of_ker_eq {φ ψ : K →ₗ[ZMod p] ZMod p} (hφ : φ ≠ 0)
    (hker : LinearMap.ker φ = LinearMap.ker ψ) : ∃ c : ZMod p, ψ = c • φ := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hψx : ψ x ≠ 0 := by
    intro h0
    apply hx
    have : x ∈ LinearMap.ker ψ := h0
    rw [← hker] at this
    exact this
  have hc : ψ x / φ x ≠ 0 := div_ne_zero hψx hx
  refine ⟨ψ x / φ x, ?_⟩
  symm
  refine Module.Dual.eq_of_ker_eq_of_apply_eq (f := (ψ x / φ x) • φ) (g := ψ) x ?_ ?_ ?_
  · have hkerc : LinearMap.ker ((ψ x / φ x) • φ) = LinearMap.ker φ := by
      ext y
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_mul]
      constructor
      · intro h
        exact (mul_eq_zero.mp h).resolve_left hc
      · intro h
        rw [h, mul_zero]
    rw [hkerc]
    exact hker
  · simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀]
    exact hx
  · simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hx

omit [Finite K] [CharP K p] in
private theorem comp_mulLeft_injective {f : K →ₗ[ZMod p] ZMod p} (hf : f ≠ 0) :
    Function.Injective fun a : K => f.comp (LinearMap.mulLeft (ZMod p) a) := by
  intro a b hab
  by_contra hne
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hzero : ∀ y, f y = 0 := by
    intro y
    have hy : y = (a - b) * (y / (a - b)) := by field_simp
    rw [hy]
    have h1 : f (a * (y / (a - b))) = f (b * (y / (a - b))) := by
      simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using
        congrArg (fun φ => φ (y / (a - b))) hab
    have h2 : f ((a - b) * (y / (a - b))) =
        f (a * (y / (a - b))) - f (b * (y / (a - b))) := by
      rw [sub_mul, map_sub]
      rfl
    rw [h2, h1]
    exact sub_self _
  exact hf (LinearMap.ext hzero)

omit [CharP K p] in
private theorem mem_stabilizer_iff_mem_bot (H : AddSubgroup K) (hH : H.index = p) (a : Kˣ) :
    a ∈ MulAction.stabilizer Kˣ (H : Set K) ↔ (a : K) ∈ (⊥ : Subfield K) := by
  obtain ⟨φ, hφmem, hφ⟩ := exists_dual_ker H hH
  have hφker : ∀ x, φ x = 0 ↔ x ∈ H := hφmem
  constructor
  · intro ha
    have hsmul : a • (H : Set K) = (H : Set K) := ha
    have hmem : ∀ x : K, (a : K) * x ∈ H ↔ x ∈ H := by
      intro x
      have h1 : (a : K) * x ∈ a • (H : Set K) ↔
          (a : K)⁻¹ * ((a : K) * x) ∈ H := by
        rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul,
          Units.val_inv_eq_inv_val]
        exact Iff.rfl
      rw [hsmul] at h1
      have h2 : (a : K)⁻¹ * ((a : K) * x) = x := by field_simp
      simpa [h2] using h1
    have hker : LinearMap.ker φ =
        LinearMap.ker (φ.comp (LinearMap.mulLeft (ZMod p) (a : K))) := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hφker, hφker, hmem]
    obtain ⟨c, hc⟩ := exists_smul_eq_of_ker_eq hφ hker
    have hceq : c • φ =
        φ.comp (LinearMap.mulLeft (ZMod p) (algebraMap (ZMod p) K c)) := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply]
      rw [← Algebra.smul_def, φ.map_smul, smul_eq_mul]
    have haeq : (a : K) = algebraMap (ZMod p) K c :=
      comp_mulLeft_injective hφ (hc.trans hceq)
    rw [Subfield.bot_eq_of_zMod_algebra p]
    exact ⟨c, haeq.symm⟩
  · intro ha
    rw [Subfield.bot_eq_of_zMod_algebra p] at ha
    obtain ⟨c, hc⟩ := ha
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : (a : K) = 0 := by rw [← hc, hc0, map_zero]
      exact a.ne_zero hzero
    have hmem : ∀ x : K, (a : K) * x ∈ H ↔ x ∈ H := by
      intro x
      have hx : (a : K) * x = c • x := by rw [← hc, Algebra.smul_def]
      rw [hx]
      constructor
      · intro h
        have hx' : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hx']
        exact zmod_smul_mem h c⁻¹
      · intro h
        exact zmod_smul_mem h c
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul,
      Units.val_inv_eq_inv_val]
    have h1 : (a : K) * ((a : K)⁻¹ * x) = x := by field_simp
    exact (show x ∈ H ↔ (a : K)⁻¹ * x ∈ H from by
      simpa [h1] using hmem ((a : K)⁻¹ * x)).symm

private theorem card_stabilizer_index_prime (H : AddSubgroup K) (hH : H.index = p) :
    Nat.card (MulAction.stabilizer Kˣ (H : Set K)) = p - 1 := by
  let F : Subfield K := ⊥
  let : Field F := F.toField
  have hstab : ∀ a : Kˣ, a ∈ MulAction.stabilizer Kˣ (H : Set K) ↔ (a : K) ∈ F :=
    mem_stabilizer_iff_mem_bot H hH
  let e : MulAction.stabilizer Kˣ (H : Set K) ≃ Fˣ :=
    { toFun := fun a =>
        Units.mk0 ⟨(a.1 : K), (hstab a.1).mp a.2⟩ (by
          intro h0
          exact a.1.ne_zero (congrArg Subtype.val h0))
      invFun := fun b =>
        ⟨Units.mk0 (b : K) (fun h0 => b.ne_zero (Subtype.ext h0)),
          (hstab _).mpr b.val.2⟩
      left_inv := fun a => Subtype.ext (Units.ext rfl)
      right_inv := fun b => Units.ext rfl }
  calc Nat.card (MulAction.stabilizer Kˣ (H : Set K)) = Nat.card Fˣ := Nat.card_congr e
    _ = Nat.card F - 1 := Nat.card_units (α := F)
    _ = p - 1 := by rw [show F = ⊥ from rfl, Subfield.card_bot]

private theorem card_orbit_index_prime (H : AddSubgroup K) (hH : H.index = p) :
    Nat.card (MulAction.orbit Kˣ (H : Set K)) = (Nat.card K - 1) / (p - 1) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Kˣ := Fintype.ofFinite Kˣ
  let : Fintype (MulAction.orbit Kˣ (H : Set K)) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer Kˣ (H : Set K)) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := Kˣ) (b := (H : Set K))
  have h1 : Nat.card (MulAction.orbit Kˣ (H : Set K)) =
      Fintype.card (MulAction.orbit Kˣ (H : Set K)) := Nat.card_eq_fintype_card
  have h2 : Nat.card (MulAction.stabilizer Kˣ (H : Set K)) =
      Fintype.card (MulAction.stabilizer Kˣ (H : Set K)) := Nat.card_eq_fintype_card
  have h3 : Nat.card Kˣ = Fintype.card Kˣ := Nat.card_eq_fintype_card
  rw [← h1, ← h2, ← h3, card_stabilizer_index_prime H hH, Nat.card_units (α := K)] at h
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  have hpos : 0 < p - 1 := Nat.pos_of_ne_zero hp1
  have hcalc : (Nat.card (MulAction.orbit Kˣ (H : Set K)) * (p - 1)) / (p - 1) =
      Nat.card (MulAction.orbit Kˣ (H : Set K)) := by
    rw [mul_comm, Nat.mul_div_right _ hpos]
  rw [h] at hcalc
  exact hcalc.symm

end FieldOrbit

section Model

variable {K : Type} [Field K]

private noncomputable def uPGL (K : Type) [Field K] : Multiplicative K →* PGL2 K where
  toFun a := Matrix.ProjGenLinGroup.mk (uGL a.toAdd)
  map_one' := by simp [uGL_zero]
  map_mul' a b := by simp [uGL_add]

private theorem uPGL_injective (K : Type) [Field K] : Function.Injective (uPGL K) := by
  intro a b h
  have := mk_uGL_inj h
  exact Multiplicative.toAdd.injective this

private theorem range_uPGL (K : Type) [Field K] : (uPGL K).range = stdU K := by
  ext x
  rw [MonoidHom.mem_range, mem_stdU]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.toAdd, rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨Multiplicative.ofAdd s, hs⟩

variable {p : ℕ}

private def scaleSubgroup (l : Kˣ) (H : AddSubgroup K) : AddSubgroup K where
  carrier := {x : K | (l : K)⁻¹ * x ∈ H}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    show (l : K)⁻¹ * (x + y) ∈ H
    rw [mul_add]
    exact H.add_mem hx hy
  neg_mem' := by
    intro x hx
    show (l : K)⁻¹ * (-x) ∈ H
    rw [mul_neg]
    exact H.neg_mem hx

private theorem scaleSubgroup_coe (l : Kˣ) (H : AddSubgroup K) :
    (scaleSubgroup l H : Set K) = l • (H : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  rfl

private theorem conj_dGL_uPGL (l : Kˣ) (x : K) :
    Matrix.ProjGenLinGroup.mk (dGL l) * uPGL K (Multiplicative.ofAdd x) *
        (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ =
      uPGL K (Multiplicative.ofAdd ((l : K)⁻¹ * x)) := by
  have h := dGL_mul_uGL (F := K) l x
  change Matrix.ProjGenLinGroup.mk (dGL l) * Matrix.ProjGenLinGroup.mk (uGL x) *
      (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ =
    Matrix.ProjGenLinGroup.mk (uGL ((l : K)⁻¹ * x))
  rw [show Matrix.ProjGenLinGroup.mk (dGL l) * Matrix.ProjGenLinGroup.mk (uGL x) *
        (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ =
      Matrix.ProjGenLinGroup.mk (dGL l * uGL x) *
        (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ by rw [map_mul]]
  rw [h, map_mul]
  have hx : x / (l : K) = (l : K)⁻¹ * x := by field_simp
  rw [← hx]
  group

private theorem map_conj_dGL (H : AddSubgroup K) (l : Kˣ) :
    ((AddSubgroup.toSubgroup H).map (uPGL K)).map
        (MulAut.conj (Matrix.ProjGenLinGroup.mk (dGL l))).toMonoidHom =
      (AddSubgroup.toSubgroup (scaleSubgroup l⁻¹ H)).map (uPGL K) := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hconj⟩
    refine ⟨Multiplicative.ofAdd ((l : K)⁻¹ * a.toAdd), ?_, ?_⟩
    · have hmem : ((l⁻¹ : Kˣ) : K)⁻¹ * ((l : K)⁻¹ * a.toAdd) ∈ H := by
        rw [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc, mul_inv_cancel₀ l.ne_zero,
          one_mul]
        exact ha
      exact hmem
    · rw [← hconj]
      exact (conj_dGL_uPGL l a.toAdd).symm
  · rintro ⟨b, hb, rfl⟩
    refine ⟨uPGL K (Multiplicative.ofAdd ((l : K) * b.toAdd)),
      ⟨Multiplicative.ofAdd ((l : K) * b.toAdd), ?_, rfl⟩, ?_⟩
    · have hb' : ((l⁻¹ : Kˣ) : K)⁻¹ * b.toAdd ∈ H := hb
      rw [Units.val_inv_eq_inv_val, inv_inv] at hb'
      exact hb'
    · rw [conj_dGL_uPGL]
      rw [← mul_assoc, inv_mul_cancel₀ l.ne_zero, one_mul]
      rfl

private noncomputable def orbitToSubgroup {H : AddSubgroup K}
    (S : MulAction.orbit Kˣ (H : Set K)) : AddSubgroup K :=
  AddSubgroup.closure S.1

private theorem orbitToSubgroup_coe {H : AddSubgroup K}
    (S : MulAction.orbit Kˣ (H : Set K)) :
    (orbitToSubgroup S : Set K) = S.1 := by
  obtain ⟨a, ha⟩ := S.2
  rw [orbitToSubgroup, ← ha]
  show AddSubgroup.closure (a • (H : Set K)) = a • (H : Set K)
  rw [← scaleSubgroup_coe a H, AddSubgroup.closure_eq]

private theorem orbitToSubgroup_mem {H : AddSubgroup K}
    (S : MulAction.orbit Kˣ (H : Set K)) :
    ∃ a : Kˣ, orbitToSubgroup S = scaleSubgroup a H := by
  obtain ⟨a, ha⟩ := S.2
  refine ⟨a, ?_⟩
  rw [orbitToSubgroup, ← ha]
  show AddSubgroup.closure (a • (H : Set K)) = scaleSubgroup a H
  rw [← scaleSubgroup_coe a H, AddSubgroup.closure_eq]

private noncomputable def orbitToPGL {H : AddSubgroup K}
    (S : MulAction.orbit Kˣ (H : Set K)) : Subgroup (PGL2 K) :=
  (AddSubgroup.toSubgroup (orbitToSubgroup S)).map (uPGL K)

private theorem orbitToPGL_mem {H : AddSubgroup K}
    (S : MulAction.orbit Kˣ (H : Set K)) :
    orbitToPGL S ∈ hypOrbit (torus0 K) ((AddSubgroup.toSubgroup H).map (uPGL K)) := by
  obtain ⟨a, ha⟩ := orbitToSubgroup_mem S
  refine ⟨Matrix.ProjGenLinGroup.mk (dGL a⁻¹), mk_dGL_mem_torus0 a⁻¹, ?_⟩
  rw [orbitToPGL, ha]
  have haa : a = (a⁻¹)⁻¹ := by simp
  rw [haa]
  exact (map_conj_dGL H a⁻¹).symm

private theorem orbitToPGL_injective {H : AddSubgroup K} :
    Function.Injective (orbitToPGL (H := H)) := by
  intro S T h
  have h1 : orbitToSubgroup S = orbitToSubgroup T := by
    have h2 : (AddSubgroup.toSubgroup (orbitToSubgroup S)) =
        (AddSubgroup.toSubgroup (orbitToSubgroup T)) :=
      Subgroup.map_injective (uPGL_injective K) h
    exact (AddSubgroup.toSubgroup (A := K)).injective h2
  have h3 : S.1 = T.1 := by
    rw [← orbitToSubgroup_coe S, ← orbitToSubgroup_coe T, h1]
  exact Subtype.ext h3

private theorem ncard_hypOrbit_torus0_stdU {e : ℕ} [Finite K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (hK : Nat.card K = p ^ e) (_he : 0 < e)
    {D : Subgroup (PGL2 K)} (hD : D ∈ hyperplanes p (stdU K)) :
    (p ^ e - 1) / (p - 1) ≤ (hypOrbit (torus0 K) D).ncard := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) K →* PGL2 K)
      Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (Subgroup (PGL2 K)) :=
    Finite.of_injective (fun H : Subgroup (PGL2 K) => (H : Set (PGL2 K)))
      (fun _ _ h => SetLike.ext (fun x => by
        have := congrArg (fun S : Set (PGL2 K) => x ∈ S) h
        simpa using this))
  let Dsub : Subgroup (Multiplicative K) := D.comap (uPGL K)
  let H : AddSubgroup K := (AddSubgroup.toSubgroup (A := K)).symm Dsub
  have hHmap : (AddSubgroup.toSubgroup H).map (uPGL K) = D := by
    have h1 : (AddSubgroup.toSubgroup H) = Dsub := rfl
    rw [h1]
    exact Subgroup.map_comap_eq_self (by rw [range_uPGL]; exact hD.1)
  have hHidx : H.index = p := by
    have h1 : H.index = Dsub.index := rfl
    rw [h1, Subgroup.index_comap, range_uPGL]
    exact hD.2
  rw [← hHmap]
  let target := hypOrbit (torus0 K) ((AddSubgroup.toSubgroup H).map (uPGL K))
  have hmem : ∀ S : MulAction.orbit Kˣ (H : Set K), orbitToPGL S ∈ target :=
    fun S => orbitToPGL_mem S
  let f : MulAction.orbit Kˣ (H : Set K) → ↥target :=
    fun S => ⟨orbitToPGL S, hmem S⟩
  have hf : Function.Injective f := by
    intro S T h
    exact orbitToPGL_injective (congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective f hf
  rw [card_orbit_index_prime H hHidx] at hle
  rw [hK] at hle
  rw [Nat.card_coe_set_eq] at hle
  exact hle

end Model


section Transport

variable {G H : Type} [Group G] [Group H]

private theorem map_conj_map (ψ : G ≃* H) (D : Subgroup G) (n : G) :
    (D.map (MulAut.conj n).toMonoidHom).map ψ.toMonoidHom =
      (D.map ψ.toMonoidHom).map (MulAut.conj (ψ n)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, map_mul]

private theorem ncard_hypOrbit_map_equiv (ψ : G ≃* H) (N D : Subgroup G) :
    (hypOrbit N D).ncard =
      (hypOrbit (N.map ψ.toMonoidHom) (D.map ψ.toMonoidHom)).ncard := by
  apply Set.ncard_congr (fun D' _ => D'.map ψ.toMonoidHom)
  · rintro D' ⟨n, hn, rfl⟩
    exact ⟨ψ n, Subgroup.mem_map_of_mem _ hn, map_conj_map ψ D n⟩
  · intro D1 D2 _ _ h
    exact Subgroup.map_injective ψ.injective h
  · rintro E ⟨n, hn, rfl⟩
    obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
    exact ⟨D.map (MulAut.conj n₀).toMonoidHom, ⟨n₀, hn₀, rfl⟩,
      map_conj_map ψ D n₀⟩

end Transport

section SubgroupOf

variable {G : Type} [Group G] {A N D E : Subgroup G}

private theorem map_conj_map_subtype (hD : D ≤ A) (n : A) :
    ((D.subgroupOf A).map (MulAut.conj n).toMonoidHom).map A.subtype =
      D.map (MulAut.conj (n : G)).toMonoidHom := by
  have hcomp : A.subtype.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp A.subtype := by
    ext a
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map]
  rw [hcomp]
  rw [← Subgroup.map_map]
  rw [Subgroup.map_subgroupOf_eq_of_le hD]

private theorem ncard_hypOrbit_subgroupOf (hN : N ≤ A) (hD : D ≤ A) :
    (hypOrbit (N.subgroupOf A) (D.subgroupOf A)).ncard = (hypOrbit N D).ncard := by
  apply Set.ncard_congr (fun H _ => H.map A.subtype)
  · rintro H ⟨n, hn, rfl⟩
    exact ⟨(n : G), hn, map_conj_map_subtype hD n⟩
  · intro H1 H2 _ _ h
    exact Subgroup.map_injective A.subtype_injective h
  · rintro E ⟨n, hn, rfl⟩
    let nA : A := ⟨n, hN hn⟩
    exact ⟨(D.subgroupOf A).map (MulAut.conj nA).toMonoidHom, ⟨nA, hn, rfl⟩,
      map_conj_map_subtype hD nA⟩

private theorem subgroupOf_inf_normalizer (hEA : E ≤ A) :
    (A ⊓ normalizer (E : Set G)).subgroupOf A = normalizer (E.subgroupOf A) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨hxA, hxN⟩ y
    constructor
    · intro hy
      exact (Subgroup.mem_normalizer_iff.mp hxN (y : G)).1 hy
    · intro hy
      exact (Subgroup.mem_normalizer_iff.mp hxN (y : G)).2 hy
  · intro hN
    refine ⟨x.property, ?_⟩
    intro g
    constructor
    · intro hg
      have hgA : g ∈ A := hEA hg
      exact (hN ⟨g, hgA⟩).1 hg
    · intro hg
      have hgA : g ∈ A := by
        have hxg : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
        rw [hxg]
        exact A.mul_mem (A.mul_mem (A.inv_mem x.property) (hEA hg)) x.property
      exact (hN ⟨g, hgA⟩).2 hg

end SubgroupOf


variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {p e : ℕ}

open CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.Blueprint (LieModel)

theorem exists_conj_eq_pow_of_isPGL2 (hM : LieModel ↥L .PSL 2 p 1) (hp2 : p ≠ 2) (hLA : L ≤ A)
    (hA : F6.IsPGL2 p ↥A) {E : Subgroup G} (hE : IsSylowIn p E L) {c : ℕ} (hc : ¬ p ∣ c) :
    ∃ n ∈ A, ∀ x ∈ E, n * x * n⁻¹ = x ^ c := by
  classical
  have hp : p.Prime := hM.admissible.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEelem, hEcard⟩ := isElemAbelian_of_isSylowIn (e := 1) hM hp2 hE
  have hEcard' : Nat.card E = p := by simpa using hEcard
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eA⟩⟩ := hA
  let : Fintype K := Fintype.ofFinite K
  have hchar : CharP K p := by
    refine charP_of_card_eq_prime_pow (p := p) (f := 1) ?_
    rw [← Nat.card_eq_fintype_card, hKcard, pow_one]
  let : CharP K p := hchar
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hoddK : Odd (Nat.card K) := by
    rw [hKcard]
    exact hp.odd_of_ne_two hp2
  let eP : (GL (Fin 2) K ⧸ CFSG.Open.StatedScalars (Fin 2) K) ≃* PGL2 K :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_eq_center (Fin 2) K)
  let ψ : ↥A ≃* PGL2 K := eA.trans eP
  let E_A : Subgroup ↥A := E.subgroupOf A
  have hEAcard : Nat.card E_A = Nat.card K := by
    calc Nat.card E_A = Nat.card E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE.1.trans hLA)).toEquiv
      _ = Nat.card K := by rw [hEcard', hKcard]
  have hEA'card : Nat.card ↥(E_A.map ψ.toMonoidHom) = Nat.card K := by
    rw [Subgroup.card_map_of_injective ψ.injective, hEAcard]
  obtain ⟨g, hg⟩ := exists_conj_stdU hoddK hEA'card
  let ψ' : ↥A ≃* PGL2 K := ψ.trans (MulAut.conj g)
  have hψ'E : E_A.map ψ' = stdU K := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      have h1 := (hg (ψ a)).mp (Subgroup.mem_map_of_mem ψ.toMonoidHom ha)
      simpa [ψ', MulAut.conj_apply] using h1
    · intro hx
      have hxx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      have h1 : g⁻¹ * x * g ∈ E_A.map ψ.toMonoidHom :=
        (hg (g⁻¹ * x * g)).mpr (by simpa [hxx] using hx)
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp h1
      refine ⟨a, ha, ?_⟩
      have h2 : ψ a = g⁻¹ * x * g := hae
      calc ψ' a = g * ψ a * g⁻¹ := rfl
        _ = x := by rw [h2]; group
  have hcK : (c : K) ≠ 0 := by
    intro h0
    exact hc ((CharP.cast_eq_zero_iff K p c).mp h0)
  let l : Kˣ := Units.mk0 ((c : K)⁻¹) (inv_ne_zero hcK)
  have hl : (l : K)⁻¹ = (c : K) := by
    show ((c : K)⁻¹)⁻¹ = (c : K)
    rw [inv_inv]
  refine ⟨(ψ'.symm (Matrix.ProjGenLinGroup.mk (dGL l)) : ↥A), ?_, ?_⟩
  · exact Subtype.coe_prop _
  · intro x hx
    have hxA : x ∈ A := hLA (hE.1 hx)
    let xA : ↥A := ⟨x, hxA⟩
    have hxE_A : xA ∈ E_A := hx
    have hxstd : ψ' xA ∈ stdU K := by
      rw [← hψ'E]
      exact Subgroup.mem_map_of_mem ψ'.toMonoidHom hxE_A
    have hxrange : ψ' xA ∈ (uPGL K).range := by rwa [range_uPGL]
    obtain ⟨a, ha⟩ : ∃ a : Multiplicative K, uPGL K a = ψ' xA :=
      MonoidHom.mem_range.mp hxrange
    have hconj : Matrix.ProjGenLinGroup.mk (dGL l) * ψ' xA *
        (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ =
        uPGL K (Multiplicative.ofAdd ((l : K)⁻¹ * a.toAdd)) := by
      rw [← ha]
      simpa using conj_dGL_uPGL l a.toAdd
    have hpow : (ψ' xA) ^ c = uPGL K (Multiplicative.ofAdd (c • a.toAdd)) := by
      rw [← ha, ← map_pow]
      congr 1
    have hgoalA : ψ'.symm (Matrix.ProjGenLinGroup.mk (dGL l)) * xA *
        (ψ'.symm (Matrix.ProjGenLinGroup.mk (dGL l)))⁻¹ = xA ^ c := by
      apply ψ'.injective
      rw [map_mul, map_mul, map_inv]
      simp only [MulEquiv.apply_symm_apply]
      rw [map_pow, hconj, hpow]
      congr 2
      rw [hl, ← smul_eq_mul, Nat.cast_smul_eq_nsmul]
    have hxG : (xA : G) = x := rfl
    rw [← hxG]
    have hcoe : (↑xA : G) ^ c = ((xA ^ c : ↥A) : G) := by simp
    rw [hcoe]
    simpa using congrArg (fun y : ↥A => (y : G)) hgoalA


theorem ncard_hypOrbit_of_isPGL2 (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2) (hLA : L ≤ A)
    (hA : F6.IsPGL2 (p ^ e) ↥A) {E : Subgroup G} (hE : IsSylowIn p E L) {D : Subgroup G}
    (hD : D ∈ hyperplanes p E) :
    (p ^ e - 1) / (p - 1) ≤ (hypOrbit (A ⊓ normalizer (E : Set G)) D).ncard := by
  classical
  have hp : p.Prime := hM.admissible.1
  have he : 0 < e := by
    have := hM.admissible.2.1
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEelem, hEcard⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eA⟩⟩ := hA
  let : Fintype K := Fintype.ofFinite K
  have hchar : CharP K p := by
    refine charP_of_card_eq_prime_pow (p := p) (f := e) ?_
    rw [← Nat.card_eq_fintype_card, hKcard]
  let : CharP K p := hchar
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hoddK : Odd (Nat.card K) := by
    rw [hKcard]
    exact Odd.pow (n := e) (hp.odd_of_ne_two hp2)
  let eP : (GL (Fin 2) K ⧸ CFSG.Open.StatedScalars (Fin 2) K) ≃* PGL2 K :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_eq_center (Fin 2) K)
  let ψ : ↥A ≃* PGL2 K := eA.trans eP
  let E_A : Subgroup ↥A := E.subgroupOf A
  have hEAcard : Nat.card E_A = Nat.card K := by
    calc Nat.card E_A = Nat.card E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE.1.trans hLA)).toEquiv
      _ = Nat.card K := by rw [hEcard, hKcard]
  have hEA'card : Nat.card ↥(E_A.map ψ.toMonoidHom) = Nat.card K := by
    rw [Subgroup.card_map_of_injective ψ.injective, hEAcard]
  obtain ⟨g, hg⟩ := exists_conj_stdU hoddK hEA'card
  let ψ' : ↥A ≃* PGL2 K := ψ.trans (MulAut.conj g)
  have hψ'E : E_A.map ψ' = stdU K := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      have h1 := (hg (ψ a)).mp (Subgroup.mem_map_of_mem ψ.toMonoidHom ha)
      simpa [ψ', MulAut.conj_apply] using h1
    · intro hx
      have hxx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      have h1 : g⁻¹ * x * g ∈ E_A.map ψ.toMonoidHom :=
        (hg (g⁻¹ * x * g)).mpr (by simpa [hxx] using hx)
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp h1
      refine ⟨a, ha, ?_⟩
      have h2 : ψ a = g⁻¹ * x * g := hae
      calc ψ' a = g * ψ a * g⁻¹ := rfl
        _ = x := by rw [h2]; group
  let D_A : Subgroup ↥A := D.subgroupOf A
  have hD_A : D_A ∈ hyperplanes p E_A := by
    refine ⟨Subgroup.subgroupOf_mono A hD.1, ?_⟩
    rw [Subgroup.relIndex_subgroupOf (hE.1.trans hLA)]
    exact hD.2
  let Dψ : Subgroup (PGL2 K) := D_A.map ψ'.toMonoidHom
  have hDψ : Dψ ∈ hyperplanes p (stdU K) := by
    refine ⟨?_, ?_⟩
    · rw [← hψ'E]
      exact Subgroup.map_mono hD_A.1
    · have hinj : Function.Injective (ψ'.toMonoidHom : ↥A → PGL2 K) :=
        fun a b h => ψ'.injective h
      rw [← hψ'E]
      change (D_A.map ψ'.toMonoidHom).relIndex (E_A.map ψ'.toMonoidHom) = p
      rw [Subgroup.relIndex_map_map_of_injective D_A E_A hinj]
      exact hD_A.2
  have : Finite (PGL2 K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) K →* PGL2 K)
      Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (Subgroup (PGL2 K)) :=
    Finite.of_injective (fun H : Subgroup (PGL2 K) => (H : Set (PGL2 K)))
      (fun _ _ h => SetLike.ext (fun x => by
        have := congrArg (fun S : Set (PGL2 K) => x ∈ S) h
        simpa using this))
  have htorus : torus0 K ≤ Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact torus0_normalizes ht hy
    · intro hy
      have h1 := torus0_normalizes ((torus0 K).inv_mem ht) hy
      have h2 : (t : PGL2 K)⁻¹ * (t * y * t⁻¹) * t = y := by group
      simpa [h2] using h1
  have hsubset : hypOrbit (torus0 K) Dψ ⊆
      hypOrbit (Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K))) Dψ := by
    rintro E' ⟨t, ht, rfl⟩
    exact ⟨t, htorus ht, rfl⟩
  have hle1 : (hypOrbit (torus0 K) Dψ).ncard ≤
      (hypOrbit (Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K))) Dψ).ncard :=
    Set.ncard_le_ncard hsubset (Set.toFinite _)
  have heq1 :
      (hypOrbit (Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K)))
        Dψ).ncard = (hypOrbit (Subgroup.normalizer E_A) D_A).ncard := by
    have hψN : Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K)) =
        (Subgroup.normalizer E_A).map ψ'.toMonoidHom := by
      rw [← hψ'E]
      exact (Subgroup.map_equiv_normalizer_eq E_A ψ').symm
    rw [hψN]
    change (hypOrbit ((Subgroup.normalizer E_A).map ψ'.toMonoidHom)
        (D_A.map ψ'.toMonoidHom)).ncard = (hypOrbit (Subgroup.normalizer E_A) D_A).ncard
    exact (ncard_hypOrbit_map_equiv ψ' (Subgroup.normalizer E_A) D_A).symm
  have heq2 : (hypOrbit (Subgroup.normalizer E_A) D_A).ncard =
      (hypOrbit (A ⊓ normalizer (E : Set G)) D).ncard := by
    have hN : (A ⊓ normalizer (E : Set G)).subgroupOf A = Subgroup.normalizer E_A :=
      subgroupOf_inf_normalizer (hE.1.trans hLA)
    have h := ncard_hypOrbit_subgroupOf (N := A ⊓ normalizer (E : Set G)) (D := D)
      inf_le_left (hD.1.trans (hE.1.trans hLA))
    rwa [hN] at h
  have hmodel := ncard_hypOrbit_torus0_stdU hKcard he hDψ
  calc (p ^ e - 1) / (p - 1) ≤ (hypOrbit (torus0 K) Dψ).ncard := hmodel
    _ ≤ (hypOrbit (Subgroup.normalizer ((stdU K : Subgroup (PGL2 K)) : Set (PGL2 K)))
          Dψ).ncard := hle1
    _ = (hypOrbit (Subgroup.normalizer E_A) D_A).ncard := heq1
    _ = (hypOrbit (A ⊓ normalizer (E : Set G)) D).ncard := heq2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

end
