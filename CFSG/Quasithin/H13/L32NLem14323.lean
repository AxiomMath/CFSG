module

public import CFSG.Quasithin.H13.L32NItems143
public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.Quasithin.H13.L32NModule
public import CFSG.Quasithin.Vol2.Ch12Sec8OneModel
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Quasithin.Background.G2Relaxed

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

theorem card_sq_le_of_isotropic {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {B : LinearMap.BilinForm (ZMod 2) W} (hB : B.Nondegenerate) {S : Submodule (ZMod 2) W}
    (hS : ∀ x ∈ S, ∀ y ∈ S, B x y = 0) : Nat.card S ^ 2 ≤ Nat.card W := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hle : S ≤ B.orthogonal S := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => hS x hx y hy
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at h1
  have h2 := Submodule.finrank_le S
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

variable {G : Type} [Group G]

namespace HatModelU

variable {U : Subgroup G} (D : HatModelU U)

theorem π_one : D.π 1 = 0 := by
  have h := D.π_mul 1 U.one_mem 1 U.one_mem
  rw [mul_one] at h
  have h2 : D.π 1 + D.π 1 = D.π 1 + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h2

theorem π_eq_zero {a : G} (ha : a ∈ U) (hc : ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ = 1) : D.π a = 0 := by
  have hZ : a ∈ centerOf U := by
    refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      _ = a * b := by rw [hc b hb, inv_one, one_mul]
  rw [← D.π_one]
  exact (D.π_eq_iff a ha 1 U.one_mem).mpr (by rw [mul_one]; exact (centerOf U).inv_mem hZ)

theorem nondegenerate : D.B.Nondegenerate := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := D.π_surj v
    exact D.π_eq_zero ha fun b hb => (D.B_spec a ha b hb).mp (hv (D.π b))
  · obtain ⟨b, hb, rfl⟩ := D.π_surj v
    refine D.π_eq_zero hb fun a ha => ?_
    have h1 := (D.B_spec a ha b hb).mp (hv (D.π a))
    calc b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1, inv_one]

@[expose] def homOn {A : Subgroup G} (hA : A ≤ U) : ↥A →* Multiplicative D.V where
  toFun a := Multiplicative.ofAdd (D.π a)
  map_one' := by
    show Multiplicative.ofAdd (D.π 1) = 1
    rw [D.π_one]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (D.π ((a : G) * b)) =
      Multiplicative.ofAdd (D.π a) * Multiplicative.ofAdd (D.π b)
    rw [D.π_mul a (hA a.2) b (hA b.2)]
    rfl

theorem homOn_eq_one {A : Subgroup G} (hA : A ≤ U) (a : ↥A) :
    D.homOn hA a = 1 ↔ (a : G) ∈ centerOf U := by
  show Multiplicative.ofAdd (D.π a) = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, ← D.π_one, D.π_eq_iff a (hA a.2) 1 U.one_mem,
    mul_one]
  exact ⟨fun h => by simpa using (centerOf U).inv_mem h, fun h => (centerOf U).inv_mem h⟩

theorem card_eq_mul_range {A : Subgroup G} (hA : A ≤ U) :
    Nat.card A = Nat.card ↥(A ⊓ centerOf U) * Nat.card (D.homOn hA).range := by
  have hker : (D.homOn hA).ker = (A ⊓ centerOf U).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, D.homOn_eq_one, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (D.homOn hA).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (D.homOn hA)).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, mul_comm]

theorem card_U : Nat.card U = Nat.card ↥(centerOf U) * Nat.card D.V := by
  have h := D.card_eq_mul_range le_rfl
  have hr : (D.homOn le_rfl).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro v
    obtain ⟨u, hu, huv⟩ := D.π_surj (Multiplicative.toAdd v)
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [show D.homOn le_rfl ⟨u, hu⟩ = Multiplicative.ofAdd (D.π u) from rfl, huv]
    rfl
  rw [hr, Subgroup.card_top,
    show U ⊓ centerOf U = centerOf U from inf_eq_right.mpr (inf_le_left : centerOf U ≤ U)] at h
  rw [h]
  rfl

theorem card_range_le_hat {A : Subgroup G} (hA : A ≤ U) {B : Subgroup G} (hAB : A ≤ B) :
    Nat.card (D.homOn hA).range ≤ Nat.card (D.hat B) := by
  have hmem : ∀ x ∈ (D.homOn hA).range, Multiplicative.toAdd x ∈ D.hat B := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Submodule.subset_span ⟨a, ⟨hAB a.2, hA a.2⟩, rfl⟩
  refine Nat.card_le_card_of_injective (fun x => ⟨Multiplicative.toAdd x.1, hmem x.1 x.2⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg Subtype.val hxy
  exact Multiplicative.toAdd.injective this

theorem isotropic_hat {A : Subgroup G} (hA : A ≤ U) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ x ∈ D.hat A, ∀ y ∈ D.hat A, D.B x y = 0 := by
  have hgen : ∀ e ∈ A, ∀ x ∈ D.hat A, D.B x (D.π e) = 0 := by
    intro e he x hx
    have hle : D.hat A ≤ LinearMap.ker (D.B.flip (D.π e)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨e', ⟨he', -⟩, rfl⟩
      show D.B (D.π e') (D.π e) = 0
      rw [D.B_spec e' (hA he') e (hA he), hAc e' he' e he]
      group
    exact hle hx
  intro x hx y hy
  have hle : D.hat A ≤ LinearMap.ker (D.B x) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, ⟨he, -⟩, rfl⟩
    exact hgen e he x hx
  exact hle hy

end HatModelU

theorem lemma14323Ge_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11)
    (h12813 : Lemma12_8_13) : Lemma14323Ge := by
  intro G _ _ T L V h
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
  obtain ⟨-, hE, -⟩ := h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  obtain ⟨hVE, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  set E := w128 V (fsuV1 T V) V₂ ⊓ CFSG.conjugate (w128 V (fsuV1 T V) V₂) g with hEdef
  have hEU : E ≤ u128 V (fsuV1 T V) := inf_le_left.trans inf_le_left
  have hVU : V ≤ u128 V (fsuV1 T V) := hVE.trans hEU
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hVhat : Nat.card (D.homOn hVU).range = 4 := by
    have h1 := D.card_eq_mul_range hVU
    rw [hVZ, hV8, hV1] at h1
    omega
  have hiso := card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)
  have h4 : 4 ≤ Nat.card (D.hat E) := hVhat ▸ D.card_range_le_hat hVU hVE
  have h16 : 16 ≤ Nat.card D.V := by nlinarith
  have hcard := D.card_U
  show 2 ^ 4 * Nat.card ↥(centerOf (u128 V (fsuV1 T V))) ≤ Nat.card ↥(u128 V (fsuV1 T V))
  rw [hcard]
  nlinarith

end CFSG.Quasithin.H13
