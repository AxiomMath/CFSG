module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColMod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Vn_comm (hS : Sit H M S) (δ : Geo H M) {x y : G} (hx : x ∈ Vn δ) (hy : y ∈ Vn δ) :
    x * y = y * x :=
  isElemAbelian_comm (Vn_isElemAbelian hS δ) hx hy

theorem Vn_sq (hS : Sit H M S) (δ : Geo H M) {x : G} (hx : x ∈ Vn δ) : x ^ 2 = 1 :=
  isElemAbelian_pow_eq_one (Vn_isElemAbelian hS δ) hx

omit [Finite G] in
theorem conj_Vn {δ : Geo H M} {g : G} (hg : g ∈ stab δ) {x : G} (hx : x ∈ Vn δ) :
    g * x * g⁻¹ ∈ Vn δ := S35.Ch.conj_mem_Vn hg hx

theorem normalizer_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    stab δ ≤ Subgroup.normalizer (Cb δ : Set G) :=
  (IsModelSec.isSec (hS.orth δ hδ) (S34.Cb_le_Vn δ)).normL

theorem conj_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {g : G}
    (hg : g ∈ stab δ) {x : G} (hx : x ∈ Cb δ) : g * x * g⁻¹ ∈ Cb δ :=
  (Subgroup.mem_normalizer_iff.mp (normalizer_Cb hS hδ hg) x).mp hx

theorem Zv_cent (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {g : G}
    (hg : g ∈ stab δ) {z : G} (hz : z ∈ Zv δ) : g * z * g⁻¹ = z := by
  have := ((hS.glob.central δ hδ) hz).2 g hg
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem hq (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin 5)) := S35.C56.quot_five hS hδ

theorem comm_Vn_Qv' (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ⁅Vn δ, pCoreOf 2 (stab δ)⁆ ≤ Zv δ := (comm_Vn_Qv hS hδ).le

omit [Finite G] in
theorem Cb_comm_L (δ : Geo H M) :
    ∀ c ∈ Cb δ, ∀ a ∈ oTwoRes (stab δ), ⁅a, c⁆ ∈ Zv δ := by
  intro c hc a ha
  have h := Subgroup.mem_centralizer_iff.mp hc.2 a ha
  have : ⁅a, c⁆ = 1 := by rw [commutatorElement_def, h]; group
  rw [this]
  exact (Zv δ).one_mem

theorem Cb_inf_comm_le (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Cb δ ⊓ ⁅Vn δ, oTwoRes (stab δ)⁆ ≤ Zv δ :=
  inf_comm_le_of_orth (hq hS hδ) (Std.Vn_normal δ) (fun _ hx => Vn_sq hS δ hx)
    (fun _ hx _ hy => Vn_comm hS δ hx hy) (S34.Zv_le_Cb hS.glob hδ) (S34.Cb_le_Vn δ)
    (Cb_comm_L δ) (comm_Vn_Qv' hS hδ) (hS.orth δ hδ)

theorem comm_sup_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    ⁅Vn δ, oTwoRes (stab δ)⁆ ⊔ Cb δ = Vn δ :=
  sup_comm_eq_of_orth (hq hS hδ) (S34.Cb_le_Vn δ) (hS.orth δ hδ)

@[expose] def Uc (δ : Geo H M) : Subgroup G := ⁅Vn δ, oTwoRes (stab δ)⁆ ⊔ Zv δ

omit [Finite G] in
theorem Zv_le_Uc (δ : Geo H M) : Zv δ ≤ Uc δ := le_sup_right

theorem comm_Lr_le_Vn (_hS : Sit H M S) (δ : Geo H M) :
    ⁅Vn δ, oTwoRes (stab δ)⁆ ≤ Vn δ := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have h1 := conj_Vn (oTwoRes_le _ ha) ((Vn δ).inv_mem hx)
  have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact (Vn δ).mul_mem hx h1

theorem Uc_le_Vn (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) : Uc δ ≤ Vn δ :=
  sup_le (comm_Lr_le_Vn hS δ) (Std.Zv_le_Vn_S5 hS hδ)

omit [Finite G] in
theorem le_normalizer_sup {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem normalizer_Zv (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    stab δ ≤ Subgroup.normalizer (Zv δ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rwa [Zv_cent hS hδ hg hz]
  · intro hz
    have h1 := Zv_cent hS hδ ((stab δ).inv_mem hg) hz
    have h2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rw [h2] at h1
    rw [h1]
    exact hz

theorem normalizer_Uc (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    stab δ ≤ Subgroup.normalizer (Uc δ : Set G) :=
  le_normalizer_sup (le_normalizer_comm (Std.Vn_normal δ) (le_normalizer_oTwoRes _))
    (normalizer_Zv hS hδ)

theorem conj_Uc (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {g : G}
    (hg : g ∈ stab δ) {x : G} (hx : x ∈ Uc δ) : g * x * g⁻¹ ∈ Uc δ :=
  (Subgroup.mem_normalizer_iff.mp (normalizer_Uc hS hδ hg) x).mp hx

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
