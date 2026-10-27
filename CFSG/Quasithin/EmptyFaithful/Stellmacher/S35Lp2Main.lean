module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2W
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Lp2Comm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpEnd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

omit [Finite G] in
theorem img_sup_Cb {δ : Geo H M} (c : Chart2 δ) {U : Subgroup G} (hUV : U ≤ Vn δ) :
    c.img (U ⊔ Cb δ) = c.img U := by
  refine le_antisymm ?_ (c.img_mono le_sup_left)
  have h1 : U ⊔ Cb δ ≤ c.pre (c.img U) := by
    refine sup_le (fun x hx => ?_) (c.Cb_le_pre _)
    exact (c.mem_pre_iff ⟨x, hUV hx⟩).mpr ((c.mem_img_iff').mpr ⟨⟨x, hUV hx⟩, hx, rfl⟩)
  simpa [c.img_pre] using c.img_mono h1

theorem img_comm_eq (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') {d : Perm (Fin 5)}
    (hbar : c.bar (Vn β) = Subgroup.zpowers d) :
    c.img ⁅Vn β, Vn α'⁆ = commW orth (Subgroup.zpowers d) ⊤ := by
  have hA : Vn β ≤ stab α' := (Std.PD_Vn_le_stab hS hp).1
  have h1 := c.img_commSec hA
  rw [hbar] at h1
  rw [← h1]
  unfold commSec
  rw [Subgroup.commutator_comm (Vn α') (Vn β)]
  exact (img_sup_Cb c ((Std.PD_comm_le hS hp).trans inf_le_right)).symm

theorem mem_R_of_img (hS : Sit H M S) (hp : S34.PD β α') (c : Chart2 α') (hU : UC α')
    (hZR : Zv α' ≤ ⁅Vn β, Vn α'⁆) {y : G} (hyV : y ∈ Vn α')
    (hyU : y ∈ ⁅Vn α', stab α'⁆) (h : c.π ⟨y, hyV⟩ ∈ c.img ⁅Vn β, Vn α'⁆) :
    y ∈ ⁅Vn β, Vn α'⁆ := by
  obtain ⟨r, hrR, hr⟩ := (c.mem_img_iff').mp h
  have hRV : ⁅Vn β, Vn α'⁆ ≤ Vn β ⊓ Vn α' := Std.PD_comm_le hS hp
  have hrU : (r : G) ∈ ⁅Vn α', stab α'⁆ := by
    have : ⁅Vn β, Vn α'⁆ ≤ ⁅Vn α', stab α'⁆ := by
      rw [Subgroup.commutator_comm (Vn β)]
      exact Subgroup.commutator_mono le_rfl (Std.PD_Vn_le_stab hS hp).1
    exact this hrR
  have hC : (y : G) * (r : G)⁻¹ ∈ Cb α' := (c.π_eq_iff ⟨y, hyV⟩ r).mp hr.symm
  have hZ : (y : G) * (r : G)⁻¹ ∈ Zv α' :=
    hU ⟨(⁅Vn α', stab α'⁆).mul_mem hyU ((⁅Vn α', stab α'⁆).inv_mem hrU), hC⟩
  have : y = (y * (r : G)⁻¹) * (r : G) := by group
  rw [this]
  exact mul_mem (hZR hZ) hrR

theorem comm_Vn_Wb_le (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Chart2 α') (hU : UC α')
    (hZR : Zv α' ≤ ⁅Vn β, Vn α'⁆) (hWQ : Wb β ≤ Qv m) :
    ∀ x ∈ Vn α', ∀ w ∈ Wb β, x * w * x⁻¹ * w⁻¹ ∈ Vn β := by
  intro x hx w hw
  obtain ⟨d, hdT, hd1, hdd, hbar⟩ := exists_d hS hneg hp hb c hU
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hb.1
  have himg := img_comm_eq hS hp c hbar
  have hRV : ⁅Vn β, Vn α'⁆ ≤ Vn β ⊓ Vn α' := Std.PD_comm_le hS hp
  have hwm : w ∈ stab α' ⊓ stab m :=
    Subgroup.mem_inf.mpr ⟨Std.Qv_le_stab hS (Std.mem_nbrs_symm.mp hb.1) (hWQ hw),
      Ch.Qv_le_stab' m (hWQ hw)⟩
  have hws : w ∈ stab α' := hwm.1
  have hmem : c.θ ⟨w, hws⟩ ∈ c.Dl m := c.mem_bar_of_mem (a := w) hwm hws
  have hcen : ∀ y ∈ commW orth (Subgroup.zpowers d) ⊤, orth.act (c.θ ⟨w, hws⟩) y = y := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨x', hx', rfl⟩ := (c.mem_img_iff').mp hy
    refine (c.comm_mem_iff ⟨w, hws⟩ x').mp ?_
    have hc := comm_of_commutator_eq_bot (Std.comm_Vn_Wb hS β) (hRV hx').1 hw
    show w * (x' : G) * w⁻¹ * (x' : G)⁻¹ ∈ Cb α'
    rw [← hc]
    simp
  have hy : w * x * w⁻¹ * x⁻¹ ∈ Vn α' :=
    (Vn α').mul_mem (Ch.conj_mem_Vn hws hx) ((Vn α').inv_mem hx)
  have hπ : c.π ⟨w * x * w⁻¹ * x⁻¹, hy⟩ =
      orth.act (c.θ ⟨w, hws⟩) (c.π ⟨x, hx⟩) * (c.π ⟨x, hx⟩)⁻¹ := by
    rw [← c.π_conj ⟨w, hws⟩ ⟨x, hx⟩, ← map_inv, ← map_mul]
    rfl
  have hyU : w * x * w⁻¹ * x⁻¹ ∈ ⁅Vn α', stab α'⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hws hx
  have hin : w * x * w⁻¹ * x⁻¹ ∈ ⁅Vn β, Vn α'⁆ := by
    refine mem_R_of_img hS hp c hU hZR hy hyU ?_
    rw [hπ, himg]
    exact comm_le_of_cen_inv hD hdT hd1 hmem hcen _
  have := (⁅Vn β, Vn α'⁆).inv_mem hin
  have e : (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ := by group
  rw [e] at this
  exact (hRV this).1

theorem claimLP_II (hS : Sit H M S) (_hII : CaseII H M) : ClaimLP H M := by
  have hU : ∀ δ : Geo H M, vtype δ = false → UC δ := fun δ hδ => UC.of_sit hS hδ
  by_contra hneg
  obtain ⟨β, α', hp⟩ := exists_PD hS
  obtain ⟨m, γ', hm, hγ, h1, h2, -⟩ := Std.PD_geodesic hS hp
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  obtain ⟨cα⟩ := exists_chart2 hS hp.vδ'
  have hnQ := not_Vn_le_Qv hS hneg hp hb cα (hU _ hp.vδ')
  have hp' : S34.PD α' β := hp.symm' hnQ
  obtain ⟨m', γ'', hm', hγ'', h1', h2', -⟩ := Std.PD_geodesic hS hp'
  have hb' : Back H M α' β m' γ'' := ⟨hm', hγ'', h1', h2'⟩
  obtain ⟨cβ⟩ := exists_chart2 hS hp.vδ
  have hZR := Zv_le_comm hS hneg hp hb hp' hb' cα cβ (hU _ hp.vδ') (hU _ hp.vδ)
  have hZα : Zv α' ≤ Vn β := fun x hx => (Std.PD_comm_le hS hp (hZR hx)).1
  obtain ⟨cγ⟩ := exists_chart2 hS (back_vtype_γ hp hb)
  have hWQ := Wb_le_Qm hS hneg hp hb cγ (hU _ (back_vtype_γ hp hb)) hZα
  have hc := comm_Vn_Wb_le hS hneg hp hb cα (hU _ hp.vδ') hZR hWQ
  exact end_contra hS hp.vδ (Std.PD_Vn_le_stab hS hp).2 hnQ hc

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
