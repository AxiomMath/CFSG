module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem comm_Vn_le {β : Geo H M} {B : Subgroup G} (hB : B ≤ stab β) : ⁅Vn β, B⁆ ≤ Vn β := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  have h : b * v⁻¹ * b⁻¹ ∈ Vn β :=
    (Subgroup.mem_normalizer_iff.mp (Vn_normal β (hB hb)) _).mp ((Vn β).inv_mem hv)
  have e : ⁅v, b⁆ = v * (b * v⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (Vn β).mul_mem hv h

theorem Wb_inf_stab_le (hS : Sit H M S) {β m α' : Geo H M} (hvm : vtype m = true)
    (hα' : α' ∈ nbrs m) (hZ : Zv α' ≤ Vn β) : Wb β ⊓ stab m ≤ stab α' := by
  rintro w ⟨hw, hwm⟩
  refine mem_stab_of_centralizes hS hvm hα' hwm fun z hz => ?_
  have h := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (comm_Vn_Wb hS β)) (hZ hz)
  have hzw : w * z = z * w := Subgroup.mem_centralizer_iff.mp h w hw
  rw [hzw]
  group

theorem B_le_Qv (hS : Sit H M S) (h7 : Claim7s H M) (h9 : Claim9 H M)
    {β α' m γ' : Geo H M} (hsec : IsSec (stab β) (Vn β) (Wb β)) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (hZ : Zv α' ≤ Vn β) {B : Subgroup G} (hBV : B ≤ Vn α')
    (hB8 : ⁅Wb β ⊓ stab α', B⁆ ≤ Zv α' ⊔ ⁅Vn β, B⁆) : B ≤ Qv β := by
  intro x hx
  by_contra hxQ
  obtain ⟨hvm, -, -, -, -, -⟩ := back_facts hS hp hb
  have hxs : x ∈ stab β := (PD_Vn_le_stab hS hp).2 (hBV hx)
  have hWst : Wb β ≤ stab β := (Wb_le_Qv hS β).trans (pCoreOf_le 2 _)
  have hNV : Wb β ≤ Subgroup.normalizer (Vn β : Set G) := fun w hw => Vn_normal β (hWst hw)
  have hxV : x ∈ Subgroup.normalizer (Vn β : Set G) := Vn_normal β hxs
  have hWm : Wb β ⊓ stab m ≤ Wb β ⊓ stab α' :=
    fun w hw => ⟨hw.1, Wb_inf_stab_le hS hvm (mem_nbrs_symm.mp hb.1) hZ hw⟩
  have hK2 : (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hWm Subgroup.index_ne_zero_of_finite).trans
      (h9 β α' m γ' hp hb)
  have hBst : B ≤ stab β := hBV.trans (PD_Vn_le_stab hS hp).2
  have hK : ∀ e ∈ Wb β ⊓ stab α', x * e * x⁻¹ * e⁻¹ ∈ Vn β := by
    intro e he
    have h1 : ⁅e, x⁆ ∈ ⁅Wb β ⊓ stab α', B⁆ := Subgroup.commutator_mem_commutator he hx
    have h2 := hB8 h1
    have h3 : Zv α' ⊔ ⁅Vn β, B⁆ ≤ Vn β := sup_le hZ (comm_Vn_le hBst)
    have e1 : x * e * x⁻¹ * e⁻¹ = ⁅e, x⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e1]
    exact (Vn β).inv_mem (h3 h2)
  have h2le := secIdx_le_two_of_le hNV hxV (inf_le_left : Wb β ⊓ stab α' ≤ Wb β) hK2 hK
  have hne2 := h7 β α' hp x (hBV hx) hxQ hsec
  have hpos := S43.secIdx_pos (Subgroup.zpowers x) (Vn β) (Wb β)
  have h1 : secIdx (Subgroup.zpowers x) (Vn β) (Wb β) = 1 := by omega
  rw [S43.secIdx_eq_one_iff hNV hxV] at h1
  exact not_centralizes_Wb hS hp.vδ hxs hxQ h1

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
