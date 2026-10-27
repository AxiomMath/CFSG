module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E14Arc
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E14

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem back_facts {β α' m γ' : Geo H M} (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    vtype m = true ∧ vtype γ' = false ∧ γ' ≠ α' ∧ dist β γ' + 3 = bMin H M := by
  obtain ⟨hm, hγ, d1, d2⟩ := hb
  have hd := hp.dist_eq
  have hm' : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  refine ⟨hm', vtype_nbr_S3 hm' hγ, ?_, by omega⟩
  rintro rfl
  omega

theorem Wb_le_stab_back (hS : Sit H M S) {β α' m γ' : Geo H M} (hp : S34.PD β α')
    (hb : Back H M β α' m γ') : Wb β ≤ stab γ' := by
  obtain ⟨-, -, -, h1⟩ := back_facts hp hb
  refine iSup₂_le fun ρ hρ => Vn_le_stab_dist hS ?_
  have h2 := dist_triangle rfl ρ β γ'
  omega

theorem mem_stab_of_centralizes_Zv (hS : Sit H M S) {l ρ : Geo H M} (hl : vtype l = true)
    (hρ : ρ ∈ nbrs l) {x : G} (hx : x ∈ stab l) (hcen : ∀ z ∈ Zv ρ, x * z * x⁻¹ = z) :
    x ∈ stab ρ := by
  let g : ↥(H ⊔ M) := ⟨x, stab_le l hx⟩
  have hgl : (g : G) ∈ stab l := hx
  have hgρ : g • ρ ∈ nbrs l := smul_mem_nbrs_of_stab hgl hρ
  have hZ : Zv (g • ρ) = Zv ρ := by
    rw [Zv_smul]
    ext y
    rw [mem_conjSub]
    constructor
    · intro h
      have := hcen _ h
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [e] at this
      rw [this]
      exact h
    · intro h
      have := hcen y h
      have e : x⁻¹ * y * x = y := by
        have h1 : x * y = y * x := by
          have := congrArg (· * x) this
          simpa [mul_assoc] using this
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [h1]
          _ = y := by group
      show x⁻¹ * y * x ∈ Zv ρ
      rw [e]
      exact h
  have heq : g • ρ = ρ := by
    by_contra hne
    exact (Zv_ne hS hl hgρ hρ hne).1 hZ
  exact mem_stab_of_smul_eq heq

theorem inter_eq_sup (hS : Sit H M S) (hI : CaseI H M) {γ' m α' : Geo H M}
    (hγ : vtype γ' = false) (hm : m ∈ nbrs γ') (hα : α' ∈ nbrs m) (hne : α' ≠ γ')
    {R : Subgroup G} (hR : R ≤ Vn γ' ⊓ Vn α') (hRZ : ¬ R ≤ Zv m) :
    Vn γ' ⊓ Vn α' = R ⊔ Zv m := by
  have hmα : m ∈ nbrs α' := mem_nbrs_symm.mpr hα
  have hm3 : vtype m = true := vtype_nbr_S5 hγ hm
  have hZm : Zv m ≤ Vn γ' ⊓ Vn α' := C1.Zv_le_inter hm hmα
  have hK : R ⊔ Zv m ≤ Vn γ' ⊓ Vn α' := sup_le hR hZm
  have hc8 : Nat.card ↥(Vn γ' ⊓ Vn α') = 8 := (hI γ' m α' hγ hm hmα hne).1
  have hc4 : Nat.card (Zv m) = 4 := hS.cardZ3 m hm3
  have hd1 : Nat.card ↥(R ⊔ Zv m) ∣ 8 := hc8 ▸ Subgroup.card_dvd_of_le hK
  have hd2 : 4 ∣ Nat.card ↥(R ⊔ Zv m) := hc4 ▸ Subgroup.card_dvd_of_le le_sup_right
  have hne4 : Nat.card ↥(R ⊔ Zv m) ≠ 4 := by
    intro h4
    have : Zv m = R ⊔ Zv m :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h4, hc4])
    exact hRZ (this ▸ le_sup_left)
  have h8 : Nat.card ↥(R ⊔ Zv m) = 8 := by
    have hpos : 0 < Nat.card ↥(R ⊔ Zv m) := Nat.card_pos
    have : Nat.card ↥(R ⊔ Zv m) ≤ 8 := Nat.le_of_dvd (by norm_num) hd1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hK (by rw [h8, hc8])).symm

theorem claim14 (hS : Sit H M S) (hI : CaseI H M) (hb7 : 7 ≤ bMin H M)
    (hclaimR : ClaimR H M) (h8b : Claim8b H M) (h16a : Claim16a H M) : Claim14 H M := by
  intro β α' hlam hZ
  have hp : S34.PD β α' := hlam.1
  obtain ⟨m, γ', hm, hγ, d1, d2, -⟩ := PD_geodesic hS hp
  have hb : Back H M β α' m γ' := ⟨hm, hγ, d1, d2⟩
  obtain ⟨hvm, hvγ, hne, -⟩ := back_facts hp hb
  have hmα : α' ∈ nbrs m := mem_nbrs_symm.mpr hm
  have hγm : m ∈ nbrs γ' := mem_nbrs_symm.mpr hγ
  have hWγ : Wb β ≤ stab γ' := Wb_le_stab_back hS hp hb
  obtain ⟨-, hRle, hRZ⟩ := hclaimR β α' m γ' hp hb
  have hRβ : ⁅Vn β, Vn α'⁆ ≤ Wb β :=
    ((PD_comm_le hS hp).trans inf_le_left).trans (Vn_le_Wb_self hS hp.vδ)
  have hcomm := Wb_comm_of_b7 hS hb7 β
  have hinter : Vn γ' ⊓ Vn α' = ⁅Vn β, Vn α'⁆ ⊔ Zv m :=
    inter_eq_sup hS hI hvγ hγm hmα hne.symm (by rwa [inf_comm]) hRZ
  have hZm : Zv m = Zv γ' ⊔ Zv α' := (Zv_ne hS hvm hγ hmα hne).2.1.symm
  obtain ⟨c⟩ : Nonempty (Ch.Chart γ') :=
    Ch.nonempty_chart (Zv_le_Vn_S5 hS hvγ) (C1.caseI_orthSec hS hI hvγ).2
  have hcenZ : ∀ x ∈ Wb β, ∀ z ∈ Zv α', x * z * x⁻¹ = z := fun x hx z hz => by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm x hx z (hZ hz)
  have hWα : Wb β ≤ stab α' := by
    intro x hx
    have hC : Vn γ' ⊓ Vn α' ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [hinter, hZm]
      refine sup_le ?_ (sup_le ?_ ?_)
      · intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm x hx r (hRβ hr)).symm
      · intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp (Zv_central hS hvγ hr).2) x (hWγ hx)).symm
      · intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm x hx r (hZ hr)).symm
    have hcen : ∀ r ∈ Vn γ' ⊓ Vn α', x * r * x⁻¹ = r := fun r hr => by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hr)).symm
    have hxm : x ∈ stab m :=
      mem_stab_of_centralizes hS hI c hvγ hγm hmα hne.symm (hWγ hx) hcen
    exact mem_stab_of_centralizes_Zv hS hvm hmα hxm (hcenZ x hx)
  have hle : Wb β ⊓ stab α' = Wb β := inf_eq_left.mpr hWα
  have h8 := h8b β α' hp (h16a β α' hlam) (by rw [hle, Subgroup.relIndex_self]; norm_num)
  rw [hle, Subgroup.relIndex_self] at h8
  exact absurd h8.2 (by norm_num)

theorem claim15a (h14 : Claim14 H M) (h8b : Claim8b H M) (h9 : Claim9 H M)
    (h16a : Claim16a H M) : Claim15a H M := by
  intro β α' m γ' hlam hb hle
  have hp : S34.PD β α' := hlam.1
  have h2 : (Wb β ⊓ stab m).relIndex (Wb β) ≤ 2 := h9 β α' m γ' hp hb
  have h3 : (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_of_le_left (L := Wb β)
      (le_inf inf_le_left hle))).trans h2
  exact h14 β α' hlam (h8b β α' hp (h16a β α' hlam) h3).1

end S35.E14

end F53.Stellmacher

end CFSG.Quasithin
