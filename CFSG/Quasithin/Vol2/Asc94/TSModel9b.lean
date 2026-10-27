module

public import CFSG.Quasithin.Vol2.Asc94.TSModel9a
public import CFSG.Quasithin.Vol2.Asc94.TSModel3
public import CFSG.Quasithin.Vol2.Asc94.TSGen

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S
open scoped commutatorElement

instance instNormalQh : Qh.Normal := MonoidHom.normal_ker piHom

theorem TQ_conj_mem {q : Hc} (hq : q ∈ TQ) (g : Hc) : g⁻¹ * q * g ∈ TQ := by
  obtain ⟨hQ, hsq, h1, hU1, hU2⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := Subgroup.Normal.conj_mem instNormalQh q hQ g⁻¹
    rwa [inv_inv] at this
  · calc g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g := by group
      _ = 1 := by rw [hsq]; group
  · intro h
    apply h1
    have : q = g * (g⁻¹ * q * g) * g⁻¹ := by group
    rw [this, h]
    group
  · intro h
    apply hU1
    have := U1_normal_conj g h
    rwa [show g * (g⁻¹ * q * g) * g⁻¹ = q by group] at this
  · intro h
    apply hU2
    have := U2_normal_conj g h
    rwa [show g * (g⁻¹ * q * g) * g⁻¹ = q by group] at this

theorem orbit_tz : {x : Hc | ∃ l ∈ (⊤ : Subgroup Hc), x = l⁻¹ * tz * l} = TQ := by
  ext x
  constructor
  · rintro ⟨l, -, rfl⟩
    exact TQ_conj_mem tz_mem_TQ l
  · intro hx
    obtain ⟨g, hg⟩ := TQ_conj_tz hx
    exact ⟨g, Subgroup.mem_top _, hg⟩

theorem card_centralizer_tz : Nat.card ↥(Subgroup.centralizer ({tz} : Set Hc)) = 2 ^ 9 := by
  have h := Gen.card_conjOrbit_mul_card_stab (⊤ : Subgroup Hc) tz
  have e1 : Nat.card {x : Hc // ∃ l ∈ (⊤ : Subgroup Hc), x = l⁻¹ * tz * l} = 42 := by
    have h2 : Nat.card ↥TQ = 42 := by rw [Nat.card_coe_set_eq, ncard_TQ]
    rw [← h2]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Set.ext_iff.1 orbit_tz x)
  rw [e1, top_inf_eq, Subgroup.card_top, card_Hc] at h
  omega

theorem centralizer_conj_eq (t g : Hc) :
    Subgroup.centralizer ({g⁻¹ * t * g} : Set Hc) =
      (Subgroup.centralizer ({t} : Set Hc)).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hx]
        _ = t * (g * x * g⁻¹) := by group
    · show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    show g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * t * g) = g⁻¹ * t * g * (g⁻¹ * y * g⁻¹⁻¹)
    calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
      _ = g⁻¹ * (t * y) * g := by rw [hy]
      _ = g⁻¹ * t * g * (g⁻¹ * y * g⁻¹⁻¹) := by group

theorem card_centralizer_TQ {t : Hc} (ht : t ∈ TQ) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set Hc)) = 2 ^ 9 := by
  obtain ⟨g, rfl⟩ := TQ_conj_tz ht
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := fun a b h =>
    (MulAut.conj g⁻¹).injective h
  rw [centralizer_conj_eq, Subgroup.card_map_of_injective hinj]
  exact card_centralizer_tz

theorem inv_eq_self_of_sq {x : Hc} (h : x * x = 1) : x⁻¹ = x := inv_eq_of_mul_eq_one_right h

theorem comm_eq_of_sq {x y : Hc} (hx : x * x = 1) (hy : y * y = 1) : ⁅x, y⁆ = x * y * x * y := by
  rw [commutatorElement_def, inv_eq_self_of_sq hx, inv_eq_self_of_sq hy]

@[expose] def sA : Hc := mkH !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def u12 : Hc := mkH !![1, 0, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def u23 : Hc := mkH !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def u02 : Hc := mkH !![1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def u24 : Hc := mkH !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sA_sq : sA * sA = 1 := cm_injective (by rw [cm_mul, cm_one]; decide +kernel)
theorem u12_sq : u12 * u12 = 1 := cm_injective (by rw [cm_mul, cm_one]; decide +kernel)
theorem u23_sq : u23 * u23 = 1 := cm_injective (by rw [cm_mul, cm_one]; decide +kernel)
theorem u02_sq : u02 * u02 = 1 := cm_injective (by rw [cm_mul, cm_one]; decide +kernel)
theorem u24_sq : u24 * u24 = 1 := cm_injective (by rw [cm_mul, cm_one]; decide +kernel)

theorem sA_comm : sA * tz = tz * sA := cm_injective (by rw [cm_mul, cm_mul]; decide +kernel)
theorem u12_comm : u12 * tz = tz * u12 := cm_injective (by rw [cm_mul, cm_mul]; decide +kernel)
theorem u23_comm : u23 * tz = tz * u23 := cm_injective (by rw [cm_mul, cm_mul]; decide +kernel)

theorem comm_sA_u12 : ⁅sA, u12⁆ = u02 := by
  rw [comm_eq_of_sq sA_sq u12_sq]
  exact cm_injective (by rw [cm_mul, cm_mul, cm_mul]; decide +kernel)

theorem comm_u23_sA : ⁅u23, sA⁆ = u24 := by
  rw [comm_eq_of_sq u23_sq sA_sq]
  exact cm_injective (by rw [cm_mul, cm_mul, cm_mul]; decide +kernel)

theorem comm_u02_u24 : ⁅u02, u24⁆ = zt := by
  rw [comm_eq_of_sq u02_sq u24_sq]
  exact cm_injective (by rw [cm_mul, cm_mul, cm_mul, cm_zt]; decide +kernel)

theorem zt_mem_comm2 :
    zt ∈ ⁅⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆,
      ⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆⁆ := by
  have hsA : sA ∈ Subgroup.centralizer ({tz} : Set Hc) :=
    Subgroup.mem_centralizer_singleton_iff.2 sA_comm
  have h12 : u12 ∈ Subgroup.centralizer ({tz} : Set Hc) :=
    Subgroup.mem_centralizer_singleton_iff.2 u12_comm
  have h23 : u23 ∈ Subgroup.centralizer ({tz} : Set Hc) :=
    Subgroup.mem_centralizer_singleton_iff.2 u23_comm
  have ha : u02 ∈ ⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆ := by
    rw [← comm_sA_u12]
    exact Subgroup.commutator_mem_commutator hsA h12
  have hb : u24 ∈ ⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆ := by
    rw [← comm_u23_sA]
    exact Subgroup.commutator_mem_commutator h23 hsA
  rw [← comm_u02_u24]
  exact Subgroup.commutator_mem_commutator ha hb

theorem derived2_centralizer_tz :
    ⁅⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆,
      ⁅Subgroup.centralizer ({tz} : Set Hc), Subgroup.centralizer ({tz} : Set Hc)⁆⁆ =
      Subgroup.zpowers zt := by
  have hST : Subgroup.centralizer ({tz} : Set Hc) ≤ Tm := fun h hh =>
    tz_cent_le_Tm h (Subgroup.mem_centralizer_singleton_iff.1 hh)
  apply le_antisymm
  · exact (Subgroup.commutator_mono (Subgroup.commutator_mono hST hST)
      (Subgroup.commutator_mono hST hST)).trans comm2_Tm_le_Z
  · rw [Subgroup.zpowers_le]
    exact zt_mem_comm2

theorem derived2_centralizer_TQ {t : Hc} (ht : t ∈ TQ) :
    ⁅⁅Subgroup.centralizer ({t} : Set Hc), Subgroup.centralizer ({t} : Set Hc)⁆,
      ⁅Subgroup.centralizer ({t} : Set Hc), Subgroup.centralizer ({t} : Set Hc)⁆⁆ =
      Subgroup.zpowers zt := by
  obtain ⟨g, rfl⟩ := TQ_conj_tz ht
  rw [centralizer_conj_eq]
  simp only [← Subgroup.map_commutator]
  rw [derived2_centralizer_tz, MonoidHom.map_zpowers]
  have hc := Subgroup.mem_center_iff.1 zt_central g⁻¹
  have : (MulAut.conj g⁻¹).toMonoidHom zt = zt := by
    show g⁻¹ * zt * g⁻¹⁻¹ = zt
    calc g⁻¹ * zt * g⁻¹⁻¹ = zt * g⁻¹ * g⁻¹⁻¹ := by rw [← hc]
      _ = zt := by group
  rw [this]

end CFSG.Quasithin.A94.L52
