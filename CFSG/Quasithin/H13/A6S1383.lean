module

public import CFSG.Quasithin.H13.A6S1373
public import CFSG.Quasithin.H13.A6S1512

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def TransList : List (Perm (Fin 6)) :=
  [1, swap 0 4 * swap 4 2 * swap 1 5 * swap 5 3, swap 0 4 * swap 4 3 * swap 3 1 * swap 2 5,
    swap 0 4 * swap 4 2 * swap 2 1 * swap 3 5, swap 0 4 * swap 4 5 * swap 5 2 * swap 2 1,
    swap 0 4 * swap 4 3 * swap 3 2 * swap 2 1, swap 1 4 * swap 4 2 * swap 2 5 * swap 5 3,
    swap 1 4 * swap 4 3 * swap 3 5 * swap 5 2, swap 1 4 * swap 4 5 * swap 5 3 * swap 3 2,
    swap 1 4 * swap 4 2, swap 2 4 * swap 3 5, swap 2 4 * swap 4 5, swap 2 4 * swap 4 3,
    swap 3 4 * swap 4 5, swap 3 5 * swap 5 4]

theorem transList_mem : ∀ σ ∈ TransList, σ ∈ alternatingGroup (Fin 6) := by
  intro σ hσ
  rw [Equiv.Perm.mem_alternatingGroup]
  revert σ
  decide +kernel

theorem trans_W4 : ∀ x : P6, InW4 x → x ≠ 1 → ∃ σ ∈ TransList, act4f σ x = e0123 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L_conj_z {y : G} (hy : y ∈ V) (hy1 : y ≠ 1) :
    ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧ (l : G) * y * (l : G)⁻¹ = S.z := by
  have hψ1 : ((S.frame.ψ ⟨y, hy⟩ : ↥W4) : P6) ≠ 1 := by
    intro h
    apply hy1
    have : (⟨y, hy⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
    exact congrArg Subtype.val this
  obtain ⟨σ, hσ, hσy⟩ := trans_W4 _ (S.frame.ψ ⟨y, hy⟩).2 hψ1
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L σ).2 (transList_mem σ hσ)
  refine ⟨l, hlL, ?_⟩
  have h1 := S.psi_conj l ⟨y, hy⟩
  have h2 : S.frame.ψ ⟨(l : G) * y * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp l.2 y).mp hy⟩ =
      S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
    rw [h1, S.psi_z]
    apply Subtype.ext
    rw [hρl]
    exact hσy
  exact congrArg Subtype.val (S.frame.ψ.injective h2)

theorem comm_conjSub_V_eq_bot (h1378 : IsMulCommutative ↥(conjClosure V S.G1)) {g : G}
    (hg : fsuV1 T V ≤ conjSub g⁻¹ V) : ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
  have hzV1 : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hy : g * S.z * g⁻¹ ∈ V := by
    have := hg hzV1
    rwa [mem_conjSub, inv_inv] at this
  have hy1 : g * S.z * g⁻¹ ≠ 1 := by
    intro h
    apply S.z_ne_one
    have e : S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    rw [e, h]
    group
  obtain ⟨l, hlL, hlz⟩ := S.exists_L_conj_z hy hy1
  have hg' : (l : G) * g ∈ S.G1 := by
    show (l : G) * g ∈ Subgroup.centralizer ({S.z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (l : G) * g * S.z = ((l : G) * (g * S.z * g⁻¹) * (l : G)⁻¹) * ((l : G) * g) := by group
      _ = S.z * ((l : G) * g) := by rw [hlz]
  have hVV : conjSub g⁻¹ V = conjSub ((l : G) * g)⁻¹ V := by
    ext x
    rw [mem_conjSub, mem_conjSub, inv_inv, inv_inv]
    have e : (l : G) * g * x * ((l : G) * g)⁻¹ = (l : G) * (g * x * g⁻¹) * (l : G)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp l.2 _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu2 : u ∈ conjSub g⁻¹ V := hu
  rw [hVV, mem_conjSub, inv_inv] at hu2
  have hu' : u ∈ conjClosure V S.G1 := by
    have e : u = ((l : G) * g)⁻¹ * ((l : G) * g * u * ((l : G) * g)⁻¹) * ((l : G) * g)⁻¹⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure (S.G1.inv_mem hg') hu2
  exact congrArg Subtype.val (h1378.is_comm.comm ⟨u, hu'⟩ ⟨v, le_conjClosure _ _ hv⟩)

theorem comm_V_centralizer_V3 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    ⁅V, H ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ ≤ fsuV1 T V := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hN : H ⊓ Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (S.V3 : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun x hx y hy => ?_
    have h := Subgroup.mem_centralizer_iff.mp hx.2 y hy
    have e : x * y * x⁻¹ = y := by rw [← h]; group
    rw [e]
    exact hy
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hF.normalizer_le ⟨hx.1, hN hx⟩
  have hρ := fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨x, hxN⟩) hx.2)
  have h1 := S.comm_mem_V1_of_rho (u := ⟨x, hxN⟩) hρ hv
  rw [commutatorElement_def]
  have e : v * x * v⁻¹ * x⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
  rw [e]
  exact (fsuV1 T V).inv_mem h1

theorem hypF98 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1378 : IsMulCommutative ↥(conjClosure V S.G1)) {H : Subgroup G} (hH : H ∈ S.Hz) :
    HypF98 T V L (fsuV1 T V) S.V3 H where
  toHypF91 := S.hypF91 hNS h13315 h1356two hH
  weak_f := fun _ hg => S.comm_conjSub_V_eq_bot h1378 hg
  case_g := Or.inl (S.comm_V_centralizer_V3 hNS h13315 h1356two hH)

end Setting4

@[expose] def Input1384Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 → False

theorem stmt13_8_3_34_of_inputs (h1332 : Stmt13_3_2)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (h1336 : Stmt13_3_6) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1384 : Input1384Six) : Stmt13_8_3_34 := by
  intro G _ _ T L V hH hA6 hV hNS hNU hab
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact hNS (h1341 G T L V hH hV h)
  obtain ⟨S⟩ := exists_setting4 h1332 h13316 hH hA6 hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  rw [hg1] at hab
  have hM : ¬ S.G1 ≤ Subgroup.normalizer (L : Set G) := by
    rcases h1336 G T L V hH hV with h | ⟨h, -⟩
    · rwa [hg1] at h
    · exact absurd hZV h
  have hG1 := S.G1_mem_Hz_of hM
  exact h1384 G T L V S hNS hNU hG1 hab (S.hypF98 hNS h13315 h1356two hab hG1)

end CFSG.Quasithin.H13.A6
