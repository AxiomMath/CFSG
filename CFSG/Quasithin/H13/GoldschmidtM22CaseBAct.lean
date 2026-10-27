module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBRho
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5

public section

namespace CFSG.Quasithin.H13.GM22

variable {G : Type} [Group G] {V : Subgroup G}

theorem conj_mem_centralizer {x q : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hq : q ∈ Subgroup.centralizer (V : Set G)) :
    x * q * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hx) v).mp hv
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hq _ hv'
  calc v * (x * q * x⁻¹) = x * ((x⁻¹ * v * x) * q) * x⁻¹ := by group
    _ = x * (q * (x⁻¹ * v * x)) * x⁻¹ := by rw [h1]
    _ = (x * q * x⁻¹) * v := by group

theorem conj_mem {x v : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) :
    x * v * x⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hx v).mp hv

@[expose] def actTriv (V : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (V : Set G) ∧
    ∀ q ∈ Subgroup.centralizer (V : Set G), x * q * x⁻¹ * q⁻¹ ∈ V}
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨(Subgroup.normalizer (V : Set G)).mul_mem hxN hyN, fun q hq => ?_⟩
    have h1 := conj_mem hxN (hy q hq)
    have h2 := V.mul_mem h1 (hx q hq)
    convert h2 using 1
    group
  one_mem' := ⟨(Subgroup.normalizer (V : Set G)).one_mem, fun q _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨(Subgroup.normalizer (V : Set G)).inv_mem hxN, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x ∈ Subgroup.centralizer (V : Set G) := by
      simpa using conj_mem_centralizer ((Subgroup.normalizer (V : Set G)).inv_mem hxN) hq
    have h1 := V.inv_mem (hx _ hq')
    convert h1 using 1
    group

theorem actTriv_le : actTriv V ≤ Subgroup.normalizer (V : Set G) := fun _ hx => hx.1

theorem conj_mem_actTriv {n x : G} (hn : n ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ actTriv V) :
    n * x * n⁻¹ ∈ actTriv V := by
  refine ⟨?_, fun q hq => ?_⟩
  · exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem hn hx.1)
      ((Subgroup.normalizer (V : Set G)).inv_mem hn)
  · have hq' : n⁻¹ * q * n ∈ Subgroup.centralizer (V : Set G) := by
      simpa using conj_mem_centralizer ((Subgroup.normalizer (V : Set G)).inv_mem hn) hq
    have h1 := conj_mem hn (hx.2 _ hq')
    convert h1 using 1
    group

theorem mem_actTriv_iff_conj {n x : G} (hn : n ∈ Subgroup.normalizer (V : Set G)) :
    x ∈ actTriv V ↔ n * x * n⁻¹ ∈ actTriv V := by
  refine ⟨conj_mem_actTriv hn, fun h => ?_⟩
  have := conj_mem_actTriv ((Subgroup.normalizer (V : Set G)).inv_mem hn) h
  simpa [mul_assoc] using this

theorem mem_normalizer_actTriv {n : G} (hn : n ∈ Subgroup.normalizer (V : Set G)) :
    n ∈ Subgroup.normalizer (actTriv V : Set G) :=
  Subgroup.mem_normalizer_iff.mpr fun _ => mem_actTriv_iff_conj hn

namespace PermRho

variable (ρ : PermRho V)

theorem exists_mul_of_actTriv {a : G} (ha : a ∈ actTriv V) (ha2 : ρ a * ρ a = 1)
    (has : Equiv.Perm.sign (ρ a) = -1) :
    ∀ n ∈ Subgroup.normalizer (V : Set G),
      ∃ c ∈ actTriv V, ∃ q ∈ Subgroup.centralizer (V : Set G), n = c * q := by
  let K : Subgroup (Equiv.Perm (Fin 5)) :=
    { carrier := {σ | ∃ c ∈ actTriv V, ρ c = σ}
      mul_mem' := by
        rintro _ _ ⟨c₁, hc₁, rfl⟩ ⟨c₂, hc₂, rfl⟩
        exact ⟨c₁ * c₂, (actTriv V).mul_mem hc₁ hc₂, (apply_mul (actTriv_le hc₁) (actTriv_le hc₂))⟩
      one_mem' := ⟨1, (actTriv V).one_mem, apply_one⟩
      inv_mem' := by
        rintro _ ⟨c, hc, rfl⟩
        exact ⟨c⁻¹, (actTriv V).inv_mem hc, apply_inv (actTriv_le hc)⟩ }
  have hKn : K.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨c, hc, rfl⟩ τ
    obtain ⟨n, hn, rfl⟩ := ρ.exists_eq τ
    exact ⟨n * c * n⁻¹, conj_mem_actTriv hn hc, apply_conj hn (actTriv_le hc)⟩
  have hK : K = ⊤ := perm5_normal_eq_top K ⟨a, ha, rfl⟩ ha2 has
  intro n hn
  have hmem : ρ n ∈ K := by rw [hK]; trivial
  obtain ⟨c, hc, hcn⟩ := hmem
  refine ⟨c, hc, c⁻¹ * n, ?_, by group⟩
  exact (eq_iff (actTriv_le hc) hn).mp hcn

end PermRho

end CFSG.Quasithin.H13.GM22
