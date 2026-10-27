module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Co2Smith.RigidCount

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u

variable {G : Type u} [Group G] [Finite G] {z : G}

theorem eq_of_le_two {x : G} {U P : Subgroup G} (hUH : U ≤ centralizer ({z} : Set G))
    (hmax : ∀ V : Subgroup G, V ≤ centralizer ({x} : Set G) → V ≤ centralizer ({z} : Set G) →
      IsPGroup 2 V → U ≤ V → V = U)
    (hzU : z ∈ U)
    (hZ : ∀ g : G, g * z * g⁻¹ ∈ U → (∀ v ∈ U, v * (g * z * g⁻¹) = g * z * g⁻¹ * v) →
      g * z * g⁻¹ = z)
    (hPx : P ≤ centralizer ({x} : Set G)) (hP : IsPGroup 2 P) (hUP : U ≤ P) : P = U := by
  by_contra hne
  have hlt : U.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    refine le_antisymm (fun y hy => ?_) hUP
    have : (⟨y, hy⟩ : P) ∈ U.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨⟨y, hyP⟩, hyN, hyU⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (U.subgroupOf P) hlt)
  have hyU' : y ∉ U := hyU
  have hnorm : ∀ v ∈ U, y * v * y⁻¹ ∈ U := by
    intro v hv
    have := (mem_normalizer_iff.mp hyN ⟨v, hUP hv⟩).mp hv
    exact this
  have hnorm' : ∀ v ∈ U, y⁻¹ * v * y ∈ U := by
    intro v hv
    have := (mem_normalizer_iff.mp (inv_mem hyN) ⟨v, hUP hv⟩).mp hv
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  by_cases hyH : y ∈ centralizer ({z} : Set G)
  ·
    set V := U ⊔ Subgroup.zpowers y
    have hVP : V ≤ P := sup_le hUP ((Subgroup.zpowers_le).mpr hyP)
    have hV := hmax V (hVP.trans hPx) (sup_le hUH ((Subgroup.zpowers_le).mpr hyH))
      (hP.to_le hVP) le_sup_left
    exact hyU' (hV ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  · apply hyH
    rw [mem_centralizer_singleton_iff]
    have hz : y * z * y⁻¹ = z := by
      refine hZ y (hnorm z hzU) fun v hv => ?_
      have hv' := hnorm' v hv
      have hc : (y⁻¹ * v * y) * z = z * (y⁻¹ * v * y) :=
        mem_centralizer_singleton_iff.mp (hUH hv')
      calc v * (y * z * y⁻¹) = y * ((y⁻¹ * v * y) * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * v * y)) * y⁻¹ := by rw [hc]
        _ = y * z * y⁻¹ * v := by group
    calc y * z = y * z * y⁻¹ * y := by group
      _ = z * y := by rw [hz]

theorem card_le_of_sylow {x : G} {U : Subgroup G} (hUx : U ≤ centralizer ({x} : Set G))
    (hUH : U ≤ centralizer ({z} : Set G)) (h2 : IsPGroup 2 U)
    (hmax : ∀ V : Subgroup G, V ≤ centralizer ({x} : Set G) → V ≤ centralizer ({z} : Set G) →
      IsPGroup 2 V → U ≤ V → V = U)
    (hzU : z ∈ U)
    (hZ : ∀ g : G, g * z * g⁻¹ ∈ U → (∀ v ∈ U, v * (g * z * g⁻¹) = g * z * g⁻¹ * v) →
      g * z * g⁻¹ = z)
    {Q : Subgroup G} (hQx : Q ≤ centralizer ({x} : Set G)) (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({x} : Set G)
  have hU' : IsPGroup 2 (U.subgroupOf K) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hUx).symm
  have hQ' : IsPGroup 2 (Q.subgroupOf K) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQx).symm
  obtain ⟨S, hS⟩ := hU'.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hQ'.exists_le_sylow
  set P := (S : Subgroup K).map K.subtype
  have hPx : P ≤ K := Subgroup.map_subtype_le _
  have hP : IsPGroup 2 P := S.isPGroup'.map K.subtype
  have hUP : U ≤ P := by
    intro u hu
    exact ⟨⟨u, hUx hu⟩, hS hu, rfl⟩
  have hPU := eq_of_le_two hUH hmax hzU hZ hPx hP hUP
  have hcardP : Nat.card P = Nat.card S :=
    Subgroup.card_map_of_injective K.subtype_injective
  calc Nat.card Q = Nat.card (Q.subgroupOf K) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQx).toEquiv).symm
    _ ≤ Nat.card S₂ := Subgroup.card_le_of_le hS₂
    _ = Nat.card S := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = Nat.card U := by rw [← hcardP, hPU]

omit [Finite G] in
theorem card_le_conj {x : G} {m : ℕ}
    (h : ∀ Q : Subgroup G, Q ≤ centralizer ({x} : Set G) → IsPGroup 2 Q → Nat.card Q ≤ m)
    (g : G) {Q : Subgroup G} (hQx : Q ≤ centralizer ({g * x * g⁻¹} : Set G))
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ m := by
  set Q' := Q.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'x : Q' ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.mp (hQx hq)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * q * g * x = g⁻¹ * (q * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * q) * g := by rw [hc]
      _ = x * (g⁻¹ * q * g) := by group
  have hQ' : IsPGroup 2 Q' := hQ.map _
  have e : Nat.card Q' = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← e]
  exact h Q' hQ'x hQ'

end CFSG.Sporadic.Co2Smith
