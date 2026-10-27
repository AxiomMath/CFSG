module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_conj_mem_zpowers {v : V} {x x' : G} (hx : x ∈ MulAction.stabilizer G v)
    (hx' : x' ∈ MulAction.stabilizer G v) (ho : orderOf x = Fan86.valence Γ v)
    (ho' : orderOf x' = Fan86.valence Γ v) :
    ∃ g ∈ MulAction.stabilizer G v, g * x' * g⁻¹ ∈ Subgroup.zpowers x := by
  have hp := F.valence_isPrime v
  have hp35 : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  have : Finite (MulAction.stabilizer G v) := F.loc_finite v
  obtain ⟨k, hk⟩ := F.exists_card_stabilizer v
  set p := Fan86.valence Γ v with hpdef
  let S : Subgroup (MulAction.stabilizer G v) := Subgroup.zpowers ⟨x, hx⟩
  let S' : Subgroup (MulAction.stabilizer G v) := Subgroup.zpowers ⟨x', hx'⟩
  have hS : Nat.card S = p := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ho]
  have hS' : Nat.card S' = p := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ho']
  have hnd : ∀ T : Subgroup (MulAction.stabilizer G v), Nat.card T = p → ¬ p ∣ T.index := by
    intro T hT hdvd
    have h1 := T.index_mul_card
    rw [hT, hk] at h1
    have h2 : T.index = 2 ^ k := by
      have := Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1]; ring : T.index * p = 2 ^ k * p)
      exact this
    rw [h2] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
    omega
  have hSp : IsPGroup p S := IsPGroup.of_card (n := 1) (by rw [hS, pow_one])
  have hSp' : IsPGroup p S' := IsPGroup.of_card (n := 1) (by rw [hS', pow_one])
  let P : Sylow p (MulAction.stabilizer G v) := hSp.toSylow (hnd S hS)
  let P' : Sylow p (MulAction.stabilizer G v) := hSp'.toSylow (hnd S' hS')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAction.stabilizer G v) P' P
  have hmem : (⟨x', hx'⟩ : MulAction.stabilizer G v) ∈ (P' : Subgroup _) := by
    show _ ∈ S'
    exact Subgroup.mem_zpowers _
  have h1 : MulAut.conj g ⟨x', hx'⟩ ∈ ((g • P' : Sylow p _) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rw [hg] at h1
  have h2 : MulAut.conj g ⟨x', hx'⟩ ∈ S := h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h2
  refine ⟨g, g.2, Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩⟩
  have := congrArg Subtype.val hj
  simpa [MulAut.conj_apply] using this


theorem finite_nbrStab (v : V) : Finite (nbrStab Γ G v) := by
  have := F.loc_finite v
  exact Finite.of_injective (Subgroup.inclusion (F.nbrStab_le_stabilizer v))
    (Subgroup.inclusion_injective _)

omit F in
theorem relIndex_ne_zero_of_finite (H K : Subgroup G) [Finite K] : H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h0, zero_mul] at this
  exact (Nat.card_pos (α := K)).ne' this.symm

theorem relIndex_centralizer_conj {v : V} {g : G} (hg : g ∈ MulAction.stabilizer G v) (y : G) :
    (Subgroup.centralizer ({g * y * g⁻¹} : Set G)).relIndex (nbrStab Γ G v) =
      (Subgroup.centralizer ({y} : Set G)).relIndex (nbrStab Γ G v) := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : ∀ k, f k = g * k * g⁻¹ := fun k => rfl
  have h1 : (Subgroup.centralizer ({g * y * g⁻¹} : Set G)).comap f =
      Subgroup.centralizer ({y} : Set G) := by
    ext k
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, hf]
    constructor
    · intro h
      have h2 : g * (y * k) * g⁻¹ = g * (k * y) * g⁻¹ := by
        calc g * (y * k) * g⁻¹ = g * y * g⁻¹ * (g * k * g⁻¹) := by group
          _ = g * k * g⁻¹ * (g * y * g⁻¹) := h
          _ = g * (k * y) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    · intro h
      calc g * y * g⁻¹ * (g * k * g⁻¹) = g * (y * k) * g⁻¹ := by group
        _ = g * (k * y) * g⁻¹ := by rw [h]
        _ = g * k * g⁻¹ * (g * y * g⁻¹) := by group
  have hg' : g • v = v := MulAction.mem_stabilizer_iff.1 hg
  have hg'' : g⁻¹ • v = v := by rw [inv_smul_eq_iff]; exact hg'.symm
  have h2 : (nbrStab Γ G v).map f = nbrStab Γ G v := by
    ext z
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact nbrStab_conj_mem F hg' hk
    · intro hz
      refine ⟨g⁻¹ * z * g, ?_, ?_⟩
      · have := nbrStab_conj_mem F hg'' hz
        simpa using this
      · simp only [hf]
        group
  rw [← h1, Subgroup.relIndex_comap, h2]

theorem centralizer_relIndex_le {v : V} {x x' : G} (hx : x ∈ MulAction.stabilizer G v)
    (hx' : x' ∈ MulAction.stabilizer G v) (ho : orderOf x = Fan86.valence Γ v)
    (ho' : orderOf x' = Fan86.valence Γ v) :
    (Subgroup.centralizer ({x'} : Set G)).relIndex (nbrStab Γ G v) ≤
      (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G v) := by
  obtain ⟨g, hg, hmem⟩ := F.exists_conj_mem_zpowers hx hx' ho ho'
  rw [← F.relIndex_centralizer_conj hg x']
  have hle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({g * x' * g⁻¹} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hj]
    exact ((show Commute x c from hc x rfl).zpow_left j).eq
  have := F.finite_nbrStab v
  exact Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)

end FanTree

end CFSG.Quasithin.Fan86
