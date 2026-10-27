module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocCtx
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocQ
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Norm

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

@[expose] noncomputable def TG : Subgroup G := Subgroup.map C.φ1 (T.subgroupOf P1)

theorem mem_TG {g : G} : g ∈ C.TG ↔ ∃ s ∈ T, C.Φ1 s = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, C.Φ1_of_mem x.2⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, T_le_P1 hs⟩, hs, (C.Φ1_of_mem _).symm⟩

theorem Φ1_mem_TG {s : Y} (hs : s ∈ T) : C.Φ1 s ∈ C.TG := C.mem_TG.2 ⟨s, hs, rfl⟩

theorem card_TG : Nat.card C.TG = 64 := by
  rw [TG, Subgroup.card_map_of_injective C.inj1,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_P1).toEquiv, card_T]

theorem isPGroup_TG : IsPGroup 2 C.TG := by
  have : IsPGroup 2 (T.subgroupOf P1) :=
    IsPGroup.of_equiv isSylow_T.2.1 (Subgroup.subgroupOfEquivOfLe T_le_P1).symm
  exact this.map _

theorem z_ne_one : C.z ≠ 1 := by
  intro h
  have : C.Φ1 xY = C.Φ1 1 := by rw [C.Φ1_one]; exact h
  exact xY_ne_one (C.Φ1_inj mem_P1_xY P1.one_mem this)

theorem comm_z_of_mem_TG {g : G} (hg : g ∈ C.TG) : g * C.z = C.z * g := by
  obtain ⟨s, hs, rfl⟩ := C.mem_TG.1 hg
  rw [z_def, ← C.Φ1_mul (T_le_P1 hs) mem_P1_xY, ← C.Φ1_mul mem_P1_xY (T_le_P1 hs),
    comm_xY_of_mem_T hs]

theorem exists_of_comm_z {g : G} (hg : g * C.z = C.z * g) : ∃ y ∈ P1, C.Φ1 y = g := by
  have hz : C.z = C.φ1 ⟨xY, mem_P1_xY⟩ := C.Φ1_of_mem mem_P1_xY
  rw [hz] at hg
  obtain ⟨y, hy⟩ := C.cent g hg
  exact ⟨y, y.2, by rw [C.Φ1_of_mem y.2]; exact hy⟩

theorem central_TG {w : G} (hw : w ∈ C.TG) (hc : ∀ g ∈ C.TG, g * w = w * g) :
    w = 1 ∨ w = C.z := by
  obtain ⟨y, hy, rfl⟩ := C.mem_TG.1 hw
  have hyc : ∀ s ∈ T, s * y = y * s := by
    intro s hs
    have := hc (C.Φ1 s) (C.Φ1_mem_TG hs)
    rw [← C.Φ1_mul (T_le_P1 hs) (T_le_P1 hy), ← C.Φ1_mul (T_le_P1 hy) (T_le_P1 hs)] at this
    exact C.Φ1_inj (P1.mul_mem (T_le_P1 hs) (T_le_P1 hy)) (P1.mul_mem (T_le_P1 hy) (T_le_P1 hs))
      this
  rcases center_T_spec hy hyc with h | h
  · left
    rw [h, C.Φ1_one]
  · right
    rw [h]
    rfl

theorem normalizer_of_map_le {y : Y} (h : T.map (MulAut.conj y).toMonoidHom ≤ T) :
    y ∈ B0 := by
  have hcard : Nat.card T ≤ Nat.card (T.map (MulAut.conj y).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj y).injective).symm.le
  have heq := Subgroup.eq_of_le_of_card_ge h hcard
  rw [← normalizer_T, Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => h ⟨t, ht, rfl⟩, fun ht => ?_⟩
  rw [← heq] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have : s = t := by
    have h2 : y * s * y⁻¹ = y * t * y⁻¹ := hst
    exact mul_left_cancel (mul_right_cancel h2)
  exact this ▸ hs

variable [Finite G]

theorem mem_TG_of_normalizes (S : Sylow 2 G) {s : G} (hsS : s ∈ (S : Subgroup G))
    (hs : ∀ x ∈ C.TG, s * x * s⁻¹ ∈ C.TG) : s ∈ C.TG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : C.TG.map (MulAut.conj s).toMonoidHom ≤ C.TG := by
    rintro _ ⟨x, hx, rfl⟩
    exact hs x hx
  have heq : C.TG.map (MulAut.conj s).toMonoidHom = C.TG :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj s).injective])
  have hinv : ∀ g ∈ C.TG, s⁻¹ * g * s ∈ C.TG := by
    intro g hg
    rw [← heq] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    have h1 : s * x * s⁻¹ = g := hxg
    have : s⁻¹ * g * s = x := by rw [← h1]; group
    rw [this]
    exact hx
  have hzT : C.z ∈ C.TG := C.Φ1_mem_TG xY_mem_T
  have hw : s * C.z * s⁻¹ = C.z := by
    have hcen : ∀ g ∈ C.TG, g * (s * C.z * s⁻¹) = (s * C.z * s⁻¹) * g := by
      intro g hg
      have h1 := C.comm_z_of_mem_TG (hinv g hg)
      calc g * (s * C.z * s⁻¹) = s * ((s⁻¹ * g * s) * C.z) * s⁻¹ := by group
        _ = s * (C.z * (s⁻¹ * g * s)) * s⁻¹ := by rw [h1]
        _ = (s * C.z * s⁻¹) * g := by group
    rcases C.central_TG (hs _ hzT) hcen with h | h
    · exact absurd (by
        have : C.z = s⁻¹ * (s * C.z * s⁻¹) * s := by group
        rw [this, h]
        group) C.z_ne_one
    · exact h
  have hcomm : s * C.z = C.z * s := by
    calc s * C.z = s * C.z * s⁻¹ * s := by group
      _ = C.z * s := by rw [hw]
  obtain ⟨y, hyP, rfl⟩ := C.exists_of_comm_z hcomm
  have hyB : y ∈ B0 := by
    refine normalizer_of_map_le ?_
    rintro _ ⟨τ, hτ, rfl⟩
    have h1 := hs (C.Φ1 τ) (C.Φ1_mem_TG hτ)
    rw [← C.Φ1_mul hyP (T_le_P1 hτ), ← C.Φ1_inv hyP, ← C.Φ1_mul (P1.mul_mem hyP (T_le_P1 hτ))
      (P1.inv_mem hyP)] at h1
    obtain ⟨τ', hτ', h2⟩ := C.mem_TG.1 h1
    have h3 : τ' = y * τ * y⁻¹ :=
      C.Φ1_inj (T_le_P1 hτ') (P1.mul_mem (P1.mul_mem hyP (T_le_P1 hτ)) (P1.inv_mem hyP)) h2
    simpa [MulAut.conj_apply, h3.symm] using hτ'
  have hp : IsPGroup 2 (Subgroup.zpowers y) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨C.Φ1 y, hsS⟩
    have h1 : orderOf (C.Φ1 y) = 2 ^ k := by
      have := hk
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf y = 2 ^ k := by
      rw [C.Φ1_of_mem hyP] at h1
      have := orderOf_injective C.φ1 C.inj1 ⟨y, hyP⟩
      rw [this, Subgroup.orderOf_mk] at h1
      exact h1
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, h2])
  have hyT : y ∈ T :=
    le_T_of_le_B0 ((Subgroup.zpowers_le).2 hyB) hp (Subgroup.mem_zpowers y)
  exact C.Φ1_mem_TG hyT

theorem sylow_eq_TG (S : Sylow 2 G) (hS : C.TG ≤ (S : Subgroup G)) :
    (S : Subgroup G) = C.TG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  set A : Subgroup ↥(S : Subgroup G) := C.TG.subgroupOf (S : Subgroup G) with hA
  have hnorm : Subgroup.normalizer (A : Set ↥(S : Subgroup G)) ≤ A := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff] at hs
    refine C.mem_TG_of_normalizes S s.2 fun x hx => ?_
    have := (hs ⟨x, hS hx⟩).1 hx
    exact this
  by_contra hne
  have hlt : A < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm (fun g hg => ?_) hS
    have : (⟨g, hg⟩ : ↥(S : Subgroup G)) ∈ A := by rw [htop]; trivial
    exact this
  have := Group.normalizerCondition_of_isNilpotent A hlt
  exact absurd hnorm (not_le_of_gt this)

theorem exists_sylow_TG : ∃ S : Sylow 2 G, (S : Subgroup G) = C.TG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := C.isPGroup_TG.exists_le_sylow
  exact ⟨S, C.sylow_eq_TG S hS⟩

end Ctx

end CFSG.Quasithin.H13.F431.U42
