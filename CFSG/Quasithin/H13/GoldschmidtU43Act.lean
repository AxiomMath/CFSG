module

public import CFSG.Quasithin.H13.GoldschmidtU43Q8
public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Hz (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

abbrev Uz (z : G) : Subgroup G := pCoreOf 2 (Hz z)

structure Hyp (z : G) : Prop where
  orderOf_z : orderOf z = 2
  iso : Nonempty (↥(Uz z) ≃* Q8Q8)
  center : Uz z ⊓ Subgroup.centralizer (Uz z : Set G) = Subgroup.zpowers z
  cent_le : Hz z ⊓ Subgroup.centralizer (Uz z : Set G) ≤ Uz z
  index : Nat.card ↥(Hz z) = 36 * Nat.card ↥(Uz z)
  exists_g : ∃ g : G, g⁻¹ * z * g ∈ Uz z ∧ g⁻¹ * z * g ≠ z ∧
    Nat.card ↥(Uz z ⊓ CFSG.conjugate (Uz z) g) = 4

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem Uz_le_Hz (z : G) : Uz z ≤ Hz z := CFSG.LieType.BorelTits.pCoreOf_le 2 (Hz z)

theorem Hz_le_normalizer (z : G) : Hz z ≤ Subgroup.normalizer (Uz z : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Hz z)

theorem isPGroup_Uz [Finite G] (z : G) : IsPGroup 2 (Uz z) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Hz z)

@[expose] def zp (z : G) (a : ZMod 2) : G := if a = 0 then 1 else z

theorem zp_zero (z : G) : zp z 0 = 1 := by simp [zp]

theorem zp_one (z : G) : zp z 1 = z := by simp [zp]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem zp_add {z : G} (hz : z * z = 1) (a b : ZMod 2) : zp z a * zp z b = zp z (a + b) := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp [zp_zero]
  · simp [zp_zero, zp_one]
  · simp [zp_zero, zp_one]
  · rw [zp_one, hz, show (1 : ZMod 2) + 1 = 0 from by decide, zp_zero]

theorem zp_injective {z : G} (hz : z ≠ 1) {a b : ZMod 2} (h : zp z a = zp z b) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [zp_zero, zp_one] at h
    exact absurd h.symm hz
  · rw [zp_zero, zp_one] at h
    exact absurd h hz
  · rfl

@[expose] def bq (v w : V4) : ZMod 2 := q (v + w) + q v + q w

@[expose] def conjU {z : G} (x : ↥(Hz z)) (u : ↥(Uz z)) : ↥(Uz z) :=
  Q8Coords.conjHom (Hz_le_normalizer z x.2) u

@[simp] theorem coe_conjU {z : G} (x : ↥(Hz z)) (u : ↥(Uz z)) :
    (conjU x u : G) = (x : G) * u * (x : G)⁻¹ := rfl

theorem sq_mul_aux {a b : G} (hu2 : a * a * b = b * (a * a)) :
    (a * b) * (a * b) = (a * b * a⁻¹ * b⁻¹) * (a * a) * (b * b) := by
  calc (a * b) * (a * b) = a * b * a⁻¹ * b⁻¹ * (b * (a * a)) * b := by group
    _ = a * b * a⁻¹ * b⁻¹ * (a * a * b) * b := by rw [hu2]
    _ = a * b * a⁻¹ * b⁻¹ * (a * a) * (b * b) := by group

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem z_mem : z ∈ Uz z := by
  have : z ∈ Uz z ⊓ Subgroup.centralizer (Uz z : Set G) := by
    rw [h.center]
    exact Subgroup.mem_zpowers z
  exact this.1

theorem z_comm {u : G} (hu : u ∈ Uz z) : z * u = u * z := by
  have : z ∈ Uz z ⊓ Subgroup.centralizer (Uz z : Set G) := by
    rw [h.center]
    exact Subgroup.mem_zpowers z
  exact (Subgroup.mem_centralizer_iff.mp this.2 u hu).symm

theorem sq_z : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.orderOf_z, pow_two] at this

theorem z_ne_one : z ≠ 1 := by
  intro h1
  have := h.orderOf_z
  rw [h1, orderOf_one] at this
  omega

theorem card_U : Nat.card ↥(Uz z) = 32 := by
  obtain ⟨e⟩ := h.iso
  rw [Nat.card_congr e.toEquiv, card_q8Q8]

theorem card_H : Nat.card ↥(Hz z) = 1152 := by
  rw [h.index, h.card_U]

theorem isQ8Sq : IsQ8Sq ↥(Uz z) := by
  obtain ⟨e⟩ := h.iso
  exact IsQ8Sq.of_mulEquiv e.symm isQ8Sq_q8Q8

noncomputable def coords : Q8Coords (Uz z) :=
  Classical.choice (nonempty_q8Coords h.isQ8Sq)

theorem coords_z : h.coords.z = z := by
  have hc : ∀ v : ↥(Uz z), (⟨z, h.z_mem⟩ : ↥(Uz z)) * v = v * ⟨z, h.z_mem⟩ := fun v =>
    Subtype.ext (h.z_comm v.2)
  rcases h.coords.center ⟨z, h.z_mem⟩ hc with h1 | h1
  · exact absurd h1 h.z_ne_one
  · exact h1.symm

noncomputable abbrev θ : ↥(Uz z) →* Multiplicative V4 := h.coords.θ

theorem θ_surj : Function.Surjective h.θ := h.coords.θ_surj

theorem θ_eq_one_iff (u : ↥(Uz z)) : h.θ u = 1 ↔ ((u : G) = 1 ∨ (u : G) = z) := by
  have := h.coords.ker_iff u
  rwa [h.coords_z] at this

theorem sq_cases (u : ↥(Uz z)) :
    (q (Multiplicative.toAdd (h.θ u)) = 0 ∧ (u : G) ^ 2 = 1) ∨
      (q (Multiplicative.toAdd (h.θ u)) = 1 ∧ (u : G) ^ 2 = z) := by
  have := h.coords.sq u
  rwa [h.coords_z] at this

theorem sq_eq (u : ↥(Uz z)) : (u : G) ^ 2 = zp z (q (Multiplicative.toAdd (h.θ u))) := by
  rcases h.sq_cases u with ⟨hq, hs⟩ | ⟨hq, hs⟩
  · rw [hq, zp_zero]
    exact hs
  · rw [hq, zp_one]
    exact hs

theorem comm_eq (u v : ↥(Uz z)) :
    (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ =
      zp z (bq (Multiplicative.toAdd (h.θ u)) (Multiplicative.toAdd (h.θ v))) := by
  have hc1 : h.θ (u * v * u⁻¹ * v⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hc := (h.θ_eq_one_iff _).1 hc1
  have hcoe : ((u * v * u⁻¹ * v⁻¹ : ↥(Uz z)) : G) = (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ := by
    simp
  obtain ⟨γ, hγ⟩ : ∃ γ : ZMod 2, (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ = zp z γ := by
    rcases hc with h1 | h1
    · exact ⟨0, by rw [← hcoe, h1, zp_zero]⟩
    · exact ⟨1, by rw [← hcoe, h1, zp_one]⟩
  rw [hγ]
  congr 1
  have hu2 : (u : G) * u * (v : G) = (v : G) * ((u : G) * u) := by
    have h2 := h.sq_eq u
    rw [pow_two] at h2
    rw [h2]
    rcases zmod_two_cases (q (Multiplicative.toAdd (h.θ u))) with h0 | h0 <;> rw [h0]
    · simp [zp_zero]
    · rw [zp_one]
      exact h.z_comm v.2
  have hcomm : ((u : G) * v) ^ 2 =
      ((u : G) * v * (u : G)⁻¹ * (v : G)⁻¹) * (u : G) ^ 2 * (v : G) ^ 2 := by
    simp only [pow_two]
    exact sq_mul_aux hu2
  have hsq : zp z (q (Multiplicative.toAdd (h.θ u) + Multiplicative.toAdd (h.θ v))) =
      zp z γ * zp z (q (Multiplicative.toAdd (h.θ u))) *
        zp z (q (Multiplicative.toAdd (h.θ v))) := by
    have h1 := h.sq_eq (u * v)
    rw [Subgroup.coe_mul, hcomm, hγ, h.sq_eq u, h.sq_eq v, map_mul, toAdd_mul] at h1
    exact h1.symm
  rw [zp_add h.sq_z, zp_add h.sq_z] at hsq
  have key := zp_injective h.z_ne_one hsq
  have key2 : ∀ γ a b c : ZMod 2, a = γ + b + c → γ = a + b + c := by decide
  exact key2 _ _ _ _ key

noncomputable def act : ↥(Hz z) →* MulAut (Multiplicative V4) :=
  h.coords.act (Hz z) (Hz_le_normalizer z) (by rw [h.coords_z])

theorem act_mem_Oq (x : ↥(Hz z)) : h.act x ∈ Oq :=
  h.coords.act_mem_Oq (Hz z) (Hz_le_normalizer z) (by rw [h.coords_z]) x

theorem act_θ (x : ↥(Hz z)) (u : ↥(Uz z)) : h.act x (h.θ u) = h.θ (conjU x u) :=
  h.coords.act_θ (Hz z) (Hz_le_normalizer z) (by rw [h.coords_z]) x u

theorem act_eq_one_iff (x : ↥(Hz z)) :
    h.act x = 1 ↔ ∀ u ∈ Uz z, (x : G) * u * (x : G)⁻¹ * u⁻¹ = 1 ∨
      (x : G) * u * (x : G)⁻¹ * u⁻¹ = z := by
  have key := h.coords.act_eq_one_iff (Hz z) (Hz_le_normalizer z) (by rw [h.coords_z]) x
  constructor
  · intro hx u hu
    have := key.1 hx u hu
    rwa [h.coords_z] at this
  · intro H
    refine key.2 fun u hu => ?_
    exact Or.imp_right (fun h' => h'.trans h.coords_z.symm) (H u hu)

theorem sq_mem_U_of_act_eq_one {x : ↥(Hz z)} (hx : h.act x = 1) : (x : G) ^ 2 ∈ Uz z := by
  have hcomm := (h.act_eq_one_iff x).1 hx
  have hxz : (x : G) * z = z * (x : G) := Subgroup.mem_centralizer_singleton_iff.mp x.2
  refine h.cent_le (Subgroup.mem_inf.mpr ⟨pow_mem x.2 2, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rcases hcomm u hu with hc | hc
  · have hxu : (x : G) * u = u * (x : G) :=
      calc (x : G) * u = ((x : G) * u * (x : G)⁻¹ * u⁻¹) * (u * (x : G)) := by group
        _ = u * (x : G) := by rw [hc, one_mul]
    rw [pow_two]
    symm
    calc (x : G) * x * u = (x : G) * (x * u) := mul_assoc _ _ _
      _ = (x : G) * (u * x) := by rw [hxu]
      _ = ((x : G) * u) * x := (mul_assoc _ _ _).symm
      _ = (u * (x : G)) * x := by rw [hxu]
      _ = u * ((x : G) * x) := mul_assoc _ _ _
  · have hxu : (x : G) * u = z * (u * (x : G)) :=
      calc (x : G) * u = ((x : G) * u * (x : G)⁻¹ * u⁻¹) * (u * (x : G)) := by group
        _ = z * (u * (x : G)) := by rw [hc]
    rw [pow_two]
    symm
    calc (x : G) * x * u = (x : G) * (x * u) := mul_assoc _ _ _
      _ = (x : G) * (z * (u * x)) := by rw [hxu]
      _ = z * ((x : G) * (u * x)) := by rw [← mul_assoc, hxz, mul_assoc]
      _ = z * (((x : G) * u) * x) := by rw [← mul_assoc (x : G) u x]
      _ = z * ((z * (u * (x : G))) * x) := by rw [hxu]
      _ = (z * z) * (u * ((x : G) * x)) := by simp only [mul_assoc]
      _ = u * ((x : G) * x) := by rw [h.sq_z, one_mul]

section Finite

variable [Finite G]

theorem mem_U_of_act_eq_one (x : ↥(Hz z)) (hx : h.act x = 1) : (x : G) ∈ Uz z := by
  have hK : IsPGroup 2 (h.act).ker := by
    intro k
    obtain ⟨n, hn⟩ := isPGroup_Uz z ⟨(k.1 : G) ^ 2, h.sq_mem_U_of_act_eq_one k.2⟩
    refine ⟨n + 1, ?_⟩
    have h1 : ((k.1 : G) ^ 2) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    apply Subtype.ext
    apply Subtype.ext
    show (k.1 : G) ^ 2 ^ (n + 1) = 1
    rw [pow_succ', pow_mul]
    exact h1
  have hNle : (h.act).ker.map (Hz z).subtype ≤ pCoreOf 2 (Hz z) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ (hK.map _)
    rw [show ((h.act).ker.map (Hz z).subtype).subgroupOf (Hz z) = (h.act).ker from
      Subgroup.comap_map_eq_self_of_injective (Hz z).subtype_injective _]
    infer_instance
  exact hNle ⟨x, hx, rfl⟩

theorem ker_act : (h.act).ker = (Uz z).subgroupOf (Hz z) := by
  ext x
  constructor
  · intro hx
    exact h.mem_U_of_act_eq_one x hx
  · intro hx
    rw [MonoidHom.mem_ker, h.act_eq_one_iff]
    intro u hu
    have hxU : (x : G) ∈ Uz z := hx
    have := (h.θ_eq_one_iff (⟨x, hxU⟩ * ⟨u, hu⟩ * ⟨x, hxU⟩⁻¹ * ⟨u, hu⟩⁻¹ : ↥(Uz z))).1 (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _))
    simpa using this

theorem card_range_act : Nat.card (h.act).range = 36 := by
  have h1 := Subgroup.card_mul_index (h.act).ker
  rw [Subgroup.index_ker, h.ker_act] at h1
  have h2 : Nat.card ((Uz z).subgroupOf (Hz z)) = Nat.card (Uz z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Uz_le_Hz z)).toEquiv
  rw [h2, h.index] at h1
  have hU : 0 < Nat.card (Uz z) := by rw [h.card_U]; norm_num
  exact Nat.eq_of_mul_eq_mul_left hU (by rw [h1, mul_comm])

end Finite

end Hyp

end CFSG.Quasithin.H13.U43
