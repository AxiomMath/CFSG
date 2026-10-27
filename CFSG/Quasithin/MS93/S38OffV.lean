module

public import CFSG.Quasithin.MS93.S38OffIV
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.GL32F

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family

theorem tinvols_uniq_axis : ∀ b₁ ∈ tinvols, ∀ b₂ ∈ tinvols, ∀ b₁' ∈ tinvols, ∀ b₂' ∈ tinvols,
    b₁ ≠ b₂ → b₁ * b₂ = b₂ * b₁ → (∀ v, (b₁ - 1) *ᵥ v = 0 ↔ (b₂ - 1) *ᵥ v = 0) →
    b₁' ≠ b₂' → b₁' * b₂' = b₂' * b₁' → (∀ v, (b₁' - 1) *ᵥ v = 0 ↔ (b₂' - 1) *ᵥ v = 0) →
    (b₁' = b₁ ∨ b₁' = b₂ ∨ b₁' = b₁ * b₂) := by
  decide +kernel

theorem inv_mulVec_eq_zero_iff (g : GL32) (w : Fin 3 → ZMod 2) :
    ((g⁻¹ : GL32) : Mat3) *ᵥ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
    calc w = ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) *ᵥ w := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

theorem conj_ax {g b₁ b₂ : GL32}
    (hax : ∀ v, ((b₁ : Mat3) - 1) *ᵥ v = 0 ↔ ((b₂ : Mat3) - 1) *ᵥ v = 0) :
    ∀ v, (((g⁻¹ * b₁ * g : GL32) : Mat3) - 1) *ᵥ v = 0 ↔
      (((g⁻¹ * b₂ * g : GL32) : Mat3) - 1) *ᵥ v = 0 := by
  intro v
  rw [conj_sub_one_mulVec, conj_sub_one_mulVec, inv_mulVec_eq_zero_iff, inv_mulVec_eq_zero_iff]
  exact hax _

theorem eq_of_axis_four {P : Subgroup GL32} (hP : IsPGroup 2 P)
    {b₁ b₂ b₁' b₂' : GL32} (h₁ : b₁ ∈ P) (h₂ : b₂ ∈ P) (h₁' : b₁' ∈ P) (h₂' : b₂' ∈ P)
    (hs₁ : b₁ ^ 2 = 1) (hs₂ : b₂ ^ 2 = 1) (hs₁' : b₁' ^ 2 = 1) (hs₂' : b₂' ^ 2 = 1)
    (hn₁ : b₁ ≠ 1) (hn₂ : b₂ ≠ 1) (hn₁' : b₁' ≠ 1) (hn₂' : b₂' ≠ 1)
    (hne : b₁ ≠ b₂) (hc : b₁ * b₂ = b₂ * b₁)
    (hax : ∀ v, ((b₁ : Mat3) - 1) *ᵥ v = 0 ↔ ((b₂ : Mat3) - 1) *ᵥ v = 0)
    (hne' : b₁' ≠ b₂') (hc' : b₁' * b₂' = b₂' * b₁')
    (hax' : ∀ v, ((b₁' : Mat3) - 1) *ᵥ v = 0 ↔ ((b₂' : Mat3) - 1) *ᵥ v = 0) :
    b₁' = b₁ ∨ b₁' = b₂ ∨ b₁' = b₁ * b₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowT hP
  have hmat : ∀ {x y : GL32}, x * y = y * x →
      ((g⁻¹ * x * g : GL32) : Mat3) * ((g⁻¹ * y * g : GL32) : Mat3) =
        ((g⁻¹ * y * g : GL32) : Mat3) * ((g⁻¹ * x * g : GL32) : Mat3) := fun hxy => by
    rw [← Units.val_mul, ← Units.val_mul, conj_comm hxy]
  have hne₀ : ∀ {x y : GL32}, x ≠ y →
      ((g⁻¹ * x * g : GL32) : Mat3) ≠ ((g⁻¹ * y * g : GL32) : Mat3) := fun hxy h =>
    hxy (conj_inj h)
  rcases tinvols_uniq_axis _ (mem_tinvols_of_conj (hg _ h₁) hs₁ hn₁)
      _ (mem_tinvols_of_conj (hg _ h₂) hs₂ hn₂) _ (mem_tinvols_of_conj (hg _ h₁') hs₁' hn₁')
      _ (mem_tinvols_of_conj (hg _ h₂') hs₂' hn₂') (hne₀ hne) (hmat hc) (conj_ax hax)
      (hne₀ hne') (hmat hc') (conj_ax hax') with h | h | h
  · exact Or.inl (conj_inj h)
  · exact Or.inr (Or.inl (conj_inj h))
  · right; right
    apply conj_inj (g := g)
    rw [h, ← Units.val_mul]
    congr 1
    group

end CFSG.Quasithin.MS93.GL32F

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace OffV

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.QuasithinUnique.Setup.Family GL32F

variable {G : Type} [Group G]

section UPart

variable (Z U : Subgroup G)

open Classical in
@[expose] noncomputable def uPart (w : G) : G :=
  if h : ∃ u ∈ U, w * u⁻¹ ∈ Z then Classical.choose h else 1

variable {Z U}

theorem uPart_spec {w : G} (h : ∃ u ∈ U, w * u⁻¹ ∈ Z) :
    uPart Z U w ∈ U ∧ w * (uPart Z U w)⁻¹ ∈ Z := by
  unfold uPart
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem uPart_unique (hZU : Z ⊓ U = ⊥) {w u : G} (hu : u ∈ U) (hw : w * u⁻¹ ∈ Z) :
    uPart Z U w = u := by
  obtain ⟨h1, h2⟩ := uPart_spec ⟨u, hu, hw⟩
  have hm : uPart Z U w * u⁻¹ ∈ Z ⊓ U := by
    refine ⟨?_, U.mul_mem h1 (U.inv_mem hu)⟩
    have := Z.mul_mem (Z.inv_mem h2) hw
    have e : (w * (uPart Z U w)⁻¹)⁻¹ * (w * u⁻¹) = uPart Z U w * u⁻¹ := by group
    rwa [e] at this
  rw [hZU, Subgroup.mem_bot, mul_inv_eq_one] at hm
  exact hm

theorem uPart_of_mem_U (hZU : Z ⊓ U = ⊥) {u : G} (hu : u ∈ U) : uPart Z U u = u :=
  uPart_unique hZU hu (by rw [mul_inv_cancel]; exact Z.one_mem)

theorem uPart_of_mem_Z (hZU : Z ⊓ U = ⊥) {z : G} (hz : z ∈ Z) : uPart Z U z = 1 :=
  uPart_unique hZU U.one_mem (by rw [inv_one, mul_one]; exact hz)

theorem uPart_mul (hZU : Z ⊓ U = ⊥) (hcomm : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) {w₁ w₂ : G}
    (h₁ : ∃ u ∈ U, w₁ * u⁻¹ ∈ Z) (h₂ : ∃ u ∈ U, w₂ * u⁻¹ ∈ Z) :
    uPart Z U (w₁ * w₂) = uPart Z U w₁ * uPart Z U w₂ := by
  obtain ⟨hu₁, hz₁⟩ := uPart_spec h₁
  obtain ⟨hu₂, hz₂⟩ := uPart_spec h₂
  refine uPart_unique hZU (U.mul_mem hu₁ hu₂) ?_
  have e : w₁ * w₂ * (uPart Z U w₁ * uPart Z U w₂)⁻¹ =
      (w₁ * (uPart Z U w₁)⁻¹) * (uPart Z U w₁ * (w₂ * (uPart Z U w₂)⁻¹) * (uPart Z U w₁)⁻¹) := by
    group
  rw [e, ← hcomm _ hz₂ _ hu₁, mul_inv_cancel_right]
  exact Z.mul_mem hz₁ hz₂

theorem uPart_conj (hZU : Z ⊓ U = ⊥) {g : G} (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) {w : G} (hw : ∃ u ∈ U, w * u⁻¹ ∈ Z) :
    uPart Z U (g * w * g⁻¹) = g * uPart Z U w * g⁻¹ := by
  obtain ⟨hu, hz⟩ := uPart_spec hw
  refine uPart_unique hZU ((Subgroup.mem_normalizer_iff.mp hgU _).mp hu) ?_
  have e : g * w * g⁻¹ * (g * uPart Z U w * g⁻¹)⁻¹ = g * (w * (uPart Z U w)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hgZ _).mp hz

theorem uPart_inv (hZU : Z ⊓ U = ⊥) {w : G} (hw : ∃ u ∈ U, w * u⁻¹ ∈ Z)
    (hwc : ∀ u ∈ U, w * u = u * w) : uPart Z U w⁻¹ = (uPart Z U w)⁻¹ := by
  obtain ⟨hu, hz⟩ := uPart_spec hw
  refine uPart_unique hZU (U.inv_mem hu) ?_
  rw [inv_inv]
  have e : w⁻¹ * uPart Z U w = (w * (uPart Z U w)⁻¹)⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv]
    calc w⁻¹ * uPart Z U w = w⁻¹ * (uPart Z U w * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * uPart Z U w) * w⁻¹ := by rw [hwc _ hu]
      _ = uPart Z U w * w⁻¹ := by group
  rw [e]
  exact Z.inv_mem hz

theorem exists_of_mem_sup (hZn : Z ≤ Subgroup.normalizer (U : Set G)) {w : G} (hw : w ∈ Z ⊔ U) :
    ∃ u ∈ U, w * u⁻¹ ∈ Z := by
  have : w ∈ ((Z ⊔ U : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Z U hZn] at this
  obtain ⟨z, hz, u, hu, rfl⟩ := this
  exact ⟨u, hu, by rw [mul_inv_cancel_right]; exact hz⟩

end UPart

theorem mem_or_mul_inv_mem {H K : Subgroup G} (h2 : H.relIndex K = 2) {x : G} (hxK : x ∈ K)
    (hxH : x ∉ H) {y : G} (hyK : y ∈ K) : y ∈ H ∨ y * x⁻¹ ∈ H := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
  by_cases hyH : y ∈ H
  · exact Or.inl hyH
  · right
    have hxa : x * a ∈ H := by
      rcases ha x hxK with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h1 hxH
    have hya : y * a ∈ H := by
      rcases ha y hyK with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h1 hyH
    have e : y * a * (x * a)⁻¹ = y * x⁻¹ := by group
    rw [← e]
    exact H.mul_mem hya (H.inv_mem hxa)

section Rho

variable {L M U : Subgroup G} {α : ↥L →* ↥(StatedSL 3 (ZMod 2))} (N : NatSec L U ⊥ α false)

@[expose] noncomputable def uOf (v : Fin 3 → ZMod 2) : G := Classical.choose (N.exists_coord_eq v)

theorem uOf_mem (v : Fin 3 → ZMod 2) : uOf N v ∈ U :=
  (Classical.choose_spec (N.exists_coord_eq v)).1

theorem coord_uOf (v : Fin 3 → ZMod 2) : N.coord (uOf N v) = v :=
  (Classical.choose_spec (N.exists_coord_eq v)).2

theorem uOf_coord {u : G} (hu : u ∈ U) : uOf N (N.coord u) = u :=
  N.eq_of_coord_eq (uOf_mem N _) hu (coord_uOf N _)

theorem conj_mem (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) {u : G} (hu : u ∈ U) :
    (m : G) * u * (m : G)⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp (hMU m.2) u).mp hu

@[expose] noncomputable def conjAdd (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) :
    (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) where
  toFun v := N.coord ((m : G) * uOf N v * (m : G)⁻¹)
  map_zero' := by
    have : uOf N 0 = 1 := by
      have := uOf_coord N U.one_mem
      rwa [N.coord_one] at this
    rw [this, mul_one, mul_inv_cancel, N.coord_one]
  map_add' v w := by
    have e : uOf N (v + w) = uOf N v * uOf N w := by
      refine N.eq_of_coord_eq (uOf_mem N _) (U.mul_mem (uOf_mem N v) (uOf_mem N w)) ?_
      rw [coord_uOf, N.coord_mul (uOf_mem N v) (uOf_mem N w), coord_uOf, coord_uOf]
    have e' : (m : G) * (uOf N v * uOf N w) * (m : G)⁻¹ =
        ((m : G) * uOf N v * (m : G)⁻¹) * ((m : G) * uOf N w * (m : G)⁻¹) := by group
    show N.coord ((m : G) * uOf N (v + w) * (m : G)⁻¹) =
      N.coord ((m : G) * uOf N v * (m : G)⁻¹) + N.coord ((m : G) * uOf N w * (m : G)⁻¹)
    rw [e, e', N.coord_mul (conj_mem hMU m (uOf_mem N v)) (conj_mem hMU m (uOf_mem N w))]

@[expose] noncomputable def conjLin (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := conjAdd N hMU m
  map_add' := (conjAdd N hMU m).map_add
  map_smul' c v := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul, map_zero, RingHom.id_apply, zero_smul]
    · rw [one_smul, RingHom.id_apply, one_smul]

@[expose] noncomputable def matOf (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) : Mat3 :=
  LinearMap.toMatrix' (conjLin N hMU m)

theorem matOf_mulVec (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) (v : Fin 3 → ZMod 2) :
    matOf N hMU m *ᵥ v = N.coord ((m : G) * uOf N v * (m : G)⁻¹) := by
  rw [matOf, LinearMap.toMatrix'_mulVec]
  rfl

theorem coord_conj_matOf (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) {u : G}
    (hu : u ∈ U) : N.coord ((m : G) * u * (m : G)⁻¹) = matOf N hMU m *ᵥ N.coord u := by
  rw [matOf_mulVec N hMU, uOf_coord N hu]

theorem matOf_mul (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m₁ m₂ : ↥M) :
    matOf N hMU (m₁ * m₂) = matOf N hMU m₁ * matOf N hMU m₂ := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, matOf_mulVec N hMU m₂ v,
    ← coord_conj_matOf N hMU m₁ (conj_mem hMU m₂ (uOf_mem N v)), matOf_mulVec N hMU]
  congr 1
  simp only [Subgroup.coe_mul]
  group

theorem matOf_one (hMU : M ≤ Subgroup.normalizer (U : Set G)) : matOf N hMU 1 = 1 := by
  apply Matrix.mulVec_injective
  funext v
  rw [matOf_mulVec N hMU, Matrix.one_mulVec]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
  exact coord_uOf N v

@[expose] noncomputable def rhoU (hMU : M ≤ Subgroup.normalizer (U : Set G)) : ↥M →* GL32 where
  toFun m := ⟨matOf N hMU m, matOf N hMU m⁻¹,
    by rw [← matOf_mul N hMU, mul_inv_cancel, matOf_one N hMU],
    by rw [← matOf_mul N hMU, inv_mul_cancel, matOf_one N hMU]⟩
  map_one' := Units.ext (matOf_one N hMU)
  map_mul' a b := Units.ext (matOf_mul N hMU a b)

theorem coord_conj_rhoU (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : ↥M) {u : G} (hu : u ∈ U) :
    N.coord ((m : G) * u * (m : G)⁻¹) = ((rhoU N hMU m : GL32) : Mat3) *ᵥ N.coord u :=
  coord_conj_matOf N hMU m hu

theorem rhoU_eq_toSL3 (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hLM : L ≤ M) (l : ↥L) :
    ((rhoU N hMU ⟨l, hLM l.2⟩ : GL32) : Mat3) = ((toSL3 α l : SL3 (ZMod 2)) : Mat3) := by
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨u, hu, rfl⟩ := N.exists_coord_eq v
  rw [← coord_conj_rhoU N hMU _ hu]
  have := N.coord_conj l hu
  rw [natAct_false] at this
  exact this

end Rho

section RhoOf

variable {M : Subgroup G} (r : ↥M →* GL32)

open Classical in
@[expose] noncomputable def rhoOf (t : G) : GL32 := if ht : t ∈ M then r ⟨t, ht⟩ else 1

variable {r}

theorem rhoOf_of_mem {t : G} (ht : t ∈ M) : rhoOf r t = r ⟨t, ht⟩ := dite_eq_left ht

theorem rhoOf_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    rhoOf r (x * y) = rhoOf r x * rhoOf r y := by
  rw [rhoOf_of_mem (M.mul_mem hx hy), rhoOf_of_mem hx, rhoOf_of_mem hy, ← map_mul]
  rfl

theorem rhoOf_inv {x : G} (hx : x ∈ M) : rhoOf r x⁻¹ = (rhoOf r x)⁻¹ := by
  rw [rhoOf_of_mem (M.inv_mem hx), rhoOf_of_mem hx, ← map_inv]
  rfl

theorem rhoOf_pow {x : G} (hx : x ∈ M) (n : ℕ) : rhoOf r (x ^ n) = rhoOf r x ^ n := by
  rw [rhoOf_of_mem (M.pow_mem hx n), rhoOf_of_mem hx, ← map_pow]
  rfl

theorem rhoOf_one : rhoOf r 1 = 1 := by
  rw [rhoOf_of_mem M.one_mem, ← map_one r]
  rfl

theorem rhoOf_sq_eq_one {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x : G}
    (hx : x ∈ F) : rhoOf r x ^ 2 = 1 := by
  rw [← rhoOf_pow (hFM hx), hF.2 x hx, rhoOf_one]

theorem rhoOf_comm {F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 2 F) {x y : G}
    (hx : x ∈ F) (hy : y ∈ F) : rhoOf r x * rhoOf r y = rhoOf r y * rhoOf r x := by
  rw [← rhoOf_mul (hFM hx) (hFM hy), ← rhoOf_mul (hFM hy) (hFM hx),
    show x * y = y * x from congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)]

theorem isPGroup_map_of_le {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) :
    IsPGroup 2 ((T.subgroupOf M).map r) :=
  (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map r

theorem rhoOf_mem_map {T : Subgroup G} (hTM : T ≤ M) {t : G} (ht : t ∈ T) :
    rhoOf r t ∈ (T.subgroupOf M).map r :=
  ⟨⟨t, hTM ht⟩, ht, (rhoOf_of_mem (hTM ht)).symm⟩

theorem exists_of_mem_map {T : Subgroup G} {b : GL32} (hb : b ∈ (T.subgroupOf M).map r) :
    ∃ t ∈ T, rhoOf r t = b := by
  obtain ⟨⟨t, htM⟩, ht, rfl⟩ := hb
  exact ⟨t, ht, rhoOf_of_mem htM⟩

end RhoOf

theorem odd_smul_eq {m : ℕ} (hm : Odd m) (v : Fin 3 → ZMod 2) : m • v = v := by
  obtain ⟨k, rfl⟩ := hm
  rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, CharTwo.add_self_eq_zero, smul_zero,
    zero_add]

theorem zmod_two_units (u : (ZMod 2)ˣ) : (u : ZMod 2) = 1 := by
  revert u
  decide

section Ker

variable [Finite G] {M T L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 (ZMod 2))}

theorem rhoOf_eq_one_of_mem_pCoreOf (h : PUHyp M T L) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {q : G} (hq : q ∈ pCoreOf 2 M) :
    rhoOf (rhoU N hMU) q = 1 := by
  rw [rhoOf_of_mem (pCoreOf_le' M hq)]
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨u, hu, rfl⟩ := N.exists_coord_eq v
  rw [← coord_conj_rhoU N hMU _ hu, Units.val_one, Matrix.one_mulVec]
  show N.coord (q * u * q⁻¹) = N.coord u
  rw [OffIV.commute_of_mem_pCoreOf hq (h.Uq_le_Xq hu), mul_inv_cancel_right]

omit [Finite G] in
theorem conj_eq_of_rhoOf_eq_one (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {t : G} (htM : t ∈ M)
    (h1 : rhoOf (rhoU N hMU) t = 1) {u : G} (hu : u ∈ Uq M T L) : t * u * t⁻¹ = u := by
  refine N.eq_of_coord_eq (conj_mem hMU ⟨t, htM⟩ hu) hu ?_
  rw [show t * u * t⁻¹ = ((⟨t, htM⟩ : ↥M) : G) * u * ((⟨t, htM⟩ : ↥M) : G)⁻¹ from rfl,
    coord_conj_rhoU N hMU _ hu, ← rhoOf_of_mem htM, h1, Units.val_one, Matrix.one_mulVec]

theorem mem_pCoreOf_of_rhoOf_eq_one (h : PUHyp M T L) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {t : G} (htM : t ∈ M)
    (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1) (h1 : rhoOf (rhoU N hMU) t = 1) : t ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_comm_Uq_two htM ht2 fun u hu => ?_
  have e : ⁅u, t⁆ = 1 :=
    calc ⁅u, t⁆ = u * (t * u * t⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = 1 := by rw [conj_eq_of_rhoOf_eq_one N hMU htM h1 hu, mul_inv_cancel]
  rw [e]
  exact Subgroup.one_mem _

theorem rhoOf_eq_one_iff (h : PUHyp M T L) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {t : G} (htT : t ∈ T) :
    rhoOf (rhoU N hMU) t = 1 ↔ t ∈ pCoreOf 2 M := by
  refine ⟨fun h1 => ?_, rhoOf_eq_one_of_mem_pCoreOf h N hMU⟩
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, htT⟩
  exact mem_pCoreOf_of_rhoOf_eq_one h N hMU (h.le htT)
    ⟨e, by simpa using congrArg Subtype.val he⟩ h1

theorem mem_sup_of_rhoOf_eq (h : PUHyp M T L) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {F : Subgroup G} (hFT : F ≤ T)
    {x y : G} (hx : x ∈ T) (hy : y ∈ F) (he : rhoOf (rhoU N hMU) x = rhoOf (rhoU N hMU) y) :
    x ∈ F ⊔ pCoreOf 2 M := by
  have hyT := hFT hy
  have hq : y⁻¹ * x ∈ pCoreOf 2 M := by
    refine (rhoOf_eq_one_iff h N hMU (T.mul_mem (T.inv_mem hyT) hx)).mp ?_
    rw [rhoOf_mul (M.inv_mem (h.le hyT)) (h.le hx), rhoOf_inv (h.le hyT), he, inv_mul_cancel]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact (F ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

omit [Finite G] in
theorem coord_conj_rhoOf (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {g : G} (hg : g ∈ M) {u : G}
    (hu : u ∈ Uq M T L) :
    N.coord (g * u * g⁻¹) = ((rhoOf (rhoU N hMU) g : GL32) : Mat3) *ᵥ N.coord u := by
  rw [rhoOf_of_mem hg]
  exact coord_conj_rhoU N hMU ⟨g, hg⟩ hu

end Ker

section NonSplit

variable [Finite G] {M T L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 (ZMod 2))}

@[expose] noncomputable def cocy (Z U : Subgroup G) (N : NatSec L U ⊥ α false) (x g : G) :
    Fin 3 → ZMod 2 :=
  N.coord (uPart Z U (g * x * g⁻¹ * x⁻¹))

theorem mem_Z0q_of_commutator_mem (h : PUHyp M T L) (hZ0 : Z0q M T = Zq M L ⊔ Uq M T L)
    (hZU : Zq M L ⊓ Uq M T L = ⊥) (hidx : (Z0q M T).relIndex (Xq M) = 2)
    (hαs : Function.Surjective α) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {f : G} (hfM : f ∈ M)
    (hf2 : rhoOf (rhoU N hMU) f ^ 2 = 1) (hf1 : rhoOf (rhoU N hMU) f ≠ 1) {x : G}
    (hxX : x ∈ Xq M) (hxf : ⁅x, f⁆ ∈ Zq M L) : x ∈ Z0q M T := by
  by_contra hx0
  have hXab : ∀ a ∈ Xq M, ∀ b ∈ Xq M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isElemAbelian_Xq.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZX : Zq M L ≤ Xq M := inf_le_left
  have hUX : Uq M T L ≤ Xq M := h.Uq_le_Xq
  have hcommZU : ∀ z ∈ Zq M L, ∀ u ∈ Uq M T L, z * u = u * z := fun z hz u hu =>
    hXab z (hZX hz) u (hUX hu)
  have hZL : ∀ z ∈ Zq M L, ∀ l ∈ L, l * z = z * l := fun z hz l hl =>
    Subgroup.mem_centralizer_iff.mp hz.2 l hl
  have hZn : Zq M L ≤ Subgroup.normalizer (Uq M T L : Set G) := Zq_le.trans hMU
  have hW : ∀ w ∈ Z0q M T, ∃ u ∈ Uq M T L, w * u⁻¹ ∈ Zq M L := fun w hw =>
    exists_of_mem_sup hZn (hZ0 ▸ hw)
  have hMZ : M ≤ Subgroup.normalizer (Zq M L : Set G) := le_normalizer_Zq h.le_normalizer
  have hMW : M ≤ Subgroup.normalizer (Z0q M T : Set G) := le_normalizer_Z0q M T
  have hMX : M ≤ Subgroup.normalizer (Xq M : Set G) := le_normalizer_Xq M
  have hδ : ∀ g ∈ M, g * x * g⁻¹ * x⁻¹ ∈ Z0q M T := by
    intro g hg
    have hgx : g * x * g⁻¹ ∈ Xq M := (Subgroup.mem_normalizer_iff.mp (hMX hg) x).mp hxX
    rcases mem_or_mul_inv_mem hidx hxX hx0 hgx with h1 | h1
    · exfalso
      apply hx0
      have := (Subgroup.mem_normalizer_iff.mp (hMW (M.inv_mem hg)) _).mp h1
      simpa [mul_assoc] using this
    · exact h1
  set r := rhoU N hMU with hr
  set c := cocy (Zq M L) (Uq M T L) N x with hc
  have hcoc : ∀ g ∈ M, ∀ k ∈ M, c (g * k) = c g + ((rhoOf r g : GL32) : Mat3) *ᵥ c k := by
    intro g hg k hk
    have e : g * k * x * (g * k)⁻¹ * x⁻¹ =
        (g * (k * x * k⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    have h1 : g * (k * x * k⁻¹ * x⁻¹) * g⁻¹ ∈ Z0q M T :=
      (Subgroup.mem_normalizer_iff.mp (hMW hg) _).mp (hδ k hk)
    obtain ⟨hu1, -⟩ := uPart_spec (hW _ (hδ k hk))
    obtain ⟨hu2, -⟩ := uPart_spec (hW _ (hδ g hg))
    show N.coord (uPart (Zq M L) (Uq M T L) (g * k * x * (g * k)⁻¹ * x⁻¹)) =
      N.coord (uPart (Zq M L) (Uq M T L) (g * x * g⁻¹ * x⁻¹)) +
        ((rhoOf r g : GL32) : Mat3) *ᵥ N.coord (uPart (Zq M L) (Uq M T L) (k * x * k⁻¹ * x⁻¹))
    rw [e, uPart_mul hZU hcommZU (hW _ h1) (hW _ (hδ g hg)),
      uPart_conj hZU (hMZ hg) (hMU hg) (hW _ (hδ k hk)),
      N.coord_mul ((Subgroup.mem_normalizer_iff.mp (hMU hg) _).mp hu1) hu2,
      coord_conj_rhoOf N hMU hg hu1, add_comm]
  have hc1 : c 1 = 0 := by
    show N.coord (uPart (Zq M L) (Uq M T L) (1 * x * 1⁻¹ * x⁻¹)) = 0
    rw [show (1 : G) * x * 1⁻¹ * x⁻¹ = 1 by group, uPart_of_mem_Z hZU (Subgroup.one_mem _),
      N.coord_one]
  have hpow : ∀ d ∈ M, rhoOf r d = 1 → ∀ n : ℕ, c (d ^ n) = n • c d := by
    intro d hd hd1 n
    induction n with
    | zero => rw [pow_zero, hc1, zero_smul]
    | succ n ih =>
      rw [pow_succ, hcoc _ (M.pow_mem hd n) _ hd, rhoOf_pow hd, hd1, one_pow, Units.val_one,
        Matrix.one_mulVec, ih, succ_nsmul]
  have hker : ∀ d ∈ M, rhoOf r d = 1 → c d = 0 := by
    intro d hd hd1
    obtain ⟨e, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
    have h2 : (d ^ m) ^ 2 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hdm, pow_orderOf_eq_one]
    have hdmQ : d ^ m ∈ pCoreOf 2 M :=
      mem_pCoreOf_of_rhoOf_eq_one h N hMU (M.pow_mem hd m) ⟨e, h2⟩
        (by rw [rhoOf_pow hd, hd1, one_pow])
    have hcm : c (d ^ m) = 0 := by
      show N.coord (uPart (Zq M L) (Uq M T L) (d ^ m * x * (d ^ m)⁻¹ * x⁻¹)) = 0
      rw [OffIV.commute_of_mem_pCoreOf hdmQ hxX, mul_inv_cancel_right, mul_inv_cancel,
        uPart_of_mem_Z hZU (Subgroup.one_mem _), N.coord_one]
    rw [← odd_smul_eq hm (c d), ← hpow d hd hd1 m, hcm]
  have hfac : ∀ g ∈ M, ∀ g' ∈ M, rhoOf r g = rhoOf r g' → c g' = c g := by
    intro g hg g' hg' he
    have hd : g⁻¹ * g' ∈ M := M.mul_mem (M.inv_mem hg) hg'
    have hd1 : rhoOf r (g⁻¹ * g') = 1 := by
      rw [rhoOf_mul (M.inv_mem hg) hg', rhoOf_inv hg, he, inv_mul_cancel]
    have := hcoc g hg _ hd
    rwa [show g * (g⁻¹ * g') = g' by group, hker _ hd hd1, Matrix.mulVec_zero, add_zero] at this
  choose lift hlift using toSL3_surjective hαs
  have hliftM : ∀ s, ((lift s : ↥L) : G) ∈ M := fun s => h.L_le (lift s).2
  have hrhoL : ∀ l : ↥L, ((rhoOf r (l : G) : GL32) : Mat3) = ((toSL3 α l : SL3 (ZMod 2)) : Mat3) :=
    fun l => by
      rw [rhoOf_of_mem (h.L_le l.2)]
      exact rhoU_eq_toSL3 N hMU h.L_le l
  have hrho_lift : ∀ s, ((rhoOf r ((lift s : ↥L) : G) : GL32) : Mat3) = (s : Mat3) := fun s => by
    rw [hrhoL, hlift]
  set c' : SL3 (ZMod 2) → Fin 3 → ZMod 2 := fun s => c ((lift s : ↥L) : G) with hc'
  have hcoc' : S4A.IsCocycle3 c' := by
    intro s₁ s₂
    have e : rhoOf r (((lift s₁ : ↥L) : G) * ((lift s₂ : ↥L) : G)) =
        rhoOf r ((lift (s₁ * s₂) : ↥L) : G) := by
      apply Units.ext
      rw [rhoOf_mul (hliftM s₁) (hliftM s₂), Units.val_mul, hrho_lift, hrho_lift, hrho_lift,
        Matrix.SpecialLinearGroup.coe_mul]
    show c ((lift (s₁ * s₂) : ↥L) : G) = c ((lift s₁ : ↥L) : G) +
      ((s₁ : SL3 (ZMod 2)) : Mat3) *ᵥ c ((lift s₂ : ↥L) : G)
    rw [hfac _ (M.mul_mem (hliftM s₁) (hliftM s₂)) _ (hliftM _) e,
      hcoc _ (hliftM s₁) _ (hliftM s₂), hrho_lift]
  have hdet : ((rhoOf r f : GL32) : Mat3).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact zmod_two_units _
  set t' : SL3 (ZMod 2) := ⟨((rhoOf r f : GL32) : Mat3), hdet⟩ with ht'
  have ht'2 : t' * t' = 1 := by
    apply Subtype.ext
    show ((rhoOf r f : GL32) : Mat3) * ((rhoOf r f : GL32) : Mat3) = 1
    rw [← Units.val_mul, ← pow_two, hf2, Units.val_one]
  have ht'1 : t' ≠ 1 := by
    intro he
    apply hf1
    apply Units.ext
    exact congrArg Subtype.val he
  have hct' : c' t' = 0 := by
    have e : rhoOf r f = rhoOf r ((lift t' : ↥L) : G) := by
      apply Units.ext
      rw [hrho_lift]
    show c ((lift t' : ↥L) : G) = 0
    rw [hfac f hfM _ (hliftM t') e]
    have hz : f * x * f⁻¹ * x⁻¹ ∈ Zq M L := by
      have := (Zq M L).inv_mem hxf
      rwa [commutatorElement_def, show (x * f * x⁻¹ * f⁻¹)⁻¹ = f * x * f⁻¹ * x⁻¹ by group]
        at this
    show N.coord (uPart (Zq M L) (Uq M T L) (f * x * f⁻¹ * x⁻¹)) = 0
    rw [uPart_of_mem_Z hZU hz, N.coord_one]
  obtain ⟨n, hn⟩ := S4A.exists_coboundary hcoc' ht'2 ht'1 hct'
  have hcl : ∀ l ∈ L, c l = ((rhoOf r l : GL32) : Mat3) *ᵥ n - n := by
    intro l hl
    have hrl : ((rhoOf r l : GL32) : Mat3) = ((toSL3 α ⟨l, hl⟩ : SL3 (ZMod 2)) : Mat3) :=
      hrhoL ⟨l, hl⟩
    have e : rhoOf r ((lift (toSL3 α ⟨l, hl⟩) : ↥L) : G) = rhoOf r l := by
      apply Units.ext
      rw [hrho_lift, hrl]
    rw [hfac _ (hliftM _) l (h.L_le hl) e]
    have := hn (toSL3 α ⟨l, hl⟩)
    rw [← hrl] at this
    exact this
  have hun := uOf_mem N n
  have hcun := coord_uOf N n
  have hx'X : x * uOf N n ∈ Xq M := (Xq M).mul_mem hxX (hUX hun)
  have hδ' : ∀ l ∈ L, l * (x * uOf N n) * l⁻¹ * (x * uOf N n)⁻¹ ∈ Zq M L := by
    intro l hl
    have hlM := h.L_le hl
    have hlu : l * uOf N n * l⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.mp (hMU hlM) _).mp hun
    have hv : l * uOf N n * l⁻¹ * (uOf N n)⁻¹ ∈ Uq M T L :=
      (Uq M T L).mul_mem hlu ((Uq M T L).inv_mem hun)
    have hlx : l * x * l⁻¹ ∈ Xq M := (Subgroup.mem_normalizer_iff.mp (hMX hlM) x).mp hxX
    have e : l * (x * uOf N n) * l⁻¹ * (x * uOf N n)⁻¹ =
        (l * x * l⁻¹ * x⁻¹) * (l * uOf N n * l⁻¹ * (uOf N n)⁻¹) := by
      have h1 := hXab _ (hUX hv) _ ((Xq M).inv_mem hxX)
      calc l * (x * uOf N n) * l⁻¹ * (x * uOf N n)⁻¹ =
          (l * x * l⁻¹) * ((l * uOf N n * l⁻¹ * (uOf N n)⁻¹) * x⁻¹) := by group
        _ = (l * x * l⁻¹) * (x⁻¹ * (l * uOf N n * l⁻¹ * (uOf N n)⁻¹)) := by rw [h1]
        _ = _ := by group
    have hw : l * (x * uOf N n) * l⁻¹ * (x * uOf N n)⁻¹ ∈ Z0q M T := by
      rw [e]
      exact (Z0q M T).mul_mem (hδ l hlM) (hZ0 ▸ Subgroup.mem_sup_right hv)
    have hv' : ∃ u ∈ Uq M T L, l * uOf N n * l⁻¹ * (uOf N n)⁻¹ * u⁻¹ ∈ Zq M L :=
      ⟨_, hv, by rw [mul_inv_cancel]; exact Subgroup.one_mem _⟩
    have hu1 : uPart (Zq M L) (Uq M T L) (l * (x * uOf N n) * l⁻¹ * (x * uOf N n)⁻¹) = 1 := by
      obtain ⟨hu0, -⟩ := uPart_spec (hW _ (hδ l hlM))
      rw [e, uPart_mul hZU hcommZU (hW _ (hδ l hlM)) hv', uPart_of_mem_U hZU hv]
      refine N.eq_one_of_coord_eq_zero ((Uq M T L).mul_mem hu0 hv) ?_
      rw [N.coord_mul hu0 hv, N.coord_mul hlu ((Uq M T L).inv_mem hun), N.coord_inv hun,
        coord_conj_rhoOf N hMU hlM hun, hcun]
      have := hcl l hl
      simp only [hc, cocy] at this
      rw [this, ← sub_eq_add_neg, CharTwo.add_self_eq_zero]
    obtain ⟨-, hz⟩ := uPart_spec (hW _ hw)
    rwa [hu1, inv_one, mul_one] at hz
  set x' := x * uOf N n with hx'
  have hφmul : ∀ g ∈ L, ∀ k ∈ L, g * k * x' * (g * k)⁻¹ * x'⁻¹ =
      (g * x' * g⁻¹ * x'⁻¹) * (k * x' * k⁻¹ * x'⁻¹) := by
    intro g hg k hk
    have hzk := hδ' k hk
    have hzg := hδ' g hg
    have e : g * k * x' * (g * k)⁻¹ * x'⁻¹ =
        (g * (k * x' * k⁻¹ * x'⁻¹) * g⁻¹) * (g * x' * g⁻¹ * x'⁻¹) := by group
    rw [e, hZL _ hzk g hg, mul_inv_cancel_right]
    exact hXab _ (hZX hzk) _ (hZX hzg)
  have hφ1 : ∀ g ∈ L, g * x' * g⁻¹ * x'⁻¹ = 1 → g * x' = x' * g := fun g _ he => by
    calc g * x' = (g * x' * g⁻¹ * x'⁻¹) * x' * g := by group
      _ = x' * g := by rw [he, one_mul]
  have hφinv : ∀ g ∈ L, g⁻¹ * x' * g⁻¹⁻¹ * x'⁻¹ = (g * x' * g⁻¹ * x'⁻¹)⁻¹ := by
    intro g hg
    have := hφmul g hg g⁻¹ (L.inv_mem hg)
    rw [mul_inv_cancel, show (1 : G) * x' * 1⁻¹ * x'⁻¹ = 1 by group] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  have hcommL : ⁅L, L⁆ ≤ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine hφ1 _ (L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)) ?_
    rw [commutatorElement_def, hφmul _ (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) _
        (L.inv_mem hb), hφmul _ (L.mul_mem ha hb) _ (L.inv_mem ha), hφmul _ ha _ hb,
      hφinv _ ha, hφinv _ hb]
    have hza := hZX (hδ' a ha)
    have hzb := hZX (hδ' b hb)
    rw [hXab _ hza _ hzb]
    group
  have hx'C : x' ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : l ∈ ⁅L, L⁆ := by rw [h.perfect]; exact hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcommL hl')
  have hx'Z : x' ∈ Zq M L := ⟨hx'X, hx'C⟩
  apply hx0
  have e : x = x' * (uOf N n)⁻¹ := by rw [hx']; group
  rw [e, hZ0]
  exact (Zq M L ⊔ Uq M T L).mul_mem (Subgroup.mem_sup_left hx'Z)
    (Subgroup.mem_sup_right ((Uq M T L).inv_mem hun))

end NonSplit

section Off

variable {L U : Subgroup G} {α : ↥L →* ↥(StatedSL 3 (ZMod 2))}

@[expose] def preK (Z W : Subgroup G) (N : NatSec L U ⊥ α false) (hZU : Z ⊓ U = ⊥)
    (hcomm : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) (hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w)
    (hW : ∀ w ∈ W, ∃ u ∈ U, w * u⁻¹ ∈ Z) (A : Mat3) : Subgroup G where
  carrier := {w | w ∈ W ∧ (A - 1) *ᵥ N.coord (uPart Z U w) = 0}
  one_mem' := ⟨W.one_mem, by rw [uPart_of_mem_U hZU U.one_mem, N.coord_one, Matrix.mulVec_zero]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    rw [uPart_mul hZU hcomm (hW a ha) (hW b hb),
      N.coord_mul (uPart_spec (hW a ha)).1 (uPart_spec (hW b hb)).1, Matrix.mulVec_add, ha', hb',
      add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨W.inv_mem ha, ?_⟩
    rw [uPart_inv hZU (hW a ha) (hWU a ha), N.coord_inv (uPart_spec (hW a ha)).1,
      Matrix.mulVec_neg, ha']
    exact neg_zero

variable {Z W : Subgroup G} {N : NatSec L U ⊥ α false} {hZU : Z ⊓ U = ⊥}
  {hcomm : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z} {hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w}
  {hW : ∀ w ∈ W, ∃ u ∈ U, w * u⁻¹ ∈ Z}

theorem mem_preK {A : Mat3} {w : G} :
    w ∈ preK Z W N hZU hcomm hWU hW A ↔ w ∈ W ∧ (A - 1) *ᵥ N.coord (uPart Z U w) = 0 :=
  Iff.rfl

theorem uPart_mul_of_mem_U {w : G} (hw : ∃ u ∈ U, w * u⁻¹ ∈ Z) {a : G} (ha : a ∈ U)
    (hZU : Z ⊓ U = ⊥) (hcomm : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) :
    uPart Z U (w * a) = uPart Z U w * a := by
  rw [uPart_mul hZU hcomm hw ⟨a, ha, by rw [mul_inv_cancel]; exact Z.one_mem⟩,
    uPart_of_mem_U hZU ha]

theorem relIndex_preK (hUW : U ≤ W) {A : Mat3} {c : Fin 3 → ZMod 2} (hc0 : c ≠ 0)
    (hc : ∀ v, (A - 1) *ᵥ v = 0 ∨ (A - 1) *ᵥ v = c) (hcv : ∃ v, (A - 1) *ᵥ v = c) :
    (preK Z W N hZU hcomm hWU hW A).relIndex W = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  obtain ⟨v₀, hv₀⟩ := hcv
  refine ⟨uOf N v₀, hUW (uOf_mem N v₀), fun b hb => ?_⟩
  rw [mem_preK, mem_preK, uPart_mul_of_mem_U (hW b hb) (uOf_mem N v₀) hZU hcomm,
    N.coord_mul (uPart_spec (hW b hb)).1 (uOf_mem N v₀), coord_uOf, Matrix.mulVec_add, hv₀]
  rcases hc (N.coord (uPart Z U b)) with h0 | h0 <;> rw [h0]
  · simp [hc0, W.mul_mem hb (hUW (uOf_mem N v₀)), hb]
  · rw [CharTwo.add_self_eq_zero]
    simp [hc0, W.mul_mem hb (hUW (uOf_mem N v₀)), hb]

theorem relIndex_preK_inf (hUW : U ≤ W) {A B : Mat3} {c : Fin 3 → ZMod 2}
    (hc : ∀ v, (B - 1) *ᵥ v = 0 ∨ (B - 1) *ᵥ v = c) {v₁ : Fin 3 → ZMod 2}
    (hv₁A : (A - 1) *ᵥ v₁ = 0) (hv₁B : (B - 1) *ᵥ v₁ ≠ 0) :
    (preK Z W N hZU hcomm hWU hW A ⊓ preK Z W N hZU hcomm hWU hW B).relIndex
      (preK Z W N hZU hcomm hWU hW A) = 2 := by
  have hv₁c : (B - 1) *ᵥ v₁ = c := (hc v₁).resolve_left hv₁B
  have hc0 : c ≠ 0 := hv₁c ▸ hv₁B
  have haA : uOf N v₁ ∈ preK Z W N hZU hcomm hWU hW A := by
    rw [mem_preK, uPart_of_mem_U hZU (uOf_mem N v₁), coord_uOf]
    exact ⟨hUW (uOf_mem N v₁), hv₁A⟩
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨uOf N v₁, haA, fun b hb => ?_⟩
  have hbW := (mem_preK.mp hb).1
  have hba : b * uOf N v₁ ∈ preK Z W N hZU hcomm hWU hW A :=
    Subgroup.mul_mem _ hb haA
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_preK (A := B), mem_preK (A := B),
    uPart_mul_of_mem_U (hW b hbW) (uOf_mem N v₁) hZU hcomm,
    N.coord_mul (uPart_spec (hW b hbW)).1 (uOf_mem N v₁), coord_uOf, Matrix.mulVec_add, hv₁c]
  rcases hc (N.coord (uPart Z U b)) with h0 | h0 <;> rw [h0]
  · simp [hc0, hba, hb, hbW, W.mul_mem hbW (hUW (uOf_mem N v₁))]
  · rw [CharTwo.add_self_eq_zero]
    simp [hc0, hba, hb, hbW, W.mul_mem hbW (hUW (uOf_mem N v₁))]

theorem preK_le {A : Mat3} : preK Z W N hZU hcomm hWU hW A ≤ W := fun _ hw => (mem_preK.mp hw).1

end Off

section Offenders

variable [Finite G] {M T L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 (ZMod 2))}

theorem exists_of_isXOff (h : PUHyp M T L) (hZ0 : Z0q M T = Zq M L ⊔ Uq M T L)
    (hZU : Zq M L ⊓ Uq M T L = ⊥) (hidx : (Z0q M T).relIndex (Xq M) = 2)
    (hαs : Function.Surjective α) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {F : Subgroup G} (hF : IsXOff M T F) :
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, rhoOf (rhoU N hMU) f₁ ≠ 1 ∧ rhoOf (rhoU N hMU) f₂ ≠ 1 ∧
      rhoOf (rhoU N hMU) f₁ ≠ rhoOf (rhoU N hMU) f₂ ∧
      (∀ v, (((rhoOf (rhoU N hMU) f₁ : GL32) : Mat3) - 1) *ᵥ v = 0 ↔
        (((rhoOf (rhoU N hMU) f₂ : GL32) : Mat3) - 1) *ᵥ v = 0) ∧
      (∀ x ∈ F, rhoOf (rhoU N hMU) x = 1 ∨ rhoOf (rhoU N hMU) x = rhoOf (rhoU N hMU) f₁ ∨
        rhoOf (rhoU N hMU) x = rhoOf (rhoU N hMU) f₂ ∨
        rhoOf (rhoU N hMU) x = rhoOf (rhoU N hMU) f₁ * rhoOf (rhoU N hMU) f₂) ∧
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F ∧
      (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨hFT, hFea, hFQ, hoff⟩ := hF
  have hFM : F ≤ M := hFT.trans h.le
  set r := rhoU N hMU with hr
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => Subgroup.index_ne_zero_of_finite
  have hXab : ∀ a ∈ Xq M, ∀ b ∈ Xq M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isElemAbelian_Xq.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcommZU : ∀ z ∈ Zq M L, ∀ u ∈ Uq M T L, z * u = u * z := fun z hz u hu =>
    hXab z hz.1 u (h.Uq_le_Xq hu)
  have hZ0X : Z0q M T ≤ Xq M := h.Z0q_le_Xq
  have hWU : ∀ w ∈ Z0q M T, ∀ u ∈ Uq M T L, w * u = u * w := fun w hw u hu =>
    hXab w (hZ0X hw) u (h.Uq_le_Xq hu)
  have hZn : Zq M L ≤ Subgroup.normalizer (Uq M T L : Set G) := Zq_le.trans hMU
  have hW : ∀ w ∈ Z0q M T, ∃ u ∈ Uq M T L, w * u⁻¹ ∈ Zq M L := fun w hw =>
    exists_of_mem_sup hZn (hZ0 ▸ hw)
  have hUW : Uq M T L ≤ Z0q M T := Uq_le_Z0q h.L_le
  let ρF : ↥F →* GL32 := r.comp (Subgroup.inclusion hFM)
  have hρF : ∀ x : ↥F, ρF x = rhoOf r x := fun x => (rhoOf_of_mem (r := r) (hFM x.2)).symm
  have hidxF : (pCoreOf 2 M).relIndex F = Nat.card ρF.range := by
    rw [Subgroup.relIndex, ← Subgroup.index_ker]
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hρF, rhoOf_eq_one_iff h N hMU (hFT x.2)]
  obtain ⟨f₁, hf₁F, hf₁Q⟩ := Set.not_subset.mp fun hs => hFQ hs
  have hb₁ : rhoOf r f₁ ≠ 1 := fun he => hf₁Q ((rhoOf_eq_one_iff h N hMU (hFT hf₁F)).mp he)
  have hs₁ := rhoOf_sq_eq_one (r := r) hFM hFea hf₁F
  obtain ⟨c₁, hc₁0, hc₁, hcv₁⟩ := transv hs₁ hb₁
  set C := Subgroup.centralizer (F : Set G) ⊓ Xq M with hC
  have hCW : C ≤ Z0q M T := by
    intro w hw
    obtain ⟨hwC, hwX⟩ := Subgroup.mem_inf.mp hw
    refine mem_Z0q_of_commutator_mem h hZ0 hZU hidx hαs N hMU (hFM hf₁F) hs₁ hb₁ hwX ?_
    have e : ⁅w, f₁⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hwC f₁ hf₁F).symm
    rw [e]
    exact Subgroup.one_mem _
  have hCK : ∀ f ∈ F, C ≤ preK (Zq M L) (Z0q M T) N hZU hcommZU hWU hW
      ((rhoOf r f : GL32) : Mat3) := by
    intro f hf w hw
    have hwW := hCW hw
    refine mem_preK.mpr ⟨hwW, ?_⟩
    have hfw : f * w * f⁻¹ = w := by
      rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).1 f hf, mul_inv_cancel_right]
    have e := uPart_conj hZU (le_normalizer_Zq h.le_normalizer (hFM hf)) (hMU (hFM hf))
      (hW w hwW)
    rw [hfw] at e
    have hcoord := coord_conj_rhoOf N hMU (hFM hf) (uPart_spec (hW w hwW)).1
    rw [← e] at hcoord
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hcoord, sub_self]
  have hXF : (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = C.relIndex (Z0q M T) * 2 := by
    rw [← Subgroup.inf_relIndex_right, ← hidx]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ hCW hZ0X).symm
  have h4 : 4 ≤ (Subgroup.centralizer (F : Set G)).relIndex (Xq M) := by
    rw [hXF]
    have := Subgroup.relIndex_le_of_le_left (hCK f₁ hf₁F) (hne C (Z0q M T))
    rw [relIndex_preK hUW hc₁0 hc₁ hcv₁] at this
    omega
  rw [hidxF] at hoff
  obtain ⟨f₂, hf₂F, hb₂, hb₂₁⟩ : ∃ f ∈ F, rhoOf r f ≠ 1 ∧ rhoOf r f ≠ rhoOf r f₁ := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hle : ρF.range ≤ Subgroup.zpowers (rhoOf r f₁) := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      by_cases hx1 : rhoOf r x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · rw [hall x x.2 hx1]
        exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hs₁ hb₁] at this
    omega
  have hs₂ := rhoOf_sq_eq_one (r := r) hFM hFea hf₂F
  obtain ⟨c₂, hc₂0, hc₂, hcv₂⟩ := transv hs₂ hb₂
  have hP := isPGroup_map_of_le (r := r) h.le h.isPGroup
  have hfour : ∀ x ∈ F, rhoOf r x = 1 ∨ rhoOf r x = rhoOf r f₁ ∨ rhoOf r x = rhoOf r f₂ ∨
      rhoOf r x = rhoOf r f₁ * rhoOf r f₂ := fun x hx =>
    mem_of_comm_four hP (rhoOf_mem_map h.le (hFT hf₁F)) (rhoOf_mem_map h.le (hFT hf₂F))
      (rhoOf_mem_map h.le (hFT hx)) hs₁ hs₂ hb₁ hb₂ (Ne.symm hb₂₁)
      (rhoOf_comm hFM hFea hf₁F hf₂F) (rhoOf_comm hFM hFea hx hf₁F) (rhoOf_comm hFM hFea hx hf₂F)
  have hle4 : Nat.card ρF.range ≤ 4 := by
    have hsub : (ρF.range : Set GL32) ⊆
        {1, rhoOf r f₁, rhoOf r f₂, rhoOf r f₁ * rhoOf r f₂} := by
      rintro _ ⟨x, rfl⟩
      rw [hρF]
      rcases hfour x x.2 with e | e | e | e <;> rw [e] <;> simp
    calc Nat.card ρF.range = Nat.card ↥(ρF.range : Set GL32) := rfl
      _ ≤ Nat.card ↥({1, rhoOf r f₁, rhoOf r f₂, rhoOf r f₁ * rhoOf r f₂} : Set GL32) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 4 := by
          rw [Nat.card_coe_set_eq]
          refine (Set.ncard_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          rw [Set.ncard_singleton]
  have hax : ∀ {f f' : G} {c c' : Fin 3 → ZMod 2}, f ∈ F → f' ∈ F → c ≠ 0 →
      (∀ v, (((rhoOf r f : GL32) : Mat3) - 1) *ᵥ v = 0 ∨
        (((rhoOf r f : GL32) : Mat3) - 1) *ᵥ v = c) →
      (∃ v, (((rhoOf r f : GL32) : Mat3) - 1) *ᵥ v = c) →
      (∀ v, (((rhoOf r f' : GL32) : Mat3) - 1) *ᵥ v = 0 ∨
        (((rhoOf r f' : GL32) : Mat3) - 1) *ᵥ v = c') →
      ∀ v, (((rhoOf r f : GL32) : Mat3) - 1) *ᵥ v = 0 →
        (((rhoOf r f' : GL32) : Mat3) - 1) *ᵥ v = 0 := by
    intro f f' c c' hf hf' hc0 hc hcv hc' v hv
    by_contra hv'
    have h2 := relIndex_preK_inf (Z := Zq M L) (W := Z0q M T) (N := N) (hZU := hZU)
      (hcomm := hcommZU) (hWU := hWU) (hW := hW) hUW hc' hv hv'
    have h1 := relIndex_preK (Z := Zq M L) (W := Z0q M T) (N := N) (hZU := hZU)
      (hcomm := hcommZU) (hWU := hWU) (hW := hW) hUW hc0 hc hcv
    set K₁ := preK (Zq M L) (Z0q M T) N hZU hcommZU hWU hW ((rhoOf r f : GL32) : Mat3)
    set K₂ := preK (Zq M L) (Z0q M T) N hZU hcommZU hWU hW ((rhoOf r f' : GL32) : Mat3)
    have hK₁ : K₁ ≤ Z0q M T := preK_le
    have h4' := Subgroup.relIndex_mul_relIndex (K₁ ⊓ K₂) K₁ (Z0q M T) inf_le_left hK₁
    rw [h2, h1] at h4'
    have := Subgroup.relIndex_le_of_le_left (le_inf (hCK f hf) (hCK f' hf')) (hne C (Z0q M T))
    rw [← h4'] at this
    omega
  refine ⟨f₁, hf₁F, f₂, hf₂F, hb₁, hb₂, Ne.symm hb₂₁, fun v =>
    ⟨hax hf₁F hf₂F hc₁0 hc₁ hcv₁ hc₂ v, hax hf₂F hf₁F hc₂0 hc₂ hcv₂ hc₁ v⟩, hfour, ?_, ?_⟩
  · rw [hidxF]
    omega
  · rw [hidxF]
    omega

theorem le_sup_of_isXOff (h : PUHyp M T L) (hZ0 : Z0q M T = Zq M L ⊔ Uq M T L)
    (hZU : Zq M L ⊓ Uq M T L = ⊥) (hidx : (Z0q M T).relIndex (Xq M) = 2)
    (hαs : Function.Surjective α) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {F₁ F₂ : Subgroup G}
    (hF₁ : IsXOff M T F₁) (hF₂ : IsXOff M T F₂) : F₂ ≤ F₁ ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hb₁, hb₂, hb₁₂, hax, -, -, -⟩ :=
    exists_of_isXOff h hZ0 hZU hidx hαs N hMU hF₁
  obtain ⟨g₁, hg₁, g₂, hg₂, hb₁', hb₂', hb₁₂', hax', hfour', -, -⟩ :=
    exists_of_isXOff h hZ0 hZU hidx hαs N hMU hF₂
  set r := rhoU N hMU
  have hM₁ : F₁ ≤ M := hF₁.1.trans h.le
  have hM₂ : F₂ ≤ M := hF₂.1.trans h.le
  have hP := isPGroup_map_of_le (r := r) h.le h.isPGroup
  have hm : ∀ {x : G} {F : Subgroup G}, IsXOff M T F → x ∈ F →
      rhoOf r x ∈ (T.subgroupOf M).map r := fun hF hx => rhoOf_mem_map h.le (hF.1 hx)
  set E := (F₁.subgroupOf M).map r
  have hE : ∀ x ∈ F₁, rhoOf r x ∈ E := fun x hx => rhoOf_mem_map hM₁ hx
  have hgE : ∀ {g g' : G}, g ∈ F₂ → g' ∈ F₂ → rhoOf r g ≠ 1 → rhoOf r g' ≠ 1 →
      rhoOf r g ≠ rhoOf r g' →
      (∀ v, (((rhoOf r g : GL32) : Mat3) - 1) *ᵥ v = 0 ↔
        (((rhoOf r g' : GL32) : Mat3) - 1) *ᵥ v = 0) →
      rhoOf r g ∈ E := fun {g g'} hg hg' hn hn' hgg' hgax => by
    rcases eq_of_axis_four hP (hm hF₁ hf₁) (hm hF₁ hf₂) (hm hF₂ hg) (hm hF₂ hg')
        (rhoOf_sq_eq_one hM₁ hF₁.2.1 hf₁) (rhoOf_sq_eq_one hM₁ hF₁.2.1 hf₂)
        (rhoOf_sq_eq_one hM₂ hF₂.2.1 hg) (rhoOf_sq_eq_one hM₂ hF₂.2.1 hg') hb₁ hb₂ hn hn' hb₁₂
        (rhoOf_comm hM₁ hF₁.2.1 hf₁ hf₂) hax hgg' (rhoOf_comm hM₂ hF₂.2.1 hg hg') hgax with
      e | e | e
    · rw [e]
      exact hE _ hf₁
    · rw [e]
      exact hE _ hf₂
    · rw [e]
      exact E.mul_mem (hE _ hf₁) (hE _ hf₂)
  have hg₁E := hgE hg₁ hg₂ hb₁' hb₂' hb₁₂' hax'
  have hg₂E := hgE hg₂ hg₁ hb₂' hb₁' (Ne.symm hb₁₂') fun v => (hax' v).symm
  intro x hx
  have hxE : rhoOf r x ∈ E := by
    rcases hfour' x hx with e | e | e | e <;> rw [e]
    · exact E.one_mem
    · exact hg₁E
    · exact hg₂E
    · exact E.mul_mem hg₁E hg₂E
  obtain ⟨y, hy, hxy⟩ := exists_of_mem_map hxE
  exact mem_sup_of_rhoOf_eq h N hMU hF₁.1 (hF₂.1 hx) hy hxy.symm

theorem mem_sup_of_mem_centralizer (h : PUHyp M T L) (hZ0 : Z0q M T = Zq M L ⊔ Uq M T L)
    (hZU : Zq M L ⊓ Uq M T L = ⊥) (hidx : (Z0q M T).relIndex (Xq M) = 2)
    (hαs : Function.Surjective α) (N : NatSec L (Uq M T L) ⊥ α false)
    (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G)) {F : Subgroup G} (hF : IsXOff M T F)
    {y : G} (hyT : y ∈ T) (hyC : y ∈ Subgroup.centralizer (F : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hb₁, hb₂, hb₁₂, -, -, -, -⟩ :=
    exists_of_isXOff h hZ0 hZU hidx hαs N hMU hF
  set r := rhoU N hMU
  have hFM : F ≤ M := hF.1.trans h.le
  have hP := isPGroup_map_of_le (r := r) h.le h.isPGroup
  have hy : ∀ {f : G}, f ∈ F → rhoOf r y * rhoOf r f = rhoOf r f * rhoOf r y := fun {f} hf => by
    rw [← rhoOf_mul (h.le hyT) (hFM hf), ← rhoOf_mul (hFM hf) (h.le hyT),
      Subgroup.mem_centralizer_iff.mp hyC f hf]
  rcases mem_of_comm_four hP (rhoOf_mem_map h.le (hF.1 hf₁)) (rhoOf_mem_map h.le (hF.1 hf₂))
      (rhoOf_mem_map h.le hyT) (rhoOf_sq_eq_one hFM hF.2.1 hf₁) (rhoOf_sq_eq_one hFM hF.2.1 hf₂)
      hb₁ hb₂ hb₁₂ (rhoOf_comm hFM hF.2.1 hf₁ hf₂) (hy hf₁) (hy hf₂) with e | e | e | e
  · exact mem_sup_of_rhoOf_eq h N hMU hF.1 hyT F.one_mem (e.trans rhoOf_one.symm)
  · exact mem_sup_of_rhoOf_eq h N hMU hF.1 hyT hf₁ e
  · exact mem_sup_of_rhoOf_eq h N hMU hF.1 hyT hf₂ e
  · exact mem_sup_of_rhoOf_eq h N hMU hF.1 hyT (F.mul_mem hf₁ hf₂)
      (e.trans (rhoOf_mul (hFM hf₁) (hFM hf₂)).symm)

end Offenders

end OffV

open OffV in
theorem PUHyp.xOffData_of_isSL3TwoZ {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hX : IsSL3TwoZ M T L) : XOffData M T := by
  obtain ⟨hZ0, hZU, hidx, α, hαs, hnat⟩ := hX
  set N := NatSec.ofIsSum hnat
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  refine XOffData.of_cent h h.centralizer_Z0q (fun F₁ F₂ h₁ h₂ => ?_) (fun F hF => ?_)
    (fun F hF y hy hyC => mem_sup_of_mem_centralizer h hZ0 hZU hidx hαs N hMU hF hy hyC)
  · exact le_antisymm (sup_le (le_sup_of_isXOff h hZ0 hZU hidx hαs N hMU h₂ h₁) le_sup_right)
      (sup_le (le_sup_of_isXOff h hZ0 hZU hidx hαs N hMU h₁ h₂) le_sup_right)
  · obtain ⟨-, -, -, -, -, -, -, -, -, heq, -⟩ := exists_of_isXOff h hZ0 hZU hidx hαs N hMU hF
    exact heq

open OffV in
theorem PUHyp.xOffCent_of_isSL3TwoZ {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hX : IsSL3TwoZ M T L) :
    (∀ F : Subgroup G, IsXOff M T F → T ⊓ Subgroup.centralizer (F : Set G) ≤ F ⊔ pCoreOf 2 M) ∧
      ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨hZ0, hZU, hidx, α, hαs, hnat⟩ := hX
  set N := NatSec.ofIsSum hnat
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  refine ⟨fun F hF y hy =>
    mem_sup_of_mem_centralizer h hZ0 hZU hidx hαs N hMU hF hy.1 hy.2, fun F hF => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h4⟩ := exists_of_isXOff h hZ0 hZU hidx hαs N hMU hF
  exact h4

end CFSG.Quasithin.MS93
