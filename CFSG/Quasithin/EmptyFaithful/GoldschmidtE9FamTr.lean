module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.E9.Tr

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {M : Type} [Group M]

@[expose] def liftHom (L : Subgroup G) (φ : ↥L ≃* M) (g : M) : M →* G :=
  L.subtype.comp (φ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom)

theorem liftHom_apply (L : Subgroup G) (φ : ↥L ≃* M) (g y : M) :
    liftHom L φ g y = ((φ.symm (g * y * g⁻¹) : ↥L) : G) := rfl

theorem liftHom_mem (L : Subgroup G) (φ : ↥L ≃* M) (g y : M) : liftHom L φ g y ∈ L :=
  (φ.symm (g * y * g⁻¹)).2

theorem liftHom_injective (L : Subgroup G) (φ : ↥L ≃* M) (g : M) :
    Function.Injective (liftHom L φ g) := by
  intro a b h
  have h1 : φ.symm (g * a * g⁻¹) = φ.symm (g * b * g⁻¹) := Subtype.ext h
  have h2 : g * a * g⁻¹ = g * b * g⁻¹ := φ.symm.injective h1
  exact mul_left_cancel (mul_right_cancel h2)

@[expose] def Carries (L P : Subgroup G) (φ : ↥L ≃* M) (g : M) (U : Subgroup M) : Prop :=
  ∀ x : M, x ∈ (P.subgroupOf L).map φ.toMonoidHom ↔ g⁻¹ * x * g ∈ U

theorem exists_carries [Finite G] {L P : Subgroup G} (hP : IsSylowTwoOf P L) (φ : ↥L ≃* M)
    {U : Subgroup M} (hU : ∃ U₀ : Sylow 2 M, (U₀ : Subgroup M) = U) :
    ∃ g : M, Carries L P φ g U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M := Finite.of_equiv _ φ.toEquiv
  obtain ⟨U₀, hU₀⟩ := hU
  let Q : Sylow 2 M := (A4.toSylow hP).mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ : (Q : Subgroup M) = (P.subgroupOf L).map φ.toMonoidHom := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M U₀ Q
  refine ⟨g, fun x => ?_⟩
  rw [← hQ, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ _
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem liftHom_mem_of_mem {L P : Subgroup G} {φ : ↥L ≃* M} {g : M} {U : Subgroup M}
    (hc : Carries L P φ g U) {u : M} (hu : u ∈ U) : liftHom L φ g u ∈ P := by
  have hmem : g * u * g⁻¹ ∈ (P.subgroupOf L).map φ.toMonoidHom := by
    rw [hc]
    simpa [mul_assoc] using hu
  obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hmem
  have h1 : φ.symm (g * u * g⁻¹) = y := by
    rw [← hyu]
    exact φ.symm_apply_apply y
  rw [liftHom_apply, h1]
  exact hy

theorem exists_liftHom_eq {L P : Subgroup G} (hP : P ≤ L) {φ : ↥L ≃* M} {g : M} {U : Subgroup M}
    (hc : Carries L P φ g U) {x : G} (hx : x ∈ P) : ∃ u ∈ U, liftHom L φ g u = x := by
  have hxL : x ∈ L := hP hx
  have hmem : φ ⟨x, hxL⟩ ∈ (P.subgroupOf L).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx, rfl⟩
  refine ⟨g⁻¹ * φ ⟨x, hxL⟩ * g, (hc _).mp hmem, ?_⟩
  rw [liftHom_apply]
  have h1 : g * (g⁻¹ * φ ⟨x, hxL⟩ * g) * g⁻¹ = φ ⟨x, hxL⟩ := by group
  rw [h1, MulEquiv.symm_apply_apply]

theorem liftHom_mem_normalizer {L P : Subgroup G} (hP : P ≤ L) {φ : ↥L ≃* M} {g : M}
    {U : Subgroup M} (hc : Carries L P φ g U) {y : M}
    (hy : y ∈ Subgroup.normalizer (U : Set M)) :
    liftHom L φ g y ∈ Subgroup.normalizer (P : Set G) := by
  set z : ↥L := φ.symm (g * y * g⁻¹) with hz
  have hzz : φ z = g * y * g⁻¹ := by simp [hz]
  have e1 : ∀ w : ↥L, w ∈ P.subgroupOf L ↔ g⁻¹ * φ w * g ∈ U := fun w => by
    rw [← hc, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hzN : ∀ x : ↥L, x ∈ P.subgroupOf L ↔ z * x * z⁻¹ ∈ P.subgroupOf L := by
    intro x
    rw [e1, e1]
    have e2 : g⁻¹ * φ (z * x * z⁻¹) * g = y * (g⁻¹ * φ x * g) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hzz]
      group
    rw [e2]
    exact Subgroup.mem_normalizer_iff.mp hy _
  show (z : G) ∈ Subgroup.normalizer (P : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have haL : a ∈ L := hP ha
    have := (hzN ⟨a, haL⟩).mp ha
    simpa [Subgroup.mem_subgroupOf] using this
  · intro ha
    have haL : (z : G) * a * (z : G)⁻¹ ∈ L := hP ha
    have haL' : a ∈ L := by
      have h1 : (z : G)⁻¹ * ((z : G) * a * (z : G)⁻¹) * (z : G) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem z.2) haL) z.2
      simpa [mul_assoc] using h1
    exact Subgroup.mem_subgroupOf.mp ((hzN ⟨a, haL'⟩).mpr (by
      simpa [Subgroup.mem_subgroupOf] using ha))

@[expose] noncomputable def conjAut (L : Subgroup G) (φ : ↥L ≃* M) (g : M) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) : MulAut M :=
  (MulAut.conj g)⁻¹ * MulAut.congr φ (conjAct L ⟨v, hv⟩) * MulAut.conj g

theorem conjAut_apply_of_commute {L : Subgroup G} (φ : ↥L ≃* M) (g : M) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) {y : M}
    (h : v * liftHom L φ g y = liftHom L φ g y * v) : conjAut L φ g hv y = y := by
  set z : ↥L := φ.symm (g * y * g⁻¹) with hz
  have hzz : φ z = g * y * g⁻¹ := by simp [hz]
  have hαz : conjAct L ⟨v, hv⟩ z = z := by
    apply Subtype.ext
    change v * (z : G) * v⁻¹ = (z : G)
    rw [show (z : G) = liftHom L φ g y from rfl, h]
    group
  have e1 : conjAut L φ g hv y =
      (MulAut.conj g)⁻¹ (φ (conjAct L ⟨v, hv⟩ (φ.symm (g * y * g⁻¹)))) := rfl
  rw [e1, ← hz, hαz, hzz]
  simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]

theorem centralizes_of_conjAut_eq_one {L : Subgroup G} (φ : ↥L ≃* M) (g : M) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) (h : conjAut L φ g hv = 1) :
    ∀ l ∈ L, v * l = l * v := by
  intro l hl
  have hβ : MulAut.congr φ (conjAct L ⟨v, hv⟩) = 1 := by
    have e : MulAut.conj g * conjAut L φ g hv * (MulAut.conj g)⁻¹ =
        MulAut.congr φ (conjAct L ⟨v, hv⟩) := by
      unfold conjAut
      group
    rw [← e, h]
    group
  have h1 : conjAct L ⟨v, hv⟩ ⟨l, hl⟩ = ⟨l, hl⟩ := by
    have := congrArg (fun γ : MulAut M => φ.symm (γ (φ ⟨l, hl⟩))) hβ
    simpa [MulAut.congr] using this
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  have h3 : v * l * v⁻¹ = l := h2
  calc v * l = (v * l * v⁻¹) * v := by group
    _ = l * v := by rw [h3]

section Field

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem odd_card_units {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) : Odd (Nat.card Kˣ) := by
  rw [Nat.card_units, hK]
  exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one

theorem exists_unit_cube_ne_one {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ c : Kˣ, c ^ 3 ≠ 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨c, fun h => ?_⟩
  have hcard : 7 ≤ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)
  omega

end Field

end CFSG.Quasithin.E9.Tr
