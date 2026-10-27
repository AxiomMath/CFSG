module

public import CFSG.Quasithin.Background.Harris.KFact2d.F5FivePerm
public import CFSG.Quasithin.Background.Harris.KFact2d.F5FiveSL
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open Subgroup

section TwFix

variable {G : Type} [Group G] (φ : G →* G) (Z : Subgroup G)
  (hZ : ∀ g, ∀ z ∈ Z, g * z = z * g)

@[expose] def twFix : Subgroup G where
  carrier := {g | φ g * g⁻¹ ∈ Z}
  one_mem' := by
    show φ 1 * (1 : G)⁻¹ ∈ Z
    simp [Z.one_mem]
  mul_mem' := by
    intro a b ha hb
    show φ (a * b) * (a * b)⁻¹ ∈ Z
    have hb' : a * (φ b * b⁻¹) * a⁻¹ = φ b * b⁻¹ := by
      rw [hZ a _ hb]
      group
    have : φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (a * (φ b * b⁻¹) * a⁻¹) := by
      rw [map_mul]
      group
    rw [this, hb']
    exact Z.mul_mem ha hb
  inv_mem' := by
    intro a ha
    show φ a⁻¹ * (a⁻¹)⁻¹ ∈ Z
    have h1 : φ a⁻¹ * (a⁻¹)⁻¹ = (φ a * a⁻¹)⁻¹ := by
      rw [map_inv]
      have hc : a⁻¹ * (φ a * a⁻¹)⁻¹ * a = (φ a * a⁻¹)⁻¹ := by
        have h2 := hZ a _ (Z.inv_mem ha)
        rw [mul_assoc, ← h2, inv_mul_cancel_left]
      calc (φ a)⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (φ a * a⁻¹)⁻¹ * a := by group
        _ = (φ a * a⁻¹)⁻¹ := hc
    rw [h1]
    exact Z.inv_mem ha

end TwFix

section Pi

variable {G : Type} [Group G] (φ : G →* G) (Z : Subgroup G)
  (hZ : ∀ g, ∀ z ∈ Z, g * z = z * g) (hZCs : Z ≤ twFix φ Z hZ)

include hZCs

theorem twFix_map {x : G} (hx : x ∈ twFix φ Z hZ) : φ x ∈ twFix φ Z hZ := by
  have : φ x = (φ x * x⁻¹) * x := by group
  rw [this]
  exact (twFix φ Z hZ).mul_mem (hZCs hx) hx

@[expose] def twMap : G ⧸ twFix φ Z hZ → G ⧸ twFix φ Z hZ :=
  Quotient.map' φ (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact twFix_map φ Z hZ hZCs h)

theorem twMap_mk (g : G) : twMap φ Z hZ hZCs (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := rfl

theorem twMap_twMap (hφ : ∀ g, φ (φ g) = g) (ω : G ⧸ twFix φ Z hZ) :
    twMap φ Z hZ hZCs (twMap φ Z hZ hZCs ω) = ω := by
  induction ω using QuotientGroup.induction_on with
  | H g => rw [twMap_mk, twMap_mk, hφ]

@[expose] def twPerm (hφ : ∀ g, φ (φ g) = g) : Equiv.Perm (G ⧸ twFix φ Z hZ) where
  toFun := twMap φ Z hZ hZCs
  invFun := twMap φ Z hZ hZCs
  left_inv := twMap_twMap φ Z hZ hZCs hφ
  right_inv := twMap_twMap φ Z hZ hZCs hφ

theorem twPerm_smul (hφ : ∀ g, φ (φ g) = g) (g : G) (ω : G ⧸ twFix φ Z hZ) :
    twPerm φ Z hZ hZCs hφ (g • ω) = φ g • twPerm φ Z hZ hZCs hφ ω := by
  induction ω using QuotientGroup.induction_on with
  | H x =>
    show twMap φ Z hZ hZCs (QuotientGroup.mk (g * x)) = φ g • twMap φ Z hZ hZCs (QuotientGroup.mk x)
    rw [twMap_mk, twMap_mk, map_mul]
    rfl

theorem smul_eq_of_mem_Z {z : G} (hz : z ∈ Z) (ω : G ⧸ twFix φ Z hZ) : z • ω = ω := by
  induction ω using QuotientGroup.induction_on with
  | H x =>
    show (QuotientGroup.mk (z * x) : G ⧸ twFix φ Z hZ) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have h2 : (z * x)⁻¹ * x = z⁻¹ := by
      have := hZ x z hz
      calc (z * x)⁻¹ * x = (x * z)⁻¹ * x := by rw [this]
        _ = z⁻¹ := by group
    rw [h2]
    exact (twFix φ Z hZ).inv_mem (hZCs hz)

theorem twPerm_comm (hφ : ∀ g, φ (φ g) = g) {h : G} (hh : h ∈ twFix φ Z hZ)
    (ω : G ⧸ twFix φ Z hZ) :
    twPerm φ Z hZ hZCs hφ (h • ω) = h • twPerm φ Z hZ hZCs hφ ω := by
  rw [twPerm_smul]
  have hz : φ h * h⁻¹ ∈ Z := hh
  have : φ h = (φ h * h⁻¹) * h := by group
  rw [this, mul_smul, smul_eq_of_mem_Z φ Z hZ hZCs hz]

end Pi

section Main

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem keyLemma (φ : G →* G) (hφ : ∀ g, φ (φ g) = g) (ζ : G) (hζc : ∀ g, g * ζ = ζ * g)
    (hcard : Nat.card G = 240)
    (L : Subgroup G) [L.Normal] (hL : Nat.card L = 120) (eL : L ≃* SL(2, ZMod 5))
    (hφL : ∀ x ∈ L, φ x ∈ L)
    (hO2 : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → Q ≤ zpowers ζ)
    (P : Subgroup G) (hP16 : 16 ∣ Nat.card P) (hPbig : 16 < Nat.card P)
    (hζP : ζ ∈ P) (hPfix : ∀ p ∈ P, φ p * p⁻¹ ∈ zpowers ζ) :
    ∀ g, φ g * g⁻¹ ∈ zpowers ζ := by
  classical
  set Z : Subgroup G := zpowers ζ with hZdef
  have hZ : ∀ g, ∀ z ∈ Z, g * z = z * g := by
    intro g z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((show Commute g ζ from hζc g).zpow_right k).eq
  set Cs := twFix φ Z hZ with hCsdef
  have hPCs : P ≤ Cs := fun p hp => hPfix p hp
  have hζCs : ζ ∈ Cs := hPCs hζP
  have hZCs : Z ≤ Cs := (zpowers_le).mpr hζCs
  by_contra hcon
  push Not at hcon
  obtain ⟨g0, hg0⟩ := hcon
  have hCsne : Cs ≠ ⊤ := fun h => hg0 (by have : g0 ∈ Cs := h ▸ mem_top g0; exact this)
  have hc1 : 16 ∣ Nat.card Cs := dvd_trans hP16 (Subgroup.card_dvd_of_le hPCs)
  have hc2 : Nat.card Cs ∣ 240 := hcard ▸ Subgroup.card_subgroup_dvd_card Cs
  have hc3 : 16 < Nat.card Cs := lt_of_lt_of_le hPbig (Subgroup.card_le_of_le hPCs)
  have hc4 : Nat.card Cs ≠ 240 := fun h =>
    hCsne ((Subgroup.card_eq_iff_eq_top Cs).mp (h.trans hcard.symm))
  have hc : Nat.card Cs = 48 ∨ Nat.card Cs = 80 := by
    obtain ⟨k, hk⟩ := hc1
    have hle : Nat.card Cs ≤ 240 := Nat.le_of_dvd (by norm_num) hc2
    have hk15 : k < 16 := by omega
    have key : ∀ k, k < 16 → 16 * k ∣ 240 → 16 < 16 * k → 16 * k ≠ 240 →
        16 * k = 48 ∨ 16 * k = 80 := by decide
    rw [hk] at hc2 hc3 hc4 ⊢
    exact key k hk15 hc2 hc3 hc4
  have hidx : Cs.index * Nat.card Cs = 240 := hcard ▸ Subgroup.index_mul_card Cs
  have : Fintype (G ⧸ Cs) := Fintype.ofFinite _
  let ρ : G →* Equiv.Perm (G ⧸ Cs) := MulAction.toPermHom G (G ⧸ Cs)
  have hρ : ∀ g ω, ρ g ω = g • ω := fun g ω => rfl
  have hker : ρ.ker ≤ Cs := by
    intro g hg
    have h1 : g • (QuotientGroup.mk 1 : G ⧸ Cs) = QuotientGroup.mk 1 := by
      rw [← hρ]
      exact congrArg (fun f => f (QuotientGroup.mk 1)) (MonoidHom.mem_ker.mp hg)
    have h2 : (QuotientGroup.mk (g * 1) : G ⧸ Cs) = QuotientGroup.mk 1 := h1
    rw [QuotientGroup.eq] at h2
    simpa using Cs.inv_mem h2
  have hsolvL : ∀ {H : Type} [Group H] [Group.IsSolvable H] (f : L →* H), f = 1 := by
    intro H _ _ f
    have h1 := sl2_five_hom_trivial (f.comp eL.symm.toMonoidHom)
    ext x
    have := congrArg (fun g => g (eL x)) h1
    simpa using this
  let ρL : L →* Equiv.Perm (G ⧸ Cs) := ρ.comp L.subtype
  have hsign : ∀ x : L, Equiv.Perm.sign (ρL x) = 1 := fun x => by
    have := hsolvL (Equiv.Perm.sign.comp ρL)
    exact congrArg (fun g => g x) this
  rcases hc with h48 | h80
  ·
    have hidx5 : Cs.index = 5 := by rw [h48] at hidx; omega
    have hcardΩ : Fintype.card (G ⧸ Cs) = 5 := by
      rw [← Nat.card_eq_fintype_card]; exact hidx5
    have hNkCs : Nat.card ρL.ker ≤ 48 := by
      have hle : ρL.ker.map L.subtype ≤ Cs := by
        rintro _ ⟨x, hx, rfl⟩
        exact hker (by simpa [ρL] using hx)
      calc Nat.card ρL.ker = Nat.card (ρL.ker.map L.subtype) :=
            (Subgroup.card_map_of_injective L.subtype_injective).symm
        _ ≤ Nat.card Cs := Subgroup.card_le_of_le hle
        _ = 48 := h48
    have hNk2 : Nat.card ρL.ker ≤ 2 := by
      have : (ρL.ker.map eL.toMonoidHom).Normal :=
        Subgroup.Normal.map inferInstance _ eL.surjective
      have h := card_normal_sl2_five_le (ρL.ker.map eL.toMonoidHom) (by
        rw [Subgroup.card_map_of_injective eL.injective]; exact hNkCs)
      rwa [Subgroup.card_map_of_injective eL.injective] at h
    have hrange : ρL.range ≤ alternatingGroup (G ⧸ Cs) := by
      rintro _ ⟨x, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsign x
    have hcr : Nat.card ρL.ker * Nat.card ρL.range = 120 := by
      rw [← hL, ← ρL.ker.card_mul_index, Subgroup.index_ker]
    have hrange_ge : 60 ≤ Nat.card ρL.range := by
      have hpos : 0 < Nat.card ρL.ker := Nat.card_pos
      nlinarith
    have halt : Nat.card (alternatingGroup (G ⧸ Cs)) = 60 := by
      have : Nontrivial (G ⧸ Cs) := by
        rw [← Fintype.one_lt_card_iff_nontrivial, hcardΩ]; norm_num
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, hcardΩ]
      rfl
    have hrange_eq : ρL.range = alternatingGroup (G ⧸ Cs) :=
      Subgroup.eq_of_le_of_card_ge hrange (by rw [halt]; exact hrange_ge)
    have hNk : Nat.card ρL.ker = 2 := by
      rw [hrange_eq, halt] at hcr
      omega
    let π := twPerm φ Z hZ hZCs hφ
    have hπ0 : π (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
      show twMap φ Z hZ hZCs (QuotientGroup.mk 1) = _
      rw [twMap_mk, map_one]
    have hπ1 : π = 1 := by
      apply perm_eq_one_of_commute_alt hcardΩ (QuotientGroup.mk 1) π hπ0
      intro w hw hw0
      rw [← hrange_eq] at hw
      obtain ⟨⟨l, hl⟩, rfl⟩ := hw
      have hlCs : l ∈ Cs := by
        have h1 : (QuotientGroup.mk (l * 1) : G ⧸ Cs) = QuotientGroup.mk 1 := hw0
        rw [QuotientGroup.eq] at h1
        simpa using Cs.inv_mem h1
      ext ω
      show π (l • ω) = l • π ω
      exact twPerm_comm φ Z hZ hZCs hφ hlCs ω
    have hπid : ∀ ω, π ω = ω := fun ω => by rw [hπ1]; rfl
    have hρφ : ∀ g, ρ (φ g * g⁻¹) = 1 := by
      intro g
      ext ω
      have h1 := twPerm_smul φ Z hZ hZCs hφ g (g⁻¹ • ω)
      rw [hπid, hπid] at h1
      rw [Equiv.Perm.one_apply, map_mul, Equiv.Perm.mul_apply]
      show φ g • (g⁻¹ • ω) = ω
      rw [← h1, smul_inv_smul]
    have hM0 : ρL.ker.map L.subtype = ρ.ker ⊓ L := by
      ext x
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf, Subgroup.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, y.2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hx2⟩, hx1, rfl⟩
    have hM0card : Nat.card (ρ.ker ⊓ L : Subgroup G) = 2 ^ 1 := by
      rw [← hM0, Subgroup.card_map_of_injective L.subtype_injective, hNk]
      rfl
    have hM0Z : (ρ.ker ⊓ L : Subgroup G) ≤ Z :=
      hO2 _ inferInstance (IsPGroup.of_card hM0card)
    have hLCs : L ≤ Cs := fun x hx =>
      hM0Z ⟨hρφ x, L.mul_mem (hφL x hx) (L.inv_mem hx)⟩
    have := Subgroup.card_dvd_of_le hLCs
    rw [hL, h48] at this
    omega
  ·
    have hidx3 : Cs.index = 3 := by rw [h80] at hidx; omega
    have hsolv : Group.IsSolvable (Equiv.Perm (G ⧸ Cs)) :=
      Equiv.Perm.isSolvable (by
        show Cs.index ≤ 4
        omega)
    have h1 := hsolvL ρL
    have hLCs : L ≤ Cs := fun l hl => hker (by
      have := congrArg (fun f => f ⟨l, hl⟩) h1
      simpa [ρL] using this)
    have := Subgroup.card_dvd_of_le hLCs
    rw [hL, h80] at this
    omega

end Main

end CFSG.Quasithin.Background.Harris.KFact2d
