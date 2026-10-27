module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] def AutIso.toGHom (iso : AutIso M₁ M₂) : ↥Bh →* G :=
  (M₁ ⊓ M₂).subtype.comp iso.phiB.toMonoidHom

theorem AutIso.toGHom_apply (iso : AutIso M₁ M₂) (x : Bh) : iso.toGHom x = iso.toG x := rfl

theorem AutIso.toG_injective (iso : AutIso M₁ M₂) : Function.Injective iso.toG := fun _ _ h =>
  iso.phiB.injective (Subtype.ext h)

theorem AutIso.toG_one (iso : AutIso M₁ M₂) : iso.toG 1 = 1 := by
  rw [← AutIso.toGHom_apply, map_one]

@[expose] def AutIso.imgG (iso : AutIso M₁ M₂) (K : Subgroup Ah) : Subgroup G :=
  (K.subgroupOf Bh).map iso.toGHom

theorem AutIso.mem_imgG (iso : AutIso M₁ M₂) {K : Subgroup Ah} {g : G} :
    g ∈ iso.imgG K ↔ ∃ b : Bh, (b : Ah) ∈ K ∧ iso.toG b = g := by
  simp only [AutIso.imgG, Subgroup.mem_map, Subgroup.mem_subgroupOf, AutIso.toGHom_apply]

theorem AutIso.imgG_le (iso : AutIso M₁ M₂) (K : Subgroup Ah) : iso.imgG K ≤ M₁ ⊓ M₂ := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := iso.mem_imgG.1 hg
  exact iso.toG_mem b

theorem AutIso.card_imgG (iso : AutIso M₁ M₂) {K : Subgroup Ah} (hK : K ≤ Bh) :
    Nat.card (iso.imgG K) = Nat.card K := by
  have h1 : Function.Injective iso.toGHom := iso.toG_injective
  rw [AutIso.imgG, Subgroup.card_map_of_injective h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem AutIso.card_B (iso : AutIso M₁ M₂) :
    Nat.card ↥(M₁ ⊓ M₂) = 384 := by
  rw [← card_Bh]
  exact (Nat.card_congr iso.phiB.toEquiv).symm

theorem AutIso.card_M₁ (iso : AutIso M₁ M₂) :
    Nat.card ↥M₁ = 1152 := by
  rw [← card_P1h]
  exact (Nat.card_congr iso.phi1.toEquiv).symm

theorem isSylowTwoOf_imgG_That [Finite G]
    (iso : AutIso M₁ M₂) :
    IsSylowTwoOf (iso.imgG That) (M₁ ⊓ M₂) := by
  refine isSylowTwoOf_of_card_eq (iso.imgG_le That) ?_ ?_
  · exact IsPGroup.of_card (n := 7) (by rw [iso.card_imgG That_le_Bh, card_That]; norm_num)
  · have h384 : twoPart (M₁ ⊓ M₂) = 128 := by
      rw [twoPart_eq_of_card_eq (k := 7) (m := 3) (by norm_num)
        (by rw [iso.card_B]; norm_num)]
      norm_num
    rw [iso.card_imgG That_le_Bh, card_That, h384]

theorem AutIso.toG_xA
    (iso : AutIso M₁ M₂) {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzc : z ∈ centerOf (M₁ ⊓ M₂)) : iso.toG ⟨xA, That_le_Bh xA_mem_That⟩ = z := by
  set z' : ↥(M₁ ⊓ M₂) := ⟨z, hzc.1⟩ with hz'
  set zh : ↥Bh := iso.phiB.symm z' with hzh
  have hcen : ∀ b : ↥Bh, b * zh = zh * b := by
    intro b
    apply iso.phiB.injective
    rw [map_mul, map_mul, hzh, MulEquiv.apply_symm_apply]
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzc.2) _ (iso.phiB b).2)
  have hzh2 : (zh : Ah) * (zh : Ah) = 1 := by
    have : zh * zh = 1 := by
      apply iso.phiB.injective
      rw [map_mul, hzh, MulEquiv.apply_symm_apply, map_one]
      exact Subtype.ext (by simpa [pow_two] using hz2)
    exact congrArg Subtype.val this
  have hzh1 : (zh : Ah) ≠ 1 := fun h => hz1 (by
    have : zh = 1 := Subtype.ext h
    have h2 : z' = 1 := by
      have := congrArg iso.phiB this
      rwa [hzh, MulEquiv.apply_symm_apply, map_one] at this
    exact congrArg Subtype.val h2)
  have hx := central_invol_Bh zh.2 (fun b hb => congrArg Subtype.val (hcen ⟨b, hb⟩)) hzh2 hzh1
  have : zh = ⟨xA, That_le_Bh xA_mem_That⟩ := Subtype.ext hx
  rw [← this]
  show ((iso.phiB zh : ↥(M₁ ⊓ M₂)) : G) = z
  rw [hzh, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.H13.F431.U42Aut
