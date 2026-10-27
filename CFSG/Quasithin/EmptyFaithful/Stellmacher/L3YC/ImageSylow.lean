module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCSelfNorm

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace Stellmacher.L3YC

section Image

variable {G : Type} [Group G] [Finite G]

theorem card_image_sylow_eight {L S : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hα : Function.Surjective α) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    Nat.card (((S ⊓ L).subgroupOf L).map
      ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype.comp α)) = 8 := by
  classical
  let Γ := CFSG.Assembly.LowTwoRank.StatedSL 3 F
  let α' : ↥L →* Matrix.GeneralLinearGroup (Fin 3) F := Γ.subtype.comp α
  let P : Subgroup ↥L := (S ⊓ L).subgroupOf L
  let Q : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) := P.map α'
  have hP2 : IsPGroup 2 ↥P :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨m, hm⟩ := hP2.exists_card_eq
  have hQdvd : Nat.card Q ∣ 2 ^ m := hm ▸ Subgroup.card_map_dvd P α'
  have hα' : Function.Surjective α' := by
    intro g
    have hg : g ∈ Γ := by
      show g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F
      rw [Stellmacher.PU.L3YC.statedSL_eq_top_of_card_two hF]; trivial
    obtain ⟨l₀, hl₀⟩ := hα ⟨g, hg⟩
    exact ⟨l₀, by simp [α', hl₀]⟩
  have hodd : ¬ 2 ∣ Q.index := fun hd =>
    hsyl.2.2 (hd.trans (Subgroup.index_map_dvd P hα'))
  obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hQdvd
  have h168 : Nat.card Q * Q.index = 168 := by
    rw [Subgroup.card_mul_index, Stellmacher.PU.L3YC.card_gl3 hF]
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hkQ] at h168
  have hk7 : k < 8 := by
    by_contra hcon
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ k ≤ 2 ^ k * Q.index := Nat.le_mul_of_pos_right _ hpos
    omega
  show Nat.card Q = 8
  rw [hkQ]
  interval_cases k <;> omega

end Image

end Stellmacher.L3YC

end CFSG.Quasithin
