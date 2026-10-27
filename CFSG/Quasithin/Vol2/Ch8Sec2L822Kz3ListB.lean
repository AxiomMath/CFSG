module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCentral
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3ListNum
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.SmithC27RHat6Lin

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem modO2_quot_iso_kz3 {Gz Lz : Subgroup G} (hLzG : Lz ≤ Gz) :
    Nonempty ((↥Lz ⧸ CFSG.pCore 2 ↥Lz) ≃*
      (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz))) := by
  have hNn : (CFSG.pCore 2 ↥Gz).Normal := CFSG.pCore_normal
  let φ : ↥Lz →* (↥Gz ⧸ CFSG.pCore 2 ↥Gz) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Gz)).comp (Subgroup.inclusion hLzG)
  have hrange : φ.range = modO2Image Gz Lz := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let Θ : ↥Lz →* ↥(modO2Image Gz Lz) :=
    φ.codRestrict (modO2Image Gz Lz) (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hsurj : Function.Surjective Θ := by
    intro y
    have hy : (y : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) ∈ φ.range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have htwo : IsPGroup 2 ↥Θ.ker := by
    intro g
    have hφ : φ (g : ↥Lz) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp g.2)
    have hx' : Subgroup.inclusion hLzG (g : ↥Lz) ∈ CFSG.pCore 2 ↥Gz := by
      rw [← QuotientGroup.eq_one_iff]
      exact hφ
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Gz)) ⟨_, hx'⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Subgroup.inclusion_injective hLzG
    rw [map_pow, map_one]
    have := congrArg Subtype.val hk
    simpa using this
  exact ⟨CGT.PushingUpLit.CGT6.TwoQuot.quotPCore ⟨hsurj, htwo⟩⟩

theorem card_modO2_form_kz3 {Gz Lz : Subgroup G} (hLzG : Lz ≤ Gz)
    (hLzq : IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz) ∨
      IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6))) :
    (∃ a : ℕ, Nat.card ↥(modO2Image Gz Lz) = 2 ^ a * 360 ∨
      Nat.card ↥(modO2Image Gz Lz) = 2 ^ a * 1080) ∧
    (Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 360 ∨
      Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 1080) := by
  obtain ⟨e⟩ := modO2_quot_iso_kz3 (G := G) hLzG
  have hM : Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) =
      Nat.card (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := (Nat.card_congr e.toEquiv).symm
  have hM' : Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 360 ∨
      Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 1080 := by
    rw [hM]
    rcases hLzq with h | h
    · left
      have h6 : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
        rw [CFSG.Quasithin.H13.two_mul_card_alternatingGroup_kz3 6 (by norm_num)]
        rfl
      rw [CFSG.Quasithin.H13.card_isAlt_kz3 h]
      omega
    · right
      exact CFSG.Quasithin.SmithC27.card_of_isHat_alt6 h
  refine ⟨?_, hM'⟩
  have hpc : ∃ j : ℕ, Nat.card ↥(CFSG.pCore 2 ↥(modO2Image Gz Lz)) = 2 ^ j :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image Gz Lz))).exists_card_eq
  obtain ⟨j, hj⟩ := hpc
  have hsplit : Nat.card ↥(modO2Image Gz Lz) =
      Nat.card (↥(modO2Image Gz Lz) ⧸ CFSG.pCore 2 ↥(modO2Image Gz Lz)) *
        Nat.card ↥(CFSG.pCore 2 ↥(modO2Image Gz Lz)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  refine ⟨j, ?_⟩
  rw [hsplit, hj]
  rcases hM' with h | h
  · left
    rw [h, mul_comm]
  · right
    rw [h, mul_comm]

end CFSG.Quasithin.H13
