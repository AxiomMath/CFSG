module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cox3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Q2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Q3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Fin

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem exists_A6
    (h : F55Ctx c R) :
    ∃ Q : Subgroup ↥(cenOf (c.iso.toG fhB)),
      Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)} ∧
      Nat.card ↥(cenOf (c.iso.toG fhB)) = 2880 ∧ Nonempty (↥Q ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨ρ, hρ, hρ2⟩ := exists_rho c h
  obtain ⟨Q, hQn, hQi, hQR, hQc⟩ := exists_Q c h (⟨hρ, hρ2⟩ : RhoCtx c R ρ)
  have := hQn
  rcases Q_recog c h hQi hQR hQc with he | he
  · obtain ⟨e⟩ := he
    exact (Q_not_L32 c h hQi hQc e).elim
  · obtain ⟨e⟩ := he
    refine ⟨Q, hQc, ?_, ⟨e⟩⟩
    have h360 : Nat.card ↥Q = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have := Subgroup.card_mul_index Q
    rw [h360, hQi] at this
    omega

theorem card_M0_cen (ι : Ah ≃* ↥(M₁ ⊔ M₂))
    (h1 : ∀ x : P1h, (ι (x : Ah) : G) = (c.iso.phi1 x : G)) :
    Nat.card ↥((M₁ ⊔ M₂) ⊓ cenOf (c.iso.toG fhB)) = 1440 := by
  have hιf : (ι fhatA : G) = c.iso.toG fhB := (h1 fP1).trans (toG1_fP1 c)
  have hK : (Subgroup.centralizer ({fhatA} : Set Ah)).map (ι : Ah →* ↥(M₁ ⊔ M₂)) =
      ((M₁ ⊔ M₂) ⊓ cenOf (c.iso.toG fhB)).subgroupOf (M₁ ⊔ M₂) := by
    ext y
    obtain ⟨a, rfl⟩ := ι.surjective y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, cenOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨b, hb, hba⟩
      have hb' : b = a := ι.injective hba
      subst hb'
      refine ⟨(ι b).2, ?_⟩
      have := congrArg (fun w : Ah => (ι w : G))
        (Subgroup.mem_centralizer_singleton_iff.1 hb)
      simpa [hιf] using this
    · rintro ⟨-, hy⟩
      refine ⟨a, Subgroup.mem_centralizer_singleton_iff.2 (ι.injective (Subtype.ext ?_)), rfl⟩
      simpa [hιf] using hy
  have hinj : Function.Injective (ι : Ah →* ↥(M₁ ⊔ M₂)) := ι.injective
  have hcard := Subgroup.card_map_of_injective (K := Subgroup.centralizer ({fhatA} : Set Ah)) hinj
  rw [hK, show Nat.card ↥(Subgroup.centralizer ({fhatA} : Set Ah)) = 1440 from
    card_centralizer_fhatA] at hcard
  rw [← hcard]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem conf55_std
    (hι : U42AutIotaOfCox) (h : F55Ctx c R) : Conf55 c (c.iso.toG fhB) := by
  obtain ⟨Q, hQc, hX, ⟨e⟩⟩ := exists_A6 c h
  obtain ⟨ι, h1, h2⟩ := hι G M₁ M₂ z c cxSP cxTP isCoxPair_st (coxRel_of_A6 c h hQc e)
  exact ⟨hX, card_M0_cen c ι h1, ι, h1, h2⟩

end Fin

end CFSG.Quasithin.H13.F431.U42Aut
