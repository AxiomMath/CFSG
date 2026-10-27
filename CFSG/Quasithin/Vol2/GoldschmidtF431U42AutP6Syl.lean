module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}

theorem coe_fhB : (fhB : Ah) = fhatA := rfl

theorem card_centralizer_fhatA :
    Nat.card ↥(Subgroup.centralizer ({fhatA} : Set Ah)) = 1440 := card_centralizer_fhat

theorem twoPart_centralizer_fhatA :
    twoPart (Subgroup.centralizer ({fhatA} : Set Ah)) = 32 := by
  rw [twoPart_eq_of_card_eq (k := 5) (m := 45) (by norm_num) (by
    rw [card_centralizer_fhatA]; norm_num)]
  norm_num

omit [Finite G] in
theorem AutIso.mem_imgG_Tf
    (iso : AutIso M₁ M₂) :
    iso.imgG (That ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) =
      iso.imgG That ⊓ cenOf (iso.toG fhB) := by
  ext g
  constructor
  · intro hg
    obtain ⟨b, ⟨hbT, hbC⟩, rfl⟩ := iso.mem_imgG.1 hg
    refine ⟨iso.mem_imgG.2 ⟨b, hbT, rfl⟩, ?_⟩
    show iso.toG b ∈ Subgroup.centralizer ({iso.toG fhB} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : b * fhB = fhB * b := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hbC)
    have h2 := congrArg iso.toG this
    rwa [AutIso.toG_mul, AutIso.toG_mul] at h2
  · rintro ⟨hgT, hgC⟩
    obtain ⟨b, hbT, rfl⟩ := iso.mem_imgG.1 hgT
    refine iso.mem_imgG.2 ⟨b, ⟨hbT, ?_⟩, rfl⟩
    have hgC' := Subgroup.mem_centralizer_singleton_iff.1
      (show iso.toG b ∈ Subgroup.centralizer ({iso.toG fhB} : Set G) from hgC)
    show (b : Ah) ∈ Subgroup.centralizer ({fhatA} : Set Ah)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : b * fhB = fhB * b := by
      apply iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul]
      exact hgC'
    have h := congrArg (fun x : ↥Bh => (x : Ah)) this
    simpa only [Subgroup.coe_mul, coe_fhB] using h

omit [Finite G] in
omit [Finite G] in
theorem card_Tf
    (iso : AutIso M₁ M₂) : Nat.card ↥(iso.imgG That ⊓ cenOf (iso.toG fhB)) = 32 := by
  have hK : That ⊓ Subgroup.centralizer ({fhatA} : Set Ah) ≤ Bh := inf_le_left.trans That_le_Bh
  rw [← iso.mem_imgG_Tf, iso.card_imgG hK]
  exact card_Tf_model

@[expose] def E1Hom (iso : AutIso M₁ M₂) (F : G) : ↥(M₁ ⊓ cenOf F) →* Ah :=
  P1h.subtype.comp (iso.phi1.symm.toMonoidHom.comp (Subgroup.inclusion inf_le_left))

omit [Finite G] in
theorem E1Hom_apply (iso : AutIso M₁ M₂) (F : G) (g : ↥(M₁ ⊓ cenOf F)) :
    E1Hom iso F g = ((iso.phi1.symm ⟨(g : G), g.2.1⟩ : ↥P1h) : Ah) := rfl

omit [Finite G] in
theorem E1Hom_injective (iso : AutIso M₁ M₂) (F : G) : Function.Injective (E1Hom iso F) := by
  intro g₁ g₂ h
  rw [E1Hom_apply, E1Hom_apply] at h
  have h2 : iso.phi1.symm ⟨(g₁ : G), g₁.2.1⟩ = iso.phi1.symm ⟨(g₂ : G), g₂.2.1⟩ :=
    Subtype.ext h
  have h3 := iso.phi1.symm.injective h2
  exact Subtype.ext (Subtype.mk.inj h3)

omit [Finite G] in
theorem E1Hom_comm (iso : AutIso M₁ M₂)
    (g : ↥(M₁ ⊓ cenOf (iso.toG fhB))) : E1Hom iso (iso.toG fhB) g * fhatA =
      fhatA * E1Hom iso (iso.toG fhB) g := by
  set p : ↥P1h := iso.phi1.symm ⟨(g : G), g.2.1⟩ with hp
  have hpg : iso.toG1 p = (g : G) := by
    show ((iso.phi1 (iso.phi1.symm ⟨(g : G), g.2.1⟩) : ↥M₁) : G) = g
    rw [MulEquiv.apply_symm_apply]
  have hgc : (g : G) * iso.toG fhB = iso.toG fhB * (g : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 g.2.2
  have hcomm : p * fP1 = fP1 * p := by
    apply iso.toG1_injective
    rw [map_mul, map_mul, hpg, fP1, AutIso.toG1_inclusion]
    exact hgc
  rw [E1Hom_apply]
  have h := congrArg (fun x : ↥P1h => (x : Ah)) hcomm
  simpa only [Subgroup.coe_mul, coe_fP1] using h

omit [Finite G] in
theorem card_E1_dvd
    (iso : AutIso M₁ M₂) : Nat.card ↥(M₁ ⊓ cenOf (iso.toG fhB)) ∣ 1440 := by
  have hψ : ∀ g : ↥(M₁ ⊓ cenOf (iso.toG fhB)),
      E1Hom iso (iso.toG fhB) g ∈ Subgroup.centralizer ({fhatA} : Set Ah) := fun g =>
    Subgroup.mem_centralizer_singleton_iff.2 (E1Hom_comm iso g)
  have hinj : Function.Injective ((E1Hom iso (iso.toG fhB)).codRestrict _ hψ) := by
    intro g₁ g₂ h
    exact E1Hom_injective iso _ (congrArg (fun x : ↥(Subgroup.centralizer ({fhatA} : Set Ah)) =>
      (x : Ah)) h)
  have := Subgroup.card_dvd_of_injective _ hinj
  rwa [card_centralizer_fhatA] at this

theorem twoPart_E1
    (iso : AutIso M₁ M₂) : twoPart (M₁ ⊓ cenOf (iso.toG fhB)) ≤ 32 := by
  unfold twoPart
  rw [show (32 : ℕ) = 2 ^ (1440 : ℕ).factorization 2 by
    have := twoPart_centralizer_fhatA
    unfold twoPart at this
    rw [card_centralizer_fhatA] at this
    exact this.symm]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by norm_num)).2 (card_E1_dvd iso) 2

omit [Finite G] in
theorem Tf_le_E1
    (iso : AutIso M₁ M₂) :
    iso.imgG That ⊓ cenOf (iso.toG fhB) ≤ M₁ ⊓ cenOf (iso.toG fhB) :=
  inf_le_inf_right _ ((iso.imgG_le That).trans inf_le_left)

theorem isSylowTwoOf_Tf_E1
    (iso : AutIso M₁ M₂) :
    IsSylowTwoOf (iso.imgG That ⊓ cenOf (iso.toG fhB)) (M₁ ⊓ cenOf (iso.toG fhB)) := by
  have hp : IsPGroup 2 (iso.imgG That ⊓ cenOf (iso.toG fhB) : Subgroup G) :=
    (isSylowTwoOf_imgG_That iso).2.1.to_le inf_le_left
  refine isSylowTwoOf_of_card_eq (Tf_le_E1 iso) hp ?_
  have h1 := card_le_twoPart (Tf_le_E1 iso) hp
  have h2 := twoPart_E1 iso
  rw [card_Tf iso] at h1 ⊢
  omega

end CFSG.Quasithin.H13.F431.U42Aut
