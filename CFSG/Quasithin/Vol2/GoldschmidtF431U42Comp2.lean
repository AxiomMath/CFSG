module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique U42F431 CFSG.Quasithin.LieSetting
  CFSG.Quasithin.RankTwoAmalgam.Completion

variable {G : Type} [Group G]
  {M₁ M₂ : Subgroup G}

@[expose] def epsOf (M₁ M₂ : Subgroup G) : ↥(M₁ ⊔ M₂) →* G := (M₁ ⊔ M₂).subtype

theorem epsOf_injective : Function.Injective (epsOf M₁ M₂) := (M₁ ⊔ M₂).subtype_injective

theorem betaOf_phi1_eq
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (a : ↥A0.N1) :
    epsOf M₁ M₂ ((betaOf iso).φ1 a) = ((isoP1 iso (isoConj1.symm a) : ↥M₁) : G) := rfl

theorem betaOf_phi2_eq
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (a : ↥A0.N2) :
    epsOf M₁ M₂ ((betaOf iso).φ2 a) = ((isoP2 iso (isoConj2.symm a) : ↥M₂) : G) := rfl

theorem betaOf_phi1
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {y : Y} (hy : y ∈ P1) (hN : MulAut.conj y ∈ A0.N1) :
    epsOf M₁ M₂ ((betaOf iso).φ1 ⟨MulAut.conj y, hN⟩) = ((isoP1 iso ⟨y, hy⟩ : ↥M₁) : G) := by
  have h : isoConj1.symm ⟨MulAut.conj y, hN⟩ = ⟨y, hy⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact (isoConj1_apply hy hN).symm
  rw [betaOf_phi1_eq, h]

theorem betaOf_phi2
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {y : Y} (hy : y ∈ P2) (hN : MulAut.conj y ∈ A0.N2) :
    epsOf M₁ M₂ ((betaOf iso).φ2 ⟨MulAut.conj y, hN⟩) = ((isoP2 iso ⟨y, hy⟩ : ↥M₂) : G) := by
  have h : isoConj2.symm ⟨MulAut.conj y, hN⟩ = ⟨y, hy⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact (isoConj2_apply hy hN).symm
  rw [betaOf_phi2_eq, h]

theorem eG_mem_Mb1 {y : Y} (hy : y ∈ P1) : eG y ∈ u42Setting.Mb1 := by
  rw [Mb1_eq]
  exact ⟨y, hy, rfl⟩

theorem eG_mem_Mb2 {y : Y} (hy : y ∈ P2) : eG y ∈ u42Setting.Mb2 := by
  rw [Mb2_eq]
  exact ⟨y, hy, rfl⟩

theorem bOne_eG
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {y : Y} (hy : y ∈ P1) :
    (bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨eG y, eG_mem_Mb1 hy⟩ : G) =
      ((isoP1 iso ⟨y, hy⟩ : ↥M₁) : G) := by
  have hN : MulAut.conj y ∈ A0.N1 := by
    rw [A0_N1]
    exact ⟨y, hy, rfl⟩
  have e : (⟨eG y, eG_mem_Mb1 hy⟩ : u42Setting.Mb1) =
      ⟨f1 (c := u42Setting.ι) ⟨MulAut.conj y, hN⟩, ⟨MulAut.conj y, hN⟩, rfl⟩ :=
    Subtype.ext (Gv_injective rfl)
  rw [e]
  exact (bOne_apply u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨MulAut.conj y, hN⟩).trans
    (betaOf_phi1 iso hy hN)

theorem bTwo_eG
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {y : Y} (hy : y ∈ P2) :
    (bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨eG y, eG_mem_Mb2 hy⟩ : G) =
      ((isoP2 iso ⟨y, hy⟩ : ↥M₂) : G) := by
  have hN : MulAut.conj y ∈ A0.N2 := by
    rw [A0_N2]
    exact ⟨y, hy, rfl⟩
  have e : (⟨eG y, eG_mem_Mb2 hy⟩ : u42Setting.Mb2) =
      ⟨f2 (c := u42Setting.ι) ⟨MulAut.conj y, hN⟩, ⟨MulAut.conj y, hN⟩, rfl⟩ :=
    Subtype.ext (Gv_injective rfl)
  rw [e]
  exact (bTwo_apply u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨MulAut.conj y, hN⟩).trans
    (betaOf_phi2 iso hy hN)

theorem range_bOne
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    (bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂)).range = M₁ := by
  ext g
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    have hu' := hu
    rw [Mb1_eq] at hu'
    obtain ⟨y, hy, rfl⟩ := hu'
    rw [show (⟨eG.toMonoidHom y, hu⟩ : u42Setting.Mb1) = ⟨eG y, eG_mem_Mb1 hy⟩ from rfl]
    rw [bOne_eG iso hy]
    exact (isoP1 iso ⟨y, hy⟩).2
  · intro hg
    set y : ↥P1 := (isoP1 iso).symm ⟨g, hg⟩ with hy
    refine ⟨⟨eG (y : Y), eG_mem_Mb1 y.2⟩, ?_⟩
    rw [bOne_eG iso y.2]
    have : isoP1 iso ⟨(y : Y), y.2⟩ = ⟨g, hg⟩ := by
      rw [hy]
      exact (isoP1 iso).apply_symm_apply _
    rw [this]

theorem range_bTwo
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    (bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂)).range = M₂ := by
  ext g
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    have hu' := hu
    rw [Mb2_eq] at hu'
    obtain ⟨y, hy, rfl⟩ := hu'
    rw [show (⟨eG.toMonoidHom y, hu⟩ : u42Setting.Mb2) = ⟨eG y, eG_mem_Mb2 hy⟩ from rfl]
    rw [bTwo_eG iso hy]
    exact (isoP2 iso ⟨y, hy⟩).2
  · intro hg
    set y : ↥P2 := (isoP2 iso).symm ⟨g, hg⟩ with hy
    refine ⟨⟨eG (y : Y), eG_mem_Mb2 y.2⟩, ?_⟩
    rw [bTwo_eG iso y.2]
    have : isoP2 iso ⟨(y : Y), y.2⟩ = ⟨g, hg⟩ := by
      rw [hy]
      exact (isoP2 iso).apply_symm_apply _
    rw [this]

theorem amalgamMap_eG₁
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {y : Y} (hy : y ∈ P1) :
    amalgamMap (bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂))
      (bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂)) (eG y) =
      ((isoP1 iso ⟨y, hy⟩ : ↥M₁) : G) := by
  rw [amalgamMap_of_mem₁ _ _ (eG_mem_Mb1 hy)]
  exact bOne_eG iso hy

theorem amalgamMap_eG₂
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    (hag : ∀ g (h1 : g ∈ u42Setting.Mb1) (h2 : g ∈ u42Setting.Mb2),
      bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨g, h1⟩ =
        bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂) ⟨g, h2⟩)
    {y : Y} (hy : y ∈ P2) :
    amalgamMap (bOne u42Setting.hι (betaOf iso) (epsOf M₁ M₂))
      (bTwo u42Setting.hι (betaOf iso) (epsOf M₁ M₂)) (eG y) =
      ((isoP2 iso ⟨y, hy⟩ : ↥M₂) : G) := by
  rw [amalgamMap_of_mem₂ _ _ hag (eG_mem_Mb2 hy)]
  exact bTwo_eG iso hy

end CFSG.Quasithin.H13.F431.U42
