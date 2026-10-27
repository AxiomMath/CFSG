module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Equiv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Label

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique U42F431
  CFSG.Quasithin.LieSetting CFSG.Quasithin.H13

@[expose] def U42LocalCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G)
      (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)),
      pCoreOf 2 (M₁ ⊔ M₂) = ⊥ →
      Subgroup.centralizer ({((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G)} : Set G) ≤ M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂ →
      Subgroup.centralizer ({((isoP2 iso ⟨tY, tY_mem_P2⟩ : ↥M₂) : G)} : Set G) ≤ M₂

theorem not_isConj_of_cent {G : Type} [Group G] {M₁ M₂ : Subgroup G} {z t : G}
    (hz : Subgroup.centralizer ({z} : Set G) = M₁) (ht : Subgroup.centralizer ({t} : Set G) ≤ M₂)
    (hcard : ¬ Nat.card ↥M₁ ∣ Nat.card ↥M₂) : ¬ IsConj z t := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e : Subgroup.centralizer ({t} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    exact centralizer_map (MulAut.conj c) z
  apply hcard
  have h1 : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = Nat.card ↥M₁ := by
    rw [e, hz]
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le ht

theorem card_M1 {G : Type} [Group G]
    {M₁ M₂ : Subgroup G}
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    Nat.card ↥M₁ = 576 := by
  rw [← card_P1]
  exact (Nat.card_congr (isoP1 iso).toEquiv).symm

theorem card_M2 {G : Type} [Group G]
    {M₁ M₂ : Subgroup G}
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    Nat.card ↥M₂ = 960 := by
  rw [← card_P2]
  exact (Nat.card_congr (isoP2 iso).toEquiv).symm

theorem le_centralizer_image_x
    {G : Type} [Group G] {M₁ M₂ : Subgroup G}
    (iso : (RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)) :
    M₁ ≤ Subgroup.centralizer ({((isoP1 iso ⟨xY, xY_mem_P1⟩ : ↥M₁) : G)} : Set G) := by
  intro m hm
  rw [Subgroup.mem_centralizer_singleton_iff]
  set p : ↥P1 := (isoP1 iso).symm ⟨m, hm⟩ with hp
  have hpc : (p : Y) ∈ Subgroup.centralizer ({xY} : Set Y) := by
    rw [centralizer_x]
    exact p.2
  have h1 : (⟨xY, xY_mem_P1⟩ : ↥P1) * p = p * ⟨xY, xY_mem_P1⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hpc).symm
  have h2 := congrArg (isoP1 iso) h1
  rw [map_mul, map_mul, hp, MulEquiv.apply_symm_apply] at h2
  exact (congrArg Subtype.val h2).symm

end CFSG.Quasithin.H13.F431.U42
