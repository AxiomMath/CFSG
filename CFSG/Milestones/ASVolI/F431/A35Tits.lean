module

public import CFSG.Milestones.ASVolI.F431.A35LieI
public import CFSG.Milestones.ASVolI.F431.A35D4
public import CFSG.Milestones.ASVolI.F45.TitsModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDZid
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDClause
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal
import CFSG.Milestones.ASVolI.F4
import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.Done
public import CFSG.Milestones.ASVolI.F431.L39Final
public import CFSG.Milestones.ASVolI.F431.L40
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Std
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Sporadic.Schreier.Tits

@[expose] def burnsideF4m_A35Rest''' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

section Tits

set_option linter.unusedSectionVars false


theorem burnsideF4m_tits_thetaD {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 f Gp M₁ M₂) :
    ∃ θ : E ≃* ↥titsD, (∀ e, θ e ∈ titsHD ↔ e ∈ M₁) ∧ (∀ e, θ e ∈ titsND ↔ e ∈ M₂) := by
  obtain ⟨-, hf1, -⟩ := hyp.model
  subst hf1
  obtain ⟨θ0, hθ1, hθ2⟩ := burnsideF45_tits_theta hyp
  have hgen : M₁ ⊔ M₂ = ⊤ := hyp.gen
  let θ : E ≃* ↥titsD := ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen.symm)).trans
    θ0).trans (MulEquiv.subgroupCongr titsH_sup_N)
  have hmem : ∀ e : E, e ∈ M₁ ⊔ M₂ := fun e => by
    rw [hgen]
    exact Subgroup.mem_top e
  have hcoe : ∀ e : E, ((θ e : ↥titsD) : Equiv.Perm (Fin 1755)) =
      ((θ0 ⟨e, hmem e⟩ : ↥(titsH ⊔ titsN)) : Equiv.Perm (Fin 1755)) := fun e => rfl
  refine ⟨θ, fun e => ?_, fun e => ?_⟩
  · rw [Subgroup.mem_subgroupOf, hcoe]
    exact (hθ1 _).symm
  · rw [Subgroup.mem_subgroupOf, hcoe]
    exact (hθ2 _).symm

theorem burnsideF4m_F_4_35_Tits {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .Tits f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hi1 : i ≠ 1) (hj1 : j ≠ 1) (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.amalgam.finite
  have hGp : Gp = ⊤ := hyp.amalgam.canonical (Or.inr rfl)
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_tits_thetaD hyp.amalgam
  have hz := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
  have hbinj := burnsideF4j_bOne_injective hyp
  have hx2 : x * x = 1 := by
    have : burnsideF4d_bOne β ε (⟨x, hx1⟩ * ⟨x, hx1⟩) = burnsideF4d_bOne β ε 1 := by
      rw [map_mul, hxz, map_one]
      exact hyp.z_inv.2
    exact congrArg Subtype.val (hbinj this)
  have hxne : x ≠ 1 := by
    intro h
    apply hyp.z_inv.1
    rw [← hxz]
    have e : (⟨x, hx1⟩ : ↥M₁) = 1 := Subtype.ext h
    rw [e, map_one]
  have hmap : (Gp ⊓ M₁).map θ.toMonoidHom = titsHD := by
    ext y
    constructor
    · rintro ⟨m, ⟨-, hm⟩, rfl⟩
      exact (h1 m).2 hm
    · intro hy
      refine ⟨θ.symm y, ⟨by rw [hGp]; exact Subgroup.mem_top _,
        (h1 _).1 (by rwa [MulEquiv.apply_symm_apply])⟩, ?_⟩
      exact θ.apply_symm_apply y
  have hO : ∀ m ∈ M₁, m ∈ oPPrime 2 (Gp ⊓ M₁) := by
    intro m hm
    have h := burnsideF4d_oPPrime_map θ.toMonoidHom θ.injective 2 (Gp ⊓ M₁)
    rw [hmap, burnsideF4gF4TwoInv_titsD_oPPrime] at h
    have hθm : θ m ∈ titsHD := (h1 m).2 hm
    rw [h] at hθm
    obtain ⟨m', hm', he⟩ := hθm
    have he' : θ m' = θ m := he
    rw [θ.injective he'] at hm'
    exact hm'
  have hcent : ∀ m ∈ M₁, m * x = x * m := fun m hm =>
    (Subgroup.mem_centralizer_iff.mp hxZ.2) m (hO m hm)
  have hθx : θ x = CFSG.Quasithin.H13.F431.TitsD.zD := by
    apply Subtype.ext
    have hxH : ((θ x : ↥titsD) : Equiv.Perm (Fin 1755)) ∈ titsH := (h1 x).2 hx1
    refine CFSG.Quasithin.H13.F431.TitsD.eq_titsZ_of_central hxH ?_ ?_ ?_
    · intro y hy
      have hyD : y ∈ titsD := titsH_le_titsD hy
      have hyHD : (⟨y, hyD⟩ : ↥titsD) ∈ titsHD := hy
      have hm : θ.symm ⟨y, hyD⟩ ∈ M₁ := (h1 _).1 (by rwa [MulEquiv.apply_symm_apply])
      have hc := congrArg θ (hcent _ hm)
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at hc
      exact congrArg Subtype.val hc
    · have h := congrArg θ hx2
      rw [map_mul, map_one] at h
      exact congrArg Subtype.val h
    · intro h
      apply hxne
      apply θ.injective
      rw [map_one]
      exact Subtype.ext h
  have hnc := burnsideF4m_lieI_hnc hyp θ h1 h2 CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI hx1
    hθx hxz (r := 3) (by rw [card_titsHD]; decide)
    CFSG.Quasithin.H13.F431.TitsD.three_dvd_card_cent_tD
  exact burnsideF4m_F_4_35_of_lieI hyp (by decide) (by decide) θ h1 h2
    CFSG.Quasithin.H13.F431.TitsD.titsD_F431LieI hnc i j hi hj hi1 hi2 hj1 hj2

theorem burnsideF4m_A35Rest''_of''' (hrest : burnsideF4m_A35Rest''') : burnsideF4m_A35Rest'' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hk i j hi hj hi1 hj1 hi2 hj2
  rcases hk with hk | hk | rfl | hk | hk
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inl hk) i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inl hk)) i j hi hj hi1 hj1 hi2 hj2
  · exact burnsideF4m_F_4_35_Tits hyp i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inl hk))) i j hi hj hi1 hj1 hi2
      hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr hk))) i j hi hj hi1 hj1 hi2
      hj2

end Tits

end CFSG.ASVolI
