module

public import CFSG.Quasithin.Background.H158Fix
public import CFSG.Quasithin.Background.H158TSyl

public section

namespace CFSG.Quasithin.H158U

open CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU
  CFSG.Monster.Code CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Open CFSG.Quasithin
  CFSG.Quasithin.H

variable {V : Type} [CommGroup V]

theorem rho_injective (ρ : ↥AutPerm →* MulAut V) (e : V ≃* W11)
    (hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v)) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply rho11_injective AutPerm le_rfl
  rw [map_one]
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [← hcompat, hγ]
  rfl

theorem card_map_sylow (ρ : ↥AutPerm →* MulAut V)
    (hinj : Function.Injective ρ) (T : Subgroup ↥AutPerm) (hT : Nat.card ↥T = 2 ^ 10) :
    Nat.card ↥(T.map ρ) = 2 ^ (Nat.card ↥ρ.range).factorization 2 := by
  rw [Subgroup.card_map_of_injective hinj, hT,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, factor_AutPerm]

theorem congrHom_twist_rho (ρ : ↥AutPerm →* MulAut V) (e : V ≃* W11)
    (hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v))
    (g γ : ↥AutPerm) :
    congrHom (twistEquiv e rhoM24 g⁻¹) (ρ γ) = rho11 AutPerm le_rfl (g⁻¹ * γ * g) := by
  refine MulEquiv.ext fun w => ?_
  have h1 : (rhoM24 g⁻¹).symm w = rhoM24 g w := by
    rw [MulEquiv.symm_apply_eq, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have h3 : ∀ x : W11, congrHom e (ρ γ) x = rho11 AutPerm le_rfl γ x := fun x =>
    (congrHom_apply e (ρ γ) x).trans ((hcompat γ _).trans (congrArg _ (e.apply_symm_apply x)))
  have h4 : rho11 AutPerm le_rfl (g⁻¹ * γ * g) = rhoM24 g⁻¹ * rhoM24 γ * rhoM24 g := by
    rw [map_mul, map_mul]
  refine (congrHom_twist_apply e rhoM24 g⁻¹ (ρ γ) w).trans ?_
  rw [h1, h3, h4]
  exact ((MulAut.mul_apply W11 (rhoM24 g⁻¹ * rhoM24 γ) (rhoM24 g) w).trans
    (MulAut.mul_apply W11 (rhoM24 g⁻¹) (rhoM24 γ) (rhoM24 g w))).symm

section Generic

variable {W : Type} [CommGroup W]

theorem exists_map_eq (eg : V ≃* W) (C : Subgroup (MulAut W)) :
    ∃ X : Subgroup (MulAut V), X.map (congrHom eg) = C :=
  ⟨C.comap (congrHom eg), Subgroup.map_comap_eq_self_of_surjective (MulAut.congr eg).surjective C⟩

theorem mem_stabSub_fixV_of_twist (eg : V ≃* W) {X : Subgroup (MulAut V)} {U₀ : Subgroup W}
    (hXU : fixV (X.map (congrHom eg)) = U₀) {s : MulAut V} (hs : congrHom eg s ∈ stabSub U₀) :
    s ∈ stabSub (fixV X) := by
  have h1 : (fixV X).map eg.toMonoidHom = U₀ := by
    rw [← fixV_map_congrHom]
    exact hXU
  have h2 : congrHom eg s ∈ stabSub ((fixV X).map eg.toMonoidHom) := by
    rw [h1]
    exact hs
  rw [stabSub_map_congrHom] at h2
  exact (Subgroup.mem_map_iff_mem (congrHom_injective eg)).1 h2

theorem hb_transport [Finite V] [Finite W] (eg : V ≃* W) {H X : Subgroup (MulAut V)}
    {H₀ : Subgroup (MulAut W)} {U₀ : Subgroup W} (hH : H.map (congrHom eg) = H₀)
    (hXU : fixV (X.map (congrHom eg)) = U₀)
    (hstd : ∀ {X' : Subgroup (MulAut W)}, fixV X' = U₀ → ∀ {z' : W}, z' ≠ 1 →
      ∀ {S' : Subgroup (MulAut W)}, S' ≤ H₀ ⊓ stabSub U₀ →
        Nat.card ↥S' = 2 ^ (Nat.card ↥H₀).factorization 2 → z' ∈ fixV S' → HBConcl H₀ X' z')
    {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hSst : ∀ s ∈ S, congrHom eg s ∈ stabSub U₀)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S)
    {A : Subgroup (MulAut V)}
    (hA : ∀ φ : MulAut V, congrHom eg φ ∈ perfectCore (H₀ ⊓ stabSub U₀) → φ ∈ A) :
    vZ H z ≤ commV A := by
  have hb : HBConcl H X z :=
    hbConcl_of_equiv eg hH hXU hstd hz1
      (fun s hs => ⟨hSH hs, mem_stabSub_fixV_of_twist eg hXU (hSst s hs)⟩) hS hzS
  refine hb.1.trans (commV_le_iff.2 fun φ hφ v => mem_commV ?_ v)
  apply hA
  have hmapY : (H ⊓ stabSub (fixV X)).map (congrHom eg) = H₀ ⊓ stabSub U₀ := by
    rw [map_inf_stab_congrHom, hH, hXU]
  have h1 : congrHom eg φ ∈ (perfectCore (H ⊓ stabSub (fixV X))).map (congrHom eg) :=
    Subgroup.mem_map_of_mem _ hφ
  rwa [← perfectCore_map_congrHom, hmapY] at h1

end Generic

theorem hb_conj
    (ρ : ↥AutPerm →* MulAut V) (e : V ≃* W11)
    (hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v))
    (g : ↥AutPerm) (T : Subgroup ↥AutPerm) (hTcard : Nat.card ↥T = 2 ^ 10)
    (hTS : ∀ t ∈ T, g⁻¹ * t * g ∈ stabUT) {z : V} (hz1 : z ≠ 1)
    (hzT : ∀ t ∈ T, ρ t z = z) :
    vZ ρ.range z ≤ commV (((trQ.subgroupOf AutPerm).map (MulAut.conj g).toMonoidHom).map ρ) := by
  haveI : Finite V := Finite.of_equiv W11 e.symm.toEquiv
  have hinj : Function.Injective ρ := rho_injective ρ e hcompat
  obtain ⟨eg, heg⟩ : ∃ eg : V ≃* W11, eg = twistEquiv e rhoM24 g⁻¹ := ⟨_, rfl⟩
  have hcg : ∀ γ : ↥AutPerm, congrHom eg (ρ γ) = rho11 AutPerm le_rfl (g⁻¹ * γ * g) := by
    intro γ
    rw [heg]
    exact congrHom_twist_rho ρ e hcompat g γ
  have hH : ρ.range.map (congrHom eg) = img11 AutPerm := by
    refine (MonoidHom.map_range (congrHom eg) ρ).trans ?_
    refine Eq.trans ?_ (range_rho11_eq_img11 AutPerm le_rfl)
    ext φ
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨g⁻¹ * γ * g, (hcg γ).symm⟩
    · rintro ⟨γ, rfl⟩
      refine ⟨g * γ * g⁻¹, ?_⟩
      show congrHom eg (ρ (g * γ * g⁻¹)) = rho11 AutPerm le_rfl γ
      rw [hcg, show g⁻¹ * (g * γ * g⁻¹) * g = γ by group]
  obtain ⟨X, hXmap⟩ := exists_map_eq eg (img11 trQ ⊓ centSub UT)
  have hXU : fixV (X.map (congrHom eg)) = UT := (congrArg fixV hXmap).trans fixV_ktCent
  refine hb_transport eg hH hXU
    (fun hX' _ hz1' _ hSH' hS' hz' => hbConcl_std hX' hz1' hSH' hS' hz') hz1
    (S := T.map ρ) (Subgroup.map_le_range ρ T) ?_ (card_map_sylow ρ hinj T hTcard) ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    rw [hcg]
    exact hTS t ht
  · refine mem_fixV.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hzT t ht
  · intro φ hφ
    obtain ⟨q, hq, hqφ⟩ := (lu_coc_std card_stab_UT_le).1.le hφ
    refine ⟨g * q * g⁻¹, ⟨q, hq, rfl⟩, ?_⟩
    apply congrHom_injective eg
    show congrHom eg (ρ (g * q * g⁻¹)) = congrHom eg φ
    rw [hcg, show g⁻¹ * (g * q * g⁻¹) * g = q by group]
    exact hqφ

end CFSG.Quasithin.H158U
