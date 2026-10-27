module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixSplitFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
public import CFSG.RankThree.PartOne.KF.ClsOmega

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13.VolI CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open Matrix

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_omegaMinus_six_natural_coordinates_aux
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] {b d : K}
    (hK : Nat.card K = 2 ^ a)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hR : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
      (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥) :
    ∃ (e : Vtil V₀ V hV ≃* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))
      (ρ : ↥(D.M) →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))),
      (∀ a : ↥(D.M), ρ a = MulAut.congr e (barHom V₀ V hV c.m_le_stabTil a)) ∧
      (StatedOmega (StatedQuadMinus 3 K b d)).map
        (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ≤ ρ.range ∧
      ρ.range ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d)) ∧
      (∀ x : Mbar D.M V₀ V hV,
        MulAut.congr e x ∈ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d))) ∧
      IsOmegaMinus ↥(lBar V₀ V hV L) 6 a := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let W := Vtil V₀ V hV
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 3 K b d)
  have hwt : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hR' : (FFModel.nat Γ).Realizes H ⊤ (⊥ : Subgroup W) := by
    have h := hR
    rw [hwt] at h
    exact h
  obtain ⟨π, β, hπs, hβs, hβk, hβe⟩ :=
    topBot_data (D := FFModel.nat Γ) rfl rfl hR'
  have hβ_inj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : u * v⁻¹ ∈ (⊥ : Subgroup W) := (hβk (u * v⁻¹)).1 h1
    have h3 : u * v⁻¹ = 1 := Subgroup.mem_bot.1 h2
    exact mul_inv_eq_one.1 h3
  let e : W ≃* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K) :=
    MulEquiv.ofBijective (β : W →* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))
      ⟨hβ_inj, hβs⟩
  have hGamEq : (FFModel.nat Γ).Gam = ↥Γ := rfl
  let castGam : ↥Γ →* (FFModel.nat Γ).Gam :=
    { toFun := fun x => hGamEq.symm ▸ x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let πs : ↥Γ →* ↥H := π.comp castGam
  have hπs_s : Function.Surjective πs := by
    intro h
    obtain ⟨g, hg⟩ := hπs h
    refine ⟨hGamEq ▸ g, ?_⟩
    show π (castGam (hGamEq ▸ g)) = h
    rw [show castGam (hGamEq ▸ g) = g from rfl, hg]
  have hβe' : ∀ (γ : ↥Γ) (w : W),
      β (((πs γ : ↥H) : MulAut W) w) =
        s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) (β w) := by
    intro γ w
    have h : β (((π (castGam γ) : ↥H) : MulAut W) w) =
        (FFModel.nat Γ).act (castGam γ) (β w) := hβe (castGam γ) w
    have h2 : s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K
          (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) (β w) =
        (FFModel.nat Γ).act (castGam γ) (β w) :=
      s16gNatHom_eq_natAct Γ γ (β w)
    rw [h2]
    exact h
  have heπ : ∀ (γ : ↥Γ) (w : W),
      e (((πs γ : ↥H) : MulAut W) w) =
        s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) (e w) := by
    intro γ w
    change β (((πs γ : ↥H) : MulAut W) w) =
      s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) (β w)
    exact hβe' γ w
  have hπs_inj : Function.Injective πs := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply Subtype.ext
    apply s16gNatHom_injective
    change (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K
        (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)) =
      (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (1 : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K))
    rw [map_one]
    apply MulEquiv.ext
    intro x
    obtain ⟨w, rfl⟩ := hβs x
    have hEW : e w = β w := rfl
    have h := heπ γ w
    rw [hEW] at h
    rw [hγ] at h
    simp only [OneMemClass.coe_one, MulAut.one_apply] at h
    rw [← h, hEW]
    rfl
  have hcongr_apply : ∀ (γ : ↥Γ) (w : W),
      (MulAut.congr e ((πs γ : ↥H) : MulAut W)) (e w) =
        s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) (e w) := by
    intro γ w
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact heπ γ w
  have hcongr_π : ∀ γ : ↥Γ,
      MulAut.congr e ((πs γ : ↥H) : MulAut W) =
        s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) := by
    intro γ
    apply MulEquiv.ext
    intro x
    obtain ⟨w, rfl⟩ := hβs x
    have h := hcongr_apply γ w
    rw [show e w = β w from rfl] at h
    exact h
  have hrange : (barHom V₀ V hV c.m_le_stabTil).range = Mbar D.M V₀ V hV :=
    range_barHom V₀ V hV c.m_le_stabTil
  have hH_le_Mbar : H ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hnat_mem : ∀ γ : ↥Γ, ∃ m : ↥D.M,
      barHom V₀ V hV c.m_le_stabTil m =
        (⟨πs γ, hH_le_Mbar (πs γ).2⟩ : Mbar D.M V₀ V hV) ∧
      MulAut.congr e (barHom V₀ V hV c.m_le_stabTil m) =
        s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) := by
    intro γ
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (by
      rw [hrange]
      exact hH_le_Mbar (πs γ).2)
    exact ⟨m, hm, by rw [hm]; exact hcongr_π γ⟩
  let ρ : ↥D.M →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K)) :=
    (MulAut.congr e).toMonoidHom.comp (barHom V₀ V hV c.m_le_stabTil)
  have hρ_apply : ∀ a : ↥D.M,
      ρ a = MulAut.congr e (barHom V₀ V hV c.m_le_stabTil a) := fun _ => rfl
  have himg : Γ.map (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ≤ ρ.range := by
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨m, -, hm⟩ := hnat_mem ⟨γ, hγ⟩
    exact ⟨m, by rw [hρ_apply]; exact hm⟩
  have hforward : ∀ a : ↥D.M, ∀ y ∈ Γ.map (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K),
      ρ a * y * (ρ a)⁻¹ ∈ Γ.map (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) := by
    intro a y hy
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨m, hbar, hρm⟩ := hnat_mem ⟨γ, hγ⟩
    have hbara : barHom V₀ V hV c.m_le_stabTil a ∈ Mbar D.M V₀ V hV := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have hbarH : barHom V₀ V hV c.m_le_stabTil m ∈ H := by
      rw [hbar]
      exact (πs ⟨γ, hγ⟩).2
    have hconjH : barHom V₀ V hV c.m_le_stabTil a *
        barHom V₀ V hV c.m_le_stabTil m *
        (barHom V₀ V hV c.m_le_stabTil a)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (s15_Three_le_normalizer hs hbara) _).1 hbarH
    have hconjH' : barHom V₀ V hV c.m_le_stabTil (a * m * a⁻¹) ∈ H := by
      rw [map_mul, map_mul, map_inv]
      exact hconjH
    have heq : ρ a * s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K
          (γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) * (ρ a)⁻¹ =
        ρ (a * m * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rw [hρ_apply m, hρm]
    rw [heq]
    obtain ⟨γ₀, hγ₀⟩ := hπs_s ⟨barHom V₀ V hV c.m_le_stabTil (a * m * a⁻¹), hconjH'⟩
    refine ⟨γ₀.1, γ₀.2, ?_⟩
    rw [hρ_apply]
    have hγ₀' : ((πs γ₀ : ↥H) : MulAut W) =
        barHom V₀ V hV c.m_le_stabTil (a * m * a⁻¹) := by
      rw [hγ₀]
    rw [← hγ₀']
    exact (hcongr_π γ₀).symm
  have hρN : ρ.range ≤ s16gNorm Γ := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    rw [s16gNorm, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward a y
    · intro hy
      have h := hforward a⁻¹ (ρ a * y * (ρ a)⁻¹) hy
      rw [map_inv] at h
      convert h using 1
      group
  have hcongrN : ∀ x : Mbar D.M V₀ V hV,
      MulAut.congr e x ∈ s16gNorm Γ := by
    intro x
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (by
      rw [hrange]
      exact x.2)
    rw [← hm, ← hρ_apply m]
    exact hρN ⟨m, rfl⟩
  have hchar : CharP K 2 := s16k_charP_two_of_card ha hK
  let := hchar
  have hbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b d)) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.statedScalars_subgroupOf_statedOmega_quadMinus_three_eq_bot
      (K := K) b d
  let ε : ↥H ≃* ↥Γ := (MulEquiv.ofBijective πs ⟨hπs_inj, hπs_s⟩).symm
  have hshape : IsOmegaMinus ↥H 6 a :=
    ⟨⟨3, rfl⟩, K, inferInstance, inferInstance, b, d, hK, hirr,
      ⟨ε.trans (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot Γ hbot)⟩⟩
  exact ⟨e, ρ, hρ_apply, himg, hρN, hcongrN, hshape⟩

private theorem s168e3_omegaMinus_six_natural_coordinates
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {a : ℕ} (ha : 1 ≤ a)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b d : K)
      (_ : Nat.card K = 2 ^ a) (_ : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
      (e : Vtil V₀ V hV ≃* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))
      (ρ : ↥(D.M) →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))),
      (∀ a : ↥(D.M), ρ a = MulAut.congr e (barHom V₀ V hV c.m_le_stabTil a)) ∧
      (StatedOmega (StatedQuadMinus 3 K b d)).map
        (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ≤ ρ.range ∧
      ρ.range ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d)) ∧
      (∀ x : Mbar D.M V₀ V hV,
        MulAut.congr e x ∈ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d))) ∧
      IsOmegaMinus ↥(lBar V₀ V hV L) 6 a := by
  obtain ⟨-, K, hF, hFin, b, d, hK, hirr, hR⟩ := hN
  let := hF
  let := hFin
  have hR' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
      (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ := by
    simpa only [show 6 / 2 = 3 by norm_num] using hR
  obtain ⟨e, ρ, hρ, himg, hρN, hcongrN, hshape⟩ :=
    s168e3_omegaMinus_six_natural_coordinates_aux c hs ha hK hirr hR'
  exact ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, hcongrN, hshape⟩

private theorem s168e3_pow_two_dvd_orthogonalGroup_quadMinus_three
    {K : Type} [Field K] [Finite K] [CharP K 2] {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    {e : Vtil V₀ V hV ≃* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K)}
    (hcongrN : ∀ x : Mbar D.M V₀ V hV,
      MulAut.congr e x ∈ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d)))
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hpσ : p ∈ D.sig)
    (hpAut : ¬ p ∣ Nat.card (RingAut K)) (hUnits : ¬ p ∣ Nat.card Kˣ) :
    p ^ 2 ∣ Nat.card
      (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) := by
  classical
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 3 K b d)
  have hp : p.Prime := (D.sig_prime p hpσ).1
  obtain ⟨E₀, hE₀el, hE₀card⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := Mbar D.M V₀ V hV) hp
      (c.two_le_pRank_mbar hpσ)
  let E : Subgroup (MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))) :=
    E₀.map ((MulAut.congr e).toMonoidHom.comp (Mbar D.M V₀ V hV).subtype)
  have hEel : IsElemAbelian p E := hE₀el.map _
  have hEcard : Nat.card E = p ^ 2 := by
    have hinj : Function.Injective
        ((MulAut.congr e).toMonoidHom.comp (Mbar D.M V₀ V hV).subtype) := by
      intro x y hxy
      exact (Mbar D.M V₀ V hV).subtype_injective ((MulAut.congr e).injective hxy)
    rw [Subgroup.card_map_of_injective hinj, hE₀card]
  have hEN : E ≤ s16gNorm Γ := by
    rintro _ ⟨x, -, rfl⟩
    exact hcongrN x
  have hΓ : AddCommutantScalar Γ :=
    addCommutantScalar_statedOmegaMinus (m := 3) (by norm_num) hirr
  have hEL : E ≤ s16gLin (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    s16g_le_lin_of_coprime hΓ hp hpAut hEN hEel.isPGroup
  obtain ⟨F, hFN, hFel, hFcard⟩ := s16g_exists_matrix_elem_of_lin hEN hEL hEel
  obtain ⟨μ, hμ⟩ :=
    s16g_exists_mult_omegaMinus (m := 3) (b := b) (c := d) (by norm_num) hirr
  have hμF : ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K))),
      (x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ∈ F → μ x = 1 :=
    s16g_mu_eq_one_of_coprime μ hFN hp hFel.isPGroup hUnits
  have hFQ : ∀ x ∈ F, ∀ v : (Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K,
      StatedQuadMinus 3 K b d
          ((x : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        StatedQuadMinus 3 K b d v := by
    intro x hx v
    exact hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) := inferInstance
  have hle : F.map (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d) := by
    rintro _ ⟨x, hx, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, coe_quadMinus]
    exact hFQ x hx v
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K).injective] at hdvd
  rw [hFcard, hEcard] at hdvd
  exact hdvd

private theorem s168e3_sigma_four_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 2 ^ 13 * 3 ^ 2 * 5 ^ 3 * 13 * 17) : p = 3 ∨ p = 5 := by
  have hpN : p ∣ 2 ^ 13 * 3 ^ 2 * 5 ^ 3 * 13 * 17 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 ∨ p = 17 := by
    rcases hp.dvd_mul.mp hpN with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
              (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
            (hp.dvd_of_dvd_pow h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · exact Or.inr rfl
  · norm_num at h
  · norm_num at h

private theorem s168e3_sigma_eight_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 2 ^ 19 * 3 ^ 7 * 5 * 7 ^ 2 * 13 * 19) : p = 3 ∨ p = 7 := by
  have hpN : p ∣ 2 ^ 19 * 3 ^ 7 * 5 * 7 ^ 2 * 13 * 19 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 := by
    rcases hp.dvd_mul.mp hpN with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
                (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
                (hp.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
              (hp.dvd_of_dvd_pow h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).mp h)))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · norm_num at h
  · exact Or.inr rfl
  · norm_num at h
  · norm_num at h

theorem s168e3_sigma_eq_three_or_five_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    {p : ℕ} (hpσ : p ∈ D.sig) : p = 3 ∨ p = 5 := by
  obtain ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, hcongrN, hshape⟩ :=
    s168e3_omegaMinus_six_natural_coordinates c hs (by norm_num) hN
  let := hF
  let := hFin
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 2) (by norm_num) hK
  let := hchar
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hpq : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hpq
    have hpAut : ¬ p ∣ Nat.card (RingAut K) := by
      rw [s16k_card_ringAut_of_card hK]
      intro h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hUnits : ¬ p ∣ Nat.card Kˣ := by
      rw [s16k_card_units_of_card hK]
      intro h3
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h3)
      exact hpq (by rw [hp3, hK]; norm_num)
    have hdvd := s168e3_pow_two_dvd_orthogonalGroup_quadMinus_three hirr hcongrN c hpσ
      hpAut hUnits
    have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 2
    have hO' : (Nat.card
          (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) : ℤ) =
        2 * 4 ^ 6 * (4 ^ 3 + 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) := by
      simpa [hK4, Finset.prod_Icc_succ_top] using hO
    have hdvdZ : (p : ℤ) ^ 2 ∣
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) : ℤ) := by
      exact_mod_cast hdvd
    rw [hO'] at hdvdZ
    norm_num at hdvdZ
    have hdvdN : p ^ 2 ∣ 2 ^ 13 * 3 ^ 2 * 5 ^ 3 * 13 * 17 := by
      norm_num
      exact_mod_cast hdvdZ
    rcases s168e3_sigma_four_arithmetic hp hp2 hdvdN with rfl | rfl
    · exact hpq (by rw [hK]; norm_num)
    · exact hpq (by rw [hK]; norm_num)
  have hpq15 : p ∣ 3 * 5 := by
    have hpq' : p ∣ 4 ^ 2 - 1 := by simpa [hK4] using hpq
    norm_num at hpq'
    exact hpq'
  rcases hp.dvd_mul.mp hpq15 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)

theorem s168e3_sigma_eq_three_or_seven_of_omegaMinus_six_eight_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 3)
    {p : ℕ} (hpσ : p ∈ D.sig) : p = 3 ∨ p = 7 := by
  obtain ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, hcongrN, hshape⟩ :=
    s168e3_omegaMinus_six_natural_coordinates c hs (by norm_num) hN
  let := hF
  let := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 3) (by norm_num) hK
  let := hchar
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hpq : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hpq
    have hpAut : ¬ p ∣ Nat.card (RingAut K) := by
      rw [s16k_card_ringAut_of_card hK]
      intro h3
      have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h3)
      exact hpq (by rw [hp3, hK]; norm_num)
    have hUnits : ¬ p ∣ Nat.card Kˣ := by
      rw [s16k_card_units_of_card hK]
      intro h7
      have hp7 : p = 7 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp (by simpa using h7)
      exact hpq (by rw [hp7, hK]; norm_num)
    have hdvd := s168e3_pow_two_dvd_orthogonalGroup_quadMinus_three hirr hcongrN c hpσ
      hpAut hUnits
    have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 2
    have hO' : (Nat.card
          (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) : ℤ) =
        2 * 8 ^ 6 * (8 ^ 3 + 1) * (8 ^ 2 - 1) * (8 ^ 4 - 1) := by
      simpa [hK8, Finset.prod_Icc_succ_top] using hO
    have hdvdZ : (p : ℤ) ^ 2 ∣
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b d)) : ℤ) := by
      exact_mod_cast hdvd
    rw [hO'] at hdvdZ
    norm_num at hdvdZ
    have hdvdN : p ^ 2 ∣ 2 ^ 19 * 3 ^ 7 * 5 * 7 ^ 2 * 13 * 19 := by
      norm_num
      exact_mod_cast hdvdZ
    rcases s168e3_sigma_eight_arithmetic hp hp2 hdvdN with rfl | rfl
    · exact hpq (by rw [hK]; norm_num)
    · exact hpq (by rw [hK]; norm_num)
  have hpq63 : p ∣ 3 ^ 2 * 7 := by
    have hpq' : p ∣ 8 ^ 2 - 1 := by simpa [hK8] using hpq
    norm_num at hpq'
    exact hpq'
  rcases hp.dvd_mul.mp hpq63 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h)


private theorem s168e3_false_of_split_prime_omegaMinus_six
    (c : S168e3Ctx D V₀ V L hV)
    {K : Type} [Field K] [Finite K] [CharP K 2] {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    {e : Vtil V₀ V hV ≃* Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K)}
    {ρ : ↥(D.M) →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2 ⊕ Fin 2) → K))}
    (hρ : ∀ a : ↥(D.M), ρ a = MulAut.congr e (barHom V₀ V hV c.m_le_stabTil a))
    (himg : (StatedOmega (StatedQuadMinus 3 K b d)).map
      (s16gNatHom (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) ≤ ρ.range)
    (hρN : ρ.range ≤ s16gNorm (StatedOmega (StatedQuadMinus 3 K b d)))
    {p : ℕ} (hpσ : p ∈ D.sig) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hpAut : ¬ p ∣ Nat.card (RingAut K)) : False := by
  have hrank : CFSG.Open.pRank p D.M = 3 := c.std.pRank_eq_three hpσ
  obtain ⟨E, hE, hEcard⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := D.M) hp (by rw [hrank])
  have hfix := s16g_actual_fixers_of_elem_cube_split_omegaMinus_six
    (X := ↥D.M) (K := K) hirr hp hp2 hpK hpAut ρ himg hρN E hE hEcard
  refine s168e3_false_of_fix_M c hp hpσ fun y hy => ?_
  have hy' : e y ≠ 1 := by
    intro h
    exact hy (e.injective (by rw [h, map_one]))
  obtain ⟨B, hBp, hBnc, hBfix⟩ := hfix (e y) hy'
  refine ⟨B, hBp, hBnc, fun b hb => ?_⟩
  have h1 : e (barHom V₀ V hV c.m_le_stabTil b y) = e y := by
    have h2 := hBfix b hb
    rw [hρ b] at h2
    have h3 : (MulAut.congr e (barHom V₀ V hV c.m_le_stabTil b)) (e y) =
        e (barHom V₀ V hV c.m_le_stabTil b y) := by
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rwa [h3] at h2
  exact e.injective h1

theorem s168e3_seven_not_mem_sig_of_omegaMinus_six_eight_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 3) :
    7 ∉ D.sig := by
  intro h7
  obtain ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, -, -⟩ :=
    s168e3_omegaMinus_six_natural_coordinates c hs (by norm_num) hN
  let := hF
  let := hFin
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 3) (by norm_num) hK
  let := hchar
  have hp : Nat.Prime 7 := by norm_num
  have hp2 : 7 ≠ 2 := by norm_num
  have hpK : 7 ∣ Nat.card K - 1 := by rw [hK8]
  have hpAut : ¬ 7 ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card hK]
    norm_num
  exact s168e3_false_of_split_prime_omegaMinus_six c hirr hρ himg hρN h7 hp hp2 hpK hpAut

private theorem s168e3_three_not_mem_sig_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2) :
    3 ∉ D.sig := by
  intro h3
  obtain ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, -, -⟩ :=
    s168e3_omegaMinus_six_natural_coordinates c hs (by norm_num) hN
  let := hF
  let := hFin
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 2) (by norm_num) hK
  let := hchar
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hK4]
  have hpAut : ¬ 3 ∣ Nat.card (RingAut K) := by
    rw [s16k_card_ringAut_of_card hK]
    norm_num
  exact s168e3_false_of_split_prime_omegaMinus_six c hirr hρ himg hρN h3 hp hp2 hpK hpAut

theorem s168e3_case163_6_of_omegaMinus_six_eight_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 3) :
    Case163_6 D V₀ V hV L := by
  obtain ⟨K, hF, hFin, b, d, hK, hirr, e, ρ, hρ, himg, hρN, hcongrN, hshape⟩ :=
    s168e3_omegaMinus_six_natural_coordinates c hs (by norm_num) hN
  have h7 : 7 ∉ D.sig :=
    s168e3_seven_not_mem_sig_of_omegaMinus_six_eight_natural c hs hN
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have h3 : 3 ∈ D.sig := by
    rcases s168e3_sigma_eq_three_or_seven_of_omegaMinus_six_eight_natural c hs hN hpσ with
      h | h
    · exact h ▸ hpσ
    · exact absurd (h ▸ hpσ) h7
  exact ⟨hshape, hN, hs, c.std.sig_eq_three_of_mem h3, c.std.pRank_eq_three h3⟩

theorem s168e3_sig_eq_five_of_omegaMinus_six_four_natural
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2) :
    D.sig = {5} ∧ CFSG.Open.pRank 5 D.M = 3 := by
  have h3not : 3 ∉ D.sig :=
    s168e3_three_not_mem_sig_of_omegaMinus_six_four_natural c hs hN
  have hbound : ∀ p ∈ D.sig, p = 5 := by
    intro p hp
    rcases s168e3_sigma_eq_three_or_five_of_omegaMinus_six_four_natural c hs hN hp with h | h
    · exact absurd (h ▸ hp) h3not
    · exact h
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have h5 : 5 ∈ D.sig := by
    have h := hbound p hp
    exact h ▸ hp
  exact ⟨Set.eq_singleton_iff_unique_mem.2 ⟨h5, fun q hq => hbound q hq⟩,
    c.std.pRank_eq_three h5⟩


theorem s168e3_case163_6_of_omegaMinus_six_eight_natural_original_denominator
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 3) :
    Case163_6 D V₀ V hV L := by
  obtain ⟨-, K, hF, hFin, b, d, hK, hirr, hR⟩ := hN
  let := hF
  let := hFin
  have hchar : CharP K 2 := s16k_charP_two_of_card (a := 3) (by norm_num) hK
  let := hchar
  have hwt : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hcomm : commV (lBar V₀ V hV L) = ⊤ := by
    rw [commV_eq_commSub]
    simpa [wTil, lBar] using hwt
  have hR' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
      (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) := by
    have h := hR
    rw [hwt, top_inf_eq] at h
    exact h
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hZbot : fixV (lBar V₀ V hV L) = ⊥ :=
    s16_omega_minus_six_cover (K := K) (b := b) (d := d)
      (by rw [hK8]; norm_num) hirr le_rfl hcomm hR'
  have hN' : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 3 :=
    ⟨⟨3, rfl⟩, K, hF, hFin, b, d, hK, hirr, by
      have h : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b d))).Realizes
          (lBar V₀ V hV L) ⊤ ⊥ := by
        have h := hR
        rw [hwt, top_inf_eq, hZbot] at h
        exact h
      simpa [hwt] using h⟩
  exact s168e3_case163_6_of_omegaMinus_six_eight_natural c hs hN'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
