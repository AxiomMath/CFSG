module

public import CFSG.Quasithin.Background.HZCoc24B

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

theorem parZ_std :
    parZ (img11 AutPerm) z0 = img11 Lz :=
  perfectCore_stab

theorem radZ_std :
    radZ (img11 AutPerm) z0 = img11 KSp := by
  show pCoreOf 2 (parZ (img11 AutPerm) z0) = _
  rw [parZ_std]
  exact pCoreOf_img11_Lz

theorem vZ_std :
    vZ (img11 AutPerm) z0 = W0 := by
  show commV (radZ (img11 AutPerm) z0) = _
  rw [radZ_std]
  exact commV_img11_KSp

theorem hzConcl_std :
    HZConcl (img11 AutPerm) z0 6 := by
  unfold HZConcl
  rw [vZ_std, radZ_std, parZ_std]
  exact ⟨card_W0, card_img11_KSp, commutator_img11_KSp_Lz,
    fun N h1 h2 h3 => eq_of_le_img11_KSp h1 h2 h3, fun Y h1 h2 h3 => eq_W0_of_lt h1 h2 h3,
    W0_inf_fixV, commV_img11_Lz⟩

theorem isPGroup_img11_KSp : IsPGroup 2 ↥(img11 KSp) :=
  (isPGroup_KSp.of_equiv (Subgroup.subgroupOfEquivOfLe KSp_le_autPerm).symm).map _

theorem img11_KSp_le : img11 KSp ≤ img11 AutPerm :=
  Subgroup.map_mono fun σ _ => Subgroup.mem_subgroupOf.2 σ.2

theorem exists_equiv_z0 {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (h : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S) :
    ∃ e : V ≃* W11, H.map (congrHom e) = img11 AutPerm ∧ e z = z0 := by
  obtain ⟨e₀, he₀⟩ := cocode24_std h
  have he₀' : H.map (congrHom e₀) = img11 AutPerm :=
    he₀.trans (range_rho11_eq_img11 AutPerm le_rfl)
  have hcH : Nat.card ↥(img11 AutPerm) = Nat.card ↥H := by
    rw [← he₀']
    exact card_map_congrHom e₀ H
  have hS' : Nat.card ↥(S.map (congrHom e₀)) =
      2 ^ (Nat.card ↥(img11 AutPerm)).factorization 2 := by
    rw [hcH, ← hS]
    exact card_map_congrHom e₀ S
  have hSH' : S.map (congrHom e₀) ≤ img11 AutPerm := by
    rw [← he₀']
    exact Subgroup.map_mono hSH
  have hz' : e₀ z ∈ fixV (S.map (congrHom e₀)) := by
    rintro _ ⟨y, hy, rfl⟩
    show e₀ (y (e₀.symm (e₀ z))) = e₀ z
    rw [MulEquiv.symm_apply_apply, hzS y hy]
  have hz1' : e₀ z ≠ 1 := fun h' => hz1 (e₀.injective (h'.trans (map_one e₀).symm))
  have hfix : ∀ w ∈ fixV (img11 KSp), w = 1 ∨ w = z0 := fun w hw =>
    fix_ksRho w fun i => hw _ (ksRho_mem_img11_KSp i)
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_of_fixV hSH' hS' img11_KSp_le isPGroup_img11_KSp hfix
    hz' hz1'
  exact exists_equiv_std e₀ he₀' hg hgz

theorem hzConcl_of_cocode24
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : HZConcl H z 6 := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  have key : ∀ (A : Subgroup (MulAut W11)) (w : W11), A = img11 AutPerm → w = z0 →
      HZConcl A w 6 := by
    rintro A w rfl rfl
    exact hzConcl_std
  exact HZConcl.of_map e (key _ _ he hez)

theorem exists_fus_of_cocode24
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : ∃ φ ∈ H, φ z ≠ z ∧ φ z ∈ vZ H z := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  obtain ⟨φ₀, hφ₀, hφ₀z, hφ₀W⟩ := exists_fus
  rw [← he] at hφ₀
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  have hze : e.symm z0 = z := by
    rw [← hez]
    exact e.symm_apply_apply z
  have hφz : congrHom e φ z0 = e (φ z) := by
    refine (congrHom_apply e φ z0).trans ?_
    exact congrArg (fun v => e (φ v)) hze
  have key : ∀ (A : Subgroup (MulAut W11)) (w : W11), A = img11 AutPerm → w = z0 →
      vZ A w = W0 := by
    rintro A w rfl rfl
    exact vZ_std
  have hW : W0 = (vZ H z).map e.toMonoidHom := ((vZ_map e H z).trans (key _ _ he hez)).symm
  refine ⟨φ, hφ, fun h' => hφ₀z ?_, ?_⟩
  · refine hφz.trans ?_
    have h2 : e (φ z) = e z := congrArg e h'
    exact h2.trans hez
  · rw [hW] at hφ₀W
    obtain ⟨u, hu, hue⟩ := hφ₀W
    have hu' : e u = e (φ z) := hue.trans hφz
    rwa [e.injective hu'] at hu

end CFSG.Quasithin.H.Coc24
