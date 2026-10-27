module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigOSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigB
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFixed
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly
open CFSG.ClassicalGroups.Orthogonal (extEquiv)
open CFSG.RankThree.Classical2 (orthDerived)

section Perp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private def plh_fixSub (V₀ : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ x ∈ V₀, g x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    rw [LinearEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    have h : a⁻¹ x = a⁻¹ (a x) := by rw [ha x hx]
    rw [h]
    simp

private lemma plh_extEquiv_fix {V₀ W : Submodule (ZMod 2) V} (hPW : IsCompl V₀ W)
    (g : ↥W ≃ₗ[ZMod 2] ↥W) {x : V} (hx : x ∈ V₀) : extEquiv hPW g x = x := by
  have h : x = x + (0 : V) := (add_zero x).symm
  rw [h, CFSG.ClassicalGroups.Orthogonal.extEquiv_add hPW g hx (Submodule.zero_mem W)]
  simp

theorem qtwoDB43_perfect_le_derived {Q : QuadraticForm (ZMod 2) V} {V₀ : Submodule (ZMod 2) V}
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0)
    (R : Subgroup (V ≃ₗ[ZMod 2] V)) (hR : ⁅R, R⁆ = R)
    (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ f ∈ R, ∀ x ∈ V₀, f x = x) :
    R ≤ (orthDerived (Q.restrict (qtwoDB43_perp Q V₀))).map
      (extEquiv (qtwoDB43_isCompl_perp hV₀nd)) := by
  obtain ⟨ρ', hρ'O, hρ'E⟩ := qtwoDB43_factor_through_ext hV₀nd R.subtype
    (fun γ => hRO γ.2) (fun γ x hx => hfix γ γ.2 x hx)
  have hRmap : R ≤ (TauCeti.QuadraticMap.orthogonalGroup
      (Q.restrict (qtwoDB43_perp Q V₀))).map
      (extEquiv (qtwoDB43_isCompl_perp hV₀nd)) := by
    intro f hf
    have h := Subgroup.mem_map_of_mem (extEquiv (qtwoDB43_isCompl_perp hV₀nd))
      (hρ'O ⟨f, hf⟩)
    rwa [hρ'E ⟨f, hf⟩] at h
  have hcomm : ⁅R, R⁆ ≤ (orthDerived (Q.restrict (qtwoDB43_perp Q V₀))).map
      (extEquiv (qtwoDB43_isCompl_perp hV₀nd)) := by
    have h := Subgroup.commutator_mono hRmap hRmap
    rwa [← Subgroup.map_commutator] at h
  rwa [hR] at hcomm

theorem qtwoDB43_cube_mem_derived {Q : QuadraticForm (ZMod 2) V} {V₀ : Submodule (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0)
    (hW6 : 6 ≤ Module.finrank (ZMod 2) (qtwoDB43_perp Q V₀)) {f : V ≃ₗ[ZMod 2] V}
    (hf : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ x ∈ V₀, f x = x)
    (hf3 : f ^ 3 = 1) :
    f ∈ (orthDerived (Q.restrict (qtwoDB43_perp Q V₀))).map
      (extEquiv (qtwoDB43_isCompl_perp hV₀nd)) := by
  classical
  have hfixmem : f ∈ plh_fixSub V₀ := hfix
  obtain ⟨ρ', hρ'O, hρ'E⟩ := qtwoDB43_factor_through_ext hV₀nd (Subgroup.zpowers f).subtype
    (fun γ => (Subgroup.zpowers_le.mpr hf) γ.2)
    (fun γ x hx => (Subgroup.zpowers_le.mpr hfixmem) γ.2 x hx)
  let g : ↥(qtwoDB43_perp Q V₀) ≃ₗ[ZMod 2] ↥(qtwoDB43_perp Q V₀) :=
    ρ' ⟨f, Subgroup.mem_zpowers f⟩
  have hEg : extEquiv (qtwoDB43_isCompl_perp hV₀nd) g = f :=
    hρ'E ⟨f, Subgroup.mem_zpowers f⟩
  have hg3 : g ^ 3 = 1 := by
    apply qtwoDB43_ext_injective (qtwoDB43_isCompl_perp hV₀nd)
    rw [map_pow, hEg, hf3, map_one]
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup
      (Q.restrict (qtwoDB43_perp Q V₀)) :=
    hρ'O ⟨f, Subgroup.mem_zpowers f⟩
  have hodd : Odd (orderOf g) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hg3)
  have hmem : g ∈ orthDerived (Q.restrict (qtwoDB43_perp Q V₀)) :=
    (CFSG.AGLEmbedding.ToralCensus.perfect_and_odd_orthDerived_of_card_two
      (K := ZMod 2) (W := ↥(qtwoDB43_perp Q V₀)) (Nat.card_zmod 2)
      (qtwoDB43_perp_nondegenerate hQ hV₀nd) hW6).2 g hgO hodd
  have h := Subgroup.mem_map_of_mem (extEquiv (qtwoDB43_isCompl_perp hV₀nd)) hmem
  rwa [hEg] at h

end Perp

theorem qtwoDB43_orthY_of_plane {G : Type} [Group G] [Finite G] {Bs N J₁ J₂ : Subgroup G}
    {m : ℕ} (hm : 6 ≤ m) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) (σ : ↥N ≃* ↥(orthDerived Q))
    (β : ↥Bs →* ↥(orthDerived Q))
    (hcompat : ∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹)
    (hne : ∃ s : ↥Bs, β s ≠ 1) {V₀ : Submodule (ZMod 2) V}
    (hV₀ : ∀ x : V, x ∈ V₀ ↔ ∀ s : ↥Bs, ((β s : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x)
    (hV₀dim : Module.finrank (ZMod 2) V₀ = 2)
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (qtwoDB43_perp Q V₀)) ↔
      Even (m - 1))
    (hJ₁N : J₁ ≤ N) (hJ₂N : J₂ ≤ N) (hJ₁ : ⁅J₁, J₁⁆ = J₁) (hJ₂ : ⁅J₂, J₂⁆ = J₂)
    (hJ₁V₀ : ∀ n : ↥N, (n : G) ∈ J₁ → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x)
    (hJ₂V₀ : ∀ n : ↥N, (n : G) ∈ J₂ → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₂ ≤ Y ∧ ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y,
      Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧ Subgroup.center ↥Y = ⊥ := by
  classical
  let W : Submodule (ZMod 2) V := qtwoDB43_perp Q V₀
  have hPW : IsCompl V₀ W := qtwoDB43_isCompl_perp hV₀nd
  have hdimW : Module.finrank (ZMod 2) W = 2 * (m - 1) := by
    have h := Submodule.finrank_add_eq_of_isCompl hPW
    rw [hdim, hV₀dim] at h
    omega
  have hW6 : 6 ≤ Module.finrank (ZMod 2) W := by rw [hdimW]; omega
  have hQW : (QuadraticMap.polarBilin (Q.restrict W)).Nondegenerate :=
    qtwoDB43_perp_nondegenerate hQ hV₀nd
  let E := extEquiv hPW
  have hOmap : (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)).map E ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, hg, rfl⟩
    exact qtwoDB43_ext_mem_orthogonalGroup hPW hg
  have hΩmap : (orthDerived (Q.restrict W)).map E ≤ orthDerived Q := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hOmap hOmap
  let Eω : ↥(orthDerived (Q.restrict W)) →* ↥(orthDerived Q) :=
    (E.comp (orthDerived (Q.restrict W)).subtype).codRestrict (orthDerived Q)
      (fun x => hΩmap (Subgroup.mem_map_of_mem E x.2))
  have hEωinj : Function.Injective Eω := by
    intro a b hab
    apply Subtype.ext
    exact qtwoDB43_ext_injective hPW (congrArg Subtype.val hab)
  let ψ' : ↥(orthDerived (Q.restrict W)) →* G := N.subtype.comp (σ.symm.toMonoidHom.comp Eω)
  have hψ'inj : Function.Injective ψ' := by
    intro a b hab
    have h1 : σ.symm (Eω a) = σ.symm (Eω b) := N.subtype_injective hab
    exact hEωinj (σ.symm.injective h1)
  obtain ⟨ρ', hρ'O, hρ'E⟩ := qtwoDB43_factor_through_ext hV₀nd ((orthDerived Q).subtype.comp β)
    (fun s => CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q) (β s).2)
    (fun s x hx => (hV₀ x).mp hx s)
  have hρ'mem : ∀ s : ↥Bs, ρ' s ∈ orthDerived (Q.restrict W) := by
    intro s
    have hβ3 : (β s) ^ 3 = 1 := by
      have hs3 : s ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 (s : G) s.2)
      rw [← map_pow, hs3, map_one]
    have h3 : (E (ρ' s)) ^ 3 = 1 := by
      rw [hρ'E s]
      change ((orthDerived Q).subtype (β s)) ^ 3 = 1
      rw [← map_pow (orthDerived Q).subtype (β s) 3, hβ3]
      rfl
    have hEfO : E (ρ' s) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      qtwoDB43_ext_mem_orthogonalGroup hPW (hρ'O s)
    have hfixE : ∀ x ∈ V₀, E (ρ' s) x = x := fun x hx => plh_extEquiv_fix hPW (ρ' s) hx
    have hmem := qtwoDB43_cube_mem_derived hQ hV₀nd hW6 hEfO hfixE h3
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hmem
    have hw' : w = ρ' s := qtwoDB43_ext_injective hPW hwe
    rwa [hw'] at hw
  let β' : ↥Bs →* ↥(orthDerived (Q.restrict W)) :=
    ρ'.codRestrict (orthDerived (Q.restrict W)) hρ'mem
  have hEβ' : ∀ s : ↥Bs, Eω (β' s) = β s := by
    intro s
    apply Subtype.ext
    exact hρ'E s
  have hcompat' : ∀ (b : ↥Bs) (y : ↥(orthDerived (Q.restrict W))),
      ψ' (β' b * y * (β' b)⁻¹) = (b : G) * ψ' y * (b : G)⁻¹ := by
    intro b y
    let n : ↥N := σ.symm (Eω y)
    have hn : (n : G) = ψ' y := rfl
    have hEhom : Eω (β' b * y * (β' b)⁻¹) = β b * Eω y * (β b)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hEβ' b]
    have hσn : σ n = Eω y := σ.apply_symm_apply (Eω y)
    have hkey : σ.symm (Eω (β' b * y * (β' b)⁻¹)) = ggGamma N hBsN b n := by
      rw [hEhom]
      have h2 : β b * Eω y * (β b)⁻¹ = σ (ggGamma N hBsN b n) := by
        rw [hcompat b n, hσn]
      rw [h2, σ.symm_apply_apply]
    have hψz : ψ' (β' b * y * (β' b)⁻¹) = ((ggGamma N hBsN b n : ↥N) : G) := by
      show N.subtype (σ.symm (Eω (β' b * y * (β' b)⁻¹))) = N.subtype (ggGamma N hBsN b n)
      rw [hkey]
    rw [hψz, ggGamma_coe, hn]
  have hne' : ∃ b : ↥Bs, β' b ≠ 1 := by
    obtain ⟨s, hs⟩ := hne
    refine ⟨s, fun h => hs ?_⟩
    have h1 := hEβ' s
    rw [h, map_one] at h1
    exact h1.symm
  have hJle : ∀ (J : Subgroup G), J ≤ N → ⁅J, J⁆ = J →
      (∀ n : ↥N, (n : G) ∈ J → ∀ x ∈ V₀,
        ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x) → J ≤ ψ'.range := by
    intro J hJN hJ hJV₀
    let A : Subgroup ↥(orthDerived Q) := (J.subgroupOf N).map σ.toMonoidHom
    let R : Subgroup (V ≃ₗ[ZMod 2] V) := A.map (orthDerived Q).subtype
    have hJsub : (J.subgroupOf N).map N.subtype = J := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
      exact hJN
    have hJsubComm : ⁅J.subgroupOf N, J.subgroupOf N⁆ = J.subgroupOf N :=
      Subgroup.map_injective N.subtype_injective (by
        rw [Subgroup.map_commutator, hJsub, hJ])
    have hAcomm : ⁅A, A⁆ = A := by
      show ⁅(J.subgroupOf N).map σ.toMonoidHom, (J.subgroupOf N).map σ.toMonoidHom⁆ =
        (J.subgroupOf N).map σ.toMonoidHom
      rw [← Subgroup.map_commutator, hJsubComm]
    have hRcomm : ⁅R, R⁆ = R := by
      show ⁅A.map (orthDerived Q).subtype, A.map (orthDerived Q).subtype⁆ =
        A.map (orthDerived Q).subtype
      rw [← Subgroup.map_commutator, hAcomm]
    have hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro x ⟨a, -, rfl⟩
      exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q) a.2
    have hRfix : ∀ f ∈ R, ∀ x ∈ V₀, f x = x := by
      rintro f ⟨a, ha, rfl⟩ x hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp ha
      exact hJV₀ n (Subgroup.mem_subgroupOf.mp hn) x hx
    have hRle := qtwoDB43_perfect_le_derived hV₀nd R hRcomm hRO hRfix
    intro n hn
    let nN : ↥N := ⟨n, hJN hn⟩
    have hσA : σ nN ∈ A :=
      Subgroup.mem_map_of_mem σ.toMonoidHom (Subgroup.mem_subgroupOf.mpr hn)
    have hσR : (orthDerived Q).subtype (σ nN) ∈ R :=
      Subgroup.mem_map_of_mem (orthDerived Q).subtype hσA
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp (hRle hσR)
    refine ⟨⟨w, hw⟩, ?_⟩
    show N.subtype (σ.symm (Eω ⟨w, hw⟩)) = n
    have hEωw : Eω ⟨w, hw⟩ = σ nN := by
      apply Subtype.ext
      exact hwe
    rw [hEωw, σ.symm_apply_apply]
    rfl
  refine ⟨ψ'.range, hJle J₁ hJ₁N hJ₁ hJ₁V₀, hJle J₂ hJ₂N hJ₂ hJ₂V₀, ?_⟩
  obtain ⟨hframe, hcenter⟩ := qtwoDB42_frameCore_of_model hBs hSC hQW (d := m - 1)
    (by omega) hdimW htype ψ' hψ'inj rfl β' hcompat' hne'
  obtain ⟨Φ, hF, hr⟩ := hframe
  exact ⟨Φ, hF, hr, hcenter⟩

end CFSG.StandardType.QTwo

end
