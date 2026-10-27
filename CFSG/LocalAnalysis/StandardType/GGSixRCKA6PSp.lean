module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedPSpCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley (adjointGroup Tag)
open LinearMap (BilinForm)
open CFSG.StandardType.A6Red CFSG.StandardType.LayerCores

private theorem rckPS_map_centralizer_eq_inf {G H : Type*} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) (H₀ : Subgroup H) (hran : ι.range = H₀)
    (S : Set G) :
    (Subgroup.centralizer S).map ι = H₀ ⊓ Subgroup.centralizer (ι '' S) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer S := hc
    refine ⟨by rw [← hran]; exact ⟨c, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro s ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc' x hx]
  · rintro ⟨hg, hgc⟩
    rw [← hran] at hg
    rcases hg with ⟨c, rfl⟩
    have hgc' : ι c ∈ Subgroup.centralizer (ι '' S) := hgc
    exact Subgroup.mem_map.mpr ⟨c, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      apply hι
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hgc' (ι x) ⟨x, hx, rfl⟩, rfl⟩

private theorem rckPS_bilinIsometryGroup_map_generalLinearEquiv
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (B : BilinForm F V) :
    (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom =
      TauCeti.BilinForm.isometryGroup B := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    change B (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V) u : V →ₗ[F] V) x)
        (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V) u : V →ₗ[F] V) y) = B x y
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
    exact (CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mp hu) x y
  · intro h
    have hsymm : (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm g :
        V →ₗ[F] V)) = (g : V →ₗ[F] V) := by
      rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
      rw [MulEquiv.apply_symm_apply]
    refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm g, ?_, ?_⟩
    · exact CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr (fun x y => by
        rw [hsymm]
        exact (TauCeti.BilinForm.mem_isometryGroup_iff.mp h) x y)
    · exact MulEquiv.apply_symm_apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F V) g

private noncomputable def rckPS_gspIsometryGroupEquiv
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (B : BilinForm F V) :
    CFSG.ClassicalGroups.Alternating.Gsp B ≃* TauCeti.BilinForm.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).subgroupMap
      (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (rckPS_bilinIsometryGroup_map_generalLinearEquiv B))

private theorem rckPS_hom_of_inner {X : Type} [Group X] (G₀ D : Subgroup X)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hZG : Subgroup.center ↥G₀ = ⊥)
    (hinner : ∀ d ∈ D, ∃ g ∈ G₀, d * g ∈ Subgroup.centralizer (G₀ : Set X)) :
    ∃ φ : D →* ↥G₀, ∀ (d : D) (h : ↥G₀),
      (d : X) * (h : X) * (d : X)⁻¹ = (φ d : X) * (h : X) * (φ d : X)⁻¹ := by
  classical
  have hinner' : ∀ d : D, ∃ g : X, g ∈ G₀ ∧ (d : X) * g ∈ Subgroup.centralizer (G₀ : Set X) :=
    fun d => hinner (d : X) d.2
  let gsel : D → X := fun d => Classical.choose (hinner' d)
  have hgmem : ∀ d : D, gsel d ∈ G₀ := fun d => (Classical.choose_spec (hinner' d)).1
  have hgcent : ∀ d : D, (d : X) * gsel d ∈ Subgroup.centralizer (G₀ : Set X) :=
    fun d => (Classical.choose_spec (hinner' d)).2
  have hgd : ∀ d : D, gsel d * (d : X) = (d : X) * gsel d := by
    intro d
    have h1 : gsel d * ((d : X) * gsel d) = ((d : X) * gsel d) * gsel d :=
      Subgroup.mem_centralizer_iff.mp (hgcent d) (gsel d) (hgmem d)
    calc gsel d * (d : X)
        = gsel d * ((d : X) * gsel d) * (gsel d)⁻¹ := by group
      _ = ((d : X) * gsel d) * gsel d * (gsel d)⁻¹ := by rw [h1]
      _ = (d : X) * gsel d := by group
  have hconj : ∀ (d : D) (h : ↥G₀),
      (d : X) * (h : X) * (d : X)⁻¹ = (gsel d)⁻¹ * (h : X) * (gsel d) := by
    intro d h
    have hc : (h : X) * ((d : X) * gsel d) = ((d : X) * gsel d) * (h : X) :=
      Subgroup.mem_centralizer_iff.mp (hgcent d) (h : X) h.2
    rw [← hgd d] at hc
    calc (d : X) * (h : X) * (d : X)⁻¹
        = (gsel d)⁻¹ * ((gsel d) * (d : X) * (h : X)) * (d : X)⁻¹ := by group
      _ = (gsel d)⁻¹ * ((h : X) * (gsel d * (d : X))) * (d : X)⁻¹ := by rw [← hc]
      _ = (gsel d)⁻¹ * (h : X) * (gsel d) := by group
  let φfun : D → ↥G₀ := fun d => ⟨(gsel d)⁻¹, G₀.inv_mem (hgmem d)⟩
  have hconjφ : ∀ (d : D) (h : ↥G₀),
      (d : X) * (h : X) * (d : X)⁻¹ = (φfun d : X) * (h : X) * (φfun d : X)⁻¹ :=
    fun d h => by simpa [φfun] using hconj d h
  have hφone : φfun 1 = 1 := by
    have h1mem : (⟨gsel 1, hgmem 1⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hc : (h : X) * (((1 : D) : X) * gsel 1) = (((1 : D) : X) * gsel 1) * (h : X) :=
        Subgroup.mem_centralizer_iff.mp (hgcent 1) (h : X) h.2
      simpa using hc
    have h1eq : (⟨gsel 1, hgmem 1⟩ : ↥G₀) = 1 := by
      rwa [hZG, Subgroup.mem_bot] at h1mem
    apply Subtype.ext
    simpa [φfun] using congrArg Subtype.val h1eq
  have hφmul : ∀ d₁ d₂ : D, φfun (d₁ * d₂) = φfun d₁ * φfun d₂ := by
    intro d₁ d₂
    have key : ∀ h : ↥G₀,
        (φfun (d₁ * d₂) : X) * (h : X) * (φfun (d₁ * d₂) : X)⁻¹
          = ((φfun d₁ * φfun d₂ : ↥G₀) : X) * (h : X)
              * (((φfun d₁ * φfun d₂ : ↥G₀) : X))⁻¹ := by
      intro h
      calc (φfun (d₁ * d₂) : X) * (h : X) * (φfun (d₁ * d₂) : X)⁻¹
          = ((d₁ * d₂ : D) : X) * (h : X) * (((d₁ * d₂ : D) : X))⁻¹ := by
              rw [hconjφ (d₁ * d₂) h]
        _ = (d₁ : X) * ((d₂ : X) * (h : X) * (d₂ : X)⁻¹) * (d₁ : X)⁻¹ := by
              simp only [Subgroup.coe_mul]; group
        _ = (d₁ : X) * ((φfun d₂ : X) * (h : X) * (φfun d₂ : X)⁻¹) * (d₁ : X)⁻¹ := by
              rw [hconjφ d₂ h]
        _ = ((φfun d₁ * φfun d₂ : ↥G₀) : X) * (h : X)
              * (((φfun d₁ * φfun d₂ : ↥G₀) : X))⁻¹ := by
              have h1 := hconjφ d₁ (φfun d₂)
              have h2 := hconjφ d₁ h
              calc (d₁ : X) * ((φfun d₂ : X) * (h : X) * (φfun d₂ : X)⁻¹) * (d₁ : X)⁻¹
                  = ((d₁ : X) * (φfun d₂ : X) * (d₁ : X)⁻¹)
                      * ((d₁ : X) * (h : X) * (d₁ : X)⁻¹)
                      * (((d₁ : X) * (φfun d₂ : X) * (d₁ : X)⁻¹))⁻¹ := by group
                _ = ((φfun d₁ : X) * (φfun d₂ : X) * (φfun d₁ : X)⁻¹)
                      * ((φfun d₁ : X) * (h : X) * (φfun d₁ : X)⁻¹)
                      * (((φfun d₁ : X) * (φfun d₂ : X) * (φfun d₁ : X)⁻¹))⁻¹ := by
                      rw [h1, h2]
                _ = ((φfun d₁ * φfun d₂ : ↥G₀) : X) * (h : X)
                      * (((φfun d₁ * φfun d₂ : ↥G₀) : X))⁻¹ := by
                      simp only [Subgroup.coe_mul]; group
    have hcen : (φfun d₁ * φfun d₂)⁻¹ * φfun (d₁ * d₂) ∈ Subgroup.center ↥G₀ := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hk := key h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (h : X) * (((φfun d₁ * φfun d₂ : ↥G₀) : X)⁻¹ * (φfun (d₁ * d₂) : X))
          = ((φfun d₁ * φfun d₂ : ↥G₀) : X)⁻¹
              * (((φfun d₁ * φfun d₂ : ↥G₀) : X) * (h : X)
                  * (((φfun d₁ * φfun d₂ : ↥G₀) : X))⁻¹) * (φfun (d₁ * d₂) : X) := by
              group
        _ = ((φfun d₁ * φfun d₂ : ↥G₀) : X)⁻¹
              * ((φfun (d₁ * d₂) : X) * (h : X) * (φfun (d₁ * d₂) : X)⁻¹)
              * (φfun (d₁ * d₂) : X) := by rw [← hk]
        _ = (((φfun d₁ * φfun d₂ : ↥G₀) : X)⁻¹ * (φfun (d₁ * d₂) : X)) * (h : X) := by
              group
    have hA1 : (φfun d₁ * φfun d₂)⁻¹ * φfun (d₁ * d₂) = 1 := by
      rwa [hZG, Subgroup.mem_bot] at hcen
    calc φfun (d₁ * d₂)
        = (φfun d₁ * φfun d₂) * ((φfun d₁ * φfun d₂)⁻¹ * φfun (d₁ * d₂)) := by group
      _ = (φfun d₁ * φfun d₂) * 1 := by rw [hA1]
      _ = φfun d₁ * φfun d₂ := by group
  refine ⟨{ toFun := φfun, map_one' := hφone, map_mul' := hφmul }, ?_⟩
  intro d h
  exact hconjφ d h

private theorem rckPS_card_alternatingGroup_six :
    Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem rckPS_simple_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {n e : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ e) (hne : (n, 2 ^ e) ≠ (2, 2)) :
    GGA6CharTwoLie (StatedSp n K) ∧ IsSimpleGroup (StatedSp n K) := by
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hadm : StatedLieAdmissible .PSp n 2 e := ⟨Nat.prime_two, he, hn, hne⟩
  have hZ : Subgroup.center (StatedSp n K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n) (F := K) (by omega)
  have hmodel : StatedClassicalModel
      (StatedSp n K ⧸ Subgroup.center (StatedSp n K)) .PSp n 2 e :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient (n := n) (F := K)
      hadm hK
  have q : StatedSp n K ≃* (StatedSp n K ⧸ Subgroup.center (StatedSp n K)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hclass : StatedClassicalModel (StatedSp n K) .PSp n 2 e :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv q.symm hmodel
  refine ⟨⟨.PSp, n, e, Or.inl ⟨by decide, hmodel⟩⟩, ?_⟩
  exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ n 2 e hclass

private theorem rckPS_simple_statedSp_one {K : Type} [Field K] [Finite K] [CharP K 2] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (h4 : 4 ≤ Nat.card K) :
    GGA6CharTwoLie (StatedSp 1 K) ∧ IsSimpleGroup (StatedSp 1 K) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hne2 : (2, 2 ^ e) ≠ (2, 2) := by
    rintro h
    have h2 : 2 ^ e = 2 := congrArg Prod.snd h
    rw [hK, h2] at h4
    omega
  have hne3 : (2, 2 ^ e) ≠ (2, 3) := by
    rintro h
    have h2 : 2 ^ e = 3 := congrArg Prod.snd h
    have hdvd : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    rw [h2] at hdvd
    norm_num at hdvd
  have hadm : StatedLieAdmissible .PSL 2 2 e := ⟨Nat.prime_two, he, le_rfl, hne2, hne3⟩
  have hmodel :=
    CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 K hadm hK
  have hcenter : Subgroup.center (StatedSL 2 K) =
      (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) :=
    (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 2 K)).symm.trans
      (map_center_eq_statedScalars 2 K)
  let e2 : StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hmodelSL : StatedClassicalModel
      (StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K)) .PSL 2 2 e :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e2.symm hmodel
  have hshapeSL : GGA6CharTwoLie (StatedSL 2 K) :=
    ⟨.PSL, 2, e, Or.inl ⟨by decide, hmodelSL⟩⟩
  have hshape : GGA6CharTwoLie (StatedSp 1 K) :=
    GGA6CharTwoLie.of_mulEquiv
      (CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two K).some.symm hshapeSL
  have hZ : Subgroup.center (StatedSp 1 K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 1) (F := K) (by omega)
  have hsub : (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K) = ⊥ := by
    rw [← CFSG.LieType.Universal.Symplectic.center_eq 1 K, hZ]
  have hproj : IsSimpleGroup (StatedProj (StatedSp 1 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 1 (by omega)
      (Or.inl (Or.inr h4))
  haveI : IsSimpleGroup
      (StatedSp 1 K ⧸ (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K)) := hproj
  have q : (StatedSp 1 K ⧸ (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K)) ≃*
      StatedSp 1 K :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
  exact ⟨hshape, MulEquiv.isSimpleGroup q.symm⟩

private theorem rckPS_fixer_center_bot {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [Finite F] [CharP F 2] [FiniteDimensional F V]
    (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule F V)
    (hWnd : (B.restrict W).Nondegenerate) {f : ℕ} (hcard : Nat.card F = 2 ^ f)
    {J : Subgroup (V ≃ₗ[F] V)} (hJ : IsComponentOf J (ggA6SpFixer B (B.orthogonal W)))
    (hA6 : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)))
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) :
    Subgroup.center ↥J = ⊥ := by
  classical
  let H : Subgroup (V ≃ₗ[F] V) := ggA6SpFixer B (B.orthogonal W)
  have hJH : J ≤ H := hJ.1
  have hWalt : (B.restrict W).IsAlt := fun x => hB x
  obtain ⟨r, hdim⟩ : ∃ r, Module.finrank F W = 2 * r := by
    obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J hWalt hWnd
    refine ⟨m, ?_⟩
    have h1 : Module.finrank F W = m + m := by simpa using Module.finrank_eq_card_basis b
    omega
  obtain ⟨e1, -⟩ := ggA6_sp_restr_equiv B hB hnd W hWnd
  obtain ⟨e2⟩ := ggA6_sp_std_equiv (V := V) (B.restrict W) hWalt hWnd r hdim
  let e : H ≃* StatedSp r F := e1.trans e2
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      rw [pow_zero] at hcard
      have h2 : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
      omega
    · exact h
  have hJcardZ : Nat.card ↥J = 360 * Nat.card (Subgroup.center ↥J) := by
    obtain ⟨eA⟩ := hA6
    have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
      rw [Nat.card_congr eA.toEquiv, rckPS_card_alternatingGroup_six]
    calc Nat.card ↥J
        = Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
      _ = 360 * Nat.card (Subgroup.center ↥J) := by rw [h1]
  have hcpos : 1 ≤ Nat.card (Subgroup.center ↥J) := by
    haveI : Nonempty (Subgroup.center ↥J) := ⟨1, Subgroup.one_mem _⟩
    exact Nat.card_pos
  have hJdvdH : Nat.card ↥J ∣ Nat.card ↥H := by
    have hcard' : Nat.card ↥(J.subgroupOf H) = Nat.card ↥J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
    have h := Subgroup.card_subgroup_dvd_card (J.subgroupOf H)
    rwa [hcard'] at h
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · exfalso
    subst hr0
    have hHcard : Nat.card ↥H = 1 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 0]
      simp
    rw [hJcardZ, hHcard] at hJdvdH
    have := Nat.le_of_dvd (by norm_num) hJdvdH
    omega
  · have hZH : Subgroup.center ↥H = ⊥ := by
      have hZSp : Subgroup.center (StatedSp r F) = ⊥ :=
        CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := r) (F := F) (by omega)
      have hmap := Subgroup.map_center_eq e
      rw [hZSp] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥H) e.injective).mp hmap
    have hsimple_goal : IsSimpleGroup ↥H → Subgroup.center ↥J = ⊥ := by
      intro hsimpleH
      haveI : IsSimpleGroup ↥H := hsimpleH
      have hsubH : (J.subgroupOf H).IsSubnormal := hJ.2.1.subgroupOf
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimpleH hsubH with hbot | htop
      · have hJbot : J = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro j hj
          have hmem : (⟨j, hJH hj⟩ : ↥H) ∈ J.subgroupOf H := hj
          rw [hbot] at hmem
          simpa using (Subgroup.mem_bot.mp hmem)
        rw [hJbot]
        rw [Subgroup.eq_bot_iff_forall]
        intro z _
        exact Subsingleton.elim z 1
      · have hJH' : J = H := le_antisymm hJH (Subgroup.subgroupOf_eq_top.mp htop)
        rw [hJH', hZH]
    by_cases hr1 : r = 1
    · subst hr1
      by_cases hF2 : Nat.card F = 2
      · exfalso
        have hHcard : Nat.card ↥H = 6 := by
          rw [Nat.card_congr e.toEquiv,
            CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 1, hF2]
          norm_num
        have hle : Nat.card ↥J ≤ Nat.card ↥H := Subgroup.card_le_of_le hJH
        rw [hJcardZ, hHcard] at hle
        omega
      · have h4 : 4 ≤ Nat.card F := by
          have hf2 : 2 ≤ f := by
            by_contra h
            have : f = 1 := by omega
            rw [this, pow_one] at hcard
            exact hF2 hcard
          rw [hcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        haveI : IsSimpleGroup (StatedSp 1 F) :=
          (rckPS_simple_statedSp_one (K := F) hcard h4).2
        exact hsimple_goal (MulEquiv.isSimpleGroup e)
    · by_cases hr2 : r = 2
      · subst hr2
        by_cases hF2 : Nat.card F = 2
        · have hHcard : Nat.card ↥H = 720 := by
            rw [Nat.card_congr e.toEquiv,
              CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two F, hF2]
            norm_num
          have hc_dvd : Nat.card (Subgroup.center ↥J) ∣ 2 := by
            have h1 : 360 * Nat.card (Subgroup.center ↥J) ∣ 720 := by
              rw [← hJcardZ]
              rw [hHcard] at hJdvdH
              exact hJdvdH
            exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 360)).mp (by simpa using h1)
          have hc_le : Nat.card (Subgroup.center ↥J) ≤ 2 := Nat.le_of_dvd (by norm_num) hc_dvd
          have hc1 : Nat.card (Subgroup.center ↥J) = 1 := by
            obtain ⟨k, hk⟩ := hZ
            omega
          rw [Subgroup.eq_bot_iff_forall]
          intro z hz
          haveI : Subsingleton (Subgroup.center ↥J) :=
            Finite.card_le_one_iff_subsingleton.mp (le_of_eq hc1)
          exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : Subgroup.center ↥J) 1)
        · have h4 : 4 ≤ Nat.card F := by
            have hf2 : 2 ≤ f := by
              by_contra h
              have : f = 1 := by omega
              rw [this, pow_one] at hcard
              exact hF2 hcard
            rw [hcard]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
          have hne : (2, 2 ^ f) ≠ (2, 2) := by
            intro h
            exact hF2 (hcard.trans (congrArg Prod.snd h))
          haveI : IsSimpleGroup (StatedSp 2 F) :=
            (rckPS_simple_statedSp (K := F) (n := 2) (e := f) (by omega) hcard hne).2
          exact hsimple_goal (MulEquiv.isSimpleGroup e)
      · have hr3 : 3 ≤ r := by omega
        have hne : (r, 2 ^ f) ≠ (2, 2) := by
          intro h
          have := congrArg Prod.fst h
          omega
        haveI : IsSimpleGroup (StatedSp r F) :=
          (rckPS_simple_statedSp (K := F) (n := r) (e := f) (by omega) hcard hne).2
        exact hsimple_goal (MulEquiv.isSimpleGroup e)

private theorem rckPS_fixer_orthogonal_le_centralizer
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (U : Submodule F V) (hU : (B.restrict U).Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hA : A ≤ ggA6SpFixer B U) :
    ggA6SpFixer B (B.orthogonal U) ≤ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcompl : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU
  have horth : B.orthogonal (B.orthogonal U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl U
  have hhU : ∀ u ∈ U, h u ∈ U := by
    intro u hu
    rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hxh : h x = x := hh.2 x hx
    have hiso : B (h x) (h u) = B x u :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mp hh.1 x u
    rw [hxh] at hiso
    rw [hiso]
    exact hB.eq_iff.mpr (hx u hu)
  have haUorth : ∀ x ∈ B.orthogonal U, a x ∈ B.orthogonal U := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hafix : a u = u := (hA ha).2 u hu
    have hiso : B (a u) (a x) = B u x :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mp (hA ha).1 u x
    rw [hafix] at hiso
    rw [hiso]
    exact hx u hu
  apply LinearEquiv.ext
  intro v
  change a (h v) = h (a v)
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ B.orthogonal U by rw [hcompl.sup_eq_top]; exact Submodule.mem_top)
  rw [← hwz]
  simp only [map_add, hh.2 z hz, (hA ha).2 w hw, hh.2 (a z) (haUorth z hz),
    (hA ha).2 (h w) (hhU w hw)]

private theorem rckPS_center_bot_of_component {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [Finite F] [CharP F 2] [FiniteDimensional F V]
    (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (P : Subgroup (V ≃ₗ[F] V)) (hPB : P ≤ TauCeti.BilinForm.isometryGroup B)
    (hodd : Odd (Nat.card P)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {f : ℕ} (hcard : Nat.card F = 2 ^ f)
    {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : IsComponentOf J (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (P : Set (V ≃ₗ[F] V))))
    (hA6 : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)))
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) :
    Subgroup.center ↥J = ⊥ := by
  classical
  have hfin : Finite (V ≃ₗ[F] V) := finite_linearEquiv (K := F) (V := V)
  haveI : Fintype P := Fintype.ofFinite P
  let W : Submodule F V := ggA6SpFixed P
  let W' : Submodule F V := B.orthogonal W
  obtain ⟨hWnd, hWcompl⟩ := ggA6_sp_fixed_nondegenerate B hB hnd P hPB hodd
  rcases ggA6_sp_dichotomy B hB hnd P hPB hodd hJ with hJfixW' | hJfixW
  · have hJleFixer : J ≤ ggA6SpFixer B W' := by
      intro j hj
      exact ⟨(Subgroup.mem_inf.mp (hJ.1 hj)).1, hJfixW' j hj⟩
    have hPfixW : P ≤ ggA6SpFixer B W := by
      intro p hp
      exact ⟨hPB hp, fun v hv => hv p hp⟩
    have hFixer_le : ggA6SpFixer B W' ≤ TauCeti.BilinForm.isometryGroup B ⊓
        Subgroup.centralizer (P : Set (V ≃ₗ[F] V)) := by
      have hcent : ggA6SpFixer B W' ≤ Subgroup.centralizer (P : Set (V ≃ₗ[F] V)) :=
        rckPS_fixer_orthogonal_le_centralizer B hB hnd W hWnd P hPfixW
      intro g hg
      exact ⟨hg.1, hcent hg⟩
    have hJcomp : IsComponentOf J (ggA6SpFixer B W') :=
      IsComponentOf.of_le_of_le hJ hJleFixer hFixer_le
    exact rckPS_fixer_center_bot B hB hnd W hWnd hcard hJcomp hA6 hZ
  · exfalso
    haveI : IsMulCommutative ↥P := ⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩
    have hnil : Group.IsNilpotent ↥P := inferInstance
    have hlie : GGA6CharTwoLie ↥J := ggA6_sp_freeShape B hB hnd P hPB hodd hnil hJ hJfixW
    have hA6c : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    have hJJ : Nonempty ((alternatingGroup (Fin 6)) ⧸
        Subgroup.center (alternatingGroup (Fin 6)) ≃* ↥J ⧸ Subgroup.center ↥J) := by
      obtain ⟨eA⟩ := hA6
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hA6c).trans QuotientGroup.quotientBot).trans
        eA.symm⟩
    exact (ggA6_not_shape_of_a6 (alternatingGroup (Fin 6)) ↥J ⟨MulEquiv.refl _⟩ hJJ) hlie


theorem rck_A6_PSp_center
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ D J : Subgroup X) (hG₀ : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU .PSp n f).D ψ d) (hD : IsElemAbelian p D)
    (hD2 : Nat.card D = p ^ 2) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hZ : Odd (Nat.card (Subgroup.center ↥J)))
    (hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    Subgroup.center ↥J = ⊥ := by
  have hG₀' : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ := hG₀
  obtain ⟨⟨hadm, hrk⟩, ⟨hr, hk⟩, hperf, hLie⟩ := hG₀
  have hcenterK : Subgroup.center (ggU .PSp n f).K = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n)
      (F := GaloisField 2 f) (by have := hadm.2.2.1; omega)
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hk.trans_eq hcenterK)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  let e : (ggU .PSp n f).K ≃* ↥G₀ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  have hZG : Subgroup.center ↥G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ : (x : X) ∈ ψ.range := by rw [hr]; exact x.2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hza : a ∈ Subgroup.center (ggU .PSp n f).K := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply hinj
      have h1 := Subgroup.mem_center_iff.mp hx ⟨ψ b, hr ▸ ⟨b, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul, ha, map_mul] using h2
    rw [hcenterK, Subgroup.mem_bot] at hza
    rw [← ha, hza, map_one]
    rfl
  have hinnerAt : GGPsiDiagInnerAt .PSp := ggPsiDiagInnerAt_of_ggInnerTag .PSp (Or.inl rfl)
  have hinner : ∀ d ∈ D, ∃ g ∈ G₀, d * g ∈ Subgroup.centralizer (G₀ : Set X) :=
    fun d hd => hinnerAt X n f ψ G₀ hG₀' d (hDN hd) (hdiag d hd)
  obtain ⟨φ, hφ⟩ := rckPS_hom_of_inner G₀ D hDN hZG hinner
  let Dhat : Subgroup ↥G₀ := φ.range
  have hCeq : G₀ ⊓ Subgroup.centralizer (D : Set X) =
      G₀ ⊓ Subgroup.centralizer ((Dhat.map G₀.subtype : Subgroup X) : Set X) := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hg, hc⟩
      refine ⟨hg, ?_⟩
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
      rcases MonoidHom.mem_range.mp hd with ⟨d', rfl⟩
      have hcomm : (d' : X) * (g : X) = (g : X) * (d' : X) := hc (d' : X) d'.2
      have hconj := hφ d' ⟨g, hg⟩
      have hg_eq : (g : X) = (φ d' : X) * (g : X) * (φ d' : X)⁻¹ := by
        rw [← hconj, hcomm]; group
      calc (φ d' : X) * (g : X) = ((φ d' : X) * (g : X) * (φ d' : X)⁻¹) * (φ d' : X) := by group
        _ = (g : X) * (φ d' : X) := by rw [← hg_eq]
    · rintro ⟨hg, hc⟩
      refine ⟨hg, ?_⟩
      intro d hd
      have hmem : (φ ⟨d, hd⟩ : ↥G₀) ∈ Dhat := MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩
      have hcx : (φ ⟨d, hd⟩ : X) * (g : X) = (g : X) * (φ ⟨d, hd⟩ : X) :=
        hc (φ ⟨d, hd⟩ : X) (Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)
      have hconj := hφ ⟨d, hd⟩ ⟨g, hg⟩
      have hdg : (d : X) * (g : X) * (d : X)⁻¹ = (g : X) := by
        rw [hconj, hcx]; group
      calc (d : X) * (g : X) = ((d : X) * (g : X) * (d : X)⁻¹) * (d : X) := by group
        _ = (g : X) * (d : X) := by rw [hdg]
  have hJhat : IsComponentOf J (G₀ ⊓
      Subgroup.centralizer ((Dhat.map G₀.subtype : Subgroup X) : Set X)) := hCeq ▸ hJ
  let Jg : Subgroup ↥G₀ := J.subgroupOf G₀
  have hCg : (G₀ ⊓ Subgroup.centralizer ((Dhat.map G₀.subtype : Subgroup X) : Set X)).subgroupOf G₀ =
      Subgroup.centralizer (Dhat : Set ↥G₀) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ d hd
      exact Subtype.ext (hc (d : X) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩))
    · rintro hc
      refine ⟨g.2, ?_⟩
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (hc d hd)
  have hJg : IsComponentOf Jg (Subgroup.centralizer (Dhat : Set ↥G₀)) := by
    have hmain : IsComponentOf ((J.subgroupOf G₀).map G₀.subtype)
        (((G₀ ⊓ Subgroup.centralizer
          ((Dhat.map G₀.subtype : Subgroup X) : Set X)).subgroupOf G₀).map G₀.subtype) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le (hJhat.1.trans inf_le_left),
        Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := G₀.subtype) G₀.subtype_injective).1 hmain
    rwa [hCg] at h'
  have hJG : J ≤ G₀ := hJhat.1.trans inf_le_left
  let F := GaloisField 2 f
  let V := Fin n ⊕ Fin n → F
  let B : BilinForm F V := CFSG.ClassicalGroups.Symplectic.spForm n F
  let H₀ : Subgroup (V ≃ₗ[F] V) := TauCeti.BilinForm.isometryGroup B
  let φsp : (ggU .PSp n f).K ≃* H₀ :=
    (CFSG.ClassicalGroups.Symplectic.spEquiv (m := n) (K := F)).trans
      (rckPS_gspIsometryGroupEquiv B)
  let φe : ↥G₀ ≃* ↥H₀ := e.symm.trans φsp
  let ι : ↥G₀ →* (V ≃ₗ[F] V) := H₀.subtype.comp φe.toMonoidHom
  have hι_inj : Function.Injective ι :=
    H₀.subtype_injective.comp φe.injective
  have hran : ι.range = H₀ := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (φe c).2
    · intro hg
      refine ⟨φe.symm ⟨g, hg⟩, ?_⟩
      simp [ι]
  let Piso : Subgroup (V ≃ₗ[F] V) := Dhat.map ι
  let Jiso : Subgroup (V ≃ₗ[F] V) := Jg.map ι
  have hPisoB : Piso ≤ TauCeti.BilinForm.isometryGroup B := by
    intro p hp
    rcases hp with ⟨q, -, rfl⟩
    exact (φe q).2
  have hJiso : IsComponentOf Jiso (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (Piso : Set (V ≃ₗ[F] V))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := ι) hι_inj
      (Q := Jg) (K := Subgroup.centralizer (Dhat : Set ↥G₀))).mpr hJg
    rw [rckPS_map_centralizer_eq_inf ι hι_inj H₀ hran (Dhat : Set ↥G₀)] at h
    exact h
  have hoddD : Odd (Nat.card D) := by
    rw [hD2]
    exact (hp.odd_of_ne_two hp2).pow
  have hoddPiso : Odd (Nat.card Piso) := by
    have hcardP : Nat.card Piso = Nat.card Dhat := by
      change Nat.card (Dhat.map ι) = Nat.card Dhat
      rw [Subgroup.card_map_of_injective hι_inj]
    rw [hcardP]
    have hdvd : Nat.card Dhat ∣ Nat.card D := Subgroup.card_range_dvd φ
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd] at hoddD ⊢
    intro h2
    exact hoddD (h2.trans hdvd)
  have habPiso : ∀ a ∈ Piso, ∀ b ∈ Piso, a * b = b * a := by
    haveI : IsMulCommutative ↥D := hD.1
    intro a ha b hb
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    rcases MonoidHom.mem_range.mp ha' with ⟨d₁, rfl⟩
    rcases MonoidHom.mem_range.mp hb' with ⟨d₂, rfl⟩
    have h1 : ι (φ d₁) * ι (φ d₂) = ι (φ (d₁ * d₂)) := by rw [← map_mul, ← map_mul]
    have h2 : ι (φ d₂) * ι (φ d₁) = ι (φ (d₂ * d₁)) := by rw [← map_mul, ← map_mul]
    rw [h1, h2, mul_comm' d₁ d₂]
  have hcardB : Nat.card F = 2 ^ f := GaloisField.card 2 f (by have := hadm.2.1; omega)
  let eJ : ↥J ≃* ↥Jiso :=
    (Subgroup.subgroupOfEquivOfLe hJG).symm.trans (Jg.equivMapOfInjective ι hι_inj)
  have hA6iso : Nonempty (↥Jiso ⧸ Subgroup.center ↥Jiso ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨eA⟩ := hA6
    exact ⟨(QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).symm.trans eA⟩
  have hZiso : Odd (Nat.card (Subgroup.center ↥Jiso)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eJ).toEquiv]
    exact hZ
  have hZiso_bot : Subgroup.center ↥Jiso = ⊥ :=
    rckPS_center_bot_of_component B CFSG.ClassicalGroups.Symplectic.spForm_isAlt
      CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate Piso hPisoB hoddPiso habPiso
      hcardB hJiso hA6iso hZiso
  have hmap := Subgroup.map_center_eq eJ
  rw [hZiso_bot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥J) eJ.injective).mp hmap

end CFSG.StandardType.RCKA6
