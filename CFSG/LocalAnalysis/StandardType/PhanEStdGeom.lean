module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom
public import CFSG.LocalAnalysis.StandardType.PhanEPanelStab
public import CFSG.LocalAnalysis.StandardType.PhanEGood
public import CFSG.LocalAnalysis.StandardType.PhanELangIso
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel
public import CFSG.LocalAnalysis.StandardType.PhanEStdBuildingData

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

variable {K : Type} [Group K] (D : UniversalRootDatum K) (n : Fin D.rank → K)
  (H : Fin D.rank → Subgroup K)

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

structure StdInput where
  w₀ : W
  hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H
  F : FrobData D n H w₀
  hext : SteinbergExtras D n H
  hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀
  hsq : ∀ i, n i * n i = 1
  hBU : BruhatExtras D H
  L : StdLevi F (nrep hct w₀)
  R : RankOneField hct F
  hsl : ∀ i j : Fin D.rank, i ≠ j →
    coxeterMatrix D.isFiniteType i j = 2 ∨ coxeterMatrix D.isFiniteType i j = 3

variable {D n H} (S : StdInput D n H)

namespace StdInput

theorem stdPanel : StdPanel S.hct S.F (nrep S.hct S.w₀) :=
  stdPanel_of_rankOneField S.hct S.F _ S.hext S.hw₀ S.hsq S.R

@[expose] noncomputable def buildingData : PhanEBuildingData (coxeterMatrix D.isFiniteType) :=
  stdBuildingData S.hct S.F S.hext S.hw₀ S.hsq S.stdPanel

noncomputable def lang : K :=
  (exists_inv_mul_phi_eq S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L S.R).choose

theorem lang_spec : S.lang⁻¹ * S.F.φ S.lang = nrep S.hct S.w₀ :=
  (exists_inv_mul_phi_eq S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L S.R).choose_spec

variable {G : Type} [Group G] (e : G ≃* frobFix S.F)

@[expose] noncomputable def rho : G →* K :=
  stdEmbed S.F S.lang_spec e

theorem rho_injective : Function.Injective (S.rho e) :=
  stdEmbed_injective S.F S.lang_spec e

theorem range_rho : (S.rho e).range = stdFix S.F (nrep S.hct S.w₀) :=
  range_stdEmbed S.F S.lang_spec e

theorem mem_stdFix_rho (g : G) : S.rho e g ∈ stdFix S.F (nrep S.hct S.w₀) :=
  S.range_rho e ▸ ⟨g, rfl⟩

variable {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] (κ : Kf ≃+* S.L.Fld)
  (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = S.L.θ (κ c))

@[expose] noncomputable def family : PhanFamilyE Kf 2 f (coxeterMatrix D.isFiniteType) G :=
  stdFamily S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hext

@[expose] noncomputable def config : PhanEConfig Kf f (coxeterMatrix D.isFiniteType) G :=
  PhanEConfig.ofData S.buildingData (S.family e κ hκ)

noncomputable instance instMulAction : MulAction G (S.config e κ hκ).C :=
  MulAction.compHom (K ⧸ borel D H) (S.rho e)

end StdInput

theorem panelRel_iff_of_building {ι : Type} {M' : CoxeterMatrix ι} {W' : Type} [Group W']
    {cs : CoxeterSystem M' W'} {C : Type} {δ : C → C → W'} (hb : IsWeylDistanceBuilding cs δ)
    (i : ι) (x y : C) : panelRel cs δ i x y ↔ x = y ∨ δ x y = cs.simple i := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact Or.inr hab
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | hab
      · exact Or.inl rfl
      · have h1 := (hb.mul_simple b a b i hab).1
        rw [(hb.eq_one_iff b b).2 rfl] at h1
        rcases h1 with h1 | h1
        · exact Or.inl ((hb.eq_one_iff b a).1 h1.symm)
        · refine Or.inr ?_
          have h2 : δ b a = (cs.simple i)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
          rw [h2, CoxeterSystem.inv_simple]
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | hab
      · exact ih2
      · rcases ih2 with rfl | hbc
        · exact Or.inr hab
        · have h1 := (hb.mul_simple a b c i hbc).1
          rw [hab] at h1
          rcases h1 with h1 | h1
          · exact Or.inr h1
          · refine Or.inl ((hb.eq_one_iff a c).1 ?_)
            rw [h1, CoxeterSystem.simple_mul_simple_self]
  · rintro (rfl | h)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h

namespace StdInput

variable {G : Type} [Group G] (e : G ≃* frobFix S.F)
  {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] (κ : Kf ≃+* S.L.Fld)
  (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = S.L.θ (κ c))

theorem map_parab_family (i : Fin D.rank) :
    ((S.family e κ hκ).parab {i}).map (S.rho e) =
      (borel D H ⊓ stdFix S.F (nrep S.hct S.w₀)) ⊔ (slSU S.L.θ 2).map (S.L.ε i) := by
  have h1 : (S.family e κ hκ).parab {i} =
      (S.family e κ hκ).torus ⊔ ((S.family e κ hκ).ι i).range := by
    simp [PhanFamilyE.parab]
  have ht : ((S.family e κ hκ).torus).map (S.rho e) =
      ⨆ i, (H i ⊓ stdFix S.F (nrep S.hct S.w₀)) :=
    map_torus_stdFamily S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hext
  have hr : (((S.family e κ hκ).ι i).range).map (S.rho e) = (slSU S.L.θ 2).map (S.L.ε i) :=
    map_range_stdFamily_ι S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hext i
  rw [h1, Subgroup.map_sup, ht, hr, borel_inf_stdFix S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L]

@[expose] noncomputable def geom : (S.config e κ hκ).Geom where
  isom g x y := stdδ_smul S.hct S.hext (S.rho e g) (id x : K ⧸ borel D H) (id y : K ⧸ borel D H)
  comm_t g x := by
    show stdFlip S.F (nrep S.hct S.w₀) (S.rho e g • (id x : K ⧸ borel D H)) =
      S.rho e g • stdFlip S.F (nrep S.hct S.w₀) (id x : K ⧸ borel D H)
    rw [stdFlip_smul S.F S.hext S.hw₀]
    have h : nrep S.hct S.w₀ * S.F.φ (S.rho e g) * (nrep S.hct S.w₀)⁻¹ = S.rho e g :=
      (mem_stdFix_iff S.F (nrep S.hct S.w₀) (S.rho e g)).1 (S.mem_stdFix_rho e g)
    rw [h]
  c₀ := ((1 : K) : K ⧸ borel D H)
  c₀_op := stdδ_one_flip S.hct S.F S.hext S.hw₀
  transitive x hx := by
    obtain ⟨g, hg, hgx⟩ := exists_stdFix_mk_eq S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L
      (id x : K ⧸ borel D H) hx
    obtain ⟨g', rfl⟩ := (S.range_rho e ▸ hg : g ∈ (S.rho e).range)
    refine ⟨g', ?_⟩
    show S.rho e g' • ((1 : K) : K ⧸ borel D H) = (id x : K ⧸ borel D H)
    rw [← hgx, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  stab_base g := by
    show S.rho e g • ((1 : K) : K ⧸ borel D H) = ((1 : K) : K ⧸ borel D H) ↔ _
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one,
      inv_mem_iff]
    have ht : ((S.family e κ hκ).torus).map (S.rho e) =
        ⨆ i, (H i ⊓ stdFix S.F (nrep S.hct S.w₀)) :=
      map_torus_stdFamily S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hext
    change _ ↔ g ∈ (S.family e κ hκ).torus
    rw [← Subgroup.mem_map_iff_mem (S.rho_injective e), ht,
      ← borel_inf_stdFix S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L]
    exact ⟨fun h => Subgroup.mem_inf.2 ⟨h, S.mem_stdFix_rho e g⟩,
      fun h => (Subgroup.mem_inf.1 h).1⟩
  stab_panel i g := by
    have hb := stdBuilding S.hct S.hext
    have hmem : S.rho e g • ((1 : K) : K ⧸ borel D H) = ((S.rho e g : K) : K ⧸ borel D H) := by
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    show panelRel (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ S.hct) i
      ((1 : K) : K ⧸ borel D H) (S.rho e g • ((1 : K) : K ⧸ borel D H)) ↔
        g ∈ (S.family e κ hκ).parab {i}
    rw [hmem, panelRel_iff_of_building hb, ← hb.eq_one_iff,
      stdδ_mk_eq_iff S.hct S.hext 1 (S.rho e g) 1,
      stdδ_mk_eq_iff S.hct S.hext 1 (S.rho e g)
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i),
      inv_one, one_mul,
      stdFix_mem_cell_iff S.hct S.F S.hext S.hw₀ S.hsq S.hBU S.L i (S.mem_stdFix_rho e g),
      ← map_parab_family S e κ hκ i, Subgroup.mem_map_iff_mem (S.rho_injective e)]
  good := stdFamily_good S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hct S.hext S.hsl

theorem config_bridge (hK : Nat.card Kf = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (S.config e κ hκ).Bridge :=
  PhanEConfig.bridge_of_geom hK hq (S.config e κ hκ) (S.geom e κ hκ)

end StdInput

end CFSG.ClassicalInvolution.Phan.PhanE
