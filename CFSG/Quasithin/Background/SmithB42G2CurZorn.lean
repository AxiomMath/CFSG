module

public import CFSG.Quasithin.Background.SmithB42G2Cur
public import CFSG.Quasithin.Background.SmithB42G2IdRoots
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.Quasithin.B42G2Cur

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Quasithin.B42G2Id
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Open CFSG.Quasithin.Explicit
  Matrix
open CFSG.Timmesfeld.RankTwo (hexRoot hexRoot_injective isRoot_hexRoot)

variable {K : Type} [Field K]

theorem xPar_single
    (i : Fin Tag.G2.rank) (c : K) :
    xPar (rootOperatorFamily .G2) (Pi.single i 1) c = xC .G2 K i c :=
  Subtype.ext (by
    rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]
    rfl)

theorem xPar_neg_single
    (i : Fin Tag.G2.rank) (c : K) :
    xPar (rootOperatorFamily .G2) (-Pi.single i 1) c = yC .G2 K i c :=
  Subtype.ext (by rw [xPar_neg_simple, RootOperatorFamily.coe_eltElement,
    RootOperatorFamily.eltUnit_neg_simple]; rfl)

theorem nC_eq (i : Fin Tag.G2.rank) :
    nC .G2 K i = xC .G2 K i 1 * yC .G2 K i (-1) * xC .G2 K i 1 := by
  refine Subtype.ext (Units.ext ?_)
  change (weylElt Tag.G2 K i 1 : Module.End K (RootModule Tag.G2 K)) = _
  rw [coe_weylElt]
  simp only [inv_one, Units.val_one]
  rfl

theorem pinnedX_eq_coe_xPar
    {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (c : K) :
    pinnedX .G2 K γ c = ((xPar (rootOperatorFamily .G2) γ
      (((rootOperatorFamily .G2).pinnedFamilySign γ : K) * c) : adjointGroup .G2 K) :
        ModGL .G2 K) := by
  rw [xPar_of_isRoot hγ, RootOperatorFamily.coe_eltElement]
  exact (rootOperatorFamily .G2).pinnedX_eq_eltUnit K hγ c

theorem dC_eq
    (i : Fin Tag.G2.rank) (t : Kˣ) :
    dC .G2 K i t = xC .G2 K i t * yC .G2 K i (-((t⁻¹ : Kˣ) : K)) * xC .G2 K i t *
      (xC .G2 K i (-1) * yC .G2 K i 1 * xC .G2 K i (-1)) := by
  refine Subtype.ext (Units.ext ?_)
  change ((weylElt Tag.G2 K i t * weylElt Tag.G2 K i (-1) : ModGL Tag.G2 K) :
    Module.End K (RootModule Tag.G2 K)) = _
  rw [Units.val_mul, coe_weylElt, coe_weylElt]
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one, neg_neg]
  rfl

theorem coe_xPar_mem
    {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (c : K) :
    ((xPar (rootOperatorFamily .G2) γ c : adjointGroup .G2 K) : ModGL .G2 K) ∈
      rootSubgroup .G2 K γ := by
  have e := pinnedX_eq_coe_xPar (K := K) hγ (((rootOperatorFamily .G2).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (rootOperatorFamily .G2).pinnedFamilySign_mul_self K γ, one_mul] at e
  rw [← e]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem g2Datum_U_eq_closure
    [Finite K] [CharP K 2] :
    (g2Datum K).U = Subgroup.closure {g | ∃ γ : Fin Tag.G2.rank → ℤ,
      (IsRoot .G2 γ ∧ 0 < height γ) ∧ ∃ c : K, xPar (rootOperatorFamily .G2) γ c = g} := by
  apply le_antisymm
  · intro u hu
    have hmem : (u : ModGL .G2 K) ∈ (Subgroup.closure {g | ∃ γ : Fin Tag.G2.rank → ℤ,
        (IsRoot .G2 γ ∧ 0 < height γ) ∧ ∃ c : K, xPar (rootOperatorFamily .G2) γ c = g}).map
          (adjointGroup .G2 K).subtype := by
      refine (iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_ :
        posUnipotent .G2 K ≤ _) hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_eq_coe_xPar hγ.1]
      exact ⟨_, Subgroup.subset_closure ⟨γ, hγ, _, rfl⟩, rfl⟩
    obtain ⟨g, hg, e⟩ := hmem
    rwa [show u = g from Subtype.ext e.symm]
  · rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, c, rfl⟩
    exact rootSubgroup_le_posUnipotent' hγ.1 hγ.2 (coe_xPar_mem hγ.1 c)

section Zorn

variable [CharP K 2] (ψ : adjointGroup .G2 K →* cayleyGroup K)

theorem psi_xC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (i : Fin Tag.G2.rank) (c : K) : ψ (xC .G2 K i c) = zPsi (Pi.single i 1) c := by
  rw [← xPar_single]
  exact hψ _ (isRoot_single .G2 i) c

theorem psi_yC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (i : Fin Tag.G2.rank) (c : K) : ψ (yC .G2 K i c) = zPsi (-Pi.single i 1) c := by
  rw [← xPar_neg_single]
  exact hψ _ (isRoot_neg_single .G2 i) c

theorem sl3P_eq_tv : (tv 1 0 (by decide) 1 * tv 0 1 (by decide) 1 * tv 1 0 (by decide) 1 :
    SL3 K) = sl3P := by
  refine Subtype.ext ?_
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  change ((tv 1 0 (by decide) 1 : SL3 K) : Matrix (Fin 3) (Fin 3) K) *
      ((tv 0 1 (by decide) 1 : SL3 K) : Matrix (Fin 3) (Fin 3) K) *
      ((tv 1 0 (by decide) 1 : SL3 K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  rw [tv10_lit, tv01_lit, Matrix.mul_fin_three, Matrix.mul_fin_three]
  simp [h2]

theorem psi_nC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (i : Fin Tag.G2.rank) : ψ (nC .G2 K i) = zW K i := by
  rw [nC_eq, map_mul, map_mul, psi_xC ψ hψ, psi_yC ψ hψ,
    show (-1 : K) = 1 from CharTwo.neg_eq 1]
  rcases fin2_cases i with rfl | rfl
  · have h5 : (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 5 := by
      funext k
      fin_cases k <;> decide
    change zPsi (Pi.single (0 : Fin 2) 1) 1 * zPsi (-Pi.single (0 : Fin 2) 1) 1 *
      zPsi (Pi.single (0 : Fin 2) 1) 1 = zW K 0
    rw [h5, zPsi_pos, zPsi_neg]
    change g2A _ * g2A _ * g2A _ = g2A sl3P
    rw [← map_mul, ← map_mul, sl3P_eq_tv]
  · have h0 : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 0 := by
      funext k
      fin_cases k <;> decide
    change zPsi (Pi.single (1 : Fin 2) 1) 1 * zPsi (-Pi.single (1 : Fin 2) 1) 1 *
      zPsi (Pi.single (1 : Fin 2) 1) 1 = zW K 1
    rw [h0, zPsi_pos, zPsi_neg]
    rfl

theorem psi_dC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (i : Fin Tag.G2.rank) (t : Kˣ) :
    ψ (dC .G2 K i t) = zPsi (Pi.single i 1) (t : K) * zPsi (-Pi.single i 1) ((t⁻¹ : Kˣ) : K) *
      zPsi (Pi.single i 1) (t : K) * zW K i := by
  rw [dC_eq, ← psi_nC ψ hψ i, nC_eq, show (-1 : K) = 1 from CharTwo.neg_eq 1,
    show (-((t⁻¹ : Kˣ) : K)) = ((t⁻¹ : Kˣ) : K) from CharTwo.neg_eq _]
  simp only [map_mul, psi_xC ψ hψ, psi_yC ψ hψ]

theorem exists_hexRoot_of_pos
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ)
    (hpos : 0 < height γ) : ∃ j, γ = hexRoot j := by
  obtain ⟨j, h | h⟩ := g2_root_cases hγ
  · exact ⟨j, h⟩
  · exfalso
    subst h
    revert hpos
    fin_cases j <;> decide

theorem map_g2Datum_U
    [Finite K]
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c) :
    (g2Datum K).U.map ψ = Subgroup.closure (⋃ j, Set.range (zPos (F := K) j)) := by
  rw [g2Datum_U_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨γ, ⟨hγ, hpos⟩, c, rfl⟩, rfl⟩
    obtain ⟨j, rfl⟩ := exists_hexRoot_of_pos hγ hpos
    exact ⟨j, c, by rw [hψ _ hγ, zPsi_pos]⟩
  · rintro ⟨j, c, rfl⟩
    refine ⟨_, ⟨hexRoot j, ⟨isRoot_hexRoot j, by fin_cases j <;> decide⟩, c, rfl⟩, ?_⟩
    rw [hψ _ (isRoot_hexRoot j), zPsi_pos]

theorem fixU_comp
    [Finite K] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ' : Representation k (cayleyGroup K) V) :
    (g2Datum K).fixU (ρ'.comp ψ) = fixSub ρ' ((g2Datum K).U.map ψ) := by
  ext v
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact hv u hu
  · intro hv u hu
    exact hv _ ⟨u, hu, rfl⟩

theorem heckeT_comp
    [Finite K] [Fintype K]
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ' : Representation k (cayleyGroup K) V) (i : Fin Tag.G2.rank) (v : V) :
    (g2Datum K).heckeT (ρ'.comp ψ) i v = ∑ c : K, ρ' (zPsi (Pi.single i 1) c * zW K i) v := by
  rw [g2_heckeT_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MonoidHom.comp_apply, map_mul, psi_xC ψ hψ, psi_nC ψ hψ]

theorem zorn_iso_of_type
    [Finite K] (hsurj : Function.Surjective ψ) {k V V' : Type*}
    [Field k]
    [Algebra K k] [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {ρ' : Representation k (cayleyGroup K) V} {σ' : Representation k (cayleyGroup K) V'}
    (hρ' : IsSimpleRep ρ') (hσ' : IsSimpleRep σ') {y : V} {y' : V'}
    {χ : adjointGroup .G2 K → k} {J : Finset (Fin Tag.G2.rank)}
    (ht : IsG2Type (ρ'.comp ψ) y χ J) (ht' : IsG2Type (σ'.comp ψ) y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : cayleyGroup K) (v : V), β (ρ' g v) = σ' g (β v) := by
  obtain ⟨β, hβ⟩ := g2_iso_of_type ((isSimpleRep_comp_iff ρ' hsurj).mpr hρ')
    ((isSimpleRep_comp_iff σ' hsurj).mpr hσ') ht ht'
  exact ⟨β, intertwines_of_comp hsurj (β := β.toLinearMap) hβ⟩

theorem zorn_exists_type
    [Finite K] (hsurj : Function.Surjective ψ) {k V : Type*}
    [Field k]
    [Algebra K k] [AddCommGroup V] [Module k V] {ρ' : Representation k (cayleyGroup K) V}
    (hρ' : IsSimpleRep ρ') :
    ∃ y : V, ∃ χ : adjointGroup .G2 K → k, ∃ J : Finset (Fin Tag.G2.rank),
      IsG2Type (ρ'.comp ψ) y χ J :=
  g2_exists_type ((isSimpleRep_comp_iff ρ' hsurj).mpr hρ')

end Zorn

end CFSG.Quasithin.B42G2Cur
