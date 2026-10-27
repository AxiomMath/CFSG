module

public import CFSG.LocalAnalysis.StandardType.GGFinModelTorus
public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots
public import CFSG.LocalAnalysis.StandardType.GGFinModelPi
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.LocalAnalysis.StandardType.GGLangData
public import CFSG.LocalAnalysis.StandardType.GGLangUniform

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section LangData


theorem ggLangData_of_torusData_retained {t : StatedLieTag} {n f p : ℕ} [NeZero p] (ht : GGExcFive t)
    (hf : 1 ≤ f)
    (_hp : p.Prime) (_hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (D : LangDatum (langTag t) GGL) (ι₀ : GGKb t n f →* ModGL (langTag t) GGL) (ζ : GGLˣ)
    (hq : D.q = 2 ^ f)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    (hρ : ∀ ρ : Equiv.Perm (Fin (langTag t).rank → ℤ), FrobRootMap D ρ →
      ∀ v ∈ (ggU (absTag t) 6 f).D.roots,
        ρ (ggLangReidx (rank_eq_langTag f ht) v) =
          eps p f • ggLangReidx (rank_eq_langTag f ht) (latPerm (piB t p f) v)) :
    ∃ B : GGLangData GGL t n f p hT.ggBfull (gram t f) (piB t p f) hT.ggCoord,
      B.τ = langTag t ∧ HEq B.setup.D D ∧
      HEq B.ι ((MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀) ∧
      HEq B.a (fun b : hT.ggBfull => ggParam (rank_eq_langTag f ht) ζ
        (Multiplicative.toAdd (hT.ggCoord b))) ∧ B.ζ = ζ := by
  classical
  obtain ⟨S, ι, hSD, hιeq, hιinj, hιrange, hu⟩ :=
    CFSG.StandardType.LangRat.exists_langSetup_of_toral_datum_uniform
      (τ := langTag t) (L := GGL) (ℓ := 2) Nat.prime_two hf D (by rw [hq])
      (p₀ := 5) Nat.prime_five (by norm_num) (Or.inl le_rfl)
      hT.pkg.desc.finite_model ι₀ hT.pkg.inj hT.pkg.desc.Γ_eq
  subst hSD
  let a : hT.ggBfull → Fin (langTag t).rank → GGLˣ :=
    fun b => ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd (hT.ggCoord b))
  have ha_coord : ∀ (b : hT.ggBfull) (j : Fin (langTag t).rank),
      a b j = ζ ^ ZMod.val (Multiplicative.toAdd (hT.ggCoord b)
        (Fin.cast (rank_eq_langTag f ht).symm j)) := fun _ _ => rfl
  have ha_torus : ∀ b : hT.ggBfull,
      rootDiagUnit (langTag t) (a b) ∈ S.D.torus := by
    intro b
    exact hT.torus_mem (Multiplicative.toAdd (hT.ggCoord b)) (hT.ggCoord_fixed b)
  have ha_act : ∀ (b : hT.ggBfull) (c : GGKb t n f),
      ι ((b : MulAut (GGKb t n f)) c) =
        rootDiagUnit (langTag t) (a b) * ι c * (rootDiagUnit (langTag t) (a b))⁻¹ := by
    intro b c
    obtain ⟨z, hz⟩ := b.2
    have hu_mem : hT.uMap z ∈ S.D.torus.map (MulAut.conj S.D.g0).toMonoidHom := by
      rw [hT.uMap_apply]
      exact Subgroup.mem_map.mpr ⟨rootDiagUnit (langTag t)
        (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1),
        hT.torus_mem _ (Multiplicative.toAdd z).2, rfl⟩
    obtain ⟨a', _ha'T, ha'eq, ha'act⟩ := hu (hT.uMap z) hu_mem
    have hb : (⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ : hT.ggBfull) = b := Subtype.ext hz
    have hcoord : Multiplicative.toAdd (hT.ggCoord b) = (Multiplicative.toAdd z).1 := by
      rw [← hb, hT.ggCoord_apply]
      rfl
    have ha'a : a' = ggParam (rank_eq_langTag f ht) ζ
        (Multiplicative.toAdd (hT.ggCoord b)) := by
      apply CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      rw [ha'eq, hT.uMap_apply]
      have hg : S.D.g0⁻¹ * (S.D.g0 * rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
            * S.D.g0⁻¹) * S.D.g0 = rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1) := by
        group
      rw [hg, hcoord]
    have hβ : ∀ c : GGKb t n f, ι₀ ((b : MulAut (GGKb t n f)) c) =
        hT.uMap z * ι₀ c * (hT.uMap z)⁻¹ := by
      intro c
      rw [← hz]
      exact hT.ggBetaHom_apply z c
    have hfin := ha'act (b : MulAut (GGKb t n f)) hβ c
    rw [ha'a] at hfin
    exact hfin
  have hcenter : Subgroup.center (GGKb t n f) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxfix : ι₀ x ∈ S.D.fix := hT.pkg.desc.range_le (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    have hxadj : ι₀ x ∈ adjointGroup (langTag t) GGL :=
      ((LangDatum.mem_fix S.D).mp hxfix).1
    have hcomm : ∀ y : GGKb t n f, ι₀ x * ι₀ y = ι₀ y * ι₀ x := by
      intro y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y).symm]
    have hcent : ι₀ x = 1 := hT.pkg.cent_triv (ι₀ x) hxadj hcomm
    exact hT.pkg.inj (by rw [map_one]; exact hcent)
  let B : GGLangData GGL t n f p hT.ggBfull (gram t f) (piB t p f) hT.ggCoord :=
    ⟨langTag t, langTag_five t, rank_eq_langTag f ht, 5, S, hq, ι, hιinj, hιrange,
    hcenter, ζ, hT.ζ_order, a, ha_torus, ha_coord, ha_act, mem_roots_iff_isRoot f ht, eps p f,
    eps_cases p f, eps_dvd hreg, (fun v hv => hρ S.ρ S.frob v hv), gram_eq f ht,
    piB_diag p f ht⟩
  refine ⟨B, rfl, HEq.rfl, ?_, HEq.rfl, rfl⟩
  apply heq_of_eq
  apply MonoidHom.ext
  intro c
  exact hιeq c

theorem ggLangData_of_torusData {t : StatedLieTag} {n f p : ℕ} [NeZero p] (ht : GGExcFive t)
    (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (D : LangDatum (langTag t) GGL) (ι₀ : GGKb t n f →* ModGL (langTag t) GGL) (ζ : GGLˣ)
    (hq : D.q = 2 ^ f)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) D ι₀ ζ)
    (hρ : ∀ ρ : Equiv.Perm (Fin (langTag t).rank → ℤ), FrobRootMap D ρ →
      ∀ v ∈ (ggU (absTag t) 6 f).D.roots,
        ρ (ggLangReidx (rank_eq_langTag f ht) v) =
          eps p f • ggLangReidx (rank_eq_langTag f ht) (latPerm (piB t p f) v)) :
    Nonempty (GGLangData GGL t n f p hT.ggBfull (gram t f) (piB t p f) hT.ggCoord) := by
  obtain ⟨B, _⟩ := ggLangData_of_torusData_retained ht hf hp hp2 hreg D ι₀ ζ hq hT hρ
  exact ⟨B⟩

end LangData

end CFSG.StandardType.GGFinModel
