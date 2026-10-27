module

public import CFSG.Quasithin.EmptyFaithful.S146zDPartI

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section SymCore

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem sym_core (S : Setting146 G T M) (c19 : Conc14619 T M) (c23 : Conc14623 T M)
    {Ko Kop Kn Knp U₁ U₂ V₁ V₂ : Subgroup G} {s t : G}
    (cKo : ThreeC.CCtx T M Ko U₁ U₂ s) (cKn : ThreeC.CCtx T M Kn V₁ V₂ t)
    (hKop : Kop ∈ cComp (mcOf T)) (hKnp : Knp ∈ cComp (mcOf T)) (hneo : Kop ≠ Ko)
    (hcompso : ∀ L ∈ cComp (mcOf T), L = Ko ∨ L = Kop)
    (hcompsn : ∀ L ∈ cComp (mcOf T), L = Kn ∨ L = Knp)
    (hkzo : perfectCore (mcOf T) = Ko ⊔ Kop) (hkzn : perfectCore (mcOf T) = Kn ⊔ Knp)
    (hc22o₁ : ⁅⁅uOfL22 T M, Ko⁆, Kop⁆ = ⊥) (hc22o₂ : ⁅⁅uOfL22 T M, Kop⁆, Ko⁆ = ⊥)
    (hc22n₁ : ⁅⁅uOfL22 T M, Kn⁆, Knp⁆ = ⊥) (hc22n₂ : ⁅⁅uOfL22 T M, Knp⁆, Kn⁆ = ⊥)
    {g k y : G} {E A₁ A₁' : Subgroup G} (hE : E = conjSub g (uOfL22 T M))
    (hA₁ : A₁ = conjSub g Zz) (hA₁' : A₁' = conjSub k Zz)
    (hEH : E ≤ mcOf T) (hEab : IsElemAbelian 2 E)
    (hEKo : E ≤ Subgroup.normalizer (Ko : Set G)) (hEKop : E ≤ Subgroup.normalizer (Kop : Set G))
    (hA₁c : Nat.card A₁ = 2) (hA₁Z : A₁ ⊓ Zz = ⊥) (hA₁UK : A₁ ≤ U₁ ⊔ U₂)
    (hnt : ¬ E ≤ centralizerMod Zz E (U₁ ⊔ U₂))
    (hA₁'c : Nat.card A₁' = 2) (hA₁'Z : A₁' ⊓ Zz = ⊥) (hA₁'UK : A₁' ≤ V₁ ⊔ V₂)
    (hy1 : y * g ∈ mcOf T) (hy2 : k⁻¹ * y ∈ mcOf T) : False := by
  classical
  obtain ⟨hKopg, hperfo⟩ := partI S c23 cKo hKop hcompso hkzo hc22o₁ hc22o₂ hA₁ hA₁c hA₁Z hA₁UK
  obtain ⟨hKnpk, hperfn⟩ := partI S c23 cKn hKnp hcompsn hkzn hc22n₁ hc22n₂ hA₁' hA₁'c hA₁'Z hA₁'UK
  have hKopH : Kop ≤ mcOf T := le_of_mem_cComp hKop
  have hKnpH : Knp ≤ mcOf T := le_of_mem_cComp hKnp
  have hconj1 : conjSub y (conjSub g (mcOf T)) = mcOf T := by
    rw [← conjSub_mul]; exact conjSub_eq_of_mem hy1
  have hconj2 : conjSub y (mcOf T) = conjSub k (mcOf T) := by
    have e : y = k * (k⁻¹ * y) := by group
    rw [e, conjSub_mul, conjSub_eq_of_mem hy2]
  have hconj3 : conjSub y⁻¹ (mcOf T) = conjSub g (mcOf T) := by
    have := congrArg (conjSub y⁻¹) hconj1
    rw [conjSub_conjSub_inv] at this
    exact this.symm
  set L : Subgroup G := conjSub y⁻¹ Knp with hL
  have hLperf : ⁅L, L⁆ = L := by
    rw [hL, conjSub_commutator, perfect_of_mem_cComp hKnp]
  have hLH : L ≤ mcOf T := by
    have h1 := conjSub_mono y⁻¹ hKnpk
    have h2 : conjSub y⁻¹ (conjSub k (mcOf T)) = mcOf T := by
      rw [← hconj2, conjSub_conjSub_inv]
    rw [h2] at h1
    exact h1
  have hLHg : L ≤ conjSub g (mcOf T) := by
    rw [← hconj3]; exact conjSub_mono y⁻¹ hKnpH
  have hL_le : L ≤ Kop := hperfo L hLH hLperf hLHg
  set P : Subgroup G := conjSub y Kop with hP
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, conjSub_commutator, perfect_of_mem_cComp hKop]
  have hPH : P ≤ mcOf T := by
    have h1 := conjSub_mono y hKopg
    rw [hconj1] at h1
    exact h1
  have hPHk : P ≤ conjSub k (mcOf T) := by
    rw [← hconj2]; exact conjSub_mono y hKopH
  have hP_le : P ≤ Knp := hperfn P hPH hPperf hPHk
  have hKop_le : Kop ≤ L := by
    have h1 := conjSub_mono y⁻¹ hP_le
    rw [hP, conjSub_conjSub_inv] at h1
    exact h1
  have hEq : Kop = L := le_antisymm hKop_le hL_le
  have hLc : L ∈ cComp (conjSub g (mcOf T)) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj y⁻¹) hKnp
    have e1 : (mcOf T).map (MulAut.conj y⁻¹).toMonoidHom = conjSub g (mcOf T) := hconj3
    rw [e1] at h1
    exact h1
  exact engine S c19 cKo hKop hneo hcompso hE hA₁ hEH hEab hEKo hEKop hA₁c hA₁Z hA₁UK hnt
    (hEq ▸ hLc)

end SymCore

section Nontriv

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem datum_nontriv (S : Setting146 G T M) (c23 : Conc14623 T M)
    {Ko Kop U₁ U₂ V₁ V₂ : Subgroup G} {s t : G} (cKo : ThreeC.CCtx T M Ko U₁ U₂ s)
    (cKop : ThreeC.CCtx T M Kop V₁ V₂ t)
    (hKop : Kop ∈ cComp (mcOf T)) (hcompso : ∀ L ∈ cComp (mcOf T), L = Ko ∨ L = Kop)
    (hkzo : perfectCore (mcOf T) = Ko ⊔ Kop)
    (hc22o₁ : ⁅⁅uOfL22 T M, Ko⁆, Kop⁆ = ⊥) (hc22o₂ : ⁅⁅uOfL22 T M, Kop⁆, Ko⁆ = ⊥)
    {g : G} {E A₁ : Subgroup G} (hE : E = conjSub g (uOfL22 T M))
    (hA₁ : A₁ = conjSub g Zz) (hA₁c : Nat.card A₁ = 2) (hA₁Z : A₁ ⊓ Zz = ⊥)
    (hA₁UK : A₁ ≤ U₁ ⊔ U₂) (hEH : E ≤ mcOf T) (hEab : IsElemAbelian 2 E)
    (hEKop : E ≤ Subgroup.normalizer (Kop : Set G))
    (hntU : ¬ E ≤ centralizerMod Zz E (uOfL22 T M)) :
    ¬ E ≤ centralizerMod Zz E (U₁ ⊔ U₂) := by
  classical
  intro h
  apply hntU
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUc : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab hx hy
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hEp : IsPGroup 2 E := isPGroup_of_isElemAbelian hEab
  have hEZ : E ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hEH he
  obtain ⟨hKopg, -⟩ := partI S c23 cKo hKop hcompso hkzo hc22o₁ hc22o₂ hA₁ hA₁c hA₁Z hA₁UK
  have hKopE : Kop ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact hKopg.trans (conjSub_le_normalizer hHU)
  have htrivp : ∀ e ∈ E, ∀ y ∈ V₁ ⊔ V₂, e * y * e⁻¹ * y⁻¹ ∈ Zz := fun e he y hy =>
    cKop.trivial_of_centralizes S (hEKop he) (le_normalizer_conjClosure _ _ (hEH he)) (hEZ he)
      (fun k hk => comm_mem_pCoreOf_of_mutual hEp hEKop hKopE e he k hk) y hy
  intro e he
  refine ⟨he, hEZ he, fun u hu => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_decomp_two S c23 hcompso cKo.hKc hKop hu
  have hEU : ∀ x ∈ uOfL22 T M, e * x * e⁻¹ ∈ uOfL22 T M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHU (hEH he)) x).mp hx
  have haU : a ∈ uOfL22 T M := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp cKo.hKc) ha
  have hbU : b ∈ uOfL22 T M := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKop) hb
  have hcU : c ∈ uOfL22 T M := cuOf_le T M hc
  have hbcU : b * c ∈ uOfL22 T M := (uOfL22 T M).mul_mem hbU hcU
  have hexp : e * (a * (b * c)) * e⁻¹ * (a * (b * c))⁻¹ =
      (e * a * e⁻¹ * a⁻¹) * ((e * b * e⁻¹ * b⁻¹) * (e * c * e⁻¹ * c⁻¹)) := by
    rw [comm_mul_of_abelian hUc hEU haU hbcU, comm_mul_of_abelian hUc hEU hbU hcU]
  rw [hexp]
  have h1 : e * a * e⁻¹ * a⁻¹ ∈ Zz := (h he).2.2 a (cKo.hsup ▸ ha)
  have h2 : e * b * e⁻¹ * b⁻¹ ∈ Zz := htrivp e he b (cKop.hsup ▸ hb)
  have h3 : e * c * e⁻¹ * c⁻¹ ∈ Zz := by
    have := (mem_cuOf.mp hc).2.2 e (hEH he)
    have e1 : e * c * e⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹)⁻¹ := by group
    rw [e1]; exact Subgroup.inv_mem _ this
  exact Subgroup.mul_mem _ h1 (Subgroup.mul_mem _ h2 h3)

end Nontriv

end CFSG.Quasithin.ThreeD
