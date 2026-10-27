module

public import CFSG.Quasithin.EmptyFaithful.S146zUF4Data
public import CFSG.Quasithin.EmptyFaithful.S146zUF2Main
public import CFSG.Quasithin.EmptyFaithful.S146zUF3Geom
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Cen
public import CFSG.Quasithin.EmptyFaithful.S146zUF3Dict

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open CFSG.Quasithin.S153M
open scoped Pointwise commutatorElement

namespace S146zU

namespace UF4

section Pkg

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem sectionPkg (hA21 : AsA21SQTKSection) (h56 : AsB56) (S : Setting146 G T M)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {W₀ J₀ : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W₀ J₀))]
    (hZW : quasithinOmegaOneCenter T ≤ W₀) (hWJ : W₀ ≤ J₀) (hJU : J₀ ≤ uOfL22 T M)
    (hWN : mcOf T ≤ Subgroup.normalizer (W₀ : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J₀ : Set G))
    (hnt : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hWN hJN).ker)
    (hFF : IsFFModule (actH hWN hJN).range) :
    (∀ x : ↥(mcOf T), actH hWN hJN x = 1 → (x : G) ∈ pCoreOf 2 (mcOf T)) ∧
      ∃ (L₁ L₂ : Subgroup (MulAut ↥(tildeOf W₀ J₀))) (τ : MulAut ↥(tildeOf W₀ J₀)),
        PairPkg (actH hWN hJN).range L₁ L₂ τ :=
  pairPkg_of_ffSection hA21 h56 hF (S.sqtkGroup_of_isHTM S.isHTM_mcOf) hK₀.symm hsT hK₂ hK₀eq
    (commutator_conjSub_le_pCoreOf hK₁ hK₂ hsN e)
    (perm_of_conjSub hK₁ hK₂ (hK₀eq ▸ hF.K₀_normal)) e
    (hcen_of_setting S hK₁ hsT hsN hK₂ hK₀eq hK₀ e) hWN hJN
    (fun _ hx => UF3.trivial_sections S hZW hWJ hJU hWN hJN hx) hnt hFF

theorem false_of_strong_section (hA21 : AsA21SQTKSection) (h56 : AsB56) (S : Setting146 G T M)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {W₀ J₀ : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W₀ J₀))]
    (hZW : quasithinOmegaOneCenter T ≤ W₀) (hWJ : W₀ ≤ J₀) (hJU : J₀ ≤ uOfL22 T M)
    (hWN : mcOf T ≤ Subgroup.normalizer (W₀ : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J₀ : Set G))
    (hnt : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hWN hJN).ker)
    (hstrong : IsStrongFFModule (actH hWN hJN).range) : False := by
  have hel : IsElemAbelian 2 (tildeOf W₀ J₀) := Fact.out
  have hV : ∀ v : ↥(tildeOf W₀ J₀), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hel.2 v v.2)
  have hFF : IsFFModule (actH hWN hJN).range := by
    obtain ⟨A, hA, hne, hAel, hlt⟩ := hstrong
    exact ⟨A, hA, hne, hAel, hlt.le⟩
  obtain ⟨-, L₁, L₂, τ, PE⟩ := sectionPkg hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hZW hWJ hJU
    hWN hJN hnt hFF
  exact UC2.not_isStrongFFModule hV PE.twoNat PE.comm PE.ffJ_eq hstrong

theorem false_of_ff_sections (hA21 : AsA21SQTKSection) (h56 : AsB56) (S : Setting146 G T M)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G)) (hK₀ : conjClosure K₁ T ⊔ T = mcOf T)
    (hK₀eq : conjClosure K₁ T = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {J : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) J))]
    [Fact (IsElemAbelian 2 (tildeOf J (uOfL22 T M)))]
    (hZJ : quasithinOmegaOneCenter T ≤ J) (hJU : J ≤ uOfL22 T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hntE : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hZN hJN).ker)
    (hntF : ¬ (conjClosure K₁ T).subgroupOf (mcOf T) ≤ (actH hJN hUN).ker)
    (hFFE : IsFFModule (actH hZN hJN).range) (hFFF : IsFFModule (actH hJN hUN).range) :
    False := by
  have FU : Fact (IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) :=
    ⟨UF3.isElemAbelian_tildeOf_of_le S _ le_rfl⟩
  obtain ⟨hkE, L₁, L₂, τ, PE⟩ := sectionPkg hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF le_rfl hZJ
    hJU hZN hJN hntE hFFE
  obtain ⟨hkF, L₁', L₂', τ', PF⟩ := sectionPkg hA21 h56 S hK₁ hK₂ hsT hsN hK₀ hK₀eq e hF hZJ hJU
    le_rfl hJN hUN hntF hFFF
  obtain ⟨ι, q, hι, hq, hexact, hιρ, hqρ⟩ := UF3.sectionSeq_of_setting S hZJ hJU hZN hJN hUN
  have hV : ∀ {W₀ J₀ : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W₀ J₀))],
      ∀ v : ↥(tildeOf W₀ J₀), v ^ 2 = 1 := fun {W₀ J₀} _ v =>
    Subtype.ext (by simpa using (Fact.out : IsElemAbelian 2 (tildeOf W₀ J₀)).2 v v.2)
  exact module_claim_false hV hV hV (actH hZN hUN) (actH hZN hJN) (actH hJN hUN) ι hι q hq hexact
    hιρ hqρ (fun g hg => UF3.actH_Z_U_eq_one_of_section S hZN hJN hZN hUN hkE g hg)
    (fun g hg => UF3.actH_Z_U_eq_one_of_section S hJN hUN hZN hUN hkF g hg) PE PF
    (UF3.hgeom_of_UE S hZN hUN)

end Pkg

end UF4

end S146zU

end CFSG.Quasithin
