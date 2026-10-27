module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Sec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5C1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Hom
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5GLY
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5E2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Y2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Y3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem case2_condD (hC : Ch.Ctx H M S)
    (hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β))
    (h15c : Claim15c H M) (h6a : Claim6a H M) (h6b : Claim6b H M)
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hgen : stab β ≤ Wb δ ⊔ Wb γ ⊔ Qv β) (hcomm : ⁅Vn δ, Vn γ⁆ = ⊥) :
    ∃ δ'' : Geo H M, δ'' ∈ nbrs l ∧ δ'' ≠ β ∧ δ'' ≠ δ ∧ Vn δ'' ≤ Vn β ⊔ Vn δ := by
  have hβ := hcfg.vβ
  obtain ⟨hYW, hYc⟩ := Y_card hC hcfg hcomm
  have hVY : Vn β ≤ Yg β δ γ := le_sup_right
  have hYW' : Yg β δ γ ≤ Wb β := sup_le hYW (Vn_le_Wb_self hC.sit hβ)
  have hidx := relIndex_normalizer_Y_le_four hC h15c hcfg hgen hcomm
  obtain ⟨hq⟩ := quot_stab_five hC.sit.glob.amalg hβ
  have hL : Lr β ≤ Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) ⊓ stab β :=
    oTwoRes_le_of_relIndex_le_four ⟨hq⟩ inf_le_right hidx
  by_cases hYL : ⁅Yg β δ γ, Lr β⁆ ≤ Vn β
  · exact (six_b_contra hC h6b hcfg hYL).elim
  · have hK := comm_Q_of_not_comm_aux hC.sit hβ hVY hYW' (hsec β hβ) hYc
      (fun F _ _ hF φ => hom_trivial_of_coprime_five ⟨hq⟩ hF φ) (hL.trans inf_le_left) hYL
    exact condD_of_comm hC h6a hcfg hK

theorem claim13_core (hC : Ch.Ctx H M S) (h10 : Claim10 H M) (h11 : Claim11 H M)
    (h15c : Claim15c H M) (hclaimR : ClaimR H M) (h6a : Claim6a H M) (h6b : Claim6b H M) :
    Claim13 H M := by
  intro hb
  have hS := hC.sit
  have hsec := wb_isSec hS h15c
  obtain ⟨β, α', hLam⟩ := h10.1
  have hp : S34.PD β α' := hLam.1
  obtain ⟨m, γ, hm, hγm, h1, h2⟩ := exists_geodesic hS hp.dist_eq
  have hback : Back H M β α' m γ := ⟨hm, hγm, h1, h2⟩
  have hd4 : dist β α' = 4 := by have := hp.dist_eq; omega
  have hvm : vtype m = true := vtype_nbr_S5 hp.vδ' hm
  have hvγ : vtype γ = false := vtype_nbr_S3 hvm hγm
  have hdγ : dist γ β = 2 := by rw [CosetGeom.dist_comm]; omega
  obtain ⟨l0, hl0, hγl0, hγne⟩ := dist_eq_two_iff.mp hdγ
  have hdα : dist α' γ = 2 := by
    have h3 := dist_triangle rfl β γ α'
    have h5 := dist_triangle rfl γ m α'
    have h6 : dist γ m = 1 := dist_eq_one_iff_adj.mpr (mem_nbrs_symm.mp hγm)
    have h7 : dist m α' = 1 := dist_eq_one_iff_adj.mpr (mem_nbrs_symm.mp hm)
    have h8 : dist β γ = 2 := by rw [CosetGeom.dist_comm]; exact hdγ
    rw [CosetGeom.dist_comm α' γ]
    omega
  have hW : ¬ Wb γ ≤ Lr β ⊔ Qv β := fun hle => h11 β α' hLam ((Vn_le_Wb hdα).trans hle)
  obtain ⟨l, hl, δ, hδ, hδβ, hgen⟩ := exists_gen hC hp.vδ hl0 hγl0 hγne hW
  have hcfg : Cfg H M β l δ l0 γ := ⟨hp.vδ, hl, hδ, hδβ, hl0, hγl0, hγne⟩
  by_cases hcomm : ⁅Vn δ, Vn γ⁆ = ⊥
  · obtain ⟨δ'', h1, h2, h3, h4⟩ := case2_condD hC hsec h15c h6a h6b hcfg hgen hcomm
    exact condD_false hC hclaimR hb (condD_of_arc hS hp.vδ hl (mem_nbrs_symm.mp hδ)
      (mem_nbrs_symm.mp h1) hδβ h2 h3 h4) hp hback
  · exact case1_false hC hsec hcfg hgen hcomm

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
