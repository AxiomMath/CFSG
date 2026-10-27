module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C
public import CFSG.Quasithin.EmptyFaithful.S14113Case
public import CFSG.Quasithin.EmptyFaithful.S14113Layer

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem layer_le_of_forall_le {M H : Subgroup G} (hcharM : CharTwo M)
    (hK : ∀ K : Subgroup G, K ∈ cComp M → CharTwo K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → K ≤ H) :
    CFSG.layer (OTwoQuot M) ≤ imageOTwoQuot M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (CFSG.Open.pCore 2 ↥M) := by
    have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥M) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥M) := hp.isNilpotent
    infer_instance
  simp only [CFSG.layer.eq_sSup]
  refine sSup_le fun Y hY => ?_
  have hYc : Y ∈ cComp (⊤ : Subgroup (OTwoQuot M)) := mem_cComp_top_of_isComponent hY
  obtain ⟨L', hL', hLY⟩ := (cComp_quotient_bijOn (CFSG.Open.pCore 2 ↥M) hsolv).surjOn hYc
  subst hLY
  have hL : L'.map M.subtype ∈ cComp M := map_subtype_mem_cComp hL'
  have hLc : CharTwo (L'.map M.subtype) :=
    charTwo_of_isSubnormal_of_charTwo hcharM (subnormal_of_mem_cComp hL)
  have hLq := isQuasisimple_pCore_quotient rfl hY.1 (subnormal_of_mem_cComp hL)
  have hLH : L'.map M.subtype ≤ H := hK _ hL hLc hLq
  have hle : L' ≤ H.subgroupOf M := fun x hx => hLH ⟨x, hx, rfl⟩
  exact Subgroup.map_mono hle

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem oTwoFstarIn_M_not_le : ¬ oTwoFstarIn M ≤ H := fun hFs => by
  apply s.ne
  refine a4_4_3 (pCoreOf_le_oTwoFstarIn H) (le_inf (oTwoFstarIn_le H) s.le)
    (a44Hyp_oTwoFstarIn H) s.inM.1 s.hyp.maxTwoLocal ?_
  rwa [map_O2Fstar_eq_oTwoFstarIn]

theorem exists_K (c : Inp425 G) :
    ∃ K : Subgroup G, K ∈ cComp M ∧ CharTwo K ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ H := by
  by_contra hno
  push Not at hno
  have hOH : pCoreOf 2 M ≤ H := s.pCoreOf_M_le.trans ((pCoreOf_le 2 _).trans inf_le_left)
  have hgen : CFSG.generalizedFitting (OTwoQuot M) ≤ imageOTwoQuot M H :=
    sup_le (fitting_le_imageOTwoQuot (s.lemma_4_2_9 c)) (layer_le_of_forall_le s.charTwo_M hno)
  apply s.oTwoFstarIn_M_not_le
  rw [← map_O2Fstar_eq_oTwoFstarIn]
  rintro _ ⟨z, hz, rfl⟩
  exact mem_of_mk_mem_imageOTwoQuot hOH (hgen hz)

end Set425

end CFSG.Quasithin.H13.Ch4
