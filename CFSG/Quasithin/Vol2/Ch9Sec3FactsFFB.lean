module

public import CFSG.Quasithin.Vol2.Ch9Sec3FFBCmp
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBRank

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem a314FFFact_of_quasisimple
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56)
    {G : Type} [Group G] [Finite G] {Y T K KY V : Subgroup G} (hSQ : SQTKGroup ↥Y)
    (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y) (hKl : K ∈ lFamily T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y V)
    (hJ : ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G))
    (hqKY : CFSG.IsQuasisimple (O2Q KY)) :
    IsSL3 4 (O2Q KY) ∨ IsPSp4 2 2 (O2Q KY) ∨ IsG2 2 2 (O2Q KY) ∨ IsAlt 7 ↥(autOn KY V) := by
  have : IsMulCommutative ↥V := hred.2.2.1.1
  obtain ⟨hlt', h314bar⟩ := FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA5 hKYc hlt
  obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
  obtain ⟨hqA, hlist, h60, π, hπ⟩ := FFB.autOn_facts h56 hSQ hT hlt.le hKYc hYKY hred
    (perfect_of_mem_cComp hKl) hA5 hJ hqKY
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hqKY
  have hqL : CFSG.IsQuasisimple ↥(modO2Image Y KY) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqKY
  set π' : ↥(modO2Image Y KY) →* ↥(autOn KY V) := π.comp e.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπ.comp e.symm.surjective
  have hne : π'.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπ's a
    obtain ⟨y, rfl⟩ := hπ's b
    have hx : x ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  have hker : π'.ker ≤ Subgroup.center ↥(modO2Image Y KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqL inferInstance).resolve_left hne
  have hc : FFB.CmpHyp (modO2Image Y KY) ↥(autOn KY V) :=
    { quasi := hqL
      center_odd := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact hodd
      map := ⟨π', hπ's, hker, hne⟩
      list := hlist
      quasiX := hqA
      dvd60 := h60 }
  rcases hc.cmp h314 h314bar hlt' with hL | hL | hL | hA7
  · exact Or.inl (IsSL3.of_mulEquiv e.symm hL)
  · exact Or.inr (Or.inl (IsPSp4.of_mulEquiv e.symm hL))
  · exact Or.inr (Or.inr (Or.inl (IsG2.of_mulEquiv e.symm hL)))
  · exact Or.inr (Or.inr (Or.inr hA7))

theorem a314FFFactE9_holds
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56) :
    A314FFFactE9 := by
  intro G _ _ Y T K KY V hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ
    ⟨a, haK, b, hbK, hab, ha, hb, ha1, hba⟩
  exact a314FFFact_of_quasisimple h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ
    (FFB.isQuasisimple_o2q h36 hSQ hKYc hYKY haK hbK hab ha hb ha1 hba)

end CFSG.Quasithin.H13.Ch9
