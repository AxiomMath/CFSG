module

public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.WeakClosure81.W19Struct
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem normalizer_le_of_comm_eq_bot (c : MinCex193 D V₀ V p X) (hVX : ⁅V, X⁆ = ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hU : U ≠ ⊥) : normalizer (U : Set G) ≤ D.M := by
  have hXc : X ≤ Subgroup.centralizer (U : Set G) :=
    (Subgroup.le_centralizer_iff).mpr (hUV.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVX))
  have hXU : X ≤ normalizer (U : Set G) :=
    hXc.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hU2 : IsPGroup 2 U := c.isPGroup_V.to_le hUV
  exact normalizer_le_of_uniqueMax (c.hyp.uniqueMax X le_rfl c.hyp.noncyclic) hU hU2 hXU

theorem inf_conj_eq_bot_of_comm_eq_bot (c : MinCex193 D V₀ V p X) (hVX : ⁅V, X⁆ = ⊥)
    {y : G} (hy : y ∉ D.M) (hV₀y : V₀ ≤ conjSubgroup D.M y) :
    V ⊓ conjSubgroup V y = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  by_contra hw1
  have hwV : w ∈ V := (Subgroup.mem_inf.1 hw).1
  have hwy : w ∈ conjSubgroup V y := (Subgroup.mem_inf.1 hw).2
  have hw'V : y * w * y⁻¹ ∈ V := (mem_conjSubgroup_iff).1 hwy
  have hw'1 : y * w * y⁻¹ ≠ 1 := by
    intro h
    apply hw1
    calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
      _ = y⁻¹ * 1 * y := by rw [h]
      _ = 1 := by group
  have hU : Subgroup.zpowers (y * w * y⁻¹) ≠ ⊥ :=
    Subgroup.zpowers_ne_bot.mpr hw'1
  have hUle : Subgroup.zpowers (y * w * y⁻¹) ≤ V :=
    Subgroup.zpowers_le.mpr hw'V
  have hN : normalizer (Subgroup.zpowers (y * w * y⁻¹) : Set G) ≤ D.M :=
    c.normalizer_le_of_comm_eq_bot hVX hUle hU
  have hcen' : Subgroup.centralizer ({y * w * y⁻¹} : Set G) ≤ D.M := by
    have hle : Subgroup.centralizer ({y * w * y⁻¹} : Set G) ≤
        normalizer (Subgroup.zpowers (y * w * y⁻¹) : Set G) := by
      intro z hz
      rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hz
      exact Subgroup.centralizer_le_normalizer _ hz
    exact hle.trans hN
  have hconjXw : ∀ x ∈ X, y * x * y⁻¹ ∈
      Subgroup.centralizer ({y * w * y⁻¹} : Set G) := by
    have hXV : X ≤ Subgroup.centralizer (V : Set G) :=
      (Subgroup.le_centralizer_iff).mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVX)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hxw : w * x = x * w := Subgroup.mem_centralizer_iff.1 (hXV hx) w hwV
    calc (y * w * y⁻¹) * (y * x * y⁻¹) = y * (w * x) * y⁻¹ := by group
      _ = y * (x * w) * y⁻¹ := by rw [hxw]
      _ = (y * x * y⁻¹) * (y * w * y⁻¹) := by group
  have hXconj : X ≤ conjSubgroup D.M y := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    exact hcen' (hconjXw x hx)
  have hbot : X ⊓ conjSubgroup D.M y = ⊥ := c.hyp.inf_eq_bot y hy hV₀y
  have hXbot : X ≤ ⊥ := by
    rw [← hbot]
    exact le_inf le_rfl hXconj
  exact c.hyp.noncyclic (le_bot_iff.mp hXbot ▸ Bot.isCyclic)

theorem exists_conj_le_T_comm_ne_bot (c : MinCex193 D V₀ V p X) :
    ∃ h : G, conjSubgroup V h ≤ D.T ∧ ⁅conjSubgroup V h, V⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  let Q : Subgroup G := D.T ⊓ Subgroup.centralizer (V : Set G)
  have hCT : Subgroup.centralizer (V : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (V : Set G)).trans (le_of_eq c.setting.normalizer_eq)
  have hMC : D.M ≤ normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer]
    have hVm : conjSubgroup V m = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (c.setting.pair.le_normalizer hm)
    rw [hVm]
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (D.M ⊓ Subgroup.centralizer (V : Set G)) := by
    have h := D.sylowM.inf_of_le_normalizer hCT hMC
    rw [inf_eq_right.mpr hCT]
    exact h
  have hgamma : E3.gammaSet V 0 D.T = E3.gammaSet V 0 Q := by
    ext A
    constructor
    · intro hA
      rw [E3.mem_gammaSet_iff] at hA ⊢
      obtain ⟨hAT, g, hAg, hmq⟩ := hA
      have hVg2 : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup c.isPGroup_V g
      have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg2 hAg).1 hmq
      have hAgT : conjSubgroup V g ≤ D.T := by
        rw [← hAeq]
        exact hAT
      have hcomm : ⁅conjSubgroup V g, V⁆ = ⊥ := hcon g hAgT
      have hAc : A ≤ Subgroup.centralizer (V : Set G) := by
        rw [hAeq]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact ⟨le_inf hAT hAc, g, hAg, hmq⟩
    · intro hA
      rw [E3.mem_gammaSet_iff] at hA ⊢
      exact ⟨hA.1.trans inf_le_left, hA.2⟩
  have hwClos : E3.wClos V 0 D.T = E3.wClos V 0 Q := by
    unfold E3.wClos
    rw [hgamma]
  have hVab : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.2 c.setting.isElemAbelian.1
  have hVQ : V ≤ Q := le_inf c.V_le_T hVab
  have hVmem : V ∈ E3.gammaSet V 0 Q := by
    rw [E3.mem_gammaSet_iff]
    refine ⟨hVQ, 1, ?_, ?_⟩
    · rw [conjSubgroup_one]
    · rw [conjSubgroup_one, E3.mQuot_self]
  have hVw : V ≤ E3.wClos V 0 Q := E3.le_wClos hVmem
  have hVne : V ≠ ⊥ := by
    intro hbot
    exact c.ne_bot (le_bot_iff.mp (c.V₀_le_V.trans (le_of_eq hbot)))
  have hWne : E3.wClos V 0 Q ≠ ⊥ := by
    intro hbot
    exact hVne (le_bot_iff.mp (hVw.trans (le_of_eq hbot)))
  have hW2 : IsPGroup 2 (E3.wClos V 0 Q) :=
    D.sylowM.isPGroup.to_le ((E3.wClos_le 0 Q).trans inf_le_left)
  have hXD : D.M ⊓ normalizer (Q : Set G) ≤ normalizer (E3.wClos V 0 Q : Set G) :=
    (inf_le_right : D.M ⊓ normalizer (Q : Set G) ≤ normalizer (Q : Set G)).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) Q)
  have hM : normalizer (E3.wClos V 0 Q : Set G) ≤ D.M :=
    normalizer_le_of_uniqueMax (c.setting.v1 Q hQ) hWne hW2 hXD
  rw [← hwClos] at hM
  exact c.fail (Or.inl hM)

private theorem exists_conj_data_of_comm_eq_bot (c : MinCex193 D V₀ V p X)
    (hVX : ⁅V, X⁆ = ⊥) :
    ∃ (y : G) (D' : Subgroup G), V ≤ normalizer (D' : Set G) ∧ y ∉ D.M ∧
      V₀ ≤ conjSubgroup D.M y ∧ D' = conjSubgroup V y ∧ ¬ D' ≤ D.M := by
  obtain ⟨h, hAhT, hAcomm⟩ := c.exists_conj_le_T_comm_ne_bot
  let y : G := h⁻¹
  let D' : Subgroup G := conjSubgroup V y
  have hVnormD' : V ≤ normalizer (D' : Set G) := by
    have h1 : conjSubgroup (conjSubgroup V h) h⁻¹ ≤ conjSubgroup D.M h⁻¹ :=
      E3.conjSubgroup_mono_left h⁻¹ (hAhT.trans D.sylowM.le)
    rw [E3.conjSubgroup_conj_inv] at h1
    have hD'M : conjSubgroup D.M h⁻¹ = normalizer (D' : Set G) := by
      rw [show D' = conjSubgroup V h⁻¹ from rfl,
        show D.M = normalizer (V : Set G) from c.setting.normalizer_eq.symm,
        E3.conjSubgroup_normalizer]
    rwa [hD'M] at h1
  have hneBot : ⁅V, D'⁆ ≠ ⊥ := by
    intro hbot
    change ⁅V, conjSubgroup V h⁻¹⁆ = ⊥ at hbot
    apply hAcomm
    have h2 := congrArg (fun W => conjSubgroup W h) hbot
    rw [E3.conjSubgroup_commutator, E3.conjSubgroup_inv_conj,
      E3.conjSubgroup_bot] at h2
    exact h2
  have hy : y ∉ D.M := by
    intro hyM
    have hhM : h ∈ D.M := by
      have := D.M.inv_mem hyM
      simpa [y] using this
    apply hAcomm
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr (c.setting.pair.le_normalizer hhM)]
    exact Subgroup.commutator_self_eq_bot_iff.mpr c.setting.isElemAbelian.1
  have hD'norm : normalizer (D' : Set G) = conjSubgroup D.M y := by
    rw [show D' = conjSubgroup V y from rfl, ← E3.conjSubgroup_normalizer,
      ← c.setting.normalizer_eq]
  have hV₀y : V₀ ≤ conjSubgroup D.M y := c.V₀_le_V.trans (hVnormD'.trans (le_of_eq hD'norm))
  have hInter : V ⊓ D' = ⊥ := c.inf_conj_eq_bot_of_comm_eq_bot hVX hy hV₀y
  have hnotLe : ¬ D' ≤ D.M := by
    intro hD'M
    have hcomm : ⁅V, D'⁆ ≤ V ⊓ D' := by
      refine Subgroup.commutator_le.2 fun v hv d hd => Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have hdN : d ∈ normalizer (V : Set G) := c.setting.pair.le_normalizer (hD'M hd)
        have h1 : d * v⁻¹ * d⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 hdN v⁻¹).1 (Subgroup.inv_mem _ hv)
        have e : v * d * v⁻¹ * d⁻¹ = v * (d * v⁻¹ * d⁻¹) := by group
        rw [e]
        exact V.mul_mem hv h1
      · rw [commutatorElement_def]
        have hvN : v ∈ normalizer (D' : Set G) := hVnormD' hv
        exact D'.mul_mem ((Subgroup.mem_normalizer_iff.1 hvN d).1 hd) (D'.inv_mem hd)
    rw [hInter] at hcomm
    exact hneBot (le_bot_iff.mp hcomm)
  exact ⟨y, D', hVnormD', hy, hV₀y, rfl, hnotLe⟩

private theorem false_of_conj_data (c : MinCex193 D V₀ V p X) (hVX : ⁅V, X⁆ = ⊥)
    {y : G} {D' : Subgroup G} (hVnormD' : V ≤ normalizer (D' : Set G))
    (hy : y ∉ D.M) (hV₀y : V₀ ≤ conjSubgroup D.M y)
    (hD'eq : D' = conjSubgroup V y) (hnotLe : ¬ D' ≤ D.M) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hInter : V ⊓ D' = ⊥ := by
    rw [hD'eq]
    exact c.inf_conj_eq_bot_of_comm_eq_bot hVX hy hV₀y
  have hD'2 : IsPGroup 2 D' := by
    rw [hD'eq]
    exact E3.isPGroup_conjSubgroup c.isPGroup_V y
  let S : Subgroup G := V ⊔ D'
  have hS2 : IsPGroup 2 S :=
    c.isPGroup_V.to_sup_of_normal_right' hD'2 hVnormD'
  have hpermD' : (V : Set G) * (D' : Set G) = (D' : Set G) * (V : Set G) :=
    Subgroup.set_mul_normalizer_comm (V : Set G) D' hVnormD'
  have hcardS : Nat.card ↥S = Nat.card ↥V * Nat.card ↥V := by
    rw [show S = V ⊔ D' from rfl, W19Aux.card_sup_of_perm hInter hpermD']
    have hD'c : Nat.card ↥D' = Nat.card ↥V := by
      rw [hD'eq, E3.card_conjSubgroup]
    rw [hD'c]
  let P : Subgroup G := S ⊓ D.M
  have hPS : P ≤ S := inf_le_left
  have hPne : P ≠ S := by
    intro hEq
    have hD'P : D' ≤ P := by
      rw [hEq]
      exact le_sup_right
    exact hnotLe (hD'P.trans inf_le_right)
  have hPlt : P.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPne ?_
    exact le_antisymm hPS (Subgroup.subgroupOf_eq_top.mp htop)
  haveI hSnil : Group.IsNilpotent ↥S := hS2.isNilpotent
  have hgrow : P.subgroupOf S < Subgroup.normalizer (P.subgroupOf S) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥S) _ hPlt
  obtain ⟨n, hnN, hnP⟩ := SetLike.exists_of_lt hgrow
  have hnN' : (n : G) ∈ normalizer (P : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPS, Subgroup.mem_subgroupOf] at hnN
    exact hnN
  have hnP' : (n : G) ∉ P := fun hn => hnP (Subgroup.mem_subgroupOf.2 hn)
  have hnM : (n : G) ∉ D.M := fun hn =>
    hnP' (Subgroup.mem_inf.2 ⟨n.2, hn⟩)
  have hnormalP : conjSubgroup P n = P :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hnN'
  let Vn : Subgroup G := conjSubgroup V n
  have hVleP : V ≤ P := le_inf le_sup_left c.V_le_M
  have hVnleP : Vn ≤ P := by
    have h1 : conjSubgroup V n ≤ conjSubgroup P n :=
      E3.conjSubgroup_mono_left (G := G) (n : G) hVleP
    rw [hnormalP] at h1
    exact h1
  have hPleConjM : P ≤ conjSubgroup D.M n := by
    have h1 : conjSubgroup P n ≤ conjSubgroup D.M n :=
      E3.conjSubgroup_mono_left (G := G) (n : G) (inf_le_right : P ≤ D.M)
    rwa [hnormalP] at h1
  have hVnNorm : V ≤ normalizer (Vn : Set G) := by
    have h1 : V ≤ conjSubgroup D.M n := hVleP.trans hPleConjM
    have hconj : conjSubgroup D.M n = normalizer (conjSubgroup V n : Set G) := by
      rw [show D.M = normalizer (V : Set G) from c.setting.normalizer_eq.symm,
        E3.conjSubgroup_normalizer]
    rw [hconj] at h1
    exact h1
  have hV₀n : V₀ ≤ conjSubgroup D.M n := c.V₀_le_V.trans (hVleP.trans hPleConjM)
  have hInterVn : V ⊓ Vn = ⊥ := c.inf_conj_eq_bot_of_comm_eq_bot hVX hnM hV₀n
  have hpermVn : (V : Set G) * (Vn : Set G) = (Vn : Set G) * (V : Set G) :=
    Subgroup.set_mul_normalizer_comm (V : Set G) Vn hVnNorm
  have hcardVn : Nat.card ↥(V ⊔ Vn) = Nat.card ↥V * Nat.card ↥V := by
    rw [W19Aux.card_sup_of_perm hInterVn hpermVn]
    have hVnc : Nat.card ↥Vn = Nat.card ↥V := by
      rw [show Vn = conjSubgroup V n from rfl, E3.card_conjSubgroup]
    rw [hVnc]
  have hVPVn : V ⊔ Vn ≤ P := sup_le hVleP hVnleP
  have hPStrict : P < S := lt_of_le_of_ne hPS hPne
  have hlt : Nat.card ↥(V ⊔ Vn) < Nat.card ↥S :=
    Subgroup.card_lt_of_lt (lt_of_le_of_lt hVPVn hPStrict)
  rw [hcardVn, hcardS] at hlt
  exact (lt_irrefl (Nat.card ↥V * Nat.card ↥V)) hlt

theorem commutator_ne_bot (c : MinCex193 D V₀ V p X) : ⁅V, X⁆ ≠ ⊥ := by
  intro hVX
  obtain ⟨y, D', hVnormD', hy, hV₀y, hD'eq, hnotLe⟩ :=
    exists_conj_data_of_comm_eq_bot c hVX
  exact false_of_conj_data c hVX hVnormD' hy hV₀y hD'eq hnotLe

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
