module

public import CFSG.Quasithin.Vol2.Ch3Sec3Cor332
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_mem_centralizer_of_le {T W : Subgroup G} (hT : IsPGroup 2 T) (hWT : W ≤ T)
    (hWn : T ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    ∃ z ∈ W, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (W.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWn
  have hne : W.subgroupOf T ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem sup_le_normalizer_reducedAggregate :
    L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
  rw [← c.omega_eq]
  exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)

theorem sup_le_normalizer_V :
    L ⊔ T ≤ Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  have hLN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.sup_le.trans c.normal
  exact fun x hx => mem_normalizer_commutator (c.sup_le_normalizer_reducedAggregate hx) (hLN hx)

theorem V_eq_commutator :
    ⁅reducedAggregate (L ⊔ T), L⁆ = ⁅⁅reducedAggregate (L ⊔ T), L⁆, L⁆ := by
  have hRL : reducedAggregate (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) :=
    ((reducedAggregate_le_omegaOneCenterOf_pCoreOf _).trans
      ((omegaOneCenterOf_le _).trans (pCoreOf_le 2 _))).trans (c.hyp421.sup_le.trans c.normal)
  exact commutator_eq_commutator_commutator_of_perfect c.hyp421.perfect hRL
    (le_sup_left.trans c.sup_le_normalizer_reducedAggregate)

theorem commutator_V_ne_bot : ⁅⁅reducedAggregate (L ⊔ T), L⁆, L⁆ ≠ ⊥ := by
  rw [← c.V_eq_commutator]
  exact c.hypC28.V_ne

theorem V_le_T : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ T :=
  (c.V_le_omega.trans (omegaOneCenterOf_le _)).trans
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le c.hyp421.sylow le_sup_right))

theorem pCoreOf_eq_inf_centralizer :
    pCoreOf 2 (L ⊔ T) =
      T ⊓ Subgroup.centralizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le c.hyp421.sylow le_sup_right))
      (c.pCoreOf_le_centralizer_V le_rfl)
  · intro t ht
    have htLT : t ∈ L ⊔ T := Subgroup.mem_sup_right ht.1
    have hC := c.hyp421.inf_centralizer_le_centralizerSection c.normal c.L_le_normalizer_V
      c.commutator_V_ne_bot ⟨htLT, ht.2⟩
    obtain ⟨k, hk⟩ := c.hyp421.sylow.1 ⟨t, ht.1⟩
    exact c.hyp421.mem_pCoreOf_of_mem_centralizerSection c.normal htLT hC (e := k)
      (by simpa using congrArg Subtype.val hk)

theorem isTwoReducedIn_V : IsTwoReducedIn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆ :=
  c.hyp421.isTwoReducedIn_of_le_omegaOneCenter c.normal
    (c.V_le_omega.trans (CFSG.Quasithin.omegaOneCenterOf_eq _).le) c.sup_le_normalizer_V
    c.commutator_V_ne_bot

theorem exists_isHStar (h332 : Stmt3_3_2MTwo) : ∃ X : Subgroup G, IsHStar T M X := by
  obtain ⟨M₁, M₂, hne, h1, h2, hT1, hT2⟩ := h332 G T c.hyp421.simple c.hyp421.nonabelian
    c.hyp421.qtke c.hyp421.sylow L c.hyp421.maximal c.hyp421.quasisimple
  by_cases h1M : M₁ = M
  · refine exists_isHStar_of c.hyp421.maxTwoLocal h2 hT2 ?_
    rw [← h1M]
    exact Ne.symm hne
  · exact exists_isHStar_of c.hyp421.maxTwoLocal h1 hT1 h1M

theorem hyp318 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h332 : Stmt3_3_2MTwo) :
    Hyp318 T M L ⁅reducedAggregate (L ⊔ T), L⁆ :=
  { inM := ⟨c.hyp421.maxTwoLocal, c.hyp421.T_le⟩
    nonempty := c.exists_isHStar h332
    perfect := eq_oTwoUpper_of_perfect c.hyp421.perfect
    le_M := c.hyp421.L_le
    normal := c.normal
    unique := (c.hyp421.isUniqueM_sup h37 h38 h39).1
    reduced := c.isTwoReducedIn_V
    centralizer := c.pCoreOf_eq_inf_centralizer }

theorem ff_of_inf_centralizer_ne_bot (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo)
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  rcases theorem318_three hC58 h317 c.hyp421.simple c.hyp421.nonabelian c.hyp421.qtke
    c.hyp421.sylow (c.hyp318 h37 h38 h39 h332) with ⟨-, hFF⟩ | ⟨-, -, hZ⟩
  · exact ⟨⟨⟨fun a b => Subtype.ext (c.V_comm _ a.2 _ b.2)⟩⟩, hFF⟩
  · exfalso
    have hTN : T ≤ Subgroup.normalizer
        ((⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
          Set G) := fun t ht =>
      mem_normalizer_inf (c.sup_le_normalizer_V (Subgroup.mem_sup_right ht))
        (mem_normalizer_centralizer_of_mem_normalizer
          (c.normal (c.hyp421.T_le ht)))
    obtain ⟨z, hz, hz1, hzT⟩ := exists_ne_one_mem_centralizer_of_le c.hyp421.sylow.1
      (inf_le_left.trans c.V_le_T) hTN hCV
    apply hz1
    have hzLT : z ∈ L ⊔ T := Subgroup.mem_sup_right (c.V_le_T hz.1)
    have hzC : z ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) := by
      have hLT : L ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := by
        refine _root_.sup_le (fun l hl => ?_) (fun t ht => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hz.2 l hl
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hzT t ht
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLT hx)
    have hzZ : z ∈ centerOf (L ⊔ T) := ⟨hzLT, hzC⟩
    rw [hZ] at hzZ
    exact hzZ

end Conf4212

end CFSG.Quasithin.H13.Ch4
