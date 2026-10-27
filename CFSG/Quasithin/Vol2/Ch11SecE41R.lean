module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts3
public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecD556B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_centralizer_le_pCoreOf (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hCV : Subgroup.normalizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) :=
    fun t ht => SecA.mem_normalizer_centralizer ht
  have hXV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (SecA.L_le_normalizer_fsuV h) (SecA.T_le_normalizer_fsuV T I)
  set N := (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) with hN
  have hN2 : IsPGroup 2 N := isPGroup_two_of_forall fun x hx => by
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 h.normal hx.1
    have hjC : x ^ 2 ^ j ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨hj, Subgroup.pow_mem _ hx.2 _⟩
    rw [SecA.centralizer_eq_pCoreOf h1102 h] at hjC
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hjC
    exact ⟨j + k, by rw [pow_add, pow_mul, hk]⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
      fun x hx => SecD.mem_normalizer_inf (Subgroup.le_normalizer hx) (hCV (hXV hx))) hN2

theorem rOf_le_TL (hP : ParInFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : ROf T L V₁ ≤ TL T L := by
  have hab := (SecA.isElemAbelian_fsuV h).1
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hflag := SecA.isFlagW_of_isVi h hV₁
  rw [hZ] at hflag
  obtain ⟨hS2, hSH, hSU⟩ :=
    SecB.autOn_T_props h (SecA.IsVi.le_fsuV hV₁) (SecA.IsVi.le_normalizer hV₁)
  have hpar : ParInConcl (autOn L (fsuV T I)) (autOn T (fsuV T I)) (V₁.subgroupOf (fsuV T I)) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, hng⟩ | ⟨K, _, _, hK, -, π, hπ, hng⟩ |
        ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
    · rw [hZ] at hπ
      exact hP.sl3 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hS2 hSH hSU hng
    · rw [hZ] at hπ
      exact hP.sp4 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hS2 hSH hSU hng
    · rw [hZ] at hπ
      exact hP.g2 K n hn hK _ hsq _ π hπ _ (SecA.isSylowTwoOf_P h) _ hflag _ hS2 hSH hSU
  have hle := SecA.IsVi.le_fsuV hV₁
  have hA : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (SecA.L_le_normalizer_fsuV h)
  unfold ParInConcl at hpar
  rw [SecB.autOn_inf_stabW hle, ← SecB.autOn_perfectCore hA] at hpar
  have hRT : ROf T L V₁ ≤ T := SecD.ROf_le_T h V₁
  intro r hr
  have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) := SecA.T_le_normalizer_fsuV T I (hRT hr)
  have h1 := hpar _ (SecA.conjV_mem_autOn (hRT hr) hrV) fun k hk => by
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hk
    rw [← SecA.conjV_inv, ← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecB.autOn_pCoreOf_le _ _
      (SecA.conjV_mem_autOn (SecB.commutator_rOf_mem h hV₁ hr hl) _)
  obtain ⟨l, hl, hlV, hlr⟩ := SecA.mem_autOn_iff.mp h1
  have hC : l⁻¹ * r ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    refine SecD.mem_centralizer_of_conjV_eq_one (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlV) hrV)
      ?_
    rw [SecA.conjV_mul _ (Subgroup.inv_mem _ hlV) hrV, SecA.conjV_inv _ hlV, hlr, inv_mul_cancel]
  have hlrLT : l⁻¹ * r ∈ L ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right (hRT hr))
  have hO : l⁻¹ * r ∈ pCoreOf 2 (L ⊔ T) := inf_centralizer_le_pCoreOf h1102 h ⟨hlrLT, hC⟩
  refine ⟨hRT hr, ?_⟩
  have e : r = l * (l⁻¹ * r) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hO)

theorem rOf_eq_TL_inf (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hRTL : ROf T L V₁ ≤ TL T L) :
    ROf T L V₁ = TL T L ⊓ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) := by
  refine le_antisymm (le_inf hRTL fun r hr => ?_) ?_
  · have hrT : r ∈ T := SecD.ROf_le_T h V₁ hr
    have hrL₁ : r ∈ Subgroup.normalizer (LOf L V₁ : Set G) :=
      SecD.mem_normalizer_lOf (h.normal hrT) (SecA.IsVi.le_normalizer hV₁ hrT)
    exact ⟨hrL₁, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrL₁,
      fun l hl => SecB.commutator_rOf_mem h hV₁ hr hl⟩
  · exact (inf_le_inf_right _ inf_le_left).trans (SecD.inf_sectionCentralizer_le_ROf h hV₁)

theorem cartan_le_normalizer_rOf (hF : SecA.NatFacts) (hP : ParInFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {V₁ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    X ≤ Subgroup.normalizer (ROf T L V₁ : Set G) := by
  rw [rOf_eq_TL_inf h hV₁ (rOf_le_TL hP h1102 h hcV hV₁)]
  intro x hx
  have hxL : x ∈ L := (hX.1 hx).1
  have hxTL : x ∈ Subgroup.normalizer (TL T L : Set G) := (hX.1 hx).2
  have hxV : x ∈ Subgroup.normalizer (V₁ : Set G) :=
    SecD.cartan_le_normalizer_V₁ hF h1102 h hV₁ hX hx
  have hxL₁ : x ∈ Subgroup.normalizer (LOf L V₁ : Set G) :=
    SecD.mem_normalizer_lOf (Subgroup.le_normalizer hxL) hxV
  exact SecD.mem_normalizer_inf hxTL (SecD.mem_normalizer_sectionCentralizer hxL₁
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxL₁))

end CFSG.Quasithin.Vol2.Ch11.SecE
