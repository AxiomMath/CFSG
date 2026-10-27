module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213A5
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KGRu
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E15FF
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFw

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autOn_le_of_le {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_mono h

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem orth_of_case1_alt
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hpsl : IsPSL 2 2 2 (ModO2 (perfectCore (L ⊓ H))))
    (halt : IsAltNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆
      (⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) 5) :
    Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆ := by
  have hV := c.isMulCommutative_V
  have hZ : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hCV
  rw [hZ] at halt
  have hAV := halt.1
  have hLV : L ≤ Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
    le_sup_left.trans c.sup_le_normalizer_V
  refine ⟨c.normal, ?_, ⟨hV, ?_⟩, fun W hCW hWV hLW => ?_⟩
  · obtain ⟨e⟩ := c.nonempty_modO2_equiv
    exact Or.inl ⟨by decide, T4213.isPSL_of_mulEquiv e hpsl⟩
  · rw [c.autOn_eq le_rfl hLV hAV]
    exact A5Herm.binaryOrthogonalFour_of_altNatural halt
  · rw [hCV]
    have hRW : pCoreOf 2 I ≤ Subgroup.normalizer (W : Set G) := fun r hr =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le hWV (c.pCoreOf_le_centralizer_V c.R_le hr))
    exact A5Herm.eq_bot_or_eq_of_altNatural halt hWV
      (_root_.sup_le (((perfectCore_le _).trans inf_le_left).trans hLW) hRW)

theorem card_V_of_isG2Block
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (h : CFSG.Quasithin.IsG2Block (perfectCore (L ⊓ H))) :
    Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLHdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  have hVc := c.isMulCommutative_V
  obtain ⟨hsh, hU, hidx, hnatural⟩ := h
  obtain ⟨-, -, ⟨hUQ, -⟩, -, -⟩ := hsh
  have hZ : V ⊓ Subgroup.centralizer (LH : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hCV
  have hne : ¬ LH ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply c.hypC28.V_ne
    have h1 := c.hypC28.V_comm
    rw [conjClosure_eq_self c.LH_normal] at h1
    rw [← h1, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hle
  have hle : Nat.card V ≤ 64 := by
    have h1 : (Subgroup.centralizer (LH : Set G)).relIndex (blockU LH) = 2 ^ 6 := by
      rw [← Subgroup.inf_relIndex_left]
      exact hidx
    have h2 : (Subgroup.centralizer (LH : Set G)).relIndex V ≤ 64 :=
      calc (Subgroup.centralizer (LH : Set G)).relIndex V
          ≤ (Subgroup.centralizer (LH : Set G)).relIndex (blockU LH) :=
            Subgroup.relIndex_le_of_le_right c.V_le_blockU (by rw [h1]; norm_num)
        _ = 64 := by rw [h1]; norm_num
    rw [← Subgroup.inf_relIndex_left, hZ, Subgroup.relIndex_bot_left] at h2
    exact h2
  have hV2 : ∀ x : ↥V, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using c.hypC28.V_elem.2 _ x.2)
  have hP2 : IsPGroup 2 ↥V := fun x => ⟨1, by rw [pow_one]; exact hV2 x⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hP2
  have hgt : ¬ Nat.card V ≤ 32 := by
    intro h32
    have h27 := T4213N.not_dvd_card_of_le hV2 h32 (autOn LH V)
    have hQV : pCoreOf 2 LH ≤ LH ⊓ Subgroup.centralizer (V : Set G) := by
      refine le_inf (pCoreOf_le 2 LH) ?_
      rw [Subgroup.le_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_inf.mp (hUQ (c.V_le_blockU hv))).2
    have hs : IsSimpleGroup (ModO2 LH) :=
      CFSG.Quasithin.SBc11.isSimpleGroup_of_list (Or.inr (Or.inr hU))
    have h27L : 27 ∣ Nat.card (ModO2 LH) := by
      rw [CFSG.Quasithin.SBc11.card_of_isPSU_three_three hU]
      norm_num
    have hNL : LH ≤ Subgroup.normalizer
        ((LH ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun x hx =>
      mem_normalizer_inf (Subgroup.le_normalizer hx)
        (mem_normalizer_centralizer_of_mem_normalizer (c.LH_le_normalizer_V hx))
    have hidxK : (LH ⊓ Subgroup.centralizer (V : Set G)).relIndex LH = Nat.card (autOn LH V) := by
      set ρ := T4213N.rhoAut c.LH_le_normalizer_V with hρ
      have hker : ρ.ker = (LH ⊓ Subgroup.centralizer (V : Set G)).subgroupOf LH := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · intro hx
          refine ⟨x.2, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          have h1 := congrArg (fun φ : ↥(autOn LH V) => (((φ : MulAut ↥V) ⟨v, hv⟩ : ↥V) : G)) hx
          simp only [hρ, T4213N.rhoAut_apply] at h1
          have h2 : (x : G) * v * (x : G)⁻¹ = v := h1
          calc v * x = ((x : G) * v * (x : G)⁻¹) * x := by rw [h2]
            _ = x * v := by group
        · rintro ⟨-, hxC⟩
          apply Subtype.ext
          exact InternalSec.conjAct_eq_one_of_mem_centralizer _ hxC
      rw [Subgroup.relIndex, ← hker, Subgroup.index_ker,
        MonoidHom.range_eq_top.mpr (T4213N.rhoAut_surjective c.LH_le_normalizer_V),
        Subgroup.card_top]
    have heq := T4213N.eq_of_isSimpleGroup hs h27L inf_le_left hNL hQV (by rw [hidxK]; exact h27)
    exact hne (fun x hx => (heq.symm ▸ hx : x ∈ LH ⊓ Subgroup.centralizer (V : Set G)).2)
  rw [hd] at hle hgt ⊢
  have hd6 : d ≤ 6 := by
    by_contra h6
    have : 2 ^ 7 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd5 : 5 < d := by
    by_contra h5
    exact hgt (calc 2 ^ d ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 32 := by norm_num)
  rw [show d = 6 by omega]

theorem ff_of_case7 (hKG : KGG2BlockRuFF)
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (h7 : C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have hV := c.isMulCommutative_V
  obtain ⟨hRu, hG2⟩ := h7
  have hcard := c.card_V_of_isG2Block hCV hG2
  have hZ : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ blockZ (perfectCore (L ⊓ H)) = ⊥ := by
    rw [eq_bot_iff, ← hCV, c.inf_centralizer_eq]
    exact inf_le_inf_left _ inf_le_right
  obtain ⟨hV', hFF⟩ := hKG G K (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
    (perfect_of_mem_cComp c.K_mem) hRu c.LH_le hG2 c.V_le_blockU hZ c.LH_le_normalizer_V hcard
  refine ⟨hV, ?_⟩
  have hTN : T ≤ Subgroup.normalizer
      ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans c.sup_le_normalizer_V
  have hTsyl := isSylowTwoOf_of_le c.hyp421.sylow hTN
  have h1 : IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
      (autOn (Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G))
        ⁅reducedAggregate (L ⊔ T), L⁆) :=
    B1Red.isFFModule_mono (autOn_le_of_le inf_le_right) hFF
  have h2 := E443.isFFModule_of_isSylowTwoOf (E443.isSylowTwoOf_autOn le_rfl hTsyl) h1
  exact B1Red.isFFModule_mono (autOn_le_of_le le_sup_right) h2

end Conf4212

end CFSG.Quasithin.H13.Ch4
