module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Phi
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25DL

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure In625 : Prop where
  h432 : Stmt4_3_2
  h6111 : Stmt6_1_11
  h6119 : Stmt6_1_19
  h37 : Vol2Native.A37ForSQTKCat
  h38 : Vol2Native.A38ForSQTKCat

structure Dat625 (T M L V : Subgroup G) (n : ℕ) (l : G) (DL K : Subgroup G) : Prop where
  hyp : Hyp6116 G T M L V n
  l_mem : l ∈ L
  l_not : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)
  hall : Lin2.IsHallTwoPrimeOf DL (borelL T L)
  comp : K ∈ cComp (Subgroup.centralizer (ch6ZS T L V : Set G))
  quasi : CFSG.IsQuasisimple (KQ K)
  not_le : ¬ ⁅K, ch6R T L V l⁆ ≤ ch6CH T L V

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem K_le_I : K ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := le_of_mem_cComp d.comp

theorem O2_le_NK : pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
    Subgroup.normalizer (K : Set G) :=
  pCoreOf_le_normalizer_of_mem_cComp d.comp

include hI in
theorem DL_le_NK : DL ≤ Subgroup.normalizer (K : Set G) :=
  (d.hyp.le_normalizer_K hI.h432 hI.h6111 hI.h6119 hI.h37 hI.h38 d.l_mem d.l_not d.hall
    d.comp).1

include hI in
theorem R_le_NK : ch6R T L V l ≤ Subgroup.normalizer (K : Set G) :=
  (d.hyp.le_normalizer_K hI.h432 hI.h6111 hI.h6119 hI.h37 hI.h38 d.l_mem d.l_not d.hall
    d.comp).2

theorem inf_O2_le : K ⊓ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (d.K_le_I hk)⟩

theorem phi_eq_one_of_mem_pCoreOf {x : G}
    (hx : x ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G))) :
    phiK K ⟨x, d.O2_le_NK hx⟩ = 1 := by
  rw [phiK_eq_one_iff d.quasi]
  intro k hk
  refine d.inf_O2_le ⟨?_, ?_⟩
  · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (d.O2_le_NK hx) k).mp hk) (K.inv_mem hk)
  · have hkI := d.K_le_I hk
    have h1 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hkI) _).mp (Subgroup.inv_mem _ hx)
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx h1

include hI in
theorem exists_phi_R_ne_one :
    ∃ r : G, ∃ hr : r ∈ ch6R T L V l, phiK K ⟨r, d.R_le_NK hI hr⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  apply d.not_le
  rw [d.hyp.ch6CH_eq hI.h432 hI.h6111 hI.h6119, Subgroup.commutator_le]
  intro k hk r hr
  have h1 := (phiK_eq_one_iff d.quasi _).mp (hcon r hr) k hk
  have h2 : pCoreOf 2 K ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp d.comp)
  have e : ⁅k, r⁆ = (r * k * r⁻¹ * k⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.inv_mem _ (h2 h1)

include hI in
theorem eq_one_of_phi_DL {x : G} (hx : x ∈ DL) (h1 : phiK K ⟨x, d.DL_le_NK hI hx⟩ = 1) :
    x = 1 := by
  by_contra hx1
  set D₀ := Subgroup.zpowers x with hD₀def
  have hD₀ : D₀ ≤ DL := Subgroup.zpowers_le.mpr hx
  have hD₀1 : D₀ ≠ ⊥ := by
    intro h0
    exact hx1 (Subgroup.zpowers_eq_bot.mp h0)
  have hR24 := (d.hyp.lemma_6_1_24_two hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).2.2 DL d.hall
    D₀ hD₀ hD₀1
  set Ker : Subgroup G := ((phiK K).ker).map (Subgroup.normalizer (K : Set G)).subtype with hKer
  have hmemKer : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (K : Set G)),
      phiK K ⟨y, hy⟩ = 1 → y ∈ Ker := fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hxN := d.DL_le_NK hI hx
  have hRK : ch6R T L V l ≤ Ker := by
    have hR' : ch6R T L V l = ⁅ch6R T L V l, D₀⁆ ⊔
        (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)) := hR24
    rw [hR']
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro r hr y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hrN := d.R_le_NK hI hr
      have hjN : x ^ j ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hxN j
      have hcN : ⁅r, x ^ j⁆ ∈ Subgroup.normalizer (K : Set G) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hjN)
          (Subgroup.inv_mem _ hrN)) (Subgroup.inv_mem _ hjN)
      refine hmemKer _ hcN ?_
      have e : (⟨⁅r, x ^ j⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⁅(⟨r, hrN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨x, hxN⟩ ^ j⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e, map_commutatorElement, map_zpow, h1, one_zpow, commutatorElement_one_right]
    · intro y hy
      have hyO : y ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
        (d.hyp.lemma_6_1_20_one hI.h432).1 hy.1
      exact hmemKer _ _ (d.phi_eq_one_of_mem_pCoreOf hyO)
  obtain ⟨r, hr, hr1⟩ := d.exists_phi_R_ne_one hI
  obtain ⟨⟨y, hyN⟩, hy1, hyr⟩ := hRK hr
  have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨r, d.R_le_NK hI hr⟩ :=
    Subtype.ext hyr
  rw [e] at hy1
  exact hr1 hy1

end Dat625

end CFSG.Quasithin.H13
