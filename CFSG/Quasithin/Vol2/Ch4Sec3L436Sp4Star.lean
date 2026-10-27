module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Setup

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_ne_bot_of_le {P W : Subgroup G} (hP : IsPGroup 2 P) (hWP : W ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem V_eq : v432 T M L = pCoreOf 2 L := by
  have h := s.concl.V_eq
  rwa [← s.L_eq] at h

theorem V_le_T : v432 T M L ≤ T := by
  rw [s.V_eq]
  exact s.sk.base.hyp421.pCoreOf_L_le_T s.sk.base.hyp.normal

theorem Z_le_V : sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ v432 T M L :=
  le_sup_right.trans (s.concl.cent_S.symm.le.trans inf_le_left)

theorem Z_ne_bot : sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≠ ⊥ := by
  intro h
  have hc := s.concl.card_Z
  rw [h, Subgroup.card_bot] at hc
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) s.sk.base.hyp.two_le
  omega

theorem C_ne_bot : sp4C (H ⊓ M ⊓ K) (v432 T M L) ≠ ⊥ := by
  intro h
  have hc := s.concl.card_C
  rw [h, Subgroup.card_bot] at hc
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) s.sk.base.hyp.two_le
  omega

theorem Z_le_pCoreOf :
    sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤
      pCoreOf 2 (Subgroup.normalizer
        (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) :=
  le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    ((s.sk.base.hyp.sylow.1.to_le (s.Z_le_V.trans s.V_le_T)))

theorem inH_GZ :
    InH T (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) :=
  ⟨s.T_le_normalizer_Z, fun h => s.Z_ne_bot (le_bot_iff.mp (h ▸ s.Z_le_pCoreOf))⟩

theorem charTwo_GZ :
    CharTwo (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) :=
  charTwo_of_inH s.sk.base.hyp.qtke.2.1 (s.sk.base.hyp.sylow.1.toSylow s.sk.base.hyp.sylow.2)
    s.inH_GZ

theorem pCoreOf_GZ_le_T :
    pCoreOf 2 (Subgroup.normalizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ≤ T :=
  pCoreOf_two_le_sylow _ (s.sk.base.hyp.sylow.1.toSylow s.sk.base.hyp.sylow.2)
    s.T_le_normalizer_Z

theorem T_le_normalizer_C :
    T ≤ Subgroup.normalizer (sp4C (H ⊓ M ⊓ K) (v432 T M L) : Set G) := by
  intro x hx
  have hxL : x ∈ Subgroup.normalizer ((perfectCore (H ⊓ M ⊓ K) : Subgroup G) : Set G) := by
    rw [← s.L_eq]
    exact s.T_le_normalizer_L hx
  exact mem_normalizer_inf (s.T_le_normalizer_V hx) (A4.mem_normalizer_centralizer hxL)

theorem C_inf_centralizer_T_ne_bot :
    sp4C (H ⊓ M ⊓ K) (v432 T M L) ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
  inf_centralizer_ne_bot_of_le s.sk.base.hyp.sylow.1
    ((inf_le_left : sp4C (H ⊓ M ⊓ K) (v432 T M L) ≤ v432 T M L).trans s.V_le_T)
    s.T_le_normalizer_C s.C_ne_bot

theorem C_inf_centralizer_T_le :
    sp4C (H ⊓ M ⊓ K) (v432 T M L) ⊓ Subgroup.centralizer (T : Set G) ≤
      omegaOneCenterOf (pCoreOf 2 (Subgroup.normalizer
        (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) := by
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  intro c hc
  have hcT : c ∈ T := s.V_le_T hc.1.1
  have hcQ : c ∈ pCoreOf 2 GZ := by
    refine s.charTwo_GZ ⟨s.T_le_normalizer_Z hcT, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp hc.2) q (s.pCoreOf_GZ_le_T hq)⟩
  exact Subgroup.subset_closure ⟨⟨hcQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    (Subgroup.mem_centralizer_iff.mp hc.2) q (s.pCoreOf_GZ_le_T hq)⟩,
    s.concl.V_sq c hc.1.1⟩

theorem C_le :
    sp4C (H ⊓ M ⊓ K) (v432 T M L) ≤
      omegaOneCenterOf (pCoreOf 2 (Subgroup.normalizer
        (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) := by
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  obtain ⟨Y₁, Y₂, hY₁N, -, -, -, -, -, -, hY₂K, -, -, -, -, htrans⟩ := s.concl.torus
  have hYGZ : Y₁ ⊔ Y₂ ≤ GZ := _root_.sup_le (hY₁N.trans inf_le_right)
    (hY₂K.trans (s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)))
  have hnorm : GZ ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 GZ) : Set G) :=
    (le_normalizer_pCoreOf 2 GZ).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  obtain ⟨c₀, hc₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp s.C_inf_centralizer_T_ne_bot
  have hc₀Ω := s.C_inf_centralizer_T_le c₀.2
  intro c hc
  by_cases hc1 : c = 1
  · rw [hc1]
    exact one_mem _
  obtain ⟨y, hy, hyc⟩ := htrans (c₀ : G) c₀.2.1 c hc (fun h => hc₀1 (Subtype.ext h)) hc1
  rw [← hyc]
  exact (Subgroup.mem_normalizer_iff.mp (hnorm (hYGZ hy)) _).mp hc₀Ω

theorem star :
    sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤
        conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
          (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ∧
      conjClosure (sp4C (H ⊓ M ⊓ K) (v432 T M L))
          (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ≤
        omegaOneCenterOf (pCoreOf 2 (Subgroup.normalizer
          (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))) := by
  set GZ := Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) with hGZ
  have hK₂GZ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ GZ :=
    s.concl.K₂_le.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm : GZ ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 GZ) : Set G) :=
    (le_normalizer_pCoreOf 2 GZ).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  refine ⟨?_, conjClosure_le fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hg) c).mp (s.C_le hc)⟩
  rw [← s.concl.Q₁_closure]
  exact conjClosure_le fun g hg c hc => mem_conjClosure (hK₂GZ hg) hc

end Setting436Sp4

end CFSG.Quasithin.H13.Ch4
