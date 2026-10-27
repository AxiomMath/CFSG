module

public import CFSG.Quasithin.Vol2.Ch11SecE43Pre

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise

theorem stmt11_4_3_of (hP : SecB.PointFacts) (hF : Facts43) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1112 : Stmt11_1_2)
    (h1123 : Stmt11_2_3) (h1132 : Stmt11_3_2) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) :
    Stmt11_4_3 := by
  intro G _ _ T L I n V₁ h hV₁ z hz hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hV₁ hX).1.1
  have hKC := kOf_le_centralizer_V₁ hP h1102 h hV₁
  have hout := out2Closed_kOf hF h1110 h1111 h1112 h1141 h hV₁ hKC
  obtain ⟨hKz, hzK⟩ := kOf_le_centralizer_of hP hF h1102 h1142 h hcV hV₁ hz hz1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 t ht)
  have hsylz : QuasithinUnique.IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hNT := SecA.normalizer_T_le h331 h
  have hzV₁ := mem_V₁_of_mem_centralizer hF h1102 h hcV hV₁ hz.1 hz.2
  have hdec := exists_mul_of_out2Closed hKz hzK hsylz hout
  refine ⟨?_, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨k, hk, y, hy, m, hm, rfl⟩ := hdec g hg
      exact Set.mul_mem_mul (Set.mul_mem_mul hk hy) ⟨hNT hm.2, hm.1⟩
    · rintro ⟨_, ⟨k, hk, y, hy, rfl⟩, m, hm, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKz hk) hy.1) hm.2
  · intro heq hY
    have hzM : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
      intro g hg
      obtain ⟨k, hk, y, hy, m, hm, rfl⟩ := hdec g hg
      have hkL : k ∈ Subgroup.normalizer (L : Set G) := by
        rw [heq] at hk
        exact Subgroup.le_normalizer ((perfectCore_le _).trans inf_le_left hk)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkL (hY hy)) (hNT hm.2)
    have hV₁M : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV₁)).trans hzM
    obtain ⟨H, hH⟩ := SecA.exists_isHStar h331 h
    have hmoves : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
      intro hc
      have hzZ : z ∈ quasithinOmegaOneCenter T :=
        Subgroup.subset_closure ⟨⟨SecA.fsuV_le_T h hz.1, hz.2⟩,
          (SecA.isElemAbelian_fsuV h).2 z hz.1⟩
      have hZH := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hzZ
      refine hH.2.1 (fun x hx => hzM ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hZH x hx)
    exact (h1132 G T L I n V₁ H h hV₁ ⟨hH, hmoves, fun _ => hV₁M⟩).2.1 hV₁M
  · have hT2 : IsPGroup 2 T := h.fsu.sylow.1
    have hTV : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
    have hCVN : Subgroup.normalizer (V₁ : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (V₁ : Set G) : Set G) :=
      fun t ht => SecA.mem_normalizer_centralizer ht
    set X' := Subgroup.centralizer (V₁ : Set G) ⊔ T with hX'
    have hX'N : X' ≤ Subgroup.normalizer (V₁ : Set G) :=
      sup_le (Subgroup.centralizer_le_normalizer (V₁ : Set G)) hTV
    have hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
      SecD.normalizer_le_normalizer_kOf L V₁ V₁
    have hNO : Subgroup.normalizer (V₁ : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 (KOf L V₁ V₁) : Set G) :=
      hNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have hsylX : QuasithinUnique.IsSylowTwoOf T X' :=
      isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
    have hdec2 := exists_mul_of_out2Closed (hKC.trans le_sup_left) (hX'N.trans hNK) hsylX hout
    set YX := X' ⊓ sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) with hYX
    have hX'YX : X' ≤ Subgroup.normalizer (YX : Set G) := fun x hx =>
      SecD.mem_normalizer_inf (Subgroup.le_normalizer hx)
        (SecD.mem_normalizer_sectionCentralizer (hNK (hX'N hx)) (hNO (hX'N hx)))
    have hYXdec := exists_mul_of_sylow_of_two_quot (P := YX)
      (Q := YX ⊓ Subgroup.centralizer (V₁ : Set G)) (S := T ⊓ YX) inf_le_left
      (fun y hy => SecD.mem_normalizer_inf (Subgroup.le_normalizer hy) (hCVN (hX'N hy.1)))
      (A4.isSylowTwoOf_inf_normal hsylX inf_le_left hX'YX)
      (fun y hy => by
        obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 (hTV.trans hCVN) hy.1
        exact ⟨j, YX.pow_mem hy _, hj⟩)
    have hG1 := (h1123 G T L I n V₁ h hV₁).1 hcV
    ext g
    constructor
    · intro hg
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hG1] at hg
      obtain ⟨c, hc, m₁, hm₁, rfl⟩ := hg
      obtain ⟨k, hk, y, hy, m, hm, rfl⟩ := hdec2 c (Subgroup.mem_sup_left hc)
      obtain ⟨q, hq, s, hs, rfl⟩ := hYXdec y hy
      refine ⟨k * q, Set.mul_mem_mul hk ⟨⟨hX'N hq.1.1, hq.2⟩, hq.1.2⟩, s * m * m₁, ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.normal hs.1) (hNT hm.2)) hm₁.1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTV hs.1) (hX'N hm.1)) hm₁.2
      · group
    · rintro ⟨_, ⟨k, hk, y, hy, rfl⟩, m, hm, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (SecD.kOf_le_normalizer
        (SecD.lOf_le_normalizer L V₁) hk) hy.1.1) hm.2

end CFSG.Quasithin.Vol2.Ch11.SecE
