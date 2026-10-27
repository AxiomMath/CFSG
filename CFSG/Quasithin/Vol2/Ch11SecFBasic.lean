module

public import CFSG.Quasithin.Vol2.Ch11SecFGroup
public import CFSG.Quasithin.Vol2.Ch11SecD551A
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem normalizer_V₁_not_le (h1154 : Stmt11_5_4) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) :
    ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := fun hle =>
  (h1154 G T L I n V₁ h hV₁).1 ((Subgroup.centralizer_le_normalizer (V₁ : Set G)).trans hle)

omit [Finite G] in
theorem lOf_sup_le_normalizer_V₁ (hV₁ : IsVi T L I n 1 V₁) :
    LOf L V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
  sup_le (SecD.lOf_le_normalizer L V₁) (SecA.IsVi.le_normalizer hV₁)

theorem V₁_le_pCoreOf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V₁
    (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))

theorem inH_normalizer_V₁ (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)) :=
  ⟨lOf_sup_le_normalizer_V₁ hV₁, fun hb => SecA.IsVi.ne_bot h hV₁ le_rfl
    (le_bot_iff.mp (hb ▸ V₁_le_pCoreOf h hV₁))⟩

theorem pCoreOf_normalizer_V₁_le_T (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ T :=
  pCoreOf_le_of_sylow h.fsu.sylow (SecA.IsVi.le_normalizer hV₁)

theorem pCoreOf_normalizer_V₁_le_ROf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))
  exact SecD.le_ROf (pCoreOf_normalizer_V₁_le_T h hV₁)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    ((SecD.lOf_le_normalizer L V₁).trans hN) ((SecA.IsVi.le_normalizer hV₁).trans hN)

theorem fsuV_le_pCoreOf_sup (h : Hyp11 G T L I n) : fsuV T I ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((SecA.fsuV_le_T h).trans le_sup_right)
    (sup_le (SecA.L_le_normalizer_fsuV h) (SecA.T_le_normalizer_fsuV T I))
    (SecA.isPGroup_fsuV h)

theorem inf_normalizer_V₁_le_normalizer_fsuV (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := fun _ hm =>
  SecA.mem_normalizer_of_isTISetIn (h1103 G T L I n h).2.2.2.1 (SecA.IsVi.le_fsuV hV₁)
    (SecA.IsVi.ne_bot h hV₁ le_rfl) hm.1 hm.2

omit [Finite G] in
theorem kOf_le_normalizer_V₁ (L V₁ : Subgroup G) :
    KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  SecD.kOf_le_normalizer (SecD.lOf_le_normalizer L V₁)

omit [Finite G] in
theorem Y_le_normalizer_V₁ (L V₁ : Subgroup G) :
    Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) ≤
      Subgroup.normalizer (V₁ : Set G) :=
  inf_le_left.trans (Subgroup.centralizer_le_normalizer _)

theorem exists_decomp (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    ∀ g ∈ Subgroup.normalizer (V₁ : Set G),
      ∃ x ∈ KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))),
        ∃ m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G), g = x * m := by
  obtain ⟨z, hzV₁, hz1, hzT⟩ := SecD.exists_z h hV₁
  have hdec := (h1143 G T L I n V₁ h hV₁ z ⟨SecA.IsVi.le_fsuV hV₁ hzV₁, hzT⟩ hz1).2.2
  intro g hg
  have hg' : g ∈ ((Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) := hg
  rw [hdec] at hg'
  obtain ⟨_, ⟨k, hk, y, hy, rfl⟩, m, hm, rfl⟩ := hg'
  exact ⟨k * y, Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right ⟨hy.1.2, hy.2⟩), m, hm, rfl⟩

omit [Finite G] in
theorem conjSubgroup_pCoreOf_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) :
    conjSubgroup (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) g =
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
  conjSubgroup_eq_iff_mem_normalizer.mpr
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg)

end CFSG.Quasithin.Vol2.Ch11.SecF
