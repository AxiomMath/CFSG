module

public import CFSG.Quasithin.Vol2.Ch11SecE42Defs
public import CFSG.Quasithin.Vol2.Ch11SecE44Pre

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem kz_spec (hF : Facts43) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h : Hyp11 G T L I n) (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    kz L V₁ z ∈ cComp (Subgroup.centralizer ({z} : Set G)) ∧
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (kz L V₁ z : Set G) ∧
      (LOf L V₁ = kz L V₁ z ∨ List11_1_1Two (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) n ∨
        (n = 2 ∧ List11_1_1Three (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)))) := by
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF h1102 h hcV hV₁ hz.1 hz.2
  have hN := normalizer_zpowers_eq_centralizer hz2
  have hTz : T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun t ht => by
    rw [hN]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 t ht)
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set G))
      (Subgroup.normalizer (Subgroup.zpowers z : Set G)) := by
    rw [inf_eq_left.mpr hTz]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hz0 : Subgroup.zpowers z ≠ ⊥ := fun h0 =>
    hz1 (Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers z))
  obtain ⟨K₀, hLK₀, hK₀, hNK₀, hcase⟩ := h1111 G T L I n 1 V₁ (Subgroup.zpowers z) h hV₁
    (Or.inl ⟨rfl, hz0, (Subgroup.zpowers_le).mpr hzV₁, hsyl⟩)
  have heq : kz L V₁ z = K₀ := kOf_eq_of_cComp' hLK₀ hK₀ hNK₀ (SecD.lOf_ne_bot h1110 h hV₁)
  rw [heq, ← hN]
  exact ⟨hK₀, hNK₀, hcase⟩

theorem kOf_V₁_spec (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₁1 : V₁ ≠ ⊥) :
    KOf L V₁ V₁ ∈ cComp (Subgroup.normalizer (V₁ : Set G)) := by
  have hTV : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.normalizer (V₁ : Set G)) := by
    rw [inf_eq_left.mpr hTV]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTV
  obtain ⟨K₀, hLK₀, hK₀, hNK₀, -⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
    (Or.inl ⟨rfl, hV₁1, le_rfl, hsyl⟩)
  rw [SecD.kOf_eq_of_cComp hLK₀ hK₀ hNK₀ (SecD.lOf_ne_bot h1110 h hV₁)]
  exact hK₀

theorem conjClosure_kOf_eq {L V₁ V₀ : Subgroup G}
    (hK : KOf L V₁ V₀ ∈ cComp (Subgroup.normalizer (V₀ : Set G))) (hL₁ : LOf L V₁ ≠ ⊥) :
    conjClosure (LOf L V₁) (KOf L V₁ V₀) = KOf L V₁ V₀ := by
  have hLK : LOf L V₁ ≤ KOf L V₁ V₀ := le_conjClosure _ _
  have hK'le : conjClosure (LOf L V₁) (KOf L V₁ V₀) ≤ KOf L V₁ V₀ :=
    conjClosure_le fun g hg x hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hLK hx))
      (Subgroup.inv_mem _ hg)
  have hsub : IsSubnormal (conjClosure (LOf L V₁) (KOf L V₁ V₀))
      (Subgroup.normalizer (V₀ : Set G)) :=
    IsSubnormal.step hK'le ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'le).mpr
      (le_normalizer_conjClosure _ _)) hK.2.2.1
  by_contra hne
  exact hK.2.2.2 _ (lt_of_le_of_ne hK'le hne) (fun h0 => hL₁ (le_bot_iff.mp
    (h0 ▸ le_conjClosure _ _))) (SecD.conjClosure_perfect (perfectCore_perfect _)) hsub

theorem kOf_le_kz (hP : SecB.PointFacts) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    {z : G} (hzV₁ : z ∈ V₁) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    KOf L V₁ V₁ ≤ kz L V₁ z := by
  have hV₁1 : V₁ ≠ ⊥ := fun h0 => hz1 (Subgroup.mem_bot.mp (h0 ▸ hzV₁))
  have hK₁ := kOf_V₁_spec h1110 h1111 h hV₁ hV₁1
  rw [← conjClosure_kOf_eq hK₁ (SecD.lOf_ne_bot h1110 h hV₁)]
  have hle : KOf L V₁ V₁ ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    rw [normalizer_zpowers_eq_centralizer hz2]
    exact (kOf_le_centralizer_V₁ hP h1102 h hV₁).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV₁))
  exact conjClosure_mono le_rfl hle

theorem not_le_centralizer_of_ne (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₁1 : V₁ ≠ ⊥) {z : G}
    (hK : kz L V₁ z ∈ cComp (Subgroup.centralizer ({z} : Set G)))
    (hle : KOf L V₁ V₁ ≤ kz L V₁ z) (hne : KOf L V₁ V₁ ≠ kz L V₁ z) :
    ¬ kz L V₁ z ≤ Subgroup.centralizer (V₁ : Set G) := by
  intro hKC
  have hK₁ := kOf_V₁_spec h1110 h1111 h hV₁ hV₁1
  have hKN : kz L V₁ z ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
    (hKC.trans (Subgroup.centralizer_le_normalizer (V₁ : Set G))).trans
      (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
  have hsub : IsSubnormal (KOf L V₁ V₁) (Subgroup.centralizer ({z} : Set G)) :=
    IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hKN) hK.2.2.1
  exact hK.2.2.2 _ (lt_of_le_of_ne hle hne) hK₁.1 hK₁.2.1 hsub

theorem pCoreOf_centralizer_ne_bot (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzle : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hzle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hzle).mpr
        (normalizer_zpowers_eq_centralizer hz2).ge)
      ((SecA.isPGroup_fsuV h).to_le ((Subgroup.zpowers_le).mpr hz.1))
  intro h0
  rw [h0] at hzO
  exact hz1 (Subgroup.mem_bot.mp (hzO (Subgroup.mem_zpowers z)))

omit [Finite G] in
theorem le_centralizer_of_mem {z : G} (hz : z ∈ Subgroup.centralizer (T : Set G)) :
    T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz t ht)

end CFSG.Quasithin.Vol2.Ch11.SecE
