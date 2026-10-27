module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Block
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113C2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactA7Gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 7)) →
    ∀ R S E : Subgroup X, IsSylowTwoOf S ⊤ → S ≤ Subgroup.normalizer (R : Set X) →
      ⁅R, R⁆ = R → ¬ E ≤ Subgroup.normalizer (R : Set X) → R ⊔ S ⊔ E = ⊤

@[expose] def Stmt5_1_13_four_A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7))

@[expose] def Stmt5_1_13_four_nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) =
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) ∧
        (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) = ⊥ →
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥) ∧
        ∃ V' : Subgroup G, IsCh5Module T L V' ∧ quasithinOmegaOneCenter T ≤ V' ∧
          IsNatQuotCh5 L V' n

@[expose] def Stmt5_1_13_four_block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      2 < n ∧ ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧
        oTwoUpper H ⊔ T ≤ Subgroup.normalizer (C : Set G) ∧
        D ⊔ T ≤ Subgroup.normalizer (C : Set G)

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem inf_centralizer_eq_bot_of_eq (h432 : Stmt4_3_2) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) =
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G)) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  obtain ⟨huniq, -⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
    h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
  by_contra hne
  have hY2 : IsPGroup 2 ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) :=
    h.sylow.1.to_le (inf_le_left.trans (quasithinOmegaOneCenter_le_self T))
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :=
    ⟨_, hne, hY2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLY : L ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine le_trans (fun l hl => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHY : H ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTH]
    refine sup_le (fun x hx => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hCZ] at hy
      exact (Subgroup.mem_centralizer_iff.mp hy.2 x (m.lt.le hx)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hy.1).2 t ht).symm
  have hM'eq : M' = M := huniq M' hM' (hLY.trans hle)
  exact m.hyp.hStar.2.1 (hM'eq ▸ hHY.trans hle)

theorem le_normalizer_hat_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hgen : FactA7Gen) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (ty : Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (hmax : quasithinIsMaximalLocal T (conjClosure Kh₁ T))
    (hA : Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7))) {C : Subgroup G}
    (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hKC : oTwoUpper H ⊔ T ≤ Subgroup.normalizer (C : Set G))
    (hDC : D ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    D ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hKKh : oTwoUpper H ≤ conjClosure Kh₁ T := m.lt.le
  have hTsyl : IsSylowTwoOf (T ⊓ conjClosure Kh₁ T) (conjClosure Kh₁ T) :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf (le_sup_right : T ≤ conjClosure Kh₁ T ⊔ T))
      le_sup_left (sup_le Subgroup.le_normalizer hTKh)
  have hOT : pCoreOf 2 (conjClosure Kh₁ T) ≤ T :=
    (F7.isSylowTwoOf_pCoreOf_le hTsyl).trans inf_le_left
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -, -⟩ := ty
  have hD₃Kh : D₃ ≤ conjClosure Kh₁ T := hD₃.trans inf_le_right
  have hAKh : oTwoUpper H ⊔ (T ⊓ conjClosure Kh₁ T) ⊔ D₃ ≤ conjClosure Kh₁ T :=
    sup_le (sup_le hKKh inf_le_right) hD₃Kh
  have hS : IsSylowTwoOf (modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) _
      (QuotientGroup.mk'_surjective _)
  have hSN : modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T) ≤ Subgroup.normalizer
      ((modO2Image (conjClosure Kh₁ T) (oTwoUpper H) : Subgroup (O2Q (conjClosure Kh₁ T))) :
        Set (O2Q (conjClosure Kh₁ T))) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer (inf_le_left.trans hTK)
  have hRperf : ⁅modO2Image (conjClosure Kh₁ T) (oTwoUpper H),
      modO2Image (conjClosure Kh₁ T) (oTwoUpper H)⁆ =
        modO2Image (conjClosure Kh₁ T) (oTwoUpper H) := by
    have : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥(modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) :=
      Group.IsPerfect.ofSurjective (barMap_surjective hKKh)
    exact Subgroup.isPerfect_iff.mp this
  have hE : ¬ modO2Image (conjClosure Kh₁ T) D₃ ≤ Subgroup.normalizer
      ((modO2Image (conjClosure Kh₁ T) (oTwoUpper H) : Subgroup (O2Q (conjClosure Kh₁ T))) :
        Set (O2Q (conjClosure Kh₁ T))) := by
    intro hle
    apply hD₃K
    intro d hd
    have hdb : QuotientGroup.mk' (CFSG.pCore 2 ↥(conjClosure Kh₁ T)) ⟨d, hD₃Kh hd⟩ ∈
        modO2Image (conjClosure Kh₁ T) D₃ :=
      ⟨⟨d, hD₃Kh hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    exact mem_normalizer_of_modO2Image hKKh hKperf (hOT.trans hTK) (hD₃Kh hd) (hle hdb)
  have hgen' : modO2Image (conjClosure Kh₁ T) (oTwoUpper H ⊔ (T ⊓ conjClosure Kh₁ T) ⊔ D₃) =
      ⊤ := by
    rw [modO2Image_sup (sup_le hKKh inf_le_right) hD₃Kh, modO2Image_sup hKKh inf_le_right]
    exact hgen _ hA _ _ _ hS hSN hRperf hE
  have h1 := Vol2.Ch11.SecS.map_comap_modO2Image hAKh
  rw [hgen', Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hD₃C : D₃ ≤ Subgroup.normalizer (C : Set G) :=
    (hD₃.trans inf_le_left).trans (le_sup_left.trans hDC)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := le_sup_right.trans hKC
  have hKhC : conjClosure Kh₁ T ≤ Subgroup.normalizer (C : Set G) := by
    rw [h1]
    exact sup_le (sup_le (sup_le (le_sup_left.trans hKC) (inf_le_left.trans hTC)) hD₃C)
      (hOT.trans hTC)
  have hU := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow hmax
  have hcc : conjClosure (conjClosure Kh₁ T) T = conjClosure Kh₁ T :=
    le_antisymm (conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTKh ht) z).mp hz)
      (le_conjClosure _ _)
  rw [hcc] at hU
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (Hyp5_0_1.isTwoLocal_normalizer hC2 hC1)
  have hM'eq := hU.2 M' ⟨hM', (sup_le hKhC hTC).trans hle⟩
  exact (le_sup_left.trans hDC).trans (hM'eq ▸ hle)

end Main513

theorem stmt5_1_13_four_be_of (h432 : Stmt4_3_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hgen : FactA7Gen) (hA7 : Stmt5_1_13_four_A7)
    (hnat : Stmt5_1_13_four_nat) (hblk : Stmt5_1_13_four_block) : Stmt5_1_13_four_be := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  have hA := hA7 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  obtain ⟨hCZ, hCK, V', hV', hZV', hnat'⟩ := hnat G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA
  have hCZL := m.inf_centralizer_eq_bot_of_eq h432 hCZ
  obtain ⟨hn, C, hC1, hC2, hKC, hDC⟩ := hblk G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hCZL
    (hCK (hCZ.symm.trans hCZL)) V' hV' hZV' hnat'
  exact ⟨hn, m.le_normalizer_hat_of h37 h38 h39 hgen ty hmax hA hC1 hC2 hKC hDC, V', hV', hnat'⟩

end CFSG.Quasithin.H13
