module

public import CFSG.Quasithin.Vol2.Ch1Unique4
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem fsuL0_le_sup (T L : Subgroup G) : fsuL0 T L ≤ L ⊔ T :=
  conjClosure_le fun _ hh _ hz =>
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hz))
      ((L ⊔ T).inv_mem (Subgroup.mem_sup_right hh))

theorem sup_eq_fsuL0_sup (T L : Subgroup G) : L ⊔ T = fsuL0 T L ⊔ T :=
  le_antisymm (sup_le_sup_right (le_conjClosure L T) T) (sup_le (fsuL0_le_sup T L) le_sup_right)

theorem le_fsuM (T L : Subgroup G) : T ≤ fsuM T L :=
  le_normalizer_conjClosure L T

variable [Finite G] {T L I : Subgroup G}

theorem stmt331_B (h331 : Stmt3_3_1) (h : Hyp10 G T L I) :
    (quasithinIsMaxTwoLocal (fsuM T L) ∧ L ⊔ T ≤ fsuM T L ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' → M' = fsuM T L) ∧
      (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧
        quasithinIsMaxTwoLocal M₂ ∧ T ≤ M₁ ∧ T ≤ M₂) ∧
      (∃ H : Subgroup G, IsHStar T (fsuM T L) H) ∧
      Subgroup.normalizer (T : Set G) ≤ fsuM T L ∧
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        IsUniqueMaxOver H T (H ⊓ fsuM T L) ∧ ¬ H ≤ Subgroup.normalizer (T : Set G) :=
  (h331 G T h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow).2 L h.fsu.maximal
    h.fsu.quasisimple

theorem isUniqueM_L0T (h331 : Stmt3_3_1) (h : Hyp10 G T L I) :
    IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) := by
  obtain ⟨⟨hmax, hle, huniq⟩, -⟩ := stmt331_B h331 h
  rw [← sup_eq_fsuL0_sup]
  exact ⟨⟨hmax, hle⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

theorem fsuM_isMaxTwoLocal (h331 : Stmt3_3_1) (h : Hyp10 G T L I) :
    quasithinIsMaxTwoLocal (fsuM T L) :=
  (isUniqueM_L0T h331 h).1.1

theorem normalizer_T_le (h331 : Stmt3_3_1) (h : Hyp10 G T L I) :
    Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
  (stmt331_B h331 h).2.2.2.1

theorem isUniqueMaxOver_of_isHStar (h331 : Stmt3_3_1) (h : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : IsUniqueMaxOver H T (H ⊓ fsuM T L) :=
  ((stmt331_B h331 h).2.2.2.2 H hH).1

theorem not_le_normalizer_of_isHStar (h331 : Stmt3_3_1) (h : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : ¬ H ≤ Subgroup.normalizer (T : Set G) :=
  ((stmt331_B h331 h).2.2.2.2 H hH).2

theorem minParabolic_of_isHStar (h331 : Stmt3_3_1) (h : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : MinParabolic H T (H ⊓ fsuM T L) :=
  ⟨isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1,
    not_le_normalizer_of_isHStar h331 h hH, isUniqueMaxOver_of_isHStar h331 h hH⟩

theorem isUniqueM_L0_sylow (h331 : Stmt3_3_1) (h : Hyp10 G T L I) {Tp : Subgroup G}
    (hTp : QuasithinUnique.IsSylowTwoOf Tp (fsuM T L)) : IsUniqueM (fsuL0 T L ⊔ Tp) (fsuM T L) := by
  have hU := isUniqueM_L0T h331 h
  have hT : QuasithinUnique.IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_fsuM T L)
  obtain ⟨m, hm, hmT⟩ := A4.exists_conj_of_isSylowTwoOf hT hTp
  have hL0M : fsuL0 T L ≤ fsuM T L := Subgroup.le_normalizer
  refine ⟨⟨hU.1.1, sup_le hL0M hTp.1⟩, fun M' hM' => ?_⟩
  have hM'' : InM (fsuL0 T L ⊔ T) (M'.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine ⟨CFSG.Quasithin.quasithinIsMaxTwoLocal_map_conj hM'.1 m⁻¹, sup_le ?_ ?_⟩
    · intro x hx
      rw [A38.mem_map_conj, inv_inv]
      apply hM'.2 (Subgroup.mem_sup_left _)
      have hmx := (Subgroup.mem_normalizer_iff.mp hm x).mp hx
      simpa [mul_assoc] using hmx
    · intro x hx
      rw [A38.mem_map_conj, inv_inv]
      apply hM'.2 (Subgroup.mem_sup_right _)
      rw [hmT]
      simpa [mul_assoc] using hx
  have heq := hU.2 _ hM''
  have h2 := CFSG.Quasithin.map_conj_map_conj_inv M' m⁻¹
  rw [inv_inv, heq] at h2
  rw [← h2]
  exact A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hm)

theorem exists_isHStar (h331 : Stmt3_3_1) (h : Hyp10 G T L I) :
    ∃ H : Subgroup G, IsHStar T (fsuM T L) H :=
  (stmt331_B h331 h).2.2.1

omit [Finite G] in
theorem mem_pCoreOf_centralizer {v : G} (hv : IsPGroup 2 (Subgroup.zpowers v)) :
    v ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.zpowers v ≤ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hnorm : Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    have h1 : Subgroup.centralizer ({v} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1]
    exact Subgroup.centralizer_le_normalizer _
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm hv
    (Subgroup.mem_zpowers v)

theorem exists_inM_centralizer {v : G} (hv : IsPGroup 2 (Subgroup.zpowers v)) (hv1 : v ≠ 1) :
    ∃ M' : Subgroup G, InM (Subgroup.centralizer ({v} : Set G)) M' := by
  refine CFSG.Quasithin.exists_inM_of_pCoreOf_ne_bot fun hbot => hv1 ?_
  have := mem_pCoreOf_centralizer hv
  rwa [hbot, Subgroup.mem_bot] at this

end CFSG.Quasithin.Vol2.Ch10.SecB
