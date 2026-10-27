module

public import CFSG.Quasithin.Vol2.Ch1Unique4
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem conjClosure_eq_of_le_normalizer {L T : Subgroup G}
    (h : T ≤ Subgroup.normalizer (L : Set G)) : conjClosure L T = L :=
  le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (h ht) _).mp hz)
    (le_conjClosure L T)

theorem le_normalizer_conjClosure_of_le {Z H K : Subgroup G}
    (hZ : K ≤ Subgroup.normalizer (Z : Set G)) (hH : K ≤ Subgroup.normalizer (H : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ conjClosure Z H, k * x * k⁻¹ ∈ conjClosure Z H := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have hh' : k * h * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hH hk) h).mp hh
      have hz' : k * z * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hk) z).mp hz
      have := mem_conjClosure hh' hz'
      simpa [mul_assoc] using this
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure Z H).mul_mem ihx ihy
    | inv x _ ihx =>
      simpa [mul_assoc] using (conjClosure Z H).inv_mem ihx
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key k hk x, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem conjClosure_eq_self (h : Hyp11 G T L I n) : conjClosure L T = L :=
  conjClosure_eq_of_le_normalizer h.normal

theorem fsuL0_eq (h : Hyp11 G T L I n) : fsuL0 T L = L :=
  conjClosure_eq_self h

theorem fsuM_eq (h : Hyp11 G T L I n) : fsuM T L = Subgroup.normalizer (L : Set G) := by
  rw [fsuM, fsuL0_eq h]

theorem fsuVM_eq (h : Hyp11 G T L I n) : fsuVM T L I = VM T L I := by
  rw [fsuVM, fsuM_eq h]

theorem fsuCVM_eq (h : Hyp11 G T L I n) : fsuCVM T L I = cVM T L I := by
  rw [fsuCVM, fsuVM_eq h, fsuL0_eq h]

theorem stmt331_B (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    (quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G)) ∧
        L ⊔ T ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
          M' = Subgroup.normalizer (L : Set G)) ∧
      (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧ quasithinIsMaxTwoLocal M₁ ∧
        quasithinIsMaxTwoLocal M₂ ∧ T ≤ M₁ ∧ T ≤ M₂) ∧
      (∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H) ∧
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
        IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) ∧
          ¬ H ≤ Subgroup.normalizer (T : Set G) := by
  have := (h331 G T h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow).2 L h.fsu.maximal
    h.fsu.quasisimple
  rwa [conjClosure_eq_self h] at this

theorem isUniqueM_LT (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
  obtain ⟨⟨hmax, hle, huniq⟩, -⟩ := stmt331_B h331 h
  exact ⟨⟨hmax, hle⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

theorem isMaxTwoLocal_M (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G)) :=
  (isUniqueM_LT h331 h).1.1

theorem normalizer_T_le (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (stmt331_B h331 h).2.2.2.1

theorem isSylowTwoOf_M (h : Hyp11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
  isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow h.normal

theorem isUniqueM_L_sylow (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {Tp : Subgroup G}
    (hTp : QuasithinUnique.IsSylowTwoOf Tp (Subgroup.normalizer (L : Set G))) :
    IsUniqueM (L ⊔ Tp) (Subgroup.normalizer (L : Set G)) := by
  have hU := isUniqueM_LT h331 h
  obtain ⟨m, hm, hmT⟩ := A4.exists_conj_of_isSylowTwoOf (isSylowTwoOf_M h) hTp
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  refine ⟨⟨hU.1.1, sup_le hLM hTp.1⟩, fun M' hM' => ?_⟩
  have hM'' : InM (L ⊔ T) (M'.map (MulAut.conj m⁻¹).toMonoidHom) := by
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

theorem exists_isHStar (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H :=
  (stmt331_B h331 h).2.2.1

theorem isSylowTwoOf_of_isHStar (h : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) : QuasithinUnique.IsSylowTwoOf T H :=
  isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1

theorem isUniqueMaxOver_of_isHStar (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) :=
  ((stmt331_B h331 h).2.2.2.2 H hH).1

theorem not_le_normalizer_of_isHStar (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    ¬ H ≤ Subgroup.normalizer (T : Set G) :=
  ((stmt331_B h331 h).2.2.2.2 H hH).2

theorem minParabolic_of_isHStar (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) :=
  ⟨isSylowTwoOf_of_isHStar h hH, not_le_normalizer_of_isHStar h331 h hH,
    isUniqueMaxOver_of_isHStar h331 h hH⟩

theorem normalizer_le_of_isPGroup (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨P, hP1, hP, rfl⟩ : IsTwoLocal _)
  rw [← (isUniqueM_LT h331 h).2 M' ⟨hM', hLT.trans hle⟩]
  exact hle

end CFSG.Quasithin.Vol2.Ch11.SecA
