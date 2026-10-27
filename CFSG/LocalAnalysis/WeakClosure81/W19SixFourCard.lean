module

public import CFSG.LocalAnalysis.WeakClosure81.W19ThirteenMod
public import CFSG.LocalAnalysis.WeakClosure81.W19InvAbel
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem card_le_of_assumption131
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {G₁ A₁ : Subgroup (LGL 2 W)}
    (h : Assumption131 G₁ {B | ∃ g ∈ G₁, B = cj g A₁} commSub 1) (hA2 : Nat.card A₁ = 2)
    (hN : IsPGroup 2 ↥(G₁ ⊓ normalizer (A₁ : Set (LGL 2 W))))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X₁ : Subgroup (LGL 2 W)} (hXG : X₁ ≤ G₁)
    (hXexp : ∀ x ∈ X₁, x ^ p = 1)
    (hAX : A₁ ≤ normalizer ((X₁ ⊔ pCoreOf 2 G₁ : Subgroup (LGL 2 W)) : Set (LGL 2 W))) :
    Nat.card X₁ ≤ p := by
  classical
  by_cases hX1 : X₁ = ⊥
  · rw [hX1, Subgroup.card_bot]
    exact hp.one_lt.le
  set Rc : Subgroup (LGL 2 W) := pCoreOf 2 G₁ with hRc
  have hR2 : IsPGroup 2 Rc := (CFSG.pCore_isPGroup (p := 2) (G := ↥G₁)).map G₁.subtype
  have hGN : G₁ ≤ normalizer (Rc : Set (LGL 2 W)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁
  have hA₁mem : A₁ ∈ {B | ∃ g ∈ G₁, B = cj g A₁} := ⟨1, G₁.one_mem, (cj_one A₁).symm⟩
  have hA₁G : A₁ ≤ G₁ := h.le_G A₁ hA₁mem
  have hA₁ne : A₁ ≠ ⊥ := h.ne_bot A₁ hA₁mem
  have hXR : X₁ ⊓ Rc = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨j, hj⟩ := hR2 ⟨x, hx2⟩
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact E1.mem_of_pow_mem_two_p (N := ⊥) hp hp2 (k := 1) (j := j)
      (by simpa using hXexp x hx1) (by simpa using hj')
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₁ne
  have haG : a ∈ G₁ := hA₁G haA
  have ha2 : a * a = 1 := by
    have hd : orderOf (⟨a, haA⟩ : ↥A₁) ∣ 2 := by
      have h0 := orderOf_dvd_natCard (⟨a, haA⟩ : ↥A₁)
      rwa [hA2] at h0
    have h2 : (⟨a, haA⟩ : ↥A₁) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa [pow_two] using congrArg Subtype.val h2
  have hA1uniq : ∀ b ∈ A₁, b = 1 ∨ b = a := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · refine Or.inr ?_
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥A₁)).1 hA2
      have e1 : (⟨b, hb⟩ : ↥A₁) = y := hy _ (fun h' => hb1 (congrArg Subtype.val h'))
      have e2 : (⟨a, haA⟩ : ↥A₁) = y := hy _ ha1
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hconj : ∀ x ∈ X₁, ⁅a, x⁆ ∈ Rc → ∀ y ∈ A₁ ⊔ Rc, x * y * x⁻¹ ∈ A₁ ⊔ Rc := by
    intro x hx hcomm y hy
    have hxG : x ∈ G₁ := hXG hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A₁ Rc
      (hA₁G.trans hGN)] at hy
    obtain ⟨b, hb, r, hr, rfl⟩ := hy
    have hxr : x * r * x⁻¹ ∈ Rc := (Subgroup.mem_normalizer_iff.1 (hGN hxG) r).1 hr
    have hxb : x * b * x⁻¹ ∈ A₁ ⊔ Rc := by
      rcases hA1uniq b hb with hb1 | hba
      · rw [hb1]
        simp
      · rw [hba]
        have h3 : x * a * x⁻¹ = ⁅x, a⁆ * a := by
          rw [commutatorElement_def]
          group
        rw [h3]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left haA)
        rw [← commutatorElement_inv]
        exact Rc.inv_mem hcomm
    have e : x * (b * r) * x⁻¹ = (x * b * x⁻¹) * (x * r * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxb (Subgroup.mem_sup_right hxr)
  have hfpf : ∀ x ∈ X₁, ⁅a, x⁆ ∈ Rc → x ∈ Rc := by
    intro x hx hcomm
    have hxG : x ∈ G₁ := hXG hx
    have hcomm' : ⁅a, x⁻¹⁆ ∈ Rc := by
      have h4 : ⁅a, x⁻¹⁆ = x⁻¹ * (⁅a, x⁆)⁻¹ * x := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [h4]
      have h5 := (Subgroup.mem_normalizer_iff.1 (hGN (G₁.inv_mem hxG)) _).1 (Rc.inv_mem hcomm)
      simpa using h5
    have hxN : x ∈ normalizer ((A₁ ⊔ Rc : Subgroup (LGL 2 W)) : Set (LGL 2 W)) := by
      refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => hconj x hx hcomm y hy, fun hy => ?_⟩
      have h6 := hconj x⁻¹ (X₁.inv_mem hx) hcomm' _ hy
      simpa [mul_assoc] using h6
    obtain ⟨m, hm, r, hr, hxmr⟩ := exists_mul_of_mem_normalizer_sup h hA2 hxG hxN
    have hmem : x ∈ (G₁ ⊓ normalizer (A₁ : Set (LGL 2 W))) ⊔ Rc := by
      rw [hxmr]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hr)
    obtain ⟨e, he⟩ := exists_pow_mem_of_mem_sup_pGroup hN (inf_le_left.trans hGN) hmem
    refine E1.mem_of_pow_mem_two_p (N := Rc) hp hp2 (k := 1) (j := e) ?_ he
    rw [pow_one, hXexp x hx]
    exact Rc.one_mem
  obtain ⟨hinv, hcommR⟩ := inv_and_comm_of_fixedPointFree (R := Rc) (X := X₁) (a := a)
    (hXG.trans hGN) (hGN haG) (hAX haA) (by rw [ha2]; exact Rc.one_mem) hfpf
  have hfaith : ∀ b ∈ A₁, (∀ x ∈ X₁, ⁅b, x⁆ ∈ Rc) → b ∈ Rc := by
    intro b hb hbx
    rcases hA1uniq b hb with hb1 | hba
    · rw [hb1]
      exact Rc.one_mem
    · exfalso
      rw [hba] at hbx
      apply hX1
      rw [eq_bot_iff]
      intro x hx
      have hxR : x ∈ X₁ ⊓ Rc := ⟨hx, hfpf x hx (hbx x hx)⟩
      rwa [hXR] at hxR
  have hXA : X₁ ≤ ⁅X₁ ⊔ Rc, A₁⁆ ⊔ Rc := by
    intro x hx
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have hxa : ⁅x, a⁆ ∈ ⁅X₁ ⊔ Rc, A₁⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hx) haA
    have e : x ^ 2 = ⁅x, a⁆ * (a * x * a⁻¹ * x) := by
      rw [commutatorElement_def, pow_two]
      group
    have hx2 : x ^ 2 ∈ ⁅X₁ ⊔ Rc, A₁⁆ ⊔ Rc := by
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxa) (Subgroup.mem_sup_right (hinv x hx))
    have e2 : x = (x ^ 2) ^ (k + 1) := by
      calc x = x ^ (p + 1) := by rw [pow_succ, hXexp x hx, one_mul]
        _ = (x ^ 2) ^ (k + 1) := by
          rw [← pow_mul]
          congr 1
          omega
    have h7 := Subgroup.pow_mem _ hx2 (k + 1)
    rwa [← e2] at h7
  exact (thirteen_four_mod h763 h hA2 hp hp2 hXG hXexp hXR hcommR hAX hXA hfaith).le

end CFSG.LocalAnalysis.WeakClosure81

end
