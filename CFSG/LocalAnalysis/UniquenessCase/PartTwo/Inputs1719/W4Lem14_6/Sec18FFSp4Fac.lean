module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFUnique
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Inn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.K148
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}
variable {Y Z : Submodule (ZMod 2) V}

theorem sp4_lemmaR [Finite G] [Finite V]
    {L B : Subgroup G} {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K)
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm1 : 1 ≤ m)
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) (hcost : secCost ρ B Y Z ≤ m) :
    ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y := by
  classical
  haveI : IsSimpleGroup (antiSp K) := isSimpleGroup_antiSp_of_four_le (four_le_card hn hK)
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  obtain ⟨hBc, hB2⟩ := elemAb_facts hBe
  have hLB : L ≤ L ⊔ B := le_sup_left
  have hBLB : B ≤ L ⊔ B := le_sup_right
  have hYL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := fun l hl => hY l (hLB hl)
  have hZL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z := fun l hl => hZ l (hLB hl)
  by_contra hnot
  push Not at hnot
  obtain ⟨W, hWL, hZW, hWY, hWZ, hWY'⟩ := hnot
  obtain ⟨Y₁, hZY₁, hY₁W, hY₁L, hY₁min⟩ :=
    exists_minimal_invariant hWL (lt_of_le_of_ne hZW (Ne.symm hWZ))
  have hZY₁' : Z ≤ Y₁ := hZY₁.le
  have hY₁Y : Y₁ ≤ Y := hY₁W.trans hWY
  have hY₁ne : Y₁ ≠ Y := fun h => hWY' (le_antisymm hWY (h ▸ hY₁W))
  set B₁ : Subgroup G := B ⊓ secKer ρ ⊥ Y₁ with hB₁
  have hmemB₁ : ∀ b, b ∈ B₁ ↔ b ∈ B ∧ (∀ w ∈ Y₁, ρ b w ∈ Y₁) ∧ ∀ w ∈ Y₁, ρ b⁻¹ w ∈ Y₁ := fun b => by
    rw [hB₁, Subgroup.mem_inf, mem_secKer_bot]
  have hB₁B : B₁ ≤ B := inf_le_left
  have hinvB : ∀ b ∈ B, b⁻¹ = b := fun b hb => inv_eq_of_mul_eq_one_right (hB2 b hb)
  have hmemB₁' : ∀ b ∈ B, (∀ w ∈ Y₁, ρ b w ∈ Y₁) → b ∈ B₁ := fun b hb h =>
    (hmemB₁ b).2 ⟨hb, h, by rw [hinvB b hb]; exact h⟩
  have hY₁B₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B₁ Y₁ := fun b hb w hw => ((hmemB₁ b).1 hb).2.1 w hw
  have hcen : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
    intro x hx hxc
    have hz : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hxc y y.2).symm
    rw [AutAux.center_eq_bot_of_equiv_antiSp e, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hinner : ∀ b ∈ B, InducesInnerOn L b → b ∈ B₁ := by
    rintro b hb ⟨l, hl, hbl⟩
    have h1 := sub_mem_of_inducesInner hcen hBN hBc hB2 hZY hY hZ hirr hb hl hbl
    refine hmemB₁' b hb fun w hw => ?_
    rw [← sub_add_cancel (ρ b w) (ρ l w)]
    exact Y₁.add_mem (hZY₁' (h1 w (hY₁Y hw))) (hY₁L l hl w hw)
  have hexb₀ : ∃ b₀ ∈ B, b₀ ∉ B₁ := by
    by_contra hcon
    push Not at hcon
    have hY₁B : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₁ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.K148.isInvariant_sup hY₁L
        fun b hb w hw => ((hmemB₁ b).1 (hcon b hb)).2.1 w hw
    rcases hirr Y₁ hY₁B hZY₁' hY₁Y with h | h
    · exact hZY₁.ne h.symm
    · exact hY₁ne h
  obtain ⟨b₀, hb₀B, hb₀B₁⟩ := hexb₀
  have hprod : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ∉ B₁ → b₂ ∉ B₁ → b₁ * b₂ ∈ B₁ := by
    intro b₁ hb₁ b₂ hb₂ h₁ h₂
    rcases inducesInnerOn_trichotomy (by omega : 1 ≤ n) hK e (hBN hb₁) (hBN hb₂)
      (hB2 b₁ hb₁) (hB2 b₂ hb₂)
      with h | h | h
    · exact absurd (hinner b₁ hb₁ h) h₁
    · exact absurd (hinner b₂ hb₂ h) h₂
    · exact hinner _ (B.mul_mem hb₁ hb₂) h
  have hcardB : Nat.card ↥B = 2 * Nat.card ↥B₁ := card_eq_two_mul_of_mul_mem hB₁B hb₀B hb₀B₁ hprod
  have hb₀inv : b₀⁻¹ = b₀ := hinvB b₀ hb₀B
  have hb₀b₀ : ∀ v, ρ b₀ (ρ b₀ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, hB2 b₀ hb₀B, map_one, Module.End.one_apply]
  have hcomm₀ : ∀ b ∈ B, b * b₀ = b₀ * b := fun b hb => hBc b hb b₀ hb₀B
  have hb₀Z : ∀ z ∈ Z, ρ b₀ z ∈ Z := fun z hz => hZ b₀ (hBLB hb₀B) z hz
  set W₀ := Y₁.map (ρ b₀) with hW₀
  have hmemW₀ : ∀ v, v ∈ W₀ ↔ ρ b₀ v ∈ Y₁ := by
    intro v
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hb₀b₀]
      exact hy
    · intro h
      exact ⟨ρ b₀ v, h, hb₀b₀ v⟩
  have hW₀L : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W₀ := isInvariant_map hY₁L fun h hh => by
    have := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb₀B)) h).1 hh
    simpa using this
  have hW₀B₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B₁ W₀ := isInvariant_map hY₁B₁ fun h hh => by
    rw [hb₀inv, mul_assoc, hcomm₀ h (hB₁B hh), ← mul_assoc, hB2 b₀ hb₀B, one_mul]
    exact hh
  have hZW₀ : Z ≤ W₀ := fun z hz => (hmemW₀ z).2 (hZY₁' (hb₀Z z hz))
  have hW₀Y : W₀ ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact hY b₀ (hBLB hb₀B) y (hY₁Y hy)
  have hinf : Y₁ ⊓ W₀ = Z := by
    have hI : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (Y₁ ⊓ W₀) := fun l hl v hv =>
      Submodule.mem_inf.2
        ⟨hY₁L l hl v (Submodule.mem_inf.1 hv).1, hW₀L l hl v (Submodule.mem_inf.1 hv).2⟩
    rcases hY₁min _ hI (le_inf hZY₁' hZW₀) inf_le_left with h | h
    · exact h
    · exfalso
      exact hb₀B₁ (hmemB₁' b₀ hb₀B fun w hw => (hmemW₀ w).1 ((inf_eq_left.1 h) hw))
  have hsupB₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B₁ (Y₁ ⊔ W₀) := isInvariant_sup_mod hY₁B₁ hW₀B₁
  have hsupb₀ : ∀ v ∈ Y₁ ⊔ W₀, ρ b₀ v ∈ Y₁ ⊔ W₀ := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact (Y₁ ⊔ W₀).add_mem (Submodule.mem_sup_right ⟨y, hy, rfl⟩)
      (Submodule.mem_sup_left ((hmemW₀ w).1 hw))
  have hsupB : ∀ b ∈ B, ∀ v ∈ Y₁ ⊔ W₀, ρ b v ∈ Y₁ ⊔ W₀ := by
    intro b hb v hv
    by_cases hbB₁ : b ∈ B₁
    · exact hsupB₁ b hbB₁ v hv
    · have hbb₀ := hprod b hb b₀ hb₀B hbB₁ hb₀B₁
      have h1 : ρ b v = ρ (b * b₀) (ρ b₀ v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_assoc, hB2 b₀ hb₀B, mul_one]
      rw [h1]
      exact hsupB₁ _ hbb₀ _ (hsupb₀ v hv)
  have hsupLB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (Y₁ ⊔ W₀) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.isInvariant_sup
      (isInvariant_sup_mod hY₁L hW₀L) hsupB
  have hsup : Y₁ ⊔ W₀ = Y := by
    rcases hirr _ hsupLB (hZY₁'.trans le_sup_left) (sup_le hY₁Y hW₀Y) with h | h
    · exfalso
      have h1 : Y₁ ≤ Z := h ▸ (le_sup_left : Y₁ ≤ Y₁ ⊔ W₀)
      exact hZY₁.ne (le_antisymm hZY₁' h1)
    · exact h
  have hnt₁ : ∃ l ∈ L, ∃ y ∈ Y₁, ρ l y - y ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl, y, hy, hly⟩ := hnt
    rw [← hsup] at hy
    obtain ⟨y₁, hy₁, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    apply hly
    have hw' : ρ l w - w ∈ Z := by
      have hl' : b₀ * l * b₀ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hBN hb₀B) l).1 hl
        rwa [hb₀inv] at this
      have h1 := hcon _ hl' _ ((hmemW₀ w).1 hw)
      have h2 : ρ (b₀ * l * b₀) (ρ b₀ w) - ρ b₀ w = ρ b₀ (ρ l w - w) := by
        rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb₀b₀]
      rw [h2] at h1
      have h3 := hb₀Z _ h1
      rwa [hb₀b₀] at h3
    have h4 : ρ l (y₁ + w) - (y₁ + w) = (ρ l y₁ - y₁) + (ρ l w - w) := by
      rw [map_add]
      abel
    rw [h4]
    exact Z.add_mem (hcon l hl y₁ hy₁) hw'
  have hR1 : finrank (ZMod 2) ↥Y₁ - finrank (ZMod 2) ↥Z ≤ secCost ρ B Y Z := by
    obtain ⟨P, hP⟩ : ∃ P, P = Y ⊓ P22x.modFix ρ Z B := ⟨_, rfl⟩
    have hPY₁ : P ⊓ Y₁ ≤ Z := by
      intro v hv
      obtain ⟨hvP, hvY₁⟩ := Submodule.mem_inf.1 hv
      rw [hP] at hvP
      have hvfix : ρ b₀ v - v ∈ Z := (Submodule.mem_inf.1 hvP).2 b₀ hb₀B
      have h1 : ρ b₀ v ∈ Y₁ := by
        rw [← sub_add_cancel (ρ b₀ v) v]
        exact Y₁.add_mem (hZY₁' hvfix) hvY₁
      have h3 : ρ b₀ v ∈ Z := by
        rw [← hinf]
        exact Submodule.mem_inf.2 ⟨h1, ⟨v, hvY₁, rfl⟩⟩
      have h4 := hb₀Z _ h3
      rwa [hb₀b₀] at h4
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq P Y₁
    have h2 : finrank (ZMod 2) ↥(P ⊔ Y₁) ≤ finrank (ZMod 2) ↥Y :=
      Submodule.finrank_mono (sup_le (hP ▸ inf_le_left) hY₁Y)
    have h3 : finrank (ZMod 2) ↥(P ⊓ Y₁) ≤ finrank (ZMod 2) ↥Z := Submodule.finrank_mono hPY₁
    have h5 : finrank (ZMod 2) ↥Z ≤ finrank (ZMod 2) ↥Y₁ := Submodule.finrank_mono hZY₁'
    rw [secCost, ← hP]
    omega
  have hZmap : Z.map (ρ b₀) = Z := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hb₀Z z hz
    · intro hv
      exact ⟨ρ b₀ v, hb₀Z v hv, hb₀b₀ v⟩
  have hR2 : 2 * secCost ρ B₁ Y₁ Z ≤ secCost ρ B Y Z := by
    have h1 := secCost_mono (ρ := ρ) hB₁B Y Z
    have h2 := secCost_superadd (ρ := ρ) (D := B₁) hZY₁' hY₁Y hY₁B₁
    have h3 : secCost ρ B₁ Y Y₁ = secCost ρ B₁ W₀ Z :=
      secCost_eq_of_isCompl (by rw [sup_comm]; exact hsup) (by rw [inf_comm]; exact hinf)
        hW₀B₁ hY₁B₁
    have h4 := secCost_map (ρ := ρ) (D := B₁) (fun a ha => (hcomm₀ a (hB₁B ha)).symm) Y₁ Z
    rw [hZmap, ← hW₀] at h4
    omega
  have hCB₁ : B ⊓ Subgroup.centralizer (L : Set G) ≤ B₁ := by
    intro b hb
    obtain ⟨hbB, hbc⟩ := Subgroup.mem_inf.1 hb
    refine hmemB₁' b hbB fun w hw => ?_
    rw [hCB b hbB hbc w (hY₁Y hw)]
    exact hw
  have hkerB₁ : B₁ ⊓ secKer ρ Y₁ Z = B ⊓ Subgroup.centralizer (L : Set G) :=
    inf_secKer_eq hBN hY₁L hZ (fun b hb hbc y hy => hCB b hb hbc y (hY₁Y hy)) hnt₁ hB₁B hCB₁
  have hcardB₁ : Nat.card ↥B₁ = 2 ^ (m - 1) * Nat.card ↥(B₁ ⊓ secKer ρ Y₁ Z) := by
    rw [hkerB₁]
    have h1 : 2 * Nat.card ↥B₁ =
        2 * (2 ^ (m - 1) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G))) := by
      rw [← hcardB, hm, ← mul_assoc, ← pow_succ']
      congr 2
      omega
    omega
  have hfr : finrank (ZMod 2) ↥Z + 2 ≤ finrank (ZMod 2) ↥Y₁ := by
    have hlt := Submodule.finrank_lt_finrank_of_lt hZY₁
    by_contra hcon
    have heq : finrank (ZMod 2) ↥Y₁ = finrank (ZMod 2) ↥Z + 1 := by omega
    obtain ⟨l, hl, y, hy, hly⟩ := hnt₁
    exact hly (sub_mem_of_finrank_eq_succ hZY₁' hY₁L hZL heq l hl y hy)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · omega
  have hcost₁ : secCost ρ B₁ Y₁ Z ≤ m - 1 := by omega
  have hB₁e : CFSG.IsElementaryAbelian 2 ↥B₁ := CFSG.IsElementaryAbelian.of_le hBe hB₁B
  have hY₁LB₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B₁) Y₁ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.isInvariant_sup hY₁L hY₁B₁
  have hZLB₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B₁) Z := fun h hh => hZ h (sup_le_sup_left hB₁B L hh)
  obtain ⟨hrk, h2, -⟩ := sec_natural hn hK e hB₁e (hB₁B.trans hBN) hZY₁' hY₁LB₁ hZLB₁ hY₁min hnt₁
    (by omega : 1 ≤ m - 1) hcardB₁ hcost₁
  omega

theorem sp4_secCoords [Finite G] [Finite V]
    {L B : Subgroup G} {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K)
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm1 : 1 ≤ m)
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hirrL : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) (hcost : secCost ρ B Y Z ≤ m) :
    ∃ (i : ℕ) (φ : SecQ Y Z ≃+ (Fin 4 → K)), ∀ (l : ↥L) (q : SecQ Y Z),
      φ (secHom hY hZ (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) l) q) =
        (glMat (((minorAut K ^ i) (e l) : antiSp K) : GL (Fin 4) K)).mulVec (φ q) := by
  classical
  haveI : IsSimpleGroup (antiSp K) := isSimpleGroup_antiSp_of_four_le (four_le_card hn hK)
  have hYL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := fun l hl => hY l (Subgroup.mem_sup_left hl)
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hk := inf_secKer_eq hBN hYL hZ hCB hnt le_rfl inf_le_left
  have hd : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ secKer ρ Y Z) := by rw [hk]; exact hm
  have hLH : L ≤ L ⊔ B := le_sup_left
  have hBH : B ≤ L ⊔ B := le_sup_right
  haveI : Finite (SecQ Y Z) := Module.finite_of_finite (ZMod 2)
  let π : antiSp K →* (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) :=
    (secHom hY hZ).comp ((Subgroup.inclusion hLH).comp e.symm.toMonoidHom)
  have hπx : ∀ x, π x = secHom hY hZ (Subgroup.inclusion hLH (e.symm x)) := fun x => rfl
  have hπ : ∀ l : ↥L, π (e l) = secHom hY hZ (Subgroup.inclusion hLH l) := fun l => by
    rw [hπx, MulEquiv.symm_apply_apply]
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, y, hy, hly⟩ := hnt
      have h1 : π (e ⟨l, hl⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      rw [hπ, secHom_eq_one_iff] at h1
      exact hly (h1 y hy)
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  have hntM : Nontrivial (SecQ Y Z) := by
    obtain ⟨l, hl, y, hy, hly⟩ := hnt
    have hyZ : y ∉ Z := fun hyZ => hly (Z.sub_mem (hZ l (hLH hl) y hyZ) hyZ)
    exact secQ_nontrivial hy hyZ
  have hirrM : ∀ U : Submodule (ZMod 2) (SecQ Y Z), (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine secHom_irr (hY := hY) (hZ := hZ) hLH hZY hirrL U fun l u hu => ?_
    rw [← hπ]
    exact hU _ u hu
  have hnorm : ∀ a ∈ secImg hY hZ B, ∀ x, ∃ y, a * π x * a⁻¹ = π y := by
    intro a ha x
    obtain ⟨y, hy⟩ := secImg_normalizes hLH hBN ha (e.symm x)
    refine ⟨e y, ?_⟩
    rw [hπ y, hπx, hy]
  have hcardA : Nat.card (secImg hY hZ B) = 2 ^ m := by
    have h1 := card_secImg_mul (hY := hY) (hZ := hZ) hBH
    rw [hd] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hA1 : secImg hY hZ B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardA
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm1
    omega
  have hfix := card_fix_secImg (hY := hY) (hZ := hZ) hZY hBH
  have hM := card_secQ (Y := Y) (Z := Z) hZY
  have hZP : Z ≤ Y ⊓ P22x.modFix ρ Z B := le_inf hZY (le_modFix fun a ha => hZ a (hBH ha))
  have hf1 := Submodule.finrank_mono hZP
  have hf2 := Submodule.finrank_mono (inf_le_left : Y ⊓ P22x.modFix ρ Z B ≤ Y)
  have hoff : Nat.card (SecQ Y Z) ≤
      Nat.card (secImg hY hZ B) * Nat.card {q : SecQ Y Z // ∀ a ∈ secImg hY hZ B, a q = q} := by
    rw [hM, hcardA, hfix, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold secCost at hcost
    omega
  obtain ⟨⟨i, φ, hφ⟩, -⟩ := natural_offender_facts hn hK π hπinj hntM hirrM (secImg hY hZ B)
    hnorm (secImg_isElementaryAbelian hBe) hA1 hoff
  exact ⟨i, φ, fun l q => by rw [← hπ l]; exact hφ (e l) q⟩

theorem sp4_factorBound [Finite G] [Finite V]
    {L : Subgroup G} {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* antiSp K) : FactorBound ρ L := by
  intro B hBe hBN m hm1 hm Y Z hZY hY hZ hCB hirr hnt hcost
  have h := (factor_lemma hn hK e hBe hBN hm1 hm hZY hY hZ hCB hirr hnt hcost).1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
