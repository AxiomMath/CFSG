module

public import CFSG.RankThree.GF2n.Smith81.Sec2Assembly
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.LinLane
import CFSG.RankThree.GF2n.Smith81.Orth216Odd
import CFSG.RankThree.GF2n.Smith81.Sec212Lanes
import CFSG.RankThree.GF2n.Smith81.Lin3Holds
import CFSG.RankThree.GF2n.Smith81.Lin22
import CFSG.RankThree.GF2n.Smith81.Lin216Count
import CFSG.RankThree.GF2n.Smith81.Sec220Local
import CFSG.RankThree.GF2n.Smith81.Lin212ComplRoot
import CFSG.RankThree.GF2n.Smith81.Sec217Final
public import CFSG.RankThree.GF2n.Smith81.Sec215
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem exists_mem_of_mem_conj_pair {V₁ V₂ W : Subgroup G} {g a : G}
    (hW : W = conjSubgroup g V₁ ∨ W = conjSubgroup g V₂) (ha : a ∈ W) :
    ∃ b : G, (b ∈ V₁ ∨ b ∈ V₂) ∧ a = g * b * g⁻¹ := by
  rcases hW with hW | hW
  · refine ⟨g⁻¹ * a * g, Or.inl ?_, by group⟩
    rw [hW, mem_conjSubgroup] at ha
    exact ha
  · refine ⟨g⁻¹ * a * g, Or.inr ?_, by group⟩
    rw [hW, mem_conjSubgroup] at ha
    exact ha

theorem le_Q_of_conj_inf_Z_ne_bot [Finite G]
    {M Q Z B U₁ U₂ W : Subgroup G} {v : G} (hc : Ctx M Q Z B)
    (h212 : Lin212Prop M Q Z B U₁ U₂) (hWM : W ≤ M)
    (hclW : ∀ a ∈ W, a ≠ 1 → InZClass Z a) (hvW : v ∈ W) (hvZ : v ∈ Z) (hv1 : v ≠ 1) :
    W ≤ Q := by
  by_contra h
  obtain ⟨a, haW, haQ⟩ := Set.not_subset.mp h
  have ha1 : a ≠ 1 := fun h1 => haQ (h1 ▸ Q.one_mem)
  obtain ⟨c, hcv⟩ := exists_conj_of_inZClass hc.hyp (u := v) (v := a)
    ⟨1, v, hvZ, hv1, by group⟩ (hclW a haW ha1)
  have hva : IsConj v a := isConj_iff.mpr ⟨c, hcv⟩
  obtain ⟨X, hs⟩ := exists_sit_of_isConj hc.hyp hvZ hva (hWM haW) haQ
  have h4 := (h212 X a hs).2.2.2.1
  have havW : a * v ∈ W := W.mul_mem haW hvW
  have hav1 : a * v ≠ 1 := by
    intro h
    apply haQ
    have e : a = v⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [e]
    exact hc.hyp.Z_normal.1 (Z.inv_mem hvZ)
  exact hv1 (h4 v hvZ (hclW (a * v) havW hav1))

theorem linPair_eq_of_conj_inf_ne_bot [Finite G]
    {M Q Z B U₁ U₂ V₁ V₂ : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B)
    (h212 : Lin212Prop M Q Z B U₁ U₂) (hS : LinSetup M Q Z B n V₁ V₂)
    (hcl : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {W : Subgroup G}
    (hW : ∃ g : G, W = conjSubgroup g V₁ ∨ W = conjSubgroup g V₂) (hWZ : W ⊓ Z ≠ ⊥) :
    W = V₁ ∨ W = V₂ := by
  have H : StrothHyp M Q Z := hc.hyp
  obtain ⟨-, hV₁Q, -, hV₂Q, -, -, -, -, hV₁card, hV₂card⟩ := hS.basic
  have hcl₂ : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₂ ∨ v ∈ V₁) := by
    intro v hv hv1
    rw [hcl v hv hv1]
    exact or_comm
  have hsq₁ : ∀ v ∈ V₁, v * v = 1 := Lin31Prop.sq_eq_one H hV₁Q hcl
  have hsq₂ : ∀ v ∈ V₂, v * v = 1 := Lin31Prop.sq_eq_one H hV₂Q hcl₂
  obtain ⟨⟨v, hvWZ⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWZ
  have hvW : v ∈ W := (Subgroup.mem_inf.mp hvWZ).1
  have hvZ : v ∈ Z := (Subgroup.mem_inf.mp hvWZ).2
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  obtain ⟨g, hWg⟩ := hW
  have hsqW : ∀ a ∈ W, a * a = 1 := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := exists_mem_of_mem_conj_pair hWg ha
    have h : b * b = 1 := hb.elim (fun h1 => hsq₁ b h1) (fun h2 => hsq₂ b h2)
    rw [hba]
    have e : g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
    rw [e, h]
    group
  have habW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := abelian_of_sq hsqW
  have hWC : W ≤ Subgroup.centralizer ({v} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (habW a ha v hvW)
  have hWM : W ≤ M := hWC.trans (centralizer_le_M H hvZ hv1)
  have hclW : ∀ a ∈ W, a ≠ 1 → InZClass Z a := by
    intro a ha ha1
    obtain ⟨b, hb, hba⟩ := exists_mem_of_mem_conj_pair hWg ha
    have hb1 : b ≠ 1 := by
      intro h
      apply ha1
      rw [hba, h]
      group
    have hbQ : b ∈ Q := hb.elim (fun h1 => hV₁Q h1) (fun h2 => hV₂Q h2)
    rw [hba]
    exact ((hcl b hbQ hb1).mpr hb).conj g
  have hWQ : W ≤ Q := le_Q_of_conj_inf_Z_ne_bot hc h212 hWM hclW hvW hvZ hv1
  have hWsub : (W : Set G) ⊆ (V₁ : Set G) ∪ (V₂ : Set G) := by
    intro w hwW
    by_cases hw1 : w = 1
    · exact Or.inl (by rw [hw1]; exact V₁.one_mem)
    · exact (hcl w (hWQ hwW) hw1).mp (hclW w hwW hw1)
  have hcardW₁ : Nat.card W = Nat.card V₁ := by
    rcases hWg with hWg | hWg
    · exact IsZConjugate.card_eq ⟨g, hWg⟩
    · rw [hWg, IsZConjugate.card_eq (Z := V₂) ⟨g, rfl⟩, hV₂card, hV₁card]
  have hcardW₂ : Nat.card W = Nat.card V₂ := by
    rcases hWg with hWg | hWg
    · rw [hWg, IsZConjugate.card_eq (Z := V₁) ⟨g, rfl⟩, hV₁card, hV₂card]
    · exact IsZConjugate.card_eq ⟨g, hWg⟩
  rcases SubgroupClass.subset_union.mp hWsub with hWV | hWV
  · left
    exact Subgroup.eq_of_le_of_card_ge hWV (le_of_eq hcardW₁.symm)
  · right
    exact Subgroup.eq_of_le_of_card_ge hWV (le_of_eq hcardW₂.symm)

theorem exists_count_of_conj_module [Finite G]
    {M Q Z B V₁ V₂ W₁ W₂ W : Subgroup G} {n : ℕ} {z y h : G}
    (hc : Ctx M Q Z B) (h212 : Lin212Prop M Q Z B V₁ V₂)
    (hSW : LinSetup M Q Z B n W₁ W₂) (hn : 2 ≤ n)
    (h31 : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ W₁ ∨ v ∈ W₂))
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hW : W = W₁ ∨ W = W₂)
    (hCW : conjSubgroup y⁻¹ (conjSubgroup h Z) ≤ W) :
    ∃ S : Subgroup G, S ≤ QB (conjSubgroup y Z) ⊓ QB (conjSubgroup h Z) ∧
      (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧ Nat.card Z ^ 2 < Nat.card S := by
  have H : StrothHyp M Q Z := hc.hyp
  obtain ⟨-, hW₁Q, -, hW₂Q, -, -, -, -, hW₁card, hW₂card⟩ := hSW.basic
  have hWQ : W ≤ Q := by
    rcases hW with hW | hW
    · rw [hW]
      exact hW₁Q
    · rw [hW]
      exact hW₂Q
  have hCS : conjSubgroup h Z ≤ conjSubgroup y W := by
    intro c hc
    rw [mem_conjSubgroup]
    have hmem : y⁻¹ * c * y ∈ conjSubgroup y⁻¹ (conjSubgroup h Z) := by
      rw [mem_conjSubgroup]
      have e : (y⁻¹)⁻¹ * (y⁻¹ * c * y) * y⁻¹ = c := by group
      rw [e]
      exact hc
    exact hCW hmem
  have hWconj : ∃ g : G, conjSubgroup h⁻¹ (conjSubgroup y W) = conjSubgroup g W₁ ∨
      conjSubgroup h⁻¹ (conjSubgroup y W) = conjSubgroup g W₂ := by
    rcases hW with hW | hW
    · refine ⟨h⁻¹ * y, Or.inl ?_⟩
      rw [hW, conjSubgroup_mul]
    · refine ⟨h⁻¹ * y, Or.inr ?_⟩
      rw [hW, conjSubgroup_mul]
  have hZle : Z ≤ conjSubgroup h⁻¹ (conjSubgroup y W) := by
    have hCeq : conjSubgroup h⁻¹ (conjSubgroup h Z) = Z := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [← hCeq]
    exact Subgroup.map_mono hCS
  have hWZ : conjSubgroup h⁻¹ (conjSubgroup y W) ⊓ Z ≠ ⊥ := by
    intro hbot
    have hle : Z ≤ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact le_inf hZle le_rfl
    exact Z_ne_bot H (le_bot_iff.mp hle)
  have hpair := linPair_eq_of_conj_inf_ne_bot hc h212 hSW h31 hWconj hWZ
  have hSQB : conjSubgroup y W ≤ conjSubgroup h Q := by
    have h1 : conjSubgroup y W =
        conjSubgroup h (conjSubgroup h⁻¹ (conjSubgroup y W)) := by
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    rw [h1]
    rcases hpair with hp | hp
    · rw [hp]
      exact Subgroup.map_mono hW₁Q
    · rw [hp]
      exact Subgroup.map_mono hW₂Q
  refine ⟨conjSubgroup y W, ?_, ?_, ?_⟩
  · refine le_inf ?_ ?_
    · rw [QB_conj_eq H y]
      intro s hs
      rw [mem_conjSubgroup] at hs ⊢
      exact hWQ hs
    · rw [QB_conj_eq H h]
      exact hSQB
  · intro s hs hs1
    have hs' : y⁻¹ * s * y ∈ W := mem_conjSubgroup.mp hs
    have hs'1 : y⁻¹ * s * y ≠ 1 := by
      intro h1
      apply hs1
      have e : s = y * (y⁻¹ * s * y) * y⁻¹ := by group
      rw [e, h1]
      group
    have hs'cl : InZClass Z (y⁻¹ * s * y) := by
      rcases hW with hW | hW
      · exact (h31 _ (hWQ hs') hs'1).mpr (Or.inl (hW ▸ hs'))
      · exact (h31 _ (hWQ hs') hs'1).mpr (Or.inr (hW ▸ hs'))
    have hcl : InZClass Z s := by
      have := hs'cl.conj y
      simpa [mul_assoc] using this
    exact isConj_of_inZClass H hz hz1 (IsZConjugate.self Z) hcl
  · have hcard : Nat.card (conjSubgroup y W) = Nat.card Z ^ (n + 1) := by
      rw [IsZConjugate.card_eq (Z := W) ⟨y, rfl⟩]
      rcases hW with hW | hW
      · rw [hW, hW₁card]
      · rw [hW, hW₂card]
    rw [hcard]
    exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega)

theorem smith216CountLin [Finite G] {M Q Z B V₁ V₂ : Subgroup G}
    {n : ℕ} (hc : Ctx M Q Z B) (hn : 2 ≤ n) (h3 : Lin3Facts M Q Z B n V₁ V₂) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) {A C : Subgroup G} (hA : IsZConjugate Z A)
    (hC : IsZConjugate Z C) (hCA : C ≤ QB A) :
    ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
      Nat.card Z ^ 2 < Nat.card S := by
  have H : StrothHyp M Q Z := hc.hyp
  obtain ⟨W₁, W₂, hSW, -, h31⟩ := h3.h31
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨h, rfl⟩ := hC
  have hQeq : QB (conjSubgroup y Z) = conjSubgroup y Q := QB_conj_eq H y
  have hCQ : conjSubgroup h Z ≤ conjSubgroup y Q := by rw [← hQeq]; exact hCA
  have hCinv : (conjSubgroup y⁻¹ (conjSubgroup h Z) : Set G) ⊆
      (W₁ : Set G) ∪ (W₂ : Set G) := by
    intro c hc
    have hcC : y * c * y⁻¹ ∈ conjSubgroup h Z := by
      have h1 := (mem_conjSubgroup (g := y⁻¹) (T := conjSubgroup h Z) (x := c)).mp hc
      simpa using h1
    by_cases hc1 : c = 1
    · exact Or.inl (by rw [hc1]; exact W₁.one_mem)
    have hc'1 : y * c * y⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      have e : c = y⁻¹ * (y * c * y⁻¹) * y := by group
      rw [e, h1]
      group
    have hcQ : c ∈ Q := by
      have h1 := hCQ hcC
      rw [mem_conjSubgroup] at h1
      have e : y⁻¹ * (y * c * y⁻¹) * y = c := by group
      rwa [e] at h1
    have hccl : InZClass Z c := by
      have h1 : InZClass Z (y * c * y⁻¹) := inZClass_of_mem_root ⟨h, rfl⟩ hcC hc'1
      have := h1.conj y⁻¹
      simpa [mul_assoc] using this
    exact (h31 c hcQ hc1).mp hccl
  rcases SubgroupClass.subset_union.mp hCinv with hle | hle
  · exact exists_count_of_conj_module hc h3.h212 hSW hn h31 hz hz1 (Or.inl rfl) hle
  · exact exists_count_of_conj_module hc h3.h212 hSW hn h31 hz hz1 (Or.inr rfl) hle

theorem smith216_of_lin3 [Finite G] {M Q Z B V₁ V₂ : Subgroup G}
    {n : ℕ} (hc : Ctx M Q Z B) (hn : 2 ≤ n) (h3 : Lin3Facts M Q Z B n V₁ V₂) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) {x z' w y : G} (hx : IsConj z x) (hz' : IsConj z z')
    (hw : IsConj z w) (hy : IsConj z y) (hxz : Commute x z') (hzw : Commute z' w)
    (hwy : Commute w y) : ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  refine Smith216Odd.smith_2_16_of_28 hc.hyp hz hz1 ?_ ?_ ?_ ?_ hx hz' hw hy hxz hzw hwy
  · intro x' hxM hxQ hxc y' hy'cos hy'c
    obtain ⟨X, hs⟩ := exists_sit_of_isConj hc.hyp hz hxc hxM hxQ
    have h1 := conjClassSet_inter_cosetSet_eq_of_inZClass hz hz1 hxc
      (h3.h212 X x' hs).2.2.2.1
    have hmem : y' ∈ conjClassSet z ∩ cosetSet x' Z := ⟨hy'c, hy'cos⟩
    rw [h1] at hmem
    exact hmem
  · exact isRootInvolutionSet_of_lin213Prop hc.hyp hz hz1 h3.h213
  · intro A C hA hC _ hCA
    exact smith216CountLin hc hn h3 hz hz1 hA hC hCA
  · intro X x' hs
    obtain ⟨A, hAconj, hAQ⟩ := h3.h28 X x' hs
    obtain ⟨g, hgA⟩ := hAconj
    obtain ⟨z₀, hz₀, hz₀1⟩ := exists_ne_one_mem_Z hc.hyp
    have hvA : g * z₀ * g⁻¹ ∈ A := by
      rw [hgA, mem_conjSubgroup]
      simpa [mul_assoc] using hz₀
    have hvA' : g * z₀ * g⁻¹ ∈ conjSubgroup g Z := hgA ▸ hvA
    have hv1 : g * z₀ * g⁻¹ ≠ 1 := by
      intro h1
      apply hz₀1
      have e : z₀ = g⁻¹ * (g * z₀ * g⁻¹) * g := by group
      rw [e, h1]
      group
    have hxcl : InZClass Z x' := inZClass_of_mem_root hs.conj hs.mem hs.ne_one
    have hvcl : InZClass Z (g * z₀ * g⁻¹) := inZClass_of_mem_root ⟨g, rfl⟩ hvA' hv1
    obtain ⟨d, hd⟩ := exists_conj_of_inZClass hc.hyp hxcl hvcl
    exact ⟨g * z₀ * g⁻¹, isConj_iff.mpr ⟨d, hd⟩, (hAQ hvA).1, (hAQ hvA).2⟩

theorem smith216E6_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ),
      Smith1981Below (Nat.card G) → Ctx M Q Z B → TypeE6 M Q Z B n → ∀ z ∈ Z, z ≠ 1 →
        ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w → IsConj z y →
          Commute x z' → Commute z' w → Commute w y →
            ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  intro G _ _ M Q Z B n hb hc hE6 z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  obtain ⟨V₁, V₂, hS, hn2⟩ := exists_linSetup_of_typeE6 lin22Statement_holds hc hE6
  have h3 : Lin3Facts M Q Z B n V₁ V₂ :=
    lin3Statement_holds G M Q Z B n V₁ V₂ hb hc hS hn2
  exact smith216_of_lin3 hc hn2 h3 hz hz1 hx hz' hw hy hxz hzw hwy

theorem smith216_of_E_orth (hE : Smith216EStatement)
    (hOrth : Smith216OrthStatement) : Smith216Statement := by
  intro G _ _ M Q Z B hb hrem z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  rcases hrem.remaining with hO | hE' | ⟨n, hn⟩
  · exact hOrth G M Q Z B hb hrem hO z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  · exact hE G M Q Z B hb ⟨hrem.toCfg, hE'⟩ z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  · exact smith216E6_holds G M Q Z B n hb hrem.ctx hn z hz hz1 x z' w y hx hz' hw hy hxz hzw
      hwy

section RootClass

theorem linRootClass_of_lin3 [Finite G] {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ}
    (hb : Smith1981Below (Nat.card G)) (hrem : RemCfg M Q Z B) (hn : 2 ≤ n)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g} ∧
      ∀ w : G, IsConj z w → ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹ := by
  have hc := hrem.ctx
  have h213 := isRootInvolutionSet_of_lin213Prop hc.hyp hz hz1 h3.h213
  have hred : ∀ x ∈ conjClassSet z, ∀ z' ∈ conjClassSet z, ∀ w ∈ conjClassSet z,
      ∀ y ∈ conjClassSet z, Commute x z' → Commute z' w → Commute w y →
        ∃ v ∈ conjClassSet z, Commute x v ∧ Commute v y := by
    intro x hx z' hz' w hw y hy hxz hzw hwy
    obtain ⟨v, hv, hxv, hvy⟩ :=
      smith216_of_lin3 hc hn h3 hz hz1 hx hz' hw hy hxz hzw hwy
    exact ⟨v, hv, hxv, hvy⟩
  have hdiam := diam_two_of_connected hred
    (fun x hx y hy => smith217_holds G M Q Z B hb hrem z hz hz1 x y hx hy)
  exact ⟨isRootInvolutionSet_conjClassSet hc.hyp hz hz1 h213 hdiam,
    fun w hw => isConj_normalClosure hc.hyp hz hz1 w hw⟩

theorem linRootClass_holds : LinRootClassStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hC hE6 hS h4 h3 z hz hz1
  have hrem : RemCfg M Q Z B := ⟨⟨hc, hC⟩, Or.inr (Or.inr ⟨n, hE6⟩)⟩
  exact linRootClass_of_lin3 hb hrem (by omega) h3 hz hz1

end RootClass

end CFSG.RankThree.GF2n.Smith81
