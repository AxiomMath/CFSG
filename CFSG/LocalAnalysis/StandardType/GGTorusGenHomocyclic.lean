module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRDefs
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.CentralizerMap
import CFSG.GH74.Uniqueness.Section14Primary
import CFSG.RankThree.PartOne.K1214.CycAlg
import CFSG.GroupTheory.ConjClassGeneration
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.GH74.Uniqueness (primaryComponent mem_primaryComponent primaryComponent_conj)
open CFSG.RankThree.PartOne.K1214 (torsionSub mem_torsionSub torsionSub_le_succ)

private lemma conj_mem_T {R : Type*} [Group R]
    {A T N : Subgroup R}
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hAT : A ≤ T)
    (hcent : Subgroup.centralizer (A : Set R) ≤ T)
    (hNA : N ≤ Subgroup.normalizer (A : Set R))
    {g : R} (hg : g ∈ N) {y : R} (hy : y ∈ T) :
    g * y * g⁻¹ ∈ T := by
  refine hcent ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hga : g⁻¹ * a * g ∈ A := by
    have hg' : g⁻¹ ∈ Subgroup.normalizer (A : Set R) := hNA (N.inv_mem hg)
    have h := (Subgroup.mem_normalizer_iff.mp hg') a
    simpa using h.mp ha
  have hy_comm : y * (g⁻¹ * a * g) = (g⁻¹ * a * g) * y :=
    hTab y hy _ (hAT hga)
  calc a * (g * y * g⁻¹) = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [← hy_comm]
    _ = (g * y * g⁻¹) * a := by group

private theorem layer_card {p n : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {A T N : Subgroup R}
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hNT : ∀ g ∈ N, ∀ y ∈ T, g * y * g⁻¹ ∈ T)
    (htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A)
    (hirr : ∀ Q : Subgroup R, Q ≤ A → N ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = A)
    (hA : Nat.card A = p ^ n)
    {B : Subgroup R} (hBT : B ≤ T)
    (hnormB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    {k : ℕ} {u : R} (huB : u ∈ B) (huord : orderOf u = p ^ k) :
    ∀ j, j ≤ k → Nat.card ↥(B ⊓ torsionSub T hTab (p ^ j)) = p ^ (n * j) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpne1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : B ⊓ torsionSub T hTab (p ^ 0) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      rw [Subgroup.mem_inf, mem_torsionSub] at hy
      simpa using hy.2.2
    rw [h0, Subgroup.card_bot]
    simp
  | succ j ih =>
    intro hj1
    have hj : j ≤ k := Nat.le_of_succ_le hj1
    let Bk : Subgroup R := B ⊓ torsionSub T hTab (p ^ (j + 1))
    have hBj_le_Bk : B ⊓ torsionSub T hTab (p ^ j) ≤ Bk := by
      change B ⊓ torsionSub T hTab (p ^ j) ≤ B ⊓ torsionSub T hTab (p ^ (j + 1))
      exact le_inf inf_le_left (le_trans inf_le_right (torsionSub_le_succ hTab j))
    let φ : Bk →* R :=
      { toFun := fun y => (y : R) ^ p ^ j
        map_one' := by simp
        map_mul' := by
          intro a b
          show ((a : R) * (b : R)) ^ p ^ j = (a : R) ^ p ^ j * (b : R) ^ p ^ j
          have hc : Commute (a : R) (b : R) := hTab (a : R) (hBT a.2.1) (b : R) (hBT b.2.1)
          exact hc.mul_pow (p ^ j) }
    have hker_eq : φ.ker = (B ⊓ torsionSub T hTab (p ^ j)).subgroupOf Bk := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_torsionSub]
      change (x : R) ^ p ^ j = 1 ↔ (x : R) ∈ B ∧ (x : R) ∈ T ∧ (x : R) ^ p ^ j = 1
      exact ⟨fun hx => ⟨x.2.1, x.2.2.1, hx⟩, fun hx => hx.2.2⟩
    have hcard_ker : Nat.card ↥(φ.ker) = Nat.card ↥(B ⊓ torsionSub T hTab (p ^ j)) := by
      rw [hker_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBj_le_Bk).toEquiv
    have hQ_le_A : φ.range ≤ A := by
      intro q hq
      obtain ⟨y, hyq⟩ := MonoidHom.mem_range.mp hq
      have hy1 : (y : R) ^ p ^ (j + 1) = 1 := (mem_torsionSub.mp y.2.2).2
      have hqT : q ∈ T := by
        rw [← hyq]
        exact T.pow_mem (hBT y.2.1) (p ^ j)
      have hqp : q ^ p = 1 := by
        rw [← hyq]
        show ((y : R) ^ p ^ j) ^ p = 1
        rw [← pow_mul, show p ^ j * p = p ^ (j + 1) by rw [pow_succ], hy1]
      exact htors q hqT hqp
    have hconj_range : ∀ g ∈ N, ∀ q ∈ φ.range, g * q * g⁻¹ ∈ φ.range := by
      intro g hg q hq
      obtain ⟨y, hyq⟩ := MonoidHom.mem_range.mp hq
      have hyB : (y : R) ∈ B := y.2.1
      have hyT : (y : R) ∈ T := hBT hyB
      have hconjB : g * (y : R) * g⁻¹ ∈ B := hnormB g hg (y : R) hyB
      have hconjTor : g * (y : R) * g⁻¹ ∈ torsionSub T hTab (p ^ (j + 1)) := by
        rw [mem_torsionSub]
        refine ⟨hNT g hg _ hyT, ?_⟩
        have hy1 : (y : R) ^ p ^ (j + 1) = 1 := (mem_torsionSub.mp y.2.2).2
        rw [conj_pow, hy1, mul_one, mul_inv_cancel]
      let z : Bk := ⟨g * (y : R) * g⁻¹, ⟨hconjB, hconjTor⟩⟩
      refine ⟨z, ?_⟩
      rw [← hyq]
      change (g * (y : R) * g⁻¹) ^ p ^ j = g * (y : R) ^ p ^ j * g⁻¹
      rw [conj_pow]
    have hnormQ : N ≤ Subgroup.normalizer (φ.range : Set R) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · exact hconj_range g hg q
      · intro hq
        have h := hconj_range g⁻¹ (N.inv_mem hg) (g * q * g⁻¹) hq
        have hcalc : g⁻¹ * (g * q * g⁻¹) * g = q := by group
        simpa [hcalc] using h
    have hQ_ne_bot : φ.range ≠ ⊥ := by
      intro hbot
      have hu'B : u ^ p ^ (k - (j + 1)) ∈ B := B.pow_mem huB _
      have hu'ord : orderOf (u ^ p ^ (k - (j + 1))) = p ^ (j + 1) := by
        rw [orderOf_pow_of_dvd (pow_ne_zero (k - (j + 1)) (Nat.pos_iff_ne_zero.mp hp0))
              (by rw [huord]; exact pow_dvd_pow p (Nat.sub_le k (j + 1))), huord]
        rw [Nat.pow_div (Nat.sub_le k (j + 1)) hp0]
        rw [show k - (k - (j + 1)) = j + 1 by omega]
      have hu'tor : u ^ p ^ (k - (j + 1)) ∈ torsionSub T hTab (p ^ (j + 1)) := by
        rw [mem_torsionSub]
        refine ⟨hBT hu'B, ?_⟩
        rw [← hu'ord]
        exact pow_orderOf_eq_one _
      let y : Bk := ⟨u ^ p ^ (k - (j + 1)), ⟨hu'B, hu'tor⟩⟩
      have hφy_ord : orderOf (φ y) = p := by
        show orderOf ((u ^ p ^ (k - (j + 1)) : R) ^ p ^ j) = p
        rw [orderOf_pow_of_dvd (pow_ne_zero j (Nat.pos_iff_ne_zero.mp hp0))
              (by rw [hu'ord]; exact pow_dvd_pow p (Nat.le_succ j)), hu'ord]
        rw [Nat.pow_div (Nat.le_succ j) hp0]
        rw [show j + 1 - j = 1 by omega, pow_one]
      have hφy_ne : φ y ≠ 1 := by
        intro h1
        exact hpne1 (hφy_ord.symm.trans (by rw [h1, orderOf_one]))
      exact hφy_ne (Subgroup.mem_bot.mp (by
        rw [← hbot]
        exact MonoidHom.mem_range.mpr ⟨y, rfl⟩))
    have hQcard : Nat.card ↥φ.range = p ^ n := by
      rcases hirr φ.range hQ_le_A hnormQ with hQbot | hQtop
      · exact absurd hQbot hQ_ne_bot
      · rw [hQtop]
        exact hA
    have hlayer := Subgroup.card_ker_mul_card_range φ
    rw [hcard_ker, ih hj, hQcard] at hlayer
    change Nat.card ↥Bk = p ^ (n * (j + 1))
    rw [← hlayer, ← pow_add]
    rfl

theorem mem_closure_conj_of_torusIrred_of_conj {p n e : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {A T N : Subgroup R} (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hNT : ∀ g ∈ N, ∀ y ∈ T, g * y * g⁻¹ ∈ T) (htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A)
    (hirr : ∀ Q : Subgroup R, Q ≤ A → N ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = A)
    (hA : Nat.card A = p ^ n) (hexp : ∀ y ∈ T, (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1)
    {S : Subgroup R} (hST : S ≤ T) (hS : ∃ s ∈ S, orderOf s = p ^ e) :
    ∀ c ∈ T, (∃ k : ℕ, c ^ p ^ k = 1) →
      c ∈ Subgroup.closure (⋃ g ∈ N, (fun s => g * s * g⁻¹) '' (S : Set R)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨s, hsS, hsord⟩ := hS
  have hsT : s ∈ T := hST hsS
  have hsP : s ∈ primaryComponent T hTab p :=
    mem_primaryComponent.mpr ⟨hsT, ⟨e, by rw [← hsord]; exact pow_orderOf_eq_one s⟩⟩
  have hnormP : ∀ g ∈ N, ∀ b ∈ primaryComponent T hTab p,
      g * b * g⁻¹ ∈ primaryComponent T hTab p := fun g hg b hb =>
    primaryComponent_conj (fun y hy => hNT g hg y hy) hb
  have hle : torsionSub T hTab (p ^ e) ≤ primaryComponent T hTab p := fun y hy =>
    mem_primaryComponent.mpr ⟨(mem_torsionSub.mp hy).1, e, (mem_torsionSub.mp hy).2⟩
  have hLayerP :
      Nat.card ↥(primaryComponent T hTab p ⊓ torsionSub T hTab (p ^ e)) = p ^ (n * e) :=
    layer_card hTab hNT htors hirr hA (fun _ hy => (mem_primaryComponent.mp hy).1)
      hnormP hsP hsord e le_rfl
  have hPcard : Nat.card ↥(primaryComponent T hTab p) = p ^ (n * e) := by
    have h := hLayerP
    rw [inf_eq_right.mpr hle] at h
    rwa [show torsionSub T hTab (p ^ e) = primaryComponent T hTab p from
      le_antisymm hle fun y hy => by
        obtain ⟨hyT, hyk⟩ := mem_primaryComponent.mp hy
        exact mem_torsionSub.mpr ⟨hyT, hexp y hyT hyk⟩] at h
  intro c hcT hcP
  let Gens : Set R := ⋃ g ∈ N, (fun s => g * s * g⁻¹) '' (S : Set R)
  let H : Subgroup R := Subgroup.closure Gens
  have hGensT : Gens ⊆ (T : Set R) := by
    rintro x hx
    simp only [Gens, Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨g, hgN, s', hsS', rfl⟩ := hx
    exact hNT g hgN s' (hST hsS')
  have hH_le_T : H ≤ T := (Subgroup.closure_le T).mpr hGensT
  have hsH : s ∈ H := by
    apply Subgroup.subset_closure
    simp only [Gens, Set.mem_iUnion, Set.mem_image]
    exact ⟨1, N.one_mem, s, hsS, by group⟩
  have hHnorm : ∀ g ∈ N, ∀ y ∈ H, g * y * g⁻¹ ∈ H := fun g hg y hy =>
    CFSG.GroupTheory.conj_mem_closure_iUnion_conj N (S : Set R) hg hy
  let B : Subgroup R := H ⊓ primaryComponent T hTab p
  have hB_le_T : B ≤ T := le_trans inf_le_left hH_le_T
  have hBnorm : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hg b hb
    change b ∈ H ⊓ primaryComponent T hTab p at hb
    change g * b * g⁻¹ ∈ H ⊓ primaryComponent T hTab p
    rw [Subgroup.mem_inf] at hb ⊢
    exact ⟨hHnorm g hg b hb.1, hnormP g hg b hb.2⟩
  have hsB : s ∈ B := Subgroup.mem_inf.mpr ⟨hsH, hsP⟩
  have hLayerB : Nat.card ↥(B ⊓ torsionSub T hTab (p ^ e)) = p ^ (n * e) :=
    layer_card hTab hNT htors hirr hA hB_le_T hBnorm hsB hsord e le_rfl
  have hB_le_tor : B ≤ torsionSub T hTab (p ^ e) := by
    intro b hb
    obtain ⟨hbT, hbk⟩ := mem_primaryComponent.mp (Subgroup.mem_inf.mp hb).2
    exact mem_torsionSub.mpr ⟨hbT, hexp b hbT hbk⟩
  have hBcard : Nat.card ↥B = p ^ (n * e) := by
    rwa [inf_eq_left.mpr hB_le_tor] at hLayerB
  have hfinP : Finite ↥(primaryComponent T hTab p) := Nat.finite_of_card_ne_zero (by
    rw [hPcard]; exact pow_ne_zero _ (Nat.pos_iff_ne_zero.mp hp0))
  have hBeq : B = primaryComponent T hTab p := by
    refine @Subgroup.eq_of_le_of_card_ge _ _ B (primaryComponent T hTab p) hfinP
      (show B ≤ primaryComponent T hTab p from inf_le_right) ?_
    rw [hBcard, hPcard]
  have hPleH : primaryComponent T hTab p ≤ H := by
    rw [← hBeq]
    exact inf_le_left
  exact hPleH (mem_primaryComponent.mpr ⟨hcT, hcP⟩)

theorem mem_closure_conj_of_torusIrred {p n e : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {A T N : Subgroup R} (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hAT : A ≤ T)
    (hcent : Subgroup.centralizer (A : Set R) ≤ T) (hNA : N ≤ Subgroup.normalizer (A : Set R))
    (htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A)
    (hirr : ∀ Q : Subgroup R, Q ≤ A → N ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = A)
    (hA : Nat.card A = p ^ n) (hexp : ∀ y ∈ T, (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1)
    {S : Subgroup R} (hST : S ≤ T) (hS : ∃ s ∈ S, orderOf s = p ^ e) :
    ∀ c ∈ T, (∃ k : ℕ, c ^ p ^ k = 1) →
      c ∈ Subgroup.closure (⋃ g ∈ N, (fun s => g * s * g⁻¹) '' (S : Set R)) :=
  mem_closure_conj_of_torusIrred_of_conj hTab
    (fun _ hg _ hy => conj_mem_T hTab hAT hcent hNA hg hy) htors hirr hA hexp hST hS

theorem pow_eq_one_of_card_torusPPart {p n e : ℕ} [Fact p.Prime] {R : Type*} [Group R]
    {A T N : Subgroup R} (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hAT : A ≤ T)
    (hcent : Subgroup.centralizer (A : Set R) ≤ T) (hNA : N ≤ Subgroup.normalizer (A : Set R))
    (htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A)
    (hirr : ∀ Q : Subgroup R, Q ≤ A → N ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = A)
    (hA : Nat.card A = p ^ n)
    (hcount : Nat.card {y : R // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (n * e))
    {s : R} (hsT : s ∈ T) (hs : orderOf s = p ^ e) :
    ∀ y ∈ T, (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hsP : s ∈ primaryComponent T hTab p :=
    mem_primaryComponent.mpr ⟨hsT, ⟨e, by rw [← hs]; exact pow_orderOf_eq_one s⟩⟩
  have hnormP : ∀ g ∈ N, ∀ b ∈ primaryComponent T hTab p,
      g * b * g⁻¹ ∈ primaryComponent T hTab p := fun g hg b hb =>
    primaryComponent_conj (fun _ hy => conj_mem_T hTab hAT hcent hNA hg hy) hb
  have hle : torsionSub T hTab (p ^ e) ≤ primaryComponent T hTab p := fun y hy =>
    mem_primaryComponent.mpr ⟨(mem_torsionSub.mp hy).1, e, (mem_torsionSub.mp hy).2⟩
  have hLayerP :
      Nat.card ↥(primaryComponent T hTab p ⊓ torsionSub T hTab (p ^ e)) = p ^ (n * e) :=
    layer_card hTab (fun _ hg _ hy => conj_mem_T hTab hAT hcent hNA hg hy) htors hirr hA
      (fun _ hy => (mem_primaryComponent.mp hy).1) hnormP hsP hs e le_rfl
  have htor_card : Nat.card ↥(torsionSub T hTab (p ^ e)) = p ^ (n * e) := by
    have h := hLayerP
    rwa [inf_eq_right.mpr hle] at h
  have hP_card : Nat.card ↥(primaryComponent T hTab p) = p ^ (n * e) := by
    change Nat.card {y : R // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (n * e)
    exact hcount
  have hfinP : Finite ↥(primaryComponent T hTab p) := Nat.finite_of_card_ne_zero (by
    rw [hP_card]; exact pow_ne_zero _ (Nat.pos_iff_ne_zero.mp hp0))
  have hEq_tor : torsionSub T hTab (p ^ e) = primaryComponent T hTab p := by
    refine @Subgroup.eq_of_le_of_card_ge _ _ (torsionSub T hTab (p ^ e))
      (primaryComponent T hTab p) hfinP hle ?_
    rw [hP_card, htor_card]
  intro y hyT hyP
  have hy : y ∈ primaryComponent T hTab p := mem_primaryComponent.mpr ⟨hyT, hyP⟩
  rw [← hEq_tor] at hy
  exact (mem_torsionSub.mp hy).2

theorem ggTorusGenR_of_torusIrred {p r n e : ℕ} [Fact p.Prime] {R : Type} [Group R]
    {A T N : Subgroup R} (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hAT : A ≤ T)
    (hcent : Subgroup.centralizer (A : Set R) ≤ T) (hNA : N ≤ Subgroup.normalizer (A : Set R))
    (htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A)
    (hirr : ∀ Q : Subgroup R, Q ≤ A → N ≤ Subgroup.normalizer (Q : Set R) → Q = ⊥ ∨ Q = A)
    (hA : Nat.card A = p ^ n)
    (hexp : (∃ s ∈ T, orderOf s = p ^ e) → ∀ y ∈ T, (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1)
    (hU : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      (∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) →
        ∃ c : R, E = A.map (MulAut.conj c).toMonoidHom)
    (hcomp : ∀ x ∈ A, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
      ∃ s ∈ J, s ∈ T ∧ orderOf s = p ^ e) :
    GGTorusGenR p r R := by
  intro E hE hcard hSC x hx hx1 J hJ c hc hcp
  obtain ⟨c₀, hE_eq⟩ := hU E hE hcard hSC
  set x' : R := c₀⁻¹ * x * c₀ with hx'_def
  set J' : Subgroup R := J.map (MulAut.conj c₀⁻¹).toMonoidHom with hJ'_def
  have hxE : x ∈ A.map (MulAut.conj c₀).toMonoidHom := by
    rw [← hE_eq]; exact hx
  have hx'A : x' ∈ A := by
    rw [hx'_def]
    obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp hxE
    have hxa : c₀⁻¹ * x * c₀ = a := by
      rw [← hfa]
      change c₀⁻¹ * (MulAut.conj c₀ a) * c₀ = a
      rw [MulAut.conj_apply]; group
    rwa [hxa]
  have hx'1 : x' ≠ 1 := by
    rw [hx'_def]
    intro h
    apply hx1
    calc x = c₀ * (c₀⁻¹ * x * c₀) * c₀⁻¹ := by group
      _ = c₀ * 1 * c₀⁻¹ := by rw [h]
      _ = 1 := by group
  have hJ' : IsComponentOf J' (Subgroup.centralizer {x'}) := by
    have hJ_open : CFSG.Open.IsComponentOf J (Subgroup.centralizer {x}) :=
      (CFSG.Assembly.isComponentOf_iff_open).1 hJ
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj c₀⁻¹) hJ_open
    rw [CFSG.centralizer_singleton_map] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).2 (by simpa [hJ'_def, hx'_def] using h)
  obtain ⟨s, hsJ', hsT, hse⟩ := hcomp x' hx'A hx'1 J' hJ'
  set S₀ : Subgroup R := Subgroup.zpowers s with hS₀_def
  set S : Subgroup R := S₀.map (MulAut.conj c₀).toMonoidHom with hS_def
  set W : Set R := (fun g => c₀ * g * c₀⁻¹) '' (N : Set R) with hW_def
  have hS₀ : IsPGroup p S₀ :=
    IsPGroup.of_card (n := e) (by rw [hS₀_def, Nat.card_zpowers, hse])
  have hS_pgroup : IsPGroup p S := by
    rw [hS_def]; exact hS₀.map (MulAut.conj c₀).toMonoidHom
  have hST0 : S₀ ≤ T := by
    rw [hS₀_def]; exact Subgroup.zpowers_le.mpr hsT
  have hT_centA : T ≤ Subgroup.centralizer (A : Set R) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hTab y hy z (hAT hz)).symm
  have hmap_cent : T.map (MulAut.conj c₀).toMonoidHom ≤
      Subgroup.centralizer (E : Set R) := by
    have h := Subgroup.map_centralizer_le_centralizer_image (A : Set R)
      (MulAut.conj c₀).toMonoidHom
    have h2 : T.map (MulAut.conj c₀).toMonoidHom ≤
        (Subgroup.centralizer (A : Set R)).map (MulAut.conj c₀).toMonoidHom :=
      Subgroup.map_mono hT_centA
    refine h2.trans ?_
    rw [hE_eq, Subgroup.coe_map]
    exact h
  have hS_cent : S ≤ Subgroup.centralizer (E : Set R) := by
    have h1 : S ≤ T.map (MulAut.conj c₀).toMonoidHom := by
      rw [hS_def]; exact Subgroup.map_mono hST0
    exact h1.trans hmap_cent
  have hc₀sJ : (MulAut.conj c₀) s ∈ J := by
    obtain ⟨j, hj, hjs⟩ := Subgroup.mem_map.mp hsJ'
    have hjs' : (MulAut.conj c₀) s = j := by
      rw [← hjs]
      change MulAut.conj c₀ (MulAut.conj c₀⁻¹ j) = j
      rw [MulAut.conj_apply, MulAut.conj_apply]; group
    rwa [hjs']
  have hS_J : S ≤ J := by
    rw [hS_def, Subgroup.map_le_iff_le_comap, hS₀_def]
    exact Subgroup.zpowers_le.mpr hc₀sJ
  have hW_norm : W ⊆ Subgroup.normalizer (E : Set R) := by
    rintro w' ⟨g, hg, rfl⟩
    have h := Subgroup.le_normalizer_map (H := A) (MulAut.conj c₀).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj c₀).toMonoidHom (hNA hg))
    rw [hE_eq]
    exact h
  set c' : R := c₀⁻¹ * c * c₀ with hc'_def
  have hc'T : c' ∈ T := by
    rw [hc'_def]
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzE : c₀ * z * c₀⁻¹ ∈ E := by
      rw [hE_eq]
      exact Subgroup.mem_map_of_mem (MulAut.conj c₀).toMonoidHom hz
    have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (c₀ * z * c₀⁻¹) hzE
    have hcalc : (c₀⁻¹ * c * c₀) * z = z * (c₀⁻¹ * c * c₀) := by
      calc c₀⁻¹ * c * c₀ * z = c₀⁻¹ * (c * (c₀ * z * c₀⁻¹)) * c₀ := by group
        _ = c₀⁻¹ * ((c₀ * z * c₀⁻¹) * c) * c₀ := by rw [hcomm]
        _ = z * (c₀⁻¹ * c * c₀) := by group
    exact hcalc.symm
  have hc'p : ∃ k : ℕ, c' ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    refine ⟨k, ?_⟩
    rw [hc'_def]
    have hc'_eq : c₀⁻¹ * c * c₀ = (MulAut.conj c₀⁻¹) c := by
      rw [MulAut.conj_apply, inv_inv]
    rw [hc'_eq]
    change ((MulAut.conj c₀⁻¹).toMonoidHom c) ^ p ^ k = 1
    rw [← MonoidHom.map_pow (MulAut.conj c₀⁻¹).toMonoidHom c (p ^ k), hk, map_one]
  set X : Set R := ⋃ g ∈ N, (fun y => g * y * g⁻¹) '' (S₀ : Set R) with hX_def
  have hgen : c' ∈ Subgroup.closure X :=
    mem_closure_conj_of_torusIrred hTab hAT hcent hNA htors hirr hA
      (hexp ⟨s, hsT, hse⟩) (S := S₀) hST0
      ⟨s, by rw [hS₀_def]; exact Subgroup.mem_zpowers s, hse⟩ c' hc'T hc'p
  set Tgt : Set R :=
    ⋃ q ∈ W, (fun y => q * y * q⁻¹) '' (S : Set R) with hTgt_def
  have hsub : (MulAut.conj c₀).toMonoidHom '' X ⊆ Tgt := by
    rintro z ⟨x, hx, rfl⟩
    rw [hX_def] at hx
    obtain ⟨g, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hgN, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hTgt_def]
    refine Set.mem_iUnion.mpr ⟨c₀ * g * c₀⁻¹, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · rw [hW_def]; exact Set.mem_image_of_mem _ hgN
    · refine ⟨(MulAut.conj c₀) y,
        Subgroup.mem_map_of_mem (MulAut.conj c₀).toMonoidHom hy, ?_⟩
      change c₀ * g * c₀⁻¹ * (MulAut.conj c₀ y) * (c₀ * g * c₀⁻¹)⁻¹ =
        (MulAut.conj c₀) (g * y * g⁻¹)
      show c₀ * g * c₀⁻¹ * (c₀ * y * c₀⁻¹) * (c₀ * g * c₀⁻¹)⁻¹ =
        c₀ * (g * y * g⁻¹) * c₀⁻¹
      group
  have hmem : c ∈ Subgroup.closure Tgt := by
    have h1 : (MulAut.conj c₀) c' ∈
        (Subgroup.closure X).map (MulAut.conj c₀).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj c₀).toMonoidHom hgen
    have hc_eq : c = (MulAut.conj c₀) c' := by
      rw [hc'_def, MulAut.conj_apply]; group
    rw [MonoidHom.map_closure] at h1
    rw [← hc_eq] at h1
    exact Subgroup.closure_mono hsub h1
  refine ⟨S, W, hS_pgroup, hS_cent, hS_J, hW_norm, ?_⟩
  change c ∈ Subgroup.closure Tgt
  exact hmem

end CFSG.StandardType
