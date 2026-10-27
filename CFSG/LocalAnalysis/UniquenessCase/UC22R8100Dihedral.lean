module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import TauCeti.GroupTheory.Transfer
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Sz
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.Quasithin.Background.D2Dihedral
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99InnerFour
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99PairFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem permutesPair_of_hyp8100 {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ}
    {r p : ℕ} {A X : Subgroup G} (h : F08.Hyp8100 D L n r p A X) :
    PartTwo.PermutesPair D.M (L 0) (L 1) := by
  obtain ⟨hLC, hne, -, -, -, -, -, -, hX, hMX⟩ := h
  have hXle : X ≤ L 0 ⊔ L 1 := by
    intro x hx
    have hx' : x ∈ (L 0 : Set G) * (L 1 : Set G) := by
      rw [← hX]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hLX : ∀ i, L i ≤ X := by
    intro i x hx
    show x ∈ (X : Set G)
    rw [hX]
    fin_cases i
    · exact ⟨x, hx, 1, (L 1).one_mem, mul_one x⟩
    · exact ⟨1, (L 0).one_mem, x, hx, one_mul x⟩
  have hconj : ∀ i, ∀ m ∈ D.M, (L i).map (MulAut.conj m).toMonoidHom = L 0 ∨
      (L i).map (MulAut.conj m).toMonoidHom = L 1 := by
    intro i m hm
    have hM : D.M.map (MulAut.conj m).toMonoidHom = D.M :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hm)
    have hJ : (L i).map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
      UC6S846.calC_map D.M (MulAut.conj m) hM (hLC i)
    have hJle : (L i).map (MulAut.conj m).toMonoidHom ≤ L 0 ⊔ L 1 :=
      ((Subgroup.map_mono (hLX i)).trans
        (le_of_eq (UC6S846.mem_normalizer_iff_map_conj.mp (hMX hm)))).trans hXle
    exact PartTwo.S19.eq_left_or_right_of_mem_calC_le_sup hJ (hLC 0) (hLC 1) hne hJle
  intro m hm
  rcases hconj 0 m hm with h0 | h0 <;> rcases hconj 1 m hm with h1 | h1
  · exact absurd (Subgroup.map_injective (MulAut.conj m).injective (h0.trans h1.symm)) hne
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (Subgroup.map_injective (MulAut.conj m).injective (h0.trans h1.symm)) hne

namespace R8100D

private theorem rhoL_eq_one_iff (L : Subgroup G) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    UC6S846.rhoL L ⟨x, hx⟩ = 1 ↔ CentralizesBar x L := by
  constructor
  · intro h
    refine ⟨hx, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL L ⟨x, hx⟩ (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) =
        QuotientGroup.mk (⟨l, hl⟩ : ↥L) := by
      rw [h, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff L ⟨x, hx⟩ ⟨l, hl⟩).1 h1
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [MulAut.one_apply]
      exact (UC6S846.rhoL_fix_iff L ⟨x, hx⟩ l).2 (h.2 l l.2)

private noncomputable def outHom (L : Subgroup G) :
    ↥(normalizer (L : Set G)) →* Outer (Bar2 L) :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
    (UC6S846.rhoL L)

omit [Finite G] in
private theorem outHom_eq_one_iff_range (L : Subgroup G) (x : ↥(normalizer (L : Set G))) :
    outHom L x = 1 ↔ UC6S846.rhoL L x ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
  unfold outHom
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

omit [Finite G] in
private theorem outHom_congr (L : Subgroup G) {a b : G} (e : a = b)
    (ha : a ∈ normalizer (L : Set G)) (hb : b ∈ normalizer (L : Set G)) :
    outHom L ⟨a, ha⟩ = outHom L ⟨b, hb⟩ := by
  subst e
  rfl

private def InnBar (L : Subgroup G) (m : G) : Prop :=
  ∃ l ∈ L, CentralizesBar (l⁻¹ * m) L

private theorem outHom_eq_one_iff (L : Subgroup G) {m : G} (hm : m ∈ normalizer (L : Set G)) :
    outHom L ⟨m, hm⟩ = 1 ↔ InnBar L m := by
  rw [outHom_eq_one_iff_range]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective b
    have hl' : l⁻¹ * m ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer (L.inv_mem hl)) hm
    refine ⟨l, hl, (rhoL_eq_one_iff L hl').1 ?_⟩
    have e : (⟨l⁻¹ * m, hl'⟩ : ↥(normalizer (L : Set G))) =
        (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L : Set G)))⁻¹ * ⟨m, hm⟩ := rfl
    rw [e, map_mul, map_inv, ← hb, UC6S846.rhoL_inner L l hl, inv_mul_cancel]
  · rintro ⟨l, hl, hc⟩
    refine ⟨QuotientGroup.mk (⟨l, hl⟩ : ↥L), ?_⟩
    have h1 := (rhoL_eq_one_iff L hc.1).2 hc
    have e : (⟨m, hm⟩ : ↥(normalizer (L : Set G))) =
        (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L : Set G))) * ⟨l⁻¹ * m, hc.1⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, h1, mul_one, UC6S846.rhoL_inner L l hl]

omit [Finite G] in
private theorem mem_normalizer_of_innBar {L : Subgroup G} {m : G} (h : InnBar L m) :
    m ∈ normalizer (L : Set G) := by
  obtain ⟨l, hl, hc⟩ := h
  have e : m = l * (l⁻¹ * m) := by group
  rw [e]
  exact (normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hl) hc.1

private theorem centralizesBar_conj (g : G) {x : G} {L : Subgroup G} (h : CentralizesBar x L) :
    CentralizesBar (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) := by
  rw [uc22p21d_centralizesBar_iff]
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hl'
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) L]
  refine Subgroup.mem_map.2 ⟨x * l * x⁻¹ * l⁻¹, h.2 l hl, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem innBar_conj (g : G) {L : Subgroup G} {m : G} (h : InnBar L m) :
    InnBar (L.map (MulAut.conj g).toMonoidHom) (g * m * g⁻¹) := by
  obtain ⟨l, hl, hc⟩ := h
  refine ⟨g * l * g⁻¹, Subgroup.mem_map.2 ⟨l, hl, by simp⟩, ?_⟩
  have e : (g * l * g⁻¹)⁻¹ * (g * m * g⁻¹) = g * (l⁻¹ * m) * g⁻¹ := by group
  rw [e]
  exact centralizesBar_conj g hc

private theorem map_eq_one_of_card_dvd {H A : Type*} [Group H] [Group A] {p : ℕ}
    (hp : p.Prime) (hA : Nat.card A ∣ p) (f : H →* A) {h : H} (hh : ¬ p ∣ orderOf h) :
    f h = 1 := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0, zero_dvd_iff] at hA
    exact hp.ne_zero hA)
  have h1 : orderOf (f h) ∣ p := (orderOf_dvd_natCard (f h)).trans hA
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · exact absurd (by rw [← h2]; exact orderOf_map_dvd f h) hh

private theorem pow_eq_one_of_card_dvd {A : Type*} [Group A] {p : ℕ} (hA : Nat.card A ∣ p)
    (a : A) : a ^ p = 1 := by
  obtain ⟨k, hk⟩ := hA
  rw [hk, pow_mul, pow_card_eq_one', one_pow]

private theorem exists_zpow_eq_of_card_dvd {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (hA : Nat.card A ∣ p) {a : A} (ha : a ≠ 1) (b : A) : ∃ k : ℤ, a ^ k = b := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card A = p := by
    rcases (Nat.dvd_prime hp).1 hA with h1 | h1
    · have := (Nat.card_eq_one_iff_unique.1 h1).1
      exact absurd (Subsingleton.elim a 1) ha
    · exact h1
  exact Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_prime_card hcard ha)

omit [Finite G] in
private theorem permutesPair_symm {M L₀ L₁ : Subgroup G} (h : PartTwo.PermutesPair M L₀ L₁) :
    PartTwo.PermutesPair M L₁ L₀ := by
  intro m hm
  rcases h m hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h1, h0⟩
  · exact Or.inr ⟨h1, h0⟩

private theorem le_normalizer_of_permutesPair {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) (hne : L₀ ≠ L₁) (hL₁M : L₁ ≤ M) :
    L₁ ≤ normalizer (L₀ : Set G) := by
  intro l hl
  rw [UC6S846.mem_normalizer_iff_map_conj]
  rcases hperm l (hL₁M hl) with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact h0
  · exact absurd ((UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hl)).symm.trans
      h1) hne.symm

private theorem mem_normalizer_of_permutesPair {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) (hne : L₀ ≠ L₁) {m : G} (hm : m ∈ M)
    (h0 : m ∈ normalizer (L₀ : Set G)) : m ∈ normalizer (L₁ : Set G) := by
  rw [UC6S846.mem_normalizer_iff_map_conj] at h0 ⊢
  rcases hperm m hm with ⟨-, h1⟩ | ⟨h1, -⟩
  · exact h1
  · exact absurd (h0.symm.trans h1) hne

private theorem swap_of_permutesPair {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) {m : G} (hm : m ∈ M)
    (h0 : m ∉ normalizer (L₀ : Set G)) :
    L₀.map (MulAut.conj m).toMonoidHom = L₁ ∧ L₁.map (MulAut.conj m).toMonoidHom = L₀ := by
  rcases hperm m hm with ⟨h1, -⟩ | h
  · exact absurd (UC6S846.mem_normalizer_iff_map_conj.2 h1) h0
  · exact h

omit [Finite G] in
private theorem map_conj_mul (u v : G) (K : Subgroup G) :
    K.map (MulAut.conj (u * v)).toMonoidHom =
      (K.map (MulAut.conj v).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj (u * v)).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj v).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [e]

private theorem mul_mem_normalizer_of_swap {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) {u v : G} (hu : u ∈ M) (hv : v ∈ M)
    (hu0 : u ∉ normalizer (L₀ : Set G)) (hv0 : v ∉ normalizer (L₀ : Set G)) :
    u * v ∈ normalizer (L₀ : Set G) := by
  rw [UC6S846.mem_normalizer_iff_map_conj, map_conj_mul, (swap_of_permutesPair hperm hv hv0).1,
    (swap_of_permutesPair hperm hu hu0).2]

private theorem conj_mem_normalizer {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) {g m : G} (hg : g ∈ M) (hm : m ∈ M)
    (hmN : m ∈ normalizer (L₀ : Set G)) : g⁻¹ * (m * g) ∈ normalizer (L₀ : Set G) := by
  by_cases hgN : g ∈ normalizer (L₀ : Set G)
  · exact (normalizer _).mul_mem ((normalizer _).inv_mem hgN) ((normalizer _).mul_mem hmN hgN)
  · have h1 : g⁻¹ ∉ normalizer (L₀ : Set G) := fun h =>
      hgN (by simpa using (normalizer (L₀ : Set G)).inv_mem h)
    have h2 : m * g ∉ normalizer (L₀ : Set G) := fun h =>
      hgN (by simpa using (normalizer (L₀ : Set G)).mul_mem ((normalizer _).inv_mem hmN) h)
    exact mul_mem_normalizer_of_swap hperm (M.inv_mem hg) (M.mul_mem hm hg) h1 h2

private theorem mem_normalizer_of_odd {M L₀ L₁ : Subgroup G}
    (hperm : PartTwo.PermutesPair M L₀ L₁) {m : G} (hm : m ∈ M) (hodd : ¬ 2 ∣ orderOf m) :
    m ∈ normalizer (L₀ : Set G) := by
  have hsq : m * m ∈ normalizer (L₀ : Set G) := by
    by_cases h : m ∈ normalizer (L₀ : Set G)
    · exact (normalizer _).mul_mem h h
    · exact mul_mem_normalizer_of_swap hperm hm hm h h
  obtain ⟨k, hk⟩ : ∃ k, orderOf m = 2 * k + 1 := ⟨orderOf m / 2, by omega⟩
  have e : m = (m * m) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf m + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact pow_mem hsq _

private theorem conj_mem_pCoreOf {L : Subgroup G} {g x : G} (hg : g ∈ normalizer (L : Set G))
    (hx : x ∈ pCoreOf 2 L) : g * x * g⁻¹ ∈ pCoreOf 2 L :=
  (Subgroup.mem_normalizer_iff.1 (UC6S846.normalizer_le_normalizer_pCoreOf L hg) x).1 hx

private theorem inf_le_pCoreOf {L P : Subgroup G} (hP : IsPGroup 2 P)
    (hLP : L ≤ normalizer (P : Set G)) : L ⊓ P ≤ pCoreOf 2 L :=
  uc22p21c_le_pCoreOf inf_le_left (hP.to_le inf_le_right) fun _ hk x hx =>
    ⟨L.mul_mem (L.mul_mem hk hx.1) (L.inv_mem hk),
      (Subgroup.mem_normalizer_iff.1 (hLP hk) x).1 hx.2⟩

private theorem inf_pCoreOf_le {M L : Subgroup G} (hLM : L ≤ M) :
    L ⊓ pCoreOf 2 M ≤ pCoreOf 2 L :=
  inf_le_pCoreOf (UC6S846.isPGroup_pCoreOf M) fun _ hx =>
    UC6S846.normalizer_le_normalizer_pCoreOf M (Subgroup.le_normalizer (hLM hx))

omit [Finite G] in
private theorem not_le_pCoreOf_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) :
    ¬ L ≤ pCoreOf 2 L := by
  intro h
  obtain ⟨-, hs⟩ := hL.2.2
  have := hs
  have h1 : ∀ q : Bar2 L, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨z, hz, hzx⟩ := h x.2
      have hzx' : z = x := Subtype.ext hzx
      subst hzx'
      exact (QuotientGroup.eq_one_iff z).2 hz
  have h2 : Subsingleton (Bar2 L ⧸ center (Bar2 L)) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => rw [h1 a, h1 b]
  exact not_subsingleton _ h2

private theorem mem_pCoreOf_of_mul_inv {M L₀ L₁ : Subgroup G} (hL₀ : L₀ ∈ calC M)
    (hL₁ : L₁ ∈ calC M) (hne : L₀ ≠ L₁) {n₁ : ℕ}
    (hS₁ : IsL2 (Bar2 L₁) n₁ ∨ IsSz (Bar2 L₁) n₁) {a b : G} (ha : a ∈ L₀) (hb : b ∈ L₁)
    (hba : b * a⁻¹ ∈ pCoreOf 2 M) : a ∈ pCoreOf 2 M := by
  have hinf : barImage M L₀ ⊓ barImage M L₁ = ⊥ :=
    u4x_inf_eq_bot (uc22p22l_barImage_commute hL₀ hL₁ hne) (u4x_center_eq_bot hL₁ hS₁)
  have haM : a ∈ M := hL₀.1.le ha
  have hbM : b ∈ M := hL₁.1.le hb
  have hq : ((⟨b, hbM⟩ : ↥M) : Bar2 M) = ((⟨a, haM⟩ : ↥M) : Bar2 M) := by
    rw [QuotientGroup.eq_iff_div_mem]
    obtain ⟨z, hz, hzeq⟩ := hba
    have hz' : ((z : ↥M) : G) = b * a⁻¹ := hzeq
    have : z = (⟨b, hbM⟩ : ↥M) / ⟨a, haM⟩ := by
      apply Subtype.ext
      rw [hz', Subgroup.coe_div, div_eq_mul_inv]
    rw [← this]
    exact hz
  have h1 : ((⟨a, haM⟩ : ↥M) : Bar2 M) ∈ barImage M L₀ ⊓ barImage M L₁ :=
    ⟨uc22p21c_mem_barImage.2 ⟨⟨a, haM⟩, ha, rfl⟩, uc22p21c_mem_barImage.2 ⟨⟨b, hbM⟩, hb, hq⟩⟩
  rw [hinf, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨a, haM⟩, h1, rfl⟩

private theorem centralizesBar_of_mem {M L₀ L₁ : Subgroup G} (hL₀ : L₀ ∈ calC M)
    (hL₁ : L₁ ∈ calC M) (hne : L₀ ≠ L₁) {n₁ : ℕ}
    (hS₁ : IsL2 (Bar2 L₁) n₁ ∨ IsSz (Bar2 L₁) n₁)
    (h10 : L₁ ≤ normalizer (L₀ : Set G)) (h01 : L₀ ≤ normalizer (L₁ : Set G))
    {b : G} (hb : b ∈ L₁) : CentralizesBar b L₀ := by
  rw [uc22p21d_centralizesBar_iff]
  intro a ha
  have hc0 : b * a * b⁻¹ * a⁻¹ ∈ L₀ :=
    L₀.mul_mem ((Subgroup.mem_normalizer_iff.1 (h10 hb) a).1 ha) (L₀.inv_mem ha)
  have hc1 : b * a * b⁻¹ * a⁻¹ ∈ L₁ := by
    have e : b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) := by group
    rw [e]
    exact L₁.mul_mem hb ((Subgroup.mem_normalizer_iff.1 (h01 ha) b⁻¹).1 (L₁.inv_mem hb))
  have hcM : b * a * b⁻¹ * a⁻¹ ∈ pCoreOf 2 M :=
    mem_pCoreOf_of_mul_inv hL₀ hL₁ hne hS₁ hc0 hc1
      (by rw [mul_inv_cancel]; exact (pCoreOf 2 M).one_mem)
  exact inf_pCoreOf_le hL₀.1.le ⟨hc0, hcM⟩

private theorem centralizesBar_of_centralizesBar_sup {M L₀ L₁ X : Subgroup G}
    (hL₀ : L₀ ∈ calC M) (hL₁ : L₁ ∈ calC M) (hne : L₀ ≠ L₁) {n₁ : ℕ}
    (hS₁ : IsL2 (Bar2 L₁) n₁ ∨ IsSz (Bar2 L₁) n₁) (hperm : PartTwo.PermutesPair M L₀ L₁)
    (hLX : L₀ ≤ X) (hXM : X ≤ M) (hMX : M ≤ normalizer (X : Set G))
    {y : G} (hyM : y ∈ M) (hy : CentralizesBar y X) : CentralizesBar y L₀ := by
  have hO : pCoreOf 2 X ≤ pCoreOf 2 M :=
    uc22p21c_le_pCoreOf ((uc22p21d_pCoreOf_le X).trans hXM) (UC6S846.isPGroup_pCoreOf X)
      fun k hk x hx => conj_mem_pCoreOf (hMX hk) hx
  have hyN : y ∈ normalizer (L₀ : Set G) := by
    by_contra hyN
    obtain ⟨h01, -⟩ := swap_of_permutesPair hperm hyM hyN
    apply not_le_pCoreOf_of_mem_calC hL₀
    intro a ha
    have hb : y * a * y⁻¹ ∈ L₁ := by
      rw [← h01]
      exact Subgroup.mem_map.2 ⟨a, ha, by simp⟩
    have hba : y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 M := hO (hy.2 a (hLX ha))
    exact inf_pCoreOf_le hL₀.1.le ⟨ha, mem_pCoreOf_of_mul_inv hL₀ hL₁ hne hS₁ ha hb hba⟩
  rw [uc22p21d_centralizesBar_iff]
  intro a ha
  have h1 : y * a * y⁻¹ * a⁻¹ ∈ L₀ :=
    L₀.mul_mem ((Subgroup.mem_normalizer_iff.1 hyN a).1 ha) (L₀.inv_mem ha)
  exact inf_le_pCoreOf (UC6S846.isPGroup_pCoreOf X)
    (fun x hx => UC6S846.normalizer_le_normalizer_pCoreOf X (Subgroup.le_normalizer (hLX hx)))
    ⟨h1, hy.2 a (hLX ha)⟩

private theorem innBar_sup {L₀ L₁ X : Subgroup G}
    (hX : (X : Set G) = (L₀ : Set G) * (L₁ : Set G))
    (h10 : L₁ ≤ normalizer (L₀ : Set G))
    (hcen0 : ∀ b ∈ L₁, CentralizesBar b L₀) (hcen1 : ∀ a ∈ L₀, CentralizesBar a L₁)
    (hO0 : pCoreOf 2 L₀ ≤ pCoreOf 2 X) (hO1 : pCoreOf 2 L₁ ≤ pCoreOf 2 X)
    (hXN : X ≤ normalizer (pCoreOf 2 X : Set G))
    {m : G} (h0 : InnBar L₀ m) (h1 : InnBar L₁ m) : InnBar X m := by
  obtain ⟨a, ha, hca⟩ := h0
  obtain ⟨b, hb, hcb⟩ := h1
  have habX : a * b ∈ X := by
    show a * b ∈ (X : Set G)
    rw [hX]
    exact Set.mul_mem_mul ha hb
  refine ⟨a * b, habX, ?_⟩
  have hy0 : CentralizesBar ((a * b)⁻¹ * m) L₀ := by
    have e : (a * b)⁻¹ * m = b⁻¹ * (a⁻¹ * m) := by group
    rw [e]
    exact uc22p21d_centralizesBar_mul (hcen0 _ (L₁.inv_mem hb)) hca
  have hy1 : CentralizesBar ((a * b)⁻¹ * m) L₁ := by
    have e : (a * b)⁻¹ * m = (b⁻¹ * a⁻¹ * b) * (b⁻¹ * m) := by group
    rw [e]
    refine uc22p21d_centralizesBar_mul (hcen1 _ ?_) hcb
    have := (Subgroup.mem_normalizer_iff.1 (h10 (L₁.inv_mem hb)) a⁻¹).1 (L₀.inv_mem ha)
    simpa using this
  rw [uc22p21d_centralizesBar_iff]
  intro x hx
  have hx' : x ∈ (L₀ : Set G) * (L₁ : Set G) := by
    rw [← hX]
    exact hx
  obtain ⟨l, hl, l', hl', rfl⟩ := hx'
  have hlX : l ∈ X := by
    show l ∈ (X : Set G)
    rw [hX]
    exact ⟨l, hl, 1, L₁.one_mem, mul_one l⟩
  set y := (a * b)⁻¹ * m
  have e : y * (l * l') * y⁻¹ * (l * l')⁻¹ =
      (y * l * y⁻¹ * l⁻¹) * (l * (y * l' * y⁻¹ * l'⁻¹) * l⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 X).mul_mem (hO0 (hy0.2 l hl))
    ((Subgroup.mem_normalizer_iff.1 (hXN hlX) _).1 (hO1 (hy1.2 l' hl')))

private theorem outHom_mul_conj_eq_one {M L₀ : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hOp : F10.OpRes p M = M) (hcard : Nat.card (Outer (Bar2 L₀)) ∣ p)
    (hcomm : ∀ a b : Outer (Bar2 L₀), a * b = b * a) (t : ↥M)
    (htN : (t : G) ∉ normalizer (L₀ : Set G))
    (hsw : ∀ x : ↥M, (x : G) ∉ normalizer (L₀ : Set G) →
      ((t⁻¹ * x : ↥M) : G) ∈ normalizer (L₀ : Set G))
    (m : ↥M) (hm : (m : G) ∈ normalizer (L₀ : Set G))
    (hm' : ((t⁻¹ * (m * t) : ↥M) : G) ∈ normalizer (L₀ : Set G)) :
    outHom L₀ ⟨m, hm⟩ * outHom L₀ ⟨(t⁻¹ * (m * t) : ↥M), hm'⟩ = 1 := by
  classical
  let _ : CommGroup (Outer (Bar2 L₀)) :=
    { (inferInstance : Group (Outer (Bar2 L₀))) with mul_comm := hcomm }
  let ϕ : ↥((normalizer (L₀ : Set G)).subgroupOf M) →* Outer (Bar2 L₀) := (outHom L₀).comp
    { toFun := fun x => ⟨((x : ↥M) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hq : ∀ x y : ↥M, (x : ↥M ⧸ (normalizer (L₀ : Set G)).subgroupOf M) = y ↔
      ((x⁻¹ * y : ↥M) : G) ∈ normalizer (L₀ : Set G) := fun x y => QuotientGroup.eq
  have htriv : ∀ g : ↥M, ϕ.transfer g = 1 := by
    intro g
    have h1 : F10.OpRes p M ≤ (ϕ.transfer.ker).map M.subtype := by
      unfold F10.OpRes
      rw [Subgroup.closure_le]
      rintro x ⟨hxM, hxp⟩
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      show ϕ.transfer ⟨x, hxM⟩ = 1
      refine map_eq_one_of_card_dvd hp hcard _ ?_
      rwa [Subgroup.orderOf_mk]
    obtain ⟨g', hg', hgg⟩ := h1 (by rw [hOp]; exact g.2)
    have hg'g : g' = g := Subtype.ext hgg
    rw [← hg'g]
    exact hg'
  have hbij : Function.Bijective fun i : Fin 2 =>
      ((![1, t] i : ↥M) : ↥M ⧸ (normalizer (L₀ : Set G)).subgroupOf M) := by
    have hne : ((1 : ↥M) : ↥M ⧸ (normalizer (L₀ : Set G)).subgroupOf M) ≠ (t : ↥M ⧸ _) := by
      intro h
      apply htN
      simpa using (hq 1 t).1 h
    refine ⟨fun i j hij => ?_, fun q => ?_⟩
    · fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    · induction q using QuotientGroup.induction_on with
      | H x =>
        by_cases hx : (x : G) ∈ normalizer (L₀ : Set G)
        · exact ⟨0, (hq 1 x).2 (by simpa using hx)⟩
        · exact ⟨1, (hq t x).2 (hsw x hx)⟩
  have hπ : ∀ i : Fin 2, ((![1, t] (id i) : ↥M) : ↥M ⧸ (normalizer (L₀ : Set G)).subgroupOf M) =
      ((m * ![1, t] i : ↥M) : ↥M ⧸ _) := by
    intro i
    fin_cases i
    · exact (hq _ _).2 (by simpa using hm)
    · exact (hq _ _).2 hm'
  have h0 : (((1 : ↥M)⁻¹ * (m * 1) : ↥M) : G) ∈ normalizer (L₀ : Set G) := by
    simpa using hm
  have hev : ϕ.transfer m =
      outHom L₀ ⟨((1 : ↥M)⁻¹ * (m * 1) : ↥M), h0⟩ * outHom L₀ ⟨(t⁻¹ * (m * t) : ↥M), hm'⟩ := by
    rw [MonoidHom.transfer_eq_prod_of_bijective ϕ ![1, t] hbij m id hπ, Fin.prod_univ_two]
    rfl
  calc outHom L₀ ⟨m, hm⟩ * outHom L₀ ⟨(t⁻¹ * (m * t) : ↥M), hm'⟩
      = outHom L₀ ⟨((1 : ↥M)⁻¹ * (m * 1) : ↥M), h0⟩ *
          outHom L₀ ⟨(t⁻¹ * (m * t) : ↥M), hm'⟩ := by
        rw [outHom_congr L₀ (show ((m : ↥M) : G) = (((1 : ↥M)⁻¹ * (m * 1) : ↥M) : G) by simp)
          hm h0]
    _ = ϕ.transfer m := hev.symm
    _ = 1 := htriv m

end R8100D

open R8100D in
theorem r8100_sp_or_dihedral {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D)
    {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X : Subgroup G}
    (hH : F08.Hyp8100 D L n r p A X)
    (hset : ({L 0, L 1} : Set (Subgroup G)) =
      {N | ∃ m ∈ D.M, N = (L 0).map (MulAut.conj m).toMonoidHom})
    (hn : n 0 = p) :
    IsStronglyPEmbedded r D.M ∨ ∃ φ : ↥D.M →* DihedralGroup p, Function.Surjective φ ∧
      φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M := by
  classical
  have hperm := permutesPair_of_hyp8100 hH
  obtain ⟨hLC, hne, hshape, hr, hrg, hp, -, -, hX, hMX⟩ := hH
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hg : Nat.gcd (n 0) (n 1) ≠ 0 := Nat.gcd_ne_zero_left (by rw [hn]; exact hpp.ne_zero)
    have h2 : 2 ∣ 2 ^ Nat.gcd (n 0) (n 1) := dvd_pow_self 2 hg
    have h1 : 1 ≤ 2 ^ Nat.gcd (n 0) (n 1) := Nat.one_le_two_pow
    omega
  have hL0M : L 0 ≤ D.M := (hLC 0).1.le
  have hL1M : L 1 ≤ D.M := (hLC 1).1.le
  have h10 : L 1 ≤ normalizer (L 0 : Set G) := le_normalizer_of_permutesPair hperm hne hL1M
  have h01 : L 0 ≤ normalizer (L 1 : Set G) :=
    le_normalizer_of_permutesPair (permutesPair_symm hperm) hne.symm hL0M
  have hcen0 : ∀ b ∈ L 1, CentralizesBar b (L 0) := fun b hb =>
    centralizesBar_of_mem (hLC 0) (hLC 1) hne (hshape 1) h10 h01 hb
  have hcen1 : ∀ a ∈ L 0, CentralizesBar a (L 1) := fun a ha =>
    centralizesBar_of_mem (hLC 1) (hLC 0) hne.symm (hshape 0) h01 h10 ha
  have hN01 : ∀ m ∈ D.M, m ∈ normalizer (L 0 : Set G) → m ∈ normalizer (L 1 : Set G) :=
    fun m hm h => mem_normalizer_of_permutesPair hperm hne hm h
  have hN10 : ∀ m ∈ D.M, m ∈ normalizer (L 1 : Set G) → m ∈ normalizer (L 0 : Set G) :=
    fun m hm h => mem_normalizer_of_permutesPair (permutesPair_symm hperm) hne.symm hm h
  have hsw : ∃ m ∈ D.M, m ∉ normalizer (L 0 : Set G) := by
    have h1 : L 1 ∈ ({L 0, L 1} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
    rw [hset] at h1
    obtain ⟨m, hm, hm1⟩ := h1
    refine ⟨m, hm, fun hN => hne ?_⟩
    rw [hm1]
    exact (UC6S846.mem_normalizer_iff_map_conj.1 hN).symm
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC (hLC 0)
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hp
  have hOp : F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hpp hsp
  obtain ⟨t, htp, htN⟩ : ∃ t : ↥D.M, ¬ p ∣ orderOf (t : G) ∧
      (t : G) ∉ normalizer (L 0 : Set G) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hmN⟩ := hsw
    apply hmN
    have hle : F10.OpRes p D.M ≤ normalizer (L 0 : Set G) := by
      unfold F10.OpRes
      rw [Subgroup.closure_le]
      intro x hx
      exact hcon ⟨x, hx.1⟩ hx.2
    exact hle (by rw [hOp]; exact hm)
  obtain ⟨ht01, -⟩ := swap_of_permutesPair hperm t.2 htN
  have hcard0 : Nat.card (Outer (Bar2 (L 0))) ∣ p := by
    rw [← hn]
    exact u81_card_outer_dvd (hshape 0)
  by_cases hcase : ∀ m : ↥D.M, ∀ hm : (m : G) ∈ normalizer (L 0 : Set G),
      outHom (L 0) ⟨m, hm⟩ = 1
  ·
    left
    have hinn1 : ∀ m (hm : m ∈ normalizer (L 1 : Set G)), m ∈ D.M →
        UC6S846.rhoL (L 1) ⟨m, hm⟩ ∈
          (MulAut.conj : Bar2 (L 1) →* MulAut (Bar2 (L 1))).range := by
      intro m hm hmM
      have hm' : (t : G)⁻¹ * (m * t) ∈ normalizer (L 0 : Set G) :=
        conj_mem_normalizer hperm t.2 hmM (hN10 m hmM hm)
      have h1 : InnBar (L 0) ((t : G)⁻¹ * (m * t)) :=
        (outHom_eq_one_iff _ hm').1 (hcase ⟨_, D.M.mul_mem (D.M.inv_mem t.2)
          (D.M.mul_mem hmM t.2)⟩ hm')
      have h2 := innBar_conj (t : G) h1
      rw [ht01, show (t : G) * ((t : G)⁻¹ * (m * t)) * (t : G)⁻¹ = m by group] at h2
      exact (outHom_eq_one_iff_range _ _).1 ((outHom_eq_one_iff _ hm).2 h2)
    obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
      UC6S846.exists_elemAbelian_card_of_le_pRank (k := 4) hpp (hfour p hp)
    have hA₀N₀ : A₀ ≤ normalizer (L 0 : Set G) := by
      intro b hb
      refine mem_normalizer_of_odd hperm (hA₀M hb) fun h2 => hp2 ?_
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1
        (h2.trans (orderOf_dvd_of_pow_eq_one (hA₀el.2 b hb)))).symm
    have hA₀N₁ : A₀ ≤ normalizer (L 1 : Set G) := fun b hb => hN01 b (hA₀M hb) (hA₀N₀ hb)
    have hZ₀ : center (Bar2 (L 0)) = ⊥ := by
      rcases hshape 0 with hX0 | hX0
      · exact uc22p22g_center_bot hX0
      · have : IsSimpleGroup (Bar2 (L 0)) :=
          CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX0
        exact uc22p21k_center_eq_bot (hLC 0).2.2
    have hZ₁ : center (Bar2 (L 1)) = ⊥ := by
      rcases hshape 1 with hX1 | hX1
      · exact uc22p22g_center_bot hX1
      · have : IsSimpleGroup (Bar2 (L 1)) :=
          CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX1
        exact uc22p21k_center_eq_bot (hLC 1).2.2
    have hle₀ : ∀ Q : Subgroup (Bar2 (L 0)), IsElemAbelian p Q → Nat.card Q ≤ p := by
      intro Q hQ
      rcases hshape 0 with hX0 | hX0
      · have : CFSG.IsElementaryAbelian p ↥Q := hQ.isElementaryAbelian
        exact uc22p22g_rank hpp hp2 hX0 Q
      · exact uc22s21r8100_card_le_of_isSz hX0 hpp hp2 hQ
    have hle₁ : ∀ Q : Subgroup (Bar2 (L 1)), IsElemAbelian p Q → Nat.card Q ≤ p := by
      intro Q hQ
      rcases hshape 1 with hX1 | hX1
      · have : CFSG.IsElementaryAbelian p ↥Q := hQ.isElementaryAbelian
        exact uc22p22g_rank hpp hp2 hX1 Q
      · exact uc22s21r8100_card_le_of_isSz hX1 hpp hp2 hQ
    obtain ⟨C₁, hC₁A₀, hC₁c, hC₁card⟩ :=
      PartOne.Section8.r899_exists_centralizesBar_of_inner (K := L 0) hpp hp2 hZ₀ hle₀ hA₀el
        hA₀N₀ fun b hb => (outHom_eq_one_iff_range _ _).1 (hcase ⟨b, hA₀M hb⟩ (hA₀N₀ hb))
    have hC₁el : IsElemAbelian p C₁ := hA₀el.mono hC₁A₀
    have hC₁N₁ : C₁ ≤ normalizer (L 1 : Set G) := hC₁A₀.trans hA₀N₁
    obtain ⟨C₂, hC₂C₁, hC₂c, hC₂card⟩ :=
      PartOne.Section8.r899_exists_centralizesBar_of_inner (K := L 1) hpp hp2 hZ₁ hle₁ hC₁el
        hC₁N₁ fun b hb => hinn1 b (hC₁N₁ hb) (hA₀M (hC₁A₀ hb))
    have hC₂p : p ^ 2 ≤ Nat.card C₂ := by
      have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card C₂ :=
        calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
          _ = Nat.card A₀ := hA₀c.symm
          _ ≤ p * Nat.card C₁ := hC₁card
          _ ≤ p * (p * Nat.card C₂) := Nat.mul_le_mul_left _ hC₂card
          _ = p ^ 2 * Nat.card C₂ := by ring
      exact Nat.le_of_mul_le_mul_left h4 (pow_pos hpp.pos 2)
    obtain ⟨A', hAC₂, hAel, hAc⟩ := UC6S846.exists_card_p_sq hpp (hC₁el.mono hC₂C₁) hC₂p
    have hAM : A' ≤ D.M := hAC₂.trans ((hC₂C₁.trans hC₁A₀).trans hA₀M)
    have hRN : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M →
        R ≤ normalizer (L 0 : Set G) ∧ R ≤ normalizer (L 1 : Set G) := by
      have : Fact r.Prime := ⟨hr⟩
      rintro R ⟨Q, rfl⟩
      have h0 : (Q : Subgroup ↥D.M).map D.M.subtype ≤ normalizer (L 0 : Set G) := by
        rintro _ ⟨q, hq, rfl⟩
        refine mem_normalizer_of_odd hperm q.2 ?_
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Q.isPGroup' ⟨q, hq⟩
        have hk' : orderOf (q : G) = r ^ k := by
          rw [Subgroup.orderOf_coe q, ← hk]
          exact Subgroup.orderOf_coe (⟨q, hq⟩ : ↥(Q : Subgroup ↥D.M))
        show ¬ 2 ∣ orderOf (q : G)
        rw [hk']
        intro h2
        exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)).symm
      exact ⟨h0, fun x hx => hN01 x (Subgroup.map_subtype_le _ hx) (h0 hx)⟩
    have h76p : Conclusion76 D.M p := F07.R76Sig_of_R76 D h76 p hp (D.sig_prime p hp).2 hsp
    exact PartOne.Section8.r899_sp_of_pair_centralizing (K₁ := L 0) (K₂ := L 1) (n₁ := n 0)
      (n₂ := n 1) (s := Nat.gcd (n 0) (n 1)) (r := r) (p := p) (A := A') hSg h614 (hLC 0)
      (hLC 1) hne (hshape 0) (hshape 1) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hr hr2
      hrg hRN hpp hp2 h76p hAM hAel hAc
      (fun a ha => ⟨hC₁c a (hC₂C₁ (hAC₂ ha)), hC₂c a (hAC₂ ha)⟩)
  ·
    right
    push Not at hcase
    obtain ⟨y₀, hy₀N, hy₀⟩ := hcase
    have : Fact p.Prime := ⟨hpp⟩
    have hcomm0 : ∀ a b : Outer (Bar2 (L 0)), a * b = b * a := by
      rcases hshape 0 with hX0 | hX0
      · exact uc22p22g_outer_comm hX0
      · exact PartOne.Section8.r899_outer_comm_Sz hX0
    have hXmem : ∀ x ∈ X, ∃ l ∈ L 0, ∃ l' ∈ L 1, l * l' = x := by
      intro x hx
      have hx' : x ∈ (L 0 : Set G) * (L 1 : Set G) := by
        rw [← hX]
        exact hx
      exact hx'
    have hL0X : L 0 ≤ X := by
      intro x hx
      show x ∈ (X : Set G)
      rw [hX]
      exact ⟨x, hx, 1, (L 1).one_mem, mul_one x⟩
    have hXM : X ≤ D.M := by
      intro x hx
      obtain ⟨l, hl, l', hl', rfl⟩ := hXmem x hx
      exact D.M.mul_mem (hL0M hl) (hL1M hl')
    have hXN0 : X ≤ normalizer (L 0 : Set G) := by
      intro x hx
      obtain ⟨l, hl, l', hl', rfl⟩ := hXmem x hx
      exact (normalizer _).mul_mem (Subgroup.le_normalizer hl) (h10 hl')
    have hXN1 : X ≤ normalizer (L 1 : Set G) := by
      intro x hx
      obtain ⟨l, hl, l', hl', rfl⟩ := hXmem x hx
      exact (normalizer _).mul_mem (h01 hl) (Subgroup.le_normalizer hl')
    have hXNX : X ≤ normalizer (pCoreOf 2 X : Set G) := fun x hx =>
      UC6S846.normalizer_le_normalizer_pCoreOf X (Subgroup.le_normalizer hx)
    have hO0 : pCoreOf 2 (L 0) ≤ pCoreOf 2 X :=
      uc22p21c_le_pCoreOf ((uc22p21d_pCoreOf_le _).trans hL0X) (UC6S846.isPGroup_pCoreOf _)
        fun k hk x hx => conj_mem_pCoreOf (hXN0 hk) hx
    have hO1 : pCoreOf 2 (L 1) ≤ pCoreOf 2 X := by
      refine uc22p21c_le_pCoreOf ((uc22p21d_pCoreOf_le _).trans ?_) (UC6S846.isPGroup_pCoreOf _)
        fun k hk x hx => conj_mem_pCoreOf (hXN1 hk) hx
      intro x hx
      show x ∈ (X : Set G)
      rw [hX]
      exact ⟨1, (L 0).one_mem, x, hx, one_mul x⟩
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥D.M →* Outer (Bar2 X),
        ∀ m : ↥D.M, ψ m = outHom X ⟨(m : G), hMX m.2⟩ :=
      ⟨(outHom X).comp (Subgroup.inclusion hMX), fun m => rfl⟩
    have hker : ψ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M := by
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, outHom_eq_one_iff]
      constructor
      · rintro ⟨x, hxX, hc⟩
        have hyC : x⁻¹ * (m : G) ∈ F08.CentOverO2 D.M X :=
          Subgroup.subset_closure ⟨D.M.mul_mem (D.M.inv_mem (hXM hxX)) m.2, hc.2⟩
        have e : (m : G) = x * (x⁻¹ * m) := by group
        rw [e]
        exact (X ⊔ F08.CentOverO2 D.M X).mul_mem (Subgroup.mem_sup_left hxX)
          (Subgroup.mem_sup_right hyC)
      · intro h
        have hK : ∀ g (hg : g ∈ normalizer (X : Set G)), InnBar X g →
            g ∈ ((outHom X).ker).map (normalizer (X : Set G)).subtype := fun g hg hi =>
          ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 ((outHom_eq_one_iff X hg).2 hi), rfl⟩
        have hle : X ⊔ F08.CentOverO2 D.M X ≤
            ((outHom X).ker).map (normalizer (X : Set G)).subtype := by
          refine sup_le (fun x hx => hK x (Subgroup.le_normalizer hx) ⟨x, hx, ?_⟩) ?_
          · rw [inv_mul_cancel]
            exact uc22p21d_centralizesBar_one X
          · unfold F08.CentOverO2
            rw [Subgroup.closure_le]
            rintro y ⟨hyM, hy⟩
            refine hK y (hMX hyM) ⟨1, X.one_mem, ?_⟩
            rw [inv_one, one_mul]
            exact uc22p21d_centralizesBar_iff.2 hy
        obtain ⟨z, hz, hzm⟩ := hle h
        have hzm' : z = ⟨m, hMX m.2⟩ := Subtype.ext hzm
        rw [hzm'] at hz
        exact (outHom_eq_one_iff X _).1 (MonoidHom.mem_ker.1 hz)
    have hkey1 : ∀ m : ↥D.M, ψ m = 1 → InnBar (L 0) m := by
      intro m h
      rw [hψ, outHom_eq_one_iff] at h
      obtain ⟨x, hxX, hc⟩ := h
      obtain ⟨l, hl, l', hl', rfl⟩ := hXmem x hxX
      have hy : CentralizesBar ((l * l')⁻¹ * m) (L 0) :=
        centralizesBar_of_centralizesBar_sup (hLC 0) (hLC 1) hne (hshape 1) hperm hL0X hXM hMX
          (D.M.mul_mem (D.M.inv_mem (hXM hxX)) m.2) hc
      refine ⟨l, hl, ?_⟩
      have e : l⁻¹ * (m : G) = l' * ((l * l')⁻¹ * m) := by group
      rw [e]
      exact uc22p21d_centralizesBar_mul (hcen0 l' hl') hy
    have htN' : (t : G)⁻¹ ∉ normalizer (L 0 : Set G) := fun h =>
      htN (by simpa using (normalizer (L 0 : Set G)).inv_mem h)
    have hsw' : ∀ x : ↥D.M, (x : G) ∉ normalizer (L 0 : Set G) →
        ((t⁻¹ * x : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := fun x hx =>
      mul_mem_normalizer_of_swap hperm (D.M.inv_mem t.2) x.2 htN' hx
    have htr : ∀ m : ↥D.M, ∀ hm : (m : G) ∈ normalizer (L 0 : Set G),
        ∀ hm' : ((t⁻¹ * (m * t) : ↥D.M) : G) ∈ normalizer (L 0 : Set G),
        outHom (L 0) ⟨m, hm⟩ * outHom (L 0) ⟨(t⁻¹ * (m * t) : ↥D.M), hm'⟩ = 1 :=
      fun m hm hm' => outHom_mul_conj_eq_one hpp hOp hcard0 hcomm0 t htN hsw' m hm hm'
    have hTR : ∀ m : ↥D.M, (m : G) ∈ normalizer (L 0 : Set G) → InnBar (L 0) m → ψ m = 1 := by
      intro m hm h0
      have hm' : ((t⁻¹ * (m * t) : ↥D.M) : G) ∈ normalizer (L 0 : Set G) :=
        conj_mem_normalizer hperm t.2 m.2 hm
      have h1 := htr m hm hm'
      rw [(outHom_eq_one_iff _ hm).2 h0, one_mul, outHom_eq_one_iff] at h1
      have h2 := innBar_conj (t : G) h1
      rw [ht01, show (t : G) * ((t⁻¹ * (m * t) : ↥D.M) : G) * (t : G)⁻¹ = m by
        push_cast; group] at h2
      rw [hψ, outHom_eq_one_iff]
      exact innBar_sup hX h10 hcen0 hcen1 hO0 hO1 hXNX h0 h2
    have hrr : ∀ x : ↥D.M, ψ x = 1 → ψ.rangeRestrict x = 1 := fun x hx => Subtype.ext hx
    obtain ⟨d, hd_def⟩ : ∃ d : ↥ψ.range, d = ψ.rangeRestrict y₀ := ⟨_, rfl⟩
    have hdo : orderOf d = p := by
      refine orderOf_eq_prime ?_ ?_
      · have hm : ((y₀ ^ p : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
          push_cast
          exact pow_mem hy₀N p
        have h1 : outHom (L 0) ⟨((y₀ ^ p : ↥D.M) : G), hm⟩ = 1 := by
          have e : (⟨((y₀ ^ p : ↥D.M) : G), hm⟩ : ↥(normalizer (L 0 : Set G))) =
              ⟨(y₀ : G), hy₀N⟩ ^ p := Subtype.ext (by simp)
          rw [e, map_pow]
          exact pow_eq_one_of_card_dvd hcard0 _
        rw [hd_def, ← map_pow]
        exact hrr _ (hTR _ hm ((outHom_eq_one_iff _ hm).1 h1))
      · rw [hd_def]
        intro h1
        apply hy₀
        exact (outHom_eq_one_iff _ hy₀N).2 (hkey1 y₀ (congrArg Subtype.val h1))
    obtain ⟨a, ha_def⟩ : ∃ a : ↥ψ.range, a = ψ.rangeRestrict t := ⟨_, rfl⟩
    have hao : orderOf a = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · have hm : ((t ^ 2 : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
          push_cast
          rw [pow_two]
          exact mul_mem_normalizer_of_swap hperm t.2 t.2 htN htN
        have h1 : outHom (L 0) ⟨((t ^ 2 : ↥D.M) : G), hm⟩ = 1 := by
          refine map_eq_one_of_card_dvd hpp hcard0 _ ?_
          rw [Subgroup.orderOf_mk]
          intro h
          exact htp (h.trans (by push_cast; exact orderOf_pow_dvd 2))
        rw [ha_def, ← map_pow]
        exact hrr _ (hTR _ hm ((outHom_eq_one_iff _ hm).1 h1))
      · rw [ha_def]
        intro h1
        exact htN (mem_normalizer_of_innBar (hkey1 t (congrArg Subtype.val h1)))
    have hinv : a * d * a⁻¹ = d⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ha_def, hd_def, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      have hm₁ : ((t * y₀ * t⁻¹ : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
        have := conj_mem_normalizer hperm (D.M.inv_mem t.2) y₀.2 hy₀N
        simpa [mul_assoc] using this
      have hm₁' : ((t⁻¹ * ((t * y₀ * t⁻¹) * t) : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
        simpa [mul_assoc] using hy₀N
      have hm : ((t * y₀ * t⁻¹ * y₀ : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
        push_cast
        exact (normalizer _).mul_mem hm₁ hy₀N
      have h1 := htr _ hm₁ hm₁'
      rw [outHom_congr (L 0) (show ((t⁻¹ * ((t * y₀ * t⁻¹) * t) : ↥D.M) : G) = y₀ by
        push_cast; group) hm₁' hy₀N] at h1
      have h2 : outHom (L 0) ⟨((t * y₀ * t⁻¹ * y₀ : ↥D.M) : G), hm⟩ = 1 := by
        have e : (⟨((t * y₀ * t⁻¹ * y₀ : ↥D.M) : G), hm⟩ : ↥(normalizer (L 0 : Set G))) =
            ⟨((t * y₀ * t⁻¹ : ↥D.M) : G), hm₁⟩ * ⟨(y₀ : G), hy₀N⟩ := Subtype.ext (by simp)
        rw [e, map_mul]
        exact h1
      exact hrr _ (hTR _ hm ((outHom_eq_one_iff _ hm).1 h2))
    have hgen0 : ∀ m : ↥D.M, (m : G) ∈ normalizer (L 0 : Set G) →
        ψ.rangeRestrict m ∈ Subgroup.zpowers d := by
      intro m hm
      obtain ⟨k, hk⟩ := exists_zpow_eq_of_card_dvd hpp hcard0 hy₀ (outHom (L 0) ⟨m, hm⟩)
      have hmk : ((m * y₀ ^ (-k) : ↥D.M) : G) ∈ normalizer (L 0 : Set G) := by
        push_cast
        exact (normalizer _).mul_mem hm (zpow_mem hy₀N _)
      have h1 : outHom (L 0) ⟨((m * y₀ ^ (-k) : ↥D.M) : G), hmk⟩ = 1 := by
        have e : (⟨((m * y₀ ^ (-k) : ↥D.M) : G), hmk⟩ : ↥(normalizer (L 0 : Set G))) =
            ⟨(m : G), hm⟩ * ⟨(y₀ : G), hy₀N⟩ ^ (-k) := Subtype.ext (by simp)
        rw [e, map_mul, map_zpow, zpow_neg, hk, mul_inv_cancel]
      have h2 : ψ.rangeRestrict m * d ^ (-k) = 1 := by
        rw [hd_def, ← map_zpow, ← map_mul]
        exact hrr _ (hTR _ hmk ((outHom_eq_one_iff _ hmk).1 h1))
      rw [mul_eq_one_iff_eq_inv, zpow_neg, inv_inv] at h2
      rw [h2]
      exact zpow_mem (Subgroup.mem_zpowers d) k
    have hgen : ∀ q : ↥ψ.range, q ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
      intro q
      obtain ⟨m, rfl⟩ := ψ.rangeRestrict_surjective q
      by_cases hm : (m : G) ∈ normalizer (L 0 : Set G)
      · exact Subgroup.mem_sup_left (hgen0 m hm)
      · have e : ψ.rangeRestrict m = a * ψ.rangeRestrict (t⁻¹ * m) := by
          rw [ha_def, ← map_mul, mul_inv_cancel_left]
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
          (Subgroup.mem_sup_left (hgen0 _ (hsw' m hm)))
    obtain ⟨e⟩ := CFSG.Quasithin.nonempty_mulEquiv_dihedral hp2 hdo hao hinv hgen
    refine ⟨e.toMonoidHom.comp ψ.rangeRestrict, e.surjective.comp ψ.rangeRestrict_surjective, ?_⟩
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, hker]

end CFSG.LocalAnalysis.UniquenessCase.UC22
