module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem s16h_closure_conj_isElemAbelian {A : Type*} [Group A] {Mb Lb B : Subgroup A}
    {p : ℕ} (hBL : B ≤ Lb) (hBe : IsElemAbelian p B)
    (hBc : ∀ b ∈ B, ∀ l ∈ Lb, b * l = l * b)
    (hcomm : ∀ q ∈ Mb, ∀ q' ∈ Mb,
      Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom →
        ⁅Lb.map (MulAut.conj q).toMonoidHom, Lb.map (MulAut.conj q').toMonoidHom⁆ = ⊥) :
    IsElemAbelian p (Subgroup.closure {x : A | ∃ q ∈ Mb, ∃ b ∈ B, x = q * b * q⁻¹}) := by
  let gen : Set A := {x | ∃ q ∈ Mb, ∃ b ∈ B, x = q * b * q⁻¹}
  have hcomm_gen : gen.Pairwise Commute := by
    rintro x ⟨q, hq, b, hb, rfl⟩ y ⟨q', hq', b', hb', rfl⟩ hxy
    have hxL : q * b * q⁻¹ ∈ Lb.map (MulAut.conj q).toMonoidHom := by
      simpa [MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom (hBL hb)
    have hyL : q' * b' * q'⁻¹ ∈ Lb.map (MulAut.conj q').toMonoidHom := by
      simpa [MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj q').toMonoidHom (hBL hb')
    by_cases heq : Lb.map (MulAut.conj q).toMonoidHom =
        Lb.map (MulAut.conj q').toMonoidHom
    · have hxL' : q * b * q⁻¹ ∈ Lb.map (MulAut.conj q').toMonoidHom := by
        rw [← heq]; exact hxL
      obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp hxL'
      have hlq' : q * b * q⁻¹ = q' * l * q'⁻¹ := by
        rw [← hlq]; rfl
      have hbl : b' * l = l * b' := hBc b' hb' l hl
      show (q * b * q⁻¹) * (q' * b' * q'⁻¹) =
        (q' * b' * q'⁻¹) * (q * b * q⁻¹)
      rw [hlq']
      simp only [conj_mul, hbl]
    · have hmem : ⁅q * b * q⁻¹, q' * b' * q'⁻¹⁆ ∈
          ⁅Lb.map (MulAut.conj q).toMonoidHom, Lb.map (MulAut.conj q').toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator hxL hyL
      rw [hcomm q hq q' hq' heq, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_commute.mp hmem
  have hcommX : IsMulCommutative (Subgroup.closure gen) :=
    Subgroup.isMulCommutative_closure hcomm_gen
  haveI := hcommX
  refine ⟨hcommX, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q, hq, b, hb, rfl⟩ := hy
    rw [conj_pow, hBe.2 b hb]
    simp
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := setLike_mul_comm hx hy
    rw [hxy.mul_pow p, ihx, ihy]
    simp
  | inv x hx ih =>
    rw [inv_pow, ih]
    simp

theorem s16h_normalClosure_data {A : Type*} [Group A] {Mb Lb B : Subgroup A} {p : ℕ}
    (hBL : B ≤ Lb) (hBe : IsElemAbelian p B) (hBc : ∀ b ∈ B, ∀ l ∈ Lb, b * l = l * b)
    (hBd : B ≤ ⁅Mb, Mb⁆)
    (hcomm : ∀ q ∈ Mb, ∀ q' ∈ Mb,
      Lb.map (MulAut.conj q).toMonoidHom ≠ Lb.map (MulAut.conj q').toMonoidHom →
        ⁅Lb.map (MulAut.conj q).toMonoidHom, Lb.map (MulAut.conj q').toMonoidHom⁆ = ⊥) :
    ∃ X : Subgroup A, X ≤ ⁅Mb, Mb⁆ ∧ (∀ q ∈ Mb, ∀ x ∈ X, q * x * q⁻¹ ∈ X) ∧
      IsElemAbelian p X ∧ ∀ q ∈ Mb, B.map (MulAut.conj q).toMonoidHom ≤ X := by
  let gen : Set A := {x | ∃ q ∈ Mb, ∃ b ∈ B, x = q * b * q⁻¹}
  refine ⟨Subgroup.closure gen, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨q, hq, b, hb, rfl⟩
    have hbMb : b ∈ Mb := Subgroup.commutator_le_self Mb (hBd hb)
    have hcq : ⁅q, b⁆ ∈ ⁅Mb, Mb⁆ := Subgroup.commutator_mem_commutator hq hbMb
    have heq : q * b * q⁻¹ = ⁅q, b⁆ * b := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact (⁅Mb, Mb⁆).mul_mem hcq (hBd hb)
  · intro q' hq' x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨q, hq, b, hb, rfl⟩ := hy
      exact Subgroup.subset_closure
        ⟨q' * q, Mb.mul_mem hq' hq, b, hb, by group⟩
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [show q' * (x * y) * q'⁻¹ = (q' * x * q'⁻¹) * (q' * y * q'⁻¹) from by group]
      exact (Subgroup.closure gen).mul_mem ihx ihy
    | inv x hx ih =>
      rw [show q' * x⁻¹ * q'⁻¹ = (q' * x * q'⁻¹)⁻¹ from by group]
      exact (Subgroup.closure gen).inv_mem ih
  · exact s16h_closure_conj_isElemAbelian hBL hBe hBc hcomm
  · intro q hq
    rintro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using
      Subgroup.subset_closure (show q * b * q⁻¹ ∈ gen from ⟨q, hq, b, hb, rfl⟩)

theorem s16h_two_le_pRank_sup {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {B₁ B₂ : Subgroup A} (hc : ⁅B₁, B₂⁆ = ⊥) (hi : B₁ ⊓ B₂ = ⊥) (h₁ : p ∣ Nat.card B₁)
    (h₂ : p ∣ Nat.card B₂) : 2 ≤ CFSG.Open.pRank p (B₁ ⊔ B₂) := by
  haveI := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p h₁
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p h₂
  have ha' : orderOf (a : A) = p := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : A) = p := by rw [Subgroup.orderOf_coe]; exact hb
  have hcomm : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
    intro x hx y hy
    have h := Subgroup.commutator_mem_commutator hx hy
    rw [hc, Subgroup.mem_bot, commutatorElement_def] at h
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
  have hza : zpowers (a : A) ≤ B₁ := Subgroup.zpowers_le.2 a.2
  have hzb : zpowers (b : A) ≤ B₂ := Subgroup.zpowers_le.2 b.2
  let f : zpowers (a : A) × zpowers (b : A) →* A := MonoidHom.noncommCoprod
    (zpowers (a : A)).subtype (zpowers (b : A)).subtype
    (fun x y => hcomm x (hza x.2) y (hzb y.2))
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : A) * y = 1 := hxy
    have hx : (x : A) ∈ B₁ ⊓ B₂ := Subgroup.mem_inf.2 ⟨hza x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact B₂.inv_mem (hzb y.2)⟩
    rw [hi, Subgroup.mem_bot] at hx
    have hy : (y : A) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hpowa : ∀ x : zpowers (a : A), x ^ p = 1 := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    have h : (x : A) ^ p = 1 := by
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha',
        pow_orderOf_eq_one, one_zpow]
    exact Subtype.ext (by simpa using h)
  have hpowb : ∀ y : zpowers (b : A), y ^ p = 1 := by
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
    have h : (y : A) ^ p = 1 := by
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hb',
        pow_orderOf_eq_one, one_zpow]
    exact Subtype.ext (by simpa using h)
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := zpowers (a : A) × zpowers (b : A))
    ?_ ?_ ?_ f hf ?_
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    exact Prod.ext (mul_comm' x₁ x₂) (mul_comm' y₁ y₂)
  · rintro ⟨x, y⟩
    exact Prod.ext (hpowa x) (hpowb y)
  · rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha', hb', sq]
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact (B₁ ⊔ B₂).mul_mem (Subgroup.mem_sup_left (hza x.2)) (Subgroup.mem_sup_right (hzb y.2))

private theorem s16h_eq_one_of_fixes_commSub {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)}
    (hgen : (⨆ X ∈ conjSubs A (commSub (⊤ : Subgroup W) L), X) = ⊤)
    (h2 : ∀ g ∈ A, g ∉ normalizer (L : Set (MulAut W)) →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥)
    {l : MulAut W} (hl : l ∈ L)
    (hfix : ∀ u ∈ commSub (⊤ : Subgroup W) L, l u = u) : l = 1 := by
  have hF : fixV (Subgroup.zpowers l) = ⊤ := by
    rw [← top_le_iff, ← hgen]
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨a, ha, rfl⟩ := hX
    intro u hu
    rw [mem_fixV_zpowers_iff_apply]
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    by_cases haN : a ∈ normalizer (L : Set (MulAut W))
    · have haw : a w ∈ commSub (⊤ : Subgroup W) L :=
        commSub_top_map151b (X := L) (Y := L) (g := a)
          (fun x hx => (Subgroup.mem_normalizer_iff.mp haN x).mp hx) w hw
      exact hfix (a w) haw
    · have hainvN : a⁻¹ ∉ normalizer (L : Set (MulAut W)) := by
        intro hcon
        exact haN ((normalizer (L : Set (MulAut W))).inv_mem hcon)
      have hbot := (h2 a⁻¹ (A.inv_mem ha) hainvN).2
      have hle := commSub_eq_bot_iff.mp hbot
      have hy : (MulAut.conj a⁻¹).toMonoidHom l ∈ L.map (MulAut.conj a⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hl
      have hconj : (MulAut.conj a⁻¹).toMonoidHom l = a⁻¹ * l * a := rfl
      have hfixy : (a⁻¹ * l * a) w = w := by
        rw [← hconj]
        exact (mem_fixV.mp (hle hw)) _ hy
      have h1 : a⁻¹ (l (a w)) = w := by
        simpa [MulAut.mul_apply] using hfixy
      have h2' : l (a w) = a w := by
        have := congrArg (fun z => a z) h1
        rwa [MulAut.apply_inv_self] at this
      exact h2'
  ext v
  have hv : v ∈ fixV (Subgroup.zpowers l) := by rw [hF]; trivial
  simpa using (mem_fixV_zpowers_iff_apply.mp hv)

theorem s16h_conj_comm_inf_of_conc {W : Type} [CommGroup W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (h : Conc4_136W A t L) {q q' : MulAut W} (hq : q ∈ A) (hq' : q' ∈ A)
    (hne : L.map (MulAut.conj q).toMonoidHom ≠ L.map (MulAut.conj q').toMonoidHom) :
    ⁅L.map (MulAut.conj q).toMonoidHom, L.map (MulAut.conj q').toMonoidHom⁆ = ⊥ ∧
      L.map (MulAut.conj q).toMonoidHom ⊓ L.map (MulAut.conj q').toMonoidHom = ⊥ := by
  let r : MulAut W := q'⁻¹ * q
  have hrA : r ∈ A := A.mul_mem (A.inv_mem hq') hq
  have hcomp : ((MulAut.conj q').toMonoidHom).comp ((MulAut.conj r).toMonoidHom) =
      (MulAut.conj q).toMonoidHom := by
    have h1 : MulAut.conj q' * MulAut.conj r = MulAut.conj q := by
      rw [← map_mul, show q' * r = q from by
        rw [show r = q'⁻¹ * q from rfl]; group]
    rw [← h1]
    rfl
  have hmap : L.map (MulAut.conj q).toMonoidHom =
      (L.map (MulAut.conj r).toMonoidHom).map (MulAut.conj q').toMonoidHom := by
    rw [Subgroup.map_map, hcomp]
  have hr_ne : L.map (MulAut.conj r).toMonoidHom ≠ L := by
    intro hLr
    apply hne
    rw [hmap, hLr]
  have hrN : r ∉ normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hr_ne
  have hrr := h.2.1 r hrA hrN
  have hcommbot : ⁅L.map (MulAut.conj q).toMonoidHom,
      L.map (MulAut.conj q').toMonoidHom⁆ = ⊥ := by
    have h1 : ⁅L.map (MulAut.conj q).toMonoidHom, L.map (MulAut.conj q').toMonoidHom⁆ =
        ⁅(L.map (MulAut.conj r).toMonoidHom).map (MulAut.conj q').toMonoidHom,
          L.map (MulAut.conj q').toMonoidHom⁆ := by rw [hmap]
    rw [h1, ← Subgroup.map_commutator]
    have h2 : ⁅L.map (MulAut.conj r).toMonoidHom, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hrr.1
    rw [h2, Subgroup.map_bot]
  have hinf : L ⊓ L.map (MulAut.conj r).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have hlL : l ∈ L := hl.1
    have hlLr : l ∈ L.map (MulAut.conj r).toMonoidHom := hl.2
    refine s16h_eq_one_of_fixes_commSub h.1 h.2.1 hlL ?_
    intro u hu
    have hu' : u ∈ fixV (L.map (MulAut.conj r).toMonoidHom) :=
      commSub_eq_bot_iff.mp hrr.2 hu
    exact (mem_fixV.mp hu') l hlLr
  refine ⟨hcommbot, ?_⟩
  rw [hmap, ← Subgroup.map_inf _ _ _ (MulAut.conj q').injective, inf_comm, hinf,
    Subgroup.map_bot]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
