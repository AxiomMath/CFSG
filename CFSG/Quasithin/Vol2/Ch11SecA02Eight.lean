module

public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem autOn_fixes_cV {L V : Subgroup G} :
    ∀ x ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, x z = z := by
  intro x hx z hz
  obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
  apply Subtype.ext
  rw [conjV_apply_coe]
  have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hz) l hl
  rw [this, mul_inv_cancel_right]

@[expose] def NaturalCases (T L I : Subgroup G) (n : ℕ) [IsMulCommutative ↥(fsuV T I)] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
      ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
        NoGraphAutomorphism π (autOn T (fsuV T I))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L (fsuV T I)) ≃* ↥(StatedSp 2 K)) ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
        NoGraphAutomorphismSp4 π (autOn T (fsuV T I))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L (fsuV T I)) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
      G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n)

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem conj_mem_autOn_of_T (h : Hyp11 G T L I n) :
    ∀ t ∈ autOn T (fsuV T I), ∀ x ∈ autOn L (fsuV T I), t * x * t⁻¹ ∈ autOn L (fsuV T I) := by
  intro t ht x hx
  obtain ⟨a, haT, haV, rfl⟩ := mem_autOn_iff.mp ht
  obtain ⟨b, hbL, hbV, rfl⟩ := mem_autOn_iff.mp hx
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul]
  exact conjV_mem_autOn (mul_mul_inv_mem (h.normal haT) hbL) _

theorem autOn_T_mem_cV_iff (h : Hyp11 G T L I n) :
    ∀ t ∈ autOn T (fsuV T I), ∀ w : ↥(fsuV T I),
      w ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) ↔
        t w ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
  intro t ht w
  obtain ⟨a, haT, haV, rfl⟩ := mem_autOn_iff.mp ht
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjV_apply_coe]
  exact Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (h.normal haT)) w

omit [Finite G] in
theorem cV_subgroupOf_eq_bot [IsMulCommutative ↥(fsuV T I)] {d : ℕ} (hd : 2 ≤ d) {K : Type}
    [Field K] {π : ↥(StatedSL d K) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL d K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥
      π) :
    (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  exact eq_one_of_fixed_of_realizesVia hd hπ fun x hx => autOn_fixes_cV x hx w hw

theorem false_of_autOn_sup_SL (hL34 : FactL34) (h : Hyp11 G T L I n) {X : Type} [Group X]
    {f : X →* ↥(autOn L (fsuV T I))} (hc : RecogCtx X _ n f) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : ↥(autOn (L ⊔ T) (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) : False := by
  have := isSimpleGroup_SL_zmod_two (n := d) (by omega)
  have heq := autOn_eq_of_isSimpleGroup hc le_sup_left (sup_le Subgroup.le_normalizer h.normal)
    e.isSimpleGroup
  set e' : ↥(StatedSL d (ZMod 2)) ≃* ↥(autOn L (fsuV T I)) :=
    ((specialLinearGroupEquivStatedSL d (ZMod 2)).symm.trans e.symm).trans
      (MulEquiv.subgroupCongr heq.symm)
  exact hc.false_of_SL_zmod_two hL34 hd e'.toMonoidHom e'.surjective

omit [Finite G] in
theorem false_of_autOn_sup_alt {X : Type} [Group X] {f : X →* ↥(autOn L (fsuV T I))}
    (hc : RecogCtx X _ n f)
    (e : ↥(autOn (L ⊔ T) (fsuV T I)) ≃* alternatingGroup (Fin 7)) : False := by
  have hdvd : Nat.card ↥(autOn L (fsuV T I)) ∣ Nat.card ↥(autOn (L ⊔ T) (fsuV T I)) :=
    Subgroup.card_dvd_of_le (Subgroup.map_mono fun _ hx => Subgroup.mem_sup_left hx)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
    show Nat.factorial 7 / 2 = 2 ^ 3 * 315 by decide] at hdvd
  exact hc.false_of_dvd (by decide) (by norm_num) hdvd

theorem false_of_3A6 {X Y : Type} [Group X] [Group Y] {f : X →* Y} (hc : RecogCtx X Y n f)
    (hZ : Nat.card (Subgroup.center Y) = 3)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) : False := by
  have h1 := (Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hZ] at h1
  exact hc.false_of_dvd (E := 3) (O := 135) (by decide) (by norm_num) (by rw [h1]; decide)

end CFSG.Quasithin.Vol2.Ch11.SecA
