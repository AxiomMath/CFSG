module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.E3Defs
import CFSG.GroupTheory.ElemAbelianClosure

section

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

namespace O8S

variable {W : Type} [CommGroup W] {Hs Ks : Subgroup (MulAut W)} {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def phi (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F)) :
    ↥Hs →* Gamma F :=
  (gammaEquivMulAut hn hF).symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
    (Ks.normalizerMonoidHom.comp (Subgroup.inclusion hHN)))

variable (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
  (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))

theorem gammaToMulAut_phi (h : ↥Hs) :
    gammaToMulAut F (phi hn hF hHN e h) =
      MulAut.congr e (Ks.normalizerMonoidHom (Subgroup.inclusion hHN h)) :=
  (gammaEquivMulAut hn hF).apply_symm_apply _

theorem phi_of_mem (hKH : Ks ≤ Hs) (k : ↥Ks) :
    phi hn hF hHN e ⟨k, hKH k.2⟩ = SemidirectProduct.inl (e k) := by
  apply (gammaToMulAut_bijective_of_card hF).1
  rw [gammaToMulAut_phi, gammaToMulAut_inl,
    ← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  congr 1

include hF in
theorem eq_one_of_mem_centralizer [Finite F] (e : ↥Ks ≃* SL(2, F)) {z : MulAut W} (hz : z ∈ Ks)
    (hzc : z ∈ Subgroup.centralizer (Ks : Set (MulAut W))) : z = 1 := by
  have : CharP F 2 := char_two_of_card hF
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc k k.2)
  rw [sl2_center_eq_bot, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hcen
  exact congrArg Subtype.val hcen

theorem centralizer_normal (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) :
    ((Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W))).subgroupOf Hs).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  refine ⟨(g * x * g⁻¹).2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hk' : (g : MulAut W)⁻¹ * k * g ∈ Ks := by
    have := (hHN (inv_mem g.2) k).mp hk
    simpa [mul_assoc] using this
  have hxk := Subgroup.mem_centralizer_iff.mp hx.2 _ hk'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc k * ((g : MulAut W) * x * (g : MulAut W)⁻¹)
      = g * (((g : MulAut W)⁻¹ * k * g) * x) * (g : MulAut W)⁻¹ := by group
    _ = g * (x * ((g : MulAut W)⁻¹ * k * g)) * (g : MulAut W)⁻¹ := by rw [hxk]
    _ = (g : MulAut W) * x * (g : MulAut W)⁻¹ * k := by group

include hF in
theorem centralizer_eq_bot [Finite F] (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W)))
    (e : ↥Ks ≃* SL(2, F)) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) :
    Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W)) = ⊥ := by
  set N : Subgroup ↥Hs := (Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W))).subgroupOf Hs
    with hN
  have hNp : IsPGroup 2 N := by
    intro x
    obtain ⟨k, hk⟩ := h2 _ (x : ↥Hs).2
    have hxC : ((x : ↥Hs) : MulAut W) ∈ Subgroup.centralizer (Ks : Set (MulAut W)) :=
      (Subgroup.mem_subgroupOf.mp x.2).2
    have h1 := eq_one_of_mem_centralizer hF e hk (pow_mem hxC _)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h1
  have hle : N ≤ CFSG.pCore 2 ↥Hs := le_sSup ⟨centralizer_normal hHN, hNp⟩
  rw [hO] at hle
  rw [eq_bot_iff]
  intro x hx
  have hxN : (⟨x, hx.1⟩ : ↥Hs) ∈ N := Subgroup.mem_subgroupOf.mpr hx
  have := hle hxN
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

include hF in
theorem phi_injective [Finite F] (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) : Function.Injective (phi hn hF hHN e) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : MulAut.congr e (Ks.normalizerMonoidHom (Subgroup.inclusion hHN h)) = 1 := by
    rw [← gammaToMulAut_phi hn hF hHN e h, hh, map_one]
  have h3 : Ks.normalizerMonoidHom (Subgroup.inclusion hHN h) = 1 :=
    (map_eq_one_iff _ (MulAut.congr e).injective).mp h1
  have hc : (h : MulAut W) ∈ Hs ⊓ Subgroup.centralizer (Ks : Set (MulAut W)) := by
    refine ⟨h.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h4 := congrArg (fun α : MulAut ↥Ks => ((α ⟨k, hk⟩ : ↥Ks) : MulAut W)) h3
    change (h : MulAut W) * k * (h : MulAut W)⁻¹ = k at h4
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4.symm
  rw [centralizer_eq_bot hF hHN e h2 hO, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

include hF in
theorem mem_of_phi_mem [Finite F] (hKH : Ks ≤ Hs) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
    (hO : CFSG.pCore 2 ↥Hs = ⊥) (h : ↥Hs) (hh : phi hn hF hHN e h ∈ linearKernel F) :
    (h : MulAut W) ∈ Ks := by
  rw [mem_linearKernel_iff] at hh
  set k : ↥Ks := e.symm (phi hn hF hHN e h).left
  have hk : phi hn hF hHN e ⟨k, hKH k.2⟩ = phi hn hF hHN e h := by
    rw [phi_of_mem hn hF hHN e hKH, MulEquiv.apply_symm_apply]
    exact SemidirectProduct.ext rfl hh.symm
  rw [← phi_injective hn hF hHN e h2 hO hk]
  exact k.2

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC

end

end

section

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin

namespace O8S

variable {W : Type} [CommGroup W]

theorem mem_fixV_zpowers {x : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fix_comm_elt (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W} (hz : z * z = 1) (w : W) :
    z (z w * w⁻¹) = z w * w⁻¹ := by
  have hzz : z (z w) = w := by rw [← MulAut.mul_apply, hz, MulAut.one_apply]
  have hinv : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hW v)
  rw [map_mul, map_inv, hzz, hinv (z w), hinv w, mul_comm]

theorem commute_of_fix_iff (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : ∀ w, x w = w ↔ y w = w) : x * y = y * x := by
  ext w
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have hcx := fix_comm_elt hW hx w
  have hdy := fix_comm_elt hW hy w
  have hcy := (hxy _).mp hcx
  have hdx := (hxy _).mpr hdy
  set a := x w * w⁻¹ with ha
  set b := y w * w⁻¹ with hb
  have hxw : x w = a * w := by rw [ha]; group
  have hyw : y w = b * w := by rw [hb]; group
  rw [hyw, map_mul, hdx, hxw, map_mul, hcy, hyw]
  exact mul_left_comm b a w

theorem conj_fix_iff (k u : MulAut W) (w : W) : (k * u * k⁻¹) w = w ↔ u (k⁻¹ w) = k⁻¹ w := by
  simp only [MulAut.mul_apply]
  constructor
  · intro h
    have := congrArg (k⁻¹ : MulAut W) h
    rwa [MulAut.inv_apply_self] at this
  · intro h
    rw [h, MulAut.apply_inv_self]

theorem fix_conj_iff {k u t : MulAut W} (hkt : k * t = t * k)
    (hut : ∀ w, u w = w ↔ t w = w) (w : W) : (k * u * k⁻¹) w = w ↔ t w = w := by
  have hkt' : k * t * k⁻¹ = t := by rw [hkt, mul_inv_cancel_right]
  rw [conj_fix_iff, hut, ← conj_fix_iff, hkt']

theorem isElementaryAbelian_of {G : Type*} [Group G] {B : Subgroup G}
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hs : ∀ a ∈ B, a ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_forall hc hs

theorem isPGroup_of_isElemAbelian2 {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) :
    IsPGroup 2 ↥A :=
  fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩

variable [Finite W]

theorem two_pow_le_card {n : ℕ} {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet n X) :
    2 ^ n ≤ Nat.card ↥A := by
  obtain ⟨-, hA1, hA2, hfix⟩ := hA
  have hP := isPGroup_of_isElemAbelian2 hA2
  have hcard := E3.card_eq_two_pow_mul hP (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
  rw [Subgroup.card_bot, mul_one] at hcard
  rw [hcard]
  refine Nat.pow_le_pow_right (by norm_num) (not_lt.mp fun hlt => hA1 ?_)
  have h1 := hfix ⊥ bot_le hlt
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ fixV (⊥ : Subgroup (MulAut W)) := fun x hx => by
    rw [Subgroup.mem_bot.mp hx]
    rfl
  rw [h1] at hw
  exact hw a ha

theorem fixV_zpowers_eq {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X)
    (h4 : Nat.card ↥A = 4) {u : MulAut W} (hu : u ∈ A) (hu1 : u ≠ 1) :
    fixV (Subgroup.zpowers u) = fixV A := by
  obtain ⟨-, -, hA2, hfix⟩ := hA
  have hle : Subgroup.zpowers u ≤ A := Subgroup.zpowers_le.mpr hu
  have hord : orderOf u = 2 := orderOf_eq_prime (hA2.2 u hu) hu1
  have hcard := E3.card_eq_two_pow_mul (isPGroup_of_isElemAbelian2 hA2) hle
  rw [h4, Nat.card_zpowers, hord] at hcard
  refine hfix _ hle ?_
  have h2 : 2 ^ E3.mQuot A (Subgroup.zpowers u) = 2 ^ 1 := by omega
  have := Nat.pow_right_injective le_rfl h2
  omega

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC

end

end

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

namespace O8S

variable {W : Type} [CommGroup W] {Hs Ks : Subgroup (MulAut W)} {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def img (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))
    (B : Subgroup (MulAut W)) : Subgroup (Gamma F) :=
  (B.subgroupOf Hs).map (phi hn hF hHN e)

theorem isElemAbelian2_closure {S : Set (MulAut W)} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a ^ 2 = 1) : IsElemAbelian2 (Subgroup.closure S) := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hc b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set (MulAut W)) :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha).symm
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (h2 hb) a ha)
  refine ⟨hcomm, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hcomm x hx y hy) 2), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem three_le_card {G : Type*} [Group G] {K : Subgroup G} [Finite K] {a b : G} (ha : a ∈ K)
    (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card K := by
  let f : Fin 3 → K := ![1, ⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;> simp_all
  simpa using Nat.card_le_card_of_injective f hf

@[expose] def ord3 [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 1], by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2⟩

theorem ord3_pow_three [CharP F 2] : (ord3 : SL(2, F)) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem ord3_ne_one [CharP F 2] : (ord3 : SL(2, F)) ≠ 1 := by
  intro h1
  have h2 := congrArg (fun s : SL(2, F) => s.1 0 0) h1
  simp [ord3] at h2

theorem ord3_mem_fixedSL2 [CharP F 2] (σ : RingAut F) : (ord3 : SL(2, F)) ∈ fixedSL2 σ := by
  rw [← sl2_field_fixed_iff]
  apply Subtype.ext
  rw [sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ord3]

section Rank

variable (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
  (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))

theorem img_isElementaryAbelian {B : Subgroup (MulAut W)} (hB : IsElemAbelian2 B) :
    CFSG.IsElementaryAbelian 2 ↥(img hn hF hHN e B) := by
  apply isElementaryAbelian_of
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.1 _ ha _ hb)
  · rintro _ ⟨a, ha, rfl⟩
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hB.2 _ ha)
    rw [← map_pow, this, map_one]

theorem phi_mem_img {B : Subgroup (MulAut W)} {b : ↥Hs} (hb : (b : MulAut W) ∈ B) :
    phi hn hF hHN e b ∈ img hn hF hHN e B :=
  Subgroup.mem_map.mpr ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩

variable [Finite F] (hKH : Ks ≤ Hs) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks)
  (hO : CFSG.pCore 2 ↥Hs = ⊥)

include h2 hO in
theorem card_img {B : Subgroup (MulAut W)} (hBH : B ≤ Hs) :
    Nat.card ↥(img hn hF hHN e B) = Nat.card ↥B := by
  rw [img, Subgroup.card_map_of_injective (phi_injective hn hF hHN e h2 hO)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv

include hKH h2 hO in
theorem rank_data {B : Subgroup (MulAut W)} (hBH : B ≤ Hs) (hB : IsElemAbelian2 B)
    {t : MulAut W} (htB : t ∈ B) (htK : t ∉ Ks) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧ Nat.card ↥B ≤ 2 ^ (s + 1) ∧
      Nat.card ↥B = 2 * Nat.card ↥(intersectionS (img hn hF hHN e B)) ∧
      Nat.card ↥(intersectionS (img hn hF hHN e B)) ≤ 2 ^ s ∧
      Nat.card (fixedField (phi hn hF hHN e ⟨t, hBH htB⟩).right) = 2 ^ s ∧
      ∃ x : SL(2, F), centralizerS (phi hn hF hHN e ⟨t, hBH htB⟩) =
        (fixedSL2 (phi hn hF hHN e ⟨t, hBH htB⟩).right).map (MulAut.conj x).toMonoidHom := by
  have := img_isElementaryAbelian hn hF hHN e hB
  have hout : phi hn hF hHN e ⟨t, hBH htB⟩ ∉ linearKernel F :=
    fun h => htK (mem_of_phi_mem hn hF hHN e hKH h2 hO _ h)
  obtain ⟨s, hs1, hns, -, hfix, ⟨x, -, hx⟩, -, hfac, hI, hA, -, -, -⟩ :=
    original_outer_elementary_field_conjugacy_and_rank hn hF (img hn hF hHN e B) _
      (phi_mem_img hn hF hHN e htB) hout
  rw [card_img hn hF hHN e h2 hO hBH] at hfac hA
  rw [linearIntersection_card_eq_intersectionS] at hfac hI
  exact ⟨s, hs1, hns, hA, hfac, hI, hfix, x, hx⟩

end Rank

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC
