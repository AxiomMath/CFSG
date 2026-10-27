module

public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

@[expose] def stabAt (A : Subgroup (MulAut W)) (w : W) : Subgroup (MulAut W) :=
  A ⊓ MulAction.stabilizer (MulAut W) w

theorem mem_stabAt {A : Subgroup (MulAut W)} {w : W} {a : MulAut W} :
    a ∈ stabAt A w ↔ a ∈ A ∧ a w = w := by
  simp [stabAt, MulAction.mem_stabilizer_iff]

theorem stabAt_le (A : Subgroup (MulAut W)) (w : W) : stabAt A w ≤ A := inf_le_left

theorem le_mQuot_stabAt_of_mem_aSet {k : ℕ} {X A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet k X) {w : W} (hw : w ∉ fixV A) : k ≤ E3.mQuot A (stabAt A w) := by
  by_contra hlt
  push Not at hlt
  have h := hA.2.2.2 (stabAt A w) (stabAt_le A w) hlt
  apply hw
  rw [← h]
  exact mem_fixV.2 fun a ha => (mem_stabAt.1 ha).2

variable [Finite W]

theorem exists_mem_secondLayer (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) {F : Subgroup W} (hF : F ≤ fixV A) (hFW : F ≠ ⊤) :
    ∃ w : W, w ∉ F ∧ ∀ a ∈ A, a w * w⁻¹ ∈ F := by
  have hNmap : ∀ a : A, F.map ((a : MulAut W) : W →* W) = F := by
    intro a
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      have hz' : ((a : MulAut W) : W →* W) z = z := by
        simpa using (mem_fixV.1 (hF hz)) (a : MulAut W) a.2
      rwa [hz']
    · intro y hy
      exact ⟨y, hy, by
        simpa using (mem_fixV.1 (hF hy)) (a : MulAut W) a.2⟩
  have hmul : ∀ a b : A,
      (QuotientGroup.congr F F ((a * b : A) : MulAut W) (hNmap (a * b)) :
          MulAut (W ⧸ F)) =
        (QuotientGroup.congr F F (a : MulAut W) (hNmap a) : MulAut (W ⧸ F)) *
          (QuotientGroup.congr F F (b : MulAut W) (hNmap b) : MulAut (W ⧸ F)) := by
    intro a b
    apply MulEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [MulAut.mul_apply, QuotientGroup.congr_mk, Subgroup.coe_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : A →* MulAut (W ⧸ F), ∀ a : A,
      φ a = QuotientGroup.congr F F (a : MulAut W) (hNmap a) :=
    ⟨MonoidHom.mk' (fun a : A => QuotientGroup.congr F F (a : MulAut W) (hNmap a)) hmul,
      fun a => rfl⟩
  letI : MulAction A (W ⧸ F) := MulAction.compHom (W ⧸ F) φ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (W ⧸ F) := (isPGroup_two_of_sq_eq_one hW).to_quotient F
  have hcard : 2 ∣ Nat.card (W ⧸ F) := by
    rcases hQp.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.index_eq_one.1 ((Subgroup.index_eq_card (H := F)).trans h1)) hFW
    · exact h2
  have hone : (1 : W ⧸ F) ∈ MulAction.fixedPoints A (W ⧸ F) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [MulAction.compHom_smul_def, MulAut.smul_def]
    exact map_one (φ a)
  obtain ⟨q, hqfix, hqne⟩ :=
    (E3.isPGroup_of_isElemAbelian2 hA).exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (W ⧸ F) hcard hone
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective q
  refine ⟨w, ?_, ?_⟩
  · intro hwF
    exact hqne (((QuotientGroup.eq_one_iff w).mpr hwF).symm.trans hw)
  · intro a ha
    have hfix := hqfix ⟨a, ha⟩
    rw [MulAction.compHom_smul_def, hφ ⟨a, ha⟩, MulAut.smul_def, ← hw,
      QuotientGroup.congr_mk] at hfix
    rw [QuotientGroup.eq_iff_div_mem] at hfix
    simpa [div_eq_mul_inv] using hfix

theorem fixV_ne_bot [Nontrivial W] (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) : fixV A ≠ ⊥ := by
  obtain ⟨m, -, hm1, hm⟩ := B1.exists_fixed_ne_one hW (E3.isPGroup_of_isElemAbelian2 hA)
    (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) fun h => by
      obtain ⟨x, hx⟩ := exists_ne (1 : W)
      exact hx ((Subgroup.eq_bot_iff_forall _).1 h x (Subgroup.mem_top x))
  intro h
  exact hm1 ((Subgroup.eq_bot_iff_forall _).1 h m (mem_fixV.2 hm))

theorem fixV_ne_top {A : Subgroup (MulAut W)} (hA : A ≠ ⊥) : fixV A ≠ ⊤ := by
  intro h
  apply hA
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  ext w
  exact mem_fixV.1 (h ▸ Subgroup.mem_top w) a ha

theorem two_pow_mQuot_stabAt_le {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    {U : Subgroup W} {w : W} (hw : ∀ a ∈ A, a w * w⁻¹ ∈ U) :
    2 ^ E3.mQuot A (stabAt A w) ≤ Nat.card U := by
  letI : MulAction A W := MulAction.compHom W A.subtype
  have hstab : MulAction.stabilizer A w = (stabAt A w).subgroupOf A := by
    ext a
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabAt,
      MulAction.compHom_smul_def, MulAut.smul_def]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  let f : MulAction.orbit A w → U := fun x =>
    let a : A := Classical.choose (MulAction.mem_orbit_iff.mp x.2)
    ⟨x.1 * w⁻¹, by
      have ha : a • w = x.1 := Classical.choose_spec (MulAction.mem_orbit_iff.mp x.2)
      rw [← ha, MulAction.compHom_smul_def, MulAut.smul_def]
      exact hw (a : MulAut W) a.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : x.1 * w⁻¹ = y.1 * w⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_right_cancel h1)
  have hcard_le : Nat.card (MulAction.orbit A w) ≤ Nat.card U :=
    Nat.card_le_card_of_injective f hf_inj
  calc
    2 ^ E3.mQuot A (stabAt A w)
        = (stabAt A w).relIndex A :=
          (E3.relIndex_eq_two_pow (E3.isPGroup_of_isElemAbelian2 hA) (stabAt A w)).symm
    _ = ((stabAt A w).subgroupOf A).index := rfl
    _ = (MulAction.stabilizer A w).index := by rw [hstab]
    _ = (MulAction.orbit A w).ncard := MulAction.index_stabilizer A w
    _ = Nat.card (MulAction.orbit A w) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card U := hcard_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
