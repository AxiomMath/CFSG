module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B15P4Res
public import CFSG.Quasithin.Background.SmithD321Kplus
public import CFSG.Quasithin.Vol2.Ch10SecA1012Six
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.RonanD321.Five

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Open CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mem_normalizer_of_comm {L : Subgroup (MulAut W)} {x : MulAut W}
    (hxL : ∀ l ∈ L, l * x = x * l) : x ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    have e : x * l * x⁻¹ = l := by rw [← hxL l hl]; group
    rw [e]
    exact hl
  · intro hl
    have e : x * l * x⁻¹ * x = x * (x * l * x⁻¹) := hxL _ hl
    have e' : l = x * l * x⁻¹ := by
      have h1 : x * l = x * (x * l * x⁻¹) := by rw [← e]; group
      exact mul_left_cancel h1
    rw [e']
    exact hl

omit [Finite W] in
theorem pow_apply_eq_self {s : MulAut W} {u : W} (h : s u = u) (n : ℕ) : (s ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem exists_isotypic_of_d321Two {L : Subgroup (MulAut W)} (hexp : ∀ w : W, w ^ 2 = 1)
    (h2 : D321Two L) :
    ∃ (I : Subgroup W) (hI : XMod.IsIrr ↥L I),
      IsotypicOfLength ↥L (commV L) I 4 ∧ Nat.card ↥(commV L) = 2 ^ 12 ∧
      Nat.card (Module.End ↥(XMod.opRing ↥L W) ↥(XMod.toSubmod hI.1)) = 2 := by
  obtain ⟨-, I, π, -, hind, hsup, hreal⟩ := h2
  have hind' : ∀ i, I i ⊓ ⨆ (j : Fin 4) (_ : j ≠ i), I j = ⊥ := fun i => by
    simpa using hind i
  have hsup' : (⨆ i, I i) = commV L := by simpa using hsup
  have hπ : Function.Surjective π := (hreal 0).1
  have hirr : ∀ i, XMod.IsIrr ↥L (I i) := fun i => B5.isIrr_of_realizes (by norm_num) (hreal i)
  have hiso : ∀ i j, XMod.Iso ↥L (I i) (I j) := fun i j =>
    B5.iso_of_realizes hπ (hreal i) (hreal j)
  have hcardI : ∀ i, Nat.card ↥(I i) = 2 ^ 3 := by
    intro i
    obtain ⟨e, -⟩ := B5.exists_linModel (hreal i)
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod]
    simp
  have hcardU : Nat.card ↥(commV L) = 2 ^ 12 := by
    rw [← hsup', Vol2.Ch10.SecA.Six.card_iSup_eq_prod I hind']
    simp [hcardI]
  have hrkI : rk ↥(I 0) = 3 := by
    have h := card_eq_two_pow hexp (I 0)
    rw [hcardI] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hrkU : rk ↥(commV L) = 12 := by
    have h := card_eq_two_pow hexp (commV L)
    rw [hcardU] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hY : IsotypicOfLength ↥L (commV L) (I 0) 4 := by
    refine ⟨fun a u hu => B15P4.map_commV_mem (Subgroup.le_normalizer a.2) u hu, ?_, ?_⟩
    · rw [← hsup']
      exact iSup_le fun i => le_isoComp (hirr i) (hiso i 0)
    · rw [hrkU, hrkI]
  have hE : Nat.card (Module.End ↥(XMod.opRing ↥L W) ↥(XMod.toSubmod (hirr 0).1)) = 2 := by
    have hR' := realizesVia_actAut (hirr 0).1 (hreal 0) (MonoidHom.id ↥L)
      Function.surjective_id (MonoidHom.id ↥(I 0)) Function.surjective_id
      (fun u => by
        rw [Subgroup.mem_bot]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
      (fun h u hu => rfl)
    have h1 := SmithD310U.card_eqv_le hR'
    rw [Nat.card_zmod] at h1
    have h2 := card_end_le (hirr 0).1
    have := (XMod.isIrr_iff (hirr 0).1).1 (hirr 0)
    have hfin : Finite (Module.End ↥(XMod.opRing ↥L W) ↥(XMod.toSubmod (hirr 0).1)) :=
      Finite.of_injective (fun g => (g : ↥(XMod.toSubmod (hirr 0).1) →
        ↥(XMod.toSubmod (hirr 0).1))) DFunLike.coe_injective
    have : Nontrivial ↥(XMod.toSubmod (hirr 0).1) :=
      IsSimpleModule.nontrivial ↥(XMod.opRing ↥L W) _
    have h3 : 1 < Nat.card (Module.End ↥(XMod.opRing ↥L W) ↥(XMod.toSubmod (hirr 0).1)) :=
      Finite.one_lt_card
    omega
  exact ⟨I 0, hirr 0, hY, hcardU, hE⟩

theorem prime_cases_of_moves {L : Subgroup (MulAut W)} (hexp : ∀ w : W, w ^ 2 = 1)
    (h2 : D321Two L) {x : MulAut W} (hxL : ∀ l ∈ L, l * x = x * l) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hxp : ∀ u ∈ commV L, (x ^ p) u = u) (hmove : ∃ u ∈ commV L, x u ≠ u) :
    p = 3 ∨ p = 7 ∨ (p = 5 ∧ ∀ u ∈ commV L, x u = u → u = 1) := by
  obtain ⟨I, hI, hY, -, hE⟩ := exists_isotypic_of_d321Two hexp h2
  have hyY : ∀ q ∈ commV L, x • q ∈ commV L := fun q hq =>
    B15P4.map_commV_mem (mem_normalizer_of_comm hxL) q hq
  set F := commV L ⊓ XMod.fixed ↥(Subgroup.zpowers x) ⊤ with hFdef
  have hFinv : XMod.IsInv ↥L F := by
    rintro ⟨l, hl⟩ q ⟨hqY, hqF⟩
    refine ⟨hY.1 ⟨l, hl⟩ q hqY, (mem_fixed_zpowers_iff (b := x)).2 ?_⟩
    have h1 := (mem_fixed_zpowers_iff (b := x)).1 hqF
    show x • (l • q) = l • q
    rw [smul_smul, ← hxL l hl, mul_smul, h1]
  obtain ⟨c', hc'⟩ := IsotypicOfLength.exists_of_le hexp hI hY hFinv inf_le_left
  have hlt : c' < 4 := by
    obtain ⟨u, hu, hxu⟩ := hmove
    have hFY : F < commV L := lt_of_le_of_ne inf_le_left fun h => by
      have huF : u ∈ F := h ▸ hu
      exact hxu ((mem_fixed_zpowers_iff (b := x)).1 huF.2)
    have h1 := Subgroup.card_lt_of_lt hFY
    rw [card_eq_two_pow hexp F, card_eq_two_pow hexp (commV L)] at h1
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h1
    rw [hc'.2.2, hY.2.2] at h2
    exact Nat.lt_of_mul_lt_mul_right h2
  have : Fact p.Prime := ⟨hp⟩
  have hmod := card_end_pow_modEq hexp hI hY hxL hyY hxp hc'
  rw [hE] at hmod
  rcases prime_of_two_pow_modEq hp hp2 le_rfl hlt hmod with h | h | ⟨h5, -, hc0⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h5, fun u hu hxu => ?_⟩)
    have hF0 : F = ⊥ := by
      rw [← rk_eq_zero_iff hexp, hc'.2.2, hc0, zero_mul]
    have huF : u ∈ F := ⟨hu, (mem_fixed_zpowers_iff (b := x)).2 hxu⟩
    rw [hF0] at huF
    exact Subgroup.mem_bot.1 huF

theorem fix_or_free {L : Subgroup (MulAut W)} (hexp : ∀ w : W, w ^ 2 = 1) (h2 : D321Two L)
    {s : MulAut W} (hsL : ∀ l ∈ L, l * s = s * l) {k : ℕ} (hsk : s ^ (5 ^ k) = 1) :
    (∀ u ∈ commV L, s u = u) ∨ ∀ u ∈ commV L, s u = u → u = 1 := by
  classical
  by_cases htriv : ∀ u ∈ commV L, s u = u
  · exact Or.inl htriv
  right
  have hex : ∃ m, ∀ u ∈ commV L, (s ^ (5 ^ m)) u = u := ⟨k, fun u _ => by rw [hsk]; rfl⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    have h1 := Nat.find_spec hex
    rw [h] at h1
    exact htriv (by simpa using h1)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  have hymove : ∃ u ∈ commV L, (s ^ (5 ^ j)) u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hex (by omega : j < Nat.find hex) hcon
  have hy5 : ∀ u ∈ commV L, ((s ^ (5 ^ j)) ^ 5) u = u := by
    intro u hu
    rw [← pow_mul, ← pow_succ, ← hj]
    exact Nat.find_spec hex u hu
  have hyL : ∀ l ∈ L, l * s ^ (5 ^ j) = s ^ (5 ^ j) * l := fun l hl =>
    (Commute.pow_right (hsL l hl) _).eq
  rcases prime_cases_of_moves hexp h2 hyL Nat.prime_five (by norm_num) hy5 hymove with
    h | h | ⟨-, hfree⟩
  · norm_num at h
  · norm_num at h
  · exact fun u hu hsu => hfree u hu (pow_apply_eq_self hsu _)

end CFSG.Quasithin.RonanD321.Five
