module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Main
public import CFSG.Quasithin.Background.SmithB45Exc3A7Nine
public import CFSG.Quasithin.EmptyFaithful.SzN28PSvGrp
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Bridge.ThreeA7Excl Equiv Equiv.Perm

namespace Case34A7

theorem card_elem_le_eight {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    (e : CQ L ≃* alternatingGroup (Fin 7)) : Nat.card E ≤ 8 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  let φ : ↥(L ⊔ E) →* MulAut (alternatingGroup (Fin 7)) := actS hEn e
  let ι : ↥E →* ↥(L ⊔ E) := Subgroup.inclusion le_sup_right
  let ε : ↥E →* Perm (Fin 7) := cEquiv.symm.toMonoidHom.comp (φ.comp ι)
  have hcε : ∀ b : ↥E, cEquiv (ε b) = φ (ι b) := fun b => cEquiv.apply_symm_apply _
  have hεinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : φ (ι b) = 1 := by rw [← hcε, hb, map_one]
    obtain ⟨h3, h4⟩ := mem_center_of_actS_eq_one hW hperf hirr hEn hEel e h1
    have hcomm : ∀ l ∈ L, l * (b : MulAut W) = (b : MulAut W) * l := fun l hl => by
      have := Subgroup.mem_center_iff.1 h4 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hodd := odd_orderOf_of_commutes hW hirr hcomm
    have hb2 : (b : MulAut W) ^ 2 = 1 := hEel.2 b b.2
    have hdvd : orderOf (b : MulAut W) ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
    have h1' : orderOf (b : MulAut W) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.1 h1')
  set B : Subgroup (Perm (Fin 7)) := ε.range with hB
  have hBcard : Nat.card B = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv).symm
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  have hB2 : ∀ a ∈ B, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
    rw [this, map_one]
  have := CFSG.Quasithin.SzN28P.s7_card_le_eight (MulEquiv.refl (Perm (Fin 7))) (X := B) hB2 hBc
  rwa [hBcard] at this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem m_le_three {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) : m ≤ 3 := by
  obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have e' := cqEquiv_toMulSub_comp e
  have h8 := card_elem_le_eight mul_self_eq_one_multiplicative hq.1 hirr hAN hAel e'
  rw [hAcard] at h8
  have : 2 ^ m ≤ 2 ^ 3 := by simpa using h8
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem card_facts_threeA7 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* alternatingGroup (Fin 7)) (hZ : Subgroup.center ↥L ≠ ⊥) :
    2 ^ 6 < Nat.card W ∧ Nat.card W % 9 = 1 := by
  classical
  have hperf : Group.IsPerfect ↥L := hq.1
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := by
    have hcov := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 7) (by norm_num)
      (by norm_num) (redHom L e) (redHom_surjective L e) (by rw [hker])
      (by rw [hker]; exact hZodd)).2 (Or.inr rfl)
    rw [hker] at hcov
    rcases hcov with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hZ
    · exact h
  have hL7560 : Nat.card ↥L = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L),
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin, hZ3]
    decide
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ3]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set zL : ↥L := (zc : ↥L) with hzL
  have hzW : orderOf (zL : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hz3 : (zL : MulAut W) ^ 3 = 1 := by
    rw [← hzW]
    exact pow_orderOf_eq_one _
  have hz1 : (zL : MulAut W) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzW
    omega
  have hcen : Subgroup.center ↥L = Subgroup.zpowers zL := by
    have hle : Subgroup.zpowers zL ≤ Subgroup.center ↥L := Subgroup.zpowers_le.2 zc.2
    have hord : orderOf zL = 3 := by
      rw [hzL, Subgroup.orderOf_coe, hzc]
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZ3, Nat.card_zpowers, hord]
  have hzcomm : ∀ l : ↥L, (l : MulAut W) * (zL : MulAut W) = (zL : MulAut W) * l := by
    intro l
    have := Subgroup.mem_center_iff.1 zc.2 l
    exact congrArg Subtype.val this
  have hzf : ∀ w : W, (zL : MulAut W) w = w → w = 1 := by
    have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers (zL : MulAut W)),
        g u ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := by
      intro g hg u hu
      rw [mem_fixV_zpowers] at hu ⊢
      have := congrArg (fun m : MulAut W => m u) (hzcomm ⟨g, hg⟩)
      simp only [MulAut.mul_apply] at this
      rw [← this, hu]
    rcases hirr.2 _ hinv with h | h
    · intro w hw
      have hmem : w ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := mem_fixV_zpowers.2 hw
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hz1
      ext w
      have hmem : w ∈ fixV (Subgroup.zpowers (zL : MulAut W)) := by rw [h]; trivial
      exact mem_fixV_zpowers.1 hmem
  have hker1 : ∀ g : ↥L, redHom L e g = 1 → g ∈ Subgroup.center ↥L := fun g hg =>
    (redHom_eq_one_iff L e g).1 hg
  have hZ3' : ∀ g ∈ Subgroup.center ↥L, g ^ 3 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨g, hg⟩)
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x, y, hx5, hx1, hyx⟩ :=
    exists_fusion_pair_alt7 (redHom L e) (redHom_surjective L e) hker1 hZ3'
  have hx5' : (x : MulAut W) ^ 5 = 1 := by simpa using congrArg Subtype.val hx5
  have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hyx' : (y : MulAut W) * (x : MulAut W) * (y : MulAut W)⁻¹ = (x : MulAut W) ^ 2 := by
    simpa using congrArg Subtype.val hyx
  have hbig := card_gt_of_fusion hW hx5' hx1' hyx' (hzcomm x).symm (hzcomm y).symm hz3 hzf
  have h27 : (Nat.card ↥L).factorization 3 = 3 := by
    rw [hL7560, show (7560 : ℕ) = 3 ^ 3 * 280 from rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact ⟨hbig, CFSG.Quasithin.B45Exc3A7.card_mod_nine_of hperf h27 hcen hz3 hz1 hzf⟩

theorem center_eq_bot {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) :
    Subgroup.center ↥L = ⊥ := by
  by_contra hZ
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have hirr := isIrrOn_toMulSub h.H_irr
  have e' := cqEquiv_toMulSub_comp e
  have hZ' : Subgroup.center ↥(toMulSub L) ≠ ⊥ := by
    intro hb
    apply hZ
    have := map_center_toMulSubEquiv L
    rw [hb] at this
    rw [eq_bot_iff]
    intro x hx
    have hx' : (toMulSubEquiv L : ↥L →* ↥(toMulSub L)) x ∈
        (Subgroup.center ↥L).map (toMulSubEquiv L : ↥L →* ↥(toMulSub L)) := ⟨x, hx, rfl⟩
    rw [this, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact (toMulSubEquiv L).injective (hx'.trans (map_one _).symm)
  obtain ⟨h1, h2⟩ := card_facts_threeA7 mul_self_eq_one_multiplicative hq hirr e' hZ'
  rw [natCard_multiplicative] at h1 h2
  have hm := m_le_three h e
  have hb := h.bound
  have hd : Module.finrank (ZMod 2) V ≤ 8 := by omega
  have h6 : 6 < Module.finrank (ZMod 2) V := by
    by_contra hc
    push Not at hc
    have : 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hc
    omega
  interval_cases hdd : Module.finrank (ZMod 2) V <;> simp at h2

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
