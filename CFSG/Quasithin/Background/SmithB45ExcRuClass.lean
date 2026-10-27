module

public import Certificates.Certificate260392
public import CFSG.Quasithin.Background.SmithB45ExcHSRuLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuMain

public section

namespace CFSG.Quasithin.B45Exc.Ru

open CFSG.Quasithin.B45Exc CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.B45Exc.HSRu
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier CFSG.Blueprint

theorem ru_b29_check : ruB29Check = true :=
  Certificates.certificate260392

theorem card_fixFinset_eq {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (fixFinset g).card = (fixSet g).ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp [fixFinset, fixSet]

theorem ru_inv_class
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruP) (h2 : x * x = 1) (h1 : x ≠ 1) :
    ((∃ g ∈ ruP, x = g * ruZ * g⁻¹) ∧ (fixFinset x).card = 92) ∨
      ((∃ g ∈ ruP, x = g * ruA0 * g⁻¹) ∧ (fixFinset x).card = 0) := by
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  have hx' : x ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hx, hord⟩
  rw [ruInvolutions_eq] at hx'
  rcases hx' with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact Or.inl ⟨⟨g, hg, rfl⟩, by rw [card_fixFinset_eq]; exact conj_ruZ_ncard⟩
  · exact Or.inr ⟨⟨g, hg, rfl⟩, by rw [card_fixFinset_eq]; exact conj_ruA0_ncard⟩

theorem two_pow_le_index_of_pow_29 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {y : MulAut W} (h29 : y ^ 29 = 1) (h1 : y ≠ 1) :
    2 ^ 28 ≤ (fixV (Subgroup.zpowers y)).index := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have h := two_pow_orderOf_le_index_fixV hW (p := 29) (by norm_num) (orderOf_eq_prime h29 h1)
  rwa [orderOf_two_zmod_29] at h

theorem ru_order29 :
    ∃ g ∈ ruP, (ruA0 * (g * ruA0 * g⁻¹)) ^ 29 = 1 ∧ ruA0 * (g * ruA0 * g⁻¹) ≠ 1 := by
  have hreg : RegIn 4060 ruP ruGens := regIn_ruP
  obtain ⟨g, hg, hgr⟩ := hreg.word ruB29W
  have hy : PRep 4060 (pMul 4060 ruA0P (pConj 4060 (pWord 4060 ruGens ruB29W) ruA0P))
      (ruA0 * (g * ruA0 * g⁻¹)) :=
    pRep_ruA0P.mul ((hgr.mul pRep_ruA0P).mul hgr.inv)
  exact ⟨g, hg, orderCheck_spec hy ru_b29_check⟩

section Disp

variable {W : Type} [CommGroup W] [Finite W]

theorem ru_disp_2B
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (ψ : Lift L E ruP ruP)
    (b : ↥(L ⊔ E)) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hb : ((ψ.hom b : ↥ruP) : Equiv.Perm (Fin 4060)) = g * ruA0 * g⁻¹) :
    2 ^ 14 ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := by
  obtain ⟨G₀, hG₀, h29, h1⟩ := ru_order29
  have hy₀ : ruA0 * (G₀ * ruA0 * G₀⁻¹) ∈ ruP :=
    ruP.mul_mem ruA0_mem (ruP.mul_mem (ruP.mul_mem hG₀ ruA0_mem) (ruP.inv_mem hG₀))
  obtain ⟨z, -, hzle, hzn⟩ := ψ.exists_mem_dihedral b hg hG₀ hb hy₀
  have hz1 : z ≠ 1 := fun h => h1 (by simpa using (hzn 1).1 (by rw [pow_one, h]))
  have h := (two_pow_le_index_of_pow_29 hW ((hzn 29).2 h29) hz1).trans hzle
  rw [show (2 : ℕ) ^ 28 = (2 ^ 14) ^ 2 by norm_num] at h
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h

theorem ru_disp_all
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hEel : IsElemAbelian2 E) (e : CQ L ≃* NativeSporadic.Carrier .Ru)
    (hcent : Subgroup.center ↥L = ⊥) {b : MulAut W} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    2 ^ 9 < (fixV (Subgroup.zpowers b)).index := by
  have hb2 : b ^ 2 = 1 := hEel.2 b hbE
  have hE' : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.zpowers_le]
    exact hE hbE
  have hEel' : IsElemAbelian2 (Subgroup.zpowers b) := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      simp only [← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := hx
      show (b ^ i) ^ 2 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb2, one_zpow]
  have : Nontrivial (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.fam_ru_simplicity.2.1
  have hL : L ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : NativeSporadic.Carrier .Ru)
    obtain ⟨l, rfl⟩ := redHom_surjective L e s
    apply hs
    have hall : ∀ x ∈ L, x = 1 := fun x hx => by
      rw [h] at hx
      exact Subgroup.mem_bot.1 hx
    have : l = 1 := Subtype.ext (hall l l.2)
    rw [this, map_one]
  have hact := actS_injective_of_center hW hperf hirr hE' hEel' e hcent
  set b' : ↥(L ⊔ Subgroup.zpowers b) := ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩
    with hb'
  have hψ1 : actS hE' e b' ≠ 1 := fun h => hb1 (by
    have := congrArg Subtype.val (hact (h.trans (map_one _).symm))
    simpa [hb'] using this)
  have hψ2 : actS hE' e b' * actS hE' e b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext (by simpa [sq] using hb2)
    rw [this, map_one]
  obtain ⟨cs, hlen, hcsin, hcsgen⟩ := ru_gen _ hψ2 hψ1
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE' e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE' e s
  have hgen : ∀ s : NativeSporadic.Carrier .Ru, MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (NativeSporadic.Carrier .Ru) | ∃ c ∈ cs, ∃ x : ↥(L ⊔ Subgroup.zpowers b),
        (x : MulAut W) ∈ Subgroup.zpowers b ∧ y = c * actS hE' e x * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, t, ht, rfl⟩
    have : t = actS hE' e b' := by simpa using ht
    subst this
    exact ⟨c, hc, b', Subgroup.mem_zpowers b, rfl⟩
  have hbound := card_le_index_pow_of_inn_le hW hperf hirr hL hE' hEel' e cs hcsr hgen
  rw [hlen] at hbound
  let eqv := redEquiv e hcent
  let σ : NativeSporadic.Carrier .Ru →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσ : Function.Injective σ := fun a b hab => eqv.symm.injective (Subtype.ext hab)
  have hdim := ru_dim W hW σ hσ
  by_contra hlt
  push Not at hlt
  have h1 : (fixV (Subgroup.zpowers b)).index ^ 3 ≤ 512 ^ 3 := Nat.pow_le_pow_left (by omega) 3
  omega

end Disp

end CFSG.Quasithin.B45Exc.Ru
