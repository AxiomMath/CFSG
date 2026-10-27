module

public import CFSG.Quasithin.Background.SmithB45ExcHSClass
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSMain

public section

namespace CFSG.Quasithin.B45Exc.HS

open CFSG.Quasithin.B45Exc CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.B45Exc.HSRu
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Bridge.HSExcl
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem card_hsCarrier :
    Nat.card (NativeSporadic.Carrier .HS) = 44352000 := by
  rw [Nat.card_congr hsEquivC.toEquiv, card_hsP]

theorem hs_two_pow_sixteen
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (eqv : ↥L ≃* NativeSporadic.Carrier .HS) {z : MulAut W} (hz : z ∈ L) (h5 : z ^ 5 = 1)
    (h1 : z ≠ 1) : 2 ^ 16 ≤ (fixV (Subgroup.zpowers z)).index := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (NativeSporadic.Carrier .HS) := Finite.of_equiv _ eqv.toEquiv
  obtain ⟨x, y, -, hx, hy, hz', hzx, hzy, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  let σ : NativeSporadic.Carrier .HS →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσ : Function.Injective σ := fun a b hab => eqv.symm.injective (Subtype.ext hab)
  have hG : ¬ 5 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .HS) := by
    rw [card_hsCarrier]
    norm_num
  set g := eqv ⟨z, hz⟩ with hg
  have hσg : σ g = z := by simp [σ, hg]
  have hg5 : g ^ 5 = 1 := by
    rw [hg, ← map_pow]
    have : (⟨z, hz⟩ : ↥L) ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [this, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply h1
    rw [← hσg, h, map_one]
  have h := two_pow_le_index_of_pow_eq_one (G := NativeSporadic.Carrier .HS) (p := 5)
    (by norm_num) (x := x) (y := y) hx hy hz' hzx hzy hG hW σ hσ hg5 hg1
  rwa [hσg, orderOf_two_zmod_5] at h

omit [Finite W] in
theorem le_of_two_pow_le_sq {a k : ℕ} (h : 2 ^ (2 * k) ≤ a ^ 2) : 2 ^ k ≤ a := by
  by_contra hlt
  push Not at hlt
  have : a ^ 2 < (2 ^ k) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  rw [← pow_mul, mul_comm] at this
  omega

section Classes


theorem hs_disp_2A (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (ψ : Lift L E hsR hsP) (eqv : ↥L ≃* NativeSporadic.Carrier .HS) (b : ↥(L ⊔ E))
    {g : Equiv.Perm (Fin 3850)} (hg : g ∈ hsP)
    (hb : ((ψ.hom b : ↥hsR) : Equiv.Perm (Fin 3850)) = g * hsT 5 * g⁻¹) :
    2 ^ 8 ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := by
  obtain ⟨G₀, hG₀, h5, h1⟩ := hs_order5
  have hy₀ : hsT 5 * (G₀ * hsT 5 * G₀⁻¹) ∈ hsP :=
    hsP.mul_mem hsT_mem_P.1 (hsP.mul_mem (hsP.mul_mem hG₀ hsT_mem_P.1) (hsP.inv_mem hG₀))
  obtain ⟨z, hzL, hzle, hzn⟩ := ψ.exists_mem_dihedral b hg hG₀ hb hy₀
  have hz5 : z ^ 5 = 1 := (hzn 5).2 h5
  have hz1 : z ≠ 1 := fun h => h1 (by simpa using (hzn 1).1 (by rw [pow_one, h]))
  have h16 := hs_two_pow_sixteen hW eqv hzL hz5 hz1
  exact le_of_two_pow_le_sq (k := 8) (h16.trans hzle)

theorem hs_disp_2BD (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (ψ : Lift L E hsR hsP) (b : ↥(L ⊔ E)) {g : Equiv.Perm (Fin 3850)} (hg : g ∈ hsP) {k : ℕ}
    (hk : k = 12 ∨ k = 34)
    (hb : ((ψ.hom b : ↥hsR) : Equiv.Perm (Fin 3850)) = g * hsT k * g⁻¹) :
    2 ^ 10 ≤ (fixV (Subgroup.zpowers (b : MulAut W))).index := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨G₁, hG₁, X, hX, Y, hY, hZ, hX5, hzx, hzy, hz1⟩ :
      ∃ g ∈ hsP, ∃ x ∈ hsP, ∃ y ∈ hsP, hsT k * (g * hsT k * g⁻¹) = ⁅x, y⁆ ∧ x ^ 5 = 1 ∧
        Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 := by
    rcases hk with rfl | rfl
    · exact hs_cfg1
    · exact hs_cfg3
  have h := ψ.two_pow_le_sq_of_cfg hW (p := 5) (by norm_num) b hg hG₁ hX hY hb hZ hX5 hzx hzy hz1
  rw [orderOf_two_zmod_5] at h
  exact le_of_two_pow_le_sq (k := 10) h

end Classes

theorem hs_disp_all
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hEel : IsElemAbelian2 E) (e : CQ L ≃* NativeSporadic.Carrier .HS)
    (hcent : Subgroup.center ↥L = ⊥) {b : MulAut W} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    2 ^ 5 ≤ (fixV (Subgroup.zpowers b)).index := by
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
  have : Nontrivial (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.1
  have hL : L ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : NativeSporadic.Carrier .HS)
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
  obtain ⟨cs, hlen, hcsin, hcsgen⟩ := hs_gen4 _ hψ2 hψ1
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE' e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE' e s
  have hgen : ∀ s : NativeSporadic.Carrier .HS, MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (NativeSporadic.Carrier .HS) | ∃ c ∈ cs, ∃ x : ↥(L ⊔ Subgroup.zpowers b),
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
  let σ : NativeSporadic.Carrier .HS →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσ : Function.Injective σ := fun a b hab => eqv.symm.injective (Subtype.ext hab)
  have hdim := hs_dim W hW σ hσ
  by_contra hlt
  push Not at hlt
  have h1 : (fixV (Subgroup.zpowers b)).index ^ 4 ≤ 31 ^ 4 := Nat.pow_le_pow_left (by omega) 4
  omega

end CFSG.Quasithin.B45Exc.HS
