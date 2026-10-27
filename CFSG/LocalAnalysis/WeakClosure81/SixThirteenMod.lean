module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.Quasithin.Background.SimsE2DihMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_quotient_imgTil {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀U : V₀ ≤ U) :
    Nat.card (Vtil V₀ V hV ⧸ imgTil V₀ V hV U) = U.relIndex V := by
  rw [← Subgroup.index_eq_card,
    ← Subgroup.index_comap_of_surjective (imgTil V₀ V hV U) (mkTil_surjective V₀ V hV)]
  have h : (imgTil V₀ V hV U).comap (mkTil V₀ V hV) = intSub V hV U := by
    unfold imgTil
    rw [Subgroup.comap_map_eq]
    have hker : (mkTil V₀ V hV).ker = modNull V₀ V hV := QuotientGroup.ker_mk' _
    rw [hker]
    exact sup_eq_left.2 fun x hx => hV₀U hx
  rw [h]
  rfl

section Quotient

open CFSG.Quasithin.SimsE2

private theorem two_pow_dParam_le_card_of_ne_one {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : ∀ q : Q, q * q = 1) {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {γ : MulAut Q}
    (hγ : orderOf γ = p ^ a) (hγ1 : γ ≠ 1) : 2 ^ dParam p ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ∀ x y : Q, x * y = y * x := mul_comm
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hγ
      exact hγ1 (orderOf_eq_one_iff.1 hγ)
    · exact h0
  set γ₀ := γ ^ p ^ (a - 1) with hγ₀
  set U := (Dih.commHom hc γ₀).range with hUdef
  have hγ₀p : γ₀ ^ p = 1 := by
    rw [hγ₀, ← pow_mul, ← pow_succ, Nat.sub_add_cancel ha, ← hγ, pow_orderOf_eq_one]
  have hγ₀1 : γ₀ ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero) ?_
    rw [hγ]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hU1 : U ≠ ⊥ := by
    intro hU
    apply hγ₀1
    ext x
    have hx : Dih.commHom hc γ₀ x ∈ U := MonoidHom.mem_range.2 ⟨x, rfl⟩
    rw [hU, Subgroup.mem_bot, Dih.commHom_apply, inv_mul_eq_one] at hx
    rw [MulAut.one_apply]
    exact hx.symm
  have hγU : ∀ u ∈ U, γ u ∈ U := by
    intro u hu
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hu
    refine MonoidHom.mem_range.2 ⟨γ x, ?_⟩
    have hcomm : γ * γ₀ = γ₀ * γ := (Commute.self_pow γ _).eq
    rw [Dih.commHom_apply, Dih.commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ← hcomm,
      MulAut.mul_apply]
  have hfree : U ⊓ Dih.fixSub γ₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvU, hv⟩
    replace hv : γ₀ v = v := hv
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hvU
    rw [Subgroup.mem_bot]
    set v := Dih.commHom hc γ₀ x with hvdef
    have hxv : γ₀ x = x * v := by rw [hvdef, Dih.commHom_apply, mul_inv_cancel_left]
    have hpow : ∀ n : ℕ, (γ₀ ^ n) x = x * v ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hxv, hv, pow_succ',
          mul_assoc]
    have hvp : v ^ p = 1 := by
      have := hpow p
      rw [hγ₀p, MulAut.one_apply] at this
      exact (mul_eq_left.1 this.symm)
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hQ v
    rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul] at hvp
    exact hvp
  have hdvd := Dih.dvd_card_sub_one hp ha hγ hγU hfree
  have h2Q : IsPGroup 2 Q := fun x => ⟨1, by rw [pow_one, pow_two]; exact hQ x⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h2Q.to_subgroup U)
  rw [hm] at hdvd
  have hpm : p ∣ 2 ^ m - 1 := (dvd_pow_self p (by omega)).trans hdvd
  have hdm : E2.dParam p ∣ m := Dih.dParam_dvd_of_dvd hpm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hm
      exact hU1 (Subgroup.card_eq_one.1 hm)
    · exact h0
  have hle : dParam p ≤ m := Nat.le_of_dvd hm0 hdm
  calc 2 ^ dParam p ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hle
    _ = Nat.card U := hm.symm
    _ ≤ Nat.card Q := Subgroup.card_le_card_group U

private theorem map_eq_of_mem_stabSub {W : Type} [CommGroup W] (U : Subgroup W)
    (g : ↥(stabSub U)) : Subgroup.map ((g : MulAut W) : W →* W) U = U := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_stabSub.1 g.2 u).2 hu
  · intro hx
    have h1 : (g : MulAut W)⁻¹ x ∈ U := by
      refine (mem_stabSub.1 g.2 _).1 ?_
      rw [MulAut.apply_inv_self]
      exact hx
    exact ⟨_, h1, by simp⟩

private noncomputable def quotHom {W : Type} [CommGroup W] (U : Subgroup W) :
    ↥(stabSub U) →* MulAut (W ⧸ U) where
  toFun g := QuotientGroup.congr U U (g : MulAut W) (map_eq_of_mem_stabSub U g)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk]
      rfl
  map_mul' g h := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply]
      simp only [QuotientGroup.congr_mk]
      rfl

private theorem quotHom_mk {W : Type} [CommGroup W] (U : Subgroup W) (g : ↥(stabSub U)) (w : W) :
    quotHom U g (QuotientGroup.mk w) = QuotientGroup.mk ((g : MulAut W) w) :=
  QuotientGroup.congr_mk _ _ _ (map_eq_of_mem_stabSub U g) w

end Quotient

theorem commutator_le_of_card_quot_lt {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsPGroup p X) {U : Subgroup W}
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) (hcard : Nat.card (W ⧸ U) < 2 ^ dParam p) :
    ∀ x ∈ X, ∀ w : W, w⁻¹ * x w ∈ U := by
  intro x hx w
  by_contra hw
  haveI := Fact.mk hp
  have hxst : x ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    refine ⟨fun hxu => ?_, hXU x hx u⟩
    have h1 := hXU x⁻¹ (X.inv_mem hx) (x u) hxu
    rwa [MulAut.inv_apply_self] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hX) ⟨x, hx⟩
  have hk' : orderOf x = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
  set γ := quotHom U ⟨x, hxst⟩ with hγdef
  have hγord : orderOf γ ∣ p ^ k := by
    have h1 := orderOf_map_dvd (quotHom U) ⟨x, hxst⟩
    rwa [Subgroup.orderOf_mk, hk'] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hγord
  have hγ1 : γ ≠ 1 := by
    intro h
    apply hw
    have h1 := congrArg (fun φ : MulAut (W ⧸ U) => φ (QuotientGroup.mk w)) h
    simp only [hγdef, quotHom_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  have hQ : ∀ q : W ⧸ U, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, ← pow_two, hW w]
      rfl
  exact absurd (two_pow_dParam_le_card_of_ne_one hQ hp hp2 hj hγ1) (not_le.2 hcard)

theorem eq_top_of_invariant_of_conjGenerated {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hgen : ConjGenerated M V₀ V) {Y : Subgroup (Vtil V₀ V hV)}
    (hY : ∀ φ ∈ Mbar M V₀ V hV, ∀ y ∈ Y, φ y ∈ Y) (hne : Y ≠ ⊥) : Y = ⊤ := by
  obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨z, rfl⟩ := mkTil_surjective V₀ V hV y
  have hzV₀ : z.val ∉ V₀ := by
    intro h
    apply hy1
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) z).2 h
  have hV_eq := hgen z.val z.val_mem hzV₀
  have hP : V ≤ preTil V₀ V hV Y := by
    refine hV_eq.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨m, hm, rfl⟩
    have hmst : m ∈ stabTil V₀ V := le_stabTil hM hM₀ hm
    have hmV : m * z.val * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hM hm) z.val).1 z.val_mem
    rw [SetLike.mem_coe, mem_preTil_iff_of_mem V₀ V hV Y hmV]
    have h1 := actTil_mk V₀ V hV ⟨m, hmst⟩ z
    have h2 : actStab V₀ V hV ⟨m, hmst⟩ z = IntMod.mk hV ⟨m * z.val * m⁻¹, hmV⟩ :=
      IntMod.val_injective (by rw [actStab_apply_val]; rfl)
    rw [h2] at h1
    rw [← h1]
    exact hY _ (actTil_mem_barSub V₀ V hV hm hmst) _ hyY
  rw [eq_top_iff]
  intro q _
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
  have hx := hP x.val_mem
  rwa [mem_preTil_iff_of_mem V₀ V hV Y x.val_mem] at hx

theorem exists_commutator_notMem {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hgen : ConjGenerated M V₀ V) {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX1 : X ≠ ⊥)
    (hXnorm : ∀ m ∈ Mbar M V₀ V hV, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    {Y : Subgroup (Vtil V₀ V hV)} (hY : Y ≠ ⊤) :
    ∃ ξ ∈ X, ∃ w : Vtil V₀ V hV, w⁻¹ * ξ w ∉ Y := by
  by_contra hcon
  push Not at hcon
  set S : Set (Vtil V₀ V hV) := {c | ∃ ξ ∈ X, ∃ w, c = w⁻¹ * ξ w} with hS
  set C := Subgroup.closure S with hC
  have hCY : C ≤ Y :=
    (Subgroup.closure_le Y).2 (by rintro _ ⟨ξ, hξ, w, rfl⟩; exact hcon ξ hξ w)
  have hinv : ∀ φ ∈ Mbar M V₀ V hV, ∀ c ∈ C, φ c ∈ C := by
    intro φ hφ c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨ξ, hξ, w, rfl⟩ := hc
      refine Subgroup.subset_closure ⟨φ * ξ * φ⁻¹, hXnorm φ hφ ξ hξ, φ w, ?_⟩
      simp [map_mul, map_inv, MulAut.mul_apply]
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact C.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact C.inv_mem hx
  have hC1 : C = ⊥ := by
    by_contra hCne
    have htop := eq_top_of_invariant_of_conjGenerated hV hM hM₀ hgen hinv hCne
    exact hY (top_le_iff.1 (htop ▸ hCY))
  apply hX1
  rw [eq_bot_iff]
  intro ξ hξ
  rw [Subgroup.mem_bot]
  ext w
  have h1 : w⁻¹ * ξ w ∈ C := Subgroup.subset_closure ⟨ξ, hξ, w, rfl⟩
  rw [hC1, Subgroup.mem_bot, inv_mul_eq_one] at h1
  rw [MulAut.one_apply]
  exact h1.symm

end CFSG.LocalAnalysis.WeakClosure81
