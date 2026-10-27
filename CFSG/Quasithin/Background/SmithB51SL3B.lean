module

public import CFSG.Quasithin.Background.SmithB51SL3Coord
public import CFSG.Quasithin.Background.B5NonId
public import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

theorem charP_two_of_card_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have hfin : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  have h2 : ringChar K = 2 := by
    have hdvd : ringChar K ∣ 2 ^ n := by
      rw [← hK, Nat.card_eq_fintype_card, hm]
      exact dvd_pow_self _ (PNat.ne_zero m)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  have := ringChar.charP K
  rwa [h2] at this

section NatSec

variable {V : Type} [CommGroup V]

structure NatSec (L : Subgroup (MulAut V)) (W U : Subgroup V) (K : Type) [Field K] : Type where
  π : ↥(StatedSL 3 K) →* ↥L
  hπ : Function.Bijective π
  f : ↥W →* Multiplicative (Fin 3 → K)
  hfs : Function.Surjective f
  hfk : ∀ w : ↥W, f w = 1 ↔ (w : V) ∈ U
  hfe : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) w ∈ W),
    f ⟨_, hw⟩ = natAct (StatedSL 3 K) γ (f w)

variable {L : Subgroup (MulAut V)} {W U : Subgroup V} {K : Type} [Field K]

@[expose] def NatSec.pre (c : NatSec L W U K) (B : Subgroup (MulAut V)) :
    Subgroup ↥(StatedSL 3 K) :=
  (B.subgroupOf L).comap c.π

theorem NatSec.card_pre (c : NatSec L W U K) {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    Nat.card (c.pre B) = Nat.card B := by
  have h1 : (c.pre B).map c.π = B.subgroupOf L := Subgroup.map_comap_eq_self_of_surjective c.hπ.2 _
  have h2 := Subgroup.card_map_of_injective (f := c.π) (K := c.pre B) c.hπ.1
  rw [h1] at h2
  rw [← h2]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv

theorem exists_natSec (hUW : U ≤ W) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U)
    (hfaith : L ⊓ centSec W U = ⊥) (h : ∃ n, BinaryNaturalSL (autSec L W U) ⊤ ⊥ 3 n) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (NatSec L W U K) := by
  obtain ⟨n, K, hKf, hKfin, hK, π', hπ'⟩ := h
  have hR := realizesVia_of_autSec hUW hLW hLU hfaith hπ'
  set π := (secEquiv L hLW hLU hfaith).symm.toMonoidHom.comp π' with hπdef
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hR
  exact ⟨n, K, hKf, hKfin, hK,
    ⟨⟨π, ⟨realizesVia_injective (FFModel.nat_faithful _) hR, hR.1⟩, f, hfs, hfk, hfe⟩⟩⟩

variable [Finite V]

theorem NatSec.axis [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (c : NatSec L W U K)
    (hUW : U ≤ W) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) {A : Subgroup (MulAut V)}
    (hAL : A ≤ L) (hAel : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hr : 2 * rkIdx (fixV (autSec A W U)) = rk A) :
    Module.finrank K (fixK (c.pre A)) = 2 ∧ c.pre A = axisSub (fixK (c.pre A)) ∧
      Nat.card A = Nat.card K ^ 2 := by
  have : CharP K 2 := charP_two_of_card_eq hK
  have hsq : ∀ g ∈ c.pre A, g * g = 1 := by
    intro g hg
    apply c.hπ.1
    rw [map_mul, map_one]
    apply Subtype.ext
    have := hAel.2 _ hg
    rw [sq] at this
    simpa using this
  have hcomm : ∀ g ∈ c.pre A, ∀ h ∈ c.pre A, g * h = h * g := by
    intro g hg h hh
    apply c.hπ.1
    rw [map_mul, map_mul]
    apply Subtype.ext
    simpa using hAel.1 _ hg _ hh
  have hcp := c.card_pre hAL
  obtain ⟨d, hdd⟩ : ∃ d, Module.finrank K (fixK (c.pre A)) = d := ⟨_, rfl⟩
  have hd : rkIdx (fixV (autSec A W U)) = n * (3 - d) := by
    rw [← hdd]
    exact rkIdx_fixV_autSec_nat hK c.hπ.2 c.f c.hfs c.hfk c.hfe hLW hLU hUW hAL
  have hpne : c.pre A ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [← Subgroup.card_eq_one, ← hcp, hbot, Subgroup.card_bot]
  have hd2 : d ≤ 2 := by
    have hne := fixK_ne_top hpne
    by_contra hlt
    push Not at hlt
    apply hne
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (fixK (c.pre A))
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  have hle := card_le_sq hsq hcomm
  rw [hcp, B1.card_elemAbelian hAel, hK, ← pow_mul] at hle
  have hrkA : rk A ≤ n * 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
      rw [hK, h0] at this
      norm_num at this
    · exact h0
  rw [hd] at hr
  have hd' : d = 2 := by
    by_contra hne
    have h3 : 2 ≤ 3 - d := by omega
    have : n * 2 < 2 * (n * (3 - d)) := by nlinarith
    omega
  have hrk : rk A = n * 2 := by
    rw [hd'] at hr
    omega
  have hcardA : Nat.card A = Nat.card K ^ 2 := by
    rw [B1.card_elemAbelian hAel, hrk, hK, ← pow_mul]
  refine ⟨hdd.trans hd', eq_axisSub_fixK hsq (hdd.trans hd') (by rw [hcp, hcardA]), hcardA⟩

end NatSec

section Transport

variable {K K' : Type} [Field K] [Field K']

@[expose] noncomputable def slMapEquiv (e : K ≃+* K') : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K') :=
  ((specialLinearGroupEquivStatedSL 3 K).symm.trans
    { toFun := Matrix.SpecialLinearGroup.map e.toRingHom
      invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
      left_inv := fun g => by
        apply Subtype.ext
        ext i j
        change e.symm (e ((g : Matrix (Fin 3) (Fin 3) K) i j)) = _
        simp
      right_inv := fun g => by
        apply Subtype.ext
        ext i j
        change e (e.symm ((g : Matrix (Fin 3) (Fin 3) K') i j)) = _
        simp
      map_mul' := map_mul _ }).trans (specialLinearGroupEquivStatedSL 3 K')

theorem coe_slMapEquiv (e : K ≃+* K') (g : ↥(StatedSL 3 K)) :
    (((slMapEquiv e g : ↥(StatedSL 3 K')) : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map e := by
  obtain ⟨g', rfl⟩ := (specialLinearGroupEquivStatedSL 3 K).surjective g
  simp only [slMapEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    specialLinearGroupEquivStatedSL_coe]
  rfl

@[expose] noncomputable def vecMapEquiv (e : K ≃+* K') :
    Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K') where
  toFun x := Multiplicative.ofAdd (fun i => e (Multiplicative.toAdd x i))
  invFun y := Multiplicative.ofAdd (fun i => e.symm (Multiplicative.toAdd y i))
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp

theorem vecMapEquiv_natAct (e : K ≃+* K') (g : ↥(StatedSL 3 K))
    (x : Multiplicative (Fin 3 → K)) :
    vecMapEquiv e (natAct (StatedSL 3 K) g x) =
      natAct (StatedSL 3 K') (slMapEquiv e g) (vecMapEquiv e x) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [vecMapEquiv, natAct, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd,
    coe_slMapEquiv]
  exact RingHom.map_mulVec e.toRingHom _ _ i

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W U : Subgroup V}

@[expose] noncomputable def NatSec.transport (c : NatSec L W U K) (e : K ≃+* K') :
    NatSec L W U K' where
  π := c.π.comp (slMapEquiv e).symm.toMonoidHom
  hπ := c.hπ.comp (slMapEquiv e).symm.bijective
  f := (vecMapEquiv e).toMonoidHom.comp c.f
  hfs := (vecMapEquiv e).surjective.comp c.hfs
  hfk w := by
    rw [← c.hfk w]
    show vecMapEquiv e (c.f w) = 1 ↔ c.f w = 1
    exact MulEquiv.map_eq_one_iff _
  hfe γ w hw := by
    have hw' : ((c.π ((slMapEquiv e).symm γ) : ↥L) : MulAut V) w ∈ W := hw
    show vecMapEquiv e (c.f ⟨_, hw'⟩) = _
    rw [c.hfe ((slMapEquiv e).symm γ) w hw', vecMapEquiv_natAct, MulEquiv.apply_symm_apply]
    rfl

end Transport

end B5

end CFSG.Quasithin
