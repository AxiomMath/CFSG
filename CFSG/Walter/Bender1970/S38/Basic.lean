module

public import CFSG.Walter.Bender1970.S38.Component
public import CFSG.Walter.Bender1970.S3.InvolutionClasses
public import CFSG.Walter.Bender1970.S3.Singleton
public import CFSG.Walter.Bender1970.S2.Layer
public import CFSG.Walter.Bender1970.S38.Omega

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}

theorem exists_mul_of_mem_sylow (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {s : G} (hs : s ∈ (T : Subgroup G)) :
    ∃ w ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), ∃ v ∈ (T : Subgroup G) ⊓ K,
      w * v = s := by
  obtain ⟨ℓ, hℓ, hconj⟩ := component_exists_inner hHA hK T hTH hs
  refine ⟨s * ℓ⁻¹, ⟨(T : Subgroup G).mul_mem hs ((T : Subgroup G).inv_mem hℓ.1), ?_⟩, ℓ, hℓ,
    inv_mul_cancel_right s ℓ⟩
  show s * ℓ⁻¹ ∈ Subgroup.centralizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := hconj (ℓ⁻¹ * x * ℓ) (K.mul_mem (K.mul_mem (K.inv_mem hℓ.2) hx) hℓ.2)
  have h2 : ℓ * (ℓ⁻¹ * x * ℓ) * ℓ⁻¹ = x := by group
  rw [h2] at h1
  calc x * (s * ℓ⁻¹) = s * (ℓ⁻¹ * x * ℓ) * s⁻¹ * (s * ℓ⁻¹) := by rw [h1]
    _ = s * ℓ⁻¹ * x := by group

theorem inf_inf_eq_bot {T Q : Subgroup G} (hTp : IsPGroup 2 T) (hKQ : Bender38Component K Q) :
    (T ⊓ Subgroup.centralizer (K : Set G)) ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro x ⟨⟨hxT, hxC⟩, hxQ⟩
  rw [Subgroup.mem_bot]
  have hxK : x ∈ K := hKQ.le hxQ
  have hxZ : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hTp
  have h1 := eq_one_of_mem_center_of_pow hKQ.odd_center hxZ (m := k)
    (Subtype.ext (by simpa using hk x hxT))
  exact congrArg Subtype.val h1

theorem card_sylow_eq_mul (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hKQ : Bender38Component K ((T : Subgroup G) ⊓ K)) :
    Nat.card (T : Subgroup G) = Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) :
      Subgroup G) * Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hW
  set Q := (T : Subgroup G) ⊓ K with hQ
  have hWQ := inf_inf_eq_bot T.isPGroup' hKQ
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun x : W × Q => (⟨(x.1 : G) * x.2,
    (T : Subgroup G).mul_mem x.1.2.1 x.2.2.1⟩ : (T : Subgroup G))) ⟨fun x y h => ?_,
    fun s => ?_⟩)).symm
  · have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val h
    have h2 : (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
    have h3 : (y.1 : G)⁻¹ * x.1 ∈ W ⊓ Q :=
      ⟨W.mul_mem (W.inv_mem y.1.2) x.1.2, h2 ▸ Q.mul_mem y.2.2 (Q.inv_mem x.2.2)⟩
    rw [hWQ, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : (x.2 : G) = y.2 := by rw [h3] at h1; exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
  · obtain ⟨w, hw, v, hv, hwv⟩ := exists_mul_of_mem_sylow hHA hK T hTH s.2
    exact ⟨(⟨w, hw⟩, ⟨v, hv⟩), Subtype.ext hwv⟩

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem bender38Component'
    {t : G} {Hm : Subgroup G} (hH : Hm ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {L : Subgroup G} (hL : IsComponentOf L Hm) :
    Bender38Component L ((T : Subgroup G) ⊓ L) :=
  bender38Component (hG.isAStar_of_isCoatom hH.1) hL T (hG.sylow_le_of_mem_benderM T htT hH)
    (hG.hasAbelianSylowTwo T)

theorem centralizer_inf_ne_bot
    {t : G} (ht : orderOf t = 2) (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) (hK : IsComponentOf K H) :
    (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
  intro hW
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hKQ := hG.bender38Component' hH T htT hK
  have hTK : (T : Subgroup G) ≤ K := by
    intro s hs
    obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hs
    rw [hW, Subgroup.mem_bot] at hw
    rw [hw, one_mul]
    exact hv.2
  obtain ⟨x, hxH, y, hyH, hx, hy, hne⟩ := bender1970_3_2 hG ht hH
  obtain ⟨a, haH, ha⟩ := exists_conj_mem_sylow_of_le T hTH hxH hx
  obtain ⟨b, hbH, hb⟩ := exists_conj_mem_sylow_of_le T hTH hyH hy
  have hconj : ∀ g z : G, orderOf (g⁻¹ * z * g) = orderOf z := fun g z => by
    have : g⁻¹ * z * g = MulAut.conj g⁻¹ z := by rw [MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq]
  obtain ⟨k, hkK, hk⟩ := hKQ.isConj _ (hTK ha) _ (hTK hb) ((hconj a x).trans hx)
    ((hconj b y).trans hy)
  apply hne (b * k * a⁻¹) (H.mul_mem (H.mul_mem hbH (hK.1 hkK)) (H.inv_mem haH))
  calc b * k * a⁻¹ * x * (b * k * a⁻¹)⁻¹ = b * (k * (a⁻¹ * x * a) * k⁻¹) * b⁻¹ := by group
    _ = b * (b⁻¹ * y * b) * b⁻¹ := by rw [hk]
    _ = y := by group

theorem mem_of_conj_mem_of_benderM (hHco : IsCoatom H) {W : Subgroup G}
    (hM : ∀ s ∈ W, orderOf s = 2 → benderM s = {H}) {w g : G} (hw : w ∈ W)
    (hw2 : orderOf w = 2) (hgw : g * w * g⁻¹ ∈ W) : g ∈ H := by
  have hgw2 : orderOf (g * w * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw2]
  have h1 := hM _ hgw hgw2
  have h2 := hM w hw hw2
  refine hG.mem_of_benderM_eq_singleton hHco h1 ?_
  rw [show g⁻¹ * (g * w * g⁻¹) * g = w by group]
  exact h2

theorem sq_eq_one_of_not_le
    {t : G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) (hK : IsComponentOf K H)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H})
    (hN : ¬ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H) :
    ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hKQ := hG.bender38Component' hH T htT hK
  have hTab := hG.hasAbelianSylowTwo T
  obtain ⟨y, hyN, hyH⟩ := Set.not_subset.mp hN
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxT, hx2⟩ := hcon
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hxT⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hx2 (by rw [hm, one_pow])
    · exact hx2 (by rw [← pow_one 2, ← hm, pow_orderOf_eq_one])
  set u := x ^ 2 ^ (m - 2) with hu
  set s := u ^ 2 with hs
  have hs2 : orderOf s = 2 := by
    rw [hs, hu, ← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega]
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hm ▸ pow_dvd_pow 2 (Nat.sub_le m 1)),
      hm, Nat.pow_div (Nat.sub_le m 1) two_pos, Nat.sub_sub_self (by omega), pow_one]
  have hsqW : ∀ u ∈ (T : Subgroup G),
      u ^ 2 ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
    intro u hu
    obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sylow hHA hK T hTH hu
    have hwv : Commute w v :=
      congrArg Subtype.val (hTab.is_comm.comm ⟨w, hw.1⟩ ⟨v, hv.1⟩)
    rw [hwv.mul_pow, hKQ.sq_eq_one v hv, mul_one]
    exact Subgroup.pow_mem _ hw 2
  have huT : u ∈ (T : Subgroup G) := (T : Subgroup G).pow_mem hxT _
  have hyuT : y * u * y⁻¹ ∈ (T : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hyN u).mp huT
  have hys : y * s * y⁻¹ = (y * u * y⁻¹) ^ 2 := by rw [hs, conj_pow]
  apply hyH
  refine hG.mem_of_conj_mem_of_benderM hH.1 hM (hsqW u huT) hs2 ?_
  rw [hys]
  exact hsqW _ hyuT

theorem card_centralizer_inf_le
    {t : G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) (hK : IsComponentOf K H)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H})
    (hN : ¬ Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H) :
    Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤
      Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hHA := hG.isAStar_of_isCoatom hH.1
  have hKQ := hG.bender38Component' hH T htT hK
  have hsq := hG.sq_eq_one_of_not_le hH T htT hK hM hN
  set W := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hW
  obtain ⟨y, hyN, hyH⟩ := Set.not_subset.mp hN
  have hWy : W.map (MulAut.conj y).toMonoidHom ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hz⟩
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hw1 : w ≠ 1 := by
      rintro rfl
      simp at hz1
    exact hyH (hG.mem_of_conj_mem_of_benderM hH.1 hM hw (orderOf_eq_prime (hsq w hw.1) hw1) hz)
  have hWyT : W.map (MulAut.conj y).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hyN w).mp hw.1
  have h1 := card_mul_card_le_of_inf_eq_bot hWyT inf_le_left hWy
  rw [Subgroup.card_map_of_injective (MulAut.conj y).injective,
    card_sylow_eq_mul hHA hK T hTH hKQ] at h1
  exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos

end BenderCounterexample

theorem map_conj_eq_iff_mem_normalizer {K : Subgroup G} {g : G} :
    K.map (MulAut.conj g).toMonoidHom = K ↔ g ∈ Subgroup.normalizer (K : Set G) := by
  constructor
  · intro h
    refine mem_normalizer_of_conj_mem' fun x hx => ?_
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro h
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp h x).mp hx

theorem le_normalizer_of_card_le
    (hHA : IsAStar H) (hK : IsComponentOf K H) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTab : IsMulCommutative (T : Subgroup G))
    (hW : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥)
    (hWQ : Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤
      Nat.card ((T : Subgroup G) ⊓ K : Subgroup G)) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hWdef
  have hKQ := bender38Component hHA hK T hTH hTab
  set c : G → Subgroup G := fun g => K.map (MulAut.conj g).toMonoidHom with hc
  have hcomp : ∀ g ∈ H, IsComponentOf (c g) H := fun g hg =>
    isComponentOf_map_conj hK (Subgroup.le_normalizer hg)
  have hA : ∀ g ∈ H, c g ≠ K → W ≤ c g := by
    intro g hg hne
    have hL := hcomp g hg
    have hcommKL : ⁅c g, K⁆ = ⊥ := by
      rcases isComponentOf_eq_or_commutator_eq_bot hL hK with h | h
      · exact absurd h hne
      · exact h
    have hTL : (T : Subgroup G) ⊓ c g ≤ W := by
      rintro x ⟨hxT, hxL⟩
      refine ⟨hxT, ?_⟩
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKL) hxL
    have hLQ := bender38Component hHA hL T hTH hTab
    have hcardL : Nat.card ((T : Subgroup G) ⊓ c g : Subgroup G) =
        Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
      rw [hLQ.card_eq, hKQ.card_eq, hc, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have heq : (T : Subgroup G) ⊓ c g = W :=
      Subgroup.eq_of_le_of_card_ge hTL (by rw [hcardL]; exact hWQ)
    exact heq ▸ inf_le_right
  intro h hhH
  by_contra hhN
  have hc1 : c h ≠ K := fun heq => hhN (map_conj_eq_iff_mem_normalizer.mp heq)
  have hsq : h ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
    by_contra hsqN
    have hc2 : c (h ^ 2) ≠ K := fun heq => hsqN (map_conj_eq_iff_mem_normalizer.mp heq)
    have hh2H : h ^ 2 ∈ H := H.pow_mem hhH 2
    have hc12 : c h ≠ c (h ^ 2) := by
      intro heq
      apply hhN
      rw [← map_conj_eq_iff_mem_normalizer]
      have h1 := congrArg (fun L : Subgroup G => L.map (MulAut.conj h⁻¹).toMonoidHom) heq
      simp only [hc, Subgroup.map_map] at h1
      have e1 : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
          MonoidHom.id G := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      have e2 : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj (h ^ 2)).toMonoidHom) =
          (MulAut.conj h).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e1, e2, Subgroup.map_id] at h1
      exact h1.symm
    have hW1 := hA h hhH hc1
    have hW2 := hA (h ^ 2) hh2H hc2
    have hcomm12 : ⁅c h, c (h ^ 2)⁆ = ⊥ := by
      rcases isComponentOf_eq_or_commutator_eq_bot (hcomp h hhH) (hcomp (h ^ 2) hh2H) with
        h' | h'
      · exact absurd h' hc12
      · exact h'
    apply hW
    have hLQ := bender38Component hHA (hcomp h hhH) T hTH hTab
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup T.isPGroup'
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hwL : w ∈ c h := hW1 hw
    have hwZ : (⟨w, hwL⟩ : c h) ∈ Subgroup.center (c h) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm12) y.2
      exact (Subgroup.mem_centralizer_iff.mp this w (hW2 hw)).symm
    have h1 := eq_one_of_mem_center_of_pow hLQ.odd_center hwZ (m := k)
      (Subtype.ext (by simpa using hk w hw.1))
    exact congrArg Subtype.val h1
  set r := ordCompl[2] (orderOf h) with hr
  have hrodd : Odd r := by
    rw [Nat.odd_iff, hr]
    have := Nat.coprime_ordCompl Nat.prime_two (isOfFinOrder_of_finite h).orderOf_pos.ne'
    exact Nat.odd_iff.mp (Nat.coprime_two_left.mp this)
  have h2el : (h ^ r) ^ 2 ^ (orderOf h).factorization 2 = 1 := by
    rw [← pow_mul, mul_comm, hr, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hrN : h ^ r ∈ Subgroup.normalizer (K : Set G) := by
    have hhr : h ^ r ∈ H := H.pow_mem hhH r
    have hp : IsPGroup 2 (Subgroup.zpowers (⟨h ^ r, hhr⟩ : H)) := by
      have hdvd : Nat.card (Subgroup.zpowers (⟨h ^ r, hhr⟩ : H)) ∣
          2 ^ (orderOf h).factorization 2 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk]
        exact orderOf_dvd_of_pow_eq_one h2el
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card hj
    have h1 := le_normalizer_of_isPGroup_of_isComponentOf hHA.1 hp
      (fstar_isComponentOf_subgroupOf_top hK) (Subgroup.mem_zpowers _)
    rw [← Subgroup.subgroupOf_normalizer_eq hK.1, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨j, hj⟩ := hrodd
  have hdecomp : h = h ^ r * ((h ^ 2) ^ j)⁻¹ := by
    rw [hj]
    group
  apply hhN
  rw [hdecomp]
  exact Subgroup.mul_mem _ hrN (Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq j))

end CFSG.Walter
