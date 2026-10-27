module

public import CFSG.Quasithin.H13.L32A1410f

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B Mat8Cert G5ACert
  L1442M
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {b : Bool}

omit [Finite G] in
theorem commutator_self_le (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun a ha c hc => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hc) (K.inv_mem ha)) (K.inv_mem hc)

omit [Finite G] in
theorem le_normalizer_commutator_self (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ K, ∀ y ∈ ⁅K, K⁆, x * y * x⁻¹ ∈ ⁅K, K⁆ := by
    intro x hx y hy
    have hle : ⁅K, K⁆ ≤ ⁅K, K⁆.comap (MulAut.conj x).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun a ha c hc => ?_
      rw [Subgroup.mem_comap, map_commutatorElement]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.commutator_mem_commutator (K.mul_mem (K.mul_mem hx ha) (K.inv_mem hx))
        (K.mul_mem (K.mul_mem hx hc) (K.inv_mem hx))
    have := hle hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have e : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
  rw [e]
  exact key x⁻¹ (K.inv_mem hx) _ hy

theorem eq_bot_of_perfect_of_le {K P : Subgroup G} (hKP : K ≤ P) (hP : IsPGroup 2 ↥P)
    (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 ↥K := hP.to_le hKP
  have : Group.IsNilpotent ↥K := hK2.isNilpotent
  by_contra hne
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K)
  have htop : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, hK, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact absurd htop hlt.ne

namespace CtxA

variable (C : CtxA G T L V V₂ g D e b)
include C

theorem card_pCoreOf_K0 (hU : fsuU T V = pCoreOf 2 (l32nH T V)) :
    Nat.card (pCoreOf 2 (preM D e KA5)) = 2 ^ 9 := by
  obtain ⟨_, S⟩ := C.base.set14
  rw [C.pCoreOf_K0, ← hU, D.card_U, C.base.zU, S.card_V1, Nat.card_congr e.toEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin]
  norm_num

theorem not_isShort2_K0 (hU : fsuU T V = pCoreOf 2 (l32nH T V)) :
    ¬ IsShort2 (preM D e KA5) := by
  intro hs
  have hle := hs.2.2.1.1
  have hQ : blockQ (preM D e KA5) = fsuU T V := C.pCoreOf_K0.trans hU.symm
  have hk' : g5aA1 ∈ img8 D e (preM D e KA5) := by rw [C.img_K0]; exact g5aA1_mem_KA5
  obtain ⟨k, hk, hkN, hke⟩ := (mem_img8 D e).mp hk'
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  have haU := C.base.V2U ha
  have hcU : k * a * k⁻¹ * a⁻¹ ∈ fsuU T V :=
    (fsuU T V).mul_mem (L128A.HatU.conj_mem hkN haU) ((fsuU T V).inv_mem haU)
  have hc : k * a * k⁻¹ * a⁻¹ ∈ blockU (preM D e KA5) := by
    rw [blockU, hQ, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hk haU
    rwa [commutatorElement_def] at this
  have hcZ : k * a * k⁻¹ * a⁻¹ ∈ centerOf (fsuU T V) := by
    have := hle hc
    rw [hQ] at this
    exact this
  have h0 := (L128A.HatU.π_eq_zero_iff D hcU).mpr hcZ
  rw [← L128A.HatU.rho_sub_π D hkN haU, sub_eq_zero] at h0
  have hfix : (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
    rw [← hke, matOf_mulVec, h0]
  exact C.base.pi_a_ne D ha haV ((map_eq_zero_iff e e.injective).mp (g5aA1_fpf hfix))

theorem eq_K0_of_normal (hU : fsuU T V = pCoreOf 2 (l32nH T V)) {P : Subgroup G}
    (hPK : P ≤ preM D e KA5) (hPN : preM D e KA5 ≤ Subgroup.normalizer (P : Set G))
    (himg : img8 D e P = KA5) : P = preM D e KA5 := by
  obtain ⟨_, S⟩ := C.base.set14
  have hUK : fsuU T V ≤ preM D e KA5 := fun u hu => C.Q_le_K0 (by rw [← hU]; exact hu)
  have hg5 : g5aA1 ∈ img8 D e P := by rw [himg]; exact g5aA1_mem_KA5
  obtain ⟨p, hp, hpN, hpe⟩ := (mem_img8 D e).mp hg5
  have h1 : ∀ u ∈ fsuU T V, ∃ c ∈ P, c ∈ fsuU T V ∧ c⁻¹ * u ∈ fsuV1 T V := by
    intro u hu
    obtain ⟨x, hx⟩ := exists_fpf_preimage (e (D.π u))
    obtain ⟨w, hw, hwx⟩ := D.π_surj (e.symm x)
    have hcU : p * w * p⁻¹ * w⁻¹ ∈ fsuU T V :=
      (fsuU T V).mul_mem (L128A.HatU.conj_mem hpN hw) ((fsuU T V).inv_mem hw)
    refine ⟨p * w * p⁻¹ * w⁻¹, ?_, hcU, ?_⟩
    · rw [show p * w * p⁻¹ * w⁻¹ = p * (w * p⁻¹ * w⁻¹) by group]
      exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (hPN (hUK hw)) _).mp (P.inv_mem hp))
    · rw [← C.base.zU]
      refine (D.π_eq_iff _ hcU u hu).mp ?_
      rw [← L128A.HatU.rho_sub_π D hpN hw, sub_eq_add_neg, L14411.neg_eq_self_zmod2]
      apply e.injective
      rw [map_add, ← matOf_mulVec, hpe, hwx, LinearEquiv.apply_symm_apply, hx]
  have hcen : ∀ z ∈ fsuV1 T V, ∀ w ∈ fsuU T V, z * w = w * z := by
    intro z hz w hw
    rw [← C.base.zU] at hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 w hw).symm
  have hV1U : fsuV1 T V ≤ fsuU T V := by rw [← C.base.zU]; exact inf_le_left
  have h2 : fsuV1 T V ≤ P := by
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ fsuU T V, ∃ y ∈ fsuU T V, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact C.base.hyp.nonab ⟨⟨fun a c => Subtype.ext (hcon a a.2 c c.2)⟩⟩
    obtain ⟨c₁, hc₁P, hc₁U, hz₁⟩ := h1 x hx
    obtain ⟨c₂, hc₂P, hc₂U, hz₂⟩ := h1 y hy
    obtain ⟨z₁, rfl⟩ : ∃ z₁, x = c₁ * z₁ := ⟨c₁⁻¹ * x, by group⟩
    obtain ⟨z₂, rfl⟩ : ∃ z₂, y = c₂ * z₂ := ⟨c₂⁻¹ * y, by group⟩
    rw [inv_mul_cancel_left] at hz₁ hz₂
    have a1 : z₁ * c₂ = c₂ * z₁ := hcen z₁ hz₁ c₂ hc₂U
    have a2 : z₁ * z₂ = z₂ * z₁ := hcen z₁ hz₁ z₂ (hV1U hz₂)
    have a3 : z₂ * c₁⁻¹ = c₁⁻¹ * z₂ := hcen z₂ hz₂ c₁⁻¹ ((fsuU T V).inv_mem hc₁U)
    have hcomm : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
      calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹
          = c₁ * (z₁ * c₂) * z₂ * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * (c₂ * z₁) * z₂ * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by rw [a1]
        _ = c₁ * c₂ * (z₁ * z₂) * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * c₂ * (z₂ * z₁) * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by rw [a2]
        _ = c₁ * c₂ * (z₂ * c₁⁻¹) * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * c₂ * (c₁⁻¹ * z₂) * z₂⁻¹ * c₂⁻¹ := by rw [a3]
        _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group
    have hzV : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ ∈ fsuV1 T V := by
      rw [← C.base.zU]; exact C.base.comm_center _ hx _ hy
    have hz1 : c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ ≠ 1 := fun h => hxy (by
      calc c₁ * z₁ * (c₂ * z₂)
          = (c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹) * ((c₂ * z₂) * (c₁ * z₁)) := by
            group
        _ = c₂ * z₂ * (c₁ * z₁) := by rw [h, one_mul])
    intro v hv
    rcases S.eq_of_mem_V1 hzV hz1 hv with rfl | rfl
    · exact P.one_mem
    · rw [hcomm]
      exact P.mul_mem (P.mul_mem (P.mul_mem hc₁P hc₂P) (P.inv_mem hc₁P)) (P.inv_mem hc₂P)
  have h3 : fsuU T V ≤ P := fun u hu => by
    obtain ⟨c, hcP, -, hcu⟩ := h1 u hu
    rw [show u = c * (c⁻¹ * u) by group]
    exact P.mul_mem hcP (h2 hcu)
  refine le_antisymm hPK fun k hk => ?_
  have hkH := preM_le_H e KA5 hk
  have hk' : matOf e (D.ρ ⟨k, HN hkH⟩) ∈ img8 D e P := by
    rw [himg]; exact (mem_preM hkH).mp hk
  obtain ⟨q, hq, hqN, hqe⟩ := (mem_img8 D e).mp hk'
  have hqH : q ∈ l32nH T V := preM_le_H e KA5 (hPK hq)
  have hqkH : q⁻¹ * k ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem hqH) hkH
  have hqk : q⁻¹ * k ∈ pCoreOf 2 (l32nH T V) := by
    refine (C.base.matOf_eq_one_iff D e hqkH).mp ?_
    calc matOf e (D.ρ ⟨q⁻¹ * k, L14332.l32nH_le_normalizer_fsuU T V hqkH⟩)
        = (matOf e (D.ρ ⟨q, hqN⟩))⁻¹ * matOf e (D.ρ ⟨k, HN hkH⟩) := by
          rw [← map_inv, ← map_mul, ← map_inv, ← map_mul]
          rfl
      _ = 1 := by rw [hqe, inv_mul_cancel]
  rw [show k = q * (q⁻¹ * k) by group]
  exact P.mul_mem hq (h3 (by rw [hU]; exact hqk))

theorem perfect_K0 (hU : fsuU T V = pCoreOf 2 (l32nH T V)) :
    ⁅preM D e KA5, preM D e KA5⁆ = preM D e KA5 := by
  have hKA5p : ⁅KA5, KA5⁆ = KA5 := by
    have : IsSimpleGroup ↥KA5 := isSimpleGroup_KA5
    rw [← Subgroup.map_subtype_commutator,
      CFSG.Walter.Suzuki.commutator_eq_top_of_card_sixty card_KA5, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hle := commutator_self_le (preM D e KA5)
  refine C.eq_K0_of_normal hU hle (le_normalizer_commutator_self _)
    (le_antisymm ((img8_mono D e hle).trans C.img_K0.le) ?_)
  calc KA5 = ⁅KA5, KA5⁆ := hKA5p.symm
    _ ≤ img8 D e ⁅preM D e KA5, preM D e KA5⁆ := by
      refine Subgroup.commutator_le.mpr fun γ₁ hγ₁ γ₂ hγ₂ => ?_
      have h1 : γ₁ ∈ img8 D e (preM D e KA5) := by rw [C.img_K0]; exact hγ₁
      have h2 : γ₂ ∈ img8 D e (preM D e KA5) := by rw [C.img_K0]; exact hγ₂
      obtain ⟨k₁, hk₁, hk₁N, rfl⟩ := (mem_img8 D e).mp h1
      obtain ⟨k₂, hk₂, hk₂N, rfl⟩ := (mem_img8 D e).mp h2
      have hN : ⁅k₁, k₂⁆ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
        (⁅(⟨k₁, hk₁N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))),
          (⟨k₂, hk₂N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G)))⁆).2
      refine (mem_img8 D e).mpr ⟨⁅k₁, k₂⁆, Subgroup.commutator_mem_commutator hk₁ hk₂, hN, ?_⟩
      show matOf e (D.ρ ⁅(⟨k₁, hk₁N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))),
        (⟨k₂, hk₂N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G)))⁆) = _
      rw [map_commutatorElement, map_commutatorElement]

theorem mem_cComp_K0 (hU : fsuU T V = pCoreOf 2 (l32nH T V)) :
    preM D e KA5 ∈ cComp (preM D e KA5 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : preM D e KA5 ≠ ⊥ := by
    intro h
    have := C.card_K0_gt
    rw [h, Subgroup.card_bot] at this
    omega
  have hnorm : ((preM D e KA5).subgroupOf (preM D e KA5 ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer C.T_le_normalizer_K0)
  refine ⟨hne, C.perfect_K0 hU, A3.subnormal_of_normal le_sup_left hnorm,
    fun K hKL hK1 hKp hKs => ?_⟩
  have hKL' : IsSubnormal K (preM D e KA5) := A3.subnormal_of_le_of_le hKs hKL.le le_sup_left
  obtain ⟨P, hPlt, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKL' hKL
  have hPK : P ≤ preM D e KA5 := hPlt.le
  have hPN : preM D e KA5 ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mp hPn
  have himgK : img8 D e P ≤ KA5 := (img8_mono D e hPK).trans C.img_K0.le
  have himgN : KA5 ≤ Subgroup.normalizer (img8 D e P : Set (GL (Fin 8) (ZMod 2))) := by
    intro γ hγ
    have hγ' : γ ∈ img8 D e (preM D e KA5) := by rw [C.img_K0]; exact hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (mem_img8 D e).mp hγ'
    refine Subgroup.mem_normalizer_fintype fun δ hδ => ?_
    obtain ⟨p, hp, hpN, rfl⟩ := (mem_img8 D e).mp hδ
    have hc : k * p * k⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hPN hk) p).mp hp
    refine (mem_img8 D e).mpr ⟨k * p * k⁻¹, hc,
      (⟨k, hkN⟩ * ⟨p, hpN⟩ * (⟨k, hkN⟩)⁻¹ : ↥(Subgroup.normalizer (fsuU T V : Set G))).2, ?_⟩
    show matOf e (D.ρ ((⟨k, hkN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨p, hpN⟩ *
      (⟨k, hkN⟩)⁻¹)) = _
    simp only [map_mul, map_inv]
  rcases eq_bot_or_eq_KA5 himgK himgN with h | h
  ·
    have hPQ : P ≤ pCoreOf 2 (l32nH T V) := fun p hp => by
      have hpH := preM_le_H e KA5 (hPK hp)
      refine (C.base.matOf_eq_one_iff D e hpH).mp ?_
      have hm : matOf e (D.ρ ⟨p, HN hpH⟩) ∈ img8 D e P := (mem_img8 D e).mpr ⟨p, hp, _, rfl⟩
      rw [h] at hm
      exact Subgroup.mem_bot.mp hm
    exact hK1 (eq_bot_of_perfect_of_le (hKP.trans hPQ)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hKp)
  · exact hPlt.ne (C.eq_K0_of_normal hU hPK hPN h)

end CtxA

end CFSG.Quasithin.H13.Q1410

end
