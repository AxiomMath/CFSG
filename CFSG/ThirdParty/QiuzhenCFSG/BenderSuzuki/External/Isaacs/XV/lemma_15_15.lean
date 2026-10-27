module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.problem_7_1
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CrossCharBrauer
public import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Isaacs Lemma 15.15

A source-faithful statement of Isaacs, *Character Theory of Finite Groups*,
Lemma 15.15. The action of `H` on `N` is given directly by a
`MulDistribMulAction`, the fixed-point-free hypothesis is expanded, and the
conjugate representations are supplied as the explicit family satisfying the
source formula `psiConj h (h • n) = psi n`.
-/

noncomputable section

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace XV

private noncomputable def isaacs_15_15_relative_actor_equiv
    {E H N V : Type*} [Field E]
    [Group H] [Group N] [MulDistribMulAction H N]
    [AddCommGroup V] [Module E V]
    (psi : Representation E N V)
    (psiConj : H -> Representation E N V)
    (hpsiConj : forall h : H, forall n : N, psiConj h (h • n) = psi n)
    (h k : H) (e : psiConj h ≃ₗ psiConj k) :
    psi ≃ₗ psi.comp (MulDistribMulAction.toMonoidHom N (k⁻¹ * h)) := by
  refine Theory.Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro n
  ext v
  calc
    e (psi n v) = e (psiConj h (h • n) v) := by rw [hpsiConj]
    _ = psiConj k (h • n) (e v) := e.isIntertwining (h • n) v
    _ = psi ((k⁻¹ * h) • n) (e v) := by
      rw [← hpsiConj k ((k⁻¹ * h) • n)]
      simp [mul_smul]

private noncomputable def isaacs_15_15_actor_pow_equiv
    {E H N V : Type*} [Field E]
    [Group H] [Group N] [MulDistribMulAction H N]
    [AddCommGroup V] [Module E V]
    (psi : Representation E N V) (a : H)
    (e : psi ≃ₗ psi.comp (MulDistribMulAction.toMonoidHom N a)) :
    ∀ m : ℕ,
      psi ≃ₗ psi.comp
        (MulDistribMulAction.toMonoidHom N (a ^ m)) := by
  intro m
  induction m with
  | zero =>
      refine Theory.Representation.RepEquiv.mk (LinearEquiv.refl E V) ?_
      intro n
      ext v
      simp [MulDistribMulAction.toMonoidHom_apply]
  | succ m ih =>
      refine Theory.Representation.RepEquiv.mk
        (e.toLinearEquiv.trans ih.toLinearEquiv) ?_
      intro n
      ext v
      calc
        ih (e (psi n v)) =
            ih (psi (a • n) (e v)) := by
          simpa [MulDistribMulAction.toMonoidHom_apply] using
            congrArg ih (e.isIntertwining n v)
        _ = psi ((a ^ m) • (a • n)) (ih (e v)) := by
          simpa [MulDistribMulAction.toMonoidHom_apply] using
            ih.isIntertwining (a • n) (e v)
        _ = psi ((a ^ (m + 1)) • n) (ih (e v)) := by
          rw [pow_succ, mul_smul]


private theorem isaacs_15_15_exists_prime_actor
    {E H N V : Type*} [Field E]
    [Group H] [Finite H] [Group N] [MulDistribMulAction H N]
    [AddCommGroup V] [Module E V]
    (psi : Representation E N V) (a : H) (ha : a ≠ 1)
    (e : psi ≃ₗ psi.comp (MulDistribMulAction.toMonoidHom N a)) :
    ∃ p : ℕ, ∃ b : H,
      p.Prime ∧ b ≠ 1 ∧ orderOf b = p ∧
        Nonempty
          (psi ≃ₗ psi.comp
            (MulDistribMulAction.toMonoidHom N b)) := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers a) ≠ 1 := by
    intro hcard
    have hzbot : Subgroup.zpowers a = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers a)).mp hcard
    have habot : a ∈ (⊥ : Subgroup H) := by
      simpa [hzbot] using Subgroup.mem_zpowers a
    exact ha (by simpa using habot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with
    ⟨p, hp, hpdvd⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b0, hb0_order⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.zpowers a) p hpdvd
  let b : H := b0
  have hb_order : orderOf b = p := by
    simpa [b, Subgroup.orderOf_coe] using hb0_order
  have hb_ne : b ≠ 1 := by
    intro hb
    exact hp.ne_one (by rw [← hb_order, hb, orderOf_one])
  have hb_zpowers : b ∈ Subgroup.zpowers a := b0.property
  have hb_powers : b ∈ Submonoid.powers a :=
    mem_powers_iff_mem_zpowers.mpr hb_zpowers
  rcases (Submonoid.mem_powers_iff b a).mp hb_powers with
    ⟨m, hm⟩
  refine ⟨p, b, hp, hb_ne, hb_order, ?_⟩
  exact ⟨by
    simpa [hm] using isaacs_15_15_actor_pow_equiv psi a e m⟩

private theorem isaacs_15_15_no_nontrivial_conj_of_fpf
    {H N : Type*} [Group H] [Finite H] [Group N] [Finite N]
    [MulDistribMulAction H N]
    (hfixed : ∀ n : N, n ≠ 1 → ∀ h : H, h • n = n → h = 1)
    {b : H} (hb : b ≠ 1) {x : N} (hx : x ≠ 1) :
    ¬ IsConj (b • x) x := by
  classical
  let φ : H →* MulAut N := MulDistribMulAction.toMulAut H N
  let SD := N ⋊[φ] H
  letI : Group SD := inferInstanceAs (Group (N ⋊[φ] H))
  letI : Finite SD :=
    Finite.of_equiv (N × H)
      (SemidirectProduct.equivProd (N := N) (G := H) (φ := φ)).symm
  let inl := SemidirectProduct.inl (φ := φ)
  let inr := SemidirectProduct.inr (φ := φ)
  let rightHom := SemidirectProduct.rightHom (N := N) (G := H) (φ := φ)
  let KN : Subgroup SD := inl.range
  let KH : Subgroup SD := inr.range
  have hKNker : KN = rightHom.ker := by
    simpa [KN, inl, rightHom, φ] using
      (SemidirectProduct.range_inl_eq_ker_rightHom
        (N := N) (G := H) (φ := φ))
  letI : KN.Normal := hKNker.symm ▸ rightHom.normal_ker
  have hKN : KN ≠ ⊥ := by
    intro hbot
    have hxmem : inl x ∈ (⊥ : Subgroup SD) := by
      rw [← hbot]
      exact ⟨x, rfl⟩
    have hxone : inl x = (1 : SD) := by simpa using hxmem
    apply hx
    apply SemidirectProduct.inl_injective (φ := φ)
    simpa using hxone
  have hKH : KH ≠ ⊥ := by
    intro hbot
    have hbmem : inr b ∈ (⊥ : Subgroup SD) := by
      rw [← hbot]
      exact ⟨b, rfl⟩
    have hbone : inr b = (1 : SD) := by simpa using hbmem
    apply hb
    apply SemidirectProduct.inr_injective (φ := φ)
    simpa using hbone
  have hprod : KN ⊔ KH = ⊤ := by
    apply top_unique
    intro z _
    have hmem : inl z.left * inr z.right ∈ KN ⊔ KH :=
      (KN ⊔ KH).mul_mem
        ((show KN ≤ KN ⊔ KH from le_sup_left) ⟨z.left, rfl⟩)
        ((show KH ≤ KN ⊔ KH from le_sup_right) ⟨z.right, rfl⟩)
    simpa [inl, inr, SemidirectProduct.inl_left_mul_inr_right (φ := φ) z] using hmem
  have hdisj : Disjoint KN KH := by
    rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro z hz
    rcases hz.1 with ⟨n, hn⟩
    rcases hz.2 with ⟨a, ha⟩
    have haone : a = 1 := by
      have hright := congrArg SemidirectProduct.right (ha.trans hn.symm)
      simpa [inl, inr] using hright
    calc
      z = inr a := ha.symm
      _ = inr 1 := by rw [haone]
      _ = (1 : SD) := map_one inr
  have hB :
      ∀ n : KN, n ≠ 1 → ∀ h : KH,
        (h : SD) * (n : SD) = (n : SD) * (h : SD) → h = 1 := by
    intro n hn h hcomm
    have hnright : (n : SD).right = 1 := by
      rcases n.2 with ⟨y, hy⟩
      have hright := congrArg SemidirectProduct.right hy
      simpa [inl] using hright.symm
    have hhleft : (h : SD).left = 1 := by
      rcases h.2 with ⟨a, ha⟩
      have hleft := congrArg SemidirectProduct.left ha
      simpa [inr] using hleft.symm
    have hnleft : (n : SD).left ≠ 1 := by
      intro hnleft
      apply hn
      apply Subtype.ext
      apply SemidirectProduct.ext
      · simpa using hnleft
      · simpa using hnright
    have hsmul : (h : SD).right • (n : SD).left = (n : SD).left := by
      have hc := congrArg SemidirectProduct.left hcomm
      change
        (h : SD).left * φ (h : SD).right (n : SD).left =
          (n : SD).left * φ (n : SD).right (h : SD).left at hc
      simpa [hnright, hhleft, φ,
        MulDistribMulAction.toMulAut_apply] using hc
    have hhright : (h : SD).right = 1 :=
      hfixed (n : SD).left hnleft (h : SD).right hsmul
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simpa using hhleft
    · simpa using hhright
  have hA :
      ∀ n : KN, n ≠ 1 → Subgroup.centralizer ({(n : SD)} : Set SD) ≤ KN :=
    (VII.isaacs_problem_7_1 KN KH hKN hKH hprod hdisj).1.mpr hB
  intro hxconj
  rcases isConj_iff.mp hxconj with ⟨n, hn⟩
  let t : SD := inl n * inr b
  have htconj : t * inl x * t⁻¹ = inl x := by
    calc
      t * inl x * t⁻¹ =
          inl n * (inr b * inl x * inr b⁻¹) * inl n⁻¹ := by
        dsimp only [t]
        rw [mul_inv_rev, map_inv, map_inv]
        group
      _ = inl n * inl (b • x) * inl n⁻¹ := by
        rw [← SemidirectProduct.inl_aut b x]
        rfl
      _ = inl (n * (b • x) * n⁻¹) := by simp
      _ = inl x := by rw [hn]
  let xKN : KN := ⟨inl x, ⟨x, rfl⟩⟩
  have hxKN : xKN ≠ 1 := by
    intro hone
    apply hx
    apply SemidirectProduct.inl_injective (φ := φ)
    simpa [xKN] using congrArg Subtype.val hone
  have htcent : t ∈ Subgroup.centralizer ({(xKN : SD)} : Set SD) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [xKN] using htconj)
  have htKN : t ∈ KN := hA xKN hxKN htcent
  have htker : t ∈ rightHom.ker := by simpa [hKNker] using htKN
  have htright : rightHom t = 1 := by simpa using htker
  change t.right = 1 at htright
  have ht_right : t.right = b := by
    change (1 : H) * b = b
    exact one_mul b
  exact hb (ht_right.symm.trans htright)

/-- Isaacs, Character Theory of Finite Groups, Lemma 15.15. -/
public theorem isaacs_lemma_15_15
    {E H N V : Type*} [Field E] [IsAlgClosed E]
    [Group H] [Finite H] [Group N] [Finite N]
    [MulDistribMulAction H N]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (psi : Representation E N V)
    (hchar : ¬ ringChar E ∣ Nat.card N)
    (hfixed : forall n : N, n ≠ 1 -> forall h : H, h • n = n -> h = 1)
    (hirr : Representation.IsIrreducible psi)
    (hnonprincipal : ¬ Nonempty (psi ≃ₗ Representation.trivial E N E))
    (psiConj : H -> Representation E N V)
    (hpsiConj : forall h : H, forall n : N, psiConj h (h • n) = psi n) :
    forall h k : H, Nonempty (psiConj h ≃ₗ psiConj k) -> h = k := by
  intro h k hequiv
  by_contra hne
  have ha : k⁻¹ * h ≠ 1 := by
    intro haone
    apply hne
    calc
      h = k * (k⁻¹ * h) := by simp
      _ = k := by rw [haone, mul_one]
  let e : psi ≃ₗ psi.comp
      (MulDistribMulAction.toMonoidHom N (k⁻¹ * h)) :=
    isaacs_15_15_relative_actor_equiv psi psiConj hpsiConj h k hequiv.some
  obtain ⟨p, b, hp, hb, hborder, hstableb⟩ :=
    isaacs_15_15_exists_prime_actor psi (k⁻¹ * h) ha e
  let α : N ≃* N := MulDistribMulAction.toMulAut H N b⁻¹
  have hbpow : b ^ p = 1 := by
    rw [← hborder]
    exact pow_orderOf_eq_one b
  have hαpow : α ^ p = 1 := by
    change (MulDistribMulAction.toMulAut H N b⁻¹) ^ p = 1
    rw [← map_pow, inv_pow, hbpow, inv_one, map_one]
  have hαsymm :
      α.symm.toMonoidHom = MulDistribMulAction.toMonoidHom N b := by
    ext n
    simp [α, MulDistribMulAction.toMulAut_apply]
  have hstable :
      Nonempty (psi ≃ₗ psi.comp α.symm.toMonoidHom) := by
    rw [hαsymm]
    exact hstableb
  rcases Theory.Character.crossChar_exists_nontrivial_fixed_conjClass_of_stable_irreducible
      hp hchar α hαpow psi hirr hnonprincipal hstable with
    ⟨x, hx, hxconj⟩
  exact isaacs_15_15_no_nontrivial_conj_of_fpf hfixed
    (inv_ne_one.mpr hb) hx (by
      simpa [α, MulDistribMulAction.toMulAut_apply] using hxconj)

end XV
end Isaacs
end External
end CFSG.BenderSuzuki
