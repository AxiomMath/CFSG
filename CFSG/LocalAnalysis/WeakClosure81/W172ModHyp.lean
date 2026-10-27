module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.LocalAnalysis.WeakClosure81.W172ModDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] def W172Hyp (p : ℕ) (A K : Subgroup (LGL 2 W)) : Prop :=
  K ≤ A ∧ K.relIndex A = p

@[expose] def w172X (A K : Subgroup (LGL 2 W)) : Submodule (ZMod 2) W :=
  fixSub K ⊓ commSub A

open scoped Classical

private lemma w172_odd_nsmul {n : ℕ} (hn : Odd n) (v : W) : n • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) n v, (ZMod.natCast_eq_one_iff_odd).mpr hn,
    one_smul]

private instance w172_finite_submodule : Finite (Submodule (ZMod 2) W) :=
  Finite.of_injective (fun U : Submodule (ZMod 2) W => (U : Set W)) SetLike.coe_injective

private noncomputable instance w172_fintype_subgroup (H : Subgroup (LGL 2 W)) : Fintype H :=
  Fintype.ofFinite H

private noncomputable def w172Sum (H : Subgroup (LGL 2 W)) : W →ₗ[ZMod 2] W :=
  ∑ h : H, (h : LGL 2 W).toLinearMap

private lemma w172Sum_apply (H : Subgroup (LGL 2 W)) (v : W) :
    w172Sum H v = ∑ h : H, (h : LGL 2 W) v := by
  simp [w172Sum, LinearMap.sum_apply]

private lemma w172Sum_left (H : Subgroup (LGL 2 W)) {k : LGL 2 W} (hk : k ∈ H) (v : W) :
    k (w172Sum H v) = w172Sum H v := by
  rw [w172Sum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨k, hk⟩ : H)) _ _ fun h => rfl

private lemma w172Sum_right (H : Subgroup (LGL 2 W)) {k : LGL 2 W} (hk : k ∈ H) (v : W) :
    w172Sum H (k v) = w172Sum H v := by
  rw [w172Sum_apply H (k v), w172Sum_apply H v]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨k, hk⟩ : H)) _ _ fun h => rfl

private lemma w172Sum_fixed {H : Subgroup (LGL 2 W)} {v : W}
    (hv : ∀ h ∈ H, h v = v) : w172Sum H v = Nat.card H • v := by
  have h' : ∀ h : H, (h : LGL 2 W) v = v := fun h => hv _ h.2
  rw [w172Sum_apply]
  simp only [h', Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

private lemma w172Sum_fixed_odd {H : Subgroup (LGL 2 W)} (hH : Odd (Nat.card H)) {v : W}
    (hv : ∀ h ∈ H, h v = v) : w172Sum H v = v := by
  rw [w172Sum_fixed hv, w172_odd_nsmul hH]

private lemma w172Sum_sum_sub {A K : Subgroup (LGL 2 W)} (hKA : K ≤ A)
    (hK : Odd (Nat.card K)) (x : W) : w172Sum A (w172Sum K x) = w172Sum A x := by
  calc w172Sum A (w172Sum K x) = ∑ h : K, w172Sum A ((h : LGL 2 W) x) := by
        rw [w172Sum_apply K x, map_sum]
    _ = ∑ _h : K, w172Sum A x := Finset.sum_congr rfl fun h _ =>
          w172Sum_right A (hKA h.2) x
    _ = Nat.card K • w172Sum A x := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    _ = w172Sum A x := w172_odd_nsmul hK _

private lemma w172_sum_eq_of_sup {A K L : Subgroup (LGL 2 W)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) (hLA : L ≤ A)
    (hsup : K ⊔ L = A) (hodd : Odd (Nat.card A)) {v : W} (hv : ∀ l ∈ L, l v = v) :
    w172Sum K v = w172Sum A v := by
  have hKodd : Odd (Nat.card K) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hKA)
  have hwK : ∀ k ∈ K, k (w172Sum K v) = w172Sum K v := fun k hk => w172Sum_left K hk v
  have hwL : ∀ l ∈ L, l (w172Sum K v) = w172Sum K v := by
    intro l hl
    calc l (w172Sum K v) = ∑ h : K, l ((h : LGL 2 W) v) := by
          rw [w172Sum_apply, map_sum]
      _ = ∑ h : K, (h : LGL 2 W) v := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hc : l * (h : LGL 2 W) = (h : LGL 2 W) * l := hA l (hLA hl) _ (hKA h.2)
        calc l ((h : LGL 2 W) v) = ((l * (h : LGL 2 W) : LGL 2 W)) v := rfl
          _ = (((h : LGL 2 W) * l : LGL 2 W)) v := by rw [hc]
          _ = (h : LGL 2 W) v := by
            rw [show ((h : LGL 2 W) * l : LGL 2 W) v = (h : LGL 2 W) (l v) from rfl,
              hv l hl]
      _ = w172Sum K v := (w172Sum_apply K v).symm
  have hwA : ∀ a ∈ A, a (w172Sum K v) = w172Sum K v := by
    have hle : A ≤ MulAction.stabilizer (LGL 2 W) (w172Sum K v) := by
      rw [← hsup]
      refine sup_le (fun k hk => ?_) (fun l hl => ?_)
      · exact MulAction.mem_stabilizer_iff.mpr (hwK k hk)
      · exact MulAction.mem_stabilizer_iff.mpr (hwL l hl)
    exact fun a ha => MulAction.mem_stabilizer_iff.mp (hle ha)
  have h1 : w172Sum A (w172Sum K v) = w172Sum K v := w172Sum_fixed_odd hodd hwA
  rw [w172Sum_sum_sub hKA hKodd v] at h1
  exact h1.symm

private lemma w172_commSub_eq_ker_sum {A : Subgroup (LGL 2 W)} (hAodd : Odd (Nat.card A)) :
    commSub A = LinearMap.ker (w172Sum A) := by
  refine le_antisymm ?_ ?_
  · rw [commSub_le_iff]
    intro a ha v
    rw [LinearMap.mem_ker, map_sub, w172Sum_right A ha v, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hsum : ∑ b : A, ((b : LGL 2 W) x - x) = x := by
      rw [Finset.sum_sub_distrib, ← w172Sum_apply, hx, zero_sub, ZModModule.neg_eq_self,
        Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, w172_odd_nsmul hAodd]
    rw [← hsum]
    exact Submodule.sum_mem _ fun b _ => sub_mem_commSub A b.2 x

private lemma w172_mem_commSub_iff {A : Subgroup (LGL 2 W)} (hAodd : Odd (Nat.card A))
    (x : W) : x ∈ commSub A ↔ w172Sum A x = 0 := by
  rw [w172_commSub_eq_ker_sum hAodd]
  exact LinearMap.mem_ker

private lemma w172_mem_X {A K : Subgroup (LGL 2 W)} (hAodd : Odd (Nat.card A)) {x : W} :
    x ∈ w172X A K ↔ (∀ k ∈ K, k x = x) ∧ w172Sum A x = 0 := by
  unfold w172X
  rw [Submodule.mem_inf, mem_fixSub, w172_mem_commSub_iff hAodd]

private lemma w172_maxsub {p : ℕ} (hp : p.Prime) {A K M : Subgroup (LGL 2 W)}
    (hK : K.relIndex A = p) (hKM : K ≤ M) (hMA : M ≤ A) (hne : M ≠ K) : M = A := by
  have h1 := Subgroup.relIndex_mul_relIndex K M A hKM hMA
  have hne1 : K.relIndex M ≠ 1 := fun h =>
    hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hKM)
  have hdvd : K.relIndex M ∣ p := ⟨M.relIndex A, by rw [← hK, ← h1]⟩
  have hKMp : K.relIndex M = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  rw [hKMp, hK] at h1
  have h2 : M.relIndex A = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1)
  exact le_antisymm hMA (Subgroup.relIndex_eq_one.mp h2)

private lemma w172_hyp_eq {p : ℕ} (hp : p.Prime) {A K L : Subgroup (LGL 2 W)}
    (hK : K.relIndex A = p) (hL : L.relIndex A = p) (hKA : K ≤ A) (hLK : L ≤ K) : L = K := by
  have h1 := Subgroup.relIndex_mul_relIndex L K A hLK hKA
  rw [hK, hL] at h1
  have h2 : L.relIndex K = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (by rw [one_mul]; exact h1)
  exact le_antisymm hLK (Subgroup.relIndex_eq_one.mp h2)

private lemma w172_hyp_sup {p : ℕ} (hp : p.Prime) {A K K' : Subgroup (LGL 2 W)}
    (hK' : K'.relIndex A = p) (hK : K.relIndex A = p) (hK'A : K' ≤ A) (hKA : K ≤ A)
    (hne : K ≠ K') : K' ⊔ K = A := by
  refine w172_maxsub hp hK' le_sup_left (sup_le hK'A hKA) fun h => hne ?_
  have hKK' : K ≤ K' := by
    have hm : K ≤ K' ⊔ K := le_sup_right
    rwa [h] at hm
  exact w172_hyp_eq hp hK' hK hK'A hKK'

private lemma w172_isPGroup {p : ℕ} (hp : p.Prime) {A : Subgroup (LGL 2 W)}
    (hexp : ∀ a ∈ A, a ^ p = 1) : IsPGroup p A := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro a
  refine ⟨1, ?_⟩
  rw [pow_one, Subgroup.orderOf_mk]
  exact orderOf_dvd_of_pow_eq_one (hexp a.1 a.2)

private lemma w172_odd_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (LGL 2 W)}
    (hAp : IsPGroup p A) : Odd (Nat.card A) := by
  obtain ⟨n, hn⟩ := hAp.exists_card_dvd_pow
  exact (hp.odd_of_ne_two hp2).pow.of_dvd_nat hn

private lemma w172_map_commSub_of_commute {A : Subgroup (LGL 2 W)} {g : LGL 2 W}
    (hg : ∀ a ∈ A, g * a = a * g) {w : W} (hw : w ∈ commSub A) : g w ∈ commSub A := by
  unfold commSub at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    have h4 : g (b v - v) = b (g v) - g v := by
      rw [map_sub]
      have hc : g * b = b * g := hg b hb
      change (g * b) v - g v = (b * g) v - g v
      rw [hc]
    rw [h4]
    exact Submodule.subset_span ⟨b, hb, g v, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

private lemma w172_map_X {A K : Subgroup (LGL 2 W)} (hKA : K ≤ A) {g : LGL 2 W}
    (hg : ∀ a ∈ A, g * a = a * g) {w : W} (hw : w ∈ w172X A K) : g w ∈ w172X A K := by
  refine Submodule.mem_inf.mpr ⟨?_, w172_map_commSub_of_commute hg hw.2⟩
  rw [mem_fixSub]
  intro k hk
  calc k (g w) = (k * g) w := rfl
    _ = (g * k) w := by rw [hg k (hKA hk)]
    _ = g (k w) := rfl
    _ = g w := by rw [(mem_fixSub K).mp hw.1 k hk]

private lemma w172_fixed_eq_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hK : W172Hyp p A K) {g : LGL 2 W} (hgA : g ∈ A)
    (hgK : g ∉ K) {w : W} (hw : w ∈ w172X A K) (hgw : g w = w) : w = 0 := by
  have hAodd := w172_odd_card hp hp2 (w172_isPGroup hp hexp)
  have hsup : K ⊔ Subgroup.zpowers g = A := by
    refine w172_maxsub hp hK.2 le_sup_left
      (sup_le hK.1 (Subgroup.zpowers_le.mpr hgA)) ?_
    intro h
    have hm : g ∈ K ⊔ Subgroup.zpowers g :=
      (le_sup_right : Subgroup.zpowers g ≤ K ⊔ Subgroup.zpowers g)
        (Subgroup.mem_zpowers g)
    rw [h] at hm
    exact hgK hm
  have hfixK : ∀ k ∈ K, k w = w := (mem_fixSub K).mp hw.1
  have hAfix : ∀ a ∈ A, a w = w := by
    have hle : K ⊔ Subgroup.zpowers g ≤ MulAction.stabilizer (LGL 2 W) w := by
      refine sup_le (fun k hk => MulAction.mem_stabilizer_iff.mpr (hfixK k hk)) ?_
      exact Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hgw)
    rw [hsup] at hle
    exact fun a ha => MulAction.mem_stabilizer_iff.mp (hle ha)
  have hsumw : w172Sum A w = w := w172Sum_fixed_odd hAodd hAfix
  have hsum0 : w172Sum A w = 0 := (w172_mem_commSub_iff hAodd w).mp hw.2
  rw [hsumw] at hsum0
  exact hsum0

private lemma w172_X_ne_bot {A K : Subgroup (LGL 2 W)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) (hAodd : Odd (Nat.card A))
    {w : W} (hw : ∀ k ∈ K, k w = w) (hwA : ∃ a ∈ A, a w ≠ w) : w172X A K ≠ ⊥ := by
  intro hbot
  obtain ⟨a, haA, haw⟩ := hwA
  have hQfix : ∀ b ∈ A, b (w172Sum A w) = w172Sum A w := fun b hb => w172Sum_left A hb w
  have hQQ : w172Sum A (w172Sum A w) = w172Sum A w := w172Sum_fixed_odd hAodd hQfix
  have huX : w - w172Sum A w ∈ w172X A K := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_fixSub]
      intro k hk
      rw [map_sub, hw k hk, w172Sum_left A (hKA hk) w]
    · rw [w172_mem_commSub_iff hAodd]
      rw [map_sub, hQQ, sub_self]
  rw [hbot, Submodule.mem_bot] at huX
  have hwfix : w = w172Sum A w := sub_eq_zero.mp huX
  exact haw (by rw [hwfix, w172Sum_left A haA w])

private lemma w172_avg {A : Subgroup (LGL 2 W)} (hodd : Odd (Nat.card A))
    (U : Submodule (ZMod 2) W) (hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) :
    ∃ U' : Submodule (ZMod 2) W, (∀ a ∈ A, ∀ u ∈ U', a u ∈ U') ∧ IsCompl U U' := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  have hC' : IsCompl (LinearMap.range U.subtype) C := by
    rw [Submodule.range_subtype]; exact hC
  let pr : W →ₗ[ZMod 2] U :=
    LinearMap.linearProjOfIsCompl C U.subtype Subtype.val_injective hC'
  let pj : W →ₗ[ZMod 2] W := U.subtype ∘ₗ pr
  have hpjU : ∀ u ∈ U, pj u = u := by
    intro u hu
    have h1 := LinearMap.linearProjOfIsCompl_apply_left C U.subtype
      Subtype.val_injective hC' ⟨u, hu⟩
    have h2 : pr u = ⟨u, hu⟩ := h1
    show U.subtype (pr u) = u
    rw [h2]
    rfl
  have hpjmem : ∀ v, pj v ∈ U := fun v => (pr v).2
  let Pav : W →ₗ[ZMod 2] W := ∑ a : A,
    ((a : LGL 2 W).toLinearMap ∘ₗ pj ∘ₗ ((a : LGL 2 W)⁻¹).toLinearMap)
  have hPav : ∀ v, Pav v = ∑ a : A, (a : LGL 2 W) (pj ((a : LGL 2 W)⁻¹ v)) := by
    intro v
    simp [Pav, LinearMap.sum_apply]
  have hPavU : ∀ u ∈ U, Pav u = u := by
    intro u hu
    rw [hPav]
    calc ∑ a : A, (a : LGL 2 W) (pj ((a : LGL 2 W)⁻¹ u)) =
          ∑ a : A, (a : LGL 2 W) ((a : LGL 2 W)⁻¹ u) :=
          Finset.sum_congr rfl fun a _ => by
            rw [hpjU _ (hU _ (A.inv_mem a.2) u hu)]
      _ = ∑ _a : A, u := Finset.sum_congr rfl fun a _ => by simp
      _ = Nat.card A • u := by
          simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      _ = u := w172_odd_nsmul hodd u
  have hPavmem : ∀ v, Pav v ∈ U := by
    intro v
    rw [hPav]
    exact Submodule.sum_mem _ fun a _ => hU _ a.2 _ (hpjmem _)
  have hPavequiv : ∀ b ∈ A, ∀ v, Pav (b v) = b (Pav v) := by
    intro b hb v
    rw [hPav, hPav, map_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft (⟨b, hb⟩ : A)) _ _ fun a => ?_).symm
    simp [mul_inv_rev, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.ker Pav, fun a ha w hw => ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hw ⊢
    rw [hPavequiv a ha, hw, map_zero]
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hxU hxK
      rw [LinearMap.mem_ker] at hxK
      rw [← hPavU x hxU, hxK]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      refine ⟨Pav v, hPavmem v, v - Pav v, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hPavU (Pav v) (hPavmem v), sub_self]

private lemma w172_simple_card {p : ℕ} (hp : p.Prime) {M G : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] [Nontrivial M] [Group G] [Finite G]
    (ψ : G →* (M ≃ₗ[ZMod 2] M))
    (hcomm : ∀ g h : G, ψ g * ψ h = ψ h * ψ g) (hexp : ∀ g : G, g ^ p = 1)
    (hsimple : ∀ N : Submodule (ZMod 2) M, (∀ g : G, ∀ x ∈ N, ψ g x ∈ N) → N = ⊥ ∨ N = ⊤) :
    Nat.card ψ.range ≤ p := by
  let E : (M ≃ₗ[ZMod 2] M) → Module.End (ZMod 2) M := fun e => (e : M →ₗ[ZMod 2] M)
  have hEmul : ∀ e f : M ≃ₗ[ZMod 2] M, E (e * f) = E e * E f := fun e f => by
    apply LinearMap.ext
    intro x
    rfl
  have hE1 : E 1 = 1 := by
    apply LinearMap.ext
    intro x
    rfl
  let S : Set (Module.End (ZMod 2) M) := {r | ∃ g : G, r = E (ψ g)}
  have hScomm : S.Pairwise Commute := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ _
    show E (ψ g) * E (ψ h) = E (ψ h) * E (ψ g)
    rw [← hEmul, ← hEmul, hcomm g h]
  letI : CommRing (Subring.closure S) := Subring.closureCommRingOfComm hScomm
  have hRS : ∀ r ∈ S, ∀ a : Subring.closure S,
      (a : Module.End (ZMod 2) M) * r = r * (a : Module.End (ZMod 2) M) := by
    intro r hr a
    have hc := mul_comm a (⟨r, Subring.subset_closure hr⟩ : Subring.closure S)
    have := congrArg Subtype.val hc
    simpa using this
  have hnzd : NoZeroDivisors (Subring.closure S) := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    have hab' : (a : Module.End (ZMod 2) M) * (b : Module.End (ZMod 2) M) = 0 := by
      have := congrArg Subtype.val hab
      simpa using this
    have hker : ∀ g : G, ∀ x ∈ LinearMap.ker (a : Module.End (ZMod 2) M),
        ψ g x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
      intro g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc := hRS (E (ψ g)) ⟨g, rfl⟩ a
      have := congrArg (fun r : Module.End (ZMod 2) M => r x) hc
      simp only [Module.End.mul_apply] at this
      rw [hx, map_zero] at this
      exact this
    rcases hsimple _ hker with hbot | htop
    · apply Subtype.ext
      apply LinearMap.ext
      intro x
      have hbx : (b : Module.End (ZMod 2) M) x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
        rw [LinearMap.mem_ker]
        have := congrArg (fun r : Module.End (ZMod 2) M => r x) hab'
        simpa [Module.End.mul_apply] using this
      rw [hbot, Submodule.mem_bot] at hbx
      simpa using hbx
    · exfalso
      apply ha
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      have hx : x ∈ LinearMap.ker (a : Module.End (ZMod 2) M) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hx
      simpa using hx
  haveI : NoZeroDivisors (Subring.closure S) := hnzd
  haveI : IsDomain (Subring.closure S) := NoZeroDivisors.to_isDomain _
  let f : Polynomial (Subring.closure S) := Polynomial.X ^ p - Polynomial.C 1
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hp.pos 1
  have hfdeg : f.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  let rts : Finset (Subring.closure S) := f.roots.toFinset
  have hrts : ∀ r : Subring.closure S, r ^ p = 1 → r ∈ rts := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0]
    simp [f, hr]
  have hcardrts : rts.card ≤ p := by
    calc rts.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = p := hfdeg
  have hmemS : ∀ x ∈ ψ.range, E (x : M ≃ₗ[ZMod 2] M) ∈ Subring.closure S := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Subring.subset_closure ⟨g, rfl⟩
  have hEpow : ∀ g : G, ∀ n : ℕ, E (ψ g) ^ n = E (ψ g ^ n) := by
    intro g n
    induction n with
    | zero => rw [pow_zero, pow_zero, hE1]
    | succ n ih => rw [pow_succ, pow_succ, ih, hEmul]
  have hpowE : ∀ x ∈ ψ.range, E (x : M ≃ₗ[ZMod 2] M) ^ p = 1 := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    have hgp : ψ g ^ p = 1 := by rw [← map_pow, hexp g, map_one]
    rw [hEpow, hgp, hE1]
  let F : ψ.range → rts := fun x =>
    ⟨⟨E (x.1 : M ≃ₗ[ZMod 2] M), hmemS x.1 x.2⟩, hrts _ (Subtype.ext (by
      simpa using hpowE x.1 x.2))⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : E (x.1 : M ≃ₗ[ZMod 2] M) = E (y.1 : M ≃ₗ[ZMod 2] M) := by
      have := congrArg (fun r : rts => (r.1 : Module.End (ZMod 2) M)) hxy
      exact this
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    exact congrArg (fun f : Module.End (ZMod 2) M => f m) h1
  have hle : Nat.card ψ.range ≤ Nat.card rts := Nat.card_le_card_of_injective F hFinj
  have hrtsc : Nat.card rts = rts.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

private lemma w172_exists_hyp_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) {z : LGL 2 W} (hzA : z ∈ A) (hz1 : z ≠ 1) :
    ∃ K : Subgroup (LGL 2 W), K ≤ A ∧ K.relIndex A = p ∧ z ∉ K ∧ w172X A K ≠ ⊥ := by
  haveI := Fact.mk hp
  have hAp : IsPGroup p A := w172_isPGroup hp hexp
  have hAodd : Odd (Nat.card A) := w172_odd_card hp hp2 hAp
  obtain ⟨u0, hu0⟩ : ∃ u : W, z u ≠ u := by
    by_contra h
    have h' : ∀ u : W, z u = u := fun u => by
      by_contra hu
      exact h ⟨u, hu⟩
    exact hz1 (LinearEquiv.ext h')
  haveI : WellFoundedLT (Submodule (ZMod 2) W) := Finite.to_wellFoundedLT
  let 𝒰 : Set (Submodule (ZMod 2) W) :=
    {U | (∀ a ∈ A, ∀ u ∈ U, a u ∈ U) ∧ ∃ u ∈ U, z u ≠ u}
  have hne : 𝒰.Nonempty :=
    ⟨⊤, fun a _ u _ => Submodule.mem_top, u0, Submodule.mem_top, hu0⟩
  obtain ⟨U, ⟨hUinv, u1, hu1U, hu1⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt 𝒰 hne
  have hsimp : ∀ U' : Submodule (ZMod 2) W, U' ≤ U →
      (∀ a ∈ A, ∀ w ∈ U', a w ∈ U') → U' = ⊥ ∨ U' = U := by
    intro U' hU'U hU'inv
    by_contra hcon
    have hU'0 : U' ≠ ⊥ := fun h => hcon (Or.inl h)
    have hU'U' : U' ≠ U := fun h => hcon (Or.inr h)
    obtain ⟨U'', hU''inv, hcompl⟩ := w172_avg hAodd U' hU'inv
    have hUeq : U' ⊔ (U'' ⊓ U) = U := by
      rw [← sup_inf_assoc_of_le U'' hU'U, hcompl.sup_eq_top, top_inf_eq]
    have hdisj : Disjoint U' (U'' ⊓ U) := hcompl.disjoint.mono_right inf_le_left
    have hU''inv' : ∀ a ∈ A, ∀ u ∈ U'' ⊓ U, a u ∈ U'' ⊓ U := fun a ha u hu =>
      ⟨hU''inv a ha u hu.1, hUinv a ha u hu.2⟩
    by_cases hzW : ∃ w ∈ U', z w ≠ w
    · exact hmin U' ⟨hU'inv, hzW⟩ (lt_of_le_of_ne hU'U hU'U')
    · by_cases hzU : ∃ u ∈ U'' ⊓ U, z u ≠ u
      · have hlt : U'' ⊓ U < U := by
          refine lt_of_le_of_ne inf_le_right fun h => ?_
          have h0 := hdisj.eq_bot
          rw [h, inf_eq_left.mpr hU'U] at h0
          exact hU'0 h0
        exact hmin (U'' ⊓ U) ⟨hU''inv', hzU⟩ hlt
      · have hzW' : ∀ w ∈ U', z w = w := fun w hw => by
          by_contra hzw
          exact hzW ⟨w, hw, hzw⟩
        have hzU' : ∀ u ∈ U'' ⊓ U, z u = u := fun u hu => by
          by_contra hzu
          exact hzU ⟨u, hu, hzu⟩
        apply hu1
        rw [← hUeq] at hu1U
        obtain ⟨w, hw, u'', hu'', hsum⟩ := Submodule.mem_sup.mp hu1U
        rw [← hsum, map_add, hzW' w hw, hzU' u'' hu'']
  have hres : ∀ a ∈ A, U.map ((a : LGL 2 W) : W →ₗ[ZMod 2] W) = U := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hUinv a ha u hu
    · intro u hu
      exact ⟨(a : LGL 2 W)⁻¹ u, hUinv _ (A.inv_mem ha) u hu, by simp⟩
  let ψ : A →* (U ≃ₗ[ZMod 2] U) :=
    { toFun := fun a => LinearEquiv.ofSubmodules (a : LGL 2 W) U U (hres a a.2)
      map_one' := by
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        rfl }
  have hcommψ : ∀ g h : A, ψ g * ψ h = ψ h * ψ g := by
    intro g h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ g.2 _ h.2)
  have hexpψ : ∀ g : A, g ^ p = 1 := fun g => Subtype.ext (by simpa using hexp _ g.2)
  have hu1pos : u1 ≠ 0 := by
    intro h
    apply hu1
    rw [h, map_zero]
  haveI : Nontrivial U := ⟨⟨⟨u1, hu1U⟩, 0, fun h => hu1pos (congrArg Subtype.val h)⟩⟩
  have hsimpleψ : ∀ N : Submodule (ZMod 2) U, (∀ g : A, ∀ x ∈ N, ψ g x ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hW : N.map U.subtype ≤ U := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hWinv : ∀ a ∈ A, ∀ w ∈ N.map U.subtype, a w ∈ N.map U.subtype := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨ψ ⟨a, ha⟩ x, hN ⟨a, ha⟩ x hx, rfl⟩
    rcases hsimp _ hW hWinv with h | h
    · left
      apply Submodule.map_injective_of_injective U.injective_subtype
      rw [Submodule.map_bot]
      exact h
    · right
      apply Submodule.map_injective_of_injective U.injective_subtype
      rw [h, Submodule.map_subtype_top]
  have hcard := w172_simple_card hp ψ hcommψ hexpψ hsimpleψ
  let K : Subgroup (LGL 2 W) := ψ.ker.map A.subtype
  have hKA : K ≤ A := Subgroup.map_subtype_le ψ.ker
  have hKmem : ∀ k ∈ K, ∀ u ∈ U, k u = u := by
    intro k hk u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hk
    have h1 : ψ a = 1 := MonoidHom.mem_ker.mp ha
    have h2 : ((ψ a) ⟨u, hu⟩ : W) = u := by rw [h1]; rfl
    exact h2
  have hzK : z ∉ K := fun hz => hu1 (hKmem z hz u1 hu1U)
  have htopA : (⊤ : Subgroup A).map A.subtype = A := by
    ext x
    simp
  have hKidx : K.relIndex A = ψ.ker.index := by
    have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype) ψ.ker ⊤
      Subtype.val_injective
    rw [htopA, Subgroup.relIndex_top_right] at h
    exact h
  have hidx_le : K.relIndex A ≤ p := by
    rw [hKidx, Subgroup.index_ker]
    exact hcard
  have hidx_ne1 : K.relIndex A ≠ 1 := by
    intro h1
    have hAK := Subgroup.relIndex_eq_one.mp h1
    exact hzK (hAK hzA)
  have hidx_pp : K.relIndex A = p := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hAp
    have hdvd : K.relIndex A ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card K A
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact absurd (by simpa using hkeq) hidx_ne1
      · simpa using hkeq
    · exfalso
      have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
      have h4 : K.relIndex A ≤ p := hidx_le
      rw [hkeq] at h4
      linarith
  refine Exists.intro K (And.intro hKA (And.intro hidx_pp (And.intro hzK ?_)))
  · exact w172_X_ne_bot hcomm hKA hAodd (w := u1)
      (fun k hk => hKmem k hk u1 hu1U) ⟨z, hzA, hu1⟩

theorem w172_X_iSupIndep {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (LGL 2 W)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ p = 1) :
    iSupIndep (fun K : {K : Subgroup (LGL 2 W) // W172Hyp p A K} => w172X A K.1) := by
  have hAodd : Odd (Nat.card A) := w172_odd_card hp hp2 (w172_isPGroup hp hexp)
  rw [iSupIndep_def]
  intro K
  rw [Submodule.disjoint_def]
  intro x hxK hxSup
  have hxK' := (w172_mem_X hAodd).mp hxK
  have hKodd : Odd (Nat.card K.1) :=
    hAodd.of_dvd_nat (Subgroup.card_dvd_of_le K.2.1)
  have hle : (⨆ (j : {K : Subgroup (LGL 2 W) // W172Hyp p A K}) (_ : j ≠ K),
      w172X A j.1) ≤ LinearMap.ker (w172Sum K.1 - w172Sum A) := by
    refine iSup₂_le fun j hj => ?_
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hj' := (w172_mem_X hAodd).mp hy
    have hne : j.1 ≠ K.1 := fun h => hj (Subtype.ext h)
    have hsup : K.1 ⊔ j.1 = A := by
      rw [sup_comm]
      exact w172_hyp_sup hp j.2.2 K.2.2 j.2.1 K.2.1 (Ne.symm hne)
    exact w172_sum_eq_of_sup hcomm K.2.1 j.2.1 hsup hAodd hj'.1
  have hxker := hle hxSup
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hxker
  rw [w172Sum_fixed_odd hKodd hxK'.1, hxK'.2] at hxker
  exact hxker

theorem w172_orderOf_two_le_finrank_X {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hK : W172Hyp p A K) (hX : w172X A K ≠ ⊥) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (w172X A K) := by
  have hAodd : Odd (Nat.card A) := w172_odd_card hp hp2 (w172_isPGroup hp hexp)
  obtain ⟨g, hgA, hgK⟩ : ∃ g ∈ A, g ∉ K := by
    by_contra hcon
    have hcon' : ∀ g, g ∈ A → g ∈ K := by
      intro g hg
      by_contra hgK
      exact hcon ⟨g, hg, hgK⟩
    have hKA' : K = A := le_antisymm hK.1 hcon'
    have hKp : K.relIndex A = p := hK.2
    rw [hKA', Subgroup.relIndex_self] at hKp
    have := hp.one_lt
    omega
  have hyM : ∀ x ∈ w172X A K, g x ∈ w172X A K :=
    fun x hx => w172_map_X hK.1 (fun a ha => hcomm g hgA a ha) hx
  have hfix : ∀ x ∈ w172X A K, g x = x → x = 0 :=
    fun x hx hgx => w172_fixed_eq_zero hp hp2 hcomm hexp hK hgA hgK hx hgx
  have hdvd := w172_orderOf_two_dvd_finrank_sub hp hp2 (hexp g hgA) (w172X A K) hyM hfix
  have hpos : 0 < Module.finrank (ZMod 2) (w172X A K) := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) (w172X A K)) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hX
    · exact h
  exact Nat.le_of_dvd hpos hdvd

theorem w172_exists_hyp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (LGL 2 W)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ p = 1) {z : LGL 2 W}
    (hzA : z ∈ A) (hz1 : z ≠ 1) : ∃ K : Subgroup (LGL 2 W), W172Hyp p A K ∧ z ∉ K ∧
      w172X A K ≠ ⊥ := by
  obtain ⟨K, hKA, hKidx, hzK, hX⟩ := w172_exists_hyp_aux hp hp2 hcomm hexp hzA hz1
  exact ⟨K, ⟨hKA, hKidx⟩, hzK, hX⟩

theorem w172_X_le_commSub_of_not_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K : Subgroup (LGL 2 W)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hK : W172Hyp p A K) {y : LGL 2 W} (hyA : y ∈ A) (hyK : y ∉ K) :
    w172X A K ≤ commSub (zpowers y) := by
  intro w hw
  let f : W →ₗ[ZMod 2] W := (y : LGL 2 W).toLinearMap - LinearMap.id
  have hM : ∀ x ∈ w172X A K, f x ∈ w172X A K := by
    intro x hx
    have hyx : y x ∈ w172X A K :=
      w172_map_X hK.1 (fun a ha => hcomm y hyA a ha) hx
    have hsub : y x - x ∈ w172X A K := Submodule.sub_mem _ hyx hx
    have hfx : f x = y x - x := rfl
    exact hfx ▸ hsub
  have hinj : Set.InjOn f (w172X A K) := by
    intro u hu v hv huv
    have h0 : f (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hdiff : u - v ∈ w172X A K := Submodule.sub_mem _ hu hv
    have hfix : y (u - v) = u - v := by
      have h2 := h0
      simp only [f, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
      exact h2
    have hz := w172_fixed_eq_zero hp hp2 hcomm hexp hK hyA hyK hdiff hfix
    exact sub_eq_zero.mp hz
  have hsurj : Set.SurjOn f (w172X A K) (w172X A K) :=
    (LinearMap.injOn_iff_surjOn (p := w172X A K) (f := f) hM).mp hinj
  obtain ⟨u, hu, hfu⟩ := hsurj hw
  have hwu : w = y u - u := by
    rw [← hfu]
    rfl
  rw [hwu]
  exact sub_mem_commSub (Subgroup.zpowers y) (Subgroup.mem_zpowers y) u

theorem w172_X_fixed_eq_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A K : Subgroup (LGL 2 W)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hK : W172Hyp p A K) {g : LGL 2 W} (hgA : g ∈ A) (hgK : g ∉ K) {w : W}
    (hw : w ∈ w172X A K) (hgw : g w = w) : w = 0 :=
  w172_fixed_eq_zero hp hp2 hcomm hexp hK hgA hgK hw hgw

theorem w172_map_X_of_commute {A K : Subgroup (LGL 2 W)} (hKA : K ≤ A) {g : LGL 2 W}
    (hg : ∀ a ∈ A, g * a = a * g) {w : W} (hw : w ∈ w172X A K) : g w ∈ w172X A K :=
  w172_map_X hKA hg hw

end CFSG.LocalAnalysis.WeakClosure81

end
