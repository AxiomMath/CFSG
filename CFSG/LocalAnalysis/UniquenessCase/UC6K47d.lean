module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K47c
public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.RankThree.FFModules (fixSub)
open scoped IsMulCommutative commutatorElement

section Basic

variable {G : Type} [Group G]

theorem exists_generator_uc6 [Finite G] {r : ℕ} (hr : r.Prime) {D : Subgroup G}
    (hD : Nat.card D = r) : ∃ x : G, D = Subgroup.zpowers x ∧ orderOf x = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hnt : ∃ y ∈ D, y ≠ 1 := by
    by_contra h
    push Not at h
    have : D = ⊥ := eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (h y hy)
    rw [this, Subgroup.card_bot] at hD
    exact hr.ne_one hD.symm
  obtain ⟨y, hyD, hy1⟩ := hnt
  have hdvd : orderOf y ∣ r := by
    have := orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D)
    rwa [Subgroup.orderOf_mk, hD] at this
  have hord : orderOf y = r := by
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  refine ⟨y, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyD)
    (by rw [Nat.card_zpowers, hord, hD])).symm, hord⟩

end Basic

section Fix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_fixSub_zpowers_uc6 (ρ : Representation (ZMod 2) G V) (x : G) (v : V) :
    v ∈ fixSub ρ (Subgroup.zpowers x) ↔ ρ x v = v := by
  refine ⟨fun h => h x (Subgroup.mem_zpowers x), fun hx a ha => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  clear ha
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, map_mul, Module.End.mul_apply, hx, ih]
  | pred i ih =>
    have hinv : ρ x⁻¹ v = v := by
      have := congrArg (ρ x⁻¹) hx
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
      simpa using this.symm
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]

theorem eq_of_fixed_uc6 [Finite V] (ρ : Representation (ZMod 2) G V) (D : Subgroup G)
    (hD : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1) (a b : V) (ha : a ≠ 0) (hb : b ≠ 0)
    (haD : a ∈ fixSub ρ D) (hbD : b ∈ fixSub ρ D) : a = b := by
  obtain ⟨v, hv⟩ := _root_.finrank_le_one_iff.1 hD
  obtain ⟨c₁, hc₁⟩ := hv ⟨a, haD⟩
  obtain ⟨c₂, hc₂⟩ := hv ⟨b, hbD⟩
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have ha' : c₁ • (v : V) = a := congrArg Subtype.val hc₁
  have hb' : c₂ • (v : V) = b := congrArg Subtype.val hc₂
  rcases h2 c₁ with h | h
  · exact absurd (by rw [← ha', h, zero_smul]) ha
  rcases h2 c₂ with h' | h'
  · exact absurd (by rw [← hb', h', zero_smul]) hb
  rw [← ha', ← hb', h, h']

end Fix

section One

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem k47_one_uc6 (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (D : Subgroup G) (hD : Nat.card D = r)
    (hfin : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1) (R : Subgroup G) (hRD : D ≤ R) (c : G)
    (hcR : c ∈ R)
    (hc : ∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ (Subgroup.center ↥R).map R.subtype) :
    ∀ d ∈ D, c * d = d * c := by
  obtain ⟨x, hxD, hxord⟩ := exists_generator_uc6 hr hD
  have hxmem : x ∈ D := hxD ▸ Subgroup.mem_zpowers x
  have hcx : c * x = x * c := by
    by_contra hne
    obtain ⟨zR, hzR, hzeq⟩ := hc x hxmem
    have hzeq' : (zR : G) = c * x * c⁻¹ * x⁻¹ := hzeq
    have hzR' : c * x * c⁻¹ * x⁻¹ ∈ R := hzeq' ▸ zR.2
    have hzc : ∀ w ∈ R, w * (c * x * c⁻¹ * x⁻¹) = (c * x * c⁻¹ * x⁻¹) * w := fun w hw => by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzR ⟨w, hw⟩)
      rwa [← hzeq'] at *
    have hxR : x ∈ R := hRD hxmem
    have hzx : (c * x * c⁻¹ * x⁻¹) * x = x * (c * x * c⁻¹ * x⁻¹) := (hzc x hxR).symm
    have hcz : c * (c * x * c⁻¹ * x⁻¹) = (c * x * c⁻¹ * x⁻¹) * c := hzc c hcR
    have hzx' : (c * x * c⁻¹ * x⁻¹) * x = c * x * c⁻¹ := by group
    have hxr : x ^ r = 1 := hxord ▸ pow_orderOf_eq_one x
    have hzr : (c * x * c⁻¹ * x⁻¹) ^ r = 1 := by
      have h1 : ((c * x * c⁻¹ * x⁻¹) * x) ^ r = 1 := by
        rw [hzx', conj_pow, hxr]
        simp
      rw [(show Commute (c * x * c⁻¹ * x⁻¹) x from hzx).mul_pow, hxr, mul_one] at h1
      exact h1
    have hfixD : ∀ a : V, ρ x a = a → a ∈ fixSub ρ D := fun a ha => by
      rw [hxD]
      exact (mem_fixSub_zpowers_uc6 ρ x a).2 ha
    have hf1 : ρ (c * x * c⁻¹ * x⁻¹) = 1 :=
      op47_one_uc6 hr hr2 (ρ (c * x * c⁻¹ * x⁻¹)) (ρ x) (ρ c) (ρ c⁻¹)
        (by rw [← map_mul, ← map_mul, hzx])
        (by rw [← map_mul, ← map_mul, hcz])
        (by rw [← map_mul, mul_inv_cancel, map_one])
        (by rw [← map_mul, inv_mul_cancel, map_one])
        (by rw [← map_mul, ← map_mul, ← map_mul, hzx'])
        (by rw [← map_pow, hzr, map_one])
        (by rw [← map_pow, hxr, map_one])
        (fun a b ha hb hga hgb =>
          eq_of_fixed_uc6 ρ D hfin a b ha hb (hfixD a hga) (hfixD b hgb))
    have hz1 : c * x * c⁻¹ * x⁻¹ = 1 := hρ (by rw [hf1, map_one])
    apply hne
    have : c * x = x * c := by
      calc c * x = (c * x * c⁻¹ * x⁻¹) * (x * c) := by group
        _ = x * c := by rw [hz1, one_mul]
    exact this
  intro d hd
  rw [hxD] at hd
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
  exact (Commute.zpow_right (show Commute c x from hcx) n).eq

theorem fixedPointFree_of_commutator_eq_uc6 {x : G} {D Q : Subgroup G} (hD : D = Subgroup.zpowers x)
    (hQab : IsMulCommutative ↥Q) (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) :
    ∀ y ∈ Q, x * y = y * x → y = 1 := by
  have hx0 : x ∈ D := hD ▸ Subgroup.mem_zpowers x
  have hconj : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun q hq =>
    (mem_normalizer_iff.1 (hDQ hx0) q).1 hq
  have hcommQ : ∀ q : ↥Q, x * (q : G) * x⁻¹ * (q : G)⁻¹ ∈ Q := fun q =>
    Q.mul_mem (hconj q q.2) (Q.inv_mem q.2)
  let f : ↥Q → ↥Q := fun q => ⟨x * (q : G) * x⁻¹ * (q : G)⁻¹, hcommQ q⟩
  have hf_mul : ∀ a b : ↥Q, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    show x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
      (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
    have hc : (a : G) * (x * (b : G) * x⁻¹ * (b : G)⁻¹) =
        (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G) :=
      congrArg Subtype.val (hQab.is_comm.comm a ⟨_, hcommQ b⟩)
    have hc' : (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹) := by
      calc (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹
          = (a : G)⁻¹ * ((a : G) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) * (a : G)⁻¹ := by group
        _ = (a : G)⁻¹ * ((x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)) * (a : G)⁻¹ := by rw [hc]
        _ = (a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹) := by group
    calc x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹
        = (x * (a : G) * x⁻¹) * ((x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (x * (a : G) * x⁻¹) * ((a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) := by rw [hc']
      _ = _ := by group
  let fh : ↥Q →* ↥Q := MonoidHom.mk' f hf_mul
  let Rg : Subgroup G := fh.range.map Q.subtype
  have hnat : ∀ k : ℕ, ∀ y ∈ Q, ⁅x ^ k, y⁆ ∈ Rg := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have hxk : x ^ k ∈ D := hD ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k
      have hyk : x ^ k * y * (x ^ k)⁻¹ ∈ Q := (mem_normalizer_iff.1 (hDQ hxk) y).1 hy
      have h1 : ⁅x ^ (k + 1), y⁆ = ⁅x, x ^ k * y * (x ^ k)⁻¹⁆ * ⁅x ^ k, y⁆ := by
        simp only [commutatorElement_def, pow_succ]
        group
      rw [h1]
      refine Rg.mul_mem ⟨fh ⟨_, hyk⟩, ⟨⟨_, hyk⟩, rfl⟩, rfl⟩ (ih y hy)
  have hle : ⁅D, Q⁆ ≤ Rg := by
    rw [Subgroup.commutator_le]
    intro d hd y hy
    classical
    rw [hD, mem_zpowers_iff_mem_range_orderOf] at hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hd
    exact hnat k y hy
  have hsurj : Function.Surjective fh := by
    intro q
    have hq : (q : G) ∈ Rg := (le_of_eq hcomm.symm |>.trans hle) q.2
    obtain ⟨_, ⟨q', rfl⟩, hq'⟩ := hq
    exact ⟨q', Subtype.ext hq'⟩
  have hinj : Function.Injective fh := Finite.injective_iff_surjective.2 hsurj
  intro y hy hxy
  have h1 : fh ⟨y, hy⟩ = fh 1 := by
    apply Subtype.ext
    show x * y * x⁻¹ * y⁻¹ = x * (1 : G) * x⁻¹ * (1 : G)⁻¹
    rw [hxy]
    group
  exact congrArg Subtype.val (hinj h1)

theorem k47_two_uc6 (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {q r : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq2 : q ≠ 2) (D : Subgroup G) (hD : Nat.card D = r)
    (hfin : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1) (Q : Subgroup G) (hQp : IsPGroup q Q)
    (hQab : IsMulCommutative ↥Q) (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) :
    IsCyclic ↥Q := by
  by_contra hnc
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (IsPGroup q ↥Q) := ⟨hQp⟩
  obtain ⟨x, hxD, hxord⟩ := exists_generator_uc6 hr hD
  have hx0 : x ∈ D := hxD ▸ Subgroup.mem_zpowers x
  have hfpf := fixedPointFree_of_commutator_eq_uc6 hxD hQab hDQ hcomm
  have hEQ : omegaCenter q Q ≤ Q := omegaCenter_le q Q
  have hxN : x ∈ normalizer (omegaCenter q Q : Set G) :=
    normalizer_le_normalizer_omegaCenter q Q (hDQ hx0)
  haveI hEab : IsMulCommutative ↥(omegaCenter q Q) := (isElemAbelian_omegaCenter q Q).1
  letI : CommGroup ↥(omegaCenter q Q) := IsMulCommutative.instCommGroup
  have hbig : q < Nat.card ↥(omegaCenter q Q) := by
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := ↥Q) (p := q) hq2 hnc
    haveI := hSel
    have hS : S.map Q.subtype ≤ omegaCenter q Q := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s.2, ?_, fun y hy => ?_⟩
      · have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := q) (A := S) s hs
        have := congrArg Subtype.val h
        simpa using this
      · exact congrArg Subtype.val (hQab.is_comm.comm s ⟨y, hy⟩)
    have h1 : Nat.card (S.map Q.subtype) = q ^ 2 := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hScard]
    have h2 := Subgroup.card_le_of_le hS
    rw [h1] at h2
    exact lt_of_lt_of_le (by nlinarith [hq.one_lt]) h2
  have hodd : Odd (Nat.card ↥(omegaCenter q Q)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hQp.to_le hEQ)
    rw [hn]
    exact (hq.odd_of_ne_two hq2).pow
  have hxr : x ^ r = 1 := hxord ▸ pow_orderOf_eq_one x
  let σ : Representation (ZMod 2) ↥(omegaCenter q Q) V := ρ.comp (omegaCenter q Q).subtype
  let α : MulAut ↥(omegaCenter q Q) := (omegaCenter q Q).normalizerMonoidHom ⟨x, hxN⟩
  have hαe : ∀ e : ↥(omegaCenter q Q), ((α e : ↥(omegaCenter q Q)) : G) = x * (e : G) * x⁻¹ :=
    fun e => rfl
  have hαr : α ^ r = 1 := by
    have h1 : (⟨x, hxN⟩ : normalizer (omegaCenter q Q : Set G)) ^ r = 1 :=
      Subtype.ext (by simpa using hxr)
    rw [show α = (omegaCenter q Q).normalizerMonoidHom ⟨x, hxN⟩ from rfl, ← map_pow, h1, map_one]
  have hfixD : ∀ a : V, ρ x a = a → a ∈ fixSub ρ D := fun a ha => by
    rw [hxD]
    exact (mem_fixSub_zpowers_uc6 ρ x a).2 ha
  obtain ⟨a, b, ha0, hb0, hab, hTa, hTb⟩ :=
    exists_two_fixed_core_uc6 (E := ↥(omegaCenter q Q)) σ
      (hρ.comp (omegaCenter q Q).subtype_injective) hq hq2
      (fun e => Subtype.ext (by simpa using (isElemAbelian_omegaCenter q Q).2 (e : G) e.2))
      hodd hbig hr (ρ x) (by rw [← map_pow, hxr, map_one]) α hαr
      (fun e => by
        show ρ x * ρ (e : G) = ρ ((α e : ↥(omegaCenter q Q)) : G) * ρ x
        rw [hαe, ← map_mul, ← map_mul]
        congr 1
        group)
      (fun e he => by
        have h1 : x * (e : G) * x⁻¹ = (e : G) := by
          have := congrArg Subtype.val he
          rwa [hαe] at this
        have h2 : x * (e : G) = (e : G) * x := by
          calc x * (e : G) = (x * (e : G) * x⁻¹) * x := by group
            _ = (e : G) * x := by rw [h1]
        exact Subtype.ext (hfpf e (hEQ e.2) h2))
  exact hab (eq_of_fixed_uc6 ρ D hfin a b ha0 hb0 (hfixD a hTa) (hfixD b hTb))

end One

theorem k47_uc6 : UCK.K47 := by
  intro G _ _ _ V _ _ _ ρ hρ q r hq hr hq2 hr2 _ D hDcard hfin
  exact ⟨fun R _ hDR c hcR hc d hd => k47_one_uc6 ρ hρ hr hr2 D hDcard hfin R hDR c hcR hc d hd,
    fun Q hQp hQab hDQ hcomm => k47_two_uc6 ρ hρ hq hr hq2 D hDcard hfin Q hQp hQab hDQ hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
