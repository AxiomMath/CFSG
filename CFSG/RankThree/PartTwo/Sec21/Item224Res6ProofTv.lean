module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open CFSG.LieType.BorelTits

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def tv (F : ReflForm K V) (a : V) : V →ₗ[K] V where
  toFun v := v + F.β a v • a
  map_add' u v := by
    rw [F.add_right, add_smul]
    abel
  map_smul' c v := by
    rw [F.smul_right, smul_add, mul_smul]
    rfl

theorem tv_apply (F : ReflForm K V) (a v : V) : tv F a v = v + F.β a v • a :=
  rfl

theorem tv_tv_apply (F : ReflForm K V) (a b v : V) :
    tv F a (tv F b v) = v + F.β b v • b + (F.β a v + F.β b v * F.β a b) • a := by
  rw [tv_apply, tv_apply, F.add_right, F.smul_right, add_smul]

variable [CharP K 2]

omit [AddCommGroup V] [Module K V] in
theorem two_eq_zero' : (2 : K) = 0 :=
  CharTwo.two_eq_zero

theorem add_self_smul' (c : K) (v : V) : c • v + c • v = 0 := by
  rw [← add_smul, ← two_mul, two_eq_zero', zero_mul, zero_smul]

theorem tv_tv_of_isotropic (F : ReflForm K V) {a : V} (ha : F.β a a = 0) (v : V) :
    tv F a (tv F a v) = v := by
  rw [tv_tv_apply, ha, mul_zero, add_zero, add_assoc, add_self_smul', add_zero]

theorem tv_mul_tv_pow_three (F : ReflForm K V) (hsymm : ∀ u v, F.β v u = F.σ (F.β u v))
    {a e : V} (ha : F.β a a = 0) (he : F.β e e = 0) (hae : F.β a e = 1) :
    (tv F a * tv F e) ^ 3 = 1 := by
  have hea : F.β e a = 1 := by rw [hsymm, hae, map_one]
  have h2 : (2 : K) = 0 := two_eq_zero'
  ext v
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
  set s := F.β a v with hs
  set t := F.β e v with ht
  have h1 : tv F a (tv F e v) = v + t • e + (s + t) • a := by
    rw [tv_tv_apply, hae, mul_one]
  have hb1 : F.β a (v + t • e + (s + t) • a) = s + t := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, hae, ha]
    ring
  have hc1 : F.β e (v + t • e + (s + t) • a) = s := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, he, hea]
    linear_combination t * h2
  have h2' : tv F a (tv F e (v + t • e + (s + t) • a)) = v + (s + t) • e + s • a := by
    rw [tv_tv_apply, hb1, hc1, hae, mul_one]
    match_scalars
    all_goals first | ring1 | linear_combination s * h2 | linear_combination t * h2 |
      linear_combination (s + t) * h2
  have hb2 : F.β a (v + (s + t) • e + s • a) = t := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, hae, ha]
    linear_combination s * h2
  have hc2 : F.β e (v + (s + t) • e + s • a) = s + t := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, he, hea]
    ring
  rw [h1, h2', tv_tv_apply, hb2, hc2, hae, mul_one]
  match_scalars
  all_goals first | ring1 | linear_combination s * h2 | linear_combination t * h2 |
    linear_combination (s + t) * h2

omit [CharP K 2] in
theorem tv_key (F : ReflForm K V) (hsymm : ∀ u v, F.β v u = F.σ (F.β u v)) {a b c : V}
    (ha : F.β a a = 0) (hab : F.β a b = 0) (hac : F.β a c = 0) (hbc : F.β b c = 1) (w : V) :
    tv F a (tv F b (tv F a (tv F c w))) - tv F a (tv F b w) - tv F a (tv F c w) + w =
      F.β c w • b := by
  have hba : F.β b a = 0 := by rw [hsymm, hab, map_zero]
  have hx : tv F a (tv F c w) = w + F.β c w • c + F.β a w • a := by
    rw [tv_tv_apply, hac, mul_zero, add_zero]
  have hbx : F.β b (w + F.β c w • c + F.β a w • a) = F.β b w + F.β c w := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, hbc, hba]
    ring
  have hax : F.β a (w + F.β c w • c + F.β a w • a) = F.β a w := by
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, hac, ha]
    ring
  rw [hx, tv_tv_apply, hbx, hax, hab, mul_zero, add_zero, tv_tv_apply, hab, mul_zero, add_zero]
  match_scalars <;> ring1

theorem subset_of_tv_stable (F : ReflForm K V) (hsymm : ∀ u v, F.β v u = F.σ (F.β u v))
    (W₀ : Set V) (hiso : ∀ a ∈ W₀, F.β a a = 0) (hadd : ∀ a ∈ W₀, ∀ b ∈ W₀, a + b ∈ W₀)
    (hscale : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c ≠ 0 → ∃ l : K, l • b ∈ W₀ ∧ F.β (l • b) c = 1)
    (hnd : ∀ c ∈ W₀, c ≠ 0 → ∃ b ∈ W₀, F.β b c ≠ 0)
    (hhyp : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c = 1 → ∃ a ∈ W₀, ∃ a' ∈ W₀, F.β a b = 0 ∧
      F.β a c = 0 ∧ F.β a' b = 0 ∧ F.β a' c = 0 ∧ F.β a a' = 1)
    (Y : Submodule K V)
    (hY : ∀ a ∈ W₀, ∀ e ∈ W₀, F.β a e = 1 → ∀ y ∈ Y, tv F a (tv F e y) ∈ Y)
    {w : V} (hw : w ∈ Y) {c : V} (hc : c ∈ W₀) (hcw : F.β c w ≠ 0) : W₀ ⊆ Y := by
  have hprod : ∀ a ∈ W₀, ∀ b ∈ W₀, ∀ e ∈ W₀, F.β a e = 1 → F.β e b = 1 →
      ∀ y ∈ Y, tv F a (tv F b y) ∈ Y := by
    intro a ha b hb e he hae heb y hy
    have hbe : F.β b e = 1 := by
      rw [hsymm, heb, map_one]
    have h1 : tv F e (tv F b y) ∈ Y := hY e he b hb heb y hy
    have h2 := hY a ha e he hae _ h1
    rwa [tv_tv_of_isotropic F (hiso e he)] at h2
  have hA : ∀ b ∈ W₀, F.β b c = 1 → b ∈ Y := by
    intro b hb hbc
    obtain ⟨a, ha, a', ha', hab, hac, ha'b, ha'c, haa'⟩ := hhyp b hb c hc hbc
    have hcb : F.β c b = 1 := by
      rw [hsymm, hbc, map_one]
    have he : a' + c ∈ W₀ := hadd a' ha' c hc
    have he' : a' + b ∈ W₀ := hadd a' ha' b hb
    have hstab_b : ∀ y ∈ Y, tv F a (tv F b y) ∈ Y :=
      hprod a ha b hb (a' + c) he (by rw [F.add_right, haa', hac, add_zero])
        (by rw [F.add_left, ha'b, hcb, zero_add])
    have hstab_c : ∀ y ∈ Y, tv F a (tv F c y) ∈ Y :=
      hprod a ha c hc (a' + b) he' (by rw [F.add_right, haa', hab, add_zero])
        (by rw [F.add_left, ha'c, hbc, zero_add])
    have hmem : F.β c w • b ∈ Y := by
      rw [← tv_key F hsymm (hiso a ha) hab hac hbc w]
      refine add_mem (sub_mem (sub_mem (hstab_b _ (hstab_c w hw)) (hstab_b w hw))
        (hstab_c w hw)) hw
    have := Y.smul_mem (F.β c w)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hcw, one_smul] at this
  intro b' hb'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcw (F.β_zero_left w)
  by_cases hb'c : F.β b' c = 0
  · obtain ⟨b₀, hb₀, hb₀c⟩ := hnd c hc hc0
    obtain ⟨l, hl, hlc⟩ := hscale b₀ hb₀ c hc hb₀c
    have h1 : l • b₀ ∈ Y := hA _ hl hlc
    have h2 : b' + l • b₀ ∈ Y := hA _ (hadd b' hb' _ hl) (by rw [F.add_left, hb'c, hlc, zero_add])
    have := sub_mem h2 h1
    rwa [add_sub_cancel_right] at this
  · obtain ⟨l, hl, hlc⟩ := hscale b' hb' c hc hb'c
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_smul, F.β_zero_left] at hlc
      exact zero_ne_one hlc
    have := Y.smul_mem l⁻¹ (hA _ hl hlc)
    rwa [smul_smul, inv_mul_cancel₀ hl0, one_smul] at this

theorem eq_bot_of_tv [Finite V] (F : ReflForm K V) (hsymm : ∀ u v, F.β v u = F.σ (F.β u v))
    {H : Type*} [Group H] (ρ : H →* Module.End K V) (hρ : IsIsometric F ρ)
    (hinj : Function.Injective ρ) (R : Subgroup H) (hR : IsPGroup 2 R)
    (W₀ : Set V) (hiso : ∀ a ∈ W₀, F.β a a = 0) (hadd : ∀ a ∈ W₀, ∀ b ∈ W₀, a + b ∈ W₀)
    (hscale : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c ≠ 0 → ∃ l : K, l • b ∈ W₀ ∧ F.β (l • b) c = 1)
    (hnd : ∀ c ∈ W₀, c ≠ 0 → ∃ b ∈ W₀, F.β b c ≠ 0)
    (hhyp : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c = 1 → ∃ a ∈ W₀, ∃ a' ∈ W₀, F.β a b = 0 ∧
      F.β a c = 0 ∧ F.β a' b = 0 ∧ F.β a' c = 0 ∧ F.β a a' = 1)
    (hpair : ∃ b ∈ W₀, ∃ c ∈ W₀, F.β b c ≠ 0)
    (hN : ∀ a ∈ W₀, ∀ e ∈ W₀, F.β a e = 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set H), ρ g = tv F a * tv F e)
    (hperp : ∀ w : V, w ≠ 0 → (∀ c ∈ W₀, F.β c w = 0) → F.β w w ≠ 0) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hR1
  set Y := isoSeq F ρ R 1 with hYdef
  have hYne : Y ≠ ⊥ := isoSeq_one_ne_bot F ρ 2 hρ hinj R hR hR1
  have hYiso : F.IsTotallyIsotropic Y := isoSeq_isTotallyIsotropic F ρ R 1
  have hYstab : ∀ a ∈ W₀, ∀ e ∈ W₀, F.β a e = 1 → ∀ y ∈ Y, tv F a (tv F e y) ∈ Y := by
    intro a ha e he hae y hy
    obtain ⟨g, hg, hρg⟩ := hN a ha e he hae
    have := apply_mem_isoSeq F ρ hρ R 1 hg hy
    rwa [hρg, Module.End.mul_apply] at this
  obtain ⟨w, hwY, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hYne
  have hww : F.β w w = 0 := hYiso hwY w hwY
  by_cases hex : ∃ c ∈ W₀, F.β c w ≠ 0
  · obtain ⟨c, hc, hcw⟩ := hex
    have hsub := subset_of_tv_stable F hsymm W₀ hiso hadd hscale hnd hhyp Y hYstab hwY hc hcw
    obtain ⟨b, hb, c', hc', hbc'⟩ := hpair
    exact hbc' (hYiso (hsub hc') b (hsub hb))
  · push Not at hex
    exact hperp w hw0 hex hww

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
