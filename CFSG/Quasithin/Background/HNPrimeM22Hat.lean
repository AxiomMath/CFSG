module

public import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.Background.HMathieuM21

public section

namespace CFSG.Quasithin.H.M22HatN

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.NPrimeHall CFSG.Quasithin.H13.A5.M22Hat
open CFSG.Quasithin.E3

variable {K : Type} [Field K] [Finite K] {Γ₀ : Subgroup (GL (Fin 6) K)}

omit [Finite K] in
theorem card_fixV_eq (y : MulAut (StdMod (Fin 6) K)) :
    Nat.card ↥(fixV (Subgroup.zpowers y)) = Nat.card {w // y w = w} :=
  Nat.card_congr ⟨fun w => ⟨w.1, mem_fixV_zpowers_iff.mp w.2⟩,
    fun w => ⟨w.1, mem_fixV_zpowers_iff.mpr w.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem card_subgroup_stdMod (hK : Nat.card K = 4) (U : Subgroup (StdMod (Fin 6) K)) :
    ∃ j ≤ 12, Nat.card U = 2 ^ j := by
  have h := Subgroup.card_dvd_of_le (le_top : U ≤ ⊤)
  rw [Subgroup.card_top, card_stdMod_six hK] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).mp h

theorem card_fixV_eleven (hK : Nat.card K = 4) {g : ↥Γ₀} (hg : orderOf g = 11) :
    Nat.card ↥(fixV (Subgroup.zpowers (natAut Γ₀ g))) = 4 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hord : orderOf (natAut Γ₀ g) = 11 := by
    rw [orderOf_injective _ (natAut_injective Γ₀), hg]
  have hmod := CFSG.Quasithin.H.card_modEq_fix hord
  rw [← card_fixV_eq, card_stdMod_six hK] at hmod
  obtain ⟨j, hj, hjc⟩ := card_subgroup_stdMod hK (fixV (Subgroup.zpowers (natAut Γ₀ g)))
  rw [hjc] at hmod ⊢
  have hne : j ≠ 12 := by
    rintro rfl
    have htop : fixV (Subgroup.zpowers (natAut Γ₀ g)) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hjc, card_stdMod_six hK]
    have h1 : natAut Γ₀ g = 1 := MulEquiv.ext fun w => by
      have : w ∈ fixV (Subgroup.zpowers (natAut Γ₀ g)) := by rw [htop]; trivial
      exact mem_fixV_zpowers_iff.mp this
    have h2 : g = 1 := natAut_injective Γ₀ (h1.trans (map_one _).symm)
    rw [h2, orderOf_one] at hg
    omega
  have : j < 12 := by omega
  interval_cases j <;> simp_all [Nat.ModEq]

section Centralizer

variable (hK : Nat.card K = 4) (hperf : commutator ↥Γ₀ = ⊤)
  (hs : IsSimpleGroup (↥Γ₀ ⧸ Subgroup.center ↥Γ₀))
  (hZ3 : Nat.card (Subgroup.center ↥Γ₀) = 3) {z : ↥Γ₀} (hz : z ∈ Subgroup.center ↥Γ₀)
  (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : ↥Γ₀} (hg : orderOf g = 11)

include hK hperf hs hZ3 hz hz3 hz1 hg in
theorem eq_one_of_commute_fix {d : MulAut (StdMod (Fin 6) K)}
    (hd : ∀ γ : ↥Γ₀, d * natAut Γ₀ γ = natAut Γ₀ γ * d) {w₀ : StdMod (Fin 6) K} (hw₀ : w₀ ≠ 1)
    (hdw : d w₀ = w₀) : d = 1 := by
  classical
  set U := fixV (Subgroup.zpowers d) with hU
  have hcomm : ∀ (γ : ↥Γ₀) (w : StdMod (Fin 6) K), d (natAut Γ₀ γ w) = natAut Γ₀ γ (d w) :=
    fun γ w => congrArg (fun φ : MulAut (StdMod (Fin 6) K) => φ w) (hd γ)
  have hinv : ∀ (γ : ↥Γ₀), ∀ u ∈ U, natAut Γ₀ γ u ∈ U := by
    intro γ u hu
    rw [mem_fixV_zpowers_iff] at hu ⊢
    rw [hcomm, hu]
  have hmove : ∃ u ∈ U, natAut Γ₀ g u ≠ u := by
    by_contra hall
    push Not at hall
    let N : Subgroup ↥Γ₀ :=
      { carrier := {γ | ∀ u ∈ U, natAut Γ₀ γ u = u}
        one_mem' := fun u _ => by simp
        mul_mem' := fun {a b} ha hb u hu => by
          rw [map_mul, MulAut.mul_apply, hb u hu, ha u hu]
        inv_mem' := fun {a} ha u hu => by
          have := ha u hu
          rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq]
          exact this.symm }
    have hNn : N.Normal := ⟨fun a ha b u hu => by
      change natAut Γ₀ (b * a * b⁻¹) u = u
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ha _ (hinv _ u hu)]
      simp [MulAut.inv_apply]⟩
    have hgN : g ∈ N := fun u hu => hall u hu
    have hgZ : g ∉ Subgroup.center ↥Γ₀ := fun hgc => by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Γ₀) hgc
      rw [hg, hZ3] at h
      omega
    have hNtop : N = ⊤ := eq_top_of_not_le_center hperf hs N fun h => hgZ (h hgN)
    have hzN : z ∈ N := by rw [hNtop]; trivial
    have hfix := fixV_natAut_eq_bot hK hperf hz hz3 hz1 hg
    have hw : w₀ ∈ fixV (Subgroup.zpowers (natAut Γ₀ z)) :=
      mem_fixV_zpowers_iff.mpr (hzN w₀ (mem_fixV_zpowers_iff.mpr hdw))
    rw [hfix, Subgroup.mem_bot] at hw
    exact hw₀ hw
  obtain ⟨m, hm, hmc⟩ := card_subgroup_stdMod hK U
  let σ : Equiv.Perm ↥U :=
    { toFun := fun u => ⟨natAut Γ₀ g u, hinv g u u.2⟩
      invFun := fun u => ⟨natAut Γ₀ g⁻¹ u, hinv g⁻¹ u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [MulAut.inv_apply])
      right_inv := fun u => Subtype.ext (by simp [MulAut.inv_apply]) }
  have hσ : σ ^ 11 = 1 := by
    have hg11 : g ^ 11 = 1 := by rw [← hg, pow_orderOf_eq_one]
    ext u
    have key : ∀ k : ℕ, ((σ ^ k) u : StdMod (Fin 6) K) = natAut Γ₀ (g ^ k) u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', map_mul, MulAut.mul_apply, ← ih]
        rfl
    rw [key, hg11, map_one]
    rfl
  have hmod := CFSG.Quasithin.H13.A5.M22Hat.card_modEq_fix σ hσ
  have hfixle : Nat.card {u // σ u = u} ≤ 4 := by
    rw [← card_fixV_eleven hK hg]
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, mem_fixV_zpowers_iff.mpr
      (congrArg Subtype.val u.2)⟩) fun a b h => ?_
    have h' : (a.1.1 : StdMod (Fin 6) K) = b.1.1 := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hfixlt : Nat.card {u // σ u = u} < Nat.card ↥U := by
    obtain ⟨u, hu, hne⟩ := hmove
    have := Fintype.ofFinite ↥U
    have := Fintype.ofFinite {u // σ u = u}
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_of_notMem (fun u => u.1) Subtype.val_injective
      (b := ⟨u, hu⟩) ?_
    rintro ⟨v, hv⟩
    apply hne
    have hv' : (v.1 : StdMod (Fin 6) K) = u := congrArg Subtype.val hv
    rw [← hv']
    exact congrArg Subtype.val v.2
  have hfixcard : ∃ j ≤ 12, Nat.card {u // σ u = u} = 2 ^ j := by
    obtain ⟨j, hj, hjc⟩ := card_subgroup_stdMod hK (U ⊓ fixV (Subgroup.zpowers (natAut Γ₀ g)))
    refine ⟨j, hj, ?_⟩
    rw [← hjc]
    exact Nat.card_congr ⟨fun u => ⟨u.1.1, u.1.2, mem_fixV_zpowers_iff.mpr
        (congrArg Subtype.val u.2)⟩,
      fun u => ⟨⟨u.1, u.2.1⟩, Subtype.ext (mem_fixV_zpowers_iff.mp u.2.2)⟩,
      fun _ => rfl, fun _ => rfl⟩
  obtain ⟨j, hj, hjc⟩ := hfixcard
  rw [hmc, hjc] at hmod
  rw [hjc] at hfixle hfixlt
  rw [hmc] at hfixlt
  have hj2 : j ≤ 2 := by
    by_contra hj2
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjm : j < m := by
    by_contra hjm
    have : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm10 : 10 ≤ m := by
    interval_cases j <;> interval_cases m <;> simp_all [Nat.ModEq]
  have hrk : rkIdx U ≤ 2 := by
    have h1 := U.card_mul_index
    rw [hmc, card_stdMod_six hK] at h1
    have h2 : U.index = 2 ^ (12 - m) := by
      have h3 : 2 ^ 12 = 2 ^ m * 2 ^ (12 - m) := by rw [← pow_add]; congr 1; omega
      rw [h3] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [rkIdx_of_index h2]
    omega
  exact eq_one_of_commute hK hperf hs hZ3 hz hz3 hz1 hg hd hrk

include hK hperf hs hZ3 hz hz3 hz1 hg in
theorem mem_center_of_commute {c : MulAut (StdMod (Fin 6) K)}
    (hc : ∀ γ : ↥Γ₀, c * natAut Γ₀ γ = natAut Γ₀ γ * c) :
    ∃ i : ℕ, c = natAut Γ₀ (z ^ i) := by
  classical
  set W := fixV (Subgroup.zpowers (natAut Γ₀ g)) with hW
  set ζ := natAut Γ₀ z with hζ
  have hWcard : Nat.card W = 4 := card_fixV_eleven hK hg
  have hζg : ζ * natAut Γ₀ g = natAut Γ₀ g * ζ := by
    rw [hζ, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g).symm]
  have hcg := hc g
  have hpres : ∀ y : MulAut (StdMod (Fin 6) K), y * natAut Γ₀ g = natAut Γ₀ g * y →
      ∀ w ∈ W, y w ∈ W := by
    intro y hy w hw
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have := congrArg (fun φ : MulAut (StdMod (Fin 6) K) => φ w) hy
    simp only [MulAut.mul_apply, hw] at this
    exact this.symm
  have hfix := fixV_natAut_eq_bot hK hperf hz hz3 hz1 hg
  have hζfix : ∀ w : StdMod (Fin 6) K, ζ w = w → w = 1 := fun w hw => by
    have : w ∈ fixV (Subgroup.zpowers ζ) := mem_fixV_zpowers_iff.mpr hw
    rwa [hfix, Subgroup.mem_bot] at this
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← map_pow, hz3, map_one]
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w₁, hw₁⟩ := exists_ne (1 : ↥W)
  have hw₁' : (w₁ : StdMod (Fin 6) K) ≠ 1 := fun h => hw₁ (Subtype.ext h)
  set a := (w₁ : StdMod (Fin 6) K)
  have ha1 : ζ a ≠ a := fun h => hw₁' (hζfix a h)
  have ha2 : ζ (ζ a) ≠ a := by
    intro h
    apply ha1
    have h3 : ζ (ζ (ζ a)) = a := by
      have := congrArg (fun φ : MulAut (StdMod (Fin 6) K) => φ a) hζ3
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [h] at h3
    exact h3
  have ha3 : ζ (ζ a) ≠ ζ a := fun h => ha1 (ζ.injective h)
  have hca : c a ≠ 1 := fun h => hw₁' (c.injective (h.trans (map_one c).symm))
  have hmem : c a = a ∨ c a = ζ a ∨ c a = ζ (ζ a) := by
    have hζa1 : ζ a ≠ 1 := fun h => hw₁' (ζ.injective (h.trans (map_one ζ).symm))
    have hζζa1 : ζ (ζ a) ≠ 1 := fun h => hζa1 (ζ.injective (h.trans (map_one ζ).symm))
    let F : Finset ↥W := {1, w₁, ⟨ζ a, hpres ζ hζg a w₁.2⟩,
      ⟨ζ (ζ a), hpres ζ hζg _ (hpres ζ hζg a w₁.2)⟩}
    have hF : F.card = 4 := by
      have e1 : (1 : ↥W) ∉ ({w₁, ⟨ζ a, hpres ζ hζg a w₁.2⟩,
          ⟨ζ (ζ a), hpres ζ hζg _ (hpres ζ hζg a w₁.2)⟩} : Finset ↥W) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hw₁ h.symm, fun h => hζa1 (congrArg Subtype.val h).symm,
          fun h => hζζa1 (congrArg Subtype.val h).symm⟩
      have e2 : w₁ ∉ ({⟨ζ a, hpres ζ hζg a w₁.2⟩,
          ⟨ζ (ζ a), hpres ζ hζg _ (hpres ζ hζg a w₁.2)⟩} : Finset ↥W) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
          fun h => ha2 (congrArg Subtype.val h).symm⟩
      have e3 : (⟨ζ a, hpres ζ hζg a w₁.2⟩ : ↥W) ≠
          ⟨ζ (ζ a), hpres ζ hζg _ (hpres ζ hζg a w₁.2)⟩ :=
        fun h => ha3 (congrArg Subtype.val h).symm
      simp only [F]
      rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
        Finset.card_pair e3]
    have := Fintype.ofFinite ↥W
    have hFu : F = Finset.univ := Finset.eq_univ_of_card F (by
      rw [hF, ← Nat.card_eq_fintype_card, hWcard])
    have hmemF : (⟨c a, hpres c hcg a w₁.2⟩ : ↥W) ∈ F := hFu ▸ Finset.mem_univ _
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hmemF
    rcases hmemF with h | h | h | h
    · exact absurd (congrArg Subtype.val h) hca
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hcommζ : ∀ (i : ℕ) (γ : ↥Γ₀),
      (ζ ^ i)⁻¹ * c * natAut Γ₀ γ = natAut Γ₀ γ * ((ζ ^ i)⁻¹ * c) := by
    intro i γ
    have hz' : ζ ^ i * natAut Γ₀ γ = natAut Γ₀ γ * ζ ^ i := by
      rw [hζ, ← map_pow, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp
        (Subgroup.pow_mem _ hz i) γ).symm]
    have hz'' : (ζ ^ i)⁻¹ * natAut Γ₀ γ = natAut Γ₀ γ * (ζ ^ i)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hz', mul_assoc, mul_inv_cancel, mul_one]
    rw [mul_assoc, hc γ, ← mul_assoc, hz'', mul_assoc]
  have key : ∀ i : ℕ, c a = (ζ ^ i) a → c = natAut Γ₀ (z ^ i) := by
    intro i hi
    have hd := eq_one_of_commute_fix hK hperf hs hZ3 hz hz3 hz1 hg (hcommζ i) hw₁' (by
      rw [MulAut.mul_apply, hi, MulAut.inv_apply, MulEquiv.symm_apply_apply])
    rw [hζ, ← map_pow] at hd
    exact (inv_mul_eq_one.mp hd).symm
  rcases hmem with h | h | h
  · exact ⟨0, key 0 (by rw [h]; rfl)⟩
  · exact ⟨1, key 1 (by rw [h, pow_one])⟩
  · exact ⟨2, key 2 (by rw [h, pow_two, MulAut.mul_apply])⟩

end Centralizer

theorem sq_mem_mog22
    {s : Equiv.Perm (Fin 24)} (hs : s ∈ mog22plus) : s ^ 2 ∈ mog22 := by
  have hle : mog22 ≤ mog22plus := mog22_le_mog22plus
  have hN : mog22plus ≤ Subgroup.normalizer (mog22 : Set (Equiv.Perm (Fin 24))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => mog22_normal_in_plus hx hy
    · intro hy
      have := mog22_normal_in_plus (mog22plus.inv_mem hx) hy
      simpa [mul_assoc] using this
  have hi : mog22.relIndex mog22plus ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := mog22) (K := mog22plus)
    rw [inf_of_le_left hle, card_mog22, card_mog22plus] at h
    omega
  exact sq_mem_of_relIndex_le_two hle hN hi s hs

variable (hK : Nat.card K = 4) (hHat : IsHat ↥Γ₀ ↥CFSG.Open.quasithinM22)

include hK hHat in
theorem sq_mem_natImage
    {x : MulAut (StdMod (Fin 6) K)} (hx : x ∈ natNorm Γ₀) : x ^ 2 ∈ natImage Γ₀ := by
  classical
  obtain ⟨⟨hperf', hs, -⟩, hZ3, ⟨e⟩⟩ := hHat
  have hperf : commutator ↥Γ₀ = ⊤ := hperf'.commutator_eq_top
  have : Nontrivial ↥(Subgroup.center ↥Γ₀) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Γ₀))
  have hz3 : (z : ↥Γ₀) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥Γ₀)) (x := z)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hz1' : (z : ↥Γ₀) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcard : Nat.card ↥Γ₀ = 3 * 443520 := by
    have h1 := (Subgroup.center ↥Γ₀).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr e.toEquiv, hZ3] at h1
    have h2 : Nat.card ↥CFSG.Open.quasithinM22 = 443520 := CFSG.Sporadic.Schreier.m22_card
    rw [h2] at h1
    omega
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 11 (by rw [hcard]; norm_num)
  set α := conjHom Γ₀ ⟨x, hx⟩ with hα
  have hαx : ∀ γ, natAut Γ₀ (α γ) = x * natAut Γ₀ γ * x⁻¹ := natAut_conjHom Γ₀ ⟨x, hx⟩
  let e' : ↥Γ₀ ⧸ Subgroup.center ↥Γ₀ ≃* ↥mog22 := e.trans mog22EquivM22.symm
  let π : ↥Γ₀ →* ↥mog22 := e'.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  let β : MulAut ↥mog22 := e'.symm.trans ((QuotientGroup.congr (Subgroup.center ↥Γ₀)
    (Subgroup.center ↥Γ₀) α (Subgroup.map_center_eq α)).trans e')
  have hβ : ∀ γ, β (π γ) = π (α γ) := fun γ => by
    change e' (QuotientGroup.congr _ _ α _ (e'.symm (e' (QuotientGroup.mk γ)))) =
      e' (QuotientGroup.mk (α γ))
    rw [MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
  obtain ⟨s, hsβ⟩ := conj22_bijective.2 β
  have hs2 : ((s : Equiv.Perm (Fin 24)) ^ 2) ∈ mog22 := sq_mem_mog22 s.2
  obtain ⟨γ, hγ⟩ := hπ ⟨_, hs2⟩
  have hγs : ((π γ : ↥mog22) : Equiv.Perm (Fin 24)) = (s : Equiv.Perm (Fin 24)) ^ 2 := by
    rw [hγ]
  have hββ : ∀ p : ↥Γ₀, ((π (α (α p)) : ↥mog22) : Equiv.Perm (Fin 24)) =
      (s : Equiv.Perm (Fin 24)) ^ 2 * (π p : Equiv.Perm (Fin 24)) *
        ((s : Equiv.Perm (Fin 24)) ^ 2)⁻¹ := by
    intro p
    rw [← hβ, ← hβ, ← hsβ, coe_conj22, coe_conj22, pow_two]
    group
  have hα2 : ∀ q : ↥Γ₀, α (α q) = γ * q * γ⁻¹ := by
    let α' : MulAut ↥Γ₀ := (α * α) * (MulAut.conj γ)⁻¹
    have hα'q : ∀ q, α' q = α (α (γ⁻¹ * q * γ)) := fun q => by
      simp only [α', MulAut.mul_apply]
      rfl
    have hα' := eq_of_mk_eq hperf α' fun q => by
      apply e'.injective
      change π (α' q) = π q
      rw [hα'q]
      apply Subtype.ext
      rw [hββ, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        hγs]
      group
    intro q
    have h1 := hα' (γ * q * γ⁻¹)
    rw [hα'q] at h1
    simpa [mul_assoc] using h1
  set y : MulAut (StdMod (Fin 6) K) := (natAut Γ₀ γ)⁻¹ * x ^ 2 with hy
  have hyc : ∀ q : ↥Γ₀, y * natAut Γ₀ q = natAut Γ₀ q * y := by
    intro q
    have h1 : natAut Γ₀ (α (α q)) = x ^ 2 * natAut Γ₀ q * (x ^ 2)⁻¹ := by
      rw [hαx, hαx, pow_two]
      group
    rw [hα2, map_mul, map_mul, map_inv] at h1
    rw [hy]
    calc (natAut Γ₀ γ)⁻¹ * x ^ 2 * natAut Γ₀ q =
        (natAut Γ₀ γ)⁻¹ * (x ^ 2 * natAut Γ₀ q * (x ^ 2)⁻¹) * x ^ 2 := by group
      _ = (natAut Γ₀ γ)⁻¹ * (natAut Γ₀ γ * natAut Γ₀ q * (natAut Γ₀ γ)⁻¹) * x ^ 2 := by
          rw [h1]
      _ = natAut Γ₀ q * ((natAut Γ₀ γ)⁻¹ * x ^ 2) := by group
  obtain ⟨i, hi⟩ := mem_center_of_commute hK hperf hs hZ3 z.2 hz3 hz1' hg hyc
  refine ⟨γ * (z : ↥Γ₀) ^ i, ?_⟩
  rw [map_mul, ← hi, hy]
  group

include hK hHat in
theorem nPrime_eq_two
    {X : Subgroup (MulAut (StdMod (Fin 6) K))} (hX1 : natImage Γ₀ ≤ X)
    (hX2 : X ≤ natNorm Γ₀) : nPrime X = 2 := by
  classical
  have hHat' := hHat
  obtain ⟨⟨hperf', hs, -⟩, hZ3, ⟨e⟩⟩ := hHat'
  have : Finite (MulAut (StdMod (Fin 6) K)) := MulEquiv.finite_left
  have hup : nPrime (natImage Γ₀) ≤ 2 := by
    refine nPrime_le_two ?_
    rw [natImage, MonoidHom.range_eq_map]
    refine indexThree_map (natAut_injective Γ₀) ?_
    let π : ↥Γ₀ →* CFSG.Blueprint.NativeSporadic.M22 :=
      e.toMonoidHom.comp (QuotientGroup.mk' _)
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center ↥Γ₀ := by
      ext q
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk q) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact indexThree_of_surjective hπ (by rw [hker, hZ3]) MathieuLat.m22_indexThree
  refine le_antisymm ((nPrime_le_of_normal hX1 (fun x hx => hX2 hx)
    fun x hx => sq_mem_natImage hK hHat (hX2 hx)).trans hup) ?_
  refine two_le_nPrime_of_normal (Z := (Subgroup.center ↥Γ₀).map (natAut Γ₀)) ?_ ?_ ?_
  · exact (Subgroup.map_mono le_top).trans (by rw [← MonoidHom.range_eq_map]; exact hX1)
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have hxN := hX2 hx
    set α := conjHom Γ₀ ⟨x, hxN⟩ with hα
    have hαx : ∀ γ, natAut Γ₀ (α γ) = x * natAut Γ₀ γ * x⁻¹ := natAut_conjHom Γ₀ ⟨x, hxN⟩
    have hαc : ∀ c ∈ Subgroup.center ↥Γ₀, α c ∈ Subgroup.center ↥Γ₀ := fun c hc => by
      rw [← Subgroup.map_center_eq α]
      exact ⟨c, hc, rfl⟩
    have hαc' : ∀ c ∈ Subgroup.center ↥Γ₀, α⁻¹ c ∈ Subgroup.center ↥Γ₀ := fun c hc => by
      rw [← Subgroup.map_center_eq α⁻¹]
      exact ⟨c, hc, rfl⟩
    intro w
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨α c, hαc c hc, hαx c⟩
    · rintro ⟨c, hc, hcw⟩
      refine ⟨α⁻¹ c, hαc' c hc, ?_⟩
      have h1 := hαx (α⁻¹ c)
      rw [MulAut.apply_inv_self, hcw] at h1
      calc natAut Γ₀ (α⁻¹ c) = x⁻¹ * (x * natAut Γ₀ (α⁻¹ c) * x⁻¹) * x := by group
        _ = w := by rw [← h1]; group
  · rw [Subgroup.card_map_of_injective (natAut_injective Γ₀), hZ3]

end CFSG.Quasithin.H.M22HatN
