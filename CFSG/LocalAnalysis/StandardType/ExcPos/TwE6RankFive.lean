module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankTorus
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
import CFSG.LocalAnalysis.StandardType.GGTableBRank

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed
  CFSG.LieType.Chevalley.ExceptionalCover TwE6Lang

private theorem torsion_image_card {C X : Type*} [CommGroup C] [Finite C] [Group X]
    (F : C →* X) (hK : F.ker ≤ (powMonoidHom 3 : C →* C).range) :
    ∃ E : Subgroup X, E ≤ F.range ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card (powMonoidHom 3 : C →* C).ker := by
  let P := (F.comp (powMonoidHom 3 : C →* C)).ker
  let π : P →* F.ker :=
    { toFun := fun c => ⟨(c : C) ^ 3, c.2⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [mul_pow] }
  have hπ : Function.Surjective π := by
    intro k
    obtain ⟨c, hc⟩ := hK k.2
    change c ^ 3 = (k : C) at hc
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    change F (c ^ 3) = 1
    rw [hc]
    exact k.2
  let e : π.ker ≃ (powMonoidHom 3 : C →* C).ker :=
    { toFun := fun c => ⟨((c : P) : C), congrArg Subtype.val c.2⟩
      invFun := fun c => ⟨⟨c, by
        change F ((c : C) ^ 3) = 1
        rw [show (c : C) ^ 3 = 1 from c.2, map_one]⟩,
        Subtype.ext c.2⟩
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl }
  have hPcard : Nat.card P =
      Nat.card (powMonoidHom 3 : C →* C).ker * Nat.card F.ker := by
    rw [← Subgroup.card_ker_mul_card_range π, π.range_eq_top.2 hπ,
      Subgroup.card_top, Nat.card_congr e]
  have hKP : F.ker ≤ P := by
    intro c hc
    change F (c ^ 3) = 1
    rw [map_pow, show F c = 1 from hc, one_pow]
  have hmap : Nat.card (P.map F) * Nat.card F.ker = Nat.card P := by
    have h := Subgroup.card_mul_index (F.ker.subgroupOf P)
    change Nat.card (F.ker.subgroupOf P) * F.ker.relIndex P = Nat.card P at h
    rw [Subgroup.relIndex_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv] at h
    exact (mul_comm _ _).trans h
  refine ⟨P.map F, Subgroup.map_le_range _ _, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨c, -, hc⟩ := a.2
      obtain ⟨d, -, hd⟩ := b.2
      apply Subtype.ext
      change (a : X) * b = (b : X) * a
      rw [← hc, ← hd, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨c, hc, rfl⟩
      rw [← map_pow]
      exact hc
  · exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card F.ker)
      (hmap.trans hPcard)

private def leviCoords {Z : Type*} [CommGroup Z] : (Fin 5 → Z) →* (Fin (Tag.rank .E6) → Z) :=
  { toFun := fun w => ![w 0, w 1, w 2, w 1 ^ 2, w 3, w 4]
    map_one' := by
      funext i
      change (![1, 1, 1, (1 : Z) ^ 2, 1, 1] : Fin 6 → Z) i = 1
      fin_cases i <;> simp
    map_mul' := by
      intro a b
      funext i
      change (![a 0 * b 0, a 1 * b 1, a 2 * b 2, (a 1 * b 1) ^ 2,
        a 3 * b 3, a 4 * b 4] : Fin 6 → Z) i =
        (![a 0, a 1, a 2, a 1 ^ 2, a 3, a 4] : Fin 6 → Z) i *
        (![b 0, b 1, b 2, b 1 ^ 2, b 3, b 4] : Fin 6 → Z) i
      fin_cases i <;> simp [mul_pow] }

private theorem leviCoords_injective {Z : Type*} [CommGroup Z] :
    Function.Injective (leviCoords : (Fin 5 → Z) →* _) := by
  intro a b h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 4
  · exact congrFun h 5

private theorem leviCoords_mem {k : Type*} [Field k] (ζ : kˣ)
    (w : Fin 5 → Subgroup.zpowers ζ) : leviCoords w ∈ sCond ζ := by
  rw [mem_sCond]
  rfl

private theorem card_cube_ker {k : Type*} [Field k] {ζ : kˣ} (hζ : orderOf ζ = 9) :
    Nat.card (powMonoidHom 3 : (Fin 5 → Subgroup.zpowers ζ) →* _).ker = 3 ^ 5 := by
  have : Finite (Subgroup.zpowers ζ) :=
    finite_zpowers.mpr (by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨9, by norm_num, hζ ▸ pow_orderOf_eq_one ζ⟩)
  let e : (powMonoidHom 3 : (Fin 5 → Subgroup.zpowers ζ) →* _).ker ≃
      (Fin 5 → (powMonoidHom 3 : Subgroup.zpowers ζ →* _).ker) :=
    { toFun := fun w i => ⟨(w : Fin 5 → Subgroup.zpowers ζ) i, congrFun w.2 i⟩
      invFun := fun w => ⟨fun i => w i, funext fun i => (w i).2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  rw [Nat.card_congr e, Nat.card_fun, IsCyclic.card_powMonoidHom_ker,
    Nat.card_zpowers, hζ]
  norm_num

private theorem scalar_cube_lift {k : Type} [Field k] {ζ v : kˣ}
    (hζ9 : orderOf ζ = 9) (hv3 : v ^ 3 = 1) :
    ∃ a : Subgroup.zpowers ζ, (a : kˣ) ^ 3 = v := by
  have hprim : IsPrimitiveRoot (ζ ^ 3) 3 :=
    (IsPrimitiveRoot.iff_orderOf.mpr hζ9).pow (by norm_num) (by norm_num)
  have hvpow : v ∈ Subgroup.zpowers (ζ ^ 3) := by
    rw [hprim.zpowers_eq]
    exact (mem_rootsOfUnity _ _).2 hv3
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hvpow
  let a : Subgroup.zpowers ζ := ⟨ζ ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers ζ) i⟩
  have ha : ((a : kˣ) ^ 3) = v := by
    change (ζ ^ i) ^ 3 = v
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    exact hi
  exact ⟨a, ha⟩

private theorem leviCoords_cube_scalar {k : Type} [Field k] {ζ v : kˣ}
    (a : Subgroup.zpowers ζ) (ha : (a : kˣ) ^ 3 = v) :
    (fun j => ((leviCoords (![a, 1, a ^ 2, a, a ^ 2] : Fin 5 → Subgroup.zpowers ζ) j :
      Subgroup.zpowers ζ) : kˣ) ^ 3) =
      tvec (v : kˣ) e6c := by
    funext j
    fin_cases j
    · change (a : kˣ) ^ 3 = (v : kˣ) ^ (1 : ℤ)
      simpa only [zpow_one] using ha
    · change (1 : kˣ) ^ 3 = (v : kˣ) ^ (0 : ℤ)
      simp
    · change ((a : kˣ) ^ 2) ^ 3 = (v : kˣ) ^ (2 : ℤ)
      rw [zpow_two, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, ha, pow_two]
    · change ((1 : kˣ) ^ 2) ^ 3 = (v : kˣ) ^ (0 : ℤ)
      simp
    · change (a : kˣ) ^ 3 = (v : kˣ) ^ (1 : ℤ)
      simpa only [zpow_one] using ha
    · change ((a : kˣ) ^ 2) ^ 3 = (v : kˣ) ^ (2 : ℤ)
      rw [zpow_two, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, ha, pow_two]

section Torus


private def leviHom {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {l : k} (hl : θ l ≠ l) (ζ : kˣ) {m : ℤ}
    (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1) :
    (Fin 5 → Subgroup.zpowers ζ) →* fixedGroup k θ :=
  ((torusConj3 k θ l ζ).comp leviCoords).codRestrict _ fun w =>
    torusConj3_mem_fixedGroup θ hθ hl hζ hm (leviCoords_mem ζ w)

private theorem leviHom_injective {k : Type} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) (ζ : kˣ) {m : ℤ}
    (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1) :
    Function.Injective (leviHom θ hθ hl ζ hζ hm) := by
  intro a b h
  exact leviCoords_injective (torusConj3_injective θ l ζ (congrArg Subtype.val h))

private theorem torusConj3_apply {k : Type} [Field k] (θ : k →+* k) (l : k) (ζ : kˣ)
    (w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ) :
    torusConj3 k θ l ζ w = langG3 k θ l *
      torusHom k (fun j => (w j : kˣ)) * (langG3 k θ l)⁻¹ := by
  rw [torusConj3, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rfl

private theorem center_cube_lift {k : Type} [Field k] [Finite k] {q : ℕ}
    (hk : Nat.card k = q ^ 2) (θ : k →+* k) (hθq : ∀ c, θ c = c ^ q)
    (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) {ζ : kˣ}
    (hζ9 : orderOf ζ = 9) {m : ℤ}
    (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1)
    {z : fixedGroup k θ} (hz : z ∈ Subgroup.center (fixedGroup k θ)) :
    ∃ w : Fin 5 → Subgroup.zpowers ζ, (leviHom θ hθ hl ζ hζ hm w) ^ 3 = z := by
  obtain ⟨v, hv⟩ := centerHom_surjective hk hθq ⟨z, hz⟩
  have hv3 : (v : kˣ) ^ 3 = 1 := ((mem_rootsOfUnity_gcd_iff hθq).1 v.2).1
  obtain ⟨a, ha⟩ := scalar_cube_lift hζ9 hv3
  let w : Fin 5 → Subgroup.zpowers ζ := ![a, 1, a ^ 2, a, a ^ 2]
  have hc := leviCoords_cube_scalar a ha
  refine ⟨w, Subtype.ext ?_⟩
  change (torusConj3 k θ l ζ (leviCoords w)) ^ 3 = (z : e6Data_valid.minGroup k)
  rw [← map_pow]
  rw [torusConj3_apply]
  have hc' : (fun j => (((leviCoords w) ^ 3) j : kˣ)) = tvec (v : kˣ) e6c := hc
  rw [hc']
  have htorus : torusHom k (tvec (v : kˣ) e6c) = (z : e6Data_valid.minGroup k) := by
    have hv' := congrArg (fun y : Subgroup.center (fixedGroup k θ) =>
      ((y : fixedGroup k θ) : e6Data_valid.minGroup k)) hv
    exact hv'
  rw [htorus]
  have hcomm := Subgroup.mem_center_iff.1
    (coe_mem_center_of_mem_center θ hθ hz) (langG3 k θ l)
  rw [hcomm, mul_inv_cancel_right]

private theorem exists_ninth_root {f : ℕ} (hf : 1 ≤ f) (h9 : 9 ∣ 2 ^ f + 1) :
    ∃ ζ : (GaloisField 2 (2 * f))ˣ, orderOf ζ = 9 := by
  obtain ⟨g, hg⟩ := exists_generator hf
  have hd : 9 ∣ orderOf g := by
    rw [hg]
    exact h9.trans (add_one_dvd_sq_sub_one _)
  have hg0 : orderOf g ≠ 0 := by
    rw [hg]
    have h2 : 2 ≤ 2 ^ f := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  exact ⟨g ^ (orderOf g / 9), orderOf_pow_orderOf_div hg0 hd⟩

private theorem central_image_localRank {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 1 ≤ f) (h9 : 9 ∣ 2 ^ f + 1) (ψ : twistedE6Group 2 f →* X)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f)) :
    ∃ U E : Subgroup X, U ≤ ψ.range ∧ E ≤ ψ.range ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set X) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hk : Nat.card k = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f hf
  have hθq : ∀ c, θ c = c ^ (2 ^ f) := frobQ_apply 2 f
  obtain ⟨ζ, hζ9⟩ := exists_ninth_root hf h9
  have : Finite (Subgroup.zpowers ζ) := finite_zpowers.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨9, by norm_num, hζ9 ▸ pow_orderOf_eq_one ζ⟩)
  obtain ⟨l, hl⟩ := exists_frobQ_ne hf
  have hm : ζ ^ ((2 : ℤ) ^ f + 1) = 1 := by
    rw [show ((2 : ℤ) ^ f + 1) = ((2 ^ f + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.1 (hζ9 ▸ h9)
  let τ := leviHom θ hθ hl ζ (units_map_frobQ ζ) hm
  let F := ψ.comp τ
  have hτi : Function.Injective τ := leviHom_injective θ hθ hl ζ (units_map_frobQ ζ) hm
  have hFker : F.ker ≤ (powMonoidHom 3 : (Fin 5 → Subgroup.zpowers ζ) →* _).range := by
    intro c hc
    have hz : τ c ∈ Subgroup.center (fixedGroup k θ) := hker hc
    obtain ⟨w, hw⟩ := center_cube_lift hk θ hθq hθ hl hζ9 (units_map_frobQ ζ) hm hz
    refine ⟨w, ?_⟩
    exact hτi ((map_pow τ w 3).trans hw)
  obtain ⟨E, hEF, hE3, hEcard⟩ := torsion_image_card F hFker
  rw [card_cube_ker hζ9] at hEcard
  let U₀ := (langRootU k θ).subgroupOf (fixedGroup k θ)
  have hU₀ : U₀ ≠ ⊥ := by
    intro hbot
    apply langRootU_ne_bot θ
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hu' : (⟨u, hu.2⟩ : fixedGroup k θ) ∈ U₀ := hu
    rw [hbot, Subgroup.mem_bot] at hu'
    exact congrArg Subtype.val hu'
  have hU₂ : IsPGroup 2 U₀ := (langRootU_isPGroup θ).comap_subtype
  have hZ : Nat.card (Subgroup.center (twistedE6Group 2 f)) = 3 := by
    rw [(card_center_fixedGroup hk hθq).1]
    exact Nat.gcd_eq_left ((by norm_num : 3 ∣ 9).trans h9)
  have hUker : ¬ U₀ ≤ ψ.ker := by
    intro hle
    have hd : Nat.card U₀ ∣ 3 := by
      have hd := Subgroup.card_dvd_of_le (hle.trans hker)
      rwa [hZ] at hd
    rcases IsPGroup.card_eq_or_dvd hU₂ with h1 | h2
    · exact hU₀ (Subgroup.eq_bot_of_card_eq U₀ h1)
    · exact absurd (h2.trans hd) (by norm_num)
  have hτN : τ.range ≤ Subgroup.normalizer (U₀ : Set (twistedE6Group 2 f)) := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe]
    exact Subgroup.mem_set_normalizer_iff.1
      (langTorusE5_le_normalizer θ l ζ
        ⟨leviCoords w, leviCoords_mem ζ w, rfl⟩)
      (y : e6Data_valid.minGroup k)
  refine ⟨U₀.map ψ, E, Subgroup.map_le_range _ _, ?_, ?_, hU₂.map ψ, ?_, hE3, hEcard⟩
  · rintro e he
    obtain ⟨w, hw⟩ := hEF he
    exact ⟨τ w, hw⟩
  · exact fun h => hUker ((Subgroup.map_eq_bot_iff U₀).1 h)
  · intro e he
    obtain ⟨w, hw⟩ := hEF he
    exact Subgroup.le_normalizer_map ψ ⟨τ w, hτN ⟨w, rfl⟩, hw⟩

end Torus


theorem twE6RankFive_holds : TwE6RankFive := by
  intro X _ _ n f ψ G₀ B₁ D J L x hpos h9 A hA
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0] at h9
    norm_num at h9
  let χ : twistedE6Group 2 f →* ↥(A ⊔ G₀) := ψ.codRestrict _ fun c =>
    (le_sup_right : G₀ ≤ A ⊔ G₀) (hpos.1 ▸ (show ψ c ∈ ψ.range from ⟨c, rfl⟩))
  have hχ : χ.ker ≤ Subgroup.center (twistedE6Group 2 f) := by
    intro c hc
    apply hpos.2.1
    exact congrArg Subtype.val hc
  obtain ⟨U, E, -, -, hU, hU2, hEN, hE3, hEc⟩ := central_image_localRank hf h9 χ hχ
  calc 3 ^ 5 = Nat.card E := hEc.symm
    _ ≤ 3 ^ LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) :=
      TableB.card_le_of_twoLocal Nat.prime_three ⟨U, hU, hU2, rfl⟩ hEN hE3
    _ ≤ Nat.card A := hA.2.2.2.2.2.2

end CFSG.StandardType.LieKnownR2.ExcPos
