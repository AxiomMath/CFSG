module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27Group
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporJ3

open CFSG CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open Item434Kit Item434Alt

section Split

variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
theorem e9_split_of_dichotomy
    (hover : ∀ (T : Sylow 3 J) (K : Subgroup J), (T : Subgroup J) ≤ K →
      K ≤ Subgroup.normalizer (T : Set J) ∨ K = ⊤)
    (hfive : ∀ T : Sylow 3 J, ¬ 5 ∣ Nat.card (Subgroup.normalizer (T : Set J)))
    (hdich : ∀ u : J, orderOf u = 3 → IsPGroup 3 (Subgroup.centralizer ({u} : Set J)) ∨
      5 ∣ Nat.card (Subgroup.centralizer ({u} : Set J)))
    {U : Subgroup J} (hU3 : ∀ u ∈ U, u ^ 3 = 1) {z : J} (hzU : z ∈ U) (hz1 : z ≠ 1)
    {T : Sylow 3 J} (hzT : Subgroup.centralizer ({z} : Set J) = (T : Subgroup J)) :
    (∀ u ∈ U, u ≠ 1 → IsPGroup 3 (Subgroup.centralizer ({u} : Set J))) ∨
      (⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set J)) = ⊤ := by
  have hle_u : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set J) ≤
      ⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set J) := fun u hu hu1 =>
    le_iSup₂_of_le u hu (le_iSup (fun _ : u ≠ 1 => Subgroup.centralizer ({u} : Set J)) hu1)
  by_cases hH : (⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set J)) = ⊤
  · exact Or.inr hH
  · left
    have hTH : (T : Subgroup J) ≤ ⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set J) :=
      hzT ▸ hle_u z hzU hz1
    rcases hover T _ hTH with hN | htop
    · intro u hu hu1
      have hu3 : orderOf u = 3 := orderOf_eq_prime (hU3 u hu) hu1
      rcases hdich u hu3 with h | h
      · exact h
      · exfalso
        have hle : Subgroup.centralizer ({u} : Set J) ≤ Subgroup.normalizer (T : Set J) :=
          (hle_u u hu hu1).trans hN
        exact hfive T (h.trans (Subgroup.card_dvd_of_le hle))
    · exact absurd htop hH

end Split

section OuterSetupE9

open CFSG.AGLEmbedding.KFactProofs.J3OuterInv

variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
theorem exists_centralizer_eq {T Z : Subgroup J} {φ : MulAut J} (H : OuterSetup J T Z φ)
    {E : Subgroup J} (hET : E ≤ T) (hE : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ z ∈ E, z ≠ 1 ∧ Subgroup.centralizer ({z} : Set J) = T := by
  obtain ⟨z, hzE, hzZ, hz1⟩ : ∃ z ∈ E, z ∈ Z ∧ z ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨W, hW, hW3, hWc⟩ := exists_elem_mul hE hE3 H.Zcomm H.Z3
      (fun a ha b hb => H.Zc b hb a (hET ha))
      (Subgroup.disjoint_def.2 fun {x} hxE hxZ => hno x hxE hxZ)
    exact H.rank ⟨W, hW, hW3, by rw [hWc, hE9, H.Z9]⟩
  have hTC : T ≤ Subgroup.centralizer ({z} : Set J) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (H.Zc z hzZ x hx)
  refine ⟨z, hzE, hz1, le_antisymm ?_ hTC⟩
  rcases H.overgroup _ hTC with hCN | hCtop
  · exact H.cent z hzZ hz1 hCN
  · exact absurd (H.cen z fun x => Subgroup.mem_centralizer_singleton_iff.1
      (hCtop ▸ Subgroup.mem_top x)) hz1

theorem exists_centralizer_sylow {S : Sylow 3 J} {Z : Subgroup J} {φ : MulAut J}
    (H : OuterSetup J (S : Subgroup J) Z φ) {E : Subgroup J} (hE : IsMulCommutative E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    ∃ z ∈ E, z ≠ 1 ∧ ∃ T : Sylow 3 J, Subgroup.centralizer ({z} : Set J) = (T : Subgroup J) := by
  have hEp : IsPGroup 3 E := fun x => ⟨1, by simpa using Subtype.ext (hE3 x x.2)⟩
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J S' S
  have hSc : (S : Subgroup J) = (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
    have h2 : ((c • S' : Sylow 3 J) : Subgroup J) =
        (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    rw [hc] at h2
    exact h2
  set E' := E.map (MulAut.conj c).toMonoidHom with hE'
  have hE'S : E' ≤ (S : Subgroup J) := hSc ▸ Subgroup.map_mono hS'
  have := hE
  obtain ⟨z', hz'E', hz'1, hz'C⟩ := exists_centralizer_eq H hE'S inferInstance
    (fun y hy => by
      obtain ⟨e, he, rfl⟩ := hy
      change (c * e * c⁻¹) ^ 3 = 1
      rw [conj_pow, hE3 e he]
      group)
    (by rw [hE', Subgroup.card_map_of_injective (MulAut.conj c).injective, hE9])
  obtain ⟨z, hzE, rfl⟩ := hz'E'
  have hz'eq : (MulAut.conj c).toMonoidHom z = c * z * c⁻¹ := rfl
  rw [hz'eq] at hz'1 hz'C
  refine ⟨z, hzE, fun h1 => hz'1 (by rw [h1]; group), c⁻¹ • S, ?_⟩
  have hT : ((c⁻¹ • S : Sylow 3 J) : Subgroup J) =
      (S : Subgroup J).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hconj : ∀ y : J, y ∈ Subgroup.centralizer ({z} : Set J) ↔
      c * y * c⁻¹ ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set J) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      calc c * y * c⁻¹ * (c * z * c⁻¹) = c * (y * z) * c⁻¹ := by group
        _ = c * (z * y) * c⁻¹ := by rw [hy]
        _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group
    · intro hy
      have h2 : c * (y * z) * c⁻¹ = c * (z * y) * c⁻¹ := by
        calc c * (y * z) * c⁻¹ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
          _ = c * z * c⁻¹ * (c * y * c⁻¹) := hy
          _ = c * (z * y) * c⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  have hmemS : ∀ w : J, w ∈ (S : Subgroup J) ↔
      w ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set J) := fun w => by rw [hz'C]
  rw [hT]
  ext y
  constructor
  · intro hy
    refine ⟨c * y * c⁻¹, (hmemS _).mpr ((hconj y).mp hy), ?_⟩
    change c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y
    group
  · rintro ⟨w, hw, rfl⟩
    have hww : c * ((MulAut.conj c⁻¹).toMonoidHom w) * c⁻¹ = w := by
      change c * (c⁻¹ * w * c⁻¹⁻¹) * c⁻¹ = w
      group
    rw [hconj, hww]
    exact (hmemS w).mp hw

end OuterSetupE9

section Normalized

variable {X : Type*} [Group X] [Finite X]

theorem mul_inv_mem_range_of_card_outer_le_two (hOut : Nat.card (Outer X) ≤ 2) {β γ : MulAut X}
    (hβ : β ∉ (MulAut.conj : X →* MulAut X).range) (hγ : γ ∉ (MulAut.conj : X →* MulAut X).range) :
    β * γ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  by_contra h
  let q : MulAut X →* Outer X := QuotientGroup.mk' (inner X)
  have hβ' : β ∉ inner X := hβ
  have hγ' : γ ∉ inner X := hγ
  have h' : β * γ⁻¹ ∉ inner X := h
  have h1 : q β ≠ 1 := fun e => hβ' ((QuotientGroup.eq_one_iff β).1 e)
  have h2 : q γ ≠ 1 := fun e => hγ' ((QuotientGroup.eq_one_iff γ).1 e)
  have h3 : q β ≠ q γ := fun e => h' (QuotientGroup.eq_iff_div_mem.1 e)
  have hinj : Function.Injective (![1, q β, q γ] : Fin 3 → Outer X) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at this
  omega

omit [Finite X] in
theorem mem_centralizer_singleton_of_conj_fix {u w : X} (hw : (MulAut.conj w) u = u) :
    w ∈ Subgroup.centralizer ({u} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : w * u * w⁻¹ = u := hw
  calc w * u = (w * u * w⁻¹) * w := by group
    _ = u * w := by rw [h]

theorem eq_bot_of_normalized_nine (hcen : Subgroup.center X = ⊥)
    {U : Subgroup X} (hE : ∀ u ∈ U, u ≠ 1 → IsPGroup 3 (Subgroup.centralizer ({u} : Set X)))
    (hOut : Nat.card (Outer X) ≤ 2)
    (hOuter : ∀ α : MulAut X, α ^ 2 = 1 → α ∉ (MulAut.conj : X →* MulAut X).range →
      ∀ B : Subgroup X, IsMulCommutative B → (∀ b ∈ B, b ^ 3 = 1) → Nat.card B = 9 →
        ∃ b ∈ B, α b ≠ b)
    (hU : IsMulCommutative U) (hU3 : ∀ x ∈ U, x ^ 3 = 1) (hU9 : Nat.card U = 9)
    {Y : Subgroup (MulAut X)} (hY : ¬ 3 ∣ Nat.card Y)
    (hUY : U.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Y : Set (MulAut X))) :
    Y = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  set V := U.map (MulAut.conj : X →* MulAut X) with hV
  have hVe : CFSG.Assembly.IsElemAbelian 3 V :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ U ⟨hU, hU3⟩
  have hV9 : Nat.card V = 9 := by rw [hV, Subgroup.card_map_of_injective hinj, hU9]
  have hcop3 : Nat.Coprime 3 (Nat.card Y) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hY
  refine le_bot_iff.mp (Sec5.le_of_forall_inf_centralizer_le (M := ⊥) hp hVe
    (by norm_num [hV9]) hUY hcop3 ?_)
  intro v hv hv1
  obtain ⟨u, huU, rfl⟩ := hv
  have hu1 : u ≠ 1 := fun h => hv1 (by rw [h, map_one])
  have hCu := hE u huU hu1
  set R : Subgroup (MulAut X) :=
    Y ⊓ Subgroup.centralizer ({MulAut.conj u} : Set (MulAut X)) with hR
  have hRfix : ∀ r ∈ R, r u = u := fun r hr =>
    fix_of_commute_conj hcen (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
  have hRcop : ∀ r ∈ R, Nat.Coprime 3 (orderOf r) := by
    intro r hr
    have h1 : orderOf r ∣ Nat.card Y := by
      rw [← Subgroup.orderOf_mk r hr.1]
      exact orderOf_dvd_natCard _
    exact hcop3.coprime_dvd_right h1
  have hRsq : ∀ r ∈ R, r ^ 2 = 1 := by
    intro r hr
    obtain ⟨x, hx⟩ := sq_mem_range_of_card_outer_le_two hOut r
    have hxu : x ∈ Subgroup.centralizer ({u} : Set X) := by
      refine mem_centralizer_singleton_of_conj_fix ?_
      rw [hx, pow_two, MulAut.mul_apply, hRfix r hr, hRfix r hr]
    have hxm : x ^ orderOf r = 1 := by
      apply hinj
      rw [map_pow, hx, map_one, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hx1 : x = 1 := eq_one_of_coprime_of_isPGroup hCu hxu (hRcop r hr) hxm
    rw [← hx, hx1, map_one]
  have hRinn : ∀ r ∈ R, r ∈ (MulAut.conj : X →* MulAut X).range → r = 1 := by
    intro r hr hrin
    obtain ⟨w, hw⟩ := hrin
    have hwu : w ∈ Subgroup.centralizer ({u} : Set X) := by
      refine mem_centralizer_singleton_of_conj_fix ?_
      rw [hw]
      exact hRfix r hr
    have hw2 : w ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hw, hRsq r hr, map_one]
    have hw1 : w = 1 := eq_one_of_coprime_of_isPGroup hCu hwu (by norm_num) hw2
    rw [← hw, hw1, map_one]
  have hRout : ∀ r ∈ R, ∀ r' ∈ R, r ∉ (MulAut.conj : X →* MulAut X).range →
      r' ∉ (MulAut.conj : X →* MulAut X).range → r = r' := by
    intro r hr r' hr' hro hro'
    have h1 : r * r'⁻¹ ∈ (MulAut.conj : X →* MulAut X).range :=
      mul_inv_mem_range_of_card_outer_le_two hOut hro hro'
    have h2 : r * r'⁻¹ = 1 := hRinn _ (R.mul_mem hr (R.inv_mem hr')) h1
    exact mul_inv_eq_one.mp h2
  intro y hy
  obtain ⟨hyY, hyC⟩ := hy
  have hyR : y ∈ R := ⟨hyY, hyC⟩
  by_cases hyin : y ∈ (MulAut.conj : X →* MulAut X).range
  · exact hRinn y hyR hyin
  · exfalso
    have hyfix : ∀ u' ∈ U, y u' = u' := by
      intro u' hu'
      refine fix_of_commute_conj hcen ?_
      have hu'N : MulAut.conj u' ∈ Subgroup.normalizer (Y : Set (MulAut X)) :=
        hUY (Subgroup.mem_map_of_mem _ hu')
      have hy' : MulAut.conj u' * y * (MulAut.conj u')⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp hu'N y).mp hyY
      have hc : Commute (MulAut.conj u') (MulAut.conj u) := by
        have h1 : Commute u' u := congrArg Subtype.val (mul_comm' (⟨u', hu'⟩ : U) ⟨u, huU⟩)
        exact h1.map (MulAut.conj : X →* MulAut X)
      have hyc : Commute y (MulAut.conj u) := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hy'C : MulAut.conj u' * y * (MulAut.conj u')⁻¹ ∈
          Subgroup.centralizer ({MulAut.conj u} : Set (MulAut X)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr ((hc.mul_left hyc).mul_left hc.inv_left)
      have hy'R : MulAut.conj u' * y * (MulAut.conj u')⁻¹ ∈ R := ⟨hy', hy'C⟩
      have hy'out : MulAut.conj u' * y * (MulAut.conj u')⁻¹ ∉
          (MulAut.conj : X →* MulAut X).range := by
        rintro ⟨w, hw⟩
        refine hyin ⟨u'⁻¹ * w * u', ?_⟩
        rw [map_mul, map_mul, hw, map_inv]
        group
      have heq := hRout _ hy'R y hyR hy'out hyin
      calc MulAut.conj u' * y = (MulAut.conj u' * y * (MulAut.conj u')⁻¹) * MulAut.conj u' := by
            group
        _ = y * MulAut.conj u' := by rw [heq]
    obtain ⟨b, hb, hne⟩ := hOuter y (hRsq y hyR) hyin U hU hU3 hU9
    exact hne (hyfix b hb)

end Normalized

theorem eq_one_of_cube_eq_one_zmod (t : ZMod 3) (h : t * (t * t) = 1) : t = 1 := by
  revert t
  decide


section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem center_layer_le (h : Ctx434Core G A M Q)
    (hZ3 : Nat.card (Subgroup.center (layer G)) = 3) :
    (Subgroup.center (layer G)).map (layer G).subtype ≤ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center (layer G)) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  by_cases hz1 : z = 1
  · rw [hz1]
    exact A.one_mem
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZz : Subgroup.center (layer G) = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [Nat.card_zpowers, hzo, hZ3])).symm
  refine h.rank3II_4_35 ?_ (by exact congrArg Subtype.val hz3)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  set α : MulAut (layer G) := layerConj G a with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, h.isE27.1.2 a ha, map_one]
  have hαz : α z ∈ Subgroup.center (layer G) := by
    rw [Subgroup.mem_center_iff]
    intro l
    have h1 := Subgroup.mem_center_iff.mp hz (α.symm l)
    calc l * α z = α (α.symm l * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = α (z * α.symm l) := by rw [h1]
      _ = α z * l := by rw [map_mul, MulEquiv.apply_symm_apply]
  rw [hZz] at hαz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hαz
  have hαk : ∀ n : ℤ, α (z ^ n) = z ^ (k * n) := fun n => by
    rw [map_zpow, ← hk, ← zpow_mul]
  have h3z : z = z ^ (k * (k * k)) := by
    have h1 : (α ^ 3) z = z := by rw [hα3]; rfl
    calc z = (α ^ 3) z := h1.symm
      _ = α (α (α z)) := by rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply]
      _ = z ^ (k * (k * k)) := by rw [← hk, hαk, hαk]
  have hdvd : (3 : ℤ) ∣ k * (k * k) - 1 := by
    have h1 : z ^ (k * (k * k) - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← h3z, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hzo] at h2
  have hk1 : (3 : ℤ) ∣ k - 1 := by
    have h1 : ((k * (k * k) - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hdvd)
    have h2 : ((k : ZMod 3)) = 1 := by
      have h3 : ((k : ZMod 3)) * (((k : ZMod 3)) * ((k : ZMod 3))) = 1 := by
        push_cast at h1
        exact sub_eq_zero.mp h1
      exact eq_one_of_cube_eq_one_zmod _ h3
    have h4 : ((k - 1 : ℤ) : ZMod 3) = 0 := by push_cast; rw [h2]; exact sub_self 1
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h4
  have hαzz : α z = z := by
    rw [← hk]
    have h1 : z ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hzo]; exact_mod_cast hk1)
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
    exact h1
  have h2 := congrArg Subtype.val hαzz
  rw [hα, layerConj_apply_coe] at h2
  change a * (z : G) * a⁻¹ = z at h2
  calc a * (z : G) = a * z * a⁻¹ * a := by group
    _ = z * a := by rw [h2]

theorem layer_le_of_centralizer_gen (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    (hZA : (Subgroup.center (layer G)).map (layer G).subtype ≤ A)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3)
    {U : Subgroup X}
    (hUA : A.map (quotConj e) = U.map (MulAut.conj : X →* MulAut X))
    (hgen : (⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set X)) = ⊤) :
    layer G ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  set φ := layerQuot e with hφ
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  set Z' : Subgroup G := A ⊓ Subgroup.centralizer (layer G : Set G) with hZ'
  have hZ'e : CFSG.Assembly.IsElemAbelian 3 Z' := Sec5.isElemAbelian_of_le h.isE27.1 inf_le_left
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hZL : ∀ z : layer G, z ∈ Subgroup.center (layer G) → (z : G) ∈ Z' := by
    intro z hz
    refine ⟨hZA ⟨z, hz, rfl⟩, ?_⟩
    show (z : G) ∈ Subgroup.centralizer (layer G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
  have hlift : ∀ u ∈ U, u ≠ 1 → ∀ σ ∈ Subgroup.centralizer ({u} : Set X), σ ∈ R.map φ := by
    intro u hu hu1 σ hσ
    obtain ⟨x, rfl⟩ := layerQuot_surjective e σ
    have hmem : (MulAut.conj u : MulAut X) ∈ A.map (quotConj e) := by
      rw [hUA]
      exact ⟨u, hu, rfl⟩
    obtain ⟨a, haA, hau⟩ := hmem
    have haZ' : a ∉ Z' := by
      intro haZ
      have h1 : quotConj e a = 1 := by
        rw [← MonoidHom.mem_ker, ker_quotConj h.isQuasisimple e]
        exact haZ.2
      rw [hau] at h1
      exact hu1 (hinj (h1.trans (map_one (MulAut.conj : X →* MulAut X)).symm))
    set B : Subgroup G := Z' ⊔ Subgroup.zpowers a with hB
    have hBA : B ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)
    obtain ⟨-, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hZ'e haZ' (h.isE27.1.2 a haA)
      (fun z hz => hcommA z hz.1 a haA)
    have hB9 : 9 ≤ Nat.card B := by
      rw [hB, hBcard, hC3]
    have hxa : (x : G) * a * (x : G)⁻¹ ∈ B := by
      set c' : layer G := x * (layerConj G a x)⁻¹ with hc'
      have hc'ker : c' ∈ Subgroup.center (layer G) := by
        rw [← ker_layerQuot e, MonoidHom.mem_ker, hc', map_mul, map_inv, ← quotConj_layerQuot,
          hau, MulAut.conj_apply]
        have h1 : u * layerQuot e x * u⁻¹ = layerQuot e x := by
          have h2 := Subgroup.mem_centralizer_singleton_iff.mp hσ
          rw [← h2, mul_inv_cancel_right]
        rw [h1, mul_inv_cancel]
      have hxa_eq : (x : G) * a * (x : G)⁻¹ = (c' : G) * a := by
        rw [hc']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, layerConj_apply_coe]
        group
      rw [hxa_eq]
      exact B.mul_mem (Subgroup.mem_sup_left (hZL c' hc'ker))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have hmapB : B.map (MulAut.conj (x : G)).toMonoidHom ≤ B := by
      rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ (Subgroup.zpowers_le.mpr hxa)
      rintro _ ⟨z, hz, rfl⟩
      have hxz : (x : G) * z * (x : G)⁻¹ = z := by
        have := Subgroup.mem_centralizer_iff.mp hz.2 x x.2
        rw [this, mul_inv_cancel_right]
      change (x : G) * z * (x : G)⁻¹ ∈ Z' ⊔ Subgroup.zpowers a
      rw [hxz]
      exact Subgroup.mem_sup_left hz
    have hxN : (x : G) ∈ Subgroup.normalizer (B : Set G) :=
      Subgroup.mem_normalizer_fintype fun n hn => hmapB ⟨n, hn, rfl⟩
    exact ⟨x, normalizer_le h hBA hB9 hxN, rfl⟩
  have hker : φ.ker ≤ Subgroup.center (layer G) := by rw [hφ, ker_layerQuot]
  have hrange : φ.range ≤ R.map φ := by
    rw [MonoidHom.range_eq_top.mpr (layerQuot_surjective e), ← hgen]
    exact iSup₂_le fun u hu => iSup_le fun hu1 σ hσ => hlift u hu hu1 σ hσ
  have htop := eq_top_of_range_le_map φ hker hrange
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434SporJ3
