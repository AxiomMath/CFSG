module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HDefs
public import CFSG.RankThree.PartTwo.Sec12.Hering129KInner
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH5

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Act

variable {P : Type} [Group P] {Yh Bh : Subgroup P}

@[expose] def innerSub (Yh : Subgroup P) : Subgroup P where
  carrier := {g | ∃ y : ↥Yh, ∀ u : ↥Yh, g * (u : P) * g⁻¹ = ((y * u * y⁻¹ : ↥Yh) : P)}
  one_mem' := ⟨1, fun u => by simp⟩
  mul_mem' := by
    rintro g g' ⟨y, hy⟩ ⟨y', hy'⟩
    refine ⟨y * y', fun u => ?_⟩
    have h1 : (g' * (u : P) * g'⁻¹) = ((y' * u * y'⁻¹ : ↥Yh) : P) := hy' u
    calc g * g' * (u : P) * (g * g')⁻¹ = g * (g' * (u : P) * g'⁻¹) * g⁻¹ := by group
      _ = g * (((y' * u * y'⁻¹ : ↥Yh)) : P) * g⁻¹ := by rw [h1]
      _ = ((y * (y' * u * y'⁻¹) * y⁻¹ : ↥Yh) : P) := hy _
      _ = (((y * y') * u * (y * y')⁻¹ : ↥Yh) : P) := by congr 1; group
  inv_mem' := by
    rintro g ⟨y, hy⟩
    refine ⟨y⁻¹, fun u => ?_⟩
    have h1 := hy (y⁻¹ * u * y)
    have h2 : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
    rw [h2] at h1
    rw [inv_inv]
    calc g⁻¹ * (u : P) * g = g⁻¹ * (g * ((y⁻¹ * u * y : ↥Yh) : P) * g⁻¹) * g := by rw [h1]
      _ = ((y⁻¹ * u * y : ↥Yh) : P) := by group
      _ = ((y⁻¹ * u * y⁻¹⁻¹ : ↥Yh) : P) := by rw [inv_inv]

theorem mem_innerSub {g : P} :
    g ∈ innerSub Yh ↔ ∃ y : ↥Yh, ∀ u : ↥Yh, g * (u : P) * g⁻¹ = ((y * u * y⁻¹ : ↥Yh) : P) :=
  Iff.rfl

theorem le_innerSub : Yh ≤ innerSub Yh := fun g hg =>
  ⟨⟨g, hg⟩, fun u => rfl⟩

theorem exists_innerAct [Yh.Normal] (hZ : Subgroup.center ↥Yh = ⊥) (hB : Bh ≤ innerSub Yh) :
    ∃ ψ : ↥(Yh ⊔ Bh) →* ↥Yh, ∀ (g : ↥(Yh ⊔ Bh)) (u : ↥Yh),
      (g : P) * (u : P) * (g : P)⁻¹ = ((ψ g * u * (ψ g)⁻¹ : ↥Yh) : P) := by
  have hle : Yh ⊔ Bh ≤ innerSub Yh := sup_le le_innerSub hB
  have hN : Yh ⊔ Bh ≤ Subgroup.normalizer (Yh : Set P) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr ‹Yh.Normal›]
    exact le_top
  let ρ : ↥Yh →* MulAut ↥Yh := MulAut.conj
  have hinj : Function.Injective ρ := fun a b h =>
    Hering129KInner.eq_of_conj_eq_conj hZ h
  let α : ↥(Yh ⊔ Bh) →* MulAut ↥Yh :=
    Yh.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hα : ∀ (g : ↥(Yh ⊔ Bh)) (u : ↥Yh),
      ((α g u : ↥Yh) : P) = (g : P) * (u : P) * (g : P)⁻¹ := fun g u =>
    Sec4.normalizerMonoidHom_apply_coe (hN g.2) u
  have hrange : ∀ g : ↥(Yh ⊔ Bh), α g ∈ ρ.range := by
    intro g
    obtain ⟨y, hy⟩ := mem_innerSub.mp (hle g.2)
    refine ⟨y, MulEquiv.ext fun u => Subtype.ext ?_⟩
    rw [hα, hy u]
    rfl
  let ψ : ↥(Yh ⊔ Bh) →* ↥Yh :=
    ((MonoidHom.ofInjective hinj).symm : ρ.range ≃* ↥Yh).toMonoidHom.comp
      (α.codRestrict ρ.range hrange)
  refine ⟨ψ, fun g u => ?_⟩
  have h1 : ρ (ψ g) = α g := by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply (α.codRestrict ρ.range hrange g)
    exact congrArg Subtype.val this
  rw [← hα, ← h1]
  rfl

structure Act (Yh Bh : Subgroup P) where
  ψ : ↥(Yh ⊔ Bh) →* ↥Yh
  conj : ∀ (g : ↥(Yh ⊔ Bh)) (u : ↥Yh),
    (g : P) * (u : P) * (g : P)⁻¹ = ((ψ g * u * (ψ g)⁻¹ : ↥Yh) : P)

namespace Act

theorem eq_of_inner (a : Act Yh Bh) (hZ : Subgroup.center ↥Yh = ⊥) {g : ↥(Yh ⊔ Bh)}
    {y : ↥Yh} (h : ∀ u : ↥Yh, (g : P) * (u : P) * (g : P)⁻¹ = ((y * u * y⁻¹ : ↥Yh) : P)) :
    a.ψ g = y := by
  apply Hering129KInner.eq_of_conj_eq_conj hZ
  ext u
  rw [MulAut.conj_apply, MulAut.conj_apply, ← a.conj g u, h u]

theorem apply_mem (a : Act Yh Bh) (hZ : Subgroup.center ↥Yh = ⊥) (l : ↥Yh)
    (hl : (l : P) ∈ Yh ⊔ Bh) : a.ψ ⟨l, hl⟩ = l :=
  a.eq_of_inner hZ fun u => rfl

theorem apply_central (a : Act Yh Bh) (hZ : Subgroup.center ↥Yh = ⊥) {g : ↥(Yh ⊔ Bh)}
    (hg : ∀ p : P, (g : P) * p = p * (g : P)) : a.ψ g = 1 :=
  a.eq_of_inner hZ fun u => by
    have : (g : P) * (u : P) * (g : P)⁻¹ = u := by rw [hg]; group
    rw [this]
    simp

theorem conj_of_apply_eq_one (a : Act Yh Bh) {g : ↥(Yh ⊔ Bh)} (h : a.ψ g = 1) (u : ↥Yh) :
    (g : P) * (u : P) * (g : P)⁻¹ = (u : P) := by
  rw [a.conj g u, h]
  simp

end Act

end Act

section Nine

variable {G : Type} [Group G]

theorem card_zpowers_sup_le {a b : G} (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≤ 9 := by
  classical
  let f : Fin 3 × Fin 3 → ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := fun ij =>
    ⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) _)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hz
    have hi : 0 ≤ i % 3 := Int.emod_nonneg _ (by norm_num)
    have hj : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
    refine ⟨(⟨(i % 3).toNat, by omega⟩, ⟨(j % 3).toNat, by omega⟩), Subtype.ext ?_⟩
    show a ^ ((i % 3).toNat) * b ^ ((j % 3).toNat) = a ^ i * b ^ j
    rw [Sec4.zpow_emod_three ha i, Sec4.zpow_emod_three hb j, ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hj]
  have := Nat.card_le_card_of_surjective f hf
  simpa using this

end Nine

section Hess


variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}

theorem xh_mem (hD : HessData Yh Bh xh bh ch) : xh ∈ Bh := by
  rw [hD.gen]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers xh))

theorem bh_mem (hD : HessData Yh Bh xh bh ch) : bh ∈ Bh := by
  rw [hD.gen]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))

theorem ch_mem (hD : HessData Yh Bh xh bh ch) : ch ∈ Bh := by
  rw [hD.gen]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ch)

theorem bh_comm_ch (hD : HessData Yh Bh xh bh ch) : bh * ch = ch * bh :=
  congrArg Subtype.val (hD.elem.1.is_comm.comm ⟨bh, bh_mem hD⟩ ⟨ch, ch_mem hD⟩)

theorem xh_comm_bh (hD : HessData Yh Bh xh bh ch) : xh * bh = bh * xh := hD.xcent bh

theorem xh_comm_ch (hD : HessData Yh Bh xh bh ch) : xh * ch = ch * xh := hD.xcent ch

theorem xh_pow (hD : HessData Yh Bh xh bh ch) : xh ^ 3 = 1 := hD.elem.2 xh (xh_mem hD)

theorem bh_pow (hD : HessData Yh Bh xh bh ch) : bh ^ 3 = 1 := hD.elem.2 bh (bh_mem hD)

theorem ch_pow (hD : HessData Yh Bh xh bh ch) : ch ^ 3 = 1 := hD.elem.2 ch (ch_mem hD)

theorem ch_ne_one (hD : HessData Yh Bh xh bh ch) : ch ≠ 1 := by
  intro h
  have hB : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers bh := by
    rw [hD.gen, h, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  have := card_zpowers_sup_le (xh_comm_bh hD) (xh_pow hD) (bh_pow hD)
  rw [← hB, hD.card] at this
  omega

theorem bh_not_mem_zpowers_xh (hD : HessData Yh Bh xh bh ch) : bh ∉ Subgroup.zpowers xh := by
  intro h
  have hB : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers ch := by
    rw [hD.gen]
    have : Subgroup.zpowers bh ≤ Subgroup.zpowers xh := Subgroup.zpowers_le.mpr h
    rw [sup_eq_left.mpr this]
  have := card_zpowers_sup_le (xh_comm_ch hD) (xh_pow hD) (ch_pow hD)
  rw [← hB, hD.card] at this
  omega

theorem bh_mem_sup (hD : HessData Yh Bh xh bh ch) : bh ∈ Yh ⊔ Bh :=
  Subgroup.mem_sup_right (bh_mem hD)

theorem ch_mem_sup (hD : HessData Yh Bh xh bh ch) : ch ∈ Yh ⊔ Bh :=
  Subgroup.mem_sup_right (ch_mem hD)

theorem xh_mem_sup (hD : HessData Yh Bh xh bh ch) : xh ∈ Yh ⊔ Bh :=
  Subgroup.mem_sup_right (xh_mem hD)

theorem Act.apply_xh (a : Act Yh Bh) (hZ : Subgroup.center ↥Yh = ⊥)
    (hD : HessData Yh Bh xh bh ch) : a.ψ ⟨xh, xh_mem_sup hD⟩ = 1 :=
  a.apply_central hZ fun p => hD.xcent p

theorem Act.mem_zpowers_xh_of_apply_eq_one (a : Act Yh Bh) (hD : HessData Yh Bh xh bh ch)
    {β : P} (hβ : β ∈ Bh) (h : a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ = 1) :
    β ∈ Subgroup.zpowers xh := by
  rw [← hD.cent]
  refine ⟨hβ, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have := a.conj_of_apply_eq_one h ⟨u, hu⟩
  have h2 : β * u * β⁻¹ = u := this
  calc u * β = (β * u * β⁻¹) * β := by rw [h2]
    _ = β * u := by group

theorem pair_facts (hD : HessData Yh Bh xh bh ch) (hZ : Subgroup.center ↥Yh = ⊥)
    (a : Act Yh Bh) :
    (⟨ch, hD.cY⟩ : ↥Yh) ^ 3 = 1 ∧ (a.ψ ⟨bh, bh_mem_sup hD⟩) ^ 3 = 1 ∧
      a.ψ ⟨bh, bh_mem_sup hD⟩ * ⟨ch, hD.cY⟩ = ⟨ch, hD.cY⟩ * a.ψ ⟨bh, bh_mem_sup hD⟩ ∧
      (⟨ch, hD.cY⟩ : ↥Yh) ≠ 1 ∧ a.ψ ⟨bh, bh_mem_sup hD⟩ ≠ 1 := by
  have hc : a.ψ ⟨ch, ch_mem_sup hD⟩ = ⟨ch, hD.cY⟩ := a.apply_mem hZ ⟨ch, hD.cY⟩ _
  refine ⟨Subtype.ext (by simpa using ch_pow hD), ?_, ?_, fun h => ch_ne_one hD (by
    simpa using congrArg Subtype.val h), fun h => bh_not_mem_zpowers_xh hD ?_⟩
  · rw [← map_pow]
    have : (⟨bh, bh_mem_sup hD⟩ : ↥(Yh ⊔ Bh)) ^ 3 = 1 := Subtype.ext (by simpa using bh_pow hD)
    rw [this, map_one]
  · rw [← hc, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (bh_comm_ch hD)
  · exact a.mem_zpowers_xh_of_apply_eq_one hD (bh_mem hD) h

theorem Act.apply_mem_of_gens (a : Act Yh Bh) (hZ : Subgroup.center ↥Yh = ⊥)
    (hD : HessData Yh Bh xh bh ch) (T : Subgroup ↥Yh)
    (hx : a.ψ ⟨xh, xh_mem_sup hD⟩ ∈ T) (hb : a.ψ ⟨bh, bh_mem_sup hD⟩ ∈ T)
    (hc : (⟨ch, hD.cY⟩ : ↥Yh) ∈ T) {β : P} (hβ : β ∈ Bh) :
    a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ ∈ T := by
  let T' : Subgroup P := (T.comap a.ψ).map (Yh ⊔ Bh).subtype
  have hmem : ∀ (g : P) (hg : g ∈ Yh ⊔ Bh), a.ψ ⟨g, hg⟩ ∈ T → g ∈ T' := fun g hg h =>
    Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr h, rfl⟩
  have hBT : Bh ≤ T' := by
    have h1 : Subgroup.zpowers xh ≤ T' := Subgroup.zpowers_le.mpr (hmem xh (xh_mem_sup hD) hx)
    have h2 : Subgroup.zpowers bh ≤ T' := Subgroup.zpowers_le.mpr (hmem bh (bh_mem_sup hD) hb)
    have h3 : Subgroup.zpowers ch ≤ T' := Subgroup.zpowers_le.mpr
      (hmem ch (ch_mem_sup hD) (by rw [a.apply_mem hZ ⟨ch, hD.cY⟩ (ch_mem_sup hD)]; exact hc))
    intro β hβ
    rw [hD.gen] at hβ
    exact (sup_le (sup_le h1 h2) h3) hβ
  obtain ⟨t, ht, htβ⟩ := Subgroup.mem_map.mp (hBT hβ)
  have : a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ = a.ψ t := by
    congr 1
    exact Subtype.ext htβ.symm
  rw [this]
  exact Subgroup.mem_comap.mp ht

theorem mem_of_zpow_mem {K : Type} [Group K] {y : K} (hy3 : y ^ 3 = 1) {F : Subgroup K} {i : ℤ}
    (hi : y ^ i ∈ F) (h3 : i % 3 ≠ 0) : y ∈ F := by
  rw [Sec4.zpow_emod_three hy3 i] at hi
  have h : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases h with h | h
  · rw [h, zpow_one] at hi
    exact hi
  · rw [h] at hi
    have h4 : y = (y ^ (2 : ℤ)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : y ^ (4 : ℤ) = 1 * y := by
        rw [show (4 : ℤ) = 3 + 1 from rfl, zpow_add, zpow_one]
        have h3' : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
        rw [h3']
      simpa using this.symm
    rw [h4]
    exact Subgroup.pow_mem _ hi 2

theorem hessConcl_of_hessF [Yh.Normal] (hD : HessData Yh Bh xh bh ch)
    (hZ : Subgroup.center ↥Yh = ⊥) (a : Act Yh Bh) {F : Subgroup ↥Yh}
    (hF : HessF (⟨ch, hD.cY⟩ : ↥Yh) (a.ψ ⟨bh, bh_mem_sup hD⟩) F) : HessConcl Yh Bh bh ch := by
  obtain ⟨hab, hcard, hcF, hyN, hcomm, hnt, htrans, hAut⟩ := hF
  obtain ⟨hc3, hy3, hyc, hc1, hy1⟩ := pair_facts hD hZ a
  set c : ↥Yh := ⟨ch, hD.cY⟩ with hc
  set y : ↥Yh := a.ψ ⟨bh, bh_mem_sup hD⟩ with hy
  have hyF : y ∉ F := by
    intro hyF
    obtain ⟨f, hf, hne⟩ := hnt
    apply hne
    have h1 : y * f = f * y :=
      congrArg Subtype.val (hab.1.is_comm.comm ⟨y, hyF⟩ ⟨f, hf⟩)
    rw [h1]
    group
  have hBN : ∀ β (hβ : β ∈ Bh), a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ ∈
      Subgroup.normalizer (F : Set ↥Yh) := fun β hβ =>
    a.apply_mem_of_gens hZ hD _ (by rw [a.apply_xh hZ hD]; exact one_mem _) hyN
      (Subgroup.le_normalizer hcF) hβ
  have hBZ : ∀ β (hβ : β ∈ Bh), a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ ∈
      Subgroup.zpowers y ⊔ Subgroup.zpowers c := fun β hβ =>
    a.apply_mem_of_gens hZ hD _ (by rw [a.apply_xh hZ hD]; exact one_mem _)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) hβ
  have hmapz : (Subgroup.zpowers c).map Yh.subtype = Subgroup.zpowers ch := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hconj1 : ∀ f ∈ F, bh * (f : P) * bh⁻¹ = ((y * f * y⁻¹ : ↥Yh) : P) := fun f _ =>
    a.conj ⟨bh, bh_mem_sup hD⟩ f
  unfold HessConcl
  refine ⟨F.map Yh.subtype, Subgroup.map_subtype_le F,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 Yh.subtype F hab,
    by rw [Subgroup.card_map_of_injective Yh.subtype_injective, hcard],
    Subgroup.mem_map.mpr ⟨c, hcF, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro β hβ
    apply Hering129KH4.mem_normalizer_of_forall_mem
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    have h1 := a.conj ⟨β, Subgroup.mem_sup_right hβ⟩ f
    have h2 : (a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩ * f * (a.ψ ⟨β, Subgroup.mem_sup_right hβ⟩)⁻¹) ∈
        F := (Subgroup.mem_normalizer_iff.mp (hBN β hβ) f).mp hf
    exact Subgroup.mem_map.mpr ⟨_, h2, h1.symm⟩
  ·
    apply le_antisymm
    · rintro x ⟨hxF, hxB⟩
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hxF
      have hψf : a.ψ ⟨(f : P), Subgroup.mem_sup_left f.2⟩ = f := a.apply_mem hZ f _
      have hz := hBZ (f : P) hxB
      rw [hψf] at hz
      have hyc' : y * c = c * y := hyc
      obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hyc' hz
      have hyi : y ^ i ∈ F := by
        have h1 : y ^ i = f * (c ^ j)⁻¹ := by rw [hij]; group
        rw [h1]
        exact F.mul_mem hf (F.inv_mem (Subgroup.zpow_mem _ hcF j))
      have hi : i % 3 = 0 := by
        by_contra hne
        exact hyF (mem_of_zpow_mem hy3 hyi hne)
      have hyi1 : y ^ i = 1 := by
        rw [Sec4.zpow_emod_three hy3 i, hi, zpow_zero]
      have hfc : f = c ^ j := by rw [hij, hyi1, one_mul]
      rw [hfc, ← hmapz]
      exact Subgroup.mem_map.mpr ⟨_, Subgroup.zpow_mem_zpowers c j, rfl⟩
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨Subgroup.zpow_mem _ (Subgroup.mem_map.mpr ⟨c, hcF, rfl⟩) k,
        Subgroup.zpow_mem _ (ch_mem hD) k⟩
  ·
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    rw [← hmapz]
    refine Subgroup.mem_map.mpr ⟨y * f * y⁻¹ * f⁻¹, hcomm f hf, ?_⟩
    show ((y * f * y⁻¹ * f⁻¹ : ↥Yh) : P) = bh * (f : P) * bh⁻¹ * (f : P)⁻¹
    rw [hconj1 f hf]
    rfl
  ·
    obtain ⟨f, hf, hne⟩ := hnt
    refine ⟨f, Subgroup.mem_map.mpr ⟨f, hf, rfl⟩, fun h => hne ?_⟩
    have h2 : ((y * f * y⁻¹ * f⁻¹ : ↥Yh) : P) = 1 := by
      have : bh * (f : P) * bh⁻¹ * (f : P)⁻¹ = ((y * f * y⁻¹ * f⁻¹ : ↥Yh) : P) := by
        rw [hconj1 f hf]
        rfl
      rw [← this]
      exact h
    exact Subtype.ext h2
  ·
    intro f' hf' hne
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    have hf1 : f ≠ 1 := fun h => hne (by rw [h]; simp)
    obtain ⟨n, hn, hnc⟩ := htrans f hf hf1
    refine ⟨(n : P), ⟨n.2, ?_⟩, congrArg Subtype.val hnc⟩
    apply Hering129KH4.mem_normalizer_of_forall_mem
    intro f'' hf''
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf''
    exact Subgroup.mem_map.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp hn g).mp hg, rfl⟩
  ·
    obtain ⟨φ⟩ := hAut
    obtain ⟨χ⟩ := Hering129KH5.nonempty_autIn_of_lift (G := P) (M := ↥Yh) (Y := Yh)
      (A := Yh ⊔ Bh) (Lh := (⊤ : Subgroup ↥Yh)) Subgroup.topEquiv.symm (ψ := a.ψ) (R := ⊤)
      (fun g x hgx => Subtype.ext (a.conj g x).symm)
      (fun g => Subgroup.mem_top _)
      (fun r _ => ⟨⟨(r : P), Subgroup.mem_sup_left r.2⟩, a.apply_mem hZ r _⟩)
      (F := F) le_top (Ft := F.map Yh.subtype)
      (fun {x} => by
        constructor
        · rintro ⟨f, hf, rfl⟩
          exact ⟨f.2, hf⟩
        · rintro ⟨hx, hxF⟩
          exact ⟨⟨x, hx⟩, hxF, rfl⟩)
    exact ⟨χ.trans φ⟩

end Hess

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
