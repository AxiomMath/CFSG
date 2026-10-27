module

public import CFSG.Quasithin.Background.SmithB57EG

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC CFSG.Quasithin.S143 CFSG.Quasithin.B3 Equiv
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
open scoped commutatorElement

section General

variable {Ω : Type*} [Group Ω]

theorem mem_sup_of_commute {H K : Subgroup Ω} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : Ω}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let P : Subgroup Ω :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hx
        obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hy
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * h₂ * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨h, hh, k, hk, rfl⟩ := hx
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact hc _ (H.inv_mem hh) _ (K.inv_mem hk) }
  have hle : H ⊔ K ≤ P := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  exact hle hx

theorem mem_of_mul_self_mem {H : Subgroup Ω} {g : Ω} (hodd : Odd (orderOf g))
    (h : g * g ∈ H) : g ∈ H := by
  obtain ⟨m, hm⟩ := hodd
  have hg1 : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
  have e : g = (g * g) ^ (m + 1) := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hg1, one_mul]
  rw [e]
  exact H.pow_mem h _

theorem commute_of_card_three [Finite Ω] {X : Subgroup Ω} (hX : Nat.card X = 3) {d : Ω}
    (hdX : ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hodd : Odd (orderOf d)) : ∀ x ∈ X, d * x = x * d := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, one_mul]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
    rw [hX] at h
    have h' := congrArg Subtype.val h
    simpa using h'
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzX : Subgroup.zpowers x = X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) ?_
    rw [hX, Nat.card_zpowers, hord]
  have hy : d * x * d⁻¹ ∈ Subgroup.zpowers x := by rw [hzX]; exact hdX x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hord] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  have hd2 : (d * d) * x = x * (d * d) := by
    rcases hk3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk
      apply hx1
      have : d * x * d⁻¹ = 1 := hk.symm
      calc x = d⁻¹ * (d * x * d⁻¹) * d := by group
        _ = 1 := by rw [this]; group
    · rw [h1, zpow_one] at hk
      have e : d * x = x * d := by
        calc d * x = d * x * d⁻¹ * d := by group
          _ = x * d := by rw [← hk]
      calc d * d * x = d * (d * x) := by group
        _ = d * (x * d) := by rw [e]
        _ = (d * x) * d := by group
        _ = x * d * d := by rw [e]
        _ = x * (d * d) := by group
    · rw [h2] at hk
      have hinv : d * x * d⁻¹ = x⁻¹ := by
        rw [← hk]
        have : x ^ (2 : ℤ) * x = 1 := by
          rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx3]
        exact eq_inv_of_mul_eq_one_left this
      have hinv' : d * x⁻¹ * d⁻¹ = x := by
        rw [show d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ by group, hinv, inv_inv]
      calc d * d * x = d * (d * x * d⁻¹) * d⁻¹ * (d * d) := by group
        _ = d * x⁻¹ * d⁻¹ * (d * d) := by rw [hinv]
        _ = x * (d * d) := by rw [hinv']
  have hmem : d * d ∈ Subgroup.centralizer ({x} : Set Ω) :=
    Subgroup.mem_centralizer_singleton_iff.2 hd2
  have hd := mem_of_mul_self_mem hodd hmem
  exact Subgroup.mem_centralizer_singleton_iff.1 hd

end General

section AutSix

noncomputable abbrev conj6 : Perm (Fin 6) →* MulAut (LG 6) := MulAut.conjNormal

theorem conj6_injective : Function.Injective conj6 := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine center_alt6 σ fun τ hτ => ?_
  have h := congrArg (fun φ : MulAut (LG 6) => ((φ ⟨τ, hτ⟩ : LG 6) : Perm (Fin 6))) hσ
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc σ * τ = σ * τ * σ⁻¹ * σ := by group
    _ = τ * σ := by rw [h]

theorem conj6_range_normal : (conj6.range).Normal := by
  have hcard : Nat.card conj6.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective conj6_injective).toEquiv, card_perm_six]
  have hle : Nat.card (MulAut (LG 6)) ≤ 1440 := automorphism_card_le
  have hmul := Subgroup.card_mul_index conj6.range
  rw [hcard] at hmul
  have h0 : conj6.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : conj6.range.index ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ conj6.range.index := by omega
    have : 720 * 3 ≤ 720 * conj6.range.index := Nat.mul_le_mul_left _ h3
    omega
  rcases Nat.lt_or_ge conj6.range.index 2 with h | h
  · have h1 : conj6.range.index = 1 := by omega
    rw [Subgroup.index_eq_one] at h1
    rw [h1]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two (le_antisymm hidx h)

theorem exists_equiv_of {Ω : Type*} [Group Ω] {L : Subgroup Ω} (f : Perm (Fin 6) →* Ω)
    (hf : Function.Injective f) (hL : ∀ σ, f σ ∈ L ↔ σ ∈ alternatingGroup (Fin 6))
    (hs : ∀ l ∈ L, ∃ σ, f σ = l) : ∃ ι : LG 6 ≃* ↥L, ∀ x, (ι x : Ω) = f x := by
  let g : LG 6 →* ↥L :=
    (f.comp (alternatingGroup (Fin 6)).subtype).codRestrict L (fun x => (hL x).2 x.2)
  have hbij : Function.Bijective g := by
    constructor
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (hf h')
    · rintro ⟨l, hl⟩
      obtain ⟨σ, rfl⟩ := hs l hl
      exact ⟨⟨σ, (hL σ).1 hl⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective g hbij, fun x => rfl⟩

theorem exists_conj_eq {Ω : Type*} [Group Ω] {L : Subgroup Ω} (f₁ f₂ : Perm (Fin 6) →* Ω)
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (h₁ : ∀ σ, f₁ σ ∈ L ↔ σ ∈ alternatingGroup (Fin 6))
    (h₂ : ∀ σ, f₂ σ ∈ L ↔ σ ∈ alternatingGroup (Fin 6))
    (hs₁ : ∀ l ∈ L, ∃ σ, f₁ σ = l) (hs₂ : ∀ l ∈ L, ∃ σ, f₂ σ = l) (σ : Perm (Fin 6)) :
    ∃ τ, ∀ l ∈ L, f₂ σ * l * (f₂ σ)⁻¹ = f₁ τ * l * (f₁ τ)⁻¹ := by
  obtain ⟨ι₁, hι₁⟩ := exists_equiv_of f₁ hf₁ h₁ hs₁
  obtain ⟨ι₂, hι₂⟩ := exists_equiv_of f₂ hf₂ h₂ hs₂
  set ψ : MulAut (LG 6) := ι₂.trans ι₁.symm with hψ
  obtain ⟨τ, hτ⟩ := conj6_range_normal.conj_mem _ ⟨σ, rfl⟩ ψ
  refine ⟨τ, fun l hl => ?_⟩
  have hτ' : conj6 τ * ψ = ψ * conj6 σ := by rw [hτ]; group
  set z := ι₂.symm ⟨l, hl⟩ with hz
  have hfz : f₂ z = l := by rw [← hι₂, hz, MulEquiv.apply_symm_apply]
  set w := ι₁.symm ⟨l, hl⟩ with hw
  have hfw : f₁ w = l := by rw [← hι₁, hw, MulEquiv.apply_symm_apply]
  have hψz : ψ z = w := by
    rw [hψ, MulEquiv.trans_apply, hz, MulEquiv.apply_symm_apply]
  have h1 := congrArg (fun φ : MulAut (LG 6) => (ι₁ (φ z) : Ω)) hτ'
  simp only [MulAut.mul_apply, hψz] at h1
  rw [hψ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hι₁, hι₂] at h1
  simp only [MulAut.conjNormal_apply, map_mul, map_inv, hfz, hfw] at h1
  exact h1.symm

end AutSix

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem genFitting_le : quasithinGenFitting G ≤ L ⊔ (pCoreOf 3 G ⊔ centerOf G) := by
  have hC : ∀ p : ℕ, p.Prime → pCoreOf p G ≤ pCoreOf 3 G ⊔ centerOf G := by
    intro p hp
    by_cases h2 : p = 2
    · subst h2
      rw [S.hO2]
      exact bot_le
    by_cases h3 : p = 3
    · subst h3
      exact le_sup_left
    · have : Fact p.Prime := ⟨hp⟩
      exact le_sup_of_le_right (le_inf (CFSG.LieType.BorelTits.pCoreOf_le p G)
        (B55.pCoreOf_le_centralizer S.hV S.hJ h2 h3))
  unfold quasithinGenFitting
  refine sup_le ?_ ?_
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNG, hNn, hnil⟩ := hN
    exact (nilpotent_le_of_pCoreOf hNG hNn hnil hC).trans le_sup_right
  · refine sSup_le fun K hK => ?_
    rw [S.hlayer K hK]
    exact le_sup_left

theorem sup_le_centralizer :
    pCoreOf 3 G ⊔ centerOf G ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
  refine sup_le (fun x hx => ?_) (fun z hz => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (S.commute_X x hx l hl).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 hz.2 l (S.hLG hl))

end Hyp

namespace SixData

variable {G L A : Subgroup (MulAut V)} {S : Hyp G L} (D : SixData S A)
include D

theorem eq_one_of_mem_L {l : MulAut V} (hl : l ∈ L) (hlL : ∀ l' ∈ L, l * l' = l' * l) :
    l = 1 := by
  obtain ⟨σ, rfl⟩ := D.f_surj ((le_sup_left : L ≤ L ⊔ A) hl)
  have hσ : σ = 1 := by
    refine center_alt6 σ fun τ hτ => D.f_injective ?_
    rw [D.f_mul, D.f_mul]
    exact hlL _ ((D.mem_L_iff τ).2 hτ)
  rw [hσ, D.f_one]

theorem card_L : Nat.card ↥L = 360 := by
  rw [card_eq_alternating (by norm_num) D.commutator_eq D.π, nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]

theorem mem_of_commute {d : MulAut V} (hd : d ∈ G) (hdL : ∀ l ∈ L, d * l = l * d) :
    d ∈ pCoreOf 3 G ⊔ centerOf G := by
  have hdX : ∀ x ∈ pCoreOf 3 G, d * x = x * d :=
    commute_of_card_three D.card_X (fun x hx => (Subgroup.mem_normalizer_iff.1
      ((le_normalizer_pCore3 G) hd) x).1 hx) (S.odd_orderOf_of_commute hd hdL)
  have hle : L ⊔ (pCoreOf 3 G ⊔ centerOf G) ≤ Subgroup.centralizer ({d} : Set (MulAut V)) := by
    refine sup_le (fun l hl => ?_) (sup_le (fun x hx => ?_) (fun z hz => ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hdL l hl).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hdX x hx).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hz.2 d hd).symm
  have hdF : d ∈ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (S.genFitting_le hf))
  have hdF' := S.genFitting_le (centralizer_quasithinGenFitting_le G ⟨hd, hdF⟩)
  obtain ⟨l, hl, k, hk, rfl⟩ := mem_sup_of_commute (fun l hl k hk =>
    (Subgroup.mem_centralizer_iff.1 (S.sup_le_centralizer hk) l hl)) hdF'
  have hkL : ∀ l' ∈ L, k * l' = l' * k := fun l' hl' =>
    (Subgroup.mem_centralizer_iff.1 (S.sup_le_centralizer hk) l' hl').symm
  have hl1 : l = 1 := by
    refine D.eq_one_of_mem_L hl fun l' hl' => ?_
    have h1 := hdL l' hl'
    have h2 := hkL l' hl'
    calc l * l' = (l * k) * l' * k⁻¹ := by
          rw [mul_assoc l k l', h2]; group
      _ = l' * (l * k) * k⁻¹ := by rw [h1]
      _ = l' * l := by group
  rw [hl1, one_mul]
  exact hk

theorem exists_six {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) (hBL : ¬ B ≤ L) :
    ∃ π₂ : Perm (Fin 6) ≃* ↥(L ⊔ B),
      ∀ σ, ((π₂ σ : ↥(L ⊔ B)) : MulAut V) ∈ L ↔ σ ∈ alternatingGroup (Fin 6) := by
  obtain ⟨-, hcase⟩ := S.case1i D.hP4 D.hA21 D.hB51 hB hBL
  rcases hcase with ⟨n, hn5, hn8, hS⟩ | hG
  · obtain ⟨π, -, halt⟩ := S.sym_data D.hP4 hB hn5 hS
    have hn : n = 6 := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h := card_eq_alternating hn5 (S.commutator_sup D.hP4 hB) π
      rw [D.card_L, nat_card_alternatingGroup] at h
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
      interval_cases n
      · norm_num [Nat.factorial] at h
      · rfl
      · norm_num [Nat.factorial] at h
      · norm_num [Nat.factorial] at h
    subst hn
    exact ⟨π, halt⟩
  · exfalso
    obtain ⟨K, _, _, hK, π, hπ⟩ := hG
    have hK2 : Nat.card K = 2 := by simpa using hK
    have h1 := G64.RealizesVia.card_eq hπ
    have h64 : Nat.card (FFModel.zornQ (quasithinG2 K)).Mod = 64 :=
      H13.U3.card_zornQ_of_card_two hK2
    rw [h64, D.card_U] at h1
    have hpos : 0 < Nat.card ↥(fixV L ⊓ commV L) := Nat.card_pos
    omega

theorem offender_le {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) :
    B ≤ (L ⊔ A) ⊔ pCoreOf 3 G := by
  by_cases hBL : B ≤ L
  · exact hBL.trans (le_sup_left.trans le_sup_left)
  obtain ⟨π₂, halt₂⟩ := D.exists_six hB hBL
  intro b hb
  have hbM : b ∈ L ⊔ B := (le_sup_right : B ≤ L ⊔ B) hb
  have hMG₂ : L ⊔ B ≤ G := sup_le S.hLG hB.1
  obtain ⟨τ, hτ⟩ := exists_conj_eq ((L ⊔ A).subtype.comp D.π.toMonoidHom)
    ((L ⊔ B).subtype.comp π₂.toMonoidHom) D.f_injective
    (Subtype.val_injective.comp π₂.injective) D.mem_L_iff halt₂
    (fun l hl => D.f_surj ((le_sup_left : L ≤ L ⊔ A) hl))
    (fun l hl => ⟨π₂.symm ⟨l, (le_sup_left : L ≤ L ⊔ B) hl⟩, by simp⟩) (π₂.symm ⟨b, hbM⟩)
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hτ
  have hτ' : ∀ l ∈ L, b * l * b⁻¹ = D.f τ * l * (D.f τ)⁻¹ := hτ
  set m := D.f τ with hm
  have hmG : m ∈ G := D.f_mem_G τ
  have hbG : b ∈ G := hB.1 hb
  have hgL : ∀ l ∈ L, (m⁻¹ * b) * l = l * (m⁻¹ * b) := by
    intro l hl
    calc m⁻¹ * b * l = m⁻¹ * (b * l * b⁻¹) * b := by group
      _ = m⁻¹ * (m * l * m⁻¹) * b := by rw [hτ' l hl]
      _ = l * (m⁻¹ * b) := by group
  have hg := D.mem_of_commute (G.mul_mem (G.inv_mem hmG) hbG) hgL
  obtain ⟨x, hx, z, hz, hxz⟩ := mem_sup_of_commute (H := pCoreOf 3 G) (K := centerOf G)
    (fun x hx z hz =>
    (Subgroup.mem_centralizer_iff.1 hz.2 x (pCore3_le G hx))) hg
  have hbe : b = m * x * z := by
    calc b = m * (m⁻¹ * b) := by group
      _ = m * x * z := by rw [← hxz]; group
  have hzc : ∀ g ∈ G, z * g = g * z := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hz.2 g hg).symm
  have hzodd : Odd (orderOf z) :=
    S.odd_orderOf_of_commute hz.1 fun l hl => hzc l (S.hLG hl)
  have hmx : m * x ∈ (L ⊔ A) ⊔ pCoreOf 3 G :=
    Subgroup.mul_mem _ ((le_sup_left : L ⊔ A ≤ (L ⊔ A) ⊔ pCoreOf 3 G) (D.f_mem τ))
      ((le_sup_right : pCoreOf 3 G ≤ (L ⊔ A) ⊔ pCoreOf 3 G) hx)
  have hb2 : b * b = 1 := by simpa [sq] using hB.2.2.1.2 b hb
  have hzz : z * z ∈ (L ⊔ A) ⊔ pCoreOf 3 G := by
    have hmxG : m * x ∈ G := G.mul_mem hmG (pCore3_le G hx)
    have e : z * z = ((m * x) * (m * x))⁻¹ := by
      have h1 : (m * x * z) * (m * x * z) = 1 := by rw [← hbe]; exact hb2
      have h2 : (m * x * z) * (m * x * z) = (m * x) * (m * x) * (z * z) := by
        have hz' : z * (m * x) = (m * x) * z := hzc _ hmxG
        calc (m * x * z) * (m * x * z) = (m * x) * (z * (m * x)) * z := by group
          _ = (m * x) * ((m * x) * z) * z := by rw [hz']
          _ = (m * x) * (m * x) * (z * z) := by group
      rw [h2] at h1
      exact eq_inv_of_mul_eq_one_right h1
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hmx hmx)
  have hzM := mem_of_mul_self_mem hzodd hzz
  rw [hbe]
  exact Subgroup.mul_mem _ hmx hzM

theorem eq_sup {t : MulAut V} (ht : t ∈ A)
    (htX : t ∉ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) :
    G = (L ⊔ pCoreOf 3 G) ⊔ Subgroup.zpowers t := by
  have hAt : A ≤ L ⊔ Subgroup.zpowers t := by
    intro a ha
    rcases D.mem_or_mul_mem ht htX ((le_sup_right : A ≤ L ⊔ A) ha) with h | h
    · exact (le_sup_left : L ≤ L ⊔ Subgroup.zpowers t) h
    · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (D.t_sq ht)
      have e : a = (a * t) * t := by
        calc a = a * t * t⁻¹ := by group
          _ = a * t * t := by rw [htinv]
      rw [e]
      exact Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ Subgroup.zpowers t) h)
        ((le_sup_right : Subgroup.zpowers t ≤ L ⊔ Subgroup.zpowers t) (Subgroup.mem_zpowers t))
  have hMX : (L ⊔ A) ⊔ pCoreOf 3 G ≤ (L ⊔ pCoreOf 3 G) ⊔ Subgroup.zpowers t := by
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) (hAt.trans ?_))
      (le_sup_right.trans le_sup_left)
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine le_antisymm (S.hJ.le.trans ?_) (sup_le (sup_le S.hLG (pCore3_le G))
    (Subgroup.zpowers_le.2 (D.hA.1 ht)))
  exact iSup₂_le fun B hB => (D.offender_le hB).trans hMX

end SixData

end SmithB57E

end CFSG.Quasithin
