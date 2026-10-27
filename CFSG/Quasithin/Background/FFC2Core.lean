module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.Quasithin

namespace FFC

open scoped commutatorElement

section QuasisimpleNormal

variable {Ω : Type*} [Group Ω]

theorem normal_quasisimple_cases {L N : Subgroup Ω} (hq : CFSG.IsQuasisimple ↥L) (hNL : N ≤ L)
    (hn : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N) :
    (∀ x ∈ N, ∀ l ∈ L, x * l = l * x) ∨ N = L := by
  obtain ⟨hperf, hsimple, -⟩ := hq
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hsimple
  set N' : Subgroup ↥L := N.subgroupOf L with hN'
  have hN'n : N'.Normal := ⟨fun x hx l => by
    have := hn l l.2 x hx
    simpa [hN', Subgroup.mem_subgroupOf] using this⟩
  let q := QuotientGroup.mk' (Subgroup.center ↥L)
  have hnorm : (N'.map q).Normal := Subgroup.Normal.map hN'n q (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with h | h
  · left
    intro x hx l hl
    have hmem : (⟨x, hNL hx⟩ : ↥L) ∈ N' := hx
    have : q ⟨x, hNL hx⟩ ∈ N'.map q := ⟨_, hmem, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hc := Subgroup.mem_center_iff.1 this ⟨l, hl⟩
    exact congrArg Subtype.val hc.symm
  · right
    refine le_antisymm (fun x hx => hNL hx) (fun x hx => ?_)
    have hall : ∀ y : ↥L, ∃ n ∈ N', ∃ z ∈ Subgroup.center ↥L, y = n * z := by
      intro y
      have : q y ∈ N'.map q := by rw [h]; trivial
      obtain ⟨n, hn1, hn2⟩ := this
      refine ⟨n, hn1, n⁻¹ * y, ?_, by group⟩
      have := QuotientGroup.eq.1 hn2
      simpa [q] using this
    have hcomm : commutator ↥L ≤ N' := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨n1, hn1, z1, hz1, rfl⟩ := hall a
      obtain ⟨n2, hn2, z2, hz2, rfl⟩ := hall b
      have e1 : QuotientGroup.mk' N' (n1 * z1) = QuotientGroup.mk' N' z1 := by
        have h1 : QuotientGroup.mk' N' n1 = 1 := (QuotientGroup.eq_one_iff n1).2 hn1
        rw [map_mul, h1, one_mul]
      have e2 : QuotientGroup.mk' N' (n2 * z2) = QuotientGroup.mk' N' z2 := by
        have h1 : QuotientGroup.mk' N' n2 = 1 := (QuotientGroup.eq_one_iff n2).2 hn2
        rw [map_mul, h1, one_mul]
      have hc : (QuotientGroup.mk' N') ⁅n1 * z1, n2 * z2⁆ = 1 := by
        rw [map_commutatorElement, e1, e2, ← map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz2 z1), map_one]
      exact (QuotientGroup.eq_one_iff _).1 hc
    have hxtop : (⟨x, hx⟩ : ↥L) ∈ commutator ↥L := by
      rw [hperf.commutator_eq_top]
      trivial
    exact hcomm hxtop


theorem commutator_le_self_aux (H : Subgroup Ω) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem commutator_normalized {H : Subgroup Ω} {g : Ω} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : ∀ d ∈ ⁅H, H⁆, g * d * g⁻¹ ∈ ⁅H, H⁆ := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hg h hh
    · intro hx
      exact ⟨g⁻¹ * x * g, hg' x hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  intro d hd
  have : (MulAut.conj g).toMonoidHom d ∈ (⁅H, H⁆).map (MulAut.conj g).toMonoidHom := ⟨d, hd, rfl⟩
  rw [Subgroup.map_commutator, hmap] at this
  exact this

theorem eq_commutator_of_normal_simple {G H L : Subgroup Ω} (hHG : H ≤ G) (hLG : L ≤ G)
    (hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hself : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L)
    (hq : CFSG.IsQuasisimple ↥L) (hDn : ∃ a b : ↥⁅H, H⁆, a * b ≠ b * a)
    (hDs : IsSimpleGroup ↥⁅H, H⁆) : L = ⁅H, H⁆ := by
  set D := ⁅H, H⁆ with hD
  have hDH : D ≤ H := commutator_le_self_aux H
  have hDG : D ≤ G := hDH.trans hHG
  have hDn' : ∀ g ∈ G, ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun g hg d hd =>
    commutator_normalized (hHn g hg) (by simpa using hHn g⁻¹ (G.inv_mem hg)) d hd
  have hN : ((D ⊓ L).subgroupOf D).Normal := ⟨fun x hx d => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨D.mul_mem (D.mul_mem d.2 hx.1) (D.inv_mem d.2), hLn d (hDG d.2) _ hx.2⟩⟩
  rcases hN.eq_bot_or_eq_top with h0 | h1
  · exfalso
    have hbot : D ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥D) ∈ (D ⊓ L).subgroupOf D := hx
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    have hcent : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d := by
      intro d hd l hl
      have h1 : d * l * d⁻¹ * l⁻¹ ∈ D ⊓ L := by
        refine ⟨?_, L.mul_mem (hLn d (hDG hd) l hl) (L.inv_mem hl)⟩
        have := D.mul_mem hd (hDn' l (hLG hl) d⁻¹ (D.inv_mem hd))
        simpa [mul_assoc] using this
      rw [hbot, Subgroup.mem_bot] at h1
      calc d * l = (d * l * d⁻¹ * l⁻¹) * l * d := by group
        _ = l * d := by rw [h1, one_mul]
    have hDL : ∀ d ∈ D, d ∈ L := fun d hd => hself d (hDG hd) (hcent d hd)
    obtain ⟨a, b, hab⟩ := hDn
    have ha : (a : Ω) = 1 := by
      have : (a : Ω) ∈ D ⊓ L := ⟨a.2, hDL _ a.2⟩
      rwa [hbot, Subgroup.mem_bot] at this
    apply hab
    apply Subtype.ext
    simp [ha]
  · have hDL : D ≤ L := by
      intro x hx
      have : (⟨x, hx⟩ : ↥D) ∈ (D ⊓ L).subgroupOf D := by rw [h1]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).2
    rcases normal_quasisimple_cases hq hDL (fun l hl x hx => hDn' l (hLG hl) x hx) with hc | heq
    · exfalso
      obtain ⟨a, b, hab⟩ := hDn
      exact hab (Subtype.ext (hc a a.2 b (hDL b.2)))
    · exact heq.symm

theorem eq_of_card_mulAut_le [Finite Ω] {G H L : Subgroup Ω} (hLH : L ≤ H) (hHG : H ≤ G) (hne : H ≠ L)
    (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hself : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1)
    (haut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L) : G = H := by
  let φ : ↥G →* MulAut ↥L :=
    { toFun := fun g =>
        { toFun := fun l => ⟨(g : Ω) * l * (g : Ω)⁻¹, hLn g g.2 l l.2⟩
          invFun := fun l => ⟨(g : Ω)⁻¹ * l * (g : Ω), by
            simpa using hLn (g : Ω)⁻¹ (G.inv_mem g.2) l l.2⟩
          left_inv := fun l => by ext; simp [mul_assoc]
          right_inv := fun l => by ext; simp [mul_assoc]
          map_mul' := fun a b => by ext; simp [mul_assoc] }
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : ((g : Ω)) = 1 := by
      refine hself g g.2 fun l hl => ?_
      have := congrArg (fun ψ : MulAut ↥L => (ψ ⟨l, hl⟩ : Ω)) hg
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
        MulAut.one_apply] at this
      calc (g : Ω) * l = ((g : Ω) * l * (g : Ω)⁻¹) * (g : Ω) := by group
        _ = l * g := by rw [this]
    exact Subtype.ext this
  have hGle : Nat.card ↥G ≤ 2 * Nat.card ↥L := (Nat.card_le_card_of_injective φ hinj).trans haut
  have hdvd : Nat.card ↥L ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hLH
  obtain ⟨k, hk⟩ := hdvd
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge hLH (by omega)).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  have hH2 : 2 * Nat.card ↥L ≤ Nat.card ↥H := by
    rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ hk2
  exact (Subgroup.eq_of_le_of_card_ge hHG (hGle.trans hH2)).symm

theorem card_mulAut_alternating_le {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Nat.card (MulAut ↥(alternatingGroup (Fin n))) ≤ 2 * Nat.card ↥(alternatingGroup (Fin n)) := by
  have hsurj := CFSG.ComponentClassification.CatalogueSchreierAlternating.conjugation_surjective hn
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card (Equiv.Perm (Fin n)) = 2 * Nat.card ↥(alternatingGroup (Fin n)) := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have := (alternatingGroup (Fin n)).card_eq_card_quotient_mul_card_subgroup
    rw [this, ← Subgroup.index, alternatingGroup.index_eq_two]
  omega

end QuasisimpleNormal



section Ident

variable {Ω : Type*} [Group Ω]

theorem nontrivial_of_isQuasisimple {L : Type*} [Group L] (h : CFSG.IsQuasisimple L) : Nontrivial L := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := h.2.1
  exact (QuotientGroup.mk_surjective :
    Function.Surjective (QuotientGroup.mk : L → L ⧸ Subgroup.center L)).nontrivial

theorem exists_noncomm_of_center_eq_bot {D : Type*} [Group D] [Nontrivial D]
    (h : Subgroup.center D = ⊥) : ∃ a b : D, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_ne (1 : D)
  have : x ∈ Subgroup.center D := Subgroup.mem_center_iff.2 fun g => (hc g x)
  rw [h, Subgroup.mem_bot] at this
  exact hx this

theorem center_eq_bot_of_simple {D : Type*} [Group D] [IsSimpleGroup D]
    (hD : ∃ a b : D, a * b ≠ b * a) : Subgroup.center D = ⊥ := by
  rcases (Subgroup.center D).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hD
    have ha : a ∈ Subgroup.center D := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem commutator_equiv_alternating {M : Subgroup Ω} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥M ≃* Equiv.Perm (Fin n)) : Nonempty (↥⁅M, M⁆ ≃* ↥(alternatingGroup (Fin n))) := by
  have hA : commutator (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) :=
    alternatingGroup.commutator_perm_eq (by simpa using hn)
  have hmap : (commutator ↥M).map e.toMonoidHom = alternatingGroup (Fin n) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 e.surjective, ← commutator_def, hA]
  have h1 : (commutator ↥M).map M.subtype = ⁅M, M⁆ := Subgroup.map_subtype_commutator M
  exact ⟨((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm).trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap))⟩

theorem commutator_simple_of_perm {M : Subgroup Ω} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥M ≃* Equiv.Perm (Fin n)) :
    IsSimpleGroup ↥⁅M, M⁆ ∧ ∃ a b : ↥⁅M, M⁆, a * b ≠ b * a := by
  obtain ⟨f⟩ := commutator_equiv_alternating hn e
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup hcard
  have hs' : IsSimpleGroup ↥⁅M, M⁆ := MulEquiv.isSimpleGroup f
  have hc4 : 4 ≤ Nat.card (Fin n) := by simpa using (by omega : 4 ≤ n)
  have : Nontrivial ↥(alternatingGroup (Fin n)) := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_center_eq_bot (alternatingGroup.center_eq_bot hc4)
  refine ⟨hs', f.symm a, f.symm b, fun h => hab ?_⟩
  have := congrArg f h
  simpa using this

theorem card_mulAut_commutator_perm_le {M : Subgroup Ω} {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (e : ↥M ≃* Equiv.Perm (Fin n)) :
    Nat.card (MulAut ↥⁅M, M⁆) ≤ 2 * Nat.card ↥⁅M, M⁆ := by
  obtain ⟨f⟩ := commutator_equiv_alternating (by omega) e
  rw [Nat.card_congr (MulAut.congr f).toEquiv, Nat.card_congr f.toEquiv]
  exact card_mulAut_alternating_le hn


theorem ident_aux [Finite Ω] {G H L : Subgroup Ω} (hHG : H ≤ G) (hLG : L ≤ G)
    (hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hself : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L)
    (hq : CFSG.IsQuasisimple ↥L) (hne : H ≠ L)
    (hDn : ∃ a b : ↥⁅H, H⁆, a * b ≠ b * a) (hDs : IsSimpleGroup ↥⁅H, H⁆)
    (haut : Nat.card (MulAut ↥⁅H, H⁆) ≤ 2 * Nat.card ↥⁅H, H⁆) : L = ⁅H, H⁆ ∧ G = H := by
  have hL : L = ⁅H, H⁆ := eq_commutator_of_normal_simple hHG hLG hHn hLn hself hq hDn hDs
  refine ⟨hL, ?_⟩
  have hLH : L ≤ H := hL ▸ commutator_le_self_aux H
  refine eq_of_card_mulAut_le hLH hHG hne hLn ?_ (by rw [hL]; exact haut)
  intro g hg hcomm
  have hgL : g ∈ L := hself g hg hcomm
  subst hL
  have hcen : (⟨g, hgL⟩ : ↥⁅H, H⁆) ∈ Subgroup.center ↥⁅H, H⁆ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2).symm
  rw [center_eq_bot_of_simple hDn, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

end Ident

section PermPerfect

theorem perm_not_isPerfect {n : ℕ} (hn : 5 ≤ n) : ¬ Group.IsPerfect (Equiv.Perm (Fin n)) := by
  intro hp
  have h1 : commutator (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) :=
    alternatingGroup.commutator_perm_eq (by simpa using hn)
  have h2 : commutator (Equiv.Perm (Fin n)) = ⊤ := hp.commutator_eq_top
  rw [h1] at h2
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [ha, hb] at this
  have hmem : Equiv.swap a b ∈ alternatingGroup (Fin n) := by
    rw [h2]
    trivial
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab] at hmem
  exact absurd hmem (by decide)

theorem not_surjective_perm_of_perfect {n : ℕ} (hn : 5 ≤ n) {Q : Type*} [Group Q] [Nontrivial Q]
    [Group.IsPerfect Q] : ¬ ∃ π : Equiv.Perm (Fin n) →* Q, Function.Surjective π := by
  rintro ⟨π, hπ⟩
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  by_cases hN : Nontrivial π.ker
  · have hA : alternatingGroup (Fin n) ≤ π.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal hcard hN
    have h1 : (commutator (Equiv.Perm (Fin n))).map π = commutator Q := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 hπ, ← commutator_def]
    rw [alternatingGroup.commutator_perm_eq hcard] at h1
    have h2 : (alternatingGroup (Fin n)).map π = ⊥ := by
      rw [eq_bot_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot]
      exact hA
    rw [h2, Group.IsPerfect.commutator_eq_top] at h1
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    have hx' : x ∈ (⊤ : Subgroup Q) := Subgroup.mem_top x
    rw [← h1, Subgroup.mem_bot] at hx'
    exact hx hx'
  · have hker : π.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hne
      exact hN ⟨⟨⟨x, hx⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
    have hbij : Function.Bijective π := ⟨(MonoidHom.ker_eq_bot_iff π).1 hker, hπ⟩
    let e : Equiv.Perm (Fin n) ≃* Q := MulEquiv.ofBijective π hbij
    have : Group.IsPerfect (Equiv.Perm (Fin n)) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact perm_not_isPerfect hn this

end PermPerfect

end FFC

end CFSG.Quasithin
