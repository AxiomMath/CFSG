module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res417Three

@[expose] def IsDatum417 (X : Type) [Group X] (D : Subgroup X) : Prop :=
  CFSG.Assembly.IsElemAbelian 3 D ∧
    (∀ x : X, x ^ 3 = 1 → (∀ d ∈ D, x * d = d * x) → x ∈ D) ∧
    ∃ F : Subgroup X, F ≤ D ∧ 9 ≤ Nat.card F ∧ ∃ T : Subgroup X, IsPGroup 2 T ∧
      F ≤ Subgroup.normalizer (T : Set X) ∧ ¬ T ≤ Subgroup.centralizer (F : Set X)

theorem IsDatum417.map {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y) {D : Subgroup X}
    (h : IsDatum417 X D) : IsDatum417 Y (D.map ψ.toMonoidHom) := by
  obtain ⟨hD, hmax, F, hFD, hF9, T, hT2, hFT, hTF⟩ := h
  refine ⟨isElemAbelian_map ψ.toMonoidHom hD, fun y hy3 hyD => ?_, F.map ψ.toMonoidHom,
    Subgroup.map_mono hFD, ?_, T.map ψ.toMonoidHom, hT2.map _, ?_, ?_⟩
  · have hx3 : (ψ.symm y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hxD : ∀ d ∈ D, ψ.symm y * d = d * ψ.symm y := by
      intro d hd
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hyD (ψ d) (Subgroup.mem_map_of_mem _ hd)
    have := hmax _ hx3 hxD
    exact ⟨_, this, by simp⟩
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact hF9
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hFT
  · intro hle
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_map_of_mem ψ.toMonoidHom ht))
      (ψ f) (Subgroup.mem_map_of_mem _ hf)
    apply ψ.injective
    simpa [map_mul] using this

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_isPGroup (h2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G}
    (hL : L.IsSubnormal) (hθ : IsPGroup 2 (aschbacherSolvableCore 3 L)) :
    aschbacherSolvableCore 3 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle1 : aschbacherSolvableCore 3 L ≤ CFSG.Open.pCore 2 L := by
    exact le_sSup ⟨inferInstance, hθ⟩
  have hle2 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hL
  rw [h2] at hle2
  have hle : (aschbacherSolvableCore 3 L).map L.subtype ≤ ⊥ :=
    (Subgroup.map_mono (f := L.subtype) hle1).trans hle2
  rw [le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hle
  exact hle

theorem theta_eq_bot_of_two_three (h2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L)
    (hZ : ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card (Subgroup.center L)) :
    aschbacherSolvableCore 3 L = ⊥ := by
  refine theta_eq_bot_of_isPGroup h2 hL.2 ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθZ := aschbacherSolvableCore_le_center hL.1
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_pos (α := aschbacherSolvableCore 3 L)).ne' fun {q} hq hqd => ?_)
  have hqZ : q ∣ Nat.card (Subgroup.center L) := hqd.trans (Subgroup.card_dvd_of_le hθZ)
  have hq2 := hq.two_le
  rcases (show q = 2 ∨ q = 3 ∨ 3 < q by omega) with h | h | h
  · exact h
  · exact absurd (h ▸ hqd) hθ3
  · exact absurd hqZ (hZ q hq h)

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.mem_centralizer (h : IsInnerOutConf417 L A E c m) :
    c ∈ Subgroup.centralizer (L : Set G) := by
  have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := h.2.2.2.2.1.2.2.1 ▸ Subgroup.mem_zpowers c
  exact this.2

theorem IsInnerOutConf417.commute (h : IsInnerOutConf417 L A E c m) {l : G} (hl : l ∈ L) :
    c * l = l * c :=
  (Subgroup.mem_centralizer_iff.mp h.mem_centralizer l hl).symm

theorem IsInnerOutConf417.card_eq (h : IsInnerOutConf417 L A E c m) :
    Nat.card A = 3 * Nat.card (A ⊓ L : Subgroup G) := by
  obtain ⟨hAmax, -, -, hc3, -⟩ := h.2.2.2.2.1
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (h.commute hy.2) k).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, -, hxL⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_bot]
    by_contra hne
    apply h.2.2.2.2.2.2.2.2.2.1
    have hord : orderOf (c ^ k) = 3 := by
      refine orderOf_eq_prime ?_ hne
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3,
        pow_orderOf_eq_one, one_zpow]
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers (c ^ k) := by
      apply le_of_eq
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
        (Subgroup.zpow_mem_zpowers c k)) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, hc3]
    exact (Subgroup.zpowers_le.mpr hxL) (hle (Subgroup.mem_zpowers c))
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3, ← h.2.2.2.2.2.2.2.2.2.2.2] at hcard
  exact hcard

theorem IsInnerOutConf417.card_inf (h : IsInnerOutConf417 L A E c m) :
    Nat.card (A ⊓ L : Subgroup G) = 3 ^ (m - 1) := by
  have h1 := h.card_eq
  rw [h.2.2.2.2.1.2.1] at h1
  have hm := three_le_of_isQuad h.2.2.2.2.1
  have : 3 ^ m = 3 * 3 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  omega

theorem IsInnerOutConf417.datum (h : IsInnerOutConf417 L A E c m) {X : Type} [Group X]
    (ψ : L ≃* X) :
    IsDatum417 X (((A ⊓ L).subgroupOf L).map ψ.toMonoidHom) ∧
      Nat.card (((A ⊓ L).subgroupOf L).map ψ.toMonoidHom) = 3 ^ (m - 1) ∧
      Nonempty (autIn L A ≃* autIn ⊤ (((A ⊓ L).subgroupOf L).map ψ.toMonoidHom)) := by
  obtain ⟨hAmax, -, hAc, hc3, hE, hEA, T, hT, hTE⟩ := h.2.2.2.2.1
  have hA := hAmax.prop
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) := h.2.2.2.2.2.2.2.2.2.2.2
  have hcA : c ∈ A := (hAc ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ _).1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hTL, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
  set D₀ : Subgroup G := A ⊓ L with hD₀
  set D : Subgroup X := (D₀.subgroupOf L).map ψ.toMonoidHom with hD
  have hcardD : Nat.card D = Nat.card D₀ := by
    rw [hD, Subgroup.card_map_of_injective ψ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨⟨?_, ?_, ?_⟩, by rw [hcardD]; exact h.card_inf, ?_⟩
  ·
    have hD₀ab : CFSG.Assembly.IsElemAbelian 3 (D₀.subgroupOf L) := by
      refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · exact hcomm _ (Subgroup.mem_subgroupOf.mp x.2).1 _ (Subgroup.mem_subgroupOf.mp y.2).1
      · simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hx).1
    exact isElemAbelian_map ψ.toMonoidHom hD₀ab
  ·
    intro x hx3 hxD
    set y : L := ψ.symm x with hy
    have hy3 : (y : G) ^ 3 = 1 := by
      have : y ^ 3 = 1 := by rw [hy, ← map_pow, hx3, map_one]
      simpa using congrArg Subtype.val this
    have hyD : ∀ d ∈ D₀, (y : G) * d = d * y := by
      intro d hd
      have h1 := hxD (ψ ⟨d, hd.2⟩) ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
      have h2 : y * ⟨d, hd.2⟩ = ⟨d, hd.2⟩ * y := by
        apply ψ.injective
        rw [map_mul, map_mul, hy, MulEquiv.apply_symm_apply]
        exact h1
      exact congrArg Subtype.val h2
    have hyA : (y : G) ∈ A := by
      refine mem_of_maximal_of_commute hAmax hy3 fun a ha => ?_
      have hle : A ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
        rw [hAeq]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact h.commute y.2
        · intro d hd
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hyD d hd).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    refine ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hyA, y.2⟩, ?_⟩
    simp [hy]
  ·
    set F₀ : Subgroup G := (E ⊔ Subgroup.zpowers c) ⊓ L with hF₀
    have hEc : E ⊔ Subgroup.zpowers c ≤ A := sup_le hEA (Subgroup.zpowers_le.mpr hcA)
    have hcommF : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ F₀, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (h.commute hy.2) k).eq
    obtain ⟨hcardF, hsetF⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommF
    have hcommA : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ D₀, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (h.commute hy.2) k).eq
    obtain ⟨-, hsetA⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommA
    have hEF : E ⊔ Subgroup.zpowers c ≤ Subgroup.zpowers c ⊔ F₀ := by
      intro e he
      have heA : e ∈ ((Subgroup.zpowers c ⊔ D₀ : Subgroup G) : Set G) := by
        rw [← hAeq]
        exact hEc he
      rw [hsetA] at heA
      obtain ⟨x, hx, d, hd, rfl⟩ := heA
      have hdF : d ∈ F₀ := by
        refine ⟨?_, (hd : d ∈ D₀).2⟩
        have : d = x⁻¹ * (x * d) := by group
        rw [this]
        exact (E ⊔ Subgroup.zpowers c).mul_mem
          (Subgroup.mem_sup_right ((Subgroup.zpowers c).inv_mem hx)) he
      exact Subgroup.mul_mem_sup hx hdF
    have hF9 : 9 ≤ Nat.card F₀ := by
      have h1 : 27 ≤ Nat.card (Subgroup.zpowers c ⊔ F₀ : Subgroup G) := by
        rw [← hE.2]
        exact (Subgroup.card_le_of_le le_sup_left).trans (Subgroup.card_le_of_le hEF)
      have h2 : 1 ≤ Nat.card (Subgroup.zpowers c ⊓ F₀ : Subgroup G) := Nat.card_pos
      rw [Nat.card_zpowers, hc3] at hcardF
      nlinarith
    have hcT : c ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.centralizer_le_normalizer (T : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (h.commute (hTL ht)).symm
    have hEcN : E ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (T : Set G) :=
      sup_le hTN (Subgroup.zpowers_le.mpr hcT)
    refine ⟨(F₀.subgroupOf L).map ψ.toMonoidHom, ?_, ?_, (T.subgroupOf L).map ψ.toMonoidHom,
      ?_, ?_, ?_⟩
    · refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ?_
      exact inf_le_inf_right L hEc (Subgroup.mem_subgroupOf.mp hx)
    · rw [Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hF9
    · have h1 : IsPGroup 2 (T.subgroupOf L) :=
        hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
      exact h1.map _
    · have hN : F₀.subgroupOf L ≤ Subgroup.normalizer ((T.subgroupOf L : Subgroup L) : Set L) := by
        intro f hf
        have hfG : (f : G) ∈ Subgroup.normalizer (T : Set G) :=
          hEcN (Subgroup.mem_subgroupOf.mp hf).1
        rw [Subgroup.mem_normalizer_iff]
        intro t
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simpa using Subgroup.mem_normalizer_iff.mp hfG (t : G)
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hN
    · intro hle
      apply hTE
      have hFT : ∀ f ∈ F₀, ∀ t ∈ T, f * t = t * f := by
        intro f hf t ht
        have h1 := Subgroup.mem_centralizer_iff.mp
          (hle ⟨⟨t, hTL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩) (ψ ⟨f, hf.2⟩)
          ⟨⟨f, hf.2⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
        have h2 : (⟨f, hf.2⟩ : L) * ⟨t, hTL ht⟩ = ⟨t, hTL ht⟩ * ⟨f, hf.2⟩ := by
          apply ψ.injective
          rw [map_mul, map_mul]
          exact h1
        exact congrArg Subtype.val h2
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have heF : e ∈ ((Subgroup.zpowers c ⊔ F₀ : Subgroup G) : Set G) :=
        hEF (Subgroup.mem_sup_left he)
      rw [hsetF] at heF
      obtain ⟨x, hx, f, hf, rfl⟩ := heF
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hck : c ^ k * t = t * c ^ k := (Commute.zpow_left (h.commute (hTL ht)) k).eq
      calc c ^ k * f * t = c ^ k * (f * t) := by group
        _ = c ^ k * (t * f) := by rw [hFT f hf t ht]
        _ = t * (c ^ k * f) := by rw [← mul_assoc, hck, mul_assoc]
  ·
    have hY : (Subgroup.zpowers c ⊔ D₀) ⊓ L = D₀ :=
      Sec13.zpowers_sup_inf_eq (by rw [← hc3]; exact pow_orderOf_eq_one c)
        h.2.2.2.2.2.2.2.2.2.1 inf_le_right (fun y hy => h.commute hy.2)
    obtain ⟨e₁⟩ := Sec13.nonempty_autIn_sup_equiv (H := L) (c := c)
      (fun l hl => (h.commute hl).symm) hY
    rw [← hAeq] at e₁
    obtain ⟨e₂⟩ := Sec13.nonempty_autIn_subgroupOf_equiv L (L := L) (A := D₀) le_rfl inf_le_right
    rw [Subgroup.subgroupOf_self] at e₂
    exact ⟨e₁.trans (e₂.symm.trans (Sporadic.autInTopCongr ψ (D₀.subgroupOf L)))⟩

end Certs

end CFSG.RankThree.PartTwo.Sec4
