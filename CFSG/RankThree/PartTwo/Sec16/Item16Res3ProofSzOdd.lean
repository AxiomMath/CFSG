module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofOmegaSolv
import CFSG.RankThree.PartOne.S15K.AutLayer
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open scoped commutatorElement

namespace Res3Omega

section Aut

variable {X : Type*} [Group X]

@[expose] def restrictAut (σ : MulAut X) (M : Subgroup X) (hM : M.map σ.toMonoidHom = M) :
    MulAut M :=
  (σ.subgroupMap M).trans (MulEquiv.subgroupCongr hM)

theorem coe_restrictAut (σ : MulAut X) (M : Subgroup X) (hM : M.map σ.toMonoidHom = M) (x : M) :
    ((restrictAut σ M hM x : M) : X) = σ x :=
  rfl

theorem apply_three (σ : MulAut X) (hσ : σ ^ 3 = 1) (x : X) : σ (σ (σ x)) = x := by
  have h := congrArg (fun τ : MulAut X => τ x) hσ
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
  exact h

theorem map_map_map (σ : MulAut X) (hσ : σ ^ 3 = 1) (M : Subgroup X) :
    ((M.map σ.toMonoidHom).map σ.toMonoidHom).map σ.toMonoidHom = M := by
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : (σ.toMonoidHom.comp σ.toMonoidHom).comp σ.toMonoidHom = MonoidHom.id X := by
    ext x
    exact apply_three σ hσ x
  rw [h, Subgroup.map_id]

theorem commutator_mem_inf {N N' : Subgroup X} [N.Normal] [N'.Normal] {a b : X} (ha : a ∈ N)
    (hb : b ∈ N') : a * b * a⁻¹ * b⁻¹ ∈ N ⊓ N' := by
  refine ⟨?_, ?_⟩
  · have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact N.mul_mem ha ((inferInstance : N.Normal).conj_mem _ (N.inv_mem ha) b)
  · have := (inferInstance : N'.Normal).conj_mem _ hb a
    exact N'.mul_mem this (N'.inv_mem hb)

theorem eq_or_eq_top_of_le {N K : Subgroup X} [N.Normal] [IsSimpleGroup (X ⧸ N)] [hK : K.Normal]
    (hNK : N ≤ K) : K = N ∨ K = ⊤ := by
  have hKn : (K.map (QuotientGroup.mk' N)).Normal := hK.map _ (QuotientGroup.mk'_surjective N)
  rcases hKn.eq_bot_or_eq_top with h | h
  · left
    refine le_antisymm ?_ hNK
    intro k hk
    have : QuotientGroup.mk' N k ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    rw [eq_top_iff]
    intro x _
    have : QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := this
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact K.mul_mem hk (hNK hkx)

end Aut

section KP

theorem isSolvable_of_aut : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = n →
    CFSG.IsKGroup X → ¬ 3 ∣ Nat.card X → ∀ σ : MulAut X, σ ^ 3 = 1 →
      (∀ x : X, σ x = x → (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1) → Group.IsSolvable X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hK h3 σ hσ hfix
  by_cases hM : ∃ M : Subgroup X, M.Normal ∧ M.map σ.toMonoidHom = M ∧ M ≠ ⊥ ∧ M ≠ ⊤
  · obtain ⟨M, hMn, hMσ, hM1, hMt⟩ := hM
    have hM3 : ¬ 3 ∣ Nat.card M := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card M))
    have hMsol : Group.IsSolvable M := by
      refine ih (Nat.card M) ?_ M rfl (CFSG.RankThree.PartOne.N143.isKGroup_subgroup hK M) hM3
        (restrictAut σ M hMσ) ?_ ?_
      · rw [← hn, ← Subgroup.card_top (G := X)]
        exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hMt)
      · refine MulEquiv.ext fun x => Subtype.ext ?_
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply,
          coe_restrictAut]
        exact apply_three σ hσ x
      · intro x hx hx2
        apply Subtype.ext
        refine hfix x (congrArg Subtype.val hx) ?_
        obtain ⟨k, hk⟩ := hx2
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hQsol : Group.IsSolvable (X ⧸ M) := by
      set σ' : MulAut (X ⧸ M) := QuotientGroup.congr M M σ hMσ with hσ'
      have hσ'mk : ∀ y : X, σ' (y : X ⧸ M) = ((σ y : X) : X ⧸ M) := fun y => rfl
      refine ih (Nat.card (X ⧸ M)) ?_ (X ⧸ M) rfl
        (CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hK M)
        (fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card M))) σ' ?_ ?_
      · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
        have h2 : Nat.card M ≠ 1 := fun h => hM1 (Subgroup.card_eq_one.mp h)
        have h0 : 0 < Nat.card (X ⧸ M) := Nat.card_pos
        have h0' : 0 < Nat.card M := Nat.card_pos
        rw [← hn, h1]
        have : 2 ≤ Nat.card M := by omega
        nlinarith
      · refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H y =>
          simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hσ'mk]
          rw [apply_three σ hσ y]
      · intro q hq hq2
        obtain ⟨y, hy, rfl⟩ := CFSG.RankThree.PartOne.S15K.exists_fixed_lift Nat.prime_three
          (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
          (by rwa [QuotientGroup.ker_mk']) σ hσ σ' (fun y => rfl) hq
        obtain ⟨a, m, hm, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
        have hy' : y ^ m = 1 := hfix (y ^ m) (by rw [map_pow, hy]) ⟨a, by
          rw [← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]⟩
        obtain ⟨k, hk⟩ := hq2
        have h1 : (QuotientGroup.mk' M y) ^ m = 1 := by rw [← map_pow, hy', map_one]
        have hcop : Nat.Coprime m (2 ^ k) :=
          Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
        have h2 := pow_gcd_eq_one.mpr ⟨h1, hk⟩
        rwa [hcop.gcd_eq_one, pow_one] at h2
    exact Group.isSolvable_of_ker_le_range M.subtype (QuotientGroup.mk' M)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  push Not at hM
  have hsimp : ∀ M : Subgroup X, M.Normal → M.map σ.toMonoidHom = M → M ≠ ⊤ → M = ⊥ :=
    fun M hMn hMσ hMt => by
      by_contra h0
      exact hMt (hM M hMn hMσ h0)
  have hchar : ∀ K : Subgroup X, K.Characteristic → K.map σ.toMonoidHom = K :=
    fun K hK => Subgroup.characteristic_iff_map_eq.mp hK σ
  by_cases hX : Subsingleton X
  · infer_instance
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp hX
  have hcharC : (commutator X).Characteristic := by
    show Subgroup.Characteristic (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆)
    infer_instance
  by_cases hab : commutator X = ⊤
  swap
  · have h0 := hsimp _ inferInstance (hchar _ hcharC) hab
    refine Group.isSolvable_of_comm fun a b => ?_
    have h1 : ⁅a, b⁆ ∈ commutator X := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hperf : Group.IsPerfect X := ⟨hab⟩
  have hZ : Subgroup.center X = ⊥ := by
    refine hsimp _ inferInstance (hchar _ inferInstance) fun h => ?_
    have : IsMulCommutative X := ⟨⟨fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative X this
  obtain ⟨N₁, hN₁n, hN₁t, hN₁s⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.exists_normal_isSimpleGroup_quotient X
  have hnab : ∃ a b : X ⧸ N₁, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have : Group.IsPerfect (X ⧸ N₁) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N₁) (QuotientGroup.mk'_surjective N₁)
    have : Nontrivial (X ⧸ N₁) := hN₁s.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative (X ⧸ N₁) ⟨⟨hc⟩⟩
  have hcat : CFSG.Assembly.InCatalog (X ⧸ N₁) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK ⊤ (X ⧸ N₁)
      ((QuotientGroup.mk' N₁).comp (⊤ : Subgroup X).subtype) (fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₁ q
        exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  obtain ⟨e, hSz⟩ := KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd (X ⧸ N₁) hnab hcat
    (fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card N₁)))
  have h2Q : 2 ∣ Nat.card (X ⧸ N₁) := two_dvd_card_of_suzukiModel hSz
  set N₂ := N₁.map σ.toMonoidHom with hN₂
  set N₃ := N₂.map σ.toMonoidHom with hN₃
  have hN₂n : N₂.Normal := hN₁n.map _ σ.surjective
  have hN₃n : N₃.Normal := hN₂n.map _ σ.surjective
  have hN₃σ : N₃.map σ.toMonoidHom = N₁ := map_map_map σ hσ N₁
  have hI : N₁ ⊓ N₂ ⊓ N₃ = ⊥ := by
    refine hsimp _ inferInstance ?_
      (fun h => hN₁t (top_le_iff.mp (h ▸ (inf_le_left.trans inf_le_left))))
    rw [Subgroup.map_inf_eq _ _ _ σ.injective, Subgroup.map_inf_eq _ _ _ σ.injective, hN₃σ,
      ← hN₂, ← hN₃, inf_comm, ← inf_assoc]
  have hmemI : ∀ {z : X}, z ∈ N₁ → z ∈ N₂ → z ∈ N₃ → z = 1 := fun h1 h2 h3 => by
    have : _ ∈ N₁ ⊓ N₂ ⊓ N₃ := ⟨⟨h1, h2⟩, h3⟩
    rwa [hI, Subgroup.mem_bot] at this
  by_cases hA : N₂ = N₁
  ·
    have hN₁b : N₁ = ⊥ := hsimp N₁ hN₁n hA hN₁t
    let eX : X ≃* X ⧸ N₁ :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hN₁b.symm)
    have : IsSimpleGroup X := eX.isSimpleGroup
    have hnabX : ∃ a b : X, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      exact Group.IsPerfect.not_isMulCommutative X ⟨⟨hc⟩⟩
    have hcatX : CFSG.Assembly.InCatalog X :=
      CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK ⊤ X
        (⊤ : Subgroup X).subtype (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    obtain ⟨e', hSzX⟩ := KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd X hnabX hcatX h3
    obtain ⟨t, ht, hft⟩ := KFacts.KP7.exists_involution_fixed_of_suzukiModel hSzX
      (MonoidHom.id (MulAut X)) (E := Subgroup.zpowers σ) (fun x hx => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow])
    have ht1 : t = 1 := hfix t (hft σ (Subgroup.mem_zpowers σ)) ⟨1, by
      rw [pow_one, ← ht, pow_orderOf_eq_one]⟩
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  ·
    have hN₁0 : N₁ ≠ ⊥ := fun h => hA (by rw [hN₂, h, Subgroup.map_bot])
    have hclaim : ¬ N₂ ⊓ N₃ ≤ N₁ := by
      intro hle
      have h23 : N₂ ⊓ N₃ = ⊥ := by
        rw [← hI, inf_assoc]
        exact le_antisymm (le_inf hle le_rfl) inf_le_right
      have h31 : N₃ ⊓ N₁ = ⊥ := by
        have := congrArg (Subgroup.map σ.toMonoidHom) h23
        rwa [Subgroup.map_inf_eq _ _ _ σ.injective, hN₃σ, Subgroup.map_bot] at this
      have h12 : N₁ ⊓ N₂ = ⊥ := by
        have := congrArg (Subgroup.map σ.toMonoidHom) h31
        rwa [Subgroup.map_inf_eq _ _ _ σ.injective, hN₃σ, Subgroup.map_bot] at this
      have hsup : N₁ ⊔ N₂ = ⊤ := by
        rcases eq_or_eq_top_of_le (N := N₁) (K := N₁ ⊔ N₂) le_sup_left with h | h
        · exfalso
          have hN₂le : N₂ ≤ N₁ := h ▸ le_sup_right
          have hN₂b : N₂ = ⊥ := le_bot_iff.mp (h12 ▸ le_inf hN₂le le_rfl)
          exact hN₁0 ((Subgroup.map_eq_bot_iff_of_injective N₁ σ.injective).mp hN₂b)
        · exact h
      have hN₃Z : N₃ ≤ Subgroup.center X := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro g
        have hcz : ∀ {N : Subgroup X} [N.Normal], N₃ ⊓ N = ⊥ → N ≤
            Subgroup.centralizer ({z} : Set X) := fun {N} _ hN w hw => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := commutator_mem_inf (N := N₃) (N' := N) hz hw
          rw [hN, Subgroup.mem_bot] at h1
          calc w * z = (z * w * z⁻¹ * w⁻¹)⁻¹ * (z * w) := by group
            _ = z * w := by rw [h1, inv_one, one_mul]
        have hle : N₁ ⊔ N₂ ≤ Subgroup.centralizer ({z} : Set X) :=
          sup_le (hcz h31) (hcz (by rw [inf_comm]; exact h23))
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hsup ▸ Subgroup.mem_top g))
      have hN₃b : N₃ = ⊥ := le_bot_iff.mp (hZ ▸ hN₃Z)
      apply hN₁0
      rw [← hN₃σ, hN₃b, Subgroup.map_bot]
    have hsup' : N₂ ⊓ N₃ ⊔ N₁ = ⊤ := by
      rcases eq_or_eq_top_of_le (N := N₁) (K := N₂ ⊓ N₃ ⊔ N₁) le_sup_right with h | h
      · exact absurd (h ▸ le_sup_left) hclaim
      · exact h
    have hsurj : Function.Surjective ((QuotientGroup.mk' N₁).comp (N₂ ⊓ N₃).subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₁ q
      have hx : x ∈ N₂ ⊓ N₃ ⊔ N₁ := hsup' ▸ Subgroup.mem_top x
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      refine ⟨⟨y, hy⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa using hz
    have h2 : 2 ∣ Nat.card (N₂ ⊓ N₃ : Subgroup X) :=
      h2Q.trans (Subgroup.card_dvd_of_surjective hsurj)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hyo' : orderOf y = 2 := by
      rw [← hyo, Subgroup.orderOf_mk]
    have hy2 : y ^ 2 = 1 := by rw [← hyo', pow_orderOf_eq_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hyo'
      exact absurd hyo' (by norm_num)
    obtain ⟨hy₂, hy₃⟩ := Subgroup.mem_inf.mp hy
    have hsy₃ : σ y ∈ N₃ := ⟨y, hy₂, rfl⟩
    have hsy₁ : σ y ∈ N₁ := hN₃σ ▸ ⟨y, hy₃, rfl⟩
    have hssy₁ : σ (σ y) ∈ N₁ := hN₃σ ▸ ⟨σ y, hsy₃, rfl⟩
    have hssy₂ : σ (σ y) ∈ N₂ := ⟨σ y, hsy₁, rfl⟩
    have hcommI : ∀ {a b : X} {P Q : Subgroup X} [P.Normal] [Q.Normal], a ∈ P → b ∈ Q →
        (a * b * a⁻¹ * b⁻¹ ∈ P ⊓ Q → a * b * a⁻¹ * b⁻¹ = 1) → a * b = b * a :=
      fun {a b} {P Q} _ _ ha hb h => by
        have h1 := h (commutator_mem_inf ha hb)
        calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
          _ = b * a := by rw [h1, one_mul]
    have c12 : y * σ y = σ y * y := hcommI (P := N₂) (Q := N₁) hy₂ hsy₁ fun h =>
      hmemI h.2 h.1 (N₃.mul_mem (N₃.mul_mem (N₃.mul_mem hy₃ hsy₃) (N₃.inv_mem hy₃))
        (N₃.inv_mem hsy₃))
    have c13 : y * σ (σ y) = σ (σ y) * y := hcommI (P := N₃) (Q := N₁) hy₃ hssy₁ fun h =>
      hmemI h.2 (N₂.mul_mem (N₂.mul_mem (N₂.mul_mem hy₂ hssy₂) (N₂.inv_mem hy₂))
        (N₂.inv_mem hssy₂)) h.1
    have c23 : σ y * σ (σ y) = σ (σ y) * σ y := hcommI (P := N₃) (Q := N₂) hsy₃ hssy₂ fun h =>
      hmemI (N₁.mul_mem (N₁.mul_mem (N₁.mul_mem hsy₁ hssy₁) (N₁.inv_mem hsy₁))
        (N₁.inv_mem hssy₁)) h.2 h.1
    set x := y * σ y * σ (σ y) with hx
    have hσx : σ x = x := by
      rw [hx, map_mul, map_mul, apply_three σ hσ y]
      calc σ y * σ (σ y) * y = σ y * (y * σ (σ y)) := by rw [mul_assoc, c13]
        _ = y * σ y * σ (σ y) := by rw [← mul_assoc, ← c12]
    have hx2 : x ^ 2 = 1 := by
      have hc1 : Commute (y * σ y) (σ (σ y)) :=
        Commute.mul_left (show Commute y (σ (σ y)) from c13)
          (show Commute (σ y) (σ (σ y)) from c23)
      have hs2 : (σ y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
      have hss2 : (σ (σ y)) ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
      rw [hx, hc1.mul_pow, (show Commute y (σ y) from c12).mul_pow, hy2, hs2, hss2, one_mul,
        one_mul]
    have hx1 : x ≠ 1 := by
      intro h1
      have hyN₁ : y ∈ N₁ := by
        have : y = (σ y * σ (σ y))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
          exact h1
        rw [this]
        exact N₁.inv_mem (N₁.mul_mem hsy₁ hssy₁)
      exact hy1 (hmemI hyN₁ hy₂ hy₃)
    exact (hx1 (hfix x hσx ⟨1, by rw [pow_one]; exact hx2⟩)).elim

theorem ks1616SzOdd : KS1616SzOdd := by
  intro Y _ _ hK X c h3 hcN hc3 hodd
  set σ : MulAut X := Res163.conjAut X hcN with hσdef
  have hσx : ∀ x : X, ((σ x : X) : Y) = c * x * c⁻¹ := fun x => Res163.conjAut_apply X hcN x
  have hσ3 : σ ^ 3 = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hσx]
    calc c * (c * (c * (x : Y) * c⁻¹) * c⁻¹) * c⁻¹ = c ^ 3 * (x : Y) * (c ^ 3)⁻¹ := by
          rw [pow_three]
          group
      _ = x := by rw [hc3]; group
  have hfix : ∀ x : X, σ x = x → (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1 := by
    intro x hx ⟨k, hk⟩
    by_contra hx1
    have hxC : (x : Y) ∈ X ⊓ Subgroup.centralizer ({c} : Set Y) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : c * (x : Y) * c⁻¹ = x := by rw [← hσx, hx]
      calc (x : Y) * c = (c * (x : Y) * c⁻¹) * c := by rw [h1]
        _ = c * x := by group
    have hk' : (x : Y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hx1 (Subtype.ext hj)
    have h2 : 2 ∣ Nat.card (X ⊓ Subgroup.centralizer ({c} : Set Y) : Subgroup Y) := by
      have := Subgroup.orderOf_dvd_natCard _ hxC
      rw [hj] at this
      exact (dvd_pow_self 2 hj0).trans this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  exact isSolvable_of_aut (Nat.card X) X rfl (CFSG.RankThree.PartOne.N143.isKGroup_subgroup hK X)
    h3 σ hσ3 hfix

end KP

end Res3Omega

open Res3Omega

end CFSG.RankThree.PartTwo.Sec16
