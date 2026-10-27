module

public import CFSG.Quasithin.Background.G8Basic
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SignalizerFunctorTheorem.Coprime
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsSubgroupComplementIn (A B D : Subgroup G) : Prop :=
  B ≤ A ∧ D ≤ A ∧ B ⊓ D = ⊥ ∧ B ⊔ D = A

namespace G8

theorem commute_of_isElemAbelian {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hA ha hb

theorem isElemAbelian_mono {p : ℕ} {A D : Subgroup G} (hA : IsElemAbelian p A) (h : D ≤ A) :
    IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono hA h

theorem mem_sup_of_commute {B D : Subgroup G} (h : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b) {x : G}
    (hx : x ∈ B ⊔ D) : ∃ b ∈ B, ∃ d ∈ D, x = b * d := by
  have hB : B ≤ Subgroup.normalizer (D : Set G) := by
    intro b hb
    refine mem_normalizer_of_conj_mem (fun d hd => ?_) (fun d hd => ?_)
    · rw [h b hb d hd]; simpa using hd
    · have := h b⁻¹ (B.inv_mem hb) d hd
      rw [this]; simpa using hd
  have hcoe : (↑(B ⊔ D) : Set G) = (B : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B D hB
  have hx' : x ∈ (B : Set G) * (D : Set G) := by rw [← hcoe]; exact hx
  obtain ⟨b, hb, d, hd, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨b, hb, d, hd, rfl⟩

theorem card_eq_mul_of_complement {A B D : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hc : IsSubgroupComplementIn A B D) :
    Nat.card A = Nat.card B * Nat.card D := by
  obtain ⟨hBA, hDA, hBD, hsup⟩ := hc
  let f : B × D → A := fun x => ⟨(x.1 : G) * (x.2 : G), A.mul_mem (hBA x.1.2) (hDA x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨b, hb⟩, ⟨d, hd⟩⟩ ⟨⟨b', hb'⟩, ⟨d', hd'⟩⟩ h
      have h1 : b * d = b' * d' := congrArg Subtype.val h
      have h2 : b'⁻¹ * b = d' * d⁻¹ := by
        calc b'⁻¹ * b = b'⁻¹ * (b * d) * d⁻¹ := by group
          _ = b'⁻¹ * (b' * d') * d⁻¹ := by rw [h1]
          _ = d' * d⁻¹ := by group
      have h3 : b'⁻¹ * b ∈ B ⊓ D :=
        ⟨B.mul_mem (B.inv_mem hb') hb, h2 ▸ D.mul_mem hd' (D.inv_mem hd)⟩
      rw [hBD, Subgroup.mem_bot] at h3
      have h4 : b = b' := by
        have := congrArg (fun x => b' * x) h3
        simpa using this
      have h5 : d = d' := by
        subst h4
        exact mul_left_cancel h1
      subst h4; subst h5
      rfl
    · rintro ⟨a, ha⟩
      have ha' : a ∈ B ⊔ D := hsup ▸ ha
      obtain ⟨b, hb, d, hd, rfl⟩ := mem_sup_of_commute
        (fun b hb d hd => hA b (hBA hb) d (hDA hd)) ha'
      exact ⟨(⟨b, hb⟩, ⟨d, hd⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

section Finite

variable [Finite G]

theorem eq_bot_or_eq_of_card_two {B S : Subgroup G} (hB : Nat.card B = 2) (hSB : S ≤ B) :
    S = ⊥ ∨ S = B := by
  have h1 : Nat.card S ∣ Nat.card B := Subgroup.card_dvd_of_le hSB
  rw [hB] at h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact Or.inl (Subgroup.card_eq_one.mp h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hSB (by rw [h, hB]))

theorem eq_of_lt_of_card_eq_two_mul {F M B : Subgroup G} (hFM : F ≤ M) (hMB : M ≤ B)
    (hB : Nat.card B = 2 * Nat.card F) (hne : F ≠ M) : M = B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hFM
  have hF : 0 < Nat.card F := Nat.card_pos
  have h1 : Nat.card F * k ∣ Nat.card F * 2 := by
    rw [← hk, mul_comm (Nat.card F) 2, ← hB]
    exact Subgroup.card_dvd_of_le hMB
  have h2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hF h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exfalso
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hFM (by rw [hk, h, mul_one])
  · exact Subgroup.eq_of_le_of_card_ge hMB (by rw [hB, hk, h, mul_comm])

omit [Finite G] in
theorem eq_of_complement_faithful {A B D Z : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hc : IsSubgroupComplementIn A B D) (hZD : Z ≤ Subgroup.centralizer (D : Set G))
    (hfaith : B ⊓ Subgroup.centralizer (Z : Set G) = ⊥) :
    D = A ⊓ Subgroup.centralizer (Z : Set G) := by
  obtain ⟨hBA, hDA, -, hsup⟩ := hc
  apply le_antisymm
  · refine le_inf hDA fun d hd => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZD hz) d hd).symm
  · rintro a ⟨haA, haC⟩
    have haA' : a ∈ B ⊔ D := hsup ▸ haA
    obtain ⟨b, hb, d, hd, rfl⟩ :=
      mem_sup_of_commute (fun b hb d hd => hA b (hBA hb) d (hDA hd)) haA'
    have hdC : d ∈ Subgroup.centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hZD hz) d hd).symm
    have hbC : b ∈ Subgroup.centralizer (Z : Set G) := by
      have := (Subgroup.centralizer (Z : Set G)).mul_mem haC
        ((Subgroup.centralizer (Z : Set G)).inv_mem hdC)
      simpa using this
    have hb1 : b ∈ B ⊓ Subgroup.centralizer (Z : Set G) := ⟨hb, hbC⟩
    rw [hfaith, Subgroup.mem_bot] at hb1
    rw [hb1, one_mul]
    exact hd

theorem g8_2_aux {X : Subgroup G} (hXs : Group.IsSolvable X) (hXodd : Odd (Nat.card X)) :
    ∀ (n : ℕ) (A B : Subgroup G), IsElemAbelian 2 A → A ≤ Subgroup.normalizer (X : Set G) →
      B ≤ A → Nat.card B = 2 ^ n → B ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
        B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) =
          ⊥ ∧
        D = A ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :
          Set G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B hA hAX hBA hBn hfaith
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    commute_of_isElemAbelian hA ha ha'
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    ·
      have hB : B = ⊥ := Subgroup.card_eq_one.mp (by simpa using hBn)
      subst hB
      refine ⟨A, ⟨hBA, le_rfl, bot_inf_eq _, bot_sup_eq _⟩, by simp, ?_⟩
      exact eq_of_complement_faithful hAcomm ⟨hBA, le_rfl, bot_inf_eq _, bot_sup_eq _⟩
        inf_le_right (by simp)
    ·
      have hB2 : Nat.card B = 2 := by simpa using hBn
      by_cases hAB : A = B
      · subst hAB
        have hZ : X ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = X := by
          apply inf_eq_left.mpr
          intro x _
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Subgroup.mem_bot.mp hy]
          simp
        refine ⟨⊥, ⟨le_rfl, bot_le, inf_bot_eq _, sup_bot_eq _⟩, ?_, ?_⟩
        · rw [hZ]; exact hfaith
        · exact eq_of_complement_faithful hAcomm ⟨le_rfl, bot_le, inf_bot_eq _, sup_bot_eq _⟩
            inf_le_right (by rw [hZ]; exact hfaith)
      ·
        have hBne : B ≠ ⊥ := by
          intro h
          rw [h, Subgroup.card_bot] at hB2
          omega
        obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
        have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
        have hbX : b ∉ Subgroup.centralizer (X : Set G) := by
          intro hc
          have : b ∈ B ⊓ Subgroup.centralizer (X : Set G) := ⟨hbB, hc⟩
          rw [hfaith, Subgroup.mem_bot] at this
          exact hb1' this
        have hA2 : 2 ^ 2 ≤ Nat.card A := by
          obtain ⟨r, hr⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
          have h1 : 2 ≤ Nat.card A := hB2 ▸ Subgroup.card_le_of_le hBA
          have h3 : Nat.card A ≠ 2 := by
            intro h
            exact hAB (Subgroup.eq_of_le_of_card_ge hBA (by rw [h, hB2])).symm
          rw [hr] at h1 h3 ⊢
          rcases Nat.lt_or_ge r 2 with hr2 | hr2
          · interval_cases r <;> simp at h1 h3
          · exact Nat.pow_le_pow_right (by norm_num) hr2
        have hcop : Nat.Coprime 2 (Nat.card X) := (Nat.coprime_two_left.mpr hXodd)
        have hcomm := commutator_eq_iSup_hyperplanes Nat.prime_two hA hA2 hAX hcop hXs (hBA hbB)
        have hne : ⁅X, Subgroup.zpowers b⁆ ≠ ⊥ := by
          intro h
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
          apply hbX
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact (Subgroup.mem_centralizer_iff.mp (h hx) b (Subgroup.mem_zpowers b)).symm
        obtain ⟨E, hE, hEne⟩ : ∃ E ∈ hyperplanes 2 A,
            ⁅X ⊓ Subgroup.centralizer (E : Set G), Subgroup.zpowers b⁆ ≠ ⊥ := by
          by_contra hcon
          push Not at hcon
          apply hne
          rw [hcomm]
          exact iSup₂_eq_bot.mpr hcon
        obtain ⟨hEA, hEcard⟩ := hE
        have hEc : b ∉ Subgroup.centralizer
            ((X ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
          intro hc
          apply hEne
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          have hxb : Commute x b := Subgroup.mem_centralizer_iff.mp hc x hx
          exact (hxb.zpow_right k).eq.symm
        have hbE : b ∉ E := by
          intro hbE
          apply hEc
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact (Subgroup.mem_centralizer_iff.mp hx.2 b hbE).symm
        have hBE : B ⊓ E = ⊥ := by
          rcases eq_bot_or_eq_of_card_two hB2 (inf_le_left : B ⊓ E ≤ B) with h | h
          · exact h
          · exfalso
            apply hbE
            have : b ∈ B ⊓ E := h.ge hbB
            exact this.2
        have hBEsup : B ⊔ E = A := by
          refine eq_of_lt_of_card_eq_two_mul (F := E) le_sup_right (sup_le hBA hEA) hEcard ?_
          intro h
          exact hbE (h ▸ (le_sup_left : B ≤ B ⊔ E) hbB)
        have hfa : B ⊓ Subgroup.centralizer
            ((X ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) = ⊥ := by
          rcases eq_bot_or_eq_of_card_two hB2 (inf_le_left : B ⊓ _ ≤ B) with h | h
          · exact h
          · exfalso
            apply hEc
            have : b ∈ B ⊓ Subgroup.centralizer
                ((X ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := h.ge hbB
            exact this.2
        exact ⟨E, ⟨hBA, hEA, hBE, hBEsup⟩, hfa,
          eq_of_complement_faithful hAcomm ⟨hBA, hEA, hBE, hBEsup⟩ inf_le_right hfa⟩
  ·
    obtain ⟨F, hFB, hFcard⟩ : ∃ F : Subgroup G, F ≤ B ∧ Nat.card F = 2 ^ (n - 1) := by
      have hdvd : 2 ^ (n - 1) ∣ Nat.card B := by
        rw [hBn]; exact pow_dvd_pow 2 (Nat.sub_le n 1)
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 2 hdvd
      exact ⟨K.map B.subtype, Subgroup.map_subtype_le K, by
        rw [Subgroup.card_map_of_injective B.subtype_injective]; exact hK⟩
    have hFA : F ≤ A := hFB.trans hBA
    have hFfaith : F ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
      le_bot_iff.mp (hfaith ▸ inf_le_inf_right _ hFB)
    obtain ⟨D', ⟨-, hD'A, hFD', hFD'sup⟩, hFfD', hD'eq⟩ :=
      ih (n - 1) (by omega) A F hA hAX hFA hFcard hFfaith
    have hFne : ∃ b ∈ B, b ∉ F := by
      by_contra hcon
      push Not at hcon
      have h1 : F = B := le_antisymm hFB (fun b hb => hcon b hb)
      have h2 : Nat.card F = Nat.card B := by rw [h1]
      rw [hFcard, hBn] at h2
      have h3 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨b, hbB, hbF⟩ := hFne
    have hbFD' : b ∈ F ⊔ D' := hFD'sup ▸ hBA hbB
    obtain ⟨f, hf, d, hd, hbfd⟩ := mem_sup_of_commute
      (fun f hf d hd => hAcomm f (hFA hf) d (hD'A hd)) hbFD'
    have hdeq : d = f⁻¹ * b := by rw [hbfd]; group
    have hdB : d ∈ B := by
      rw [hdeq]; exact B.mul_mem (B.inv_mem (hFB hf)) hbB
    have hd1 : d ≠ 1 := by
      intro h
      apply hbF
      rw [hbfd, h, mul_one]; exact hf
    have hd2 : d ^ 2 = 1 := hA.2 d (hD'A hd)
    set B' := Subgroup.zpowers d with hB'
    have hB'card : Nat.card B' = 2 ^ 1 := by
      rw [hB', Nat.card_zpowers, orderOf_eq_prime hd2 hd1, pow_one]
    have hB'B : B' ≤ B := Subgroup.zpowers_le.mpr hdB
    have hB'D' : B' ≤ D' := Subgroup.zpowers_le.mpr hd
    have hdF : d ∉ F := by
      intro h
      have : d ∈ F ⊓ D' := ⟨h, hd⟩
      rw [hFD', Subgroup.mem_bot] at this
      exact hd1 this
    have hBeq : F ⊔ B' = B := by
      refine eq_of_lt_of_card_eq_two_mul (F := F) le_sup_left (sup_le hFB hB'B) ?_ ?_
      · rw [hBn, hFcard, ← pow_succ']; congr 1; omega
      · intro h
        exact hdF (h ▸ (le_sup_right : B' ≤ F ⊔ B') (Subgroup.mem_zpowers d))
    have hBD'le : B ⊓ D' ≤ B' := by
      rintro y ⟨hyB, hyD'⟩
      have hy : y ∈ F ⊔ B' := hBeq ▸ hyB
      obtain ⟨f₁, hf₁, d₁, hd₁, rfl⟩ := mem_sup_of_commute
        (fun f hf d hd => hAcomm f (hFA hf) d (hD'A (hB'D' hd))) hy
      have hf₁D' : f₁ ∈ D' := by
        have := D'.mul_mem hyD' (D'.inv_mem (hB'D' hd₁))
        simpa using this
      have : f₁ ∈ F ⊓ D' := ⟨hf₁, hf₁D'⟩
      rw [hFD', Subgroup.mem_bot] at this
      rw [this, one_mul]
      exact hd₁
    have hB'faith : B' ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
      le_bot_iff.mp (hfaith ▸ inf_le_inf_right _ hB'B)
    obtain ⟨D, ⟨-, hDD', hB'D, hB'Dsup⟩, hB'fD, -⟩ :=
      ih 1 (by omega) D' B' (isElemAbelian_mono hA hD'A) (hD'A.trans hAX) hB'D' hB'card hB'faith
    have hDA : D ≤ A := hDD'.trans hD'A
    have hBD : B ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ B' ⊓ D := ⟨hBD'le ⟨hy.1, hDD' hy.2⟩, hy.2⟩
      rw [hB'D] at this
      exact this
    have hBDsup : B ⊔ D = A := by
      apply le_antisymm (sup_le hBA hDA)
      rw [← hFD'sup]
      refine sup_le (hFB.trans le_sup_left) ?_
      rw [← hB'Dsup]
      exact sup_le (hB'B.trans le_sup_left) le_sup_right
    have hfa : B ⊓ Subgroup.centralizer
        ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hle : X ⊓ Subgroup.centralizer (D' : Set G) ≤ X ⊓ Subgroup.centralizer (D : Set G) :=
        inf_le_inf_left X (Subgroup.centralizer_le hDD')
      have hyD' : y ∈ D' := by
        rw [hD'eq]
        exact ⟨hBA hy.1, Subgroup.centralizer_le hle hy.2⟩
      have : y ∈ B' ⊓ Subgroup.centralizer
          ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
        ⟨hBD'le ⟨hy.1, hyD'⟩, hy.2⟩
      rw [hB'fD] at this
      exact this
    exact ⟨D, ⟨hBA, hDA, hBD, hBDsup⟩, hfa,
      eq_of_complement_faithful hAcomm ⟨hBA, hDA, hBD, hBDsup⟩ inf_le_right hfa⟩

theorem g8_5_aux {X A B Y : Subgroup G} (hXn : Group.IsNilpotent X) (hXodd : Odd (Nat.card X))
    (hA : IsElemAbelian 2 A) (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hBA : B ≤ A)
    (hYX : Y ≤ X) (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hBY : B ≤ Subgroup.centralizer (Y : Set G))
    (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
      B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) :
        Subgroup G) : Set G) = ⊥ := by
  have hB2 : IsPGroup 2 B := (isPGroup_of_isElemAbelian hA).to_le hBA
  set X' := X ⊓ Subgroup.centralizer (Y : Set G) with hX'
  have hB' : B ⊓ Subgroup.centralizer (X' : Set G) = ⊥ :=
    G8.g8_4_of hXn hXodd hB2 (hBA.trans hAX) hYX hBY hfaith
  have hX'nil : Group.IsNilpotent X' := by
    have := hXn
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X' ≤ X))).mp
      inferInstance
  have hX's : Group.IsSolvable X' := by
    have := hX'nil
    infer_instance
  have hX'odd : Odd (Nat.card X') := hXodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hAX' : A ≤ Subgroup.normalizer (X' : Set G) := by
    have key : ∀ g ∈ A, ∀ x ∈ X', g * x * g⁻¹ ∈ X' := by
      intro g hg x hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAX hg) x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer Y (hYA hg)) x).mp
          hx.2⟩
    intro g hg
    exact G8.mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
      simpa using key g⁻¹ (A.inv_mem hg) x hx)
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  obtain ⟨D, hD, hDfaith, -⟩ :=
    G8.g8_2_aux hX's hX'odd n A B hA hAX' hBA hn hB'
  refine ⟨D, hD, ?_⟩
  have : X' ⊓ Subgroup.centralizer (D : Set G) =
      X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) := by
    rw [G8.centralizer_sup, hX', inf_assoc, inf_comm (Subgroup.centralizer (Y : Set G))]
  rw [← this]
  exact hDfaith

end Finite

end G8

section Finite

variable [Finite G]

theorem g8_2 {X P A : Subgroup G} (h : G81 X P A) {B : Subgroup G} (hBA : B ≤ A)
    (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
      B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) =
        ⊥ ∧
      D = A ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :
        Set G) := by
  have : Group.IsNilpotent X := h.nilpotent
  have hXs : Group.IsSolvable X := inferInstance
  have hAn : A ≤ Subgroup.normalizer (X : Set G) := h.le_pGroup.trans h.le_normalizer
  obtain ⟨n, hn⟩ := ((isPGroup_of_isElemAbelian h.elemAbelian).to_le hBA).exists_card_eq
  exact G8.g8_2_aux hXs h.odd n A B h.elemAbelian hAn hBA hn hfaith

theorem g8_5 {X P A : Subgroup G} (h : G81 X P A) {B Y : Subgroup G} (hBA : B ≤ A)
    (hYX : Y ≤ X) (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hBY : B ≤ Subgroup.centralizer (Y : Set G))
    (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
      B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) :
        Subgroup G) : Set G) = ⊥ :=
  G8.g8_5_aux h.nilpotent h.odd h.elemAbelian (h.le_pGroup.trans h.le_normalizer) hBA hYX hYA
    hBY hfaith

end Finite

end CFSG.Quasithin
