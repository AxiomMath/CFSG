module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310P
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139A5

public section

namespace CFSG.Quasithin.H13.Ch8310Q

open CFSG.Quasithin.H13.Ch8310 CFSG.Quasithin.H13.Ch8310P

variable {Q : Type} [Group Q]

theorem conj_mem_of_map_eq {A B : Subgroup Q} {s : Q}
    (h : A.map (MulAut.conj s).toMonoidHom = B) {a : Q} (ha : a ∈ A) : s * a * s⁻¹ ∈ B := by
  rw [← h]
  exact ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem conj_inv_mem_of_map_eq {A B : Subgroup Q} {s : Q}
    (h : A.map (MulAut.conj s).toMonoidHom = B) {b : Q} (hb : b ∈ B) : s⁻¹ * b * s ∈ A := by
  rw [← h] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  simpa [MulAut.conj_apply, mul_assoc] using ha

@[expose] noncomputable def tr {N₁ : Subgroup Q} {Y : Type*} [Group Y] (ι : ↥N₁ ≃* Y)
    (Z : Subgroup Q) : Subgroup Y :=
  (Z.subgroupOf N₁).map ι.toMonoidHom

theorem card_tr {N₁ : Subgroup Q} {Y : Type*} [Group Y] (ι : ↥N₁ ≃* Y) {Z : Subgroup Q}
    (hZ : Z ≤ N₁) : Nat.card (tr ι Z) = Nat.card Z := by
  rw [tr, Subgroup.card_map_of_injective ι.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv]

@[expose] noncomputable def trEquiv {N₁ : Subgroup Q} {Y : Type*} [Group Y] (ι : ↥N₁ ≃* Y)
    {Z : Subgroup Q} (hZ : Z ≤ N₁) : ↥Z ≃* ↥(tr ι Z) :=
  (Subgroup.subgroupOfEquivOfLe hZ).symm.trans ((Z.subgroupOf N₁).equivMapOfInjective _
    ι.injective)

theorem tr_le_iff {N₁ : Subgroup Q} {Y : Type*} [Group Y] (ι : ↥N₁ ≃* Y) {Z Z' : Subgroup Q}
    (hZ : Z ≤ N₁) : tr ι Z ≤ tr ι Z' ↔ Z ≤ Z' := by
  constructor
  · intro h x hx
    have h1 : ι.toMonoidHom ⟨x, hZ hx⟩ ∈ tr ι Z' :=
      h ⟨⟨x, hZ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hZ hx⟩ := ι.injective hyx
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · rintro h _ ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hy)), rfl⟩

theorem tr_eq_top_iff {N₁ : Subgroup Q} {Y : Type*} [Group Y] (ι : ↥N₁ ≃* Y)
    {Z : Subgroup Q} : tr ι Z = ⊤ ↔ N₁ ≤ Z := by
  constructor
  · intro h x hx
    have h1 : ι ⟨x, hx⟩ ∈ tr ι Z := by rw [h]; trivial
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hx⟩ := ι.injective hyx
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := ι.surjective y
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (h x.2), rfl⟩

section A5Data

variable [Finite Q] {p : ℕ} [hp : Fact p.Prime]

theorem a5_data (hp7 : 7 ≤ p) {N₁ N₂ : Subgroup Q}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥)
    (ι : ↥N₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    {E W Hh : Subgroup Q} (hEN : E ≤ N₁) (hE1 : E ≠ ⊥) (hEH : E ≤ Hh)
    (hWp : ⁅W, W⁆ = W) (hWJ : W ≤ N₁ ⊔ N₂) (hB1 : proj1 N₁ N₂ W hc ≠ ⊥) (hWH : W ≤ Hh)
    (hN1H : ¬ N₁ ≤ Hh) :
    Nonempty (↥(proj1 N₁ N₂ W hc) ≃* alternatingGroup (Fin 5)) ∧ E ≤ proj1 N₁ N₂ W hc ∧
      proj1 N₁ N₂ W hc ≤ Hh := by
  have hp2 : p ≠ 2 := by omega
  set B := proj1 N₁ N₂ W hc with hBdef
  set Pr₁ := proj1 N₁ N₂ (Hh ⊓ (N₁ ⊔ N₂)) hc with hPrdef
  set F := Hh ⊓ N₁ with hFdef
  have hBN : B ≤ N₁ := proj1_le hc
  have hPrN : Pr₁ ≤ N₁ := proj1_le hc
  have hBPr : B ≤ Pr₁ := proj1_mono hc (le_inf hWH hWJ)
  have hFPr : F ≤ Pr₁ := fun x hx =>
    inf_le_proj1 hc ⟨⟨hx.1, Subgroup.mem_sup_left hx.2⟩, hx.2⟩
  have hEF : E ≤ F := le_inf hEH hEN
  have hPrF : ∀ a ∈ Pr₁, ∀ f ∈ F, a * f * a⁻¹ ∈ F := fun a ha f hf => by
    have h := proj1_conj_mem hc ha (Y := Hh ⊓ (N₁ ⊔ N₂))
      ⟨⟨hf.1, Subgroup.mem_sup_left hf.2⟩, hf.2⟩
    exact ⟨h.1.1, h.2⟩
  have := CFSG.Quasithin.Vol2.Ch11.SecB.isSimpleGroup_psl2 (p := p) (by omega)
  have hN₁s : IsSimpleGroup ↥N₁ := ι.isSimpleGroup
  have hfill : ∀ X : Subgroup Q, IsSimpleGroup ↥X → E ≤ X → F ≤ X →
      (∀ a ∈ X, ∀ f ∈ F, a * f * a⁻¹ ∈ F) → X ≤ F := by
    intro X hXs hEX hFX hXF
    have hn : (F.subgroupOf X).Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      (hXF g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      apply hE1
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hEX hx⟩ : ↥X) ∈ F.subgroupOf X := Subgroup.mem_subgroupOf.mpr (hEF hx)
      rw [h, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
    · intro x hx
      have h1 : (⟨x, hx⟩ : ↥X) ∈ F.subgroupOf X := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp h1
  have hPrtop : ¬ N₁ ≤ Pr₁ := by
    intro h
    have hPreq : Pr₁ = N₁ := le_antisymm hPrN h
    have := hfill N₁ hN₁s hEN inf_le_right (fun a ha f hf => hPrF a (h ha) f hf)
    exact hN1H (this.trans inf_le_left)
  have hBp : ⁅B, B⁆ = B := commutator_proj1 hc hd hWp hWJ
  have hB'p : ⁅tr ι B, tr ι B⁆ = tr ι B := by
    have h1 : ⁅B.subgroupOf N₁, B.subgroupOf N₁⁆ = B.subgroupOf N₁ := by
      apply Subgroup.map_injective N₁.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBN, hBp]
    rw [tr, ← Subgroup.map_commutator, h1]
  have hB'1 : tr ι B ≠ ⊥ := by
    intro h
    apply hB1
    have h1 := card_tr ι hBN
    rw [h, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq B h1.symm
  rcases CFSG.Quasithin.Dickson.perfect_subgroup_psl2_prime hp2 (tr ι B) hB'p hB'1 with
    htop | ⟨⟨e5⟩, -⟩
  · exact absurd (((tr_eq_top_iff ι).mp htop).trans hBPr) hPrtop
  have eB : ↥B ≃* alternatingGroup (Fin 5) := (trEquiv ι hBN).trans e5
  have hPr60 := CFSG.Quasithin.Dickson.overgroup_alternating_five_psl2_prime hp2
    ((tr_le_iff ι hBN).mpr hBPr) ⟨e5⟩
  have hPrB : Pr₁ = B := by
    rcases hPr60 with h | h
    · exact absurd ((tr_eq_top_iff ι).mp h) hPrtop
    · refine (Subgroup.eq_of_le_of_card_ge hBPr ?_).symm
      rw [← card_tr ι hPrN, h, Nat.card_congr eB.toEquiv]
      exact (CFSG.Quasithin.Dickson.card_alt_five).ge
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hBF := hfill B eB.isSimpleGroup (hEF.trans (hPrB ▸ hFPr)) (hPrB ▸ hFPr)
    (fun a ha f hf => hPrF a (hPrB ▸ ha) f hf)
  exact ⟨⟨eB⟩, hEF.trans (hPrB ▸ hFPr), hBF.trans inf_le_left⟩

end A5Data

section Borel

variable [Finite Q]

theorem sup_inf_left_eq {N₁ N₂ E₁ E₂ : Subgroup Q} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : N₁ ⊓ N₂ = ⊥) (h₁ : E₁ ≤ N₁) (h₂ : E₂ ≤ N₂) : (E₁ ⊔ E₂) ⊓ N₁ = E₁ := by
  refine le_antisymm ?_ (le_inf le_sup_left h₁)
  rintro x ⟨hx, hxN⟩
  have hnorm : E₁ ≤ Subgroup.normalizer (E₂ : Set Q) := fun a ha =>
    A4.mem_normalizer_of_conj_mem fun b hb => by
      rw [hc a (h₁ ha) b (h₂ hb), mul_inv_cancel_right]
      exact hb
  have hx' : x ∈ ((E₁ ⊔ E₂ : Subgroup Q) : Set Q) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₂ hnorm] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hbN : b ∈ N₁ ⊓ N₂ := by
    refine ⟨?_, h₂ hb⟩
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact N₁.mul_mem (N₁.inv_mem (h₁ ha)) hxN
  rw [hd, Subgroup.mem_bot] at hbN
  subst hbN
  simpa using ha

theorem le_mh {N₁ N₂ S Hh Mh B : Subgroup Q} {σ : Q} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : N₁ ⊓ N₂ = ⊥) (hσS : σ ∈ S)
    (hperm : ∀ s ∈ S, (N₁.map (MulAut.conj s).toMonoidHom = N₁ ∧
        N₂.map (MulAut.conj s).toMonoidHom = N₂) ∨
      (N₁.map (MulAut.conj s).toMonoidHom = N₂ ∧ N₂.map (MulAut.conj s).toMonoidHom = N₁))
    (hBN : B ≤ N₁) (hBH : B ≤ Hh) (hSH : S ≤ Hh)
    (hcard : Nat.card ↥(B ⊓ Subgroup.normalizer ((S ⊓ N₁ : Subgroup Q) : Set Q)) < Nat.card B)
    (humax : ∀ Y : Subgroup Q, S ≤ Y → Y ≤ Hh → Y ≠ Hh → Y ⊓ (N₁ ⊔ N₂) ≤ Mh) :
    B ⊓ Subgroup.normalizer ((S ⊓ N₁ : Subgroup Q) : Set Q) ≤ Mh := by
  set E₁ := S ⊓ N₁ with hE₁
  set E₂ := S ⊓ N₂ with hE₂
  set A := B ⊓ Subgroup.normalizer (E₁ : Set Q) with hA
  set NE := Subgroup.normalizer ((E₁ ⊔ E₂ : Subgroup Q) : Set Q) with hNE
  have hconjS : ∀ s ∈ S, ∀ (N : Subgroup Q) (N' : Subgroup Q),
      N.map (MulAut.conj s).toMonoidHom = N' →
        (S ⊓ N).map (MulAut.conj s).toMonoidHom ≤ S ⊓ N' := by
    rintro s hs N N' hN _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using S.mul_mem (S.mul_mem hs hx.1) (S.inv_mem hs)
    · rw [← hN]
      exact ⟨x, hx.2, rfl⟩
  have hSNE : S ≤ NE := by
    intro s hs
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hmap : (E₁ ⊔ E₂).map (MulAut.conj s).toMonoidHom ≤ E₁ ⊔ E₂ := by
      rw [Subgroup.map_sup]
      rcases hperm s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact sup_le_sup (hconjS s hs N₁ N₁ h1) (hconjS s hs N₂ N₂ h2)
      · exact sup_le ((hconjS s hs N₁ N₂ h1).trans le_sup_right)
          ((hconjS s hs N₂ N₁ h2).trans le_sup_left)
    have := hmap ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hANE : A ≤ NE := by
    intro a ha
    refine E1.mem_normalizer_sup ha.2 (A4.mem_normalizer_of_conj_mem fun b hb => ?_)
    rw [hc a (hBN ha.1) b hb.2, mul_inv_cancel_right]
    exact hb
  set Y := (A ⊔ A.map (MulAut.conj σ).toMonoidHom) ⊔ S with hY
  have hYNE : Y ≤ NE := by
    refine sup_le (sup_le hANE ?_) hSNE
    rintro _ ⟨a, ha, rfl⟩
    have h1 := NE.mul_mem (NE.mul_mem (hSNE hσS) (hANE ha)) (NE.inv_mem (hSNE hσS))
    simpa [MulAut.conj_apply] using h1
  have hYH : Y ≤ Hh := by
    refine sup_le (sup_le (inf_le_left.trans hBH) ?_) hSH
    rintro _ ⟨a, ha, rfl⟩
    have h1 := Hh.mul_mem (Hh.mul_mem (hSH hσS) (hBH ha.1)) (Hh.inv_mem (hSH hσS))
    simpa [MulAut.conj_apply] using h1
  have hYne : Y ≠ Hh := by
    intro hYeq
    apply (lt_irrefl (Nat.card B))
    refine lt_of_le_of_lt (Nat.card_mono (Set.toFinite _) ?_) hcard
    intro b hb
    refine ⟨hb, ?_⟩
    have hbNE : b ∈ NE := hYNE (hYeq ▸ hBH hb)
    have h1 := E1.mem_normalizer_inf hbNE (Subgroup.le_normalizer (hBN hb))
    rwa [sup_inf_left_eq hc hd inf_le_right inf_le_right] at h1
  have hAY : A ≤ Y ⊓ (N₁ ⊔ N₂) :=
    le_inf (le_sup_left.trans le_sup_left) ((inf_le_left.trans hBN).trans le_sup_left)
  exact hAY.trans (humax Y le_sup_right hYH hYne)

end Borel

section E9

variable [Finite Q] {p : ℕ} [hp : Fact p.Prime]

omit [Finite Q] in
theorem card_dvd_three_of_le (hp5 : 5 ≤ p) {N Z : Subgroup Q}
    (ι : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) (hZN : Z ≤ N)
    (hZ : ∀ x ∈ Z, x ^ 3 = 1) : Nat.card Z ∣ 3 := by
  rw [← card_tr ι hZN]
  refine card_dvd_three_of_pow_three hp5 ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : x ^ 3 = 1 := Subtype.ext (by simpa using hZ x (Subgroup.mem_subgroupOf.mp hx))
  rw [← map_pow, h1, map_one]

theorem card_inf_eq_three (hp5 : 5 ≤ p) {N₁ N₂ P : Subgroup Q}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥)
    (ι₁ : ↥N₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (ι₂ : ↥N₂ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (hPJ : P ≤ N₁ ⊔ N₂) (hP9 : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1) :
    Nat.card ↥(P ⊓ N₁) = 3 ∧ Nat.card ↥(P ⊓ N₂) = 3 := by
  have hc' : ∀ a ∈ N₂, ∀ b ∈ N₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hd' : N₂ ⊓ N₁ = ⊥ := by rw [inf_comm]; exact hd
  have hPJ' : P ≤ N₂ ⊔ N₁ := by rw [sup_comm]; exact hPJ
  have hproj : ∀ {A B : Subgroup Q} (hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a), A ⊓ B = ⊥ →
      ∀ x ∈ proj1 A B P hcAB, x ^ 3 = 1 := by
    intro A B hcAB hdAB x ⟨hxA, b, hb, hxb⟩
    have h1 := hP3 _ hxb
    have hcomm : Commute x b := hcAB x hxA b hb
    rw [hcomm.mul_pow] at h1
    have h2 : x ^ 3 ∈ A ⊓ B := by
      refine ⟨A.pow_mem hxA 3, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact B.inv_mem (B.pow_mem hb 3)
    rw [hdAB, Subgroup.mem_bot] at h2
    exact h2
  have hd1 := card_dvd_three_of_le hp5 ι₁ (proj1_le hc) (hproj hc hd)
  have hd2 := card_dvd_three_of_le hp5 ι₂ (proj1_le hc') (hproj hc' hd')
  have hi1 := card_dvd_three_of_le hp5 ι₁ inf_le_right (fun x hx => hP3 x hx.1)
  have hi2 := card_dvd_three_of_le hp5 ι₂ inf_le_right (fun x hx => hP3 x hx.1)
  have h1 := card_eq_card_proj1_mul hc hd hPJ
  have h2 := card_eq_card_proj1_mul hc' hd' hPJ'
  rw [hP9] at h1 h2
  have key : ∀ a b : ℕ, a ∣ 3 → b ∣ 3 → 9 = a * b → b = 3 := by
    intro a b ha hb hab
    have ha' := Nat.le_of_dvd (by norm_num) ha
    have hb' := Nat.le_of_dvd (by norm_num) hb
    interval_cases a <;> interval_cases b <;> omega
  exact ⟨key _ _ hd2 hi1 h2, key _ _ hd1 hi2 h1⟩

end E9

section AutCyclic

theorem conj_eq_or_inv_of_card_three [Finite Q] {C : Subgroup Q} (hC : Nat.card C = 3) {t : Q}
    (ht : ∀ x ∈ C, t * x * t⁻¹ ∈ C) :
    (∀ x ∈ C, t * x * t⁻¹ = x) ∨ (∀ x ∈ C, t * x * t⁻¹ = x⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥C := isCyclic_of_prime_card hC
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hgo : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hC]
  have hgo' : orderOf (g : Q) = 3 := by rw [Subgroup.orderOf_coe]; exact hgo
  have hpow : ∀ x ∈ C, ∃ m : ℤ, x = (g : Q) ^ m := fun x hx => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have h1 := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_zpow] at h1
    exact ⟨m, h1.symm⟩
  have hconj : ∀ m : ℤ, t * (g : Q) ^ m * t⁻¹ = (t * (g : Q) * t⁻¹) ^ m := fun m => by
    have := map_zpow (MulAut.conj t) (g : Q) m
    simp only [MulAut.conj_apply] at this
    exact this
  obtain ⟨k, hk⟩ := hpow _ (ht _ g.2)
  have hkmod : (g : Q) ^ k = (g : Q) ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hgo']
    norm_cast
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hg3 : (g : Q) ^ 3 = 1 := by rw [← hgo']; exact pow_orderOf_eq_one _
  rw [hkmod] at hk
  interval_cases hkk : k % 3
  · exfalso
    have h1 : t * (g : Q) * t⁻¹ = 1 := by rw [hk]; simp
    have h2 : (g : Q) = 1 := by
      have := congrArg (fun y => t⁻¹ * y * t) h1
      simpa [mul_assoc] using this
    rw [h2, orderOf_one] at hgo'
    exact absurd hgo' (by norm_num)
  · left
    intro x hx
    obtain ⟨m, rfl⟩ := hpow x hx
    rw [hconj, hk, zpow_one]
  · right
    intro x hx
    obtain ⟨m, rfl⟩ := hpow x hx
    have hg2 : (g : Q) ^ (2 : ℤ) = (g : Q)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
      exact_mod_cast hg3
    rw [hconj, hk, hg2, inv_zpow]

theorem exists_inv_of_not_autCyclic [Finite Q] {N₁ N₂ P S' : Subgroup Q}
    (hperm : ∀ s ∈ S', (N₁.map (MulAut.conj s).toMonoidHom = N₁ ∧
        N₂.map (MulAut.conj s).toMonoidHom = N₂) ∨
      (N₁.map (MulAut.conj s).toMonoidHom = N₂ ∧ N₂.map (MulAut.conj s).toMonoidHom = N₁))
    (hS'P : ∀ t ∈ S', ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hP1 : Nat.card ↥(P ⊓ N₁) = 3) (hP2 : Nat.card ↥(P ⊓ N₂) = 3)
    (hPsup : P = (P ⊓ N₁) ⊔ (P ⊓ N₂))
    (hnc : ¬ ∃ c ∈ S', ∀ s ∈ S', ∃ k : ℕ, ∀ x ∈ P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹) :
    ∃ t ∈ S', N₁.map (MulAut.conj t).toMonoidHom = N₁ ∧
      N₂.map (MulAut.conj t).toMonoidHom = N₂ ∧ ∀ x ∈ P ⊓ N₁, t * x * t⁻¹ = x⁻¹ := by
  by_contra hno
  push Not at hno
  apply hnc
  set P₁ := P ⊓ N₁ with hP₁
  set P₂ := P ⊓ N₂ with hP₂
  have hmapP : ∀ s ∈ S', ∀ {N N' : Subgroup Q}, N.map (MulAut.conj s).toMonoidHom = N' →
      ∀ x ∈ P ⊓ N, s * x * s⁻¹ ∈ P ⊓ N' := fun s hs N N' h x hx =>
    ⟨hS'P s hs x hx.1, conj_mem_of_map_eq h hx.2⟩
  have hfix1 : ∀ t ∈ S', N₁.map (MulAut.conj t).toMonoidHom = N₁ →
      N₂.map (MulAut.conj t).toMonoidHom = N₂ → ∀ x ∈ P₁, t * x * t⁻¹ = x := by
    intro t ht h1 h2
    rcases conj_eq_or_inv_of_card_three hP1 (hmapP t ht h1) with h | h
    · exact h
    · obtain ⟨x, hx, hne⟩ := hno t ht h1 h2
      exact absurd (h x hx) hne
  have hcentP : ∀ g : Q, (∀ x ∈ P₁, g * x * g⁻¹ = x) → (∀ x ∈ P₂, g * x * g⁻¹ = x) →
      ∀ x ∈ P, g * x * g⁻¹ = x := by
    intro g h1 h2 x hx
    have hle : P₁ ⊔ P₂ ≤ Subgroup.centralizer ({g} : Set Q) := sup_le
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := h1 y hy
        calc y * g = g * y * g⁻¹ * g := by rw [this]
          _ = g * y := by group))
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := h2 y hy
        calc y * g = g * y * g⁻¹ * g := by rw [this]
          _ = g * y := by group))
    rw [hPsup] at hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    rw [← this]
    group
  have hcomp : ∀ {a b : Q} {X Y Z : Subgroup Q}, X.map (MulAut.conj a).toMonoidHom = Y →
      Y.map (MulAut.conj b).toMonoidHom = Z → X.map (MulAut.conj (b * a)).toMonoidHom = Z := by
    intro a b X Y Z h1 h2
    rw [← h2, ← h1, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hinvmap : ∀ {a : Q} {X Y : Subgroup Q}, X.map (MulAut.conj a).toMonoidHom = Y →
      Y.map (MulAut.conj a⁻¹).toMonoidHom = X := by
    intro a X Y h
    rw [← h]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa [mul_assoc] using hz
    · intro hx
      exact ⟨a * x * a⁻¹, ⟨x, hx, rfl⟩, by group⟩
  by_cases hswap : ∃ u ∈ S', N₁.map (MulAut.conj u).toMonoidHom = N₂ ∧
      N₂.map (MulAut.conj u).toMonoidHom = N₁
  ·
    obtain ⟨u, hu, hu1, hu2⟩ := hswap
    have hfixP : ∀ t ∈ S', N₁.map (MulAut.conj t).toMonoidHom = N₁ →
        N₂.map (MulAut.conj t).toMonoidHom = N₂ → ∀ x ∈ P, t * x * t⁻¹ = x := by
      intro t ht h1 h2
      refine hcentP t (hfix1 t ht h1 h2) ?_
      intro y hy
      have hx : u⁻¹ * y * u ∈ P₁ := ⟨by
          have := hS'P u⁻¹ (S'.inv_mem hu) y hy.1
          simpa using this, conj_inv_mem_of_map_eq hu1 hy.2⟩
      have hv : u⁻¹ * t * u ∈ S' := S'.mul_mem (S'.mul_mem (S'.inv_mem hu) ht) hu
      have hv1 : N₁.map (MulAut.conj (u⁻¹ * t * u)).toMonoidHom = N₁ := by
        have e : u⁻¹ * t * u = u⁻¹ * (t * u) := by group
        rw [e]
        exact hcomp (hcomp hu1 h2) (hinvmap hu1)
      have hv2 : N₂.map (MulAut.conj (u⁻¹ * t * u)).toMonoidHom = N₂ := by
        have e : u⁻¹ * t * u = u⁻¹ * (t * u) := by group
        rw [e]
        exact hcomp (hcomp hu2 h1) (hinvmap hu2)
      have h3 := hfix1 _ hv hv1 hv2 _ hx
      calc t * y * t⁻¹ = u * ((u⁻¹ * t * u) * (u⁻¹ * y * u) * (u⁻¹ * t * u)⁻¹) * u⁻¹ := by
            group
        _ = y := by rw [h3]; group
    refine ⟨u, hu, fun s hs => ?_⟩
    rcases hperm s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, fun x hx => by rw [hfixP s hs h1 h2 x hx]; simp⟩
    · refine ⟨1, fun x hx => ?_⟩
      have hv : u⁻¹ * s ∈ S' := S'.mul_mem (S'.inv_mem hu) hs
      have hv1 : N₁.map (MulAut.conj (u⁻¹ * s)).toMonoidHom = N₁ := hcomp h1 (hinvmap hu1)
      have hv2 : N₂.map (MulAut.conj (u⁻¹ * s)).toMonoidHom = N₂ := hcomp h2 (hinvmap hu2)
      have h3 := hfixP _ hv hv1 hv2 x hx
      calc s * x * s⁻¹ = u * ((u⁻¹ * s) * x * (u⁻¹ * s)⁻¹) * u⁻¹ := by group
        _ = u ^ 1 * x * (u ^ 1)⁻¹ := by rw [h3, pow_one]
  ·
    push Not at hswap
    have hfixall : ∀ s ∈ S', N₁.map (MulAut.conj s).toMonoidHom = N₁ ∧
        N₂.map (MulAut.conj s).toMonoidHom = N₂ := fun s hs => by
      rcases hperm s hs with h | ⟨h1, h2⟩
      · exact h
      · exact absurd h2 (hswap s hs h1)
    by_cases hinv : ∃ c ∈ S', ∀ y ∈ P₂, c * y * c⁻¹ = y⁻¹
    · obtain ⟨c, hc, hcinv⟩ := hinv
      refine ⟨c, hc, fun s hs => ?_⟩
      obtain ⟨h1, h2⟩ := hfixall s hs
      rcases conj_eq_or_inv_of_card_three hP2 (hmapP s hs h2) with h | h
      · exact ⟨0, fun x hx => by
          rw [hcentP s (hfix1 s hs h1 h2) h x hx]
          simp⟩
      · refine ⟨1, fun x hx => ?_⟩
        obtain ⟨c1, c2⟩ := hfixall c hc
        have hv : c⁻¹ * s ∈ S' := S'.mul_mem (S'.inv_mem hc) hs
        have hv1 := hcomp h1 (hinvmap c1)
        have hv2 := hcomp h2 (hinvmap c2)
        have hP2c : ∀ y ∈ P₂, (c⁻¹ * s) * y * (c⁻¹ * s)⁻¹ = y := by
          intro y hy
          have hsy := h y hy
          calc (c⁻¹ * s) * y * (c⁻¹ * s)⁻¹ = c⁻¹ * (s * y * s⁻¹) * c := by group
            _ = c⁻¹ * y⁻¹ * c := by rw [hsy]
            _ = y := by
              rw [← hcinv y hy]
              group
        have h3 := hcentP _ (hfix1 _ hv hv1 hv2) hP2c x hx
        calc s * x * s⁻¹ = c * ((c⁻¹ * s) * x * (c⁻¹ * s)⁻¹) * c⁻¹ := by group
          _ = c ^ 1 * x * (c ^ 1)⁻¹ := by rw [h3, pow_one]
    · push Not at hinv
      refine ⟨1, S'.one_mem, fun s hs => ⟨0, fun x hx => ?_⟩⟩
      obtain ⟨h1, h2⟩ := hfixall s hs
      rcases conj_eq_or_inv_of_card_three hP2 (hmapP s hs h2) with h | h
      · rw [hcentP s (hfix1 s hs h1 h2) h x hx]
        simp
      · exfalso
        obtain ⟨y, hy, hne⟩ := hinv s hs
        exact hne (h y hy)

end AutCyclic

section Config

theorem a5_sq_of_pow_four : ∀ x : alternatingGroup (Fin 5), x ^ 4 = 1 → x ^ 2 = 1 := by
  decide +kernel

theorem exists_mul_of_mem_sup {N₁ N₂ : Subgroup Q} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    {w : Q} (hw : w ∈ N₁ ⊔ N₂) : ∃ a ∈ N₁, ∃ b ∈ N₂, w = a * b := by
  have hnorm : N₁ ≤ Subgroup.normalizer (N₂ : Set Q) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hc a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have e : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [e, hc a⁻¹ (N₁.inv_mem ha) _ hb]
      simpa [mul_assoc] using hb
  have hw' : w ∈ ((N₁ ⊔ N₂ : Subgroup Q) : Set Q) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ hnorm] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  exact ⟨a, ha, b, hb, rfl⟩

theorem two_dvd_card_psl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have h := CFSG.Quasithin.Vol2.Ch11.SecB.two_mul_card_psl2 (p := p) hp2
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h8 : 8 ∣ p ^ 2 - 1 := by
    have e : p ^ 2 - 1 = 4 * (k * (k + 1)) := by
      rw [hk]
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [e]
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    rw [hm]
    exact ⟨m, by ring⟩
  have h8' : 8 ∣ 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    h ▸ dvd_mul_of_dvd_right h8 p
  have h4 : 4 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa [mul_comm] using h8')
  exact (by norm_num : 2 ∣ 4).trans h4

variable [Finite Q] {p : ℕ} [hp : Fact p.Prime]

theorem false_of_a5_config
    (hp7 : 7 ≤ p) {N₁ N₂ : Subgroup Q} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : N₁ ⊓ N₂ = ⊥) (ι : ↥N₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    {S : Subgroup Q} {σ : Q} (hσS : σ ∈ S) (hσ1 : N₁.map (MulAut.conj σ).toMonoidHom = N₂)
    (hperm : ∀ s ∈ S, (N₁.map (MulAut.conj s).toMonoidHom = N₁ ∧
        N₂.map (MulAut.conj s).toMonoidHom = N₂) ∨
      (N₁.map (MulAut.conj s).toMonoidHom = N₂ ∧ N₂.map (MulAut.conj s).toMonoidHom = N₁))
    (hSyl : IsSylowIn 2 (S ⊓ N₁) N₁)
    {W : Subgroup Q} (hWp : ⁅W, W⁆ = W) (hWJ : W ≤ N₁ ⊔ N₂) (hW1 : W ≠ ⊥)
    (hWS : ∀ s ∈ S, ∀ w ∈ W, s * w * s⁻¹ ∈ W)
    {Hh : Subgroup Q} (hSH : S ≤ Hh) (hWH : W ≤ Hh) (hN1H : ¬ N₁ ≤ Hh)
    {Mh Ch : Subgroup Q}
    (humax : ∀ Y : Subgroup Q, S ≤ Y → Y ≤ Hh → Y ≠ Hh → Y ⊓ (N₁ ⊔ N₂) ≤ Mh)
    (hCn : ∀ m ∈ Mh, ∀ c ∈ Ch, m * c * m⁻¹ ∈ Ch)
    (hCH : ∀ x ∈ Ch ⊓ Hh, ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hlift : ∀ d ∈ Mh ⊓ N₁, ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf d = r → d ∈ Ch)
    {P S' : Subgroup Q} (hPJ : P ≤ N₁ ⊔ N₂) (hP9 : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPM : P ≤ Mh) (hS'S : S' ≤ S)
    (hS'P : ∀ t ∈ S', ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hnc : ¬ ∃ c ∈ S', ∀ s ∈ S', ∃ k : ℕ, ∀ x ∈ P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  set E := S ⊓ N₁ with hEdef
  have hEN : E ≤ N₁ := inf_le_right
  have hES : E ≤ S := inf_le_left
  have hN₁card : Nat.card N₁ = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Nat.card_congr ι.toEquiv
  have hE1 : E ≠ ⊥ := by
    intro h
    apply hSyl.not_dvd_relIndex
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := N₁)
    rw [h, bot_inf_eq, Subgroup.card_bot, mul_one] at h1
    rw [h, h1, hN₁card]
    exact two_dvd_card_psl2 hp2
  have hN₁1 : N₁ ≠ ⊥ := fun h => hE1 (eq_bot_iff.mpr (h ▸ hEN))
  have hσ2 : N₂.map (MulAut.conj σ).toMonoidHom = N₁ := by
    rcases hperm σ hσS with ⟨h1, -⟩ | ⟨-, h2⟩
    · exfalso
      apply hN₁1
      rw [← hd, ← hσ1.symm.trans h1, inf_idem]
    · exact h2
  set B := proj1 N₁ N₂ W hc with hBdef
  have hBN : B ≤ N₁ := proj1_le hc
  have hB1 : B ≠ ⊥ := by
    intro hB
    apply hW1
    have hWN₂ : W ≤ N₂ := by
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc (hWJ hw)
      have haB : a ∈ B := ⟨ha, b, hb, hw⟩
      rw [hB, Subgroup.mem_bot] at haB
      rw [haB, one_mul]
      exact hb
    rw [eq_bot_iff]
    intro w hw
    have h1 : σ⁻¹ * w * σ ∈ N₁ ⊓ N₂ := by
      refine ⟨conj_inv_mem_of_map_eq hσ1 (hWN₂ hw), hWN₂ ?_⟩
      have := hWS σ⁻¹ (S.inv_mem hσS) w hw
      simpa using this
    rw [hd, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have e : w = σ * (σ⁻¹ * w * σ) * σ⁻¹ := by group
    rw [e, h1]
    group
  obtain ⟨⟨eB⟩, hEB, hBH⟩ := a5_data hp7 hc hd ι hEN hE1 ((inf_le_left.trans hSH))
    hWp hWJ hB1 hWH hN1H
  have hESyl : IsSylowIn 2 E B := by
    refine ⟨hEB, hSyl.isPGroup, fun h2 => hSyl.not_dvd_relIndex ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex E B N₁ hEB hBN]
    exact dvd_mul_of_dvd_left h2 _
  obtain ⟨-, hEf⟩ := a5_facts eB
  have hE'2 : IsPGroup 2 ↥(E.subgroupOf B) :=
    hESyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hEB).symm
  obtain ⟨hE4', hNEidx⟩ := hEf (E.subgroupOf B) hE'2 hESyl.not_dvd_relIndex
  have hE4 : Nat.card E = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv).symm.trans hE4'
  have hB60 : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv]
    exact CFSG.Quasithin.Dickson.card_alt_five
  set A := B ⊓ Subgroup.normalizer (E : Set Q) with hAdef
  have hAB : A ≤ B := inf_le_left
  have hAsub : A.subgroupOf B = Subgroup.normalizer ((E.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_normalizer_subgroupOf_iff hEB]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hA12 : Nat.card A = 12 := by
    have h1 := (Subgroup.normalizer ((E.subgroupOf B : Subgroup ↥B) : Set ↥B)).card_mul_index
    rw [hNEidx, Nat.card_congr eB.toEquiv, CFSG.Quasithin.Dickson.card_alt_five] at h1
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAsub]
    omega
  have hEsq : ∀ e ∈ E, e ^ 2 = 1 := by
    intro e he
    have h4 : (⟨e, he⟩ : ↥E) ^ 4 = 1 := by
      rw [← hE4]
      exact pow_card_eq_one'
    have h4' : (eB ⟨e, hEB he⟩) ^ 4 = 1 := by
      rw [← map_pow]
      have : (⟨e, hEB he⟩ : ↥B) ^ 4 = 1 := Subtype.ext (by simpa using congrArg Subtype.val h4)
      rw [this, map_one]
    have h2 := a5_sq_of_pow_four _ h4'
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
    simpa using congrArg Subtype.val h2
  have h8 : ¬ 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [← hN₁card]
    intro h
    have h1 := Subgroup.relIndex_mul_card (H := E) (K := N₁)
    rw [inf_eq_left.mpr hEN, hE4] at h1
    rw [← h1] at h
    have h2 : 2 ∣ E.relIndex N₁ := by
      obtain ⟨m, hm⟩ := h
      exact ⟨m, by omega⟩
    exact hSyl.not_dvd_relIndex h2
  obtain ⟨c₀', hc₀o⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 3 (by rw [hA12]; norm_num)
  set c₀ : Q := (c₀' : Q) with hc₀def
  have hc₀A : c₀ ∈ A := c₀'.2
  have hc₀o' : orderOf c₀ = 3 := by rw [hc₀def, Subgroup.orderOf_coe]; exact hc₀o
  have hc₀3 : c₀ ^ 3 = 1 := by rw [← hc₀o']; exact pow_orderOf_eq_one c₀
  have hc₀1 : c₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hc₀o'; omega
  have hAM : A ≤ Mh := le_mh hc hd hσS hperm hBN hBH hSH (by rw [hA12, hB60]; norm_num) humax
  have ι₂ : ↥N₂ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (MulEquiv.subgroupCongr hσ1).symm.trans
      ((MulEquiv.subgroupMap (MulAut.conj σ) N₁).symm.trans ι)
  obtain ⟨hP1, hP2⟩ := card_inf_eq_three hp5 hc hd ι ι₂ hPJ hP9 hP3
  set P₁ := P ⊓ N₁ with hP₁def
  set P₂ := P ⊓ N₂ with hP₂def
  have hPsup : P = P₁ ⊔ P₂ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
    rw [CFSG.Quasithin.SBc15.card_sup_eq_mul_of_commute (A := P₁) (B := P₂)
      (fun a ha b hb => hc a ha.2 b hb.2) ?_, hP1, hP2, hP9]
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [← hd]
    exact ⟨hx.1.2, hx.2.2⟩
  set D := A ⊔ P₁ with hDdef
  have hDN : D ≤ N₁ := sup_le (hAB.trans hBN) inf_le_right
  have hDM : D ≤ Mh := sup_le hAM (inf_le_left.trans hPM)
  have hP₁A : P₁ ≤ A := by
    have hED : E ≤ D := by
      intro e he
      exact Subgroup.mem_sup_left ⟨hEB he, Subgroup.le_normalizer he⟩
    have hc₀D : c₀ ∈ D := Subgroup.mem_sup_left hc₀A
    rcases card_eq_twelve_or_simple hp7 h8 ((tr_le_iff ι hEN).mpr hED)
        ((card_tr ι hEN).trans hE4)
        (by
          rintro _ ⟨x, hx, rfl⟩
          have h1 : x ^ 2 = 1 := Subtype.ext (by
            simpa using hEsq _ (Subgroup.mem_subgroupOf.mp hx))
          rw [← map_pow, h1, map_one])
        (c := ι ⟨c₀, hDN hc₀D⟩) ⟨⟨c₀, hDN hc₀D⟩, Subgroup.mem_subgroupOf.mpr hc₀D, rfl⟩
        (by
          rw [Ne, MulEquiv.map_eq_one_iff]
          intro h
          exact hc₀1 (congrArg Subtype.val h))
        (by
          rw [← map_pow]
          have : (⟨c₀, hDN hc₀D⟩ : ↥N₁) ^ 3 = 1 := Subtype.ext (by simpa using hc₀3)
          rw [this, map_one])
        (by
          refine A4.mem_normalizer_of_conj_mem ?_
          rintro _ ⟨x, hx, rfl⟩
          refine ⟨⟨c₀, hDN hc₀D⟩ * x * ⟨c₀, hDN hc₀D⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
            by simp⟩
          have := (Subgroup.mem_normalizer_iff.mp hc₀A.2 _).mp (Subgroup.mem_subgroupOf.mp hx)
          simpa using this) with h12 | ⟨hDs, d, hd', r, hr, hr5, hdo⟩
    · rw [card_tr ι hDN] at h12
      have hDA : D = A := (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h12, hA12])).symm
      exact hDA ▸ le_sup_right
    · exfalso
      obtain ⟨x, hx, rfl⟩ := hd'
      have hxD : (x : Q) ∈ D := Subgroup.mem_subgroupOf.mp hx
      have hxo : orderOf (x : Q) = r := by
        rw [Subgroup.orderOf_coe, ← hdo]
        exact (MulEquiv.orderOf_eq ι x).symm
      have hxC : (x : Q) ∈ Ch := hlift _ ⟨hDM hxD, x.2⟩ r hr hr5 hxo
      have hDs' : IsSimpleGroup ↥D := (trEquiv ι hDN).isSimpleGroup
      have hn : ((Ch ⊓ D).subgroupOf D).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact ⟨hCn _ (hDM g.2) _ hn.1, D.mul_mem (D.mul_mem g.2 hn.2) (D.inv_mem g.2)⟩⟩
      rcases hn.eq_bot_or_eq_top with h | h
      · have h1 : (⟨x, hxD⟩ : ↥D) ∈ (Ch ⊓ D).subgroupOf D :=
          Subgroup.mem_subgroupOf.mpr ⟨hxC, hxD⟩
        rw [h, Subgroup.mem_bot] at h1
        have h2 : (x : Q) = 1 := congrArg Subtype.val h1
        rw [h2, orderOf_one] at hxo
        omega
      · have h1 : (⟨c₀, hc₀D⟩ : ↥D) ∈ (Ch ⊓ D).subgroupOf D := by rw [h]; trivial
        have hc₀C : c₀ ∈ Ch := (Subgroup.mem_subgroupOf.mp h1).1
        obtain ⟨k, hk⟩ := hCH c₀ ⟨hc₀C, hBH (hAB hc₀A)⟩
        have h3 : orderOf c₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
        rw [hc₀o'] at h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)
        omega
  obtain ⟨t, htS', ht1, ht2, htinv⟩ := exists_inv_of_not_autCyclic
    (fun s hs => hperm s (hS'S hs)) hS'P hP1 hP2 hPsup hnc
  have htS : t ∈ S := hS'S htS'
  obtain ⟨ĉ', hĉo⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₁) 3 (by rw [hP1])
  set ĉ : Q := (ĉ' : Q) with hĉdef
  have hĉP : ĉ ∈ P₁ := ĉ'.2
  have hĉA : ĉ ∈ A := hP₁A hĉP
  have hĉo' : orderOf ĉ = 3 := by rw [hĉdef, Subgroup.orderOf_coe]; exact hĉo
  have hĉ3 : ĉ ^ 3 = 1 := by rw [← hĉo']; exact pow_orderOf_eq_one ĉ
  have hĉ1 : ĉ ≠ 1 := fun h => by rw [h, orderOf_one] at hĉo'; omega
  have htB : ∀ y ∈ B, t * y * t⁻¹ ∈ B := by
    rintro y ⟨hyN, b, hb, hyb⟩
    refine ⟨conj_mem_of_map_eq ht1 hyN, t * b * t⁻¹, conj_mem_of_map_eq ht2 hb, ?_⟩
    have e : t * y * t⁻¹ * (t * b * t⁻¹) = t * (y * b) * t⁻¹ := by group
    rw [e]
    exact hWS t htS _ hyb
  have hsec := CFSG.Quasithin.L139A5.a5SecInner_of_equiv_psl2 (by omega : 5 < p) ι
  set β : MulAut ↥N₁ :=
    (MulEquiv.subgroupMap (MulAut.conj t) N₁).trans (MulEquiv.subgroupCongr ht1) with hβ
  have hβapp : ∀ x : ↥N₁, ((β x : ↥N₁) : Q) = t * x * t⁻¹ := fun x => by
    rw [hβ]
    rfl
  have : ((⊥ : Subgroup ↥N₁).subgroupOf (B.subgroupOf N₁)).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hB5 : Nonempty ((↥(B.subgroupOf N₁) ⧸ (⊥ : Subgroup ↥N₁).subgroupOf (B.subgroupOf N₁)) ≃*
      alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans ((Subgroup.subgroupOfEquivOfLe hBN).trans eB))⟩
  obtain ⟨a, haB, ha⟩ := hsec (B.subgroupOf N₁) ⊥ bot_le IsPGroup.of_bot hB5 β
    (fun x hx => Subgroup.mem_subgroupOf.mpr (by
      rw [hβapp]
      exact htB _ (Subgroup.mem_subgroupOf.mp hx)))
    (fun x hx => by
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx, map_one])
  set ℓ : Q := ((a : ↥N₁) : Q) with hℓdef
  have hℓB : ℓ ∈ B := Subgroup.mem_subgroupOf.mp haB
  have hℓact : ∀ y ∈ B, t * y * t⁻¹ = ℓ * y * ℓ⁻¹ := by
    intro y hy
    have h1 := ha ⟨y, hBN hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
    rw [Subgroup.mem_bot] at h1
    have h2 : β ⟨y, hBN hy⟩ = a * ⟨y, hBN hy⟩ * a⁻¹ := (inv_mul_eq_one.mp h1)
    have h3 := congrArg Subtype.val h2
    rw [hβapp] at h3
    simpa using h3
  have hℓE : ℓ ∈ Subgroup.normalizer (E : Set Q) := by
    refine A4.mem_normalizer_of_conj_mem fun e he => ?_
    rw [← hℓact e (hEB he)]
    exact ⟨S.mul_mem (S.mul_mem htS he.1) (S.inv_mem htS), conj_mem_of_map_eq ht1 he.2⟩
  have hℓc : ℓ * ĉ * ℓ⁻¹ = ĉ⁻¹ := by
    rw [← hℓact ĉ (hAB hĉA)]
    exact htinv ĉ hĉP
  have hĉB : ĉ ∈ B := hAB hĉA
  refine CFSG.Quasithin.H13.A5F.a5_false eB (E := E.subgroupOf B) (c := ⟨ĉ, hĉB⟩)
    (ℓ := ⟨ℓ, hℓB⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv, hE4]
  · exact fun h => hĉ1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hĉ3)
  · intro e he
    have heE : (e : Q) ∈ E := Subgroup.mem_subgroupOf.mp he
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hĉA.2) e).mp heE
    have h1' : ĉ⁻¹ * (e : Q) * ĉ ∈ E := by simpa using h1
    have h2 : ĉ⁻¹ * (e : Q) * ĉ ∈ B := B.mul_mem (B.mul_mem (B.inv_mem hĉB) e.2) hĉB
    refine ⟨1, ⟨ĉ⁻¹ * (e : Q) * ĉ, h2⟩, Subgroup.mem_subgroupOf.mpr h1', Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, pow_one]
    group
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hℓE x
  · exact Subtype.ext (by simpa using hℓc)

end Config

end CFSG.Quasithin.H13.Ch8310Q
