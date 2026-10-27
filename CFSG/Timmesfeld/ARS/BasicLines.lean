module

public import CFSG.Timmesfeld.ARS.BasicTwoGroup

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem exists_conjSub_eq_of_opposite_opposite (hR : IsRootClass R) {A B C : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Opposite A B) (hBC : Opposite B C)
    (hAC : Commuting A C) :
    ∃ E ∈ R, E ≤ A ⊔ B ⊔ C ∧ Commuting B E ∧ ∃ e ∈ E, ∃ b ∈ B, conjSub A (b * e) = C := by
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  obtain ⟨c, hc, -, hcb⟩ := hBC.2.1 b hb hb1
  have hcc := hR.mul_self C hC c hc
  have hEeq : conjSub B (c * a) = conjSub A (c * b) := by rw [conjSub_mul, hab, ← conjSub_mul]
  have hBeq : B = conjSub C (c * b) := by
    rw [conjSub_mul, ← hcb, ← conjSub_mul, hcc, conjSub_one]
  have hcR : c * b ∈ A ⊔ B ⊔ C := Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
  refine ⟨conjSub A (c * b), hR.conjSub_mem hA _, conjSub_le (le_sup_left.trans le_sup_left) hcR,
    ?_, c * a * b * (c * a)⁻¹, ?_, b⁻¹, B.inv_mem hb, ?_⟩
  · have := hAC.symm.conjSub (c * b)
    rwa [← hBeq] at this
  · rw [← hEeq]
    exact conj_mem_conjSub (c * a) hb
  · have hfix : conjSub A (a⁻¹ * c⁻¹) = A := by
      rw [conjSub_mul, conjSub_of_forall_commute fun x hx => (hAC x hx _ (C.inv_mem hc)).symm,
        conjSub_of_mem (A.inv_mem ha)]
    calc conjSub A (b⁻¹ * (c * a * b * (c * a)⁻¹))
        = conjSub A (b⁻¹ * c * a * b * (a⁻¹ * c⁻¹)) := by congr 1; group
      _ = conjSub (conjSub (conjSub A (a⁻¹ * c⁻¹)) b) (b⁻¹ * c * a) := by
          rw [conjSub_mul, conjSub_mul]
      _ = conjSub (conjSub B a) (b⁻¹ * c * a) := by rw [hfix, hab]
      _ = conjSub B (b⁻¹ * c * (a * a)) := by rw [← conjSub_mul, mul_assoc]
      _ = C := by
          rw [hR.mul_self A hA a ha, mul_one, conjSub_mul, hcb, ← conjSub_mul, inv_mul_cancel,
            conjSub_one]

theorem exists_mem_iSup_conjSub_eq_of_opposite_opposite (hR : IsRootClass R) {A B C : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Opposite A B) (hBC : Opposite B C)
    (hAC : Commuting A C) :
    ∃ g ∈ ⨆ E ∈ {E | E ∈ R ∧ E ≤ A ⊔ B ⊔ C ∧ Commuting B E}, E, conjSub A g = C := by
  obtain ⟨E, hE, hEle, hBE, e, he, b, hb, heq⟩ :=
    exists_conjSub_eq_of_opposite_opposite hR hA hB hC hAB hBC hAC
  refine ⟨b * e, Subgroup.mul_mem _ ?_ ?_, heq⟩
  · exact le_iSup₂_of_le (f := fun (E : Subgroup G) (_ : E ∈ {E | E ∈ R ∧ E ≤ A ⊔ B ⊔ C ∧
      Commuting B E}) => E) B ⟨hB, le_sup_right.trans le_sup_left, hR.commuting_self hB⟩
      le_rfl hb
  · exact le_iSup₂_of_le (f := fun (E : Subgroup G) (_ : E ∈ {E | E ∈ R ∧ E ≤ A ⊔ B ⊔ C ∧
      Commuting B E}) => E) E ⟨hE, hEle, hBE⟩ le_rfl he

theorem card_mul_card_le_card_sup [Finite G] {H K : Subgroup G} (h : H ⊓ K = ⊥) :
    Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : H × K => (⟨p.1 * p.2, Subgroup.mul_mem _
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(H ⊔ K))) ?_
  rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
  have heq' : (h₁ : G) * k₁ = h₂ * k₂ := congrArg Subtype.val heq
  have hmem : (h₂ : G)⁻¹ * h₁ ∈ H ⊓ K := by
    refine ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, ?_⟩
    have e : (h₂ : G)⁻¹ * h₁ = k₂ * (k₁ : G)⁻¹ := by
      calc (h₂ : G)⁻¹ * h₁ = (h₂ : G)⁻¹ * (h₁ * k₁) * (k₁ : G)⁻¹ := by group
        _ = (h₂ : G)⁻¹ * (h₂ * k₂) * (k₁ : G)⁻¹ := by rw [heq']
        _ = k₂ * (k₁ : G)⁻¹ := by group
    rw [e]
    exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hk : (k₁ : G) = k₂ := by
    rw [← hmem] at heq'
    exact mul_left_cancel heq'
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hk)

theorem card_sup_le_of_commuting [Finite G] {H K : Subgroup G} (h : Commuting H K) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p : H × K => (⟨p.1 * p.2, Subgroup.mul_mem _
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(H ⊔ K))) ?_
  rintro ⟨x, hx⟩
  have hle : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_conjSub_le fun g hg =>
    (conjSub_of_forall_commute fun k hk => h g hg k hk).le
  have hx' : x ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

theorem sup_eq_of_le_of_commuting [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A C D₁ D₂ : Subgroup G} (hA : A ∈ R) (hC : C ∈ R) (hD₁ : D₁ ∈ R) (hD₂ : D₂ ∈ R)
    (hAC : Commuting A C) (h₁ : D₁ ≤ A ⊔ C) (h₂ : D₂ ≤ A ⊔ C) (hne : D₁ ≠ D₂) :
    D₁ ⊔ D₂ = A ⊔ C := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le h₁ h₂) ?_
  calc Nat.card ↥(A ⊔ C) ≤ Nat.card A * Nat.card C := card_sup_le_of_commuting hAC
    _ = Nat.card D₁ * Nat.card D₂ := by rw [hR.card_eq hA hD₁, hR.card_eq hC hD₂]
    _ ≤ Nat.card ↥(D₁ ⊔ D₂) := card_mul_card_le_card_sup (inf_eq_bot hR hiso hD₁ hD₂ hne)

theorem coxeter_pow_three {a b c : G} (ha : a * a = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hcb : c * b * c = b * c * b) (hac : a * c = c * a) :
    (b * (a * c)) ^ 3 = b * (b * (a * c)) * b := by
  have h1 : b * (a * c) * (a * c) = b := by
    calc b * (a * c) * (a * c) = b * (a * (c * a) * c) := by group
      _ = b * (a * (a * c) * c) := by rw [hac]
      _ = b * ((a * a) * (c * c)) := by group
      _ = b := by rw [ha, hc, mul_one, mul_one]
  have h2 : (b * (a * c)) ^ 2 = a * c * (b * (a * c)) * b := by
    rw [pow_two]
    calc b * (a * c) * (b * (a * c)) = b * a * (c * b * (a * c)) := by group
      _ = b * a * (c * b * (c * a)) := by rw [hac]
      _ = b * a * (c * b * c) * a := by group
      _ = b * a * (b * c * b) * a := by rw [hcb]
      _ = b * a * b * c * b * a := by group
      _ = a * b * a * c * b * a := by rw [hab]
      _ = a * b * (a * c) * b * a := by group
      _ = a * b * (c * a) * b * a := by rw [hac]
      _ = a * b * c * (a * b * a) := by group
      _ = a * b * c * (b * a * b) := by rw [hab]
      _ = a * (b * c * b) * a * b := by group
      _ = a * (c * b * c) * a * b := by rw [hcb]
      _ = a * c * b * (c * a) * b := by group
      _ = a * c * b * (a * c) * b := by rw [hac]
      _ = a * c * (b * (a * c)) * b := by group
  rw [pow_succ', h2]
  calc b * (a * c) * (a * c * (b * (a * c)) * b)
      = b * (a * c) * (a * c) * (b * (a * c)) * b := by group
    _ = b * (b * (a * c)) * b := by rw [h1]

theorem coxeter_pow_four {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hcb : c * b * c = b * c * b) (hac : a * c = c * a) :
    (b * (a * c)) ^ 4 = 1 := by
  calc (b * (a * c)) ^ 4 = (b * (a * c)) ^ 3 * (b * (a * c)) := pow_succ _ 3
    _ = b * (b * (a * c)) * b * (b * (a * c)) := by
        rw [coxeter_pow_three ha hc hab hcb hac]
    _ = (b * b) * (a * c) * (b * b) * (a * c) := by group
    _ = a * (c * a) * c := by rw [hb, one_mul, mul_one]; group
    _ = 1 := by rw [← hac, ← mul_assoc, ha, one_mul, hc]

theorem coxeter_mul_eq_one {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hcb : c * b * c = b * c * b) (hac : a * c = c * a)
    (h : (b * (a * c)) ^ 2 = 1) : a * c = 1 := by
  have ht : b * (a * c) = a * c * b := by
    have h3 := coxeter_pow_three ha hc hab hcb hac
    rw [pow_succ, h, one_mul, ← mul_assoc b b, hb, one_mul] at h3
    exact h3
  have e2 : b * (a * c) * b = a * b * c * (a * b * c) := by
    calc b * (a * c) * b = b * a * (b * b) * c * b := by rw [hb]; group
      _ = (b * a * b) * (b * c * b) := by group
      _ = (a * b * a) * (c * b * c) := by rw [hab, hcb]
      _ = a * b * (a * c) * b * c := by group
      _ = a * b * (c * a) * b * c := by rw [hac]
      _ = a * b * c * (a * b * c) := by group
  have e3 : b * (a * c) * b = a * c := by rw [ht, mul_assoc, hb, mul_one]
  have e4 : c = b * c * a * b * c := by
    have : a * c = a * (b * c * a * b * c) := by rw [← e3, e2]; group
    exact mul_left_cancel this
  have e5 : b * c * a * b = 1 := by
    have : b * c * a * b * c = 1 * c := by rw [one_mul, ← e4]
    exact mul_right_cancel this
  have e6 : c * a = 1 := by
    calc c * a = (b * b) * (c * a) * (b * b) := by rw [hb, one_mul, mul_one]
      _ = b * (b * c * a * b) * b := by group
      _ = 1 := by rw [e5, mul_one, hb]
  rw [hac, e6]

theorem existsUnique_mem_psiSet_of_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hC : C ∈ lambdaSet R A) : ∃! D, D ∈ R ∧ D ≤ A ⊔ C ∧ D ∈ psiSet R B := by
  have hCΛ := hC
  obtain ⟨⟨hCR, hCA, hAC⟩, hcov⟩ := hC
  have hBC : ¬ Commuting B C := not_commuting_of_opposite_of_mem_lambdaSet hR hB hAB.symm hCΛ
  have hBneC : B ≠ C := fun e => hBC (e ▸ hR.commuting_self hB)
  have hline : Commuting (A ⊔ C) (A ⊔ C) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hA) hAC)
      (Commuting.sup_right hAC.symm (hR.commuting_self hCR))
  have huniq : ∀ D₁ D₂ : Subgroup G, D₁ ∈ R → D₁ ≤ A ⊔ C → Special R B D₁ → D₂ ∈ R →
      D₂ ≤ A ⊔ C → Special R B D₂ → D₁ = D₂ := by
    intro D₁ D₂ hD₁ hle₁ hs₁ hD₂ hle₂ hs₂
    by_contra hne
    have hsup := sup_eq_of_le_of_commuting hR hiso hA hCR hD₁ hD₂ hAC hle₁ hle₂ hne
    have hP := isPGroup_sup_of_special_special hR hiso hD₁ hB hD₂ hs₁.symm hs₂
      (hline.mono hle₁ hle₂)
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
    obtain ⟨b, hb, hb1, -⟩ := hAB.2.1 a ha ha1
    have hodd := hAB.odd_orderOf_mul (hR.mul_self A hA) ha ha1 hb hb1
    have haP : a ∈ D₁ ⊔ B ⊔ D₂ := by
      have : a ∈ D₁ ⊔ D₂ := hsup ▸ Subgroup.mem_sup_left ha
      exact (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
        D₁ ⊔ D₂ ≤ D₁ ⊔ B ⊔ D₂) this
    have hmem : a * b ∈ D₁ ⊔ B ⊔ D₂ :=
      Subgroup.mul_mem _ haP (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
    have h1 := eq_one_of_odd_orderOf_of_isPGroup hP hmem hodd
    have : a ∈ A ⊓ B := ⟨ha, by rw [eq_inv_of_mul_eq_one_left h1]; exact B.inv_mem hb⟩
    rw [hAB.inf_eq_bot, Subgroup.mem_bot] at this
    exact ha1 this
  have hex : ∃ D, D ∈ R ∧ D ≤ A ⊔ C ∧ D ∈ psiSet R B := by
    rcases hR.rel B hB C hCR hBneC with h | h | h
    · exact absurd h hBC
    · obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
      obtain ⟨a, ha, ha1, hab⟩ := hAB.2.2 b hb hb1
      obtain ⟨c, hc, hc1, hcb⟩ := h.symm.2.2 b hb hb1
      have haa := hR.mul_self A hA a ha
      have hbb := hR.mul_self B hB b hb
      have hcc := hR.mul_self C hCR c hc
      have haba : a * b * a = b * a * b := hAB.mul_mul_eq (hR.mul_self A hA) ha ha1 hb hab.symm
      have hcbc : c * b * c = b * c * b :=
        h.symm.mul_mul_eq (hR.mul_self C hCR) hc hc1 hb hcb.symm
      have hac : a * c = c * a := (hAC a ha c hc).eq
      have hd1 : a * c ≠ 1 := by
        intro h1
        have : a ∈ A ⊓ C := ⟨ha, by rw [eq_inv_of_mul_eq_one_left h1]; exact C.inv_mem hc⟩
        rw [inf_eq_bot hR hiso hA hCR (Ne.symm hCA), Subgroup.mem_bot] at this
        exact ha1 this
      obtain ⟨D, hD, hDle, hdD⟩ :=
        hcov (a * c) (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hc))
          hd1
      refine ⟨D, hD, hDle, hD, ?_⟩
      have ht4 := coxeter_pow_four haa hbb hcc haba hcbc hac
      have ht2 : (b * (a * c)) ^ 2 ≠ 1 := fun h2 => hd1 (coxeter_mul_eq_one haa hbb hcc haba hcbc
        hac h2)
      have hsq : ∀ x y : G, x * x = 1 → y * y = 1 → Commute x y → (x * y) ^ 2 = 1 :=
        fun x y hx hy hxy => by
          rw [pow_two, mul_assoc, ← mul_assoc y x, ← hxy.eq, mul_assoc, hy, mul_one, hx]
      have hBD : B ≠ D := by
        rintro rfl
        exact ht2 (hsq _ _ hbb (hR.mul_self B hB _ hdD) (hR.commute hB hb hdD))
      rcases hR.rel B hB D hD hBD with h' | h' | h'
      · exact absurd (hsq _ _ hbb (hR.mul_self D hD _ hdD) (h' b hb _ hdD)) ht2
      · exfalso
        have hodd := h'.odd_orderOf_mul (hR.mul_self B hB) hb hb1 hdD hd1
        have hdvd : orderOf (b * (a * c)) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one ht4
        have hcop : Nat.Coprime (orderOf (b * (a * c))) (2 ^ 2) :=
          (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)).symm
        have h1 := orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)
        exact ht2 (by rw [h1, one_pow])
      · exact h'
    · exact ⟨C, hCR, le_sup_right, hCR, h⟩
  obtain ⟨D, hD⟩ := hex
  exact ⟨D, hD, fun D' hD' => huniq D' D hD'.1 hD'.2.1 hD'.2.2.2 hD.1 hD.2.1 hD.2.2.2⟩

theorem Opposite.conj {A B : Subgroup G} (h : Opposite A B) (g : G) :
    Opposite (conjSub A g) (conjSub B g) := by
  refine ⟨fun e => h.1 (RankOne.map_conj_inj.1 e), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ hx1
    have ha1 : a ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha ha1
    refine ⟨g * b * g⁻¹, conj_mem_conjSub g hb, fun h1 => hb1 (conj_eq_one_iff.1 h1), ?_⟩
    change conjSub (conjSub A g) (g * b * g⁻¹) = conjSub (conjSub B g) (g * a * g⁻¹)
    rw [← conjSub_mul, ← conjSub_mul, show g * b * g⁻¹ * g = g * b by group,
      show g * a * g⁻¹ * g = g * a by group, conjSub_mul A g b, conjSub_mul B g a, hab]
  · rintro _ ⟨b, hb, rfl⟩ hx1
    have hb1 : b ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    obtain ⟨a, ha, ha1, hab⟩ := h.2.2 b hb hb1
    refine ⟨g * a * g⁻¹, conj_mem_conjSub g ha, fun h1 => ha1 (conj_eq_one_iff.1 h1), ?_⟩
    change conjSub (conjSub B g) (g * a * g⁻¹) = conjSub (conjSub A g) (g * b * g⁻¹)
    rw [← conjSub_mul, ← conjSub_mul, show g * a * g⁻¹ * g = g * a by group,
      show g * b * g⁻¹ * g = g * b by group, conjSub_mul B g a, conjSub_mul A g b, hab]

theorem reflTransGen_opposite_conj (hR : IsRootClass R) {A B : Subgroup G}
    (h : Relation.ReflTransGen (fun C D => C ∈ R ∧ D ∈ R ∧ Opposite C D) A B) (g : G) :
    Relation.ReflTransGen (fun C D => C ∈ R ∧ D ∈ R ∧ Opposite C D) (conjSub A g)
      (conjSub B g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hCD ih =>
    exact ih.tail ⟨hR.conjSub_mem hCD.1 g, hR.conjSub_mem hCD.2.1 g, hCD.2.2.conj g⟩

theorem opposite_reflTransGen [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) :
    Relation.ReflTransGen (fun C D => C ∈ R ∧ D ∈ R ∧ Opposite C D) A B := by
  set r : Subgroup G → Subgroup G → Prop := fun C D => C ∈ R ∧ D ∈ R ∧ Opposite C D with hr
  have hsymm : ∀ {X Y : Subgroup G}, Relation.ReflTransGen r X Y →
      Relation.ReflTransGen r Y X := by
    intro X Y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hCD ih => exact Relation.ReflTransGen.head ⟨hCD.2.1, hCD.1, hCD.2.2.symm⟩ ih
  set Δ : Set (Subgroup G) := {F | Relation.ReflTransGen r A F} with hΔ
  have hΔR : ∀ F ∈ Δ, F ∈ R := by
    intro F hF
    induction hF with
    | refl => exact hA
    | tail _ hCD _ => exact hCD.2.1
  set U : Subgroup G := ⨆ F ∈ Δ, F with hU
  have hFU : ∀ F ∈ Δ, F ≤ U := fun F hF =>
    le_iSup₂ (f := fun (E : Subgroup G) (_ : E ∈ Δ) => E) F hF
  let S : Subgroup G :=
    { carrier := {g | Relation.ReflTransGen r A (conjSub A g)}
      one_mem' := by
        change Relation.ReflTransGen r A (conjSub A 1)
        rw [conjSub_one]
      mul_mem' := fun {g h} hg hh => by
        change Relation.ReflTransGen r A (conjSub A (g * h))
        rw [conjSub_mul]
        exact hg.trans (reflTransGen_opposite_conj hR hh g)
      inv_mem' := fun {g} hg => by
        change Relation.ReflTransGen r A (conjSub A g⁻¹)
        have := reflTransGen_opposite_conj hR (hg : Relation.ReflTransGen r A (conjSub A g)) g⁻¹
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
        exact hsymm this }
  have hSΔ : ∀ g ∈ S, ∀ F ∈ Δ, conjSub F g ∈ Δ := fun g hg F hF =>
    (hg : Relation.ReflTransGen r A (conjSub A g)).trans (reflTransGen_opposite_conj hR hF g)
  have hUS : U ≤ S := by
    refine iSup₂_le fun E hE d hd => ?_
    have h1 := reflTransGen_opposite_conj hR (hE : Relation.ReflTransGen r A E) d
    rw [conjSub_of_mem hd] at h1
    exact (hE : Relation.ReflTransGen r A E).trans (hsymm h1)
  have key : ∀ F ∈ Δ, ∀ C ∈ R, ∀ c ∈ C, conjSub F c ≤ U := by
    intro F hF C hC c hc
    have hFR := hΔR F hF
    by_cases hFc : conjSub F c ∈ Δ
    · exact hFU _ hFc
    have hCΔ : C ∉ Δ := fun hCΔ => hFc (hSΔ c (hUS (hFU C hCΔ hc)) F hF)
    have hFC : F ≠ C := fun e => hCΔ (e ▸ hF)
    have hc1 : c ≠ 1 := fun e => hFc (by rw [e, conjSub_one]; exact hF)
    rcases hR.rel F hFR C hC hFC with hcomm | hopp | hspec
    · exact (hFc (by
        rw [conjSub_of_forall_commute fun x hx => (hcomm x hx c hc).symm]; exact hF)).elim
    · exact absurd ((hF : Relation.ReflTransGen r A F).tail ⟨hFR, hC, hopp⟩) hCΔ
    have hDR : ⁅F, C⁆ ∈ R := hspec.1
    have hDΛ : ⁅F, C⁆ ∈ lambdaSet R F :=
      mem_lambdaSet_comm hDR (mem_lambdaSet_commutator hR hiso hFR hC hspec).1
    have hFcle : conjSub F c ≤ ⁅F, C⁆ ⊔ F := conjSub_le_commutator_sup hc
    obtain ⟨B', hB'R, hFB'⟩ := hiso F hFR
    have hB'Δ : B' ∈ Δ := (hF : Relation.ReflTransGen r A F).tail ⟨hFR, hB'R, hFB'⟩
    suffices hDΔ : ⁅F, C⁆ ∈ Δ from hFcle.trans (sup_le (hFU _ hDΔ) (hFU F hF))
    by_contra hDΔ
    have hs1 : Special R B' ⁅F, C⁆ := by
      have hB'D : ¬ Commuting B' ⁅F, C⁆ :=
        not_commuting_of_opposite_of_mem_lambdaSet hR hB'R hFB'.symm hDΛ
      have hne : B' ≠ ⁅F, C⁆ := fun e => hDΔ (e ▸ hB'Δ)
      rcases hR.rel B' hB'R _ hDR hne with h | h | h
      · exact absurd h hB'D
      · exact absurd ((hB'Δ : Relation.ReflTransGen r A B').tail ⟨hB'R, hDR, h⟩) hDΔ
      · exact h
    have hFcR := hR.conjSub_mem hFR c
    have hFcΛ : conjSub F c ∈ lambdaSet R F := by
      refine ⟨⟨hFcR, fun e => hFc (by rw [e]; exact hF), ?_⟩, ?_⟩
      · exact (Commuting.sup_left hspec.2.1 (hR.commuting_self hFR)).symm.mono le_rfl hFcle
      · rw [sup_conjSub_eq_sup_commutator hR hiso hFR hC hspec hc hc1]
        exact hDΛ.2
    have hs2 : Special R B' (conjSub F c) := by
      have hB'F : ¬ Commuting B' (conjSub F c) :=
        not_commuting_of_opposite_of_mem_lambdaSet hR hB'R hFB'.symm hFcΛ
      have hne : B' ≠ conjSub F c := fun e => hFc (e ▸ hB'Δ)
      rcases hR.rel B' hB'R _ hFcR hne with h | h | h
      · exact absurd h hB'F
      · exact absurd ((hB'Δ : Relation.ReflTransGen r A B').tail ⟨hB'R, hFcR, h⟩) hFc
      · exact h
    have heq := (existsUnique_mem_psiSet_of_le hR hiso hFR hB'R hFB' hDΛ).unique
      ⟨hDR, le_sup_right, hDR, hs1⟩ ⟨hFcR, hFcle.trans (sup_comm _ _).le, hFcR, hs2⟩
    have hcomm : Commuting (conjSub F c) C := heq ▸ hspec.2.2
    have := hcomm.conjSub c⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_of_mem (C.inv_mem hc)] at this
    exact hspec.not_commuting hR this
  have hnorm : ∀ C ∈ R, C ≤ Subgroup.normalizer (U : Set G) := fun C hC =>
    le_normalizer_of_conjSub_le fun c hc => by
      rw [Subgroup.map_le_iff_le_comap]
      exact iSup₂_le fun F hF => Subgroup.map_le_iff_le_comap.1 (key F hF C hC c hc)
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 (hR.gen ▸ iSup₂_le fun E hE => ?_)
    obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hE
    have hg : g ∈ Subgroup.normalizer (U : Set G) := by
      have : (⊤ : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := hR.gen ▸ iSup₂_le hnorm
      exact this (Subgroup.mem_top g)
    rw [← conjSub_eq_self_iff.2 hg]
    exact Subgroup.map_mono (hFU A Relation.ReflTransGen.refl)
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
  exact (hUS (hUtop ▸ Subgroup.mem_top g) : Relation.ReflTransGen r A (conjSub A g))

theorem mem_lambdaSet_of_commutator_eq [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (h : ⁅B, C⁆ = A) :
    B ∈ lambdaSet R A := by
  have hBC : B ≠ C := by
    rintro rfl
    exact hR.ne_bot A hA (h ▸ hR.commutator_self_eq_bot hB)
  rcases hR.rel B hB C hC hBC with hc | ho | hs
  · exact absurd (h ▸ commuting_iff_commutator_eq_bot.1 hc) (hR.ne_bot A hA)
  · exfalso
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
    obtain ⟨c, hc, hc1, hbc⟩ := ho.2.1 b hb hb1
    have hbb := hR.mul_self B hB b hb
    have hcc := hR.mul_self C hC c hc
    have hbraid : b * c * b = c * b * c := ho.mul_mul_eq (hR.mul_self B hB) hb hb1 hc hbc
    have hmem : ⁅b, c⁆ ∈ A := h ▸ Subgroup.commutator_mem_commutator hb hc
    have hsq := hR.mul_self A hA _ hmem
    have hu : ⁅b, c⁆ = b * c * (b * c) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hbb, inv_eq_of_mul_eq_one_right hcc]
      group
    have h3 : b * c * (b * c) * (b * c) = 1 := by
      calc b * c * (b * c) * (b * c) = (b * c * b) * (c * b * c) := by group
        _ = (c * b * c) * (c * b * c) := by rw [hbraid]
        _ = c * b * (c * c) * b * c := by group
        _ = 1 := by rw [hcc, mul_one, mul_assoc c b b, hbb, mul_one, hcc]
    have hbc1 : b * c = 1 := by
      calc b * c = (b * c * (b * c)) * (b * c * (b * c)) * (b * c * (b * c) * (b * c))⁻¹ := by
            group
        _ = 1 := by rw [h3, ← hu, hsq, inv_one, mul_one]
    have : c ∈ B ⊓ C := ⟨by rw [eq_inv_of_mul_eq_one_right hbc1]; exact B.inv_mem hb, hc⟩
    rw [ho.inf_eq_bot, Subgroup.mem_bot] at this
    exact hc1 this
  · have := (mem_lambdaSet_commutator hR hiso hB hC hs).1
    rwa [h] at this

end CFSG.Timmesfeld.ARS
