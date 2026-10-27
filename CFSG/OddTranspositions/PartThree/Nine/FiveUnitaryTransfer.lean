module

public import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryLocal
import CFSG.OddTranspositions.PartThree.Nine.FinalCentral
import CFSG.GH74.GLS.Bg.Local.Transfer1515
import CFSG.GH74.Uniqueness.Bender.Out
import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.GH74.Uniqueness.Section14Aut

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

namespace IsTranslationSubgroup

variable {L L₀ Y V : Subgroup G} {Γ : Set G}

section Helpers

variable {X : Type*} [Group X]

private theorem mem_normalizer_of_forall_conj_mem [Finite X] {A : Subgroup X} {g : X}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem conj_mem_sup_of_forall {A B : Subgroup X} {g : X}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) :
    ∀ w ∈ A ⊔ B, g * w * g⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left (hA a ha))
      (fun b hb => Subgroup.mem_sup_right (hB b hb))
  exact fun w hw => hle hw

private theorem conj_mem_commutator_of_forall {Y : Subgroup X} {g : X}
    (hY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : ∀ c ∈ ⁅Y, Y⁆, g * c * g⁻¹ ∈ ⁅Y, Y⁆ := by
  have hmap : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact hY y hy
  have h : ⁅Y, Y⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅Y, Y⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact fun c hc => h ⟨c, hc, rfl⟩

private theorem conj_mem_closure_of_forall {Γ : Set X} {g : X}
    (h : ∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ) :
    ∀ y ∈ Subgroup.closure Γ, g * y * g⁻¹ ∈ Subgroup.closure Γ := by
  have hle : Subgroup.closure Γ ≤ (Subgroup.closure Γ).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun c hc => Subgroup.subset_closure (h c hc)
  exact fun y hy => hle hy

private theorem reach_conj_of_forall {D' : Set X} {g : X} (hg : ∀ x ∈ D', g * x * g⁻¹ ∈ D')
    {x y : X} (h : Reach D' x y) : Reach D' (g * x * g⁻¹) (g * y * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨hg _ hbc.1, hg _ hbc.2.1, (Commute.conj_iff g).2 hbc.2.2⟩

private theorem conj_mem_centralizer_of_mem_normalizer {s : Set X} {g x : X}
    (hg : g ∈ Subgroup.normalizer s) (hx : x ∈ Subgroup.centralizer s) :
    g * x * g⁻¹ ∈ Subgroup.centralizer s := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have h1 := hx _ ((Subgroup.mem_set_normalizer_iff''.mp hg h).mp hh)
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * h := by group

private theorem eq_one_of_mem_of_isPGroup {L P : Subgroup X} (hL : Odd (Nat.card L))
    (hP : IsPGroup 2 P) {x : X} (hxL : x ∈ L) (hxP : x ∈ P) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd := Subgroup.orderOf_dvd_natCard L hxL
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rwa [hk0, pow_zero, orderOf_eq_one_iff] at hk
  · exact absurd (Odd.of_dvd_nat hL hdvd)
      (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩))

private theorem eq_one_of_mul_self_eq_one_of_odd {L : Subgroup X} (hL : Odd (Nat.card L))
    {l : X} (hl : l ∈ L) (h : l * l = 1) : l = 1 := by
  have h1 : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h])
  have h3 : Odd (orderOf l) := Odd.of_dvd_nat hL (Subgroup.orderOf_dvd_natCard L hl)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h4 | h4
  · exact orderOf_eq_one_iff.mp h4
  · rw [h4] at h3
    exact absurd h3 (by decide)

private theorem eq_one_or_eq_of_mem_zpowers {a y : X} (ha : a * a = 1)
    (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem commute_of_forall_conj_eq_inv {L : Subgroup X} {a : X}
    (ha : ∀ l ∈ L, a * l * a⁻¹ = l⁻¹) {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L) :
    Commute l l' := by
  have h1 := ha _ (L.mul_mem hl hl')
  have h2 : a * (l * l') * a⁻¹ = (a * l * a⁻¹) * (a * l' * a⁻¹) := by group
  rw [h2, ha l hl, ha l' hl', mul_inv_rev] at h1
  have h3 := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h3
  exact h3.symm

private theorem le_of_isPGroup_of_forall_conj_mem [Finite X] {T L L₀ B K : Subgroup X}
    (hB : B = T ⊔ L₀) (hTn : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T) (hT : IsPGroup 2 T)
    (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥) (hLL₀ : L ≤ L₀)
    (hL₀ : L₀ = L ∨ ∃ a ∈ L₀, a * a = 1 ∧ a ∉ L ∧ (∀ l ∈ L, a * l * a⁻¹ = l⁻¹) ∧
      L₀ = L ⊔ Subgroup.zpowers a)
    (hKB : K ≤ B) (hK : IsPGroup 2 K) (hKn : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K) : K ≤ T := by
  intro k hk
  have hL₀B : L₀ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hL₀T : L₀ ≤ Subgroup.normalizer (T : Set X) := fun l hl =>
    mem_normalizer_of_forall_conj_mem (hTn l (hL₀B hl))
  have hKT : K ≤ Subgroup.normalizer (T : Set X) := fun x hx =>
    mem_normalizer_of_forall_conj_mem (hTn x (hKB hx))
  have hM : IsPGroup 2 (T ⊔ K : Subgroup X) := hT.to_sup_of_normal_left' hK hKT
  have hMn : ∀ b ∈ B, ∀ m ∈ T ⊔ K, b * m * b⁻¹ ∈ T ⊔ K := fun b hb =>
    conj_mem_sup_of_forall (hTn b hb) (hKn b hb)
  have hkB : k ∈ ((T ⊔ L₀ : Subgroup X) : Set X) := by
    rw [← hB]
    exact hKB hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T L₀ hL₀T] at hkB
  obtain ⟨t, ht, l₀, hl₀, rfl⟩ := Set.mem_mul.mp hkB
  have hl₀M : l₀ ∈ T ⊔ K := by
    have e : l₀ = t⁻¹ * (t * l₀) := by group
    rw [e]
    exact (T ⊔ K).mul_mem (Subgroup.mem_sup_left (T.inv_mem ht)) (Subgroup.mem_sup_right hk)
  have hLM : ∀ l ∈ L, l ∈ T ⊔ K → l = 1 := fun l hl hlM =>
    eq_one_of_mem_of_isPGroup hLo hM hl hlM
  suffices hl₀1 : l₀ = 1 by
    rw [hl₀1, mul_one]
    exact ht
  rcases hL₀ with hL₀ | ⟨a, -, ha2, -, hainv, hL₀eq⟩
  · exact hLM l₀ (hL₀ ▸ hl₀) hl₀M
  · have hzL : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set X) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_forall_conj_mem fun l hl => by
        rw [hainv l hl]
        exact L.inv_mem hl
    have hl₀' : l₀ ∈ ((L ⊔ Subgroup.zpowers a : Subgroup X) : Set X) := by
      rw [← hL₀eq]
      exact hl₀
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hzL] at hl₀'
    obtain ⟨l, hl, y, hy, hly⟩ := Set.mem_mul.mp hl₀'
    rcases eq_one_or_eq_of_mem_zpowers ha2 hy with hy1 | hya
    · rw [← hly, hy1, mul_one] at hl₀M ⊢
      exact hLM l hl hl₀M
    · exfalso
      rw [← hly, hya] at hl₀M
      apply hL1
      rw [eq_bot_iff]
      intro l' hl'
      rw [Subgroup.mem_bot]
      have hl'B : l' ∈ B := hL₀B (hLL₀ hl')
      have he : l * a * l' * (l * a)⁻¹ * l'⁻¹ = l'⁻¹ * l'⁻¹ := by
        have h1 : a * l' * a⁻¹ = l'⁻¹ := hainv l' hl'
        have h2 : l * l'⁻¹ = l'⁻¹ * l :=
          (commute_of_forall_conj_eq_inv hainv hl (L.inv_mem hl')).eq
        calc l * a * l' * (l * a)⁻¹ * l'⁻¹ = l * (a * l' * a⁻¹) * l⁻¹ * l'⁻¹ := by group
          _ = l * l'⁻¹ * l⁻¹ * l'⁻¹ := by rw [h1]
          _ = l'⁻¹ * l * l⁻¹ * l'⁻¹ := by rw [h2]
          _ = l'⁻¹ * l'⁻¹ := by group
      have hmem : l'⁻¹ * l'⁻¹ ∈ T ⊔ K := by
        rw [← he]
        have h3 := hMn l' hl'B _ ((T ⊔ K).inv_mem hl₀M)
        have e : l * a * l' * (l * a)⁻¹ * l'⁻¹ = (l * a) * (l' * (l * a)⁻¹ * l'⁻¹) := by group
        rw [e]
        exact (T ⊔ K).mul_mem hl₀M h3
      have h4 := hLM _ (L.mul_mem (L.inv_mem hl') (L.inv_mem hl')) hmem
      have h5 : l' * l' = 1 := by
        have := congrArg (·⁻¹) h4
        simpa [mul_inv_rev] using this
      exact eq_one_of_mul_self_eq_one_of_odd hLo hl' h5

private theorem eq_one_or_eq_of_isCyclic [Finite X] [IsCyclic X] {x y : X} (hx : x * x = 1)
    (hx1 : x ≠ 1) (hy : y * y = 1) : y = 1 ∨ y = x := by
  classical
  have := Fintype.ofFinite X
  by_contra hne
  push Not at hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset X) ⊆ Finset.univ.filter (fun a : X => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two, hx]
    · rw [pow_two, hy]
  have h3 : ({1, x, y} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne.2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx1.symm, hne.1.symm⟩
  have := Finset.card_le_card hsub
  omega

private theorem mem_zpowers_of_isCyclic [Finite X] [IsCyclic X] {x y : X} (hx : x * x = 1)
    (hx1 : x ≠ 1) (hy : IsPGroup 2 (Subgroup.zpowers y)) (hy1 : y ≠ 1) :
    x ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers y) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hy
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hk
      exact absurd hk hy1
    · rw [hk]
      exact dvd_pow_self 2 hk0.ne'
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers y) 2 h2
  have hy'1 : (y' : X) ≠ 1 := by
    intro h
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hy'
    exact absurd hy' (by decide)
  have hy'2 : (y' : X) * (y' : X) = 1 := by
    rw [← pow_two, ← hy', ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  rcases eq_one_or_eq_of_isCyclic hx hx1 hy'2 with h | h
  · exact absurd h hy'1
  · rw [← h]
    exact y'.2

private theorem commutator_le_of_isCyclic {N : Subgroup X} [N.Normal] (h : IsCyclic (X ⧸ N)) :
    commutator X ≤ N := by
  have : IsMulCommutative (X ⧸ N) := inferInstance
  have h2 := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rwa [QuotientGroup.ker_mk'] at h2

private theorem not_mem_commutator_of_forall [Finite X] {P W : Subgroup X} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hWP : W ≤ P) (hWn : ∀ t ∈ P, ∀ w ∈ W, t * w * t⁻¹ ∈ W) {a : X}
    (haP : a ∈ P) (haW : a ∉ W) (ha2 : a * a = 1) (hgen : ∀ t ∈ P, t ∈ W ∨ a⁻¹ * t ∈ W)
    (hconj : ∀ g : X, g⁻¹ * a * g ∈ P → a⁻¹ * (g⁻¹ * a * g) ∈ W) : a ∉ commutator X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hcyc, -, haN⟩ | ⟨g, hgW, -, -⟩ :=
    CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP hPidx hWn
      ⟨a, haP, fun t ht => by
        rcases hgen t ht with htW | htW
        · exact ⟨0, by simpa using htW⟩
        · exact ⟨1, by simpa using htW⟩⟩
      haP haW (fun g k _ => by
        rw [pow_mul, pow_two, ha2, one_pow, mul_one, inv_mul_cancel]
        exact W.one_mem)
      (fun g hg _ => Or.inr (hconj g hg))
  · have := hN
    exact fun ha => haN (commutator_le_of_isCyclic hcyc ha)
  · have h1 := hconj g (hWP hgW)
    intro _
    apply haW
    have e : a = ((a⁻¹ * (g⁻¹ * a * g)) * (g⁻¹ * a * g)⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem (W.mul_mem h1 (W.inv_mem hgW))

end Helpers

omit [Finite G] in
private theorem sylow_le_normalizer_inter (hC : HypothesisC D) (S : Sylow 2 G) :
    (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) := by
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxD⟩
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hxS)
      ((S : Subgroup G).inv_mem hs), hC.setup.conj_mem s hxD⟩
  · rintro ⟨hxS, hxD⟩
    have e : x = s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs)
      hxS) ((S : Subgroup G).inv_mem ((S : Subgroup G).inv_mem hs)),
      hC.setup.conj_mem s⁻¹ hxD⟩

omit [Finite G] in
private theorem mul_mem_inter (hU : DeltaSetup hC T S U) {z : G} (hz : z ∈ U) :
    hC.d * z ∈ (S : Set G) ∩ D := by
  rw [hU.sylow_inter]
  exact ⟨z, hz, rfl⟩

omit [Finite G] in
private theorem d_mem_inter (hU : DeltaSetup hC T S U) : hC.d ∈ (S : Set G) ∩ D := by
  simpa using mul_mem_inter hU U.one_mem

omit [Finite G] in
private theorem conj_mem_of_mem_normalizer (hU : DeltaSetup hC T S U) {g : G}
    (hg : g ∈ Subgroup.normalizer ((S : Set G) ∩ D)) {z : G} (hz : z ∈ U) :
    g * z * g⁻¹ ∈ U := by
  have h1 := (Subgroup.mem_set_normalizer_iff.mp hg _).mp (d_mem_inter hU)
  have h2 := (Subgroup.mem_set_normalizer_iff.mp hg _).mp (mul_mem_inter hU hz)
  rw [hU.sylow_inter] at h1 h2
  obtain ⟨z₁, hz₁, e₁ : hC.d * z₁ = g * hC.d * g⁻¹⟩ := h1
  obtain ⟨z₂, hz₂, e₂ : hC.d * z₂ = g * (hC.d * z) * g⁻¹⟩ := h2
  have e : g * z * g⁻¹ = (g * hC.d * g⁻¹)⁻¹ * (g * (hC.d * z) * g⁻¹) := by group
  rw [e, ← e₁, ← e₂, show (hC.d * z₁)⁻¹ * (hC.d * z₂) = z₁⁻¹ * z₂ by group]
  exact U.mul_mem (U.inv_mem hz₁) hz₂

omit [Finite G] in
private theorem commute_of_mem_centralizer (hU : DeltaSetup hC T S U) {x z : G}
    (hx : x ∈ Subgroup.centralizer ((S : Set G) ∩ D)) (hz : z ∈ U) : Commute x z := by
  rw [Subgroup.mem_centralizer_iff] at hx
  have h1 : Commute x hC.d := (hx _ (d_mem_inter hU)).symm
  have h2 : Commute x (hC.d * z) := (hx _ (mul_mem_inter hU hz)).symm
  have h3 := h1.inv_right.mul_right h2
  rwa [inv_mul_cancel_left] at h3

omit [Finite G] in
private theorem sylow_map_le_centralizer (hL : UnitaryCentralizerData hC T S U n L L₀) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.centralizer ((S : Set G) ∩ D) := by
  rw [hL.centralizer_eq]
  exact le_sup_left

private theorem inter_subset_component (hU : DeltaSetup hC T S U)
    (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) :
    (S : Set G) ∩ D ⊆ Γ := by
  have hD' : ∀ x ∈ (S : Set G) ∩ D, x ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D :=
    fun x hx => ⟨Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hL.le_centralizer hl) x hx).symm, hx.2⟩
  intro δ hδ
  rw [hΓ]
  have hδ' := hδ
  rw [hU.sylow_inter] at hδ'
  obtain ⟨z, hz, rfl⟩ := hδ'
  have huz : Commute hC.d z :=
    (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer z hz).symm
  exact reach_of_commute (hD' _ (d_mem_inter hU)) (hD' _ hδ) ((Commute.refl _).mul_right huz)

private theorem conj_mem_component (hU : DeltaSetup hC T S U)
    (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) {g : G}
    (hgN : g ∈ Subgroup.normalizer ((S : Set G) ∩ D))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) : ∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ := by
  have hΔΓ := inter_subset_component hU hL hΓ
  have hD' : ∀ x ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D,
      g * x * g⁻¹ ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D := fun x hx =>
    ⟨conj_mem_centralizer_of_mem_normalizer hgL hx.1, hC.setup.conj_mem g hx.2⟩
  have hu : g * hC.d * g⁻¹ ∈ Γ :=
    hΔΓ ((Subgroup.mem_set_normalizer_iff.mp hgN _).mp (d_mem_inter hU))
  intro c hc
  rw [hΓ] at hu hc ⊢
  exact reach_trans hu (reach_conj_of_forall hD' hc)

omit [Finite G] in
private theorem conj_mem_of_forall (hV : IsTranslationSubgroup hC S U Y V n) {g : G}
    (hYg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hUg : ∀ z ∈ U, g⁻¹ * z * g ∈ U) :
    ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
  have hle := hV.unique (V.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_
  · exact fun v hv => hle ⟨v, hv, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact conj_mem_commutator_of_forall hYg v (hV.le_commutator hv)
  · exact (S.isPGroup'.to_le hV.le_sylow).map _
  · intro z hz
    refine ⟨g⁻¹ * z * g, hV.le (hUg z hz), ?_⟩
    show g * (g⁻¹ * z * g) * g⁻¹ = z
    group

section HelpersOut

variable {X : Type*} [Group X]

private theorem mem_centralizer_sup_of_mem {A B : Subgroup X} {x : X}
    (hA : x ∈ Subgroup.centralizer (A : Set X)) (hB : x ∈ Subgroup.centralizer (B : Set X)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup X) : Set X) := by
  have h : A ⊔ B ≤ Subgroup.centralizer ({x} : Set X) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hB b hb))
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (h hy)

private theorem isPGroup_zpowers_of_mul_self {a : X} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  rintro ⟨y, hy⟩
  refine ⟨1, Subtype.ext ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers ha hy with rfl | rfl
  · simp
  · simp [pow_two, ha]

private theorem commute_of_mem_of_isElementaryAbelian {A : Subgroup X}
    (hA : IsElementaryAbelian 2 A) {a b : X} (ha : a ∈ A) (hb : b ∈ A) : Commute a b :=
  congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem conjAut_eq_conj_of_mul_inv_mem {K : Subgroup X} {c : X}
    (hcN : c ∈ Subgroup.normalizer (K : Set X)) {l : X} (hl : l ∈ K)
    (h : c * l⁻¹ ∈ Subgroup.centralizer (K : Set X)) :
    CFSG.GH74.Uniqueness.conjAut K ⟨c, hcN⟩ = MulAut.conj ⟨l, hl⟩ := by
  ext x
  rw [CFSG.GH74.Uniqueness.conjAut_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have h1 := Subgroup.mem_centralizer_iff.mp h _ (K.mul_mem (K.mul_mem hl x.2) (K.inv_mem hl))
  calc c * x * c⁻¹ = (c * l⁻¹) * (l * x * l⁻¹) * (c * l⁻¹)⁻¹ := by group
    _ = (l * x * l⁻¹) * (c * l⁻¹) * (c * l⁻¹)⁻¹ := by rw [← h1]
    _ = l * x * l⁻¹ := by group

private theorem exists_outer_involution_of_benderType {K : Type}
    [Group K] [Finite K] {m e : ℕ} (h : CFSG.GH74.Uniqueness.Bender.BenderType K m 3 e) :
    ∃ α : MulAut K, α * α = 1 ∧ α ∉ (MulAut.conj : K →* MulAut K).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := Sylow.nonempty
  obtain ⟨Dd, hinf, hsup, hnorm, hcard, -⟩ := h.lemma_3_6_c_unitary Q
  obtain ⟨δ, hδ⟩ := exists_prime_orderOf_dvd_card' (G := Dd) 2
    (by rw [hcard]; exact dvd_mul_right 2 _)
  have hδ' : orderOf (δ : MulAut K) = 2 := by rw [Subgroup.orderOf_coe]; exact hδ
  have hδ2 : (δ : MulAut K) * δ = 1 := by rw [← pow_two, ← hδ', pow_orderOf_eq_one]
  have hδC : (δ : MulAut K) ∈ CFSG.GH74.Uniqueness.Bender.autCentralizer
      (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)) := by
    rw [← hsup]
    exact Subgroup.mem_sup_right δ.2
  have hδI : (δ : MulAut K) ∉ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    intro hI
    have h1 : (δ : MulAut K) ∈ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) ⊓ Dd :=
      ⟨hI, δ.2⟩
    rw [hinf, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hδ'
    exact absurd hδ' (by decide)
  refine ⟨δ, hδ2, ?_⟩
  rintro ⟨k, hk⟩
  have hkZ : k ∈ Subgroup.centralizer
      ((CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K) : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := (CFSG.GH74.Uniqueness.Bender.mem_autCentralizer_iff.mp hδC) z hz
    rw [← hk, MulAut.conj_apply] at h1
    calc z * k = k * z * k⁻¹ * k := by rw [h1]
      _ = k * z := by group
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hcent := hc.centralizer_rootCenter_eq
  rw [hcent, sup_comm] at hkZ
  have hFQ : CFSG.GH74.Uniqueness.Bender.fixCartan (Q : Subgroup K) t ≤
      Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
    (CFSG.GH74.Uniqueness.Bender.fixCartan_le_cartan _ _).trans inf_le_left
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFQ] at hkZ
  obtain ⟨d, hd, q, hq, rfl⟩ := Set.mem_mul.mp hkZ
  have hnorm' := hnorm
  have hqC : MulAut.conj q ∈ CFSG.GH74.Uniqueness.Bender.autCentralizer
      (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)) := by
    intro z hz
    rw [MulAut.conj_apply, (CFSG.GH74.Uniqueness.Bender.mem_rootCenter_iff.mp hz).2 q hq,
      mul_inv_cancel_right]
  have hdC : MulAut.conj d ∈ CFSG.GH74.Uniqueness.Bender.autCentralizer
      (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)) := by
    intro z hz
    have hd' : d ∈ Subgroup.centralizer
        ((CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K) : Subgroup K) : Set K) := by
      rw [hcent]
      exact Subgroup.mem_sup_right hd
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.mp hd' z hz, mul_inv_cancel_right]
  have heq : (QuotientGroup.mk' (((Q : Subgroup K).map (MulAut.conj : K →* MulAut K)).subgroupOf
      (CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K))))) ⟨δ, hδC⟩ =
      QuotientGroup.mk' _ ⟨MulAut.conj d, hdC⟩ := by
    have h1 : (⟨δ, hδC⟩ : CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K))) =
        ⟨MulAut.conj d, hdC⟩ * ⟨MulAut.conj q, hqC⟩ := by
      apply Subtype.ext
      show (δ : MulAut K) = MulAut.conj d * MulAut.conj q
      rw [← hk, map_mul]
    have h2 : QuotientGroup.mk' (((Q : Subgroup K).map (MulAut.conj : K →* MulAut K)).subgroupOf
        (CFSG.GH74.Uniqueness.Bender.autCentralizer
          (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)))) ⟨MulAut.conj q, hqC⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ⟨q, hq, rfl⟩)
    rw [h1, map_mul, h2, mul_one]
  have hord1 : orderOf (QuotientGroup.mk' (((Q : Subgroup K).map
      (MulAut.conj : K →* MulAut K)).subgroupOf (CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)))) ⟨δ, hδC⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hδI ?_
    · have h2 : (⟨δ, hδC⟩ : CFSG.GH74.Uniqueness.Bender.autCentralizer
          (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K))) ^ 2 = 1 :=
        Subtype.ext (by simp [pow_two, hδ2])
      rw [← map_pow, h2, map_one]
    · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
  have hord2 : Odd (orderOf (QuotientGroup.mk' (((Q : Subgroup K).map
      (MulAut.conj : K →* MulAut K)).subgroupOf (CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K)))) ⟨MulAut.conj d, hdC⟩)) := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (((Q : Subgroup K).map
      (MulAut.conj : K →* MulAut K)).subgroupOf (CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K))))) ⟨MulAut.conj d, hdC⟩
    have h2 : orderOf (⟨MulAut.conj d, hdC⟩ : CFSG.GH74.Uniqueness.Bender.autCentralizer
        (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup K))) ∣ orderOf d := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_map_dvd MulAut.conj d
    have h3 : orderOf d ∣ Nat.card (CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t) :=
      Subgroup.orderOf_dvd_natCard _ (CFSG.GH74.Uniqueness.Bender.fixCartan_le_cartan _ _ hd)
    exact Odd.of_dvd_nat hc.odd_card_cartan (h1.trans (h2.trans h3))
  rw [← heq, hord1] at hord2
  exact absurd hord2 (by decide)

end HelpersOut

private theorem centralizer_d_le_normalizer_pResidualOf (h3 : Conclusion9_3 D hC) :
    Subgroup.centralizer ({hC.d} : Set G) ≤
      Subgroup.normalizer (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Set G) := by
  intro c hc
  have hcu : c * hC.d = hC.d * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
    (mem_normalizer_of_forall_conj_mem ?_)
  have hH : Halpha D hC.alpha = Subgroup.closure (commSet D hC.d) := by
    rw [← DalphaStar_eq_commSet hC h3.1]
    rfl
  rw [hH]
  refine conj_mem_closure_of_forall ?_
  rintro e ⟨heD, heu, hne⟩
  refine ⟨hC.setup.conj_mem c heD, ?_, ?_⟩
  · have h1 := (Commute.conj_iff c).mpr heu
    rwa [hcu, mul_inv_cancel_right] at h1
  · intro h
    apply hne
    calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
      _ = c⁻¹ * hC.d * c := by rw [h]
      _ = hC.d := by rw [mul_assoc, ← hcu, inv_mul_cancel_left]

private theorem mem_zpowers_of_mem_centralizer (h3 : Conclusion9_3 D hC)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d) {x : G}
    (hxu : Commute x hC.d)
    (hxJ : x ∈ Subgroup.centralizer (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Set G)) :
    x ∈ Subgroup.zpowers hC.d := by
  have h1 : x ∈ Subgroup.centralizer ((Subgroup.zpowers hC.d ⊔
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) : Set G) := by
    refine mem_centralizer_sup_of_mem ?_ hxJ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hxu.zpow_right k).symm
  rw [h3.2.2.1, hCH] at h1
  exact h1

private theorem center_pResidualOf_eq_bot (h3 : Conclusion9_3 D hC)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d) :
    Subgroup.center ↥(CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH : (z : G) ∈ Halpha D hC.alpha := Subgroup.map_subtype_le _ z.2
  have hzu : Commute (z : G) hC.d :=
    Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hzH)
  have hzJ : (z : G) ∈ Subgroup.centralizer
      (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  exact Subtype.ext (Subgroup.disjoint_def.mp h3.2.2.2
    (mem_zpowers_of_mem_centralizer h3 hCH hzu hzJ) z.2)

omit [Finite G] in
private theorem mem_sylow_map_of_mem_of_le
    (hTgS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) {c : G}
    (hcS : c ∈ (S : Subgroup G)) (hcH : c ∈ Halpha D hC.alpha) :
    c ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have hP : IsPGroup 2 ((S : Subgroup G).subgroupOf (Halpha D hC.alpha)) :=
    S.isPGroup'.comap_subtype
  have hTP : (T : Subgroup (Halpha D hC.alpha)) ≤
      (S : Subgroup G).subgroupOf (Halpha D hC.alpha) := fun t ht => hTgS ⟨t, ht, rfl⟩
  have hc' : (⟨c, hcH⟩ : Halpha D hC.alpha) ∈ (S : Subgroup G).subgroupOf (Halpha D hC.alpha) :=
    hcS
  rw [T.is_maximal' hP hTP] at hc'
  exact ⟨⟨c, hcH⟩, hc', rfl⟩

private theorem mem_sylow_map_of_mem_sup (hU : DeltaSetup hC T S U)
    (hL : UnitaryCentralizerData hC T S U n L L₀) (hV : IsTranslationSubgroup hC S U Y V n)
    {x : G} (hx : x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V)
    (hxu : Commute x hC.d) :
    x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have hVN : V ≤ Subgroup.normalizer ((S : Set G) ∩ D) :=
    hV.le_sylow.trans (sylow_le_normalizer_inter hC S)
  have hVT : V ≤ Subgroup.normalizer (((T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_of_forall_conj_mem (hL.sylow_normal v (hVN hv))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVT] at hx
  obtain ⟨t, ht, v, hv, rfl⟩ := Set.mem_mul.mp hx
  have htu : Commute t hC.d :=
    (Subgroup.mem_centralizer_iff.mp (sylow_map_le_centralizer hL ht) _ (d_mem_inter hU)).symm
  have hvu : Commute v hC.d := by
    have h1 := htu.inv_left.mul_left hxu
    rwa [inv_mul_cancel_left] at h1
  have hvB : v ∈ Subgroup.centralizer ((S : Set G) ∩ D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro δ hδ
    rw [hU.sylow_inter] at hδ
    obtain ⟨z, hz, rfl⟩ := hδ
    exact ((hvu.mul_right (commute_of_mem_of_isElementaryAbelian hV.isElementaryAbelian hv
      (hV.le hz))).symm)
  have hvU : v ∈ U := by
    rw [← hV.inf_centralizer]
    exact ⟨hv, hvB⟩
  exact Subgroup.mul_mem _ ht (hU.le_sylow_map hvU)

omit [Finite G] in
private theorem card_sup_mul_card_inf_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : φ.range = A ⊔ B := by
    simp only [φ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : G), k.1.1.2, ?_⟩
        invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, B.inv_mem x.2.2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have h1 : (k.1.1 : G) * (k.1.2 : G) = 1 := by simpa [φ] using hk
      rw [eq_inv_of_mul_eq_one_left h1]
      exact B.inv_mem k.1.2.2
    · simp [φ]
    · rintro ⟨⟨a, b⟩, hk⟩
      rw [MonoidHom.mem_ker] at hk
      have h1 : (a : G) * (b : G) = 1 := by simpa [φ] using hk
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [eq_inv_of_mul_eq_one_left h1]
    · intro x
      rfl
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker] at h
  rw [mul_comm, h, Nat.card_prod]

omit [Finite G] in
private theorem component_le_centralizer (hU : DeltaSetup hC T S U)
    (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) : Y ≤ Subgroup.centralizer (L : Set G) := by
  have hu : hC.d ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D :=
    ⟨Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hL.le_centralizer hl) _ (d_mem_inter hU)).symm, hC.hd⟩
  rw [hY, Subgroup.closure_le]
  intro c hc
  rw [hΓ] at hc
  exact (mem_of_reach (fun _ _ y hy _ => hy) hu hc).1

omit [Finite G] in
private theorem commutator_self_le (Y : Subgroup G) : ⁅Y, Y⁆ ≤ Y :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)

theorem commutator_mem_omega (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    ∀ v ∈ V, ∀ r ∈ R, v * r * v⁻¹ * r⁻¹ ∈ U := by
  subst hR
  intro v hv r hr
  by_contra hvr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfacts := DeltaSetup.sylow_inter_pResidualOf_facts_of_psu3 hH h3 hU hCH eH hUn
    (R := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) rfl
  have hTgB := sylow_map_le_centralizer hL
  have hVN : V ≤ Subgroup.normalizer ((S : Set G) ∩ D) :=
    hV.le_sylow.trans (sylow_le_normalizer_inter hC S)
  have hBN := Subgroup.centralizer_le_normalizer ((S : Set G) ∩ D)
  have hRU : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), ∀ z ∈ U, Commute x z :=
    fun x hx z hz => commute_of_mem_centralizer hU (hTgB hx.1) hz
  have hU2 : ∀ z ∈ U, z * z = 1 := fun z hz => by
    have := hU.isElementaryAbelian
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian z hz
  have hv2 : v * v = 1 := by
    have := hV.isElementaryAbelian
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvU : ∀ z ∈ U, Commute v z := fun z hz =>
    commute_of_mem_of_isElementaryAbelian hV.isElementaryAbelian hv (hV.le hz)
  have hvl : ∀ l ∈ L, Commute v l := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (component_le_centralizer hU hL hΓ hY
      (commutator_self_le Y (hV.le_commutator hv))) l hl).symm
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL.ne_bot
  have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
  set s := r⁻¹ * (v * r * v⁻¹) with hsdef
  have hs : s ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hr) (hL.sylow_inter_normal v (hVN hv) r hr)
  have hvr' : v * r * v⁻¹ = r * s := by
    rw [hsdef]
    group
  have hsU : s ∉ U := by
    intro hsU
    apply hvr
    rw [hvr', (hRU r hr s hsU).eq, mul_inv_cancel_right]
    exact hsU
  have hvs : v * s * v⁻¹ = s⁻¹ := by
    rw [hsdef, hvinv]
    calc v * (r⁻¹ * (v * r * v)) * v = v * r⁻¹ * v * r * (v * v) := by group
      _ = v * r⁻¹ * v * r := by rw [hv2, mul_one]
      _ = (r⁻¹ * (v * r * v))⁻¹ := by
        rw [show (r⁻¹ * (v * r * v))⁻¹ = v⁻¹ * r⁻¹ * v⁻¹ * r by group, hvinv]
  have hvw : v * (l * s * l⁻¹) * v⁻¹ = (l * s * l⁻¹)⁻¹ := by
    calc v * (l * s * l⁻¹) * v⁻¹ = (v * l) * s * (v * l)⁻¹ := by group
      _ = (l * v) * s * (l * v)⁻¹ := by rw [(hvl l hl).eq]
      _ = l * (v * s * v⁻¹) * l⁻¹ := by group
      _ = l * s⁻¹ * l⁻¹ := by rw [hvs]
      _ = (l * s * l⁻¹)⁻¹ := by group
  set w := l * s * l⁻¹ with hwdef
  have hw : w ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :=
    hL.sylow_inter_normal l (hBN (hL.le_centralizer hl)) s hs
  have hc₁ := hfacts.2.2.1 r hr w hw
  have hc₂ := hfacts.2.2.1 s hs w⁻¹ (Subgroup.inv_mem _ hw)
  rw [inv_inv] at hc₂
  have hE1 : r * s * w⁻¹ * (r * s)⁻¹ * w = r * w * r⁻¹ * w⁻¹ := by
    have h1 : v * (r * w * r⁻¹ * w⁻¹) * v⁻¹ = r * w * r⁻¹ * w⁻¹ := by
      rw [(hvU _ hc₁).eq, mul_inv_cancel_right]
    rw [← h1]
    calc r * s * w⁻¹ * (r * s)⁻¹ * w =
        (v * r * v⁻¹) * (v * w * v⁻¹) * (v * r * v⁻¹)⁻¹ * (v * w * v⁻¹)⁻¹ := by
          rw [hvr', hvw, inv_inv]
      _ = v * (r * w * r⁻¹ * w⁻¹) * v⁻¹ := by group
  have hE2 : (s * w⁻¹ * s⁻¹ * w) * (r * w⁻¹ * r⁻¹ * w) = r * w * r⁻¹ * w⁻¹ := by
    rw [← hE1]
    calc (s * w⁻¹ * s⁻¹ * w) * (r * w⁻¹ * r⁻¹ * w) =
        ((s * w⁻¹ * s⁻¹ * w) * r) * (w⁻¹ * r⁻¹ * w) := by group
      _ = (r * (s * w⁻¹ * s⁻¹ * w)) * (w⁻¹ * r⁻¹ * w) := by rw [← (hRU r hr _ hc₂).eq]
      _ = r * s * w⁻¹ * (r * s)⁻¹ * w := by group
  have hE3 : r * w⁻¹ * r⁻¹ * w = (r * w * r⁻¹ * w⁻¹)⁻¹ := by
    calc r * w⁻¹ * r⁻¹ * w = w⁻¹ * ((r * w * r⁻¹ * w⁻¹)⁻¹ * w) := by group
      _ = w⁻¹ * (w * (r * w * r⁻¹ * w⁻¹)⁻¹) := by rw [← (hRU w hw _ hc₁).inv_right.eq]
      _ = (r * w * r⁻¹ * w⁻¹)⁻¹ := by group
  have hc₂1 : s * w⁻¹ * s⁻¹ * w = 1 := by
    rw [hE3] at hE2
    calc s * w⁻¹ * s⁻¹ * w =
        ((s * w⁻¹ * s⁻¹ * w) * (r * w * r⁻¹ * w⁻¹)⁻¹) * (r * w * r⁻¹ * w⁻¹) := by group
      _ = (r * w * r⁻¹ * w⁻¹) * (r * w * r⁻¹ * w⁻¹) := by rw [hE2]
      _ = 1 := hU2 _ hc₁
  apply not_commute_conj_of_psu3 hH h3 hU hCH eH hUn hL.odd_card hL.le_centralizer hl hl1' hs hsU
  have h1 : s * w⁻¹ = w⁻¹ * s := by
    calc s * w⁻¹ = (s * w⁻¹ * s⁻¹ * w) * (w⁻¹ * s) := by group
      _ = w⁻¹ * s := by rw [hc₂1, one_mul]
  exact (Commute.inv_right_iff.mp h1).symm

theorem commute_of_mem (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    ∀ v ∈ V, ∀ r ∈ R, Commute v r := by
  subst hR
  have h10a := commutator_mem_omega hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hVL : V ≤ Subgroup.centralizer (L : Set G) :=
    (hV.le_commutator.trans (commutator_self_le Y)).trans
      (component_le_centralizer hU hL hΓ hY)
  have hUL : U ≤ Subgroup.centralizer (L : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (commute_of_mem_centralizer hU (hL.le_centralizer hl) hz).eq
  have h1 : ⁅⁅L, V⁆, (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hVL),
      Subgroup.commutator_bot_left]
  have hVR : ⁅V, (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)⁆ ≤ U :=
    Subgroup.commutator_le.mpr fun v hv r hr => by
      rw [commutatorElement_def]
      exact h10a v hv r hr
  have h2 : ⁅⁅V, (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)⁆, L⁆ = ⊥ := by
    rw [eq_bot_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUL]
    exact Subgroup.commutator_mono hVR le_rfl
  have h3' := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hL.commutator_eq] at h3'
  intro v hv r hr
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3' hr) v hv

theorem card_sup_and_mem (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    Nat.card (R ⊔ V : Subgroup G) = 2 ^ (4 * n) ∧ (∀ x ∈ R ⊔ V, x * x = 1 → x ∈ V) ∧
      hC.d ∉ R ⊔ V := by
  subst hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRV := commute_of_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hfacts := DeltaSetup.sylow_inter_pResidualOf_facts_of_psu3 hH h3 hU hCH eH hUn
    (R := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) rfl
  have hTgB := sylow_map_le_centralizer hL
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hVRn : V ≤ Subgroup.normalizer
      (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_of_forall_conj_mem fun r hr => by
      rw [(hRV v hv r hr).eq, mul_inv_cancel_right]
      exact hr
  refine ⟨?_, fun x hx hx2 => ?_, fun hu => ?_⟩
  ·
    have hinf : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊓ V = U := by
      refine le_antisymm (fun x hx => ?_) (le_inf (le_inf hU.le_sylow_map hU.le_pResidualOf) hV.le)
      rw [← hV.inf_centralizer]
      exact ⟨hx.2, hTgB hx.1.1⟩
    have hcard := card_sup_mul_card_inf_of_commute
      (A := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (B := V)
      (fun a ha b hb => (hRV b hb a ha).eq.symm)
    rw [hinf, hfacts.1, hV.card_eq, hUn,
      show 2 ^ (3 * n) * 2 ^ (2 * n) = 2 ^ (4 * n) * 2 ^ n by rw [← pow_add, ← pow_add]; ring_nf]
      at hcard
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hcard
  ·
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVRn] at hx
    obtain ⟨r, hr, v, hv, rfl⟩ := Set.mem_mul.mp hx
    have hv2 : v * v = 1 := by
      have := hV.isElementaryAbelian
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
    have hr2 : r * r = 1 := by
      calc r * r = r * r * (v * v) := by rw [hv2, mul_one]
        _ = r * (r * v) * v := by group
        _ = r * (v * r) * v := by rw [(hRV v hv r hr).eq]
        _ = (r * v) * (r * v) := by group
        _ = 1 := hx2
    have hrU : r ∈ U := by
      by_cases hr1 : r = 1
      · rw [hr1]
        exact U.one_mem
      · rw [hU.eq_closure]
        exact Subgroup.subset_closure ⟨hr, orderOf_eq_prime (by rw [pow_two, hr2]) hr1⟩
    exact V.mul_mem (hV.le hrU) hv
  ·
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVRn] at hu
    obtain ⟨r, hr, v, hv, hrv⟩ := Set.mem_mul.mp hu
    have huY : hC.d ∈ Y := by
      rw [hY]
      exact Subgroup.subset_closure (inter_subset_component hU hL hΓ (d_mem_inter hU))
    have hrY : r ∈ Y := by
      have e : r = hC.d * v⁻¹ := by rw [← hrv]; group
      rw [e]
      exact Y.mul_mem huY (Y.inv_mem (commutator_self_le Y (hV.le_commutator hv)))
    have hr' := (hL.centralizer_inf r hr.1).mp fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (component_le_centralizer hU hL hΓ hY hrY) l hl).symm
    have hzU : Subgroup.zpowers hC.d ≤ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_forall_conj_mem fun z hz => by
        rw [← (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer z hz), mul_inv_cancel_right]
        exact hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzU] at hr'
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hr'
    rcases eq_one_or_eq_of_mem_zpowers hu2 hy with rfl | rfl
    ·
      apply hV.d_not_mem
      rw [← hrv, ← hyz, one_mul]
      exact V.mul_mem (hV.le hz) hv
    ·
      have huJ : hC.d ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
        have e : hC.d = r * z⁻¹ := by rw [← hyz]; group
        rw [e]
        exact Subgroup.mul_mem _ hr.2 (Subgroup.inv_mem _ (hU.le_pResidualOf hz))
      exact hC.setup.oddT.ne_one hC.hd
        (Subgroup.disjoint_def.mp h3.2.2.2 (Subgroup.mem_zpowers _) huJ)

theorem normal (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    (∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
      (∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ w ∈ R ⊔ V, g * w * g⁻¹ ∈ R ⊔ V) ∧
      (∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
        ∀ w ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V,
          g * w * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V) ∧
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V =
        (CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
          (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype := by
  subst hR
  have hTgB := sylow_map_le_centralizer hL
  have hBN : Subgroup.centralizer ((S : Set G) ∩ D) ≤ Subgroup.normalizer ((S : Set G) ∩ D) :=
    Subgroup.centralizer_le_normalizer _
  have hSN := sylow_le_normalizer_inter hC S
  have hVN : V ≤ Subgroup.normalizer ((S : Set G) ∩ D) := hV.le_sylow.trans hSN
  have hUg : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ z ∈ U, g⁻¹ * z * g ∈ U :=
    fun g hg z hz => by
      simpa using conj_mem_of_mem_normalizer hU (Subgroup.inv_mem _ hg) hz
  have hΔΓ := inter_subset_component hU hL hΓ
  have hNL : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), g ∈ Subgroup.normalizer (L : Set G) →
      ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hgN hgL
    have hYg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
      rw [hY]
      exact conj_mem_closure_of_forall (conj_mem_component hU hL hΓ hgN hgL)
    exact conj_mem_of_forall hV hYg (hUg g hgN)
  have huY : hC.d ∈ Y := by
    rw [hY]
    exact Subgroup.subset_closure (hΔΓ (d_mem_inter hU))
  have huTg := d_mem_sylow_map hC h3 T
  have hu : ∀ v ∈ V, hC.d * v * hC.d⁻¹ ∈ V := by
    refine conj_mem_of_forall hV (fun y hy => Y.mul_mem (Y.mul_mem huY hy) (Y.inv_mem huY)) ?_
    intro z hz
    have hc := commute_of_mem_centralizer hU (hTgB huTg) hz
    rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
    exact hz
  have hRV := commute_of_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hTgV : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.normalizer (V : Set G) := by
    rw [sylow_map_eq_sup hC h3 T]
    refine sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_conj_mem hu)) ?_
    intro r hr
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    rw [← (hRV v hv r hr).eq, mul_inv_cancel_right]
    exact hv
  have hVn : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    obtain ⟨t, ht, htg⟩ := hL.normalizer_eq g hg
    have htN : t * g ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
      Subgroup.mul_mem _ (hBN (hTgB ht)) hg
    have hw := hNL (t * g) htN htg v hv
    have ht' : t⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ (hTgV ht)
    have h1 := (Subgroup.mem_normalizer_iff.mp ht' _).mp hw
    have e : g * v * g⁻¹ = t⁻¹ * (t * g * v * (t * g)⁻¹) * t⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hQn : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      ∀ w ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V,
        g * w * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V :=
    fun g hg => conj_mem_sup_of_forall (hL.sylow_normal g hg) (hVn g hg)
  refine ⟨hVn, fun g hg => conj_mem_sup_of_forall (hL.sylow_inter_normal g hg) (hVn g hg),
    hQn, ?_⟩
  have hXN : Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V ≤
      Subgroup.normalizer ((S : Set G) ∩ D) := sup_le hBN hVN
  have hTgp : IsPGroup 2 ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :=
    T.isPGroup'.map _
  have hVp : IsPGroup 2 V := S.isPGroup'.to_le hV.le_sylow
  have hVTg : V ≤ Subgroup.normalizer
      (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Subgroup G) :
        Set G) := fun v hv => mem_normalizer_of_forall_conj_mem (hL.sylow_normal v (hVN hv))
  have hQp : IsPGroup 2
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V : Subgroup G) :=
    hTgp.to_sup_of_normal_left' hVp hVTg
  apply le_antisymm
  · have hQX : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V ≤
        Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V := sup_le_sup_right hTgB V
    rw [← Subgroup.map_subgroupOf_eq_of_le hQX]
    refine Subgroup.map_mono (le_sSup ⟨⟨fun k hk x => ?_⟩, hQp.comap_subtype⟩)
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hQn x (hXN x.2) k hk
  · intro x hx
    have hP₀X : (CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
        (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype ≤
          Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V := Subgroup.map_subtype_le _
    have hP₀p : IsPGroup 2 ((CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
        (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype) := CFSG.pCore_isPGroup.map _
    have hP₀n : ∀ y ∈ Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V,
        ∀ p ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
          (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype,
        y * p * y⁻¹ ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
          (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype := by
      rintro y hy _ ⟨p, hp, rfl⟩
      exact ⟨⟨y, hy⟩ * p * ⟨y, hy⟩⁻¹, CFSG.pCore_normal.conj_mem p hp ⟨y, hy⟩, rfl⟩
    have hP₀Q : (CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
        (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype ≤ Subgroup.normalizer
          (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V :
            Subgroup G) : Set G) := fun p hp =>
      mem_normalizer_of_forall_conj_mem (hQn p (hXN (hP₀X hp)))
    have hMp := hP₀p.to_sup_of_normal_right' hQp hP₀Q
    have hMn := fun y (hy : y ∈ Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V) =>
      conj_mem_sup_of_forall (hP₀n y hy) (hQn y (hXN hy))
    have hMB := le_of_isPGroup_of_forall_conj_mem (K := ((CFSG.pCore 2
        ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
          (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V)) ⊓
          Subgroup.centralizer ((S : Set G) ∩ D))
      hL.centralizer_eq (fun b hb => hL.sylow_normal b (hBN hb)) hTgp hL.odd_card hL.ne_bot
      hL.le hL.eq_or_eq_sup inf_le_right (hMp.to_le inf_le_left)
      (fun b hb m hm => ⟨hMn b (Subgroup.mem_sup_left hb) m hm.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hm.2) (Subgroup.inv_mem _ hb)⟩)
    have hVB : V ≤ Subgroup.normalizer
        ((Subgroup.centralizer ((S : Set G) ∩ D) : Subgroup G) : Set G) := fun v hv =>
      mem_normalizer_of_forall_conj_mem fun b hb =>
        conj_mem_centralizer_of_mem_normalizer (hVN hv) hb
    have hxX : x ∈ ((Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V : Subgroup G) : Set G) :=
      hP₀X hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVB] at hxX
    obtain ⟨b, hb, v, hv, rfl⟩ := Set.mem_mul.mp hxX
    have hbM : b ∈ ((CFSG.pCore 2 ↥(Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V)).map
        (Subgroup.centralizer ((S : Set G) ∩ D) ⊔ V).subtype ⊔
          ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V)) ⊓
            Subgroup.centralizer ((S : Set G) ∩ D) := by
      refine ⟨?_, hb⟩
      have e : b = b * v * v⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (V.inv_mem hv)))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMB hbM)) (Subgroup.mem_sup_right hv)

theorem sylow_eq_sup (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) :
    (S : Subgroup G) = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn2, -⟩ := DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  have hJB := CFSG.GH74.Uniqueness.Bender.BenderType.unitary n hn2 eJ
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΔ := d_mem_inter hU
  have huS : hC.d ∈ (S : Subgroup G) := huΔ.1
  have huTg := d_mem_sylow_map hC h3 T
  have hTgB := sylow_map_le_centralizer hL
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) := h4.2.1
  have hVN : V ≤ Subgroup.normalizer ((S : Set G) ∩ D) := hV.le_sylow.trans hSN
  have hnorm := normal hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hTgu : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      Commute t hC.d := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hTgB ht) _ huΔ).symm
  have hΔT : ∀ δ ∈ (S : Set G) ∩ D,
      δ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    intro δ hδ
    rw [hU.sylow_inter, ← hU.sylow_map_inter] at hδ
    exact hδ.1
  have hTgS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S := by
    have hp : IsPGroup 2 ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔
        (S : Subgroup G) : Subgroup G) :=
      (T.isPGroup'.map _).to_sup_of_normal_left' S.isPGroup' fun s hs =>
        mem_normalizer_of_forall_conj_mem (hL.sylow_normal s (hSN hs))
    exact le_sup_left.trans (S.is_maximal' hp le_sup_right).le
  have hdecomp : ∀ s ∈ (S : Subgroup G), ∃ v ∈ V, ∃ c ∈ (S : Subgroup G),
      Commute c hC.d ∧ s = v * c := by
    intro s hs
    obtain ⟨v, hv, hvu⟩ := hV.transitive _ huΔ _
      ((Subgroup.mem_set_normalizer_iff.mp (hSN hs) _).mp huΔ)
    refine ⟨v, hv, v⁻¹ * s, (S : Subgroup G).mul_mem
      ((S : Subgroup G).inv_mem (hV.le_sylow hv)) hs, ?_, by group⟩
    have e : s * hC.d = v * hC.d * v⁻¹ * s := by rw [hvu]; group
    show v⁻¹ * s * hC.d = hC.d * (v⁻¹ * s)
    calc v⁻¹ * s * hC.d = v⁻¹ * (s * hC.d) := by group
      _ = v⁻¹ * (v * hC.d * v⁻¹ * s) := by rw [e]
      _ = hC.d * (v⁻¹ * s) := by group
  have hQu : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V,
      Commute x hC.d → x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    fun x hx hxu => mem_sylow_map_of_mem_sup hU hL hV hx hxu
  suffices hmain : ∀ c ∈ (S : Subgroup G), Commute c hC.d →
      c ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype by
    refine le_antisymm (fun s hs => ?_) (sup_le hTgS hV.le_sylow)
    obtain ⟨v, hv, c, hc, hcu, rfl⟩ := hdecomp s hs
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left (hmain c hc hcu))
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  set CS := (S : Subgroup G) ⊓ Subgroup.centralizer ({hC.d} : Set G) with hCS
  have hCSN : CS ≤ Subgroup.normalizer (J : Set G) :=
    inf_le_right.trans (centralizer_d_le_normalizer_pResidualOf h3)
  set ρ : ↥CS →* MulAut ↥J := (CFSG.GH74.Uniqueness.conjAut J).comp (Subgroup.inclusion hCSN)
    with hρ
  have hρapp : ∀ c : ↥CS, ρ c = CFSG.GH74.Uniqueness.conjAut J ⟨c, hCSN c.2⟩ := fun c => rfl
  have hcu : ∀ c : ↥CS, Commute (c : G) hC.d := fun c =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
  have hmemCS : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      x ∈ CS := fun x hx =>
    ⟨hTgS hx, Subgroup.mem_centralizer_singleton_iff.mpr (hTgu x hx).eq⟩
  have huJ : hC.d ∈ Subgroup.centralizer (J : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hl))
  have hρinn : ∀ c : ↥CS,
      ρ c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J → (c : G) ∈
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rintro c ⟨j, hj⟩
    have h1 := CFSG.GH74.Uniqueness.mul_inv_mem_centralizer_of_conjAut_eq J ⟨c, hCSN c.2⟩ j
      ((hρapp c).symm.trans hj.symm)
    have hju : Commute (j : G) hC.d := Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ j.2))
    have h2 := mem_zpowers_of_mem_centralizer h3 hCH ((hcu c).mul_left hju.inv_left) h1
    have hcH : (c : G) ∈ Halpha D hC.alpha := by
      have e : (c : G) = ((c : G) * (j : G)⁻¹) * j := by group
      rw [e]
      exact (Halpha D hC.alpha).mul_mem
        (Subgroup.zpowers_le.mpr (d_mem_Halpha hC h3) h2) (Subgroup.map_subtype_le _ j.2)
    exact mem_sylow_map_of_mem_of_le hTgS (Subgroup.mem_inf.mp c.2).1 hcH
  have hinnρ : ∀ c : ↥CS, (c : G) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype →
        ρ c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J := by
    intro c hc
    rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ hc) with hcJ | hcJ
    · refine ⟨⟨c, hcJ⟩, ((hρapp c).trans (conjAut_eq_conj_of_mul_inv_mem (hCSN c.2) hcJ ?_)).symm⟩
      rw [mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine ⟨⟨hC.d * c, hcJ⟩,
        ((hρapp c).trans (conjAut_eq_conj_of_mul_inv_mem (hCSN c.2) hcJ ?_)).symm⟩
      rw [mul_inv_rev, mul_inv_cancel_left]
      exact Subgroup.inv_mem _ huJ
  have hρone : ∀ c : ↥CS, ρ c = 1 → (c : G) ∈ Subgroup.zpowers hC.d := fun c h =>
    mem_zpowers_of_mem_centralizer h3 hCH (hcu c)
      ((CFSG.GH74.Uniqueness.conjAut_eq_one_iff J _).mp ((hρapp c).symm.trans h))
  set π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J) with hπ
  have hψ1 : ∀ c : ↥CS, π (ρ c) = 1 ↔ (c : G) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := fun c =>
    ⟨fun h => hρinn c ((QuotientGroup.eq_one_iff _).mp h),
      fun h => (QuotientGroup.eq_one_iff _).mpr (hinnρ c h)⟩
  have : Finite (MulAut ↥J) :=
    Finite.of_injective (fun f : MulAut ↥J => (f : ↥J → ↥J)) DFunLike.coe_injective
  have hCSp : IsPGroup 2 ↥CS := S.isPGroup'.to_le inf_le_left
  obtain ⟨PA, hPA⟩ :=
    (hCSp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective).exists_le_sylow
  have hπPA : IsPGroup 2 ((PA : Subgroup (MulAut ↥J)).map π) := PA.isPGroup'.map π
  obtain ⟨Ŝ, hŜ⟩ := hπPA.exists_le_sylow
  have := hJB.isCyclic_sylow_outer Ŝ
  have hcycPA : IsCyclic ((PA : Subgroup (MulAut ↥J)).map π) :=
    isCyclic_of_injective (Subgroup.inclusion hŜ) (Subgroup.inclusion_injective hŜ)
  have hψle : (π.comp ρ).range ≤ (PA : Subgroup (MulAut ↥J)).map π := by
    rintro _ ⟨c, rfl⟩
    exact ⟨ρ c, hPA ⟨c, rfl⟩, rfl⟩
  have hcycψ : IsCyclic (π.comp ρ).range :=
    isCyclic_of_injective (Subgroup.inclusion hψle) (Subgroup.inclusion_injective hψle)
  have hψr1 : ∀ c : ↥CS, (π.comp ρ).rangeRestrict c = 1 ↔ (c : G) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := fun c => by
    rw [← hψ1 c, ← Subtype.coe_inj, MonoidHom.coe_rangeRestrict]
    rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨c₀, hc₀S, hc₀u, hc₀T⟩ := hcon
  set c₀' : ↥CS := ⟨c₀, hc₀S, Subgroup.mem_centralizer_singleton_iff.mpr hc₀u.eq⟩ with hc₀'
  obtain ⟨α₀, hα₀2, hα₀out⟩ := exists_outer_involution_of_benderType hJB
  obtain ⟨γ, -, hγ⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2)
    (le_top : Subgroup.zpowers α₀ ≤ ⊤) (isPGroup_zpowers_of_mul_self hα₀2) le_top PA.isPGroup'
    (by rw [Subgroup.relIndex_top_right]; exact PA.not_dvd_index)
  have hα₁PA : γ⁻¹ * α₀ * γ ∈ PA := hγ α₀ (Subgroup.mem_zpowers α₀)
  have hα₁2 : (γ⁻¹ * α₀ * γ) * (γ⁻¹ * α₀ * γ) = 1 := by
    calc (γ⁻¹ * α₀ * γ) * (γ⁻¹ * α₀ * γ) = γ⁻¹ * (α₀ * α₀) * γ := by group
      _ = 1 := by rw [hα₀2]; group
  have hα₁out : γ⁻¹ * α₀ * γ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J := by
    intro h
    apply hα₀out
    have h1 := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥J).conj_mem _ h γ
    rwa [show γ * (γ⁻¹ * α₀ * γ) * γ⁻¹ = α₀ by group] at h1
  have hmem := mem_zpowers_of_isCyclic (x := (⟨π (γ⁻¹ * α₀ * γ),
      Subgroup.mem_map_of_mem _ hα₁PA⟩ : ↥((PA : Subgroup (MulAut ↥J)).map π)))
    (y := ⟨π (ρ c₀'), Subgroup.mem_map_of_mem _ (hPA ⟨c₀', rfl⟩)⟩)
    (Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, hα₁2, map_one, Subgroup.coe_one]))
    (fun h => hα₁out ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
    (hπPA.to_subgroup _)
    (fun h => hc₀T (hρinn c₀' ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h))))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm' : π (ρ (c₀' ^ m)) = π (γ⁻¹ * α₀ * γ) := by
    have h1 := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_zpow] at h1
    rw [map_zpow, map_zpow, h1]
  have hι : (ρ (c₀' ^ m))⁻¹ * (γ⁻¹ * α₀ * γ) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hm'
    exact QuotientGroup.eq.mp hm'
  have hιPA : (ρ (c₀' ^ m))⁻¹ * (γ⁻¹ * α₀ * γ) ∈ PA :=
    (PA : Subgroup (MulAut ↥J)).mul_mem ((PA : Subgroup (MulAut ↥J)).inv_mem (hPA ⟨_, rfl⟩))
      hα₁PA
  obtain ⟨j, hj⟩ := hι
  obtain ⟨R', hR'⟩ := exists_sylow_pResidualOf T
  have hker : (MulAut.conj : ↥J →* MulAut ↥J).ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [← center_pResidualOf_eq_bot h3 hCH]
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have h1 := congrArg (fun σ : MulAut ↥J => σ g) (MonoidHom.mem_ker.mp hz)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * z = z * g * z⁻¹ * z := by rw [h1]
      _ = z * g := by group
  have hRj : IsPGroup 2
      ((PA : Subgroup (MulAut ↥J)).comap (MulAut.conj : ↥J →* MulAut ↥J)) :=
    PA.isPGroup'.comap_of_ker_isPGroup _ (by rw [hker]; exact IsPGroup.of_bot)
  have hR'le : (R' : Subgroup ↥J) ≤
      (PA : Subgroup (MulAut ↥J)).comap (MulAut.conj : ↥J →* MulAut ↥J) := by
    intro r hr
    have hrT : (r : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        J := by
      rw [← hR']
      exact ⟨r, hr, rfl⟩
    have h1 : ρ ⟨r, hmemCS _ hrT.1⟩ = MulAut.conj r :=
      CFSG.GH74.Uniqueness.conjAut_of_mem J r.2
    show MulAut.conj r ∈ PA
    rw [← h1]
    exact hPA ⟨_, rfl⟩
  have hjR' : j ∈ (R' : Subgroup ↥J) := by
    rw [← R'.is_maximal' hRj hR'le]
    show MulAut.conj j ∈ PA
    rw [hj]
    exact hιPA
  have hjT : (j : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ J := by
    rw [← hR']
    exact ⟨j, hjR', rfl⟩
  set a' : ↥CS := c₀' ^ m * ⟨j, hmemCS _ hjT.1⟩ with ha'
  have hρa : ρ a' = γ⁻¹ * α₀ * γ := by
    rw [ha', map_mul, show ρ ⟨j, hmemCS _ hjT.1⟩ = MulAut.conj j from
      CFSG.GH74.Uniqueness.conjAut_of_mem J j.2, hj]
    group
  have haT : (a' : G) ∉ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    fun h => hα₁out (hρa ▸ hinnρ a' h)
  have ha2 : (a' : G) * a' ∈ Subgroup.zpowers hC.d := by
    have h1 : ρ (a' * a') = 1 := by rw [map_mul, hρa, hα₁2]
    exact hρone (a' * a') h1
  obtain ⟨b, hbCS, hbT, hb2, hbK⟩ : ∃ b : G, b ∈ CS ∧
      b ∉ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
      b * b ∈ Subgroup.zpowers hC.d ∧ b ∈ commutator G := by
    by_cases haK : (a' : G) ∈ commutator G
    · exact ⟨a', a'.2, haT, ha2, haK⟩
    · have huCS : hC.d ∈ CS := ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      refine ⟨(a' : G) * hC.d, CS.mul_mem a'.2 huCS, fun h => haT ?_, ?_, ?_⟩
      · have e : (a' : G) = ((a' : G) * hC.d) * hC.d⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ huTg)
      · have e : ((a' : G) * hC.d) * ((a' : G) * hC.d) = (a' : G) * a' := by
          calc ((a' : G) * hC.d) * ((a' : G) * hC.d) = a' * (hC.d * a') * hC.d := by group
            _ = a' * (a' * hC.d) * hC.d := by rw [(hcu a').eq]
            _ = a' * a' * (hC.d * hC.d) := by group
            _ = a' * a' := by rw [hu2, mul_one]
        rw [e]
        exact ha2
      · have huK : hC.d ∉ commutator G := by
          intro huK
          apply haK
          have hDK : D ⊆ commutator G :=
            (hC.setup.subset_or_disjoint (commutator G)).resolve_right fun h => h _ hC.hd huK
          rw [hC.setup.eq_top_of_subset _ hDK]
          exact Subgroup.mem_top _
        have hidx : (commutator G).index = 2 := by
          have h1 := hC.setup.index_commutator_le_two
          have h2 : (commutator G).index ≠ 1 := fun h =>
            haK (by rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _)
          have h3 : (commutator G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
          omega
        exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false haK huK)
  have hbS : b ∈ (S : Subgroup G) := (Subgroup.mem_inf.mp hbCS).1
  have hbu : Commute b hC.d := Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.mem_inf.mp hbCS).2
  have hbQ : b ∉ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V :=
    fun h => hbT (hQu b h hbu)
  have hzS : ∀ g z : G, z ∈ Subgroup.zpowers hC.d → g⁻¹ * z * g ∈ (S : Subgroup G) →
      g⁻¹ * z * g ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V := by
    intro g z hz hzS'
    rcases eq_one_or_eq_of_mem_zpowers hu2 hz with rfl | rfl
    · rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left
        (hΔT _ ⟨hzS', by simpa using hC.setup.conj_mem g⁻¹ hC.hd⟩)
  obtain ⟨ĝ, hĝ⟩ := hcycψ.exists_generator
  obtain ⟨c₁, hc₁⟩ := (π.comp ρ).rangeRestrict_surjective ĝ
  have hcycS : ∃ x ∈ (S : Subgroup G), ∀ t ∈ (S : Subgroup G), ∃ k : ℤ,
      (x ^ k)⁻¹ * t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V := by
    refine ⟨c₁, (Subgroup.mem_inf.mp c₁.2).1, fun t ht => ?_⟩
    obtain ⟨v, hv, c, hc, hcu', rfl⟩ := hdecomp t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hĝ ((π.comp ρ).rangeRestrict ⟨c, hc, Subgroup.mem_centralizer_singleton_iff.mpr hcu'.eq⟩))
    have h1 := (hψr1 ((c₁ ^ k)⁻¹ * ⟨c, hc, Subgroup.mem_centralizer_singleton_iff.mpr hcu'.eq⟩)).mp
      (by rw [map_mul, map_inv, map_zpow, hc₁, hk, inv_mul_cancel])
    refine ⟨k, ?_⟩
    have hk' : ((c₁ : G) ^ k)⁻¹ ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
      hSN ((S : Subgroup G).inv_mem ((S : Subgroup G).zpow_mem (Subgroup.mem_inf.mp c₁.2).1 k))
    have e : ((c₁ : G) ^ k)⁻¹ * (v * c) =
        (((c₁ : G) ^ k)⁻¹ * v * ((c₁ : G) ^ k)⁻¹⁻¹) * (((c₁ : G) ^ k)⁻¹ * c) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (hnorm.1 _ hk' v hv))
      (Subgroup.mem_sup_left ?_)
    simpa using h1
  have hcosets : ∀ z ∈ (S : Subgroup G), z * z ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V →
      z ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V ∨
        b⁻¹ * z ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V := by
    intro z hz hz2
    obtain ⟨v, hv, c, hc, hcu', rfl⟩ := hdecomp z hz
    have hcv : c * v * c⁻¹ ∈ V := hnorm.1 c (hSN hc) v hv
    have hcc : c * c ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ V := by
      have e : c * c = (c * v * c⁻¹)⁻¹ * v⁻¹ * ((v * c) * (v * c)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (V.inv_mem hcv))
        (Subgroup.mem_sup_right (V.inv_mem hv))) hz2
    have hcT := hQu _ hcc (hcu'.mul_left hcu')
    set c' : ↥CS := ⟨c, hc, Subgroup.mem_centralizer_singleton_iff.mpr hcu'.eq⟩ with hc'
    set b' : ↥CS := ⟨b, hbCS⟩ with hb'
    rcases eq_one_or_eq_of_isCyclic (x := (π.comp ρ).rangeRestrict b')
        (y := (π.comp ρ).rangeRestrict c')
        (by rw [← map_mul, hψr1]; exact Subgroup.zpowers_le.mpr huTg hb2)
        (fun h => hbT ((hψr1 b').mp h))
        (by rw [← map_mul, hψr1]; exact hcT) with h | h
    · left
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left ((hψr1 c').mp h))
    · right
      have h1 := (hψr1 (b'⁻¹ * c')).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
      have hbv : b⁻¹ * v * b⁻¹⁻¹ ∈ V := hnorm.1 _ (hSN ((S : Subgroup G).inv_mem hbS)) v hv
      have e : b⁻¹ * (v * c) = (b⁻¹ * v * b⁻¹⁻¹) * (b⁻¹ * c) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hbv)
        (Subgroup.mem_sup_left (by simpa using h1))
  obtain ⟨N, hN, hcycN, -, hbN⟩ | ⟨g, hgQ, -, hgC⟩ :=
    CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) S.isPGroup' S.not_dvd_index
      (fun t ht q hq => hnorm.2.2.1 t (hSN ht) q hq) hcycS hbS hbQ
      (fun g k hgk => hzS g _ (by rw [pow_mul, pow_two]; exact Subgroup.pow_mem _ hb2 k) hgk)
      (fun g hg _ => hcosets _ hg (by
        rw [show g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g by group]
        refine hzS g _ hb2 ?_
        rw [show g⁻¹ * (b * b) * g = g⁻¹ * b * g * (g⁻¹ * b * g) by group]
        exact (S : Subgroup G).mul_mem hg hg))
  ·
    have := hN
    exact hbN (commutator_le_of_isCyclic hcycN hbK)
  have hug := hgC hC.d ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr hbu.eq.symm⟩
  have hugΔ : g⁻¹ * hC.d * g ∈ (S : Set G) ∩ D :=
    ⟨hug.1, by simpa using hC.setup.conj_mem g⁻¹ hC.hd⟩
  obtain ⟨v, hv, hvu⟩ := hV.transitive _ hugΔ _ huΔ
  have hz₁T : (g * v⁻¹)⁻¹ * b * (g * v⁻¹) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    have e : (g * v⁻¹)⁻¹ * b * (g * v⁻¹) = v * (g⁻¹ * b * g) * v⁻¹ := by group
    rw [e]
    refine hQu _ (hnorm.2.2.1 v (hVN hv) _ hgQ) ?_
    have hc1 : Commute (g⁻¹ * b * g) (g⁻¹ * hC.d * g) :=
      (Subgroup.mem_centralizer_singleton_iff.mp hug.2).symm
    have hc2 := (Commute.conj_iff v).mpr hc1
    rwa [hvu] at hc2
  set h := g * v⁻¹ with hh
  have hbz : b = h * (h⁻¹ * b * h) * h⁻¹ := by group
  have hbD : h⁻¹ * b * h ∈ D → False := fun hD =>
    hbT (hΔT _ ⟨hbS, by rw [hbz]; exact hC.setup.conj_mem h hD⟩)
  have hfacts := DeltaSetup.sylow_inter_pResidualOf_facts_of_psu3 hH h3 hU hCH eH hUn
    (R := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ J) rfl
  obtain ⟨r, hrR, hr⟩ : ∃ r ∈ (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ⊓ J, h⁻¹ * b * h = r ∨ h⁻¹ * b * h = hC.d * r := by
    rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ hz₁T) with hJ' | hJ'
    · exact ⟨_, ⟨hz₁T, hJ'⟩, Or.inl rfl⟩
    · refine ⟨_, ⟨Subgroup.mul_mem _ huTg hz₁T, hJ'⟩, Or.inr ?_⟩
      rw [← mul_assoc hC.d hC.d, hu2, one_mul]
  have hru : Commute r hC.d := hTgu r hrR.1
  have hzr : (h⁻¹ * b * h) * (h⁻¹ * b * h) = r * r := by
    rcases hr with hr | hr
    · rw [hr]
    · rw [hr]
      calc hC.d * r * (hC.d * r) = hC.d * (r * hC.d) * r := by group
        _ = hC.d * (hC.d * r) * r := by rw [hru.eq]
        _ = (hC.d * hC.d) * (r * r) := by group
        _ = r * r := by rw [hu2, one_mul]
  have hz₁sq : (h⁻¹ * b * h) * (h⁻¹ * b * h) = h⁻¹ * (b * b) * h := by group
  rcases eq_one_or_eq_of_mem_zpowers hu2 hb2 with hb1 | hbu2
  ·
    have hrr : r * r = 1 := by rw [← hzr, hz₁sq, hb1, mul_one, inv_mul_cancel]
    by_cases hr1 : r = 1
    · rcases hr with hr | hr
      · apply hbT
        rw [hbz, hr, hr1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · exact hbD (by rw [hr, hr1, mul_one]; exact hC.hd)
    · have hrU : r ∈ U := by
        rw [hU.eq_closure]
        exact Subgroup.subset_closure ⟨hrR, orderOf_eq_prime (by rw [pow_two, hrr]) hr1⟩
      rcases hr with hr | hr
      ·
        have hde : h * hC.d * h⁻¹ * (h * (hC.d * r) * h⁻¹) = b := by
          rw [hbz, hr]
          calc h * hC.d * h⁻¹ * (h * (hC.d * r) * h⁻¹) = h * (hC.d * hC.d * r) * h⁻¹ := by group
            _ = h * r * h⁻¹ := by rw [hu2, one_mul]
        have hne : h * hC.d * h⁻¹ ≠ h * (hC.d * r) * h⁻¹ := fun he => hr1 (by
          have h1 : hC.d = hC.d * r := by
            have := congrArg (fun x => h⁻¹ * x * h) he
            simpa [mul_assoc] using this
          have h2 := congrArg (fun x => hC.d⁻¹ * x) h1
          simpa using h2.symm)
        have hcomm : Commute (h * hC.d * h⁻¹) (h * (hC.d * r) * h⁻¹) :=
          (Commute.conj_iff h).mpr ((Commute.refl _).mul_right hru.symm)
        have hbU := DeltaSetup.mul_mem_omega_of_center hH h3 hU hL.center_eq
          (hC.setup.conj_mem h hC.hd) (hC.setup.conj_mem h (mul_mem_inter hU hrU).2) hne hcomm
          (by rw [hde]; exact hSN hbS) huΔ (by rw [hde]; exact hbu)
        rw [hde] at hbU
        exact hbT (hU.le_sylow_map hbU)
      · exact hbD (by rw [hr]; exact (mul_mem_inter hU hrU).2)
  ·
    have hD : r * r ∈ D := by
      rw [← hzr, hz₁sq, hbu2]
      simpa using hC.setup.conj_mem h⁻¹ hC.hd
    exact not_mem_pResidualOf_of_mem hH h3 hD (hU.le_pResidualOf (hfacts.2.1 r hrR))

theorem inter_commutator_eq (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (hV : IsTranslationSubgroup hC S U Y V n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    (S : Subgroup G) ⊓ commutator G = R ⊔ V ∧ hC.d ∉ commutator G := by
  subst hR
  have hSeq := sylow_eq_sup hH h3 h4 hU hCH eH hUn hL hΓ hY hV
  have hnorm := normal hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hcard := card_sup_and_mem hH h3 hU hCH eH hUn hL hΓ hY hV rfl
  have hSN := sylow_le_normalizer_inter hC S
  have hTgS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S := by
    rw [hSeq]
    exact le_sup_left
  have hWS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V ≤ S :=
    sup_le (inf_le_left.trans hTgS) hV.le_sylow
  have huS : hC.d ∈ (S : Subgroup G) := (d_mem_inter hU).1
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hWK : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V ≤ commutator G := by
    refine sup_le ?_ (hV.le_commutator.trans (Subgroup.commutator_mono le_top le_top))
    rw [← hL.commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hgen : ∀ t ∈ (S : Subgroup G),
      t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V ∨
      hC.d⁻¹ * t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V := by
    intro t ht
    have hS' : (S : Subgroup G) = Subgroup.zpowers hC.d ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V) := by
      have h := sylow_map_eq_sup hC h3 T
      calc (S : Subgroup G) = (T : Subgroup (Halpha D hC.alpha)).map
            (Halpha D hC.alpha).subtype ⊔ V := hSeq
        _ = Subgroup.zpowers hC.d ⊔ ((T : Subgroup (Halpha D hC.alpha)).map
            (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ⊔
              V := by rw [← h]
        _ = _ := sup_assoc _ _ _
    have hzW : Subgroup.zpowers hC.d ≤ Subgroup.normalizer
        (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_forall_conj_mem (hnorm.2.1 _ (hSN huS))
    have ht' : t ∈ ((Subgroup.zpowers hC.d ⊔
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V) : Subgroup G) : Set G) := by
      rw [← hS']
      exact ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzW] at ht'
    obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.mp ht'
    rcases eq_one_or_eq_of_mem_zpowers hu2 hy with rfl | rfl
    · left
      simpa using hw
    · right
      simpa using hw
  have hconj : ∀ g : G, g⁻¹ * hC.d * g ∈ (S : Subgroup G) →
      hC.d⁻¹ * (g⁻¹ * hC.d * g) ∈ (T : Subgroup (Halpha D hC.alpha)).map
        (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ⊔ V := by
    intro g hg
    have hmem : g⁻¹ * hC.d * g ∈ (S : Set G) ∩ D :=
      ⟨hg, by simpa using hC.setup.conj_mem g⁻¹ hC.hd⟩
    rw [hU.sylow_inter] at hmem
    obtain ⟨z, hz, hze : hC.d * z = g⁻¹ * hC.d * g⟩ := hmem
    rw [← hze, inv_mul_cancel_left]
    exact Subgroup.mem_sup_right (hV.le hz)
  have hnot : hC.d ∉ commutator G :=
    not_mem_commutator_of_forall S.isPGroup' S.not_dvd_index hWS
      (fun t ht => hnorm.2.1 t (hSN ht)) huS hcard.2.2 hu2 hgen hconj
  refine ⟨le_antisymm ?_ (le_inf hWS hWK), hnot⟩
  rintro x ⟨hxS, hxK⟩
  rcases hgen x hxS with hx | hx
  · exact hx
  · exfalso
    apply hnot
    have e : hC.d = x * (hC.d⁻¹ * x)⁻¹ := by group
    rw [e]
    exact (commutator G).mul_mem hxK ((commutator G).inv_mem (hWK hx))

end IsTranslationSubgroup

end Chain

end CFSG.OddTranspositions.PartThree.Nine
