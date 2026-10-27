module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement

private theorem k89qr_elemAbelian_card {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {D E : Subgroup G} (hED : E ≤ D) (hE : IsElemAbelian q E)
    (hrank : CFSG.Open.pRank (G := G) q D ≤ 2) :
    ∃ k, Nat.card E = q ^ k ∧ k ≤ 2 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q) (G := E)).mp hE.isPGroup
  refine ⟨k, hk, ?_⟩
  have h1 : k ≤ CFSG.Open.pRank (G := G) q E :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hE hk
  have h2 : CFSG.Open.pRank (G := G) q E ≤ CFSG.Open.pRank (G := G) q D :=
    CFSG.SectionRank.pRank_mono hq.one_lt hED
  omega

private theorem k89qr_elemAbelian_le {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {D E : Subgroup G} (hED : E ≤ D) (hE : IsElemAbelian q E)
    (hrank : CFSG.Open.pRank (G := G) q D ≤ 2) :
    Nat.card E ≤ q ^ 2 := by
  obtain ⟨k, hk, hk2⟩ := k89qr_elemAbelian_card hq hED hE hrank
  rw [hk]
  exact (Nat.pow_le_pow_iff_right hq.one_lt).mpr hk2

private theorem k89qr_closure_union_elemAbelian {G : Type*} [Group G] {q : ℕ}
    {Z : Subgroup G} (hZea : IsElemAbelian q Z) {t : Set G}
    (htZ : ∀ a ∈ t, ∀ b ∈ Z, a * b = b * a)
    (htt : ∀ a ∈ t, ∀ b ∈ t, a * b = b * a)
    (htq : ∀ a ∈ t, a ^ q = 1) :
    IsElemAbelian q (Subgroup.closure (t ∪ (Z : Set G))) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · exact htt a ha b hb
    · exact htZ a ha b hb
    · exact (htZ b hb a ha).symm
    · exact hZea.comm ha hb
  · rintro a (ha | ha)
    · exact htq a ha
    · exact hZea.2 a ha

private theorem k89qr_center_elemAbelian {G : Type*} [Group G] {q : ℕ} {D : Subgroup G}
    (hpow : ∀ x ∈ D, x ^ q = 1) :
    IsElemAbelian q ((Subgroup.center D).map D.subtype) := by
  have hZeq := CFSG.center_map_subtype_eq_inf_centralizer D
  have hZleD : (Subgroup.center D).map D.subtype ≤ D := by
    rw [hZeq]; exact inf_le_left
  have hZc : (Subgroup.center D).map D.subtype ≤ Subgroup.centralizer (D : Set G) := by
    rw [hZeq]; exact inf_le_right
  refine ⟨IsMulCommutative.of_comm ?_, fun x hx => hpow x (hZleD hx)⟩
  intro a b
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hZc a.2) (b : G) (hZleD b.2)).symm

theorem s889_qrank : S889QRank := by
  intro G _ _ q hq hq2 D hpow hclass hrank
  classical
  set D' : Subgroup G := ⁅D, D⁆ with hD'def
  set Z : Subgroup G := (Subgroup.center D).map D.subtype with hZdef
  have hD'leD : D' ≤ D := by
    rw [hD'def]
    exact Subgroup.commutator_le_of_le le_rfl le_rfl
  have hZeq : Z = D ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hZdef]
    exact CFSG.center_map_subtype_eq_inf_centralizer D
  have hZleD : Z ≤ D := by rw [hZeq]; exact inf_le_left
  have hZc : Z ≤ Subgroup.centralizer (D : Set G) := by rw [hZeq]; exact inf_le_right
  have hZea : IsElemAbelian q Z := k89qr_center_elemAbelian hpow
  have hD'leZ : D' ≤ Z := by
    have h1 : D' ≤ Subgroup.centralizer (D : Set G) := by
      have h2 : ⁅D', D⁆ = ⊥ := by rw [hD'def]; exact hclass
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h2
    rw [hZeq]
    exact le_inf hD'leD h1
  have hmain : Nat.card D ≤ Nat.card D' * q ^ 2 := by
    by_cases hD'bot : D' = ⊥
    · have hDab : IsElemAbelian q D := by
        refine ⟨?_, hpow⟩
        exact (Subgroup.commutator_self_eq_bot_iff).mp (by rw [← hD'def]; exact hD'bot)
      have hcardD : Nat.card D ≤ q ^ 2 := k89qr_elemAbelian_le hq le_rfl hDab hrank
      have hD'card : Nat.card D' = 1 := by rw [hD'bot, Subgroup.card_bot]
      calc Nat.card D ≤ q ^ 2 := hcardD
        _ = Nat.card D' * q ^ 2 := by rw [hD'card, one_mul]
    · have hZne : Z ≠ ⊥ := by
        intro hZbot
        exact hD'bot (le_bot_iff.mp (hZbot ▸ hD'leZ))
      have : Fact q.Prime := ⟨hq⟩
      have hZpg : IsPGroup q Z := hZea.isPGroup
      obtain ⟨s, hs⟩ := (IsPGroup.iff_card (p := q) (G := Z)).mp hZpg
      have hZcard_le : Nat.card Z ≤ q ^ 2 := k89qr_elemAbelian_le hq hZleD hZea hrank
      have hs_le : s ≤ 2 :=
        (Nat.pow_le_pow_iff_right hq.one_lt).mp (by rw [← hs]; exact hZcard_le)
      have hs_ge : 1 ≤ s := by
        by_contra h
        have hs0 : s = 0 := by omega
        have h1 : Nat.card Z = 1 := by rw [hs, hs0, pow_zero]
        exact (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZne |>.ne' h1
      have hs_cases : s = 1 ∨ s = 2 := by omega
      rcases hs_cases with hs1 | hs2
      · have hZcard : Nat.card Z = q := by rw [hs, hs1, pow_one]
        have hD'card : Nat.card D' = q := by
          have hdiv : Nat.card D' ∣ q := by
            have h1 : Nat.card (D'.subgroupOf Z) ∣ Nat.card Z :=
              Subgroup.card_subgroup_dvd_card (D'.subgroupOf Z)
            rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'leZ).toEquiv, hZcard] at h1
          have hgt : 1 < Nat.card D' := (Subgroup.one_lt_card_iff_ne_bot D').mpr hD'bot
          rcases (Nat.dvd_prime hq).mp hdiv with h1 | h1
          · omega
          · exact h1
        have hnotDleZ : ¬ D ≤ Z := by
          intro hDZ
          apply hD'bot
          have hDab : IsMulCommutative D :=
            IsMulCommutative.of_comm fun a b =>
              Subtype.ext (hZea.comm (hDZ a.2) (hDZ b.2))
          rw [hD'def]
          exact (Subgroup.commutator_self_eq_bot_iff (H := D)).mpr hDab
        obtain ⟨x, hxD, hxZ⟩ := Set.not_subset.mp hnotDleZ
        let φ : ↥D →* G := {
          toFun := fun y => ⁅x, (y : G)⁆
          map_one' := by simp [commutatorElement_one_right]
          map_mul' := fun a b => by
            have hmem : ⁅x, (b : G)⁆ ∈ Z :=
              hD'leZ (Subgroup.commutator_mem_commutator hxD b.2)
            have hcomm : (a : G) * ⁅x, (b : G)⁆ = ⁅x, (b : G)⁆ * (a : G) :=
              Subgroup.mem_centralizer_iff.mp (hZc hmem) (a : G) a.2
            have hconj : (a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹ = ⁅x, (b : G)⁆ := by
              rw [hcomm]; group
            calc ⁅x, ((a * b : ↥D) : G)⁆
                = ⁅x, (a : G) * (b : G)⁆ := rfl
              _ = ⁅x, (a : G)⁆ * (a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹ :=
                    commutatorElement_mul_right_eq_mul_conj _ _ _
              _ = ⁅x, (a : G)⁆ * ((a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹) := by group
              _ = ⁅x, (a : G)⁆ * ⁅x, (b : G)⁆ := by rw [hconj] }
        have hrangeZ : φ.range ≤ Z := by
          rintro z ⟨y, rfl⟩
          exact hD'leZ (Subgroup.commutator_mem_commutator hxD y.2)
        have hrange_ne : φ.range ≠ ⊥ := by
          intro hbot
          apply hxZ
          rw [hZeq]
          refine ⟨hxD, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
          have hy1 : φ ⟨y, hy⟩ = 1 := by
            have hmem : φ ⟨y, hy⟩ ∈ φ.range := ⟨⟨y, hy⟩, rfl⟩
            rw [hbot] at hmem
            simpa using hmem
          exact (commutatorElement_eq_one_iff_mul_comm.mp hy1).symm
        have hrange_card : Nat.card φ.range = q := by
          have hdiv : Nat.card φ.range ∣ q := by
            have h1 : Nat.card (φ.range.subgroupOf Z) ∣ Nat.card Z :=
              Subgroup.card_subgroup_dvd_card (φ.range.subgroupOf Z)
            rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrangeZ).toEquiv, hZcard] at h1
          have hgt : 1 < Nat.card φ.range :=
            (Subgroup.one_lt_card_iff_ne_bot φ.range).mpr hrange_ne
          rcases (Nat.dvd_prime hq).mp hdiv with h1 | h1
          · omega
          · exact h1
        have hker_index : φ.ker.index = q := by rw [Subgroup.index_ker φ, hrange_card]
        let E : Subgroup G := Subgroup.closure ({x} ∪ (Z : Set G))
        have hEea : IsElemAbelian q E := by
          dsimp only [E]
          refine k89qr_closure_union_elemAbelian hZea ?_ ?_ ?_
          · rintro a ha b hb
            rw [Set.mem_singleton_iff] at ha
            rw [ha]
            exact Subgroup.mem_centralizer_iff.mp (hZc hb) x hxD
          · rintro a ha b hb
            rw [Set.mem_singleton_iff] at ha hb
            rw [ha, hb]
          · rintro a ha
            rw [Set.mem_singleton_iff] at ha
            rw [ha]
            exact hpow x hxD
        have hEleD : E ≤ D := by
          dsimp only [E]
          refine (Subgroup.closure_le _).mpr ?_
          rintro a (ha | ha)
          · rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hxD
          · exact hZleD ha
        have hZleE : Z ≤ E := by
          dsimp only [E]
          intro z hz
          exact Subgroup.subset_closure (Or.inr hz)
        have hxE : x ∈ E := by
          dsimp only [E]
          exact Subgroup.subset_closure (Or.inl (by simp))
        have hZneE : Z ≠ E := by
          intro heq
          exact hxZ (heq.symm ▸ hxE)
        have hEcard : Nat.card E = q ^ 2 := by
          obtain ⟨k, hkE, _hkE2⟩ := k89qr_elemAbelian_card hq hEleD hEea hrank
          have hEgt : q < Nat.card E := by
            have hle : Nat.card Z ≤ Nat.card E := Subgroup.card_le_of_le hZleE
            have hne : Nat.card Z ≠ Nat.card E := by
              intro heq
              exact hZneE (Subgroup.eq_of_le_of_card_ge hZleE (le_of_eq heq.symm))
            omega
          have hkE_eq : k = 2 := by
            have hkE_ge : 2 ≤ k := by
              by_contra h
              have hk1 : k ≤ 1 := by omega
              have hle' : q ^ k ≤ q ^ 1 := (Nat.pow_le_pow_iff_right hq.one_lt).mpr hk1
              rw [pow_one] at hle'
              omega
            omega
          rw [hkE, hkE_eq]
        have hker_le : φ.ker ≤ E.subgroupOf D := by
          intro y hy
          rw [Subgroup.mem_subgroupOf]
          have hycomm : ⁅x, (y : G)⁆ = 1 := MonoidHom.mem_ker.mp hy
          let F : Subgroup G := Subgroup.closure ({(x : G), (y : G)} ∪ (Z : Set G))
          have hFea : IsElemAbelian q F := by
            dsimp only [F]
            refine k89qr_closure_union_elemAbelian hZea ?_ ?_ ?_
            · rintro a ha b hb
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
              rcases ha with ha | ha
              · rw [ha]; exact Subgroup.mem_centralizer_iff.mp (hZc hb) x hxD
              · rw [ha]; exact Subgroup.mem_centralizer_iff.mp (hZc hb) (y : G) y.2
            · rintro a ha b hb
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · rw [ha, hb]
              · rw [ha, hb]; exact commutatorElement_eq_one_iff_mul_comm.mp hycomm
              · rw [ha, hb]; exact (commutatorElement_eq_one_iff_mul_comm.mp hycomm).symm
              · rw [ha, hb]
            · rintro a ha
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
              rcases ha with ha | ha
              · rw [ha]; exact hpow x hxD
              · rw [ha]; exact hpow (y : G) y.2
          have hFleD : F ≤ D := by
            dsimp only [F]
            refine (Subgroup.closure_le _).mpr ?_
            rintro a (ha | ha)
            · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
              rcases ha with ha | ha
              · rw [ha]; exact hxD
              · rw [ha]; exact y.2
            · exact hZleD ha
          have hFcard : Nat.card F ≤ q ^ 2 := k89qr_elemAbelian_le hq hFleD hFea hrank
          have hEleF : E ≤ F := by
            dsimp only [E, F]
            refine (Subgroup.closure_le _).mpr ?_
            rintro a (ha | ha)
            · rw [Set.mem_singleton_iff] at ha; rw [ha]
              exact Subgroup.subset_closure (Or.inl (by simp))
            · exact Subgroup.subset_closure (Or.inr ha)
          have hEF : E = F := Subgroup.eq_of_le_of_card_ge hEleF (by rw [hEcard]; exact hFcard)
          rw [hEF]
          exact Subgroup.subset_closure (Or.inl (by simp))
        have hker_card_le : Nat.card φ.ker ≤ q ^ 2 := by
          calc Nat.card φ.ker ≤ Nat.card (E.subgroupOf D) := Subgroup.card_le_of_le hker_le
            _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEleD).toEquiv
            _ = q ^ 2 := hEcard
        have hDcard : Nat.card D = q * Nat.card φ.ker := by
          rw [← Subgroup.index_mul_card (H := φ.ker), hker_index]
        calc Nat.card D = q * Nat.card φ.ker := hDcard
          _ ≤ q * q ^ 2 := Nat.mul_le_mul_left q hker_card_le
          _ = Nat.card D' * q ^ 2 := by rw [hD'card]
      · exfalso
        apply hD'bot
        have hZcard : Nat.card Z = q ^ 2 := by rw [hs, hs2]
        have hDleZ : D ≤ Z := by
          intro x hxD
          let E : Subgroup G := Subgroup.closure ({x} ∪ (Z : Set G))
          have hEea : IsElemAbelian q E := by
            dsimp only [E]
            refine k89qr_closure_union_elemAbelian hZea ?_ ?_ ?_
            · rintro a ha b hb
              rw [Set.mem_singleton_iff] at ha; rw [ha]
              exact Subgroup.mem_centralizer_iff.mp (hZc hb) x hxD
            · rintro a ha b hb
              rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
            · rintro a ha
              rw [Set.mem_singleton_iff] at ha; rw [ha]
              exact hpow x hxD
          have hEleD : E ≤ D := by
            dsimp only [E]
            refine (Subgroup.closure_le _).mpr ?_
            rintro a (ha | ha)
            · rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hxD
            · exact hZleD ha
          have hZleE : Z ≤ E := by
            dsimp only [E]
            intro z hz
            exact Subgroup.subset_closure (Or.inr hz)
          have hxE : x ∈ E := by
            dsimp only [E]
            exact Subgroup.subset_closure (Or.inl (by simp))
          have hEcard : Nat.card E = q ^ 2 := by
            have hle : Nat.card E ≤ q ^ 2 := k89qr_elemAbelian_le hq hEleD hEea hrank
            have hZleE_card : Nat.card Z ≤ Nat.card E := Subgroup.card_le_of_le hZleE
            omega
          exact (Subgroup.eq_of_le_of_card_ge hZleE (by rw [hEcard, hZcard])).symm ▸ hxE
        have hDab : IsMulCommutative D :=
          IsMulCommutative.of_comm fun a b =>
            Subtype.ext (hZea.comm (hDleZ a.2) (hDleZ b.2))
        rw [hD'def]
        exact (Subgroup.commutator_self_eq_bot_iff (H := D)).mpr hDab
  rw [Subgroup.index_eq_card_div]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'leD).toEquiv]
  exact Nat.div_le_of_le_mul hmain

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
