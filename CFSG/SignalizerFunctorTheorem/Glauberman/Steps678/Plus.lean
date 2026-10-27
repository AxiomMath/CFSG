module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Eight

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem final_step (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) {S H Z : Subgroup G} {x z : G}
    (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hH : Maximal (solvableSignalizerCompatible p 1 A θ) H)
    (hCAH : signalizerCommonFixed p 1 A θ ≤ H) (hcore : primeCoreIn ({q}ᶜ : Set ℕ) H = ⊥)
    (hZS : Z ≤ S) (hZc : Z ≤ Subgroup.centralizer (S : Set G))
    (hZA : A ≤ Subgroup.normalizer (Z : Set G)) (hxH : x ∈ H) (hz : z ∈ Z)
    (hxz : ¬ IsPGroup q (Subgroup.zpowers ⁅x, z⁆)) : False := by
  have hq' := prime_of_two_or_three hq
  have hsyl : IsSylowOf q (S ⊓ H) H := isSylowOf_of_maximal h hq hS hH.prop.1 hCAH
  have hHN : H ≤ Subgroup.normalizer (primeCoreIn {q} H : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hXS : primeCoreIn {q} H ≤ S ⊓ H :=
    sylowOf_le_of_normal hsyl (primeCoreIn_le _ H) (isPGroup_primeCoreIn hq' H) hHN
  have hX0 : primeCoreIn {q} H ≠ ⊥ := by
    intro hb
    have hH0 : H = ⊥ := eq_bot_of_primeCoreIn_eq_bot hq' hH.prop.2 hcore hb
    have hx1 : x = 1 := by
      have hmem : x ∈ (⊥ : Subgroup G) := by
        rw [← hH0]
        exact hxH
      exact Subgroup.mem_bot.mp hmem
    apply hxz
    have hc : ⁅x, z⁆ = 1 := by rw [hx1]; simp
    rw [hc, Subgroup.zpowers_one_eq_bot]
    exact IsPGroup.of_bot
  have hXcomp : solvableSignalizerCompatible p 1 A θ (primeCoreIn {q} H) :=
    compat_of_le hH.prop (primeCoreIn_le _ H) (le_normalizer_primeCoreIn _ hH.prop.1.1)
  obtain ⟨hNcomp, -, -, hNmax⟩ := normalizerCompletion_spec h hX0 hXcomp
  have hHN' : H ≤ signalizerNormalizerCompletion p 1 A θ (primeCoreIn {q} H) :=
    hNmax H hH.prop.1 hHN
  have hNH : signalizerNormalizerCompletion p 1 A θ (primeCoreIn {q} H) ≤ H :=
    hH.2 hNcomp hHN'
  have hZX : Z ≤ Subgroup.centralizer (primeCoreIn {q} H : Set G) :=
    hZc.trans (Subgroup.centralizer_le (hXS.trans inf_le_left))
  have hZcomp : signalizerCompatible p 1 A θ Z :=
    signalizer_compatible_of_le p 1 A θ hS.prop.1 hZS hZA
  have hZH : Z ≤ H :=
    (hNmax Z hZcomp (hZX.trans (Subgroup.centralizer_le_normalizer _))).trans hNH
  have hZO : Z ≤ primeCoreIn {q} H := fun y hy =>
    centralizer_primeCoreIn_le hq' hH.prop.2 hcore ⟨hZH hy, hZX hy⟩
  have hzX : z ∈ primeCoreIn {q} H := hZO hz
  have hxz' : x * z * x⁻¹ ∈ primeCoreIn {q} H :=
    (Subgroup.mem_normalizer_iff.mp (hHN hxH) z).mp hzX
  have hcomm : ⁅x, z⁆ ∈ primeCoreIn {q} H :=
    Subgroup.mul_mem _ hxz' (Subgroup.inv_mem _ hzX)
  exact hxz ((isPGroup_primeCoreIn hq' H).to_le ((Subgroup.zpowers_le).mpr hcomm))

theorem exists_plus (h : Setting p A θ) {q r : ℕ} (hqr : (q = 2 ∧ r = 3) ∨ (q = 3 ∧ r = 2))
    {S : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S) (hS0 : S ≠ ⊥) :
    ∃ (Z B' : Subgroup G) (x z : G), Z ≤ S ∧ Z ≤ Subgroup.centralizer (S : Set G) ∧
      A ≤ Subgroup.normalizer (Z : Set G) ∧ B' ∈ Coprime.hyperplanes p A ∧
      (∀ S' ∈ signalizerFunctorEk p 1 A, S' ≤ B' → x ∈ θ S') ∧ z ∈ Z ∧
      ¬ IsPGroup q (Subgroup.zpowers ⁅x, z⁆) := by
  obtain ⟨hq', hr', hqr'⟩ := prime_of_roles hqr
  have hq : q = 2 ∨ q = 3 := by rcases hqr with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hr : r = 2 ∨ r = 3 := by rcases hqr with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  have hScomp := hS.prop
  have hSq : IsPGroup q S := hScomp.2
  obtain ⟨ZS, hZSdef⟩ : ∃ ZS : Subgroup G, ZS = (Subgroup.center S).map S.subtype := ⟨_, rfl⟩
  have hZSle : ZS ≤ S := by
    rw [hZSdef]
    exact Subgroup.map_subtype_le _
  have hZSc : ZS ≤ Subgroup.centralizer (S : Set G) := by
    rw [hZSdef]
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨b, hb⟩)
  have hZS0 : ZS ≠ ⊥ := by
    have : Fact q.Prime := ⟨hq'⟩
    have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS0
    have := hSq.center_nontrivial
    obtain ⟨⟨a, ha⟩, hane⟩ := exists_ne (1 : Subgroup.center S)
    intro hb
    apply hane
    have hmem : (a : G) ∈ ZS := by
      rw [hZSdef]
      exact ⟨a, ha, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hAZS : A ≤ Subgroup.normalizer (ZS : Set G) := by
    rw [hZSdef]
    exact characteristic_subgroup_map_normalized A S hScomp.1.1 (Subgroup.center S)
  have hZScop : Nat.Coprime p (Nat.card ZS) :=
    (coprime_card h hScomp.1).of_dvd_right (Subgroup.card_dvd_of_le hZSle)
  have hgen := generation_hyperplanes h.prime h.elementary (large_sq h) hAZS hZScop
  obtain ⟨B, hB, hZB⟩ : ∃ B ∈ Coprime.hyperplanes p A,
      ZS ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    by_contra hcon
    have hall : ∀ B ∈ Coprime.hyperplanes p A, ZS ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
      intro B hB
      by_contra hb
      exact hcon ⟨B, hB, hb⟩
    apply hZS0
    rw [← hgen]
    exact iSup_eq_bot.mpr fun B => iSup_eq_bot.mpr fun hB => hall B hB
  have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
    (elementary_abelian_le_centralizer p A B h.elementary hB.1).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZbS : ZS ⊓ Subgroup.centralizer (B : Set G) ≤ S := inf_le_left.trans hZSle
  have hZbC : ZS ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (S : Set G) :=
    inf_le_left.trans hZSc
  have hAZb : A ≤ Subgroup.normalizer ((ZS ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :
      Set G) := normalizer_inf_of_le A _ _ hAZS (le_normalizer_centralizer hAB)
  have hZbθ : ∀ S₀ ∈ signalizerFunctorEk p 1 A, S₀ ≤ B →
      ZS ⊓ Subgroup.centralizer (B : Set G) ≤ θ S₀ := fun S₀ hS₀ hS₀B =>
    (le_inf hZbS (inf_le_right.trans (Subgroup.centralizer_le hS₀B))).trans
      (hScomp.1.2 S₀ hS₀)
  obtain ⟨S₀, hS₀, hS₀B, hS₀not⟩ : ∃ S₀ ∈ signalizerFunctorEk p 1 A, S₀ ≤ B ∧
      ¬ ZS ⊓ Subgroup.centralizer (B : Set G) ≤ primeCoreIn ({r}ᶜ : Set ℕ) (θ S₀) := by
    by_contra hcon
    have hall : ∀ S₀ ∈ signalizerFunctorEk p 1 A, S₀ ≤ B →
        ZS ⊓ Subgroup.centralizer (B : Set G) ≤ primeCoreIn ({r}ᶜ : Set ℕ) (θ S₀) := by
      intro S₀ h1 h2
      by_contra hb
      exact hcon ⟨S₀, h1, h2, hb⟩
    have hle : ZS ⊓ Subgroup.centralizer (B : Set G) ≤ hyperplaneMeet p r A B θ :=
      le_iInf fun S₀ => le_iInf fun h1 => le_iInf fun h2 => hall S₀ h1 h2
    have hle2 : ZS ⊓ Subgroup.centralizer (B : Set G) ≤ hyperplaneMeetJoin p r A θ :=
      hle.trans (by unfold hyperplaneMeetJoin; exact le_iSup₂_of_le B hB le_rfl)
    rw [hyperplaneMeetJoin_eq_bot h hr] at hle2
    exact hZB (le_bot_iff.mp hle2)
  obtain ⟨M, hM, hθM⟩ := exists_maximal_ge (compat_value h hS₀)
  have hCAM : signalizerCommonFixed p 1 A θ ≤ M := (commonFixed_le_value hS₀).trans hθM
  have hsylM : IsSylowOf q (S ⊓ M) M := isSylowOf_of_maximal h hq hS hM.prop.1 hCAM
  have hMN : M ≤ Subgroup.normalizer (primeCoreIn {q} M : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hXqS : primeCoreIn {q} M ≤ S ⊓ M :=
    sylowOf_le_of_normal hsylM (primeCoreIn_le _ M) (isPGroup_primeCoreIn hq' M) hMN
  have hZbM : ZS ⊓ Subgroup.centralizer (B : Set G) ≤ M :=
    (hZbθ S₀ hS₀ hS₀B).trans hθM
  have hZbX : ZS ⊓ Subgroup.centralizer (B : Set G) ≤
      Subgroup.centralizer (primeCoreIn {q} M : Set G) :=
    hZbC.trans (Subgroup.centralizer_le (hXqS.trans inf_le_left))
  have hZbnX : ¬ ZS ⊓ Subgroup.centralizer (B : Set G) ≤ primeCoreIn {q} M := by
    intro hle
    apply hS₀not
    refine le_trans (le_inf hle (hZbθ S₀ hS₀ hS₀B)) ?_
    refine le_primeCoreIn_compl hr' inf_le_right ?_ ?_
    · exact normalizer_inf_of_le _ _ _
        (le_normalizer_primeCoreIn _ (hθM.trans Subgroup.le_normalizer)) Subgroup.le_normalizer
    · exact coprime_of_isPGroup hq' hr' hqr'.symm
        ((isPGroup_primeCoreIn hq' M).to_le inf_le_left)
  obtain ⟨q₀, hq₀, hcore⟩ := exists_primeCoreIn_eq_bot h hM hCAM
  have hq₀' : q₀ = q ∨ q₀ = r := by
    rcases hqr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hq₀ with h3 | h3 <;> simp [h1, h2, h3]
  have hcore' : primeCoreIn ({r}ᶜ : Set ℕ) M = ⊥ := by
    rcases hq₀' with hqq | hqr₀
    · exfalso
      rw [hqq] at hcore
      exact hZbnX fun y hy =>
        centralizer_primeCoreIn_le hq' hM.prop.2 hcore ⟨hZbM hy, hZbX hy⟩
    · rw [hqr₀] at hcore
      exact hcore
  have hMY : M ≤ Subgroup.normalizer (primeCoreIn {r} M : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hYself := centralizer_primeCoreIn_le hr' hM.prop.2 hcore'
  have hZbY : ¬ ZS ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer
      (primeCoreIn {r} M : Set G) := by
    intro hle
    apply hZB
    exact eq_bot_of_isPGroup_of_isPGroup hq' hr' hqr' hSq (isPGroup_primeCoreIn hr' M) hZbS
      (fun y hy => hYself ⟨hZbM hy, hle hy⟩)
  have hAY : A ≤ Subgroup.normalizer (primeCoreIn {r} M : Set G) :=
    le_normalizer_primeCoreIn _ hM.prop.1.1
  have hYcop : Nat.Coprime p (Nat.card (primeCoreIn {r} M)) :=
    (coprime_card h hM.prop.1).of_dvd_right (Subgroup.card_dvd_of_le (primeCoreIn_le _ M))
  have hgenY := generation_hyperplanes h.prime h.elementary (large_sq h) hAY hYcop
  obtain ⟨B', hB', hB'not⟩ : ∃ B' ∈ Coprime.hyperplanes p A,
      ¬ primeCoreIn {r} M ⊓ Subgroup.centralizer (B' : Set G) ≤
        Subgroup.centralizer (ZS ⊓ Subgroup.centralizer (B : Set G) : Set G) := by
    by_contra hcon
    have hall : ∀ B' ∈ Coprime.hyperplanes p A, primeCoreIn {r} M ⊓
        Subgroup.centralizer (B' : Set G) ≤
          Subgroup.centralizer (ZS ⊓ Subgroup.centralizer (B : Set G) : Set G) := by
      intro B' hB'
      by_contra hb
      exact hcon ⟨B', hB', hb⟩
    have hYle : primeCoreIn {r} M ≤
        Subgroup.centralizer (ZS ⊓ Subgroup.centralizer (B : Set G) : Set G) :=
      le_trans (le_of_eq hgenY.symm) (iSup₂_le fun B' hB' => hall B' hB')
    exact hZbY (Subgroup.le_centralizer_iff.mp hYle)
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.not_le_iff_exists.mp hB'not
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ ZS ⊓ Subgroup.centralizer (B : Set G), z * x ≠ x * z := by
    by_contra hcon
    apply hxn
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    by_contra hne
    exact hcon ⟨z, hz, hne⟩
  have hxY : x ∈ primeCoreIn {r} M := hx.1
  have hxC : x ∈ Subgroup.centralizer (B' : Set G) := hx.2
  have hxθ : ∀ S' ∈ signalizerFunctorEk p 1 A, S' ≤ B' → x ∈ θ S' := fun S' hS' hS'B' =>
    hM.prop.1.2 S' hS' ⟨primeCoreIn_le _ M hxY, Subgroup.centralizer_le hS'B' hxC⟩
  have hcY : ⁅x, z⁆ ∈ primeCoreIn {r} M := by
    have h1 : z * x⁻¹ * z⁻¹ ∈ primeCoreIn {r} M :=
      (Subgroup.mem_normalizer_iff.mp (hMY (hZbM hz)) x⁻¹).mp (Subgroup.inv_mem _ hxY)
    have h2 := Subgroup.mul_mem _ hxY h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hc1 : ⁅x, z⁆ ≠ 1 := by
    intro hc
    exact hzx (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
  refine ⟨ZS ⊓ Subgroup.centralizer (B : Set G), B', x, z, hZbS, hZbC, hAZb, hB', hxθ, hz, ?_⟩
  intro hcq
  exact hc1 (eq_one_of_mem_of_isPGroup hq' hr' hqr' (isPGroup_primeCoreIn hr' M) hcY hcq)

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
