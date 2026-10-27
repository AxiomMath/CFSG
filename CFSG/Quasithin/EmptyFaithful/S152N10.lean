module

public import CFSG.Quasithin.EmptyFaithful.S152NAbs
public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S152N

section Dihedral

variable {Γ : Type*} [Group Γ]

theorem exists_involution_of_equiv_dihedral {A : Subgroup Γ} {n : ℕ} [NeZero n]
    (e : ↥A ≃* DihedralGroup n) : ∃ u ∈ A, u ^ 2 = 1 ∧ u ≠ 1 := by
  refine ⟨((e.symm (DihedralGroup.sr 0) : ↥A) : Γ), (e.symm (DihedralGroup.sr 0)).2, ?_, ?_⟩
  · have h : e.symm (DihedralGroup.sr 0) ^ 2 = 1 := by
      rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
    exact congrArg Subtype.val h
  · intro h1
    have h2 : e.symm (DihedralGroup.sr 0) = 1 := Subtype.ext h1
    have h3 : DihedralGroup.sr (0 : ZMod n) = 1 := by
      have := congrArg e h2
      simpa using this
    rw [DihedralGroup.one_def] at h3
    cases h3

theorem props_of_not_four_dvd [Finite Γ] {Mb Tb M0 : Subgroup Γ} (hsyl : IsSylowTwoOf Tb Mb)
    (h4 : ¬ 4 ∣ Nat.card Mb) (hM0 : M0 ≤ Mb) (hnorm : ∀ g ∈ Mb, ∀ y ∈ M0, g * y * g⁻¹ ∈ M0)
    {u : Γ} (hu : u ∈ M0) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    (∀ a ∈ Tb, ∀ b ∈ Tb, a * b = b * a) ∧ ∀ x ∈ Tb, x ^ 2 = 1 → x ≠ 1 → x ∈ M0 := by
  have hcard : Nat.card Tb ≤ 2 :=
    card_le_two_of_dvd hsyl.2.1 (Subgroup.card_dvd_of_le hsyl.1) h4
  refine ⟨comm_of_card_le_four hsyl.2.1 (by omega), fun x hx hx2 hx1 => ?_⟩
  exact involution_mem_of_normal hsyl hM0 hnorm
    (fun a ha b hb _ _ ha1 hb1 => eq_of_card_le_two hcard ha hb ha1 hb1) hu hu2 hu1 hx hx2 hx1

end Dihedral

section Main

variable {G : Type} [Group G] [Finite G]

theorem tbar_props {T Mc M : Subgroup G} (hs : Setting152 T Mc M) (hc : Lemma15201Concl T Mc M)
    (hV : IsElemAbelian 2 (V154 T Mc M)) :
    (∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a * b = b * a) ∧
      ∀ x ∈ autOn T (V154 T Mc M), x ^ 2 = 1 → x ≠ 1 → x ∈ mBar0 T Mc M := by
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M)) :=
    B2F.isSylowTwoOf_autI hV hMN (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM)
  have hM0le : mBar0 T Mc M ≤ autOn M (V154 T Mc M) := by
    unfold mBar0
    rw [JhatOn_eq hV]
    exact @Jhat_le ↥(V154 T Mc M) (commGroupOfElemAbelian hV) inferInstance _
  have hnorm : ∀ g ∈ autOn M (V154 T Mc M), ∀ y ∈ mBar0 T Mc M, g * y * g⁻¹ ∈ mBar0 T Mc M :=
    fun g hg y hy => JhatOn_normalized hg hy
  rcases hc.cases with ⟨-, hA, ⟨e⟩⟩ | ⟨-, ⟨e⟩, ⟨e'⟩⟩ | ⟨-, hA, hΩ⟩ | ⟨-, ⟨e⟩, hT, -⟩
  ·
    obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral e
    refine props_of_not_four_dvd hsyl ?_ hM0le hnorm hu hu2 hu1
    have : Nat.card (autOn M (V154 T Mc M)) = 6 := by
      rw [hA, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  ·
    obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral e
    refine props_of_not_four_dvd hsyl ?_ hM0le hnorm hu hu2 hu1
    have : Nat.card (autOn M (V154 T Mc M)) = 18 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      have : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [this]
    omega
  ·
    obtain ⟨hV', hX⟩ := hΩ
    have hW2 : ∀ w : IntMod (V154 T Mc M) hV, w * w = 1 := fun w => by
      rw [← pow_two]; exact IntMod.sq_eq_one w
    refine ⟨comm_of_isOmegaFourPlus (W := IntMod (V154 T Mc M) hV) hW2 hX hsyl.1 hsyl.2.1, ?_⟩
    intro x hx _ _
    rw [← hA]
    exact hsyl.1 hx
  ·
    obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral e
    have hcomm : ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a * b = b * a := by
      have key : ∀ {n : ℕ} (f : ↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod n)),
          ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a * b = b * a := by
        intro n f a ha b hb
        have := f.injective ((map_mul f ⟨a, ha⟩ ⟨b, hb⟩).trans
          ((mul_comm _ _).trans (map_mul f ⟨b, hb⟩ ⟨a, ha⟩).symm))
        exact congrArg Subtype.val this
      rcases hT with hT | hT
      · obtain ⟨f⟩ := hT
        exact key f
      · obtain ⟨f⟩ := hT
        exact key f
    have huniq : ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 → b ^ 2 = 1 →
        a ≠ 1 → b ≠ 1 → a = b := by
      have key : ∀ {n : ℕ} (f : ↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod n)),
          (∀ x y : Multiplicative (ZMod n), x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y) →
          ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 → b ^ 2 = 1 →
            a ≠ 1 → b ≠ 1 → a = b := by
        intro n f hall a ha b hb ha2 hb2 ha1 hb1
        have h1 : f ⟨a, ha⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨a, ha⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext ha2
          rw [this, map_one]
        have h2 : f ⟨b, hb⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨b, hb⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext hb2
          rw [this, map_one]
        have h3 : f ⟨a, ha⟩ ≠ 1 := fun h =>
          ha1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
        have h4 : f ⟨b, hb⟩ ≠ 1 := fun h =>
          hb1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
        exact congrArg Subtype.val (f.injective (hall _ _ h1 h2 h3 h4))
      rcases hT with hT | hT
      · obtain ⟨f⟩ := hT
        exact key f (by decide)
      · obtain ⟨f⟩ := hT
        exact key f (by decide)
    exact ⟨hcomm, fun x hx hx2 hx1 =>
      involution_mem_of_normal hsyl hM0le hnorm huniq hu hu2 hu1 hx hx2 hx1⟩

end Main

end S152N

open S152N

section Final

variable {G : Type} [Group G] [Finite G]

theorem stageLemma15210_of (h1518 : StageLemma1518) (h15201 : StageLemma15201) :
    StageLemma15210 := by
  intro G _ _ T Mc M hs D hD
  have hc := h15201 G T Mc M hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hV : IsElemAbelian 2 (V154 T Mc M) := by
    by_contra hV
    have : D ∈ (∅ : Set (Subgroup (MulAut (V154 T Mc M)))) := by
      unfold QsetOn at hD
      rwa [dite_eq_right hV] at hD
    exact this
  have hD0 : D ∈ @Qset ↥(V154 T Mc M) (commGroupOfElemAbelian hV) (autOn T (V154 T Mc M)) := by
    unfold QsetOn at hD
    rwa [dite_eq_left hV] at hD
  obtain ⟨⟨hA2, hr⟩, hcq⟩ := hD0
  have hrk : rk (IntMod (V154 T Mc M) hV) = 4 := by
    have h1 := card_eq_two_pow_of_isPGroup
      (isPGroup_two_of_sq_eq_one (fun v : IntMod (V154 T Mc M) hV => IntMod.sq_eq_one v))
    have h2 : Nat.card (IntMod (V154 T Mc M) hV) = 16 := hc.card
    rw [h2] at h1
    have : (2 : ℕ) ^ rk (IntMod (V154 T Mc M) hV) = 2 ^ 4 := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  have hq : (2 : WithTop ℚ) ≤ qOf (autI hV M) := by
    have h18 := h1518 G T Mc M hs.qtfe hs.mf hs.ce
    have hqOn : qOn M (V154 T Mc M) = 2 := by
      rcases h18 with ⟨-, h⟩ | ⟨-, -, h⟩ <;> exact h
    have : qInt M (V154 T Mc M) hV = 2 := by rw [← qOn_eq hV]; exact hqOn
    exact this.ge
  have hTbM : autI hV T ≤ autI hV M := autI_mono hV hTM
  have hD' : D ∈ Qset (autI hV M) := ⟨⟨⟨hA2.1.trans hTbM, hA2.2⟩, hr⟩, hcq⟩
  obtain ⟨hrkD, hrkC⟩ := rk_of_mem_Qset (V := IntMod (V154 T Mc M) hV)
    (fun v => IntMod.sq_eq_one v) hrk hq hD'
  obtain ⟨hcomm, hP2⟩ := tbar_props hs hc hV
  have hA2I : IsA2 (autI hV T) D := hA2
  have hDp : IsPGroup 2 D := hA2I.isElemAbelian2.isPGroup
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · exact hP2 x (hA2.1 hx) (hA2I.isElemAbelian2.2 x hx) hx1
  ·
    have h1 : Nat.card D = 2 ^ rk D := card_eq_two_pow_of_isPGroup hDp
    have h2 : rk D = 1 := hrkD
    rw [h1, h2, pow_one]
  ·
    have hY : preOn T (V154 T Mc M) D ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      (preOn_le _ _ _).trans (hTM.trans hMN)
    have h1 := S1417.commutator_eq_map_commV hV hY
    have h2 : autI hV (preOn T (V154 T Mc M) D) = D := autOn_preOn hA2.1
    rw [h1, h2, Subgroup.card_map_of_injective (S1417.inclMod_injective hV),
      card_eq_two_pow (fun v : IntMod (V154 T Mc M) hV => IntMod.sq_eq_one v) (commV D), hrkC]
    norm_num
  ·
    intro x hx
    have hxV := hMN (hTM hx)
    have hxP : x ∈ Subgroup.normalizer (preOn T (V154 T Mc M) D : Set G) :=
      le_normalizer_preOn (hTM.trans hMN) (fun g hg y hy => by
        have hgy : g * y * g⁻¹ = y := by
          rw [hcomm g hg y (hA2.1 hy)]; group
        rw [hgy]; exact hy) hx
    exact A4.mem_normalizer_commutator hxV hxP

end Final

end CFSG.Quasithin
