module

public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.Quasithin.Vol2.Ch11G2Q8Borel
public import CFSG.Quasithin.Vol2.KGNatSL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CGT.Timmesfeld75
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)
open scoped MatrixGroups

namespace BK4

theorem isSolvable_subgroupOf {G : Type*} [Group G] {Y : Subgroup G} (hY : Group.IsSolvable Y)
    (S : Subgroup G) : Group.IsSolvable (Y.subgroupOf S) := by
  have := hY
  let φ : ↥(Y.subgroupOf S) →* ↥Y :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun a b h => ?_
  have h1 : ((φ a : ↥Y) : G) = ((φ b : ↥Y) : G) := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h1)

theorem isSolvable_map {G G' : Type*} [Group G] [Group G'] (φ : G →* G') {H : Subgroup G}
    (hH : Group.IsSolvable H) : Group.IsSolvable (H.map φ) := by
  have := hH
  exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective H)

section SL2

variable {F : Type} [Field F]

theorem le_borel_of_utri_le {J : Subgroup SL(2, F)} (hU : utri F ≤ J) (hJ : J ≠ ⊤) :
    J ≤ borel F := by
  intro h hh
  by_contra hnb
  apply hJ
  rw [eq_top_iff, ← KGNat.utri_sup_conj_eq_top hnb]
  refine sup_le hU fun x hx => ?_
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
  have := J.mul_mem (J.mul_mem hh (hU hx)) (J.inv_mem hh)
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this

theorem apply_01_eq_zero_of_ltri_le {J : Subgroup SL(2, F)} (hL : ltri F ≤ J) (hJ : J ≠ ⊤)
    {g : SL(2, F)} (hg : g ∈ J) : g 0 1 = 0 := by
  set w : SL(2, F) := wElt with hw
  set J' := CFSG.CGT.Timmesfeld75.conjSubgroup w⁻¹ J with hJ'def
  have hmem : ∀ x, x ∈ J' ↔ w * x * w⁻¹ ∈ J := fun x => by
    rw [hJ'def, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv]
  have hU : utri F ≤ J' := by
    intro u hu
    rw [hmem]
    refine hL ?_
    rw [← conjSubgroup_wElt_utri, CFSG.CGT.Timmesfeld75.mem_conjSubgroup, ← hw]
    rwa [show w⁻¹ * (w * u * w⁻¹) * w = u by group]
  have hJ' : J' ≠ ⊤ := by
    intro htop
    apply hJ
    refine eq_top_iff.mpr fun x _ => ?_
    have h1 : w⁻¹ * x * w ∈ J' := htop ▸ Subgroup.mem_top _
    rw [hmem] at h1
    rwa [show w * (w⁻¹ * x * w) * w⁻¹ = x by group] at h1
  have h1 : w⁻¹ * g * w ∈ J' := by
    rw [hmem]
    rwa [show w * (w⁻¹ * g * w) * w⁻¹ = g by group]
  have h2 : (w⁻¹ * g * w) 1 0 = 0 := le_borel_of_utri_le hU hJ' h1
  have e10 : ((w⁻¹ * g * w : SL(2, F)) 1 0) = - g 0 1 := by
    rw [hw]
    sl2_simp
    ring
  rw [e10, neg_eq_zero] at h2
  exact h2

theorem ne_top_of_isSolvable [CharP F 2] (h4 : 4 ≤ Nat.card F) {J : Subgroup SL(2, F)}
    (hJ : Group.IsSolvable J) : J ≠ ⊤ := by
  rintro rfl
  have := hJ
  exact E1.RootLift.not_isSolvable_SL2 h4
    (Group.isSolvable_of_surjective (f := (⊤ : Subgroup SL(2, F)).subtype)
      fun x => ⟨⟨x, trivial⟩, rfl⟩)

end SL2

variable {F : Type} [Field F] [CharP F 2]

theorem mem_sup_torusG_of_levi1Mat {b : ↥(cayleyGroup F)} (hbS : b ∈ G2Q8.stabV0 F)
    (h01 : G2Q8.levi1Mat b 0 1 = 0) : b ∈ G2Q8.U0 F ⊔ G2Q8.torusG F := by
  have hdet := G2Q8.det_levi1Mat hbS
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  have hx0 : G2Q8.levi1Mat b 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  obtain ⟨s, hs⟩ : ∃ s : Fˣ × Fˣ, s = (1, Units.mk0 (G2Q8.levi1Mat b 0 0) hx0) := ⟨_, rfl⟩
  have htS : g2T s ∈ G2Q8.stabV0 F := by
    rw [G2Q8.mem_stabV0, G2Q8.g2Act_g2T_eu]
    simp [hs]
  obtain ⟨r, hr⟩ : ∃ r : F, r = G2Q8.levi1Mat b 0 0 * G2Q8.levi1Mat b 1 0 := ⟨_, rfl⟩
  have hu : g2A (uSL 0 0 r) ∈ G2Q8.U0 F := G2Q8.g2A_mem_U0 0 0 _
  have hM : G2Q8.levi1Mat (g2T s * b) = G2Q8.levi1Mat (g2A (uSL 0 0 r)) := by
    rw [G2Q8.levi1Mat_mul htS hbS, G2Q8.levi1Mat_g2T, G2Q8.levi1Mat_uSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hs, h01, hx0, hdet, hr]
  have hb₃ := G2Q8.inv_mul_mem_U0_of_levi1Mat ((G2Q8.stabV0 F).mul_mem htS hbS) hu hM
  have hbeq : b = (g2T s)⁻¹ * (g2A (uSL 0 0 r) * ((g2A (uSL 0 0 r))⁻¹ * (g2T s * b))) := by
    group
  rw [hbeq]
  exact Subgroup.mul_mem _ (le_sup_right (a := G2Q8.U0 F) (Subgroup.inv_mem _ ⟨s, rfl⟩))
    (le_sup_left (b := G2Q8.torusG F) (Subgroup.mul_mem _ hu hb₃))

omit [CharP F 2] in
theorem one_le_of_card [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [pow_zero] at hK
    exact absurd hK (Finite.one_lt_card (α := F)).ne'
  · exact h

theorem le_U0_of_le_normalizer [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n)
    {X : Subgroup ↥(cayleyGroup F)} (hX : IsPGroup 2 X)
    (hXN : X ≤ Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F))) : X ≤ G2Q8.U0 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := hX.to_sup_of_normal_right' G2Q8.isPGroup_U0 hXN
  have hmax := (IsPGroup.toSylow G2Q8.isPGroup_U0
    (G2Q8.not_two_dvd_index_U0 hK (one_le_of_card hK))).is_maximal' hsup le_sup_right
  intro x hx
  have hmem : x ∈ X ⊔ G2Q8.U0 F := le_sup_left (b := G2Q8.U0 F) hx
  rw [hmax] at hmem
  exact hmem

theorem le_normalizer_of_le_stabQ_one [Finite F] (h4 : 4 ≤ Nat.card F) {n : ℕ}
    (hK : Nat.card F = 2 ^ n) {Y : Subgroup ↥(cayleyGroup F)} (hY : Group.IsSolvable Y)
    (hU : G2Q8.U0 F ≤ Y) (hY1 : Y ≤ G2Q8.stabQ (G2Q8.stdF F 1)) :
    Y ≤ Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F)) := by
  have hnorm : ∀ y ∈ Y, ∀ x ∈ G2Q8.stabV0 F, y * x * y⁻¹ ∈ G2Q8.stabV0 F := by
    intro y hy x hxS
    obtain ⟨c, hc⟩ := G2Q8.mem_stdF_one_iff.mp
      ((G2Q8.mem_stabQ.mp (hY1 (Y.inv_mem hy)) _).mp
        (G2Q8.mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩))
    rw [G2Q8.mem_stabV0, G2Q8.g2Act_mul_apply, G2Q8.g2Act_mul_apply, hc, G2Q8.g2Act_smul,
      G2Q8.mem_stabV0.mp hxS, ← hc, G2Q8.g2Act_apply_inv]
  have hJs : Group.IsSolvable ((Y.subgroupOf (G2Q8.stabV0 F)).map G2Q8.levi1) :=
    isSolvable_map _ (isSolvable_subgroupOf hY _)
  have hLJ : ltri F ≤ (Y.subgroupOf (G2Q8.stabV0 F)).map G2Q8.levi1 := by
    intro x hx
    obtain ⟨t, rfl⟩ := mem_ltri_iff.mp hx
    have hmem : g2A (uSL 0 0 t) ∈ G2Q8.U0 F := G2Q8.g2A_mem_U0 0 0 t
    refine ⟨⟨_, G2Q8.U0_le_stabV0 hmem⟩, hU hmem, Subtype.ext ?_⟩
    rw [G2Q8.levi1_apply, G2Q8.levi1Mat_uSL]
    rfl
  have hY0 : ∀ y ∈ Y, y ∈ G2Q8.stabV0 F →
      y ∈ Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F)) := by
    intro y hy hyS
    have h1 := apply_01_eq_zero_of_ltri_le hLJ (ne_top_of_isSolvable h4 hJs)
      (Subgroup.mem_map_of_mem G2Q8.levi1
        (show (⟨y, hyS⟩ : ↥(G2Q8.stabV0 F)) ∈ Y.subgroupOf (G2Q8.stabV0 F) from hy))
    rw [G2Q8.levi1_apply] at h1
    rw [G2Q8.normalizer_U0_eq]
    exact mem_sup_torusG_of_levi1Mat hyS h1
  have hfwd : ∀ y ∈ Y, ∀ u ∈ G2Q8.U0 F, y * u * y⁻¹ ∈ G2Q8.U0 F := by
    intro y hy u hu
    have hXN : (G2Q8.U0 F).map (MulAut.conj y).toMonoidHom ≤
        Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F)) := by
      rintro _ ⟨v, hv, rfl⟩
      have hvY := hU hv
      exact hY0 _ (Y.mul_mem (Y.mul_mem hy hvY) (Y.inv_mem hy))
        (hnorm y hy v (G2Q8.U0_le_stabV0 hv))
    exact le_U0_of_le_normalizer hK (G2Q8.isPGroup_U0.map _) hXN ⟨u, hu, rfl⟩
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => hfwd y hy u hu, fun hu => ?_⟩
  have := hfwd y⁻¹ (Y.inv_mem hy) _ hu
  rwa [show y⁻¹ * (y * u * y⁻¹) * y⁻¹⁻¹ = u by group] at this

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
