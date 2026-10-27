module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Milestones.ASVolI.F431.J3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Gen

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4r_conj_of_same_type (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3)
    (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d) {i j : E} (hi : i ∈ Gp) (hj : j ∈ Gp) (hi1 : i ≠ 1)
    (hi2 : i * i = 1) (hj1 : j ≠ 1) (hj2 : j * j = 1)
    (hL : (∃ g ∈ Gp, g * i * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ↔
      (∃ g ∈ Gp, g * j * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))))) :
    ∃ g ∈ Gp, g * i * g⁻¹ = j := by
  haveI := hyp.finite
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp
  have h27 := as_F_4_27 κ f ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨-, -, -, h3, -, -⟩ := h27
  obtain ⟨hcard, ⟨C, ⟨hCI, hCm⟩, hCu⟩, -, -, -⟩ := h3 ⟨hL3, hSp, hG2d⟩
  have hS : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
      (ctr (pCoreOf 2 ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp))).map
        Gp.subtype := by
    rw [burnsideF4j_inf_inf_eq_map, burnsideF4j_pCoreOf_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective]
  have hmemI : ∀ (x : E) (hx : x ∈ Gp), x ≠ 1 → x * x = 1 →
      ConjClasses.mk (⟨x, hx⟩ : ↥Gp) ∈ InvClasses ↥Gp := fun x hx hx1 hx2 =>
    ⟨⟨x, hx⟩, ConjClasses.mem_carrier_mk, fun h => hx1 (congrArg Subtype.val h),
      Subtype.ext hx2⟩
  have hLC : ∀ (x : E) (hx : x ∈ Gp), x ≠ 1 → x * x = 1 →
      ((∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ↔
        ConjClasses.mk (⟨x, hx⟩ : ↥Gp) = C) := by
    intro x hx hx1 hx2
    constructor
    · rintro ⟨g, hg, hgx⟩
      rw [hS] at hgx
      obtain ⟨w, hw, hwx⟩ := hgx
      refine hCu _ ⟨hmemI x hx hx1 hx2, w, ?_, hw⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      refine isConj_iff.mpr ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩
      show g⁻¹ * (w : E) * g⁻¹⁻¹ = x
      have hwx' : (w : E) = g * x * g⁻¹ := hwx
      rw [hwx']
      group
    · intro hxC
      obtain ⟨w, hwC, hwS⟩ := hCm
      rw [← hxC, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hwC
      obtain ⟨c, hc⟩ := isConj_iff.mp hwC.symm
      refine ⟨(c : E), c.2, ?_⟩
      rw [hS]
      exact ⟨w, hwS, (congrArg Subtype.val hc).symm⟩
  have hiI := hmemI i hi hi1 hi2
  have hjI := hmemI j hj hj1 hj2
  have hconj : ConjClasses.mk (⟨i, hi⟩ : ↥Gp) = ConjClasses.mk (⟨j, hj⟩ : ↥Gp) := by
    by_cases hLi : ∃ g ∈ Gp, g * i * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    · rw [(hLC i hi hi1 hi2).mp hLi, (hLC j hj hj1 hj2).mp (hL.mp hLi)]
    · have hLj : ¬ ∃ g ∈ Gp, g * j * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
        fun h => hLi (hL.mpr h)
      have hiC : ConjClasses.mk (⟨i, hi⟩ : ↥Gp) ≠ C := fun h => hLi ((hLC i hi hi1 hi2).mpr h)
      have hjC : ConjClasses.mk (⟨j, hj⟩ : ↥Gp) ≠ C := fun h => hLj ((hLC j hj hj1 hj2).mpr h)
      by_contra hne
      have hsub : ({C, ConjClasses.mk (⟨i, hi⟩ : ↥Gp), ConjClasses.mk (⟨j, hj⟩ : ↥Gp)} :
          Set (ConjClasses ↥Gp)) ⊆ InvClasses ↥Gp := by
        intro D hD
        rcases hD with rfl | rfl | hD
        · exact hCI
        · exact hiI
        · rw [Set.mem_singleton_iff] at hD
          rw [hD]
          exact hjI
      have h3 : Set.ncard ({C, ConjClasses.mk (⟨i, hi⟩ : ↥Gp),
          ConjClasses.mk (⟨j, hj⟩ : ↥Gp)} : Set (ConjClasses ↥Gp)) = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne]
        rintro (h | h)
        · exact hiC h.symm
        · exact hjC (Set.mem_singleton_iff.mp h).symm
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hconj)
  exact ⟨(c : E), c.2, congrArg Subtype.val hc⟩

variable {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4r_zbar (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3) :
    ∃ x : ↥(M₁ ⊓ M₂), (x : E) ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧ bM β ε x = z ∧
      x ≠ 1 ∧ x * x = 1 := by
  haveI := hyp.amalgam.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz := hyp.z_mem.1 hL3
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
  have hbinj := burnsideF4j_bOne_injective hyp
  have hxO : x ∈ oPPrime 2 (Gp ⊓ M₁) := hxZ.1
  have hxGp : x ∈ Gp := (burnsideF4d_oPPrime_le _ hxO).1
  have hxne : x ≠ 1 := by
    intro h
    apply hyp.z_inv.1
    rw [← hxz]
    have e : (⟨x, hx1⟩ : ↥M₁) = 1 := Subtype.ext h
    rw [e, map_one]
  have hx2 : x * x = 1 := by
    have : burnsideF4d_bOne β ε (⟨x, hx1⟩ * ⟨x, hx1⟩) = burnsideF4d_bOne β ε 1 := by
      rw [map_mul, hxz, map_one]
      exact hyp.z_inv.2
    exact congrArg Subtype.val (hbinj this)
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hSp : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS1 : S ≤ Gp ⊓ M₁ := fun s hs => ⟨(hSB hs).1, (hSB hs).2.1⟩
  have hSO : S ≤ oPPrime 2 (Gp ⊓ M₁) := burnsideF4d_Z1_le_oPPrime hSp hS1
  have hxc : ∀ s ∈ S, s * x = x * s := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp hxZ.2) s (hSO hs)
  have hxN : x ∈ Subgroup.normalizer (S : Set E) := by
    have e : ∀ s ∈ S, x * s * x⁻¹ = s := fun s hs => by
      rw [← hxc s hs, mul_assoc, mul_inv_cancel, mul_one]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [e s hs]
      exact hs
    · intro hs
      have h1 : s = x * (x * s * x⁻¹) * x⁻¹ := by
        rw [hxi]
        calc s = (x * x) * s * (x * x) := by rw [hx2, one_mul, mul_one]
          _ = x * (x * s * x) * x := by simp only [mul_assoc]
      rw [h1, e _ hs]
      exact hs
  have hX : IsPGroup 2 (Subgroup.zpowers x) :=
    CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one, pow_two, hx2])
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set E) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer (S : Set E))).mpr hxN
  have hP : IsPGroup 2 (S ⊔ Subgroup.zpowers x : Subgroup E) :=
    IsPGroup.to_sup_of_normal_left' hSp hX hXN
  have hPG : S ⊔ Subgroup.zpowers x ≤ Gp :=
    sup_le (hSB.trans inf_le_left) ((Subgroup.zpowers_le (H := Gp)).mpr hxGp)
  have hPS := burnsideF4j_eq_of_sylow_le hSyl hP le_sup_left hPG
  have hxS : x ∈ S := by
    rw [← hPS]
    exact (le_sup_right : Subgroup.zpowers x ≤ S ⊔ Subgroup.zpowers x)
      (Subgroup.mem_zpowers x)
  have hxM : x ∈ M₁ ⊓ M₂ := (hSB hxS).2
  refine ⟨⟨x, hxM⟩, ⟨hxS, Subgroup.mem_centralizer_iff.mpr fun s hs => hxc s hs⟩, ?_, ?_, ?_⟩
  · rw [burnsideF4j_bM_eq_bOne]
    exact hxz
  · intro h
    exact hxne (congrArg Subtype.val h)
  · exact Subtype.ext hx2

theorem burnsideF4r_F_4_35_of_nonfused (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3)
    (hSp : κ ≠ .Sp4) {v : ↥(M₁ ⊓ M₂)} (hvS : (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hv1 : v ≠ 1) (hv2 : v * v = 1) (hnc : ¬ IsConj z (bM β ε v))
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1)
    (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.amalgam.finite
  refine ⟨burnsideF4j_F_4_35_forward hyp i j hi hj, fun h => ?_⟩
  obtain ⟨x, hxZ, hxz, hx1, hx2⟩ := burnsideF4r_zbar hyp hL3
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hSGp : ∀ {y : E}, y ∈ S → y ∈ Gp := fun hy =>
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy).1
  have hval1 : ∀ y : ↥(M₁ ⊓ M₂), y ≠ 1 → (y : E) ≠ 1 := fun y hy h => hy (Subtype.ext h)
  have hval2 : ∀ y : ↥(M₁ ⊓ M₂), y * y = 1 → (y : E) * y = 1 := fun y hy =>
    congrArg Subtype.val hy
  have hxL : ∃ g ∈ Gp, g * (x : E) * g⁻¹ ∈ ctr S :=
    ⟨1, Gp.one_mem, by rw [one_mul, inv_one, mul_one]; exact hxZ⟩
  have hsame : ∀ a b : ↥(M₁ ⊓ M₂), (a : E) ∈ S → (b : E) ∈ S → a ≠ 1 → b ≠ 1 →
      a * a = 1 → b * b = 1 →
      ((∃ g ∈ Gp, g * (a : E) * g⁻¹ ∈ ctr S) ↔ (∃ g ∈ Gp, g * (b : E) * g⁻¹ ∈ ctr S)) →
      IsConj (bM β ε a) (bM β ε b) := by
    intro a b ha hb ha1 hb1 ha2 hb2 hab
    exact burnsideF4j_F_4_35_forward hyp a b ha hb
      (burnsideF4r_conj_of_same_type hyp.amalgam hL3 hSp hyp.not_G2d (hSGp ha) (hSGp hb)
        (hval1 a ha1) (hval2 a ha2) (hval1 b hb1) (hval2 b hb2) hab)
  have hxS : (x : E) ∈ S := hxZ.1
  have hvL : ¬ ∃ g ∈ Gp, g * (v : E) * g⁻¹ ∈ ctr S := by
    intro hvL
    apply hnc
    have := hsame x v hxS hvS hx1 hv1 hx2 hv2 ⟨fun _ => hvL, fun _ => hxL⟩
    rwa [hxz] at this
  by_cases hiL : ∃ g ∈ Gp, g * (i : E) * g⁻¹ ∈ ctr S
  · by_cases hjL : ∃ g ∈ Gp, g * (j : E) * g⁻¹ ∈ ctr S
    · exact burnsideF4r_conj_of_same_type hyp.amalgam hL3 hSp hyp.not_G2d (hSGp hi) (hSGp hj)
        (hval1 i hi1) (hval2 i hi2) (hval1 j hj1) (hval2 j hj2) ⟨fun _ => hjL, fun _ => hiL⟩
    · exfalso
      have h1 := hsame x i hxS hi hx1 hi1 hx2 hi2 ⟨fun _ => hiL, fun _ => hxL⟩
      have h2 := hsame j v hj hvS hj1 hv1 hj2 hv2
        ⟨fun h' => absurd h' hjL, fun h' => absurd h' hvL⟩
      rw [hxz] at h1
      exact hnc ((h1.trans h).trans h2)
  · by_cases hjL : ∃ g ∈ Gp, g * (j : E) * g⁻¹ ∈ ctr S
    · exfalso
      have h1 := hsame x j hxS hj hx1 hj1 hx2 hj2 ⟨fun _ => hjL, fun _ => hxL⟩
      have h2 := hsame i v hi hvS hi1 hv1 hi2 hv2
        ⟨fun h' => absurd h' hiL, fun h' => absurd h' hvL⟩
      rw [hxz] at h1
      exact hnc ((h1.trans h.symm).trans h2)
    · exact burnsideF4r_conj_of_same_type hyp.amalgam hL3 hSp hyp.not_G2d (hSGp hi) (hSGp hj)
        (hval1 i hi1) (hval2 i hi2) (hval1 j hj1) (hval2 j hj2)
        ⟨fun h' => absurd h' hiL, fun h' => absurd h' hjL⟩

end Gen

end CFSG.ASVolI
