module

public import CFSG.Quasithin.Background.E1TwoAbs

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isTwoClosed_subgroupOf {R J : Subgroup G} (hRJ : R ≤ J) (h : IsTwoClosed R) :
    IsTwoClosed (R.subgroupOf J) := by
  obtain ⟨P, hP, hn⟩ := h
  refine ⟨P.subgroupOf J, (isSylowIn_subgroupOf_iff (hP.le.trans hRJ) hRJ).mpr hP, ?_⟩
  have hRn : R ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP.le).mp hn
  have hle : P.subgroupOf J ≤ R.subgroupOf J := fun x hx => hP.le hx
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := Subgroup.mem_normalizer_iff.mp (hRn hx) (y : G)
  simpa [Subgroup.mem_subgroupOf] using this

section Main

variable [Finite G]

theorem ten_seven_eTwo {T A Y : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) {i : ℕ} {I : Subgroup (G ⧸ Y)}
    (hI : IsE i ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) I)
    (hE : ETwo ↥I ((T.map (QuotientGroup.mk' Y) ⊓ I).subgroupOf I)
        ((A.map (QuotientGroup.mk' Y)).subgroupOf I) ∧
      Nat.card (barRad ↥I ((A.map (QuotientGroup.mk' Y)).subgroupOf I)) ≤ 2 ^ i) :
    ∃ J : Subgroup G, IsE i ⊤ T A J ∧
      twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hI' := hI
  obtain ⟨-, hIτ, hIS, -⟩ := hI
  set Tb : Subgroup (G ⧸ Y) := T.map π with hTb
  set Ab : Subgroup (G ⧸ Y) := A.map π with hAb
  have hTb' : IsSylowIn 2 Tb ⊤ := isSylowIn_two_map_top hπs hT
  have hAbT : Ab ≤ Tb := Subgroup.map_mono hA
  have hAbab : IsElemAbelian 2 Ab := isElemAbelian_map' π hAab
  have hAbI : Ab ≤ I := by
    have h1 : Ab ⊔ pCoreOf 2 ⊤ ≤ tauOf ⊤ Tb Ab := le_tauOf hTb' hAbT hAbab
    exact (le_sup_left.trans (h1.trans hIτ)).trans inf_le_right
  set H1 : Subgroup G := I.comap π with hH1
  set T1 : Subgroup G := T ⊓ H1 with hT1
  have hYH1 : Y ≤ H1 := fun y hy => by
    show π y ∈ I
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [h1]
    exact Subgroup.one_mem _
  have hmapH1 : H1.map π = I := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hT1H1 : T1 ≤ H1 := inf_le_right
  have hπT1 : T1.map π = Tb ⊓ I := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ ht.1, ht.2⟩
    · rintro _ ⟨⟨t, ht, rfl⟩, h2⟩
      exact ⟨t, ⟨ht, h2⟩, rfl⟩
  have hSyl1 : IsSylowIn 2 T1 H1 := by
    have hidx : ¬ 2 ∣ T.index := by
      have := hT.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this
    let C : Sylow 2 G := hT.isPGroup.toSylow hidx
    have hC : (C : Subgroup G) = T := rfl
    have := isSylowIn_inf_of_quotient Y hYH1 C (by rw [hC, hmapH1]; exact hIS)
    rwa [hC] at this
  have hT1' : IsPGroup 2 T1 := hSyl1.isPGroup
  have hτT1 : tauOf ⊤ T A ≤ T1 := by
    intro t ht
    refine ⟨tauOf_le _ _ _ ht, ?_⟩
    have h1 : (tauOf ⊤ T A).map π ≤ tauOf ⊤ Tb Ab := by
      have := tauOf_map_le π (A := A) (le_top : T ≤ ⊤)
      rwa [Subgroup.map_top_of_surjective π hπs] at this
    exact (hIτ (h1 (Subgroup.mem_map_of_mem π ht))).2
  have hAT1 : A ≤ T1 := fun a ha => hτT1 (le_tauOf hT hA hAab (Subgroup.mem_sup_left ha))
  obtain ⟨J, hJmin⟩ := (Set.toFinite {K' : Subgroup G | K' ≤ H1 ⊔ T1 ∧ T1 ≤ K' ∧
      H1 ⊔ T1 = K' ⊔ Y}).exists_minimal ⟨H1 ⊔ T1, le_rfl, le_sup_right,
      (sup_eq_left.mpr (hYH1.trans le_sup_left)).symm⟩
  have hJ : J ∈ sFamily T1 H1 Y :=
    ⟨hJmin.prop.1, hJmin.prop.2.1, hJmin.prop.2.2,
      fun K' h1 h2 h3 h4 => hJmin.eq_of_le ⟨h1, h2, h3⟩ h4⟩
  obtain ⟨hJle, hT1J, hEq, hmin⟩ := hJ
  have hH1T1 : H1 ⊔ T1 = H1 := sup_eq_left.mpr hT1H1
  have hJH1 : J ≤ H1 := hH1T1 ▸ hJle
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hYbot : Y.map π = ⊥ := (Subgroup.map_eq_bot_iff Y).mpr hker.ge
  have hπJ : J.map π = I := by
    have h2 : (J ⊔ Y).map π = J.map π := by rw [Subgroup.map_sup, hYbot, sup_bot_eq]
    calc J.map π = (J ⊔ Y).map π := h2.symm
      _ = (H1 ⊔ T1).map π := by rw [hEq]
      _ = I := by rw [hH1T1, hmapH1]
  have hTJ : T ⊓ J = T1 := by
    refine le_antisymm (le_inf inf_le_left (inf_le_right.trans hJH1)) (le_inf inf_le_left hT1J)
  have hSylJ : IsSylowIn 2 T1 J := B6.isSylowTwoOf_mono hSyl1 hT1J hJH1
  have hAJ : A ≤ J := hAT1.trans hT1J
  have hτJ : tauOf ⊤ T A ≤ T ⊓ J := le_inf (tauOf_le _ _ _) (hτT1.trans hT1J)
  have hmem : ∀ j : ↥J, π (j : G) ∈ I := fun j => hJH1 j.2
  let φ : ↥J →* ↥I := (π.comp J.subtype).codRestrict I hmem
  have hφval : ∀ j : ↥J, ((φ j : ↥I) : G ⧸ Y) = π (j : G) := fun j => rfl
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : G ⧸ Y) ∈ J.map π := by
      rw [hπJ]
      exact y.2
    obtain ⟨j, hj, hjy⟩ := hy
    exact ⟨⟨j, hj⟩, Subtype.ext hjy⟩
  have hkerY : ∀ j : ↥J, φ j = 1 → (j : G) ∈ Y := fun j hj => by
    have h1 : π (j : G) = 1 := congrArg Subtype.val hj
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hZeq : (CFSG.Open.pCore 2 ↥I).comap φ = (preO2 J Y).subgroupOf J := by
    ext j
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    unfold preO2
    rw [Subgroup.mem_inf, Subgroup.mem_comap, hπJ]
    simp only [j.2, true_and]
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem I.subtype_injective).symm
  have hZ : IsTwoClosed ((CFSG.Open.pCore 2 ↥I).comap φ) := by
    rw [hZeq]
    exact isTwoClosed_subgroupOf inf_le_left
      (ten_two hSyl1 le_rfl (⟨hJle, hT1J, hEq, hmin⟩ : J ∈ sFamily T1 H1 Y))
  have hkersolv := isSolvable_ker_of_isTwoClosed φ hZ
  set S : Subgroup ↥J := (T ⊓ J).subgroupOf J with hS
  set B : Subgroup ↥J := A.subgroupOf J with hB
  have hSylS : IsSylowIn 2 S ⊤ := by
    have := (isSylowIn_subgroupOf_iff (P := T1) (K := J) (H := J) hT1J le_rfl).mpr hSylJ
    rw [Subgroup.subgroupOf_self] at this
    rw [hS, hTJ]
    exact this
  have hS2 : IsPGroup 2 S := hSylS.isPGroup
  have hBS : B ≤ S := fun x hx => ⟨hA hx, x.2⟩
  have hSmap : S.map φ = (Tb ⊓ I).subgroupOf I := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem π hs.1, (φ s).2⟩
    · intro hy
      have hy' : (y : G ⧸ Y) ∈ T1.map π := by
        rw [hπT1]
        exact hy
      obtain ⟨t, ht, hty⟩ := hy'
      have htJ : t ∈ J := hT1J ht
      exact ⟨⟨t, htJ⟩, ⟨ht.1, htJ⟩, Subtype.ext hty⟩
  have hBmap : B.map φ = Ab.subgroupOf I := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_map_of_mem π ha
    · intro hy
      obtain ⟨a, ha, hay⟩ := hy
      exact ⟨⟨a, hAJ ha⟩, ha, Subtype.ext hay⟩
  have hres' : twoResidual (⊤ : Subgroup ↥I) = perfectCore (⊤ : Subgroup ↥I) := hE.1.2.2.1
  have hmin' : ∀ M : Subgroup ↥J, S ≤ M → M ⊔ φ.ker = ⊤ → M = ⊤ := by
    intro M hSM hMk
    set M' : Subgroup G := M.map J.subtype with hM'
    have hM'J : M' ≤ J := Subgroup.map_subtype_le M
    have hT1M' : T1 ≤ M' := fun t ht =>
      ⟨⟨t, hT1J ht⟩, hSM (show t ∈ T ⊓ J from ⟨ht.1, hT1J ht⟩), rfl⟩
    have hJM : J ≤ M' ⊔ Y := by
      intro j hj
      have hjt : (⟨j, hj⟩ : ↥J) ∈ (↑(M ⊔ φ.ker) : Set ↥J) := by
        rw [hMk]
        exact Subgroup.mem_top _
      rw [Subgroup.coe_mul_of_left_le_normalizer_right M φ.ker (fun x _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top x)] at hjt
      obtain ⟨m, hm, k, hk, hmk⟩ := hjt
      have hjmk : j = (m : G) * (k : G) := congrArg Subtype.val hmk.symm
      rw [hjmk]
      exact Subgroup.mul_mem_sup ⟨m, hm, rfl⟩ (hkerY k hk)
    have hEqM : H1 ⊔ T1 = M' ⊔ Y := by
      refine le_antisymm ?_ ?_
      · rw [hEq]
        exact sup_le hJM le_sup_right
      · exact sup_le (hM'J.trans hJle) (hYH1.trans le_sup_left)
    have hMJ : M' = J := hmin M' (hM'J.trans hJle) hT1M' hEqM hM'J
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : G) ∈ M' := by
      rw [hMJ]
      exact x.2
    obtain ⟨m, hm, hmx⟩ := hx
    have : m = x := Subtype.ext hmx
    exact this ▸ hm
  have hres : twoResidual (⊤ : Subgroup ↥J) = perfectCore (⊤ : Subgroup ↥J) :=
    twoResidual_eq_perfectCore_of_surjective φ hφ hSylS hmin' hres'
  have hETwo : ETwo ↥J S B :=
    eTwo_of_surjective φ hφ hZ hS2 hBS hres (by rw [hSmap, hBmap]; exact hE.1)
  have hcard : Nat.card (barRad ↥J B) ≤ 2 ^ i := by
    have := card_barRad_eq_of_surjective φ hφ hkersolv B
    rw [hBmap] at this
    rw [← this]
    exact hE.2
  refine ⟨J, ⟨le_top, hτJ, ?_, Or.inr ⟨hETwo, hcard⟩⟩, ?_⟩
  · rw [hTJ]
    exact hSylJ
  · rw [map_twoResidual π J, hπJ]

theorem ten_seven {T A Y : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) {i : ℕ} {I : Subgroup (G ⧸ Y)}
    (hI : IsE i ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) I) :
    ∃ J : Subgroup G, IsE i ⊤ T A J ∧
      twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y) := by
  rcases hI.2.2.2 with hE | hE
  · exact ten_seven_eOne hT hA hAab hI hE
  · exact ten_seven_eTwo hT hA hAab hI hE

end Main

end E1

end CFSG.Quasithin
