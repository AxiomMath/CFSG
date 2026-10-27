module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagProd
public import CFSG.LocalAnalysis.StandardType.PhanEFlagA2A1

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] def _root_.CFSG.ClassicalInvolution.Phan.PhanE.PhanCode.diam : PhanCode → ℕ
  | .a1far | .a1moved => 1
  | .a2chamber | .a2panel | .a2coll | .a2pol => 3
  | .a3_1111 | .a3_211 | .a3_121 | .a3_22p | .a3_22x | .a3_13c | .a3_13p | .a3_4c | .a3_4p => 6
  | .exchA1A1 => 2
  | .exchA2A1 => 4
  | .prod c c' => c.diam + c'.diam

@[expose] noncomputable def _root_.CFSG.ClassicalInvolution.Phan.PhanE.PhanCode.R0 :
    (c : PhanCode) → Set (c.Ω K)
  | .a1far => refSet K 2 [0, 1, 2]
  | .a1moved => refSet K 2 [0, 2]
  | .a2chamber => refSet K 3 [0, 1, 2, 3]
  | .a2panel => refSet K 3 [0, 1, 3]
  | .a2coll => refSet K 3 [0, 3]
  | .a2pol => refSet K 3 [0, 3]
  | .a3_1111 => refSet K 4 [0, 1, 2, 3, 4]
  | .a3_211 => refSet K 4 [0, 2, 3, 4]
  | .a3_121 => refSet K 4 [0, 1, 3, 4]
  | .a3_22p => refSet K 4 [0, 2, 4]
  | .a3_22x => refSet K 4 [0, 2, 4]
  | .a3_13c => refSet K 4 [0, 1, 4]
  | .a3_13p => refSet K 4 [0, 1, 4]
  | .a3_4c => refSet K 4 [0, 4]
  | .a3_4p => refSet K 4 [0, 4]
  | .exchA1A1 => Set.univ
  | .exchA2A1 => {c | c.1 ∈ refSet K 3 [0, 1, 3]}
  | .prod c c' => c.R0 ×ˢ c'.R0

@[expose] noncomputable def _root_.CFSG.ClassicalInvolution.Phan.PhanE.PhanCode.psi
    (hK : Nat.card K = (2 ^ f) ^ 2) : (c : PhanCode) → c.Ω K → c.Ω K
  | .a1far => flagPsi' K f hK 2 [0, 1, 2] []
  | .a1moved => flagPsi' K f hK 2 [0, 2] [false]
  | .a2chamber => flagPsi' K f hK 3 [0, 1, 2, 3] []
  | .a2panel => flagPsi' K f hK 3 [0, 1, 3] []
  | .a2coll => flagPsi' K f hK 3 [0, 3] [false]
  | .a2pol => flagPsi' K f hK 3 [0, 3] [true]
  | .a3_1111 => flagPsi' K f hK 4 [0, 1, 2, 3, 4] []
  | .a3_211 => flagPsi' K f hK 4 [0, 2, 3, 4] []
  | .a3_121 => flagPsi' K f hK 4 [0, 1, 3, 4] []
  | .a3_22p => flagPsi' K f hK 4 [0, 2, 4] []
  | .a3_22x => flagPsiX hK
  | .a3_13c => flagPsi' K f hK 4 [0, 1, 4] []
  | .a3_13p => flagPsi' K f hK 4 [0, 1, 4] [false, true]
  | .a3_4c => flagPsi' K f hK 4 [0, 4] [false]
  | .a3_4p => flagPsi' K f hK 4 [0, 4] [true]
  | .exchA1A1 => psiA1A1 hK
  | .exchA2A1 => psiA2A1 hK
  | .prod c c' => Prod.map (c.psi hK) (c'.psi hK)

variable {K f}

theorem q2cFCo_isCut_012 : IsCut 2 [0, 1, 2] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 2 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_02 : IsCut 2 [0, 2] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 1 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_0123 : IsCut 3 [0, 1, 2, 3] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 3 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_013 : IsCut 3 [0, 1, 3] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 2 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_03 : IsCut 3 [0, 3] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 1 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_01234 : IsCut 4 [0, 1, 2, 3, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 4 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_0234 : IsCut 4 [0, 2, 3, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 3 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_0134 : IsCut 4 [0, 1, 3, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 3 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_024 : IsCut 4 [0, 2, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 2 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_014 : IsCut 4 [0, 1, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 2 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

theorem q2cFCo_isCut_04 : IsCut 4 [0, 4] := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  have hi' : i < 1 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> decide

private theorem q2cFCo_flagPsi'_eq (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} {d : List ℕ}
    (hd : IsCut n d) (pol : List Bool) :
    flagPsi' K f hK n d pol = flagPsi hK hd pol := by
  funext x
  unfold flagPsi'
  rw [dif_pos hd]

private theorem q2cFCo_prod_isGallery_inl {I J : Type} {C D : Type}
    {X : ChamberSystem I C} {Y : ChamberSystem J D} {x : C × D} {γ : List (I × C)}
    (hγ : X.IsGallery x.1 γ) :
    (X.prod Y).IsGallery x (γ.map fun p => ((Sum.inl p.1 : I ⊕ J), (p.2, x.2))) ∧
      galleryEnd x (γ.map fun p => ((Sum.inl p.1 : I ⊕ J), (p.2, x.2))) =
        (galleryEnd x.1 γ, x.2) := by
  induction γ generalizing x with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨ihg, ihe⟩ := ih (x := (p.2, x.2)) h2
    exact ⟨⟨⟨h1, rfl⟩, ihg⟩, by simpa using ihe⟩

private theorem q2cFCo_prod_isGallery_inr {I J : Type} {C D : Type}
    {X : ChamberSystem I C} {Y : ChamberSystem J D} {x : C × D} {γ : List (J × D)}
    (hγ : Y.IsGallery x.2 γ) :
    (X.prod Y).IsGallery x (γ.map fun p => ((Sum.inr p.1 : I ⊕ J), (x.1, p.2))) ∧
      galleryEnd x (γ.map fun p => ((Sum.inr p.1 : I ⊕ J), (x.1, p.2))) =
        (x.1, galleryEnd x.2 γ) := by
  induction γ generalizing x with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨ihg, ihe⟩ := ih (x := (x.1, p.2)) h2
    exact ⟨⟨⟨rfl, h1⟩, ihg⟩, by simpa using ihe⟩

theorem q2cFCo_prod_connected {I J : Type} {C D : Type}
    {X : ChamberSystem I C} {Y : ChamberSystem J D} (hX : X.Connected) (hY : Y.Connected) :
    (X.prod Y).Connected := by
  intro a b
  obtain ⟨α, hα, heα⟩ := hX a.1 b.1
  obtain ⟨β, hβ, heβ⟩ := hY a.2 b.2
  refine ⟨α.map (fun p => (Sum.inl p.1, (p.2, a.2))) ++
      β.map (fun p => (Sum.inr p.1, (b.1, p.2))), ?_, ?_⟩
  · refine (ChamberSystem.isGallery_append (X := X.prod Y) a _ _).mpr
      ⟨(q2cFCo_prod_isGallery_inl (X := X) (Y := Y) hα).1, ?_⟩
    rw [(q2cFCo_prod_isGallery_inl (X := X) (Y := Y) hα).2, heα]
    exact (q2cFCo_prod_isGallery_inr (X := X) (Y := Y) (x := (b.1, a.2)) hβ).1
  · rw [galleryEnd_append, (q2cFCo_prod_isGallery_inl (X := X) (Y := Y) hα).2, heα,
      (q2cFCo_prod_isGallery_inr (X := X) (Y := Y) (x := (b.1, a.2)) hβ).2, heβ]

theorem q2cFCo_flagSg_stdFlag (hK : Nat.card K = (2 ^ f) ^ 2) (n : ℕ) :
    flagSg hK (stdFlag K n) = stdFlag K n := by
  apply FlagK.ext
  intro j
  rw [flagSg_E]
  exact sgS_Vsub j

theorem q2cFCo_adj_flagSys_one (x y : FlagK K 2) (i : Fin 1) :
    (flagSys K 1).adj i x y := by
  intro j hj
  have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hj' : j ≠ 1 := by simpa [hi] using hj
  rcases lt_or_ge j 2 with h | h
  · interval_cases j
    · rw [FlagK.E_zero, FlagK.E_zero]
    · exact absurd rfl hj'
  · rw [x.top j h, y.top j h]

theorem q2cFCo_adj_refSet_013 (x y : FlagK K 3) (hx : x ∈ refSet K 3 [0, 1, 3])
    (hy : y ∈ refSet K 3 [0, 1, 3]) : (flagSys K 2).adj 1 x y := by
  intro j hj
  rcases lt_or_ge j 3 with h | h
  · interval_cases j
    · rw [FlagK.E_zero, FlagK.E_zero]
    · simpa using (hx 1 (by decide)).trans (hy 1 (by decide)).symm
    · exact absurd rfl hj
  · rw [x.top j h, y.top j h]

theorem q2cFCo_cdist_eq_one_of_adj {m : ℕ} {i : Fin m} {x y : FlagK K (m + 1)}
    (hne : x ≠ y) (hadj : (flagSys K m).adj i x y) :
    cdist (flagSys K m) x y = 1 := by
  rw [← length_flagδ_eq_cdist]
  rw [(flagδ_eq_simple_iff x y i).mpr ⟨hne, hadj⟩]
  exact (symCox m).length_simple i

theorem q2cFCo_cdist_le_one_of_adj {m : ℕ} {i : Fin m} {x y : FlagK K (m + 1)}
    (hadj : (flagSys K m).adj i x y) : cdist (flagSys K m) x y ≤ 1 := by
  rcases eq_or_ne x y with rfl | hne
  · rw [cdist_self]; omega
  · rw [q2cFCo_cdist_eq_one_of_adj hne hadj]

theorem q2cFCo_intrSet_block (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (m : ℕ) (hm : m + 1 ≤ 4) (d : List ℕ) (hd : IsCut (m + 1) d) (pol : List Bool) (D : ℕ)
    (hD : (m + 1) * m / 2 = D) :
    IntrSet (flagSys K m) (refSet K (m + 1) d) (flagPsi' K f hK (m + 1) d pol) D =
      genSet K f (m + 1) d pol := by
  rw [q2cFCo_flagPsi'_eq hK hd pol, ← hD]
  exact intrSet_flagSys_eq_genSet hK hq hm hd pol

theorem q2cFCo_exists_diam_psi_block (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (m : ℕ) (hm : m + 1 ≤ 4) (d : List ℕ) (hd : IsCut (m + 1) d) (pol : List Bool) :
    ∃ x ∈ refSet K (m + 1) d, ∀ y ∈ refSet K (m + 1) d, ∀ z ∈ refSet K (m + 1) d,
      cdist (flagSys K m) y z ≤ cdist (flagSys K m) x (flagPsi' K f hK (m + 1) d pol x) := by
  rw [q2cFCo_flagPsi'_eq hK hd pol]
  obtain ⟨x, hx, hxlong⟩ := exists_opp_flagPsi (K := K) (f := f) hK hq hm hd pol
  refine ⟨x, hx, fun y hy z hz => ?_⟩
  calc cdist (flagSys K m) y z
      = (symCox m).length (flagδ m y z) := (length_flagδ_eq_cdist m y z).symm
    _ ≤ (symCox m).length (longest (symCox m) (cutTypes m d)) :=
        (isLongest_longest (cutTypes m d)).2 _
          (flagδ_mem_parabolic_of_mem_refSet hd hy hz)
    _ = cdist (flagSys K m) x (flagPsi hK hd pol x) := by
        rw [← hxlong, length_flagδ_eq_cdist]

theorem q2cFCo_exists_cdist_eq_diam_flag (m : ℕ) :
    ∃ x y : FlagK K (m + 1), cdist (flagSys K m) x y = (m + 1) * m / 2 := by
  obtain ⟨F, hF⟩ := exists_opp (stdFlag K (m + 1))
  refine ⟨stdFlag K (m + 1), F, ?_⟩
  rw [← length_flagδ_eq_cdist]
  exact (opp_iff_length_flagδ _ _).mp hF

theorem q2cFCo_exists_cdist_eq_diam_exchA1A1 :
    ∃ x y : FlagK K 2 × FlagK K 2,
      cdist ((flagSys K 1).prod (flagSys K 1)) x y = 2 := by
  obtain ⟨F, hF⟩ := exists_opp (stdFlag K 2)
  refine ⟨(stdFlag K 2, stdFlag K 2), (F, F), ?_⟩
  rw [cdist_prod (flagSys_connected K 1) (flagSys_connected K 1)]
  have h1 : cdist (flagSys K 1) (stdFlag K 2) F = 1 := by
    rw [← length_flagδ_eq_cdist]
    exact (opp_iff_length_flagδ _ _).mp hF
  rw [h1]

theorem q2cFCo_exists_cdist_eq_diam_exchA2A1 :
    ∃ x y : FlagK K 3 × FlagK K 2,
      cdist ((flagSys K 2).prod (flagSys K 1)) x y = 4 := by
  obtain ⟨F, hF⟩ := exists_opp (stdFlag K 3)
  obtain ⟨G, hG⟩ := exists_opp (stdFlag K 2)
  refine ⟨(stdFlag K 3, stdFlag K 2), (F, G), ?_⟩
  rw [cdist_prod (flagSys_connected K 2) (flagSys_connected K 1)]
  have h1 : cdist (flagSys K 2) (stdFlag K 3) F = 3 := by
    rw [← length_flagδ_eq_cdist]
    exact (opp_iff_length_flagδ _ _).mp hF
  have h2 : cdist (flagSys K 1) (stdFlag K 2) G = 1 := by
    rw [← length_flagδ_eq_cdist]
    exact (opp_iff_length_flagδ _ _).mp hG
  rw [h1, h2]

theorem q2cFCo_Vsub3_ne_sup (L : Submodule K (Fin 2 → K)) (hLdim : finrank K L = 1)
    (hLne : L ≠ Vsub (K := K) 2 1) :
    Vsub (K := K) 3 2 ≠ Vsub (K := K) 3 1 ⊔
      Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K))) := by
  intro heq
  have hnotle : ¬ (L ≤ Vsub (K := K) 2 1) := by
    intro hle
    apply hLne
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [finrank_Vsub (K := K) (n := 2) (c := 1) (by norm_num), hLdim]
  have hnotle' : ¬ (∀ x, x ∈ L → x ∈ Vsub (K := K) 2 1) := hnotle
  obtain ⟨v, hv⟩ := not_forall.mp hnotle'
  obtain ⟨hvL, hvV⟩ := not_imp.mp hv
  have hv1 : v 1 ≠ 0 := by
    intro h0
    exact hvV (by
      intro j hj
      fin_cases j
      · simp at hj
      · exact h0)
  have hjv : jShift21 K f v ∉ Vsub (K := K) 3 2 := by
    intro hmem
    have h2 : jShift21 K f v 2 = 0 := hmem 2 (by norm_num)
    have hval : jShift21 K f v 2 = sg K f (v 1) := by simp [jShift21]
    rw [hval] at h2
    exact hv1 ((sg K f).map_eq_zero_iff.mp h2)
  have hmemspan : jShift21 K f v ∈
      Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K))) :=
    Submodule.subset_span ⟨v, hvL, rfl⟩
  have hle : Submodule.span K (jShift21 K f '' (L : Set (Fin 2 → K))) ≤
      Vsub (K := K) 3 2 := by
    rw [heq]
    exact le_sup_right
  exact hjv (hle hmemspan)

theorem q2cFCo_span_jShift21Inv_le :
    Submodule.span K (jShift21Inv K f '' (Vsub (K := K) 3 2 : Set (Fin 3 → K))) ≤
      Vsub (K := K) 2 1 := by
  rw [Submodule.span_le]
  rintro w ⟨v, hv, rfl⟩
  intro j hj
  have hv2 : v 2 = 0 := hv 2 (by norm_num)
  fin_cases j
  · simp at hj
  · simp [jShift21Inv, hv2]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
