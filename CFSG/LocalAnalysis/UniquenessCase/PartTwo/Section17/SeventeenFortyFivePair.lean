module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem s17_45_shape_bar2 {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (hl : l = 1)
    (hnU3 : ¬ IsU3 (BarInf L) n) (hN : uc22p20rNativeGriess) :
    IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := by
  have hshape : IsL2 (BarInf L) n ∨ IsSz (BarInf L) n := by
    rcases s17_45_rank_one_shapes ctx.rank hl with h | h | h
    exacts [Or.inl h, Or.inr h, absurd h hnU3]
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
  rcases hshape with hL2 | hSz
  · have hQ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 2 2 n :=
      LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC ctx.mem_calC).some hL2
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 2 n = (1, 1) := by
      have hn1 : 1 ≤ n := hL2.admissible.2.1
      have hodd' : Odd (2 ^ n - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          (even_two.pow_of_ne_zero (by omega)) odd_one
      have hcop : Nat.Coprime 2 (2 ^ n - 1) := Nat.coprime_two_left.mpr hodd'
      show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
      rw [Nat.Coprime.gcd_eq_one hcop]
    have hZ := uc22p20v_center_eq_bot hN ctx.mem_calC.2.2 hodd hQ hg
    exact Or.inl (LieModel.of_mulEquiv (uc22p21k_quotCenter_equiv hZ).some hQ)
  · have hQ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .twistedB2 0 2 n :=
      LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC ctx.mem_calC).some hSz
    have hZ := uc22p20v_center_eq_bot hN ctx.mem_calC.2.2 hodd hQ rfl
    exact Or.inr (LieModel.of_mulEquiv (uc22p21k_quotCenter_equiv hZ).some hQ)

theorem s17_45_pair {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (hl : l = 1)
    (hnU3 : ¬ IsU3 (BarInf L) n) (hN : uc22p20rNativeGriess)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (h44_1 : R17_44_1AtB D V₀ V) (h44_2 : R17_44_2AtB D V₀ V)
    (h44_3 : R17_44_3AtB D V₀ V) (h899 : F08.R899 D) :
    (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∧
      ∃ x ∈ D.M, X = L ⊔ CFSG.Quasithin.conjSubgroup L x ∧ X ≠ L := by
  have hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n :=
    s17_45_shape_bar2 ctx hl hnU3 hN
  have hshapeInf : IsL2 (BarInf L) n ∨ IsSz (BarInf L) n := by
    rcases s17_45_rank_one_shapes ctx.rank hl with h | h | h
    exacts [Or.inl h, Or.inr h, absurd h hnU3]
  have hB : Inputs1719.BorelChevOver (BarInf L) n :=
    ctx.borelChevOver hK3 fun t m h => ⟨by rw [h, hl]; norm_num,
      by rintro ⟨rfl, rfl, -⟩; simp [CS17LieRank] at h; omega⟩
  have hoddC : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
  have hZbot : Subgroup.center (Bar2 L) = ⊥ := by
    rcases hshapeInf with hL2 | hSz
    · have hQ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 2 2 n :=
        LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC ctx.mem_calC).some hL2
      have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 2 n = (1, 1) := by
        have hn1 : 1 ≤ n := hL2.admissible.2.1
        have hodd' : Odd (2 ^ n - 1) :=
          Nat.Even.sub_odd Nat.one_le_two_pow
            (even_two.pow_of_ne_zero (by omega)) odd_one
        have hcop : Nat.Coprime 2 (2 ^ n - 1) := Nat.coprime_two_left.mpr hodd'
        show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
        rw [Nat.Coprime.gcd_eq_one hcop]
      exact uc22p20v_center_eq_bot hN ctx.mem_calC.2.2 hoddC hQ hg
    · have hQ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .twistedB2 0 2 n :=
        LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC ctx.mem_calC).some hSz
      exact uc22p20v_center_eq_bot hN ctx.mem_calC.2.2 hoddC hQ rfl
  have hZnot : ∀ r : ℕ, r.Prime → ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    intro r hr
    rw [hZbot, Subgroup.card_bot]
    exact hr.not_dvd_one
  have hCrank : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
      1 ≤ CFSG.Open.pRank r C := by
    intro r hr hr2 hrdvd
    rcases hshapeInf with hL2 | hSz
    · have hbound := cartanRank_le_pRank_cartan_on hK4 ctx.mem_calC ctx.cartan (by decide) hL2
        hr hr2 hrdvd
        (fun _ hdvd => by
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact hr.ne_one h
          · exact hr2 h)
        (fun h => absurd h (by decide))
      simpa [CS17LieRank] using hbound
    · have hbound := cartanRank_le_pRank_cartan_on hK4 ctx.mem_calC ctx.cartan (by decide) hSz
        hr hr2 hrdvd (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      simpa [CS17LieRank] using hbound
  have hXne : X ≠ L := by
    intro hXL
    apply ctx.counter
    refine Concl17_42.of_p1 ?_
    rw [hXL]
    rcases hshape with h | h
    · exact Or.inl (thin8_of_isL2 h)
    · exact Or.inl (thin8_of_isSz h)
  have hc2 : (conjSetOf D.M L).ncard = 2 := by
    have hpos : 0 < (conjSetOf D.M L).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext y; simp⟩⟩
    have hne1 : (conjSetOf D.M L).ncard ≠ 1 := fun h1 =>
      hXne (ctx.X_eq.trans (uc22s217_conjClosure_eq_of_ncard_eq_one h1))
    rcases Nat.even_or_odd n with hnEven | hnOdd
    · have h3dvd : 3 ∣ 2 ^ n - 1 := by
        obtain ⟨k, rfl⟩ := hnEven
        have h4 : (4 : ℕ) ^ k ≡ 1 [MOD 3] := by
          have h1 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
          simpa using h1.pow k
        have hpow : 2 ^ (k + k) = 4 ^ k := by
          rw [show k + k = 2 * k by ring, pow_mul]
          norm_num
        rw [hpow]
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow k 4 (by norm_num))).mp h4.symm
      have hle : Gamma.ncard ≤ 2 :=
        (ctx.ncard_le_pRank_Dc Nat.prime_three (by norm_num) (hZnot 3 Nat.prime_three)
          (hCrank 3 Nat.prime_three (by norm_num) h3dvd)).trans
          ((h44_3 L X p n l C Dc Gamma ctx n hB).1)
      have hle' : (conjSetOf D.M L).ncard ≤ 2 := by
        rw [← ctx.ncard_Gamma_eq_card_conjSet]
        exact hle
      omega
    · have hn3 : 3 ≤ n := by
        rcases hshapeInf with hL2 | hSz
        · have h2 := s13_two_le_of_isL2 hL2
          obtain ⟨k, hk⟩ := hnOdd
          omega
        · exact CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
      obtain ⟨r, hr, hrdvd⟩ := s13_exists_prime_dvd (show 1 < n by omega)
      have hr7 : 7 ≤ r := s13_seven_le_of_dvd hnOdd hr hrdvd
      have hr2 : r ≠ 2 := by omega
      have hCr : 1 ≤ CFSG.Open.pRank r C := hCrank r hr hr2 hrdvd
      have hle3 : Gamma.ncard ≤ 3 :=
        (ctx.ncard_le_pRank_Dc hr hr2 (hZnot r hr) hCr).trans
          (h44_1 L X p n l C Dc Gamma ctx n hB r hr hr2)
      have hle3' : (conjSetOf D.M L).ncard ≤ 3 := by
        rw [← ctx.ncard_Gamma_eq_card_conjSet]
        exact hle3
      by_contra hne2
      have hconj3 : (conjSetOf D.M L).ncard = 3 := by omega
      obtain ⟨x1, x2, x3, h12, h13, h23, hset3⟩ := Set.ncard_eq_three.mp hconj3
      let Lf : Fin 3 → Subgroup G := fun i =>
        if (i : ℕ) = 0 then x1 else if (i : ℕ) = 1 then x2 else x3
      have hmem : ∀ i, Lf i ∈ conjSetOf D.M L := by
        intro i
        have hi : Lf i = x1 ∨ Lf i = x2 ∨ Lf i = x3 := by
          fin_cases i <;> simp [Lf]
        rw [hset3]
        rcases hi with h | h | h <;> rw [h] <;> simp
      have hrange3 : Set.range Lf = ({x1, x2, x3} : Set (Subgroup G)) := by
        ext K
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp [Lf]
        · intro hK
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
          rcases hK with rfl | rfl | rfl
          exacts [⟨0, by simp [Lf]⟩, ⟨1, by simp [Lf]⟩, ⟨2, by simp [Lf]⟩]
      have hrange : Set.range Lf =
          {N | ∃ m ∈ D.M, N = (Lf 0).map (MulAut.conj m).toMonoidHom} := by
        have h0 : Lf 0 ∈ conjSetOf D.M L := hmem 0
        rw [hrange3, ← hset3]
        exact (uc22p2214_conjSetOf_eq h0).symm
      have hinj : Function.Injective Lf := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [Lf]
      have hcalC : ∀ i, Lf i ∈ calC D.M := fun i =>
        uc22p2214_calC_of_mem_conjSetOf ctx.mem_calC (hmem i)
      have hshapes : ∀ i, IsSz (Bar2 (Lf i)) n ∨ IsL2 (Bar2 (Lf i)) n := by
        intro i
        obtain ⟨g, -, hEq⟩ := hmem i
        have hLi : IsL2 (Bar2 (Lf i)) n ∨ IsSz (Bar2 (Lf i)) n := by
          rcases hshape with hL2 | hSz
          · exact Or.inl (hEq ▸ LieModel.of_mulEquiv (uc22p20d_bar2_conj g L).some hL2)
          · exact Or.inr (hEq ▸ LieModel.of_mulEquiv (uc22p20d_bar2_conj g L).some hSz)
        exact hLi.symm
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
        h899 Lf (fun _ => n) n r hinj hcalC hshapes hnOdd
          (fun _ => dvd_refl n) hr hrdvd (Or.inl hrange)
      have hle2 : Gamma.ncard ≤ 2 :=
        (ctx.ncard_le_pRank_Dc hr hr2 (hZnot r hr) hCr).trans
          (h44_2 L X p n l C Dc Gamma ctx n hB r hr (by omega) (Or.inr hstr))
      have hle2' : (conjSetOf D.M L).ncard ≤ 2 := by
        rw [← ctx.ncard_Gamma_eq_card_conjSet]
        exact hle2
      omega
  refine ⟨hshape, ?_⟩
  obtain ⟨a, b, -, hset2⟩ := Set.ncard_eq_two.mp hc2
  have hLmem : L ∈ conjSetOf D.M L := ⟨1, D.M.one_mem, by ext y; simp⟩
  have hLa : L = a ∨ L = b := by
    have h : L ∈ ({a, b} : Set (Subgroup G)) := by rw [← hset2]; exact hLmem
    simpa using h
  rcases hLa with hLa | hLb
  · have hset' : conjSetOf D.M L = {L, b} := by rw [hset2, ← hLa]
    obtain ⟨m, hm, hbm⟩ := show b ∈ conjSetOf D.M L by rw [hset']; simp
    refine ⟨m⁻¹, D.M.inv_mem hm, ?_, hXne⟩
    have hx : CFSG.Quasithin.conjSubgroup L m⁻¹ = b := by
      rw [hbm]
      simp [CFSG.Quasithin.conjSubgroup]
    have hsup : (⨆ K ∈ ({L, b} : Set (Subgroup G)), K) = L ⊔ b := by
      refine le_antisymm ?_ ?_
      · refine iSup_le fun K => iSup_le fun hK => ?_
        rcases hK with rfl | rfl
        exacts [le_sup_left, le_sup_right]
      · exact sup_le (le_iSup₂_of_le L (by simp) le_rfl)
          (le_iSup₂_of_le b (by simp) le_rfl)
    rw [ctx.X_eq, hx]
    unfold conjClosure
    rw [hset']
    exact hsup
  · have hset' : conjSetOf D.M L = {a, L} := by rw [hset2, ← hLb]
    obtain ⟨m, hm, ham⟩ := show a ∈ conjSetOf D.M L by rw [hset']; simp
    refine ⟨m⁻¹, D.M.inv_mem hm, ?_, hXne⟩
    have hx : CFSG.Quasithin.conjSubgroup L m⁻¹ = a := by
      rw [ham]
      simp [CFSG.Quasithin.conjSubgroup]
    have hsup : (⨆ K ∈ ({a, L} : Set (Subgroup G)), K) = L ⊔ a := by
      refine le_antisymm ?_ ?_
      · refine iSup_le fun K => iSup_le fun hK => ?_
        rcases hK with rfl | rfl
        exacts [le_sup_right, le_sup_left]
      · exact sup_le (le_iSup₂_of_le L (by simp) le_rfl)
          (le_iSup₂_of_le a (by simp) le_rfl)
    rw [ctx.X_eq, hx]
    unfold conjClosure
    rw [hset']
    exact hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
