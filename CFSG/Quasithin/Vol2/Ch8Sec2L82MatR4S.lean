module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Background.HLUCoc24

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Coc24 CFSG.Quasithin.E3
  CFSG.Quasithin.H13

@[expose] def mb4L9 : List ℕ := [2015, 1642, 1113, 1245, 1350, 1359, 1596, 922, 1288]

@[expose] def mb4L2 : List ℕ := [1274, 411, 1855, 13, 74, 1745, 1671, 902, 297]

theorem mb4L9_lt : ∀ a ∈ mb4L9, a < 2 ^ 11 := by decide +kernel

theorem mb4L9_nodup : (combos mb4L9).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

theorem unitA_r4s : ∀ j < 11, (actM trACols (2 ^ j) ^^^ 2 ^ j) ∈ combos mb4L9 := by
  decide +kernel

theorem unitB_r4s : ∀ j < 11, (actM trBCols (2 ^ j) ^^^ 2 ^ j) ∈ combos mb4L9 := by
  decide +kernel

theorem utMem_r4s : ∀ u ∈ uTBasis, u ∈ combos mb4L9 := by decide +kernel

theorem gen9_r4s : ∀ l ∈ mb4L9, (∃ c ∈ [trACols, trBCols], ∃ j < 11,
    l = actM c (2 ^ j) ^^^ 2 ^ j) ∨ l ∈ combos uTBasis := by
  decide +kernel

theorem gen2_r4s : ∀ l ∈ mb4L2, (∃ c ∈ [trACols, trBCols], ∃ b ∈ mb4L9,
    l = actM c b ^^^ b) ∨ l ∈ combos uTBasis := by
  decide +kernel

theorem cover_r4s : ∀ l ∈ mb4L9, l ∈ combos mb4L2 := by decide +kernel

theorem ktTriv_r4s : ∀ i < 6, ∀ b ∈ mb4L9, (actM (ktCols i) b ^^^ b) ∈ combos uTBasis := by
  decide +kernel

theorem maskSub_le_of_combos_r4s {n : ℕ} {L L' : List ℕ} (h : ∀ l ∈ L, l ∈ combos L') :
    maskSub n L ≤ maskSub n L' := by
  rintro _ ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (mem_of_combos (fun m => m ∈ combos L') (zero_mem_combos L')
    (fun a b ha hb => xor_mem_combos L' ha hb) L h m hm)

theorem img11_trQ_closure_r4s :
    img11 trQ = Subgroup.closure ({rhoTrA, rhoTrB} : Set (MulAut W11)) := by
  refine le_antisymm ?_ ?_
  · have key : ∀ σ : Equiv.Perm (Fin 24),
        σ ∈ Subgroup.closure ({trA, trB} : Set (Equiv.Perm (Fin 24))) →
        ∀ h : σ ∈ AutPerm, rho11 AutPerm le_rfl ⟨σ, h⟩ ∈
          Subgroup.closure ({rhoTrA, rhoTrB} : Set (MulAut W11)) := by
      intro σ hσ
      induction hσ using Subgroup.closure_induction with
      | mem x hx =>
        intro h
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      | one =>
        intro h
        have e : (⟨1, h⟩ : ↥AutPerm) = 1 := rfl
        rw [e, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        intro h
        have hx' : x ∈ AutPerm := trQ_le hx
        have hy' : y ∈ AutPerm := trQ_le hy
        have e : (⟨x * y, h⟩ : ↥AutPerm) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
        rw [e, map_mul]
        exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
      | inv x hx ihx =>
        intro h
        have hx' : x ∈ AutPerm := trQ_le hx
        have e : (⟨x⁻¹, h⟩ : ↥AutPerm) = (⟨x, hx'⟩ : ↥AutPerm)⁻¹ := rfl
        rw [e, map_inv]
        exact Subgroup.inv_mem _ (ihx hx')
    rintro _ ⟨y, hy, rfl⟩
    exact key y.1 (Subgroup.mem_subgroupOf.1 hy) y.2
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact rhoTrA_mem
    · exact rhoTrB_mem

theorem std4_commV_sup : commV (img11 trQ) ⊔ UT = maskSub 11 mb4L9 := by
  have hUT : UT ≤ maskSub 11 mb4L9 := maskSub_le_of_combos_r4s utMem_r4s
  refine le_antisymm (sup_le ?_ hUT) ?_
  · have hgen : ∀ g ∈ ({rhoTrA, rhoTrB} : Set (MulAut (Wn 11))), ∃ c, ActsBy g c ∧
        ∀ j < 11, (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos mb4L9 := by
      rintro g (rfl | rfl)
      · exact ⟨trACols, actsBy_rhoTrA, unitA_r4s⟩
      · exact ⟨trBCols, actsBy_rhoTrB, unitB_r4s⟩
    exact (congrArg commV img11_trQ_closure_r4s).le.trans (commV_closure_le_maskSub hgen)
  · have hL9 : ∀ l ∈ mb4L9, (∃ g ∈ ({rhoTrA, rhoTrB} : Set (MulAut (Wn 11))), ∃ c, ActsBy g c ∧
        ∃ j < 11, l = actM c (2 ^ j) ^^^ 2 ^ j) ∨ l ∈ combos uTBasis := by
      intro l hl
      rcases gen9_r4s l hl with ⟨c, hc, j, hj, he⟩ | hU
      · left
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨rhoTrA, Set.mem_insert _ _, _, actsBy_rhoTrA, j, hj, he⟩
        · exact ⟨rhoTrB, Set.mem_insert_of_mem _ rfl, _, actsBy_rhoTrB, j, hj, he⟩
      · exact Or.inr hU
    have h := maskSub_le_commV_sup (n := 11) (S := ({rhoTrA, rhoTrB} : Set (MulAut (Wn 11))))
      (L := mb4L9) (Ub := uTBasis) hL9
    exact h.trans (sup_le_sup_right (congrArg commV img11_trQ_closure_r4s).ge _)

theorem std4_mQuot : mQuot ⊤ (maskSub 11 mb4L9) = 2 :=
  (mQuot_top_maskSub mb4L9_lt mb4L9_nodup).trans rfl

theorem std4_MB1 : s828CommSub (img11 trQ) (maskSub 11 mb4L9) ⊔ UT = maskSub 11 mb4L9 := by
  refine le_antisymm (sup_le ?_ (le_sup_right.trans std4_commV_sup.le)) ?_
  · exact (s828CommSub_le_commV _ _).trans (le_sup_left.trans std4_commV_sup.le)
  · have hL2 : ∀ l ∈ mb4L2, (∃ g ∈ ({rhoTrA, rhoTrB} : Set (MulAut (Wn 11))), ∃ c, ActsBy g c ∧
        ∃ b ∈ mb4L9, l = actM c b ^^^ b) ∨ l ∈ combos uTBasis := by
      intro l hl
      rcases gen2_r4s l hl with ⟨c, hc, b, hb, he⟩ | hU
      · left
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨rhoTrA, Set.mem_insert _ _, _, actsBy_rhoTrA, b, hb, he⟩
        · exact ⟨rhoTrB, Set.mem_insert_of_mem _ rfl, _, actsBy_rhoTrB, b, hb, he⟩
      · exact Or.inr hU
    have h := maskSub_le_commSub_sup_of_cover (n := 11)
      (S := ({rhoTrA, rhoTrB} : Set (MulAut (Wn 11)))) (L := mb4L9) (L2 := mb4L2)
      (Ub := uTBasis) hL2 cover_r4s
    exact h.trans (sup_le_sup_right
      (congrArg (fun Y => s828CommSub Y (maskSub 11 mb4L9)) img11_trQ_closure_r4s).ge _)

theorem le_card_of_ktRho_r4s [Finite (MulAut W11)] (K : Subgroup (MulAut W11))
    (hK : ∀ i < 6, ktRho i ∈ K) : 64 ≤ Nat.card ↥K := by
  have hgen : ∀ g : ℕ, ktRho (g % 6) ∈ K ∧ ActsBy (ktRho (g % 6)) (ktCols (g % 6)) := fun g =>
    ⟨hK _ (Nat.mod_lt _ (by norm_num)), actsBy_ktRho (Nat.mod_lt _ (by norm_num))⟩
  have h := Parab.le_card_of_tree (K := K)
    (fun φ : MulAut W11 => Parab.maskOf 11 (φ (toW 11 1))) ktAct (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      refine ⟨ktRho (g % 6) * φ, Subgroup.mul_mem _ (hgen g).1 hφ, ?_⟩
      have hm := (Parab.maskOf_spec (φ (toW 11 1))).2
      calc Parab.maskOf 11 (ktRho (g % 6) (φ (toW 11 1)))
          = Parab.maskOf 11 (ktRho (g % 6) (toW 11 (Parab.maskOf 11 (φ (toW 11 1))))) := by
            rw [hm]
        _ = ktAct g (Parab.maskOf 11 (φ (toW 11 1))) := by
            rw [(hgen g).2, Parab.maskOf_toW (actM_lt
              (ktCols_lt _ (Nat.mod_lt _ (by norm_num))) _)]
            rfl)
    ⟨1, Subgroup.one_mem _, Parab.maskOf_toW (by norm_num)⟩ ktTree_ok
  rwa [ktTree_length] at h

theorem std4_cent_le_closure
    (hS : Nat.card ↥(img11 AutPerm ⊓ stabSub UT) ≤ 64512) :
    img11 trQ ⊓ centSub UT ≤ Subgroup.closure (Set.range fun i : Fin 6 => ktRho i) := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hC64 := le_card_cent
  have hCK := card_cent_mul_le
  have hQ : 10752 ≤ Nat.card ↥trQ := by
    rw [← card_img11_trQ]
    omega
  have hQc : Nat.card ↥trQ = 10752 := (perfectCore_stabUTP (card_stabUTP.trans_le hS) hQ).2
  have hI : Nat.card ↥(img11 trQ) = 10752 := card_img11_trQ.trans hQc
  have hK64 : Nat.card ↥(img11 trQ ⊓ centSub UT) ≤ 64 := by omega
  have hCle : Subgroup.closure (Set.range fun i : Fin 6 => ktRho i) ≤ img11 trQ ⊓ centSub UT := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨ktRho_mem_img _, ktRho_mem_cent i.isLt⟩
  have hCard := le_card_of_ktRho_r4s (Subgroup.closure (Set.range fun i : Fin 6 => ktRho i))
    (fun i hi => Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩)
  have heq : Subgroup.closure (Set.range fun i : Fin 6 => ktRho i) =
      img11 trQ ⊓ centSub UT :=
    Subgroup.eq_of_le_of_card_ge hCle (by omega)
  exact heq.ge

theorem std4_trivK
    (hS : Nat.card ↥(img11 AutPerm ⊓ stabSub UT) ≤ 64512) :
    ∀ x ∈ img11 trQ ⊓ centSub UT, ∀ b ∈ maskSub 11 mb4L9, x b * b⁻¹ ∈ UT := by
  intro x hx b hb
  have hUB : maskSub 11 uTBasis ≤ maskSub 11 mb4L9 := maskSub_le_of_combos_r4s utMem_r4s
  have hgen : ∀ g ∈ Set.range (fun i : Fin 6 => ktRho i), ∃ c, ActsBy g c ∧
      ∀ b ∈ mb4L9, (actM c b ^^^ b) ∈ combos uTBasis := by
    rintro g ⟨i, rfl⟩
    exact ⟨ktCols (i : ℕ), actsBy_ktRho i.isLt, fun b hb => ktTriv_r4s (i : ℕ) i.isLt b hb⟩
  have hT := closure_le_trivOnAut hUB hgen
  have hC := std4_cent_le_closure hS hx
  exact mem_trivOnAut.1 (hT hC) b hb

end CFSG.Quasithin.H13.Mat
