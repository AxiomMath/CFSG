module

public import CFSG.Quasithin.Background.HLUCoc24

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc

def ktGenSet : Set (MulAut W11) := {φ | ∃ i < 6, φ = ktRho i}

def ktSub : Subgroup (MulAut W11) := Subgroup.closure ktGenSet

theorem ktSub_le : ktSub ≤ img11 trQ ⊓ centSub UT := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨ktRho_mem_img i, ktRho_mem_cent hi⟩

theorem ktSub_card_ge [Finite (MulAut W11)] : 64 ≤ Nat.card ↥ktSub := by
  have hgen : ∀ g : ℕ, ktRho (g % 6) ∈ ktSub := fun g =>
    Subgroup.subset_closure ⟨g % 6, Nat.mod_lt _ (by norm_num), rfl⟩
  have hact : ∀ g : ℕ, ActsBy (ktRho (g % 6)) (ktCols (g % 6)) := fun g =>
    actsBy_ktRho (Nat.mod_lt _ (by norm_num))
  have h := le_card_of_tree (K := ktSub)
    (fun φ : MulAut W11 => Parab.maskOf 11 (φ (toW 11 1))) ktAct (fun g m => by
      rintro ⟨φ, hφ, rfl⟩
      refine ⟨ktRho (g % 6) * φ, Subgroup.mul_mem _ (hgen g) hφ, ?_⟩
      have hm := (Parab.maskOf_spec (φ (toW 11 1))).2
      calc Parab.maskOf 11 (ktRho (g % 6) (φ (toW 11 1)))
          = Parab.maskOf 11 (ktRho (g % 6) (toW 11 (Parab.maskOf 11 (φ (toW 11 1))))) := by
            rw [hm]
        _ = ktAct g (Parab.maskOf 11 (φ (toW 11 1))) := by
            rw [(hact g) _, Parab.maskOf_toW (actM_lt
              (ktCols_lt _ (Nat.mod_lt _ (by norm_num))) _)]
            rfl)
    ⟨1, Subgroup.one_mem _, Parab.maskOf_toW (by norm_num)⟩ ktTree_ok
  rwa [ktTree_length] at h

theorem card_ktCent :
    Nat.card ↥(img11 trQ ⊓ centSub UT) = 64 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hS := card_stab_UT_le
  have hC64 := le_card_cent
  have hCK := card_cent_mul_le
  have hQ : 10752 ≤ Nat.card ↥trQ := by
    rw [← card_img11_trQ]
    omega
  obtain ⟨-, hQc⟩ := perfectCore_stabUTP (card_stabUTP.trans_le hS) hQ
  rw [card_img11_trQ, hQc] at hCK
  have hle : Nat.card ↥(img11 trQ ⊓ centSub UT) ≤ 64 := by omega
  have hk := ktSub_card_ge
  have heq : ktSub = img11 trQ ⊓ centSub UT :=
    Subgroup.eq_of_le_of_card_ge ktSub_le (by omega)
  have hC : Nat.card ↥(img11 trQ ⊓ centSub UT) = Nat.card ↥ktSub := by rw [heq]
  omega

end CFSG.Quasithin.H.Coc24
