module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
import CFSG.LargeExtraspecial.S45QLin
import CFSG.Quasithin.Vol2.KGFactSLnTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem s16c1610_not_isTensorS3L2_of_normal {G N : Subgroup (MulAut W)} {m : ℕ} (hm : 3 ≤ m)
    (hNG : N ≤ G) (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h6 : ¬ Nat.card N ∣ 6)
    (hGL : ¬ Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) ∣ Nat.card N) :
    ¬ IsTensorS3L2 W G m := by
  rintro ⟨φ, -, -⟩
  let S := Equiv.Perm (Fin 3)
  let Γ := Matrix.GeneralLinearGroup (Fin m) (ZMod 2)
  let Nc : Subgroup (S × Γ) := (N.subgroupOf G).map φ.toMonoidHom
  have hNsub : (N.subgroupOf G).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNn (g : MulAut W) g.2 (n : MulAut W) hn⟩
  have hNc_normal : Nc.Normal := hNsub.map φ.toMonoidHom φ.surjective
  have hNc_card : Nat.card Nc = Nat.card N :=
    (Subgroup.card_map_of_injective (K := N.subgroupOf G) (f := φ.toMonoidHom)
      φ.injective).trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG).toEquiv)
  let P : Subgroup (S × Γ) := (⊥ : Subgroup S).prod (⊤ : Subgroup Γ)
  have hP_normal : P.Normal := Subgroup.prod_normal _ _
  haveI : Nc.Normal := hNc_normal
  haveI : P.Normal := hP_normal
  let K : Subgroup (S × Γ) := Nc ⊓ P
  have hK_normal : K.Normal := inferInstance
  let KΓ : Subgroup Γ := K.map (MonoidHom.snd S Γ)
  have hKΓ_normal : KΓ.Normal := hK_normal.map _ Prod.snd_surjective
  haveI : KΓ.Normal := hKΓ_normal
  haveI : IsSimpleGroup Γ := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two hm
  have hcardP : Nat.card P = Nat.card Γ := by
    show Nat.card ((⊥ : Subgroup S).prod (⊤ : Subgroup Γ)) = Nat.card Γ
    rw [Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup S) (⊤ : Subgroup Γ)).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top, one_mul]
  have hcardTop : Nat.card ((⊤ : Subgroup S).prod (⊥ : Subgroup Γ)) = 6 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup S) (⊥ : Subgroup Γ)).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top, mul_one]
    show Nat.card (Equiv.Perm (Fin 3)) = 6
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal KΓ with hbot | htop
  · have hNc_le : Nc ≤ (⊤ : Subgroup S).prod (⊥ : Subgroup Γ) := by
      intro x hx
      rw [Subgroup.mem_prod]
      refine ⟨Subgroup.mem_top _, ?_⟩
      have hcomm : ∀ h : Γ, x.2 * h = h * x.2 := by
        intro h
        have h2P : ((1 : S), h) ∈ P := by
          rw [Subgroup.mem_prod]
          exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
        have hcm : ⁅x, ((1 : S), h)⁆ ∈ ⁅Nc, P⁆ :=
          Subgroup.commutator_mem_commutator hx h2P
        have hmemK : ⁅x, ((1 : S), h)⁆ ∈ K :=
          (Subgroup.commutator_le_inf (H₁ := Nc) (H₂ := P)) hcm
        have hmemKΓ : (⁅x, ((1 : S), h)⁆).2 ∈ KΓ := Subgroup.mem_map_of_mem _ hmemK
        rw [hbot] at hmemKΓ
        have hval : (⁅x, ((1 : S), h)⁆).2 = 1 := Subgroup.mem_bot.mp hmemKΓ
        have hcoord : x.2 * h * x.2⁻¹ * h⁻¹ = 1 := by
          simpa [commutatorElement_def] using hval
        have hcoord' : (x.2 * h) * (h * x.2)⁻¹ = 1 := by
          simpa only [mul_inv_rev, mul_assoc] using hcoord
        exact mul_inv_eq_one.mp hcoord'
      exact CFSG.Quasithin.SLnTwo.eq_one_of_forall_commute_GL hcomm
    have hdvd : Nat.card Nc ∣ 6 := by
      have h := Subgroup.card_dvd_of_le hNc_le
      rwa [hcardTop] at h
    exact h6 (by rwa [hNc_card] at hdvd)
  · have hPle : P ≤ Nc := by
      intro x hx
      have hx1 : x.1 = 1 := by
        have h := (Subgroup.mem_prod.mp hx).1
        simpa using h
      have hx2 : x.2 ∈ KΓ := by rw [htop]; exact Subgroup.mem_top x.2
      rw [Subgroup.mem_map] at hx2
      obtain ⟨k, hkK, hk⟩ := hx2
      have hk1 : k.1 = 1 := by
        have h := (Subgroup.mem_prod.mp hkK.2).1
        simpa using h
      have hkx : k = x := by
        refine Prod.ext ?_ ?_
        · rw [hk1, hx1]
        · simpa using hk
      rw [← hkx]
      exact hkK.1
    have hdvd : Nat.card Γ ∣ Nat.card Nc := by
      have h := Subgroup.card_dvd_of_le hPle
      rwa [hcardP] at h
    exact hGL (by rwa [hNc_card] at hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
