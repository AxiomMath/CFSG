module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenL
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenG
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w16pLa_card_sp {J E : Subgroup G} (M : ModDataE J E) (S : Subgroup G) :
    Nat.card ↥(M.sp S) = Nat.card ↥(S ⊓ E) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : ↥(S ⊓ E) => (⟨M.ι (x : G), M.mem_sp.2 ⟨(x : G), x.2, rfl⟩⟩ : ↥(M.sp S)))
    ⟨?_, ?_⟩)).symm
  · intro x y hxy
    apply Subtype.ext
    exact M.ι_injOn x.2.2 y.2.2 (congrArg Subtype.val hxy)
  · intro w
    obtain ⟨e, he, hwe⟩ := M.mem_sp.1 w.2
    exact ⟨⟨e, he⟩, Subtype.ext hwe⟩

theorem le_mQuot_of_setting12Two (hMult : SchurMultiplierInput)
    {M Y D N P Q : Subgroup G} {k : ℕ}
    (h12 : Setting12Two (D.subgroupOf Y) (M.subgroupOf Y) k) (hD : IsElemAbelian 2 D)
    (hDY : D ≤ Y) (hN : IsElemAbelian 2 N) (hYN : Y ≤ normalizer (N : Set G))
    (hquad : ∀ a ∈ D, ∀ b ∈ D, ∀ e ∈ N, a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹)
    (hQP : Q < P) (hPN : P ≤ N) (hPD : ∀ d ∈ D, ∀ p ∈ P, d * p * d⁻¹ = p)
    (hP : ∀ m ∈ Y ⊓ M, m ∈ normalizer (P : Set G))
    (hQ : ∀ m ∈ Y ⊓ M, m ∈ normalizer (Q : Set G))
    (hfix : P ⊓ centralizer (Y : Set G) ≤ Q) : k ≤ E3.mQuot P Q := by
  classical
  obtain ⟨MD⟩ := exists_modDataE (J := Y) (E := N) hN hYN
  have hDsub : IsElemAbelian 2 (D.subgroupOf Y) := hD.subgroupOf Y
  have hcomm : ⁅⁅N, D⁆, D⁆ = ⊥ := by
    have hle : ⁅D, N⁆ ≤ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.commutator_le]
      intro b hb e he
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := hquad a ha b hb e he
      calc a * (b * e * b⁻¹ * e⁻¹)
          = (a * (b * e * b⁻¹ * e⁻¹) * a⁻¹) * a := by group
        _ = (b * e * b⁻¹ * e⁻¹) * a := by rw [h]
    have hbot : ⁅⁅D, N⁆, D⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [Subgroup.commutator_comm N D]
    exact hbot
  have hq : RepQuad MD.ρ (D.subgroupOf Y) :=
    MD.commSpace_commSub_img_eq_bot hDY hcomm
  have hPleC : P ≤ Subgroup.centralizer (D : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hPD d hd p hp
    calc d * p = (d * p * d⁻¹) * d := by group
      _ = p * d := by rw [h]
  have hPA : MD.sp P ≤ fixSub ((D.subgroupOf Y).map MD.ρ) := by
    change MD.sp P ≤ fixSub (MD.img D)
    rw [MD.fixSub_img hDY]
    exact MD.sp_mono hPleC
  have hQleP : MD.sp Q ≤ MD.sp P := MD.sp_mono hQP.le
  have hne : MD.sp Q ≠ MD.sp P := by
    intro heq
    have hPQ : P ≤ Q := by
      intro p hp
      have hmem : MD.ι p ∈ MD.sp Q := by
        rw [heq]
        exact MD.mem_sp.2 ⟨p, ⟨hp, hPN hp⟩, rfl⟩
      obtain ⟨q, hq', hqe⟩ := MD.mem_sp.1 hmem
      have hpq : p = q := MD.ι_injOn (hPN hp) hq'.2 hqe.symm
      rw [hpq]
      exact hq'.1
    exact hQP.ne (le_antisymm hQP.le hPQ)
  have hQP' : MD.sp Q < MD.sp P := lt_of_le_of_ne hQleP hne
  have hPinv : ∀ m ∈ M.subgroupOf Y, ∀ v ∈ MD.sp P, MD.ρ m v ∈ MD.sp P := by
    intro m hm v hv
    obtain ⟨p, hp, rfl⟩ := MD.mem_sp.1 hv
    have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.1 hm
    have hmY : (m : G) ∈ Y := m.2
    have hpP : p ∈ P := hp.1
    have hpN : p ∈ N := hPN hpP
    have hnorm := hP (m : G) ⟨hmY, hmM⟩
    have hconj : (m : G) * p * (m : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 hnorm p).1 hpP
    have hconjN : (m : G) * p * (m : G)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (hYN hmY) p).1 hpN
    exact MD.mem_sp.2 ⟨(m : G) * p * (m : G)⁻¹, ⟨hconj, hconjN⟩,
      (MD.ρ_ι m p hpN).symm⟩
  have hQinv : ∀ m ∈ M.subgroupOf Y, ∀ v ∈ MD.sp Q, MD.ρ m v ∈ MD.sp Q := by
    intro m hm v hv
    obtain ⟨p, hp, rfl⟩ := MD.mem_sp.1 hv
    have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.1 hm
    have hmY : (m : G) ∈ Y := m.2
    have hpQ : p ∈ Q := hp.1
    have hpN : p ∈ N := hPN (hQP.le hpQ)
    have hnorm := hQ (m : G) ⟨hmY, hmM⟩
    have hconj : (m : G) * p * (m : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 hnorm p).1 hpQ
    have hconjN : (m : G) * p * (m : G)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (hYN hmY) p).1 hpN
    exact MD.mem_sp.2 ⟨(m : G) * p * (m : G)⁻¹, ⟨hconj, hconjN⟩,
      (MD.ρ_ι m p hpN).symm⟩
  have hfix' : MD.sp P ⊓ fixSub MD.ρ.range ≤ MD.sp Q := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := MD.mem_sp.1 hw.1
    have hpP : p ∈ P := hp.1
    have hpN : p ∈ N := hp.2
    have hpC : p ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hfixw : MD.ρ ⟨y, hy⟩ (MD.ι p) = MD.ι p :=
        hw.2 (MD.ρ ⟨y, hy⟩) (MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩)
      rw [MD.ρ_ι ⟨y, hy⟩ p hpN] at hfixw
      have heq : y * p * y⁻¹ = p :=
        MD.ι_injOn ((Subgroup.mem_normalizer_iff.1 (hYN hy) p).1 hpN) hpN hfixw
      calc y * p = (y * p * y⁻¹) * y := by group
        _ = p * y := by rw [heq]
    exact MD.mem_sp.2 ⟨p, ⟨hfix ⟨hpP, hpC⟩, hpN⟩, rfl⟩
  have hcardP : Nat.card ↥((MD.sp P).toAddSubgroup) = Nat.card ↥P := by
    change Nat.card ↥(MD.sp P) = Nat.card ↥P
    rw [w16pLa_card_sp MD P, inf_of_le_left hPN]
  have hcardQ : Nat.card ↥((MD.sp Q).toAddSubgroup) = Nat.card ↥Q := by
    change Nat.card ↥(MD.sp Q) = Nat.card ↥Q
    rw [w16pLa_card_sp MD Q, inf_of_le_left (hQP.le.trans hPN)]
  have hrel : (MD.sp Q).toAddSubgroup.relIndex (MD.sp P).toAddSubgroup = Q.relIndex P := by
    have hQle : (MD.sp Q).toAddSubgroup ≤ (MD.sp P).toAddSubgroup := MD.sp_mono hQP.le
    have h1 := AddSubgroup.relIndex_mul_card (H := (MD.sp Q).toAddSubgroup)
      (K := (MD.sp P).toAddSubgroup)
    rw [inf_of_le_left hQle, hcardP, hcardQ] at h1
    have h2 := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_of_le_left hQP.le] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hP2 : IsPGroup 2 P := hN.isPGroup.to_le hPN
  have hcard : Nat.card (↥(MD.sp P) ⧸ (MD.sp Q).comap (MD.sp P).subtype)
      = 2 ^ E3.mQuot P Q := by
    change (MD.sp Q).toAddSubgroup.relIndex (MD.sp P).toAddSubgroup = 2 ^ E3.mQuot P Q
    rw [hrel, E3.relIndex_eq_two_pow hP2 Q]
  have hcount := Setting12Two.two_pow_le_card_quotient hMult h12 hDsub MD.ρ hq
    hPA hQP' hPinv hQinv hfix'
  rw [hcard] at hcount
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcount

variable {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

private theorem w16pLa_conjSubgroup_le_centralizer_V (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
  (E3.le_wClos (E3.mem_gammaSet_iff.mpr ⟨hX.le_S, g, le_rfl, E3.mQuot_self _⟩)).trans
    (hX.cex.wClos_le_centralizer h1 hS)

theorem Hyp167.le_n_of_quad (hMult : SchurMultiplierInput)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) {Y D : Subgroup G} {k : ℕ} (hD : IsElemAbelian 2 D)
    (hDA : D ≤ conjSubgroup V g) (hDY : D ≤ Y) (hYX : Y ≤ X) (hYM : ¬ Y ≤ M)
    (h12 : Setting12Two (D.subgroupOf Y) (M.subgroupOf Y) k)
    (hquad : ∀ a ∈ D, ∀ b ∈ D, ∀ e ∈ conjClosure V X,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹) :
    k ≤ E3.mQuot V (U ⊔ V₀) := by
  have hI : IsElemAbelian 2 (conjClosure V X) := Hyp167.isElemAbelian_I h1 hS hX hVO
  have hYN : Y ≤ normalizer (conjClosure V X : Set G) :=
    hYX.trans (le_normalizer_conjClosure V X)
  have hAc : conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
    w16pLa_conjSubgroup_le_centralizer_V h1 hS hX
  have hPD : ∀ d ∈ D, ∀ p ∈ V, d * p * d⁻¹ = p := by
    intro d hd p hp
    have hdC : d ∈ Subgroup.centralizer (V : Set G) := hAc (hDA hd)
    have hcomm : p * d = d * p := (Subgroup.mem_centralizer_iff.1 hdC) p hp
    rw [← hcomm]
    group
  have hQP : U ⊔ V₀ < V :=
    lt_of_le_of_ne (sup_le hX.cex.le hX.cex.hyp.h6.le) (hX.cex.sup_ne_top h152)
  have hPnorm : ∀ m ∈ Y ⊓ M, m ∈ normalizer (V : Set G) := by
    intro m hm
    rw [hX.cex.hyp.h6.normalizer_eq]
    exact hm.2
  have hQnorm : ∀ m ∈ Y ⊓ M, m ∈ normalizer (U ⊔ V₀ : Subgroup G) := by
    intro m hm
    have hmV₀ : m ∈ normalizer (V₀ : Set G) := by
      rw [hX.cex.hyp.normalizer₀]
      exact hm.2
    have hmU : m ∈ normalizer (U : Set G) :=
      Subgroup.centralizer_le_normalizer (U : Set G)
        (hX.min.1.2.1 ((hYX.trans hX.mem.1) hm.1))
    exact Subgroup.inf_normalizer_le_normalizer_sup U V₀ ⟨hmU, hmV₀⟩
  have hfix : V ⊓ centralizer (Y : Set G) ≤ U ⊔ V₀ := by
    rw [Hyp167.inf_centralizer_eq hX hYX hYM]
    exact le_sup_left
  exact le_mQuot_of_setting12Two hMult h12 hD hDY hI hYN hquad hQP (le_conjClosure V X)
    hPD hPnorm hQnorm hfix

theorem Hyp167.le_mSub_of_F (hMult : SchurMultiplierInput)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) {Y : Subgroup G} {k : ℕ} (hAY : conjSubgroup V g ≤ Y)
    (hYX : Y ≤ X) (hYM : ¬ Y ≤ M)
    (h12 : Setting12Two ((conjSubgroup V g).subgroupOf Y) (M.subgroupOf Y) k)
    (hFA : conjClosure V₀ X ≤ conjSubgroup M g) : k ≤ mSub V₀ := by
  have hAab : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hFab : IsElemAbelian 2 (conjClosure V₀ X) :=
    CFSG.Open.IsElemAbelian.mono (Hyp167.isElemAbelian_I h1 hS hX hVO)
      (conjClosure_mono hX.cex.hyp.h6.le le_rfl)
  have hYN : Y ≤ normalizer (conjClosure V₀ X : Set G) :=
    hYX.trans (le_normalizer_conjClosure V₀ X)
  have hAc : conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
    w16pLa_conjSubgroup_le_centralizer_V h1 hS hX
  have hAc₀ : conjSubgroup V g ≤ Subgroup.centralizer (V₀ : Set G) :=
    hAc.trans (Subgroup.centralizer_le hX.cex.hyp.h6.le)
  have hnormA : conjClosure V₀ X ≤ normalizer (conjSubgroup V g : Set G) := by
    have hMM : conjSubgroup M g = normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, hX.cex.hyp.h6.normalizer_eq]
    rwa [hMM] at hFA
  have hquad : ∀ a ∈ conjSubgroup V g, ∀ b ∈ conjSubgroup V g,
      ∀ e ∈ conjClosure V₀ X,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹ := by
    intro a ha b hb e he
    have heN : e ∈ normalizer (conjSubgroup V g : Set G) := hnormA he
    have hx : b * e * b⁻¹ * e⁻¹ ∈ conjSubgroup V g := by
      have h1 : ⁅e, b⁆ ∈ conjSubgroup V g := by
        have hmem : e * b * e⁻¹ ∈ conjSubgroup V g :=
          (Subgroup.mem_normalizer_iff.1 heN b).1 hb
        exact (conjSubgroup V g).mul_mem hmem ((conjSubgroup V g).inv_mem hb)
      have h2 : ⁅e, b⁆⁻¹ ∈ conjSubgroup V g := (conjSubgroup V g).inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hcomm := CFSG.Quasithin.B2F.isElemAbelian_comm hAab ha hx
    calc a * (b * e * b⁻¹ * e⁻¹) * a⁻¹
        = (b * e * b⁻¹ * e⁻¹) * a * a⁻¹ := by rw [hcomm]
      _ = b * e * b⁻¹ * e⁻¹ := by group
  have hQP : (⊥ : Subgroup G) < V₀ := bot_lt_iff_ne_bot.mpr hX.cex.hyp.ne_bot
  have hPnorm : ∀ m ∈ Y ⊓ M, m ∈ normalizer (V₀ : Set G) := by
    intro m hm
    rw [hX.cex.hyp.normalizer₀]
    exact hm.2
  have hQnorm : ∀ m ∈ Y ⊓ M, m ∈ normalizer (⊥ : Subgroup G) := by
    intro m hm
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top m
  have hfix : V₀ ⊓ centralizer (Y : Set G) ≤ (⊥ : Subgroup G) := by
    intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    have hYle : Y ≤ Subgroup.centralizer ({v} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ((Subgroup.mem_centralizer_iff.1 hv.2) y hy).symm
    exact hYM (hYle.trans (hX.cex.hyp.centralizer_le hv.1 hv1))
  have hPD : ∀ d ∈ conjSubgroup V g, ∀ p ∈ V₀, d * p * d⁻¹ = p := by
    intro d hd p hp
    have hdC : d ∈ Subgroup.centralizer (V₀ : Set G) := hAc₀ hd
    have hcomm : p * d = d * p := (Subgroup.mem_centralizer_iff.1 hdC) p hp
    rw [← hcomm]
    group
  have hres := le_mQuot_of_setting12Two hMult h12 hAab hAY hFab hYN hquad hQP
    (le_conjClosure V₀ X) hPD hPnorm hQnorm hfix
  have hbot : E3.mQuot V₀ ⊥ = mSub V₀ := by
    change padicValNat 2 ((⊥ : Subgroup G).relIndex V₀) = mSub V₀
    rw [Subgroup.relIndex_bot_left, card_eq_two_pow_mSub hX.cex.hyp.elemAbelian₀.isPGroup,
      padicValNat.prime_pow]
  rwa [hbot] at hres

end CFSG.LocalAnalysis.WeakClosure81

end
