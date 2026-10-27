module

public import CFSG.Quasithin.H13.A6S13827Gc
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB45U33Mid

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.B42U33
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open scoped Pointwise IsMulCommutative

namespace A6G2

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem card_eq_64_of_irr
    (hV : ∀ v : V, v ^ 2 = 1) (hP : B42TypeU33 ↥L)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (h12 : Nat.card V ≤ 2 ^ 12) : Nat.card V = 2 ^ 6 := by
  classical
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (fun v : V => by rw [← pow_two]; exact hV v)
  set ψ := binPsi θ with hψ
  obtain ⟨θL⟩ := nonempty_equiv_g2Derived hP
  let σ : ↥(g2Derived (ZMod 2)) →* (M →ₗ[ZMod 2] M) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp
      (ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom))
  have hσ : ∀ h u, σ h u = ψ ((θL.symm h : ↥L) : MulAut V) u := fun _ _ => rfl
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ h, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h2 := hU (θL ⟨y, hy⟩) u hu
    rwa [hσ, MulEquiv.symm_apply_apply] at h2
  have hntσ : ∃ h, σ h ≠ 1 := by
    have : Nontrivial ↥L := (isSimpleGroup_of_b42 hP).toNontrivial
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    refine ⟨θL x, fun h => hx1 ?_⟩
    have h2 : ψ ((x : ↥L) : MulAut V) = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have h3 := h
      change (ψ ((θL.symm (θL x) : ↥L) : MulAut V)).toLinearMap = 1 at h3
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3
    exact Subtype.ext (ψ.injective (h2.trans (map_one ψ).symm))
  have hMV : Nat.card M = Nat.card V := (natCard_eq θ).symm
  have h6 := B45U33.card_le_of_g2Derived σ hntσ hirrM (hMV ▸ h12)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 := six_le_of_card_dvd hV hk L (card_of_b42TypeU33 hP)
  rw [hMV, hk] at h6
  rw [hk, show k = 6 from le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h6) hk6]

theorem exists_equiv_Q_of_le
    (hV : ∀ v : V, v ^ 2 = 1) (h64 : Nat.card V = 2 ^ 6)
    (hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V))) (hP : B42TypeU33 ↥L) :
    ∃ e : V ≃* ModQ, L.map (MulAut.congr e).toMonoidHom =
        (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
      ∀ x ∈ G, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
  obtain ⟨e, hLe⟩ := exists_equiv_Q hV h64 hP
  refine ⟨e, hLe, fun x hx => normalizer_two_Q _ fun h => ?_⟩
  obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
  have hxN := Subgroup.mem_normalizer_iff.1 (hGN hx) h'
  rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
  change (MulAut.congr e).toMonoidHom h' ∈ L.map (MulAut.congr e).toMonoidHom ↔
    (MulAut.congr e).toMonoidHom (x * h' * x⁻¹) ∈ L.map (MulAut.congr e).toMonoidHom
  rw [Subgroup.mem_map_iff_mem (MulAut.congr e).injective,
    Subgroup.mem_map_iff_mem (MulAut.congr e).injective]
  exact hxN

end A6G2

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem card_eq_64_of_le_sq
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ ((F ⊓ pCoreOf 2 H).relIndex F) ^ 2) :
    W.relIndex X = 2 ^ 6 := by
  set A := autSec (autOn F X) ⊤ (W.subgroupOf X) with hAdef
  have hA : Nat.card A = (F ⊓ pCoreOf 2 H).relIndex F := hs.card_autSec hFH
  have hi := hs.index_fixV_le hFH
  have hV : ∀ v : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs.sec_sq v
  have hP := hs.b42TypeU33 hU
  have hfix := hs.fixV_eq_bot hirr
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle'⟩ := A6G2.short_generation (hs.autSec_le hs.hKH le_rfl)
    hs.autSec_le_normalizer hs.inf_centralizer_le hP (hs.autSec_le hFH le_rfl)
    (hs.autSec_ne_bot hFH hF) (hs.isElemAbelian2_autSec hFH hFc hFs)
  have h1 := HatA6.card_le_pow_of_le_closure hfix l hle'
  have hidx : (fixV A).index ≤ Nat.card A ^ 2 := by rw [hA]; exact hi.trans hle
  have h12 : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 12 := by
    refine h1.trans ((Nat.pow_le_pow_left hidx m).trans ?_)
    rw [hr, ← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  rw [← card_sec]
  exact A6G2.card_eq_64_of_irr hV hP
    (hs.isIrr_autSec_K hU hirr (by rw [← card_sec]; exact h12)) h12

theorem exists_equiv_Q
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) (h64 : W.relIndex X = 2 ^ 6) :
    ∃ e : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X) ≃* ModQ,
      (autSec (autOn K X) ⊤ (W.subgroupOf X)).map (MulAut.congr e).toMonoidHom =
          (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        ∀ x ∈ autSec (autOn H X) ⊤ (W.subgroupOf X),
          MulAut.congr e x ∈ (g2QAct (ZMod 2)).range :=
  A6G2.exists_equiv_Q_of_le (fun v => by rw [pow_two]; exact hs.sec_sq v)
    (by rw [card_sec]; exact h64) hs.autSec_le_normalizer (hs.b42TypeU33 hU)

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
