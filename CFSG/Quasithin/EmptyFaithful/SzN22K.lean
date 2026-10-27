module

public import CFSG.Quasithin.EmptyFaithful.SzN22Star
public import CFSG.Quasithin.EmptyFaithful.SzN19L

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace SzN22

@[expose] def LieRigid : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K : Subgroup Ω) (e : ℕ), 1 < e → IsLieOver2e ↥K e → KRig K

theorem krig_of_b56
    (hR : LieRigid) {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (hq : CFSG.IsQuasisimple ↥K) (hl : B56QuasisimpleList ↥K) : KRig K := by
  by_cases hlie : ∃ e : ℕ, 1 < e ∧ IsLieOver2e ↥K e
  · obtain ⟨e, he, hKe⟩ := hlie
    exact hR Ω K e he hKe
  · exact krig_of_listL (SzN19.isListL_of_b56 hq hl (fun e he h => hlie ⟨e, he, h⟩))

section Main

theorem input49K_of_lieRigid
    (h113 : StageLemma14113) (h56 : AsB56) (hR : LieRigid) : S1549C.Input49K := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L lctx
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := S153L.Y0_le_H hb
  have hWH : W ≤ H := od.W_le.trans ((pCoreOf_le 2 _).trans (sup_le hY0H hTH))
  have hHs : StarOf T M V₁ H H = starOfSub h H := starOf_eq_starOfSub cx hb le_rfl
  have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
    have := od.off
    rwa [hHs] at this
  have hBW : B ≤ starOfSub h W := by
    have := od.B_le
    rwa [starOf_eq_starOfSub cx hb hWH] at this
  have hJ : Jgrp hb B = preStar h (conjClosure B (starOfSub h H)) := by
    unfold Jgrp
    rw [hHs]
  set A : Subgroup (MulAut (UTil T M V₁ H)) := conjClosure B (starOfSub h H) with hAdef
  have hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut (UTil T M V₁ H))) :=
    le_normalizer_conjClosure B _
  have hAn' : ∀ g : MulAut (UTil T M V₁ H), g ∈ starOfSub h H → ∀ j ∈ A, g * j * g⁻¹ ∈ A :=
    fun g hg j hj => (Subgroup.mem_normalizer_iff.mp (hAn hg) j).mp hj
  have hAH : A ≤ starOfSub h H := conjClosure_le fun g hg b hb' =>
    (starOfSub h H).mul_mem ((starOfSub h H).mul_mem hg (hoff.1 hb')) ((starOfSub h H).inv_mem hg)
  have hSQ : SQTKGroup ↥A := by
    have := sqtkGroup_starOfSub cx hb (K := preStar h A) (preStar_le h A)
    rwa [S153L.starOfSub_preStar h hAH] at this
  have hBR : B ≤ pCoreOf 2 (starOfSub h (Y0 T Mc M) ⊔ starOfSub h T) := by
    rw [← starOfSub_sup h hY0H hTH]
    exact hBW.trans ((starOfSub_mono h od.W_le).trans (starOfSub_pCoreOf_le h (sup_le hY0H hTH)))
  have hmain := S153L.ns_main (V := UTil T M V₁ H) h56 hV (starOfSub h H) A (starOfSub h (M ⊓ H))
    (starOfSub h (Y0 T Mc M)) (starOfSub h T) B hAH hAn' (pCoreOf_starOfSub_H h) hSQ
    (starOfSub_mono h (S153L.Y0_le_inf hb)) (starOfSub_mono h inf_le_right) hoff
    (le_conjClosure B _) hBR rfl (fun x hx hx3 => S153L.theta_star hb hx3 hx) (S153L.Ystar_gen hb)
    (fun X hXH hXY => S153L.hKL_star h113 hb X hXH hXY)
    (fun E hE hE3 => S153L.hY3_star hb hE hE3)
  obtain ⟨hAne, hB53⟩ := SzN19.b53_of_offender (V := UTil T M V₁ H) (starOfSub h H) A B hAH hAn'
    (pCoreOf_starOfSub_H h) hSQ hoff (le_conjClosure B _) rfl
  have hcases := h56 (UTil T M V₁ H) hV A hAne hB53
  have hLcomp : L ∈ cComp (preStar h A) := by
    have := lctx.comp
    rwa [hJ] at this
  have hLmem : starOfSub h L ∈ cComp A := S153L.starOfSub_mem_cComp h hAH hLcomp
  have hLH : L ≤ H := (le_of_mem_cComp hLcomp).trans (preStar_le h A)
  obtain ⟨hq, hl⟩ := SzN19.list_of_mem_cComp hcases hLmem
  have hKrig : KRig (starOfSub h L) := krig_of_b56 hR hq hl
  have hTM : T ≤ Subgroup.normalizer (Y0 T Mc M : Set G) :=
    cx.c.hyp.T_le.trans (le_normalizer_Y0 cx.c.hyp)
  have hTY := SzN19.starOfSub_le_normalizer h hTM
  have hTs : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
    have := isSylowTwoOf_starOfSub_T h
    rwa [← starOfSub_H h] at this
  have hmin : ∀ K' : Subgroup (MulAut (UTil T M V₁ H)),
      starOfSub h (Y0 T Mc M) ⊔ starOfSub h T ≤ K' → K' ≤ starOfSub h H →
        K' ≠ starOfSub h H → K' ≤ starOfSub h (M ⊓ H) := fun K' h1 h2 h3 => by
    refine overgroup_le_M_of_minimal cx hb ?_ h2 h3
    rwa [starOfSub_sup h hY0H hTH]
  have hord : ∀ y ∈ starOfSub h (Y0 T Mc M), ∃ k : ℕ, y ^ (2 ^ k * 3) = 1 := by
    intro y hy
    obtain ⟨x, hxY, rfl⟩ := (mem_starOfSub h).mp hy
    obtain ⟨k, hk'⟩ := SzN19.exists_pow_Y0 cx.case2 hxY
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (x : ↥H) ^ (2 ^ k * 3) = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hL₀H : conjClosure L T ≤ H :=
    conjClosure_le fun g hg l hl => H.mul_mem (H.mul_mem (hTH hg) (hLH hl)) (H.inv_mem (hTH hg))
  have hHeq : starOfSub h H =
      starOfSub h (conjClosure L T) ⊔ starOfSub h (Y0 T Mc M) ⊔ starOfSub h T := by
    rw [congrArg (starOfSub h) lctx.eq, starOfSub_sup h (sup_le hL₀H hY0H) hTH,
      starOfSub_sup h hL₀H hY0H]
  have hle : conjClosure L T ≤ preStar h (conjClosure (starOfSub h L) (starOfSub h T)) := by
    refine conjClosure_le fun g hg l hl => ?_
    have hgH : g ∈ H := hTH hg
    have hlH : l ∈ H := hLH hl
    refine (mem_preStar_iff h).mpr ⟨H.mul_mem (H.mul_mem hgH hlH) (H.inv_mem hgH), ?_⟩
    have e : (⟨g * l * g⁻¹, H.mul_mem (H.mul_mem hgH hlH) (H.inv_mem hgH)⟩ : ↥H) =
        ⟨g, hgH⟩ * ⟨l, hlH⟩ * (⟨g, hgH⟩ : ↥H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact mem_conjClosure ((mem_starOfSub h).mpr ⟨⟨g, hgH⟩, hg, rfl⟩)
      ((mem_starOfSub h).mpr ⟨⟨l, hlH⟩, hl, rfl⟩)
  have hL₀s : starOfSub h (conjClosure L T) ≤ conjClosure (starOfSub h L) (starOfSub h T) := by
    intro y hy
    obtain ⟨⟨x, hxH⟩, hx, rfl⟩ := (mem_starOfSub h).mp hy
    exact ((mem_preStar_iff h).mp (hle hx)).2
  have hkstar : starOfSub h (Y0 T Mc M) ≤ conjClosure (starOfSub h L) (starOfSub h T) :=
    k_star (V := UTil T M V₁ H) (Hs := starOfSub h H) (As := A) (Ms := starOfSub h (M ⊓ H)) hcases hAH hAn' hLmem
      hmain.2 (pCoreOf_starOfSub_H h) hTs (starOfSub_mono h (S153L.Y0_le_inf hb))
      (starOfSub_mono h inf_le_right) hTY hord (SzN19.exists_orderThree_star hb lctx)
      (fun E hE hE3 => S153L.hY3_star hb hE hE3) (S153L.Ystar_gen hb)
      (fun x hx hx3 => S153L.theta_star hb hx3 hx) hmin hHeq hL₀s hKrig
  have hKT : conjClosure (starOfSub h L) (starOfSub h T) ≤ starOfSub h (conjClosure L T) := by
    refine conjClosure_le fun s hs k hk => ?_
    obtain ⟨⟨t', ht'H⟩, ht', rfl⟩ := (mem_starOfSub h).mp hs
    obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := (mem_starOfSub h).mp hk
    have hmem : t' * l * t'⁻¹ ∈ H := H.mul_mem (H.mul_mem ht'H hlH) (H.inv_mem ht'H)
    refine (mem_starOfSub h).mpr ⟨⟨t' * l * t'⁻¹, hmem⟩, mem_conjClosure ht' hl, ?_⟩
    have e : (⟨t' * l * t'⁻¹, hmem⟩ : ↥H) = ⟨t', ht'H⟩ * ⟨l, hlH⟩ * (⟨t', ht'H⟩ : ↥H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hAnH : ∀ y ∈ H, ∀ x, x ∈ preStar h A ↔ y * x * y⁻¹ ∈ preStar h A := fun y hy x =>
    ⟨S153L.preStar_conj_mem h hAn hy, fun hx => by
      simpa [mul_assoc] using S153L.preStar_conj_mem h hAn (H.inv_mem hy) hx⟩
  have hQn : pCoreOf 2 H ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
    have key : ∀ q ∈ pCoreOf 2 H, ∀ x ∈ conjClosure L T, q * x * q⁻¹ ∈ conjClosure L T := by
      intro q hq x hx
      let X : Subgroup G := (conjClosure L T).comap (MulAut.conj q).toMonoidHom
      have hX : conjClosure L T ≤ X := by
        refine conjClosure_le fun g hg l hl => ?_
        show q * (g * l * g⁻¹) * q⁻¹ ∈ conjClosure L T
        have hqH : q ∈ H := pCoreOf_le 2 H hq
        have hLg : L.map (MulAut.conj g).toMonoidHom ∈ cComp (preStar h A) :=
          S153L.comp_conj_mem_cComp (hAnH g (hTH hg)) hLcomp
        have hq1 : starHom h ⟨q, hqH⟩ = 1 := (starHom_eq_one_iff h ⟨q, hqH⟩).mpr hq
        have hqLg : q ∈ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
          S153L.normalizes_of_star h hAH hAn hLg hqH (by rw [hq1]; exact Subgroup.one_mem _)
        have h1 : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
          ⟨l, hl, by simp [MulAut.conj_apply]⟩
        obtain ⟨l', hl', hl'eq⟩ := (Subgroup.mem_normalizer_iff.mp hqLg _).mp h1
        have := mem_conjClosure hg hl'
        simpa [MulAut.conj_apply, ← hl'eq] using this
      exact hX hx
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key q hq x, fun hx => by simpa [mul_assoc] using key q⁻¹ (Subgroup.inv_mem _ hq) _ hx⟩
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  rw [hb.claimB]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyMH, hy3⟩
  have hyY : y ∈ Y0 T Mc M := by
    rw [hb.claimB]
    exact Subgroup.subset_closure ⟨hyMH, hy3⟩
  have hyH : y ∈ H := hyMH.2
  have hys : starHom h ⟨y, hyH⟩ ∈ conjClosure (starOfSub h L) (starOfSub h T) :=
    hkstar ((mem_starOfSub h).mpr ⟨⟨y, hyH⟩, hyY, rfl⟩)
  obtain ⟨⟨x, hxH⟩, hxL₀, hxy⟩ := (mem_starOfSub h).mp (hKT hys)
  have hq : x⁻¹ * y ∈ pCoreOf 2 H := by
    have : starHom h ((⟨x, hxH⟩ : ↥H)⁻¹ * ⟨y, hyH⟩) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    exact (starHom_eq_one_iff h _).mp this
  have hyS : y ∈ conjClosure L T ⊔ pCoreOf 2 H := by
    have e : y = x * (x⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hxL₀ hq
  exact mem_of_pow_three_sup hQ2 hQn hyS (hy3 ▸ pow_orderOf_eq_one y)

end Main

end SzN22

end CFSG.Quasithin
