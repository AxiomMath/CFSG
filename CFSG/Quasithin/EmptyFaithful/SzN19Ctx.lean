module

public import CFSG.Quasithin.EmptyFaithful.SzN19Star
public import CFSG.Quasithin.Background.S1549DLnStar
public import CFSG.Quasithin.EmptyFaithful.S153LXfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
open scoped commutatorElement Pointwise

namespace SzN19

section Offender

variable {V : Type} [CommGroup V] [Finite V]

theorem b53_of_offender (Hs Js Bs : Subgroup (MulAut V))
    (hJH : Js ≤ Hs) (hJn : ∀ h ∈ Hs, ∀ j ∈ Js, h * j * h⁻¹ ∈ Js)
    (hO2 : pCoreOf 2 Hs = ⊥) (hSQ : SQTKGroup ↥Js)
    (hBoff : IsFFStarOffender Hs Bs) (hBJ : Bs ≤ Js) (hJgen : Js = conjClosure Bs Hs) :
    Js ≠ ⊥ ∧ B53Hyp Js := by
  have hJnorm : ∀ y ∈ Hs, ∀ x, x ∈ Js ↔ y * x * y⁻¹ ∈ Js := fun y hy x =>
    ⟨hJn y hy x, fun hx => by simpa [mul_assoc] using hJn y⁻¹ (Hs.inv_mem hy) _ hx⟩
  have hJne : Js ≠ ⊥ := fun h => hBoff.2.1 (le_bot_iff.mp (h ▸ hBJ))
  have hO2J : pCoreOf 2 Js = ⊥ := by
    have hn : Hs ≤ Subgroup.normalizer (Js : Set (MulAut V)) := fun y hy => by
      rw [Subgroup.mem_normalizer_iff]
      exact hJnorm y hy
    have : pCoreOf 2 Js ≤ pCoreOf 2 Hs :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Js).trans hJH)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (hn hg)) (pCoreOf_isPGroup 2 Js)
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hffJ : Js = ffJ Js := by
    refine le_antisymm ?_ (B6.ffJ_le Js)
    have hle : conjClosure Bs Hs ≤ ffJ Js := by
      refine conjClosure_le fun h hh b hb => ?_
      have hoff := B1.isFFStarOffender_conjAut hBoff hh
      have hle : B1.conjAut h Bs ≤ Js := by
        intro x hx
        have h1 := hJn h hh _ (hBJ (B1.mem_conjAut.mp hx))
        simpa [mul_assoc] using h1
      have hoffJ : IsFFStarOffender Js (B1.conjAut h Bs) :=
        ⟨hle, hoff.2.1, hoff.2.2.1, hoff.2.2.2⟩
      exact B6.le_ffJ hoffJ (B1.mem_conjAut.mpr (by simpa [mul_assoc] using hb))
    rwa [← hJgen] at hle
  exact ⟨hJne, hO2J, hffJ, ↥Js, inferInstance, inferInstance, ⊥, inferInstance, hSQ,
    ⟨(QuotientGroup.quotientBot).symm⟩⟩

end Offender

section Star

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem starOfSub_le_normalizer (h : HypF91 T V L V₁ Vp H) {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    starOfSub h X ≤ Subgroup.normalizer
      (starOfSub h Y : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) := by
  intro x' hx'
  obtain ⟨x, hxX, rfl⟩ := (mem_starOfSub h).mp hx'
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨y, hyY, rfl⟩ := (mem_starOfSub h).mp hz
    refine (mem_starOfSub h).mpr ⟨x * y * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hXY hxX) (y : G)).mp hyY
    simpa using this
  · intro hz
    obtain ⟨y, hyY, hyz⟩ := (mem_starOfSub h).mp hz
    refine (mem_starOfSub h).mpr ⟨x⁻¹ * y * x, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hXY (Subgroup.inv_mem _ hxX)) (y : G)).mp hyY
      simpa using this
    · have e : starHom h x⁻¹ * starHom h y * starHom h x =
          (starHom h x)⁻¹ * (starHom h x * z * (starHom h x)⁻¹) * starHom h x := by
        rw [map_inv, hyz]
      calc starHom h (x⁻¹ * y * x) = starHom h x⁻¹ * starHom h y * starHom h x := by
            simp only [map_mul]
        _ = z := by rw [e]; group

end Star

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G}

theorem exists_orderThree_star (hb : InspBase cx H) {W : Subgroup G}
    {B : Subgroup (MulAut (UTil T M V₁ H))} {od : OffData hb W B} {L : Subgroup G}
    (lctx : LCtx hb od L) :
    ∃ y ∈ starOfSub hb.hF98.toHypF91 (Y0 T Mc M), orderOf y = 3 := by
  have h := hb.hF98.toHypF91
  have h3 : ∃ y₀ : G, y₀ ∈ M ⊓ H ∧ orderOf y₀ = 3 := by
    by_contra hno
    push Not at hno
    have hθ : thetaOf (M ⊓ H) = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hx, hx3⟩
      exact absurd hx3 (hno x hx)
    have hY0 : Y0 T Mc M = ⊥ := hb.claimB.trans hθ
    have hcomm : L = ⁅L, Y0 T Mc M⁆ := lctx.comm
    rw [hY0, Subgroup.commutator_bot_right] at hcomm
    exact ne_bot_of_mem_cComp lctx.comp hcomm
  obtain ⟨y₀, hy₀MH, hy₀3⟩ := h3
  have hy₀Y : y₀ ∈ Y0 T Mc M := by
    rw [hb.claimB]
    exact Subgroup.subset_closure ⟨hy₀MH, hy₀3⟩
  have hy₀H : y₀ ∈ H := hy₀MH.2
  let x₀ : ↥H := ⟨y₀, hy₀H⟩
  have hy1 : starHom h x₀ ≠ 1 := by
    intro h1
    have hq : (x₀ : G) ∈ pCoreOf 2 H := (starHom_eq_one_iff h x₀).mp h1
    obtain ⟨k, hk2⟩ := pCoreOf_isPGroup 2 H ⟨(x₀ : G), hq⟩
    have hpow : y₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk2
    have hdvd : 3 ∣ 2 ^ k := hy₀3 ▸ orderOf_dvd_of_pow_eq_one hpow
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hy3 : orderOf (starHom h x₀) = 3 := by
    have hx3 : x₀ ^ 3 = 1 := by
      apply Subtype.ext
      show y₀ ^ 3 = 1
      rw [← hy₀3]
      exact pow_orderOf_eq_one y₀
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hy1
  exact ⟨starHom h x₀, (mem_starOfSub h).mpr ⟨x₀, hy₀Y, rfl⟩, hy3⟩

theorem star_setup (h56 : AsB56) (hb : InspBase cx H)
    {W : Subgroup G} {B : Subgroup (MulAut (UTil T M V₁ H))} {od : OffData hb W B} {L : Subgroup G}
    (lctx : LCtx hb od L) :
    letI : CommGroup (UTil T M V₁ H) := modInst hb.hF98.toHypF91
    ∃ A : Subgroup (MulAut (UTil T M V₁ H)), A ≤ starOfSub hb.hF98.toHypF91 H ∧
      starOfSub hb.hF98.toHypF91 H ≤ Subgroup.normalizer (A : Set (MulAut (UTil T M V₁ H))) ∧
      L ∈ cComp (preStar hb.hF98.toHypF91 A) ∧ starOfSub hb.hF98.toHypF91 L ∈ cComp A ∧
      (B56Case1 A ∨ B56Case2 A ∨ B56Case3 A ∨ B56Case4 A ∨ B56Case5 A) := by
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hHs : StarOf T M V₁ H H = starOfSub h H := starOf_eq_starOfSub cx hb le_rfl
  have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
    have := od.off
    rwa [hHs] at this
  have hJ : Jgrp hb B = preStar h (conjClosure B (starOfSub h H)) := by
    unfold Jgrp
    rw [hHs]
  set A : Subgroup (MulAut (UTil T M V₁ H)) := conjClosure B (starOfSub h H) with hAdef
  have hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut (UTil T M V₁ H))) :=
    le_normalizer_conjClosure B _
  have hAH : A ≤ starOfSub h H := conjClosure_le fun g hg b hb' =>
    (starOfSub h H).mul_mem ((starOfSub h H).mul_mem hg (hoff.1 hb')) ((starOfSub h H).inv_mem hg)
  have hSQ : SQTKGroup ↥A := by
    have := sqtkGroup_starOfSub cx hb (K := preStar h A) (preStar_le h A)
    rwa [S153L.starOfSub_preStar h hAH] at this
  obtain ⟨hAne, hB53⟩ := b53_of_offender (V := UTil T M V₁ H) (starOfSub h H) A B hAH
    (fun g hg j hj => (Subgroup.mem_normalizer_iff.mp (hAn hg) j).mp hj)
    (pCoreOf_starOfSub_H h) hSQ hoff (le_conjClosure B _) rfl
  have hLcomp : L ∈ cComp (preStar h A) := by
    have := lctx.comp
    rwa [hJ] at this
  exact ⟨A, hAH, hAn, hLcomp, S153L.starOfSub_mem_cComp h hAH hLcomp,
    h56 (UTil T M V₁ H) hV A hAne hB53⟩

theorem T_le_normalizer_of_k (h113 : StageLemma14113) (h56 : AsB56) (hb : InspBase cx H)
    {W : Subgroup G} {B : Subgroup (MulAut (UTil T M V₁ H))} {od : OffData hb W B} {L : Subgroup G}
    (lctx : LCtx hb od L) (hk : Y0 T Mc M ≤ conjClosure L T) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  obtain ⟨A, hAH, hAn, hLcomp, hLmem, hcases⟩ := star_setup h56 hb lctx
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := S153L.Y0_le_H hb
  have hTM : T ≤ Subgroup.normalizer (Y0 T Mc M : Set G) :=
    cx.c.hyp.T_le.trans (le_normalizer_Y0 cx.c.hyp)
  have hTY := starOfSub_le_normalizer h hTM
  have hYs : Group.IsSolvable ↥(starOfSub h (Y0 T Mc M)) :=
    S153L.isSolvable_starOfSub h hY0H
      (S153D.isSolvable_of_le_Y153 h113 cx.c.hyp ((Y0_le T Mc M).trans inf_le_left))
  have hT2 : IsPGroup 2 (starOfSub h T) := isPGroup_starOfSub h hTH h.sylow_H.2.1
  have hTHs : starOfSub h T ≤ starOfSub h H := starOfSub_mono h hTH
  have hmin : ∀ K' : Subgroup (MulAut (UTil T M V₁ H)),
      starOfSub h (Y0 T Mc M) ⊔ starOfSub h T ≤ K' → K' ≤ starOfSub h H → K' ≠ starOfSub h H →
        K' ≤ starOfSub h (M ⊓ H) := fun K' h1 h2 h3 => by
    refine overgroup_le_M_of_minimal cx hb ?_ h2 h3
    rwa [starOfSub_sup h hY0H hTH]
  have hYK : starOfSub h (Y0 T Mc M) ≤ conjClosure (starOfSub h L) (starOfSub h T) := by
    intro y hy
    obtain ⟨x, hxY, rfl⟩ := (mem_starOfSub h).mp hy
    have hle : conjClosure L T ≤ preStar h (conjClosure (starOfSub h L) (starOfSub h T)) := by
      refine conjClosure_le fun g hg l hl => ?_
      have hgH : g ∈ H := hTH hg
      have hlH : l ∈ H := (le_of_mem_cComp hLcomp |>.trans (preStar_le h A)) hl
      refine (mem_preStar_iff h).mpr ⟨H.mul_mem (H.mul_mem hgH hlH) (H.inv_mem hgH), ?_⟩
      have e : (⟨g * l * g⁻¹, H.mul_mem (H.mul_mem hgH hlH) (H.inv_mem hgH)⟩ : ↥H) =
          ⟨g, hgH⟩ * ⟨l, hlH⟩ * (⟨g, hgH⟩ : ↥H)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact mem_conjClosure ((mem_starOfSub h).mpr ⟨⟨g, hgH⟩, hg, rfl⟩)
        ((mem_starOfSub h).mpr ⟨⟨l, hlH⟩, hl, rfl⟩)
    exact ((mem_preStar_iff h).mp (hle (hk hxY))).2
  have hnorm := normalizes_component hcases hAH (fun g hg j hj =>
      (Subgroup.mem_normalizer_iff.mp (hAn hg) j).mp hj) hTHs hT2 hTY hYs hmin
    (fun x hx hx3 => S153L.theta_star hb hx3 hx) (fun E hE hE3 => S153L.hY3_star hb hE hE3)
    (exists_orderThree_star hb lctx) hLmem hYK
  intro y hy
  exact S153L.normalizes_of_star h hAH hAn hLcomp (hTH hy)
    (hnorm ((mem_starOfSub h).mpr ⟨⟨y, hTH hy⟩, hy, rfl⟩))

theorem conjClosure_eq_of_k (h113 : StageLemma14113) (h56 : AsB56) (hb : InspBase cx H)
    {W : Subgroup G} {B : Subgroup (MulAut (UTil T M V₁ H))} {od : OffData hb W B} {L : Subgroup G}
    (lctx : LCtx hb od L) (hk : Y0 T Mc M ≤ conjClosure L T) : conjClosure L T = L := by
  refine le_antisymm (conjClosure_le fun g hg l hl => ?_) (le_conjClosure L T)
  have := (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_of_k h113 h56 hb lctx hk hg) l).mp hl
  exact this

end Ctx

end SzN19

end CFSG.Quasithin
