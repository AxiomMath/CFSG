module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B5

section Invariance

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)}

theorem commV_inv {g : MulAut V} (hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    ∀ w ∈ commV L, g w ∈ commV L := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, v, rfl⟩ := hc
    have h1 : (g * x * g⁻¹) (g v) * (g v)⁻¹ ∈ commV L :=
      Subgroup.subset_closure ⟨g * x * g⁻¹, hg x hx, g v, rfl⟩
    have h2 : g (x v * v⁻¹) = (g * x * g⁻¹) (g v) * (g v)⁻¹ := by
      simp
    rw [h2]
    exact h1
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact (commV L).mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact (commV L).inv_mem hx

theorem fixV_inv {g : MulAut V} (hg : ∀ l ∈ L, g⁻¹ * l * g ∈ L) :
    ∀ w ∈ fixV L, g w ∈ fixV L := by
  intro w hw x hx
  have h1 := hw (g⁻¹ * x * g) (hg x hx)
  have h2 : (g⁻¹ * x * g) w = w := h1
  have : x (g w) = g w := by
    have := congrArg (fun y => g y) h2
    simpa using this
  exact this


theorem mem_stabSub_of_inv {W : Subgroup V} {g : MulAut V} (h1 : ∀ w ∈ W, g w ∈ W)
    (h2 : ∀ w ∈ W, g⁻¹ w ∈ W) : g ∈ stabSub W := by
  intro u
  refine ⟨fun hu => ?_, h1 u⟩
  have := h2 _ hu
  simpa using this

theorem le_stabSub_commV (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hGn : ∀ g ∈ G, g⁻¹ ∈ G) :
    G ≤ stabSub (commV L) := fun g hg =>
  mem_stabSub_of_inv (commV_inv (hn g hg)) (commV_inv (hn g⁻¹ (hGn g hg)))

theorem le_stabSub_fixV_inf_commV (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hGn : ∀ g ∈ G, g⁻¹ ∈ G) : G ≤ stabSub (fixV L ⊓ commV L) := fun g hg => by
  refine mem_stabSub_of_inv (fun w hw => ⟨fixV_inv (fun l hl => ?_) w hw.1,
    commV_inv (hn g hg) w hw.2⟩) (fun w hw => ⟨fixV_inv (fun l hl => ?_) w hw.1,
    commV_inv (hn g⁻¹ (hGn g hg)) w hw.2⟩)
  · have := hn g⁻¹ (hGn g hg) l hl
    simpa using this
  · have := hn g hg l hl
    simpa using this

end Invariance

section Stability

variable {V : Type} [CommGroup V]

theorem sq_trivial_of_stab (hV : ∀ v : V, v ^ 2 = 1) {W C : Subgroup V} {g : MulAut V}
    (h1 : ∀ w ∈ W, g w * w⁻¹ ∈ C) (h2 : ∀ c ∈ C, g c = c) : ∀ w ∈ W, (g * g) w = w := by
  intro w hw
  set u := g w * w⁻¹ with hu_def
  have hu : u ∈ C := h1 w hw
  have hgw : g w = w * u := by
    rw [hu_def, mul_comm (g w) w⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hgu : g u = u := h2 u hu
  have huu : u * u = 1 := by rw [← pow_two]; exact hV u
  show g (g w) = w
  calc g (g w) = g (w * u) := congrArg g hgw
    _ = g w * g u := map_mul g w u
    _ = (w * u) * u := by rw [hgu, hgw]
    _ = w := by rw [mul_assoc, huu, mul_one]

end Stability

section Faithful

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} (h : B51Hyp G L)
include h

theorem isSubnormal_L : CFSG.Open.IsSubnormal L G := by
  have hnormG : (L.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := normal_L h (g : MulAut V) g.2 x hx
    simpa using this
  exact CFSG.Open.IsSubnormal.step (le_G h) hnormG (CFSG.Open.IsSubnormal.refl _)

theorem normal_two_subgroup_bot {N : Subgroup (MulAut V)} (hNL : N ≤ L)
    (hNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : L ≤ Subgroup.normalizer (N : Set (MulAut V)) := le_normalizer_of_conj hNn
  have h1 : N ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNL hnorm hN2
  have h2 : pCoreOf 2 L ≤ pCoreOf 2 G := A4.pCoreOf_le_of_subnormal 2 (isSubnormal_L h)
  rw [o2_G h] at h2
  exact le_bot_iff.1 (h1.trans h2)

theorem L_inf_centSec_eq_bot (hV : ∀ v : V, v ^ 2 = 1) :
    L ⊓ centSec (commV L) (fixV L ⊓ commV L) = ⊥ := by
  have hn := normal_L h
  have hLG := le_G h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (fixV L ⊓ commV L) := le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg)
  set K := L ⊓ centSec (commV L) (fixV L ⊓ commV L) with hK
  apply normal_two_subgroup_bot h inf_le_left
  · intro l hl k hk
    exact ⟨L.mul_mem (L.mul_mem hl hk.1) (L.inv_mem hl),
      conj_mem_centSec (hGU (hLG hl)) (hGC (hLG hl)) hk.2⟩
  · intro k
    refine ⟨2, ?_⟩
    have hkL : (k : MulAut V) ∈ L := k.2.1
    have hkc := k.2.2
    have hk2 : ∀ w ∈ commV L, ((k : MulAut V) * k) w = w := by
      refine sq_trivial_of_stab hV (W := commV L) (C := fixV L ⊓ commV L) ?_ ?_
      · exact hkc.2
      · intro c hc
        exact hc.1 _ hkL
    have hk4 : ∀ v : V, (((k : MulAut V) * k) * ((k : MulAut V) * k)) v = v := by
      intro v
      refine sq_trivial_of_stab hV (W := ⊤) (C := commV L) ?_ hk2 v trivial
      intro w _
      have e : ((k : MulAut V) * k) w * w⁻¹ =
          (((k : MulAut V) ((k : MulAut V) w)) * ((k : MulAut V) w)⁻¹) *
            (((k : MulAut V) w) * w⁻¹) := by
        change (k : MulAut V) ((k : MulAut V) w) * w⁻¹ = _
        group
      rw [e]
      refine (commV L).mul_mem ?_ ?_
      · exact Subgroup.subset_closure ⟨k, hkL, (k : MulAut V) w, rfl⟩
      · exact Subgroup.subset_closure ⟨k, hkL, w, rfl⟩
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have e4 : (k : MulAut V) ^ 2 ^ 2 = ((k : MulAut V) * k) * ((k : MulAut V) * k) := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
    show ((k : MulAut V) ^ 2 ^ 2) v = v
    rw [e4]
    exact hk4 v


theorem sup_inf_centSec_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {T : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hT2 : IsPGroup 2 T) :
    (L ⊔ T) ⊓ centSec (commV L) (fixV L ⊓ commV L) = ⊥ := by
  have hn := normal_L h
  have hLG := le_G h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (fixV L ⊓ commV L) := le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg)
  have hMG : L ⊔ T ≤ G := sup_le hLG hTG
  have hLf := L_inf_centSec_eq_bot h hV
  set N := (L ⊔ T) ⊓ centSec (commV L) (fixV L ⊓ commV L) with hN
  have hNL : N ⊓ L = ⊥ := by
    rw [eq_bot_iff, ← hLf]
    intro x hx
    exact ⟨hx.2, hx.1.2⟩
  have hNn : ∀ m ∈ L ⊔ T, ∀ x ∈ N, m * x * m⁻¹ ∈ N := by
    intro m hm x hx
    exact ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hm hx.1) ((L ⊔ T).inv_mem hm),
      conj_mem_centSec (hGU (hMG hm)) (hGC (hMG hm)) hx.2⟩
  have hLn' := sup_normal_L h hTG
  have hcomm : ⁅N, L⁆ ≤ N ⊓ L :=
    B1Red.commutator_le_inf_of_normalizes (fun n hn l hl => hLn' n hn.1 l hl)
      (fun l hl n hn => hNn l (Subgroup.mem_sup_left hl) n hn)
  rw [hNL] at hcomm
  have hNc : N ≤ Subgroup.centralizer (L : Set (MulAut V)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 hcomm)
  have hNle : N ≤ L := fun x hx =>
    sup_inf_centralizer_le h hTG hT2 ⟨hx.1, hNc hx⟩
  rw [eq_bot_iff, ← hNL]
  exact fun x hx => ⟨hx, hNle hx⟩

end Faithful

section Offender

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem exists_offender_le_sylow {T A : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G)
    (hA : IsFFStarOffender G A) :
    ∃ x ∈ G, IsFFStarOffender G (B1.conjAut x⁻¹ A) ∧ B1.conjAut x⁻¹ A ≤ T := by
  obtain ⟨x, hxG, hle⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hT hA.1 hA.2.2.1.isPGroup
  refine ⟨x, hxG, B1.isFFStarOffender_conjAut hA (G.inv_mem hxG), ?_⟩
  intro y hy
  have := B1.mem_conjAut.1 hy
  have h2 : x⁻¹⁻¹ ∈ G := G.inv_mem (G.inv_mem hxG)
  have hy' : x * y * x⁻¹ ∈ A := by simpa using this
  have := hle hy'
  rw [CFSG.Quasithin.mem_conjSub] at this
  simpa [mul_assoc] using this

end Offender

section B42Section

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem irr_data {I : Subgroup V} (hU : I ∈ IrrPlus L (⊤ : Subgroup V)) :
    (∀ x ∈ L, ∀ w ∈ I, x w ∈ I) ∧ commSub I L = I ∧ I ⊓ fixV L < I ∧
      ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → I ⊓ fixV L ≤ J → J ≤ I →
        J = I ⊓ fixV L ∨ J = I :=
  mem_irrPlus_top_iff.1 hU

theorem b4Hyp_section (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT2 : IsPGroup 2 T) :
    B4Hyp (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L))
      (autSec L (commV L) (fixV L ⊓ commV L)) := by
  have hn := normal_L h
  have hLG := le_G h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (fixV L ⊓ commV L) :=
    le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg)
  have hMG : L ⊔ T ≤ G := sup_le hLG hTG
  have hfL := L_inf_centSec_eq_bot h hV
  have hfM := sup_inf_centSec_eq_bot h hV hTG hT2
  obtain ⟨hinv, -, hlt, hirr⟩ := irr_data hU
  refine ⟨sqtk_autSec (hMG.trans hGU) (hMG.trans hGC) hfM (sqtk_sup h hTG hT2), ?_,
    isQuasisimple_autSec (hLG.trans hGU) (hLG.trans hGC) hfL (quasi_L h), ?_⟩
  · exact (genFitting_autSec le_sup_left (hMG.trans hGU) (hMG.trans hGC) hfM
      (genFitting_sup_eq h hTG hT2)).symm
  · rw [inf_comm] at hlt hirr
    exact isIrrSec_autSec hlt hirr (hLG.trans hGU) (hLG.trans hGC)


theorem exists_offender (h : B51Hyp G L) : ∃ A, IsFFStarOffender G A := by
  by_contra hnone
  push Not at hnone
  have hJ : ffJ G = ⊥ := by
    unfold ffJ
    simp [hnone]
  have hG : G = ⊥ := h.2.2.2.2.2.trans hJ
  have hLG := le_G h
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open (quasi_L h))
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
  apply hx
  apply Subtype.ext
  have := hLG x.2
  rw [hG, Subgroup.mem_bot] at this
  exact this

theorem exists_section_offender (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∈ IrrPlus L ⊤) {T : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) :
    ∃ A, IsFFStarOffender G A ∧ A ≤ T ∧ ∃ B, B ≤ autSec A (commV L) (fixV L ⊓ commV L) ∧
      IsFFStarOffender (autSec (L ⊔ T) (commV L) (fixV L ⊓ commV L)) B := by
  have hn := normal_L h
  have hLG := le_G h
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (fixV L ⊓ commV L) :=
    le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg)
  have hMG : L ⊔ T ≤ G := sup_le hLG hTG
  obtain ⟨A₀, hA₀⟩ := exists_offender h
  obtain ⟨x, hxG, hA', hA'T⟩ := exists_offender_le_sylow hT hA₀
  set A := B1.conjAut x⁻¹ A₀ with hA
  have hAM : IsFFStarOffender (L ⊔ T) A :=
    ⟨hA'T.trans le_sup_right, hA'.2.1, hA'.2.2.1, hA'.2.2.2⟩
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := irr_data hU
  have hS : ¬ commSub (commV L) (quasithinGenFitting (L ⊔ T)) ≤ fixV L ⊓ commV L := by
    rw [genFitting_sup_eq h hTG hT2, hcomm]
    intro hle
    have h1 : fixV L ⊓ commV L = commV L := le_antisymm inf_le_right hle
    rw [inf_comm, h1] at hlt
    exact lt_irrefl _ hlt
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ T)) := by
    rw [genFitting_sup_eq h hTG hT2]; exact quasi_L h
  obtain ⟨-, ⟨B, hBA, hB⟩, -⟩ := B1_5_8 hV hAM (W := commV L) (U := fixV L ⊓ commV L) inf_le_right
    (hMG.trans hGU) (hMG.trans hGC) hq (pCoreOf_sup_eq_bot h hTG hT2) hS
  exact ⟨A, hA', hA'T, B, hBA, hB⟩

end B42Section

end B5

end CFSG.Quasithin
