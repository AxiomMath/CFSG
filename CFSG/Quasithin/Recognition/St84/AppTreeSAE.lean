module

public import CFSG.Quasithin.Recognition.St84.AppTreeSA
import CFSG.Quasithin.Background.F1VertexCore
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def f112saX1 (L1 L2 S : Subgroup H) : Subgroup H :=
  oTwoRes L1 ⊓ bigB L1 L2 S

@[expose] noncomputable def f112saX2 (L1 L2 S : Subgroup H) : Subgroup H :=
  oTwoRes L2 ⊓ bigB L1 L2 S

@[expose] noncomputable def f112saK (L1 L2 S : Subgroup H) : Subgroup H :=
  f112saX1 L1 L2 S ⊔ f112saX2 L1 L2 S

@[expose] noncomputable def f112saP1' (L1 L2 S : Subgroup H) : Subgroup H :=
  oTwoRes L1 ⊔ f112saX2 L1 L2 S

@[expose] noncomputable def f112saP2' (L1 L2 S : Subgroup H) : Subgroup H :=
  oTwoRes L2 ⊔ f112saX1 L1 L2 S

noncomputable abbrev f112saE0 (L1 L2 S : Subgroup H) : Type :=
  ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)

noncomputable abbrev f112saK' (L1 L2 S : Subgroup H) : Subgroup (f112saE0 L1 L2 S) :=
  (f112saK L1 L2 S).subgroupOf (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)

noncomputable abbrev f112saQ (L1 L2 S : Subgroup H) : Type :=
  f112saE0 L1 L2 S ⧸ f112saK' L1 L2 S

theorem f112sa_bigB_le_normalizer_oTwoRes_left
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub b (oTwoRes L1) = oTwoRes L1
  rw [conjSub_oTwoRes,
    F1.conjSub_eq_of_mem_normalizer (bigB_le_normalizer_of_hyp111 hF.1 hb)]

theorem f112sa_bigB_le_normalizer_oTwoRes_right
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) := by
  have hN : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) := by
    have h := bigB_le_normalizer_of_hyp111 hF.1.symm
    rwa [bigB_comm] at h
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub b (oTwoRes L2) = oTwoRes L2
  rw [conjSub_oTwoRes, F1.conjSub_eq_of_mem_normalizer (hN hb)]

theorem f112sa_bigB_le_normalizer_X1
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (f112saX1 L1 L2 S : Set H) := by
  have hO := f112sa_bigB_le_normalizer_oTwoRes_left hF
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx, hxB⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hO hb) x).mp hx,
      bigB L1 L2 S |>.mul_mem (bigB L1 L2 S |>.mul_mem hb hxB)
        (bigB L1 L2 S |>.inv_mem hb)⟩
  · rintro ⟨hx, hxB⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hO hb) x).mpr hx, ?_⟩
    have h := (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem
      ((bigB L1 L2 S).inv_mem hb) hxB) hb
    simpa [mul_assoc] using h

theorem f112sa_bigB_le_normalizer_X2
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (f112saX2 L1 L2 S : Set H) := by
  have hO := f112sa_bigB_le_normalizer_oTwoRes_right hF
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx, hxB⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hO hb) x).mp hx,
      bigB L1 L2 S |>.mul_mem (bigB L1 L2 S |>.mul_mem hb hxB)
        (bigB L1 L2 S |>.inv_mem hb)⟩
  · rintro ⟨hx, hxB⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hO hb) x).mpr hx, ?_⟩
    have h := (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem
      ((bigB L1 L2 S).inv_mem hb) hxB) hb
    simpa [mul_assoc] using h

theorem f112sa_X1_le_bigB (L1 L2 S : Subgroup H) :
    f112saX1 L1 L2 S ≤ bigB L1 L2 S := inf_le_right

theorem f112sa_X2_le_bigB (L1 L2 S : Subgroup H) :
    f112saX2 L1 L2 S ≤ bigB L1 L2 S := inf_le_right

theorem f112sa_X1_le_oTwoRes (L1 L2 S : Subgroup H) :
    f112saX1 L1 L2 S ≤ oTwoRes L1 := inf_le_left

theorem f112sa_X2_le_oTwoRes (L1 L2 S : Subgroup H) :
    f112saX2 L1 L2 S ≤ oTwoRes L2 := inf_le_left

theorem f112sa_K_le_bigB (L1 L2 S : Subgroup H) :
    f112saK L1 L2 S ≤ bigB L1 L2 S :=
  sup_le (f112sa_X1_le_bigB L1 L2 S) (f112sa_X2_le_bigB L1 L2 S)

theorem f112sa_bigB_le_normalizer_K
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
  F1.le_normalizer_sup (f112sa_bigB_le_normalizer_X1 hF) (f112sa_bigB_le_normalizer_X2 hF)

theorem f112saK'_normal_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) : (f112saK' L1 L2 S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgB : (g : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact g.2
  exact (Subgroup.mem_normalizer_iff.mp (f112sa_bigB_le_normalizer_K hF hgB) (n : H)).mp hn

theorem f112sa_L1_le_oTwoRes_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    L1 ≤ oTwoRes L1 ⊔ bigB L1 L2 S := by
  refine (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h1.sylow).trans
    (sup_le_sup_left (inf_le_left.trans le_sup_right) (oTwoRes L1))

theorem f112sa_L2_le_oTwoRes_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    L2 ≤ oTwoRes L2 ⊔ bigB L1 L2 S := by
  refine (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h2.sylow).trans
    (sup_le_sup_left (inf_le_left.trans le_sup_right) (oTwoRes L2))

theorem f112sa_P1_eq_oTwoRes_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P1 L1 L2 S = oTwoRes L1 ⊔ bigB L1 L2 S := by
  refine le_antisymm ?_ ?_
  · rw [f112P1]
    exact sup_le (f112sa_L1_le_oTwoRes_sup_bigB hF) le_sup_right
  · rw [f112P1]
    exact sup_le_sup (oTwoRes_le L1) le_rfl

theorem f112sa_P2_eq_oTwoRes_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P2 L1 L2 S = oTwoRes L2 ⊔ bigB L1 L2 S := by
  refine le_antisymm ?_ ?_
  · rw [f112P2]
    exact sup_le (f112sa_L2_le_oTwoRes_sup_bigB hF) le_sup_right
  · rw [f112P2]
    exact sup_le_sup (oTwoRes_le L2) le_rfl

theorem f112sa_P1'_le_P1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) : f112saP1' L1 L2 S ≤ f112P1 L1 L2 S := by
  rw [f112sa_P1_eq_oTwoRes_sup_bigB hF]
  exact sup_le le_sup_left ((f112sa_X2_le_bigB L1 L2 S).trans le_sup_right)

theorem f112sa_P2'_le_P2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) : f112saP2' L1 L2 S ≤ f112P2 L1 L2 S := by
  rw [f112sa_P2_eq_oTwoRes_sup_bigB hF]
  exact sup_le le_sup_left ((f112sa_X1_le_bigB L1 L2 S).trans le_sup_right)

theorem f112sa_P1_eq_P1'_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P1 L1 L2 S = f112saP1' L1 L2 S ⊔ bigB L1 L2 S := by
  rw [f112sa_P1_eq_oTwoRes_sup_bigB hF]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_sup_left
      · exact (f112sa_X2_le_bigB L1 L2 S).trans le_sup_right
    · exact le_sup_right

theorem f112sa_P2_eq_P2'_sup_bigB
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P2 L1 L2 S = f112saP2' L1 L2 S ⊔ bigB L1 L2 S := by
  rw [f112sa_P2_eq_oTwoRes_sup_bigB hF]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_sup_left
      · exact (f112sa_X1_le_bigB L1 L2 S).trans le_sup_right
    · exact le_sup_right

theorem f112sa_P1'_inf_bigB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    f112saP1' L1 L2 S ⊓ bigB L1 L2 S = f112saK L1 L2 S := by
  have hX2norm : f112saX2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H) :=
    (f112sa_X2_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_left hF)
  refine le_antisymm ?_ ?_
  · rintro p ⟨hpP1', hpB⟩
    have hmem : p ∈ (oTwoRes L1 : Set H) * (f112saX2 L1 L2 S : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (oTwoRes L1)
        (f112saX2 L1 L2 S) hX2norm]
      exact hpP1'
    obtain ⟨a, ha, x, hx, rfl⟩ := hmem
    have hxB : x ∈ bigB L1 L2 S := f112sa_X2_le_bigB L1 L2 S hx
    have haB : a ∈ bigB L1 L2 S := by
      have := (bigB L1 L2 S).mul_mem hpB ((bigB L1 L2 S).inv_mem hxB)
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem_sup (show a ∈ f112saX1 L1 L2 S from ⟨ha, haB⟩) hx
  · refine le_inf ?_ (f112sa_K_le_bigB L1 L2 S)
    exact sup_le ((show f112saX1 L1 L2 S ≤ oTwoRes L1 from inf_le_left).trans le_sup_left)
      (show f112saX2 L1 L2 S ≤ f112saP1' L1 L2 S from le_sup_right)

theorem f112sa_P2'_inf_bigB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    f112saP2' L1 L2 S ⊓ bigB L1 L2 S = f112saK L1 L2 S := by
  have hX1norm : f112saX1 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    (f112sa_X1_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_right hF)
  refine le_antisymm ?_ ?_
  · rintro p ⟨hpP2', hpB⟩
    have hmem : p ∈ (oTwoRes L2 : Set H) * (f112saX1 L1 L2 S : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (oTwoRes L2)
        (f112saX1 L1 L2 S) hX1norm]
      exact hpP2'
    obtain ⟨a, ha, x, hx, rfl⟩ := hmem
    have hxB : x ∈ bigB L1 L2 S := f112sa_X1_le_bigB L1 L2 S hx
    have haB : a ∈ bigB L1 L2 S := by
      have := (bigB L1 L2 S).mul_mem hpB ((bigB L1 L2 S).inv_mem hxB)
      simpa [mul_assoc] using this
    exact (f112saK L1 L2 S).mul_mem
      (Subgroup.mem_sup_right (show a ∈ f112saX2 L1 L2 S from ⟨ha, haB⟩))
      (Subgroup.mem_sup_left hx)
  · refine le_inf ?_ (f112sa_K_le_bigB L1 L2 S)
    exact sup_le (show f112saX1 L1 L2 S ≤ f112saP2' L1 L2 S from le_sup_right)
      ((show f112saX2 L1 L2 S ≤ oTwoRes L2 from inf_le_left).trans le_sup_left)

theorem f112sa_P1_le_normalizer_P1'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P1 L1 L2 S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) := by
  have hO : oTwoRes L1 ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    (show oTwoRes L1 ≤ f112saP1' L1 L2 S from le_sup_left).trans Subgroup.le_normalizer
  have hB : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    F1.le_normalizer_sup (f112sa_bigB_le_normalizer_oTwoRes_left hF)
      (f112sa_bigB_le_normalizer_X2 hF)
  rw [f112sa_P1_eq_oTwoRes_sup_bigB hF]
  exact sup_le hO hB

theorem f112sa_P2_le_normalizer_P2'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    f112P2 L1 L2 S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) := by
  have hO : oTwoRes L2 ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (show oTwoRes L2 ≤ f112saP2' L1 L2 S from le_sup_left).trans Subgroup.le_normalizer
  have hB : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    F1.le_normalizer_sup (f112sa_bigB_le_normalizer_oTwoRes_right hF)
      (f112sa_bigB_le_normalizer_X1 hF)
  rw [f112sa_P2_eq_oTwoRes_sup_bigB hF]
  exact sup_le hO hB

theorem f112sa_P1'_normal {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    (f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S) |>.Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (f112sa_P1'_le_P1 hF)).mpr
    (f112sa_P1_le_normalizer_P1' hF)

theorem f112sa_P2'_normal {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    (f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S) |>.Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (f112sa_P2'_le_P2 hF)).mpr
    (f112sa_P2_le_normalizer_P2' hF)

noncomputable def f112saPhi1 (L1 L2 S : Subgroup H)
    [hN : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    f112saE0 L1 L2 S →*
      (↥(f112P1 L1 L2 S) ⧸ (f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) :=
  (QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))).comp
    (Subgroup.inclusion inf_le_left)

noncomputable def f112saPhi2 (L1 L2 S : Subgroup H)
    [hN : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    f112saE0 L1 L2 S →*
      (↥(f112P2 L1 L2 S) ⧸ (f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) :=
  (QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))).comp
    (Subgroup.inclusion inf_le_right)

theorem f112saPhi1_surjective_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    Function.Surjective (f112saPhi1 L1 L2 S) := by
  intro q
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective
    ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) q
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S).trans
      (f112sa_P1_le_normalizer_P1' hF)
  have hp : (p : H) ∈ f112saP1' L1 L2 S ⊔ bigB L1 L2 S := by
    rw [← f112sa_P1_eq_P1'_sup_bigB hF]
    exact p.2
  have hp' : (p : H) ∈ (↑(f112saP1' L1 L2 S ⊔ bigB L1 L2 S) : Set H) := hp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (f112saP1' L1 L2 S)
    (bigB L1 L2 S) hBN] at hp'
  have hmem : (p : H) ∈ (f112saP1' L1 L2 S : Set H) * (bigB L1 L2 S : Set H) := hp'
  obtain ⟨n, hn, b, hb, hnb⟩ := hmem
  have hb' : b ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S := by
    rw [f112_inf_eq_bigB_of_hyp111R hR]
    exact hb
  refine ⟨⟨b, hb'⟩, ?_⟩
  have hp_split : p = ⟨n, f112sa_P1'_le_P1 hF hn⟩ * ⟨b, hb'.1⟩ :=
    Subtype.ext hnb.symm
  have hmk : QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) p =
      QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) ⟨b, hb'.1⟩ := by
    rw [hp_split, map_mul]
    have hn1 : QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))
        ⟨n, f112sa_P1'_le_P1 hF hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    rw [hn1, one_mul]
  show QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))
      (Subgroup.inclusion inf_le_left ⟨b, hb'⟩) = _
  have hincl : (Subgroup.inclusion inf_le_left ⟨b, hb'⟩ : ↥(f112P1 L1 L2 S)) =
      ⟨b, hb'.1⟩ := rfl
  rw [hincl, ← hmk]

theorem f112saPhi2_surjective_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    Function.Surjective (f112saPhi2 L1 L2 S) := by
  intro q
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective
    ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) q
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S).trans
      (f112sa_P2_le_normalizer_P2' hF)
  have hp : (p : H) ∈ f112saP2' L1 L2 S ⊔ bigB L1 L2 S := by
    rw [← f112sa_P2_eq_P2'_sup_bigB hF]
    exact p.2
  have hp' : (p : H) ∈ (↑(f112saP2' L1 L2 S ⊔ bigB L1 L2 S) : Set H) := hp
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (f112saP2' L1 L2 S)
    (bigB L1 L2 S) hBN] at hp'
  have hmem : (p : H) ∈ (f112saP2' L1 L2 S : Set H) * (bigB L1 L2 S : Set H) := hp'
  obtain ⟨n, hn, b, hb, hnb⟩ := hmem
  have hb' : b ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S := by
    rw [f112_inf_eq_bigB_of_hyp111R hR]
    exact hb
  refine ⟨⟨b, hb'⟩, ?_⟩
  have hp_split : p = ⟨n, f112sa_P2'_le_P2 hF hn⟩ * ⟨b, hb'.2⟩ :=
    Subtype.ext hnb.symm
  have hmk : QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) p =
      QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) ⟨b, hb'.2⟩ := by
    rw [hp_split, map_mul]
    have hn1 : QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))
        ⟨n, f112sa_P2'_le_P2 hF hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    rw [hn1, one_mul]
  show QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))
      (Subgroup.inclusion inf_le_right ⟨b, hb'⟩) = _
  have hincl : (Subgroup.inclusion inf_le_right ⟨b, hb'⟩ : ↥(f112P2 L1 L2 S)) =
      ⟨b, hb'.2⟩ := rfl
  rw [hincl, ← hmk]

theorem f112saPhi1_ker_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    (f112saPhi1 L1 L2 S).ker = f112saK' L1 L2 S := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change (QuotientGroup.mk (Subgroup.inclusion inf_le_left x) :
      ↥(f112P1 L1 L2 S) ⧸ (f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) = 1 ↔
    (x : H) ∈ f112saK L1 L2 S
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hxB : (x : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact x.2
  constructor
  · intro hx
    have : (x : H) ∈ f112saP1' L1 L2 S ⊓ bigB L1 L2 S := ⟨hx, hxB⟩
    rwa [f112sa_P1'_inf_bigB hF] at this
  · intro hx
    have : (x : H) ∈ f112saP1' L1 L2 S ⊓ bigB L1 L2 S := by
      rw [f112sa_P1'_inf_bigB hF]
      exact hx
    exact this.1

theorem f112saPhi2_ker_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    (f112saPhi2 L1 L2 S).ker = f112saK' L1 L2 S := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change (QuotientGroup.mk (Subgroup.inclusion inf_le_right x) :
      ↥(f112P2 L1 L2 S) ⧸ (f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) = 1 ↔
    (x : H) ∈ f112saK L1 L2 S
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hxB : (x : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact x.2
  constructor
  · intro hx
    have : (x : H) ∈ f112saP2' L1 L2 S ⊓ bigB L1 L2 S := ⟨hx, hxB⟩
    rwa [f112sa_P2'_inf_bigB hF] at this
  · intro hx
    have : (x : H) ∈ f112saP2' L1 L2 S ⊓ bigB L1 L2 S := by
      rw [f112sa_P2'_inf_bigB hF]
      exact hx
    exact this.1

@[expose] noncomputable def f112saE1R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    f112saQ L1 L2 S ≃*
      (↥(f112P1 L1 L2 S) ⧸ (f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) :=
  (QuotientGroup.quotientMulEquivOfEq (f112saPhi1_ker_of_hyp111R hF hR).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := f112saPhi1 L1 L2 S)
      (f112saPhi1_surjective_of_hyp111R hF hR))

@[expose] noncomputable def f112saE2R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    f112saQ L1 L2 S ≃*
      (↥(f112P2 L1 L2 S) ⧸ (f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) :=
  (QuotientGroup.quotientMulEquivOfEq (f112saPhi2_ker_of_hyp111R hF hR).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := f112saPhi2 L1 L2 S)
      (f112saPhi2_surjective_of_hyp111R hF hR))

theorem f112saE1R_mk {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    (x : f112saE0 L1 L2 S) :
    f112saE1R hF hR (QuotientGroup.mk' (f112saK' L1 L2 S) x) =
      QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))
        (Subgroup.inclusion inf_le_left x) := by
  rw [f112saE1R, MulEquiv.trans_apply]
  change (QuotientGroup.quotientKerEquivOfSurjective (φ := f112saPhi1 L1 L2 S)
      (f112saPhi1_surjective_of_hyp111R hF hR))
      ((QuotientGroup.quotientMulEquivOfEq (f112saPhi1_ker_of_hyp111R hF hR).symm)
        (QuotientGroup.mk x : f112saE0 L1 L2 S ⧸ f112saK' L1 L2 S)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  change QuotientGroup.kerLift (f112saPhi1 L1 L2 S)
    (QuotientGroup.mk x : f112saE0 L1 L2 S ⧸ (f112saPhi1 L1 L2 S).ker) = _
  rw [QuotientGroup.kerLift_mk]
  rfl

theorem f112saE2R_mk {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal]
    (x : f112saE0 L1 L2 S) :
    f112saE2R hF hR (QuotientGroup.mk' (f112saK' L1 L2 S) x) =
      QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))
        (Subgroup.inclusion inf_le_right x) := by
  rw [f112saE2R, MulEquiv.trans_apply]
  change (QuotientGroup.quotientKerEquivOfSurjective (φ := f112saPhi2 L1 L2 S)
      (f112saPhi2_surjective_of_hyp111R hF hR))
      ((QuotientGroup.quotientMulEquivOfEq (f112saPhi2_ker_of_hyp111R hF hR).symm)
        (QuotientGroup.mk x : f112saE0 L1 L2 S ⧸ f112saK' L1 L2 S)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  change QuotientGroup.kerLift (f112saPhi2 L1 L2 S)
    (QuotientGroup.mk x : f112saE0 L1 L2 S ⧸ (f112saPhi2 L1 L2 S).ker) = _
  rw [QuotientGroup.kerLift_mk]
  rfl

@[expose] noncomputable def f112saChi1R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    ↥(f112P1 L1 L2 S) →* f112saQ L1 L2 S :=
  (f112saE1R hF hR).symm.toMonoidHom.comp
    (QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)))

@[expose] noncomputable def f112saChi2R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    ↥(f112P2 L1 L2 S) →* f112saQ L1 L2 S :=
  (f112saE2R hF hR).symm.toMonoidHom.comp
    (QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)))

theorem f112saChi1R_incl {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    (x : f112saE0 L1 L2 S) :
    f112saChi1R hF hR (Subgroup.inclusion inf_le_left x) =
      QuotientGroup.mk' (f112saK' L1 L2 S) x := by
  change (f112saE1R hF hR).symm
    (QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S))
      (Subgroup.inclusion inf_le_left x)) = _
  rw [← f112saE1R_mk hF hR x, MulEquiv.symm_apply_apply]

theorem f112saChi2R_incl {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal]
    (x : f112saE0 L1 L2 S) :
    f112saChi2R hF hR (Subgroup.inclusion inf_le_right x) =
      QuotientGroup.mk' (f112saK' L1 L2 S) x := by
  change (f112saE2R hF hR).symm
    (QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S))
      (Subgroup.inclusion inf_le_right x)) = _
  rw [← f112saE2R_mk hF hR x, MulEquiv.symm_apply_apply]

theorem f112saChi1R_eq_one_iff {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    (p : ↥(f112P1 L1 L2 S)) :
    f112saChi1R hF hR p = 1 ↔ (p : H) ∈ f112saP1' L1 L2 S := by
  have hiff : f112saChi1R hF hR p = 1 ↔
      QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) p = 1 := by
    constructor
    · intro h
      have := congrArg (f112saE1R hF hR) h
      simpa [f112saChi1R] using this
    · intro h
      change (f112saE1R hF hR).symm
        (QuotientGroup.mk' ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) p) = 1
      rw [h, map_one]
  rw [hiff]
  change (QuotientGroup.mk p : ↥(f112P1 L1 L2 S) ⧸
    (f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)) = 1 ↔
    (p : H) ∈ f112saP1' L1 L2 S
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem f112saChi2R_eq_one_iff {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal]
    (p : ↥(f112P2 L1 L2 S)) :
    f112saChi2R hF hR p = 1 ↔ (p : H) ∈ f112saP2' L1 L2 S := by
  have hiff : f112saChi2R hF hR p = 1 ↔
      QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) p = 1 := by
    constructor
    · intro h
      have := congrArg (f112saE2R hF hR) h
      simpa [f112saChi2R] using this
    · intro h
      change (f112saE2R hF hR).symm
        (QuotientGroup.mk' ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) p) = 1
      rw [h, map_one]
  rw [hiff]
  change (QuotientGroup.mk p : ↥(f112P2 L1 L2 S) ⧸
    (f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)) = 1 ↔
    (p : H) ∈ f112saP2' L1 L2 S
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem f112saChi1R_comp_toA {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal] :
    (f112saChi1R hF hR).comp (f112Gold L1 L2 S).toA =
      QuotientGroup.mk' (f112saK' L1 L2 S) :=
  MonoidHom.ext fun x => f112saChi1R_incl hF hR x

theorem f112saChi2R_comp_toB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    (f112saChi2R hF hR).comp (f112Gold L1 L2 S).toB =
      QuotientGroup.mk' (f112saK' L1 L2 S) :=
  MonoidHom.ext fun x => f112saChi2R_incl hF hR x

@[expose] noncomputable def f112saChiFamilyR {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    ∀ i : Bool, goldVertexGroup ↥(f112P1 L1 L2 S) ↥(f112P2 L1 L2 S) i →*
      f112saQ L1 L2 S
  | true => f112saChi1R hF hR
  | false => f112saChi2R hF hR

theorem f112saChiFamilyR_compat {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    ∀ i, (f112saChiFamilyR hF hR i).comp ((f112Gold L1 L2 S).diagram i) =
      QuotientGroup.mk' (f112saK' L1 L2 S)
  | true => f112saChi1R_comp_toA hF hR
  | false => f112saChi2R_comp_toB hF hR

@[expose] noncomputable def f112saChiR {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    (f112Gold L1 L2 S).Universal →* f112saQ L1 L2 S :=
  Monoid.PushoutI.lift (φ := (f112Gold L1 L2 S).diagram)
    (f112saChiFamilyR hF hR) (QuotientGroup.mk' (f112saK' L1 L2 S))
    (f112saChiFamilyR_compat hF hR)

theorem f112saChiR_ofA {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal]
    (p : ↥(f112P1 L1 L2 S)) :
    f112saChiR hF hR ((f112Gold L1 L2 S).ofA p) = f112saChi1R hF hR p := by
  change Monoid.PushoutI.lift (φ := (f112Gold L1 L2 S).diagram)
      (f112saChiFamilyR hF hR) (QuotientGroup.mk' (f112saK' L1 L2 S))
      (f112saChiFamilyR_compat hF hR) (Monoid.PushoutI.of true p) = f112saChi1R hF hR p
  rw [Monoid.PushoutI.lift_of]
  rfl

theorem f112saChiR_ofB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal]
    (p : ↥(f112P2 L1 L2 S)) :
    f112saChiR hF hR ((f112Gold L1 L2 S).ofB p) = f112saChi2R hF hR p := by
  change Monoid.PushoutI.lift (φ := (f112Gold L1 L2 S).diagram)
      (f112saChiFamilyR hF hR) (QuotientGroup.mk' (f112saK' L1 L2 S))
      (f112saChiFamilyR_compat hF hR) (Monoid.PushoutI.of false p) = f112saChi2R hF hR p
  rw [Monoid.PushoutI.lift_of]
  rfl

theorem f112saQ_isPGroup_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) (h1 : VS3 L1)
    [hN : (f112saK' L1 L2 S).Normal] :
    IsPGroup 2 (f112saQ L1 L2 S) := by
  refine CFSG.Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem
    (f112saK' L1 L2 S) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hxodd : Odd (orderOf (x : H)) := by
    have hne : ¬ Even (orderOf x) := by
      intro he
      exact hx (even_iff_two_dvd.mp he)
    rw [Subgroup.orderOf_coe]
    exact Nat.not_even_iff_odd.mp hne
  have hxB : (x : H) ∈ bigB L1 L2 S := by
    rw [← f112_inf_eq_bigB_of_hyp111R hR]
    exact x.2
  have hxP2 : (x : H) ∈ L2 ⊔ bigB L1 L2 S :=
    (le_sup_right (a := L2) (b := bigB L1 L2 S)) hxB
  have hxO : (x : H) ∈ oTwoRes L2 := f112sa_mem_oTwoRes_of_odd hF h1 hxP2 hxodd
  exact Subgroup.mem_sup_right (show (x : H) ∈ f112saX2 L1 L2 S from ⟨hxO, hxB⟩)

theorem f112saQ_eq_one_of_odd_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) (h1 : VS3 L1)
    [hN : (f112saK' L1 L2 S).Normal]
    {q : f112saQ L1 L2 S} (hodd : Odd (orderOf q)) : q = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ orderOf q := (f112saQ_isPGroup_of_hyp111R hF hR h1).dvd_orderOf hne
  have hne' : ¬ Even (orderOf q) := Nat.not_even_iff_odd.mpr hodd
  exact hne' (even_iff_two_dvd.mpr h2)

theorem f112saEOdd_le_ker_chi_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) (h1 : VS3 L1)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    f112EOdd L1 L2 S ≤ (f112saChiR hF.toW hR).ker := by
  rw [f112EOdd, Subgroup.closure_le]
  rintro u ⟨-, huodd⟩
  change f112saChiR hF.toW hR u = 1
  exact f112saQ_eq_one_of_odd_of_hyp111R hF hR h1
    (huodd.of_dvd_nat (orderOf_map_dvd (f112saChiR hF.toW hR) u))

theorem f112sa_subgroupOf_closure_eq {K L : Subgroup H} {s : Set H}
    (hK : K = Subgroup.closure s) (hs : s ⊆ L) :
    K.subgroupOf L = Subgroup.closure ((↑) ⁻¹' s : Set L) := by
  subst hK
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le L).mpr hs)]
  rw [MonoidHom.map_closure]
  have himg : (⇑L.subtype '' (Subtype.val ⁻¹' s) : Set H) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [himg]

theorem f112sa_ofA_eq_ofB_of_mem_inf (L1 L2 S : Subgroup H)
    {x : H} (hx : x ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S) :
    (f112Gold L1 L2 S).ofA ⟨x, hx.1⟩ = (f112Gold L1 L2 S).ofB ⟨x, hx.2⟩ := by
  let c : f112saE0 L1 L2 S := ⟨x, hx⟩
  have h1 : (f112Gold L1 L2 S).toA c = ⟨x, hx.1⟩ := rfl
  have h2 : (f112Gold L1 L2 S).toB c = ⟨x, hx.2⟩ := rfl
  rw [← h1, ← h2, (f112Gold L1 L2 S).ofA_toA, (f112Gold L1 L2 S).ofB_toB]

theorem f112sa_oTwoRes_left_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((oTwoRes L1).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112EOdd L1 L2 S := by
  rw [f112sa_subgroupOf_closure_eq (K := oTwoRes L1) (L := f112P1 L1 L2 S)
    (s := {x | x ∈ L1 ∧ ∃ m, Odd m ∧ x ^ m = 1}) rfl]
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le (f112EOdd L1 L2 S)).mpr ?_
    rintro u ⟨a, ha, rfl⟩
    obtain ⟨haL, m, hm, ham⟩ := ha
    have hoddH : Odd (orderOf (a : H)) :=
      hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ham)
    have hodd : Odd (orderOf ((f112Gold L1 L2 S).ofA a)) := by
      rw [orderOf_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective a,
        ← Subgroup.orderOf_coe]
      exact hoddH
    exact Subgroup.subset_closure ⟨Or.inl ⟨a, rfl⟩, hodd⟩
  · rintro x ⟨hxL, -⟩
    exact Subgroup.mem_sup_left hxL

theorem f112sa_oTwoRes_right_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((oTwoRes L2).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112EOdd L1 L2 S := by
  rw [f112sa_subgroupOf_closure_eq (K := oTwoRes L2) (L := f112P2 L1 L2 S)
    (s := {x | x ∈ L2 ∧ ∃ m, Odd m ∧ x ^ m = 1}) rfl]
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le (f112EOdd L1 L2 S)).mpr ?_
    rintro u ⟨a, ha, rfl⟩
    obtain ⟨haL, m, hm, ham⟩ := ha
    have hoddH : Odd (orderOf (a : H)) :=
      hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ham)
    have hodd : Odd (orderOf ((f112Gold L1 L2 S).ofB a)) := by
      rw [orderOf_injective (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective a,
        ← Subgroup.orderOf_coe]
      exact hoddH
    exact Subgroup.subset_closure ⟨Or.inr ⟨a, rfl⟩, hodd⟩
  · rintro x ⟨hxL, -⟩
    exact Subgroup.mem_sup_left hxL

theorem f112sa_X2_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((f112saX2 L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112EOdd L1 L2 S := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  have haX2 : (a : H) ∈ f112saX2 L1 L2 S := Subgroup.mem_subgroupOf.mp ha
  have haO : (a : H) ∈ oTwoRes L2 := haX2.1
  have haB : (a : H) ∈ bigB L1 L2 S := haX2.2
  have haP2 : (a : H) ∈ L2 ⊔ bigB L1 L2 S :=
    (le_sup_left (a := L2) (b := bigB L1 L2 S)) ((oTwoRes_le L2) haO)
  have heq : (f112Gold L1 L2 S).ofA a =
      (f112Gold L1 L2 S).ofB ⟨(a : H), haP2⟩ := by
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩]
  rw [heq]
  refine f112sa_oTwoRes_right_map_le_EOdd (L1 := L1) (L2 := L2) (S := S) ?_
  exact Subgroup.mem_map_of_mem (f112Gold L1 L2 S).ofB
    (Subgroup.mem_subgroupOf.mpr haO)

theorem f112sa_P1'_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112EOdd L1 L2 S := by
  rw [f112saP1', Subgroup.subgroupOf_sup
    ((oTwoRes_le L1).trans le_sup_left)
    ((f112sa_X2_le_bigB L1 L2 S).trans le_sup_right), Subgroup.map_sup]
  exact sup_le f112sa_oTwoRes_left_map_le_EOdd f112sa_X2_map_le_EOdd

theorem f112sa_X1_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((f112saX1 L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112EOdd L1 L2 S := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  have haX1 : (a : H) ∈ f112saX1 L1 L2 S := Subgroup.mem_subgroupOf.mp ha
  have haO : (a : H) ∈ oTwoRes L1 := haX1.1
  have haP1 : (a : H) ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_left (a := L1) (b := bigB L1 L2 S)) ((oTwoRes_le L1) haO)
  have heq : (f112Gold L1 L2 S).ofB a =
      (f112Gold L1 L2 S).ofA ⟨(a : H), haP1⟩ := by
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨haP1, a.2⟩]
  rw [heq]
  refine f112sa_oTwoRes_left_map_le_EOdd (L1 := L1) (L2 := L2) (S := S) ?_
  exact Subgroup.mem_map_of_mem (f112Gold L1 L2 S).ofA
    (Subgroup.mem_subgroupOf.mpr haO)

theorem f112sa_P2'_map_le_EOdd
    {L1 L2 S : Subgroup H} :
    ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112EOdd L1 L2 S := by
  rw [f112saP2', Subgroup.subgroupOf_sup
    ((oTwoRes_le L2).trans le_sup_left)
    ((f112sa_X1_le_bigB L1 L2 S).trans le_sup_right), Subgroup.map_sup]
  exact sup_le f112sa_oTwoRes_right_map_le_EOdd f112sa_X1_map_le_EOdd

theorem f112sa_EOdd_inf_ofA_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range =
      ((oTwoRes L1 ⊔ (oTwoRes L2 ⊓ bigB L1 L2 S)).subgroupOf (f112P1 L1 L2 S)).map
        (f112Gold L1 L2 S).ofA := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := 2) (by norm_num) (by norm_num) hF.1
      (isL2Quot_of_VS3 h1) h2
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF.toW hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF.toW
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF.toW
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huA⟩
    obtain ⟨p, hp⟩ := huA
    have hchi : f112saChiR hF.toW hR u = 1 := MonoidHom.mem_ker.mp
      (f112saEOdd_le_ker_chi_of_hyp111R hF hR h1 huE)
    have hchi1 : f112saChi1R hF.toW hR p = 1 := by
      rw [← f112saChiR_ofA hF.toW hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP1' L1 L2 S :=
      (f112saChi1R_eq_one_iff hF.toW hR p).mp hchi1
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P1'_map_le_EOdd (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112sa_EOdd_inf_ofB_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range =
      ((oTwoRes L2 ⊔ (oTwoRes L1 ⊓ bigB L1 L2 S)).subgroupOf (f112P2 L1 L2 S)).map
        (f112Gold L1 L2 S).ofB := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := 2) (by norm_num) (by norm_num) hF.1
      (isL2Quot_of_VS3 h1) h2
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF.toW hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF.toW
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF.toW
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huB⟩
    obtain ⟨p, hp⟩ := huB
    have hchi : f112saChiR hF.toW hR u = 1 := MonoidHom.mem_ker.mp
      (f112saEOdd_le_ker_chi_of_hyp111R hF hR h1 huE)
    have hchi2 : f112saChi2R hF.toW hR p = 1 := by
      rw [← f112saChiR_ofB hF.toW hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP2' L1 L2 S :=
      (f112saChi2R_eq_one_iff hF.toW hR p).mp hchi2
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P2'_map_le_EOdd (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112sa_EOdd_inf_ofA_range_inf_ofB_range
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      ((oTwoRes L1 ⊓ bigB L1 L2 S ⊔ (oTwoRes L2 ⊓ bigB L1 L2 S)).subgroupOf
        (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := 2) (by norm_num) (by norm_num) hF.1
      (isL2Quot_of_VS3 h1) h2
  let X := f112Gold L1 L2 S
  have hKP1' : f112saK L1 L2 S ≤ f112saP1' L1 L2 S :=
    sup_le ((show f112saX1 L1 L2 S ≤ oTwoRes L1 from inf_le_left).trans le_sup_left)
      (show f112saX2 L1 L2 S ≤ f112saP1' L1 L2 S from le_sup_right)
  rw [f112sa_EOdd_inf_ofA_range hF h1 h2]
  refine le_antisymm ?_ ?_
  · rintro u ⟨huM, huB⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp huM
    have haP1' : (a : H) ∈ f112saP1' L1 L2 S := Subgroup.mem_subgroupOf.mp ha
    have huBase : X.ofA a ∈ (Monoid.PushoutI.base X.diagram).range := by
      rw [← X.ofA_range_inf_ofB_range]
      exact ⟨⟨a, rfl⟩, huB⟩
    obtain ⟨c, hc⟩ := huBase
    have htoA : X.toA c = a := X.ofA_injective (by rw [X.ofA_toA, hc])
    have haB : (a : H) ∈ bigB L1 L2 S := by
      rw [← htoA]
      exact (f112_inf_eq_bigB_of_hyp111R hR) ▸ c.2
    have haK : (a : H) ∈ f112saK L1 L2 S := by
      have h : (a : H) ∈ f112saP1' L1 L2 S ⊓ bigB L1 L2 S := ⟨haP1', haB⟩
      rwa [f112sa_P1'_inf_bigB hF.toW] at h
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr haK, rfl⟩
  · refine le_inf ?_ ?_
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) hKP1')
    · rintro u ⟨a, ha, rfl⟩
      have haB : (a : H) ∈ bigB L1 L2 S :=
        f112sa_K_le_bigB L1 L2 S (Subgroup.mem_subgroupOf.mp ha)
      have haP2 : (a : H) ∈ f112P2 L1 L2 S :=
        ((f112_inf_eq_bigB_of_hyp111R hR) ▸ haB).2
      have heq : X.ofA a = X.ofB ⟨(a : H), haP2⟩ :=
        f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩
      rw [heq]
      exact ⟨⟨(a : H), haP2⟩, rfl⟩

end CFSG.Quasithin.F112R.St84
