module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828SLem13

variable {G : Type} [Group G] [Finite G]

theorem s828_derived_le_of_quot {Y N : Subgroup G} (hN : N ≤ Y) [(N.subgroupOf Y).Normal]
    [hsolv : Group.IsSolvable (↥Y ⧸ N.subgroupOf Y)] :
    ∃ m : ℕ, derivedSeries ↥Y m ≤ N.subgroupOf Y := by
  obtain ⟨m, hm⟩ := hsolv.solvable
  refine ⟨m, fun x hx => ?_⟩
  have hmap : (derivedSeries ↥Y m).map (QuotientGroup.mk' (N.subgroupOf Y)) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _) m, hm]
  have hmem : QuotientGroup.mk' (N.subgroupOf Y) x ∈
      (⊥ : Subgroup (↥Y ⧸ N.subgroupOf Y)) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

theorem s828_perfect_le_of_solvable_quot {Y N W : Subgroup G} (hN : N ≤ Y)
    [(N.subgroupOf Y).Normal] [hsolv : Group.IsSolvable (↥Y ⧸ N.subgroupOf Y)] (hWY : W ≤ Y)
    (hperf : ⁅W, W⁆ = W) :
    W ≤ N := by
  obtain ⟨m, hm⟩ := s828_derived_le_of_quot hN
  have hW'perf : ⁅W.subgroupOf Y, W.subgroupOf Y⁆ = W.subgroupOf Y := by
    apply Subgroup.map_injective (f := Y.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWY, hperf]
  have hW'D : ∀ n : ℕ, W.subgroupOf Y ≤ derivedSeries ↥Y n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      calc W.subgroupOf Y = ⁅W.subgroupOf Y, W.subgroupOf Y⁆ := hW'perf.symm
        _ ≤ ⁅derivedSeries ↥Y n, derivedSeries ↥Y n⁆ := Subgroup.commutator_mono ih ih
        _ = derivedSeries ↥Y (n + 1) := (derivedSeries_succ _ _).symm
  intro w hw
  have hw' : (⟨w, hWY hw⟩ : ↥Y) ∈ W.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hw
  exact Subgroup.mem_subgroupOf.mp (hm (hW'D m hw'))

theorem s828_mem_mul_of_sup {Y L S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G))
    (hY : Y = L ⊔ S) {y : G} (hy : y ∈ Y) : ∃ l ∈ L, ∃ s ∈ S, y = l * s := by
  let M : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ s ∈ S, x = l * s}
      one_mem' := ⟨1, L.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l, hl, s, hs, rfl⟩ ⟨l', hl', s', hs', rfl⟩
        have hn : s * l' * s⁻¹ ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (hS hs) l').mp hl'
          exact this
        refine ⟨l * (s * l' * s⁻¹), L.mul_mem hl hn, s * s', S.mul_mem hs hs', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, s, hs, rfl⟩
        have hn : s⁻¹ * l⁻¹ * s ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (hS (S.inv_mem hs)) l⁻¹).mp (L.inv_mem hl)
          simpa using this
        refine ⟨s⁻¹ * l⁻¹ * s, hn, s⁻¹, S.inv_mem hs, ?_⟩
        group }
  have hLM : L ≤ M := fun l hl => ⟨l, hl, 1, S.one_mem, by simp⟩
  have hSM : S ≤ M := fun s hs => ⟨1, L.one_mem, s, hs, by simp⟩
  have hYM : Y ≤ M := by rw [hY]; exact sup_le hLM hSM
  exact hYM hy

theorem s828_normal_sup {Y L S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G))
    (hY : Y = L ⊔ S) : (L.subgroupOf Y).Normal := by
  have hLY : L ≤ Y := hY ▸ le_sup_left
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr ?_
  rw [hY]
  exact sup_le Subgroup.le_normalizer hS

theorem s828_quot_solvable_of_sup {Y L S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G))
    (hY : Y = L ⊔ S) (hSY : S ≤ Y) (hSp : IsPGroup 2 ↥S) [(L.subgroupOf Y).Normal] :
    Group.IsSolvable (↥Y ⧸ L.subgroupOf Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥S := by
    haveI : Group.IsNilpotent ↥S := hSp.isNilpotent
    infer_instance
  let f : ↥S →* ↥Y ⧸ L.subgroupOf Y :=
    (QuotientGroup.mk' (L.subgroupOf Y)).comp (Subgroup.inclusion hSY)
  refine Group.isSolvable_of_surjective (f := f) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l, hl, s, hs, hys⟩ := s828_mem_mul_of_sup hS hY y.2
  refine ⟨⟨s, hs⟩, ?_⟩
  simp only [f, MonoidHom.comp_apply]
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf]
  have hn : s⁻¹ * l * s ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hS (S.inv_mem hs)) l).mp hl
    simpa using this
  simp only [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inclusion]
  rw [show ((y : G)) = l * s from hys]
  convert hn using 1
  group

theorem s828_lemma13 {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (hC5 : Concl825 T L I h k)
    (hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (hLUT : T ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G))
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hhI : h ∈ ch82I (fsuV T I) h)
    (hLUC : ¬ ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G))
    {K : Subgroup G}
    (hK : quasithinIsCComponent K (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)))
    (hKle : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hKn : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLUK : ch82LU L (ch82U (fsuV T I) h) ≤ K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ch82I (fsuV T I) h ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) ∧
      ⁅ch82LU L (ch82U (fsuV T I) h), ch82I (fsuV T I) h⁆ ≤
        pCoreOf 2 (ch82LU L (ch82U (fsuV T I) h)) ∧
      ⁅ch82I (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ pCoreOf 2 (ch82I (fsuV T I) h) ∧
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hIU⟩ := hC5
  set V := fsuV T I with hV
  set Ih := ch82I V h with hIh
  set U := ch82U V h with hU
  set LU := ch82LU L U with hLU
  have hLUN : LU ≤ Subgroup.normalizer (U : Set G) := (perfectCore_le _).trans inf_le_right
  have hperfLU : ⁅LU, LU⁆ = LU := perfectCore_perfect _
  have hXV : LU ≤ Subgroup.normalizer (V : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hO2T : pCoreOf 2 K ≤ T := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKle)
        (hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact h1.trans (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)
  have hS' : pCoreOf 2 K ≤ Subgroup.normalizer (LU : Set G) := hO2T.trans hLUT
  have hYdef : LU ⊔ pCoreOf 2 K = LU ⊔ pCoreOf 2 K := rfl
  haveI hnorm : (LU.subgroupOf (LU ⊔ pCoreOf 2 K)).Normal := s828_normal_sup hS' rfl
  haveI hsolv : Group.IsSolvable (↥(LU ⊔ pCoreOf 2 K) ⧸ LU.subgroupOf (LU ⊔ pCoreOf 2 K)) :=
    s828_quot_solvable_of_sup hS' rfl le_sup_right (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hXC : ¬ K ≤ Subgroup.centralizer (U : Set G) := fun hKC => hLUC (hLUK.trans hKC)
  have hcc := commutator_centralizer_le_828 hKle hKn hK.2.1 hq hXC
  have hcomm : ∀ l ∈ LU, ∀ i ∈ Ih, ⁅l, i⁆ ∈ pCoreOf 2 K := by
    intro l hl i hi
    apply hcc
    exact Subgroup.commutator_mem_commutator (hLUK hl) (hIU hi)
  have hconjY : ∀ i ∈ Ih, ∀ l ∈ LU, i * l * i⁻¹ ∈ LU ⊔ pCoreOf 2 K := by
    intro i hi l hl
    have h1 : (⁅l, i⁆)⁻¹ ∈ pCoreOf 2 K := (pCoreOf 2 K).inv_mem (hcomm l hl i hi)
    have e : i * l * i⁻¹ = (⁅l, i⁆)⁻¹ * l := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LU ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hl)
  have hLUI : ∀ i ∈ Ih, ∀ l ∈ LU, i * l * i⁻¹ ∈ LU := by
    intro i hi
    let c : G →* G := (MulAut.conj i).toMonoidHom
    have hWperf : ⁅LU.map c, LU.map c⁆ = LU.map c := by
      rw [← Subgroup.map_commutator, hperfLU]
    have hWY : LU.map c ≤ LU ⊔ pCoreOf 2 K := by
      rintro _ ⟨l, hl, rfl⟩
      exact hconjY i hi l hl
    have hWLU := s828_perfect_le_of_solvable_quot (Y := LU ⊔ pCoreOf 2 K) (N := LU)
      (W := LU.map c) le_sup_left hWY hWperf
    intro l hl
    exact hWLU (Subgroup.mem_map_of_mem c hl)
  have hconj : ∀ x ∈ LU, h⁻¹ * x * h ∈ LU := fun x hx => by
    have := hLUI h⁻¹ (Ih.inv_mem hhI) x hx
    simpa using this
  have hXVh : LU ≤ Subgroup.normalizer (B6.conjSub h V : Set G) := by
    intro x hx
    have hx1 := hconj x hx
    have hx2 := hconj x⁻¹ (LU.inv_mem hx)
    refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [B6.mem_conjSub] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXV hx1) _).mp hy
      have e : h⁻¹ * (x * y * x⁻¹) * h =
          h⁻¹ * x * h * (h⁻¹ * y * h) * (h⁻¹ * x * h)⁻¹ := by group
      rw [e]
      exact h1
    · rw [B6.mem_conjSub] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXV hx2) _).mp hy
      have e : h⁻¹ * (x⁻¹ * y * x) * h =
          h⁻¹ * x⁻¹ * h * (h⁻¹ * y * h) * (h⁻¹ * x⁻¹ * h)⁻¹ := by group
      rw [e]
      exact h1
  have hLUNI : LU ≤ Subgroup.normalizer (Ih : Set G) := by
    intro x hx
    have h1 := hXV hx
    have h2 := hXVh hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    show (V ⊔ B6.conjSub h V).map _ = V ⊔ B6.conjSub h V
    rw [Subgroup.map_sup, h1, h2]
  have hIN : Ih ≤ Subgroup.normalizer (LU : Set G) := by
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hLUI i hi x hx
    · intro hx
      convert hLUI i⁻¹ (Ih.inv_mem hi) _ hx using 1
      group
  have hS0_norm : ∀ l ∈ LU, ∀ x ∈ LU ⊓ pCoreOf 2 K, l * x * l⁻¹ ∈ LU ⊓ pCoreOf 2 K := by
    intro l hl x hx
    refine ⟨LU.mul_mem (LU.mul_mem hl hx.1) (LU.inv_mem hl), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLUK hl)) x).mp hx.2
  have hcore : ⁅LU, Ih⁆ ≤ pCoreOf 2 LU := by
    have hS0le : LU ⊓ pCoreOf 2 K ≤ pCoreOf 2 LU := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
      · intro l hl
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hS0_norm l hl x
        · intro hx
          have := hS0_norm l⁻¹ (LU.inv_mem hl) _ hx
          convert this using 1
          group
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right
    rw [Subgroup.commutator_le]
    intro l hl i hi
    apply hS0le
    refine ⟨?_, hcomm l hl i hi⟩
    have e : ⁅l, i⁆ = l * (i * l⁻¹ * i⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact LU.mul_mem hl (hLUI i hi l⁻¹ (LU.inv_mem hl))
  have hIL_le_I : ⁅Ih, LU⁆ ≤ Ih := by
    rw [Subgroup.commutator_le]
    intro i hi l hl
    have h1 := (Subgroup.mem_normalizer_iff.mp (hLUNI hl) i⁻¹).mp (Ih.inv_mem hi)
    have e : ⁅i, l⁆ = i * (l * i⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Ih.mul_mem hi (by simpa using h1)
  have hIL_le_P : ⁅Ih, LU⁆ ≤ pCoreOf 2 Ih := by
    have hmap : ∀ j ∈ Ih, (⁅Ih, LU⁆).map (MulAut.conj j).toMonoidHom ≤ ⁅Ih, LU⁆ := by
      intro j hj
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact Ih.mul_mem (Ih.mul_mem hj hx) (Ih.inv_mem hj)
      · rintro _ ⟨x, hx, rfl⟩
        exact hLUI j hj x hx
    have hnorm : Ih ≤ Subgroup.normalizer ((⁅Ih, LU⁆ : Subgroup G) : Set G) := by
      intro j hj
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hmap j hj ⟨y, hy, rfl⟩
      · intro hy
        have h3 := hmap j⁻¹ (Ih.inv_mem hj) ⟨j * y * j⁻¹, hy, rfl⟩
        have e : (MulAut.conj j⁻¹).toMonoidHom (j * y * j⁻¹) = y := by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e] at h3
        exact h3
    have h2 : IsPGroup 2 ↥(⁅Ih, LU⁆) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU).to_le
        (by rw [Subgroup.commutator_comm]; exact hcore)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hIL_le_I hnorm h2
  have hVB : ⁅V, LU⁆ ≤ ch82B V h := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    refine ⟨?_, hIL_le_P (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hv) hl)⟩
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hv (by simpa using (Subgroup.mem_normalizer_iff.mp (hXV hl) v⁻¹).mp (V.inv_mem hv))
  exact ⟨hIN, hcore, hIL_le_P, hVB⟩

end L828SLem13

end CFSG.Quasithin.H13
