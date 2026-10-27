module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

variable {X : Type} [Group X]

@[expose, reducible] def tcT1 (Lb Tb : Subgroup X) : Subgroup X := Tb ⊓ normalizer (Lb : Set X)

@[expose, reducible] def tcN1 (Lb Tb : Subgroup X) : Subgroup X := Lb ⊔ tcT1 Lb Tb

@[expose] def tcBase (Lb Tb : Subgroup X) : Subgroup X :=
  ⨆ (t : X) (_ : t ∈ Tb), conjSubgroup Lb t

variable [Finite X] {B : Type} [Group B] [Finite B]

structure TCBar (Lb Tb : Subgroup X) (π : ↥(tcN1 Lb Tb) →* B) (Es : Subgroup B) : Prop where
  sylow : IsSylowIn 2 Tb ⊤
  o2 : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥
  quasi : CFSG.IsQuasisimple ↥Lb
  center3 : IsPGroup 3 (center ↥Lb)
  comm : ∀ t ∈ Tb, ∀ t' ∈ Tb, conjSubgroup Lb t ≠ conjSubgroup Lb t' →
    ∀ x ∈ conjSubgroup Lb t, ∀ y ∈ conjSubgroup Lb t', x * y = y * x
  gen : tcBase Lb Tb ⊔ Tb = ⊤
  surj : Function.Surjective π
  ker : ∀ x, π x = 1 ↔ (x : X) ∈ pCoreOf 2 (tcN1 Lb Tb)
  facts : CoordFacts914 (barSub π Lb) (barSub π Tb) Es

@[expose] def TCAbstract : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V T N : Subgroup G), Hyp9 V T → T ≤ N →
    N ≤ normalizer (V : Set G) → Star914 V N →
    ∀ (X : Type) [Group X] [Finite X] (ψ : ↥N →* X), Function.Surjective ψ →
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) →
      ∀ (Lb : Subgroup X) (B : Type) [Group B] [Finite B] (π : ↥(tcN1 Lb (barSub ψ T)) →* B)
        (Es : Subgroup B), TCBar Lb (barSub ψ T) π Es →
      normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
        N ≤ normalizer (E3.wClos V 0 T : Set G)

omit [Finite X] in
theorem le_normalizer_iSup {ι : Sort*} {K : Subgroup X} {H : ι → Subgroup X}
    (h : ∀ i, K ≤ normalizer (H i : Set X)) : K ≤ normalizer ((⨆ i, H i : Subgroup X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => mem_normalizer_iff_map_conj_eq.mp (h i hg)

omit [Finite X] in
theorem mem_normalizer_conjSubgroup {A : Subgroup X} {g t : X}
    (h : t * g * t⁻¹ ∈ normalizer (A : Set X)) : g ∈ normalizer (conjSubgroup A t : Set X) := by
  rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
  exact h

theorem isSylowIn_inf_normalizer {Tb Bs P : Subgroup X} (hT : IsSylowIn 2 Tb ⊤) [Bs.Normal]
    (hgen : Bs ⊔ Tb = ⊤) (hBP : Bs ≤ normalizer (P : Set X)) :
    IsSylowIn 2 (Tb ⊓ normalizer (P : Set X)) (normalizer (P : Set X)) := by
  set NP := normalizer (P : Set X)
  set S := Tb ⊓ NP
  refine ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, ?_⟩
  have hNP : S ⊔ Bs = NP := by
    refine le_antisymm (sup_le inf_le_right hBP) fun x hx => ?_
    have hx' : x ∈ Bs ⊔ Tb := hgen ▸ mem_top x
    obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hx'
    have htN : t ∈ NP := by
      have := NP.mul_mem (inv_mem (hBP hb)) hx
      simpa using this
    exact mul_mem (mem_sup_right hb) (mem_sup_left ⟨ht, htN⟩)
  have hBS : Bs ⊓ S = Bs ⊓ Tb := by
    ext x
    simp only [mem_inf, S]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hBP h.1⟩⟩
  have i1 := relIndex_mul_card (H := Bs) (K := Tb)
  have i2 := relIndex_mul_card (H := Bs) (K := S)
  have i3 := relIndex_mul_card (H := Tb) (K := NP)
  have i4 := relIndex_mul_card (H := Bs) (K := NP)
  have i5 := index_mul_card Bs
  have i6 := index_mul_card Tb
  have ha : relIndex Bs (Tb ⊔ Bs) = relIndex Bs Tb := relIndex_sup_right Tb Bs
  have hb : relIndex Bs (S ⊔ Bs) = relIndex Bs S := relIndex_sup_right S Bs
  rw [sup_comm, hgen, relIndex_top_right] at ha
  rw [hNP] at hb
  rw [hBS] at i2
  rw [inf_eq_left.mpr hBP, hb] at i4
  have hTS : Tb ⊓ NP = S := rfl
  rw [hTS] at i3
  rw [ha] at i5
  have hpa : 0 < Nat.card ↥(Bs ⊓ Tb) := Nat.card_pos
  have hpb : 0 < Nat.card ↥Bs := Nat.card_pos
  have hr : Tb.relIndex NP * Nat.card ↥(Bs ⊓ Tb) = Nat.card ↥Bs := by
    have h1 : Bs.relIndex S ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at i2
      exact (Nat.card_pos (α := ↥S)).ne' i2.symm
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
    calc Bs.relIndex S * (Tb.relIndex NP * Nat.card ↥(Bs ⊓ Tb))
        = Tb.relIndex NP * (Bs.relIndex S * Nat.card ↥(Bs ⊓ Tb)) := by ring
      _ = Bs.relIndex S * Nat.card ↥Bs := by rw [i2, i3, i4]
  have hq : Tb.index * Nat.card ↥(Bs ⊓ Tb) = Nat.card ↥Bs := by
    have h1 : Bs.relIndex Tb ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at i1
      exact (Nat.card_pos (α := ↥Tb)).ne' i1.symm
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
    calc Bs.relIndex Tb * (Tb.index * Nat.card ↥(Bs ⊓ Tb))
        = Tb.index * (Bs.relIndex Tb * Nat.card ↥(Bs ⊓ Tb)) := by ring
      _ = Bs.relIndex Tb * Nat.card ↥Bs := by rw [i1, i6, ← i5]
  have heq : Tb.relIndex NP = Tb.index :=
    Nat.eq_of_mul_eq_mul_right hpa (hr.trans hq.symm)
  have hT2 := hT.not_dvd_relIndex
  rw [relIndex_top_right] at hT2
  rw [show S = Tb ⊓ NP from rfl, inf_relIndex_right, heq]
  exact hT2

omit [Finite X] in
theorem conj_mem_iSup_conj {A Tb : Subgroup X} {s : X} (hs : s ∈ Tb) {x : X}
    (hx : x ∈ ⨆ (t : X) (_ : t ∈ Tb), conjSubgroup A t) :
    s * x * s⁻¹ ∈ ⨆ (t : X) (_ : t ∈ Tb), conjSubgroup A t := by
  have hle : (⨆ (t : X) (_ : t ∈ Tb), conjSubgroup A t).map (MulAut.conj s).toMonoidHom ≤
      ⨆ (t : X) (_ : t ∈ Tb), conjSubgroup A t := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht => ?_
    have he : (conjSubgroup A t).map (MulAut.conj s).toMonoidHom = conjSubgroup A (t * s⁻¹) := by
      rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup]
      unfold CFSG.Quasithin.conjSubgroup
      rw [inv_inv]
    rw [he]
    exact le_iSup₂_of_le (t * s⁻¹) (mul_mem ht (inv_mem hs)) le_rfl
  exact hle ⟨x, hx, rfl⟩

omit [Finite X] in
theorem le_normalizer_iSup_conj (A Tb : Subgroup X) :
    Tb ≤ normalizer ((⨆ (t : X) (_ : t ∈ Tb), conjSubgroup A t : Subgroup X) : Set X) :=
  NFW.le_normalizer_of_conj_mem fun _ hs _ hx => conj_mem_iSup_conj hs hx

omit [Finite X] in
theorem conj_le_tcBase {Lb Tb : Subgroup X} {t : X} (ht : t ∈ Tb) :
    conjSubgroup Lb t ≤ tcBase Lb Tb :=
  le_iSup₂_of_le t ht le_rfl

omit [Finite X] in
theorem le_tcBase (Lb Tb : Subgroup X) : Lb ≤ tcBase Lb Tb := by
  have h : conjSubgroup Lb 1 ≤ tcBase Lb Tb := conj_le_tcBase Tb.one_mem
  rwa [CFSG.Quasithin.conjSubgroup_one] at h

omit [Finite X] in
theorem inf_tcN1 (Lb Tb : Subgroup X) : Tb ⊓ tcN1 Lb Tb = tcT1 Lb Tb :=
  le_antisymm (fun _ hx => ⟨hx.1, (sup_le le_normalizer inf_le_right) hx.2⟩)
    (le_inf inf_le_left le_sup_right)

omit [Finite X] [Finite B] in
theorem barSub_tcT1 {Lb Tb : Subgroup X} (π : ↥(tcN1 Lb Tb) →* B) :
    barSub π Tb = barSub π (tcT1 Lb Tb) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have : (x : X) ∈ Tb ⊓ tcN1 Lb Tb := ⟨hx, x.2⟩
    rwa [inf_tcN1] at this
  · exact barSub_mono inf_le_left

namespace TCBar

variable {Lb Tb : Subgroup X} {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}
variable (c : TCBar Lb Tb π Es)
include c

omit [Finite X] [Finite B] in
theorem base_normal : (tcBase Lb Tb).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← c.gen]
  exact sup_le le_normalizer (le_normalizer_iSup_conj Lb Tb)

omit [Finite X] [Finite B] in
theorem conj_le_normalizer_conj {t t' : X} (ht : t ∈ Tb) (ht' : t' ∈ Tb) :
    conjSubgroup Lb t ≤ normalizer (conjSubgroup Lb t' : Set X) := by
  by_cases h : conjSubgroup Lb t = conjSubgroup Lb t'
  · rw [h]
    exact le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (conjSubgroup Lb t' : Set X))
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (c.comm t ht t' ht' h x hx y hy).symm

omit [Finite X] [Finite B] in
theorem base_le_normalizer_conj {t : X} (ht : t ∈ Tb) :
    tcBase Lb Tb ≤ normalizer (conjSubgroup Lb t : Set X) :=
  iSup₂_le fun _ ht' => c.conj_le_normalizer_conj ht' ht

omit [Finite X] [Finite B] in
theorem base_le_normalizer_Lb : tcBase Lb Tb ≤ normalizer (Lb : Set X) := by
  have := c.base_le_normalizer_conj Tb.one_mem
  rwa [CFSG.Quasithin.conjSubgroup_one] at this

omit [Finite B] in
theorem isSylowIn_inf_normalizer' {P : Subgroup X} (hBP : tcBase Lb Tb ≤ normalizer (P : Set X)) :
    IsSylowIn 2 (Tb ⊓ normalizer (P : Set X)) (normalizer (P : Set X)) := by
  have := c.base_normal
  exact isSylowIn_inf_normalizer c.sylow c.gen hBP

omit [Finite B] in
theorem isSylowIn_T1 : IsSylowIn 2 (tcT1 Lb Tb) (tcN1 Lb Tb) := by
  have h := c.isSylowIn_inf_normalizer' c.base_le_normalizer_Lb
  refine ⟨le_sup_right, h.isPGroup, fun hd => h.not_dvd_relIndex ?_⟩
  have hle : tcN1 Lb Tb ≤ normalizer (Lb : Set X) := sup_le le_normalizer inf_le_right
  rw [← relIndex_mul_relIndex _ _ _ (le_sup_right : tcT1 Lb Tb ≤ tcN1 Lb Tb) hle]
  exact dvd_mul_of_dvd_left hd _

omit [Finite X] [Finite B] in
theorem eq_one_of_centralizes {x : X} (hxT : x ∈ Tb)
    (hx : ∀ t ∈ Tb, x ∈ centralizer (conjSubgroup Lb t : Set X)) : x = 1 := by
  set C := Tb ⊓ centralizer (tcBase Lb Tb : Set X) with hC
  have hCn : C.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← c.gen]
    refine sup_le ((le_centralizer_iff.mp inf_le_right).trans (centralizer_le_normalizer C)) ?_
    intro t ht
    exact mem_normalizer_inf (le_normalizer ht)
      (mem_normalizer_centralizer (le_normalizer_iSup_conj Lb Tb ht))
  have hC2 : IsPGroup 2 C := c.sylow.isPGroup.to_le inf_le_left
  have hxC : x ∈ C := by
    refine mem_inf.mpr ⟨hxT, ?_⟩
    have hle : tcBase Lb Tb ≤ centralizer ({x} : Set X) :=
      iSup₂_le fun t ht => (le_centralizer_iff.mp
        (zpowers_le.mpr (hx t ht))).trans (centralizer_le (by simp))
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle hy)
  rw [c.o2 C hCn hC2] at hxC
  exact hxC

omit [Finite B] in
theorem pCore_le_T1 : pCoreOf 2 (tcN1 Lb Tb) ≤ tcT1 Lb Tb :=
  CFSG.Quasithin.AppendixH.H14.pCoreOf_le_of_sylow c.isSylowIn_T1.le c.isSylowIn_T1.isPGroup
    c.isSylowIn_T1.not_dvd_relIndex

omit [Finite B] in
theorem eq_bot_of_le_Lb {P : Subgroup X} (hPL : P ≤ Lb) (hPn : Lb ≤ normalizer (P : Set X))
    (hP : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914.le_map_center_of_isPGroup c.quasi
    hPL (fun l hl h hh => (mem_normalizer_iff.mp (hPn hl) h).mp hh) hP
  have h3 : IsPGroup 3 ((center ↥Lb).map Lb.subtype) := c.center3.map _
  exact disjoint_self.mp ((IsPGroup.disjoint_of_ne 2 3 (by norm_num) P _ hP h3).mono_right hZ)

omit [Finite B] in
theorem pCore_inf_Lb : pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine c.eq_bot_of_le_Lb inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact fun l hl => mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hl)) (le_normalizer hl)

omit [Finite B] in
theorem pCore_le_centralizer : pCoreOf 2 (tcN1 Lb Tb) ≤ centralizer (Lb : Set X) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro l hl
  have hqN : q ∈ tcN1 Lb Tb := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have hqL : q ∈ normalizer (Lb : Set X) := (sup_le le_normalizer inf_le_right) hqN
  have hcomm : l * q * l⁻¹ * q⁻¹ ∈ pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem ((mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hl)) q).mp hq)
        (inv_mem hq)
    · have h1 : q * l⁻¹ * q⁻¹ ∈ Lb := (mem_normalizer_iff.mp hqL l⁻¹).mp (inv_mem hl)
      have := mul_mem hl h1
      simpa [mul_assoc] using this
  rw [c.pCore_inf_Lb, mem_bot] at hcomm
  calc l * q = (l * q * l⁻¹ * q⁻¹) * (q * l) := by group
    _ = q * l := by rw [hcomm, one_mul]

omit [Finite B] in
theorem mem_of_ker {x : ↥(tcN1 Lb Tb)} (hx : π x = 1) :
    (x : X) ∈ tcT1 Lb Tb ∧ (x : X) ∈ centralizer (Lb : Set X) :=
  ⟨c.pCore_le_T1 ((c.ker x).mp hx), c.pCore_le_centralizer ((c.ker x).mp hx)⟩

omit [Finite B] in
theorem eq_of_map_eq {x y : ↥(tcN1 Lb Tb)} (hx : (x : X) ∈ Lb) (hy : (y : X) ∈ Lb)
    (h : π x = π y) : x = y := by
  have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((x⁻¹ * y : ↥(tcN1 Lb Tb)) : X) ∈ pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb :=
    ⟨(c.ker _).mp h1, by simpa using mul_mem (inv_mem hx) hy⟩
  rw [c.pCore_inf_Lb, mem_bot] at h2
  have h3 : x⁻¹ * y = 1 := Subtype.ext h2
  exact (inv_mul_eq_one.mp h3)

omit [Finite B] in
theorem liftSub_barSub_T : liftSub π (barSub π Tb) = tcT1 Lb Tb := by
  rw [barSub_tcT1]
  exact liftSub_barSub c.ker c.pCore_le_T1 le_sup_right

end TCBar

end CFSG.LocalAnalysis.WeakClosure81
