module

public import CFSG.Quasithin.Vol2.Ch7Sec77Tp
public import CFSG.Quasithin.Vol2.Ch7Lem776b

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conj_mem_oTwoUpper {H : Subgroup G} {h y : G} (hh : h ∈ H) (hy : y ∈ oTwoUpper H) :
    h * y * h⁻¹ ∈ oTwoUpper H := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), ?_⟩
    have h1 := (MulAut.conj h).orderOf_eq x
    rw [MulAut.conj_apply] at h1
    rw [h1]
    exact hx.2
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

namespace Setup

variable (S : Setup T L I)
include S

variable {S}

structure Conf (θ : G) (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)) (Vp H : Subgroup G) :
    Prop where
  hc : S.Coord θ e
  case : Vp = fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) ∨
    (Vp = Subgroup.zpowers (S.vec e a1) ∧ (2 : ℕ∞) < rParam (fsuV T I))
  sylG : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G)) (Subgroup.centralizer (Vp : Set G))
  sylM : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G))
    (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G))
  hLH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
    (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H
  hHG : H ≤ Subgroup.centralizer (Vp : Set G)

namespace Conf

variable {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G} {Vp H : Subgroup G}
  (C : S.Conf θ e Vp H)
include C

theorem vp_le : Vp ≤ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) := by
  rcases C.case with h | ⟨h, -⟩
  · exact h.le
  · rw [h, Subgroup.zpowers_le]
    exact vec_a1_mem_V0 C.hc

theorem vp_le_V : Vp ≤ fsuV T I := C.vp_le.trans inf_le_left

theorem z_mem : S.vec e a1 ∈ Vp := by
  rcases C.case with h | ⟨h, -⟩
  · rw [h]
    exact vec_a1_mem_V0 C.hc
  · rw [h]
    exact Subgroup.mem_zpowers _

theorem tp_le_H : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ H := le_sup_right.trans C.hLH

theorem sylH : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G)) H := by
  refine ⟨C.tp_le_H, C.sylG.2.1, fun h2 => C.sylG.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ Subgroup.centralizer (Vp : Set G)) H
    (Subgroup.centralizer (Vp : Set G)) C.tp_le_H C.hHG
  exact h2.trans (Dvd.intro _ h1)

theorem V_le_tp : fsuV T I ≤ T ⊓ Subgroup.centralizer (Vp : Set G) :=
  le_inf S.fsuV_le_T (S.fsuV_le_centralizer C.vp_le_V)

theorem vm_le_H : S.vm e ≤ H := ((vm_le (S := S)).trans C.V_le_tp).trans C.tp_le_H

theorem th_mem_H : θ ∈ H := le_sup_left.trans C.hLH (S.th_mem_oTwoUpper C.hc C.vp_le)

theorem hA : Subgroup.centralizer (Vp : Set G) ⊓ Subgroup.centralizer (S.vm e : Set G) ≤
    fsuM T L := by
  rcases C.case with h | ⟨h, hr⟩
  · rw [h]
    exact centralizer_inf_vm_le_H0 C.hc
  · exact centralizer_inf_vm_le_H1 hr C.vp_le_V

theorem pCoreOf_ne_bot : pCoreOf 2 H ≠ ⊥ :=
  S.pCoreOf_ne_bot C.vp_le_V C.z_mem vec_a1_ne_one C.tp_le_H C.hHG

theorem oddCoreIn_eq_bot : oddCoreIn H = ⊥ :=
  S.oddCoreIn_eq_bot_of_coord C.hc C.vp_le C.z_mem vec_a1_ne_one C.hA C.hLH C.hHG

theorem vm_le_oTwoUpper : S.vm e ≤ oTwoUpper H := by
  rw [← commutator_vm C.hc, Subgroup.commutator_le]
  intro v hv x hx
  have hθ : θ ∈ oTwoUpper H := mem_oTwoUpper_of_odd C.th_mem_H C.hc.odd
  have hx' : x ∈ oTwoUpper H := (Subgroup.zpowers_le).mpr hθ hx
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (conj_mem_oTwoUpper (C.vm_le_H hv) hx') (Subgroup.inv_mem _ hx')

variable (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)

include h37c h38c in
theorem vm_le_normalizer {K : Subgroup G} (hK : IsComponentIn K H) :
    S.vm e ≤ Subgroup.normalizer (K : Set G) :=
  C.vm_le_oTwoUpper.trans (S.oTwoUpper_le_normalizer h37c h38c C.pCoreOf_ne_bot hK)

include h37c h38c in
theorem th_mem_normalizer {K : Subgroup G} (hK : IsComponentIn K H) :
    θ ∈ Subgroup.normalizer (K : Set G) :=
  S.th_mem_normalizer C.hc h37c h38c C.vp_le C.z_mem vec_a1_ne_one C.hLH C.hHG hK

include h37c h38c in
theorem eq_one_of_mem_centralizer (h3108 : Stmt3_2_10_eight) (h755 : Input7_5_5)
    {K : Subgroup G} (hK : IsComponentIn K H) {w : G} (hw : w ∈ S.vm e)
    (hwK : w ∈ Subgroup.centralizer (K : Set G)) : w = 1 := by
  by_contra hw1
  have hθK := C.th_mem_normalizer h37c h38c hK
  rcases C.case with h | ⟨h, hr⟩
  · subst h
    exact S.not_mem_centralizer_H0 h3108 C.hc C.sylM C.hLH C.hHG hK hθK hw hw1 hwK
  · subst h
    exact S.not_mem_centralizer_H1 h3108 h755 hr C.hc C.sylM C.hLH C.hHG hK
      (S.not_le_of_isComponentIn ((inf_le_inf_left _ (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr C.vp_le_V))).trans C.tp_le_H) hK) hθK hw hw1 hwK

theorem exists_conj_eq {t : G} (ht : t ∈ T ⊓ Subgroup.centralizer (Vp : Set G)) {w : G}
    (hw : w ∈ S.vm e) : ∃ a ∈ Vp, ∃ b ∈ S.vm e, t * w * t⁻¹ = a * b := by
  have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := S.T_le_normalizer_V ht.1
  rcases C.case with h | ⟨h, -⟩
  · have hmem : t * w * t⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp htN w).mp (vm_le (S := S) hw)
    obtain ⟨a, ha, b, hb, hab⟩ := exists_V0_mul_vm C.hc hmem
    exact ⟨a, h ▸ ha, b, hb, hab⟩
  · have htM : t ∈ fsuM T L := S.T_le_fsuM ht.1
    have ht1 : t ∈ Subgroup.centralizer ({S.vec e a1} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr C.z_mem) ht.2
    obtain ⟨g, hg1, hg⟩ := exists_stab C.hc htM ht1
    obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
    set q := SL3One.rho g p with hq
    have key : congrHom e (convI S.hV ⟨t, htN⟩) p = q := by rw [hg]; exact hq.symm
    have hq2 : (vp q).2 0 = 0 := by
      rw [hq, vp_rho]
      exact dact_zero_of_stab hg1 hp.2
    set x := (vp q).1 with hx
    set c := x 0 with hcdef
    refine ⟨S.vec e (pv (c • ((e1, 0) : Vec × Vec))), ?_, S.vec e (pv (x - c • e1, (vp q).2)),
      vec_mem_vm ⟨by change (x - c • e1) 0 = 0; simp [hcdef], hq2⟩, ?_⟩
    · rw [h]
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h0
      · rw [h0, zero_smul, show pv (0 : Vec × Vec) = 1 from rfl, vec_one]
        exact Subgroup.one_mem _
      · rw [h0, one_smul]
        exact Subgroup.mem_zpowers _
    · rw [conj_vec htN, key, ← vec_mul]
      congr 1
      apply vp_injective
      refine Prod.ext ?_ ?_
      · change x = c • e1 + (x - c • e1)
        exact (add_sub_cancel _ _).symm
      · change (vp q).2 = c • 0 + (vp q).2
        rw [smul_zero, zero_add]

theorem exists_index_two : ∃ R : Subgroup G, R ≤ T ⊓ Subgroup.centralizer (Vp : Set G) ∧
    R.relIndex (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ 2 ∧
      ∀ t ∈ R, ∀ w ∈ S.vm e, t * w * t⁻¹ * w⁻¹ ∈ Vp := by
  have hXM : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ fsuM T L := inf_le_left.trans S.T_le_fsuM
  have hX1 : T ⊓ Subgroup.centralizer (Vp : Set G) ≤
      Subgroup.centralizer ({S.vec e a1} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr C.z_mem))
  obtain ⟨R, hRX, hRi, hR⟩ := S.exists_index_two C.hc hXM hX1 C.sylG.2.1
  refine ⟨R, hRX, hRi, fun t ht w hw => ?_⟩
  obtain ⟨g, hg1, hgb, hg⟩ := hR t ht
  have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := S.T_le_normalizer_V (hRX ht).1
  rcases C.case with h | ⟨h, -⟩
  · have hb : t ∈ Subgroup.centralizer ({S.vec e b1} : Set G) := by
      refine Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ?_) (hRX ht).2
      rw [h]
      exact vec_b1_mem_V0 C.hc
    have htV := mem_centralizer_of_blk htN hg1 hgb (hg htN) hb
    have : t * w * t⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_iff.mp htV w (vm_le (S := S) hw), mul_inv_cancel_right]
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h]
    exact conj_mem_of_blk htN hg1 hgb (hg htN) hw

theorem mem_centralizer_V {x : G} (hx1 : x ∈ Subgroup.centralizer (Vp : Set G))
    (hx2 : x ∈ Subgroup.centralizer (S.vm e : Set G)) :
    x ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  rcases C.case with h | ⟨h, -⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_V0_mul_vm C.hc hw
    have h1 := Subgroup.mem_centralizer_iff.mp hx1 a (h ▸ ha)
    have h2 := Subgroup.mem_centralizer_iff.mp hx2 b hb
    calc a * b * x = a * (b * x) := mul_assoc _ _ _
      _ = a * x * b := by rw [h2, mul_assoc]
      _ = x * (a * b) := by rw [h1, mul_assoc]
  · have hxM : x ∈ fsuM T L := C.hA ⟨hx1, hx2⟩
    have hx1' : x ∈ Subgroup.centralizer ({S.vec e a1} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr C.z_mem) hx1
    exact mem_centralizer_of_hyp C.hc hxM hx1' hx2

end Conf

end Setup

end CFSG.Quasithin.H13.Sec77
