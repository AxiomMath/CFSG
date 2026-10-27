module

public import CFSG.Quasithin.H13.A5S1521e
public import CFSG.Quasithin.H13.A5S1521f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff piQ_eq_iff Tstar polarQ)
open scoped commutatorElement

@[expose] noncomputable def tz {G : Type} [Group G] (x : G) : ZMod 2 := by
  classical exact if x = 1 then 0 else 1

theorem tz_one {G : Type} [Group G] : tz (1 : G) = 0 := by
  classical
  simp [tz]

theorem tz_eq_zero_iff {G : Type} [Group G] (x : G) : tz x = 0 ↔ x = 1 := by
  classical
  unfold tz
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem tz_mul {x y : G} (hx : x ∈ V₁) (hy : y ∈ V₁) : tz (x * y) = tz x + tz y := by
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, tz_one, zero_add]
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, tz_one, add_zero]
  have hxy : x = y := by
    have := A5.HypL1.eq_of_ne_one_of_card_two S.card_V1 (a := ⟨x, hx⟩) (c := ⟨y, hy⟩)
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hx2 : x * y = 1 := by
    rw [← hxy, ← pow_two]
    exact S.elemAbelian_V.2 x (S.V1_le_V hx)
  have h1 : tz x = 1 := by
    have := (tz_eq_zero_iff x).not.mpr hx1
    revert this
    generalize tz x = t
    decide +revert
  have h2 : tz y = 1 := by
    have := (tz_eq_zero_iff y).not.mpr hy1
    revert this
    generalize tz y = t
    decide +revert
  rw [hx2, tz_one, h1, h2]
  decide

theorem UH_le_H' : conjClosure V₃ H ≤ H :=
  S.hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)

theorem comm_V1 {x v : G} (hx : x ∈ H) (hv : v ∈ V₁) : v * x = x * v :=
  Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer hx) v hv

@[expose] noncomputable def sqF : S.Ut → ZMod 2 := fun w =>
  tz (((Function.surjInv S.utMk_surjective w : ↥(conjClosure V₃ H)) : G) ^ 2)

theorem sqF_mk (u : ↥(conjClosure V₃ H)) : S.sqF (S.utMk u) = tz ((u : G) ^ 2) := by
  have hu' : S.utMk (Function.surjInv S.utMk_surjective (S.utMk u)) = S.utMk u :=
    Function.surjInv_eq _ _
  have hv : ((u⁻¹ * Function.surjInv S.utMk_surjective (S.utMk u) : ↥(conjClosure V₃ H)) : G) ∈
      V₁ := by
    rw [← S.utMk_eq_one_iff, map_mul, map_inv, hu', inv_mul_cancel]
  show tz (((Function.surjInv S.utMk_surjective (S.utMk u) : ↥(conjClosure V₃ H)) : G) ^ 2) = _
  generalize hv' : ((u⁻¹ * Function.surjInv S.utMk_surjective (S.utMk u) :
    ↥(conjClosure V₃ H)) : G) = v at hv
  have e : ((Function.surjInv S.utMk_surjective (S.utMk u) : ↥(conjClosure V₃ H)) : G) =
      (u : G) * v := by
    rw [← hv']
    simp
  have hvc : v * u = u * v := S.comm_V1 (S.UH_le_H' u.2) hv
  have hv2 : v ^ 2 = 1 := S.elemAbelian_V.2 v (S.V1_le_V hv)
  rw [e]
  congr 1
  calc ((u : G) * v) ^ 2 = (u : G) ^ 2 * v ^ 2 := by
        rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc v, hvc, mul_assoc, mul_assoc]
    _ = (u : G) ^ 2 := by rw [hv2, mul_one]

theorem comm_mem_V1 {a w : G} (ha : a ∈ conjClosure V₃ H) (hw : w ∈ conjClosure V₃ H) :
    a⁻¹ * w * a * w⁻¹ ∈ V₁ := by
  have h := S.hF.commutator_conjClosure_le a⁻¹ (Subgroup.inv_mem _ ha) w
    (S.hF.conjClosure_Vp_le_pCoreOf hw)
  simpa using h

theorem polar_sqF (a w : ↥(conjClosure V₃ H)) :
    polarQ S.sqF (S.utMk a) (S.utMk w) =
      tz ((a : G)⁻¹ * (w : G) * (a : G) * (w : G)⁻¹) := by
  have hc := S.comm_mem_V1 a.2 w.2
  have ha2 := S.hF.sq_mem_conjClosure _ a.2
  have hw2 := S.hF.sq_mem_conjClosure _ w.2
  have hcw : ((a : G)⁻¹ * w * a * (w : G)⁻¹) * w = w * ((a : G)⁻¹ * w * a * (w : G)⁻¹) :=
    S.comm_V1 (S.UH_le_H' w.2) hc
  have e : ((a : G) * w) ^ 2 = (a : G) ^ 2 * ((w : G) ^ 2 * ((a : G)⁻¹ * w * a * (w : G)⁻¹)) := by
    have h1 : (w : G) * w * ((a : G)⁻¹ * w * a * (w : G)⁻¹) =
        ((a : G)⁻¹ * w * a * (w : G)⁻¹) * (w * w) := by
      rw [mul_assoc, ← hcw, ← mul_assoc, ← hcw]
      group
    rw [pow_two, pow_two, pow_two, h1]
    group
  rw [polarQ, ← map_mul, S.sqF_mk, S.sqF_mk, S.sqF_mk, Subgroup.coe_mul, e,
    S.tz_mul ha2 (V₁.mul_mem hw2 hc), S.tz_mul hw2 hc]
  ring

theorem polar_sqF_add (x y w : S.Ut) :
    polarQ S.sqF (x * y) w = polarQ S.sqF x w + polarQ S.sqF y w := by
  obtain ⟨a, rfl⟩ := S.utMk_surjective x
  obtain ⟨b, rfl⟩ := S.utMk_surjective y
  obtain ⟨c, rfl⟩ := S.utMk_surjective w
  rw [← map_mul, S.polar_sqF, S.polar_sqF, S.polar_sqF, Subgroup.coe_mul]
  have hca := S.comm_mem_V1 a.2 c.2
  have hcb := S.comm_mem_V1 b.2 c.2
  have hk : ((a : G)⁻¹ * c * a * (c : G)⁻¹) * (b : G)⁻¹ =
      (b : G)⁻¹ * ((a : G)⁻¹ * c * a * (c : G)⁻¹) :=
    S.comm_V1 (H.inv_mem (S.UH_le_H' b.2)) hca
  have e : ((a : G) * b)⁻¹ * c * (a * b) * (c : G)⁻¹ =
      ((a : G)⁻¹ * c * a * (c : G)⁻¹) * ((b : G)⁻¹ * c * b * (c : G)⁻¹) := by
    have h2 : ((a : G)⁻¹ * c * a * (c : G)⁻¹) * ((b : G)⁻¹ * c * b * (c : G)⁻¹) =
        ((a : G)⁻¹ * c * a * (c : G)⁻¹) * (b : G)⁻¹ * (c * b * (c : G)⁻¹) := by group
    rw [h2, hk]
    group
  rw [e, S.tz_mul hca hcb]

theorem sqF_rhoA (x : Hstar H) (w : S.Ut) : S.sqF (S.rhoA x w) = S.sqF w := by
  obtain ⟨h, rfl⟩ := piQ_surjective H x
  obtain ⟨u, rfl⟩ := S.utMk_surjective w
  have hmem : (h : G) * u * (h : G)⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H h.2) u).mp u.2
  rw [S.rhoA_mk h u ⟨_, hmem⟩ rfl, S.sqF_mk, S.sqF_mk]
  have hu2 := S.hF.sq_mem_conjClosure _ u.2
  have e : ((h : G) * u * (h : G)⁻¹) ^ 2 = (h : G) * (u : G) ^ 2 * (h : G)⁻¹ := by
    rw [pow_two, pow_two]
    group
  show tz (((h : G) * u * (h : G)⁻¹) ^ 2) = tz ((u : G) ^ 2)
  rw [e, ← S.comm_V1 h.2 hu2, mul_inv_cancel_right]

theorem polar_sqF_ne : ∃ x w : S.Ut, polarQ S.sqF x w ≠ 0 := by
  by_contra hall
  push Not at hall
  apply S.nonabelian
  rw [conjClosure]
  refine F7.isElemAbelian_closure _ ?_ ?_
  · rintro _ ⟨h, hh, z, hz, rfl⟩ _ ⟨h', hh', z', hz', rfl⟩
    have hx : h * z * h⁻¹ ∈ conjClosure V₃ H := mem_conjClosure hh hz
    have hy : h' * z' * h'⁻¹ ∈ conjClosure V₃ H := mem_conjClosure hh' hz'
    have h0 := hall (S.utMk ⟨_, hx⟩) (S.utMk ⟨_, hy⟩)
    rw [S.polar_sqF, tz_eq_zero_iff] at h0
    simp only at h0
    have e := h0
    rw [mul_inv_eq_one] at e
    calc h * z * h⁻¹ * (h' * z' * h'⁻¹) =
          h * z * h⁻¹ * ((h * z * h⁻¹)⁻¹ * (h' * z' * h'⁻¹) * (h * z * h⁻¹)) := by rw [e]
      _ = h' * z' * h'⁻¹ * (h * z * h⁻¹) := by group
  · rintro _ ⟨h, hh, z, hz, rfl⟩
    have e : (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by rw [pow_two, pow_two]; group
    rw [e, F7.isElemAbelian_pow_eq_one S.hF.elemAbelian_Vp hz]
    group

theorem Tstar_le_normalizer_L1 :
    Tstar T H ≤ Subgroup.normalizer (imQ H L₁ : Set (Hstar H)) := by
  rintro _ ⟨t, ht, rfl⟩
  have htN := S.T_le_normalizer_L1 (show (t : G) ∈ T from ht)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨l, hl, rfl⟩ := (mem_imQ S.L1_le_H).mp hy
    have hmem : (t : G) * l * (t : G)⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp htN l).mp hl
    refine (mem_imQ S.L1_le_H).mpr ⟨_, hmem, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro hy
    obtain ⟨l, hl, hly⟩ := (mem_imQ S.L1_le_H).mp hy
    have hmem : (t : G)⁻¹ * l * t ∈ L₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) l).mp hl
      simpa using this
    refine (mem_imQ S.L1_le_H).mpr ⟨_, hmem, ?_⟩
    have e : piQ H ⟨(t : G)⁻¹ * l * t, S.L1_le_H hmem⟩ =
        (piQ H t)⁻¹ * piQ H ⟨l, S.L1_le_H hl⟩ * piQ H t := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, hly]
    group

theorem iSup_Vt3 : (⨆ y : Hstar H, S.Vt3.map (S.rhoA y).toMonoidHom) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  obtain ⟨⟨u, hu⟩, rfl⟩ := S.utMk_surjective w
  have key : ∀ x (hx : x ∈ Subgroup.closure {x | ∃ h ∈ H, ∃ z ∈ V₃, h * z * h⁻¹ = x}),
      S.utMk ⟨x, hx⟩ ∈ ⨆ y : Hstar H, S.Vt3.map (S.rhoA y).toMonoidHom := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      refine Subgroup.mem_iSup_of_mem (piQ H ⟨h, hh⟩) ⟨S.utMk ⟨z, le_conjClosure V₃ H hz⟩,
        ⟨⟨z, le_conjClosure V₃ H hz⟩, hz, rfl⟩, ?_⟩
      exact S.rhoA_mk ⟨h, hh⟩ _ _ rfl
    | one =>
      convert Subgroup.one_mem (⨆ y : Hstar H, S.Vt3.map (S.rhoA y).toMonoidHom) using 1
      exact map_one S.utMk
    | mul a b ha hb iha ihb =>
      have e : S.utMk ⟨a * b, Subgroup.mul_mem _ ha hb⟩ = S.utMk ⟨a, ha⟩ * S.utMk ⟨b, hb⟩ := by
        rw [← map_mul]
        rfl
      rw [e]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have e : S.utMk ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ = (S.utMk ⟨a, ha⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e]
      exact Subgroup.inv_mem _ iha
  exact key u hu

theorem exists_comm_sq_ne_one
    (hF956 : A5.StmtF956i) (h38 : A38ForSQTK) {Y : Subgroup G}
    (SY : A5SitY S Y) (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)))
    (h3 : ∀ l ∈ L₁, l ^ 3 ∈ pCoreOf 2 L₁) (hF : A5.Facts1321) (hR : A5.FactRankRows1321)
    (hA7 : A5.FactA7Grp1321) (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321)
    (hQ : A5.FactQuadRows1321) {c : G} (hc : c ∈ L₁) (hc3 : c ^ 3 = 1)
    (hcQ : c ∉ pCoreOf 2 H) :
    ∃ u ∈ conjClosure V₃ H, u * c = c * u ∧ u ^ 2 ≠ 1 := by
  obtain ⟨v, hv, hvQ⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 H := Set.not_subset.mp S.not_V_le
  obtain ⟨K, hK, hKb⟩ := S.exists_component hF956 SY h1519 hv hvQ
  have hcH : c ∈ H := S.L1_le_H hc
  have hcs3 : piQ H ⟨c, hcH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext hc3
    rw [this, map_one]
  have hcs1 : piQ H ⟨c, hcH⟩ ≠ 1 := fun h => hcQ ((piQ_eq_one_iff _).mp h)
  obtain ⟨w, hw, hqw⟩ := A5.Hyp1321.exists_fix_quad (S.toHyp1321 hF956 hv hvQ K hK hKb)
    (S.toHypY hF956 h38 hv hvQ K hK hKb SY h1519) (S.toHypL1 hF956 h38 hv hvQ K hK hKb h3)
    hF hR hA7 hL3 hO hQ (h38 _ S.sqtkHyp_Hstar) S.isSylowTwoOf_Tstar S.Tstar_le_normalizer_L1
    S.iSup_Vt3 S.sqF S.sqF_rhoA S.polar_sqF_add S.polar_sqF_ne
    ((mem_imQ S.L1_le_H).mpr ⟨c, hc, rfl⟩) hcs3 hcs1
  obtain ⟨u, rfl⟩ := S.utMk_surjective w
  have hmem : c * u * c⁻¹ ∈ conjClosure V₃ H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H hcH) u).mp u.2
  have hw' : S.rhoA (piQ H ⟨c, hcH⟩) (S.utMk u) = S.utMk u := hw
  rw [S.rhoA_mk ⟨c, hcH⟩ u ⟨_, hmem⟩ rfl] at hw'
  have hvV : (u : G)⁻¹ * (c * u * c⁻¹) ∈ V₁ := by
    have h' : S.utMk (u⁻¹ * ⟨_, hmem⟩) = 1 := by rw [map_mul, map_inv, hw', inv_mul_cancel]
    rw [S.utMk_eq_one_iff] at h'
    exact h'
  generalize hvdef : (u : G)⁻¹ * (c * u * c⁻¹) = x at hvV
  have hcx : c * x * c⁻¹ = x := by
    rw [← S.comm_V1 hcH hvV]
    group
  have f1 : c * u * c⁻¹ = u * x := by rw [← hvdef]; group
  have f2 : c * ((u : G) * x) * c⁻¹ = u * x * x := by
    calc c * ((u : G) * x) * c⁻¹ = (c * u * c⁻¹) * (c * x * c⁻¹) := by group
      _ = u * x * x := by rw [f1, hcx]
  have f3 : c * ((u : G) * x * x) * c⁻¹ = u * x * x * x := by
    calc c * ((u : G) * x * x) * c⁻¹ = (c * (u * x) * c⁻¹) * (c * x * c⁻¹) := by group
      _ = u * x * x * x := by rw [f2, hcx]
  have hx2 : x * x = 1 := by
    rw [← pow_two]
    exact S.elemAbelian_V.2 x (S.V1_le_V hvV)
  have hx1 : x = 1 := by
    have hc3' : c * (c * c) = 1 := by rw [← pow_three]; exact hc3
    have e : c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * u * (c * (c * c))⁻¹ := by
      group
    rw [hc3', one_mul, inv_one, mul_one] at e
    have h : (u : G) = u * x * x * x := by
      calc (u : G) = c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ := e.symm
        _ = u * x * x * x := by rw [f1, f2, f3]
    rw [mul_assoc (u : G) x x, hx2, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  refine ⟨u, u.2, ?_, ?_⟩
  · rw [hx1, mul_one] at f1
    calc (u : G) * c = c * u * c⁻¹ * c := by rw [f1]
      _ = c * u := by group
  · intro hu2
    apply hqw
    rw [S.sqF_mk, hu2, tz_one]

end A5Sit

end CFSG.Quasithin.H13
