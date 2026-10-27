module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4C
public import CFSG.Quasithin.Vol2.Ch12Sec7L22a
public import CFSG.Quasithin.Vol2.Ch12Sec7ModP

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem K_le_normalizer (h : Hyp1271 G T L V) (t : G) :
    L ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (V : Set G) :=
  inf_le_left.trans (L_le_normalizer h)

omit [Finite G] in
theorem mem_autOn_K_iff {C : Coding ↥V} (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V)
    (h1 : C.cd ⟨t, ht⟩ = 1) (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.centralizer ({t} : Set G)) V ↔ C.cB a ∈ stab1 := by
  have e := mem_autOn_inf_centralizer hC ⟨t, ht⟩ a
  simp only at e
  rw [e, h1, stab1, List.mem_filter, beq_iff_eq]

theorem mem_autOn_Lt_iff
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V)
    (h1 : C.cd ⟨t, ht⟩ = 1) (a : MulAut ↥V) :
    a ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V ↔ C.cB a ∈ stab1 := by
  rw [autOn_oTwoUpper (K_le_normalizer h t)]
  constructor
  · intro ha
    exact (mem_autOn_K_iff hC ht h1 a).1 (oTwoUpper_le' _ ha)
  · intro ha
    obtain ⟨u, hu, v, hv, hu3, hv3, he⟩ := cert4_gen3 _ ha
    obtain ⟨b, rfl⟩ := hC.2 u (stab1_sub hu).1
    obtain ⟨d, rfl⟩ := hC.2 v (stab1_sub hv).1
    have hab : a = b * d := C.cB_injective (by rw [C.cB_mul, ← he])
    rw [hab]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨(mem_autOn_K_iff hC ht h1 b).2 hu, odd_of_pow3 C hu3⟩)
      (Subgroup.subset_closure ⟨(mem_autOn_K_iff hC ht h1 d).2 hv, odd_of_pow3 C hv3⟩)

theorem exists_Lt_of_stab1
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V)
    (h1 : C.cd ⟨t, ht⟩ = 1) {B : B6} (hB : B ∈ stab1) :
    ∃ x, ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      x ∈ oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) ∧ C.cB (conjAct V ⟨x, hx⟩) = B := by
  obtain ⟨a, rfl⟩ := hC.2 B (stab1_sub hB).1
  obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ((mem_autOn_Lt_iff h hC ht h1 a).2 hB)
  exact ⟨x, hx, hxL, rfl⟩

omit [IsMulCommutative ↥V] in
theorem commutator_le_V (h : Hyp1271 G T L V) (K : Subgroup G) (hK : K ≤ L) :
    ⁅V, K⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hm := (Subgroup.mem_normalizer_iff.1 (L_le_normalizer h (hK hx)) v⁻¹).1 (V.inv_mem hv)
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact V.mul_mem hv (by simpa [mul_assoc] using hm)

theorem V_eq_commutator
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V)
    (h1 : C.cd ⟨t, ht⟩ = 1) :
    V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))⁆ := by
  apply le_antisymm
  · apply le_of_comm_codes (C := C)
    intro g hg c hc
    obtain ⟨x, hx, hxL, hxg⟩ := exists_Lt_of_stab1 h hC ht h1 hg
    have hmem := Subgroup.commutator_mem_commutator (C.dc c).2 hxL
    rw [commutator_eq_coe hx] at hmem
    have e : (C.dc c * (conjAct V ⟨x, hx⟩ (C.dc c))⁻¹ : ↥V) = C.dc (c ^^^ g.app c) := by
      apply C.cd_injective
      rw [cd_commutator, C.cd_dc c hc, hxg,
        C.cd_dc _ (xor_lt_64' hc (B6.app_lt (gm6_valid g (stab1_sub hg).1) c))]
    rw [e] at hmem
    exact hmem
  · exact commutator_le_V h _ ((oTwoUpper_le' _).trans inf_le_left)

theorem V_le_Lt
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {t : G} (ht : t ∈ V) (h1 : C.cd ⟨t, ht⟩ = 1) :
    V ≤ oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hVK : V ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G) := by
    intro v hv
    apply normalizer_of_maps
    intro x hx
    obtain ⟨hxL, hxt⟩ := Subgroup.mem_inf.1 hx
    have hvL : v ∈ Subgroup.normalizer (L : Set G) :=
      h.hyp.normalizes (le_T_of_1222 h1222 h hv)
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hvL x).1 hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt ⊢
    have hvt : v * t = t * v := congrArg Subtype.val (mul_comm (⟨v, hv⟩ : ↥V) ⟨t, ht⟩)
    have hvt' : v⁻¹ * t = t * v⁻¹ := by
      calc v⁻¹ * t = v⁻¹ * (t * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * t) * v⁻¹ := by rw [hvt]
        _ = t * v⁻¹ := by group
    calc v * x * v⁻¹ * t = v * x * (v⁻¹ * t) := by group
      _ = v * x * (t * v⁻¹) := by rw [hvt']
      _ = v * (x * t) * v⁻¹ := by group
      _ = v * (t * x) * v⁻¹ := by rw [hxt]
      _ = v * t * x * v⁻¹ := by group
      _ = t * v * x * v⁻¹ := by rw [hvt]
      _ = t * (v * x * v⁻¹) := by group
  have hVO := hVK.trans (normalizer_le_normalizer_oTwoUpper _)
  have hle : ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))⁆ ≤
      oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 (hVO hv) x).1 hx)
      (Subgroup.inv_mem _ hx)
  calc V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))⁆ :=
        V_eq_commutator h hC ht h1
    _ ≤ _ := hle

end CFSG.Quasithin.H13.S127.Mod

end
