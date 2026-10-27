module

public import CFSG.Quasithin.Recognition.RuTypeNorm2
public import CFSG.Quasithin.Recognition.RuTypeSL3b
public import CFSG.Quasithin.Recognition.RuTypeJ22d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem SL3.exists_perp_two : ∀ v w : Fin 3 → ZMod 2,
    ∃ a : Fin 3 → ZMod 2, a ≠ 0 ∧ a ⬝ᵥ v = 0 ∧ a ⬝ᵥ w = 0 := by
  decide +kernel

@[expose] def SL3.inSpan3 (w1 w2 w v : Fin 3 → ZMod 2) : Bool :=
  v == 0 || v == w1 || v == w2 || v == w1 + w2 || v == w || v == w + w1 || v == w + w2 ||
    v == w + w1 + w2

@[expose] def SL3.indep3 (w1 w2 w : Fin 3 → ZMod 2) : Bool :=
  w1 != 0 && w2 != 0 && w1 != w2 && w != 0 && w != w1 && w != w2 && w != w1 + w2

theorem SL3.span_three : ∀ w1 w2 w v : Fin 3 → ZMod 2,
    SL3.indep3 w1 w2 w = true → SL3.inSpan3 w1 w2 w v = true := by
  decide +kernel

theorem SL3.exists_perp_of_ne_top (W : AddSubgroup (Fin 3 → ZMod 2)) (hW : W ≠ ⊤) :
    ∃ a : Fin 3 → ZMod 2, a ≠ 0 ∧ ∀ w ∈ W, a ⬝ᵥ w = 0 := by
  by_cases h1 : ∃ w1 ∈ W, w1 ≠ 0
  · obtain ⟨w1, hw1, hw10⟩ := h1
    by_cases h2 : ∃ w2 ∈ W, w2 ≠ 0 ∧ w2 ≠ w1
    · obtain ⟨w2, hw2, hw20, hw21⟩ := h2
      obtain ⟨a, ha0, ha1, ha2⟩ := SL3.exists_perp_two w1 w2
      refine ⟨a, ha0, fun w hw => ?_⟩
      by_contra haw
      apply hW
      rw [eq_top_iff]
      intro v _
      have hw0 : w ≠ 0 := by rintro rfl; exact haw (dotProduct_zero a)
      have hw1' : w ≠ w1 := by rintro rfl; exact haw ha1
      have hw2' : w ≠ w2 := by rintro rfl; exact haw ha2
      have hw12 : w ≠ w1 + w2 := by
        rintro rfl
        exact haw (by rw [dotProduct_add, ha1, ha2, add_zero])
      have hind : SL3.indep3 w1 w2 w = true := by
        simp only [SL3.indep3, Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨⟨⟨⟨⟨⟨hw10, hw20⟩, Ne.symm hw21⟩, hw0⟩, hw1'⟩, hw2'⟩, hw12⟩
      have hv := SL3.span_three w1 w2 w v hind
      simp only [SL3.inSpan3, Bool.or_eq_true, beq_iff_eq] at hv
      rcases hv with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
      · exact W.zero_mem
      · exact hw1
      · exact hw2
      · exact W.add_mem hw1 hw2
      · exact hw
      · exact W.add_mem hw hw1
      · exact W.add_mem hw hw2
      · exact W.add_mem (W.add_mem hw hw1) hw2
    · push Not at h2
      obtain ⟨a, ha0, ha1, -⟩ := SL3.exists_perp_two w1 w1
      refine ⟨a, ha0, fun w hw => ?_⟩
      by_cases hw0 : w = 0
      · rw [hw0, dotProduct_zero]
      · rw [h2 w hw hw0]
        exact ha1
  · push Not at h1
    refine ⟨![1, 0, 0], by decide, fun w hw => ?_⟩
    rw [h1 w hw, dotProduct_zero]

namespace RuDataN

variable (N : RuDataN G)

theorem toAdd_χ_mul (s t : ruS N.L) :
    Multiplicative.toAdd (N.χ (s * t)) =
      Multiplicative.toAdd (N.χ s) + Multiplicative.toAdd (N.χ t) := by
  rw [map_mul]
  rfl

theorem toAdd_χ_inv (s : ruS N.L) :
    Multiplicative.toAdd (N.χ s⁻¹) = Multiplicative.toAdd (N.χ s) := by
  rw [map_inv]
  ext i j
  have h2 : ∀ x : ZMod 2, -x = x := by decide
  exact h2 _

theorem toAdd_ψU_mul (u u' : ruU N.L N.T) :
    Multiplicative.toAdd (N.ψU (u * u')) =
      Multiplicative.toAdd (N.ψU u) + Multiplicative.toAdd (N.ψU u') := by
  rw [map_mul]
  rfl

theorem toAdd_ψU_inv (u : ruU N.L N.T) :
    Multiplicative.toAdd (N.ψU u⁻¹) = Multiplicative.toAdd (N.ψU u) := by
  rw [map_inv]
  funext i
  have h2 : ∀ a : F4, -a = a := by decide
  exact h2 _

theorem comm_mem_V {s t : G} (hs : s ∈ ruS N.L) (ht : t ∈ ruS N.L) :
    s * t * s⁻¹ * t⁻¹ ∈ ruV N.L := by
  have hmem : s * t * s⁻¹ * t⁻¹ ∈ ruS N.L :=
    mul_mem (mul_mem (mul_mem hs ht) (inv_mem hs)) (inv_mem ht)
  have : (⟨_, hmem⟩ : ruS N.L) ∈ N.χ.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    have e : (⟨_, hmem⟩ : ruS N.L) = ⟨s, hs⟩ * ⟨t, ht⟩ * ⟨s, hs⟩⁻¹ * ⟨t, ht⟩⁻¹ := rfl
    rw [e, N.toAdd_χ_mul, N.toAdd_χ_mul, N.toAdd_χ_mul, N.toAdd_χ_inv, N.toAdd_χ_inv, toAdd_one]
    ext i j
    have h2 : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
    exact h2 _ _
  rw [N.χ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem V_comm_S {v s : G} (hv : v ∈ ruV N.L) (hs : s ∈ ruS N.L) : s * v = v * s :=
  (N.toRuData.mem_V_iff.mp hv).2 s hs

@[expose] noncomputable def sOf (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ruS N.L := by
  classical
  exact if h : IsTraceZero A then (N.χ_surj A h).choose else 1

theorem χ_sOf {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    N.χ (N.sOf A) = Multiplicative.ofAdd A := by
  unfold sOf
  simp only [hA, ↓reduceDIte]
  exact (N.χ_surj A hA).choose_spec

theorem comm_congr_S {s s' t t' : ruS N.L} (hs : N.χ s = N.χ s') (ht : N.χ t = N.χ t') :
    (s : G) * t * (s : G)⁻¹ * (t : G)⁻¹ = (s' : G) * t' * (s' : G)⁻¹ * (t' : G)⁻¹ := by
  have hv : s⁻¹ * s' ∈ N.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs]
    exact inv_mul_cancel _
  have hw : t⁻¹ * t' ∈ N.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ht]
    exact inv_mul_cancel _
  rw [N.χ_ker, Subgroup.mem_subgroupOf] at hv hw
  set v : G := ((s⁻¹ * s' : ruS N.L) : G)
  set w : G := ((t⁻¹ * t' : ruS N.L) : G)
  have hs' : (s' : G) = s * v := by simp [v]
  have ht' : (t' : G) = t * w := by simp [w]
  have h1 : Commute v (t : G) := (N.V_comm_S hv t.2).symm
  have h2 : Commute w (s : G) := (N.V_comm_S hw s.2).symm
  have h3 : Commute v w := (N.V_comm_S hv (N.toRuData.V_le_S hw)).symm
  have hvtw : v * (t * w) = (t * w) * v := (h1.mul_right h3).eq
  have hws : w * (s : G)⁻¹ = (s : G)⁻¹ * w := h2.inv_right.eq
  rw [hs', ht']
  symm
  calc (s : G) * v * (t * w) * (s * v)⁻¹ * (t * w)⁻¹
      = s * (v * (t * w)) * v⁻¹ * (s : G)⁻¹ * w⁻¹ * (t : G)⁻¹ := by group
    _ = s * ((t * w) * v) * v⁻¹ * (s : G)⁻¹ * w⁻¹ * (t : G)⁻¹ := by rw [hvtw]
    _ = s * t * (w * (s : G)⁻¹) * w⁻¹ * (t : G)⁻¹ := by group
    _ = s * t * ((s : G)⁻¹ * w) * w⁻¹ * (t : G)⁻¹ := by rw [hws]
    _ = s * t * (s : G)⁻¹ * (t : G)⁻¹ := by group

@[expose] noncomputable def cform (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Fin 3 → ZMod 2 :=
  Multiplicative.toAdd (N.ψV ⟨_, N.comm_mem_V (N.sOf A).2 (N.sOf B).2⟩)

theorem ψV_comm (s t : ruS N.L) :
    Multiplicative.toAdd (N.ψV ⟨_, N.comm_mem_V s.2 t.2⟩) =
      N.cform (Multiplicative.toAdd (N.χ s)) (Multiplicative.toAdd (N.χ t)) := by
  unfold cform
  congr 3
  exact N.comm_congr_S (by rw [N.χ_sOf (N.χ_trace s), ofAdd_toAdd])
    (by rw [N.χ_sOf (N.χ_trace t), ofAdd_toAdd])

theorem comm_eq_one_iff_cform (s t : ruS N.L) :
    (s : G) * t * (s : G)⁻¹ * (t : G)⁻¹ = 1 ↔
      N.cform (Multiplicative.toAdd (N.χ s)) (Multiplicative.toAdd (N.χ t)) = 0 := by
  rw [← N.ψV_comm]
  constructor
  · intro h
    have : (⟨_, N.comm_mem_V s.2 t.2⟩ : ruV N.L) = 1 := Subtype.ext h
    rw [this, map_one, toAdd_one]
  · intro h
    have : N.ψV ⟨_, N.comm_mem_V s.2 t.2⟩ = 1 :=
      Multiplicative.toAdd.injective (by rw [h, toAdd_one])
    have := congrArg Subtype.val (N.ψV.injective (this.trans (map_one N.ψV).symm))
    exact this

theorem cform_add_left {A B C : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A)
    (hB : IsTraceZero B) (hC : IsTraceZero C) :
    N.cform (A + B) C = N.cform A C + N.cform B C := by
  have hAB : IsTraceZero (A + B) := by
    unfold IsTraceZero at *
    rw [Matrix.trace_add, hA, hB, add_zero]
  set s := N.sOf A
  set t := N.sOf B
  set r := N.sOf C
  have e1 : N.cform (A + B) C = Multiplicative.toAdd (N.ψV ⟨_, N.comm_mem_V (s * t).2 r.2⟩) := by
    rw [N.ψV_comm, map_mul, N.χ_sOf hA, N.χ_sOf hB, N.χ_sOf hC]
    rfl
  have e2 := N.ψV_comm s r
  have e3 := N.ψV_comm t r
  rw [N.χ_sOf hA, N.χ_sOf hC, toAdd_ofAdd, toAdd_ofAdd] at e2
  rw [N.χ_sOf hB, N.χ_sOf hC, toAdd_ofAdd, toAdd_ofAdd] at e3
  rw [e1, ← e2, ← e3, ← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [MulMemClass.coe_mul]
  have hc : Commute ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) (s : G) :=
    (N.V_comm_S (N.comm_mem_V t.2 r.2) s.2).symm
  calc (s : G) * t * r * ((s : G) * t)⁻¹ * (r : G)⁻¹
      = s * ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) * (r * (s : G)⁻¹ * (r : G)⁻¹) := by group
    _ = ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) * s * (r * (s : G)⁻¹ * (r : G)⁻¹) := by
        rw [← hc.eq]
    _ = (s : G) * r * (s : G)⁻¹ * (r : G)⁻¹ * ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) := by
        have hc' : Commute ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹)
            ((s : G) * r * (s : G)⁻¹ * (r : G)⁻¹) :=
          (N.V_comm_S (N.comm_mem_V t.2 r.2) (N.toRuData.V_le_S (N.comm_mem_V s.2 r.2))).symm
        calc ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) * s * (r * (s : G)⁻¹ * (r : G)⁻¹)
            = ((t : G) * r * (t : G)⁻¹ * (r : G)⁻¹) * ((s : G) * r * (s : G)⁻¹ * (r : G)⁻¹) := by
              group
          _ = _ := hc'.eq

theorem cform_self (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : N.cform A A = 0 := by
  unfold cform
  have : (⟨_, N.comm_mem_V (N.sOf A).2 (N.sOf A).2⟩ : ruV N.L) = 1 :=
    Subtype.ext (by simp)
  rw [this, map_one, toAdd_one]

theorem cform_comm {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A)
    (hB : IsTraceZero B) : N.cform B A = N.cform A B := by
  have hinv : ∀ X Y, IsTraceZero X → IsTraceZero Y → N.cform Y X = - N.cform X Y := by
    intro X Y hX hY
    have e := N.ψV_comm (N.sOf X) (N.sOf Y)
    have e' := N.ψV_comm (N.sOf Y) (N.sOf X)
    rw [N.χ_sOf hX, N.χ_sOf hY, toAdd_ofAdd, toAdd_ofAdd] at e e'
    rw [← e, ← e', ← toAdd_inv, ← map_inv]
    congr 2
    apply Subtype.ext
    simp only [InvMemClass.coe_inv]
    group
  rw [hinv A B hA hB]
  have : ∀ v : Fin 3 → ZMod 2, -v = v := fun v => by
    funext i
    have : ∀ x : ZMod 2, -x = x := by decide
    exact this _
  rw [this]

theorem cform_add_right {A B C : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A)
    (hB : IsTraceZero B) (hC : IsTraceZero C) :
    N.cform A (B + C) = N.cform A B + N.cform A C := by
  have hBC : IsTraceZero (B + C) := by
    unfold IsTraceZero at *
    rw [Matrix.trace_add, hB, hC, add_zero]
  rw [N.cform_comm hBC hA, N.cform_add_left hB hC hA, N.cform_comm hA hB, N.cform_comm hA hC]

theorem cform_stAct {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A)
    (hB : IsTraceZero B) (l : N.L) :
    N.cform (stAct (N.θ l) A) (stAct (N.θ l) B) = natAct3 (N.θ l) (N.cform A B) := by
  set s := N.sOf A
  set t := N.sOf B
  have hconj : ∀ x : ruS N.L, (l : G) * x * (l : G)⁻¹ ∈ ruS N.L := fun x =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N.L l.2) x).mp x.2
  let s' : ruS N.L := ⟨_, hconj s⟩
  let t' : ruS N.L := ⟨_, hconj t⟩
  have hs' : Multiplicative.toAdd (N.χ s') = stAct (N.θ l) A := by
    rw [N.χ_equiv l s s' rfl, N.χ_sOf hA, toAdd_ofAdd, toAdd_ofAdd]
  have ht' : Multiplicative.toAdd (N.χ t') = stAct (N.θ l) B := by
    rw [N.χ_equiv l t t' rfl, N.χ_sOf hB, toAdd_ofAdd, toAdd_ofAdd]
  rw [← hs', ← ht', ← N.ψV_comm s' t']
  have e := N.ψV_comm s t
  rw [N.χ_sOf hA, N.χ_sOf hB, toAdd_ofAdd, toAdd_ofAdd] at e
  rw [← e]
  have := N.ψV_equiv l ⟨_, N.comm_mem_V s.2 t.2⟩ ⟨_, N.comm_mem_V s'.2 t'.2⟩ (by
    simp only [s', t']
    group)
  rw [this, toAdd_ofAdd]

theorem eq_zero_of_cform {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A)
    (h : ∀ B, IsTraceZero B → N.cform A B = 0) : A = 0 := by
  have hcent : (N.sOf A : G) ∈ ruV N.L := by
    rw [N.toRuData.mem_V_iff]
    refine ⟨(N.sOf A).2, fun t ht => ?_⟩
    have := (N.comm_eq_one_iff_cform (N.sOf A) ⟨t, ht⟩).mpr (by
      rw [N.χ_sOf hA, toAdd_ofAdd]
      exact h _ (N.χ_trace _))
    calc t * (N.sOf A : G) = ((N.sOf A : G) * t * (N.sOf A : G)⁻¹ * t⁻¹)⁻¹ * N.sOf A * t := by
          group
      _ = (N.sOf A : G) * t := by
          rw [show (N.sOf A : G) * t * (N.sOf A : G)⁻¹ * t⁻¹ = 1 from this, inv_one, one_mul]
  have hk : N.sOf A ∈ N.χ.ker := by
    rw [N.χ_ker, Subgroup.mem_subgroupOf]
    exact hcent
  rw [MonoidHom.mem_ker, N.χ_sOf hA] at hk
  have := congrArg Multiplicative.toAdd hk
  simpa using this

variable [Finite G]

theorem comm_R1_U {r u : G} (hr : r ∈ N.R1) (hu : u ∈ ruU N.L N.T) :
    r * u * r⁻¹ * u⁻¹ ∈ ruV N.L := by
  let W : Subgroup G :=
    { carrier := {r | r ∈ N.L ∧ ∀ u ∈ ruU N.L N.T, r * u * r⁻¹ * u⁻¹ ∈ ruV N.L}
      one_mem' := ⟨N.L.one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hau⟩ ⟨hb, hbu⟩
        refine ⟨mul_mem ha hb, fun u hu => ?_⟩
        have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
            a * (b * u * b⁻¹ * u⁻¹) * a⁻¹ * (a * u * a⁻¹ * u⁻¹) := by group
        rw [e]
        exact mul_mem (N.toRuData.conj_mem_V ha (hbu u hu)) (hau u hu)
      inv_mem' := by
        rintro a ⟨ha, hau⟩
        refine ⟨inv_mem ha, fun u hu => ?_⟩
        have e : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ = a⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact N.toRuData.conj_mem_V (inv_mem ha) (inv_mem (hau u hu)) }
  have hQ : ruQ N.T ≤ W := fun q hq =>
    ⟨N.Q_le_L hq, fun u hu => N.toRuData.Z_le_V (N.comm_mem_Z hq hu)⟩
  have hS : ruS N.L ≤ W := fun s hs =>
    ⟨N.toRuData.S_le_L hs, fun u hu => N.comm_mem_V hs (N.U_le_S hu)⟩
  rw [← N.Q_sup_S] at hr
  exact ((sup_le hQ hS) hr).2 u hu

theorem mem_U_iff {s : G} (hs : s ∈ ruS N.L) :
    s ∈ ruU N.L N.T ↔ SL3.IsRow0 (Multiplicative.toAdd (N.χ ⟨s, hs⟩)) := by
  have hfix : ∀ u (hu : u ∈ ruU N.L N.T),
      SL3.IsRow0 (Multiplicative.toAdd (N.χ ⟨u, N.U_le_S hu⟩)) := by
    intro u hu
    refine (SL3.fix_R0_iff _ (N.χ_trace _)).mp fun g hg => ?_
    obtain ⟨r, rfl⟩ := N.θ_surj g
    have hr : (r : G) ∈ N.R1 := mem_pullL.mpr ⟨r.2, hg⟩
    have hmem := N.comm_R1_U hr hu
    have hru : (r : G) * u * (r : G)⁻¹ ∈ ruS N.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N.L r.2) u).mp (N.U_le_S hu)
    have e := N.χ_equiv r ⟨u, N.U_le_S hu⟩ ⟨_, hru⟩ rfl
    have hk : (⟨_, hru⟩ : ruS N.L) * ⟨u, N.U_le_S hu⟩⁻¹ ∈ N.χ.ker := by
      rw [N.χ_ker, Subgroup.mem_subgroupOf]
      exact hmem
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hk
    have hk' := mul_inv_eq_one.mp hk
    rw [e] at hk'
    have := congrArg Multiplicative.toAdd hk'
    rwa [toAdd_ofAdd] at this
  constructor
  · intro hu
    exact hfix s hu
  · intro h
    let X : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ ruS N.L, SL3.IsRow0 (Multiplicative.toAdd (N.χ ⟨x, hx⟩))}
        one_mem' := ⟨(ruS N.L).one_mem, by
          rw [show (⟨1, (ruS N.L).one_mem⟩ : ruS N.L) = 1 from rfl, map_one, toAdd_one]
          decide⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨mul_mem ha hb, ?_⟩
          rw [show (⟨a * b, mul_mem ha hb⟩ : ruS N.L) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
            N.toAdd_χ_mul]
          obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ha'
          obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb'
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [*]
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨inv_mem ha, ?_⟩
          rw [show (⟨a⁻¹, inv_mem ha⟩ : ruS N.L) = (⟨a, ha⟩ : ruS N.L)⁻¹ from rfl,
            N.toAdd_χ_inv]
          exact ha' }
    have hUX : ruU N.L N.T ≤ X := fun u hu => ⟨N.U_le_S hu, hfix u hu⟩
    have hXS : X ≤ ruS N.L := fun x ⟨hx, _⟩ => hx
    have hcardX : Nat.card X ≤ 32 := by
      have hX := Subgroup.card_ker_mul_card_range (N.χ.comp (X.subgroupOf (ruS N.L)).subtype)
      rw [card_subgroupOf_of_le hXS] at hX
      have hker : Nat.card (N.χ.comp (X.subgroupOf (ruS N.L)).subtype).ker ≤ 8 := by
        rw [← N.toRuData.card_V]
        refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1.1, ?_⟩) ?_
        · have hx := x.2
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
          have : x.1.1 ∈ N.χ.ker := hx
          rw [N.χ_ker, Subgroup.mem_subgroupOf] at this
          exact this
        · intro a b h
          have h' := Subtype.ext_iff.mp h
          exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      have hrange : Nat.card (N.χ.comp (X.subgroupOf (ruS N.L)).subtype).range ≤ 4 := by
        rw [← SL3.card_row0, ← Nat.card_eq_fintype_card]
        refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_
        · obtain ⟨x, hx⟩ := y.2
          rw [← hx]
          exact (Subgroup.mem_subgroupOf.mp x.2).2
        · intro a b h
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Multiplicative.toAdd.injective h')
      calc Nat.card X = _ := hX.symm
        _ ≤ 8 * 4 := Nat.mul_le_mul hker hrange
        _ = 32 := by norm_num
    have heq : ruU N.L N.T = X := Subgroup.eq_of_le_of_card_ge hUX (by
      rw [N.toRuData.card_U]; exact hcardX)
    rw [heq]
    exact ⟨hs, h⟩

omit [Finite G] in
theorem χ_conj (l : N.L) (s : ruS N.L) :
    Multiplicative.toAdd (N.χ ⟨(l : G) * s * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N.L l.2) s).mp s.2⟩) =
      stAct (N.θ l) (Multiplicative.toAdd (N.χ s)) := by
  rw [N.χ_equiv l s _ rfl, toAdd_ofAdd]

theorem U_inf_conjU {l : G} (hl : l ∈ N.L) (hne : N.conjU l ≠ ruU N.L N.T) :
    ruU N.L N.T ⊓ N.conjU l = ruV N.L := by
  refine le_antisymm (fun s hs => ?_) (le_inf N.V_le_U (N.V_le_conjU hl))
  obtain ⟨hsU, hsl⟩ := Subgroup.mem_inf.mp hs
  have hsS := N.U_le_S hsU
  have h1 := (N.mem_U_iff hsS).mp hsU
  have hl' : l⁻¹ * s * l ∈ ruU N.L N.T := N.mem_conjU.mp hsl
  have hl'S := N.U_le_S hl'
  have h2 := (N.mem_U_iff hl'S).mp hl'
  have e := N.χ_conj ⟨l⁻¹, inv_mem hl⟩ ⟨s, hsS⟩
  simp only [inv_inv] at e
  rw [e, show N.θ ⟨l⁻¹, inv_mem hl⟩ = (N.θ ⟨l, hl⟩)⁻¹ from by
    rw [← map_inv]; rfl] at h2
  have hnot : N.θ ⟨l, hl⟩ ∉ SL3.Stab0 := by
    intro hst
    exact hne ((N.conjU_eq_U_iff hl).mpr (mem_pullL.mpr ⟨hl, hst⟩))
  have h0 := SL3.row0_conj_inter _ hnot _ h1 h2
  have hk : (⟨s, hsS⟩ : ruS N.L) ∈ N.χ.ker := by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  rw [N.χ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

end RuDataN

@[expose] def lineSub : Subgroup (Multiplicative (Fin 2 → F4)) where
  carrier := {x | Multiplicative.toAdd x 1 = 0}
  mul_mem' := fun {a b} ha hb => by
    show Multiplicative.toAdd a 1 + Multiplicative.toAdd b 1 = 0
    rw [show Multiplicative.toAdd a 1 = 0 from ha, show Multiplicative.toAdd b 1 = 0 from hb,
      add_zero]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    show -(Multiplicative.toAdd a 1) = 0
    rw [show Multiplicative.toAdd a 1 = 0 from ha, neg_zero]

instance : DecidablePred (· ∈ lineSub) := fun x =>
  inferInstanceAs (Decidable (Multiplicative.toAdd x 1 = 0))

theorem card_lineSub : Nat.card lineSub = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem θ_mem_P0 {t : G} (ht : t ∈ (M.T : Subgroup G)) : M.θ ⟨t, M.toRuData.T_le_L ht⟩ ∈ SL3.P0 :=
  M.toRuDataN.θ_mem_P0 ht _

omit [Finite G] in
theorem φ_mem_SP0 {t : G} (ht : t ∈ (M.T : Subgroup G)) :
    M.φ ⟨t, M.toRuData.T_le_H ht⟩ ∈ Sigma.SP0 := by
  rw [← M.hSP0]
  exact ⟨⟨t, _⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩

omit [Finite G] in
theorem exists_T_of_SP0 {g : SigmaL2F4} (hg : g ∈ Sigma.SP0) :
    ∃ t, ∃ ht : t ∈ (M.T : Subgroup G), M.φ ⟨t, M.toRuData.T_le_H ht⟩ = g := by
  rw [← M.hSP0] at hg
  obtain ⟨⟨t, htH⟩, ht, rfl⟩ := hg
  exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩

theorem card_ψU_V : Nat.card (((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU) = 4 := by
  have h := Subgroup.relIndex_ker (K := (ruV M.L).subgroupOf (ruU M.L M.T)) M.ψU
  have h2 := Subgroup.relIndex_mul_card M.ψU.ker ((ruV M.L).subgroupOf (ruU M.L M.T))
  have hker : M.ψU.ker ≤ (ruV M.L).subgroupOf (ruU M.L M.T) := by
    rw [M.ψU_ker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact M.toRuData.Z_le_V hx
  rw [inf_eq_left.mpr hker, h, M.ψU_ker, card_subgroupOf_of_le M.two.Z_le_U, M.toRuData.card_Z,
    card_subgroupOf_of_le M.V_le_U, M.toRuData.card_V] at h2
  omega

theorem ψU_V_eq : ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU = lineSub := by
  have hcard := M.card_ψU_V
  by_contra hne
  have hnle : ¬ ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU ≤ lineSub := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_lineSub]))
  obtain ⟨_, ⟨⟨v, hvU⟩, hv, rfl⟩, hx⟩ := Set.not_subset.mp hnle
  have hv' : v ∈ ruV M.L := Subgroup.mem_subgroupOf.mp hv
  set x := Multiplicative.toAdd (M.ψU ⟨v, hvU⟩) with hxdef
  have hx1 : x 1 ≠ 0 := hx
  have hline : lineSub ≤ ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := Sigma.SP0_moves x (Multiplicative.toAdd y) hx1 hy
    obtain ⟨t, ht, rfl⟩ := M.exists_T_of_SP0 hg
    have htL := M.toRuData.T_le_L ht
    have hw : t * v * t⁻¹ * v⁻¹ ∈ ruV M.L :=
      mul_mem (M.toRuData.conj_mem_V htL hv') (inv_mem hv')
    refine ⟨⟨_, M.V_le_U hw⟩, Subgroup.mem_subgroupOf.mpr hw, ?_⟩
    apply Multiplicative.toAdd.injective
    have e : (⟨t * v * t⁻¹ * v⁻¹, M.V_le_U hw⟩ : ruU M.L M.T) =
        ⟨t * v * t⁻¹, M.conj_mem_U (M.toRuData.T_le_H ht) hvU⟩ *
          (⟨v, hvU⟩ : ruU M.L M.T)⁻¹ := rfl
    rw [e, M.toAdd_ψU_mul, M.toAdd_ψU_inv, M.ψU_conj ⟨t, M.toRuData.T_le_H ht⟩ ⟨v, hvU⟩,
      ← hxdef, hgy]
  exact hne (Subgroup.eq_of_le_of_card_ge hline (by rw [hcard, card_lineSub])).symm

theorem ψU_V_mem {v : G} (hv : v ∈ ruV M.L) :
    (Multiplicative.toAdd (M.ψU ⟨v, M.V_le_U hv⟩)) 1 = 0 := by
  have : M.ψU ⟨v, M.V_le_U hv⟩ ∈ lineSub := by
    rw [← M.ψU_V_eq]
    exact ⟨⟨v, M.V_le_U hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  exact this

theorem exists_V_of_line {y : Fin 2 → F4} (hy : y 1 = 0) :
    ∃ v, ∃ hv : v ∈ ruV M.L, Multiplicative.toAdd (M.ψU ⟨v, M.V_le_U hv⟩) = y := by
  have : Multiplicative.ofAdd y ∈ ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU := by
    rw [M.ψU_V_eq]
    exact hy
  obtain ⟨⟨v, hvU⟩, hv, hvy⟩ := this
  exact ⟨v, Subgroup.mem_subgroupOf.mp hv, by rw [hvy, toAdd_ofAdd]⟩

theorem φ_S_mem {s : G} (hs : s ∈ ruS M.L) :
    M.φ ⟨s, M.toRuData.T_le_H (M.toRuData.S_le_T hs)⟩ ∈ Sigma.U0 := by
  have hsH := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
  refine Sigma.mem_U0_of_trivial _ (fun x hx => ?_) (fun x => ?_)
  · obtain ⟨v, hv, rfl⟩ := M.exists_V_of_line hx
    rw [← M.ψU_conj ⟨s, hsH⟩ ⟨v, M.V_le_U hv⟩]
    congr 3
    simp only
    rw [M.V_comm_S hv hs, mul_inv_cancel_right]
  · obtain ⟨u, hu⟩ := M.ψU_surj (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (M.ψU u) := by rw [hu, toAdd_ofAdd]
    have huS := M.U_le_S u.2
    have hw := M.comm_mem_V hs huS
    have := M.ψU_V_mem hw
    have e : (⟨s * u * s⁻¹ * (u : G)⁻¹, M.V_le_U hw⟩ : ruU M.L M.T) =
        ⟨s * u * s⁻¹, M.conj_mem_U hsH u.2⟩ * u⁻¹ := rfl
    rw [e, M.toAdd_ψU_mul, M.toAdd_ψU_inv, M.ψU_conj ⟨s, hsH⟩ u] at this
    rw [hx]
    exact this

theorem exists_S_of_U0 {g : SigmaL2F4} (hg : g ∈ Sigma.U0) :
    ∃ s, ∃ hs : s ∈ ruS M.L, M.φ ⟨s, M.toRuData.T_le_H (M.toRuData.S_le_T hs)⟩ = g := by
  have hSH : ruS M.L ≤ ruH M.T := M.toRuData.S_le_T.trans M.toRuData.T_le_H
  have hQH : ruQ M.T ≤ ruH M.T := pCoreOf_le 2 _
  set X := ((ruS M.L).subgroupOf (ruH M.T)).map M.φ
  have hR : (M.R1.subgroupOf (ruH M.T)).map M.φ = X := by
    rw [← M.Q_sup_S, Subgroup.subgroupOf_sup hQH hSH, Subgroup.map_sup]
    have : ((ruQ M.T).subgroupOf (ruH M.T)).map M.φ = ⊥ := by
      rw [← M.φ_ker]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [this, bot_sup_eq]
  have hR1H : M.R1 ≤ ruH M.T := by rw [← M.Q_sup_S]; exact sup_le hQH hSH
  have hcard : Nat.card X = 4 := by
    rw [← hR]
    have h1 := Subgroup.relIndex_ker (K := M.R1.subgroupOf (ruH M.T)) M.φ
    have h2 := Subgroup.relIndex_mul_card M.φ.ker (M.R1.subgroupOf (ruH M.T))
    have hk : M.φ.ker ≤ M.R1.subgroupOf (ruH M.T) := by
      rw [M.φ_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [← M.Q_sup_S]
      exact Subgroup.mem_sup_left hx
    rw [inf_eq_left.mpr hk, h1, M.φ_ker, card_subgroupOf_of_le hQH, M.toRuData.card_Q,
      card_subgroupOf_of_le hR1H, M.card_R1] at h2
    omega
  have hXle : X ≤ Sigma.U0 := by
    rintro _ ⟨⟨s, hsH⟩, hs, rfl⟩
    exact M.φ_S_mem (Subgroup.mem_subgroupOf.mp hs)
  have hXeq : X = Sigma.U0 := Subgroup.eq_of_le_of_card_ge hXle (by rw [hcard, Sigma.card_U0])
  rw [← hXeq] at hg
  obtain ⟨⟨s, hsH⟩, hs, rfl⟩ := hg
  exact ⟨s, Subgroup.mem_subgroupOf.mp hs, rfl⟩

theorem stAct_zero (g : SL(3, ZMod 2)) : stAct g 0 = 0 := by
  have h := SL3.stAct_add g 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem isTraceZero_stA0 : IsTraceZero SL3.stA0 := by
  unfold IsTraceZero
  decide

theorem neg_vec3 (v : Fin 3 → ZMod 2) : -v = v := by
  funext i
  have : ∀ x : ZMod 2, -x = x := by decide
  exact this _

omit [Finite G] in
theorem cform_zero {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    M.cform A 0 = 0 := by
  have h0 : IsTraceZero (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    unfold IsTraceZero
    simp
  have := M.cform_add_right hA h0 h0
  rw [add_zero] at this
  exact (add_eq_left.mp this.symm)

@[expose] def Wc {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    AddSubgroup (Fin 3 → ZMod 2) where
  carrier := {y | ∃ B, IsTraceZero B ∧ M.cform A B = y}
  zero_mem' := ⟨0, by unfold IsTraceZero; simp, M.cform_zero hA⟩
  add_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    refine ⟨B + C, ?_, (M.cform_add_right hA hB hC)⟩
    unfold IsTraceZero at *
    rw [Matrix.trace_add, hB, hC, add_zero]
  neg_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, (neg_vec3 _).symm⟩

omit [Finite G] in
theorem mem_Wc {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) {y : Fin 3 → ZMod 2} :
    y ∈ M.Wc hA ↔ ∃ B, IsTraceZero B ∧ M.cform A B = y := Iff.rfl

omit [Finite G] in
theorem natAct3_mem_Wc {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) (l : M.L)
    {y : Fin 3 → ZMod 2} (hy : y ∈ M.Wc hA) :
    natAct3 (M.θ l) y ∈ M.Wc (A := stAct (M.θ l) A) (by
      unfold IsTraceZero at *; rw [SL3.trace_stAct, hA]) := by
  obtain ⟨B, hB, rfl⟩ := hy
  refine ⟨stAct (M.θ l) B, by unfold IsTraceZero at *; rw [SL3.trace_stAct, hB], ?_⟩
  exact M.cform_stAct hA hB l

@[expose] noncomputable def u0 : ruS M.L := M.sOf SL3.stA0

omit [Finite G] in
theorem χ_u0 : M.χ M.u0 = Multiplicative.ofAdd SL3.stA0 := M.χ_sOf isTraceZero_stA0

theorem u0_mem_U : (M.u0 : G) ∈ ruU M.L M.T := by
  rw [M.mem_U_iff M.u0.2]
  show SL3.IsRow0 (Multiplicative.toAdd (M.χ M.u0))
  rw [M.χ_u0, toAdd_ofAdd]
  decide

omit [Finite G] in
theorem u0_not_mem_V : (M.u0 : G) ∉ ruV M.L := by
  intro h
  have hk : M.u0 ∈ M.χ.ker := by
    rw [M.χ_ker, Subgroup.mem_subgroupOf]
    exact h
  rw [MonoidHom.mem_ker, M.χ_u0] at hk
  have := congrArg Multiplicative.toAdd hk
  rw [toAdd_ofAdd, toAdd_one] at this
  exact absurd (congrFun (congrFun this 0) 2) (by decide)

theorem Wc_stA0 (y : Fin 3 → ZMod 2) : y ∈ M.Wc isTraceZero_stA0 := by
  set W := M.Wc isTraceZero_stA0
  have hcover : ∀ y : Fin 3 → ZMod 2, y ∈ W ∨ y + SL3.e0 ∈ W := by
    intro y
    obtain ⟨v, hv⟩ := M.ψV.surjective (Multiplicative.ofAdd y)
    have hx : (Multiplicative.toAdd (M.ψU ⟨M.u0, M.u0_mem_U⟩)) 1 ≠ 0 := by
      intro h1
      obtain ⟨v', hv', he⟩ := M.exists_V_of_line h1
      apply M.u0_not_mem_V
      have hk : (⟨v', M.V_le_U hv'⟩ : ruU M.L M.T)⁻¹ * ⟨M.u0, M.u0_mem_U⟩ ∈ M.ψU.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        rw [inv_mul_eq_one]
        exact Multiplicative.toAdd.injective he
      rw [M.ψU_ker, Subgroup.mem_subgroupOf] at hk
      have : (M.u0 : G) = v' * (((⟨v', M.V_le_U hv'⟩ : ruU M.L M.T)⁻¹ * ⟨M.u0, M.u0_mem_U⟩ :
          ruU M.L M.T) : G) := by simp
      rw [this]
      exact mul_mem hv' (M.toRuData.Z_le_V hk)
    obtain ⟨g, hg, hgx⟩ := Sigma.U0_moves _ (Multiplicative.toAdd (M.ψU ⟨v, M.V_le_U v.2⟩)) hx
      (M.ψU_V_mem v.2)
    obtain ⟨s, hs, rfl⟩ := M.exists_S_of_U0 hg
    have hsH := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
    have hc := M.comm_mem_V hs M.u0.2
    have hkey : (⟨s * M.u0 * s⁻¹ * (M.u0 : G)⁻¹, M.V_le_U hc⟩ : ruU M.L M.T) *
        (⟨v, M.V_le_U v.2⟩ : ruU M.L M.T)⁻¹ ∈ M.ψU.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      have e : (⟨s * M.u0 * s⁻¹ * (M.u0 : G)⁻¹, M.V_le_U hc⟩ : ruU M.L M.T) =
          ⟨s * M.u0 * s⁻¹, M.conj_mem_U hsH M.u0_mem_U⟩ * (⟨M.u0, M.u0_mem_U⟩)⁻¹ := rfl
      rw [M.toAdd_ψU_mul, M.toAdd_ψU_inv, e, M.toAdd_ψU_mul, M.toAdd_ψU_inv,
        M.ψU_conj ⟨s, hsH⟩ ⟨M.u0, M.u0_mem_U⟩, hgx, toAdd_one]
      funext i
      have h2 : ∀ a : F4, a + a = 0 := by decide
      exact h2 _
    rw [M.ψU_ker, Subgroup.mem_subgroupOf] at hkey
    have hcform : M.cform SL3.stA0 (Multiplicative.toAdd (M.χ ⟨s, hs⟩)) =
        Multiplicative.toAdd (M.ψV ⟨_, hc⟩) := by
      rw [← M.cform_comm isTraceZero_stA0 (M.χ_trace _), ← toAdd_ofAdd SL3.stA0, ← M.χ_u0,
        ← M.ψV_comm ⟨s, hs⟩ M.u0]
    have hmem : Multiplicative.toAdd (M.ψV ⟨_, hc⟩) ∈ W :=
      ⟨_, M.χ_trace _, hcform⟩
    rcases M.mem_Z_iff.mp hkey with h1 | h1
    · left
      have : (⟨_, hc⟩ : ruV M.L) = v := by
        apply Subtype.ext
        have h1' : s * ↑M.u0 * s⁻¹ * (↑M.u0)⁻¹ * (↑v : G)⁻¹ = 1 := h1
        show s * ↑M.u0 * s⁻¹ * (↑M.u0)⁻¹ = ↑v
        rw [← mul_inv_eq_one]
        exact h1'
      rw [this, hv, toAdd_ofAdd] at hmem
      exact hmem
    · right
      have : (⟨_, hc⟩ : ruV M.L) = M.zV * v := by
        apply Subtype.ext
        have h1' : s * ↑M.u0 * s⁻¹ * (↑M.u0)⁻¹ * (↑v : G)⁻¹ = M.z := h1
        show s * ↑M.u0 * s⁻¹ * (↑M.u0)⁻¹ = M.z * ↑v
        rw [← h1']
        group
      rw [this, map_mul, toAdd_mul, M.ψV_zV, hv, toAdd_ofAdd, add_comm] at hmem
      exact hmem
  have hinv : ∀ g ∈ SL3.P0, ∀ y ∈ W, natAct3 g y ∈ W := by
    intro g hg y hy
    rw [← M.hP0] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    have := M.natAct3_mem_Wc isTraceZero_stA0 t hy
    have hfix : stAct (M.θ t) SL3.stA0 = SL3.stA0 :=
      SL3.stA0_fix _ (M.θ_mem_P0 (Subgroup.mem_subgroupOf.mp ht))
    simp only [hfix] at this
    exact this
  have x0 : (⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ : SL(3, ZMod 2)) ∈ SL3.P0 :=
    ⟨by decide, by decide, by decide⟩
  have he1 : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ W := by
    rcases hcover ![0, 1, 0] with h | h
    · exact h
    · have := hinv _ x0 _ h
      have e : natAct3 ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ (![0, 1, 0] + SL3.e0) =
          ![0, 1, 0] := by decide
      rwa [e] at this
  have he01 : (![1, 1, 0] : Fin 3 → ZMod 2) ∈ W := by
    have := hinv _ x0 _ he1
    have e : natAct3 ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ ![0, 1, 0] = ![1, 1, 0] := by
      decide
    rwa [e] at this
  have he0 : SL3.e0 ∈ W := by
    have := W.add_mem he1 he01
    have e : (![0, 1, 0] : Fin 3 → ZMod 2) + ![1, 1, 0] = SL3.e0 := by decide
    rwa [e] at this
  have he2 : (![0, 0, 1] : Fin 3 → ZMod 2) ∈ W := by
    rcases hcover ![0, 0, 1] with h | h
    · exact h
    · have := W.add_mem h he0
      have e : (![0, 0, 1] : Fin 3 → ZMod 2) + SL3.e0 + SL3.e0 = ![0, 0, 1] := by decide
      rwa [e] at this
  have hy : y = (y 0) • SL3.e0 + (y 1) • ![0, 1, 0] + (y 2) • ![0, 0, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hy]
  have hsm : ∀ (c : ZMod 2) (w : Fin 3 → ZMod 2), w ∈ W → c • w ∈ W := by
    intro c w hw
    have : c = 0 ∨ c = 1 := by revert c; decide
    rcases this with rfl | rfl
    · rw [zero_smul]; exact W.zero_mem
    · rw [one_smul]; exact hw
  exact W.add_mem (W.add_mem (hsm _ _ he0) (hsm _ _ he1)) (hsm _ _ he2)

theorem Wc_top {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) (hA0 : A ≠ 0)
    (y : Fin 3 → ZMod 2) : y ∈ M.Wc hA := by
  by_contra hy
  set W := M.Wc hA
  obtain ⟨a, ha0, hWa⟩ := SL3.exists_perp_of_ne_top W (fun h => hy (h ▸ AddSubgroup.mem_top y))
  obtain ⟨h, hh⟩ := SL3.exists_functional_basis a ha0
  have hPh : ∀ g ∈ SL3.P0, ∀ y, a ⬝ᵥ y = 0 → a ⬝ᵥ natAct3 (h * g * h⁻¹) y = 0 := by
    intro g hg y hy
    have h1 : (natAct3 h⁻¹ y) 2 = 0 := by
      rw [← hh (natAct3 h⁻¹ y), ← SL3.natAct3_mul, mul_inv_cancel, SL3.natAct3_one, hy]
    rw [SL3.natAct3_mul, SL3.natAct3_mul, hh]
    exact SL3.P0_plane g hg _ h1
  let X : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    AddSubgroup.closure {B | ∃ g : SL(3, ZMod 2), (∀ y, a ⬝ᵥ y = 0 → a ⬝ᵥ natAct3 g y = 0) ∧
      B = stAct g A}
  have hXprop : ∀ B ∈ X, IsTraceZero B ∧ ∀ C, IsTraceZero C → a ⬝ᵥ M.cform B C = 0 := by
    intro B hB
    induction hB using AddSubgroup.closure_induction with
    | mem B hB =>
      obtain ⟨g, hg, rfl⟩ := hB
      refine ⟨by unfold IsTraceZero at *; rw [SL3.trace_stAct, hA], fun C hC => ?_⟩
      obtain ⟨l, rfl⟩ := M.θ_surj g
      have hC' : IsTraceZero (stAct (M.θ l)⁻¹ C) := by
        unfold IsTraceZero at *; rw [SL3.trace_stAct, hC]
      have e : C = stAct (M.θ l) (stAct (M.θ l)⁻¹ C) := by
        rw [← SL3.stAct_mul, mul_inv_cancel, SL3.stAct_one]
      rw [e, M.cform_stAct hA hC' l]
      exact hg _ (hWa _ ⟨_, hC', rfl⟩)
    | zero =>
      refine ⟨by unfold IsTraceZero; simp, fun C hC => ?_⟩
      have h0 : IsTraceZero (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        unfold IsTraceZero; simp
      have := M.cform_add_left h0 h0 hC
      rw [add_zero] at this
      rw [add_eq_left.mp this.symm, dotProduct_zero]
    | add B B' _ _ hB hB' =>
      refine ⟨by unfold IsTraceZero at *; rw [Matrix.trace_add, hB.1, hB'.1, add_zero],
        fun C hC => ?_⟩
      rw [M.cform_add_left hB.1 hB'.1 hC, dotProduct_add, hB.2 C hC, hB'.2 C hC, add_zero]
    | neg B _ hB =>
      have e : -B = B := by
        ext i j
        have : ∀ x : ZMod 2, -x = x := by decide
        exact this _
      exact (congrArg (fun D => IsTraceZero D ∧ ∀ C, IsTraceZero C → a ⬝ᵥ M.cform D C = 0) e).mpr
        hB
  have hP : IsPGroup 2 SL3.P0 := by
    rw [IsPGroup.iff_card, SL3.card_P0]
    exact ⟨3, rfl⟩
  have hXinv : ∀ g ∈ SL3.P0, ∀ B ∈ X, stAct (h * g * h⁻¹) B ∈ X := by
    intro g hg B hB
    induction hB using AddSubgroup.closure_induction with
    | mem B hB =>
      obtain ⟨g', hg', rfl⟩ := hB
      refine AddSubgroup.subset_closure ⟨h * g * h⁻¹ * g', fun y hy => ?_, ?_⟩
      · rw [SL3.natAct3_mul]
        exact hPh g hg _ (hg' y hy)
      · exact (SL3.stAct_mul _ _ _).symm
    | zero => rw [stAct_zero]; exact X.zero_mem
    | add B B' _ _ hB hB' => rw [SL3.stAct_add]; exact X.add_mem hB hB'
    | neg B _ hB =>
      have e : -B = B := by
        ext i j
        have : ∀ x : ZMod 2, -x = x := by decide
        exact this _
      exact (congrArg (fun D => stAct (h * g * h⁻¹) D ∈ X) e).mpr hB
  have hAX : A ∈ X := AddSubgroup.subset_closure ⟨1, fun y hy => by rwa [SL3.natAct3_one],
    by rw [SL3.stAct_one]⟩
  have h2 : 2 ∣ Nat.card (X : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
    have hdvd : Nat.card X ∣ 2 ^ 9 := by
      have := AddSubgroup.card_addSubgroup_dvd_card X
      rwa [Nat.card_eq_fintype_card (α := Matrix (Fin 3) (Fin 3) (ZMod 2)),
        show Fintype.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 2 ^ 9 by
          show Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 2 ^ 9
          rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
          norm_num] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk'
      have := AddSubgroup.eq_bot_of_card_eq X hk'
      rw [this] at hAX
      exact hA0 ((AddSubgroup.mem_bot).mp hAX)
    show 2 ∣ Nat.card X
    rw [hk']
    exact dvd_pow_self 2 hk0
  obtain ⟨B, hB, hB0, hBfix⟩ := SL3.exists_fixed_ne hP
    (fun g B => stAct (h * (g : SL(3, ZMod 2)) * h⁻¹) B)
    (fun B => by rw [OneMemClass.coe_one, mul_one, mul_inv_cancel, SL3.stAct_one])
    (fun g g' B => by
      rw [show h * ((g * g' : SL3.P0) : SL(3, ZMod 2)) * h⁻¹ =
          (h * (g : SL(3, ZMod 2)) * h⁻¹) * (h * (g' : SL(3, ZMod 2)) * h⁻¹) by
        rw [Subgroup.coe_mul]; group, SL3.stAct_mul])
    (X : Set _) (fun g B hB => hXinv g g.2 B hB) h2 X.zero_mem
    (fun g => stAct_zero _)
  have hB' : stAct h⁻¹ B = SL3.stA0 := by
    have hBtr := (hXprop B hB).1
    have htr : (stAct h⁻¹ B).trace = 0 := by
      rw [SL3.trace_stAct]
      exact hBtr
    have hfixP : ∀ g ∈ SL3.P0, stAct g (stAct h⁻¹ B) = stAct h⁻¹ B := by
      intro g hg
      have := hBfix ⟨g, hg⟩
      simp only at this
      calc stAct g (stAct h⁻¹ B) = stAct h⁻¹ (stAct (h * g * h⁻¹) B) := by
            rw [← SL3.stAct_mul, ← SL3.stAct_mul,
              show h⁻¹ * (h * g * h⁻¹) = g * h⁻¹ by group]
        _ = stAct h⁻¹ B := by rw [this]
    rcases SL3.fix_P0_st (stAct h⁻¹ B) htr hfixP with h0 | h0
    · exfalso
      apply hB0
      have := congrArg (stAct h) h0
      rwa [← SL3.stAct_mul, mul_inv_cancel, SL3.stAct_one, stAct_zero] at this
    · exact h0
  have hBeq : B = stAct h SL3.stA0 := by
    rw [← hB', ← SL3.stAct_mul, mul_inv_cancel, SL3.stAct_one]
  obtain ⟨l, rfl⟩ := M.θ_surj h
  obtain ⟨C, hC, hCy⟩ := M.Wc_stA0 (Pi.single 2 1)
  have := (hXprop B hB).2 _ (show IsTraceZero (stAct (M.θ l) C) by
    unfold IsTraceZero at *; rw [SL3.trace_stAct, hC])
  rw [hBeq, M.cform_stAct isTraceZero_stA0 hC l, hCy, hh] at this
  exact absurd this (by decide)

theorem card_centralizer_S {t : G} (ht : t ∈ ruS M.L) (htV : t ∉ ruV M.L) :
    Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 8 := by
  set A := Multiplicative.toAdd (M.χ ⟨t, ht⟩)
  have hA : IsTraceZero A := M.χ_trace _
  have hA0 : A ≠ 0 := by
    intro h0
    apply htV
    have hk : (⟨t, ht⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h0)
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  let f : ruS M.L →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun s => Multiplicative.ofAdd (M.cform A (Multiplicative.toAdd (M.χ s)))
      map_one' := by rw [map_one, toAdd_one, M.cform_zero hA]; rfl
      map_mul' := fun s s' => by
        rw [map_mul, toAdd_mul, M.cform_add_right hA (M.χ_trace s) (M.χ_trace s'), ofAdd_add] }
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨B, hB, hBy⟩ := M.Wc_top hA hA0 (Multiplicative.toAdd y)
    obtain ⟨s, hs⟩ := M.χ_surj B hB
    refine ⟨s, ?_⟩
    show Multiplicative.ofAdd (M.cform A (Multiplicative.toAdd (M.χ s))) = y
    rw [hs, toAdd_ofAdd, hBy, ofAdd_toAdd]
  have hcomm : ∀ s : ruS M.L, f s = 1 ↔ t * s = s * t := by
    intro s
    have e1 : f s = 1 ↔ M.cform A (Multiplicative.toAdd (M.χ s)) = 0 := by
      constructor
      · intro h
        have := congrArg Multiplicative.toAdd h
        simpa [f] using this
      · intro h
        show Multiplicative.ofAdd _ = 1
        rw [h]
        rfl
    rw [e1, ← M.comm_eq_one_iff_cform ⟨t, ht⟩ s]
    constructor
    · intro h
      calc t * (s : G) = t * s * t⁻¹ * (s : G)⁻¹ * s * t := by group
        _ = s * t := by rw [show t * (s : G) * t⁻¹ * (s : G)⁻¹ = 1 from h, one_mul]
    · intro h
      show t * (s : G) * t⁻¹ * (s : G)⁻¹ = 1
      rw [h]
      group
  have hker : Nat.card f.ker = Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer ({t} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((hcomm s.1).mp (MonoidHom.mem_ker.mp s.2)).symm⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.mp s.2).1⟩, MonoidHom.mem_ker.mpr
          ((hcomm _).mpr (Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.mem_inf.mp s.2).2).symm)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, M.toRuData.card_S, Nat.card_eq_fintype_card (α := Multiplicative (Fin 3 → ZMod 2))]
    at h
  have : Fintype.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := rfl
  rw [this] at h
  omega

end RuDataM

end CFSG.Quasithin.RuType
