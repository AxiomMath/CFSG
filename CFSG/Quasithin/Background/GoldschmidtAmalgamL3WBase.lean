module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VNbr

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] def commPre (U S : Subgroup D) (hab : IsElemAbelian 2 U) (hS : S ≤ U)
    (t : D) (ht : t ∈ Subgroup.normalizer (U : Set D)) : Subgroup D where
  carrier := {w | w ∈ U ∧ t * w * t⁻¹ * w⁻¹ ∈ S}
  mul_mem' := by
    rintro w w' ⟨hw, hwS⟩ ⟨hw', hw'S⟩
    refine ⟨U.mul_mem hw hw', ?_⟩
    have e : t * (w * w') * t⁻¹ * (w * w')⁻¹ =
        (t * w * t⁻¹ * w⁻¹) * (w * (t * w' * t⁻¹ * w'⁻¹) * w⁻¹) := by group
    rw [e]
    have hc : w * (t * w' * t⁻¹ * w'⁻¹) = (t * w' * t⁻¹ * w'⁻¹) * w :=
      isElemAbelian_comm hab hw (hS hw'S)
    rw [hc]
    have e2 : (t * w' * t⁻¹ * w'⁻¹) * w * w⁻¹ = t * w' * t⁻¹ * w'⁻¹ := by group
    rw [e2]
    exact S.mul_mem hwS hw'S
  one_mem' := ⟨U.one_mem, by simp⟩
  inv_mem' := by
    rintro w ⟨hw, hwS⟩
    refine ⟨U.inv_mem hw, ?_⟩
    have htw : t * w * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp ht w).mp hw
    have hc' : (t * w * t⁻¹)⁻¹ * w = w * (t * w * t⁻¹)⁻¹ :=
      isElemAbelian_comm hab (U.inv_mem htw) hw
    have e : t * w⁻¹ * t⁻¹ * (w⁻¹)⁻¹ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by
      calc t * w⁻¹ * t⁻¹ * (w⁻¹)⁻¹ = (t * w * t⁻¹)⁻¹ * w := by group
        _ = w * (t * w * t⁻¹)⁻¹ := hc'
        _ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by group
    show t * w⁻¹ * t⁻¹ * (w⁻¹)⁻¹ ∈ S
    rw [e]
    exact S.inv_mem hwS

omit [Finite D] in
theorem conjSub_commutator_sub (g : D) (H K : Subgroup D) :
    conjSub g ⁅H, K⁆ = ⁅conjSub g H, conjSub g K⁆ :=
  Subgroup.map_commutator H K (MulAut.conj g).toMonoidHom

@[expose] noncomputable def Theta (z : D) (V : Subgroup D) (u v : CosetGeom (A ⊔ B) A B) :
    Subgroup D :=
  Zv z v ⊔ ⁅stab u ⊓ stab v, Vv V v⁆

omit [Finite D] in
theorem comm_mem_Theta {u v : CosetGeom (A ⊔ B) A B} {t w : D} (ht : t ∈ stab u ⊓ stab v)
    (hw : w ∈ Vv V v) (z : D) : t * w * t⁻¹ * w⁻¹ ∈ Theta z V u v :=
  Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator ht hw)

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem isElemAbelian_Vv_B {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    IsElemAbelian 2 (Vv V v) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1]
  exact F7.isElemAbelian_conjSub h.abelian

omit [Finite D] in
theorem stab_le_normalizer_Vv' (v : CosetGeom (A ⊔ B) A B) :
    stab v ≤ Subgroup.normalizer (Vv V v : Set D) :=
  stab_le_normalizer_Vv h.natural.reduced.2.1 v

theorem exists_three_nbrs {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    ∃ u₁ u₂ u₃ : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj v u₁ ∧
      (graph (A ⊔ B) A B).Adj v u₂ ∧ (graph (A ⊔ B) A B).Adj v u₃ ∧ u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧
      u₂ ≠ u₃ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  have hxT : x ∉ A ⊓ B := h.gold.vertex_right.not_mem_of_orderOf hx3
  have hx2T : x * x ∉ A ⊓ B := h.gold.vertex_right.sq_not_mem_of_orderOf hx3
  have hxB' : x ∈ A ⊔ B := (le_sup_right : B ≤ A ⊔ B) hxB
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hxxB' : x * x ∈ A ⊔ B := (le_sup_right : B ≤ A ⊔ B) hxxB
  have hadj : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) :=
    (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm
  have hk1 : (⟨x, hxB'⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B :=
    smul_γ₁_of_mem le_sup_right hxB
  have hk2 : (⟨x * x, hxxB'⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B :=
    smul_γ₁_of_mem le_sup_right hxxB
  have hn1 : (⟨x, hxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B ≠ γ₀ (A ⊔ B) A B := fun e => by
    have := mem_stab_of_smul_eq e
    rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
    exact hxT ⟨this, hxB⟩
  have hn2 : (⟨x * x, hxxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B ≠ γ₀ (A ⊔ B) A B := fun e => by
    have := mem_stab_of_smul_eq e
    rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
    exact hx2T ⟨this, hxxB⟩
  have hn12 : (⟨x, hxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B ≠
      (⟨x * x, hxxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B := fun e => by
    have e' : (⟨x * x, hxxB'⟩ : ↥(A ⊔ B)) = (⟨x, hxB'⟩ : ↥(A ⊔ B)) * ⟨x, hxB'⟩ := rfl
    rw [e', mul_smul] at e
    exact hn1 (smul_left_cancel _ e).symm
  refine ⟨g • γ₀ (A ⊔ B) A B, g • (⟨x, hxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B,
    g • (⟨x * x, hxxB'⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B, (smul_adj g).mpr hadj, ?_, ?_,
    fun e => hn1 (smul_left_cancel g e).symm, fun e => hn2 (smul_left_cancel g e).symm,
    fun e => hn12 (smul_left_cancel g e)⟩
  · have := (smul_adj (⟨x, hxB'⟩ : ↥(A ⊔ B))).mpr hadj
    rw [hk1] at this
    exact (smul_adj g).mpr this
  · have := (smul_adj (⟨x * x, hxxB'⟩ : ↥(A ⊔ B))).mpr hadj
    rw [hk2] at this
    exact (smul_adj g).mpr this

theorem Vv_le_sup_zpowers {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) {a : D} (ha : a ∈ Vv V u) (ha' : a ∉ Zv z v) :
    Vv V u ≤ Zv z v ⊔ Subgroup.zpowers a := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  have hZ : Zv z v ≤ Vv V u := h.Zv_le_Vv huv hu
  have hS : Zv z v ⊔ Subgroup.zpowers a ≤ Vv V u := sup_le hZ (Subgroup.zpowers_le.mpr ha)
  have hd1 : 2 ∣ Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Zv z v ≤ Zv z v ⊔ Subgroup.zpowers a)
    rwa [h.card_Zv hv] at this
  have hd2 : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) ∣ 4 := by
    have := Subgroup.card_dvd_of_le hS
    rwa [h.card_Vv_A hu] at this
  have hne : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) ≠ 2 := fun e => by
    have heq : Zv z v = Zv z v ⊔ Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [e, h.card_Zv hv])
    exact ha' (heq ▸ (le_sup_right : Subgroup.zpowers a ≤ Zv z v ⊔ Subgroup.zpowers a)
      (Subgroup.mem_zpowers a))
  have hle4 := Nat.le_of_dvd (by norm_num) hd2
  have hpos : 0 < Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) := Nat.card_pos
  have h4 : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) = 4 := by
    obtain ⟨k, hk⟩ := hd1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [h4, h.card_Vv_A hu])).ge

omit [Finite D] in
theorem mul_inv_mem_Zv_of_mem_Vv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) {a y : D} (ha : a ∈ Vv V u) (ha' : a ∉ Zv z v)
    (hy : y ∈ Vv V u) (hy' : y ∉ Zv z v) : y * a⁻¹ ∈ Zv z v := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  have e := Subgroup.relIndex_mul_card (Zv z v) (Vv V u)
  rw [inf_eq_left.mpr (h.Zv_le_Vv huv hu), h.card_Zv hv, h.card_Vv_A hu] at e
  have hidx : (Zv z v).relIndex (Vv V u) = 2 := by omega
  exact mul_inv_mem_of_relIndex_eq_two hidx hy ha hy' ha'

theorem exists_mem_Vv_not_mem_Zv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) : ∃ a ∈ Vv V u, a ∉ Zv z v := by
  by_contra hcon
  push Not at hcon
  have hle : Vv V u ≤ Zv z v := fun a ha => hcon a ha
  have := Subgroup.card_le_of_le hle
  rw [h.card_Vv_A hu, h.card_Zv (vtype_eq_true_of_adj huv hu)] at this
  omega

theorem exists_frame {u v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (huv : (graph (A ⊔ B) A B).Adj v u) :
    ∃ u₂ u₃ : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj v u₂ ∧
      (graph (A ⊔ B) A B).Adj v u₃ ∧ u ≠ u₂ ∧ u ≠ u₃ ∧ u₂ ≠ u₃ := by
  obtain ⟨w₁, w₂, w₃, a₁, a₂, a₃, h12, h13, h23⟩ := h.exists_three_nbrs hv
  rcases h.eq_or_eq_of_adj a₁ a₂ a₃ huv h12 h13 h23 with e | e | e
  · subst e
    exact ⟨w₂, w₃, a₂, a₃, h12, h13, h23⟩
  · subst e
    exact ⟨w₁, w₃, a₁, a₃, h12.symm, h23, h13⟩
  · subst e
    exact ⟨w₁, w₂, a₁, a₂, h13.symm, h23.symm, h12⟩

theorem exists_frame_elems {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) :
    ∃ (u₂ u₃ : CosetGeom (A ⊔ B) A B) (a₂ a₃ : D), (graph (A ⊔ B) A B).Adj v u₂ ∧
      (graph (A ⊔ B) A B).Adj v u₃ ∧ u ≠ u₂ ∧ u ≠ u₃ ∧ u₂ ≠ u₃ ∧ a₂ ∈ Vv V u₂ ∧ a₂ ∉ Zv z v ∧
      a₃ ∈ Vv V u₃ ∧ a₃ ∉ Zv z v := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  obtain ⟨u₂, u₃, h₂, h₃, h12, h13, h23⟩ := h.exists_frame hv huv.symm
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  obtain ⟨a₂, ha₂, ha₂'⟩ := h.exists_mem_Vv_not_mem_Zv (u := u₂) (v := v) hu₂ h₂.symm
  obtain ⟨a₃, ha₃, ha₃'⟩ := h.exists_mem_Vv_not_mem_Zv (u := u₃) (v := v) hu₃ h₃.symm
  exact ⟨u₂, u₃, a₂, a₃, h₂, h₃, h12, h13, h23, ha₂, ha₂', ha₃, ha₃'⟩

theorem comm_mem_sup_zpowers {u₁ u₂ u₃ v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (h₁ : (graph (A ⊔ B) A B).Adj v u₁) (h₂ : (graph (A ⊔ B) A B).Adj v u₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v u₃) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    {a₂ a₃ : D} (ha₂ : a₂ ∈ Vv V u₂) (ha₂' : a₂ ∉ Zv z v) (ha₃ : a₃ ∈ Vv V u₃)
    (ha₃' : a₃ ∉ Zv z v) {t : D} (ht : t ∈ stab u₁ ⊓ stab v) {w : D} (hw : w ∈ Vv V v) :
    t * w * t⁻¹ * w⁻¹ ∈ Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) := by
  have hu₁ : vtype u₁ = false := vtype_eq_false_of_adj h₁ hv
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  have hU := h.isElemAbelian_Vv_B (V := V) hv
  have hUn : t ∈ Subgroup.normalizer (Vv V v : Set D) := h.stab_le_normalizer_Vv' v ht.2
  have hZ1 : Zv z v ≤ Vv V u₁ := h.Zv_le_Vv h₁.symm hu₁
  have hZU : Zv z v ≤ Vv V v := hZ1.trans (Vv_le_Vv_of_adj h₁.symm hu₁)
  have ha₂U : a₂ ∈ Vv V v := Vv_le_Vv_of_adj h₂.symm hu₂ ha₂
  have ha₃U : a₃ ∈ Vv V v := Vv_le_Vv_of_adj h₃.symm hu₃ ha₃
  have hΘU : Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) ≤ Vv V v :=
    sup_le hZU (Subgroup.zpowers_le.mpr ((Vv V v).mul_mem ha₂U ha₃U))
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hU.2 a₂ ha₂U
  have ha₃sq : a₃ * a₃ = 1 := by rw [← pow_two]; exact hU.2 a₃ ha₃U
  have hcomm : a₂ * a₃ = a₃ * a₂ := isElemAbelian_comm hU ha₂U ha₃U
  have hG : t ∈ A ⊔ B := stab_le _ ht.1
  have key : ∀ (ua ub : CosetGeom (A ⊔ B) A B) (a b : D), (graph (A ⊔ B) A B).Adj v ua →
      (graph (A ⊔ B) A B).Adj v ub → u₁ ≠ ua → u₁ ≠ ub → ua ≠ ub → a ∈ Vv V ua → a ∉ Zv z v →
      b ∈ Vv V ub → b ∉ Zv z v → a * a = 1 → a * b = b * a →
      t * a * t⁻¹ * a⁻¹ ∈ Zv z v ⊔ Subgroup.zpowers (a * b) := by
    intro ua ub a b hua hub h1a h1b hab ha ha' hb hb' haa habc
    have huat : vtype ua = false := vtype_eq_false_of_adj hua hv
    have hubt : vtype ub = false := vtype_eq_false_of_adj hub hv
    lift t to ↥(A ⊔ B) using hG with g
    have hgv : g • v = v := smul_eq_of_mem_stab ht.2
    have hgu : g • u₁ = u₁ := smul_eq_of_mem_stab ht.1
    have hadj : (graph (A ⊔ B) A B).Adj v (g • ua) := by
      have := (smul_adj g).mpr hua
      rwa [hgv] at this
    have hne1 : u₁ ≠ g • ua := fun e => h1a (by
      have : g • u₁ = g • ua := by rw [hgu]; exact e
      exact smul_left_cancel g this)
    rcases h.eq_or_eq_of_adj h₁ hua hub hadj h1a h1b hab with e | e | e
    · exact absurd e.symm hne1
    · have hts : (g : D) ∈ stab ua ⊓ stab v :=
        ⟨mem_stab_of_smul_eq e, ht.2⟩
      exact Subgroup.mem_sup_left (h.commutator_mem_Zv hua.symm huat hts ha)
    · have hconj : (g : D) * a * (g : D)⁻¹ ∈ Vv V ub := by
        have := (Vv_smul h.natural.reduced.2.1 g ua) ▸ (mul_mem_conjSub (g := (g : D)) ha)
        rw [e] at this
        exact this
      have hnz : (g : D) * a * (g : D)⁻¹ ∉ Zv z v := fun hz => by
        have := h.stab_centralizes_Zv hv ((stab v).inv_mem ht.2) hz
        apply ha'
        have e2 : ((g : D)⁻¹) * ((g : D) * a * (g : D)⁻¹) * ((g : D)⁻¹)⁻¹ = a := by group
        rw [e2] at this
        rw [this]
        exact hz
      have hζ : (g : D) * a * (g : D)⁻¹ * b⁻¹ ∈ Zv z v :=
        h.mul_inv_mem_Zv_of_mem_Vv hubt hub.symm hb hb' hconj hnz
      have e3 : (g : D) * a * (g : D)⁻¹ * a⁻¹ =
          ((g : D) * a * (g : D)⁻¹ * b⁻¹) * (a * b) := by
        have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        have h2 : b * a⁻¹ = a * b := by rw [h1, habc]
        calc (g : D) * a * (g : D)⁻¹ * a⁻¹
            = ((g : D) * a * (g : D)⁻¹ * b⁻¹) * (b * a⁻¹) := by group
          _ = _ := by rw [h2]
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hζ)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have k2 := key u₂ u₃ a₂ a₃ h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃' ha₂sq hcomm
  have k3 := key u₃ u₂ a₃ a₂ h₃ h₂ h13 h12 h23.symm ha₃ ha₃' ha₂ ha₂' ha₃sq hcomm.symm
  rw [← hcomm] at k3
  let X := commPre (Vv V v) (Zv z v ⊔ Subgroup.zpowers (a₂ * a₃)) hU hΘU t hUn
  have hZX : Zv z v ≤ X := fun ζ hζ => by
    refine ⟨hZU hζ, ?_⟩
    have := h.stab_centralizes_Zv hv ht.2 hζ
    rw [this]
    simp
  obtain ⟨a₁, ha₁, ha₁'⟩ := h.exists_mem_Vv_not_mem_Zv (u := u₁) (v := v) hu₁ h₁.symm
  have ha₁X : a₁ ∈ X :=
    ⟨Vv_le_Vv_of_adj h₁.symm hu₁ ha₁,
      Subgroup.mem_sup_left (h.commutator_mem_Zv h₁.symm hu₁ ht ha₁)⟩
  have ha₂X : a₂ ∈ X := ⟨ha₂U, k2⟩
  have ha₃X : a₃ ∈ X := ⟨ha₃U, k3⟩
  have hVX : Vv V v ≤ X := by
    refine (Vv_B_le_iff hv).mpr fun u' hu' => ?_
    rcases h.eq_or_eq_of_adj h₁ h₂ h₃ hu' h12 h13 h23 with e | e | e
    · subst e
      exact (h.Vv_le_sup_zpowers hu₁ h₁.symm ha₁ ha₁').trans
        (sup_le hZX (Subgroup.zpowers_le.mpr ha₁X))
    · subst e
      exact (h.Vv_le_sup_zpowers hu₂ h₂.symm ha₂ ha₂').trans
        (sup_le hZX (Subgroup.zpowers_le.mpr ha₂X))
    · subst e
      exact (h.Vv_le_sup_zpowers hu₃ h₃.symm ha₃ ha₃').trans
        (sup_le hZX (Subgroup.zpowers_le.mpr ha₃X))
  exact (hVX hw).2

omit [Finite D] in
theorem Theta_le_Vv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) : Theta z V u v ≤ Vv V v := by
  refine sup_le ((h.Zv_le_Vv huv hu).trans (Vv_le_Vv_of_adj huv hu)) ?_
  refine Subgroup.commutator_le.mpr fun t ht w hw => ?_
  have h1 : t * w * t⁻¹ ∈ Vv V v := (Subgroup.mem_normalizer_iff.mp
    (h.stab_le_normalizer_Vv' v ht.2) w).mp hw
  show t * w * t⁻¹ * w⁻¹ ∈ Vv V v
  exact (Vv V v).mul_mem h1 ((Vv V v).inv_mem hw)

theorem Theta_le_frame {u₁ u₂ u₃ v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (h₁ : (graph (A ⊔ B) A B).Adj v u₁) (h₂ : (graph (A ⊔ B) A B).Adj v u₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v u₃) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    {a₂ a₃ : D} (ha₂ : a₂ ∈ Vv V u₂) (ha₂' : a₂ ∉ Zv z v) (ha₃ : a₃ ∈ Vv V u₃)
    (ha₃' : a₃ ∉ Zv z v) : Theta z V u₁ v ≤ Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) := by
  refine sup_le le_sup_left (Subgroup.commutator_le.mpr fun t ht w hw => ?_)
  show t * w * t⁻¹ * w⁻¹ ∈ Zv z v ⊔ Subgroup.zpowers (a₂ * a₃)
  exact h.comm_mem_sup_zpowers hv h₁ h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃' ht hw

theorem card_frame_le_four {u₁ u₂ u₃ v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (h₁ : (graph (A ⊔ B) A B).Adj v u₁) (h₂ : (graph (A ⊔ B) A B).Adj v u₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v u₃) {a₂ a₃ : D} (ha₂ : a₂ ∈ Vv V u₂) (ha₃ : a₃ ∈ Vv V u₃) :
    Nat.card ↥(Zv z v ⊔ Subgroup.zpowers (a₂ * a₃)) ≤ 4 := by
  have hu₁ : vtype u₁ = false := vtype_eq_false_of_adj h₁ hv
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  have hU := h.isElemAbelian_Vv_B (V := V) hv
  have ha₂U : a₂ ∈ Vv V v := Vv_le_Vv_of_adj h₂.symm hu₂ ha₂
  have ha₃U : a₃ ∈ Vv V v := Vv_le_Vv_of_adj h₃.symm hu₃ ha₃
  have hZU : Zv z v ≤ Vv V v := (h.Zv_le_Vv h₁.symm hu₁).trans (Vv_le_Vv_of_adj h₁.symm hu₁)
  have hcomm : a₂ * a₃ = a₃ * a₂ := isElemAbelian_comm hU ha₂U ha₃U
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hU.2 a₂ ha₂U
  have ha₃sq : a₃ * a₃ = 1 := by rw [← pow_two]; exact hU.2 a₃ ha₃U
  have hn2 : (a₂ * a₃) ^ 2 = 1 := by
    have : (a₂ * a₃) * (a₂ * a₃) = 1 := by
      calc (a₂ * a₃) * (a₂ * a₃) = a₂ * (a₃ * a₂) * a₃ := by group
        _ = a₂ * (a₂ * a₃) * a₃ := by rw [hcomm]
        _ = (a₂ * a₂) * (a₃ * a₃) := by group
        _ = 1 := by rw [ha₂sq, ha₃sq]; simp
    rwa [← pow_two] at this
  have hnorm : Zv z v ≤ Subgroup.normalizer (Subgroup.zpowers (a₂ * a₃) : Set D) := by
    intro ζ hζ
    exact mem_normalizer_zpowers_of_mul_comm
      (isElemAbelian_comm hU (hZU hζ) ((Vv V v).mul_mem ha₂U ha₃U))
  have c1 := GoldAmN.card_sup_le_of_le_normalizer (Zv z v) (Subgroup.zpowers (a₂ * a₃)) hnorm
  rw [h.card_Zv hv] at c1
  have c2 := card_zpowers_le_two hn2
  calc Nat.card ↥(Zv z v ⊔ Subgroup.zpowers (a₂ * a₃))
      ≤ 2 * Nat.card (Subgroup.zpowers (a₂ * a₃)) := c1
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 c2

theorem card_Theta_le_four {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) : Nat.card (Theta z V u v) ≤ 4 := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  obtain ⟨u₂, u₃, a₂, a₃, h₂, h₃, h12, h13, h23, ha₂, ha₂', ha₃, ha₃'⟩ :=
    h.exists_frame_elems hu huv
  have hle := h.Theta_le_frame hv huv.symm h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃'
  exact (Subgroup.card_le_of_le hle).trans (h.card_frame_le_four hv huv.symm h₂ h₃ ha₂ ha₃)

omit [Finite D] in
theorem conj_mul_inv_mem_Zv {v ua ub : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (hub : (graph (A ⊔ B) A B).Adj v ub) {a b : D}
    (ha : a ∈ Vv V ua) (ha' : a ∉ Zv z v) (hb : b ∈ Vv V ub) (hb' : b ∉ Zv z v)
    (g : ↥(A ⊔ B)) (hgv : (g : D) ∈ stab v) (hgu : g • ua = ub) :
    (g : D) * a * (g : D)⁻¹ * b⁻¹ ∈ Zv z v := by
  have hubt : vtype ub = false := vtype_eq_false_of_adj hub hv
  have hconj : (g : D) * a * (g : D)⁻¹ ∈ Vv V ub := by
    have := (Vv_smul h.natural.reduced.2.1 g ua) ▸ (mul_mem_conjSub (g := (g : D)) ha)
    rw [hgu] at this
    exact this
  have hnz : (g : D) * a * (g : D)⁻¹ ∉ Zv z v := fun hz => by
    have := h.stab_centralizes_Zv hv ((stab v).inv_mem hgv) hz
    apply ha'
    have e2 : ((g : D)⁻¹) * ((g : D) * a * (g : D)⁻¹) * ((g : D)⁻¹)⁻¹ = a := by group
    rw [e2] at this
    rw [this]
    exact hz
  exact h.mul_inv_mem_Zv_of_mem_Vv hubt hub.symm hb hb' hconj hnz

theorem comm_mul_mem_Zv {u₁ u₂ u₃ v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (h₁ : (graph (A ⊔ B) A B).Adj v u₁) (h₂ : (graph (A ⊔ B) A B).Adj v u₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v u₃) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    {a₂ a₃ : D} (ha₂ : a₂ ∈ Vv V u₂) (ha₂' : a₂ ∉ Zv z v) (ha₃ : a₃ ∈ Vv V u₃)
    (ha₃' : a₃ ∉ Zv z v) {t : D} (ht : t ∈ stab u₁ ⊓ stab v) :
    t * (a₂ * a₃) * t⁻¹ * (a₂ * a₃)⁻¹ ∈ Zv z v := by
  have hu₁ : vtype u₁ = false := vtype_eq_false_of_adj h₁ hv
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  have hU := h.isElemAbelian_Vv_B (V := V) hv
  have hUn : t ∈ Subgroup.normalizer (Vv V v : Set D) := h.stab_le_normalizer_Vv' v ht.2
  have hZ1 : Zv z v ≤ Vv V u₁ := h.Zv_le_Vv h₁.symm hu₁
  have hZU : Zv z v ≤ Vv V v := hZ1.trans (Vv_le_Vv_of_adj h₁.symm hu₁)
  have ha₂U : a₂ ∈ Vv V v := Vv_le_Vv_of_adj h₂.symm hu₂ ha₂
  have ha₃U : a₃ ∈ Vv V v := Vv_le_Vv_of_adj h₃.symm hu₃ ha₃
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hU.2 a₂ ha₂U
  have ha₃sq : a₃ * a₃ = 1 := by rw [← pow_two]; exact hU.2 a₃ ha₃U
  have hcomm : a₂ * a₃ = a₃ * a₂ := isElemAbelian_comm hU ha₂U ha₃U
  have hG : t ∈ A ⊔ B := stab_le _ ht.1
  have hgen : ∀ (ua : CosetGeom (A ⊔ B) A B), (graph (A ⊔ B) A B).Adj v ua → u₁ ≠ ua →
      ua ≠ u₂ → ua ≠ u₃ → False := fun ua hua h1 h2 h3 => by
    rcases h.eq_or_eq_of_adj h₁ h₂ h₃ hua h12 h13 h23 with e | e | e
    · exact h1 e.symm
    · exact h2 e
    · exact h3 e
  lift t to ↥(A ⊔ B) using hG with g
  have hgv : g • v = v := smul_eq_of_mem_stab ht.2
  have hgu : g • u₁ = u₁ := smul_eq_of_mem_stab ht.1
  have hadj : ∀ ua, (graph (A ⊔ B) A B).Adj v ua → (graph (A ⊔ B) A B).Adj v (g • ua) :=
    fun ua hua => by
      have := (smul_adj g).mpr hua
      rwa [hgv] at this
  have hne1 : ∀ ua, u₁ ≠ ua → u₁ ≠ g • ua := fun ua h1 e => h1 (by
    have : g • u₁ = g • ua := by rw [hgu]; exact e
    exact smul_left_cancel g this)
  have hcls : ∀ ua, (graph (A ⊔ B) A B).Adj v ua → u₁ ≠ ua → (g • ua = u₂ ∨ g • ua = u₃) :=
    fun ua hua h1 => by
      rcases h.eq_or_eq_of_adj h₁ h₂ h₃ (hadj ua hua) h12 h13 h23 with e | e | e
      · exact absurd e.symm (hne1 ua h1)
      · exact Or.inl e
      · exact Or.inr e
  rcases hcls u₂ h₂ h12 with e2 | e2
  ·
    have e3 : g • u₃ = u₃ := by
      rcases hcls u₃ h₃ h13 with e | e
      · exact absurd (smul_left_cancel g (e.trans e2.symm)).symm h23
      · exact e
    let Y := commPre (Vv V v) (Zv z v) hU hZU (g : D) hUn
    have ha₂Y : a₂ ∈ Y := ⟨ha₂U, h.commutator_mem_Zv h₂.symm hu₂
      ⟨mem_stab_of_smul_eq e2, ht.2⟩ ha₂⟩
    have ha₃Y : a₃ ∈ Y := ⟨ha₃U, h.commutator_mem_Zv h₃.symm hu₃
      ⟨mem_stab_of_smul_eq e3, ht.2⟩ ha₃⟩
    exact (Y.mul_mem ha₂Y ha₃Y).2
  ·
    have e3 : g • u₃ = u₂ := by
      rcases hcls u₃ h₃ h13 with e | e
      · exact e
      · exact absurd (smul_left_cancel g (e.trans e2.symm)).symm h23
    have hζ₂ := h.conj_mul_inv_mem_Zv hv h₃ ha₂ ha₂' ha₃ ha₃' g ht.2 e2
    have hζ₃ := h.conj_mul_inv_mem_Zv hv h₂ ha₃ ha₃' ha₂ ha₂' g ht.2 e3
    set ζ₂ := (g : D) * a₂ * (g : D)⁻¹ * a₃⁻¹ with hζ₂def
    set ζ₃ := (g : D) * a₃ * (g : D)⁻¹ * a₂⁻¹ with hζ₃def
    have hq₂ : (g : D) * a₂ * (g : D)⁻¹ = ζ₂ * a₃ := by rw [hζ₂def]; group
    have hq₃ : (g : D) * a₃ * (g : D)⁻¹ = ζ₃ * a₂ := by rw [hζ₃def]; group
    have hζ₃U : ζ₃ ∈ Vv V v := hZU hζ₃
    have hcz : a₃ * ζ₃ = ζ₃ * a₃ := isElemAbelian_comm hU ha₃U hζ₃U
    have hinv : (a₂ * a₃)⁻¹ = a₃ * a₂ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha₃sq, inv_eq_of_mul_eq_one_right ha₂sq]
    have e1 : (g : D) * (a₂ * a₃) * (g : D)⁻¹ * (a₂ * a₃)⁻¹ =
        (ζ₂ * ζ₃) * (a₃ * (a₂ * a₃ * a₂)) := by
      have h0 : (g : D) * (a₂ * a₃) * (g : D)⁻¹ =
          ((g : D) * a₂ * (g : D)⁻¹) * ((g : D) * a₃ * (g : D)⁻¹) := by group
      rw [hinv, h0, hq₂, hq₃]
      calc ζ₂ * a₃ * (ζ₃ * a₂) * (a₃ * a₂) = ζ₂ * (a₃ * ζ₃) * (a₂ * (a₃ * a₂)) := by group
        _ = ζ₂ * (ζ₃ * a₃) * (a₂ * (a₃ * a₂)) := by rw [hcz]
        _ = (ζ₂ * ζ₃) * (a₃ * (a₂ * a₃ * a₂)) := by
          have : a₂ * (a₃ * a₂) = a₂ * a₃ * a₂ := by group
          rw [this]; group
    have e4 : a₂ * a₃ * a₂ = a₃ := by
      rw [hcomm]
      calc a₃ * a₂ * a₂ = a₃ * (a₂ * a₂) := by group
        _ = a₃ := by rw [ha₂sq]; simp
    rw [e1, e4, ha₃sq, mul_one]
    exact (Zv z v).mul_mem hζ₂ hζ₃

theorem comm_Theta_le_Zv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) {t f : D} (ht : t ∈ stab u ⊓ stab v)
    (hf : f ∈ Theta z V u v) : t * f * t⁻¹ * f⁻¹ ∈ Zv z v := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  obtain ⟨u₂, u₃, a₂, a₃, h₂, h₃, h12, h13, h23, ha₂, ha₂', ha₃, ha₃'⟩ :=
    h.exists_frame_elems hu huv
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  have hU := h.isElemAbelian_Vv_B (V := V) hv
  have hUn : t ∈ Subgroup.normalizer (Vv V v : Set D) := h.stab_le_normalizer_Vv' v ht.2
  have hZU : Zv z v ≤ Vv V v := (h.Zv_le_Vv huv hu).trans (Vv_le_Vv_of_adj huv hu)
  let Y := commPre (Vv V v) (Zv z v) hU hZU t hUn
  have hZY : Zv z v ≤ Y := fun ζ hζ => by
    refine ⟨hZU hζ, ?_⟩
    have := h.stab_centralizes_Zv hv ht.2 hζ
    rw [this]
    simp
  have hnY : a₂ * a₃ ∈ Y := ⟨(Vv V v).mul_mem (Vv_le_Vv_of_adj h₂.symm hu₂ ha₂)
    (Vv_le_Vv_of_adj h₃.symm hu₃ ha₃), h.comm_mul_mem_Zv hv huv.symm h₂ h₃ h12 h13 h23 ha₂ ha₂'
      ha₃ ha₃' ht⟩
  have hle := h.Theta_le_frame hv huv.symm h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃'
  have hY : Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) ≤ Y := sup_le hZY (Subgroup.zpowers_le.mpr hnY)
  exact (hY (hle hf)).2

theorem mul_not_mem_Vv_frame {u₁ u₂ u₃ v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true)
    (h₁ : (graph (A ⊔ B) A B).Adj v u₁) (h₂ : (graph (A ⊔ B) A B).Adj v u₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v u₃) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    {a₂ a₃ : D} (ha₂ : a₂ ∈ Vv V u₂) (ha₂' : a₂ ∉ Zv z v) (ha₃ : a₃ ∈ Vv V u₃)
    (ha₃' : a₃ ∉ Zv z v) (hU16 : Nat.card (Vv V v) = 16) : a₂ * a₃ ∉ Vv V u₁ := by
  intro hn
  have hu₁ : vtype u₁ = false := vtype_eq_false_of_adj h₁ hv
  have hu₂ : vtype u₂ = false := vtype_eq_false_of_adj h₂ hv
  have hu₃ : vtype u₃ = false := vtype_eq_false_of_adj h₃ hv
  have hU := h.isElemAbelian_Vv_B (V := V) hv
  have ha₂U : a₂ ∈ Vv V v := Vv_le_Vv_of_adj h₂.symm hu₂ ha₂
  have hZ1 : Zv z v ≤ Vv V u₁ := h.Zv_le_Vv h₁.symm hu₁
  have hV1U : Vv V u₁ ≤ Vv V v := Vv_le_Vv_of_adj h₁.symm hu₁
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hU.2 a₂ ha₂U
  set S := Vv V u₁ ⊔ Subgroup.zpowers a₂ with hS
  have ha₂S : a₂ ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers a₂)
  have ha₃S : a₃ ∈ S := by
    have e : a₃ = a₂⁻¹ * (a₂ * a₃) := by group
    rw [e]
    exact S.mul_mem (S.inv_mem ha₂S) (Subgroup.mem_sup_left hn)
  have hZS : Zv z v ≤ S := hZ1.trans le_sup_left
  have hle : Vv V v ≤ S := by
    refine (Vv_B_le_iff hv).mpr fun u' hu' => ?_
    rcases h.eq_or_eq_of_adj h₁ h₂ h₃ hu' h12 h13 h23 with e | e | e
    · subst e
      exact le_sup_left
    · subst e
      exact (h.Vv_le_sup_zpowers hu₂ h₂.symm ha₂ ha₂').trans
        (sup_le hZS (Subgroup.zpowers_le.mpr ha₂S))
    · subst e
      exact (h.Vv_le_sup_zpowers hu₃ h₃.symm ha₃ ha₃').trans
        (sup_le hZS (Subgroup.zpowers_le.mpr ha₃S))
  have hnorm : Vv V u₁ ≤ Subgroup.normalizer (Subgroup.zpowers a₂ : Set D) := fun y hy =>
    mem_normalizer_zpowers_of_mul_comm (isElemAbelian_comm hU (hV1U hy) ha₂U)
  have c1 : Nat.card ↥S ≤ Nat.card ↥(Vv V u₁) * Nat.card ↥(Subgroup.zpowers a₂) :=
    GoldAmN.card_sup_le_of_le_normalizer (Vv V u₁) (Subgroup.zpowers a₂) hnorm
  rw [h.card_Vv_A hu₁] at c1
  have c2 := card_zpowers_le_two (w := a₂) (by rw [pow_two]; exact ha₂sq)
  have c3 := Subgroup.card_le_of_le hle
  rw [hU16] at c3
  have : 4 * Nat.card (Subgroup.zpowers a₂) ≤ 4 * 2 := Nat.mul_le_mul_left 4 c2
  omega

theorem Theta_inf_Vv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) (hU16 : Nat.card (Vv V v) = 16) :
    Theta z V u v ⊓ Vv V u = Zv z v := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  obtain ⟨u₂, u₃, a₂, a₃, h₂, h₃, h12, h13, h23, ha₂, ha₂', ha₃, ha₃'⟩ :=
    h.exists_frame_elems hu huv
  have hZle : Zv z v ≤ Theta z V u v ⊓ Vv V u := le_inf le_sup_left (h.Zv_le_Vv huv hu)
  refine le_antisymm ?_ hZle
  have hle := h.Theta_le_frame hv huv.symm h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃'
  have hn := h.mul_not_mem_Vv_frame hv huv.symm h₂ h₃ h12 h13 h23 ha₂ ha₂' ha₃ ha₃' hU16
  have hc0 := h.card_frame_le_four hv huv.symm h₂ h₃ ha₂ ha₃
  have hd1 : 2 ∣ Nat.card ↥(Theta z V u v ⊓ Vv V u) := by
    have := Subgroup.card_dvd_of_le hZle
    rwa [h.card_Zv hv] at this
  have hd2 : Nat.card ↥(Theta z V u v ⊓ Vv V u) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : Theta z V u v ⊓ Vv V u ≤ Vv V u)
    rwa [h.card_Vv_A hu] at this
  have hle4 := Nat.le_of_dvd (by norm_num) hd2
  have hpos : 0 < Nat.card ↥(Theta z V u v ⊓ Vv V u) := Nat.card_pos
  by_cases h2 : Nat.card ↥(Theta z V u v ⊓ Vv V u) = 2
  · have heq : Zv z v = Theta z V u v ⊓ Vv V u :=
      Subgroup.eq_of_le_of_card_ge hZle (by rw [h2, h.card_Zv hv])
    exact heq.ge
  · exfalso
    have h4 : Nat.card ↥(Theta z V u v ⊓ Vv V u) = 4 := by
      obtain ⟨k, hk⟩ := hd1
      omega
    have hVu : Theta z V u v ⊓ Vv V u = Vv V u :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h4, h.card_Vv_A hu])
    have hV1 : Vv V u ≤ Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) :=
      (hVu ▸ (inf_le_left : Theta z V u v ⊓ Vv V u ≤ Theta z V u v)).trans hle
    have hEq : Vv V u = Zv z v ⊔ Subgroup.zpowers (a₂ * a₃) :=
      Subgroup.eq_of_le_of_card_ge hV1 (by rw [h.card_Vv_A hu]; exact hc0)
    apply hn
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem exists_swap_edge {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) : ∃ t ∈ stab u ⊓ stab v, t ∉ ballStab 1 v := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  obtain ⟨t₀, ht₀, ht₀Q⟩ := h.exists_mem_inf_not_mem_pCoreOf_right
  refine ⟨(g : D) * t₀ * (g : D)⁻¹, ?_, ?_⟩
  · rw [stab_smul, stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B),
      stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf]
    exact mul_mem_conjSub ht₀
  · rw [ballStab_smul, h.ballStab_one_γ₁_eq, mem_conjSub]
    intro hmem
    apply ht₀Q
    have e : (g : D)⁻¹ * ((g : D) * t₀ * (g : D)⁻¹) * (g : D) = t₀ := by group
    rwa [e] at hmem

theorem card_Theta {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) (hU16 : Nat.card (Vv V v) = 16) :
    Nat.card (Theta z V u v) = 4 := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  have hle4 := h.card_Theta_le_four hu huv
  have hZle : Zv z v ≤ Theta z V u v := le_sup_left
  have hd1 : 2 ∣ Nat.card (Theta z V u v) := by
    have := Subgroup.card_dvd_of_le hZle
    rwa [h.card_Zv hv] at this
  have hd2 : Nat.card (Theta z V u v) ∣ 16 := by
    have := Subgroup.card_dvd_of_le (h.Theta_le_Vv hu huv)
    rwa [hU16] at this
  have hne : Nat.card (Theta z V u v) ≠ 2 := fun e => by
    have heq : Zv z v = Theta z V u v :=
      Subgroup.eq_of_le_of_card_ge hZle (by rw [e, h.card_Zv hv])
    obtain ⟨t, ht, htQ⟩ := h.exists_swap_edge hu huv
    apply htQ
    refine h.mem_ballStab_one_of_commutator hv ht.2 fun w hw => ?_
    rw [heq]
    exact comm_mem_Theta ht hw z
  have hpos : 0 < Nat.card (Theta z V u v) := Nat.card_pos
  obtain ⟨k, hk⟩ := hd1
  omega

omit [Finite D] in
theorem Theta_smul (g : ↥(A ⊔ B)) (u v : CosetGeom (A ⊔ B) A B) :
    Theta z V (g • u) (g • v) = conjSub (g : D) (Theta z V u v) := by
  unfold Theta
  rw [Zv_smul h.normalizes_zpowers g v, Vv_smul h.natural.reduced.2.1 g v, stab_smul, stab_smul,
    conjSub_sup, ← conjSub_inf, conjSub_commutator_sub]

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
