module

public import CFSG.Quasithin.H13.A6S13829b
public import CFSG.Quasithin.H13.A6S13227

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

theorem indep3_of_pl {a b c : Fin 4 → ZMod 2} (hb : pl a b ≠ 0) (hc : pl a c ≠ 0)
    (hbc : pl a b ≠ pl a c) {s₀ s₁ s₂ : ZMod 2} (h : s₀ • a + s₁ • b + s₂ • c = 0) :
    s₀ = 0 ∧ s₁ = 0 ∧ s₂ = 0 := by
  have ha : a ≠ 0 := ((pl_ne_zero_iff a b).1 hb).1
  have h2 : s₂ = 0 := by
    rcases zmodTwo_cases s₂ with h' | h'
    · exact h'
    exfalso
    rw [h', one_smul] at h
    have hc' : c = s₀ • a + s₁ • b := (eq_of_add_eq_zero_vec4 h).symm
    have : pl a c = s₁ • pl a b := by
      rw [hc', pl_add_right]
      rcases zmodTwo_cases s₀ with h0 | h0 <;> rcases zmodTwo_cases s₁ with h1 | h1 <;>
        simp [h0, h1, pl_self, pl_zero_right]
    rcases zmodTwo_cases s₁ with h1 | h1
    · rw [h1, zero_smul] at this
      exact hc this
    · rw [h1, one_smul] at this
      exact hbc this.symm
  rw [h2, zero_smul, add_zero] at h
  have h1 : s₁ = 0 := by
    rcases zmodTwo_cases s₁ with h' | h'
    · exact h'
    exfalso
    rw [h', one_smul] at h
    have hb' : b = s₀ • a := (eq_of_add_eq_zero_vec4 h).symm
    apply hb
    rw [hb']
    rcases zmodTwo_cases s₀ with h0 | h0 <;> simp [h0, pl_self, pl_zero_right]
  rw [h1, zero_smul, add_zero] at h
  refine ⟨?_, h1, h2⟩
  rcases zmodTwo_cases s₀ with h' | h'
  · exact h'
  · rw [h', one_smul] at h
    exact absurd h ha

theorem add_mem_of_pl_eq {a x x' : Fin 4 → ZMod 2} (ha : a ≠ 0) (h : pl a x = pl a x') :
    x + x' = 0 ∨ x + x' = a := by
  have h1 : pl a (x + x') = 0 := by rw [pl_add_right, h, Setting4.add_self_vec6]
  by_contra hne
  push Not at hne
  exact (pl_ne_zero_iff a (x + x')).2 ⟨ha, hne.1, Ne.symm hne.2⟩ h1

@[expose] def pt3 (b c d : Fin 4 → ZMod 2) (ε : Fin 3 → ZMod 2) : Fin 4 → ZMod 2 :=
  ε 0 • b + ε 1 • c + ε 2 • d

theorem zmod2_eq_of_add_eq_zero : ∀ s t : ZMod 2, s + t = 0 → s = t := by
  decide

theorem pt3_add (b c d : Fin 4 → ZMod 2) (ε ε' : Fin 3 → ZMod 2) :
    pt3 b c d ε + pt3 b c d ε' = pt3 b c d (ε + ε') := by
  simp only [pt3, Pi.add_apply, add_smul]
  abel

theorem pl_pt3_injective {a b c d : Fin 4 → ZMod 2}
    (h : ∀ x : Fin 4 → ZMod 2, x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0)
    {ε ε' : Fin 3 → ZMod 2} (heq : pl a (pt3 b c d ε) = pl a (pt3 b c d ε')) : ε = ε' := by
  have ha : a ≠ 0 := by
    intro h0
    have := congrFun (h ![1, 0, 0, 0] (by simp [h0])) 0
    exact absurd this (by decide)
  have key : ∀ s : ZMod 2, s • a + pt3 b c d (ε + ε') = 0 → ε = ε' := by
    intro s hs
    have h1 := h ![s, (ε + ε') 0, (ε + ε') 1, (ε + ε') 2] (by
      rw [← hs]
      simp only [pt3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      abel)
    funext i
    have hi := congrFun h1 i.succ
    fin_cases i <;> simp at hi <;> exact zmod2_eq_of_add_eq_zero _ _ hi
  rcases add_mem_of_pl_eq ha heq with h1 | h1
  · refine key 0 ?_
    rw [zero_smul, zero_add, ← pt3_add, h1]
  · refine key 1 ?_
    rw [one_smul, ← pt3_add, h1, add_self_vec4]

theorem false_of_classes {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {n : ℕ}
    (hidx : B.relIndex A ≤ n) (x : Fin (n + 1) → G) (hx : ∀ i, x i ∈ A)
    (hdist : ∀ i j, i ≠ j → (x i)⁻¹ * x j ∉ B) : False := by
  let f : Fin (n + 1) → ↥A ⧸ B.subgroupOf A := fun i => QuotientGroup.mk ⟨x i, hx i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply hdist i j hne
    have := QuotientGroup.eq.mp hij
    simpa [Subgroup.mem_subgroupOf] using this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : Nat.card (↥A ⧸ B.subgroupOf A) = B.relIndex A := rfl
  omega

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem z_comm_of_mem_G1 {k : G} (hk : k ∈ S.G1) : k * S.z = S.z * k :=
  Subgroup.mem_centralizer_singleton_iff.mp hk

theorem mem_V2_cases {v : G} (hv : v ∈ S.V2) :
    v = 1 ∨ v = S.z ∨ v = S.u1 ∨ v = S.z * S.u1 := by
  obtain ⟨hV, hW⟩ := S.mem_pre.1 hv
  have hW' : InW2 (S.frame.ψ ⟨v, hV⟩ : P6) := hW
  have inj : ∀ (w : G) (hw : w ∈ V),
      (S.frame.ψ ⟨v, hV⟩ : P6) = (S.frame.ψ ⟨w, hw⟩ : P6) → v = w := fun w hw h =>
    congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hz : (S.frame.ψ ⟨S.z, S.z_mem_V⟩ : P6) = e0123 := by rw [S.psi_z]
  rcases hW' with h | h | h | h
  · left
    refine inj 1 V.one_mem ?_
    rw [h, show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one]
    rfl
  · right; right; left
    exact inj S.u1 S.u1_mem_V (by rw [h, S.psi_u1])
  · right; right; right
    refine inj (S.z * S.u1) (V.mul_mem S.z_mem_V S.u1_mem_V) ?_
    have e : (⟨S.z * S.u1, V.mul_mem S.z_mem_V S.u1_mem_V⟩ : ↥V) =
        ⟨S.z, S.z_mem_V⟩ * ⟨S.u1, S.u1_mem_V⟩ := rfl
    rw [h, e, map_mul, Subgroup.coe_mul, hz, S.psi_u1]
    decide
  · right; left
    exact inj S.z S.z_mem_V (by rw [h, hz])

theorem mem_C2_of {k : G} (hk : k ∈ S.G1) (hku : k * S.u1 = S.u1 * k) :
    k ∈ Subgroup.centralizer (S.V2 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hz := S.z_comm_of_mem_G1 hk
  rcases S.mem_V2_cases hv with rfl | rfl | rfl | rfl
  · simp
  · exact hz.symm
  · exact hku.symm
  · calc S.z * S.u1 * k = S.z * (S.u1 * k) := by group
      _ = S.z * (k * S.u1) := by rw [hku]
      _ = k * (S.z * S.u1) := by rw [← mul_assoc, ← hz, mul_assoc]

theorem C2_le_G1 : Subgroup.centralizer (S.V2 : Set G) ≤ S.G1 := fun _ hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hk) S.z (S.V1_le_V2 (S.mem_V1_iff.2 (Or.inr rfl)))).symm

section Lines

variable {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

theorem exists_lift_C2 (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hρs : Function.Surjective ρ)
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
    (hQu1 : ∃ q ∈ pCoreOf 2 S.G1, q * S.u1 * q⁻¹ ≠ S.u1)
    (g' : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (hg' : (g' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (S.w1 β) = S.w1 β) :
    ∃ k : ↥S.G1, ρ k = g' ∧ (k : G) ∈ Subgroup.centralizer (S.V2 : Set G) := by
  obtain ⟨k₀, hk₀⟩ := hρs g'
  have hu1U : S.u1 ∈ conjClosure S.V3 S.G1 := S.V3_le_UH S.u1_mem_V3
  have hcU : (k₀ : G) * S.u1 * (k₀ : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
    mem_conjClosure k₀.2 S.u1_mem_V3
  have hbv : S.bv β ⟨_, hcU⟩ = S.bv β ⟨S.u1, hu1U⟩ := by
    have := hβe k₀ ⟨S.u1, hu1U⟩ ⟨_, hcU⟩ rfl
    change S.bv β _ = _ at this
    rw [this, hk₀]
    exact hg'
  have hmod : (k₀ : G) * S.u1 * (k₀ : G)⁻¹ * S.u1⁻¹ ∈ fsuV1 T V := (S.bv_eq_iff hβk _ _).1 hbv
  rcases S.mem_V1_iff.1 hmod with h | h
  · refine ⟨k₀, hk₀, S.mem_C2_of k₀.2 ?_⟩
    have h1 : (k₀ : G) * S.u1 * (k₀ : G)⁻¹ = S.u1 := mul_inv_eq_one.mp h
    calc (k₀ : G) * S.u1 = (k₀ : G) * S.u1 * (k₀ : G)⁻¹ * k₀ := by group
      _ = S.u1 * k₀ := by rw [h1]
  · obtain ⟨q, hq, hqu⟩ := hQu1
    have hqG : q ∈ S.G1 := pCoreOf_le 2 _ hq
    have hqmod : q * S.u1 * q⁻¹ * S.u1⁻¹ ∈ fsuV1 T V := by
      have h2 := (fsuV1 T V).inv_mem (hF.toHypF91.commutator_conjClosure_le S.u1 hu1U q hq)
      have e : (S.u1 * q * S.u1⁻¹ * q⁻¹)⁻¹ = q * S.u1 * q⁻¹ * S.u1⁻¹ := by group
      rwa [e] at h2
    rcases S.mem_V1_iff.1 hqmod with h' | h'
    · exact absurd (mul_inv_eq_one.mp h') hqu
    · have hA : (k₀ : G) * S.u1 * (k₀ : G)⁻¹ = S.z * S.u1 := by
        rw [← h]
        group
      have hB : q * S.u1 * q⁻¹ = S.z * S.u1 := by
        rw [← h']
        group
      refine ⟨⟨q, hqG⟩⁻¹ * k₀, ?_, S.mem_C2_of (S.G1.mul_mem (S.G1.inv_mem hqG) k₀.2) ?_⟩
      · rw [map_mul, map_inv, (hker ⟨q, hqG⟩).2 hq, inv_one, one_mul, hk₀]
      · show q⁻¹ * k₀ * S.u1 = S.u1 * (q⁻¹ * k₀)
        calc q⁻¹ * k₀ * S.u1 = q⁻¹ * ((k₀ : G) * S.u1 * (k₀ : G)⁻¹) * k₀ := by group
          _ = q⁻¹ * (q * S.u1 * q⁻¹) * k₀ := by rw [hA, hB]
          _ = S.u1 * (q⁻¹ * k₀) := by group

theorem conj_mem_C2 {g k : G} (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hk : k ∈ Subgroup.centralizer (S.V2 : Set G)) :
    g⁻¹ * k * g ∈ Subgroup.centralizer (S.V2 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : g * v * g⁻¹ ∈ S.V2 := (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  have h1 := Subgroup.mem_centralizer_iff.mp hk _ hv'
  calc v * (g⁻¹ * k * g) = g⁻¹ * ((g * v * g⁻¹) * k) * g := by group
    _ = g⁻¹ * (k * (g * v * g⁻¹)) * g := by rw [h1]
    _ = g⁻¹ * k * g * v := by group

theorem conj_mem_U' {g k b : G} (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hk : k ∈ Subgroup.centralizer (S.V2 : Set G)) (hb : b ∈ conjSub g S.V3) :
    k * b * k⁻¹ ∈ conjSub g (conjClosure S.V3 S.G1) := by
  rw [mem_conjSub] at hb ⊢
  have h1 := mem_conjClosure (S.C2_le_G1 (S.conj_mem_C2 hgN hk)) hb
  have e : g⁻¹ * (k * b * k⁻¹) * g =
      (g⁻¹ * k * g) * (g⁻¹ * b * g) * (g⁻¹ * k * g)⁻¹ := by group
  rw [e]
  exact h1

theorem exists_conj_V3_not_mem {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgH : g ∉ S.G1) : ∃ b ∈ conjSub g S.V3, b ∉ S.V3 := by
  by_contra hall
  push Not at hall
  apply hgH
  set xN : ↥(Subgroup.normalizer (V : Set G)) := ⟨g, hgV⟩ with hxN
  have hst : ∀ y : P6, InW4 y → InW3 y → InW3 (act4f (S.frame.ρ xN) y) := by
    intro y hy4 hy3
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy4⟩
    have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by
      have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨y, hy4⟩ := hv
      rw [e]; exact hy3⟩
    obtain ⟨_, hW⟩ := S.mem_pre.1 (hall _ (mul_mem_conjSub hv3))
    have e : S.frame.ψ ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp xN.2 v).mp v.2⟩ =
        act4 (S.frame.ρ xN) ⟨y, hy4⟩ := by
      rw [S.psi_conj xN v, hv]
    have hW' : S.frame.ψ ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp xN.2 v).mp v.2⟩ ∈
        W3sub := hW
    rw [e] at hW'
    exact hW'
  have hz := stabW3e_all _ hst
  have h1 : g * S.z * g⁻¹ = S.z := by
    rw [show g = (xN : G) from rfl, S.conj_eq_iff xN ⟨S.z, S.z_mem_V⟩, S.psi_z]
    exact Subtype.ext hz
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [h1])

theorem relIndex_U'_le {g : G} (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hcard : Nat.card ↥(conjClosure S.V3 S.G1) = 32) :
    (conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1).relIndex
      (conjSub g (conjClosure S.V3 S.G1)) ≤ 8 := by
  have hV2 : S.V2 ≤ conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1 := by
    intro v hv
    refine Subgroup.mem_inf.2 ⟨?_, S.V3_le_UH (S.V2_le_V3 hv)⟩
    rw [mem_conjSub]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
    simpa using S.V3_le_UH (S.V2_le_V3 this)
  have h1 := Subgroup.relIndex_mul_card
    (conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1) (conjSub g (conjClosure S.V3 S.G1))
  rw [inf_eq_left.2 (inf_le_left.trans le_rfl :
    conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1 ≤ conjSub g (conjClosure S.V3 S.G1)),
    CosetGeom.card_conjSub, hcard] at h1
  have h2 : 4 ≤ Nat.card ↥(conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1) :=
    S.card_V2 ▸ Subgroup.card_le_of_le hV2
  by_contra h
  push Not at h
  nlinarith

theorem not_normalizes_UH (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hG1 : S.G1 ∈ S.Hz)
    {g : G} (hgL : g ∈ L) (hgH : g ∉ S.G1)
    (hgU : g ∈ Subgroup.normalizer (conjClosure S.V3 S.G1 : Set G)) : False := by
  set N := Subgroup.normalizer (conjClosure S.V3 S.G1 : Set G) with hN
  have hG1N : S.G1 ≤ N := le_normalizer_conjClosure S.V3 S.G1
  have hM : (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤ (L ⊔ T) ⊓ N := fun x hx =>
    ⟨hx.1, hG1N (by rw [S.normalizer_V1] at hx; exact hx.2)⟩
  rcases S.NLTV1_max ((L ⊔ T) ⊓ N) hM inf_le_left with h | h
  · have : g ∈ (L ⊔ T) ⊓ N := ⟨Subgroup.mem_sup_left hgL, hgU⟩
    rw [h, S.normalizer_V1] at this
    exact hgH this.2
  · have hLT : L ⊔ T ≤ N := h ▸ inf_le_right
    have hU2 : IsPGroup 2 ↥(conjClosure S.V3 S.G1) :=
      (isPGroup_of_isElemAbelian hF.F911_2).to_le (conjClosure_mono S.V3_le_V le_rfl)
    have hU1 : conjClosure S.V3 S.G1 ≠ ⊥ := by
      intro h0
      have := S.V3_le_UH S.u1_mem_V3
      rw [h0, Subgroup.mem_bot] at this
      have hu := (S.mem_V1_iff_psi S.u1_mem_V).not.mpr (by
        rw [S.psi_u1]
        exact fun h' => by rcases h' with h' | h' <;> exact absurd h' (by decide))
      exact hu (this ▸ (fsuV1 T V).one_mem)
    have hloc : IsTwoLocal N := ⟨_, hU1, hU2, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hMeq := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
    exact hG1.2.2 (hMeq ▸ hG1N.trans hle)

structure LineData (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)) : Prop where
  hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1
  hG1 : S.G1 ∈ S.Hz
  hρs : Function.Surjective ρ
  hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1
  hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V
  hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) =
      ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))
  hv0 : S.v04 ∉ conjClosure S.V3 S.G1
  hVU : V ⊓ conjClosure S.V3 S.G1 = S.V3
  hQu1 : ∃ q ∈ pCoreOf 2 S.G1, q * S.u1 * q⁻¹ ≠ S.u1
  hcard : Nat.card ↥(conjClosure S.V3 S.G1) = 32

theorem mem_V2_of_bv (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (x : ↥(conjClosure S.V3 S.G1)) (hx : S.bv β x = 0 ∨ S.bv β x = S.w1 β) :
    (x : G) ∈ S.V2 := by
  rcases hx with h | h
  · exact S.V1_le_V2 ((S.bv_eq_zero_iff hβk x).1 h)
  · have h1 := (S.bv_eq_iff hβk x ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩).1 h
    have e : (x : G) = ((x * (⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ : ↥(conjClosure S.V3 S.G1))⁻¹ :
        ↥(conjClosure S.V3 S.G1)) : G) * S.u1 := by simp
    rw [e]
    exact S.V2.mul_mem (S.V1_le_V2 h1) S.u1_mem_V2

theorem exists_GL_fix_w1 {x y : Fin 4 → ZMod 2} (hx : pl (S.w1 β) x ≠ 0) (hy : pl (S.w1 β) y ≠ 0) :
    ∃ g' : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
      (g' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (S.w1 β) = S.w1 β ∧
      (g' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec x = y := by
  obtain ⟨h1, h2, h3⟩ := (pl_ne_zero_iff _ _).1 hx
  obtain ⟨-, h2', h3'⟩ := (pl_ne_zero_iff _ _).1 hy
  obtain ⟨c, d, hcd⟩ := exists_basis_of_pair h1 h2 h3
  obtain ⟨c', d', hcd'⟩ := exists_basis_of_pair h1 h2' h3'
  obtain ⟨g', e1, e2, -, -⟩ := exists_GL_map4 hcd hcd'
  exact ⟨g', e1, e2⟩

theorem bv_eq_zero_or_w1 {y : Fin 4 → ZMod 2} (hβk : ∀ u : ↥(conjClosure S.V3 S.G1),
    β u = 1 ↔ (u : G) ∈ fsuV1 T V) (h : pl (S.w1 β) y = 0) : y = 0 ∨ y = S.w1 β := by
  have hw : S.w1 β ≠ 0 := ((pl_ne_zero_iff _ _).1 (S.pl_w1_w2_ne_zero hβk)).1
  by_contra hne
  push Not at hne
  exact (pl_ne_zero_iff _ _).2 ⟨hw, hne.1, Ne.symm hne.2⟩ h

theorem conj_mem_U'_of_mem {g k x : G} (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hk : k ∈ Subgroup.centralizer (S.V2 : Set G)) (hx : x ∈ conjSub g (conjClosure S.V3 S.G1)) :
    k * x * k⁻¹ ∈ conjSub g (conjClosure S.V3 S.G1) := by
  rw [mem_conjSub] at hx ⊢
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_conjClosure S.V3 S.G1 (S.C2_le_G1 (S.conj_mem_C2 hgN hk))) _).mp hx
  have e : g⁻¹ * (k * x * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * x * g) * (g⁻¹ * k * g)⁻¹ := by group
  rw [e]
  exact h1

theorem V2_le_U' {g : G} (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) :
    S.V2 ≤ conjSub g (conjClosure S.V3 S.G1) := by
  intro v hv
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
  simpa using S.V3_le_UH (S.V2_le_V3 this)

theorem exists_nonconst [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1) :
    ∃ k : ↥S.G1, (k : G) ∈ Subgroup.centralizer (S.V2 : Set G) ∧
      S.cls (S.cV k S.v0H) ≠ S.cls S.v0H := by
  by_contra hall
  push Not at hall
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hgL
  have h12 := S.pl_w1_w2_ne_zero D.hβk
  have hUC : conjClosure S.V3 S.G1 ≤
      conjClosure S.V3 (Subgroup.centralizer (S.V2 : Set G)) := by
    intro x hx
    by_cases hp : pl (S.w1 β) (S.bv β ⟨x, hx⟩) = 0
    · exact le_conjClosure _ _
        (S.V2_le_V3 (S.mem_V2_of_bv D.hβk ⟨x, hx⟩ (S.bv_eq_zero_or_w1 D.hβk hp)))
    · obtain ⟨g', hg'1, hg'2⟩ := S.exists_GL_fix_w1 h12 hp
      obtain ⟨k, hk, hkC⟩ := S.exists_lift_C2 D.hF D.hρs D.hker D.hβk D.hβe D.hQu1 g' hg'1
      have hm : (k : G) * S.u2 * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
        mem_conjClosure k.2 S.u2_mem_V3
      have hbv : S.bv β ⟨x, hx⟩ = S.bv β ⟨_, hm⟩ := by
        rw [← hg'2]
        have := D.hβe k ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ ⟨_, hm⟩ rfl
        change S.bv β _ = _ at this
        rw [this, hk]
        rfl
      have h1 := (S.bv_eq_iff D.hβk _ _).1 hbv
      have e : x = (x * ((k : G) * S.u2 * (k : G)⁻¹)⁻¹) * ((k : G) * S.u2 * (k : G)⁻¹) := by
        group
      rw [e]
      exact Subgroup.mul_mem _ (le_conjClosure _ _ (S.V1_le_V3 h1))
        (mem_conjClosure hkC S.u2_mem_V3)
  have hC2g : conjSub g (Subgroup.centralizer (S.V2 : Set G)) =
      Subgroup.centralizer (S.V2 : Set G) := by
    rw [← conjSub_centralizer, F7.conjSub_eq_of_mem_normalizer hgN]
  have hU'le : conjSub g (conjClosure S.V3 S.G1) ≤ V ⊔ conjClosure S.V3 S.G1 := by
    refine (conjSub_mono g hUC).trans ?_
    rw [conjSub_conjClosure_eq, hC2g]
    refine conjClosure_le fun k hk b hb => ?_
    have hbV : b ∈ V := by
      rw [mem_conjSub] at hb
      have := (Subgroup.mem_normalizer_iff.mp hgV _).mp (S.V3_le_V hb)
      simpa [mul_assoc] using this
    by_cases hb3 : b ∈ S.V3
    · exact Subgroup.mem_sup_right (mem_conjClosure (S.C2_le_G1 hk) hb3)
    · have hm := inv_mul_mem_of_relIndex_two S.relIndex_V3_V S.v04_mem_V hbV
        S.v04_not_mem_V3 hb3
      have hk' := (S.cls_eq_iff _ _).1 (hall ⟨k, S.C2_le_G1 hk⟩ hk)
      rw [cV_coe] at hk'
      have e : k * b * k⁻¹ = S.v04 * ((k * S.v04 * k⁻¹)⁻¹ * S.v04)⁻¹ *
          (k * ((S.v04)⁻¹ * b) * k⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left S.v04_mem_V)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hk'))) (Subgroup.mem_sup_right
          (mem_conjClosure (S.C2_le_G1 hk) hm))
  have hVN : V ≤ Subgroup.normalizer (conjClosure S.V3 S.G1 : Set G) :=
    D.hF.toHypF91.V_le_H.trans (le_normalizer_conjClosure S.V3 S.G1)
  have hcVU : Nat.card ↥(V ⊔ conjClosure S.V3 S.G1) = 64 := by
    have hp := card_sup_mul_card_inf' hVN
    rw [D.hVU, S.card_V, S.card_V3, D.hcard] at hp
    omega
  have hidx : (conjClosure S.V3 S.G1).relIndex (V ⊔ conjClosure S.V3 S.G1) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (conjClosure S.V3 S.G1) (V ⊔ conjClosure S.V3 S.G1)
    rw [inf_eq_left.2 (le_sup_right : conjClosure S.V3 S.G1 ≤ V ⊔ conjClosure S.V3 S.G1),
      hcVU, D.hcard] at h1
    omega
  have hidx' : (conjClosure S.V3 S.G1).relIndex (conjSub g (conjClosure S.V3 S.G1)) ≤ 2 :=
    hidx ▸ Subgroup.relIndex_le_of_le_right hU'le (relIndex_ne_zero' _ _)
  have hcard16 : 16 ≤ Nat.card ↥(conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1) := by
    have h1 := Subgroup.relIndex_mul_card (conjClosure S.V3 S.G1)
      (conjSub g (conjClosure S.V3 S.G1))
    rw [CosetGeom.card_conjSub, D.hcard, inf_comm] at h1
    nlinarith [Nat.pos_of_ne_zero (relIndex_ne_zero' (conjClosure S.V3 S.G1)
      (conjSub g (conjClosure S.V3 S.G1)))]
  obtain ⟨x, hxI, hxp⟩ : ∃ x ∈ conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1,
      ∃ hx : x ∈ conjClosure S.V3 S.G1, pl (S.w1 β) (S.bv β ⟨x, hx⟩) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : conjSub g (conjClosure S.V3 S.G1) ⊓ conjClosure S.V3 S.G1 ≤ S.V2 := fun x hx =>
      S.mem_V2_of_bv D.hβk ⟨x, hx.2⟩ (S.bv_eq_zero_or_w1 D.hβk (hcon x hx hx.2))
    have := Subgroup.card_le_of_le hle
    rw [S.card_V2] at this
    omega
  obtain ⟨hxU, hxp⟩ := hxp
  have hUle : conjClosure S.V3 S.G1 ≤ conjSub g (conjClosure S.V3 S.G1) := by
    intro y hy
    have hV2I : S.V2 ≤ conjSub g (conjClosure S.V3 S.G1) := S.V2_le_U' hgN
    by_cases hp : pl (S.w1 β) (S.bv β ⟨y, hy⟩) = 0
    · exact hV2I (S.mem_V2_of_bv D.hβk ⟨y, hy⟩ (S.bv_eq_zero_or_w1 D.hβk hp))
    · obtain ⟨g', hg'1, hg'2⟩ := S.exists_GL_fix_w1 hxp hp
      obtain ⟨k, hk, hkC⟩ := S.exists_lift_C2 D.hF D.hρs D.hker D.hβk D.hβe D.hQu1 g' hg'1
      have hm : (k : G) * x * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) x).mp hxU
      have hbv : S.bv β ⟨y, hy⟩ = S.bv β ⟨_, hm⟩ := by
        rw [← hg'2]
        have := D.hβe k ⟨x, hxU⟩ ⟨_, hm⟩ rfl
        change S.bv β _ = _ at this
        rw [this, hk]
        rfl
      have h1 := (S.bv_eq_iff D.hβk _ _).1 hbv
      have e : y = (y * ((k : G) * x * (k : G)⁻¹)⁻¹) * ((k : G) * x * (k : G)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hV2I (S.V1_le_V2 h1)) (S.conj_mem_U'_of_mem hgN hkC hxI.1)
  have heq : conjSub g (conjClosure S.V3 S.G1) = conjClosure S.V3 S.G1 :=
    (Subgroup.eq_of_le_of_card_ge hUle (by rw [CosetGeom.card_conjSub])).symm
  exact S.not_normalizes_UH D.hF D.hG1 hgL hgH (mem_normalizer_of_conjSub_eq heq)

@[expose] def e7 : Fin 7 → Fin 3 → ZMod 2 :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

theorem e7_injective : Function.Injective e7 := by decide

theorem e7_ne_zero : ∀ m, e7 m ≠ 0 := by decide

theorem pl_pt3_ne_zero {a b c d : Fin 4 → ZMod 2}
    (h : ∀ x : Fin 4 → ZMod 2, x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0)
    {ε : Fin 3 → ZMod 2} (hε : ε ≠ 0) : pl a (pt3 b c d ε) ≠ 0 := by
  intro h0
  apply hε
  refine pl_pt3_injective h ?_
  rw [h0]
  simp [pt3, pl_zero_right]

theorem Phi_ne_zero [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    {a b : Fin 4 → ZMod 2} (hab : pl a b ≠ 0) : S.Phi ρ β (pl a b) ≠ 0 := by
  obtain ⟨k, hk1, hk2⟩ := S.exists_k_of_pl D.hρs D.hβk hab
  rw [← hk1, ← hk2, S.Phi_spec D.hF D.hβk D.hβe, Ne, cls_eq_zero_iff, cV_coe]
  intro h
  apply D.hv0
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1
    (S.G1.inv_mem k.2)) _).mp h
  have h' : ((S.v0H : ↥(conjClosure V S.G1)) : G) ∈ conjClosure S.V3 S.G1 := by
    simpa [mul_assoc] using this
  exact h'

theorem rv_w1_of_C2 (D : S.LineData ρ β) {k : ↥S.G1}
    (hk : (k : G) ∈ Subgroup.centralizer (S.V2 : Set G)) : S.rv ρ k (S.w1 β) = S.w1 β := by
  have hc : (k : G) * S.u1 * (k : G)⁻¹ = S.u1 := by
    have := Subgroup.mem_centralizer_iff.mp hk S.u1 S.u1_mem_V2
    calc (k : G) * S.u1 * (k : G)⁻¹ = S.u1 * k * (k : G)⁻¹ := by rw [this]
      _ = S.u1 := by group
  have := D.hβe k ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ hc.symm
  exact this.symm

theorem Phi_w1_injective [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    {x x' : Fin 4 → ZMod 2} (hx : pl (S.w1 β) x ≠ 0) (hx' : pl (S.w1 β) x' ≠ 0)
    (hxx : pl (S.w1 β) x ≠ pl (S.w1 β) x') :
    S.Phi ρ β (pl (S.w1 β) x) ≠ S.Phi ρ β (pl (S.w1 β) x') := by
  intro heq
  obtain ⟨k, hkC, hk⟩ := S.exists_nonconst D hgL hgN hgH
  apply hk
  have h12 := S.pl_w1_w2_ne_zero D.hβk
  have e1 : S.cls (S.cV 1 S.v0H) = S.cls S.v0H := by
    congr 1
    apply Subtype.ext
    simp [cV_coe]
  rw [← e1, ← S.Phi_spec D.hF D.hβk D.hβe, ← S.Phi_spec D.hF D.hβk D.hβe,
    S.rv_w1_of_C2 D hkC]
  have hr1 : S.rv ρ 1 (S.w1 β) = S.w1 β := by simp [rv]
  have hr2 : S.rv ρ 1 (S.w2 β) = S.w2 β := by simp [rv]
  rw [hr1, hr2]
  set y := S.rv ρ k (S.w2 β) with hy
  have hy0 : pl (S.w1 β) y ≠ 0 := by
    rw [hy, ← S.rv_w1_of_C2 D hkC, pl_rv]
    intro h0
    apply h12
    have := congrArg (fun z => (wedge2 ((ρ k⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec z) h0
    simp only [Matrix.mulVec_zero] at this
    rwa [← pl_rv, ← pl_rv, rv_inv_rv, rv_inv_rv] at this
  by_cases hyw : pl (S.w1 β) y = pl (S.w1 β) (S.w2 β)
  · rw [hyw]
  obtain ⟨d, hd⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hx hx' hxx hs)
  obtain ⟨d', hd'⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hy0 h12 hyw hs)
  obtain ⟨g'', e1', e2', e3', -⟩ := exists_GL_map4 hd hd'
  obtain ⟨k'', hk''⟩ := D.hρs g''
  have hrv : ∀ z, S.rv ρ k'' z = (g'' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec z := fun z => by
    rw [rv, hk'']
  have h1 := S.Phi_equiv D.hF D.hρs D.hβk D.hβe k'' (S.w1 β) x
  have h2 := S.Phi_equiv D.hF D.hρs D.hβk D.hβe k'' (S.w1 β) x'
  rw [hrv, hrv, e1', e2'] at h1
  rw [hrv, hrv, e1', e3'] at h2
  rw [h1, h2, heq]

theorem exists_rep [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    {b₀ : G} (hb₀ : b₀ ∈ conjSub g S.V3) (hb₀3 : b₀ ∉ S.V3)
    {x : Fin 4 → ZMod 2} (hx : pl (S.w1 β) x ≠ 0) :
    ∃ r : ↥(conjClosure V S.G1), (r : G) ∈ conjSub g (conjClosure S.V3 S.G1) ∧
      S.cls r = S.Phi ρ β (pl (S.w1 β) x) := by
  have h12 := S.pl_w1_w2_ne_zero D.hβk
  obtain ⟨g', hg'1, hg'2⟩ := S.exists_GL_fix_w1 h12 hx
  obtain ⟨k, hk, hkC⟩ := S.exists_lift_C2 D.hF D.hρs D.hker D.hβk D.hβe D.hQu1 g' hg'1
  have hgV := S.frame.L_le hgL
  have hb₀V : b₀ ∈ V := by
    rw [mem_conjSub] at hb₀
    have := (Subgroup.mem_normalizer_iff.mp hgV _).mp (S.V3_le_V hb₀)
    simpa [mul_assoc] using this
  refine ⟨⟨(k : G) * b₀ * (k : G)⁻¹, mem_conjClosure k.2 hb₀V⟩, S.conj_mem_U' hgN hkC hb₀, ?_⟩
  have hr1 : S.rv ρ k (S.w1 β) = S.w1 β := by rw [rv, hk]; exact hg'1
  have hr2 : S.rv ρ k (S.w2 β) = x := by rw [rv, hk]; exact hg'2
  rw [← hr1, ← hr2, S.Phi_spec D.hF D.hβk D.hβe, eq_comm, cls_eq_iff, cV_coe]
  have hm := inv_mul_mem_of_relIndex_two S.relIndex_V3_V S.v04_mem_V hb₀V S.v04_not_mem_V3 hb₀3
  have e : ((k : G) * S.v04 * (k : G)⁻¹)⁻¹ * ((k : G) * b₀ * (k : G)⁻¹) =
      (k : G) * ((S.v04)⁻¹ * b₀) * (k : G)⁻¹ := by group
  have e2 : ((S.v0H : ↥(conjClosure V S.G1)) : G) = S.v04 := rfl
  rw [e2]
  show ((k : G) * S.v04 * (k : G)⁻¹)⁻¹ * ((k : G) * b₀ * (k : G)⁻¹) ∈ conjClosure S.V3 S.G1
  rw [e]
  exact mem_conjClosure k.2 hm

theorem line_w1 [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    {b c : Fin 4 → ZMod 2} (hb : pl (S.w1 β) b ≠ 0) (hc : pl (S.w1 β) c ≠ 0)
    (hbc : pl (S.w1 β) b ≠ pl (S.w1 β) c) :
    S.Phi ρ β (pl (S.w1 β) b) + S.Phi ρ β (pl (S.w1 β) c) = S.Phi ρ β (pl (S.w1 β) (b + c)) := by
  obtain ⟨b₀, hb₀, hb₀3⟩ := S.exists_conj_V3_not_mem (S.frame.L_le hgL) hgH
  obtain ⟨d, hd⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hb hc hbc hs)
  set f : (Fin 3 → ZMod 2) → S.VUQ := fun ε => S.Phi ρ β (pl (S.w1 β) (pt3 b c d ε)) with hfdef
  have hp : ∀ m, pl (S.w1 β) (pt3 b c d (e7 m)) ≠ 0 := fun m => pl_pt3_ne_zero hd (e7_ne_zero m)
  have hfinj : ∀ m m', m ≠ m' → f (e7 m) ≠ f (e7 m') := fun m m' hmm =>
    S.Phi_w1_injective D hgL hgN hgH (hp m) (hp m')
      (fun h => hmm (e7_injective (pl_pt3_injective hd h)))
  have hf0 : ∀ m, f (e7 m) ≠ 0 := fun m => S.Phi_ne_zero D (hp m)
  have hb' : pt3 b c d (e7 0) = b := by simp [pt3, e7]
  have hc' : pt3 b c d (e7 1) = c := by simp [pt3, e7]
  have hbc' : pt3 b c d (e7 2) = b + c := by simp [pt3, e7]
  suffices key : f (e7 0) + f (e7 1) = f (e7 2) by
    simp only [hfdef, hb', hc', hbc'] at key
    exact key
  by_contra hne
  have hd₁ : ∀ x : Fin 4 → ZMod 2,
      x 0 • S.w1 β + x 1 • b + x 2 • c + x 3 • (d + b) = 0 → x = 0 := by
    intro x hx
    have h1 := hd ![x 0, x 1 + x 3, x 2, x 3] (by
      rw [← hx]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, add_smul, smul_add]
      abel)
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    have e3 := congrFun h1 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at e0 e1 e2 e3
    rw [e3, add_zero] at e1
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  obtain ⟨g₁, f1, f2, f3, f4⟩ := exists_GL_map4 hd hd₁
  obtain ⟨k₁, hk₁⟩ := D.hρs g₁
  have hrv : ∀ z, S.rv ρ k₁ z = (g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec z := fun z => by
    rw [rv, hk₁]
  have hact : ∀ ε : Fin 3 → ZMod 2, S.act k₁ (f ε) = f (ε + ![ε 2, 0, 0]) := by
    intro ε
    simp only [hfdef]
    rw [← S.Phi_equiv D.hF D.hρs D.hβk D.hβe, hrv, hrv, f1]
    congr 2
    simp only [pt3, Matrix.mulVec_add, Matrix.mulVec_smul, f2, f3, f4, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, add_zero, add_smul, smul_add]
    abel
  have hy : S.act k₁ (f (e7 0) + f (e7 1)) = f (e7 0) + f (e7 1) := by
    rw [map_add, hact, hact]
    congr 2 <;> funext i <;> fin_cases i <;> simp [e7]
  have hmove : ∀ m₁ m₂ : Fin 7, e7 m₁ + ![e7 m₁ 2, 0, 0] = e7 m₂ → m₁ ≠ m₂ →
      f (e7 0) + f (e7 1) ≠ f (e7 m₁) := by
    intro m₁ m₂ he hne' hm
    apply hfinj m₂ m₁ (Ne.symm hne')
    rw [← he, ← hact, ← hm, hy]
  have hyne : ∀ m, f (e7 0) + f (e7 1) ≠ f (e7 m) := by
    intro m
    fin_cases m
    · intro h
      exact hf0 1 (by
        have := congrArg (fun z => z - f (e7 0)) h
        simpa using this)
    · intro h
      exact hf0 0 (by
        have := congrArg (fun z => z - f (e7 1)) h
        simpa using this)
    · exact hne
    · exact hmove 3 4 (by decide) (by decide)
    · exact hmove 4 3 (by decide) (by decide)
    · exact hmove 5 6 (by decide) (by decide)
    · exact hmove 6 5 (by decide) (by decide)
  have hy0 : f (e7 0) + f (e7 1) ≠ 0 := by
    intro h
    apply hfinj 0 1 (by decide)
    have := congrArg (fun z => z - f (e7 1)) h
    simp only [add_sub_cancel_right, zero_sub] at this
    rw [this]
    exact neg_eq_of_add_eq_zero_right (S.cls_add_self D.hF _)
  choose rf hrfU hrfc using fun m => S.exists_rep D hgL hgN hb₀ hb₀3 (hp m)
  let cl : Fin 9 → S.VUQ := Fin.cons 0 (Fin.cons (f (e7 0) + f (e7 1)) fun m => f (e7 m))
  have hcl : Function.Injective cl := by
    refine Fin.cons_injective_of_injective ?_ (Fin.cons_injective_of_injective ?_ ?_)
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.cases ?_ (fun m => ?_) i
      · intro hi
        simp only [Fin.cons_zero] at hi
        exact hy0 hi
      · intro hi
        simp only [Fin.cons_succ] at hi
        exact hf0 m hi
    · rintro ⟨m, hm⟩
      exact hyne m hm.symm
    · intro m m' h
      by_contra hmm
      exact hfinj m m' hmm h
  let reps : Fin 9 → ↥(conjClosure V S.G1) := Fin.cons 1 (Fin.cons (rf 0 * rf 1) rf)
  have hreps : ∀ i, S.cls (reps i) = cl i := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun m => ?_) j) i
    · exact (S.cls_eq_zero_iff 1).2 (conjClosure S.V3 S.G1).one_mem
    · show S.cls (rf 0 * rf 1) = f (e7 0) + f (e7 1)
      rw [cls_mul, hrfc, hrfc]
    · exact hrfc m
  have hrepsU : ∀ i, ((reps i : ↥(conjClosure V S.G1)) : G) ∈
      conjSub g (conjClosure S.V3 S.G1) := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun m => ?_) j) i
    · exact Subgroup.one_mem _
    · exact Subgroup.mul_mem _ (hrfU 0) (hrfU 1)
    · exact hrfU m
  refine false_of_classes (S.relIndex_U'_le hgN D.hcard) (fun i => (reps i : G)) hrepsU
    fun i j hij hmem => hij (hcl ?_)
  rw [← hreps, ← hreps, cls_eq_iff]
  exact hmem.2

theorem line_relations [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (a b c : Fin 4 → ZMod 2) (hb : pl a b ≠ 0) (hc : pl a c ≠ 0) (hbc : pl a b ≠ pl a c) :
    S.Phi ρ β (pl a b) + S.Phi ρ β (pl a c) = S.Phi ρ β (pl a (b + c)) := by
  have h12 := S.pl_w1_w2_ne_zero D.hβk
  obtain ⟨w1n, w2n, w12⟩ := (pl_ne_zero_iff _ _).1 h12
  obtain ⟨c₀, d₀, hcd₀⟩ := exists_basis_of_pair w1n w2n w12
  obtain ⟨d, hd⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hb hc hbc hs)
  obtain ⟨g', e1, e2, e3, -⟩ := exists_GL_map4 hcd₀ hd
  obtain ⟨k, hk⟩ := D.hρs g'
  have hrv : ∀ z, S.rv ρ k z = (g' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec z := fun z => by
    rw [rv, hk]
  have hw2 : pt3 (S.w2 β) c₀ d₀ (e7 0) = S.w2 β := by simp [pt3, e7]
  have hc₀ : pt3 (S.w2 β) c₀ d₀ (e7 1) = c₀ := by simp [pt3, e7]
  have hp1 : pl (S.w1 β) c₀ ≠ 0 := hc₀ ▸ pl_pt3_ne_zero hcd₀ (e7_ne_zero 1)
  have hp2 : pl (S.w1 β) (S.w2 β) ≠ pl (S.w1 β) c₀ := by
    intro h
    have h' := pl_pt3_injective hcd₀ (ε := e7 0) (ε' := e7 1) (by rw [hw2, hc₀]; exact h)
    exact absurd (e7_injective h') (by decide)
  have hl := congrArg (S.act k) (S.line_w1 D hgL hgN hgH h12 hp1 hp2)
  rw [map_add, ← S.Phi_equiv D.hF D.hρs D.hβk D.hβe, ← S.Phi_equiv D.hF D.hρs D.hβk D.hβe,
    ← S.Phi_equiv D.hF D.hρs D.hβk D.hβe, hrv, hrv, hrv, hrv, Matrix.mulVec_add, e1, e2,
    e3] at hl
  exact hl

end Lines

end Setting4

end CFSG.Quasithin.H13.A6
