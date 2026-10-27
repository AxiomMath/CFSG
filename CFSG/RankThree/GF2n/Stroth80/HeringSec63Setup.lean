module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Split
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Inputs : Prop where
  h34 : Stroth34Statement
  hRoot : Stroth310RootStatement
  h51 : Stroth51Statement
  hNt : StrothNtStatement

structure Env (hc : Ctx M Q Z B) (n : ℕ) (t : G) (m : ℕ) (X : Subgroup G) : Prop where
  hs : Stroth6Hyp hc n t
  hm : 3 ≤ m
  hn : n = 2 * m
  hΩ : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m
  hQX : Q ≤ X
  hXR : X ≤ Rt M (LB M Q B) t
  hNX : hc.CN t ⊔ X = Rt M (LB M Q B) t
  hNXQ : hc.CN t ⊓ X = Q
  hcen : ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.card_Vt (e : Env hc n t m X) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  rcases e.hΩ with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have h := card_of_naturalRep hnat sec39_Z_le_Vt hK
    rw [h, Fintype.card_sum, Fintype.card_fin]
    rw [← pow_succ']
    congr 1
    omega
  · have h := card_of_naturalRep hnat sec39_Z_le_Vt hK
    rw [h, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    rw [← pow_succ']
    congr 1
    have := e.hm
    omega

theorem natSO_of_omega {hc : Ctx M Q Z B} {t : G} {m : ℕ} (hm : 3 ≤ m)
    (h : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) : SpNat hc t ∨ OmegaNat hc t := by
  rcases h with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · exact Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  · exact Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, by omega, hirr, hnat⟩⟩

theorem Env.W_eq_V (h34 : Stroth34Statement) (e : Env hc n t m X) :
    Wt Q (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  have hVW := Vt_le_Wt h34 hc e.hs.toSec5
  have h1 := hc.card_Wt_mul_card_Vt t
  have h2 := e.card_Vt
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := e.hs.toSec5.width
  rw [h2, hw] at h1
  have hq : 0 < Nat.card Z := Nat.card_pos
  have h3 : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * m + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * m + 1))
    rw [h1, e.hn]
    ring
  exact (Subgroup.eq_of_le_of_card_ge hVW (by rw [h3, h2])).symm

theorem Env.U_eq_V_and_Q1_eq_V (h34 : Stroth34Statement) (e : Env hc n t m X) :
    Ut Q Z t = Vt M (LB M Q B) B Z t ∧ Q1 hc t = Vt M (LB M Q B) B Z t := by
  obtain ⟨h1, h2⟩ := stroth310Chi_of_34 h34 G M Q Z B hc n t e.hs.toSec5
    (natSO_of_omega e.hm e.hΩ)
  rw [e.W_eq_V h34] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem Env.chi (h34 : Stroth34Statement) (e : Env hc n t m X) :
    IsChiIso Q (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Vt M (LB M Q B) B Z t) Z t := by
  have h := hc.isChiIso_Q1_Ut e.hs.toSec5.mem
  obtain ⟨h1, h2⟩ := e.U_eq_V_and_Q1_eq_V h34
  rw [h1, h2] at h
  exact h

section ChiVec

variable {R V : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  [(Z.subgroupOf V).Normal]

@[expose] noncomputable def chiVec {Q K₀ : Subgroup G} {t : G}
    (hχ : IsChiIso Q R K₀ V Z t) (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (x : ↥Q) : ι → K :=
  secVec ψ ⟨⁅(x : G), t⁆, hχ.1 x x.2⟩

variable {Q K₀ : Subgroup G} {t : G} (hχ : IsChiIso Q R K₀ V Z t)
  (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))

theorem chiVec_mul (x y : ↥Q) : chiVec hχ ψ (x * y) = chiVec hχ ψ x + chiVec hχ ψ y := by
  have h3 := hχ.2.2.1 (x : G) x.2 (y : G) y.2
  have h := (secVec_eq_iff ψ ⟨⁅((x * y : ↥Q) : G), t⁆, hχ.1 _ (x * y).2⟩
    ⟨⁅(x : G), t⁆ * ⁅(y : G), t⁆, V.mul_mem (hχ.1 _ x.2) (hχ.1 _ y.2)⟩).mpr h3
  have e : chiVec hχ ψ (x * y) =
      secVec ψ ⟨⁅(x : G), t⁆ * ⁅(y : G), t⁆, V.mul_mem (hχ.1 _ x.2) (hχ.1 _ y.2)⟩ := h
  rw [e]
  exact secVec_mul ψ ⟨⁅(x : G), t⁆, hχ.1 _ x.2⟩ ⟨⁅(y : G), t⁆, hχ.1 _ y.2⟩

theorem chiVec_eq_zero_iff (x : ↥Q) : chiVec hχ ψ x = 0 ↔ (x : G) ∈ K₀ := by
  unfold chiVec
  rw [secVec_eq_zero_iff]
  exact hχ.2.2.2.1 x x.2

theorem chiVec_conj (φ : ↥R →* GL ι K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hQM : ∀ r ∈ R, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q) (r : ↥R) (x : ↥Q) :
    chiVec hχ ψ ⟨(r : G) * x * (r : G)⁻¹, hQM r r.2 x x.2⟩ =
      (φ r : Matrix ι ι K) *ᵥ chiVec hχ ψ x := by
  have h5 := hχ.2.2.2.2 (r : G) r.2 (x : G) x.2
  have hmem : (r : G) * ⁅(x : G), t⁆ * (r : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hRV r.2) _).mp (hχ.1 _ x.2)
  have h := (secVec_eq_iff ψ ⟨⁅(r : G) * x * (r : G)⁻¹, t⁆, hχ.1 _ (hQM r r.2 x x.2)⟩
    ⟨(r : G) * ⁅(x : G), t⁆ * (r : G)⁻¹, hmem⟩).mpr h5
  have e : chiVec hχ ψ ⟨(r : G) * x * (r : G)⁻¹, hQM r r.2 x x.2⟩ =
      secVec ψ ⟨(r : G) * ⁅(x : G), t⁆ * (r : G)⁻¹, hmem⟩ := h
  rw [e]
  exact hψ r ⟨⁅(x : G), t⁆, hχ.1 _ x.2⟩ _ rfl

theorem chiVec_inv (hK₀ : (1 : G) ∈ K₀) (x : ↥Q) :
    chiVec hχ ψ x⁻¹ = -chiVec hχ ψ x := by
  have h := chiVec_mul hχ ψ x x⁻¹
  rw [mul_inv_cancel] at h
  have h1 : chiVec hχ ψ (1 : ↥Q) = 0 := (chiVec_eq_zero_iff hχ ψ 1).mpr hK₀
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end ChiVec

section VecOf

variable {V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))

@[expose] noncomputable def vecOf (g : G) : ι → K := by
  classical
  exact if h : g ∈ V then secVec ψ ⟨g, h⟩ else 0

theorem vecOf_of_mem {g : G} (hg : g ∈ V) : vecOf ψ g = secVec ψ ⟨g, hg⟩ := by
  unfold vecOf
  exact dif_pos hg

theorem vecOf_mul {g h : G} (hg : g ∈ V) (hh : h ∈ V) :
    vecOf ψ (g * h) = vecOf ψ g + vecOf ψ h := by
  rw [vecOf_of_mem ψ (V.mul_mem hg hh), vecOf_of_mem ψ hg, vecOf_of_mem ψ hh]
  exact secVec_mul ψ ⟨g, hg⟩ ⟨h, hh⟩

theorem vecOf_inv {g : G} (hg : g ∈ V) : vecOf ψ g⁻¹ = -vecOf ψ g := by
  rw [vecOf_of_mem ψ (V.inv_mem hg), vecOf_of_mem ψ hg]
  exact secVec_inv ψ ⟨g, hg⟩

theorem vecOf_eq_zero_iff {g : G} (hg : g ∈ V) : vecOf ψ g = 0 ↔ g ∈ Z := by
  rw [vecOf_of_mem ψ hg]
  exact secVec_eq_zero_iff ψ ⟨g, hg⟩

theorem vecOf_eq_iff {g h : G} (hg : g ∈ V) (hh : h ∈ V) :
    vecOf ψ g = vecOf ψ h ↔ g * h⁻¹ ∈ Z := by
  rw [vecOf_of_mem ψ hg, vecOf_of_mem ψ hh]
  exact secVec_eq_iff ψ ⟨g, hg⟩ ⟨h, hh⟩

theorem vecOf_of_mem_Z {g : G} (hg : g ∈ Z) (hZV : Z ≤ V) : vecOf ψ g = 0 :=
  (vecOf_eq_zero_iff ψ (hZV hg)).mpr hg

theorem vecOf_mul_Z {g z : G} (hg : g ∈ V) (hz : z ∈ Z) (hZV : Z ≤ V) :
    vecOf ψ (g * z) = vecOf ψ g := by
  rw [vecOf_mul ψ hg (hZV hz), vecOf_of_mem_Z ψ hz hZV, add_zero]

theorem vecOf_conj {R : Subgroup G} (φ : ↥R →* GL ι K)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (r : ↥R) {g : G} (hg : g ∈ V) :
    vecOf ψ ((r : G) * g * (r : G)⁻¹) = (φ r : Matrix ι ι K) *ᵥ vecOf ψ g := by
  have hm : (r : G) * g * (r : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hRV r.2) g).mp hg
  rw [vecOf_of_mem ψ hm, vecOf_of_mem ψ hg]
  exact hψ r ⟨g, hg⟩ ⟨_, hm⟩ rfl

end VecOf

section Derived

theorem Env.exists_nat (e : Env hc n t m X) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K 2) (Xm : Subgroup (GL ι K)), AddCommutantScalar Xm ∧
      Nat.card K = Nat.card Z ∧
      NaturalRep (ι := ι) K Xm (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := by
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  rcases e.hΩ with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    exact ⟨Fin m ⊕ Fin m, inferInstance, inferInstance, K, fK, finK, inferInstance, _,
      addCommutantScalar_statedOmegaPlus e.hm, hK, hnat⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    exact ⟨Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, inferInstance, inferInstance, K, fK, finK,
      inferInstance, _, addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr, hK,
      hnat⟩

theorem Env.comm_mem_V (h34 : Stroth34Statement) (e : Env hc n t m X) {a x : G}
    (ha : a ∈ hc.CN t) (hx : x ∈ Q) : ⁅a, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨ι, _, _, K, _, _, _, Xm, -, -, φ, -, hφk, hRV, hn, ψ, hψ⟩ := e.exists_nat
  haveI := hn
  have hχ := e.chi h34
  have hNR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  have haφ : φ ⟨a, hNR⟩ = 1 := by
    have : (⟨a, hNR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr ha
    exact this
  have hQM : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx
  have h1 := chiVec_conj hχ ψ φ hψ hRV hQM ⟨a, hNR⟩ ⟨x, hx⟩
  rw [haφ, Units.val_one, Matrix.one_mulVec] at h1
  have hV1 : (1 : G) ∈ Vt M (LB M Q B) B Z t := Subgroup.one_mem _
  have hy : a * x * a⁻¹ ∈ Q := hQM a hNR x hx
  have h2 : chiVec hχ ψ (⟨a * x * a⁻¹, hy⟩ * (⟨x, hx⟩ : ↥Q)⁻¹) = 0 := by
    rw [chiVec_mul, chiVec_inv hχ ψ hV1]
    have h3 : chiVec hχ ψ ⟨a * x * a⁻¹, hy⟩ = chiVec hχ ψ ⟨x, hx⟩ := h1
    rw [h3]
    abel
  have h4 := (chiVec_eq_zero_iff hχ ψ _).mp h2
  simpa [commutatorElement_def] using h4

theorem Env.N_mod_Q (h34 : Stroth34Statement) (e : Env hc n t m X) :
    (∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Q) ∧ ∀ a ∈ hc.CN t, a ^ 2 ∈ Q := by
  obtain ⟨ι, _, _, K, _, _, hch, Xm, -, -, φ, -, hφk, hRV, hn, ψ, hψ⟩ := e.exists_nat
  haveI := hn
  have hNR : ∀ a ∈ hc.CN t, a ∈ Rt M (LB M Q B) t := fun a ha => (Ctx.mem_CN.mp ha).1
  have hφ1 : ∀ (a : G) (ha : a ∈ hc.CN t), φ ⟨a, hNR a ha⟩ = 1 := fun a ha => by
    have : (⟨a, hNR a ha⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr ha
    exact this
  have hact : ∀ (a : G) (ha : a ∈ hc.CN t) (v : ↥(Vt M (LB M Q B) B Z t))
      (hv : a * v * a⁻¹ ∈ Vt M (LB M Q B) B Z t), secVec ψ ⟨a * v * a⁻¹, hv⟩ = secVec ψ v := by
    intro a ha v hv
    have h := hψ ⟨a, hNR a ha⟩ v ⟨a * v * a⁻¹, hv⟩ rfl
    rw [hφ1 a ha] at h
    exact h.trans (Matrix.one_mulVec _)
  have hcomm : ∀ (x : G) (hx : x ∈ Q), ∃ f : ↥(hc.CN t) →* Multiplicative (ι → K),
      ∀ a : ↥(hc.CN t),
      f a = Multiplicative.ofAdd (secVec ψ ⟨⁅(a : G), x⁆, e.comm_mem_V h34 a.2 hx⟩) := by
    intro x hx
    refine ⟨MonoidHom.mk' (fun a => Multiplicative.ofAdd
      (secVec ψ ⟨⁅(a : G), x⁆, e.comm_mem_V h34 a.2 hx⟩)) ?_, fun a => rfl⟩
    intro a b
    have hid : ⁅((a * b : ↥(hc.CN t)) : G), x⁆ =
        (a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹ * ⁅(a : G), x⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    have hbm := e.comm_mem_V h34 b.2 hx
    have ham := e.comm_mem_V h34 a.2 hx
    have hconj : (a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRV (hNR a a.2)) _).mp hbm
    have hsub : (⟨⁅((a * b : ↥(hc.CN t)) : G), x⁆, e.comm_mem_V h34 (a * b).2 hx⟩ :
        ↥(Vt M (LB M Q B) B Z t)) = ⟨(a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹, hconj⟩ *
          ⟨⁅(a : G), x⁆, ham⟩ := Subtype.ext hid
    show Multiplicative.ofAdd (secVec ψ ⟨⁅((a * b : ↥(hc.CN t)) : G), x⁆, _⟩) = _
    rw [hsub, secVec_mul, hact a a.2 ⟨⁅(b : G), x⁆, hbm⟩ hconj, ← ofAdd_add, add_comm]
  have hker : ∀ c : ↥(hc.CN t), (∀ (x : G) (hx : x ∈ Q),
      secVec ψ ⟨⁅(c : G), x⁆, e.comm_mem_V h34 c.2 hx⟩ = 0) → (c : G) ∈ Q := by
    intro c hc0
    refine hc.hyp.centralizer_Qt c (hc.Rt_le_M t (hNR c c.2)) fun x hx => ?_
    exact (secVec_eq_zero_iff ψ _).mp (hc0 x hx)
  constructor
  · intro a ha b hb
    have hcm : ⁅a, b⁆ = (((⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥(hc.CN t))) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rw [hcm]
    refine hker _ fun x hx => ?_
    obtain ⟨f, hf⟩ := hcomm x hx
    have h1 : f (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_comm (f ⟨a, ha⟩) (f ⟨b, hb⟩)]
      simp
    rw [hf] at h1
    exact toAdd_eq_zero.mpr h1
  · intro a ha
    have hsq : a ^ 2 = (((⟨a, ha⟩ * ⟨a, ha⟩ : ↥(hc.CN t))) : G) := by
      simp [pow_two]
    rw [hsq]
    refine hker _ fun x hx => ?_
    obtain ⟨f, hf⟩ := hcomm x hx
    have h1 : f (⟨a, ha⟩ * ⟨a, ha⟩) = 1 := by
      rw [map_mul, hf, ← ofAdd_add]
      have : secVec ψ ⟨⁅a, x⁆, e.comm_mem_V h34 ha hx⟩ + secVec ψ ⟨⁅a, x⁆, e.comm_mem_V h34 ha hx⟩
          = 0 := by
        ext i
        exact CharTwo.add_self_eq_zero _
      rw [this]
      rfl
    rw [hf] at h1
    exact toAdd_eq_zero.mpr h1

theorem Env.exists_hypPlane (I : Inputs) (e : Env hc n t m X) :
    (SpNat hc t ∨ OmegaNat hc t) ∧
      ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t := by
  rcases e.hΩ with hP | hM
  · exact exists_hypPlane_omegaPlus I.h34 I.hRoot hc e.hs.toSec5 e.hm hP
  · exact exists_hypPlane_omegaMinus I.h34 I.hRoot hc e.hs.toSec5 (by have := e.hm; omega) hM

theorem Env.CN_eq_LB_inf (I : Inputs) (e : Env hc n t m X) :
    ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t ∧
      LB M Q B ⊓ LB M Q (conjSubgroup r B) = hc.CN t := by
  obtain ⟨hnatSO, r, hr, hplane⟩ := e.exists_hypPlane I
  obtain ⟨-, hcard, -, hopp⟩ := I.h51 G M Q Z B hc n t e.hs.toSec5 hnatSO r hr hplane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
    rfl rfl rfl rfl rfl
  exact ⟨r, hr, hplane, Subgroup.eq_of_le_of_card_ge (hopp.1.trans hopp.2.1)
    (by rw [hcard, e.hs.cardN])⟩

theorem Env.N_le_LB (I : Inputs) (e : Env hc n t m X) : hc.CN t ≤ LB M Q B := by
  obtain ⟨r, -, -, h⟩ := e.CN_eq_LB_inf I
  rw [← h]
  exact inf_le_left

theorem Env.N_central (h34 : Stroth34Statement) (e : Env hc n t m X) :
    ∀ s ∈ Rt M (LB M Q B) t, ∀ a ∈ hc.CN t, ⁅s, a⁆ ∈ Q := by
  intro s hs a ha
  have hXn : X ≤ Subgroup.normalizer (hc.CN t : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    exact hc.CN_conj_mem e.hs.toSec5.mem (e.hXR hx) hy
  have hs' : s ∈ X ⊔ hc.CN t := by rw [sup_comm, e.hNX]; exact hs
  obtain ⟨x, hx, n', hn', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hXn hs'
  have hid : ⁅x * n', a⁆ = x * ⁅n', a⁆ * x⁻¹ * ⁅x, a⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  have hxM : x ∈ M := hc.Rt_le_M t (e.hXR hx)
  refine Q.mul_mem ?_ ?_
  · exact (hc.conj_mem_Q_of_mem_M hxM).1 _ ((e.N_mod_Q h34).1 n' hn' a ha)
  · have h := e.hcen a ha x hx
    have : ⁅x, a⁆ = ⁅a, x⁆⁻¹ := (commutatorElement_inv a x).symm
    rw [this]
    exact Q.inv_mem h

theorem Env.X_le_normalizer_CN (e : Env hc n t m X) :
    X ≤ Subgroup.normalizer (hc.CN t : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  exact hc.CN_conj_mem e.hs.toSec5.mem (e.hXR hx) hy

theorem Env.LB_decomp (I : Inputs) (e : Env hc n t m X) {l : G} (hl : l ∈ LB M Q B) :
    ∃ x ∈ X, x ∈ LB M Q B ∧ ∃ a ∈ hc.CN t, l = x * a := by
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) e.hs.toSec5.mem hl
  have hl' : l ∈ X ⊔ hc.CN t := by rw [sup_comm, e.hNX]; exact hlR
  obtain ⟨x, hx, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer e.X_le_normalizer_CN hl'
  refine ⟨x, hx, ?_, a, ha, rfl⟩
  have : x = (x * a) * a⁻¹ := by group
  rw [this]
  exact (LB M Q B).mul_mem hl ((LB M Q B).inv_mem (e.N_le_LB I ha))

theorem Env.Nt_eq (I : Inputs) (e : Env hc n t m X) :
    Nt M (LB M Q B) t = hc.CN t :=
  I.hNt G M Q Z B hc n e.hs.toSec5.width e.hs.toSec5.n_gt e.hs.toSec5.noA2 e.hs.toSec5.gen t
    e.hs.toSec5.mem e.hs.toSec5.notQ

end Derived

end HS6

end CFSG.RankThree.GF2n.Stroth80
