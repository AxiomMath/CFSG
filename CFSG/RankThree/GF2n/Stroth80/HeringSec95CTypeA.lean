module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CPts
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CEich
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def CentMod (Z S : Subgroup G) (hS : S ≤ Subgroup.normalizer (Z : Set G)) (x : G) :
    Subgroup G where
  carrier := {a | a ∈ S ∧ ⁅x, a⁆ ∈ Z}
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨S.mul_mem ha hb, ?_⟩
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem hax ((Subgroup.mem_normalizer_iff.mp (hS ha) _).mp hbx)
  one_mem' := ⟨S.one_mem, by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨S.inv_mem ha, ?_⟩
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hS (S.inv_mem ha)) _).mp (Z.inv_mem hax)
    simpa [mul_assoc] using this

theorem mem_CentMod {Z S : Subgroup G} {hS : S ≤ Subgroup.normalizer (Z : Set G)} {x a : G} :
    a ∈ CentMod Z S hS x ↔ a ∈ S ∧ ⁅x, a⁆ ∈ Z := Iff.rfl

structure Coord95 (hc : Ctx M Q Z B) (t : G) (K : Type) [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal] where
  E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))
  φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K
  ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (Fin 2 ⊕ Fin 2 → K)
  u : Fin 2 ⊕ Fin 2 → K
  hK : Nat.card K = Nat.card Z
  hφ : φ.range = StatedOmega (StatedQuadPlus 2 K)
  hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)
  hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
    (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  hQu : quadPlus 2 K u = 0
  hu0 : u ≠ 0
  hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
    (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u
  hW : ∀ x : Fin 2 ⊕ Fin 2 → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
    (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ polar (quadPlus 2 K) u x = 0
  hLB : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u

theorem exists_coord95 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal), Nonempty (Coord95 hc t K) := by
  obtain ⟨K, fK, finK, hK2, E, hnrm, φ, ψ, u, hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, -, hLB,
    -⟩ := exists_points95 h34 hs hr
  exact ⟨K, fK, finK, hK2, hnrm,
    ⟨⟨E, φ, ψ, u, hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, hLB⟩⟩⟩

theorem Vt_le_normalizer (hc : Ctx M Q Z B) (t : G) :
    Vt M (LB M Q B) B Z t ≤ Subgroup.normalizer (Z : Set G) := fun v hv =>
  hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Vt_le_Q t hv))

section PlaneFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.plane_facts {hc : Ctx M Q Z B} {n : ℕ} (C : Coord95 hc t K)
    (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) :
    ∃ w : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) C.u w = 0 ∧ (∀ c : K, w ≠ c • C.u) ∧
      (∀ v, (C.φ ⟨x, le_Rt (M := M) (LB M Q B) hs.mem hxL⟩ :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = eichler (quadPlus 2 K) C.u w v) ∧
      Nat.card ↥(⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) =
        Nat.card Z ^ 3 ∧
      (∀ s ∈ (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G),
        ∃ hsV : s ∈ Vt M (LB M Q B) B Z t, ∃ a b : K,
          secVec C.ψ ⟨s, hsV⟩ = a • C.u + b • w) ∧
      Nat.card ↥(CentMod Z (Vt M (LB M Q B) B Z t) (Vt_le_normalizer hc t) x) =
        Nat.card Z ^ 3 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  set xR : ↥(Rt M (LB M Q B) t) := ⟨x, hxR⟩ with hxRdef
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have hmem : C.φ xR ∈ C.E.LomGL C.u := by
    rw [← C.hLB]
    exact Subgroup.mem_map_of_mem C.φ (Subgroup.mem_subgroupOf.mpr hxL)
  obtain ⟨-, w, hw, hEw⟩ := (Om10.mem_LomGL_iff_eichler C.E).mp hmem
  have hind : ∀ c : K, w ≠ c • C.u := by
    intro c hc'
    apply hxN
    have h1 : eichler (quadPlus 2 K) C.u w = 1 := by
      rw [hc', ← zero_add (c • C.u), eichler_add_smul_self C.hQu, eichler_zero_right]
    have h2 : C.φ xR = 1 := by
      refine Units.ext ?_
      rw [Matrix.ext_iff_mulVec]
      intro v
      rw [hEw v, h1]
      simp
    have h3 : xR ∈ C.φ.ker := MonoidHom.mem_ker.mpr h2
    rw [C.hker, Subgroup.mem_subgroupOf] at h3
    exact h3
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      ρ * v * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t := fun ρ hρ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) v).mp hv
  have hVRn : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  have hcomV : ∀ v : ↥(Vt M (LB M Q B) B Z t), ⁅x, (v : G)⁆ ∈ Vt M (LB M Q B) B Z t := fun v =>
    comm_mem_of_le_normalizer hVRn xR v
  have hsec : ∀ v : ↥(Vt M (LB M Q B) B Z t),
      secVec C.ψ ⟨⁅x, (v : G)⁆, hcomV v⟩ =
        eichler (quadPlus 2 K) C.u w (secVec C.ψ v) - secVec C.ψ v := by
    intro v
    have h1 := secVec_comm C.φ C.ψ C.hψ hVRn xR v
    rw [hEw] at h1
    exact h1
  let f : K × K → (Fin 2 ⊕ Fin 2 → K) := fun p => p.1 • C.u + p.2 • w
  have hfinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f] at h
    have h0 : (b - b') • w = (a' - a) • C.u := by
      have h' := sub_eq_zero.mpr h
      have : (b - b') • w - (a' - a) • C.u = a • C.u + b • w - (a' • C.u + b' • w) := by module
      rw [h'] at this
      exact sub_eq_zero.mp this
    have hbb : b = b' := by
      by_contra hne
      apply hind ((b - b')⁻¹ * (a' - a))
      have := congrArg (fun z => (b - b')⁻¹ • z) h0
      simp only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
      exact this
    subst hbb
    have h1 : (a' - a) • C.u = 0 := by rw [← h0, sub_self, zero_smul]
    have h2 : a' - a = 0 := (smul_eq_zero.mp h1).resolve_right C.hu0
    have : a = a' := (sub_eq_zero.mp h2).symm
    rw [this]
  let T : Set (Fin 2 ⊕ Fin 2 → K) := Set.range f
  have hTcard : Nat.card T = Nat.card K ^ 2 := by
    rw [Nat.card_range_of_injective hfinj, Nat.card_prod, _root_.sq]
  have hT0 : (0 : Fin 2 ⊕ Fin 2 → K) ∈ T := ⟨(0, 0), by simp [f]⟩
  have hTadd : ∀ s₁ ∈ T, ∀ s₂ ∈ T, s₁ + s₂ ∈ T := by
    rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨⟨a', b'⟩, rfl⟩
    exact ⟨(a + a', b + b'), by simp only [f]; module⟩
  have hTneg : ∀ s ∈ T, -s ∈ T := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨(-a, -b), by simp only [f]; module⟩
  have hTchar : ∀ p, p ∈ T ↔ ∃ y, eichler (quadPlus 2 K) C.u w y - y = p := by
    intro p
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact exists_eichler_sub_eq' hQnd C.hQu hw C.hu0 hind a b
    · rintro ⟨y, rfl⟩
      obtain ⟨a, b, hab⟩ := eichler_sub_mem' C.hQu hw y
      exact ⟨(a, b), hab.symm⟩
  set S : Subgroup G := ⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z with hS
  have hSV : S ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le ?_ hZV
    rw [Subgroup.commutator_le]
    intro v hv y hy
    have hyR : y ∈ Rt M (LB M Q B) t := (Subgroup.zpowers_le.mpr hxR) hy
    have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem hv (hVR y hyR _ ((Vt M (LB M Q B) B Z t).inv_mem hv))
  have hsqx : C.φ xR * C.φ xR = 1 := by
    have hxx : xR * xR ∈ C.φ.ker := by
      rw [C.hker, Subgroup.mem_subgroupOf]
      show x * x ∈ hc.CN t
      rw [← pow_two]
      exact hc.Q_le_CN ht (hc.sq_mem_Q_of_mem_LB hxL)
    rw [← map_mul]
    exact MonoidHom.mem_ker.mp hxx
  have hsq2 : C.φ xR ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hsqx
  have hpow : ∀ k : ℤ, C.φ xR ^ k = 1 ∨ C.φ xR ^ k = C.φ xR := by
    intro k
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hsq2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, hsq2, one_zpow, one_mul]
  let Pg : Subgroup G :=
    { carrier := {y | ∃ hy : y ∈ Vt M (LB M Q B) B Z t, secVec C.ψ ⟨y, hy⟩ ∈ T}
      mul_mem' := by
        rintro a b ⟨ha, hsa⟩ ⟨hb, hsb⟩
        refine ⟨(Vt M (LB M Q B) B Z t).mul_mem ha hb, ?_⟩
        have : secVec C.ψ (⟨a * b, (Vt M (LB M Q B) B Z t).mul_mem ha hb⟩ :
            ↥(Vt M (LB M Q B) B Z t)) = secVec C.ψ ⟨a, ha⟩ + secVec C.ψ ⟨b, hb⟩ :=
          secVec_mul C.ψ ⟨a, ha⟩ ⟨b, hb⟩
        rw [this]
        exact hTadd _ hsa _ hsb
      one_mem' := by
        refine ⟨(Vt M (LB M Q B) B Z t).one_mem, ?_⟩
        have : secVec C.ψ (⟨1, (Vt M (LB M Q B) B Z t).one_mem⟩ :
            ↥(Vt M (LB M Q B) B Z t)) = 0 :=
          (secVec_eq_zero_iff C.ψ _).mpr Z.one_mem
        rw [this]
        exact hT0
      inv_mem' := by
        rintro a ⟨ha, hsa⟩
        refine ⟨(Vt M (LB M Q B) B Z t).inv_mem ha, ?_⟩
        have : secVec C.ψ (⟨a⁻¹, (Vt M (LB M Q B) B Z t).inv_mem ha⟩ :
            ↥(Vt M (LB M Q B) B Z t)) = -secVec C.ψ ⟨a, ha⟩ := secVec_inv C.ψ ⟨a, ha⟩
        rw [this]
        exact hTneg _ hsa }
  have hPg : ∀ y, y ∈ Pg ↔ ∃ hy : y ∈ Vt M (LB M Q B) B Z t, secVec C.ψ ⟨y, hy⟩ ∈ T :=
    fun y => Iff.rfl
  have hSPg : S ≤ Pg := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro v hv y hy
      have hyR : y ∈ Rt M (LB M Q B) t := (Subgroup.zpowers_le.mpr hxR) hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyV : ⁅v, x ^ k⁆ ∈ Vt M (LB M Q B) B Z t := by
        have e : ⁅v, x ^ k⁆ = v * (x ^ k * v⁻¹ * (x ^ k)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Vt M (LB M Q B) B Z t).mul_mem hv
          (hVR _ hyR _ ((Vt M (LB M Q B) B Z t).inv_mem hv))
      refine ⟨hyV, ?_⟩
      set yR : ↥(Rt M (LB M Q B) t) := ⟨x ^ k, hyR⟩ with hyRdef
      have hcom := secVec_comm C.φ C.ψ C.hψ hVRn yR ⟨v, hv⟩
      have hinv : (⟨⁅v, x ^ k⁆, hyV⟩ : ↥(Vt M (LB M Q B) B Z t)) =
          (⟨⁅(yR : G), v⁆, comm_mem_of_le_normalizer hVRn yR ⟨v, hv⟩⟩ :
            ↥(Vt M (LB M Q B) B Z t))⁻¹ := by
        apply Subtype.ext
        show ⁅v, x ^ k⁆ = ⁅(x ^ k : G), v⁆⁻¹
        rw [commutatorElement_inv]
      rw [hinv, secVec_inv, hcom]
      have hφy : C.φ yR = 1 ∨ C.φ yR = C.φ xR := by
        have : yR = xR ^ k := Subtype.ext (by simp [hyRdef, xR])
        rw [this, map_zpow]
        exact hpow k
      rcases hφy with h1 | h1
      · rw [h1]
        simpa using hT0
      · rw [h1, hEw]
        obtain ⟨a, b, hab⟩ := eichler_sub_mem' C.hQu hw (secVec C.ψ ⟨v, hv⟩)
        rw [hab]
        exact hTneg _ ⟨(a, b), rfl⟩
    · intro z hz
      refine ⟨hZV hz, ?_⟩
      have : secVec C.ψ (⟨z, hZV hz⟩ : ↥(Vt M (LB M Q B) B Z t)) = 0 :=
        (secVec_eq_zero_iff C.ψ _).mpr hz
      rw [this]
      exact hT0
  let g : ↥S →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    (C.ψ.toMonoidHom.comp
      (QuotientGroup.mk' (Z.subgroupOf (Vt M (LB M Q B) B Z t)))).comp (Subgroup.inclusion hSV)
  have hg : ∀ s : ↥S, g s = Multiplicative.ofAdd (secVec C.ψ ⟨s, hSV s.2⟩) := fun s => rfl
  have hZS : Z ≤ S := le_sup_right
  have hkerg : g.ker = Z.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, hg, ofAdd_eq_one, secVec_eq_zero_iff, Subgroup.mem_subgroupOf]
  have hkerCard : Nat.card g.ker = Nat.card Z := by
    rw [hkerg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv
  have hrange : (g.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) =
      Multiplicative.ofAdd '' T := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨hy, hT⟩ := (hPg _).mp (hSPg s.2)
      exact ⟨secVec C.ψ ⟨s, hSV s.2⟩, hT, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, hy⟩ := (hTchar q).mp hq
      obtain ⟨v, hv⟩ := exists_secVec_eq C.ψ y
      have hcv : ⁅x, (v : G)⁆ ∈ S := by
        have h1 : ⁅(v : G), x⁆ ∈ ⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ :=
          Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers x)
        have h2 : ⁅x, (v : G)⁆ = ⁅(v : G), x⁆⁻¹ := (commutatorElement_inv _ _).symm
        rw [h2]
        exact S.inv_mem (Subgroup.mem_sup_left h1)
      refine ⟨⟨⁅x, (v : G)⁆, hcv⟩, ?_⟩
      have h3 : secVec C.ψ ⟨⁅x, (v : G)⁆, hcomV v⟩ =
          eichler (quadPlus 2 K) C.u w y - y := by
        rw [hsec v, hv]
      show Multiplicative.ofAdd (secVec C.ψ ⟨⁅x, (v : G)⁆, hSV hcv⟩) = Multiplicative.ofAdd q
      congr 1
      exact h3.trans hy
  have hcardR : Nat.card g.range = Nat.card K ^ 2 := by
    calc Nat.card g.range
        = Nat.card (g.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) := rfl
      _ = Nat.card (Multiplicative.ofAdd '' T) := by rw [hrange]
      _ = Nat.card T := Nat.card_image_of_injective Multiplicative.ofAdd.injective T
      _ = Nat.card K ^ 2 := hTcard
  have hmul := Subgroup.card_ker_mul_card_range g
  rw [hkerCard, hcardR, C.hK] at hmul
  have hVN := Vt_le_normalizer hc t
  let gV : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd
        (eichler (quadPlus 2 K) C.u w (secVec C.ψ v) - secVec C.ψ v)
      map_one' := by
        have h0 : secVec C.ψ (1 : ↥(Vt M (LB M Q B) B Z t)) = 0 :=
          (secVec_eq_zero_iff C.ψ _).mpr Z.one_mem
        rw [h0, map_zero, sub_zero]
        rfl
      map_mul' := fun a b => by
        rw [secVec_mul, map_add, ← ofAdd_add]
        congr 1
        abel }
  have hgV : ∀ v, gV v = Multiplicative.ofAdd
      (eichler (quadPlus 2 K) C.u w (secVec C.ψ v) - secVec C.ψ v) := fun v => rfl
  have hkerV : gV.ker = (CentMod Z (Vt M (LB M Q B) B Z t) hVN x).subgroupOf
      (Vt M (LB M Q B) B Z t) := by
    ext v
    rw [MonoidHom.mem_ker, hgV, ofAdd_eq_one, Subgroup.mem_subgroupOf, mem_CentMod, ← hsec v,
      secVec_eq_zero_iff]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hrangeV : (gV.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) =
      Multiplicative.ofAdd '' T := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, (hTchar _).mpr ⟨_, rfl⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, hy⟩ := (hTchar q).mp hq
      obtain ⟨v, hv⟩ := exists_secVec_eq C.ψ y
      refine ⟨v, ?_⟩
      rw [hgV, hv, hy]
  have hcardRV : Nat.card gV.range = Nat.card K ^ 2 := by
    calc Nat.card gV.range
        = Nat.card (gV.range : Set (Multiplicative (Fin 2 ⊕ Fin 2 → K))) := rfl
      _ = Nat.card (Multiplicative.ofAdd '' T) := by rw [hrangeV]
      _ = Nat.card T := Nat.card_image_of_injective Multiplicative.ofAdd.injective T
      _ = Nat.card K ^ 2 := hTcard
  have hmulV := Subgroup.card_ker_mul_card_range gV
  have hCVle : CentMod Z (Vt M (LB M Q B) B Z t) hVN x ≤ Vt M (LB M Q B) B Z t :=
    fun a ha => (mem_CentMod.mp ha).1
  have hCV : Nat.card ↥(CentMod Z (Vt M (LB M Q B) B Z t) hVN x) = Nat.card gV.ker := by
    rw [hkerV]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCVle).toEquiv).symm
  refine ⟨w, hw, hind, hEw, ?_, ?_, ?_⟩
  · rw [← hmul]
    ring
  · intro s hs'
    obtain ⟨hy, hT⟩ := (hPg _).mp (hSPg hs')
    obtain ⟨⟨a, b⟩, hab⟩ := hT
    exact ⟨hy, a, b, hab.symm⟩
  · have h5 := hs.card_V
    rw [hCV]
    rw [hcardRV, C.hK, h5] at hmulV
    have hq : 0 < Nat.card Z ^ 2 := pow_pos Nat.card_pos 2
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [hmulV, ← pow_add]

theorem typeA2_of_polar_zero {hc : Ctx M Q Z B} {n : ℕ} (C : Coord95 hc t K)
    (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t)
    (hz : ∀ v : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) v
      ((C.φ ⟨x, le_Rt (M := M) (LB M Q B) hs.mem hxL⟩ :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = 0) :
    IsTypeA2 M Q Z B t x := by
  classical
  obtain ⟨w, hw, hind, hEw, hcard, -, -⟩ := C.plane_facts hs hxL hxN
  refine ⟨hcard, ?_⟩
  have ht : t ∈ LB M Q B := hs.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  set xR : ↥(Rt M (LB M Q B) t) := ⟨x, hxR⟩ with hxRdef
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have hQw : quadPlus 2 K w = 0 := by
    obtain ⟨v₀, hv₀⟩ := exists_polar_ne_zero hQnd C.hu0
    have h1 := hz v₀
    rw [hEw v₀, polar_eichler_self_char2 C.hQu hw] at h1
    exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero 2 hv₀)
  have hVR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      ρ * v * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t := fun ρ hρ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) v).mp hv
  have hVRn : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  have hcomV : ∀ v : ↥(Vt M (LB M Q B) B Z t), ⁅x, (v : G)⁆ ∈ Vt M (LB M Q B) B Z t := fun v =>
    comm_mem_of_le_normalizer hVRn xR v
  have hsec : ∀ v : ↥(Vt M (LB M Q B) B Z t),
      secVec C.ψ ⟨⁅x, (v : G)⁆, hcomV v⟩ =
        eichler (quadPlus 2 K) C.u w (secVec C.ψ v) - secVec C.ψ v := by
    intro v
    have h1 := secVec_comm C.φ C.ψ C.hψ hVRn xR v
    rw [hEw] at h1
    exact h1
  intro v hv
  have hs' := hsec ⟨v, hv⟩
  have hQs' : quadPlus 2 K (secVec C.ψ ⟨⁅x, v⁆, hcomV ⟨v, hv⟩⟩) = 0 := by
    rw [hs']
    obtain ⟨a, b, hab⟩ := eichler_sub_mem C.hQu hw hQw (secVec C.ψ ⟨v, hv⟩)
    rw [hab]
    exact map_comb_eq_zero C.hQu hw hQw a b
  by_cases hz0 : secVec C.ψ ⟨⁅x, v⁆, hcomV ⟨v, hv⟩⟩ = 0
  · refine ⟨1, (Rt M (LB M Q B) t).one_mem, 1, B.one_mem, ?_⟩
    have := (secVec_eq_zero_iff C.ψ _).mp hz0
    simpa using this
  · obtain ⟨A, hA, hAu⟩ := C.E.exists_mulVec_eq hQnd (P := plusPair K 0) (P' := plusPair K 1)
      (plusPair_orth (by decide)) C.hu0 hz0 (by rw [C.hQu, hQs'])
    obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp (C.hφ ▸ hA)
    obtain ⟨b, hbB, hbs⟩ := (C.hBiff C.u).mpr ⟨1, (one_smul K C.u).symm⟩
    refine ⟨ρ, ρ.2, b, hbB, ?_⟩
    have hbV : (b : G) ∈ Vt M (LB M Q B) B Z t := b.2
    have hb' : secVec C.ψ ⟨(ρ : G) * b * (ρ : G)⁻¹, hVR ρ ρ.2 b hbV⟩ =
        (C.φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ b :=
      C.hψ ρ b ⟨(ρ : G) * b * (ρ : G)⁻¹, hVR ρ ρ.2 b hbV⟩ rfl
    rw [hρ, hbs, hAu] at hb'
    have hsame : secVec C.ψ ⟨⁅x, v⁆, hcomV ⟨v, hv⟩⟩ =
        secVec C.ψ ⟨(ρ : G) * b * (ρ : G)⁻¹, hVR ρ ρ.2 b hbV⟩ := hb'.symm
    exact (secVec_eq_iff C.ψ _ _).mp hsame

end PlaneFacts

end HS9

end CFSG.RankThree.GF2n.Stroth80
