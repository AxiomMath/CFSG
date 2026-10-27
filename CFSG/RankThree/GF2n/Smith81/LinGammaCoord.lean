module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem LinSetup.exists_subspaces {n : ℕ} {V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hn : 3 ≤ n)
    (hS : LinSetup M Q Z B n V₁ V₂) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    ∃ W₁ W₂ : Submodule K M₀.E, (∀ e, e ∈ W₁ ↔ e ∈ M₀.img V₁) ∧
      ∀ e, e ∈ W₂ ↔ e ∈ M₀.img V₂ := by
  obtain ⟨F, hFfield, hFfin, hFcard, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φ, hΦ, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ'
    hn hrange (by rw [h.card, hFcard]) Φ hΦ
  subst hCΦ
  refine ⟨{ carrier := {e | (C.Ψ e).2 = 0}
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, map_add, Prod.snd_add] at *
              rw [ha, hb, add_zero]
            zero_mem' := by simp
            smul_mem' := fun c e he => by
              simp only [Set.mem_setOf_eq] at *
              rw [C.smul, he, smul_zero] },
    { carrier := {e | (C.Ψ e).1 = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, Prod.fst_add] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c e he => by
        simp only [Set.mem_setOf_eq] at *
        rw [C.smul, he, smul_zero] }, fun e => (hΦ₁ e).symm, fun e => (hΦ₂ e).symm⟩

section Model

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {x : G}

theorem card_commSup_section (A : XAct M₀ x) (H : StrothHyp M Q Z) (hxM : x ∈ M)
    (hx2 : x * x = 1) {V : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ Q)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (W : Submodule K M₀.E)
    (hW : ∀ e, e ∈ W ↔ e ∈ M₀.img V) :
    Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊔ Z) =
      Nat.card Z * Nat.card ↥(W.map ((A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id)) := by
  set N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id with hNdef
  have hNapp : ∀ f, N f = A.T f - f := fun f => rfl
  have hZQ : Z ≤ Q := hZV.trans hVQ
  have hcommV : ∀ v ∈ V, ⁅v, x⁆ ∈ V := fun v hv => by
    have e : ⁅v, x⁆ = v * (x * v * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hv (V.inv_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv))
  set S : Subgroup G := ⁅V, Subgroup.zpowers x⁆ ⊔ Z with hSdef
  have hSV : S ≤ V := by
    refine sup_le ?_ hZV
    rw [commutator_zpowers_eq_closure hx2, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    exact hcommV v hv
  have hSQ : S ≤ Q := hSV.trans hVQ
  have hZS : Z ≤ S := le_sup_right
  have hST : S ≤ preimageSub M₀ (W.map N) := by
    refine sup_le ?_ ?_
    · rw [commutator_zpowers_eq_closure hx2, Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      refine mem_preimageSub.mpr ⟨hVQ (hcommV v hv), ?_⟩
      rw [A.pi_comm H hxM (hVQ hv)]
      refine ⟨-(M₀.π v), W.neg_mem ((hW _).mpr (M₀.pi_mem_img hv (hVQ hv))), ?_⟩
      rw [hNapp, map_neg]
      abel
    · intro z hz
      exact mem_preimageSub.mpr ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]
        exact Submodule.zero_mem _⟩
  rw [M₀.card_eq hSQ hZS]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
  constructor
  · rintro ⟨y, hyS, hyQ, rfl⟩
    exact (mem_preimageSub.mp (hST hyS)).2
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hvV, hvQ, hvw⟩ := (hW w).mp hw
    have hy : x * v * x⁻¹ * v⁻¹ = (⁅v, x⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hyS : x * v * x⁻¹ * v⁻¹ ∈ S := by
      rw [hy]
      exact S.inv_mem (Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator hvV (Subgroup.mem_zpowers x)))
    refine ⟨x * v * x⁻¹ * v⁻¹, hyS, hSQ hyS, ?_⟩
    rw [M₀.π_mul _ (conj_mem_Q H hxM hvQ) _ (Q.inv_mem hvQ), A.hπ v hvQ,
      Tim79.QuadModel.pi_inv M₀ hvQ, hvw, hNapp, sub_eq_add_neg]

end Model

section Group

variable {V : Subgroup G} {x : G}

theorem gamma_conclusions_of_card {M Q Z : Subgroup G} {m : ℕ} (H : StrothHyp M Q Z)
    (hZV : Z ≤ V) (hVQ : V ≤ Q) (hVsq : ∀ v ∈ V, v * v = 1)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx2 : x * x = 1)
    (hVcard : Nat.card V = Nat.card Z ^ (2 * m + 2))
    (hC : Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Z ^ (m + 2))
    (hdim : HasDimOn V Z m x) :
    ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧ Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
  have hinv : ∀ a ∈ V, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hVsq a ha)
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have h := inv_eq_of_mul_eq_one_right (hVsq (a * b) (V.mul_mem ha hb))
    rw [mul_inv_rev, hinv a ha, hinv b hb] at h
    exact h.symm
  have hcommV : ∀ v ∈ V, ⁅v, x⁆ ∈ V := fun v hv => by
    have e : ⁅v, x⁆ = v * (x * v * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hv (V.inv_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv))
  have key : ∀ a ∈ V, ∀ b ∈ V, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb
    have hcb : ⁅b, x⁆ ∈ V := hcommV b hb
    have e1 : ⁅a * b, x⁆ = a * ⁅b, x⁆ * (x * a⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1, hcomm a ha _ hcb, hcomm _ (hcommV a ha) _ hcb]
    simp only [commutatorElement_def]
    group
  let f : V →* G :=
    { toFun := fun v => ⁅(v : G), x⁆
      map_one' := by simp
      map_mul' := fun a b => key a a.2 b b.2 }
  have hker : f.ker = (V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show ⁅(v : G), x⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have hrange : f.range = ⁅V, Subgroup.zpowers x⁆ := by
    rw [commutator_zpowers_eq_closure hx2]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, v.2, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hkercard : Nat.card f.ker = Nat.card Z ^ (m + 2) := by
    rw [hker, ← hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card V := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hrcard : Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m := by
    rw [← hrange]
    have h1 : Nat.card Z ^ (m + 2) * Nat.card f.range =
        Nat.card Z ^ (m + 2) * Nat.card Z ^ m := by
      have h := hmul
      rw [hkercard, hVcard] at h
      rw [h, ← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hZpos _) h1
  refine ⟨?_, hrcard⟩
  have hDV : ⁅V, Subgroup.zpowers x⁆ ≤ V := by
    rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact hcommV v v.2
  have hZQ : Z ≤ Q := hZV.trans hVQ
  have hZn : Z ≤ Subgroup.normalizer ((⁅V, Subgroup.zpowers x⁆ : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhQ := hVQ (hDV hh)
      rwa [show z * h * z⁻¹ = h by rw [Z_central H hz hhQ]; group]
    · intro hh
      have hhQ' : z * h * z⁻¹ ∈ Q := hVQ (hDV hh)
      have hhQ : h ∈ Q := by
        have := Q.mul_mem (Q.mul_mem (Q.inv_mem (hZQ hz)) hhQ') (hZQ hz)
        rwa [show z⁻¹ * (z * h * z⁻¹) * z = h by group] at this
      rwa [show z * h * z⁻¹ = h by rw [Z_central H hz hhQ]; group] at hh
  have hprod := card_sup_mul_card_inf_of_normalizer hZn
  unfold HasDimOn at hdim
  rw [hdim, hrcard] at hprod
  have h1 : Nat.card Z ^ (m + 1) * Nat.card ↥(⁅V, Subgroup.zpowers x⁆ ⊓ Z) =
      Nat.card Z ^ (m + 1) * 1 := by
    rw [hprod, mul_one]
    ring
  exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_of_mul_eq_mul_left (pow_pos hZpos _) h1)

end Group

end CFSG.RankThree.GF2n.Smith81
