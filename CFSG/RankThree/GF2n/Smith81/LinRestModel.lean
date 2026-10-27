module

public import CFSG.RankThree.GF2n.Smith81.LinTLAbelian
public import CFSG.RankThree.GF2n.Smith81.LinOddAssembly

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

structure RestModel (M Q Z : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G) where
  hyp : StrothHyp M Q Z
  ZV₁ : Z ≤ V₁
  V₁Q : V₁ ≤ Q
  ZV₂ : Z ≤ V₂
  V₂Q : V₂ ≤ Q
  V₁₂ : V₁ ⊓ V₂ = Z
  dec : ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b ∈ V₂, q = a * b
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  γ : G → K
  M₀ : Tim79.QuadModel Q Z K γ
  gm : GlobalModelData M Q Z γ M₀
  φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  φπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
    M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  φker : ∀ m : ↥(H0 M Z), φ m = 1 ↔ (m : G) ∈ Q
  φQf : ∀ (m : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ m e) = M₀.Qf e
  W₁ : Submodule K M₀.E
  W₂ : Submodule K M₀.E
  memW₁ : ∀ e, e ∈ W₁ ↔ e ∈ M₀.img V₁
  memW₂ : ∀ e, e ∈ W₂ ↔ e ∈ M₀.img V₂
  hsup : W₁ ⊔ W₂ = ⊤
  hint : W₁ ⊓ W₂ = ⊥
  iso₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, M₀.B u v = 0
  iso₂ : ∀ u ∈ W₂, ∀ v ∈ W₂, M₀.B u v = 0
  card_W₁ : Nat.card ↥W₁ = Nat.card Z ^ n
  card_W₂ : Nat.card ↥W₂ = Nat.card Z ^ n

attribute [instance] RestModel.instField RestModel.instFinite RestModel.instChar

def subOfSmulRest {K E : Type} [Field K] [AddCommGroup E] [Module K E] (S : AddSubgroup E)
    (hS : ∀ (c : K) {x : E}, x ∈ S → c • x ∈ S) : Submodule K E where
  carrier := (S : Set E)
  add_mem' := fun ha hb => S.add_mem ha hb
  zero_mem' := S.zero_mem
  smul_mem' := fun c {_} hx => hS c hx

section Model

variable [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
  {V₁ V₂ : Subgroup G}

theorem exists_restModel (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    Nonempty (RestModel M Q Z n V₁ V₂) := by
  have hcom₁ : ∀ u ∈ V₁, ∀ v ∈ V₁, u * v = v * u := fun u hu v hv =>
    LinSetup.comm_eq_one_V₁ hc hS hn hu hv
  have hcom₂ : ∀ u ∈ V₂, ∀ v ∈ V₂, u * v = v * u := fun u hu v hv =>
    LinSetup.comm_eq_one_V₂ hc hS hn hu hv
  have hsumQ : ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b' ∈ V₂, q = a * b' := LinSetup.exists_mul hc.hyp hS
  have hS2 := hS
  obtain ⟨F₀, hF₀field, hF₀fin, hF₀card, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS2
  obtain ⟨K, hKf, hKfin, hKch, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφQf⟩ := exists_actionHom_H0 hc.hyp hGM
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φc, hΦc, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [hGM.card, hF₀card]) Φc hΦc
  have hV1 : ∀ e : M₀.E, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0 := fun e => by
    rw [hCΦ]; exact hΦ₁ e
  have hV2 : ∀ e : M₀.E, e ∈ M₀.img V₂ ↔ (C.Ψ e).1 = 0 := fun e => by
    rw [hCΦ]; exact hΦ₂ e
  have hK₁ : ∀ (c : K) {x : M₀.E}, x ∈ M₀.img V₁ → c • x ∈ M₀.img V₁ := by
    intro c x hx
    rw [hV1] at hx ⊢
    rw [C.smul]
    show C.θ₂ c • (C.Ψ x).2 = 0
    rw [hx, smul_zero]
  have hK₂ : ∀ (c : K) {x : M₀.E}, x ∈ M₀.img V₂ → c • x ∈ M₀.img V₂ := by
    intro c x hx
    rw [hV2] at hx ⊢
    rw [C.smul]
    show C.θ₁ c • (C.Ψ x).1 = 0
    rw [hx, smul_zero]
  let W₁ : Submodule K M₀.E := subOfSmulRest (M₀.img V₁) hK₁
  let W₂ : Submodule K M₀.E := subOfSmulRest (M₀.img V₂) hK₂
  have hW₁mem : ∀ x : M₀.E, x ∈ W₁ ↔ x ∈ M₀.img V₁ := fun x => Iff.rfl
  have hW₂mem : ∀ x : M₀.E, x ∈ W₂ ↔ x ∈ M₀.img V₂ := fun x => Iff.rfl
  have hsumE : ∀ e : M₀.E, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, e = w₁ + w₂ := by
    intro e
    obtain ⟨q, hq, rfl⟩ := M₀.π_surj e
    obtain ⟨a, ha, b', hb', rfl⟩ := hsumQ q hq
    exact ⟨M₀.π a, (hW₁mem _).mpr (M₀.pi_mem_img ha (hV₁Q ha)), M₀.π b',
      (hW₂mem _).mpr (M₀.pi_mem_img hb' (hV₂Q hb')), M₀.π_mul a (hV₁Q ha) b' (hV₂Q hb')⟩
  have hcard1 : Nat.card ↥W₁ = Nat.card Z ^ n := by
    have h1 := (hS.basic).2.2.2.2.2.2.2.2.1
    have h2 := M₀.card_eq hV₁Q hZV₁
    rw [h1, pow_succ'] at h2
    have hz : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card ↥(M₀.img V₁) = Nat.card Z ^ n := by
      have := Nat.eq_of_mul_eq_mul_left hz h2.symm
      exact this
    rw [← h3]
    exact Nat.card_congr (Equiv.refl _)
  have hcard2 : Nat.card ↥W₂ = Nat.card Z ^ n := by
    have h1 := (hS.basic).2.2.2.2.2.2.2.2.2
    have h2 := M₀.card_eq hV₂Q hZV₂
    rw [h1, pow_succ'] at h2
    have hz : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card ↥(M₀.img V₂) = Nat.card Z ^ n := by
      have := Nat.eq_of_mul_eq_mul_left hz h2.symm
      exact this
    rw [← h3]
    exact Nat.card_congr (Equiv.refl _)
  refine ⟨{ hyp := hc.hyp
            ZV₁ := hZV₁
            V₁Q := hV₁Q
            ZV₂ := hZV₂
            V₂Q := hV₂Q
            V₁₂ := hinf
            dec := hsumQ
            K := K
            γ := γ
            M₀ := M₀
            gm := hGM
            φ := φ
            φπ := hφπ
            φker := hφQ
            φQf := hφQf
            W₁ := W₁
            W₂ := W₂
            memW₁ := hW₁mem
            memW₂ := hW₂mem
            hsup := ?_
            hint := ?_
            iso₁ := ?_
            iso₂ := ?_
            card_W₁ := hcard1
            card_W₂ := hcard2 }⟩
  · rw [eq_top_iff]
    intro e _
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hsumE e
    exact Submodule.add_mem_sup hw₁ hw₂
  · rw [eq_bot_iff]
    intro e he
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₁mem e).mp he.1
    have hb : M₀.π a ∈ M₀.img V₂ := (hW₂mem _).mp he.2
    have haV₂ : a ∈ V₂ := (M₀.mem_img_iff hZV₂ haQ).mp hb
    have haZ : a ∈ Z := by rw [← hinf]; exact ⟨ha, haV₂⟩
    rw [Submodule.mem_bot]
    exact (M₀.π_ker a haQ).mpr haZ
  · intro x hx y hy
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₁mem x).mp hx
    obtain ⟨a', ha', ha'Q, rfl⟩ := (hW₁mem y).mp hy
    exact (M₀.comm_iff_B hGM.reg haQ ha'Q).mp (hcom₁ a ha a' ha')
  · intro x hx y hy
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₂mem x).mp hx
    obtain ⟨a', ha', ha'Q, rfl⟩ := (hW₂mem y).mp hy
    exact (M₀.comm_iff_B hGM.reg haQ ha'Q).mp (hcom₂ a ha a' ha')

end Model

end CFSG.RankThree.GF2n.Smith81
