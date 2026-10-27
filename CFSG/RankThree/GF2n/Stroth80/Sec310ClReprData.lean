module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClCommForm
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClRepr
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure ReprData (V R N : Subgroup G) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V) (t : G) where
  F : LinearMap.BilinForm K ↥(imgSub M₀ V hS)
  ρ : ↥R →* (↥(imgSub M₀ V hS) ≃ₗ[K] ↥(imgSub M₀ V hS))
  nondeg : F.Nondegenerate
  alt : F.IsAlt
  ρ_apply : ∀ (r : ↥R) (S : M₀.E ≃ₗ[K] M₀.E),
    (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
    ∀ w : ↥(imgSub M₀ V hS), ∃ hw : S (w : M₀.E) ∈ imgSub M₀ V hS, ρ r w = ⟨S (w : M₀.E), hw⟩
  form : ∀ (S : M₀.E ≃ₗ[K] M₀.E), (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = S (M₀.π x)) →
    ∀ (w w' : ↥(imgSub M₀ V hS)) (x : M₀.E), S x - x = (w' : M₀.E) →
      F w w' = M₀.B (w : M₀.E) x
  onto : ∀ (S : M₀.E ≃ₗ[K] M₀.E), (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = S (M₀.π x)) →
    ∀ w : ↥(imgSub M₀ V hS), ∃ x : M₀.E, S x - x = (w : M₀.E)
  ker : ρ.ker = N.subgroupOf R
  isom : ∀ r, Classify.IsIsom F (ρ r)
  sec : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K ↥(imgSub M₀ V hS)),
    ∃ φ : ↥R →* GL ι K, (∀ r, φ r = b.toGL (ρ r)) ∧ φ.ker = N.subgroupOf R ∧
      SectionAct K R V Z φ (fun g => (g : Matrix ι ι K))

theorem Ctx.exists_reprData (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    Nonempty (ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t) := by
  classical
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  obtain ⟨F, hnd, halt, hinv, hform, honto⟩ := hc.exists_comm_form' h35 hs.mem hs.notQ hnot h hS
  obtain ⟨ρ, hρ, hker, hsec⟩ := exists_repr_of_subspace hc.hyp (hc.Vt_le_Q t) (hc.Rt_le_H0 t)
    (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) h hS
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  refine ⟨⟨F, ρ, hnd, halt, hρ, hform, honto, hker, fun r w w' => ?_, hsec⟩⟩
  have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 t r.2
  obtain ⟨hw, hρw⟩ := hρ r (φ₀ ⟨r, hrH⟩) (fun x hx => hφπ ⟨r, hrH⟩ x hx) w
  obtain ⟨hw', hρw'⟩ := hρ r (φ₀ ⟨r, hrH⟩) (fun x hx => hφπ ⟨r, hrH⟩ x hx) w'
  rw [hρw, hρw']
  exact hinv r (φ₀ ⟨r, hrH⟩) (fun x hx => hφπ ⟨r, hrH⟩ x hx) w w' hw hw'

end CFSG.RankThree.GF2n.Stroth80
