module

public import CFSG.Quasithin.MS93.S45Cen
public import CFSG.Quasithin.MS93.S45Phi3
public import CFSG.Quasithin.MS93.S45Q4PD

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem whv_smul_smul {M T L : Subgroup G} (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (δ μ : Vtx (puAmalgam h.le)) :
    whv h (g • δ) (g • μ) = (whv h δ μ).map (MulAut.conj g).toMonoidHom := by
  rw [whv, whv, conjCl_map_conj, Subgroup.map_sup, ← vcirc_smul h, ← zm_smul, ← stab_smul]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem vsix_eq_of_smul {α γ : Vtx (puAmalgam c.hyp.le)} {g : (puAmalgam c.hyp.le).Universal}
    (hg : g ∈ stab (puAmalgam c.hyp.le) α) :
    conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp (g • γ) α) =
      conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α) := by
  have hgα : g • α = α := (mem_stab _).mp hg
  have e : whv c.hyp (g • γ) α = (whv c.hyp γ α).map (MulAut.conj g).toMonoidHom := by
    rw [← whv_smul_smul c.hyp g γ α, hgα]
  rw [e, conjCl_map_conj_of_mem hg]

theorem exists_deep_isGoodPath {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) (K : ℕ) :
    ∃ (q : ℕ → Vtx (puAmalgam c.hyp.le)) (Nq b : ℕ), IsGoodPath _ q Nq ∧ Even b ∧ K ≤ b ∧
      b + K ≤ Nq ∧ Even Nq ∧ q b = p a := by
  obtain ⟨u, hu⟩ := ha
  have hp₀ : IsGoodPath _ p (a + 30) := hp.mono haN
  obtain ⟨p₁, hp₁e, hp₁⟩ := c.exists_extend hp₀ (by omega) ⟨u + 15, by omega⟩ (K + 10)
  set m := a + 30 + 2 * (K + 10) - 2 with hm
  have hr := c.isGoodPath_rev hp₁ (m := m) ⟨u + K + 24, by omega⟩ (by omega) (by omega)
  obtain ⟨r₁, hr₁e, hr₁⟩ := c.exists_extend hr (by omega) ⟨u + K + 18, by omega⟩ (K + 10)
  set m' := m - 12 + 2 * (K + 10) - 2 with hm'
  have hq := c.isGoodPath_rev hr₁ (m := m') ⟨u + 2 * K + 27, by omega⟩ (by omega) (by omega)
  refine ⟨fun i => r₁ (m' - i), m' - 12, m' - (m - a), hq, ⟨u + K + 3, by omega⟩, by omega,
    by omega, ⟨u + 2 * K + 21, by omega⟩, ?_⟩
  show r₁ (m' - (m' - (m - a))) = p a
  rw [show m' - (m' - (m - a)) = m - a by omega, hr₁e (m - a) (by omega)]
  show p₁ (m - (m - a)) = p a
  rw [show m - (m - a) = a by omega, hp₁e a (by omega)]

theorem top_data (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) {α γ μ ν : Vtx (puAmalgam c.hyp.le)} (hα : p a = α)
    (hγ : p (a + 2) = γ) (hμ : p (a + 4) = μ) (hν : p (a + 6) = ν)
    {ψ : ↥(stab (puAmalgam c.hyp.le) α) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.hyp.le L α) ⊥ ψ false 1) :
    conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ ≤
        conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α) ∧
      ⁅conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ,
          Qv (puAmalgam c.hyp.le) α⁆ ≤ whv c.hyp α γ ∧
      IsSumOfNaturalModulesVia (stab _ α)
        (⁅conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ,
          stab (puAmalgam c.hyp.le) α⁆ ⊔ whv c.hyp α γ) (whv c.hyp α γ) ψ false 1 ∧
      IsC1 c.hyp.le L (Fintype.card F) α
        (conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ)
        (whv c.hyp α γ) ∧
      ⁅conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ,
          stab (puAmalgam c.hyp.le) α⁆ ⊔ whv c.hyp α γ ≤
        ⁅Qv (puAmalgam c.hyp.le) α, Ltil c.hyp.le L α⁆ ⊔ whv c.hyp α γ ∧
      ⁅Qv (puAmalgam c.hyp.le) α, Ltil c.hyp.le L α⁆ ≤
        conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α) ∧
      ZM (puAmalgam c.hyp.le) ν ≤
        conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ ∧
      ⁅conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α),
          conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α)⁆ ≤
        Vcirc c.hyp.le L α ⊔ ZM _ α ∧
      conjCl (stab (puAmalgam c.hyp.le) α) (whv c.hyp γ α) ≤ Qv (puAmalgam c.hyp.le) α ∧
      ⁅whv c.hyp α γ, Qv (puAmalgam c.hyp.le) α⁆ ≤ ZM _ α := by
  subst hα hγ hμ hν
  have h := c.hyp
  have hQ4 := S45Q4.hQ4 c
  have hαM := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  obtain ⟨p', hp', hpp', -, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hvsix := c.top_le_vsix hZV hp hp' ha (by omega) (by omega) hpp'
  have hV := c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3
  have hd2 : (puAmalgam h.le).treeGraph.dist (p (a + 2)) (p a) = 2 := by
    rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  have hDQ : conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) ≤
      Qv (puAmalgam h.le) (p a) :=
    conjCl_le_of_le_normalizer (c.whv_le_qv_of_dist hαM hd2 (by omega))
      (stab_le_normalizer_qv _ _)
  have h6 := c.zm_le_vhat_right hZV hp (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
  rw [show a + 4 + 2 = a + 6 by omega] at h6
  refine ⟨le_sup_left.trans hvsix, c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega),
    c.top_isSum h14 hSQ hZV hQ4 hp ha h34 haN hψs hψ, c.isC1_top h14 hSQ hZV hQ4 hp ha h34 haN,
    ?_, hV.trans hvsix, h6.trans ((S4A.le_conjCl _ _).trans le_sup_left),
    c.commutator_vsix_le_vhat h14 hSQ hZV hQ4 hp ha h34 haN, hDQ,
    c.commutator_whv_qv_le' hZV hp ha (by omega) (by omega)⟩
  rw [c.sup_whv_eq hZV hQ4 hp hp' ha h34 haN hpp' hU3]
  exact le_sup_left

end Ctx

end CFSG.Quasithin.MS93.S45R
