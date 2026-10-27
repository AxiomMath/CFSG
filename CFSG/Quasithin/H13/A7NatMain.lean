module

public import CFSG.Quasithin.H13.A7NatFusion
public import CFSG.Quasithin.H13.A7Elimination
public import CFSG.Quasithin.H13.A7NatAssembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def Stmt12_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ

@[expose] def Stmt12_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∀ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) →
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) →
      ∀ e : V, (e : G) ∈ quasithinOmegaOneCenter T → hammingNorm (vec ψ e) = 6 →
        centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G)

@[expose] def Stmt12_3_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∀ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) →
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ) →
      ∀ e : V, (e : G) ∈ quasithinOmegaOneCenter T → hammingNorm (vec ψ e) = 2 →
        centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G)

section Weights

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem centralizer_le_of_conj {x w l : G} (hl : l ∈ normalizer (L : Set G))
    (hw : w = l * x * l⁻¹) (hx : centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({w} : Set G) ≤ normalizer (L : Set G) := by
  intro c hc
  rw [mem_centralizer_singleton_iff] at hc
  have h1 : l⁻¹ * c * l ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hx' : x = l⁻¹ * w * l := by rw [hw]; group
    rw [hx']
    calc l⁻¹ * c * l * (l⁻¹ * w * l) = l⁻¹ * (c * w) * l := by group
      _ = l⁻¹ * (w * c) * l := by rw [hc]
      _ = l⁻¹ * w * l * (l⁻¹ * c * l) := by group
  have h2 := mul_mem (mul_mem hl (hx h1)) (inv_mem hl)
  rwa [show l * (l⁻¹ * c * l) * l⁻¹ = c by group] at h2

theorem A7NatPre.centralizer_le_of_weight (h : A7NatPre T L V ψ)
    {m : ℕ} {x : V} (hxm : hammingNorm (vec ψ x) = m)
    (hxM : centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) {w : V}
    (hwm : hammingNorm (vec ψ w) = m) :
    centralizer ({(w : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨l, hl, hlw⟩ := h.exists_conj_of_weight (u := x) (w := w) (hxm.trans hwm.symm)
  have hLM : L ≤ normalizer (L : Set G) := le_normalizer
  exact centralizer_le_of_conj (hLM hl) hlw hxM

theorem mem_omegaOneCenter_of_central (hVT : V ≤ T) {x : V}
    (hx : (x : G) ∈ centralizer (T : Set G)) (hx2 : (x : G) ^ 2 = 1) :
    (x : G) ∈ quasithinOmegaOneCenter T :=
  Subgroup.subset_closure ⟨⟨hVT x.2, hx⟩, hx2⟩

end Weights

section Weak

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatPre.weight_four_of_mem_conjugate (h331 : Stmt3_3_1) (hyp : Hyp1223 G T L V)
    (h : A7NatPre T L V ψ)
    (wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : CFSG.conjugate V g ≠ V) (v : V) (hv : (v : G) ∈ CFSG.conjugate V g)
    (hv1 : v ≠ 1) : hammingNorm (vec ψ v) = 4 := by
  have hwt := weight_of_mem_evenWeight _ (vec_mem ψ v) (by rwa [ne_eq, vec_eq_zero_iff])
  rcases hwt with h2 | h4 | h6
  rotate_left
  · exact h4
  all_goals
    exfalso
    rw [mem_conjugate_iff_mem] at hv
    set u : V := ⟨g * v * g⁻¹, hv⟩ with hu
    obtain ⟨l, hl, hlu⟩ := h.exists_conj_of_conj h331 hyp (u := v) (w := u) (g := g) rfl
    have hc : l⁻¹ * g ∈ centralizer ({(v : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : g * (v : G) * g⁻¹ = l * v * l⁻¹ := hlu
      calc l⁻¹ * g * v = l⁻¹ * (g * v * g⁻¹) * g := by group
        _ = l⁻¹ * (l * v * l⁻¹) * g := by rw [h1]
        _ = v * (l⁻¹ * g) := by group
    have hcM := wt26 v (by first | exact Or.inl ‹_› | exact Or.inr ‹_›) hc
    have hgM : g ∈ normalizer (L : Set G) := by
      have h2 := mul_mem ((le_normalizer : L ≤ normalizer (L : Set G)) hl) hcM
      rwa [mul_inv_cancel_left] at h2
    rcases h.TI g hgM with hVg | hVg
    · exact hg hVg
    · have hmem : (v : G) ∈ V ⊓ CFSG.conjugate V g := by
        refine ⟨v.2, ?_⟩
        show (v : G) ∈ CFSG.conjugate V g
        rw [mem_conjugate_iff_mem]
        exact hv
      rw [hVg, mem_bot] at hmem
      exact hv1 (Subtype.ext hmem)

end Weak

theorem stmtA7NaturalModuleConfigHyp_of_lemmas (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1233 : Stmt12_3_3) (h1236 : Stmt12_3_6) (h1238 : Stmt12_3_8) :
    StmtA7NaturalModuleConfigHyp := by
  intro G _ _ T L V hyp hA7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨ψ₀, hLact, hLonto⟩ := h1233 G T L V hyp hA7
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ₀ :=
    ⟨hVT, hLV, hTV, hLact, hLonto, nact_of_lact hLV hLact hLonto hNM, hNM, hTI⟩
  obtain ⟨ψ, h, hcent⟩ := hpre.exists_aligned_central hyp.sylow
  have hZ : ∀ x : V, (x : G) ∈ centralizer (T : Set G) → (x : G) ∈ quasithinOmegaOneCenter T :=
    fun x hx => mem_omegaOneCenter_of_central hVT hx (by
      rw [pow_two]
      exact congrArg Subtype.val (sq_eq_one_of_vec ψ x))
  have wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨x, hx, hxc⟩ := hcent 2 (Or.inl rfl)
      exact h.centralizer_le_of_weight hx
        (h1238 G T L V hyp hA7 ψ h.Lact h.Lonto x (hZ x hxc) hx) hv
    · obtain ⟨x, hx, hxc⟩ := hcent 6 (Or.inr (Or.inr rfl))
      exact h.centralizer_le_of_weight hx
        (h1236 G T L V hyp hA7 ψ h.Lact h.Lonto x (hZ x hxc) hx) hv
  exact ⟨ψ, h.toConfig wt26 (h.weight_four_of_mem_conjugate h331 hyp wt26)⟩

theorem stmtA7NaturalModuleConfig_of_lemmas (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1233 : Stmt12_3_3) (h1236 : Stmt12_3_6) (h1238 : Stmt12_3_8) :
    StmtA7NaturalModuleConfig :=
  stmtA7NaturalModuleConfig_of_hyp h1222
    (stmtA7NaturalModuleConfigHyp_of_lemmas h1222 h331 h1233 h1236 h1238)

theorem stmt12_3_1_of_lemmas
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h1233 : Stmt12_3_3)
    (h1236 : Stmt12_3_6) (h1238 : Stmt12_3_8) (h12213 : Stmt12_2_13) (h1227 : Stmt12_2_7)
    (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) : Stmt12_3_1 :=
  stmt12_3_1_of_inputs (stmtA7NaturalModuleConfigHyp_of_lemmas h1222 h331 h1233 h1236 h1238)
    h12213 h1227 h1228 h1229 h331

end CFSG.Quasithin.H13.A7
