module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Z1
public import CFSG.Quasithin.Vol2.Ch5Sec1L34V2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem isCh5Module_VZ (h : Hyp5_1_14 G T M L V H B D n) (h5114 : Stmt5_1_14_first) :
    IsCh5Module T L (conjClosure (quasithinOmegaOneCenter T) L) := by
  have hh := h.hyp.toHyp5_0_1
  have hT2 : IsPGroup 2 T := hh.sylow.1
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.2
  obtain ⟨-, hVZel, hVZred⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (hh.isSylowTwoOf le_sup_right) h.charTwo_LT (le_refl (quasithinOmegaOneCenter T))
  rw [hh.conjClosure_sup_eq] at hVZel hVZred
  have hred := h.module.isTwoReducedIn
  have hVne : V ≠ ⊥ := by
    intro hb
    apply h.module.2.2
    rw [hb, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l _
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv]
    simp
  obtain ⟨z₀, -, hz₀1, hz₀Z⟩ := exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl
    (hh.V_le_T h.module) (le_sup_right.trans hred.2.1) hVne
  have hVZL : ⁅conjClosure (quasithinOmegaOneCenter T) L, L⁆ ≠ ⊥ := by
    intro hb
    have hC : conjClosure (quasithinOmegaOneCenter T) L ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have : z₀ ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hz₀Z, hC (le_conjClosure _ L hz₀Z)⟩
    rw [hZL, Subgroup.mem_bot] at this
    exact hz₀1 this
  exact ⟨hVZred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hVZred).2, hVZL⟩

theorem pCoreOf_le_centralizer_VZ (h : Hyp5_1_14 G T M L V H B D n) (h5114 : Stmt5_1_14_first) :
    pCoreOf 2 L ≤ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) L : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  have hVZmod := isCh5Module_VZ h h5114
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (hh.sup_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L))
      (pCoreOf_isPGroup 2 L)
  rw [← hh.centralizer_eq_pCoreOf hVZmod] at h1
  exact h1.trans inf_le_right

theorem mul_comm_mem_commutator {H K : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ K) :
    x * y * x⁻¹ * y⁻¹ ∈ ⁅H, K⁆ := by
  have := Subgroup.commutator_mem_commutator hx hy
  rwa [commutatorElement_def] at this

theorem conj_mem_commVL {VZ : Subgroup G} (hVZ : ∀ ℓ ∈ L, ∀ x ∈ VZ, ℓ * x * ℓ⁻¹ ∈ VZ)
    {ℓ : G} (hℓ : ℓ ∈ L) {y : G} (hy : y ∈ ⁅VZ, L⁆) : ℓ * y * ℓ⁻¹ ∈ ⁅VZ, L⁆ := by
  have key : ⁅VZ, L⁆ ≤ ⁅VZ, L⁆.comap (MulAut.conj ℓ).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    show ℓ * (x * l * x⁻¹ * l⁻¹) * ℓ⁻¹ ∈ ⁅VZ, L⁆
    have e : ℓ * (x * l * x⁻¹ * l⁻¹) * ℓ⁻¹ =
        (ℓ * x * ℓ⁻¹) * (ℓ * l * ℓ⁻¹) * (ℓ * x * ℓ⁻¹)⁻¹ * (ℓ * l * ℓ⁻¹)⁻¹ := by
      group
    rw [e]
    exact mul_comm_mem_commutator (hVZ ℓ hℓ x hx)
      (L.mul_mem (L.mul_mem hℓ hl) (L.inv_mem hℓ))
  exact key hy

theorem V₂_le_commVL {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
    (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    conjClosure Z₁ D₃ ≤ ⁅conjClosure (quasithinOmegaOneCenter T) L, L⁆ := by
  set VZ := conjClosure (quasithinOmegaOneCenter T) L with hVZ
  have hVZn : ∀ ℓ ∈ L, ∀ x ∈ VZ, ℓ * x * ℓ⁻¹ ∈ VZ := by
    intro ℓ hℓ x hx
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hℓ) x).mp hx
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hzVZ : z ∈ VZ := le_conjClosure _ L (s.Z₁_le_Z hz)
  have hdL : d ∈ L := s.D₃_le_L hd
  set w := z * (d * z * d⁻¹)⁻¹ with hw
  have hwV : w ∈ ⁅VZ, L⁆ := by
    have : w = z * d * z⁻¹ * d⁻¹ := by
      rw [hw]
      group
    rw [this]
    exact mul_comm_mem_commutator hzVZ hdL
  have hwV₂ : w ∈ conjClosure Z₁ D₃ := by
    rw [hw]
    exact (conjClosure Z₁ D₃).mul_mem (le_conjClosure Z₁ D₃ hz)
      ((conjClosure Z₁ D₃).inv_mem (mem_conjClosure hd hz))
  have hw1 : w ≠ 1 := by
    intro h1
    rw [hw, mul_inv_eq_one] at h1
    exact (s.b_props hz hz1 hd hd1 h5114).2.2.2 h1.symm
  have hzVL : z ∈ ⁅VZ, L⁆ := by
    obtain ⟨e, he, hez⟩ := s.exists_conj_eq hz hz1 hd hd1 h5114 hF hwV₂ hw1
    rw [← hez]
    exact conj_mem_commVL hVZn (s.D₃_le_L he) hwV
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact (⁅VZ, L⁆).one_mem
  obtain ⟨e, he, hev⟩ := s.exists_conj_eq hz hz1 hd hd1 h5114 hF hv hv1
  have hvz : v = e⁻¹ * z * e⁻¹⁻¹ := by
    rw [← hev]
    group
  rw [hvz]
  exact conj_mem_commVL hVZn (L.inv_mem (s.D₃_le_L he)) hzVL

theorem isElemAbelian_VZ (h : Hyp5_1_14 G T M L V H B D n) :
    IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) L) := by
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨-, hVZel, -⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (hh.isSylowTwoOf le_sup_right) h.charTwo_LT (le_refl (quasithinOmegaOneCenter T))
  rw [hh.conjClosure_sup_eq] at hVZel
  exact hVZel

end CFSG.Quasithin.H13
