module

public import CFSG.Quasithin.H13.A6S1357

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem three_cycles : (Perm.sign (swap (0 : Fin 6) 1 * swap 1 2) = 1 ∧
    (swap 0 1 * swap 1 2 : Perm (Fin 6)) 4 = 4 ∧ (swap 0 1 * swap 1 2 : Perm (Fin 6)) 5 = 5 ∧
    (swap 0 1 * swap 1 2 : Perm (Fin 6)) ^ 3 = 1) ∧
    (Perm.sign (swap (1 : Fin 6) 2 * swap 2 3) = 1 ∧ (swap 1 2 * swap 2 3 : Perm (Fin 6)) 4 = 4 ∧
    (swap 1 2 * swap 2 3 : Perm (Fin 6)) 5 = 5 ∧ (swap 1 2 * swap 2 3 : Perm (Fin 6)) ^ 3 = 1) := by
  decide +kernel

theorem fix_e0123_of : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → act4f σ e0123 = e0123 := by
  decide +kernel

@[expose] def CommDec (x : P6) : Prop :=
  ∃ y : P6, InW34 y ∧ ∃ y' : P6, InW34 y' ∧
    x = y * (act4f (swap 0 1 * swap 1 2) y)⁻¹ * (y' * (act4f (swap 1 2 * swap 2 3) y')⁻¹)

instance (x : P6) : Decidable (CommDec x) := by unfold CommDec; infer_instance

theorem W3_commDec : ∀ x : P6, InW34 x → CommDec x := by
  decide +kernel

theorem comm_W3_of_fix : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → ∀ x : P6, InW4 x →
    InW3 (x * (act4f σ x)⁻¹) := by
  decide +kernel

theorem fix45_of_odd : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → σ ^ 45 = 1 →
    σ 4 = 4 ∧ σ 5 = 5 := by
  decide +kernel

@[expose] def K4L : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

@[expose] def MemK4At (σ : Perm (Fin 6)) : Prop :=
  σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 → σ ^ 4 = 1 → σ ∈ K4L

instance (σ : Perm (Fin 6)) : Decidable (MemK4At σ) := by unfold MemK4At; infer_instance

theorem memK4At_all : ∀ σ : Perm (Fin 6), MemK4At σ := by
  decide +kernel

theorem mem_K4L (σ : Perm (Fin 6)) (h4 : σ 4 = 4) (h5 : σ 5 = 5) (hs : Perm.sign σ = 1)
    (h2 : σ ^ 4 = 1) : σ ∈ K4L :=
  memK4At_all σ h4 h5 hs h2

theorem K4L_orbit : ∀ σ ∈ K4L, ∀ τ ∈ K4L, σ ≠ 1 → τ ≠ 1 →
    τ = σ ∨ τ = swap 0 1 * swap 1 2 * σ * (swap 0 1 * swap 1 2)⁻¹ ∨
      τ = (swap 0 1 * swap 1 2)⁻¹ * σ * (swap 0 1 * swap 1 2) := by
  decide +kernel

theorem pow_four_pow_of_cube {σ : Perm (Fin 6)} (h3 : σ ^ 3 = 1) (a : ℕ) : σ ^ (4 ^ a) = σ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, show σ ^ 4 = σ ^ 3 * σ from pow_succ σ 3, h3, one_mul]

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L1_of_three {σ : Perm (Fin 6)} (hs : Perm.sign σ = 1) (h4 : σ 4 = 4)
    (h5 : σ 5 = 5) (h3 : σ ^ 3 = 1) : ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ S.L1 ∧ S.frame.ρ g = σ := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hs)
  have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
    rw [S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩, S.psi_z, hg]
    exact Subtype.ext (fix_e0123_of σ h4 h5)
  have hgN : (g : G) ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
    refine ⟨hgL, ?_⟩
    show (g : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc (g : G) * S.z = (g : G) * S.z * (g : G)⁻¹ * g := by group
      _ = S.z * g := by rw [hgz]
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (4 ^ a), ?_, by rw [map_pow, hg, pow_four_pow_of_cube h3]⟩
  refine Subgroup.subset_closure ⟨?_, m, hm, ?_⟩
  · simpa using Subgroup.pow_mem _ hgN (4 ^ a)
  · have h1 : (g ^ (4 ^ a)) ^ m = (g ^ (2 ^ a * m)) ^ (2 ^ a) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have h2 : g ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
    have h3 : (g ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
    simpa using congrArg Subtype.val h3

theorem rho_L1 {g : ↥(Subgroup.normalizer (V : Set G))} (hg : (g : G) ∈ S.L1) :
    S.frame.ρ g 4 = 4 ∧ S.frame.ρ g 5 = 5 ∧ Perm.sign (S.frame.ρ g) = 1 := by
  have key : ∀ x ∈ S.L1, ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ 4 = 4 ∧ S.frame.ρ ⟨x, hx⟩ 5 = 5 ∧ Perm.sign (S.frame.ρ ⟨x, hx⟩) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨hyL, hyN⟩, m, hm, hym⟩ := hy
      have hyV := S.frame.L_le hyL
      refine ⟨hyV, ?_⟩
      have hfix := S.fix_e0123 ⟨y, hyV⟩ (S.conj_z_of_normalizes hyN)
      have h45 : (S.frame.ρ ⟨y, hyV⟩) ^ 45 = 1 := by
        refine pow_45_of_odd hm ?_
        rw [← map_pow]
        have : (⟨y, hyV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ m = 1 :=
          Subtype.ext (by simpa using hym)
        rw [this, map_one]
      obtain ⟨h4, h5⟩ := fix45_of_odd _ hfix h45
      exact ⟨h4, h5, Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨_, hyL, rfl⟩)⟩
    | one =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      show S.frame.ρ 1 4 = 4 ∧ S.frame.ρ 1 5 = 5 ∧ Perm.sign (S.frame.ρ 1) = 1
      rw [map_one]
      exact ⟨rfl, rfl, Perm.sign_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxV, hx4, hx5, hxs⟩ := hx
      obtain ⟨hyV, hy4, hy5, hys⟩ := hy
      refine ⟨Subgroup.mul_mem _ hxV hyV, ?_⟩
      have e : (⟨x * y, Subgroup.mul_mem _ hxV hyV⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hxV⟩ * ⟨y, hyV⟩ := rfl
      rw [e, map_mul, Perm.mul_apply, Perm.mul_apply, hy4, hx4, hy5, hx5, Perm.sign_mul, hxs,
        hys]
      exact ⟨rfl, rfl, rfl⟩
    | inv x _ hx =>
      obtain ⟨hxV, hx4, hx5, hxs⟩ := hx
      refine ⟨Subgroup.inv_mem _ hxV, ?_⟩
      have e : (⟨x⁻¹, Subgroup.inv_mem _ hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hxV⟩⁻¹ := rfl
      rw [e, map_inv, Perm.inv_eq_iff_eq.2 hx4.symm, Perm.inv_eq_iff_eq.2 hx5.symm, Perm.sign_inv,
        hxs]
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨_, h⟩ := key g hg
  exact h

theorem psi_commutator (v : ↥V) (g : ↥(Subgroup.normalizer (V : Set G))) :
    ∃ h : (v : G) * g * (v : G)⁻¹ * (g : G)⁻¹ ∈ V,
      S.frame.ψ ⟨_, h⟩ = S.frame.ψ v * (act4 (S.frame.ρ g) (S.frame.ψ v))⁻¹ := by
  have hc : (g : G) * (v : G) * (g : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp g.2 _).mp v.2
  have he : (v : G) * g * (v : G)⁻¹ * (g : G)⁻¹ = (v : G) * ((g : G) * (v : G) * (g : G)⁻¹)⁻¹ := by
    group
  refine ⟨he ▸ V.mul_mem v.2 (V.inv_mem hc), ?_⟩
  have h1 : (⟨(v : G) * g * (v : G)⁻¹ * (g : G)⁻¹, he ▸ V.mul_mem v.2 (V.inv_mem hc)⟩ : ↥V) =
      v * (⟨(g : G) * (v : G) * (g : G)⁻¹, hc⟩ : ↥V)⁻¹ := Subtype.ext (by simpa using he)
  rw [h1, map_mul, map_inv, S.psi_conj g v]

theorem commutator_V_L1_le : ⁅V, S.L1⁆ ≤ S.V3 := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le.trans inf_le_left hl)
  obtain ⟨h, hψ⟩ := S.psi_commutator ⟨v, hv⟩ ⟨l, hlN⟩
  dsimp only at h hψ
  rw [commutatorElement_def]
  refine S.mem_pre.2 ⟨h, ?_⟩
  rw [hψ]
  have hfix := S.fix_e0123 ⟨l, hlN⟩ (S.conj_z_of_normalizes (S.L1_le.trans inf_le_right hl))
  exact comm_W3_of_fix _ hfix _ (S.frame.ψ ⟨v, hv⟩).2

theorem V3_le_commutator_V3_L1 : S.V3 ≤ ⁅S.V3, S.L1⁆ := by
  intro x hx
  obtain ⟨hxV, hx3⟩ := S.mem_pre.1 hx
  obtain ⟨y, hy, y', hy', he⟩ := W3_commDec _ ⟨(S.frame.ψ ⟨x, hxV⟩).2, hx3⟩
  obtain ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩ := three_cycles
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three c1 c2 c3 c4
  obtain ⟨g', hg'L1, hg'⟩ := S.exists_L1_of_three d1 d2 d3 d4
  obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨y, hy.1⟩
  obtain ⟨v', hv'⟩ := S.frame.ψ.surjective ⟨y', hy'.1⟩
  have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by
    have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨y, hy.1⟩ := hv
    rw [e]
    exact hy.2⟩
  have hv'3 : (v' : G) ∈ S.V3 := S.mem_pre.2 ⟨v'.2, by
    have e : S.frame.ψ ⟨(v' : G), v'.2⟩ = ⟨y', hy'.1⟩ := hv'
    rw [e]
    exact hy'.2⟩
  obtain ⟨h1, hψ1⟩ := S.psi_commutator v g
  obtain ⟨h2, hψ2⟩ := S.psi_commutator v' g'
  have hx_eq : x = ((v : G) * g * (v : G)⁻¹ * (g : G)⁻¹) *
      ((v' : G) * g' * (v' : G)⁻¹ * (g' : G)⁻¹) := by
    have : (⟨x, hxV⟩ : ↥V) = ⟨_, h1⟩ * ⟨_, h2⟩ := by
      apply S.frame.ψ.injective
      rw [map_mul, hψ1, hψ2, hg, hg', hv, hv']
      exact Subtype.ext he
    exact congrArg Subtype.val this
  rw [hx_eq]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hv3 hgL1)
    (Subgroup.commutator_mem_commutator hv'3 hg'L1)

theorem commutator_V_L1 : ⁅V, S.L1⁆ = S.V3 :=
  le_antisymm S.commutator_V_L1_le
    (S.V3_le_commutator_V3_L1.trans (Subgroup.commutator_mono S.V3_le_V le_rfl))

theorem commutator_V3_L1 : ⁅S.V3, S.L1⁆ = S.V3 :=
  le_antisymm ((Subgroup.commutator_mono S.V3_le_V le_rfl).trans S.commutator_V_L1_le)
    S.V3_le_commutator_V3_L1

theorem T_le_normalizer_L1 : T ≤ Subgroup.normalizer (S.L1 : Set G) :=
  A5.le_normalizer_oTwoRes_of_le_normalizer
    (F7.le_normalizer_inf S.T_le_NL (S.T_le_NV1.trans Subgroup.le_normalizer))

theorem UH_le_T
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {H : Subgroup G} (hH : H ∈ S.Hz) : conjClosure S.V3 H ≤ T := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H)

theorem lemma13_5_14_one
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V = conjClosure S.V3 H) :
    ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H ∧ conjClosure S.V3 H ≤ S.L1 := by
  have hV1 : fsuV1 T V ≤ ⁅conjClosure S.V3 H, S.L1⁆ :=
    (S.V1_le_V2.trans S.V2_le_V3).trans (S.commutator_V3_L1.ge.trans
      (Subgroup.commutator_mono (le_conjClosure _ _) le_rfl))
  have h1 : ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H :=
    calc ⁅conjClosure S.V3 H, S.L1⁆ = ⁅conjClosure S.V3 H, S.L1⁆ ⊔ fsuV1 T V :=
          (sup_eq_left.mpr hV1).symm
      _ = conjClosure S.V3 H := hU
  refine ⟨h1, ?_⟩
  rw [← h1, Subgroup.commutator_le]
  intro u hu l hl
  have huN : u ∈ Subgroup.normalizer (S.L1 : Set G) :=
    S.T_le_normalizer_L1 (S.UH_le_T hNS h1356two h13315 hH hu)
  have : u * l * u⁻¹ ∈ S.L1 := (Subgroup.mem_normalizer_iff.mp huN l).mp hl
  rw [commutatorElement_def]
  exact S.L1.mul_mem this (S.L1.inv_mem hl)

theorem isElemAbelian_UH_of_le {H : Subgroup G}
    (hC : conjClosure S.V3 H ≤ Subgroup.centralizer (V : Set G)) :
    IsElemAbelian 2 (conjClosure S.V3 H) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall
    (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) fun k hk z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyU : y ∈ conjClosure S.V3 H := HypF91.conjSub_le_conjClosure hk hy
  exact (Subgroup.mem_centralizer_iff.mp (hC hyU) z (S.V3_le_V hz)).symm

theorem lemma13_5_14_two
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hle : conjClosure S.V3 H ≤ S.L1) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    (∀ u (hu : u ∈ conjClosure S.V3 H),
        S.frame.ρ ⟨u, S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))⟩ ∈ K4L) ∧
      ∀ σ ∈ K4L, ∃ u, ∃ hu : u ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨u, S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))⟩ = σ := by
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.L_le (S.L1_le.trans inf_le_left (hle hu))
  have hT := S.UH_le_T hNS h1356two h13315 hH
  have hK4 : ∀ u (hu : u ∈ conjClosure S.V3 H), S.frame.ρ ⟨u, hUN u hu⟩ ∈ K4L := by
    intro u hu
    obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨u, hUN u hu⟩) (hle hu)
    refine mem_K4L _ h4 h5 hs ?_
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨u, hT hu⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨u, hUN u hu⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  refine ⟨hK4, fun σ hσ => ?_⟩
  by_cases hσ1 : σ = 1
  · exact ⟨1, Subgroup.one_mem _, by rw [hσ1]; exact map_one _⟩
  obtain ⟨u₀, hu₀, hne⟩ : ∃ u₀, ∃ hu₀ : u₀ ∈ conjClosure S.V3 H,
      S.frame.ρ ⟨u₀, hUN u₀ hu₀⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hna (S.isElemAbelian_UH_of_le fun u hu => (S.rho_eq_one_iff _).1 (hcon u hu))
  obtain ⟨c, hcL1, hc⟩ := S.exists_L1_c012
  have hcH : (c : G) ∈ H := (le_sup_left.trans hH.1.1) hcL1
  have hUH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  rcases K4L_orbit _ (hK4 u₀ hu₀) σ hσ hne hσ1 with h | h | h
  · exact ⟨u₀, hu₀, h.symm⟩
  · have hm : (c : G) * u₀ * (c : G)⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hUH hcH) u₀).mp hu₀
    refine ⟨_, hm, ?_⟩
    have e : (⟨(c : G) * u₀ * (c : G)⁻¹, hUN _ hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        c * ⟨u₀, hUN u₀ hu₀⟩ * c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hc, h]
  · have hm : (c : G)⁻¹ * u₀ * (c : G)⁻¹⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hUH (H.inv_mem hcH)) u₀).mp hu₀
    refine ⟨_, hm, ?_⟩
    have e : (⟨(c : G)⁻¹ * u₀ * (c : G)⁻¹⁻¹, hUN _ hm⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = c⁻¹ * ⟨u₀, hUN u₀ hu₀⟩ * c⁻¹⁻¹ := rfl
    rw [e, inv_inv, map_mul, map_mul, map_inv, hc, h]

end Setting4

end CFSG.Quasithin.H13.A6
