module

public import CFSG.RankThree.GF2n.Tim79a34BigLocal
public import CFSG.RankThree.GF2n.Tim79a34TwZR
public import CFSG.Timmesfeld.ARS.CaseMSpPlane
public import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.GroupTheory.SteinbergBK
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem MinCex.exists_eq_conj_of_mem_omegaOf (hc : MinCex M V Q P H) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) : ∃ x : ↥(xOf V H), U = conjSubgroup (x : G) V := by
  obtain ⟨k, hkH, rfl⟩ := hU
  have hsup : k ∈ xOf V H ⊔ P := by
    rw [hc.sec2.H_eq]
    exact hkH
  have hPN : P ≤ Subgroup.normalizer (xOf V H : Set G) :=
    hc.PleH.trans (H_le_normalizer_xOf V H)
  obtain ⟨v, hv, c, hcP, hvc⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hPN hsup
  have hcC : c ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => hc.commute_of_mem_P hcP hw
  have hcV : conjSubgroup c V = V :=
    mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.centralizer_le_normalizer _ hcC)
  refine ⟨⟨v, hv⟩, ?_⟩
  show conjSubgroup k V = conjSubgroup v V
  rw [hvc, ← conjSubgroup_conjSubgroup, hcV]

structure BigNatData (h : BigEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥) where
  f : ℕ
  n : ℕ
  k : Fin n
  Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H
  g : ↥(StatedSp n (GaloisField 2 f))
  θ : (Fin 2 → GaloisField 2 f) → G
  hn : 2 ≤ n
  hf : 2 ≤ f
  h2f : 2 ^ f = qBar V H
  T : Subgroup ↥(StatedSp n (GaloisField 2 f))
  hT : IsTransGroup (SpExtras.mat n (GaloisField 2 f) g *ᵥ
    Pi.single (Sum.inl k) (1 : GaloisField 2 f)) T
  hTmap : T.map Φ.toMonoidHom = Vy V H
  hadd : ∀ u u', θ (u + u') = θ u * θ u'
  hinj : Function.Injective θ
  hmemW : ∀ u, θ u ∈ wOf V H
  hmemV : ∀ c, θ ![c, 0] ∈ V
  hsurj : ∀ x ∈ V ⊓ wOf V H, ∃ c, θ ![c, 0] = x
  hequiv : ∀ (x : ↥(xOf V H))
      (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
    xToXbar h.setup.mc.toMinCex.V_le_H x =
      Φ (g * longBlock (GaloisField 2 f) n k s * g⁻¹) →
    ∀ u, θ ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *ᵥ u) =
      (x : G) * θ u * (x : G)⁻¹

namespace BigNatData

variable {h : BigEndHyp M V Q P H} {hZ : Subgroup.center (Xbar V H) = ⊥} (D : BigNatData h hZ)

@[expose] noncomputable def a : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f :=
  SpExtras.mat D.n (GaloisField 2 D.f) D.g *ᵥ
    Pi.single (Sum.inl D.k) (1 : GaloisField 2 D.f)

@[expose] noncomputable def b : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f :=
  SpExtras.mat D.n (GaloisField 2 D.f) D.g *ᵥ
    Pi.single (Sum.inr D.k) (1 : GaloisField 2 D.f)

@[expose] noncomputable def w0 : G := D.θ ![1, 0]

@[simp] theorem spForm_a_b : spForm D.a D.b = 1 := by
  rw [a, b, spForm_longBlock_pair, spForm_single_inl_single_inr]

theorem a_ne_zero : D.a ≠ 0 := by
  rw [a]
  refine mat_mulVec_ne_zero' D.g ?_
  intro h
  have := congrFun h (Sum.inl D.k)
  simpa using this

theorem theta_zero : D.θ 0 = 1 := by
  have h : D.θ 0 * D.θ 0 = D.θ 0 := by
    simpa using (D.hadd 0 0).symm
  exact mul_left_cancel (h.trans (mul_one (D.θ 0)).symm)

theorem w0_mem_V : D.w0 ∈ V := by
  simpa [w0] using D.hmemV 1

theorem w0_mem_W : D.w0 ∈ wOf V H := D.hmemW ![1, 0]

theorem w0_ne_one : D.w0 ≠ 1 := by
  intro h
  have h0 : (![1, 0] : Fin 2 → GaloisField 2 D.f) = 0 :=
    D.hinj (h.trans D.theta_zero.symm)
  have h1 := congrFun h0 0
  simpa using h1

end BigNatData

theorem commutator_mem_wOf_of_centralizes_Vy (hVH : V ≤ H) {x : G} (hx : x ∈ xOf V H)
    (hxVy : xToXbar hVH ⟨x, hx⟩ ∈
      Subgroup.centralizer (Vy V H : Set (Xbar V H))) :
    ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ wOf V H := by
  intro v hv
  have hxH : x ∈ H := xOf_le_H hVH hx
  have hvH : v ∈ H := hVH hv
  have h1 : x * v * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hvH) (H.inv_mem hxH)
  have hxv : (⟨x * v * x⁻¹, h1⟩ : ↥H) =
      (⟨x, hxH⟩ : ↥H) * ⟨v, hvH⟩ * (⟨x, hxH⟩ : ↥H)⁻¹ := by
    ext
    simp
  have hmemX : piBar V H ⟨v, hvH⟩ ∈ barOf V H (xOf V H) :=
    mem_barOf_iff.mpr ⟨⟨v, hvH⟩, le_xOf (V_mem_omegaOf V H) hv, rfl⟩
  have hmemv : (⟨piBar V H ⟨v, hvH⟩, hmemX⟩ : Xbar V H) ∈ Vy V H :=
    Subgroup.mem_subgroupOf.mpr (mem_barOf_iff.mpr ⟨⟨v, hvH⟩, hv, rfl⟩)
  have hcent := Subgroup.mem_centralizer_iff.mp hxVy _ hmemv
  have hcent' : piBar V H ⟨v, hvH⟩ * (xToXbar hVH ⟨x, hx⟩ : Hbar V H) =
      (xToXbar hVH ⟨x, hx⟩ : Hbar V H) * piBar V H ⟨v, hvH⟩ := by
    have := congrArg (Subtype.val : Xbar V H → Hbar V H) hcent
    simpa using this
  have hxbar : piBar V H ⟨x, hxH⟩ = (xToXbar hVH ⟨x, hx⟩ : Hbar V H) := by
    rw [coe_xToXbar]
    rfl
  have h2 : piBar V H ⟨x * v * x⁻¹, h1⟩ = piBar V H ⟨v, hvH⟩ := by
    rw [hxv, map_mul, map_mul, map_inv, hxbar, ← hcent']
    group
  have h3 : piBar V H (⟨x * v * x⁻¹, h1⟩ * ⟨v, hvH⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := (piBar_eq_one_iff _).mp h3
  simpa using h4

namespace BigNatData

variable {h : BigEndHyp M V Q P H} {hZ : Subgroup.center (Xbar V H) = ⊥} (D : BigNatData h hZ)

@[expose] def pointRel (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) (y : G) : Prop :=
  (v = 0 ∧ y = 1) ∨
    ∃ (s : ↥(StatedSp D.n (GaloisField 2 D.f))) (x : ↥(xOf V H)),
      SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ D.a = v ∧
        xToXbar h.setup.mc.toMinCex.V_le_H x = D.Φ s ∧
          y = (x : G) * D.w0 * (x : G)⁻¹

theorem pointRel_exists (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    ∃ y : G, D.pointRel v y := by
  by_cases hv : v = 0
  · exact ⟨1, Or.inl ⟨hv, rfl⟩⟩
  · obtain ⟨s, hs⟩ := twZR_exists_mat_mulVec_eq D.a_ne_zero hv
    obtain ⟨x, hx⟩ := xToXbar_surjective h.setup.mc.toMinCex.V_le_H (D.Φ s)
    exact ⟨_, Or.inr ⟨s, x, hs, hx, rfl⟩⟩

theorem pointRel_unique {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f} {y y' : G}
    (hy : D.pointRel v y) (hy' : D.pointRel v y') : y = y' := by
  rcases hy with ⟨rfl, rfl⟩ | ⟨s, x, hs, hx, rfl⟩
  · rcases hy' with ⟨-, rfl⟩ | ⟨s', x', hs', -, -⟩
    · rfl
    · exact absurd hs' (mat_mulVec_ne_zero' s' D.a_ne_zero)
  · rcases hy' with ⟨hv, -⟩ | ⟨s', x', hs', hx', rfl⟩
    · exact absurd hs (hv ▸ mat_mulVec_ne_zero' s D.a_ne_zero)
    · set k : ↥(xOf V H) := x'⁻¹ * x with hk
      have hkG : (k : G) = (x' : G)⁻¹ * (x : G) := rfl
      have hfix : SpExtras.mat D.n (GaloisField 2 D.f) (s'⁻¹ * s) *ᵥ D.a = D.a := by
        calc SpExtras.mat D.n (GaloisField 2 D.f) (s'⁻¹ * s) *ᵥ D.a
            = SpExtras.mat D.n (GaloisField 2 D.f) s'⁻¹ *ᵥ
                (SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ D.a) := by
              rw [map_mul, Matrix.mulVec_mulVec]
          _ = SpExtras.mat D.n (GaloisField 2 D.f) s'⁻¹ *ᵥ v := by rw [hs]
          _ = SpExtras.mat D.n (GaloisField 2 D.f) s'⁻¹ *ᵥ
                (SpExtras.mat D.n (GaloisField 2 D.f) s' *ᵥ D.a) := by rw [hs']
          _ = D.a := by
              rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      have hcomm := commute_of_mat_mulVec_eq D.hT hfix
      have hcen : D.Φ (s'⁻¹ * s) ∈ Subgroup.centralizer (Vy V H : Set (Xbar V H)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← D.hTmap] at hy
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
        have hh : D.Φ (t * (s'⁻¹ * s)) = D.Φ ((s'⁻¹ * s) * t) :=
          (congrArg D.Φ (hcomm t ht)).symm
        change D.Φ t * D.Φ (s'⁻¹ * s) = D.Φ (s'⁻¹ * s) * D.Φ t
        simpa only [map_mul] using hh
      have hkbar : xToXbar h.setup.mc.toMinCex.V_le_H k = D.Φ (s'⁻¹ * s) := by
        rw [hk, map_mul, map_inv, hx, hx', map_mul, map_inv]
      have hkVy : xToXbar h.setup.mc.toMinCex.V_le_H k ∈
          Subgroup.centralizer (Vy V H : Set (Xbar V H)) := by
        rw [hkbar]
        exact hcen
      have hxV : ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ wOf V H :=
        commutator_mem_wOf_of_centralizes_Vy h.setup.mc.toMinCex.V_le_H k.2 hkVy
      have hkw : (k : G) * D.w0 = D.w0 * (k : G) :=
        h.commute_of_bar_centralizes hZ k.2 hxV D.w0 ⟨D.w0_mem_V, D.w0_mem_W⟩
      rw [hkG] at hkw
      calc (x : G) * D.w0 * (x : G)⁻¹
          = (x' : G) * ((x' : G)⁻¹ * (x : G) * D.w0) * (x : G)⁻¹ := by group
        _ = (x' : G) * (D.w0 * ((x' : G)⁻¹ * (x : G))) * (x : G)⁻¹ := by rw [hkw]
        _ = (x' : G) * D.w0 * (x' : G)⁻¹ := by group

@[expose] noncomputable def psi0 (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) : G :=
  Classical.choose (D.pointRel_exists v)

theorem psi0_spec (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) : D.pointRel v (D.psi0 v) :=
  Classical.choose_spec (D.pointRel_exists v)

theorem psi0_eq_of_rel {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f} {y : G}
    (hy : D.pointRel v y) : D.psi0 v = y :=
  D.pointRel_unique (D.psi0_spec v) hy

@[simp] theorem psi0_zero : D.psi0 0 = 1 :=
  D.psi0_eq_of_rel (Or.inl ⟨rfl, rfl⟩)

theorem psi0_mem (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) : D.psi0 v ∈ wOf V H := by
  rcases D.psi0_spec v with ⟨-, hy⟩ | ⟨s, x, -, -, hy⟩
  · rw [hy]
    exact (wOf V H).one_mem
  · rw [hy]
    have hxH : (x : G) ∈ H := xOf_le_H h.setup.mc.toMinCex.V_le_H x.2
    exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH) D.w0).mp D.w0_mem_W

theorem psi0_ne_one {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f} (hv : v ≠ 0) :
    D.psi0 v ≠ 1 := by
  intro h1
  rcases D.psi0_spec v with ⟨hv0, -⟩ | ⟨s, x, -, -, hy⟩
  · exact hv hv0
  · apply D.w0_ne_one
    rw [hy] at h1
    calc D.w0 = (x : G)⁻¹ * ((x : G) * D.w0 * (x : G)⁻¹) * (x : G) := by group
      _ = 1 := by rw [h1]; group

theorem psi0_a : D.psi0 D.a = D.w0 := by
  have hrel : D.pointRel D.a D.w0 :=
    Or.inr ⟨1, 1, by simp, by simp, by simp [w0]⟩
  rw [D.psi0_eq_of_rel hrel]

theorem psi0_eq_conj {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f}
    {s : ↥(StatedSp D.n (GaloisField 2 D.f))} {x : ↥(xOf V H)}
    (hs : SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ D.a = v)
    (hx : xToXbar h.setup.mc.toMinCex.V_le_H x = D.Φ s) :
    D.psi0 v = (x : G) * D.w0 * (x : G)⁻¹ :=
  D.psi0_eq_of_rel (Or.inr ⟨s, x, hs, hx, rfl⟩)

theorem psi0_conj {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f}
    (s : ↥(StatedSp D.n (GaloisField 2 D.f))) (x : ↥(xOf V H))
    (hx : xToXbar h.setup.mc.toMinCex.V_le_H x = D.Φ s) :
    D.psi0 (SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ v) =
      (x : G) * D.psi0 v * (x : G)⁻¹ := by
  by_cases hv : v = 0
  · subst v
    simp [psi0_zero]
  · rcases D.psi0_spec v with ⟨hv0, -⟩ | ⟨s₀, x₀, hs₀, hx₀, hy⟩
    · exact absurd hv0 hv
    · have hmat : SpExtras.mat D.n (GaloisField 2 D.f) (s * s₀) *ᵥ D.a =
          SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ v := by
        rw [map_mul, ← Matrix.mulVec_mulVec, hs₀]
      have hx' : xToXbar h.setup.mc.toMinCex.V_le_H (x * x₀) =
          D.Φ (s * s₀) := by
        rw [map_mul, hx, hx₀, map_mul]
      have hval := D.psi0_eq_conj hmat hx'
      rw [hval, hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
      group

theorem psi0_plane (u : Fin 2 → GaloisField 2 D.f) :
    D.psi0 (u 0 • D.a + u 1 • D.b) = D.θ u := by
  by_cases hu : u = 0
  · subst u
    simp [psi0_zero, theta_zero]
  · obtain ⟨s, hs⟩ := exists_sl2_mulVec_single u hu
    obtain ⟨x, hx⟩ := xToXbar_surjective h.setup.mc.toMinCex.V_le_H
      (D.Φ (D.g * longBlock (GaloisField 2 D.f) D.n D.k s * D.g⁻¹))
    have h10 : (![1, 0] : Fin 2 → GaloisField 2 D.f) = Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp [Pi.single_apply]
    have hs' : (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 D.f)) *ᵥ ![1, 0] = u := by
      rw [h10, hs]
    have hmat : SpExtras.mat D.n (GaloisField 2 D.f)
          (D.g * longBlock (GaloisField 2 D.f) D.n D.k s * D.g⁻¹) *ᵥ D.a =
        u 0 • D.a + u 1 • D.b := by
      have h := mat_longBlock_conj_mulVec_plane (F := GaloisField 2 D.f) (n := D.n)
        (k := D.k) (g := D.g) (s := s) ![1, 0]
      rw [hs'] at h
      simpa [a, b] using h
    have h := D.psi0_conj (v := D.a) _ x hx
    rw [hmat, D.psi0_a] at h
    rw [h]
    have hθ : D.θ u = (x : G) * D.w0 * (x : G)⁻¹ := by
      have he := D.hequiv x s hx ![1, 0]
      rw [hs'] at he
      simpa [w0] using he
    rw [hθ]

theorem psi0_smul_eq {v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f}
    (s : ↥(StatedSp D.n (GaloisField 2 D.f))) (x : ↥(xOf V H))
    (hs : SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ D.a = v)
    (hx : xToXbar h.setup.mc.toMinCex.V_le_H x = D.Φ s) (c : GaloisField 2 D.f) :
    D.psi0 (c • v) = (x : G) * D.θ ![c, 0] * (x : G)⁻¹ := by
  have h := D.psi0_conj (v := c • D.a) s x hx
  rw [Matrix.mulVec_smul, hs] at h
  rw [h]
  have hc : D.psi0 (c • D.a) = D.θ ![c, 0] := by
    have := D.psi0_plane ![c, 0]
    simpa using this
  rw [hc]

theorem psi0_add_smul (c d : GaloisField 2 D.f)
    (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    D.psi0 (c • v + d • v) = D.psi0 (c • v) * D.psi0 (d • v) := by
  by_cases hv : v = 0
  · subst v
    simp [psi0_zero]
  · obtain ⟨s, hs⟩ := twZR_exists_mat_mulVec_eq D.a_ne_zero hv
    obtain ⟨x, hx⟩ := xToXbar_surjective h.setup.mc.toMinCex.V_le_H (D.Φ s)
    rw [← add_smul, D.psi0_smul_eq s x hs hx (c + d),
      D.psi0_smul_eq s x hs hx c, D.psi0_smul_eq s x hs hx d]
    have hvec : (![c, 0] + ![d, 0] : Fin 2 → GaloisField 2 D.f) = ![c + d, 0] := by
      funext i
      fin_cases i <;> simp
    have hsum : D.θ ![c + d, 0] = D.θ ![c, 0] * D.θ ![d, 0] := by
      have h := D.hadd ![c, 0] ![d, 0]
      rw [hvec] at h
      exact h
    rw [hsum]
    group

theorem psi0_transvection (z v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f)
    (lam : GaloisField 2 D.f) :
    D.psi0 (v + (lam * spForm z v) • z) =
      D.psi0 v * D.psi0 ((lam * spForm z v) • z) := by
  by_cases hB : spForm z v = 0
  · rw [hB, mul_zero, zero_smul, add_zero]
    simp [psi0_zero]
  · have hBv : spForm v z ≠ 0 := by
      rw [spForm_comm]
      exact neg_ne_zero.mpr hB
    set c : GaloisField 2 D.f := (spForm v z)⁻¹ with hc
    have hpair : spForm v (c • z) = 1 := by
      rw [spForm_smul_right', hc, inv_mul_cancel₀ hBv]
    obtain ⟨s, hsA, hsB⟩ := exists_mat_mulVec_eq_pair D.spForm_a_b hpair
    obtain ⟨x, hx⟩ := xToXbar_surjective h.setup.mc.toMinCex.V_le_H (D.Φ s)
    set mu : GaloisField 2 D.f := lam * spForm z v * spForm v z with hmu
    have hμc : mu * c = lam * spForm z v := by
      rw [hmu, hc, mul_assoc, mul_assoc, mul_inv_cancel₀ hBv, mul_one]
    have hmat : SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ (D.a + mu • D.b) =
        v + (lam * spForm z v) • z := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hsA, hsB, smul_smul, hμc]
    have h1 := D.psi0_conj (v := D.a + mu • D.b) s x hx
    rw [hmat] at h1
    have h2 : D.psi0 (D.a + mu • D.b) = D.θ ![1, mu] := by
      have := D.psi0_plane ![1, mu]
      simpa using this
    have h0 : D.psi0 v = (x : G) * D.θ ![1, 0] * (x : G)⁻¹ := D.psi0_eq_conj hsA hx
    have hz : (lam * spForm z v) • z =
        SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ (mu • D.b) := by
      rw [Matrix.mulVec_smul, hsB, smul_smul, hμc]
    have h3 := D.psi0_conj (v := mu • D.b) s x hx
    rw [← hz] at h3
    have h4 : D.psi0 (mu • D.b) = D.θ ![0, mu] := by
      have := D.psi0_plane ![0, mu]
      simpa using this
    rw [h4] at h3
    rw [h1, h2, h0, h3]
    have hθ : D.θ ![1, mu] = D.θ ![1, 0] * D.θ ![0, mu] := by
      have h := D.hadd ![1, 0] ![0, mu]
      have hv : (![1, 0] + ![0, mu] : Fin 2 → GaloisField 2 D.f) = ![1, mu] := by
        funext i
        fin_cases i <;> simp
      rw [hv] at h
      exact h
    rw [hθ]
    group

theorem psi0_conj_x (x : ↥(xOf V H)) (y : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    (x : G) * D.psi0 y * (x : G)⁻¹ =
      D.psi0 (SpExtras.mat D.n (GaloisField 2 D.f)
        (D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x)) *ᵥ y) := by
  symm
  exact D.psi0_conj (D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x)) x
    (D.Φ.apply_symm_apply _).symm

theorem mem_T_of_mem_V (vx : ↥(xOf V H)) (hv : (vx : G) ∈ V) :
    D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H vx) ∈ D.T := by
  have hmemX : (xToXbar h.setup.mc.toMinCex.V_le_H vx : Hbar V H) ∈
      barOf V H (xOf V H) :=
    mem_barOf_iff.mpr ⟨⟨(vx : G), xOf_le_H h.setup.mc.toMinCex.V_le_H vx.2⟩,
      vx.2, rfl⟩
  have hVbar : (⟨(xToXbar h.setup.mc.toMinCex.V_le_H vx : Hbar V H), hmemX⟩ :
      Xbar V H) ∈ Vy V H :=
    Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨⟨(vx : G), xOf_le_H h.setup.mc.toMinCex.V_le_H vx.2⟩, hv, rfl⟩)
  have hVbar' : xToXbar h.setup.mc.toMinCex.V_le_H vx ∈ Vy V H := hVbar
  rw [← D.hTmap] at hVbar'
  obtain ⟨t', ht', ht'eq⟩ := Subgroup.mem_map.mp hVbar'
  have ht_eq : D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H vx) = t' :=
    D.Φ.injective (by
      rw [MulEquiv.apply_symm_apply]
      exact ht'eq.symm)
  rw [ht_eq]
  exact ht'

theorem exists_spTrans_of_conj_mem_T {s₀ t : ↥(StatedSp D.n (GaloisField 2 D.f))}
    (ht : t ∈ D.T) :
    ∃ (z : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) (lam : GaloisField 2 D.f),
      SpExtras.mat D.n (GaloisField 2 D.f) (s₀ * t * s₀⁻¹) = spTrans z lam := by
  have hmemT : s₀ * t * s₀⁻¹ ∈ conjSub D.T s₀ := by
    rw [mem_conjSub]
    have e : s₀⁻¹ * (s₀ * t * s₀⁻¹) * s₀ = t := by group
    rw [e]
    exact ht
  obtain ⟨lam, hlam⟩ := ((D.hT.conjSub s₀).1 (s₀ * t * s₀⁻¹)).mp hmemT
  exact ⟨SpExtras.mat D.n (GaloisField 2 D.f) s₀ *ᵥ D.a, lam, hlam⟩

theorem exists_spTrans_of_mem_omegaOf {U : Subgroup G} (hU : U ∈ omegaOf V H) {u : G}
    (hu : u ∈ U) :
    ∃ (z : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) (lam : GaloisField 2 D.f),
      SpExtras.mat D.n (GaloisField 2 D.f)
        (D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H
          (⟨u, le_xOf hU hu⟩ : ↥(xOf V H)))) = spTrans z lam := by
  obtain ⟨x₀, hUeq⟩ := h.setup.mc.toMinCex.exists_eq_conj_of_mem_omegaOf hU
  have hu' : u ∈ conjSubgroup (x₀ : G) V := by rw [← hUeq]; exact hu
  set v : G := (x₀ : G)⁻¹ * u * (x₀ : G) with hvdef
  have hv : v ∈ V := mem_conjSubgroup.mp hu'
  let vx : ↥(xOf V H) := ⟨v, le_xOf (V_mem_omegaOf V H) hv⟩
  let ux : ↥(xOf V H) := ⟨u, le_xOf hU hu⟩
  have hux : ux = x₀ * vx * x₀⁻¹ := by
    apply Subtype.ext
    show u = (x₀ : G) * v * (x₀ : G)⁻¹
    rw [hvdef]
    group
  set s₀ : ↥(StatedSp D.n (GaloisField 2 D.f)) :=
    D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x₀) with hs₀
  set t : ↥(StatedSp D.n (GaloisField 2 D.f)) :=
    D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H vx) with htdef
  have htT : t ∈ D.T := by
    simpa [t] using D.mem_T_of_mem_V vx hv
  have hsu : D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ux) = s₀ * t * s₀⁻¹ := by
    rw [hux]
    simpa [s₀, t] using D.conj_symm_eq x₀ vx
  rw [hsu]
  exact D.exists_spTrans_of_conj_mem_T (s₀ := s₀) (t := t) htT

theorem exists_conj_action {U : Subgroup G} (hU : U ∈ omegaOf V H) {u : G} (hu : u ∈ U) :
    ∃ (z : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) (lam : GaloisField 2 D.f),
      ∀ y, u * D.psi0 y * u⁻¹ =
        D.psi0 y * D.psi0 ((lam * spForm z y) • z) := by
  obtain ⟨z, lam, hmat⟩ := D.exists_spTrans_of_mem_omegaOf hU hu
  let ux : ↥(xOf V H) := ⟨u, le_xOf hU hu⟩
  let s : ↥(StatedSp D.n (GaloisField 2 D.f)) :=
    D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ux)
  have hsp : ∀ y, SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ y =
      y + (lam * spForm z y) • z := by
    intro y
    rw [show s = D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H
      (⟨u, le_xOf hU hu⟩ : ↥(xOf V H))) from rfl, hmat, spTrans_mulVec]
  refine ⟨z, lam, fun y => ?_⟩
  rw [show u * D.psi0 y * u⁻¹ =
      D.psi0 (SpExtras.mat D.n (GaloisField 2 D.f) s *ᵥ y) from by
    simpa [s, ux] using D.psi0_conj_x ux y]
  rw [hsp, D.psi0_transvection]

theorem psi0_add_conj_key (A B C p q t : ↥(wOf V H)) (ht : t = p * q)
    (hcomm : ∀ x y : ↥(wOf V H), x * y = y * x) :
    (A * t) * (B * p)⁻¹ * (C * q)⁻¹ = A * B⁻¹ * C⁻¹ := by
  letI : CommGroup ↥(wOf V H) :=
    { (inferInstance : Group ↥(wOf V H)) with mul_comm := hcomm }
  rw [ht]
  apply Additive.ofMul.injective
  change (Additive.ofMul A + (Additive.ofMul p + Additive.ofMul q)) +
      -(Additive.ofMul B + Additive.ofMul p) +
      -(Additive.ofMul C + Additive.ofMul q) =
    Additive.ofMul A + -Additive.ofMul B + -Additive.ofMul C
  abel

theorem psi0_add_conj_eq (v v' : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f)
    {U : Subgroup G} (hU : U ∈ omegaOf V H) {u : G} (hu : u ∈ U) :
    u * (D.psi0 (v + v') * (D.psi0 v)⁻¹ * (D.psi0 v')⁻¹) * u⁻¹ =
      D.psi0 (v + v') * (D.psi0 v)⁻¹ * (D.psi0 v')⁻¹ := by
  obtain ⟨z, lam, hact⟩ := D.exists_conj_action hU hu
  have hA := hact (v + v')
  have hB := hact v
  have hC := hact v'
  have hBi : u * (D.psi0 v)⁻¹ * u⁻¹ =
      (D.psi0 v * D.psi0 ((lam * spForm z v) • z))⁻¹ := by
    rw [show u * (D.psi0 v)⁻¹ * u⁻¹ = (u * D.psi0 v * u⁻¹)⁻¹ by group, hB]
  have hCi : u * (D.psi0 v')⁻¹ * u⁻¹ =
      (D.psi0 v' * D.psi0 ((lam * spForm z v') • z))⁻¹ := by
    rw [show u * (D.psi0 v')⁻¹ * u⁻¹ = (u * D.psi0 v' * u⁻¹)⁻¹ by group, hC]
  have ht : D.psi0 ((lam * spForm z (v + v')) • z) =
      D.psi0 ((lam * spForm z v) • z) * D.psi0 ((lam * spForm z v') • z) := by
    rw [spForm_add_right, mul_add, add_smul]
    exact D.psi0_add_smul _ _ z
  have hW := D.psi0_mem
  let A : ↥(wOf V H) := ⟨D.psi0 (v + v'), hW _⟩
  let B : ↥(wOf V H) := ⟨D.psi0 v, hW _⟩
  let C : ↥(wOf V H) := ⟨D.psi0 v', hW _⟩
  let p : ↥(wOf V H) := ⟨D.psi0 ((lam * spForm z v) • z), hW _⟩
  let q : ↥(wOf V H) := ⟨D.psi0 ((lam * spForm z v') • z), hW _⟩
  let t : ↥(wOf V H) := ⟨D.psi0 ((lam * spForm z (v + v')) • z), hW _⟩
  have ht' : t = p * q := Subtype.ext ht
  have hcomm : ∀ x y : ↥(wOf V H), x * y = y * x :=
    fun x y => Subtype.ext (h.setup.mc.toMinCex.wOf_comm x.2 y.2)
  have hkey' := psi0_add_conj_key A B C p q t ht' hcomm
  have hkey : (D.psi0 (v + v') * D.psi0 ((lam * spForm z (v + v')) • z)) *
        (D.psi0 v * D.psi0 ((lam * spForm z v) • z))⁻¹ *
        (D.psi0 v' * D.psi0 ((lam * spForm z v') • z))⁻¹ =
      D.psi0 (v + v') * (D.psi0 v)⁻¹ * (D.psi0 v')⁻¹ := by
    have := congrArg (Subtype.val : ↥(wOf V H) → G) hkey'
    simpa [A, B, C, p, q, t] using this
  rw [show u * (D.psi0 (v + v') * (D.psi0 v)⁻¹ * (D.psi0 v')⁻¹) * u⁻¹ =
      (u * D.psi0 (v + v') * u⁻¹) * (u * (D.psi0 v)⁻¹ * u⁻¹) *
        (u * (D.psi0 v')⁻¹ * u⁻¹) by group]
  rw [hA, hBi, hCi]
  exact hkey

theorem psi0_add (v v' : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    D.psi0 (v + v') = D.psi0 v * D.psi0 v' := by
  let E : G := D.psi0 (v + v') * (D.psi0 v)⁻¹ * (D.psi0 v')⁻¹
  have hEW : E ∈ wOf V H :=
    (wOf V H).mul_mem ((wOf V H).mul_mem (D.psi0_mem _)
      ((wOf V H).inv_mem (D.psi0_mem _))) ((wOf V H).inv_mem (D.psi0_mem _))
  have hUK : ∀ U ∈ omegaOf V H, U ≤ Subgroup.centralizer ({E} : Set G) := by
    intro U hU x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := D.psi0_add_conj_eq v v' hU hx
    calc x * E = (x * E * x⁻¹) * x := by group
      _ = E * x := by rw [h]
  have hXK : xOf V H ≤ Subgroup.centralizer ({E} : Set G) := by
    rw [xOf]
    exact iSup₂_le hUK
  have hEC : E ∈ Subgroup.centralizer (xOf V H : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXK hx)
  have hEbot : E ∈ (⊥ : Subgroup G) := by
    rw [← h.setup.mc.toMinCex.sec2.centralizer_w]
    exact Subgroup.mem_inf.mpr ⟨hEW, hEC⟩
  have hE1 : E = 1 := Subgroup.mem_bot.mp hEbot
  have h1 : D.psi0 (v + v') * (D.psi0 v)⁻¹ = D.psi0 v' := by
    have := congrArg (fun z => z * D.psi0 v') hE1
    simpa [E, mul_assoc] using this
  have h2 : D.psi0 (v + v') = D.psi0 v' * D.psi0 v := by
    have := congrArg (fun z => z * D.psi0 v) h1
    simpa [mul_assoc] using this
  rw [h2, h.setup.mc.toMinCex.wOf_comm (D.psi0_mem v') (D.psi0_mem v)]

theorem psi0_neg (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    D.psi0 (-v) = (D.psi0 v)⁻¹ := by
  have h := D.psi0_add v (-v)
  rw [add_neg_cancel, psi0_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem psi0_injective : Function.Injective D.psi0 := by
  intro v v' hvv'
  by_contra hne
  have hsub : D.psi0 (v - v') = 1 := by
    rw [sub_eq_add_neg, D.psi0_add, D.psi0_neg, hvv', mul_inv_cancel]
  exact D.psi0_ne_one (sub_ne_zero.mpr hne) hsub

theorem psi0_surjective_w : ∀ w : ↥(wOf V H), ∃ v, D.psi0 v = (w : G) := by
  let Im : Subgroup G :=
    { carrier := Set.range D.psi0
      one_mem' := ⟨0, D.psi0_zero⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by rw [D.psi0_add]⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, D.psi0_neg a⟩ }
  have hWIm : wOf V H ≤ Im := by
    rw [wOf]
    refine iSup₂_le fun U hU => ?_
    intro w hw
    have hwW : w ∈ wOf V H := inf_pCore_le_wOf hU hw
    obtain ⟨x, hUx⟩ := h.setup.mc.toMinCex.exists_eq_conj_of_mem_omegaOf hU
    have hwU : w ∈ conjSubgroup (x : G) V := by rw [← hUx]; exact hw.1
    set v : G := (x : G)⁻¹ * w * (x : G) with hvdef
    have hvV : v ∈ V := mem_conjSubgroup.mp hwU
    have hxH : (x : G) ∈ H := xOf_le_H h.setup.mc.toMinCex.V_le_H x.2
    have hvW : v ∈ wOf V H := by
      rw [hvdef]
      simpa using (Subgroup.mem_normalizer_iff.mp
        (H_le_normalizer_wOf V H (H.inv_mem hxH)) w).mp hwW
    obtain ⟨c, hc⟩ := D.hsurj v ⟨hvV, hvW⟩
    refine ⟨SpExtras.mat D.n (GaloisField 2 D.f)
      (D.Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H x)) *ᵥ (c • D.a), ?_⟩
    rw [← D.psi0_conj_x x (c • D.a)]
    have hplane : D.psi0 (c • D.a) = D.θ ![c, 0] := by
      have := D.psi0_plane ![c, 0]
      simpa using this
    rw [hplane, hc, hvdef]
    group
  intro w
  exact hWIm w.2

@[expose] noncomputable def psi0W (v : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) : ↥(wOf V H) :=
  ⟨D.psi0 v, D.psi0_mem v⟩

theorem psi0W_add (v v' : Fin D.n ⊕ Fin D.n → GaloisField 2 D.f) :
    D.psi0W (v + v') = D.psi0W v * D.psi0W v' :=
  Subtype.ext (D.psi0_add v v')

theorem psi0W_bijective : Function.Bijective D.psi0W := by
  constructor
  · intro v v' h
    exact D.psi0_injective (congrArg Subtype.val h)
  · intro w
    obtain ⟨v, hv⟩ := D.psi0_surjective_w w
    exact ⟨v, Subtype.ext hv⟩

end BigNatData

end CFSG.RankThree.GF2n.Tim79a
