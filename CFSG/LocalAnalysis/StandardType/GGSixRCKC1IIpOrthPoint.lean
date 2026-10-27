module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
public import CFSG.ClassicalGroups.Orthogonal.EichlerNonsingularTwo
import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rck_pCore_le_rootGroup {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} (hF : ∀ a : F, a = 0 ∨ a = 1)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank F V) {z x : V}
    (hz0 : z ≠ 0) (hz : Q z = 0) (hzx : QuadraticMap.polar Q z x = 0) (hx : Q x = 1)
    (P : Subgroup (V ≃ₗ[F] V)) (hP2 : IsPGroup 2 P)
    (hPE : P ≤ CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hPc : ∀ g ∈ P, g * CFSG.ClassicalGroups.Orthogonal.eichler Q z x =
      CFSG.ClassicalGroups.Orthogonal.eichler Q z x * g)
    (hPn : ∀ a : V, Q a = 0 → QuadraticMap.polar Q z a = 0 → QuadraticMap.polar Q x a = 0 →
      ∀ g ∈ P, CFSG.ClassicalGroups.Orthogonal.eichler Q a x * g *
        (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ ∈ P) :
    P ≤ CFSG.ClassicalGroups.Orthogonal.rootGroup Q z := by
  classical
  set N : Submodule F V := Submodule.span F {z, x} with hN
  set M : Submodule F V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) N with hM
  have hM_orth : ∀ m ∈ M, ∀ n ∈ N, QuadraticMap.polar Q n m = 0 := by
    intro m hm n hn
    rw [hM] at hm
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hm) n hn
  have hM_iff : ∀ v : V, v ∈ M ↔ QuadraticMap.polar Q z v = 0 ∧
      QuadraticMap.polar Q x v = 0 := by
    intro v
    constructor
    · intro hv
      exact ⟨hM_orth v hv z (by
          rw [hN]; exact Submodule.subset_span (by simp)),
        hM_orth v hv x (by rw [hN]; exact Submodule.subset_span (by simp))⟩
    · rintro ⟨hz, hx⟩
      have hv : v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) N := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        rw [hN] at hn
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
        change QuadraticMap.polar Q (a • z + b • x) v = 0
        rw [QuadraticMap.polar_add_left,
          CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
          CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hz, hx]
        simp
      rwa [hM]
  have hzN : z ∈ N := by rw [hN]; exact Submodule.subset_span (by simp)
  have hxN : x ∈ N := by rw [hN]; exact Submodule.subset_span (by simp)
  have hNM : N ≤ M := by
    rw [hN, Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hvz | hvx
    · rw [hvz]
      exact (hM_iff z).mpr
        ⟨CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hz,
          by rw [QuadraticMap.polar_comm]; exact hzx⟩
    · rw [hvx]
      have hxx : QuadraticMap.polar Q x x = 0 := by
        rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hx, mul_one,
          CharTwo.two_eq_zero]
      exact (hM_iff x).mpr ⟨hzx, hxx⟩
  have hnegV : ∀ v : V, -v = v := fun v => by
    rw [← neg_one_smul F v, CharTwo.neg_eq (1 : F), one_smul]
  have h2V : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have hmemO : ∀ g ∈ P, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup Q (hPE hg)
  have hfixz : ∀ g ∈ P, g z = z := fun g hg =>
    (CFSG.ClassicalGroups.Orthogonal.fix_of_commute_eichler hF hQ hz0 hz hzx hx
      (hmemO g hg) (hPc g hg)).1
  have hfixx : ∀ g ∈ P, g x - x ∈ Submodule.span F {z} := fun g hg =>
    (CFSG.ClassicalGroups.Orthogonal.fix_of_commute_eichler hF hQ hz0 hz hzx hx
      (hmemO g hg) (hPc g hg)).2
  have hgxN : ∀ g ∈ P, g x ∈ N := by
    intro g hg
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfixx g hg)
    have hgx : g x = x + c • z := by rw [hc]; abel
    rw [hN, hgx]
    exact Submodule.add_mem _ hxN (Submodule.smul_mem _ _ hzN)
  have hgNle : ∀ g ∈ P, ∀ n ∈ N, g n ∈ N := by
    intro g hg n hn
    rw [hN] at hn
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
    rw [map_add, map_smul, map_smul, hfixz g hg]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hzN)
      (Submodule.smul_mem _ _ (hgxN g hg))
  have hcomm_inv : ∀ g ∈ P, g⁻¹ * CFSG.ClassicalGroups.Orthogonal.eichler Q z x =
      CFSG.ClassicalGroups.Orthogonal.eichler Q z x * g⁻¹ := by
    intro g hg
    have h := congrArg (fun t : V ≃ₗ[F] V => g⁻¹ * t * g⁻¹) (hPc g hg)
    simpa [mul_assoc] using h.symm
  have hfix_inv : ∀ g ∈ P, g⁻¹ z = z ∧
      g⁻¹ x - x ∈ Submodule.span F {z} := fun g hg =>
    CFSG.ClassicalGroups.Orthogonal.fix_of_commute_eichler hF hQ hz0 hz hzx hx
      (inv_mem (hmemO g hg)) (hcomm_inv g hg)
  have hgxN_inv : ∀ g ∈ P, g⁻¹ x ∈ N := by
    intro g hg
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix_inv g hg).2
    have hgx : g⁻¹ x = x + c • z := by rw [hc]; abel
    rw [hN, hgx]
    exact Submodule.add_mem _ hxN (Submodule.smul_mem _ _ hzN)
  have hMpres : ∀ g ∈ P, ∀ m ∈ M, g m ∈ M := by
    intro g hg m hm
    have hmz : QuadraticMap.polar Q z m = 0 := (hM_iff m).mp hm |>.1
    have hmx : QuadraticMap.polar Q x m = 0 := (hM_iff m).mp hm |>.2
    refine (hM_iff (g m)).mpr ⟨?_, ?_⟩
    · have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
        (inv_mem (hmemO g hg)) z (g m)
      rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
      rw [← h, (hfix_inv g hg).1]
      exact hmz
    · have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
        (inv_mem (hmemO g hg)) x (g m)
      rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
      rw [← h]
      exact hM_orth m hm (g⁻¹ x) (hgxN_inv g hg)
  have hcoeff : ∀ {g : V ≃ₗ[F] V}, g ∈ P → ∀ {m : V}, m ∈ M → ∀ {α β : F},
      g m - m = α • z + β • x → β = 0 := by
    intro g hg m hm α β h
    have hgm : g m = m + (α • z + β • x) := by rw [← h]; abel
    have hmz : QuadraticMap.polar Q m z = 0 := by
      rw [QuadraticMap.polar_comm]; exact hM_orth m hm z hzN
    have hmx : QuadraticMap.polar Q m x = 0 := by
      rw [QuadraticMap.polar_comm]; exact hM_orth m hm x hxN
    have hBt : QuadraticMap.polar Q m (α • z + β • x) = 0 := by
      rw [QuadraticMap.polar_add_right,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hmz, hmx]
      simp
    have hQt : Q (α • z + β • x) = β * β := by
      rw [QuadraticMap.map_add Q (α • z) (β • x), QuadraticMap.map_smul,
        QuadraticMap.map_smul, hz, hx,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hzx]
      simp [smul_eq_mul]
    have hQgm : Q (g m) = Q m + β * β := by
      rw [hgm, QuadraticMap.map_add Q m (α • z + β • x), hQt, hBt, add_zero]
    have hEq : Q m + β * β = Q m := by
      rw [← hQgm, CFSG.ClassicalGroups.Orthogonal.map_of_mem (hmemO g hg) m]
    have hβ2 : β * β = 0 := by
      have h' : Q m + β * β = Q m + 0 := by rw [add_zero]; exact hEq
      exact add_left_cancel h'
    exact mul_self_eq_zero.mp hβ2
  have hzM : z ∈ M := hNM hzN
  have hxM : x ∈ M := hNM hxN
  set M₀ : Submodule F V :=
    M ⊓ ⨅ g : P, N.comap
      (((g : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id) with hM₀
  have hM₀_iff : ∀ v : V, v ∈ M₀ ↔ v ∈ M ∧
      ∀ g : P, ((g : V ≃ₗ[F] V) v - v) ∈ N := by
    intro v
    rw [hM₀, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨hm, hg⟩
      refine ⟨hm, fun g => ?_⟩
      have := hg g
      rw [Submodule.mem_comap] at this
      simpa using this
    · rintro ⟨hm, hg⟩
      refine ⟨hm, fun g => ?_⟩
      rw [Submodule.mem_comap]
      simpa using hg g
  have hNM₀ : N ≤ M₀ := by
    intro n hn
    rw [hM₀_iff]
    refine ⟨hNM hn, fun g => ?_⟩
    exact N.sub_mem (hgNle (g : V ≃ₗ[F] V) g.2 n hn) hn
  let act : P →* Module.End F M :=
    { toFun := fun g => LinearMap.codRestrict M
        (((g : V ≃ₗ[F] V) : V →ₗ[F] V).comp M.subtype)
        (fun m => hMpres (g : V ≃ₗ[F] V) g.2 (m : V) m.2)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro g h
        ext m
        rfl }
  let W : Submodule F M := N.comap M.subtype
  have hWle : ∀ g : P, W ≤ W.comap (act g) := by
    intro g m hm
    rw [Submodule.mem_comap]
    change (((act g) m : M) : V) ∈ N
    rw [show (((act g) m : M) : V) = (g : V ≃ₗ[F] V) ((m : M) : V) from rfl]
    exact hgNle (g : V ≃ₗ[F] V) g.2 ((m : M) : V) hm
  let ρQ : Representation F P (M ⧸ W) := Representation.quotient act W hWle
  have hNfin : Module.finrank F N ≤ 2 := by
    rw [hN]
    have h := finrank_span_finset_le_card (R := F) ({z, x} : Finset V)
    have h2 : (({z, x} : Finset V) : Set V) = {z, x} := by simp
    rw [Set.finrank, h2] at h
    exact h.trans Finset.card_le_two
  have hMfin : 4 ≤ Module.finrank F M := by
    have h := LinearMap.BilinForm.finrank_orthogonal
      (B := QuadraticMap.polarBilin Q) hQ N
    rw [← hM] at h
    omega
  have hNMne : N ≠ M := by
    intro hEq
    rw [hEq] at hNfin
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    have hMN : M ≤ N := by
      intro m hm
      have hmW : (⟨m, hm⟩ : M) ∈ W := by
        rw [htop]
        exact Submodule.mem_top
      exact hmW
    have hle := Submodule.finrank_mono hMN
    omega
  have hnt : Nontrivial (M ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hWtop
  obtain ⟨q, hq0, hqfix⟩ :=
    @Representation.exists_common_fixed_vector_of_isPGroup F P (M ⧸ W) _ _ _ _
      2 (expChar_prime (R := F) 2) (inferInstance) hnt hP2 ρQ
  obtain ⟨m₀, rfl⟩ := Submodule.mkQ_surjective W q
  have hm₀N : M.subtype m₀ ∉ N := by
    intro h
    apply hq0
    rw [show (0 : M ⧸ W) = Submodule.mkQ W 0 from rfl]
    exact (Submodule.Quotient.eq W).mpr (by
      have h' : M.subtype (m₀ - 0) ∈ N := by simpa using h
      exact h')
  have hm₀M : M.subtype m₀ ∈ M := m₀.2
  have hm₀M₀ : M.subtype m₀ ∈ M₀ := by
    rw [hM₀_iff]
    refine ⟨hm₀M, fun g => ?_⟩
    have hfixg : ρQ g (Submodule.mkQ W m₀) = Submodule.mkQ W m₀ := hqfix g
    simp only [ρQ, Representation.quotient_apply] at hfixg
    have hsub : (act g) m₀ - m₀ ∈ W := (Submodule.Quotient.eq W).mp hfixg
    have hsub' : M.subtype ((act g) m₀ - m₀) ∈ N := by simpa [W] using hsub
    rw [map_sub] at hsub'
    have hcoe : M.subtype ((act g) m₀) = (g : V ≃ₗ[F] V) (M.subtype m₀) := rfl
    rwa [hcoe] at hsub'
  have hM₀ne : M₀ ≠ N := by
    intro hEq
    exact hm₀N (hEq ▸ hm₀M₀)
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := fun x y h => by
    rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
    rwa [QuadraticMap.polar_comm]
  have hMorth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) M = N := by
    rw [hM, LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl N]
  have hMpres_inv : ∀ {g : V ≃ₗ[F] V},
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → g⁻¹ z = z → g⁻¹ x ∈ N →
        ∀ m ∈ M, g m ∈ M := by
    intro g hgO hgiz hgix m hm
    have hmz : QuadraticMap.polar Q z m = 0 := (hM_iff m).mp hm |>.1
    have hmx : QuadraticMap.polar Q x m = 0 := (hM_iff m).mp hm |>.2
    refine (hM_iff (g m)).mpr ⟨?_, ?_⟩
    · have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (inv_mem hgO) z (g m)
      rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
      rw [← h, hgiz]
      exact hmz
    · have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (inv_mem hgO) x (g m)
      rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
      rw [← h]
      exact hM_orth m hm (g⁻¹ x) hgix
  have hstab : ∀ (a : V), Q a = 0 → QuadraticMap.polar Q z a = 0 →
      QuadraticMap.polar Q a x = 0 → ∀ m ∈ M₀,
        CFSG.ClassicalGroups.Orthogonal.eichler Q a x m ∈ M₀ := by
    intro a ha haz hax m hm
    set h : V ≃ₗ[F] V := CFSG.ClassicalGroups.Orthogonal.eichler Q a x with hh
    have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [hh]
      exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup Q a x
    have hhz : h z = z := by
      rw [hh, CFSG.ClassicalGroups.Orthogonal.eichler_apply ha hax]
      simp [haz, hzx]
    have hxx : QuadraticMap.polar Q x x = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hx, mul_one]
      exact CharTwo.two_eq_zero
    have hax' : QuadraticMap.polar Q x a = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hax
    have hhx : h x = x := by
      rw [hh, CFSG.ClassicalGroups.Orthogonal.eichler_apply ha hax]
      simp [hax', hxx]
    have hN_img : ∀ n ∈ N, h n ∈ N := by
      intro n hn
      rw [hN] at hn
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hn
      rw [map_add, map_smul, map_smul, hhz, hhx]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hzN)
        (Submodule.smul_mem _ _ hxN)
    have hh_inv : h⁻¹ = h := by
      rw [hh, CFSG.ClassicalGroups.Orthogonal.eichler_inv hax, hnegV x]
    have hhiz : h⁻¹ z = z := by rw [hh_inv, hhz]
    have hhix : h⁻¹ x ∈ N := by rw [hh_inv]; exact hN_img x hxN
    have hM_img : ∀ m ∈ M, h m ∈ M := hMpres_inv (g := h) hhO hhiz hhix
    have hmM : m ∈ M := ((hM₀_iff m).mp hm).1
    have hmfix : ∀ g : P, ((g : V ≃ₗ[F] V) m - m) ∈ N := ((hM₀_iff m).mp hm).2
    rw [hM₀_iff]
    refine ⟨hM_img m hmM, fun g => ?_⟩
    have hg'P : h⁻¹ * (g : V ≃ₗ[F] V) * h ∈ P := by
      have hax'' : QuadraticMap.polar Q x a = 0 := by
        rw [QuadraticMap.polar_comm]
        exact hax
      have h1 : CFSG.ClassicalGroups.Orthogonal.eichler Q a x * (g : V ≃ₗ[F] V) *
          (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ ∈ P :=
        hPn a ha haz hax'' (g : V ≃ₗ[F] V) g.2
      rw [← hh] at h1
      rwa [← hh_inv, inv_inv] at h1
    have hmul : (g : V ≃ₗ[F] V) * h = h * (h⁻¹ * (g : V ≃ₗ[F] V) * h) := by
      rw [← mul_assoc h (h⁻¹ * (g : V ≃ₗ[F] V)) h,
        ← mul_assoc h h⁻¹ (g : V ≃ₗ[F] V), mul_inv_cancel, one_mul]
    have hdiff : (g : V ≃ₗ[F] V) (h m) - h m =
        h ((h⁻¹ * (g : V ≃ₗ[F] V) * h) m - m) := by
      calc (g : V ≃ₗ[F] V) (h m) - h m
          = ((g : V ≃ₗ[F] V) * h) m - h m := rfl
        _ = (h * (h⁻¹ * (g : V ≃ₗ[F] V) * h)) m - h m := by rw [hmul]
        _ = h ((h⁻¹ * (g : V ≃ₗ[F] V) * h) m) - h m := rfl
        _ = h ((h⁻¹ * (g : V ≃ₗ[F] V) * h) m - m) := by rw [map_sub]
    rw [hdiff]
    exact hN_img _ (hmfix ⟨h⁻¹ * (g : V ≃ₗ[F] V) * h, hg'P⟩)
  have hkey : ∀ m ∈ M, QuadraticMap.polar Q (M.subtype m₀) m ≠ 0 → m ∈ M₀ := by
    intro m hm hBm
    by_cases hq : Q m = 0
    · have hmz : QuadraticMap.polar Q z m = 0 := (hM_iff m).mp hm |>.1
      have hmx : QuadraticMap.polar Q m x = 0 := by
        rw [QuadraticMap.polar_comm]
        exact (hM_iff m).mp hm |>.2
      have hhm : CFSG.ClassicalGroups.Orthogonal.eichler Q m x (M.subtype m₀) ∈ M₀ :=
        hstab m hq hmz hmx (M.subtype m₀) hm₀M₀
      have hBm0x : QuadraticMap.polar Q (M.subtype m₀) x = 0 := by
        rw [QuadraticMap.polar_comm]
        exact hM_orth (M.subtype m₀) hm₀M x hxN
      have hdiff : CFSG.ClassicalGroups.Orthogonal.eichler Q m x (M.subtype m₀) -
          M.subtype m₀ = QuadraticMap.polar Q (M.subtype m₀) m • (x + m) := by
        rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hq hmx]
        simp only [hBm0x, hx, zero_add, one_mul]
        simp only [sub_eq_add_neg, hnegV]
        have h1 : M.subtype m₀ + QuadraticMap.polar Q (M.subtype m₀) m • x +
            QuadraticMap.polar Q (M.subtype m₀) m • m + M.subtype m₀ =
            (M.subtype m₀ + M.subtype m₀) +
              (QuadraticMap.polar Q (M.subtype m₀) m • x +
                QuadraticMap.polar Q (M.subtype m₀) m • m) := by
          abel
        rw [h1, h2V (M.subtype m₀), zero_add, ← smul_add]
      have hscale : QuadraticMap.polar Q (M.subtype m₀) m • (x + m) ∈ M₀ := by
        have h := M₀.sub_mem hhm hm₀M₀
        rwa [hdiff] at h
      have hsum : x + m ∈ M₀ := by
        have h := M₀.smul_mem (QuadraticMap.polar Q (M.subtype m₀) m)⁻¹ hscale
        rwa [smul_smul, inv_mul_cancel₀ hBm, one_smul] at h
      have hxm : x ∈ M₀ := hNM₀ hxN
      have := M₀.sub_mem hsum hxm
      simpa using this
    · have hq1 : Q m = 1 := (hF (Q m)).resolve_left hq
      have hmx : QuadraticMap.polar Q m x = 0 := by
        rw [QuadraticMap.polar_comm]
        exact (hM_iff m).mp hm |>.2
      have hQmx : Q (m + x) = 0 := by
        rw [QuadraticMap.map_add Q m x, hq1, hx, hmx, add_zero]
        exact CharTwo.add_self_eq_zero 1
      have hzmx : QuadraticMap.polar Q z (m + x) = 0 := by
        rw [QuadraticMap.polar_add_right, (hM_iff m).mp hm |>.1, hzx, add_zero]
      have hmxx : QuadraticMap.polar Q (m + x) x = 0 := by
        rw [QuadraticMap.polar_add_left, hmx]
        have hxx0 : QuadraticMap.polar Q x x = 0 := by
          rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hx, mul_one,
            CharTwo.two_eq_zero]
        rw [hxx0, add_zero]
      have hhm : CFSG.ClassicalGroups.Orthogonal.eichler Q (m + x) x (M.subtype m₀) ∈ M₀ :=
        hstab (m + x) hQmx hzmx hmxx (M.subtype m₀) hm₀M₀
      have hBm0x : QuadraticMap.polar Q (M.subtype m₀) x = 0 := by
        rw [QuadraticMap.polar_comm]
        exact hM_orth (M.subtype m₀) hm₀M x hxN
      have hBmx : QuadraticMap.polar Q (M.subtype m₀) (m + x) ≠ 0 := by
        rw [QuadraticMap.polar_add_right, hBm0x, add_zero]
        exact hBm
      have hxm' : x + (m + x) = m := by
        calc x + (m + x) = (x + m) + x := by rw [add_assoc]
          _ = m + (x + x) := by abel
          _ = m := by rw [show x + x = 0 from h2V x, add_zero]
      have hdiff : CFSG.ClassicalGroups.Orthogonal.eichler Q (m + x) x (M.subtype m₀) -
          M.subtype m₀ = QuadraticMap.polar Q (M.subtype m₀) (m + x) • m := by
        rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hQmx hmxx]
        simp only [hBm0x, hx, zero_add, one_mul]
        simp only [sub_eq_add_neg, hnegV]
        have h1 : M.subtype m₀ + QuadraticMap.polar Q (M.subtype m₀) (m + x) • x +
            QuadraticMap.polar Q (M.subtype m₀) (m + x) • (m + x) + M.subtype m₀ =
            (M.subtype m₀ + M.subtype m₀) +
              (QuadraticMap.polar Q (M.subtype m₀) (m + x) • x +
                QuadraticMap.polar Q (M.subtype m₀) (m + x) • (m + x)) := by
          abel
        rw [h1, h2V (M.subtype m₀), zero_add, ← smul_add, hxm']
      have hscale : QuadraticMap.polar Q (M.subtype m₀) (m + x) • m ∈ M₀ := by
        have h := M₀.sub_mem hhm hm₀M₀
        rwa [hdiff] at h
      have h := M₀.smul_mem (QuadraticMap.polar Q (M.subtype m₀) (m + x))⁻¹ hscale
      rwa [smul_smul, inv_mul_cancel₀ hBmx, one_smul] at h
  have hm₁ex : ∃ m₁ ∈ M, QuadraticMap.polar Q (M.subtype m₀) m₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hm₀N
    have hm₀orth : (m₀ : V) ∈
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) M := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      change QuadraticMap.polar Q y (m₀ : V) = 0
      rw [QuadraticMap.polar_comm]
      exact hcon y hy
    rwa [hMorth] at hm₀orth
  have hM₀eq : M₀ = M := by
    apply le_antisymm
    · rw [hM₀]
      exact inf_le_left
    · intro m hm
      by_cases hBm : QuadraticMap.polar Q (M.subtype m₀) m = 0
      · obtain ⟨m₁, hm₁, hB₁⟩ := hm₁ex
        have hsum : m + m₁ ∈ M := M.add_mem hm hm₁
        have hBsum : QuadraticMap.polar Q (M.subtype m₀) (m + m₁) ≠ 0 := by
          rw [QuadraticMap.polar_add_right, hBm]
          simpa using hB₁
        have h1 : m + m₁ ∈ M₀ := hkey (m + m₁) hsum hBsum
        have h2 : m₁ ∈ M₀ := hkey m₁ hm₁ hB₁
        have := M₀.sub_mem h1 h2
        simpa using this
      · exact hkey m hm hBm
  have hspan : ∀ (g : V ≃ₗ[F] V), g ∈ P → ∀ v : V,
      QuadraticMap.polar Q z v = 0 → g v - v ∈ N := by
    intro g hg v hvz
    have hzero : ∀ m ∈ M, QuadraticMap.polar Q (g v - v) m = 0 := by
      intro m hm
      have hm₀ : m ∈ M₀ := by rwa [hM₀eq]
      have hgim : g⁻¹ m - m ∈ N :=
        ((hM₀_iff m).mp hm₀).2 ⟨g⁻¹, inv_mem hg⟩
      rw [hN] at hgim
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hgim
      have hβ : β = 0 := hcoeff (g := g⁻¹) (inv_mem hg) hm hαβ.symm
      have hαz : g⁻¹ m - m = α • z := by
        rw [← hαβ, hβ, zero_smul, add_zero]
      have hBgv : QuadraticMap.polar Q (g v) m =
          QuadraticMap.polar Q v (g⁻¹ m) := by
        have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (hmemO g hg) v (g⁻¹ m)
        rwa [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply'] at h
      calc QuadraticMap.polar Q (g v - v) m
          = QuadraticMap.polar Q (g v) m - QuadraticMap.polar Q v m := by
              rw [QuadraticMap.polar_sub_left]
        _ = QuadraticMap.polar Q v (g⁻¹ m) - QuadraticMap.polar Q v m := by rw [hBgv]
        _ = QuadraticMap.polar Q v (g⁻¹ m - m) := by rw [QuadraticMap.polar_sub_right]
        _ = QuadraticMap.polar Q v (α • z) := by rw [hαz]
        _ = α * QuadraticMap.polar Q v z := by
              rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq]
        _ = 0 := by
              have hvz' : QuadraticMap.polar Q v z = 0 := by
                rw [QuadraticMap.polar_comm]
                exact hvz
              rw [hvz', mul_zero]
    have horth : (g v - v) ∈
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) M := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro m hm
      change QuadraticMap.polar Q m (g v - v) = 0
      rw [QuadraticMap.polar_comm]
      exact hzero m hm
    rwa [hMorth] at horth
  intro g hg
  refine CFSG.ClassicalGroups.Orthogonal.mem_rootGroup_of_mem_elementaryGroup
    hQ hz0 hz hzx hx (hPE hg) (hfixz g hg) (fun v hv => ?_)
  have h := hspan g hg v hv
  rwa [hN] at h

private theorem rckOrthPointK2_via {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (GaloisField 2 1) (ι → GaloisField 2 1))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinAction Q))
    (hrange : (Spin.spinAction Q).range =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hcenter : Subgroup.center (spinGroup Q) = ⊥)
    (h6 : 6 ≤ Module.finrank (GaloisField 2 1) (ι → GaloisField 2 1))
    {X : Type} [Group X] [Finite X] {K V : Subgroup X} {r : X}
    (horth : OrthPointVia Q K V r) : K2At K V r := by
  classical
  obtain ⟨φ, r₀, V₀, z, x, hφrange, hφker, hφr, hr₀V₀, hV₀map,
    hz0, hz, hzx, hx, hspinr₀, hV₀root⟩ := horth
  let C : Subgroup (spinGroup Q) := Subgroup.centralizer ({r₀} : Set (spinGroup Q))
  let P' : Subgroup (spinGroup Q) := CFSG.Open.pCoreOf 2 C
  let P : Subgroup ((ι → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (ι → GaloisField 2 1)) := P'.map (Spin.spinAction Q)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (by rwa [hcenter] at hφker)
  have hK : K ⊓ Subgroup.centralizer ({r} : Set X) = C.map φ := by
    apply le_antisymm
    · rintro g ⟨hgK, hgC⟩
      rw [← hφrange] at hgK
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hgK
      refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
      have hgC' : φ s * r = r * φ s :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (show φ s ∈ Subgroup.centralizer ({r} : Set X) from hgC)
      change s ∈ Subgroup.centralizer ({r₀} : Set (spinGroup Q))
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      apply hφinj
      rw [map_mul, map_mul, hφr]
      exact hgC'
    · rintro g ⟨s, hsC, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hφrange]
        exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
      · have hsC' : s * r₀ = r₀ * s :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (show s ∈ Subgroup.centralizer ({r₀} : Set (spinGroup Q)) from hsC)
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc φ s * r = φ s * φ r₀ := by rw [hφr]
          _ = φ (s * r₀) := by rw [map_mul]
          _ = φ (r₀ * s) := by rw [hsC']
          _ = φ r₀ * φ s := by rw [map_mul]
          _ = r * φ s := by rw [hφr]
  have hpcmap : CFSG.Open.pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) =
      P'.map φ := by
    rw [hK]
    exact CFSG.GroupTheory.pCoreOf_map_of_injective 2 φ hφinj C
  have hP'2 : IsPGroup 2 P' :=
    (CFSG.pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hP2 : IsPGroup 2 P := hP'2.map (Spin.spinAction Q)
  have hPE : P ≤ CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q := by
    intro g hg
    have hg' : g ∈ (Spin.spinAction Q).range :=
      Subgroup.map_le_range (Spin.spinAction Q) P' hg
    rwa [hrange] at hg'
  have hPc : ∀ g ∈ P, g * CFSG.ClassicalGroups.Orthogonal.eichler Q z x =
      CFSG.ClassicalGroups.Orthogonal.eichler Q z x * g := by
    intro g hg
    obtain ⟨s, hsP', rfl⟩ := Subgroup.mem_map.mp hg
    have hsC : s ∈ C := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (H := C) hsP'
    have hcomm : s * r₀ = r₀ * s :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (show s ∈ Subgroup.centralizer ({r₀} : Set (spinGroup Q)) from hsC)
    calc Spin.spinAction Q s * CFSG.ClassicalGroups.Orthogonal.eichler Q z x
        = Spin.spinAction Q s * Spin.spinAction Q r₀ := by rw [hspinr₀]
      _ = Spin.spinAction Q (s * r₀) := by rw [map_mul]
      _ = Spin.spinAction Q (r₀ * s) := by rw [hcomm]
      _ = Spin.spinAction Q r₀ * Spin.spinAction Q s := by rw [map_mul]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler Q z x * Spin.spinAction Q s := by
            rw [hspinr₀]
  have hPn : ∀ a : ι → GaloisField 2 1, Q a = 0 → QuadraticMap.polar Q z a = 0 →
      QuadraticMap.polar Q x a = 0 → ∀ g ∈ P,
        CFSG.ClassicalGroups.Orthogonal.eichler Q a x * g *
          (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ ∈ P := by
    intro a ha haz hax g hg
    obtain ⟨s, hsP', rfl⟩ := Subgroup.mem_map.mp hg
    have hxx : QuadraticMap.polar Q x x = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hx, mul_one]
      exact CharTwo.two_eq_zero
    have hax' : QuadraticMap.polar Q a x = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hax
    have hHfix : CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
        CFSG.ClassicalGroups.Orthogonal.eichler Q z x *
        (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ =
        CFSG.ClassicalGroups.Orthogonal.eichler Q z x := by
      have hH : CFSG.ClassicalGroups.Orthogonal.eichler Q a x ∈
          TauCeti.QuadraticMap.orthogonalGroup Q :=
        CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup Q a x
      rw [CFSG.ClassicalGroups.Orthogonal.eichler_conj hH z x]
      congr 1
      · rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply ha hax']
        simp [haz, hzx]
      · rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply ha hax']
        simp [hax, hxx]
    have hcommE : CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
        CFSG.ClassicalGroups.Orthogonal.eichler Q z x =
        CFSG.ClassicalGroups.Orthogonal.eichler Q z x *
          CFSG.ClassicalGroups.Orthogonal.eichler Q a x := by
      have h := hHfix
      calc CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
            CFSG.ClassicalGroups.Orthogonal.eichler Q z x
          = CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
              CFSG.ClassicalGroups.Orthogonal.eichler Q z x *
              ((CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ *
                CFSG.ClassicalGroups.Orthogonal.eichler Q a x) := by
              rw [inv_mul_cancel, mul_one]
        _ = (CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
              CFSG.ClassicalGroups.Orthogonal.eichler Q z x *
              (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹) *
              CFSG.ClassicalGroups.Orthogonal.eichler Q a x := by
              simp only [mul_assoc]
        _ = CFSG.ClassicalGroups.Orthogonal.eichler Q z x *
              CFSG.ClassicalGroups.Orthogonal.eichler Q a x := by rw [h]
    have hEax_mem : CFSG.ClassicalGroups.Orthogonal.eichler Q a x ∈
        (Spin.spinAction Q).range := by
      rw [hrange]
      exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup Q a x
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hEax_mem
    have htC : t ∈ C := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      apply hinj
      rw [map_mul, map_mul, ht, hspinr₀]
      exact hcommE
    have htsP' : t * s * t⁻¹ ∈ P' := by
      have hnorm : t ∈
          Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set (spinGroup Q)) :=
        CFSG.StandardType.mem_normalizer_pCoreOf (p := 2) (H := C) htC
      exact (Subgroup.mem_normalizer_iff.mp hnorm s).mp hsP'
    have hfinal : CFSG.ClassicalGroups.Orthogonal.eichler Q a x *
        Spin.spinAction Q s *
        (CFSG.ClassicalGroups.Orthogonal.eichler Q a x)⁻¹ =
        Spin.spinAction Q (t * s * t⁻¹) := by
      rw [← ht, ← map_mul, ← map_inv, ← map_mul]
    rw [hfinal]
    exact Subgroup.mem_map.mpr ⟨t * s * t⁻¹, htsP', rfl⟩
  have hProot : P ≤ CFSG.ClassicalGroups.Orthogonal.rootGroup Q z :=
    rck_pCore_le_rootGroup (F := GaloisField 2 1)
      (V := ι → GaloisField 2 1) (Q := Q) (z := z) (x := x)
      rck1416_gf2_eq_zero_or_one hQ h6 hz0 hz hzx hx P hP2 hPE hPc hPn
  have hψP' : ∀ s ∈ P', Spin.spinAction Q s ∈
      CFSG.ClassicalGroups.Orthogonal.rootGroup Q z := fun s hs =>
    hProot (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  have hψV₀ : ∀ v ∈ V₀, Spin.spinAction Q v ∈
      CFSG.ClassicalGroups.Orthogonal.rootGroup Q z := fun v hv =>
    hV₀root (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)
  have hcent : ∀ s ∈ P', ∀ v ∈ V₀, s * v = v * s := by
    intro s hs v hv
    apply hinj
    rw [map_mul, map_mul]
    exact CFSG.ClassicalGroups.Orthogonal.rootGroup_commute (hψP' s hs) (hψV₀ v hv)
  change CFSG.Open.pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤
    Subgroup.normalizer (V : Set X)
  rw [hpcmap]
  rintro g ⟨s, hsP', rfl⟩
  refine Subgroup.centralizer_le_normalizer (V : Set X) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [← hV₀map] at hy
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
  calc φ v * φ s = φ (v * s) := by rw [map_mul]
    _ = φ (s * v) := by rw [hcent s hsP' v hv]
    _ = φ s * φ v := by rw [map_mul]

theorem rckOrthPointK2 : RCKOrthPointK2 := by
  rintro X _ _ K V r _hodd (⟨n, hn, horth⟩ | ⟨n, hn, horth⟩)
  · obtain ⟨hQ, hinj, hrange, hcenter, hfin⟩ := rck1416_quadPlus_facts hn
    exact rckOrthPointK2_via (Q := Spin.quadPlus n (GaloisField 2 1))
      hQ hinj hrange hcenter (by rw [hfin]; omega) horth
  · obtain ⟨hQ, hinj, hrange, hcenter, hfin⟩ := rck1416_quadMinus_facts hn
    exact rckOrthPointK2_via
      (Q := Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)
      hQ hinj hrange hcenter (by rw [hfin]; omega) horth

end CFSG.StandardType.RCKC1
