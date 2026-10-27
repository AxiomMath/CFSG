module

public import CFSG.RankThree.GF2n.Stroth80.Sec108LeviX

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open Matrix
open scoped commutatorElement

variable {𝓜 : Type} [Group 𝓜] [Finite 𝓜] {K : Type} [Field K] [Finite K] [CharP K 2]
  {L R N Y : Subgroup 𝓜} {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

private theorem rho_eq_one_iff_mem_N (hC : Levi108 K L R N Y ρ μ T) {r : 𝓜} (hr : r ∈ R) :
    ρ ⟨r, hr⟩ = 1 ↔ r ∈ N := by
  rw [← MonoidHom.mem_ker, hC.ker_rho, Subgroup.mem_subgroupOf]

private theorem conj_mem_N_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {l n : 𝓜}
    (hl : l ∈ L) (hn : n ∈ N) : l * n * l⁻¹ ∈ N := by
  have hlR : l ∈ R := hC.L_le_R hl
  have hnR : n ∈ R := hC.N_le_R hn
  have hmemR : l * n * l⁻¹ ∈ R := R.mul_mem (R.mul_mem hlR hnR) (R.inv_mem hlR)
  rw [← rho_eq_one_iff_mem_N hC hmemR]
  have hsub : (⟨l * n * l⁻¹, hmemR⟩ : ↥R) = ⟨l, hlR⟩ * ⟨n, hnR⟩ * ⟨l, hlR⟩⁻¹ := rfl
  rw [hsub, map_mul, map_mul, map_inv]
  have hn1 : ρ ⟨n, hnR⟩ = 1 := (rho_eq_one_iff_mem_N hC hnR).mpr hn
  rw [hn1]
  simp

private theorem mu_conj_L_eq (hC : Levi108 K L R N Y ρ μ T) {l n : 𝓜} (hl : l ∈ L)
    {u : Fin 3 → K} (hu0 : u 0 = 0)
    (hu : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (e₀ K) u)
    (hn : n ∈ N) :
    Multiplicative.toAdd (μ ⟨l * n * l⁻¹, conj_mem_N_of_mem_L hC hl hn⟩) =
      Multiplicative.toAdd (μ ⟨n, hn⟩) - Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u :=
  hC.mu_conj_L hl hu0 hu hn (conj_mem_N_of_mem_L hC hl hn)

private theorem mem_N_of_commutator_eq_one (hC : Levi108 K L R N Y ρ μ T) {l n : 𝓜}
    (hl : l ∈ L) (hn : n ∈ N) (hnL : n ∉ L) (hc : ⁅l, n⁆ = 1) : l ∈ N := by
  obtain ⟨u, hu0, hu⟩ := hC.rho_L l hl
  have hn' : l * n * l⁻¹ ∈ N := conj_mem_N_of_mem_L hC hl hn
  have hmuc := mu_conj_L_eq hC hl hu0 hu hn
  have hln : l * n * l⁻¹ = n := by
    have h1 : l * n * l⁻¹ * n⁻¹ = 1 := by
      simpa only [commutatorElement_def] using hc
    exact mul_inv_eq_one.mp h1
  have hmu_eq : Multiplicative.toAdd (μ ⟨l * n * l⁻¹, hn'⟩) =
      Multiplicative.toAdd (μ ⟨n, hn⟩) := by
    have hsub : (⟨l * n * l⁻¹, hn'⟩ : ↥N) = ⟨n, hn⟩ := Subtype.ext hln
    rw [hsub]
  have hc0 : Multiplicative.toAdd (μ ⟨n, hn⟩) 0 ≠ 0 := by
    intro h0
    exact hnL ((hC.mem_L_iff_mu n hn).mpr h0)
  have hzero : Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u = 0 := by
    have h2 : Multiplicative.toAdd (μ ⟨n, hn⟩) =
        Multiplicative.toAdd (μ ⟨n, hn⟩) -
          Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u := hmu_eq.symm.trans hmuc
    have h2' : Multiplicative.toAdd (μ ⟨n, hn⟩) + 0 =
        Multiplicative.toAdd (μ ⟨n, hn⟩) +
          (-(Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u)) := by
      rw [add_zero]
      simpa [sub_eq_add_neg] using h2
    have hneg : -(Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u) = 0 :=
      (add_left_cancel h2').symm
    have hd : Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u = 0 := by
      simpa using congrArg Neg.neg hneg
    exact hd
  have hu_eq : u = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd h hc0
    · exact h
  have hrho : ρ ⟨l, hC.L_le_R hl⟩ = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hmat : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hu, hu_eq]
      simp
    simpa using congrFun₂ hmat i j
  exact (rho_eq_one_iff_mem_N hC (hC.L_le_R hl)).mp hrho

private theorem commutator_eq_one_of_mem_N (hC : Levi108 K L R N Y ρ μ T) {l n : 𝓜}
    (hlN : l ∈ N) (hn : n ∈ N) : ⁅l, n⁆ = 1 := by
  have hNcomm : N ≤ Subgroup.centralizer (N : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_N.1
  have hcomm : n * l = l * n := (Subgroup.mem_centralizer_iff.mp (hNcomm hlN)) n hn
  rw [commutatorElement_def, ← hcomm]
  group

private theorem commutator_eq_one_iff_mem_N (hC : Levi108 K L R N Y ρ μ T) {l n : 𝓜}
    (hl : l ∈ L) (hn : n ∈ N) (hnL : n ∉ L) : ⁅l, n⁆ = 1 ↔ l ∈ N :=
  ⟨mem_N_of_commutator_eq_one hC hl hn hnL, fun hlN =>
    commutator_eq_one_of_mem_N hC hlN hn⟩

private theorem exists_mem_N_not_mem_L (hC : Levi108 K L R N Y ρ μ T) :
    ∃ n ∈ N, n ∉ L := by
  obtain ⟨x, hx⟩ := hC.surjective_mu
    (Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K)))
  refine ⟨(x : 𝓜), x.2, fun hxL => ?_⟩
  have h0 : Multiplicative.toAdd (μ x) 0 = 0 :=
    (hC.mem_L_iff_mu (x : 𝓜) x.2).mp hxL
  rw [hx] at h0
  simpa using h0

private theorem commute_iff_mem_N_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {n l : 𝓜}
    (hn : n ∈ N) (hnL : n ∉ L) (hl : l ∈ L) : l * n = n * l ↔ l ∈ N := by
  constructor
  · intro hcomm
    have hc : ⁅l, n⁆ = 1 := by
      rw [commutatorElement_def, hcomm]
      group
    exact (commutator_eq_one_iff_mem_N hC hl hn hnL).mp hc
  · intro hlN
    have hNcomm : N ≤ Subgroup.centralizer (N : Set 𝓜) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_N.1
    exact ((Subgroup.mem_centralizer_iff.mp (hNcomm hlN)) n hn).symm

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

private theorem commute_of_commute_mul_of_commute {G : Type*} [Group G] {a b c : G}
    (h1 : a * (b * c) = (b * c) * a) (h2 : a * b = b * a) : a * c = c * a := by
  have h : b * (a * c) = b * (c * a) := by
    calc b * (a * c) = b * a * c := by rw [mul_assoc]
      _ = a * b * c := by rw [← h2]
      _ = a * (b * c) := by rw [mul_assoc]
      _ = (b * c) * a := h1
      _ = b * (c * a) := by rw [mul_assoc]
  exact mul_left_cancel h

private theorem mem_Nfrak_iff (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NL L)) :
    mkG L g ∈ Nfrak L Y ↔ (g : 𝓜) ∈ Subgroup.normalizer (Y : Set 𝓜) := by
  unfold Nfrak
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨h, hh, l, hl, hhl⟩
    have hh' : (h : 𝓜) ∈ Subgroup.normalizer (Y : Set 𝓜) := hh
    have hl' : (l : 𝓜) ∈ L := hl
    have hg : (h : 𝓜) * (l : 𝓜) = (g : 𝓜) :=
      congrArg (fun x : ↥(NL L) => (x : 𝓜)) hhl
    rw [← hg]
    exact (Subgroup.normalizer (Y : Set 𝓜)).mul_mem hh'
      (hC.R_le_normalizer_Y (hC.L_le_R hl'))
  · intro hg
    exact ⟨g, Subgroup.mem_subgroupOf.mpr hg, 1, (L.subgroupOf (NL L)).one_mem,
      by simp⟩

private theorem commute_of_commute_mul_of_commute_right {G : Type*} [Group G] {a b c : G}
    (h1 : a * (b * c) = (b * c) * a) (h2 : a * c = c * a) : a * b = b * a := by
  have h : (a * b) * c = (b * a) * c := by
    calc a * b * c = a * (b * c) := by rw [mul_assoc]
      _ = (b * c) * a := h1
      _ = b * (c * a) := by rw [mul_assoc]
      _ = b * (a * c) := by rw [h2]
      _ = b * a * c := by rw [mul_assoc]
  exact mul_right_cancel h

private theorem N_normal_subgroupOf_R (hC : Levi108 K L R N Y ρ μ T) :
    (N.subgroupOf R).Normal := by
  rw [← hC.ker_rho]
  exact MonoidHom.normal_ker ρ

private theorem conj_mem_N_of_mem_R (hC : Levi108 K L R N Y ρ μ T) {r n : 𝓜}
    (hr : r ∈ R) (hn : n ∈ N) : r * n * r⁻¹ ∈ N := by
  letI : (N.subgroupOf R).Normal := N_normal_subgroupOf_R hC
  have hnR : n ∈ R := hC.N_le_R hn
  have hconj : (⟨r, hr⟩ * ⟨n, hnR⟩ * ⟨r, hr⟩⁻¹ : ↥R) ∈ N.subgroupOf R :=
    Subgroup.Normal.conj_mem (inferInstance : (N.subgroupOf R).Normal)
      ⟨n, hnR⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨r, hr⟩
  exact Subgroup.mem_subgroupOf.mp hconj

private theorem matrix_conj_eq_of_fixed (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜}
    (hl : l ∈ L) {g : ↥(NL L)} (hgR : (g : 𝓜) ∈ R)
    (hfixg : (g : 𝓜) * l * (g : 𝓜)⁻¹ = l) :
    (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) := by
  have hgl : (g : 𝓜) * l * (g : 𝓜)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp g.2 l).mp hl
  have hglR : (g : 𝓜) * l * (g : 𝓜)⁻¹ ∈ R := hC.L_le_R hgl
  have h_eq_R : (⟨(g : 𝓜) * l * (g : 𝓜)⁻¹, hglR⟩ : ↥R) = ⟨l, hC.L_le_R hl⟩ :=
    Subtype.ext hfixg
  have hprod : (ρ ⟨(g : 𝓜) * l * (g : 𝓜)⁻¹, hglR⟩ : GL (Fin 3) K) =
      ρ ⟨(g : 𝓜), hgR⟩ * ρ ⟨l, hC.L_le_R hl⟩ * (ρ ⟨(g : 𝓜), hgR⟩)⁻¹ := by
    rw [show (⟨(g : 𝓜) * l * (g : 𝓜)⁻¹, hglR⟩ : ↥R) =
        ⟨(g : 𝓜), hgR⟩ * ⟨l, hC.L_le_R hl⟩ * ⟨(g : 𝓜), hgR⟩⁻¹ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv]
  have hGL : ρ ⟨(g : 𝓜), hgR⟩ * ρ ⟨l, hC.L_le_R hl⟩ * (ρ ⟨(g : 𝓜), hgR⟩)⁻¹ =
      ρ ⟨l, hC.L_le_R hl⟩ := hprod.symm.trans (congrArg ρ h_eq_R)
  have hmat := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hGL
  simpa [Matrix.GeneralLinearGroup.coe_inv] using hmat

private theorem first_col_eq_e0 (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NL L)}
    (hgX : mkG L g ∈ Xlevi L R) (hgR : (g : 𝓜) ∈ R) :
    (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ K = e₀ K := by
  have hgP0 : mkG L g ∈ P0frak L R := Xlevi_le_P0frak L R hgX
  have h00 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
    (hC.mem_P0frak_iff g hgR).mp hgP0
  have h10 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    ((hC.mem_normalizer_iff (g : 𝓜) hgR).mp g.2).1
  have h20 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    ((hC.mem_normalizer_iff (g : 𝓜) hgR).mp g.2).2
  rw [Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> simp [e₀, Matrix.col_apply, h00, h10, h20]

private theorem vecMul_inv_eq_self_of_matrix_conj (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hgR : (g : 𝓜) ∈ R) {u : Fin 3 → K}
    (hmat : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (1 + Matrix.vecMulVec (e₀ K) u) *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      1 + Matrix.vecMulVec (e₀ K) u)
    (hcol : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ K = e₀ K) :
    u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ = u := by
  have hgl : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
      (mul_inv_cancel (ρ ⟨(g : 𝓜), hgR⟩))
  have hgl' : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
      (inv_mul_cancel (ρ ⟨(g : 𝓜), hgR⟩))
  have hexp : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
      (1 + Matrix.vecMulVec (e₀ K) u) *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      1 + (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        Matrix.vecMulVec (e₀ K) u *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgl]
  have hEE : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
      Matrix.vecMulVec (e₀ K) u *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      Matrix.vecMulVec (e₀ K) u := by
    have h1 : 1 + (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        Matrix.vecMulVec (e₀ K) u *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
        1 + Matrix.vecMulVec (e₀ K) u := hexp.symm.trans hmat
    exact add_left_cancel h1
  have hrow : u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ = u := by
    have hEE' : Matrix.vecMulVec (e₀ K)
        (u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹) =
        Matrix.vecMulVec (e₀ K) u := by
      calc Matrix.vecMulVec (e₀ K)
            (u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹)
          = Matrix.vecMulVec ((ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ K)
              (u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹) := by
              rw [hcol]
        _ = (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
              Matrix.vecMulVec (e₀ K) u *
              (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ := by
              rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
        _ = Matrix.vecMulVec (e₀ K) u := hEE
    funext j
    have h := congrFun₂ hEE' 0 j
    simpa [e₀, Matrix.vecMulVec] using h
  exact hrow

private theorem vecMul_eq_self_of_matrix_conj (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NL L)}
    (hgR : (g : 𝓜) ∈ R) {u : Fin 3 → K}
    (hmat : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (1 + Matrix.vecMulVec (e₀ K) u) *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ =
      1 + Matrix.vecMulVec (e₀ K) u)
    (hcol : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ K = e₀ K) :
    u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = u := by
  have hrow := vecMul_inv_eq_self_of_matrix_conj hC hgR hmat hcol
  have hgl' : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
      (inv_mul_cancel (ρ ⟨(g : 𝓜), hgR⟩))
  have hrow' : u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = u := by
    have h1 : (u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹) ᵥ*
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) =
        u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) := by
      rw [hrow]
    rw [Matrix.vecMul_vecMul, hgl', Matrix.vecMul_one] at h1
    exact h1.symm
  exact hrow'

private theorem row_fixed_by_X (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L)
    (hfix : ∀ g : ↥(NL L), mkG L g ∈ Xlevi L R → (g : 𝓜) * l * (g : 𝓜)⁻¹ = l)
    {u : Fin 3 → K} (hu0 : u 0 = 0)
    (hu : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (e₀ K) u) :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (fun j : Fin 2 => u j.succ) ᵥ* (A : Matrix (Fin 2) (Fin 2) K) =
        fun j => u j.succ := by
  intro A
  obtain ⟨g, hgX, hgR, hblock⟩ := hC.exists_Xlevi_block A
  have hfixg : (g : 𝓜) * l * (g : 𝓜)⁻¹ = l := hfix g hgX
  have hmat := matrix_conj_eq_of_fixed hC hl hgR hfixg
  rw [hu] at hmat
  have hcol := first_col_eq_e0 hC hgX hgR
  have hrow' := vecMul_eq_self_of_matrix_conj hC hgR hmat hcol
  funext j
  have h := congrFun hrow' (Fin.succ j)
  have hleft : (u ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)) (Fin.succ j) =
      ((fun i : Fin 2 => u i.succ) ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) j := by
    have hb0 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 1 j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 j := by
      simpa using hblock 0 j
    have hb1 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 2 j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) 1 j := by
      simpa using hblock 1 j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hu0, hb0, hb1]
  rw [hleft] at h
  exact h

private theorem vecMul_eq_self_of_inv_transpose_conj (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hgR : (g : 𝓜) ∈ R) {v : Fin 3 → K}
    (hmuc' : v = (((ρ ⟨(g : 𝓜), hgR⟩)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ v) :
    v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = v := by
  rw [Matrix.GeneralLinearGroup.coe_inv] at hmuc'
  have hrow : v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ = v := by
    have h := Matrix.vecMul_transpose
      ((ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹)ᵀ v
    rw [Matrix.transpose_transpose] at h
    exact h.trans hmuc'.symm
  have hgl' : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹ *
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
      (inv_mul_cancel (ρ ⟨(g : 𝓜), hgR⟩))
  have hrow' : v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) = v := by
    have h1 : (v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)⁻¹) ᵥ*
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) =
        v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) := by
      rw [hrow]
    rw [Matrix.vecMul_vecMul, hgl', Matrix.vecMul_one] at h1
    exact h1.symm
  exact hrow'

private theorem mu_row_fixed_by_X (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L)
    (hlN : l ∈ N)
    (hfix : ∀ g : ↥(NL L), mkG L g ∈ Xlevi L R → (g : 𝓜) * l * (g : 𝓜)⁻¹ = l) :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (fun j : Fin 2 => Multiplicative.toAdd (μ ⟨l, hlN⟩) j.succ) ᵥ*
          (A : Matrix (Fin 2) (Fin 2) K) =
        fun j => Multiplicative.toAdd (μ ⟨l, hlN⟩) j.succ := by
  intro A
  obtain ⟨g, hgX, hgR, hblock⟩ := hC.exists_Xlevi_block A
  have hfixg : (g : 𝓜) * l * (g : 𝓜)⁻¹ = l := hfix g hgX
  have hl' : (g : 𝓜) * l * (g : 𝓜)⁻¹ ∈ N := conj_mem_N_of_mem_R hC hgR hlN
  have hmuc := hC.mu_conj (g : 𝓜) hgR l hlN ((g : 𝓜) * l * (g : 𝓜)⁻¹) hl' rfl
  have hmu_eq : Multiplicative.toAdd (μ ⟨(g : 𝓜) * l * (g : 𝓜)⁻¹, hl'⟩) =
      Multiplicative.toAdd (μ ⟨l, hlN⟩) := by
    have hsub : (⟨(g : 𝓜) * l * (g : 𝓜)⁻¹, hl'⟩ : ↥N) = ⟨l, hlN⟩ := Subtype.ext hfixg
    rw [hsub]
  have hmuc' : Multiplicative.toAdd (μ ⟨l, hlN⟩) =
      (((ρ ⟨(g : 𝓜), hgR⟩)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
        Multiplicative.toAdd (μ ⟨l, hlN⟩) := hmu_eq.symm.trans hmuc
  let v : Fin 3 → K := Multiplicative.toAdd (μ ⟨l, hlN⟩)
  have hrow' := vecMul_eq_self_of_inv_transpose_conj hC hgR hmuc'
  have hv0 : v 0 = 0 := (hC.mem_L_iff_mu l hlN).mp hl
  funext j
  have h := congrFun hrow' (Fin.succ j)
  have hleft : (v ᵥ* (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K)) (Fin.succ j) =
      ((fun i : Fin 2 => v i.succ) ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) j := by
    have hb0 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 1 j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 j := by
      simpa using hblock 0 j
    have hb1 : (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) 2 j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) 1 j := by
      simpa using hblock 1 j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hv0, hb0, hb1]
  rw [hleft] at h
  exact h

private theorem Y_le_L (hC : Levi108 K L R N Y ρ μ T) : Y ≤ L := by
  intro y hy
  have hyN : y ∈ N := hC.Y_le_N hy
  have hy1 : μ ⟨y, hyN⟩ = 1 := by
    have hmem : (⟨y, hyN⟩ : ↥N) ∈ μ.ker := by
      rw [hC.ker_mu]
      exact Subgroup.mem_subgroupOf.mpr hy
    exact MonoidHom.mem_ker.mp hmem
  exact (hC.mem_L_iff_mu y hyN).mpr (by rw [hy1]; rfl)

private theorem mem_Yhat_iff (hC : Levi108 K L R N Y ρ μ T) (x : ↥(NL L)) :
    mkG L x ∈ Yhat L N ↔ (x : 𝓜) ∈ N ⊔ L := by
  unfold Yhat
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    ← Subgroup.subgroupOf_sup hC.N_le_NL Subgroup.le_normalizer, Subgroup.mem_subgroupOf]

private theorem N_normal_in_sup (hC : Levi108 K L R N Y ρ μ T) :
    (N.subgroupOf (N ⊔ L)).Normal := by
  have hNR : (N.subgroupOf R).Normal := by
    rw [← hC.ker_rho]
    exact MonoidHom.normal_ker ρ
  have hR : R ≤ Subgroup.normalizer (N : Set 𝓜) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hC.N_le_R
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    ((sup_le hC.N_le_R hC.L_le_R).trans hR)

private theorem exists_mul_of_mem_sup_of_normal {G : Type*} [Group G] {N L K : Subgroup G}
    (hNK : N ≤ K) (hLK : L ≤ K) (hKL : K ≤ N ⊔ L)
    (hN : (N.subgroupOf K).Normal) {y : G} (hy : y ∈ K) :
    ∃ n ∈ N, ∃ l ∈ L, n * l = y := by
  letI : (N.subgroupOf K).Normal := hN
  have htop : (N.subgroupOf K) ⊔ (L.subgroupOf K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNK hLK, Subgroup.subgroupOf_eq_top.mpr hKL]
  have hyK : (⟨y, hy⟩ : ↥K) ∈ (N.subgroupOf K) ⊔ (L.subgroupOf K) := by
    rw [htop]
    trivial
  obtain ⟨n, hn, l, hl, hnl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := N.subgroupOf K) (t := L.subgroupOf K)).mp hyK
  refine ⟨(n : G), hn, (l : G), hl, ?_⟩
  have := congrArg (fun z : ↥K => (z : G)) hnl
  simpa using this

private theorem exists_l0_of_centralizing (hC : Levi108 K L R N Y ρ μ T) {g n : ↥(NL L)}
    (hcomm : mkG L g * mkG L n = mkG L n * mkG L g) :
    ∃ l₀ ∈ L, (g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹ = l₀ * (n : 𝓜) := by
  have hker : mkG L (g * n * g⁻¹ * n⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hmemL : ((g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹ * (n : 𝓜)⁻¹) ∈ L := by
    have h := hker
    change (((g * n * g⁻¹ * n⁻¹ : ↥(NL L)) : GG L) = 1) at h
    rw [QuotientGroup.eq_one_iff] at h
    exact h
  refine ⟨(g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹ * (n : 𝓜)⁻¹, hmemL, ?_⟩
  group

private theorem conj_mem_inf_of_conj_eq (hC : Levi108 K L R N Y ρ μ T) {g n : ↥(NL L)}
    (hnN : (n : 𝓜) ∈ N) (hnL : (n : 𝓜) ∉ L) {l₀ : 𝓜} (hl₀ : l₀ ∈ L)
    (hconjN : (g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹ = l₀ * (n : 𝓜)) :
    ∀ x ∈ L ⊓ N, (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ L ⊓ N := by
  have hNcomm : N ≤ Subgroup.centralizer (N : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_N.1
  have hLcomm : L ≤ Subgroup.centralizer (L : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_L.1
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxN : x ∈ N := hx.2
  have hgxL : (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp g.2 x).mp hxL
  have hxn : x * (n : 𝓜) = (n : 𝓜) * x := by
    exact ((Subgroup.mem_centralizer_iff.mp (hNcomm hxN)) n hnN).symm
  have hconj_comm : ((g : 𝓜) * x * (g : 𝓜)⁻¹) *
      ((g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹) =
      ((g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹) * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by
    calc (g : 𝓜) * x * (g : 𝓜)⁻¹ * ((g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹)
        = (g : 𝓜) * (x * (n : 𝓜)) * (g : 𝓜)⁻¹ := by group
      _ = (g : 𝓜) * ((n : 𝓜) * x) * (g : 𝓜)⁻¹ := by rw [hxn]
      _ = (g : 𝓜) * (n : 𝓜) * (g : 𝓜)⁻¹ * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by group
  have h1 : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * (l₀ * (n : 𝓜)) =
      (l₀ * (n : 𝓜)) * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by
    rw [← hconjN]
    exact hconj_comm
  have h2 : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * l₀ =
      l₀ * ((g : 𝓜) * x * (g : 𝓜)⁻¹) :=
    ((Subgroup.mem_centralizer_iff.mp (hLcomm hgxL)) l₀ hl₀).symm
  have hgn : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * (n : 𝓜) =
      (n : 𝓜) * ((g : 𝓜) * x * (g : 𝓜)⁻¹) :=
    commute_of_commute_mul_of_commute h1 h2
  have hgxN : (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ N :=
    (commute_iff_mem_N_of_mem_L hC hnN hnL hgxL).mp hgn
  exact ⟨hgxL, hgxN⟩

theorem Levi108.centralizer_le_Nfrak (hC : Levi108 K L R N Y ρ μ T) {r : GG L}
    (hr : r ∈ Yhat L N) (hr1 : r ≠ 1) :
    Subgroup.centralizer ({r} : Set (GG L)) ≤ Nfrak L Y := by
  intro k hk
  obtain ⟨n, hnNsub, rfl⟩ := Subgroup.mem_map.mp hr
  have hnN : (n : 𝓜) ∈ N := hnNsub
  have hnL : (n : 𝓜) ∉ L := by
    intro hnLmem
    refine hr1 ?_
    change (n : GG L) = 1
    exact (QuotientGroup.eq_one_iff n).mpr (Subgroup.mem_subgroupOf.mpr hnLmem)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (NL L)) k
  have hcomm : mkG L g * mkG L n = mkG L n * mkG L g :=
    Subgroup.mem_centralizer_singleton_iff.mp hk
  obtain ⟨l₀, hl₀, hconjN⟩ := exists_l0_of_centralizing hC hcomm
  have hmem_inf := conj_mem_inf_of_conj_eq hC hnN hnL hl₀ hconjN
  have hgN : (g : 𝓜) ∈ Subgroup.normalizer ((L ⊓ N : Subgroup 𝓜) : Set 𝓜) :=
    mem_normalizer_of_conj_mem hmem_inf
  exact (mem_Nfrak_iff hC g).mpr (hC.normalizer_inf_le hgN)

private theorem conj_mem_sup_of_mem_normalizer_Yhat (hC : Levi108 K L R N Y ρ μ T)
    (g : ↥(NL L)) (hk : mkG L g ∈ Subgroup.normalizer (Yhat L N : Set (GG L))) :
    ∀ x ∈ (N ⊔ L : Subgroup 𝓜), (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ N ⊔ L := by
  have hKNL : N ⊔ L ≤ NL L := sup_le hC.N_le_NL Subgroup.le_normalizer
  intro x hx
  have hxNL : x ∈ NL L := hKNL hx
  have hxY : mkG L ⟨x, hxNL⟩ ∈ Yhat L N := (mem_Yhat_iff hC ⟨x, hxNL⟩).mpr hx
  have hy : mkG L g * mkG L ⟨x, hxNL⟩ * (mkG L g)⁻¹ ∈ Yhat L N :=
    (Subgroup.mem_normalizer_iff.mp hk (mkG L ⟨x, hxNL⟩)).mp hxY
  have hval : mkG L (g * ⟨x, hxNL⟩ * g⁻¹) =
      mkG L g * mkG L ⟨x, hxNL⟩ * (mkG L g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  exact (mem_Yhat_iff hC (g * ⟨x, hxNL⟩ * g⁻¹)).mp (hval ▸ hy)

private theorem exists_conj_n0_decomp (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NL L))
    (hgK : (g : 𝓜) ∈ Subgroup.normalizer ((N ⊔ L : Subgroup 𝓜) : Set 𝓜))
    (n₀ : 𝓜) (hn₀N : n₀ ∈ N) (hn₀L : n₀ ∉ L) :
    ∃ n₁ ∈ N, ∃ l₁ ∈ L, n₁ * l₁ = (g : 𝓜) * n₀ * (g : 𝓜)⁻¹ ∧ n₁ ∉ L := by
  have hgn₀K : (g : 𝓜) * n₀ * (g : 𝓜)⁻¹ ∈ N ⊔ L :=
    (Subgroup.mem_normalizer_iff.mp hgK n₀).mp (Subgroup.mem_sup_left hn₀N)
  obtain ⟨n₁, hn₁N, l₁, hl₁L, hn₁l₁⟩ :=
    exists_mul_of_mem_sup_of_normal (K := N ⊔ L) le_sup_left le_sup_right le_rfl
      (N_normal_in_sup hC) hgn₀K
  have hginv : (g : 𝓜)⁻¹ ∈ Subgroup.normalizer (L : Set 𝓜) :=
    (Subgroup.normalizer (L : Set 𝓜)).inv_mem g.2
  have hgn₀L : (g : 𝓜) * n₀ * (g : 𝓜)⁻¹ ∉ L := by
    intro hmem
    have hconjL : (g : 𝓜)⁻¹ * ((g : 𝓜) * n₀ * (g : 𝓜)⁻¹) * (g : 𝓜) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hginv
        ((g : 𝓜) * n₀ * (g : 𝓜)⁻¹)).mp hmem
      simpa using this
    exact hn₀L (by simpa [mul_assoc] using hconjL)
  refine ⟨n₁, hn₁N, l₁, hl₁L, hn₁l₁, ?_⟩
  intro hn₁
  exact hgn₀L (by rw [← hn₁l₁]; exact L.mul_mem hn₁ hl₁L)

private theorem conj_mem_inf_of_normalizes_sup (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NL L))
    {n₀ n₁ l₁ : 𝓜} (hn₀N : n₀ ∈ N) (hn₀L : n₀ ∉ L) (hn₁N : n₁ ∈ N)
    (hl₁L : l₁ ∈ L) (hn₁L : n₁ ∉ L)
    (hn₁l₁ : n₁ * l₁ = (g : 𝓜) * n₀ * (g : 𝓜)⁻¹) :
    ∀ x ∈ L ⊓ N, (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ L ⊓ N := by
  have hNcomm : N ≤ Subgroup.centralizer (N : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_N.1
  have hLcomm : L ≤ Subgroup.centralizer (L : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_L.1
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxN : x ∈ N := hx.2
  have hgxL : (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp g.2 x).mp hxL
  have hxn₀ : x * n₀ = n₀ * x :=
    ((Subgroup.mem_centralizer_iff.mp (hNcomm hxN)) n₀ hn₀N).symm
  have hconj_comm : ((g : 𝓜) * x * (g : 𝓜)⁻¹) *
      ((g : 𝓜) * n₀ * (g : 𝓜)⁻¹) =
      ((g : 𝓜) * n₀ * (g : 𝓜)⁻¹) * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by
    calc (g : 𝓜) * x * (g : 𝓜)⁻¹ * ((g : 𝓜) * n₀ * (g : 𝓜)⁻¹)
        = (g : 𝓜) * (x * n₀) * (g : 𝓜)⁻¹ := by group
      _ = (g : 𝓜) * (n₀ * x) * (g : 𝓜)⁻¹ := by rw [hxn₀]
      _ = (g : 𝓜) * n₀ * (g : 𝓜)⁻¹ * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by group
  have h1 : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * (n₁ * l₁) =
      (n₁ * l₁) * ((g : 𝓜) * x * (g : 𝓜)⁻¹) := by
    rw [hn₁l₁]
    exact hconj_comm
  have h2 : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * l₁ =
      l₁ * ((g : 𝓜) * x * (g : 𝓜)⁻¹) :=
    ((Subgroup.mem_centralizer_iff.mp (hLcomm hgxL)) l₁ hl₁L).symm
  have hgn₁ : ((g : 𝓜) * x * (g : 𝓜)⁻¹) * n₁ =
      n₁ * ((g : 𝓜) * x * (g : 𝓜)⁻¹) :=
    commute_of_commute_mul_of_commute_right h1 h2
  have hgxN : (g : 𝓜) * x * (g : 𝓜)⁻¹ ∈ N :=
    (commute_iff_mem_N_of_mem_L hC hn₁N hn₁L hgxL).mp hgn₁
  exact ⟨hgxL, hgxN⟩

theorem Levi108.normalizer_Yhat_le_Nfrak (hC : Levi108 K L R N Y ρ μ T) :
    Subgroup.normalizer (Yhat L N : Set (GG L)) ≤ Nfrak L Y := by
  intro k hk
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (NL L)) k
  obtain ⟨n₀, hn₀N, hn₀L⟩ := exists_mem_N_not_mem_L hC
  have hmemK := conj_mem_sup_of_mem_normalizer_Yhat hC g hk
  have hgK : (g : 𝓜) ∈ Subgroup.normalizer ((N ⊔ L : Subgroup 𝓜) : Set 𝓜) :=
    mem_normalizer_of_conj_mem hmemK
  obtain ⟨n₁, hn₁N, l₁, hl₁L, hn₁l₁, hn₁L⟩ :=
    exists_conj_n0_decomp hC g hgK n₀ hn₀N hn₀L
  have hmem_inf := conj_mem_inf_of_normalizes_sup hC g hn₀N hn₀L hn₁N hl₁L hn₁L hn₁l₁
  have hgN : (g : 𝓜) ∈ Subgroup.normalizer ((L ⊓ N : Subgroup 𝓜) : Set 𝓜) :=
    mem_normalizer_of_conj_mem hmem_inf
  exact (mem_Nfrak_iff hC g).mpr (hC.normalizer_inf_le hgN)

private theorem mem_N_of_fixed_by_X (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L)
    (hfix : ∀ g : ↥(NL L), mkG L g ∈ Xlevi L R → (g : 𝓜) * l * (g : 𝓜)⁻¹ = l) :
    l ∈ N := by
  obtain ⟨u, hu0, hu⟩ := hC.rho_L l hl
  let A₁ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.transvection (0 : Fin 2) (1 : Fin 2) 1,
      Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩
  let A₂ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.transvection (1 : Fin 2) (0 : Fin 2) 1,
      Matrix.det_transvection_of_ne 1 0 (by decide) 1⟩
  have hA₁ := row_fixed_by_X hC hl hfix hu0 hu A₁
  have hA₂ := row_fixed_by_X hC hl hfix hu0 hu A₂
  have hu1 : u 1 = 0 := by
    have h := congrFun hA₁ 1
    simpa [A₁, Matrix.transvection, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single] using h
  have hu2 : u 2 = 0 := by
    have h := congrFun hA₂ 0
    simpa [A₂, Matrix.transvection, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single] using h
  have hu_eq : u = 0 := by
    funext i
    fin_cases i <;> simp [hu0, hu1, hu2]
  have hrho : ρ ⟨l, hC.L_le_R hl⟩ = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hmat : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hu, hu_eq]
      simp
    simpa using congrFun₂ hmat i j
  exact (rho_eq_one_iff_mem_N hC (hC.L_le_R hl)).mp hrho

private theorem mem_Y_of_fixed_by_X_of_mem_N (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜}
    (hl : l ∈ L) (hlN : l ∈ N)
    (hfix : ∀ g : ↥(NL L), mkG L g ∈ Xlevi L R → (g : 𝓜) * l * (g : 𝓜)⁻¹ = l) :
    l ∈ Y := by
  let A₁ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.transvection (0 : Fin 2) (1 : Fin 2) 1,
      Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩
  let A₂ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.transvection (1 : Fin 2) (0 : Fin 2) 1,
      Matrix.det_transvection_of_ne 1 0 (by decide) 1⟩
  have hmu := mu_row_fixed_by_X hC hl hlN hfix
  have hv1 : Multiplicative.toAdd (μ ⟨l, hlN⟩) 1 = 0 := by
    have h := congrFun (hmu A₁) 1
    simpa [A₁, Matrix.transvection, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single] using h
  have hv2 : Multiplicative.toAdd (μ ⟨l, hlN⟩) 2 = 0 := by
    have h := congrFun (hmu A₂) 0
    simpa [A₂, Matrix.transvection, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single] using h
  have hv0 : Multiplicative.toAdd (μ ⟨l, hlN⟩) 0 = 0 :=
    (hC.mem_L_iff_mu l hlN).mp hl
  have hv : Multiplicative.toAdd (μ ⟨l, hlN⟩) = 0 := by
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2]
  have hmem : (⟨l, hlN⟩ : ↥N) ∈ Y.subgroupOf N := by
    rw [← hC.ker_mu, MonoidHom.mem_ker]
    exact toAdd_eq_zero.mp hv
  exact hmem

theorem Levi108.fix_Xlevi_iff (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L) :
    (∀ g : ↥(NL L), mkG L g ∈ Xlevi L R → (g : 𝓜) * l * (g : 𝓜)⁻¹ = l) ↔ l ∈ Y := by
  constructor
  · intro hfix
    have hlN : l ∈ N := mem_N_of_fixed_by_X hC hl hfix
    exact mem_Y_of_fixed_by_X_of_mem_N hC hl hlN hfix
  · intro hlY g hgX
    have hP : mkG L g ∈ Pfrak L R :=
      (P0frak_le_Pfrak (L := L) (R := R)) ((Xlevi_le_P0frak (L := L) (R := R)) hgX)
    have hgR : (g : 𝓜) ∈ R := hC.mem_R_of_mem_Pfrak hP
    have hcomm : (g : 𝓜) * l = l * (g : 𝓜) :=
      (Subgroup.mem_centralizer_iff.mp (hC.Y_le_centralizer hlY)) (g : 𝓜) hgR
    calc (g : 𝓜) * l * (g : 𝓜)⁻¹ = l * (g : 𝓜) * (g : 𝓜)⁻¹ := by rw [hcomm]
      _ = l := by rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_transport_of_centralizes_X (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hk : mkG L g ∈ Kfrak L R) {x : ↥(NL L)} (hxX : mkG L x ∈ Xlevi L R)
    {y : 𝓜} (hyL : y ∈ L) :
    ((g⁻¹ * x * g : ↥(NL L)) : 𝓜) * y * ((g⁻¹ * x * g : ↥(NL L)) : 𝓜)⁻¹ =
      (x : 𝓜) * y * (x : 𝓜)⁻¹ := by
  have hLcomm : L ≤ Subgroup.centralizer (L : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_L.1
  have hxcomm : mkG L x * mkG L g = mkG L g * mkG L x :=
    Subgroup.mem_centralizer_iff.mp hk (mkG L x) hxX
  have hxg : mkG L (g⁻¹ * x * g) = mkG L x := by
    rw [map_mul, map_mul, map_inv, mul_assoc, hxcomm]
    group
  have hker : mkG L (x⁻¹ * (g⁻¹ * x * g)) = 1 := by
    rw [map_mul, map_inv, hxg]
    group
  have hmemL : (x⁻¹ * (g⁻¹ * x * g) : ↥(NL L)) ∈ L.subgroupOf (NL L) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hker
  let l' : 𝓜 := ((x⁻¹ * (g⁻¹ * x * g) : ↥(NL L)) : 𝓜)
  have hl'L : l' ∈ L := hmemL
  have hxl : ((g⁻¹ * x * g : ↥(NL L)) : 𝓜) = (x : 𝓜) * l' := by
    dsimp [l']
    group
  have hly : l' * y = y * l' :=
    ((Subgroup.mem_centralizer_iff.mp (hLcomm hl'L)) y hyL).symm
  rw [hxl]
  calc (x : 𝓜) * l' * y * ((x : 𝓜) * l')⁻¹
      = (x : 𝓜) * (l' * y * l'⁻¹) * (x : 𝓜)⁻¹ := by group
    _ = (x : 𝓜) * y * (x : 𝓜)⁻¹ := by
        rw [hly]
        group

private theorem fixed_by_X_of_centralizes_X (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hk : mkG L g ∈ Kfrak L R) {y : 𝓜} (hy : y ∈ Y) (hyL : y ∈ L)
    (hgyL : (g : 𝓜) * y * (g : 𝓜)⁻¹ ∈ L) :
    ∀ x : ↥(NL L), mkG L x ∈ Xlevi L R →
      (x : 𝓜) * ((g : 𝓜) * y * (g : 𝓜)⁻¹) * (x : 𝓜)⁻¹ =
        (g : 𝓜) * y * (g : 𝓜)⁻¹ := by
  intro x hxX
  have hxR : (x : 𝓜) ∈ R :=
    hC.mem_R_of_mem_Pfrak
      ((P0frak_le_Pfrak (L := L) (R := R)) ((Xlevi_le_P0frak (L := L) (R := R)) hxX))
  have hinner := conj_transport_of_centralizes_X hC hk hxX hyL
  have hxy : (x : 𝓜) * y = y * (x : 𝓜) :=
    Subgroup.mem_centralizer_iff.mp (hC.Y_le_centralizer hy) (x : 𝓜) hxR
  calc (x : 𝓜) * ((g : 𝓜) * y * (g : 𝓜)⁻¹) * (x : 𝓜)⁻¹
      = (g : 𝓜) * (((g⁻¹ * x * g : ↥(NL L)) : 𝓜) * y *
          ((g⁻¹ * x * g : ↥(NL L)) : 𝓜)⁻¹) * (g : 𝓜)⁻¹ := by
          rw [show ((g⁻¹ * x * g : ↥(NL L)) : 𝓜) =
            (g : 𝓜)⁻¹ * (x : 𝓜) * (g : 𝓜) from rfl]
          group
    _ = (g : 𝓜) * ((x : 𝓜) * y * (x : 𝓜)⁻¹) * (g : 𝓜)⁻¹ := by rw [hinner]
    _ = (g : 𝓜) * y * (g : 𝓜)⁻¹ := by
        rw [hxy]
        group

theorem Levi108.Kfrak_le_Nfrak (hC : Levi108 K L R N Y ρ μ T) : Kfrak L R ≤ Nfrak L Y := by
  intro k hk
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (NL L)) k
  have hYleL : Y ≤ L := Y_le_L hC
  have hLcomm : L ≤ Subgroup.centralizer (L : Set 𝓜) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.elemAb_L.1
  have hmem : ∀ y ∈ Y, (g : 𝓜) * y * (g : 𝓜)⁻¹ ∈ Y := by
    intro y hy
    have hyL : y ∈ L := hYleL hy
    have hgyL : (g : 𝓜) * y * (g : 𝓜)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp g.2 y).mp hyL
    have hconj := fixed_by_X_of_centralizes_X hC hk hy hyL hgyL
    exact (hC.fix_Xlevi_iff hgyL).mp hconj
  exact (mem_Nfrak_iff hC g).mpr (mem_normalizer_of_conj_mem hmem)

theorem Levi108.normalizer_le_of_normal (hC : Levi108 K L R N Y ρ μ T)
    (hX : (Xlevi L R).Normal) :
    Subgroup.normalizer (L : Set 𝓜) ≤ Subgroup.normalizer (Y : Set 𝓜) := by
  intro g hg
  let gg : ↥(NL L) := ⟨g, hg⟩
  have hYleL : Y ≤ L := Y_le_L hC
  have hmem : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro y hy
    have hyL : y ∈ L := hYleL hy
    have hgyL : g * y * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hg y).mp hyL
    have hconj : ∀ x : ↥(NL L), mkG L x ∈ Xlevi L R →
        (x : 𝓜) * (g * y * g⁻¹) * (x : 𝓜)⁻¹ = g * y * g⁻¹ := by
      intro x hxX
      have hxgX : mkG L (gg⁻¹ * x * gg) ∈ Xlevi L R := by
        rw [map_mul, map_mul, map_inv]
        simpa using hX.conj_mem (mkG L x) hxX ((mkG L gg)⁻¹)
      have hinner : ((gg⁻¹ * x * gg : ↥(NL L)) : 𝓜) * y *
          ((gg⁻¹ * x * gg : ↥(NL L)) : 𝓜)⁻¹ = y :=
        (hC.fix_Xlevi_iff hyL).mpr hy (gg⁻¹ * x * gg) hxgX
      calc (x : 𝓜) * (g * y * g⁻¹) * (x : 𝓜)⁻¹
          = g * (((gg⁻¹ * x * gg : ↥(NL L)) : 𝓜) * y *
              ((gg⁻¹ * x * gg : ↥(NL L)) : 𝓜)⁻¹) * g⁻¹ := by
              rw [show ((gg⁻¹ * x * gg : ↥(NL L)) : 𝓜) =
                g⁻¹ * (x : 𝓜) * g from rfl]
              group
        _ = g * y * g⁻¹ := by rw [hinner]
    exact (hC.fix_Xlevi_iff hgyL).mp hconj
  exact mem_normalizer_of_conj_mem hmem

end CFSG.RankThree.GF2n.Stroth80.Sec108
