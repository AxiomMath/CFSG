module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private theorem rckRPlr_pow_card_eq_zero_of_isNilpotent {F : Type} [Field F] {n : Type}
    [Fintype n] [DecidableEq n] {N : Matrix n n F} (h : IsNilpotent N) :
    N ^ Fintype.card n = 0 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card n :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
  have h2 := Matrix.aeval_self_charpoly N
  rw [h1] at h2
  simpa using h2

private theorem rckRPlr_sub_one_pow_eq_zero {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    [CharP F 2] {x : GL (Fin n) F} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    ((x : Matrix (Fin n) (Fin n) F) - 1) ^ 2 ^ k = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hx' : ((x : Matrix (Fin n) (Fin n) F)) ^ 2 ^ k = 1 := by
    simpa using congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hx
  rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right _), hx', one_pow, sub_self]

private theorem rckRPlr_sub_one_pow_card_eq_zero {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    [CharP F 2] {x : GL (Fin n) F} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    ((x : Matrix (Fin n) (Fin n) F) - 1) ^ n = 0 := by
  have hnil : IsNilpotent ((x : Matrix (Fin n) (Fin n) F) - 1) :=
    ⟨2 ^ k, rckRPlr_sub_one_pow_eq_zero hn hx⟩
  have h := rckRPlr_pow_card_eq_zero_of_isNilpotent hnil
  simpa using h

private theorem rckRPlr_exists_pow_eq_one {n : ℕ} {F : Type} [Field F]
    {P : Subgroup (GL (Fin n) F)} (hP : IsPGroup 2 P) {x : GL (Fin n) F} (hx : x ∈ P) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg (fun g : ↥P => (g : GL (Fin n) F)) hk⟩

private theorem rckRPlr_sub_one_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) {F : Type}
    [Field F] [CharP F 2] {x : GL (Fin n) F} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    ((x : Matrix (Fin n) (Fin n) F) - 1) = 0 := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  · have hn0 : n = 0 := by omega
    subst hn0
    simpa using rckRPlr_sub_one_pow_card_eq_zero (n := 1) (by norm_num) hx

private theorem rckRPlr_toLin'_zero {F : Type} [Field F] :
    Matrix.toLin' (0 : Matrix (Fin 2) (Fin 2) F) = 0 := by
  ext v
  simp

private theorem rckRPlr_range_eq_ker_and_finrank {F : Type} [Field F]
    {N : Matrix (Fin 2) (Fin 2) F} (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    LinearMap.range (Matrix.toLin' N) = LinearMap.ker (Matrix.toLin' N) ∧
      Module.finrank F (LinearMap.range (Matrix.toLin' N)) = 1 := by
  let f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) := Matrix.toLin' N
  have hf : f = Matrix.toLin' N := rfl
  have hff : f.comp f = 0 := by
    rw [hf, ← Matrix.toLin'_mul, hN2]
    ext v
    simp
  have hle : LinearMap.range f ≤ LinearMap.ker f := LinearMap.range_le_ker_iff.mpr hff
  have hne : LinearMap.range f ≠ ⊥ := by
    rw [hf]
    intro h0
    rw [LinearMap.range_eq_bot] at h0
    exact hN0 (Matrix.toLin'.injective (h0.trans rckRPlr_toLin'_zero.symm))
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  have hV : Module.finrank F (Fin 2 → F) = 2 := by simp
  rw [hV] at hsum
  have hge : 1 ≤ Module.finrank F (LinearMap.range f) := by
    rw [Submodule.one_le_finrank_iff]
    exact hne
  have hfr : Module.finrank F (LinearMap.range f) = 1 := by
    have hle' : Module.finrank F (LinearMap.range f) ≤
        Module.finrank F (LinearMap.ker f) := Submodule.finrank_mono hle
    omega
  have hfk : Module.finrank F (LinearMap.ker f) = 1 := by omega
  refine ⟨Submodule.eq_of_le_of_finrank_eq hle ?_, ?_⟩
  · rw [hfr, hfk]
  · rw [← hf]
    exact hfr

private theorem rckRPlr_range_eq_of_sq_zero_of_commute {F : Type} [Field F]
    {N M : Matrix (Fin 2) (Fin 2) F} (hN2 : N * N = 0) (hM2 : M * M = 0)
    (hNM : N * M = M * N) (hN0 : N ≠ 0) (hM0 : M ≠ 0) :
    LinearMap.range (Matrix.toLin' N) = LinearMap.range (Matrix.toLin' M) := by
  by_contra hne
  have hN := rckRPlr_range_eq_ker_and_finrank hN2 hN0
  have hM := rckRPlr_range_eq_ker_and_finrank hM2 hM0
  let I : Submodule F (Fin 2 → F) :=
    LinearMap.range (Matrix.toLin' N) ⊓ LinearMap.range (Matrix.toLin' M)
  have hI_le_N : I ≤ LinearMap.range (Matrix.toLin' N) := by
    dsimp [I]
    exact inf_le_left
  have hI_le_M : I ≤ LinearMap.range (Matrix.toLin' M) := by
    dsimp [I]
    exact inf_le_right
  have hinf : I = ⊥ := by
    by_contra hbot
    have h1 : Module.finrank F ↥I = 1 := by
      apply le_antisymm
      · calc Module.finrank F ↥I
            ≤ Module.finrank F ↥(LinearMap.range (Matrix.toLin' N)) :=
              Submodule.finrank_mono hI_le_N
          _ = 1 := hN.2
      · rw [Submodule.one_le_finrank_iff]
        exact hbot
    have heqN : I = LinearMap.range (Matrix.toLin' N) :=
      Submodule.eq_of_le_of_finrank_eq hI_le_N (by rw [h1, hN.2])
    have heqM : I = LinearMap.range (Matrix.toLin' M) :=
      Submodule.eq_of_le_of_finrank_eq hI_le_M (by rw [h1, hM.2])
    exact hne (heqN.symm.trans heqM)
  have hzero : ∀ w : Fin 2 → F, Matrix.toLin' M w = 0 := by
    intro w
    have h1 : Matrix.toLin' N (Matrix.toLin' M w) = 0 := by
      have hmem : Matrix.toLin' N (Matrix.toLin' M w) ∈ I := by
        change Matrix.toLin' N (Matrix.toLin' M w) ∈
          LinearMap.range (Matrix.toLin' N) ⊓ LinearMap.range (Matrix.toLin' M)
        refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self _ _, ?_⟩
        have he : Matrix.toLin' N (Matrix.toLin' M w) =
            Matrix.toLin' M (Matrix.toLin' N w) := by
          calc Matrix.toLin' N (Matrix.toLin' M w)
              = Matrix.toLin' (N * M) w := by rw [Matrix.toLin'_mul]; rfl
            _ = Matrix.toLin' (M * N) w := by rw [hNM]
            _ = Matrix.toLin' M (Matrix.toLin' N w) := by rw [Matrix.toLin'_mul]; rfl
        rw [he]
        exact LinearMap.mem_range_self _ _
      rwa [hinf, Submodule.mem_bot] at hmem
    have h2 : Matrix.toLin' M w ∈ LinearMap.range (Matrix.toLin' N) := by
      rw [hN.1]
      exact LinearMap.mem_ker.mpr h1
    have hmem : Matrix.toLin' M w ∈ I := by
      change Matrix.toLin' M w ∈
        LinearMap.range (Matrix.toLin' N) ⊓ LinearMap.range (Matrix.toLin' M)
      exact Submodule.mem_inf.mpr ⟨h2, LinearMap.mem_range_self _ _⟩
    rwa [hinf, Submodule.mem_bot] at hmem
  have hMzero : M = 0 := by
    apply Matrix.toLin'.injective
    rw [rckRPlr_toLin'_zero]
    exact LinearMap.ext hzero
  exact hM0 hMzero

private abbrev rckRPlr_subOne {F : Type} [Field F] (x : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F :=
  (x : Matrix (Fin 2) (Fin 2) F) - 1

private theorem rckRPlr_subOne_ne_zero {F : Type} [Field F] {x : GL (Fin 2) F}
    (hx : x ≠ 1) : rckRPlr_subOne x ≠ 0 := by
  intro h
  exact hx (Units.ext (by simpa [rckRPlr_subOne] using sub_eq_zero.mp h))

private theorem rckRPlr_subOne_sq_zero {F : Type} [Field F] [CharP F 2]
    {P : Subgroup (GL (Fin 2) F)} (hP : IsPGroup 2 P) {x : GL (Fin 2) F} (hx : x ∈ P) :
    rckRPlr_subOne x * rckRPlr_subOne x = 0 := by
  obtain ⟨k, hk⟩ := rckRPlr_exists_pow_eq_one hP hx
  have h := rckRPlr_sub_one_pow_card_eq_zero (n := 2) (by norm_num) (x := x) (k := k) hk
  simpa [rckRPlr_subOne, pow_two] using h

private theorem rckRPlr_mul_self_of_mem {F : Type} [Field F] [CharP F 2]
    {P : Subgroup (GL (Fin 2) F)} (hP : IsPGroup 2 P) {x : GL (Fin 2) F} (hx : x ∈ P) :
    x * x = 1 := by
  have hN := rckRPlr_subOne_sq_zero hP hx
  have hpow : (x : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1 := by
    have hxsub : (x : Matrix (Fin 2) (Fin 2) F) = rckRPlr_subOne x + 1 := by
      rw [rckRPlr_subOne, sub_add_cancel]
    rw [hxsub, add_pow_char_of_commute (p := 2) (Commute.one_right _), pow_two, hN]
    simp
  refine Units.ext ?_
  simpa [Units.val_mul, pow_two] using hpow

private theorem rckRPlr_mul_comm_of_isPGroup {F : Type} [Field F] [CharP F 2]
    {P : Subgroup (GL (Fin 2) F)} (hP : IsPGroup 2 P) {x y : GL (Fin 2) F}
    (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  have hx2 : x * x = 1 := rckRPlr_mul_self_of_mem hP hx
  have hy2 : y * y = 1 := rckRPlr_mul_self_of_mem hP hy
  have hxy2 : (x * y) * (x * y) = 1 := rckRPlr_mul_self_of_mem hP (P.mul_mem hx hy)
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy2
  have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h3 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rw [← h1, mul_inv_rev, h2, h3]

private theorem rckRPlr_subOne_mul_comm {F : Type} [Field F] [CharP F 2]
    {P : Subgroup (GL (Fin 2) F)} (hP : IsPGroup 2 P) {x y : GL (Fin 2) F}
    (hx : x ∈ P) (hy : y ∈ P) :
    rckRPlr_subOne x * rckRPlr_subOne y = rckRPlr_subOne y * rckRPlr_subOne x := by
  have hxy : x * y = y * x := rckRPlr_mul_comm_of_isPGroup hP hx hy
  have hXY : (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) := by
    simpa using congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hxy
  have hc : Commute (x : Matrix (Fin 2) (Fin 2) F) (y : Matrix (Fin 2) (Fin 2) F) := hXY
  have h := (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  simpa [rckRPlr_subOne] using h.eq

theorem rckRP_glGeoFlag_none_of_isPGroup_two_le_two {n : ℕ} (hn : n ≤ 2) {F : Type}
    [Field F] [CharP F 2] {P : Subgroup (GL (Fin n) F)} (hP : IsPGroup 2 P) :
    GLGeoFlag none P := by
  classical
  interval_cases n
  · refine ⟨⊥, ⊥, bot_le, ?_, ?_⟩
    · intro x hx hx1
      obtain ⟨k, hk⟩ := rckRPlr_exists_pow_eq_one hP hx
      have hN := rckRPlr_sub_one_eq_zero_of_le_one (n := 0) (by norm_num) (x := x) hk
      exact absurd (Units.ext (sub_eq_zero.mp hN)) hx1
    · intro b hb
      exact absurd hb (Option.not_mem_none b)
  · refine ⟨⊥, ⊥, bot_le, ?_, ?_⟩
    · intro x hx hx1
      obtain ⟨k, hk⟩ := rckRPlr_exists_pow_eq_one hP hx
      have hN := rckRPlr_sub_one_eq_zero_of_le_one (n := 1) (by norm_num) (x := x) hk
      exact absurd (Units.ext (sub_eq_zero.mp hN)) hx1
    · intro b hb
      exact absurd hb (Option.not_mem_none b)
  · by_cases hPbot : P = ⊥
    · refine ⟨⊥, ⊥, bot_le, ?_, ?_⟩
      · intro x hx hx1
        rw [hPbot, Subgroup.mem_bot] at hx
        exact absurd hx hx1
      · intro b hb
        exact absurd hb (Option.not_mem_none b)
    · have hex : ∃ x ∈ P, x ≠ 1 := by
        by_contra h
        apply hPbot
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        by_contra hx1
        exact h ⟨x, hx, hx1⟩
      obtain ⟨x₀, hx₀P, hx₀1⟩ := hex
      have hN₀2 : rckRPlr_subOne x₀ * rckRPlr_subOne x₀ = 0 :=
        rckRPlr_subOne_sq_zero hP hx₀P
      have hN₀0 : rckRPlr_subOne x₀ ≠ 0 := rckRPlr_subOne_ne_zero hx₀1
      have hN₀ := rckRPlr_range_eq_ker_and_finrank hN₀2 hN₀0
      refine ⟨LinearMap.range (Matrix.toLin' (rckRPlr_subOne x₀)),
        LinearMap.ker (Matrix.toLin' (rckRPlr_subOne x₀)), ?_, ?_, ?_⟩
      · rw [hN₀.1]
      · intro x hx hx1
        have hx2 : rckRPlr_subOne x * rckRPlr_subOne x = 0 :=
          rckRPlr_subOne_sq_zero hP hx
        have hx0 : rckRPlr_subOne x ≠ 0 := rckRPlr_subOne_ne_zero hx1
        have hcomm : rckRPlr_subOne x * rckRPlr_subOne x₀ =
            rckRPlr_subOne x₀ * rckRPlr_subOne x :=
          rckRPlr_subOne_mul_comm hP hx hx₀P
        have hxker := rckRPlr_range_eq_ker_and_finrank hx2 hx0
        have hrange : LinearMap.range (Matrix.toLin' (rckRPlr_subOne x)) =
            LinearMap.range (Matrix.toLin' (rckRPlr_subOne x₀)) :=
          rckRPlr_range_eq_of_sq_zero_of_commute hx2 hN₀2 hcomm hx0 hN₀0
        exact ⟨hrange, by rw [← hxker.1, ← hN₀.1, hrange]⟩
      · intro b hb
        exact absurd hb (Option.not_mem_none b)

theorem rckRP_ggRootPosFlag_PSU_le_two {X : Type} [Group X] {n g : ℕ} (hn : n ≤ 2) (hg : 1 ≤ g)
    (φ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n) →*
      X)
    {K R : Subgroup X} (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center _) (hRK : R ≤ K)
    (hR : IsPGroup 2 R) : GGRootPosFlag K R := by
  classical
  let F := GaloisField 2 (2 * g)
  let σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 g
  let H : Subgroup ↥(Unitary.SU σ n) := R.comap φ
  let f : ↥H →* ↥R :=
    (φ.comp H.subtype).codRestrict R (fun x => Subgroup.mem_comap.mp x.2)
  have hf_surj : Function.Surjective f := by
    intro r
    have hrK : (r : X) ∈ K := hRK r.2
    have hrrange : (r : X) ∈ φ.range := by
      rwa [hφr]
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hrrange
    refine ⟨⟨u, ?_⟩, ?_⟩
    · exact Subgroup.mem_comap.mpr (hu ▸ r.2)
    · apply Subtype.ext
      exact hu
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  have htop : IsPGroup 2 (⊤ : Subgroup ↥R) := hR.to_subgroup ⊤
  have hSmap : (S : Subgroup ↥H).map f = ⊤ := by
    have h := (Sylow.mapSurjective (p := 2) (f := f) (hf := hf_surj) S).is_maximal'
      htop le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  set R' : Subgroup ↥(Unitary.SU σ n) := (S : Subgroup ↥H).map H.subtype with hR'def
  have hR'map : R'.map φ = R := by
    have hcomp : R.subtype.comp f = φ.comp H.subtype := by
      ext x
      rfl
    calc R'.map φ = ((S : Subgroup ↥H).map H.subtype).map φ := by rw [hR'def]
      _ = (S : Subgroup ↥H).map (φ.comp H.subtype) := by rw [Subgroup.map_map]
      _ = ((S : Subgroup ↥H).map f).map R.subtype := by rw [← hcomp, Subgroup.map_map]
      _ = R := by rw [hSmap, Subgroup.map_top, Subgroup.range_subtype]
  have hR'pg : IsPGroup 2 R' := S.isPGroup'.map H.subtype
  have hP : IsPGroup 2 (R'.map (Unitary.SU σ n).subtype) := hR'pg.map _
  have hflag : GLGeoFlag none (R'.map (Unitary.SU σ n).subtype) :=
    rckRP_glGeoFlag_none_of_isPGroup_two_le_two hn hP
  exact ggRootPosFlag_of_glGeoFlag_PSU hg φ hφr hφk hR'map hflag

end CFSG.StandardType.RCKRP
