module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriOctRank
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.Open Module

section CommRing

variable {R : Type*} [CommRing R]

local syntax (name := octPolarExpand) "oct_polar_expand" : tactic

local macro_rules
  | `(tactic| oct_polar_expand) =>
    `(tactic| simp only [octPolar_eq, octA_octMul, octB_octMul, octU_octMul, octW_octMul,
      octA_octConj, octB_octConj, octU_octConj, octW_octConj, dot3, cross3_apply_zero,
      cross3_apply_one, cross3_apply_two])

theorem octPolar_octMul_add_octMul (a b c d : Oct R) :
    octPolar (octMul a c) (octMul b d) + octPolar (octMul a d) (octMul b c) =
      octPolar a b * octPolar c d := by
  oct_polar_expand
  ring

theorem octPolar_mulLeft_adjoint (a z w : Oct R) :
    octPolar (octMul a z) w = octPolar z (octMul (octConj a) w) := by
  oct_polar_expand
  ring

theorem octPolar_octConj (a b : Oct R) : octPolar (octConj a) (octConj b) = octPolar a b := by
  oct_polar_expand
  ring

end CommRing

section Alternating

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem even_finrank_range_of_isAlt {b : LinearMap.BilinForm K E} (hb : b.IsAlt) :
    Even (finrank K (LinearMap.range b)) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker b)
  let bC : LinearMap.BilinForm K C := b.compl₁₂ C.subtype C.subtype
  have hbC : bC.IsAlt := fun c => hb c
  have hsepL : ∀ c : C, (∀ d : C, bC c d = 0) → c = 0 := by
    intro c hc
    have hcker : (c : E) ∈ LinearMap.ker b := by
      rw [LinearMap.mem_ker]
      ext v
      have hv : v ∈ LinearMap.ker b ⊔ C := by
        rw [hC.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
      have hnc : b n c = 0 := by rw [LinearMap.mem_ker.mp hn]; rfl
      have h1 : b (c : E) n = 0 := hb.eq_iff.mp hnc
      have h2 : b (c : E) d = 0 := hc ⟨d, hd⟩
      simp [h1, h2]
    have hcC : (c : E) ∈ LinearMap.ker b ⊓ C := ⟨hcker, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hcC
    exact Subtype.ext hcC
  have hnd : bC.Nondegenerate := ⟨hsepL, fun d hd => hsepL d fun e => hbC.eq_iff.mp (hd e)⟩
  have heven := hbC.even_finrank hnd
  have h2 := LinearMap.finrank_range_add_finrank_ker b
  have h3 := Submodule.finrank_add_eq_of_isCompl hC
  rw [show finrank K (LinearMap.range b) = finrank K C by omega]
  exact heven

end Alternating

section Pairing

variable {K : Type*} [Field K]

theorem octPolarBil_orthogonal_eq {W : Submodule K (Oct K)} (hW : ∀ v ∈ W, octNorm v = 0)
    (h4 : finrank K W = 4) : LinearMap.BilinForm.orthogonal octPolarBil W = W := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal octPolarBil W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [octPolarBil_apply, octPolar, hW _ (W.add_mem hn hv), hW _ hn, hW _ hv]
    ring
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal octPolarBil_nondegenerate, finrank_oct_eq_eight, h4]

theorem finrank_comap_eq_finrank_ker_add (f : Oct K →ₗ[K] Oct K) (W : Submodule K (Oct K)) :
    finrank K (W.comap f) = finrank K (LinearMap.ker f) + finrank K ↥(LinearMap.range f ⊓ W) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (W.mkQ.comp f)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (W.mkQ.comp (LinearMap.range f).subtype)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp, Submodule.range_subtype] at h2
  have h3 : finrank K ↥(W.comap (LinearMap.range f).subtype) =
      finrank K ↥(LinearMap.range f ⊓ W) := by
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  have h4 := LinearMap.finrank_range_add_finrank_ker f
  omega

@[expose] def octPairing (f g : Oct K →ₗ[K] Oct K) : LinearMap.BilinForm K (Oct K) :=
  octPolarBil.compl₁₂ f g

@[simp] theorem octPairing_apply (f g : Oct K →ₗ[K] Oct K) (z w : Oct K) :
    octPairing f g z w = octPolar (f z) (g w) := rfl

theorem mem_ker_octPairing {f g : Oct K →ₗ[K] Oct K} {z : Oct K} :
    z ∈ LinearMap.ker (octPairing f g) ↔
      f z ∈ LinearMap.BilinForm.orthogonal octPolarBil (LinearMap.range g) := by
  rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h n hn
    obtain ⟨w, rfl⟩ := hn
    rw [octPolarBil_apply, octPolar_comm]
    exact LinearMap.congr_fun h w
  · intro h
    refine LinearMap.ext fun w => ?_
    simpa [octPolar_comm] using h (g w) ⟨w, rfl⟩

theorem finrank_ker_octPairing {f g : Oct K →ₗ[K] Oct K}
    (hg : ∀ v ∈ LinearMap.range g, octNorm v = 0) (hg4 : finrank K (LinearMap.range g) = 4) :
    finrank K (LinearMap.ker (octPairing f g)) =
      finrank K (LinearMap.ker f) + finrank K ↥(LinearMap.range f ⊓ LinearMap.range g) := by
  have hker : LinearMap.ker (octPairing f g) = (LinearMap.range g).comap f := by
    ext z
    rw [mem_ker_octPairing, octPolarBil_orthogonal_eq hg hg4]
    rfl
  rw [hker]
  exact finrank_comap_eq_finrank_ker_add f _

end Pairing

section Mixed

variable {K : Type*} [Field K]

theorem octPolar_zero_left (w : Oct K) : octPolar 0 w = 0 := by
  rw [← octPolarBil_apply, map_zero, LinearMap.zero_apply]

theorem octNorm_add (x y : Oct K) : octNorm (x + y) = octNorm x + octNorm y + octPolar x y := by
  unfold octPolar
  ring

theorem octPolar_octMul_octMul_eq (x y z w : Oct K) :
    octPolar (octMul x z) (octMul w y) =
      octPolar x w * octPolar z y - octPolar (octMul x y) (octMul w z) := by
  have h := octPolar_octMul_add_octMul x w z y
  linear_combination h

theorem finrank_ker_octPolarBil {y : Oct K} (hy : y ≠ 0) :
    finrank K (LinearMap.ker (octPolarBil y)) = 7 := by
  have h := LinearMap.finrank_range_add_finrank_ker (octPolarBil y)
  have hrange : LinearMap.range (octPolarBil y) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun c => ?_
    obtain ⟨z, hz⟩ := exists_octPolar_eq_one hy
    refine ⟨c • z, ?_⟩
    rw [map_smul, octPolarBil_apply, hz, smul_eq_mul, mul_one]
  rw [hrange, finrank_top, finrank_oct_eq_eight, Module.finrank_self] at h
  omega

theorem finrank_range_mulLeft_inf_mulRight_of_mul_eq_zero {x y : Oct K} (hx0 : x ≠ 0)
    (hx : octNorm x = 0) (hy0 : y ≠ 0) (hy : octNorm y = 0) (hxy : octMul x y = 0) :
    finrank K ↥(LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil.flip y)) = 3 := by
  have hkerdim := finrank_ker_octPairing (f := octMulBil x) (g := octMulBil.flip y)
    (fun v hv => octNorm_eq_zero_of_mem_range_mulRight hy hv)
    (finrank_range_mulRight_of_singular hy0 hy)
  rw [finrank_ker_mulLeft_of_singular hx0 hx] at hkerdim
  have hker : LinearMap.ker (octPairing (octMulBil x) (octMulBil.flip y)) =
      LinearMap.ker (octPolarBil y) := by
    ext z
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      obtain ⟨w, hw⟩ := exists_octPolar_eq_one hx0
      have h1 := LinearMap.congr_fun h w
      simp only [octPairing_apply, octMulBil_apply, LinearMap.flip_apply, LinearMap.zero_apply,
        octPolar_octMul_octMul_eq, hxy, octPolar_zero_left, sub_zero, hw, one_mul] at h1
      rw [octPolar_comm] at h1
      exact h1
    · intro h
      refine LinearMap.ext fun w => ?_
      have h' : octPolar y z = 0 := h
      simp only [octPairing_apply, octMulBil_apply, LinearMap.flip_apply, LinearMap.zero_apply,
        octPolar_octMul_octMul_eq, hxy, octPolar_zero_left, sub_zero]
      rw [octPolar_comm z y, h', mul_zero]
  rw [hker, finrank_ker_octPolarBil hy0] at hkerdim
  omega

theorem finrank_range_mulLeft_inf_mulRight_of_mul_ne_zero {x y : Oct K} (hx0 : x ≠ 0)
    (hx : octNorm x = 0) (hy0 : y ≠ 0) (hy : octNorm y = 0) (hxy : octMul x y ≠ 0) :
    finrank K ↥(LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil.flip y)) = 1 := by
  have hpn : octNorm (octMul x y) = 0 := by rw [octNorm_mul, hx, zero_mul]
  have hkerdim := finrank_ker_octPairing (f := octMulBil x) (g := octMulBil.flip y)
    (fun v hv => octNorm_eq_zero_of_mem_range_mulRight hy hv)
    (finrank_range_mulRight_of_singular hy0 hy)
  rw [finrank_ker_mulLeft_of_singular hx0 hx] at hkerdim
  have hlow : 1 ≤
      finrank K ↥(LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil.flip y)) := by
    rw [Submodule.one_le_finrank_iff, Ne, Submodule.eq_bot_iff]
    intro h
    exact hxy (h _ ⟨⟨y, rfl⟩, ⟨x, rfl⟩⟩)
  set Z := LinearMap.ker (octPairing (octMulBil x) (octMulBil.flip y)) with hZ
  have hinf : Z ⊓ LinearMap.ker (octPolarBil y) ≤
      LinearMap.range (octMulBil.flip (octMul x y)) := by
    intro z hz
    rw [Submodule.mem_inf, hZ, LinearMap.mem_ker, LinearMap.mem_ker] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzy : octPolar z y = 0 := by
      rw [octPolar_comm]
      exact hz2
    have hperp : ∀ w, octPolar (octMul x y) (octMul w z) = 0 := by
      intro w
      have h1 : octPolar (octMul x z) (octMul w y) = 0 := LinearMap.congr_fun hz1 w
      rw [octPolar_octMul_octMul_eq, hzy, mul_zero, zero_sub, neg_eq_zero] at h1
      exact h1
    have hmem : z ∈ LinearMap.BilinForm.orthogonal octPolarBil
        (LinearMap.range (octMulBil.flip (octMul x y))) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro _ ⟨u, rfl⟩
      have h2 := octPolar_mulLeft_adjoint (octConj u) z (octMul x y)
      rw [octConj_conj] at h2
      rw [octPolarBil_apply, LinearMap.flip_apply, octMulBil_apply, octPolar_comm, ← h2,
        octPolar_comm]
      exact hperp _
    rwa [octPolarBil_orthogonal_eq
      (fun v hv => octNorm_eq_zero_of_mem_range_mulRight hpn hv)
      (finrank_range_mulRight_of_singular hxy hpn)] at hmem
  have hZ5 : finrank K ↥Z ≤ 5 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Z (LinearMap.ker (octPolarBil y))
    have h2 := Submodule.finrank_le (Z ⊔ LinearMap.ker (octPolarBil y))
    have h3 := finrank_ker_octPolarBil hy0
    have h4 := Submodule.finrank_mono hinf
    rw [finrank_range_mulRight_of_singular hxy hpn] at h4
    rw [finrank_oct_eq_eight] at h2
    omega
  omega

theorem odd_finrank_range_mulLeft_inf_mulRight {x y : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hy0 : y ≠ 0) (hy : octNorm y = 0) :
    Odd (finrank K ↥(LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil.flip y))) := by
  by_cases hxy : octMul x y = 0
  · rw [finrank_range_mulLeft_inf_mulRight_of_mul_eq_zero hx0 hx hy0 hy hxy]
    exact ⟨1, rfl⟩
  · rw [finrank_range_mulLeft_inf_mulRight_of_mul_ne_zero hx0 hx hy0 hy hxy]
    exact ⟨0, rfl⟩

end Mixed

section Same

variable {K : Type*} [Field K]

theorem even_finrank_range_inf_of_alt {f g : Oct K →ₗ[K] Oct K}
    (hf4 : finrank K (LinearMap.ker f) = 4) (hg : ∀ v ∈ LinearMap.range g, octNorm v = 0)
    (hg4 : finrank K (LinearMap.range g) = 4) (halt : ∀ z, octPolar (f z) (g z) = 0) :
    Even (finrank K ↥(LinearMap.range f ⊓ LinearMap.range g)) := by
  have hb : (octPairing f g).IsAlt := fun z => halt z
  obtain ⟨r, hr⟩ := even_finrank_range_of_isAlt hb
  have h2 := LinearMap.finrank_range_add_finrank_ker (octPairing f g)
  have h3 := finrank_ker_octPairing (f := f) hg hg4
  rw [hf4] at h3
  rw [finrank_oct_eq_eight] at h2
  exact ⟨2 - r, by omega⟩

theorem inf_range_mulRight_eq_bot {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0) (hb : octPolar y y' ≠ 0) :
    LinearMap.range (octMulBil.flip y) ⊓ LinearMap.range (octMulBil.flip y') = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := hu
  rw [range_mulRight_eq_ker_mulRight_conj hy0 hy] at hu1
  rw [range_mulRight_eq_ker_mulRight_conj hy0' hy'] at hu2
  have h1 : octMul u (octConj y) = 0 := hu1
  have h2 : octMul u (octConj y') = 0 := hu2
  have hus : octMul u (octConj y + octConj y') = 0 := by
    rw [octMul_add_right, h1, h2, add_zero]
  have hns : octNorm (octConj y + octConj y') ≠ 0 := by
    rw [octNorm_add, octNorm_conj, octNorm_conj, hy, hy', octPolar_octConj, zero_add, zero_add]
    exact hb
  have h := octMul_mul_conj (octConj y + octConj y') u
  rw [hus, octMul_zero_left] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hns

theorem inf_range_mulLeft_eq_bot {x x' : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hx0' : x' ≠ 0) (hx' : octNorm x' = 0) (hb : octPolar x x' ≠ 0) :
    LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil x') = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := hu
  rw [range_mulLeft_eq_ker_mulLeft_conj hx0 hx] at hu1
  rw [range_mulLeft_eq_ker_mulLeft_conj hx0' hx'] at hu2
  have h1 : octMul (octConj x) u = 0 := hu1
  have h2 : octMul (octConj x') u = 0 := hu2
  have hus : octMul (octConj x + octConj x') u = 0 := by
    rw [octMul_add_left, h1, h2, add_zero]
  have hns : octNorm (octConj x + octConj x') ≠ 0 := by
    rw [octNorm_add, octNorm_conj, octNorm_conj, hx, hx', octPolar_octConj, zero_add, zero_add]
    exact hb
  have h := octMul_conj_mul (octConj x + octConj x') u
  rw [hus, octMul_zero_right] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hns

theorem even_finrank_range_mulRight_inf {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0) :
    Even (finrank K
      ↥(LinearMap.range (octMulBil.flip y) ⊓ LinearMap.range (octMulBil.flip y'))) := by
  by_cases hb : octPolar y y' = 0
  · refine even_finrank_range_inf_of_alt (finrank_ker_mulRight_of_singular hy0 hy)
      (fun v hv => octNorm_eq_zero_of_mem_range_mulRight hy' hv)
      (finrank_range_mulRight_of_singular hy0' hy') fun z => ?_
    simp only [LinearMap.flip_apply, octMulBil_apply]
    rw [octPolar_mul_left, hb, mul_zero]
  · rw [inf_range_mulRight_eq_bot hy0 hy hy0' hy' hb, finrank_bot]
    exact ⟨0, rfl⟩

theorem even_finrank_range_mulLeft_inf {x x' : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hx0' : x' ≠ 0) (hx' : octNorm x' = 0) :
    Even (finrank K ↥(LinearMap.range (octMulBil x) ⊓ LinearMap.range (octMulBil x'))) := by
  by_cases hb : octPolar x x' = 0
  · refine even_finrank_range_inf_of_alt (finrank_ker_mulLeft_of_singular hx0 hx)
      (fun v hv => octNorm_eq_zero_of_mem_range_mulLeft hx' hv)
      (finrank_range_mulLeft_of_singular hx0' hx') fun z => ?_
    simp only [octMulBil_apply]
    rw [octPolar_mul_right, hb, mul_zero]
  · rw [inf_range_mulLeft_eq_bot hx0 hx hx0' hx' hb, finrank_bot]
    exact ⟨0, rfl⟩

end Same

section Line

variable {K : Type*} [Field K]

theorem octConj_smul (c : K) (x : Oct K) : octConj (c • x) = c • octConj x :=
  oct_ext (by simp) (funext fun i => by simp) (funext fun i => by simp) (by simp)

theorem octConj_ne_zero_of_ne_zero {y : Oct K} (hy : y ≠ 0) : octConj y ≠ 0 := by
  intro h
  apply hy
  have h0 : octConj (0 : Oct K) = 0 :=
    oct_ext (by simp) (funext fun i => by simp) (funext fun i => by simp) (by simp)
  rw [← octConj_conj y, h, h0]

theorem exists_octNorm_eq_zero_not_mem {W : Submodule K (Oct K)} (hW : W ≠ ⊤) :
    ∃ z : Oct K, octNorm z = 0 ∧ z ∉ W := by
  by_contra hcon
  push Not at hcon
  refine hW (eq_top_iff.mpr ?_)
  rw [← (Pi.basisFun K (Fin 4 ⊕ Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine hcon _ ?_
  rw [Pi.basisFun_apply]
  rcases i with i | i <;> fin_cases i <;>
    simp [octNorm, octA, octB, octU, octW, dot3, Pi.single_apply]

theorem ker_mulRight_le_of_range_eq {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0)
    (h : LinearMap.range (octMulBil.flip y) = LinearMap.range (octMulBil.flip y')) :
    LinearMap.ker (octMulBil.flip y) ≤ LinearMap.ker (octMulBil.flip y') := by
  intro z hz
  by_cases hz0 : z = 0
  · rw [hz0]
    exact Submodule.zero_mem _
  by_contra hzy'
  have hzy : octMul z y = 0 := hz
  have hzy'' : octMul z y' ≠ 0 := hzy'
  have hzn : octNorm z = 0 := octNorm_eq_zero_of_mem_ker_mulRight hy0 hy hz
  have h1 := finrank_range_mulLeft_inf_mulRight_of_mul_ne_zero hz0 hzn hy0' hy' hzy''
  rw [← h] at h1
  have h3 := finrank_range_mulLeft_inf_mulRight_of_mul_eq_zero hz0 hzn hy0 hy hzy
  omega

theorem exists_smul_eq_of_range_mulRight_eq {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0)
    (h : LinearMap.range (octMulBil.flip y) = LinearMap.range (octMulBil.flip y')) :
    ∃ c : K, y' = c • y := by
  by_contra hne
  push Not at hne
  have hker : LinearMap.ker (octMulBil.flip y) = LinearMap.ker (octMulBil.flip y') :=
    le_antisymm (ker_mulRight_le_of_range_eq hy0 hy hy0' hy' h)
      (ker_mulRight_le_of_range_eq hy0' hy' hy0 hy h.symm)
  have hne_top : LinearMap.ker (octMulBil.flip y) ≠ ⊤ := by
    intro htop
    have h4 := finrank_ker_mulRight_of_singular hy0 hy
    rw [htop, finrank_top, finrank_oct_eq_eight] at h4
    omega
  obtain ⟨z, hzn, hzW⟩ := exists_octNorm_eq_zero_not_mem hne_top
  have hz0 : z ≠ 0 := fun h0 => hzW (h0 ▸ Submodule.zero_mem _)
  have hzy : octMul z y ≠ 0 := hzW
  have hzy' : octMul z y' ≠ 0 := by
    intro h0
    apply hzW
    rw [hker]
    exact h0
  have h1 := finrank_range_mulLeft_inf_mulRight_of_mul_ne_zero hz0 hzn hy0 hy hzy
  have hv : (⟨octMul z y, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ :
      ↥(LinearMap.range (octMulBil z) ⊓ LinearMap.range (octMulBil.flip y))) ≠ 0 := fun h0 =>
    hzy (congrArg Subtype.val h0)
  have hmem : octMul z y' ∈ LinearMap.range (octMulBil z) ⊓ LinearMap.range (octMulBil.flip y) := by
    refine ⟨⟨y', rfl⟩, ?_⟩
    rw [h]
    exact ⟨z, rfl⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).mp h1 ⟨octMul z y', hmem⟩
  have hc' : c • octMul z y = octMul z y' := congrArg Subtype.val hc
  have hzs : octMul z (y' - c • y) = 0 := by
    rw [octMul_sub_right, octMul_smul_right, hc', sub_self]
  have hs0 : y' - c • y ≠ 0 := fun h0 => hne c (sub_eq_zero.mp h0)
  have hsn : octNorm (y' - c • y) = 0 := by
    have h2 := octMul_mul_conj (y' - c • y) z
    rw [hzs, octMul_zero_left] at h2
    exact (smul_eq_zero.mp h2.symm).resolve_right hz0
  have hle : LinearMap.ker (octMulBil.flip y) ≤ LinearMap.ker (octMulBil.flip (y' - c • y)) := by
    intro u hu
    have hu1 : octMul u y = 0 := hu
    have hu2 : octMul u y' = 0 := by
      have hu' : u ∈ LinearMap.ker (octMulBil.flip y') := hker ▸ hu
      exact hu'
    show octMul u (y' - c • y) = 0
    rw [octMul_sub_right, octMul_smul_right, hu1, hu2, smul_zero, sub_zero]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_ker_mulRight_of_singular hy0 hy, finrank_ker_mulRight_of_singular hs0 hsn])
  exact hzW (heq ▸ (show z ∈ LinearMap.ker (octMulBil.flip (y' - c • y)) from hzs))

theorem exists_smul_eq_of_ker_mulRight_eq {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0)
    (h : LinearMap.ker (octMulBil.flip y) = LinearMap.ker (octMulBil.flip y')) :
    ∃ c : K, y' = c • y := by
  rw [ker_mulRight_eq_range_mulRight_conj hy0 hy,
    ker_mulRight_eq_range_mulRight_conj hy0' hy'] at h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_range_mulRight_eq (octConj_ne_zero_of_ne_zero hy0)
    (by rwa [octNorm_conj]) (octConj_ne_zero_of_ne_zero hy0') (by rwa [octNorm_conj]) h
  refine ⟨c, ?_⟩
  have := congrArg octConj hc
  rwa [octConj_conj, octConj_smul, octConj_conj] at this

theorem exists_smul_eq_of_mulRight_eq {y y' : Oct K} (hy0 : y ≠ 0) (hy : octNorm y = 0)
    (hy0' : y' ≠ 0) (hy' : octNorm y' = 0)
    (h : LinearMap.range (octMulBil.flip y) = LinearMap.range (octMulBil.flip y') ∨
      LinearMap.ker (octMulBil.flip y) = LinearMap.ker (octMulBil.flip y')) :
    ∃ c : K, y' = c • y :=
  h.elim (exists_smul_eq_of_range_mulRight_eq hy0 hy hy0' hy')
    (exists_smul_eq_of_ker_mulRight_eq hy0 hy hy0' hy')

theorem range_mulRight_conj_le_of_range_mulLeft_le {x x' : Oct K}
    (h : LinearMap.range (octMulBil x) ≤ LinearMap.range (octMulBil x')) :
    LinearMap.range (octMulBil.flip (octConj x)) ≤
      LinearMap.range (octMulBil.flip (octConj x')) := by
  rintro _ ⟨u, rfl⟩
  have hv : octConj (octMul u (octConj x)) ∈ LinearMap.range (octMulBil x) := by
    rw [octConj_mul, octConj_conj]
    exact ⟨octConj u, rfl⟩
  obtain ⟨w, hw⟩ := h hv
  refine ⟨octConj w, ?_⟩
  show octMul (octConj w) (octConj x') = octMul u (octConj x)
  rw [← octConj_mul]
  have h2 : octMul x' w = octConj (octMul u (octConj x)) := hw
  rw [h2, octConj_conj]

theorem exists_smul_eq_of_range_mulLeft_eq {x x' : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hx0' : x' ≠ 0) (hx' : octNorm x' = 0)
    (h : LinearMap.range (octMulBil x) = LinearMap.range (octMulBil x')) :
    ∃ c : K, x' = c • x := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_range_mulRight_eq (octConj_ne_zero_of_ne_zero hx0)
    (by rwa [octNorm_conj]) (octConj_ne_zero_of_ne_zero hx0') (by rwa [octNorm_conj])
    (le_antisymm (range_mulRight_conj_le_of_range_mulLeft_le h.le)
      (range_mulRight_conj_le_of_range_mulLeft_le h.ge))
  refine ⟨c, ?_⟩
  have := congrArg octConj hc
  rwa [octConj_conj, octConj_smul, octConj_conj] at this

theorem exists_smul_eq_of_ker_mulLeft_eq {x x' : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hx0' : x' ≠ 0) (hx' : octNorm x' = 0)
    (h : LinearMap.ker (octMulBil x) = LinearMap.ker (octMulBil x')) :
    ∃ c : K, x' = c • x := by
  rw [ker_mulLeft_eq_range_mulLeft_conj hx0 hx,
    ker_mulLeft_eq_range_mulLeft_conj hx0' hx'] at h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_range_mulLeft_eq (octConj_ne_zero_of_ne_zero hx0)
    (by rwa [octNorm_conj]) (octConj_ne_zero_of_ne_zero hx0') (by rwa [octNorm_conj]) h
  refine ⟨c, ?_⟩
  have := congrArg octConj hc
  rwa [octConj_conj, octConj_smul, octConj_conj] at this

theorem exists_smul_eq_of_mulLeft_eq {x x' : Oct K} (hx0 : x ≠ 0) (hx : octNorm x = 0)
    (hx0' : x' ≠ 0) (hx' : octNorm x' = 0)
    (h : LinearMap.range (octMulBil x) = LinearMap.range (octMulBil x') ∨
      LinearMap.ker (octMulBil x) = LinearMap.ker (octMulBil x')) :
    ∃ c : K, x' = c • x :=
  h.elim (exists_smul_eq_of_range_mulLeft_eq hx0 hx hx0' hx')
    (exists_smul_eq_of_ker_mulLeft_eq hx0 hx hx0' hx')

end Line

end CFSG.RankThree.GF2n.Stroth80.Tri

end
