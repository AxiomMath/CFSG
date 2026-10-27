module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortSpF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.Exceptional

@[expose] def RCKLemmaHCore (M : LieUniversal) (β : Fin M.D.rank → ℤ) : Prop :=
  ∀ x ∈ M.D.rootGroup β, x ≠ 1 →
    pCoreOf 2 (Subgroup.centralizer ({x} : Set M.K)) ≤
      Subgroup.centralizer (M.D.rootGroup β : Set M.K)

private theorem rckXF_exists_pow_two_eq_one_of_mem_pCoreOf {X : Type*} [Group X]
    {H : Subgroup X} {k : X} (hk : k ∈ pCoreOf 2 H) :
    ∃ b : ℕ, k ^ (2 ^ b) = 1 := by
  have hP : IsPGroup 2 (pCoreOf 2 H) := by
    change IsPGroup 2 ((pCore 2 ↥H).map H.subtype)
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  obtain ⟨b, hb⟩ := hP ⟨k, hk⟩
  exact ⟨b, by simpa using congrArg (Subtype.val) hb⟩

private theorem rckXF_conj_pow_apply {G : Type*} [Group G] {k y z : G}
    (hz : z ∈ Subgroup.center G) (h : k * y * k⁻¹ = z * y) (n : ℕ) :
    ((MulAut.conj k) ^ n) y = z ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul]
    have hzpow : (MulAut.conj k) (z ^ n) = z ^ n := by
      rw [MulAut.conj_apply]
      have hzc : z ^ n ∈ Subgroup.center G := pow_mem hz n
      have hcomm := Subgroup.mem_center_iff.mp hzc k
      rw [hcomm]; group
    rw [hzpow, MulAut.conj_apply, h, pow_succ]
    group

private theorem rckXF_finite_spinGroup_two {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type}
    [Field K] [Finite K] (Q : QuadraticForm K (σ → K)) {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) : Finite (spinGroup Q) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinMatrix Q)]
  refine ⟨?_, inferInstance⟩
  have hfin : ((spinMatrix Q).ker : Set (spinGroup Q)).Finite :=
    hker ▸ (Set.finite_singleton x).insert 1
  exact hfin.to_subtype

private theorem rckXF_finite_adjointGroup_two
    (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type*)
    [Field K] [Finite K] : Finite (CFSG.Blueprint.Chevalley.adjointGroup τ K) := by
  have : Finite (Module.End K (CFSG.Blueprint.Chevalley.RootModule τ K)) :=
    Module.finite_of_finite K
  infer_instance

private theorem rckXF_finite_minGroup_two
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {D : CFSG.LieType.Steinberg.Minuscule.MinData τ} (hV : D.Valid) (K : Type*) [Field K]
    [Finite K] : Finite ↥(hV.minGroup K) := by
  have : Finite (Module.End K (Fin D.d →₀ K)) := Module.finite_of_finite K
  infer_instance

theorem rckXF_finite_ggU
    {t' : StatedLieTag} (ht : GGPosTag t') {m g : ℕ} (hg : 1 ≤ g) :
    Finite (ggU t' m g).K := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases m with _ | m'
    · rw [show ggU .PSL 0 g = trivialUniversal from by simp only [ggU, lieUniversal]]
      change Finite (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
    · change Finite (Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 g))
      infer_instance
  · have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
      card_galoisField_two_mul 2 g hg
    have hK : ggU .PSU m g = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * g)) 2 g) m, Unitary.rootDatum hF m⟩ := by
      simp only [ggU, lieUniversal, hg, ↓reduceDIte]
    rw [hK]
    change Finite ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) m)
    infer_instance
  · change Finite ↥(CFSG.Open.StatedSp m (GaloisField 2 g))
    infer_instance
  · by_cases hm : 3 ≤ m
    · have hK : ggU .POmegaPlus m g = ⟨spinGroup (Spin.quadPlus m (GaloisField 2 g)),
          Spin.plusDatum m (GaloisField 2 g) hm⟩ := by
        simp only [ggU, lieUniversal, hm, ↓reduceDIte]
      rw [hK]
      haveI : NeZero m := ⟨by omega⟩
      exact rckXF_finite_spinGroup_two _
        (coe_ker_spinMatrix_quadPlus (n := m) (K := GaloisField 2 g))
    · rw [show ggU .POmegaPlus m g = trivialUniversal from by
        simp only [ggU, lieUniversal]
        rw [dif_neg hm]]
      change Finite (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
      infer_instance
  · exact rckXF_finite_spinGroup_two _
      (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr 2 g))
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 g))
    exact rckXF_finite_adjointGroup_two _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 g)
    exact rckXF_finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 g)
    exact rckXF_finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e7Data)
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid _
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 g))
    exact rckXF_finite_adjointGroup_two _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 g)
    have hfin : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        (GaloisField 2 (2 * g))) :=
      rckXF_finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
    infer_instance

theorem rckGL1_of_core
    {X : Type} [Group X] [Finite X] {K R : Subgroup X}
    {t' : StatedLieTag} {m g : ℕ} {β : Fin (ggU t' m g).D.rank → ℤ} (ht : GGPosTag t')
    (hg : 1 ≤ g) (hPM : t' = .POmegaMinus → 2 ≤ m) (hcore : RCKLemmaHCore (ggU t' m g) β)
    (hvia : GGRootVia (ggU t' m g) K R β) {r : X} (hr : r ∈ R) (hr1 : r ≠ 1) :
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X) := by
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  haveI : Finite (ggU t' m g).K := rckXF_finite_ggU ht hg
  have hoddCenter : Odd (Nat.card (Subgroup.center (ggU t' m g).K)) :=
    LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two
      (rckGL1_centerPPrime_ggU ht hg hPM)
  have hoddker : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hoddCenter (Subgroup.card_dvd_of_le hφker)
  intro k hk
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  rw [hR] at hs hr
  obtain ⟨y', hy'mem, hy's⟩ := Subgroup.mem_map.mp hs
  obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hy'mem
  obtain ⟨y, hymem, hyr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨x, hxmem, hxeq⟩ := Subgroup.mem_map.mp hymem
  have hxeq' : u * x * u⁻¹ = y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxeq
  have hx'eq' : u * x' * u⁻¹ = y' := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'eq
  have hx1 : x ≠ 1 := by
    intro hx0
    apply hr1
    rw [← hyr, ← hxeq', hx0]
    simp
  set N : Subgroup X := K ⊓ Subgroup.centralizer ({r} : Set X) with hNdef
  set Cst : Subgroup (ggU t' m g).K := N.comap φ with hCdef
  have hkC : φ.ker ≤ Cst := by
    intro z hz
    rw [hCdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact Subgroup.one_mem N
  have hCmap : Cst.map φ = N := by
    rw [hCdef, Subgroup.map_comap_eq, hφrange]
    exact inf_eq_right.mpr (hNdef.le.trans inf_le_left)
  have hmapcore : (pCoreOf 2 Cst).map φ = pCoreOf 2 N := by
    rw [LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hφker hoddker hkC, hCmap]
  have hk' : k ∈ (pCoreOf 2 Cst).map φ := by
    rw [hmapcore]; exact hk
  obtain ⟨k0, hk0, hk0eq⟩ := Subgroup.mem_map.mp hk'
  have hcore_le_cent : pCoreOf 2 Cst ≤
      Subgroup.centralizer ({y} : Set (ggU t' m g).K) := by
    intro kk hkk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkkN : φ kk ∈ N := by
      have h := GGRootNorm.pCoreOf_le Cst hkk
      rwa [hCdef, Subgroup.mem_comap] at h
    have hkr : φ kk * r = r * φ kk := Subgroup.mem_centralizer_singleton_iff.mp hkkN.2
    set z : (ggU t' m g).K := kk * y * kk⁻¹ * y⁻¹ with hzdef
    have hzker : z ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hzdef, hyr]
      have h1 : φ kk * r * (φ kk)⁻¹ = r := by rw [hkr]; group
      rw [h1, mul_inv_cancel]
    have hzcenter : z ∈ Subgroup.center (ggU t' m g).K := hφker hzker
    have hzy : kk * y * kk⁻¹ = z * y := by rw [hzdef]; group
    have hkkcoreN : φ kk ∈ pCoreOf 2 N := by
      rw [← hmapcore]
      exact Subgroup.mem_map_of_mem φ hkk
    obtain ⟨b, hkbN⟩ := rckXF_exists_pow_two_eq_one_of_mem_pCoreOf hkkcoreN
    have hkpow : kk ^ (2 ^ b) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hkbN]
    have hkpow_center : kk ^ (2 ^ b) ∈ Subgroup.center (ggU t' m g).K := hφker hkpow
    have hconj := rckXF_conj_pow_apply hzcenter hzy (2 ^ b)
    have hconj_triv : ((MulAut.conj kk) ^ (2 ^ b)) y = y := by
      rw [← map_pow, MulAut.conj_apply]
      have hcomm := Subgroup.mem_center_iff.mp hkpow_center y
      rw [← hcomm]; group
    rw [hconj_triv] at hconj
    have hzpow : z ^ (2 ^ b) = 1 := by
      have h : (1 : (ggU t' m g).K) * y = z ^ (2 ^ b) * y := by simpa using hconj
      exact (mul_right_cancel h).symm
    have hz1 : z = 1 := rckGL1_eq_one_of_pow_two_eq_one_of_centerPPrime
      (rckGL1_centerPPrime_ggU ht hg hPM) hzcenter b hzpow
    show kk * y = y * kk
    have h1 : kk * y * kk⁻¹ = y := by rw [hzy, hz1, one_mul]
    calc kk * y = kk * y * kk⁻¹ * kk := by group
      _ = y * kk := by rw [h1]
  have hcent_le_C : Subgroup.centralizer ({y} : Set (ggU t' m g).K) ≤ Cst := by
    intro mw hmw
    rw [hCdef, Subgroup.mem_comap]
    refine ⟨?_, ?_⟩
    · rw [← hφrange]
      exact ⟨mw, rfl⟩
    · have hmw' : mw * y = y * mw := Subgroup.mem_centralizer_singleton_iff.mp hmw
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← hyr, ← map_mul, ← map_mul, hmw']
  have hcore_le_ycore : pCoreOf 2 Cst ≤
      pCoreOf 2 (Subgroup.centralizer ({y} : Set (ggU t' m g).K)) :=
    GGRootNorm.le_pCoreOf_of_normalized hcore_le_cent (GGRootNorm.isPGroup_pCoreOf Cst) (by
      intro mw hmw t ht
      exact (Subgroup.mem_normalizer_iff.mp (GGRootNorm.le_normalizer_pCoreOf Cst
        (hcent_le_C hmw)) t).mp ht)
  let e : MulAut (ggU t' m g).K := MulAut.conj u⁻¹
  have hCy_map : (Subgroup.centralizer ({y} : Set (ggU t' m g).K)).map e.toMonoidHom =
      Subgroup.centralizer ({x} : Set (ggU t' m g).K) := by
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_map] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hv ⊢
      change e v * x = x * e v
      have hev : e v = u⁻¹ * v * u := by
        simp only [e, MulAut.conj_apply, inv_inv]
      have hx_of_y : x = u⁻¹ * y * u := by rw [← hxeq']; group
      rw [hev, hx_of_y]
      calc u⁻¹ * v * u * (u⁻¹ * y * u) = u⁻¹ * (v * y) * u := by group
        _ = u⁻¹ * (y * v) * u := by rw [hv]
        _ = u⁻¹ * y * u * (u⁻¹ * v * u) := by group
    · intro w hw
      rw [Subgroup.mem_map]
      refine ⟨e.symm w, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      change e.symm w * y = y * e.symm w
      have hesym : e.symm w = u * w * u⁻¹ := by
        simp only [e, MulAut.conj_symm_apply, inv_inv]
      rw [hesym, ← hxeq']
      calc u * w * u⁻¹ * (u * x * u⁻¹) = u * (w * x) * u⁻¹ := by group
        _ = u * (x * w) * u⁻¹ := by rw [hw]
        _ = u * x * u⁻¹ * (u * w * u⁻¹) := by group
  have hcorex : pCoreOf 2 (Subgroup.centralizer ({x} : Set (ggU t' m g).K)) =
      (pCoreOf 2 (Subgroup.centralizer ({y} : Set (ggU t' m g).K))).map e.toMonoidHom := by
    rw [← hCy_map, GGRootNorm.pCoreOf_map_mulEquiv e
      (Subgroup.centralizer ({y} : Set (ggU t' m g).K))]
  have hek0 : e k0 ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set (ggU t' m g).K)) := by
    rw [hcorex]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hcore_le_ycore hk0)
  have hxk : e k0 ∈ Subgroup.centralizer
      ((ggU t' m g).D.rootGroup β : Set (ggU t' m g).K) :=
    hcore x hxmem hx1 hek0
  have hx'comm : x' * e k0 = e k0 * x' :=
    Subgroup.mem_centralizer_iff.mp hxk x' hx'mem
  have hk0y' : k0 * y' = y' * k0 := by
    have hek0' : e k0 = u⁻¹ * k0 * u := by
      simp only [e, MulAut.conj_apply, inv_inv]
    have h := hx'comm
    rw [hek0'] at h
    rw [← hx'eq']
    calc k0 * (u * x' * u⁻¹) = u * (u⁻¹ * k0 * u * x') * u⁻¹ := by group
      _ = u * ((u⁻¹ * k0 * u) * x') * u⁻¹ := by group
      _ = u * (x' * (u⁻¹ * k0 * u)) * u⁻¹ := by rw [h]
      _ = u * x' * u⁻¹ * k0 := by group
  rw [← hk0eq, ← hy's, ← map_mul, ← map_mul, hk0y']

end CFSG.StandardType.RCKC1
