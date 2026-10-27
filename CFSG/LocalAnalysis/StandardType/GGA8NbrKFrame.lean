module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.Open CFSG.StandardType Matrix
open CFSG.StandardType.GGHalf (F2)

private noncomputable def a8kf_fieldEquiv : F2 ≃+* ZMod 2 := by
  classical
  letI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  exact FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])

private noncomputable def a8kf_slFieldEquiv :
    SpecialLinearGroup (Fin 9) F2 ≃* SpecialLinearGroup (Fin 9) (ZMod 2) := by
  classical
  let ε : F2 ≃+* ZMod 2 := a8kf_fieldEquiv
  refine MulEquiv.ofBijective (SpecialLinearGroup.map ε.toRingHom) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have h' := congrArg
      (fun X : SpecialLinearGroup (Fin 9) (ZMod 2) =>
        ((X : Matrix (Fin 9) (Fin 9) (ZMod 2)) i j)) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
    exact ε.injective h'
  · intro b
    refine ⟨SpecialLinearGroup.map ε.symm.toRingHom b, ?_⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    simp

private noncomputable def a8kf_slGL :
    SpecialLinearGroup (Fin 9) (ZMod 2) ≃* GL (Fin 9) (ZMod 2) :=
  MulEquiv.ofBijective SpecialLinearGroup.toGL
    (toGL_nine_bijective_of_card_two (K := ZMod 2) (Nat.card_zmod 2))

private noncomputable def a8kf_rho0 {G : Type} [Group G] {K : Subgroup G}
    (φ : SpecialLinearGroup (Fin 9) F2 →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K) : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm).trans
    (a8kf_slFieldEquiv.trans (a8kf_slGL.trans ggSL9GLEquiv))

private theorem a8kf_center_eq_bot {G : Type} [Group G] {K : Subgroup G}
    (ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply ρ₀.injective
  rw [map_one]
  have hc : ρ₀ x ∈ Subgroup.center (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := Subgroup.mem_center_iff.mp hx (ρ₀.symm z)
    calc z * ρ₀ x = ρ₀ (ρ₀.symm z) * ρ₀ x := by rw [MulEquiv.apply_symm_apply]
      _ = ρ₀ (ρ₀.symm z * x) := by rw [map_mul]
      _ = ρ₀ (x * ρ₀.symm z) := by rw [h]
      _ = ρ₀ x * ρ₀ (ρ₀.symm z) := by rw [map_mul]
      _ = ρ₀ x * z := by rw [MulEquiv.apply_symm_apply]
  have h1 : ρ₀ x ∈ (⊥ : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rwa [center_ggSL9_eq_bot] at hc
  exact Subgroup.mem_bot.mp h1

private theorem a8kf_F2_card : Nat.card F2 = 2 := by
  have := GaloisField.card 2 1 (by omega)
  simpa using this

private theorem a8kf_exists_realizing {G : Type} [Group G] {K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} {hrange : φ.range = K}
    {A : GL (Fin 9) F2} {b : G}
    (hb : (b, A) ∈ LinFusion.ggInducedPairs φ) :
    ∃ k : ↥K, ∀ u : SpecialLinearGroup (Fin 9) F2,
      b * φ u * b⁻¹ = (k : G) * φ u * (k : G)⁻¹ := by
  obtain ⟨B, hB⟩ := (toGL_nine_bijective_of_card_two (K := F2) a8kf_F2_card).2 A
  have hBmat : (B : Matrix (Fin 9) (Fin 9) F2) = (A : Matrix (Fin 9) (Fin 9) F2) := by
    have := congrArg (fun X : GL (Fin 9) F2 => (X : Matrix (Fin 9) (Fin 9) F2)) hB
    simpa using this
  refine ⟨⟨φ B, ?_⟩, ?_⟩
  · rw [← hrange]; exact ⟨B, rfl⟩
  · intro u
    have h1 : b * φ u * b⁻¹ = φ (InnerDiagA.conjSL A u) :=
      (LinFusion.mem_ggInducedPairs.mp hb) u
    have h2 : InnerDiagA.conjSL A u = B * u * B⁻¹ :=
      LinFusion.conjSL_eq_of_smul (m := 8) (c := 1) (by simpa using hBmat) u
    calc b * φ u * b⁻¹ = φ (InnerDiagA.conjSL A u) := h1
      _ = φ (B * u * B⁻¹) := by rw [h2]
      _ = φ B * φ u * (φ B)⁻¹ := by rw [map_mul, map_mul, map_inv]

private noncomputable def a8kf_kappa {G : Type} [Group G] {K : Subgroup G}
    {Bs : Subgroup G} {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2}
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ) (b : ↥Bs) : ↥K :=
  Classical.choose (a8kf_exists_realizing (K := K) (φ := φ) (hrange := hrange) (A := A b) (hA b))

private theorem a8kf_kappa_spec {G : Type} [Group G] {K : Subgroup G}
    {Bs : Subgroup G} {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2}
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (b : ↥Bs) (u : SpecialLinearGroup (Fin 9) F2) :
    (b : G) * φ u * (b : G)⁻¹ =
      (a8kf_kappa hrange hA b : G) * φ u * (a8kf_kappa hrange hA b : G)⁻¹ :=
  Classical.choose_spec (a8kf_exists_realizing (K := K) (φ := φ) (hrange := hrange)
    (A := A b) (hA b)) u

private theorem a8kf_kappa_unique {G : Type} [Group G] {K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} {hrange : φ.range = K}
    (hZ : Subgroup.center K = ⊥) {b : G} {k k' : ↥K}
    (hk : ∀ u : SpecialLinearGroup (Fin 9) F2,
      b * φ u * b⁻¹ = (k : G) * φ u * (k : G)⁻¹)
    (hk' : ∀ u : SpecialLinearGroup (Fin 9) F2,
      b * φ u * b⁻¹ = (k' : G) * φ u * (k' : G)⁻¹) : k = k' := by
  have hmem : k'⁻¹ * k ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : (x : G) ∈ φ.range := by rw [hrange]; exact x.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx
    have h3 : (k : G) * φ u * (k : G)⁻¹ = (k' : G) * φ u * (k' : G)⁻¹ :=
      (hk u).symm.trans (hk' u)
    have h5 : (k' : G)⁻¹ * (k : G) * φ u * ((k' : G)⁻¹ * (k : G))⁻¹ = φ u := by
      calc (k' : G)⁻¹ * (k : G) * φ u * ((k' : G)⁻¹ * (k : G))⁻¹
          = (k' : G)⁻¹ * ((k : G) * φ u * (k : G)⁻¹) * (k' : G) := by group
        _ = (k' : G)⁻¹ * ((k' : G) * φ u * (k' : G)⁻¹) * (k' : G) := by rw [h3]
        _ = φ u := by group
    have h4 : (k' : G)⁻¹ * (k : G) * φ u = φ u * ((k' : G)⁻¹ * (k : G)) := by
      calc (k' : G)⁻¹ * (k : G) * φ u
          = ((k' : G)⁻¹ * (k : G) * φ u * ((k' : G)⁻¹ * (k : G))⁻¹) *
              ((k' : G)⁻¹ * (k : G)) := by group
        _ = φ u * ((k' : G)⁻¹ * (k : G)) := by rw [h5]
    show x * ((k'⁻¹ * k : ↥K)) = ((k'⁻¹ * k : ↥K)) * x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (x : G) = φ u from hu.symm]
    exact h4.symm
  rw [hZ] at hmem
  have h1 : k'⁻¹ * k = 1 := Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp h1).symm

private theorem a8kf_kappa_conj {G : Type} [Group G] {K : Subgroup G}
    {Bs : Subgroup G} {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2}
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (b : ↥Bs) (x : ↥K) :
    (b : G) * (x : G) * (b : G)⁻¹ =
      (a8kf_kappa hrange hA b : G) * (x : G) * (a8kf_kappa hrange hA b : G)⁻¹ := by
  have hx : (x : G) ∈ φ.range := by rw [hrange]; exact x.2
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx
  rw [← hu]
  exact a8kf_kappa_spec hrange hA b u

private noncomputable def a8kf_kappaHom {G : Type} [Group G] {K : Subgroup G}
    {Bs : Subgroup G} {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2}
    (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ) : ↥Bs →* ↥K where
  toFun := a8kf_kappa hrange hA
  map_one' := by
    apply a8kf_kappa_unique (K := K) (φ := φ) (hrange := hrange) hZ
    · exact a8kf_kappa_spec hrange hA 1
    · intro u; simp
  map_mul' b b' := by
    apply a8kf_kappa_unique (K := K) (φ := φ) (hrange := hrange) hZ
    · exact a8kf_kappa_spec hrange hA (b * b')
    · intro u
      have hb' : (b' : G) * φ u * (b' : G)⁻¹ =
          (a8kf_kappa hrange hA b' : G) * φ u * (a8kf_kappa hrange hA b' : G)⁻¹ :=
        a8kf_kappa_spec hrange hA b' u
      have hyK : ((a8kf_kappa hrange hA b' : G) * φ u * (a8kf_kappa hrange hA b' : G)⁻¹) ∈ K :=
        K.mul_mem (K.mul_mem (a8kf_kappa hrange hA b').2
          (by rw [← hrange]; exact ⟨u, rfl⟩)) (K.inv_mem (a8kf_kappa hrange hA b').2)
      have hconj := a8kf_kappa_conj hrange hA b ⟨_, hyK⟩
      calc ((b * b' : ↥Bs) : G) * φ u * ((b * b' : ↥Bs) : G)⁻¹
          = (b : G) * ((b' : G) * φ u * (b' : G)⁻¹) * (b : G)⁻¹ := by
            simp only [Subgroup.coe_mul]; group
        _ = (b : G) * ((a8kf_kappa hrange hA b' : G) * φ u *
              (a8kf_kappa hrange hA b' : G)⁻¹) * (b : G)⁻¹ := by rw [hb']
        _ = (a8kf_kappa hrange hA b : G) *
              ((a8kf_kappa hrange hA b' : G) * φ u * (a8kf_kappa hrange hA b' : G)⁻¹) *
              (a8kf_kappa hrange hA b : G)⁻¹ := hconj
        _ = ((a8kf_kappa hrange hA b * a8kf_kappa hrange hA b' : ↥K) : G) * φ u *
              ((a8kf_kappa hrange hA b * a8kf_kappa hrange hA b' : ↥K) : G)⁻¹ := by
            simp only [Subgroup.coe_mul]; group

private theorem a8kf_kappa_image_comm {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) (b b' : ↥Bs) :
    (a8kf_kappa hrange hA b : G) * (a8kf_kappa hrange hA b' : G) =
      (a8kf_kappa hrange hA b' : G) * (a8kf_kappa hrange hA b : G) := by
  have h1 : a8kf_kappaHom hrange hZ hA (b * b') = a8kf_kappaHom hrange hZ hA (b' * b) := by
    rw [hcomm b b']
  rw [map_mul, map_mul] at h1
  exact congrArg (fun x : ↥K => (x : G)) h1

private theorem a8kf_kappa_centralizes {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2}
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ) (b : ↥Bs) :
    (a8kf_kappa hrange hA b : G)⁻¹ * (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := a8kf_kappa_conj hrange hA b ⟨x, hx⟩
  have hcalc : (a8kf_kappa hrange hA b : G)⁻¹ * (b : G) * x =
      x * ((a8kf_kappa hrange hA b : G)⁻¹ * (b : G)) := by
    calc (a8kf_kappa hrange hA b : G)⁻¹ * (b : G) * x
        = (a8kf_kappa hrange hA b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by group
      _ = (a8kf_kappa hrange hA b : G)⁻¹ *
            ((a8kf_kappa hrange hA b : G) * x * (a8kf_kappa hrange hA b : G)⁻¹) *
            (b : G) := by rw [h]
      _ = x * ((a8kf_kappa hrange hA b : G)⁻¹ * (b : G)) := by group
  exact hcalc.symm

private theorem a8kf_kappa_comm_bs {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) (b b' : ↥Bs) :
    (a8kf_kappa hrange hA b : G) * (b' : G) = (b' : G) * (a8kf_kappa hrange hA b : G) := by
  have hz := a8kf_kappa_centralizes hrange hA b'
  have hzκ : ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G)) * (a8kf_kappa hrange hA b : G) =
      (a8kf_kappa hrange hA b : G) * ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G)) :=
    (Subgroup.mem_centralizer_iff.mp hz _ (a8kf_kappa hrange hA b).2).symm
  have himg := a8kf_kappa_image_comm hrange hZ hA hcomm b b'
  calc (a8kf_kappa hrange hA b : G) * (b' : G)
      = (a8kf_kappa hrange hA b : G) *
          ((a8kf_kappa hrange hA b' : G) * ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G))) := by
            group
    _ = ((a8kf_kappa hrange hA b : G) * (a8kf_kappa hrange hA b' : G)) *
          ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G)) := by group
    _ = ((a8kf_kappa hrange hA b' : G) * (a8kf_kappa hrange hA b : G)) *
          ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G)) := by rw [himg]
    _ = (a8kf_kappa hrange hA b' : G) *
          ((a8kf_kappa hrange hA b : G) * ((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G))) := by
            group
    _ = (a8kf_kappa hrange hA b' : G) *
          (((a8kf_kappa hrange hA b' : G)⁻¹ * (b' : G)) * (a8kf_kappa hrange hA b : G)) := by
            rw [hzκ]
    _ = (b' : G) * (a8kf_kappa hrange hA b : G) := by group

private theorem a8kf_kappa_mem_centralizer {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) (b : ↥Bs) :
    (a8kf_kappa hrange hA b : G) ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  simpa using (a8kf_kappa_comm_bs hrange hZ hA hcomm b ⟨x, hx⟩).symm

private theorem a8kf_kappa_pow_seven {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    {b : ↥Bs} (hpow : (b : G) ^ 7 = 1) :
    (a8kf_kappa hrange hA b : G) ^ 7 = 1 := by
  have h := map_pow (a8kf_kappaHom hrange hZ hA) b 7
  have hb7 : b ^ 7 = 1 := Subtype.ext hpow
  rw [hb7, map_one] at h
  exact congrArg (fun x : ↥K => (x : G)) h.symm

private theorem a8kf_kappa_mem_Bs {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    {b : ↥Bs} (hpow : (b : G) ^ 7 = 1) :
    (a8kf_kappa hrange hA b : G) ∈ Bs :=
  hSC _ (a8kf_kappa_mem_centralizer hrange hZ hA hcomm b)
    (a8kf_kappa_pow_seven hrange hZ hA hpow)

private theorem a8kf_kappa_retract {G : Type} [Group G] {K Bs : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (b : ↥Bs) (hb : (b : G) ∈ K) :
    a8kf_kappa hrange hA b = ⟨(b : G), hb⟩ := by
  apply a8kf_kappa_unique (K := K) (φ := φ) (hrange := hrange) hZ
  · exact a8kf_kappa_spec hrange hA b
  · intro u; rfl

private theorem a8kf_card_ker {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcfg : GGConfig 7 B Bs x L D J) (hnb : GGNbr 7 B x D J y K)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) :
    Nat.card (a8kf_kappaHom hrange hZ hA).ker = 7 := by
  have hker_eq : (a8kf_kappaHom hrange hZ hA).ker =
      (Bs ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : a8kf_kappa hrange hA b = 1 := h
      refine ⟨b.2, ?_⟩
      show (b : G) ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hc := a8kf_kappa_conj hrange hA b ⟨x, hx⟩
      rw [h'] at hc
      have h1 : (b : G) * x * (b : G)⁻¹ = x := by simpa using hc
      calc x * (b : G) = ((b : G) * x * (b : G)⁻¹) * (b : G) := by rw [h1]
        _ = (b : G) * x := by group
    · intro h
      apply a8kf_kappa_unique (K := K) (φ := φ) (hrange := hrange) hZ
      · exact a8kf_kappa_spec hrange hA b
      · intro u
        have hφK : (φ u : G) ∈ K := by rw [← hrange]; exact ⟨u, rfl⟩
        have hcomm := (Subgroup.mem_centralizer_iff.mp h.2) (φ u) hφK
        calc (b : G) * φ u * (b : G)⁻¹ = (b : G) * φ u * (b : G)⁻¹ := rfl
          _ = ((b : G) * φ u) * (b : G)⁻¹ := by group
          _ = ((φ u * (b : G))) * (b : G)⁻¹ := by rw [hcomm.symm]
          _ = φ u := by group
          _ = (1 : G) * φ u * (1 : G)⁻¹ := by group
  rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact GGNbr.card_bstar_inf_centralizer hcfg hnb hCJ hJK

private theorem a8kf_card_range {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcfg : GGConfig 7 B Bs x L D J) (hnb : GGNbr 7 B x D J y K)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) :
    7 * Nat.card (a8kf_kappaHom hrange hZ hA).range = Nat.card ↥Bs := by
  have h := Subgroup.card_ker_mul_card_range (a8kf_kappaHom hrange hZ hA)
  rw [a8kf_card_ker hrange hZ hA hcfg hnb hCJ hJK] at h
  exact h

private theorem a8kf_card_E {G : Type} [Group G] {Bs K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hZ : Subgroup.center K = ⊥)
    (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    (hpow : ∀ b : ↥Bs, (b : G) ^ 7 = 1) :
    Nat.card ↥(Bs ⊓ K) = Nat.card (a8kf_kappaHom hrange hZ hA).range := by
  have hmap : (a8kf_kappaHom hrange hZ hA).range.map K.subtype = Bs ⊓ K := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hk
      exact ⟨a8kf_kappa_mem_Bs hrange hZ hA hcomm hSC (hpow b),
        (a8kf_kappa hrange hA b).2⟩
    · intro hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hg.2⟩, ?_, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨g, hg.1⟩, a8kf_kappa_retract hrange hZ hA ⟨g, hg.1⟩ hg.2⟩
  rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]

private noncomputable def a8kf_tail {G : Type} [Group G] {Bs K : Subgroup G}
    {φ : SpecialLinearGroup (Fin 9) F2 →* G} (hrange : φ.range = K)
    {A : ↥Bs → GL (Fin 9) F2} (hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ)
    (hκB : ∀ b : ↥Bs, (a8kf_kappa hrange hA b : G) ∈ Bs)
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (b : ↥Bs) : Fin 3 → ZMod 7 :=
  Multiplicative.toAdd (Classical.choose (show ∃ f : Multiplicative (Fin 3 → ZMod 7),
      ggSL9TorusCoord f = ρ (a8kf_kappa hrange hA b) from by
    have hmem : ρ (a8kf_kappa hrange hA b) ∈
        ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom :=
      Subgroup.mem_map_of_mem ρ.toMonoidHom
        ⟨hκB b, (a8kf_kappa hrange hA b).2⟩
    rw [hρE] at hmem
    rw [← range_ggSL9TorusCoord] at hmem
    exact hmem))

private noncomputable def a8kf_eVFun {G : Type} [Group G] {K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (v : Fin 4 → ZMod 7) : G :=
  ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) : ↥K) : G)

private theorem a8kf_eVFun_mem {G : Type} [Group G] {Bs K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (v : Fin 4 → ZMod 7) : a8kf_eVFun ρ v ∈ Bs := by
  have ht : ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ)) ∈
      ggSL9Torus := by
    rw [← range_ggSL9TorusCoord]
    exact ⟨_, rfl⟩
  rw [← hρE] at ht
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp ht
  have hsymm : ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) = e := by
    rw [← heq]
    simpa using MulEquiv.symm_apply_apply ρ e
  change ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) : ↥K) : G) ∈ Bs
  rw [hsymm]
  exact he.1

private theorem a8kf_eVFun_add {G : Type} [Group G] {K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (v w : Fin 4 → ZMod 7) :
    a8kf_eVFun ρ (v + w) = a8kf_eVFun ρ v * a8kf_eVFun ρ w := by
  have h : ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => (v + w) i.succ))) =
      ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) *
        ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => w i.succ))) := by
    have hof : Multiplicative.ofAdd (fun i : Fin 3 => (v + w) i.succ) =
        Multiplicative.ofAdd (fun i : Fin 3 => v i.succ) *
          Multiplicative.ofAdd (fun i : Fin 3 => w i.succ) := by
      apply Multiplicative.toAdd.injective
      funext i
      simp
    rw [hof, map_mul, map_mul]
  change ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => (v + w) i.succ))) : ↥K) : G) =
    ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) : ↥K) : G) *
      ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => w i.succ))) : ↥K) : G)
  exact congrArg (fun x : ↥K => (x : G)) h

private theorem a8kf_eVFun_zero {G : Type} [Group G] {K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) : a8kf_eVFun ρ 0 = 1 := by
  change ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => (0 : Fin 4 → ZMod 7) i.succ))) : ↥K) : G) = 1
  have h0 : (fun i : Fin 3 => (0 : Fin 4 → ZMod 7) i.succ) = (0 : Fin 3 → ZMod 7) := rfl
  rw [h0]
  simp

private theorem a8kf_y_comm_eVFun {G : Type} [Group G] {K : Subgroup G} {y : G}
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G))
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (v : Fin 4 → ZMod 7) :
    Commute y (a8kf_eVFun ρ v) := by
  have he : a8kf_eVFun ρ v ∈ K := (ρ.symm _).2
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hyK he)
  exact h.symm

private noncomputable def a8kf_PhiFun {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hy : y ∈ Bs) (v : Fin 4 → ZMod 7) : ↥Bs :=
  ⟨y ^ (v 0).val * a8kf_eVFun ρ v,
    Bs.mul_mem (Bs.pow_mem hy _) (a8kf_eVFun_mem ρ hρE v)⟩

private noncomputable def a8kf_Phi {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hy : y ∈ Bs) (hy7 : y ^ 7 = 1)
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G)) :
    (Fin 4 → ZMod 7) →+ Additive ↥Bs where
  toFun v := Additive.ofMul (a8kf_PhiFun ρ hρE hy v)
  map_zero' := by
    change Additive.ofMul (a8kf_PhiFun ρ hρE hy 0) = (0 : Additive ↥Bs)
    rw [show a8kf_PhiFun ρ hρE hy 0 = 1 by
      apply Subtype.ext
      simp [a8kf_PhiFun, a8kf_eVFun_zero]]
    rfl
  map_add' v w := by
    change Additive.ofMul (a8kf_PhiFun ρ hρE hy (v + w)) =
      Additive.ofMul (a8kf_PhiFun ρ hρE hy v) + Additive.ofMul (a8kf_PhiFun ρ hρE hy w)
    rw [show Additive.ofMul (a8kf_PhiFun ρ hρE hy v) +
          Additive.ofMul (a8kf_PhiFun ρ hρE hy w) =
        Additive.ofMul (a8kf_PhiFun ρ hρE hy v * a8kf_PhiFun ρ hρE hy w) from rfl]
    congr 1
    have hpowv : y ^ ((v + w) 0).val = y ^ (v 0).val * y ^ (w 0).val := by
      rw [show (v + w) 0 = v 0 + w 0 from rfl]
      exact ggSL9_pow_val_add hy7 (v 0) (w 0)
    have heV := a8kf_eVFun_add ρ v w
    have hcy : Commute (y ^ (w 0).val) (a8kf_eVFun ρ v) :=
      (a8kf_y_comm_eVFun hyK ρ v).pow_left (w 0).val
    apply Subtype.ext
    simp only [a8kf_PhiFun, Subgroup.coe_mul, Subgroup.coe_mk]
    rw [hpowv, heV]
    calc y ^ (v 0).val * y ^ (w 0).val * (a8kf_eVFun ρ v * a8kf_eVFun ρ w)
        = y ^ (v 0).val * (y ^ (w 0).val * a8kf_eVFun ρ v) * a8kf_eVFun ρ w := by group
      _ = y ^ (v 0).val * (a8kf_eVFun ρ v * y ^ (w 0).val) * a8kf_eVFun ρ w := by
            rw [hcy.eq]
      _ = y ^ (v 0).val * a8kf_eVFun ρ v * (y ^ (w 0).val * a8kf_eVFun ρ w) := by group

private theorem a8kf_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    apply Subtype.ext
    change (u : H) * v = v * u
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, Subgroup.mul_comm_of_mem_isMulCommutative E hx hy]
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hp x hx, map_one]

private theorem a8kf_zpowers_y_inf_K {G : Type} [Group G] {K : Subgroup G} {y : G}
    (hZ : Subgroup.center K = ⊥) (hyK : y ∈ Subgroup.centralizer (K : Set G)) :
    Subgroup.zpowers y ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hgC : g ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hyK) hg.1
  have hcenter : (⟨g, hg.2⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgC (k : G) k.2
  rw [hZ] at hcenter
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hcenter)

private theorem a8kf_pow_y_eq_one_of_mem_K {G : Type} [Group G] {K : Subgroup G} {y : G}
    (hZ : Subgroup.center K = ⊥) (hyK : y ∈ Subgroup.centralizer (K : Set G))
    {j : ℕ} (hj : y ^ j ∈ K) : y ^ j = 1 := by
  have hmem : y ^ j ∈ Subgroup.zpowers y ⊓ K :=
    ⟨Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]⟩, hj⟩
  rw [a8kf_zpowers_y_inf_K hZ hyK] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem a8kf_Phi_eq_zero {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hy : y ∈ Bs) (hy7 : y ^ 7 = 1)
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G))
    (hyK' : y ∈ Subgroup.centralizer (K : Set G)) (hy_ne : y ≠ 1)
    (hZ : Subgroup.center K = ⊥) {v : Fin 4 → ZMod 7}
    (hv : a8kf_Phi ρ hρE hy hy7 hyK v = 0) : v = 0 := by
  have hfun : a8kf_PhiFun ρ hρE hy v = 1 := by
    have := congrArg Additive.toMul hv
    simpa [a8kf_Phi] using this
  have hmul : y ^ (v 0).val * a8kf_eVFun ρ v = 1 := by
    have := congrArg (fun x : ↥Bs => (x : G)) hfun
    simpa [a8kf_PhiFun] using this
  have hyKmem : y ^ (v 0).val ∈ K := by
    have h1 : y ^ (v 0).val = (a8kf_eVFun ρ v)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [h1]
    exact K.inv_mem (ρ.symm _).2
  have hy_one : y ^ (v 0).val = 1 := a8kf_pow_y_eq_one_of_mem_K hZ hyK' hyKmem
  have hval0 : (v 0).val = 0 := by
    have hdvd : 7 ∣ (v 0).val := by
      have hord : orderOf y = 7 := orderOf_eq_prime hy7 hy_ne
      have := orderOf_dvd_of_pow_eq_one hy_one
      rwa [hord] at this
    have hlt : (v 0).val < 7 := ZMod.val_lt (v 0)
    omega
  have hv0 : v 0 = 0 := (ZMod.val_eq_zero (v 0)).mp hval0
  have heVone : a8kf_eVFun ρ v = 1 := by
    rw [hy_one, one_mul] at hmul
    exact hmul
  have htail : (fun i : Fin 3 => v i.succ) = 0 := by
    have h1 : ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ))) =
        (1 : ↥K) := Subtype.ext heVone
    have h2 : ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => v i.succ)) = 1 := by
      have := congrArg (fun x : ↥K => (ρ x : GGSL9V ≃ₗ[ZMod 2] GGSL9V)) h1
      simpa using this
    have h3 : Multiplicative.ofAdd (fun i : Fin 3 => v i.succ) = 1 := by
      apply ggSL9TorusCoord_injective
      rw [h2, map_one]
    have h4 : (fun i : Fin 3 => v i.succ) = 0 := by
      have := congrArg Multiplicative.toAdd h3
      simpa using this
    exact h4
  funext i
  fin_cases i
  · exact hv0
  · exact congrFun htail 0
  · exact congrFun htail 1
  · exact congrFun htail 2

private theorem a8kf_Phi_injective {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hy : y ∈ Bs) (hy7 : y ^ 7 = 1)
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G))
    (hyK' : y ∈ Subgroup.centralizer (K : Set G)) (hy_ne : y ≠ 1)
    (hZ : Subgroup.center K = ⊥) :
    Function.Injective (a8kf_Phi ρ hρE hy hy7 hyK) := by
  intro v w hvw
  have hzero : a8kf_Phi ρ hρE hy hy7 hyK (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have := a8kf_Phi_eq_zero ρ hρE hy hy7 hyK hyK' hy_ne hZ hzero
  exact sub_eq_zero.mp this

private theorem a8kf_Phi_surjective {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {y : G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hy : y ∈ Bs) (hy7 : y ^ 7 = 1)
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G))
    (hyK' : y ∈ Subgroup.centralizer (K : Set G)) (hy_ne : y ≠ 1)
    (hZ : Subgroup.center K = ⊥) (hcardBs : Nat.card ↥Bs = 7 ^ 4) :
    Function.Surjective (a8kf_Phi ρ hρE hy hy7 hyK) := by
  have hinj := a8kf_Phi_injective ρ hρE hy hy7 hyK hyK' hy_ne hZ
  have hker : (a8kf_Phi ρ hρE hy hy7 hyK).ker = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [AddMonoidHom.mem_ker] at hv
    exact a8kf_Phi_eq_zero ρ hρE hy hy7 hyK hyK' hy_ne hZ hv
  have hcard_dom : Nat.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcard_range : Nat.card (a8kf_Phi ρ hρE hy hy7 hyK).range =
      Nat.card (Additive ↥Bs) := by
    have h := AddSubgroup.card_ker_mul_card_range (a8kf_Phi ρ hρE hy hy7 hyK)
    rw [hker, AddSubgroup.card_bot, one_mul, hcard_dom] at h
    rw [h, Nat.card_congr Additive.toMul, hcardBs]
  haveI : Finite ↥Bs := Finite.of_injective (fun x : ↥Bs => (x : G)) Subtype.coe_injective
  haveI : Finite (Additive ↥Bs) := Finite.of_equiv ↥Bs Additive.ofMul
  haveI : Finite (a8kf_Phi ρ hρE hy hy7 hyK).range :=
    Finite.of_injective (fun x : ↥(a8kf_Phi ρ hρE hy hy7 hyK).range => (x : Additive ↥Bs))
      Subtype.coe_injective
  have htop : (a8kf_Phi ρ hρE hy hy7 hyK).range = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ hcard_range
  intro b
  exact AddMonoidHom.mem_range.mp (by rw [htop]; exact AddSubgroup.mem_top b)

theorem ggA8Nbr_kFrame
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr 7 B x D J y K) (hinn : GGInnerDiagOn Bs K)
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1)
    (hJK : J ≤ K) (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hy : y ∈ Bs) :
    ∃ (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)),
      GGA8KFrame Bs K y hy ρ ι := by
  classical
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hperf : commutator K = ⊤ := hKc.2.2.1
  obtain ⟨φ, hrange, hinj⟩ :=
    GGHalf.exists_slLift_two (m := 6) (by norm_num) hperf hKm
  let ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := a8kf_rho0 φ hinj hrange
  have hZ : Subgroup.center K = ⊥ := a8kf_center_eq_bot ρ₀
  have hkerφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 9) F2) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hinj]
    exact bot_le
  have hAex0 := exists_mem_ggInducedPairs_of_innerDiagOn (Bs := Bs) (X := K) (n := 8) (f := 1)
      hMp (by norm_num) hKm.1 hinn hkerφ hrange
  have hAex : ∀ b : ↥Bs, ∃ A : GL (Fin 9) F2,
      ((b : G), A) ∈ LinFusion.ggInducedPairs φ := fun b => hAex0 (b : G) b.2
  let A : ↥Bs → GL (Fin 9) F2 := fun b => Classical.choose (hAex b)
  have hA : ∀ b : ↥Bs, ((b : G), A b) ∈ LinFusion.ggInducedPairs φ :=
    fun b => Classical.choose_spec (hAex b)
  haveI : IsMulCommutative ↥Bs := hcfg.2.1.2.1.1
  have hcomm : ∀ a b : ↥Bs, a * b = b * a :=
    fun a b => Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative Bs a.2 b.2)
  have hpow : ∀ b : ↥Bs, (b : G) ^ 7 = 1 := fun b => hcfg.2.1.2.1.2 b b.2
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hκB : ∀ b : ↥Bs, (a8kf_kappa hrange hA b : G) ∈ Bs :=
    fun b => a8kf_kappa_mem_Bs hrange hZ hA hcomm hSC (hpow b)
  have hcardE_range : Nat.card ↥(Bs ⊓ K) =
      Nat.card (a8kf_kappaHom hrange hZ hA).range :=
    a8kf_card_E hrange hZ hA hcomm hSC hpow
  have hrange_card : 7 * Nat.card (a8kf_kappaHom hrange hZ hA).range = Nat.card ↥Bs :=
    a8kf_card_range hrange hZ hA hcfg hnb hCJ hJK
  have hmulti : 7 * Nat.card ↥(Bs ⊓ K) = Nat.card ↥Bs := by
    rw [hcardE_range]
    exact hrange_card
  have hge : 7 ^ 3 ≤ Nat.card ↥(Bs ⊓ K) := by
    have h := hcfg.tableB_facts.2.2.2.2
    rw [← hmulti] at h
    have h' : 7 * 7 ^ 3 ≤ 7 * Nat.card ↥(Bs ⊓ K) := by
      calc 7 * 7 ^ 3 = 7 ^ 4 := by norm_num
        _ ≤ 7 * Nat.card ↥(Bs ⊓ K) := h
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  have hEab : IsElemAbelian 7 ((Bs ⊓ K).subgroupOf K) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mul_comm_of_mem_isMulCommutative Bs a.2.1 b.2.1
    · apply Subtype.ext
      exact hcfg.2.1.2.1.2 (x : G) hx.1
  have hEab' : IsElemAbelian 7 (((Bs ⊓ K).subgroupOf K).map ρ₀.toMonoidHom) :=
    a8kf_isElemAbelian_map ρ₀.toMonoidHom hEab
  have hcard_map : Nat.card ↥(((Bs ⊓ K).subgroupOf K).map ρ₀.toMonoidHom) =
      Nat.card ↥(Bs ⊓ K) := by
    rw [Subgroup.card_map_of_injective ρ₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  have hge' : 7 ^ 3 ≤ Nat.card ↥(((Bs ⊓ K).subgroupOf K).map ρ₀.toMonoidHom) := by
    rw [hcard_map]
    exact hge
  obtain ⟨g₀, hg₀⟩ := exists_conj_eq_ggSL9Torus hEab' hge'
  have hcardE : Nat.card ↥(Bs ⊓ K) = 7 ^ 3 := by
    rw [← hcard_map, hg₀,
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective, card_ggSL9Torus]
  have hcardBs : Nat.card ↥Bs = 7 ^ 4 := by
    rw [← hmulti, hcardE]
    norm_num
  let ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := ρ₀.trans (MulAut.conj g₀⁻¹)
  have hρE : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus := by
    show ((Bs ⊓ K).subgroupOf K).map
      ((MulAut.conj g₀⁻¹).toMonoidHom.comp ρ₀.toMonoidHom) = ggSL9Torus
    rw [← Subgroup.map_map, hg₀, Subgroup.map_map]
    have hconj : (MulAut.conj g₀⁻¹).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change MulAut.conj g₀⁻¹ (MulAut.conj g₀ x) = x
      rw [show MulAut.conj g₀⁻¹ = (MulAut.conj g₀)⁻¹ from map_inv _ _]
      exact (MulAut.conj g₀).symm_apply_apply x
    rw [hconj, Subgroup.map_id]
  have hy7 : y ^ 7 = 1 := hnb.1.1.1.2 y hnb.1.2.1
  have hyK' : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)
  have hy_ne : y ≠ 1 := hnb.1.2.2.1
  have hyKle : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  let Φ : (Fin 4 → ZMod 7) →+ Additive ↥Bs := a8kf_Phi ρ hρE hy hy7 hyKle
  have hinjΦ : Function.Injective Φ :=
    a8kf_Phi_injective ρ hρE hy hy7 hyKle hyK' hy_ne hZ
  have hsurjΦ : Function.Surjective Φ :=
    a8kf_Phi_surjective ρ hρE hy hy7 hyKle hyK' hy_ne hZ hcardBs
  let Φe : (Fin 4 → ZMod 7) ≃+ Additive ↥Bs := AddEquiv.ofBijective Φ ⟨hinjΦ, hsurjΦ⟩
  let ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) := Φe.symm
  let v : ↥Bs → (Fin 4 → ZMod 7) := fun b => ι (Additive.ofMul b)
  have hvPhi : ∀ b : ↥Bs, Φ (v b) = Additive.ofMul b := fun b =>
    Φe.apply_symm_apply (Additive.ofMul b)
  have hPhiFun : ∀ b : ↥Bs, a8kf_PhiFun ρ hρE hy (v b) = b := by
    intro b
    have h := congrArg Additive.toMul (hvPhi b)
    simpa [Φ, a8kf_Phi] using h
  have hval : ∀ b : ↥Bs, (b : G) = y ^ ((v b) 0).val * a8kf_eVFun ρ (v b) := by
    intro b
    have h := congrArg (fun x : ↥Bs => (x : G)) (hPhiFun b)
    simpa [a8kf_PhiFun] using h.symm
  have hy_pow_mem_K : ∀ b : ↥Bs, (b : G) ∈ K → y ^ ((v b) 0).val ∈ K := by
    intro b hbK
    have h := hval b
    have h1 : y ^ ((v b) 0).val = (b : G) * (a8kf_eVFun ρ (v b))⁻¹ := by
      rw [h]
      group
    rw [h1]
    exact K.mul_mem hbK (K.inv_mem (ρ.symm _).2)
  refine ⟨ρ, ι, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    have hsingle : Φ (Pi.single 0 1) = Additive.ofMul ⟨y, hy⟩ := by
      change Additive.ofMul (a8kf_PhiFun ρ hρE hy (Pi.single 0 1)) =
        Additive.ofMul ⟨y, hy⟩
      congr 1
      apply Subtype.ext
      have htail : (fun i : Fin 3 =>
          (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) i.succ) = 0 := by
        funext i; simp
      have heV : a8kf_eVFun ρ (Pi.single 0 (1 : ZMod 7)) = 1 := by
        change ((ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd
          (fun i : Fin 3 => (Pi.single 0 (1 : ZMod 7) : Fin 4 → ZMod 7) i.succ))) : ↥K) : G) = 1
        rw [htail]
        exact a8kf_eVFun_zero ρ
      simp only [a8kf_PhiFun, Subgroup.coe_mk]
      rw [heV]
      haveI : Fact (1 < 7) := ⟨by norm_num⟩
      simp [ZMod.val_one]
    exact (Φe.symm_apply_eq).mpr hsingle.symm
  ·
    intro b
    constructor
    · intro h0
      have hb : (b : G) = a8kf_eVFun ρ (v b) := by
        have h0' : (v b) 0 = 0 := h0
        rw [hval b, h0']
        simp
      rw [hb]
      exact (ρ.symm _).2
    · intro hbK
      have hyKmem := hy_pow_mem_K b hbK
      have hy_one := a8kf_pow_y_eq_one_of_mem_K hZ hyK' hyKmem
      have hdvd : 7 ∣ ((v b) 0).val := by
        have hord : orderOf y = 7 := orderOf_eq_prime hy7 hy_ne
        have := orderOf_dvd_of_pow_eq_one hy_one
        rwa [hord] at this
      have hlt : ((v b) 0).val < 7 := ZMod.val_lt _
      have hzero : ((v b) 0).val = 0 := by omega
      exact (ZMod.val_eq_zero ((v b) 0)).mp hzero
  ·
    intro b hb
    have hyKmem := hy_pow_mem_K b hb
    have hy_one := a8kf_pow_y_eq_one_of_mem_K hZ hyK' hyKmem
    have hb_eq : (b : G) = a8kf_eVFun ρ (v b) := by
      rw [hval b, hy_one, one_mul]
    have heq : (⟨b, hb⟩ : ↥K) =
        ρ.symm (ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => (v b) i.succ))) := by
      apply Subtype.ext
      simpa [a8kf_eVFun] using hb_eq
    rw [heq, MulEquiv.apply_symm_apply]

end CFSG.StandardType.A8Coord

end
