module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux7
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux8

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type u} [Group Γ]

theorem qpre_mono (V : Subgroup Γ) {U U' : Subgroup (QG V)} (h : U ≤ U') :
    qpre V U ≤ qpre V U' := fun x hx => by
  obtain ⟨hn, hxU⟩ := mem_qpre_iff.mp hx
  exact mem_qpre_iff.mpr ⟨hn, h hxU⟩

theorem qimg_self (V : Subgroup Γ) : qimg V V = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff V V u).mp hu
  rw [Subgroup.mem_bot]
  exact (qmap_eq_one_iff V y).mpr hy

theorem qpre_bot (V : Subgroup Γ) : qpre V ⊥ = V := by
  refine le_antisymm (fun x hx => ?_) (le_qpre V ⊥)
  obtain ⟨hn, h⟩ := mem_qpre_iff.mp hx
  rw [Subgroup.mem_bot, qmap_eq_one_iff] at h
  exact h

theorem isChiefFactorOf_qimg {V H M N : Subgroup Γ} (hH : H ≤ nrm V) (hVN : V ≤ N)
    (h : IsChiefFactorOf H M N) : IsChiefFactorOf (qimg V H) (qimg V M) (qimg V N) := by
  obtain ⟨hNH, hMH, hNM, hmin⟩ := h
  have hMn : M ≤ nrm V := hMH.1.trans hH
  have hNn : N ≤ nrm V := hNH.1.trans hH
  have hVM : V ≤ M := hVN.trans hNM.le
  have hVH : V ≤ H := hVN.trans hNH.1
  refine ⟨⟨qimg_mono V hNH.1, qimg_le_normalizer hNH.2⟩,
    ⟨qimg_mono V hMH.1, qimg_le_normalizer hMH.2⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne (qimg_mono V hNM.le) fun heq => hNM.ne ?_
    have := congrArg (qpre V) heq
    rwa [qpre_qimg hVN hNn, qpre_qimg hVM hMn] at this
  · intro K' hK' hNK hKM
    have hKH : qpre V K' ≤ H := by
      have := qpre_mono V hK'.1
      rwa [qpre_qimg hVH hH] at this
    have hKnorm : IsNormalIn (qpre V K') H :=
      ⟨hKH, fun x hx => mem_nrm_of_qmap_normalizer (hH hx) (hK'.2 (mem_qimg_of_mem hx (hH hx)))⟩
    have hNK' : N ≤ qpre V K' := by
      have := qpre_mono V hNK
      rwa [qpre_qimg hVN hNn] at this
    have hKM' : qpre V K' ≤ M := by
      have := qpre_mono V hKM
      rwa [qpre_qimg hVM hMn] at this
    rcases hmin _ hKnorm hNK' hKM' with h | h
    · left
      rw [← qimg_qpre V K', h]
    · right
      rw [← qimg_qpre V K', h]

theorem isChiefFactorOf_qpre {V H : Subgroup Γ} (hVH : V ≤ H) (hH : H ≤ nrm V)
    {M' N' : Subgroup (QG V)} (h : IsChiefFactorOf (qimg V H) M' N') :
    IsChiefFactorOf H (qpre V M') (qpre V N') := by
  obtain ⟨hNH, hMH, hNM, hmin⟩ := h
  have hlift : ∀ U : Subgroup (QG V), IsNormalIn U (qimg V H) → IsNormalIn (qpre V U) H := by
    intro U hU
    refine ⟨?_, fun x hx => mem_nrm_of_qmap_normalizer (hH hx) (hU.2 (mem_qimg_of_mem hx (hH hx)))⟩
    have := qpre_mono V hU.1
    rwa [qpre_qimg hVH hH] at this
  refine ⟨hlift _ hNH, hlift _ hMH, ?_, ?_⟩
  · refine lt_of_le_of_ne (qpre_mono V hNM.le) fun heq => hNM.ne ?_
    have := congrArg (qimg V) heq
    rwa [qimg_qpre, qimg_qpre] at this
  · intro K hK hNK hKM
    have hVK : V ≤ K := (le_qpre V N').trans hNK
    have hKn : K ≤ nrm V := hK.1.trans hH
    have hK' : IsNormalIn (qimg V K) (qimg V H) :=
      ⟨qimg_mono V hK.1, qimg_le_normalizer hK.2⟩
    have h1 : N' ≤ qimg V K := by
      have := qimg_mono V hNK
      rwa [qimg_qpre] at this
    have h2 : qimg V K ≤ M' := by
      have := qimg_mono V hKM
      rwa [qimg_qpre] at this
    rcases hmin _ hK' h1 h2 with h | h
    · left
      rw [← qpre_qimg hVK hKn, h]
    · right
      rw [← qpre_qimg hVK hKn, h]

section Orbit

variable [Finite Γ]

omit [Finite Γ] in
theorem orbitClosure_le_of_le_of_normalizes {J R X : Subgroup Γ} (hJ : J ≤ R)
    (hXR : X ≤ Subgroup.normalizer (R : Set Γ)) : orbitClosure J X ≤ R := by
  refine iSup₂_le fun x hx => ?_
  rintro _ ⟨j, hj, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (hXR hx) j).mp (hJ hj)
  exact this

omit [Finite Γ] in
theorem orbitClosure_le_of_le {J X : Subgroup Γ} (hJ : J ≤ X) : orbitClosure J X ≤ X :=
  orbitClosure_le_of_le_of_normalizes hJ (fun x hx => Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => mul_mem (mul_mem hx hy) (inv_mem hx), fun hy => by
      simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hx) hy) hx⟩)

theorem isChiefFactorOf_orbitClosure {R X J : Subgroup Γ} (hRX : R ≤ X)
    (hXR : X ≤ Subgroup.normalizer (R : Set Γ)) (hJ : J ∈ lcal R) :
    IsChiefFactorOf X (orbitClosure J X) ⊥ := by
  have hsub := L514.conjOrbit_subset_lcal hXR hJ
  have hL := L514.isDirectProduct_conjOrbit hXR hJ
  have hJX : J ≤ X := (mem_lcal_iff.mp hJ).1.trans hRX
  have hMX : orbitClosure J X ≤ X := orbitClosure_le_of_le hJX
  have hAS : IsASimple X (orbitClosure J X) :=
    isASimple_of_isDirectProduct hL (fun D hD => simple_of_mem_lcal (hsub hD))
      ⟨J, L514.self_mem_conjOrbit X J⟩ (fun x hx => L514.mem_normalizer_orbitClosure hx)
      (fun D hD D' hD' => L514.exists_conj_of_mem_conjOrbit hD hD')
  obtain ⟨-, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
  have hJbot : J ≠ ⊥ := fun h => hnc (by rw [h]; infer_instance)
  refine ⟨⟨bot_le, Subgroup.le_normalizer_of_normal⟩,
    ⟨hMX, fun x hx => L514.mem_normalizer_orbitClosure hx⟩,
    bot_lt_iff_ne_bot.mpr fun h => hJbot (eq_bot_iff.mpr (h ▸ le_orbitClosure J X)), ?_⟩
  intro K hK hbK hKM
  have hnorm : (K.subgroupOf (orbitClosure J X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr (hMX.trans hK.2)
  exact hAS.2.2 K hKM hnorm hK.2

omit [Finite Γ] in
theorem mem_normalizer_orbitClosure_of_normalizer {J X : Subgroup Γ} {d : Γ}
    (hdJ : d ∈ Subgroup.normalizer (J : Set Γ)) (hdX : d ∈ Subgroup.normalizer (X : Set Γ)) :
    d ∈ Subgroup.normalizer ((orbitClosure J X : Subgroup Γ) : Set Γ) := by
  have key : ∀ d : Γ, d ∈ Subgroup.normalizer (J : Set Γ) → d ∈ Subgroup.normalizer (X : Set Γ) →
      ∀ y ∈ orbitClosure J X, d * y * d⁻¹ ∈ orbitClosure J X := by
    intro d hdJ hdX
    have hJd := L514.map_conj_eq_of_mem_normalizer hdJ
    have hle : orbitClosure J X ≤ (orbitClosure J X).comap (MulAut.conj d).toMonoidHom := by
      refine iSup₂_le fun x hx => ?_
      intro z hz
      obtain ⟨j, hj, rfl⟩ := hz
      have hx' : d * x * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hdX x).mp hx
      have e : (d * x * d⁻¹) * d = d * x := by group
      have h1 : (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj d).toMonoidHom =
          J.map (MulAut.conj (d * x * d⁻¹)).toMonoidHom := by
        calc (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj d).toMonoidHom
            = J.map (MulAut.conj (d * x)).toMonoidHom := L514.map_conj_map_conj J x d
          _ = J.map (MulAut.conj ((d * x * d⁻¹) * d)).toMonoidHom := by rw [e]
          _ = (J.map (MulAut.conj d).toMonoidHom).map (MulAut.conj (d * x * d⁻¹)).toMonoidHom :=
            (L514.map_conj_map_conj J d (d * x * d⁻¹)).symm
          _ = J.map (MulAut.conj (d * x * d⁻¹)).toMonoidHom := by rw [hJd]
      have h2 : (J.map (MulAut.conj (d * x * d⁻¹)).toMonoidHom) ≤ orbitClosure J X :=
        map_conj_le_orbitClosure J hx'
      have h3 : MulAut.conj d (MulAut.conj x j) ∈
          (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj d).toMonoidHom :=
        ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      rw [h1] at h3
      exact h2 h3
    intro y hy
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key d hdJ hdX y, fun hy => ?_⟩
  have := key d⁻¹ (inv_mem hdJ) (inv_mem hdX) _ hy
  simpa [mul_assoc] using this

omit [Finite Γ] in
theorem centralizer_orbitClosure {A J : Subgroup Γ} (hA : IsMulCommutative A) {c : Γ} (hc : c ∈ A)
    (hcJ : c ∈ Subgroup.centralizer (J : Set Γ)) :
    c ∈ Subgroup.centralizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  have hle : orbitClosure J A ≤ Subgroup.centralizer ({c} : Set Γ) := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hca : c * a = a * c := (commute_of_mem hA hc ha).eq
    have hcj : c * j = j * c := (Subgroup.mem_centralizer_iff.mp hcJ j hj).symm
    show (MulAut.conj a) j * c = c * (MulAut.conj a) j
    simp only [MulAut.conj_apply]
    calc a * j * a⁻¹ * c = a * j * (a⁻¹ * c) := by group
      _ = a * j * (c * a⁻¹) := by
        have : a⁻¹ * c = c * a⁻¹ := by
          have h2 := congrArg (fun z => a⁻¹ * z * a⁻¹) hca
          simpa [mul_assoc] using h2
        rw [this]
      _ = a * (j * c) * a⁻¹ := by group
      _ = a * (c * j) * a⁻¹ := by rw [hcj]
      _ = (a * c) * j * a⁻¹ := by group
      _ = (c * a) * j * a⁻¹ := by rw [hca]
      _ = c * (a * j * a⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

end Orbit

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
