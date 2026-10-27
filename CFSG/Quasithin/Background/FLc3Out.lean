module

public import CFSG.Quasithin.Background.FLcAut
public import CFSG.Quasithin.Background.FLcFlagU

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {V : Type} [CommGroup V]

structure StSetting (n : ℕ) (ρ : SLt n →* MulAut V) (Sst : Subgroup (MulAut V)) : Prop where
  inj : Function.Injective ρ
  p2 : IsPGroup 2 Sst
  T_le : ∀ u ∈ Ut n, ρ u ∈ Sst
  norm : ∀ s ∈ Sst, ∀ y : SLt n, ∃ y' : SLt n, s * ρ y * s⁻¹ = ρ y'
  cent : ∀ s ∈ Sst, (∀ y : SLt n, s * ρ y = ρ y * s) → s = 1

namespace StSetting

variable {n : ℕ} {ρ : SLt n →* MulAut V} {Sst : Subgroup (MulAut V)} (h : StSetting n ρ Sst)

include h

theorem inter (hn : 1 ≤ n) {y : SLt n} (hy : ρ y ∈ Sst) : y ∈ Ut n := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  have hY : IsPGroup 2 ↥(Sst.comap ρ) := h.p2.comap_of_injective ρ h.inj
  have hle : (P : Subgroup (SLt n)) ≤ Sst.comap ρ := by
    rw [hP]
    exact fun u hu => h.T_le u hu
  have hPY := P.is_maximal' hY hle
  have hy' : y ∈ Sst.comap ρ := hy
  rw [hPY, hP] at hy'
  exact hy'

theorem mem_normalizer {s : MulAut V} (hs : s ∈ Sst) :
    s ∈ Subgroup.normalizer (ρ.range : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := h.norm s hs y
    exact ⟨y', hy'.symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy'⟩ := h.norm s⁻¹ (Sst.inv_mem hs) y
    refine ⟨y', ?_⟩
    have : g = s⁻¹ * (s * g * s⁻¹) * s⁻¹⁻¹ := by group
    rw [this, ← hy, hy']

@[expose] noncomputable def phi {s : MulAut V} (hs : s ∈ Sst) : SLt n ≃* SLt n :=
  (MonoidHom.ofInjective h.inj).trans
    (((ρ.range.normalizerMonoidHom ⟨s, h.mem_normalizer hs⟩ : MulAut ↥ρ.range) :
      ↥ρ.range ≃* ↥ρ.range).trans (MonoidHom.ofInjective h.inj).symm)

theorem rho_phi {s : MulAut V} (hs : s ∈ Sst) (y : SLt n) : ρ (h.phi hs y) = s * ρ y * s⁻¹ := by
  have h1 := (MonoidHom.ofInjective h.inj).apply_symm_apply
    ((ρ.range.normalizerMonoidHom ⟨s, h.mem_normalizer hs⟩ : MulAut ↥ρ.range) (MonoidHom.ofInjective h.inj y))
  have h2 := congrArg Subtype.val h1
  have h3 : ((MonoidHom.ofInjective h.inj) ((MonoidHom.ofInjective h.inj).symm
      ((ρ.range.normalizerMonoidHom ⟨s, h.mem_normalizer hs⟩ : MulAut ↥ρ.range)
        (MonoidHom.ofInjective h.inj y))) : MulAut V) = ρ (h.phi hs y) := rfl
  rw [h3] at h2
  rw [h2]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe ρ.range ⟨s, h.mem_normalizer hs⟩
    (MonoidHom.ofInjective h.inj y)

theorem phi_Ut (hn : 1 ≤ n) {s : MulAut V} (hs : s ∈ Sst) :
    (Ut n).map (h.phi hs).toMonoidHom = Ut n := by
  have hle : (Ut n).map (h.phi hs).toMonoidHom ≤ Ut n := by
    rintro _ ⟨u, hu, rfl⟩
    apply h.inter hn
    have : ρ (h.phi hs u) = s * ρ u * s⁻¹ := h.rho_phi hs u
    show ρ (h.phi hs u) ∈ Sst
    rw [this]
    exact Sst.mul_mem (Sst.mul_mem hs (h.T_le u hu)) (Sst.inv_mem hs)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have : Nat.card ↥((Ut n).map (h.phi hs).toMonoidHom) = Nat.card ↥(Ut n) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (Ut n) (h.phi hs).toMonoidHom
      (h.phi hs).injective).toEquiv.symm
  rw [this]

theorem eq_rho_of_inner {s : MulAut V} (hs : s ∈ Sst) {b : SLt n} (hb : b ∈ Ut n)
    (hφ : ∀ g, h.phi hs g = b * g * b⁻¹) : s = ρ b := by
  have hc : (ρ b)⁻¹ * s ∈ Sst := Sst.mul_mem (Sst.inv_mem (h.T_le b hb)) hs
  have h1 : (ρ b)⁻¹ * s = 1 := by
    refine h.cent _ hc fun y => ?_
    have e1 := h.rho_phi hs y
    rw [hφ, map_mul, map_mul, map_inv] at e1
    calc (ρ b)⁻¹ * s * ρ y = (ρ b)⁻¹ * (s * ρ y * s⁻¹) * s := by group
      _ = (ρ b)⁻¹ * (ρ b * ρ y * (ρ b)⁻¹) * s := by rw [← e1]
      _ = ρ y * ((ρ b)⁻¹ * s) := by group
  have := congrArg (fun x => ρ b * x) h1
  simpa using this

end StSetting

theorem map_QI_of_outer {n : ℕ} {φ : SLt n ≃* SLt n}
    (hφ : ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map φ.toMonoidHom =
      stabilizer (flagSpace n (ZMod 2) (n - d))) {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i) :
    (QI n I).map φ.toMonoidHom = QI n ((fun i => n - i) '' I) := by
  ext g
  have key : ∀ (d : ℕ), IsNode n d → ∀ x : SLt n,
      x ∈ stabilizer (flagSpace n (ZMod 2) (n - d)) ↔ φ.symm x ∈ stabilizer (flagSpace n (ZMod 2) d) := by
    intro d hd x
    rw [← hφ d hd.1 hd.2]
    exact (mem_map_mulEquiv_iff φ _ x)
  show g ∈ (QI n I).map (φ : SLt n →* SLt n) ↔ _
  rw [mem_map_mulEquiv_iff, mem_flagStabilizer, mem_flagStabilizer]
  constructor
  · intro hg j hj
    obtain ⟨i, hiI, rfl⟩ := hj
    exact (key i (hI i hiI) g).2 (hg i hiI)
  · intro hg i hi
    exact (key i (hI i hi) g).1 (hg _ ⟨i, hi, rfl⟩)

namespace StSetting

variable {n : ℕ} {ρ : SLt n →* MulAut V} {Sst : Subgroup (MulAut V)} (h : StSetting n ρ Sst)

include h

theorem Q_le_rhoUt (hn : 3 ≤ n) {Q : Subgroup (MulAut V)} (hQS : Q ≤ Sst) {I : Set ℕ}
    (hI : ∀ i ∈ I, IsNode n i) (hasym : ∃ i ∈ I, n - i ∉ I)
    (hnormQ : ∀ x ∈ QI n I, ∀ a ∈ Q, ρ x * a * (ρ x)⁻¹ ∈ Q) : Q ≤ (Ut n).map ρ := by
  intro a ha
  have hs : a ∈ Sst := hQS ha
  rcases aut_dichotomy hn (h.phi hs) (h.phi_Ut (by omega) hs) with ⟨b, hb, hbφ⟩ | hout
  · exact ⟨b, hb, (h.eq_rho_of_inner hs hb hbφ).symm⟩
  · exfalso
    have hmap : (QI n I).map (h.phi hs).toMonoidHom ≤ QI n I := by
      rintro _ ⟨x, hx, rfl⟩
      have hc : a * (ρ x * a⁻¹ * (ρ x)⁻¹) ∈ Q :=
        Q.mul_mem ha (hnormQ x hx a⁻¹ (Q.inv_mem ha))
      have hce : a * (ρ x * a⁻¹ * (ρ x)⁻¹) = ρ (h.phi hs x * x⁻¹) := by
        rw [map_mul, h.rho_phi hs x, map_inv]
        group
      have hUt : h.phi hs x * x⁻¹ ∈ Ut n := by
        apply h.inter (by omega)
        rw [← hce]
        exact hQS hc
      have : h.phi hs x = (h.phi hs x * x⁻¹) * x := by group
      show (h.phi hs) x ∈ QI n I
      rw [this]
      exact (QI n I).mul_mem (Ut_le_QI n I hUt) hx
    rw [map_QI_of_outer hout hI] at hmap
    have hsub := (QI_le_QI_iff hI).1 hmap
    obtain ⟨i, hiI, hni⟩ := hasym
    obtain ⟨j, hjI, hj⟩ := hsub hiI
    apply hni
    have hjn : j < n := (hI j hjI).2
    have hj' : n - j = i := hj
    have : n - i = j := by omega
    rw [this]
    exact hjI

end StSetting

theorem mat_transv_mulVec_apply {n : ℕ} {a b : Fin n} (h : a ≠ b) (v : Vt n) (c : Fin n) :
    ((1 + Matrix.single a b (1 : ZMod 2)) *ᵥ v) c = v c + (if c = a then v b else 0) := by
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.one_mulVec]
  congr 1
  by_cases hc : c = a
  · subst hc
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have : a ≠ c := Ne.symm hc
    simp [Matrix.mulVec, dotProduct, hc, this]

theorem transvection_sq {n : ℕ} {i j : Fin n} (hji : j ≠ i) :
    (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) *
      Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  have hE : Matrix.single j i (1 : ZMod 2) * Matrix.single j i (1 : ZMod 2) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ hji.symm _
  have h2 : (1 + Matrix.single j i (1 : ZMod 2)) * (1 + Matrix.single j i (1 : ZMod 2)) =
      1 + (Matrix.single j i (1 : ZMod 2) + Matrix.single j i (1 : ZMod 2)) +
        Matrix.single j i (1 : ZMod 2) * Matrix.single j i (1 : ZMod 2) := by
    noncomm_ring
  rw [h2, hE, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl]
  simp

theorem transv_mem_QI {n : ℕ} {I : Set ℕ} {i j : Fin n} (hji : j ≠ i)
    (hblock : ∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) :
    (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) ∈ QI n I := by
  rw [mem_flagStabilizer]
  intro d hd
  have hpres : ∀ v : Vt n, v ∈ flagSpace n (ZMod 2) d →
      mat (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) *ᵥ v ∈
        flagSpace n (ZMod 2) d := by
    intro v hv
    rw [mem_flagSpace] at hv ⊢
    intro k hk
    have hco : mat (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) =
        1 + Matrix.single j i (1 : ZMod 2) := Matrix.SpecialLinearGroup.transvection_coe hji 1
    rw [hco, mat_transv_mulVec_apply hji, hv k hk]
    by_cases hkj : k = j
    · subst hkj
      have : ¬ (i : ℕ) < d := fun hid => absurd (hblock d hd hid) (not_lt.mpr hk)
      simp [hv i (not_lt.mp this)]
    · simp [hkj]
  rw [mem_stabilizer_iff]
  intro v
  refine ⟨hpres v, fun hv => ?_⟩
  have h1 := hpres _ hv
  have e : mat (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) *ᵥ
      (mat (Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) : SLt n) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← mat_mul, transvection_sq hji, mat_one, Matrix.one_mulVec]
  rwa [e] at h1

theorem entry_zero_of_normalized {n : ℕ} {Y : Subgroup (SLt n)} (hY : Y ≤ Ut n) {I : Set ℕ}
    (hnorm : ∀ x ∈ QI n I, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) {i j : Fin n} (hij : i < j)
    (hblock : ∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) {y : SLt n} (hy : y ∈ Y) : mat y i j = 0 := by
  have hji : j ≠ i := hij.ne'
  set t : SLt n := Matrix.SpecialLinearGroup.transvection hji (1 : ZMod 2) with ht
  have ht2 : t * t = 1 := transvection_sq hji
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : t * y * t⁻¹ ∈ Y := hnorm t (transv_mem_QI hji hblock) y hy
  have hU := hY hconj
  have hyU := hY hy
  have hentry : mat (t * y * t⁻¹) j i = 0 := hU.1 j i hij
  rw [htinv, mat_mul, mat_mul] at hentry
  have hco : mat t = 1 + Matrix.single j i (1 : ZMod 2) := Matrix.SpecialLinearGroup.transvection_coe hji 1
  rw [hco] at hentry
  have hexp : ((1 + Matrix.single j i (1 : ZMod 2)) * mat y * (1 + Matrix.single j i (1 : ZMod 2))) j i =
      mat y j i + mat y i i + mat y j j + mat y i j := by
    simp [add_mul, mul_add, Matrix.mul_assoc, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same]
    ring
  have h1 : mat y j i = 0 := hyU.1 j i hij
  have h2 : mat y i i = 1 := hyU.2 i
  have h3 : mat y j j = 1 := hyU.2 j
  rw [hexp, h1, h2, h3] at hentry
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  calc mat y i j = 0 + 1 + 1 + mat y i j := by rw [add_assoc 0, h11]; simp
    _ = 0 := hentry

end CFSG.Quasithin.FLc
