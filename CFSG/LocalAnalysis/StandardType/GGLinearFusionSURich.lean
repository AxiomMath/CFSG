module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LieType.Universal.Unitary

namespace UFusion

open InnerDiagSU

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

theorem norm_one_mul {a b : Fˣ} (ha : σ (a : F) * a = 1) (hb : σ (b : F) * b = 1) :
    σ ((a * b : Fˣ) : F) * ((a * b : Fˣ) : F) = 1 := by
  rw [Units.val_mul, map_mul]
  calc σ (a : F) * σ (b : F) * ((a : F) * b) = (σ (a : F) * a) * (σ (b : F) * b) := by ring
    _ = 1 := by rw [ha, hb, one_mul]

theorem norm_one_inv {a : Fˣ} (ha : σ (a : F) * a = 1) :
    σ ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) = 1 := by
  have h1 : σ ((a⁻¹ : Fˣ) : F) * σ (a : F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc σ ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) =
      σ ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) * (σ (a : F) * a) := by rw [ha, mul_one]
    _ = (σ ((a⁻¹ : Fˣ) : F) * σ (a : F)) * (((a⁻¹ : Fˣ) : F) * a) := by ring
    _ = 1 := by rw [h1, Units.inv_mul, one_mul]

theorem exists_mem_suInducedPairs_mulSingle (ψ : SU σ (m + 1) →* G) {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) (k j : Fin (m + 1)) {ζ : Fˣ} (hζ : σ (ζ : F) * ζ = 1) :
    ∃ z ∈ ψ.range, (z, LinFusion.ggFrameDiag Q (Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹)) ∈
      suInducedPairs ψ := by
  classical
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹ with he
  have hprod : ∏ x, ((e x : Fˣ) : F) = 1 := by
    rw [← Units.coe_prod]
    simp only [he, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true, mul_inv_cancel, Units.val_one]
  have hnorm : ∀ i, σ ((e i : Fˣ) : F) * ((e i : Fˣ) : F) = 1 := by
    intro i
    have h1 : ∀ c : Fˣ, σ (c : F) * c = 1 → ∀ l : Fin (m + 1),
        σ (((Pi.mulSingle l c : Fin (m + 1) → Fˣ) i : Fˣ) : F) *
          (((Pi.mulSingle l c : Fin (m + 1) → Fˣ) i : Fˣ) : F) = 1 := by
      intro c hc l
      by_cases hil : i = l
      · rw [hil, Pi.mulSingle_eq_same, hc]
      · rw [Pi.mulSingle_eq_of_ne hil, Units.val_one, map_one, one_mul]
    rw [he, Pi.mul_apply]
    exact norm_one_mul (h1 ζ hζ k) (h1 ζ⁻¹ (norm_one_inv hζ) j)
  have hdet : ((LinFusion.ggFrameDiag Q e : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
    rw [LinFusion.ggFrameDiag, det_frame_conj, InnerDiagA.coe_diagGL, det_diagonal, hprod]
  let s : SU σ (m + 1) := ⟨LinFusion.ggFrameDiag Q e,
    mem_SU.mpr ⟨hdet, isJUnitary_frame hQ (isIdUnitary_diagGL hnorm)⟩⟩
  exact ⟨ψ s, ⟨s, rfl⟩, mem_suInducedPairs_coe ψ s⟩

variable [CharP F 2]

theorem card_lt_card_centralizer_uFrameBlock [Finite G] {ψ : SU σ (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) {p : ℕ} {Bs D : Subgroup G} (hBT : Bs ≤ uFrameTorus ψ Q)
    (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ : Finset (Fin (m + 1))}
    (hD : Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I₀ : Set G) = D)
    {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hζσ : σ (ζ : F) * ζ = 1) (hI₀2 : 2 ≤ I₀.card)
    (hI₀u : I₀ ≠ Finset.univ) {I : Finset (Fin (m + 1))} (hI : I.card < I₀.card) :
    Nat.card D <
      Nat.card (Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) : Subgroup G) := by
  classical
  obtain ⟨τ, hτ⟩ := LinFusion.exists_perm_mapsTo hI.le
  set I' : Finset (Fin (m + 1)) := I₀.image τ.symm with hI'
  have hII' : I ⊆ I' := fun i hi => Finset.mem_image.mpr ⟨τ i, hτ i hi, by simp⟩
  have hcardI' : I'.card = I₀.card := Finset.card_image_of_injective _ (Equiv.injective _)
  have hτI' : ∀ i ∈ I', τ i ∈ I₀ := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    simpa using ha
  obtain ⟨k, hkI', hkI⟩ := Finset.exists_mem_notMem_of_card_lt_card (hcardI'.symm ▸ hI)
  obtain ⟨j, hjI'⟩ : ∃ j, j ∉ I' := by
    by_contra hcon
    apply hI₀u
    refine Finset.eq_univ_of_forall fun a => ?_
    have ha : τ.symm a ∈ I' := by_contra fun ha => hcon ⟨_, ha⟩
    simpa using hτI' (τ.symm a) ha
  have hkj : k ≠ j := fun h => hjI' (h ▸ hkI')
  obtain ⟨k₂, hk₂I', hk₂k⟩ : ∃ k₂ ∈ I', k₂ ≠ k := by
    by_contra hcon
    have hsub : I' ⊆ {k} := fun a ha =>
      Finset.mem_singleton.mpr (by_contra fun hne => hcon ⟨a, ha, hne⟩)
    have h := Finset.card_le_card hsub
    rw [Finset.card_singleton, hcardI'] at h
    omega
  set w := ψ (uFramePerm hQ τ⁻¹) with hw
  have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_le_abelian hBT (fun g hg h hh => uFrameTorus_comm hC hg hh) hexp hSC
      (uFramePerm_mem_normalizer hQ τ⁻¹)
  have hconjD : ∀ d ∈ D, w⁻¹ * d * w ∈ Bs ∧ ∀ I'' : Finset (Fin (m + 1)),
      (∀ i ∈ I'', τ i ∈ I₀) →
        w⁻¹ * d * w ∈ Subgroup.centralizer (uFrameBlock ψ Q I'' : Set G) := by
    intro d hd
    rw [← hD] at hd
    obtain ⟨hdB, hdC⟩ := hd
    obtain ⟨e, he⟩ := hBT hdB
    refine ⟨?_, fun I'' hI'' => ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) d).mp hdB
      rwa [inv_inv] at h
    · have h := conj_mem_suInducedPairs he (uFramePerm hQ τ⁻¹)
      rw [uFramePerm_conj] at h
      refine mem_centralizer_uFrameBlock h fun a ha b hb => ?_
      simp only [inv_inv]
      exact eq_of_mem_centralizer_uFrameBlock hker hQ he hdC (hI'' a ha) (hI'' b hb)
  set K := D.map (MulAut.conj w⁻¹).toMonoidHom with hK
  have hKle : K ≤ Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    have h := hconjD d hd
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact ⟨h.1, h.2 I hτ⟩
  obtain ⟨z, -, hz⟩ := exists_mem_suInducedPairs_mulSingle ψ hQ k j hζσ
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹ with he
  have he_k : e k = ζ := by simp [he, Pi.mulSingle_eq_of_ne hkj]
  have he_other : ∀ a, a ≠ k → a ≠ j → e a = 1 := by
    intro a hak haj
    simp [he, Pi.mulSingle_eq_of_ne hak, Pi.mulSingle_eq_of_ne haj]
  have hzT : z ∈ uFrameTorus ψ Q := ⟨e, hz⟩
  have hzp : z ^ p = 1 := by
    have h := (suInducedPairs ψ).pow_mem hz p
    have hep : e ^ p = 1 := by
      rw [he, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hζp, inv_pow, hζp, inv_one,
        Pi.mulSingle_one, Pi.mulSingle_one, mul_one]
    rw [Prod.pow_mk, ← LinFusion.ggFrameDiag_pow, hep, LinFusion.ggFrameDiag_one] at h
    have h2 := mem_centralizer_of_mem_suInducedPairs_one h
    rwa [hC, Subgroup.mem_bot] at h2
  have hzB : z ∈ Bs := hSC z (by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact uFrameTorus_comm hC (hBT hb) hzT) hzp
  have hzC : z ∈ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) := by
    refine mem_centralizer_uFrameBlock hz fun a ha b hb => ?_
    rw [he_other a (fun h => hkI (h ▸ ha)) (fun h => hjI' (h ▸ hII' ha)),
      he_other b (fun h => hkI (h ▸ hb)) (fun h => hjI' (h ▸ hII' hb))]
  have hzK : z ∉ K := by
    rintro ⟨d, hd, hdz⟩
    have h := (hconjD d hd).2 I' hτI'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hdz
    rw [hdz] at h
    have h2 := eq_of_mem_centralizer_uFrameBlock hker hQ hz h hkI' hk₂I'
    rw [he_k, he_other k₂ hk₂k (fun h => hjI' (h ▸ hk₂I'))] at h2
    exact hζ1 h2
  have hlt : K < Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) :=
    lt_of_le_of_ne hKle fun h => hzK (h ▸ ⟨hzB, hzC⟩)
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective
  rw [← hcardK]
  exact Subgroup.card_lt_of_lt hlt

theorem exists_uFrame_conj_mem {ψ : SU σ (m + 1) →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) {p : ℕ} {Bs : Subgroup G} (hBT : Bs ≤ uFrameTorus ψ Q)
    (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ I : Finset (Fin (m + 1))} (hcard : I₀.card ≤ I.card) {b : G} (hbB : b ∈ Bs)
    {d : Fin (m + 1) → Fˣ} (hb : (b, LinFusion.ggFrameDiag Q d) ∈ suInducedPairs ψ)
    (hdI : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ψ.range ∧ w⁻¹ * b * w ∈ Bs ∧
      w⁻¹ * b * w ∈ Subgroup.centralizer (uFrameBlock ψ Q I₀ : Set G) := by
  obtain ⟨τ, hτ⟩ := LinFusion.exists_perm_mapsTo hcard
  set w := ψ (uFramePerm hQ τ⁻¹) with hw
  have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_le_abelian hBT (fun g hg h hh => uFrameTorus_comm hC hg hh) hexp hSC
      (uFramePerm_mem_normalizer hQ τ⁻¹)
  refine ⟨w, hwN, ⟨_, rfl⟩, ?_, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) b).mp hbB
    rwa [inv_inv] at h
  · have h := conj_mem_suInducedPairs hb (uFramePerm hQ τ⁻¹)
    rw [uFramePerm_conj] at h
    refine mem_centralizer_uFrameBlock h fun i hi j hj => ?_
    simp only [inv_inv]
    exact hdI _ (hτ i hi) _ (hτ j hj)

theorem exists_conj_mem_of_uFrameEq [Finite G] {ψ : SU σ (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) {p : ℕ} {Bs D : Subgroup G} (hpp : p.Prime)
    (hζ : ∃ ζ : Fˣ, ζ ≠ 1 ∧ ζ ^ p = 1 ∧ σ (ζ : F) * ζ = 1)
    (hBT : Bs ≤ uFrameTorus ψ Q) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ : Finset (Fin (m + 1))}
    (hD : Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I₀ : Set G) = D)
    (hDcard : Nat.card D = p ^ 2) {b : G} (hbB : b ∈ Bs) {d : Fin (m + 1) → Fˣ}
    (hb : (b, LinFusion.ggFrameDiag Q d) ∈ suInducedPairs ψ) {I : Finset (Fin (m + 1))}
    (hdI : ∀ i ∈ I, ∀ j ∈ I, d i = d j)
    (hcardI : Nat.card (Bs ⊓ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ψ.range ∧ w⁻¹ * b * w ∈ D := by
  by_cases hI₀ : I₀.card ≤ 1
  · refine ⟨1, one_mem _, one_mem _, ?_⟩
    rw [inv_one, one_mul, mul_one, ← hD]
    refine Subgroup.mem_inf.mpr ⟨hbB, ?_⟩
    rw [uFrameBlock_eq_bot_of_card_le_one ψ Q hI₀, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
  have hI₀2 : 2 ≤ I₀.card := by omega
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hpp.one_lt
  have hI₀u : I₀ ≠ Finset.univ := by
    rintro rfl
    rw [uFrameBlock_univ, hC] at hD
    have hDbot : D = ⊥ := by rw [← hD, inf_bot_eq]
    rw [hDbot, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨ζ, hζ1, hζp, hζσ⟩ := hζ
  have hcard : I₀.card ≤ I.card := by
    by_contra hlt
    have h := card_lt_card_centralizer_uFrameBlock hker hC hQ hBT hexp hSC hD hζ1 hζp hζσ hI₀2
      hI₀u (lt_of_not_ge hlt)
    omega
  obtain ⟨w, hwN, hwR, hwB, hwC⟩ := exists_uFrame_conj_mem hC hQ hBT hexp hSC hcard hbB hb hdI
  exact ⟨w, hwN, hwR, hD ▸ Subgroup.mem_inf.mpr ⟨hwB, hwC⟩⟩

end UFusion

end CFSG.StandardType
