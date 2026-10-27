module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot Matrix

namespace LinFusion

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem conjSL_inv_conjSL (A : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A⁻¹ (InnerDiagA.conjSL A u) = u := by
  rw [← conjSL_mul, inv_mul_cancel, conjSL_one]

theorem ker_comp_conjSL_le_center {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) (A : GL (Fin (m + 1)) F) :
    (ψ.comp (InnerDiagA.conjSL A)).ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
  intro v hv
  have h := hker hv
  rw [Subgroup.mem_center_iff] at h ⊢
  intro u
  have h1 := h (InnerDiagA.conjSL A u)
  rw [← map_mul, ← map_mul] at h1
  have h2 := congrArg (InnerDiagA.conjSL A⁻¹) h1
  rwa [conjSL_inv_conjSL, conjSL_inv_conjSL] at h2

theorem eq_of_mem_centralizer_ggFrameBlock {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {P : GL (Fin (m + 1)) F} {I : Finset (Fin (m + 1))} {g : G} {e : Fin (m + 1) → Fˣ}
    (hg : (g, ggFrameDiag P e) ∈ ggInducedPairs ψ)
    (hgc : g ∈ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G)) {i j : Fin (m + 1)}
    (hi : i ∈ I) (hj : j ∈ I) : e i = e j := by
  by_cases hij : i = j
  · rw [hij]
  set ψ' := ψ.comp (InnerDiagA.conjSL P⁻¹) with hψ'
  set x := SpecialLinearGroup.transvection hij (1 : F) with hx
  have hxJ : ψ' x ∈ ggFrameBlock F ψ P I :=
    Subgroup.mem_map_of_mem _ (transvection_mem_blockSpecialLinear hij hi hj 1)
  have hcomm := Subgroup.mem_centralizer_iff.mp hgc _ hxJ
  have h1 := mem_ggInducedPairs.mp hg (InnerDiagA.conjSL P⁻¹ x)
  rw [← conjSL_mul, ggFrameDiag, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, conjSL_mul,
    hx, InnerDiagA.conjSL_diagGL_transvection] at h1
  have h2 : ψ' (SpecialLinearGroup.transvection hij 1) =
      ψ' (SpecialLinearGroup.transvection hij ((e i : F) * 1 * ((e j)⁻¹ : Fˣ))) := by
    simp only [hψ', hx, MonoidHom.comp_apply] at hcomm ⊢
    rw [← h1, ← mul_assoc, ← hcomm, mul_inv_cancel_right]
  have h3 := InnerDiagA.eq_of_map_transvection_eq ψ' (ker_comp_conjSL_le_center hker P⁻¹) hij h2
  rw [mul_one, ← Units.val_mul, eq_comm, Units.val_eq_one, mul_inv_eq_one] at h3
  exact h3

theorem ggFrameDiag_one (P : GL (Fin (m + 1)) F) : ggFrameDiag P 1 = 1 := by
  rw [ggFrameDiag, diagGL_one, mul_one, inv_mul_cancel]

theorem ggFrameDiag_pow (P : GL (Fin (m + 1)) F) (d : Fin (m + 1) → Fˣ) (n : ℕ) :
    ggFrameDiag P (d ^ n) = ggFrameDiag P d ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ggFrameDiag_one]
  | succ n ih => rw [pow_succ, pow_succ, ggFrameDiag_mul, ih]

theorem exists_mem_ggInducedPairs_mulSingle (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) (k j : Fin (m + 1)) (ζ : Fˣ) :
    ∃ z ∈ ψ.range,
      (z, ggFrameDiag P (Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹)) ∈ ggInducedPairs ψ := by
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹ with he
  have hprod : ∏ x, ((e x : Fˣ) : F) = 1 := by
    rw [← Units.coe_prod]
    simp only [he, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true, mul_inv_cancel, Units.val_one]
  have hdet : ((ggFrameDiag P e : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
    have hP : ((P⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det *
        (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    rw [ggFrameDiag, Units.val_mul, Units.val_mul, det_mul, det_mul, InnerDiagA.coe_diagGL,
      det_diagonal, hprod, mul_one, hP]
  let s : SpecialLinearGroup (Fin (m + 1)) F := ⟨_, hdet⟩
  have hs : SpecialLinearGroup.toGL s = ggFrameDiag P e := Units.ext rfl
  exact ⟨ψ s, ⟨s, rfl⟩, hs ▸ mem_ggInducedPairs_toGL ψ s⟩

theorem card_lt_card_centralizer_ggFrameBlock [Finite G] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {P : GL (Fin (m + 1)) F} {p : ℕ}
    {Bs D : Subgroup G} (hBT : Bs ≤ ggFrameTorus F ψ P) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ : Finset (Fin (m + 1))}
    (hD : Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I₀ : Set G) = D)
    {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hI₀2 : 2 ≤ I₀.card) (hI₀u : I₀ ≠ Finset.univ)
    {I : Finset (Fin (m + 1))} (hI : I.card < I₀.card) :
    Nat.card D <
      Nat.card (Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) : Subgroup G) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_mapsTo hI.le
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
  set w := ψ (ggFramePermSL F P τ⁻¹) with hw
  have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_le_abelian hBT (fun g hg h hh => ggFrameTorus_comm hC hg hh) hexp hSC
      (ggFramePerm_mem_normalizer τ⁻¹)
  have hconjD : ∀ d ∈ D, w⁻¹ * d * w ∈ Bs ∧ ∀ I'' : Finset (Fin (m + 1)),
      (∀ i ∈ I'', τ i ∈ I₀) →
        w⁻¹ * d * w ∈ Subgroup.centralizer (ggFrameBlock F ψ P I'' : Set G) := by
    intro d hd
    rw [← hD] at hd
    obtain ⟨hdB, hdC⟩ := hd
    obtain ⟨e, he⟩ := hBT hdB
    refine ⟨?_, fun I'' hI'' => ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) d).mp hdB
      rwa [inv_inv] at h
    · have h := (ggInducedPairs ψ).mul_mem ((ggInducedPairs ψ).mul_mem
        ((ggInducedPairs ψ).inv_mem (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P τ⁻¹))) he)
        (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P τ⁻¹))
      rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, toGL_ggFramePermSL_conj] at h
      refine mem_centralizer_ggFrameBlock h fun a ha b hb => ?_
      simp only [inv_inv]
      exact eq_of_mem_centralizer_ggFrameBlock hker he hdC (hI'' a ha) (hI'' b hb)
  set K := D.map (MulAut.conj w⁻¹).toMonoidHom with hK
  have hKle : K ≤ Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    have h := hconjD d hd
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact ⟨h.1, h.2 I hτ⟩
  obtain ⟨z, -, hz⟩ := exists_mem_ggInducedPairs_mulSingle ψ P k j ζ
  set e : Fin (m + 1) → Fˣ := Pi.mulSingle k ζ * Pi.mulSingle j ζ⁻¹ with he
  have he_k : e k = ζ := by simp [he, Pi.mulSingle_eq_of_ne hkj]
  have he_other : ∀ a, a ≠ k → a ≠ j → e a = 1 := by
    intro a hak haj
    simp [he, Pi.mulSingle_eq_of_ne hak, Pi.mulSingle_eq_of_ne haj]
  have hzT : z ∈ ggFrameTorus F ψ P := ⟨e, hz⟩
  have hzp : z ^ p = 1 := by
    have h := (ggInducedPairs ψ).pow_mem hz p
    have hpow : ((z, ggFrameDiag P e) ^ p : G × GL (Fin (m + 1)) F) =
        (z ^ p, ggFrameDiag P e ^ p) :=
      Prod.ext (map_pow (MonoidHom.fst G (GL (Fin (m + 1)) F)) _ p)
        (map_pow (MonoidHom.snd G (GL (Fin (m + 1)) F)) _ p)
    have hep : e ^ p = 1 := by
      rw [he, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hζp, inv_pow, hζp, inv_one,
        Pi.mulSingle_one, Pi.mulSingle_one, mul_one]
    rw [hpow, ← ggFrameDiag_pow, hep, ggFrameDiag_one] at h
    have h2 := mem_centralizer_of_mem_ggInducedPairs_one h
    rwa [hC, Subgroup.mem_bot] at h2
  have hzB : z ∈ Bs := hSC z (by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ggFrameTorus_comm hC (hBT hb) hzT) hzp
  have hzC : z ∈ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) := by
    refine mem_centralizer_ggFrameBlock hz fun a ha b hb => ?_
    rw [he_other a (fun h => hkI (h ▸ ha)) (fun h => hjI' (h ▸ hII' ha)),
      he_other b (fun h => hkI (h ▸ hb)) (fun h => hjI' (h ▸ hII' hb))]
  have hzK : z ∉ K := by
    rintro ⟨d, hd, hdz⟩
    have h := (hconjD d hd).2 I' hτI'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hdz
    rw [hdz] at h
    have h2 := eq_of_mem_centralizer_ggFrameBlock hker hz h hkI' hk₂I'
    rw [he_k, he_other k₂ hk₂k (fun h => hjI' (h ▸ hk₂I'))] at h2
    exact hζ1 h2
  have hlt : K < Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) :=
    lt_of_le_of_ne hKle fun h => hzK (h ▸ ⟨hzB, hzC⟩)
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective
  rw [← hcardK]
  exact Subgroup.card_lt_of_lt hlt

theorem blockSpecialLinear_eq_bot_of_card_le_one {I : Finset (Fin (m + 1))} (hI : I.card ≤ 1) :
    blockSpecialLinear (K := F) I = ⊥ := by
  have : Subsingleton (I : Type) := Finset.card_le_one_iff_subsingleton_coe.mp hI
  rw [← range_blockEmbed, eq_bot_iff]
  rintro _ ⟨A, rfl⟩
  have hA : A = 1 := by
    ext a b
    rw [Subsingleton.elim b a]
    have h := A.prop
    rw [det_eq_elem_of_subsingleton _ a] at h
    rw [h]
    simp
  rw [hA, map_one]
  exact one_mem _

theorem ggFrameBlock_univ (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G) (P : GL (Fin (m + 1)) F) :
    ggFrameBlock F ψ P Finset.univ = ψ.range := by
  rw [ggFrameBlock, blockSpecialLinear_univ, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (fun u => ⟨InnerDiagA.conjSL P u, conjSL_inv_conjSL P u⟩),
    ← MonoidHom.range_eq_map]

theorem exists_conj_mem_of_frameEq [Finite G] [Finite F] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {P : GL (Fin (m + 1)) F} {p : ℕ}
    {Bs D : Subgroup G} (hpp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    (hBT : Bs ≤ ggFrameTorus F ψ P) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ : Finset (Fin (m + 1))}
    (hD : Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I₀ : Set G) = D)
    (hDcard : Nat.card D = p ^ 2) {b : G} (hbB : b ∈ Bs) {d : Fin (m + 1) → Fˣ}
    (hb : (b, ggFrameDiag P d) ∈ ggInducedPairs ψ) {I : Finset (Fin (m + 1))}
    (hdI : ∀ i ∈ I, ∀ j ∈ I, d i = d j)
    (hcardI : Nat.card (Bs ⊓ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) :
      Subgroup G) ≤ p ^ 2) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ψ.range ∧ w⁻¹ * b * w ∈ D := by
  by_cases hI₀ : I₀.card ≤ 1
  · refine ⟨1, one_mem _, one_mem _, ?_⟩
    rw [inv_one, one_mul, mul_one, ← hD]
    have hbot : ggFrameBlock F ψ P I₀ = ⊥ := by
      rw [ggFrameBlock, blockSpecialLinear_eq_bot_of_card_le_one hI₀, Subgroup.map_bot]
    refine Subgroup.mem_inf.mpr ⟨hbB, ?_⟩
    rw [hbot, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
  have hI₀2 : 2 ≤ I₀.card := by omega
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hpp.one_lt
  have hI₀u : I₀ ≠ Finset.univ := by
    rintro rfl
    rw [ggFrameBlock_univ, hC] at hD
    have hDbot : D = ⊥ := by rw [← hD, inf_bot_eq]
    rw [hDbot, Subgroup.card_bot] at hDcard
    omega
  have := Fact.mk hpp
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [Nat.card_units]; exact hpF)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hpp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hcard : I₀.card ≤ I.card := by
    by_contra hlt
    have h := card_lt_card_centralizer_ggFrameBlock hker hC hBT hexp hSC hD hζ1 hζp hI₀2 hI₀u
      (lt_of_not_ge hlt)
    omega
  obtain ⟨w, hwN, hwR, hwB, hwC⟩ := exists_frame_conj_mem hC hBT hexp hSC hcard hbB hb hdI
  exact ⟨w, hwN, hwR, hD ▸ Subgroup.mem_inf.mpr ⟨hwB, hwC⟩⟩

end LinFusion

section Inputs

@[expose] def GGLinearFrameEqInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
    GGSixStepOne p B Bs x L D J → p ∣ 2 ^ f - 1 →
      ∃ (P : GL (Fin (m + 1)) (GaloisField 2 f)) (I₀ : Finset (Fin (m + 1))),
        Bs ≤ LinFusion.ggFrameTorus (GaloisField 2 f) ψ P ∧
        Bs ⊓ Subgroup.centralizer (LinFusion.ggFrameBlock (GaloisField 2 f) ψ P I₀ : Set G) = D

theorem ggStepTwoLinearFusion_PSL_of_frameEq (hcomp : GGLinearSemisimpleComponentInput)
    (hL : GGLinearFrameEqInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p ∣ 2 ^ f - 1) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ggG0 p B x L D J ∧ w⁻¹ * b * w ∈ D := by
  obtain ⟨P, I₀, hBT, hD⟩ := hL G p B Bs x L D J m f ψ hctx s1 hp
  have hpp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨-, hBel, -, hSC⟩, ⟨⟨-, -, hDcard, -⟩, -⟩, ⟨hadm, -⟩, ⟨hrange, hker⟩, -⟩ := hctx.2
  obtain ⟨-, hf, -⟩ := hadm
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  obtain ⟨hbB, -, hcomp₁, hcard₁⟩ := hpair
  obtain ⟨d, hd⟩ := hBT hbB
  have hcomp₂ : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) := by
    rw [hrange]
    exact hcomp₁
  obtain ⟨I, hLI, hdI⟩ := hcomp G m f ψ hker P d b hd L₁ hcomp₂
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hp
  obtain ⟨w, hwN, hwR, hw⟩ := LinFusion.exists_conj_mem_of_frameEq hker hC hpp hpF hBT
    (fun b hb => hBel.2 b hb) hSC hD hDcard hbB hd hdI (by rw [← hLI]; exact hcard₁)
  exact ⟨w, hwN, hrange ▸ hwR, hw⟩

theorem ggStepTwoLinearFusionInput_of_frameEq (hcomp : GGLinearSemisimpleComponentInput)
    (hL : GGLinearFrameEqInput) (hU : GGStepTwoUnitaryFusionInput) :
    GGStepTwoLinearFusionInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
  rcases hlin with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hwN, -, hw⟩ := ggStepTwoLinearFusion_PSL_of_frameEq hcomp hL hctx s1 hp hpair
    exact ⟨w, hwN, hw⟩
  · exact hU G p B Bs x L D J n f ψ hctx s1 hp b L₁ hpair

end Inputs

end CFSG.StandardType
