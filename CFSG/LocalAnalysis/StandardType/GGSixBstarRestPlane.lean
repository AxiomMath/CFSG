module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace RestSL

open SLNS

variable {F : Type} [Field F] {n e s r : ℕ}

@[expose] def planeExp {p : ℕ} (i₀ i₁ : Fin s) (a : ZMod p × ZMod p) : Fin s → ℕ :=
  fun i => if i = i₀ then a.1.val else if i = i₁ then a.2.val else 0

theorem planeExp_zero {p : ℕ} (i₀ i₁ : Fin s) : planeExp (p := p) i₀ i₁ 0 = 0 := by
  funext i
  simp [planeExp]

theorem planeExp_add_mod {p : ℕ} [NeZero p] (i₀ i₁ : Fin s) (a b : ZMod p × ZMod p) (i : Fin s) :
    planeExp i₀ i₁ (a + b) i % p = (planeExp i₀ i₁ a + planeExp i₀ i₁ b) i % p := by
  simp only [planeExp, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp [ZMod.val_add]

theorem planeExp_lt {p : ℕ} [NeZero p] (i₀ i₁ : Fin s) (a : ZMod p × ZMod p) (i : Fin s) :
    planeExp i₀ i₁ a i < p := by
  simp only [planeExp]
  split_ifs
  · exact ZMod.val_lt _
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero p

theorem planeExp_eq_zero_of_ne {p : ℕ} {i₀ i₁ i : Fin s} (h0 : i ≠ i₀) (h1 : i ≠ i₁)
    (a : ZMod p × ZMod p) : planeExp i₀ i₁ a i = 0 := by
  simp [planeExp, h0, h1]

theorem planeExp_left {p : ℕ} (i₀ i₁ : Fin s) (a : ZMod p × ZMod p) :
    planeExp i₀ i₁ a i₀ = a.1.val := by
  simp [planeExp]

theorem planeExp_right {p : ℕ} {i₀ i₁ : Fin s} (h : i₀ ≠ i₁) (a : ZMod p × ZMod p) :
    planeExp i₀ i₁ a i₁ = a.2.val := by
  simp [planeExp, h.symm]

variable (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)

@[expose] noncomputable def planeHom {p : ℕ} [NeZero p] (hCp : C ^ p = 1) (i₀ i₁ : Fin s) :
    Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin n) F where
  toFun a := nsSL ε hC (planeExp i₀ i₁ (Multiplicative.toAdd a))
  map_one' := by
    rw [toAdd_one, planeExp_zero, nsSL_zero]
  map_mul' a b := by
    rw [toAdd_mul, nsSL_mul]
    exact nsSL_congr ε hC hCp (planeExp_add_mod i₀ i₁ _ _)

theorem planeHom_apply {p : ℕ} [NeZero p] (hCp : C ^ p = 1) (i₀ i₁ : Fin s)
    (a : Multiplicative (ZMod p × ZMod p)) :
    planeHom ε hC hCp i₀ i₁ a = nsSL ε hC (planeExp i₀ i₁ (Multiplicative.toAdd a)) := rfl

section Ctx

variable {ε} {hC} {G : Type} [Group G] [Finite F] {p : ℕ} {B Bs G₀ : Subgroup G}
  {ψ : SpecialLinearGroup (Fin n) F →* G} {A₀ : SpecialLinearGroup (Fin n) F}

theorem NSCtx.exists_rootPlane (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (hs : 4 ≤ s) (he : 2 ≤ e) :
    ∃ (E : Subgroup G) (x y : Fin n) (hxy : x ≠ y),
      E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (∀ b ∈ E, ∀ t : F, SLRep.ggFrame ψ A₀ (SpecialLinearGroup.transvection hxy t) * b =
        b * SLRep.ggFrame ψ A₀ (SpecialLinearGroup.transvection hxy t)) ∧
      ∀ b ∈ E, b ≠ 1 → ∃ L₁ : Subgroup G,
        IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hc.prime.ne_zero⟩
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set i₀ : Fin s := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin s := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin s := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h20 : i₂ ≠ i₀ := by simp [hi₀, hi₂, Fin.ext_iff]
  have h21 : i₂ ≠ i₁ := by simp [hi₁, hi₂, Fin.ext_iff]
  set ρ := planeHom ε hC hc.cp i₀ i₁ with hρ
  set x : Fin n := ε.symm (Sum.inl (⟨0, by omega⟩, i₂)) with hx
  set y : Fin n := ε.symm (Sum.inl (⟨1, by omega⟩, i₂)) with hy
  have hxy : x ≠ y := by
    intro h
    have h3 := congrArg (fun z : Fin e × Fin s => (z.1 : ℕ))
      (Sum.inl_injective (ε.symm.injective h))
    simp at h3
  set supp : Multiplicative (ZMod p × ZMod p) → Finset (Fin s) :=
    fun a => Finset.univ.filter fun i => planeExp i₀ i₁ (Multiplicative.toAdd a) i ≠ 0 with hsupp
  have hk0 : ∀ a i, i ∉ supp a → planeExp i₀ i₁ (Multiplicative.toAdd a) i = 0 := by
    intro a i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hkp : ∀ a, ∀ i ∈ supp a, ¬ p ∣ planeExp i₀ i₁ (Multiplicative.toAdd a) i := by
    intro a i hi hdvd
    exact (Finset.mem_filter.mp hi).2 (Nat.eq_zero_of_dvd_of_lt hdvd (planeExp_lt i₀ i₁ _ i))
  have hsub : ∀ a, supp a ⊆ {i₀, i₁} := by
    intro a i hi
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact (Finset.mem_filter.mp hi).2 (planeExp_eq_zero_of_ne h.1 h.2 _)
  have hi₂s : ∀ a, i₂ ∉ supp a := fun a h => by
    have := hsub a h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact h20 h'
    · exact h21 h'
  have ho : 1 ≤ Nat.card (Matrix (Fin e) (Fin e) F)ˣ := Nat.card_pos
  have hko : ∀ a, ∀ i ∈ supp a, (C ^ planeExp i₀ i₁ (Multiplicative.toAdd a) i - 1) ^
      Nat.card (Matrix (Fin e) (Fin e) F)ˣ = 1 :=
    fun a i hi => RestSL.NSCtx.pow_card_units hc (hkp a i hi)
  have hxS : ∀ a, x ∈ fixS ε (supp a) := fun a => by
    rw [mem_fixS, hx, Equiv.apply_symm_apply]
    exact hi₂s a
  have hyS : ∀ a, y ∈ fixS ε (supp a) := fun a => by
    rw [mem_fixS, hy, Equiv.apply_symm_apply]
    exact hi₂s a
  have hn : n = e * s + r := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have hpair : 3 ≤ (fixS ε {i₀, i₁}).card := by
    rw [card_fixS_pair (ε := ε) h01]
    have : e * 4 ≤ e * s := Nat.mul_le_mul_left e hs
    omega
  have hfixmono : ∀ a, fixS ε {i₀, i₁} ⊆ fixS ε (supp a) := by
    intro a z hz
    rw [mem_fixS] at hz ⊢
    intro hin
    apply hz
    rcases hεz : ε z with ⟨b, j⟩ | u
    · rw [hεz] at hin
      exact hsub a hin
    · rw [hεz] at hin
      exact (hin : False).elim
  have hinj : Function.Injective (φ.comp ρ) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : φ (nsSL ε hC (planeExp i₀ i₁ (Multiplicative.toAdd a))) = 1 := ha
    have hdvd := fun j => RestSL.NSCtx.dvd_of_frame_eq_one hc (by omega) (j₀ := i₂)
      (planeExp_eq_zero_of_ne h20 h21 _) h1 j
    have hv0 : (Multiplicative.toAdd a).1.val = 0 := by
      have := hdvd i₀
      rw [planeExp_left] at this
      exact Nat.eq_zero_of_dvd_of_lt this (ZMod.val_lt _)
    have hv1 : (Multiplicative.toAdd a).2.val = 0 := by
      have := hdvd i₁
      rw [planeExp_right h01] at this
      exact Nat.eq_zero_of_dvd_of_lt this (ZMod.val_lt _)
    have h0 : Multiplicative.toAdd a = 0 :=
      Prod.ext ((ZMod.val_eq_zero _).mp hv0) ((ZMod.val_eq_zero _).mp hv1)
    rw [← ofAdd_toAdd a, h0, ofAdd_zero]
  refine ⟨(φ.comp ρ).range, x, y, hxy, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hc.mem_bstar _
  · refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := u
      obtain ⟨_, b, rfl⟩ := v
      apply Subtype.ext
      change φ (ρ a) * φ (ρ b) = φ (ρ b) * φ (ρ a)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
    · rintro _ ⟨a, rfl⟩
      change φ (ρ a) ^ p = 1
      rw [← map_pow, hρ, planeHom_apply, nsSL_pow_p ε hC hc.cp, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    change Nat.card (ZMod p × ZMod p) = p ^ 2
    rw [Nat.card_prod, Nat.card_zmod, sq]
  · rintro _ ⟨a, rfl⟩ t
    have hT : SpecialLinearGroup.transvection hxy t ∈ coordBlockSL F (fixS ε (supp a)) :=
      SLRep.transvection_mem_coordBlockSL (hxS a) (hyS a) hxy t
    have hcomm := RestSL.coordBlockSL_le_centralizer ε hC _ (supp a) (hk0 a) ho (hko a) hT
    rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
    change φ (SpecialLinearGroup.transvection hxy t) * φ (ρ a) =
      φ (ρ a) * φ (SpecialLinearGroup.transvection hxy t)
    rw [← map_mul, ← map_mul, hρ, planeHom_apply, hcomm]
  · rintro _ ⟨a, rfl⟩ hb1
    have hne : (supp a).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      apply hb1
      have hk : planeExp i₀ i₁ (Multiplicative.toAdd a) = 0 :=
        funext fun i => hk0 a i (by rw [hemp]; simp)
      change φ (ρ a) = 1
      rw [hρ, planeHom_apply, hk, nsSL_zero, map_one]
    obtain ⟨j, hj⟩ := hne
    have hj' : ε.symm (Sum.inl (⟨0, by omega⟩, j)) ∉ fixS ε (supp a) := by
      rw [mem_fixS, Equiv.apply_symm_apply, not_not]
      exact hj
    have hS3 : 3 ≤ (fixS ε (supp a)).card := hpair.trans (Finset.card_le_card (hfixmono a))
    refine ⟨(coordBlockSL F (fixS ε (supp a))).map φ, ?_, ?_⟩
    · exact RestSL.NSCtx.isComponentOf_gen hc _ (supp a) (hk0 a) (hkp a) hS3 hj'
    · refine (hc.card_centralizer_le (supp a) (by omega) (by omega)).trans ?_
      exact Nat.pow_le_pow_right hc.prime.pos
        ((Finset.card_le_card (hsub a)).trans Finset.card_le_two)

end Ctx

end RestSL

section Inputs

theorem ggRootPlaneInputOn_PSLNonsplit_of_frame (hF : GGSLNonsplitFrameInput) :
    GGRootPlaneInputOn GGPSLNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, hns⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  obtain ⟨e, s, r', C, hC, ε, A₀, hCp, hcunit, hframe⟩ := hF G p B Bs x L D J m f ψ hctx s1 hns
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnsplit : ∀ c : GaloisField 2 f, c ^ p = 1 → c = 1 := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hc
      exact zero_ne_one hc
    set u := Units.mk0 c hc0 with hu
    have hup : u ^ p = 1 := Units.ext (by simp [hu, hc])
    have h1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
    have h2' : orderOf u ∣ 2 ^ f - 1 := by
      have := orderOf_dvd_natCard u
      rwa [Nat.card_units, hcardF] at this
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · have := orderOf_eq_one_iff.mp h
      have := congrArg Units.val this
      simpa [hu] using this
    · exact absurd (h ▸ h2') hns
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hc : SLNS.NSCtx ε hC p B Bs (ggG0 p B x L D J) ψ A₀ :=
    ⟨hctx.2.1, hker, hrange, s1.1, hp, hnsplit, hCp, hcunit, hframe⟩
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hs4 : 4 ≤ s :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hc.card_bstar_le)
  have he1 : 1 ≤ e := by
    by_contra he0
    have he0' : e = 0 := by omega
    have hsub : Bs ≤ ⊥ := fun b hb => by
      obtain ⟨k, rfl⟩ := hframe b hb
      rw [SLNS.nsSL_eq_one_of_e_zero ε hC he0' k, map_one]
      exact Subgroup.one_mem _
    have h1 : Nat.card Bs ≤ 1 := by
      have := Subgroup.card_le_of_le hsub
      rwa [Subgroup.card_bot] at this
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hp.one_lt
    omega
  have he2 : 2 ≤ e := by
    by_contra he
    obtain rfl : e = 1 := by omega
    have hu := hcunit 1 (Nat.Prime.not_dvd_one hp) (C 0 0)
    have h0 : C ^ 1 - C 0 0 • (1 : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) = 0 := by
      ext a b
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simp
    rw [h0] at hu
    exact not_isUnit_zero hu
  obtain ⟨E, x₁, y₁, hxy, hEBs, hEel, hEcard, hcomm, hcomp⟩ :=
    RestSL.NSCtx.exists_rootPlane hc hs4 he2
  refine ⟨E, InnerDiagA.typeARoot x₁ y₁, A₀, ψ (A₀ * SpecialLinearGroup.transvection hxy 1 * A₀⁻¹),
    hEBs, hEel, hEcard, ⟨InnerDiagA.typeARoot_mem_roots _ hxy, fun h => ?_⟩, ?_, ?_,
    RootPlaneA.orderOf_psi_conj_transvection hker hxy A₀, fun b hb hb1 => Or.inr (hcomp b hb hb1)⟩
  · rcases h with h | h | h <;> cases h
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    change z ∈ SpecialLinear.rootGroup m (GaloisField 2 f) (InnerDiagA.typeARoot x₁ y₁) at hz
    rw [InnerDiagA.rootGroup_typeARoot hxy] at hz
    obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hxy z).mp hz
    exact hcomm b hb t
  · refine ⟨_, ⟨SpecialLinearGroup.transvection hxy 1, ?_, rfl⟩, rfl⟩
    change _ ∈ SpecialLinear.rootGroup m (GaloisField 2 f) (InnerDiagA.typeARoot x₁ y₁)
    rw [InnerDiagA.rootGroup_typeARoot hxy]
    exact SpecialLinear.transvection_mem_rootSubgroup hxy 1

theorem ggRootPlaneInputOn_notPSLSplit_of_frame_rest (hF : GGSLNonsplitFrameInput)
    (hPSU : GGRootPlaneAt .PSU) (hPSp : GGRootPlaneAt .PSp) (hPlus : GGRootPlaneAt .POmegaPlus)
    (hMinus : GGRootPlaneAt .POmegaMinus) (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p :=
  ggRootPlaneInputOn_notPSLSplit_of_remaining (ggRootPlaneInputOn_PSLNonsplit_of_frame hF) hPSU
    hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggRootPlaneInput_of_frame_rest (hF : GGSLNonsplitFrameInput)
    (hPSU : GGRootPlaneAt .PSU) (hPSp : GGRootPlaneAt .PSp) (hPlus : GGRootPlaneAt .POmegaPlus)
    (hMinus : GGRootPlaneAt .POmegaMinus) (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneInput :=
  ggRootPlaneInput_of_notPSLSplit
    (ggRootPlaneInputOn_notPSLSplit_of_frame_rest hF hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6)

end Inputs

end CFSG.StandardType
