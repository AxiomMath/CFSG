module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br

open CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.G11.Harris.L2
open scoped MatrixGroups Matrix

section Transport

variable {F : Type} [Field F] {X₁ X₂ : Type} [AddCommGroup X₁] [Module (ZMod 2) X₁]
  [AddCommGroup X₂] [Module (ZMod 2) X₂]

theorem isNaturalModule_of_equiv {σ₁ : Representation (ZMod 2) SL(2, F) X₁}
    {σ₂ : Representation (ZMod 2) SL(2, F) X₂} (h : IsNaturalModule σ₁) (f : X₂ ≃+ X₁)
    (hf : ∀ g x, f (σ₂ g x) = σ₁ g (f x)) : IsNaturalModule σ₂ := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨f.trans φ, fun g w => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [hf, hφ]

theorem isOrthModule_of_equiv [Fintype F] [CharP F 2] {l : ℕ} {hl : Fintype.card F = 2 ^ (2 * l)}
    {σ₁ : Representation (ZMod 2) SL(2, F) X₁} {σ₂ : Representation (ZMod 2) SL(2, F) X₂}
    (h : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hl σ₁) (f : X₂ ≃+ X₁)
    (hf : ∀ g x, f (σ₂ g x) = σ₁ g (f x)) : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hl σ₂ := by
  obtain ⟨j, β, hβ⟩ := h
  refine ⟨j, f.trans β, fun g w => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [hf, hβ]

end Transport

theorem omega_of_orth {K X : Type} [Group K] [AddCommGroup X] [Module (ZMod 2) X] {F : Type}
    [Field F] [Fintype F] [CharP F 2] {a : ℕ} (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    (φ : K ≃* SL(2, F)) (σ : Representation (ZMod 2) K X) (β : X ≃+ ↥(hermA a F)) (j : ℕ)
    (hβ : ∀ k w, β (σ k w) = hermAct a (sig_sig hF) (fieldAut F j (φ k)) (β w)) :
    ∃ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (Θ : K ≃* ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c)))
        (ψ : X ≃+ (QIdx → GaloisField 2 a)), ∀ k w,
          ψ (σ k w) = ((Θ k : GL QIdx (GaloisField 2 a)) : Matrix QIdx QIdx (GaloisField 2 a)) *ᵥ
            ψ w := by
  set σ' : F →+* F := sig (F := F) a
  have ha0 : a ≠ 0 := by omega
  have hσ : ∀ x, σ' x = x ^ 2 ^ a := sig_apply a
  have hF' : Nat.card F = (2 ^ a) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm, pow_mul]
  obtain ⟨ω, hω⟩ := exists_frob_ne ha hF' hσ
  have hcard : Nat.card (frobFixed σ') = Nat.card (GaloisField 2 a) := by
    rw [card_frobFixed ha hF' hσ, GaloisField.card 2 a ha0]
  have : Fintype (frobFixed σ') := Fintype.ofFinite _
  have : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  obtain ⟨e⟩ : Nonempty (frobFixed σ' ≃+* GaloisField 2 a) :=
    ⟨FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)⟩
  obtain ⟨M, ψ, b, c, hbc, hMinj, hMrange, hψ, -⟩ := exists_omegaRep ha hF' hσ e hω
  refine ⟨b, c, hbc, ?_⟩
  let g₀ : K ≃* SL(2, F) := φ.trans (CFSG.Quasithin.B45L2.fieldAutEquiv j)
  let Θ : K ≃* ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c)) :=
    g₀.trans ((MonoidHom.ofInjective hMinj).trans (MulEquiv.subgroupCongr hMrange))
  refine ⟨Θ, (β.trans (hermToTwisted F a)).trans ψ, fun k w => ?_⟩
  show ψ (hermToTwisted F a (β (σ k w))) =
    (M (g₀ k) : Matrix QIdx QIdx (GaloisField 2 a)) *ᵥ ψ (hermToTwisted F a (β w))
  rw [hβ, hermToTwisted_hermAct, hψ]
  rfl

section Sections

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {L : Subgroup G}

theorem isInvariant_bot : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L ⊥ := fun a _ u hu => by
  rw [(Submodule.mem_bot _).mp hu, map_zero]
  exact Submodule.zero_mem _

@[expose] def restr {A : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A) :
    Representation (ZMod 2) ↥L ↥A :=
  Subrepresentation.toRepresentation
    (⟨A, fun h _ hv => hA h h.2 _ hv⟩ : Subrepresentation (ρ.comp L.subtype))

@[simp] theorem coe_restr_apply {A : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A) (h : ↥L)
    (w : ↥A) : ((restr ρ hA h w : ↥A) : V) = ρ h w := rfl

theorem exists_extend {Y : Type} [AddCommGroup Y] (A : Submodule (ZMod 2) V) (ψ : ↥A ≃+ Y) :
    ∃ Ψ : V →+ Y, (∀ x ∈ (⊥ : Submodule (ZMod 2) V), Ψ x = 0) ∧
      (∀ x ∈ A, Ψ x = 0 → x ∈ (⊥ : Submodule (ZMod 2) V)) ∧ (∀ y : Y, ∃ x ∈ A, Ψ x = y) ∧
      ∀ w : ↥A, Ψ w = ψ w := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl A
  let p : V →ₗ[ZMod 2] ↥A := Submodule.projectionOnto A C hC
  have hp : ∀ w : ↥A, p w = w := Submodule.projectionOnto_apply_left hC
  refine ⟨ψ.toAddMonoidHom.comp p.toAddMonoidHom, fun x hx => ?_, fun x hx h0 => ?_,
    fun y => ⟨(ψ.symm y : V), (ψ.symm y).2, ?_⟩, fun w => ?_⟩
  · rw [(Submodule.mem_bot _).mp hx, map_zero]
  · have h1 : ψ ⟨x, hx⟩ = 0 := by
      have := hp ⟨x, hx⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe] at h0
      rwa [this] at h0
    have h2 : (⟨x, hx⟩ : ↥A) = 0 := ψ.injective (h1.trans (map_zero ψ).symm)
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h2
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      AddEquiv.coe_toAddMonoidHom]
    rw [hp, AddEquiv.apply_symm_apply]
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      AddEquiv.coe_toAddMonoidHom]
    rw [hp]

theorem natL2_of_isNaturalModule {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* SL(2, F)) {A : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A)
    (σ : Representation (ZMod 2) ↥L ↥A) (hσ : ∀ h w, (σ h w : V) = ρ h w)
    (hnat : IsNaturalModule (σ.comp e.symm.toMonoidHom)) : NatL2 ρ L A ⊥ n := by
  obtain ⟨φ, hφ⟩ := hnat
  obtain ⟨Ψ, h0, hker, hsurj, hΨ⟩ := exists_extend A φ
  refine ⟨F, inferInstance, inferInstance, hF, hA, isInvariant_bot ρ, bot_le,
    e.trans (specialLinearGroupEquivStatedSL 2 F), Ψ, h0, hker, hsurj, fun h x hx => ?_⟩
  have h1 : ρ (h : G) x = ((σ h ⟨x, hx⟩ : ↥A) : V) := (hσ h ⟨x, hx⟩).symm
  have h3 : Ψ x = φ ⟨x, hx⟩ := hΨ ⟨x, hx⟩
  rw [h1, hΨ, h3]
  have h2 := hφ (e h) ⟨x, hx⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] at h2
  rw [h2]
  rfl

theorem natOmegaMinus4_of_isOrthModule {F : Type} [Field F] [Fintype F] [CharP F 2] {s : ℕ}
    (hs1 : 1 ≤ s) (hs : Fintype.card F = 2 ^ (2 * s)) (e : ↥L ≃* SL(2, F))
    {A : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A) (σ : Representation (ZMod 2) ↥L ↥A)
    (hσ : ∀ h w, (σ h w : V) = ρ h w)
    (horth : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs (σ.comp e.symm.toMonoidHom)) :
    NatOmegaMinus4 ρ L A ⊥ s := by
  obtain ⟨j, β, hβ⟩ := horth
  have hβ' : ∀ k w, β (σ k w) = hermAct s (sig_sig hs) (fieldAut F j (e k)) (β w) := by
    intro k w
    have h := hβ (e k) w
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] at h
    exact h
  obtain ⟨b, c, hbc, Θ, ψ, hψ⟩ := omega_of_orth hs1 hs e σ β j hβ'
  obtain ⟨Ψ, h0, hker, hsurj, hΨ⟩ := exists_extend A ψ
  refine ⟨GaloisField 2 s, inferInstance, inferInstance, GaloisField.card 2 s (by omega), b, c,
    hbc, hA, isInvariant_bot ρ, bot_le, Θ, Ψ, h0, hker, hsurj, fun h x hx => ?_⟩
  have h1 : ρ (h : G) x = ((σ h ⟨x, hx⟩ : ↥A) : V) := (hσ h ⟨x, hx⟩).symm
  have h3 : Ψ x = ψ ⟨x, hx⟩ := hΨ ⟨x, hx⟩
  rw [h1, hΨ, h3, hψ]

theorem secIrr_of_card {A : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A) {r : ℕ}
    (hcard : Nat.card A = 2 ^ r)
    (hirr : ∀ C : Submodule (ZMod 2) V, C ≤ A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A) :
    SecIrr ρ L A ⊥ r := by
  refine ⟨hA, isInvariant_bot ρ, bot_le, ?_, fun C _ hCA hC => hirr C hCA hC⟩
  have h1 : Nat.card (⊥ : Submodule (ZMod 2) V) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, inferInstance⟩
  rw [hcard, h1, mul_one]

theorem secSum_one {P : Submodule (ZMod 2) V → Submodule (ZMod 2) V → Prop}
    {A : Submodule (ZMod 2) V} (h : P A ⊥) : SecSum P 1 A ⊥ := by
  refine ⟨fun _ => A, fun _ => ⟨bot_le, le_rfl, h⟩, iSup_const, fun i => ?_⟩
  have h1 : (⨆ j ∈ {j : Fin 1 | j ≠ i}, (fun _ : Fin 1 => A) j) = ⊥ := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
    exact absurd (Subsingleton.elim j i) hj
  rw [h1, inf_bot_eq]

theorem secSum_two {P : Submodule (ZMod 2) V → Submodule (ZMod 2) V → Prop}
    {A U C : Submodule (ZMod 2) V} (hU : P U ⊥) (hC : P C ⊥) (hsup : U ⊔ C = A)
    (hinf : U ⊓ C = ⊥) : SecSum P 2 A ⊥ := by
  have hUA : U ≤ A := hsup ▸ le_sup_left
  have hCA : C ≤ A := hsup ▸ le_sup_right
  refine ⟨![U, C], fun i => ?_, ?_, fun i => ?_⟩
  · fin_cases i
    · exact ⟨bot_le, hUA, hU⟩
    · exact ⟨bot_le, hCA, hC⟩
  · rw [← hsup]
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup_of_le 0 le_rfl)
      (le_iSup_of_le 1 le_rfl))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · fin_cases i
    · have h1 : (⨆ j ∈ {j : Fin 2 | j ≠ 0}, ![U, C] j) ≤ C := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact absurd rfl hj
        · exact le_rfl
      calc U ⊓ (⨆ j ∈ {j : Fin 2 | j ≠ 0}, ![U, C] j) ≤ U ⊓ C := inf_le_inf_left _ h1
        _ = ⊥ := hinf
        _ ≤ ⊥ := le_rfl
    · have h1 : (⨆ j ∈ {j : Fin 2 | j ≠ 1}, ![U, C] j) ≤ U := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact le_rfl
        · exact absurd rfl hj
      calc C ⊓ (⨆ j ∈ {j : Fin 2 | j ≠ 1}, ![U, C] j) ≤ C ⊓ U := inf_le_inf_left _ h1
        _ = ⊥ := by rw [inf_comm, hinf]
        _ ≤ ⊥ := le_rfl

end Sections

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br
