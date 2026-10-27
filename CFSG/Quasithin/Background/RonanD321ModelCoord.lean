module

public import CFSG.Quasithin.Background.RonanD321ModelSemi
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithD321Q

public section

namespace CFSG.Quasithin.RonanD321.SL2Model

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
open Matrix Multiplicative
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_col (hB : D321Base M Mp T L V t) {K : Type} [Field K] {I : Subgroup W}
    {π : ↥(StatedSL 2 K) →* ↥L} (hIU : I ≤ commV L)
    (hreal : (FFModel.nat (StatedSL 2 K)).RealizesVia L I (commV L ⊓ fixV Mp) π) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ ψ : Multiplicative (Fin 2 → K) →* (W ⧸ modFix Mp (⊤ : Subgroup W)),
      Function.Injective ψ ∧ ψ.range = tilde Mp ⊤ I ∧
      ∀ γ v, ψ (ofAdd (slm γ *ᵥ v)) =
        (⟨(π γ : MulAut W), hB.L_le (π γ).2⟩ : ↥M) • ψ (ofAdd v) := by
  letI := qAct hB.hD.hyp.Mp_normal
  obtain ⟨-, -, -, hHU, -, -, -, β, hβs, hβk, hβe⟩ := hreal
  let e : Multiplicative (Fin 2 → K) → (↥(FFModel.nat (StatedSL 2 K)).sec ⧸
      (FFModel.nat (StatedSL 2 K)).ker.subgroupOf (FFModel.nat (StatedSL 2 K)).sec) :=
    fun v => QuotientGroup.mk ⟨v, trivial⟩
  have he : ∀ a b, e (a * b) = e a * e b := fun a b => rfl
  choose sec hsec using fun v => hβs (e v)
  have hmk : ∀ a b : ↥I, β a = β b →
      (QuotientGroup.mk (a : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk (b : W) := by
    intro a b hab
    have h1 : β (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 := ((hβk _).1 h1).2
    rw [QuotientGroup.eq, modFix_top_eq]
    exact h2
  let ψ : Multiplicative (Fin 2 → K) →* (W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    MonoidHom.mk' (fun v => QuotientGroup.mk (sec v : W)) fun a b => by
      rw [← QuotientGroup.mk_mul, ← Subgroup.coe_mul]
      exact hmk _ _ (by rw [hsec, map_mul, hsec, hsec, he])
  have hψ : ∀ (u : ↥I) v, β u = e v → ψ v = QuotientGroup.mk (u : W) :=
    fun u v h => hmk _ _ ((hsec v).trans h.symm)
  refine ⟨ψ, ?_, ?_, fun γ v => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : ((sec v : ↥I) : W) ∈ fixV Mp := by
      rw [← modFix_top_eq]
      exact (QuotientGroup.eq_one_iff _).1 hv
    have h2 : e v = 1 := by
      rw [← hsec]
      exact (hβk _).2 ⟨hIU (sec v).2, h1⟩
    have h3 := (QuotientGroup.eq_one_iff _).1 h2
    rw [Subgroup.mem_subgroupOf] at h3
    exact Subgroup.mem_bot.1 h3
  · ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact mem_tilde_iff.2 ⟨_, (sec v).2, rfl⟩
    · intro hq
      obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.1 hq
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
      exact ⟨m.1, hψ ⟨w, hw⟩ _ hm.symm⟩
  · have h1 := hβe γ (sec (ofAdd v)) ⟨ofAdd v, trivial⟩ (hHU (π γ) _ (sec (ofAdd v)).2) trivial
      (hsec _)
    have h2 : ψ (ofAdd (slm γ *ᵥ v)) = QuotientGroup.mk ((π γ : MulAut W) (sec (ofAdd v) : W)) :=
      hψ ⟨_, hHU (π γ) _ (sec (ofAdd v)).2⟩ (ofAdd (slm γ *ᵥ v)) h1
    rw [h2]
    rfl

theorem exists_coord (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K = 2 ∧
      ∃ (π : ↥(StatedSL 2 K) →* ↥M)
        (Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* (W ⧸ modFix Mp (⊤ : Subgroup W))),
        IsCoord π Ψ ∧ Ψ.range = tilde Mp ⊤ (commV L) ∧ (∀ γ, ((π γ : ↥M) : MulAut W) ∈ L) ∧
        ∀ l ∈ L, ∃ γ, ((π γ : ↥M) : MulAut W) = l := by
  letI := qAct hB.hD.hyp.Mp_normal
  obtain ⟨n, -, K, _, _, hcard, I, π, -, hind, hsup, hreal⟩ := h3
  have hIU : ∀ i, I i ≤ commV L := fun i => hsup ▸ (le_iSup I i).trans le_sup_right
  have hcol : ∀ i, ∃ ψ : Multiplicative (Fin 2 → K) →* (W ⧸ modFix Mp (⊤ : Subgroup W)),
      Function.Injective ψ ∧ ψ.range = tilde Mp ⊤ (I i) ∧
      ∀ γ v, ψ (ofAdd (slm γ *ᵥ v)) =
        (⟨(π γ : MulAut W), hB.L_le (π γ).2⟩ : ↥M) • ψ (ofAdd v) :=
    fun i => exists_col hB (hIU i) (hreal i)
  choose ψ hψi hψr hψe using hcol
  have hK : ringChar K = 2 := by
    let _ : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    exact ringChar.eq K 2
  let col (j : Fin 2) : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* Multiplicative (Fin 2 → K) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mk' (fun X i => X i j) fun _ _ => rfl)
  let Ψ := (ψ 0).comp (col 0) * (ψ 1).comp (col 1)
  have hΨ : ∀ X : Matrix (Fin 2) (Fin 2) K,
      Ψ (ofAdd X) = ψ 0 (ofAdd fun i => X i 0) * ψ 1 (ofAdd fun i => X i 1) := fun X => rfl
  have hmem : ∀ i v, ψ i v ∈ tilde Mp ⊤ (I i) := fun i v => by
    rw [← hψr i]
    exact ⟨v, rfl⟩
  have hdisj : ∀ q, q ∈ tilde Mp ⊤ (I 0) → q ∈ tilde Mp ⊤ (I 1) → q = 1 := by
    intro q h0 h1
    obtain ⟨a, ha, rfl⟩ := mem_tilde_iff.1 h0
    obtain ⟨b, hb, hab⟩ := mem_tilde_iff.1 h1
    have hba : b⁻¹ * a ∈ fixV Mp := by
      rw [← modFix_top_eq]
      exact QuotientGroup.eq.1 hab
    have hZ : a * b⁻¹ ∈ commV L ⊓ fixV Mp :=
      ⟨(commV L).mul_mem (hIU 0 ha) ((commV L).inv_mem (hIU 1 hb)), by rw [mul_comm]; exact hba⟩
    have h1le : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl
    have ha' : a ∈ I 0 ⊓ (commV L ⊓ fixV Mp ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := by
      refine ⟨ha, ?_⟩
      have e : a = (a * b⁻¹) * b := by rw [inv_mul_cancel_right]
      rw [e]
      exact Subgroup.mul_mem_sup hZ (h1le hb)
    rw [hind 0] at ha'
    rw [QuotientGroup.eq_one_iff, modFix_top_eq]
    exact ha'.2
  refine ⟨K, inferInstance, inferInstance, hK, (Subgroup.inclusion hB.L_le).comp π, Ψ,
    ⟨?_, fun γ X => ?_⟩, ?_, fun γ => (π γ).2, fun l hl => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro X hX
    have hX' : ψ 0 (ofAdd fun i => toAdd X i 0) * ψ 1 (ofAdd fun i => toAdd X i 1) = 1 := hX
    have e0 : ψ 0 (ofAdd fun i => toAdd X i 0) = 1 := by
      refine hdisj _ (hmem 0 _) ?_
      rw [eq_inv_of_mul_eq_one_left hX']
      exact (tilde Mp ⊤ (I 1)).inv_mem (hmem 1 _)
    rw [e0, one_mul] at hX'
    have f0 := congrArg toAdd ((injective_iff_map_eq_one _).1 (hψi 0) _ e0)
    have f1 := congrArg toAdd ((injective_iff_map_eq_one _).1 (hψi 1) _ hX')
    have hX0 : toAdd X = 0 := by
      ext i j
      fin_cases j
      · exact congrFun f0 i
      · exact congrFun f1 i
    rw [← ofAdd_toAdd X, hX0, ofAdd_zero]
  · rw [hΨ, hΨ, smul_mul']
    have hc : ∀ j, (fun i => (slm γ * X) i j) = slm γ *ᵥ (fun i => X i j) := fun j => by
      ext i
      simp [mul_apply, mulVec, dotProduct]
    rw [hc 0, hc 1, hψe 0, hψe 1]
    rfl
  · apply le_antisymm
    · rintro _ ⟨X, rfl⟩
      exact (tilde Mp ⊤ (commV L)).mul_mem (tilde_mono (hIU 0) (hmem 0 _))
        (tilde_mono (hIU 1) (hmem 1 _))
    · rw [← hsup]
      unfold tilde
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun z hz => ?_) (iSup_le fun i => fun u hu => ?_)
      · rw [Subgroup.mem_comap]
        have h1 : (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) z) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
          exact hz.2
        rw [h1]
        exact Ψ.range.one_mem
      · rw [Subgroup.mem_comap]
        have hu' : (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) u) ∈ (ψ i).range := by
          rw [hψr i]
          exact ⟨u, hu, rfl⟩
        obtain ⟨v, hv⟩ := hu'
        refine ⟨ofAdd (vecMulVec (toAdd v) (Pi.single i 1)), ?_⟩
        rw [← hv]
        show Ψ (ofAdd _) = _
        rw [hΨ]
        fin_cases i
        · have h0 : (ofAdd fun k => vecMulVec (toAdd v) (Pi.single (0 : Fin 2) (1 : K)) k 1) =
              (1 : Multiplicative (Fin 2 → K)) := by
            ext k
            simp [vecMulVec]
          have h1 :
              (ofAdd fun k => vecMulVec (toAdd v) (Pi.single (0 : Fin 2) (1 : K)) k 0) = v := by
            ext k
            simp [vecMulVec]
          simp only [Fin.zero_eta, Fin.isValue] at h0 h1 ⊢
          rw [h0, h1, map_one, mul_one]
        · have h0 : (ofAdd fun k => vecMulVec (toAdd v) (Pi.single (1 : Fin 2) (1 : K)) k 0) =
              (1 : Multiplicative (Fin 2 → K)) := by
            ext k
            simp [vecMulVec]
          have h1 :
              (ofAdd fun k => vecMulVec (toAdd v) (Pi.single (1 : Fin 2) (1 : K)) k 1) = v := by
            ext k
            simp [vecMulVec]
          simp only [Fin.mk_one, Fin.isValue] at h0 h1 ⊢
          rw [h0, h1, map_one, one_mul]
  · obtain ⟨γ, hγ⟩ := (hreal 0).1 ⟨l, hl⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩

theorem normalizer_hyps (hB : D321Base M Mp T L V t) {X : Subgroup (MulAut W)} {K : Type}
    [Field K] {π : ↥(StatedSL 2 K) →* ↥M}
    {Ψ : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hrange : letI := qAct hB.hD.hyp.Mp_normal; Ψ.range = tilde Mp ⊤ (commV X))
    (hπL : ∀ γ, ((π γ : ↥M) : MulAut W) ∈ X)
    (hπs : ∀ l ∈ X, ∃ γ, ((π γ : ↥M) : MulAut W) = l) :
    letI := qAct hB.hD.hyp.Mp_normal
    (∀ g ∈ (Subgroup.normalizer (X : Set (MulAut W))).subgroupOf M, ∀ γ,
      ∃ δ, g * π γ * g⁻¹ = π δ) ∧
    ∀ g ∈ (Subgroup.normalizer (X : Set (MulAut W))).subgroupOf M, ∀ Y,
      ∃ Y', g • Ψ (ofAdd Y) = Ψ (ofAdd Y') := by
  letI := qAct hB.hD.hyp.Mp_normal
  refine ⟨fun g hg γ => ?_, fun g hg Y => ?_⟩
  · have hg' := Subgroup.mem_subgroupOf.1 hg
    have h1 : (g : MulAut W) * (π γ : MulAut W) * (g : MulAut W)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 hg' _).1 (hπL γ)
    obtain ⟨δ, hδ⟩ := hπs _ h1
    exact ⟨δ, Subtype.ext hδ.symm⟩
  · have hg' := Subgroup.mem_subgroupOf.1 hg
    have h1 : Ψ (ofAdd Y) ∈ tilde Mp ⊤ (commV X) := by
      rw [← hrange]
      exact ⟨_, rfl⟩
    have h2 : g • tilde Mp ⊤ (commV X) = tilde Mp ⊤ (commV X) := by
      rw [smul_tildeQ hB.hD.hyp.Mp_normal]
      congr 1
      change (commV X).map (g : MulAut W).toMonoidHom = commV X
      rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hg']
    have h3 : g • Ψ (ofAdd Y) ∈ Ψ.range := by
      rw [hrange, ← h2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    obtain ⟨Y', hY'⟩ := h3
    exact ⟨toAdd Y', hY'.symm⟩

end CFSG.Quasithin.RonanD321.SL2Model
