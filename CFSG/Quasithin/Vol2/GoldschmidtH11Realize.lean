module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Model

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem mem_statedSL_iff (γ : GL (Fin 2) K) :
    γ ∈ StatedSL 2 K ↔ (γ : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

omit [Finite K] [CharP K 2] in
theorem toGL_mem_statedSL (γ₀ : SL(2, K)) : Matrix.SpecialLinearGroup.toGL γ₀ ∈ StatedSL 2 K := by
  rw [mem_statedSL_iff]
  exact γ₀.2

omit [Finite K] [CharP K 2] in
theorem exists_toGL_eq {γ : GL (Fin 2) K} (hγ : γ ∈ StatedSL 2 K) :
    ∃ γ₀ : SL(2, K), Matrix.SpecialLinearGroup.toGL γ₀ = γ :=
  ⟨⟨(γ : Matrix (Fin 2) (Fin 2) K), (mem_statedSL_iff γ).mp hγ⟩, Units.ext rfl⟩

theorem exists_equiv_of_realizes {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (a : ℕ)
    (hcard : Nat.card K = 2 ^ (2 * a))
    (hreal : (FFModel.twistTensor a (StatedSL 2 K)).Realizes L ⊤ ⊥) :
    ∃ e : V ≃* HV K a, ∀ φ : MulAut V, φ ∈ L ↔
      ∃ γ : SL(2, K), ∀ v, e (φ v) = actHom a hcard γ (e v) := by
  obtain ⟨π, hs, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hreal
  let qe : (↥(FFModel.twistTensor a (StatedSL 2 K)).sec ⧸
      (FFModel.twistTensor a (StatedSL 2 K)).ker.subgroupOf
        (FFModel.twistTensor a (StatedSL 2 K)).sec) ≃* HV K a :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans QuotientGroup.quotientBot
  let β' : V →* HV K a :=
    ((qe : _ →* HV K a).comp β).comp (Subgroup.topEquiv.symm : V ≃* ↥(⊤ : Subgroup V)).toMonoidHom
  have hβ'inj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : β ⟨v, trivial⟩ = 1 := by
      have : qe (β ⟨v, trivial⟩) = 1 := hv
      exact qe.injective (by rw [this, map_one])
    simpa using (hβk ⟨v, trivial⟩).mp h1
  have hβ'surj : Function.Surjective β' := fun w => by
    obtain ⟨u, hu⟩ := hβs (qe.symm w)
    exact ⟨u.1, by
      show qe (β ⟨u.1, trivial⟩) = w
      rw [show (⟨u.1, trivial⟩ : ↥(⊤ : Subgroup V)) = u from rfl, hu]
      simp⟩
  let e : V ≃* HV K a := MulEquiv.ofBijective β' ⟨hβ'inj, hβ'surj⟩
  have key : ∀ (γ : ↥(StatedSL 2 K)) (γ₀ : SL(2, K)),
      Matrix.SpecialLinearGroup.toGL γ₀ = γ.1 → ∀ v : V,
        e ((π γ : MulAut V) v) = actHom a hcard γ₀ (e v) := by
    intro γ γ₀ hγ v
    have hm0 : ((FFModel.twistTensor a (StatedSL 2 K)).act γ (e v).1) ∈
        (FFModel.twistTensor a (StatedSL 2 K)).sec := hsec γ _ (e v).2
    have hβu : β ⟨v, trivial⟩ = (QuotientGroup.mk (e v) :
        ↥(FFModel.twistTensor a (StatedSL 2 K)).sec ⧸
          (FFModel.twistTensor a (StatedSL 2 K)).ker.subgroupOf
            (FFModel.twistTensor a (StatedSL 2 K)).sec) := by
      change β ⟨v, trivial⟩ = qe.symm (qe (β ⟨v, trivial⟩))
      simp
    have h1 := hβe γ ⟨v, trivial⟩ (e v) trivial hm0 hβu
    apply hm_injective a
    have h2 : e ((π γ : MulAut V) v) = ⟨_, hm0⟩ := by
      change qe (β ⟨(π γ : MulAut V) v, trivial⟩) = _
      rw [h1]; rfl
    rw [h2]
    show Multiplicative.toAdd ((FFModel.twistTensor a (StatedSL 2 K)).act γ (e v).1) = _
    simp only [FFModel.twistTensor, twistAct, hm_actHom]
    rw [← hγ]
    rfl
  refine ⟨e, fun φ => ⟨fun hφ => ?_, fun ⟨γ₀, hγ₀⟩ => ?_⟩⟩
  · obtain ⟨γ, hγ⟩ := hs ⟨φ, hφ⟩
    obtain ⟨γ₀, hγ₀⟩ := exists_toGL_eq γ.2
    refine ⟨γ₀, fun v => ?_⟩
    have hφ' : (π γ : MulAut V) = φ := congrArg Subtype.val hγ
    rw [← hφ']
    exact key γ γ₀ hγ₀ v
  · let γ : ↥(StatedSL 2 K) := ⟨Matrix.SpecialLinearGroup.toGL γ₀, toGL_mem_statedSL γ₀⟩
    have hπγ : (π γ : MulAut V) = φ := by
      refine MulEquiv.ext fun v => e.injective ?_
      rw [key γ γ₀ rfl v, hγ₀ v]
    rw [← hπγ]
    exact (π γ).2

end CFSG.Quasithin.H11
