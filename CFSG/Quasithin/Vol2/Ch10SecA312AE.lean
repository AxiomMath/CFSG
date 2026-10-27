module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def AutFixInner (K : Type) [Group K] : Prop :=
  ∀ T : Subgroup K, IsSylowTwoOf T ⊤ → ∀ β : MulAut K, β * β = 1 → (∀ t ∈ T, β t = t) →
    ∃ g : K, β = MulAut.conj g

variable {K L : Type} [Group K] [Group L]

theorem eq_conj_of_isInnerAut {β : MulAut K} (h : Ch1.IsInnerAut β) :
    ∃ g : K, β = MulAut.conj g := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l⁻¹, ?_⟩
  ext x
  rw [hl x, MulAut.conj_apply, inv_inv]

theorem apply_apply_of_mul_self {β : MulAut K} (hβ : β * β = 1) (x : K) : β (β x) = x := by
  have := congrArg (fun φ : MulAut K => φ x) hβ
  simpa using this

theorem not_dvd_index {T : Subgroup K} (hT : IsSylowTwoOf T ⊤) : ¬ 2 ∣ T.index := by
  rw [← index_subgroupOf_top]
  exact hT.2.2

theorem autFixInner_of_lie [Finite K] (hE : Ch1.EvenLieAutInner) (hK : Ch1.SQTKCharTwoLie K) :
    AutFixInner K := by
  intro T hT β hβ hβT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_conj_of_isInnerAut (hE K hK β (apply_apply_of_mul_self hβ)
    ⟨hT.isPGroup.toSylow (not_dvd_index hT), fun t ht => hβT t ht⟩)

theorem autFixInner_of_sporadic [Finite K] (hS : Ch1.SporadicAutInner)
    {s : TauCeti.SporadicName} (hs : Ch1.IsSQTKSporadicName s) (hs1 : s ≠ .J1)
    (h : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) : AutFixInner K := by
  intro T hT β hβ hβT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_conj_of_isInnerAut (hS s hs hs1 K h β (apply_apply_of_mul_self hβ)
    ⟨hT.isPGroup.toSylow (not_dvd_index hT), fun t ht => hβT t ht⟩)

theorem autFixInner_of_mulEquiv [Finite K] [Finite L] (e : K ≃* L) (h : AutFixInner L) :
    AutFixInner K := by
  intro T hT β hβ hβT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Sylow 2 K := hT.isPGroup.toSylow (not_dvd_index hT)
  set P' : Sylow 2 L := P.mapSurjective (f := e.toMonoidHom) e.surjective
  set β' : MulAut L := e.symm.trans (β.trans e)
  have hβ' : β' * β' = 1 := by
    ext y
    show e (β (e.symm (e (β (e.symm y))))) = y
    rw [MulEquiv.symm_apply_apply, apply_apply_of_mul_self hβ, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := h _ (isSylowTwoOf_top_of_sylow P') β' hβ' (by
    rintro _ ⟨t, ht, rfl⟩
    show e (β (e.symm (e t))) = e t
    rw [MulEquiv.symm_apply_apply, hβT t ht])
  refine ⟨e.symm g, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut L => φ (e x)) hg
  change e (β (e.symm (e x))) = g * e x * g⁻¹ at h1
  rw [MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_one_of_central (hp : commutator K = ⊤) (γ : MulAut K)
    (hγ : ∀ x : K, x⁻¹ * γ x ∈ Subgroup.center K) : γ = 1 := by
  let F : Subgroup K :=
    { carrier := {x | γ x = x}
      one_mem' := map_one γ
      mul_mem' := fun {a b} ha hb => by
        show γ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show γ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have key : ∀ c ∈ Subgroup.center K, ∀ Y : K, c * Y * c⁻¹ = Y := fun c hc Y => by
    rw [(Subgroup.mem_center_iff.mp hc Y).symm, mul_inv_cancel_right]
  have hle : commutator K ≤ F := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show γ ⁅a, b⁆ = ⁅a, b⁆
    have hza : γ a = a * (a⁻¹ * γ a) := by group
    have hwb : γ b = b * (b⁻¹ * γ b) := by group
    set z := a⁻¹ * γ a with hz
    set w := b⁻¹ * γ b with hw
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc γ a * γ b * (γ a)⁻¹ * (γ b)⁻¹ = a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ := by
          rw [← hza, ← hwb]
      _ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
      _ = a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [key z (hγ a)]
      _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [key w (hγ b)]
  ext x
  have hx : x ∈ F := hle (hp ▸ Subgroup.mem_top x)
  exact hx

theorem autFixInner_of_quotient [Finite K] (hp : commutator K = ⊤)
    (h : AutFixInner (K ⧸ Subgroup.center K)) : AutFixInner K := by
  intro T hT β hβ hβT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : (Subgroup.center K).map β.toMonoidHom = Subgroup.center K := Subgroup.map_center_eq β
  set βb : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) β hc with hβb
  have hβbmk : ∀ x : K, βb (QuotientGroup.mk x) = QuotientGroup.mk (β x) := fun x => rfl
  set P : Sylow 2 K := hT.isPGroup.toSylow (not_dvd_index hT)
  set P' : Sylow 2 (K ⧸ Subgroup.center K) :=
    P.mapSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  have hβb2 : βb * βb = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show βb (βb (QuotientGroup.mk x)) = QuotientGroup.mk x
    rw [hβbmk, hβbmk, apply_apply_of_mul_self hβ]
  obtain ⟨gb, hg⟩ := h _ (isSylowTwoOf_top_of_sylow P') βb hβb2 (by
    rintro _ ⟨t, ht, rfl⟩
    show βb (QuotientGroup.mk t) = QuotientGroup.mk t
    rw [hβbmk, hβT t ht])
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  refine ⟨g, ?_⟩
  have h1 : ∀ x : K, (g * x * g⁻¹)⁻¹ * β x ∈ Subgroup.center K := fun x => by
    have h2 := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ (QuotientGroup.mk x)) hg
    change βb (QuotientGroup.mk x) = _ at h2
    rw [hβbmk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at h2
    exact QuotientGroup.eq.mp h2.symm
  have hγ := eq_one_of_central hp ((MulAut.conj g)⁻¹ * β) fun x => by
    have h3 := (inferInstance : (Subgroup.center K).Normal).conj_mem _ (h1 x) g⁻¹
    show x⁻¹ * (g⁻¹ * β x * g) ∈ Subgroup.center K
    convert h3 using 1
    group
  calc β = MulAut.conj g * ((MulAut.conj g)⁻¹ * β) := by group
    _ = MulAut.conj g := by rw [hγ, mul_one]

theorem sqtkCharTwoLie_of_isSL3 {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f) (h : IsSL3 (2 ^ f) Y) :
    Ch1.SQTKCharTwoLie (Y ⧸ Subgroup.center Y) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let e₁ : Y ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  let e₂ : Y ⧸ Subgroup.center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  refine Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, ⟨Nat.prime_two, hf, by norm_num, by simp,
    by simp⟩, F, inferInstance, inferInstance, hF,
    ⟨e₂.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩)⟩)

end CFSG.Quasithin.Vol2.Ch10.A312A
