module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalMaxElem
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFiveCycle
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalTvQ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_omegaOneCenter' (R : Subgroup G) :
    IsElemAbelian 2 (quasithinOmegaOneCenter R) := by
  have hle : quasithinOmegaOneCenter R ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hcomm : ∀ a ∈ quasithinOmegaOneCenter R, ∀ b ∈ quasithinOmegaOneCenter R, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hle hb).2 a (hle ha).1
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hcomm a ha b hb) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

omit [Finite G] in
theorem omegaOneCenter_le_self (R : Subgroup G) : quasithinOmegaOneCenter R ≤ R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {V : Subgroup G} (h : conjSub g V = V) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ conjSub g V := mem_conjSub_of_mem' hy
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    have := mem_conjSub.mp hy
    simpa [mul_assoc] using this

theorem pu_d_geo (F : Frame L1 L2 S D X) {δ u : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) (hu : u ∈ nbrs δ)
    (hZQδ : ∀ u' ∈ nbrs δ, Zv u' ≤ Qv δ)
    (hZQ : ∀ u' ∈ nbrs δ, ∀ u'' ∈ nbrs δ, Zv u' ≤ Qv u'') :
    ¬ stab δ ≤ Subgroup.normalizer ((Qv δ ⊓ Qv u : Subgroup G) : Set G) := by
  intro hR
  have hA := Amal.of_frame F
  set R : Subgroup G := Qv δ ⊓ Qv u with hRdef
  obtain ⟨A, hAmax, hAnot⟩ := exists_maxElem_not_le F hu hR
  obtain ⟨hAQ, hAe, hAm⟩ : A ≤ Qv u ∧ IsElemAbelian 2 A ∧ ∀ B : Subgroup G, B ≤ Qv u →
      IsElemAbelian 2 B → Nat.card B ≤ Nat.card A := hAmax
  have hQs : ∀ δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S), Qv δ' ≤ stab δ' := fun δ' => pCoreOf_le 2 (stab δ')
  have hQu_sd : Qv u ≤ stab δ :=
    hA.Qv_le_stab_of_mem_nbrs (show δ ∈ nbrs u from (show (graph _ _ _).Adj δ u from hu).symm)
  set V : Subgroup G := quasithinOmegaOneCenter R with hV
  have hVR : V ≤ R := omegaOneCenter_le_self R
  have hVe := isElemAbelian_omegaOneCenter' R
  have hVle : V ≤ R ⊓ Subgroup.centralizer (R : Set G) := (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hconjR : ∀ g ∈ stab δ, conjSub g R = R := fun g hg => conjSub_eq_of_mem_normalizer (hR hg)
  have hVN : stab δ ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_of_conjSub_eq (by rw [hV, conjSub_omegaOneCenter, hconjR g hg])
  have hAC : A ⊓ Qv δ ≤ A ⊓ Subgroup.centralizer (V : Set G) := by
    intro x hx
    refine ⟨hx.1, fun v hv => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hVle hv).2) x ⟨hx.2, hAQ hx.1⟩).symm
  have hidxA : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left (L := A) hAC Subgroup.index_ne_zero_of_finite).trans
      (relIndex_inf_Qv_le_two F hδ (hAQ.trans hQu_sd) hAe)
  have hVcard := card_le_relIndex_mul_card hVe (hVR.trans inf_le_right)
    (show IsMaxElemAbelian (Qv u) A from ⟨hAQ, hAe, hAm⟩)
  have hpos : 0 < Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hmul : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card V := by
    have := Subgroup.relIndex_mul_card (H := V ⊓ Subgroup.centralizer (A : Set G)) (K := V)
    rwa [inf_eq_left.mpr inf_le_left] at this
  have hVA : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ 2 := by
    have h1 : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
        (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      rw [hmul]; exact hVcard
    exact h1.trans hidxA
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ A, a ∉ Qv δ := by
    by_contra h
    push Not at h
    exact hAnot h
  have hidxa : (V ⊓ Subgroup.centralizer {a}).relIndex V ≤ 2 := by
    have hle : V ⊓ Subgroup.centralizer (A : Set G) ≤ V ⊓ Subgroup.centralizer {a} := by
      intro x hx
      exact ⟨hx.1, Subgroup.centralizer_le (by simpa using haA) hx.2⟩
    exact (Subgroup.relIndex_le_of_le_left (L := V) hle Subgroup.index_ne_zero_of_finite).trans hVA
  have ha2 : a * a ∈ Qv δ := by
    have : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
    rw [this]; exact (Qv δ).one_mem
  obtain ⟨e, he, heC, heQ, he5⟩ :=
    exists_centralizing_five F hδ hVe hVN (hAQ.trans hQu_sd haA) haQ ha2 hidxa
  have hZV : ∀ u' ∈ nbrs δ, Zv u' ≤ V := by
    intro u' hu'
    obtain ⟨g, hg, hgu⟩ := stab_transitive_on_nbrs hu hu'
    have hgδ : g • δ = δ := smul_eq_of_mem_stab hg
    have hRu' : R ≤ Qv u' := by
      have h1 : conjSub (g : G) R = Qv δ ⊓ Qv u' := by
        rw [hRdef, conjSub_inf, ← hgu, ← Qv_smul, ← Qv_smul, hgδ]
      rw [← hconjR g hg, h1]; exact inf_le_right
    intro z hz
    have hzc := hA.Zv_le_centerOf_Qv u' hz
    have hzR : z ∈ R := ⟨hZQδ u' hu' hz, hZQ u' hu' u hu hz⟩
    have hzC : z ∈ Subgroup.centralizer (R : Set G) := fun r hr =>
      Subgroup.mem_centralizer_iff.mp hzc.2 r (hRu' hr)
    have hz2 : z ^ 2 = 1 := (hA.isElemAbelian_Zv u').2 z hz
    exact Subgroup.subset_closure ⟨⟨hzR, hzC⟩, hz2⟩
  have hZeq : ∀ u' ∈ nbrs δ, Zv u' = Zv u := by
    intro u' hu'
    obtain ⟨g, hgz, hgu⟩ := exists_zpow_smul_nbr F hδ he heQ he5 hu hu'
    have hgC : (g : G) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.zpowers_le.mpr heC) hgz
    have hgN : (g : G) ∈ Subgroup.normalizer ((Zv u : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (hZV u hu) hgC)
    rw [← hgu, Zv_smul, conjSub_eq_of_mem_normalizer hgN]
  have hNδ : stab δ ≤ Subgroup.normalizer ((Zv u : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxG, hxfix⟩ := mem_stab.mp hx
    apply mem_normalizer_of_conjSub_eq
    have hmem : (⟨x, hxG⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • u ∈ nbrs δ := by
      have := (smul_adj ⟨x, hxG⟩).mpr hu
      rwa [hxfix] at this
    rw [← Zv_smul (⟨x, hxG⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) u]
    exact hZeq _ hmem
  have hNu : stab u ≤ Subgroup.normalizer ((Zv u : Subgroup G) : Set G) :=
    hA.stab_le_normalizer_Zv u
  have hZle : Zv u ≤ stab δ ⊓ stab u :=
    le_inf ((hZQδ u hu).trans (hQs δ)) ((hA.Zv_le_Qv u).trans (hQs u))
  have hbot := hA.eq_bot_of_normalizes_both hu hZle hNδ hNu
  exact hA.Zv_ne_bot u hbot

theorem pu_d (F : Frame L1 L2 S D X)
    (hZQδ : ∀ u' ∈ nbrs (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)),
      Zv u' ≤ Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)))
    (hZQ : ∀ u' ∈ nbrs (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)),
      ∀ u'' ∈ nbrs (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)), Zv u' ≤ Qv u'') :
    ¬ P1 L1 L2 S ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have h := pu_d_geo F (δ := γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    (u := γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) (by simp [vtype_γ₀])
    adj_γ₀_γ₁ hZQδ hZQ
  have e0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have e1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  rw [stab_γ₀ h₁, e0, e1] at h
  exact h

end CFSG.Quasithin.Kleidman.F204
