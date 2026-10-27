module

public import CFSG.Quasithin.EmptyFaithful.S153MAR2
public import CFSG.Quasithin.EmptyFaithful.S153MTwoA
public import CFSG.Quasithin.EmptyFaithful.S153MTwoB
public import CFSG.Quasithin.EmptyFaithful.S1565L11
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153M

section TwoData

theorem layer_eq_top_of_sup_commute {Γ : Type} [Group Γ] {A B R : Subgroup Γ}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : CFSG.IsQuasisimple ↥A)
    (hB : CFSG.IsQuasisimple ↥B) (hR : R = A ⊔ B) : CFSG.layer ↥R = ⊤ := by
  subst hR
  have hAR : A ≤ A ⊔ B := le_sup_left
  have hBR : B ≤ A ⊔ B := le_sup_right
  have hBA : B ≤ Subgroup.centralizer (A : Set Γ) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb
  have hAB : A ≤ Subgroup.centralizer (B : Set Γ) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm
  have hnA : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).2
      (sup_le Subgroup.le_normalizer (hBA.trans (Subgroup.centralizer_le_normalizer _)))
  have hnB : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBR).2
      (sup_le (hAB.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)
  have hcA : CFSG.IsComponent (A.subgroupOf (A ⊔ B)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAR).symm hA,
      hnA.isSubnormal⟩
  have hcB : CFSG.IsComponent (B.subgroupOf (A ⊔ B)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBR).symm hB,
      hnB.isSubnormal⟩
  refine eq_top_iff.2 ?_
  rw [← Subgroup.subgroupOf_self (A ⊔ B), Subgroup.subgroupOf_sup hAR hBR]
  exact sup_le (CFSG.LocalCores.component_le_layer hcA) (CFSG.LocalCores.component_le_layer hcB)

variable {V : Type} [CommGroup V] [Finite V]

theorem b53Hyp_of_two (hA21 : AsA21SQTKSection) {Hg : Type} [Group Hg] [Finite Hg]
    (hS : SQTKGroup Hg) (ρ : Hg →* MulAut V) {L₁ L₂ : Subgroup (MulAut V)}
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hL₁J : L₁ ≤ ffJ ρ.range)
    (hL₂J : L₂ ≤ ffJ ρ.range)
    (hn : ∀ x ∈ ρ.range, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (h2 : ∀ x ∈ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂) (hO2 : pCoreOf 2 ρ.range = ⊥) :
    B53Hyp (ffJ ρ.range) := by
  set X : Subgroup (MulAut V) := ρ.range with hX
  set J : Subgroup (MulAut V) := ffJ X with hJ
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J := fun x hx j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) j).mp hj
  have hXN : X ≤ Subgroup.normalizer (J : Set (MulAut V)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun j => ⟨hXJ x hx j, fun hj => by
      have := hXJ x⁻¹ (X.inv_mem hx) _ hj
      simpa [mul_assoc] using this⟩
  refine ⟨?_, (InternalSec.ffJ_ffJ X).symm, ↥J, inferInstance, inferInstance, ⊥, inferInstance, ?_,
    ⟨(QuotientGroup.quotientBot).symm⟩⟩
  · refine eq_bot_iff.2 ?_
    have h1 : pCoreOf 2 J ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 J).trans hJX)
        (hXN.trans (normalizer_le_normalizer_pCoreOf 2 J)) (pCoreOf_isPGroup 2 J)
    exact h1.trans hO2.le
  · let Hs : Subgroup Hg := J.comap ρ
    let π : ↥Hs →* ↥J := (ρ.comp Hs.subtype).codRestrict J fun x => x.2
    have hπ : Function.Surjective π := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hJX hy
      exact ⟨⟨x, hy⟩, rfl⟩
    set R : Subgroup ↥J := (L₁ ⊔ L₂).subgroupOf J with hR
    have hRn : R.Normal := by
      refine ⟨fun n hn' g => ?_⟩
      rw [hR, Subgroup.mem_subgroupOf] at hn' ⊢
      exact hn g (hJX g.2) _ hn'
    have hcomm' : ∀ a ∈ L₁.subgroupOf J, ∀ b ∈ L₂.subgroupOf J, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
    have hq₁' : CFSG.IsQuasisimple ↥(L₁.subgroupOf J) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₁J).symm hq₁
    have hq₂' : CFSG.IsQuasisimple ↥(L₂.subgroupOf J) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₂J).symm hq₂
    have hlayer : CFSG.layer ↥R = ⊤ :=
      layer_eq_top_of_sup_commute hcomm' hq₁' hq₂' (Subgroup.subgroupOf_sup hL₁J hL₂J)
    refine hA21 Hg hS Hs ↥J π hπ R hlayer ?_
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 j (hJX j.2)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hR, Subgroup.mem_subgroupOf]
    simpa using he

@[expose] def TwoActConcl {Hg : Type} [Group Hg] (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg) :
    Prop :=
  ffJ ρ.range = K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ ∧
    TwoNat (K₁.map ρ) ((K₁.map (MulAut.conj t).toMonoidHom).map ρ) (ρ t) ∧
    (∀ a ∈ K₁.map ρ, ∀ b ∈ (K₁.map (MulAut.conj t).toMonoidHom).map ρ, a * b = b * a) ∧
    (∀ x ∈ ρ.range, ∀ l ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ,
      x * l * x⁻¹ ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
    (∀ g ∈ K₁.map ρ, (ρ t)⁻¹ * g * ρ t ∈ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
    (K₁.map (MulAut.conj t).toMonoidHom).map ρ = (K₁.map ρ).map (MulAut.conj (ρ t)).toMonoidHom

theorem twoNat_of_action (hA21 : AsA21SQTKSection) (h56 : AsB56)
    {Hg : Type} [Group Hg] [Finite Hg] (hS : SQTKGroup Hg) (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg)
    (hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hKn : (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal)
    (hcomm : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg)
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (hperm : ∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg))
    (hnt : ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker) (hFF : IsFFModule ρ.range)
    (hK : KsCoverTwo ↥(K₁.map ρ)) : TwoActConcl ρ K₁ t := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ := ar_facts_two ρ K₁ t hqK hKn hcomm hQ h2 hperm hnt
  have hτX : ρ t ∈ ρ.range := ⟨t, rfl⟩
  have hL₁X : K₁.map ρ ≤ ρ.range := Subgroup.map_le_range ρ K₁
  have hL₂X : (K₁.map (MulAut.conj t).toMonoidHom).map ρ ≤ ρ.range := Subgroup.map_le_range ρ _
  obtain ⟨hL₁J, hL₂J⟩ := twoA_le_ffJ hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 := b53Hyp_of_two hA21 hS ρ hq₁ hq₂ hc hL₁J hL₂J hn h2' hO2
  have hcard : 504 ≤ Nat.card ↥(K₁.map ρ) := by
    obtain ⟨Y, _, Ks, n, σ, hn3, -, hKs, hσ, -⟩ := hK
    exact (le_card_of_psl2_or_sz hn3 hKs).trans (Nat.card_le_card_of_surjective σ hσ)
  have hTwoB := twoB56_of_ffModule h56 hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hcard hO2 hFF hB53
  refine ⟨hTwoB.1, twoNat_of_twoB56 hτX hL₁X hL₂X hc hconj hn hq₁ hK hTwoB, hc, hn, ?_, hconj⟩
  have ht2 : t ^ 2 ∈ Subgroup.normalizer (K₁ : Set Hg) := by
    rcases hperm (t ^ 2) with h | h
    · exact h
    · have h' : t ∈ Subgroup.normalizer (K₁ : Set Hg) := by
        have : t⁻¹ * t ^ 2 = t := by group
        rwa [this] at h
      rw [pow_two]
      exact Subgroup.mul_mem _ h' h'
  intro g hg
  obtain ⟨k₁, hk₁, rfl⟩ := hg
  have hk₂ : (t ^ 2)⁻¹ * k₁ * t ^ 2 ∈ K₁ := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht2) k₁).mp hk₁
    simpa [mul_assoc] using h1
  refine ⟨t * ((t ^ 2)⁻¹ * k₁ * t ^ 2) * t⁻¹,
    ⟨(t ^ 2)⁻¹ * k₁ * t ^ 2, hk₂, by simp [MulAut.conj_apply]⟩, ?_⟩
  have e : t * ((t ^ 2)⁻¹ * k₁ * t ^ 2) * t⁻¹ = t⁻¹ * k₁ * t := by group
  rw [e, map_mul, map_mul, map_inv]

end TwoData

end S153M

end CFSG.Quasithin
