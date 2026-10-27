module

public import CFSG.Quasithin.EmptyFaithful.S146zUC1Piece
public import CFSG.Quasithin.EmptyFaithful.S153MTwoData

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.S153M
open scoped commutatorElement

namespace S146zU

theorem twoNat_of_action_L216 (hA21 : AsA21SQTKSection) (h56 : AsB56)
    {V : Type} [CommGroup V] [Finite V] {Hg : Type} [Group Hg] [Finite Hg] (hS : SQTKGroup Hg)
    (hV : ∀ v : V, v ^ 2 = 1) (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg)
    (hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hKn : (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal)
    (hcomm : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg)
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (hperm : ∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg))
    (hnt : ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker) (hFF : IsFFModule ρ.range)
    (hK : L216Cover ↥(K₁.map ρ)) : TwoActConcl ρ K₁ t := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ := ar_facts_two ρ K₁ t hqK hKn hcomm hQ h2 hperm hnt
  have hτX : ρ t ∈ ρ.range := ⟨t, rfl⟩
  have hL₁X : K₁.map ρ ≤ ρ.range := Subgroup.map_le_range ρ K₁
  have hL₂X : (K₁.map (MulAut.conj t).toMonoidHom).map ρ ≤ ρ.range := Subgroup.map_le_range ρ _
  obtain ⟨hL₁J, hL₂J⟩ := twoA_le_ffJ hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 := b53Hyp_of_two hA21 hS ρ hq₁ hq₂ hc hL₁J hL₂J hn h2' hO2
  have hcard : 504 ≤ Nat.card ↥(K₁.map ρ) := by
    have := UC1.card_of_L216Cover hK
    omega
  have hTwoB := twoB56_of_ffModule h56 hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hcard hO2 hFF hB53
  refine ⟨hTwoB.1, UC1.twoNat_of_twoB56_L216 hc hconj hq₁ hK hTwoB, hc, hn, ?_, hconj⟩
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

end S146zU

end CFSG.Quasithin
