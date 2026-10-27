module

public import CFSG.Quasithin.Vol2.Ch10SecKL7q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem exists_sylow_data (c₁ : Coord L₁ W₁) :
    ∃ S : Subgroup (MulAut W), IsSylowIn 2 S Mb ∧ U3.map c₁.phi ≤ S ∧
      (∃ t ∈ S, t ∉ Subgroup.normalizer (L₁ : Set (MulAut W))) ∧
      ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) →
        ∃ p ∈ U3.map c₁.phi, p⁻¹ * s ∈ Subgroup.centralizer (L₁ : Set (MulAut W)) := by
  have := h.finite_aut
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := c₁.P_le
  have hPM : U3.map c₁.phi ≤ Mb := hPL.trans h.le₁
  have hPp : IsPGroup 2 ↥((U3.map c₁.phi).subgroupOf Mb) :=
    c₁.isPGroup_P.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  obtain ⟨Q, hQ⟩ := hPp.exists_le_sylow
  set S := (Q : Subgroup ↥Mb).map Mb.subtype with hS
  have hSM : S ≤ Mb := Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 ↥S := Q.isPGroup'.map Mb.subtype
  have hSsub : S.subgroupOf Mb = Q := Subgroup.comap_map_eq_self_of_injective
    Subtype.val_injective _
  have hSyl : IsSylowIn 2 S Mb := ⟨hSM, hSp, by
    rw [Subgroup.relIndex, hSsub]
    exact Q.not_dvd_index⟩
  have hPS : U3.map c₁.phi ≤ S := fun p hp => ⟨⟨p, hPM hp⟩, hQ hp, rfl⟩
  refine ⟨S, hSyl, hPS, ?_, ?_⟩
  · by_contra hall
    have hSK : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := fun s hs =>
      by_contra fun hn => hall ⟨s, hs, hn⟩
    obtain ⟨e, m, hm, hτ⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos τ).ne'
    have hτ₂M : τ ^ m ∈ Mb := pow_mem h.memτ m
    have hτ₂K : τ ^ m ∉ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
      rw [h.mem_K_pow_iff]
      exact Nat.not_even_iff_odd.2 hm
    have hτ₂p : (τ ^ m) ^ 2 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hτ, pow_orderOf_eq_one]
    have hz : IsPGroup 2 ↥(Subgroup.zpowers (⟨τ ^ m, hτ₂M⟩ : ↥Mb)) := fun g => ⟨e, by
      obtain ⟨z, hz⟩ := g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have : (⟨τ ^ m, hτ₂M⟩ : ↥Mb) ^ 2 ^ e = 1 := Subtype.ext hτ₂p
      rw [this, one_zpow]
      rfl⟩
    obtain ⟨Q₂, hQ₂⟩ := hz.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Mb Q₂ Q
    have hmem : MulAut.conj g • (⟨τ ^ m, hτ₂M⟩ : ↥Mb) ∈ (Q : Subgroup ↥Mb) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ₂ (Subgroup.mem_zpowers _))
    have h1 : (g : MulAut W) * τ ^ m * (g : MulAut W)⁻¹ ∈
        Subgroup.normalizer (L₁ : Set (MulAut W)) := hSK _ ⟨_, hmem, rfl⟩
    have h2 := h.conj_mem_K (Mb.inv_mem g.2) (mul_mem (mul_mem g.2 hτ₂M) (Mb.inv_mem g.2)) h1
    exact hτ₂K (by simpa [mul_assoc] using h2)
  · set K := Mb ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) with hK
    let SK : Subgroup ↥K := (S ⊓ K).subgroupOf K
    have hSKp : IsPGroup 2 ↥SK :=
      (hSp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    let T : Subgroup (MulAut W) := (SK.map h.pr₁).map L₁.subtype
    have hTL : T ≤ L₁ := Subgroup.map_subtype_le _
    have hTp : IsPGroup 2 ↥T := (hSKp.map h.pr₁).map L₁.subtype
    have hPT : U3.map c₁.phi ≤ T := fun p hp => by
      have hpK : p ∈ K := ⟨hPM hp, Subgroup.le_normalizer (hPL hp)⟩
      refine ⟨h.pr₁ ⟨p, hpK⟩, ⟨⟨p, hpK⟩, ⟨hPS hp, hpK⟩, rfl⟩, ?_⟩
      rw [h.pr₁_of_mem ⟨p, hpK⟩ (hPL hp)]
      rfl
    have hTeq : T = U3.map c₁.phi := c₁.eq_P_of_le hTL hTp hPT
    intro s hs hsK
    have hsK' : s ∈ K := ⟨hSM hs, hsK⟩
    obtain ⟨y, hy, hsy⟩ := h.pr₁_spec ⟨s, hsK'⟩
    refine ⟨(h.pr₁ ⟨s, hsK'⟩ : MulAut W), hTeq ▸ ⟨_, ⟨⟨s, hsK'⟩, ⟨hs, hsK'⟩, rfl⟩, rfl⟩, ?_⟩
    have hsy' : s = (h.pr₁ ⟨s, hsK'⟩ : MulAut W) * y := hsy
    have h3 : (h.pr₁ ⟨s, hsK'⟩ : MulAut W)⁻¹ * s = y := by
      rw [inv_mul_eq_iff_eq_mul]
      exact hsy'
    rw [h3]
    exact hy

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
