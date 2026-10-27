module

public import CFSG.Quasithin.Vol2.F134J1
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1Model
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem autInner_of_isSporadic_J1 {Q : Type} [Group Q] [Finite Q]
    (hQ : IsSporadic .J1 Q) {P : Subgroup Q} (hP : IsSylowTwoOf P ⊤) (α : MulAut Q)
    (hαP : P.map α.toMonoidHom = P) :
    ∃ g : Q, α = MulAut.conj g ∧ ((∃ k : ℕ, α ^ 2 ^ k = 1) → g ∈ P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hQ
  let e : Q ≃* CFSG.Open.walterJ1 := e₀.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.autInner_walterJ1 ((e.symm.trans α).trans e)
  have hαg : α = MulAut.conj (e.symm x⁻¹) := by
    ext q
    have h1 := hx (e q)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply, map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    rw [h2, MulAut.conj_apply, map_inv, inv_inv]
  refine ⟨e.symm x⁻¹, hαg, ?_⟩
  rintro ⟨k, hk⟩
  have : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.J1_simple
  have hsimp : IsSimpleGroup Q := e.isSimpleGroup
  have hnab : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative Q := ⟨⟨hcon⟩⟩
    have hp := Group.is_simple_iff_prime_card.mp hsimp
    rw [Nat.card_congr e₀.toEquiv, F134.card_carrier_J1] at hp
    norm_num at hp
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center Q := by rw [h0]; exact Subgroup.mem_top b
      exact hab ((Subgroup.mem_center_iff.mp hb a).symm ▸ rfl)
  set g := e.symm x⁻¹ with hg
  have hgk : g ^ 2 ^ k = 1 := by
    have h1 : MulAut.conj (g ^ 2 ^ k) = 1 := by rw [map_pow, ← hαg, hk]
    have h2 : g ^ 2 ^ k ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h3 := congrArg (fun φ : MulAut Q => φ q) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc q * g ^ 2 ^ k = (g ^ 2 ^ k * q * (g ^ 2 ^ k)⁻¹) * g ^ 2 ^ k := by rw [h3]
        _ = g ^ 2 ^ k * q := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hgN : g ∈ Subgroup.normalizer (P : Set Q) :=
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr (hαg ▸ hαP)
  have hg2 : IsPGroup 2 (Subgroup.zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (g ^ m) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgk, one_zpow]
  have hP2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers g) :=
    IsPGroup.to_sup_of_normal_left' hP.2.1 hg2 (Subgroup.zpowers_le.mpr hgN)
  have h1 := hP.eq_of_le le_sup_left le_top hP2
  rw [← h1]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

end CFSG.Quasithin.H13
