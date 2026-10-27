module

public import CFSG.RankThree.GF2n.Smith81.S81WIrrD6
public import CFSG.RankThree.GF2n.Smith81.S81D6Model
public import CFSG.RankThree.GF2n.Stroth80.Sec1111NotTI
public import CFSG.RankThree.GF2n.Smith81.ESetup

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def ETacitE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ B' : Subgroup G, Ctx M Q Z B' →
      NoA2 Q Z (LB M Q B') ∧ GenByB M Q B'

@[expose] def ETacitE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ B' : Subgroup G, Ctx M Q Z B' →
      NoA2 Q Z (LB M Q B') ∧ GenByB M Q B'

section E4

variable {G : Type} [Group G]

private theorem quad_pi_one' {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem quad_pi_inv' {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {x : G} (hx : x ∈ Q) : M₀.π x⁻¹ = -M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, quad_pi_one'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem noA2All_of_inCaseE4_uniform [Finite G] (hFE1 : D6Spin.Smith24E4UniformStatement)
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (h4 : InCaseE4 M Q Z B) : NoA2All M Q Z := by
  obtain ⟨t, -, hQ, -⟩ := id h4
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  have hQZ : Q ≠ Z := by
    intro h
    have h1 : Nat.card Z ^ 33 = Nat.card Z ^ 1 := by
      rw [pow_one, ← hQ, h]
    have := Nat.pow_right_injective hq2 h1
    omega
  obtain ⟨h1, -⟩ := hc.toCfg.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, -, -⟩ | ⟨-, hA | hVI⟩
  ·
    exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    omega
  ·
    exact hA.1
  ·
    exfalso
    have hw : Width Q Z 16 := hQ
    obtain ⟨K₁, _, _, -, φ₁, -, -, V₁, V₂, hZ1, h1Q, -, -, hinf, hsup, hA1, -, x, hxM, hx⟩ :=
      caseVICore_of_caseVI hc.ctx hw hVI
    obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
    obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h4 K γ M₀ hg
    let T : AddSubgroup (D6Spin.W K) :=
      { carrier := {e | ∃ v ∈ V₁, ψ (M₀.π v) = e}
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a * b, V₁.mul_mem ha hb, by rw [M₀.π_mul a (h1Q ha) b (h1Q hb), map_add]⟩
        zero_mem' := ⟨1, V₁.one_mem, by rw [quad_pi_one', map_zero]⟩
        neg_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨a⁻¹, V₁.inv_mem ha, by rw [quad_pi_inv' M₀ (h1Q ha), map_neg]⟩ }
    have hT : ∀ g ∈ D6Spin.LamW K, ∀ s ∈ T, (g : Module.End K (D6Spin.W K)) s ∈ T := by
      rintro g hgL _ ⟨v, hv, rfl⟩
      have hγ : D6Spin.vAut0 K g ∈ φ.range := by
        rw [d.range]
        exact Subgroup.mem_map_of_mem (D6Spin.vAut0 K).toMonoidHom hgL
      obtain ⟨s, hs⟩ := hγ
      refine ⟨(s : G) * v * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hA1.1 s.2) v).mp hv, ?_⟩
      rw [d.equivariant s v (h1Q hv), hs]
      rfl
    rcases D6Spin.LamW_irreducible_W T hT with hbot | htop
    ·
      have hV1 : V₁ ≤ Z := fun v hv => by
        have h0 : ψ (M₀.π v) ∈ T := ⟨v, hv, rfl⟩
        rw [hbot, AddSubgroup.mem_bot, LinearEquiv.map_eq_zero_iff] at h0
        exact (M₀.π_ker v (h1Q hv)).mp h0
      have hV1Z : V₁ = Z := le_antisymm hV1 hZ1
      have hV2 : V₂ = Z := by rw [← hx, hV1Z, hc.ctx.conj_Z_eq hxM]
      exact hQZ (by rw [← hsup, hV1Z, hV2, sup_idem])
    ·
      have hQV1 : Q ≤ V₁ := fun y hy => by
        have hmem : ψ (M₀.π y) ∈ T := by
          rw [htop]
          exact AddSubgroup.mem_top _
        obtain ⟨v, hv, he⟩ := hmem
        have e' : M₀.π v = M₀.π y := ψ.injective he
        have hz : y * v⁻¹ ∈ Z := (M₀.π_ker _ (Q.mul_mem hy (Q.inv_mem (h1Q hv)))).mp (by
          rw [M₀.π_mul y hy v⁻¹ (Q.inv_mem (h1Q hv)), quad_pi_inv' M₀ (h1Q hv), e',
            add_neg_cancel])
        have hy' : y = (y * v⁻¹) * v := by group
        rw [hy']
        exact V₁.mul_mem (hZ1 hz) hv
      have hV1Q : V₁ = Q := le_antisymm h1Q hQV1
      have hV2 : V₂ = Q := by rw [← hx, hV1Q, hc.ctx.conj_Q_eq hxM]
      exact hQZ (by rw [← hinf, hV1Q, hV2, inf_idem])

theorem eTacitE4_of_uniform (hFE1 : D6Spin.Smith24E4UniformStatement)
    (hGen : StrothGenByBStatement) : ETacitE4Statement := by
  intro G _ _ M Q Z B IH hc h4 B' hB'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_inCaseE4_uniform hFE1 IH hc h4 B' hB'.conj hB'.le hB'.ne
  obtain ⟨-, -, hQ, -⟩ := h4
  have hw : Width Q Z 16 := by simpa [Width] using hQ
  exact ⟨hno, hGen G M Q Z B' hB' 16 hw (by norm_num) hno⟩

end E4

end CFSG.RankThree.GF2n.Smith81
