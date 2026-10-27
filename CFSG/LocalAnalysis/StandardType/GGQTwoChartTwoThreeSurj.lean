module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

private theorem qTwoChartTwoThree_diag_one :
    qTwoChartTwoThree_diag (1 : Fin m → F0ˣ) = 1 := by
  apply Units.ext
  simp only [Units.val_one, qTwoChartTwoThree_diag]
  rw [← Matrix.diagonal_one]
  congr 1

private theorem qTwoChartTwoThree_diag_mul (c c' : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag (c * c') =
      qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag c' := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1

private theorem qTwoChartTwoThree_diag_inv (c : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag c⁻¹ = (qTwoChartTwoThree_diag c)⁻¹ := by
  have h : qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag c⁻¹ = 1 := by
    rw [← qTwoChartTwoThree_diag_mul, mul_inv_cancel, qTwoChartTwoThree_diag_one]
  exact eq_inv_of_mul_eq_one_right h

private theorem qTwoChartTwoThree_diag_const_comm (t : F0ˣ) (u : GL (Fin m) F0) :
    qTwoChartTwoThree_diag (fun _ : Fin m => t) * u =
      u * qTwoChartTwoThree_diag (fun _ : Fin m => t) := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private def qTwoChartTwoThree_graph (hF0 : Nat.card F0 = 4) (Bs : Subgroup G)
    (ψ : Su F0 2 1 m →* G) : Subgroup (↥Bs × (Fin m → F0ˣ)) where
  carrier := {p | qTwoChartTwoThree_induces ψ (p.1 : G) p.2}
  mul_mem' := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hp hq u
    obtain ⟨u₁, hu₁v, hu₁ψ⟩ := hq u
    obtain ⟨u₂, hu₂v, hu₂ψ⟩ := hp u₁
    refine ⟨u₂, ?_, ?_⟩
    · rw [hu₂v, hu₁v]
      simp only [Prod.snd_mul]
      rw [qTwoChartTwoThree_diag_mul]
      group
    · rw [hu₂ψ, hu₁ψ]
      simp only [Prod.fst_mul]
      rw [Subgroup.coe_mul]
      group
  one_mem' := by
    intro u
    have h1 : (1 : ↥Bs × (Fin m → F0ˣ)).2 = (1 : Fin m → F0ˣ) := rfl
    exact ⟨u, by rw [h1, qTwoChartTwoThree_diag_one]; group, by simp⟩
  inv_mem' := by
    rintro ⟨b, c⟩ hp u
    obtain ⟨u₀, hu₀v⟩ := qTwoChartTwoThree_diag_conj_mem hF0 c⁻¹ u
    obtain ⟨u₂, hu₂v, hu₂ψ⟩ := hp u₀
    have hu₂u : u₂ = u := by
      apply Subtype.ext
      rw [hu₂v, hu₀v, qTwoChartTwoThree_diag_inv]
      group
    have hψ : ψ u = (b : G) * ψ u₀ * (b : G)⁻¹ := by
      rw [← hu₂u]
      exact hu₂ψ
    refine ⟨u₀, hu₀v, ?_⟩
    change ψ u₀ = (↑(b⁻¹) : G) * ψ u * (↑(b⁻¹) : G)⁻¹
    rw [Subgroup.coe_inv, hψ]
    group

theorem qTwoChartTwoThree_centralizer_card_le (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) :
    Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u} ≤ 3 := by
  let f : {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u} →
      ↥(Subgroup.zpowers x) := fun b =>
    ⟨(b.1 : G), S.hLocal.fixed b.1 (by
      intro a ha
      rw [mem_ggAutomizer_iff] at ha
      obtain ⟨g, hgL, -, hg⟩ := ha
      rw [← hψ.1] at hgL
      obtain ⟨u₀, rfl⟩ := hgL
      apply Subtype.ext
      have h2 := b.2 u₀
      have h1 : (b.1 : G) * ψ u₀ = ψ u₀ * (b.1 : G) := by
        calc (b.1 : G) * ψ u₀
            = (b.1 : G) * ψ u₀ * (b.1 : G)⁻¹ * (b.1 : G) := by group
          _ = ψ u₀ * (b.1 : G) := by rw [h2]
      rw [hg, ← h1]
      group)⟩
  have hf : Function.Injective f := by
    intro b b' h
    apply Subtype.ext
    apply Subtype.ext
    have hpair : (f b).1 = (f b').1 := Subtype.ext_iff.mp h
    exact hpair
  calc Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u}
      ≤ Nat.card ↥(Subgroup.zpowers x) := Nat.card_le_card_of_injective f hf
    _ = orderOf x := Nat.card_zpowers x
    _ ≤ 3 := Nat.le_of_dvd (by norm_num) <|
        orderOf_dvd_of_pow_eq_one (S.hLocal.elemAb.2 x S.hLocal.mem)

theorem qTwoChartTwoThree_exists_induces_aux (hF0 : Nat.card F0 = 4) (hm : 0 < m)
    {Bs : Subgroup G} (ψ : Su F0 2 1 m →* G)
    (hdiag : ∀ b : ↥Bs, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (b : G) c)
    (hcard : Nat.card ↥Bs = 3 ^ m)
    (hcent : Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u} ≤ 3)
    (c : Fin m → F0ˣ) : ∃ b : ↥Bs, qTwoChartTwoThree_induces ψ (b : G) c := by
  classical
  have hcardF0 : Nat.card F0ˣ = 3 := by
    rw [Nat.card_units F0, hF0]
  have hcardD : Nat.card (Fin m → F0ˣ) = 3 ^ m := by
    rw [Nat.card_fun, hcardF0, Nat.card_fin]
  let Γ : Subgroup (↥Bs × (Fin m → F0ˣ)) := qTwoChartTwoThree_graph hF0 Bs ψ
  let φ₁ : Γ →* ↥Bs := (MonoidHom.fst ↥Bs (Fin m → F0ˣ)).comp Γ.subtype
  let φ₂ : Γ →* (Fin m → F0ˣ) :=
    (MonoidHom.snd ↥Bs (Fin m → F0ˣ)).comp Γ.subtype
  have hsurj₁ : Function.Surjective φ₁ := by
    intro b
    obtain ⟨c', hc'⟩ := hdiag b
    exact ⟨⟨(b, c'), hc'⟩, rfl⟩
  have hΓ₁ : Nat.card Γ = Nat.card φ₁.ker * Nat.card ↥Bs :=
    (Subgroup.card_ker_mul_card_of_surjective hsurj₁).symm
  have hscal : 3 ≤ Nat.card φ₁.ker := by
    let scal : F0ˣ → Γ := fun t =>
      ⟨((1 : ↥Bs), fun _ : Fin m => t), by
        intro u
        exact ⟨u, by rw [qTwoChartTwoThree_diag_const_comm]; group, by simp⟩⟩
    let scalK : F0ˣ → φ₁.ker :=
      fun t => ⟨scal t, MonoidHom.mem_ker.mpr (by rfl)⟩
    have hinj : Function.Injective scalK := by
      intro t s h
      have h1 : scal t = scal s := Subtype.ext_iff.mp h
      have hp : ((1 : ↥Bs), fun _ : Fin m => t) = ((1 : ↥Bs), fun _ : Fin m => s) := by
        simpa [scal] using congrArg (fun γ : Γ => γ.1) h1
      have h3 : (fun _ : Fin m => t) = (fun _ : Fin m => s) := by
        simpa using congrArg Prod.snd hp
      simpa using congrFun h3 ⟨0, hm⟩
    calc 3 = Nat.card F0ˣ := hcardF0.symm
      _ ≤ Nat.card φ₁.ker := Nat.card_le_card_of_injective scalK hinj
  have hA : 3 * 3 ^ m ≤ Nat.card Γ := by
    rw [hΓ₁, hcard]
    exact Nat.mul_le_mul_right _ hscal
  have hker₂ : Nat.card φ₂.ker ≤ 3 := by
    let g : φ₂.ker →
        {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u} := fun γ =>
      ⟨(γ : Γ).1.1, by
        have h2 : (γ : Γ).1.2 = (1 : Fin m → F0ˣ) := MonoidHom.mem_ker.mp γ.2
        have hγ : qTwoChartTwoThree_induces ψ (((γ : Γ).1.1 : ↥Bs) : G) 1 := by
          rw [← h2]
          exact (γ : Γ).2
        intro u
        obtain ⟨u', hu'v, hu'ψ⟩ := hγ u
        rw [qTwoChartTwoThree_diag_one, one_mul, inv_one, mul_one] at hu'v
        have hu' : u' = u := Subtype.ext hu'v
        rw [hu'] at hu'ψ
        exact hu'ψ.symm⟩
    have hgInj : Function.Injective g := by
      intro γ δ h
      have hfst : ((γ : Γ).1.1) = ((δ : Γ).1.1) := Subtype.ext_iff.mp h
      have h2γ : (γ : Γ).1.2 = (1 : Fin m → F0ˣ) := MonoidHom.mem_ker.mp γ.2
      have h2δ : (δ : Γ).1.2 = (1 : Fin m → F0ˣ) := MonoidHom.mem_ker.mp δ.2
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hfst
      · rw [h2γ, h2δ]
    calc Nat.card φ₂.ker
        ≤ Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m, (b : G) * ψ u * (b : G)⁻¹ = ψ u} :=
          Nat.card_le_card_of_injective g hgInj
      _ ≤ 3 := hcent
  have hB : Nat.card Γ ≤ 3 * Nat.card φ₂.range := by
    rw [← Subgroup.card_ker_mul_card_range φ₂]
    exact Nat.mul_le_mul_right _ hker₂
  have hC : 3 ^ m ≤ Nat.card φ₂.range := by
    have h : 3 * 3 ^ m ≤ 3 * Nat.card φ₂.range := le_trans hA hB
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hD : Nat.card φ₂.range = 3 ^ m := by
    apply le_antisymm
    · calc Nat.card φ₂.range ≤ Nat.card (Fin m → F0ˣ) :=
            Nat.card_le_card_of_injective (fun γ : φ₂.range => (γ : Fin m → F0ˣ))
              Subtype.val_injective
        _ = 3 ^ m := hcardD
    · exact hC
  have htop : φ₂.range = ⊤ :=
    (Subgroup.card_eq_iff_eq_top φ₂.range).mp (hD.trans hcardD.symm)
  have hc_mem : c ∈ φ₂.range := by rw [htop]; exact Subgroup.mem_top c
  obtain ⟨γ, hγc⟩ := hc_mem
  refine ⟨(γ : Γ).1.1, ?_⟩
  have hγ' : (γ : Γ).1.2 = c := hγc
  have hγ : qTwoChartTwoThree_induces ψ (((γ : Γ).1.1 : ↥Bs) : G) c := by
    rw [← hγ']
    exact (γ : Γ).2
  exact hγ

theorem qTwoChartTwoThree_exists_induces (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hF0 : Nat.card F0 = 4) {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ)
    (c : Fin m → F0ˣ) : ∃ b : ↥Bs, qTwoChartTwoThree_induces ψ (b : G) c := by
  exact qTwoChartTwoThree_exists_induces_aux hF0 (Nat.lt_of_lt_of_le (by norm_num) S.hm) ψ
    (fun b => qTwoChartTwoThree_induces_of_ordModel hψ b)
    S.hLocal.card (qTwoChartTwoThree_centralizer_card_le S hψ) c

end CFSG.StandardType.QTwo

end
