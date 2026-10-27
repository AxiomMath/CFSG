module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.Quasithin.H13.A6S1372L76R
public import CFSG.Quasithin.H13.A7Nat1233ModAbs
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1Orbit
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.A6S1372L76Q
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_a7Four_of_s15_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 1) : False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  have hW2 : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hW2mul : ∀ w : W, w * w = 1 := fun w => by simpa [pow_two] using hW2 w
  have hcomm : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have htop : commV H = ⊤ := by
    rw [commV_eq_commSub]
    exact hcomm
  have hrowV : A7Four H (commV H) (fixV H ⊓ commV H) := by
    simpa [H, W, hcomm, commV_eq_commSub, inf_comm] using hrow
  have hfixbot : fixV H = ⊥ :=
    CFSG.Quasithin.H13.A6.A6L76R.fixV_eq_bot_of_a7Four W H hW2mul htop hrowV
  have hrowTopBot : A7Four H ⊤ ⊥ := by
    simpa [H, hcomm, hfixbot] using hrow
  have hcardH : Nat.card ↥H = 2520 :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four hrowTopBot
  have hWcard : Nat.card W = 2 ^ 4 := by
    have h16 := CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four_bot
      (V := W) (L := H) (U := ⊤) hrowTopBot
    rw [Subgroup.card_top] at h16
    rw [h16]
    norm_num
  have hHA : H ≤ A := by
    simpa [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs ha)
  have hAH : A ≤ H := by
    intro a ha
    exact CFSG.Quasithin.H13.A7.mem_of_mem_normalizer_four hW2mul hWcard hcardH (hAN ha)
  have hAeqH : A = H := le_antisymm hAH hHA
  have hcardA : Nat.card ↥A = 2520 := by
    rw [hAeqH]
    exact hcardH
  have hsig3 : 3 ∈ D.sig := by
    obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
    have hp : p.Prime := (D.sig_prime p hpσ).1
    have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
    have h2rank : 2 ≤ CFSG.Open.pRank p A := c.two_le_pRank_mbar hpσ
    obtain ⟨E, hEA, -, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2)
        (hp := ⟨hp⟩) h2rank
    have hdvd : p ^ 2 ∣ Nat.card ↥A := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le hEA
    rw [hcardA] at hdvd
    have hle : p ^ 2 ≤ 2520 := Nat.le_of_dvd (by norm_num) hdvd
    have hp50 : p ≤ 50 := by
      by_contra h
      have h51 : 51 ≤ p := by omega
      have hle' : 51 ^ 2 ≤ p ^ 2 := pow_le_pow_left' h51 2
      norm_num at hle'
      omega
    have hcheck : ∀ q : Fin 51, (q : ℕ).Prime → (q : ℕ) ≠ 2 → (q : ℕ) ^ 2 ∣ 2520 →
        (q : ℕ) = 3 := by decide
    have hp3 : p = 3 := hcheck ⟨p, by omega⟩ hp hp2 hdvd
    rw [hp3] at hpσ
    exact hpσ
  have hfixA : ∀ x : W, x ≠ 1 → ∃ b ∈ A, orderOf b = 3 ∧ b x = x := by
    obtain ⟨α, π, hπ⟩ := hrowTopBot
    have hπinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFC.a7Four_faithful α) hπ
    let θ : ↥(alternatingGroup (Fin 7)) →* MulAut W := H.subtype.comp π
    have hθinj : Function.Injective θ := by
      intro a b hab
      apply hπinj
      apply Subtype.ext
      show (π a : MulAut W) = (π b : MulAut W)
      exact hab
    let _ : MulAction ↥(alternatingGroup (Fin 7)) W := MulAction.compHom W θ
    have hact : ∀ (g : ↥(alternatingGroup (Fin 7))) (u : W), g • u = θ g u :=
      fun _ _ => rfl
    have h0 : ∀ g : ↥(alternatingGroup (Fin 7)), g • (1 : W) = 1 := fun g => by
      rw [hact, map_one]
    intro x hx
    have hW16 : Nat.card W = 16 := by
      rw [hWcard]
      norm_num
    have h3dvd : 3 ∣ Nat.card (MulAction.stabilizer ↥(alternatingGroup (Fin 7)) x) :=
      CFSG.AGLEmbeddingD2.GN.three_dvd_card_stabilizer_of_card_sixteen hW16 (1 : W) h0 hx
    obtain ⟨σ, hσord⟩ :=
      exists_prime_orderOf_dvd_card' 3 (hp := ⟨Nat.prime_three⟩) h3dvd
    refine ⟨θ (σ : ↥(alternatingGroup (Fin 7))), hHA (π (σ : ↥(alternatingGroup (Fin 7)))).2,
      ?_, ?_⟩
    · rw [orderOf_injective θ hθinj (σ : ↥(alternatingGroup (Fin 7))), Subgroup.orderOf_coe,
        hσord]
    · show θ (σ : ↥(alternatingGroup (Fin 7))) x = x
      rw [← hact]
      exact σ.2
  have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥A := by
    rw [hcardA]
    norm_num
  have hk : S168e3Kernel A 3 := s168e3_kernel_of_cube Nat.prime_three A hcube hfixA
  exact s168e3_false_of_kernel c Nat.prime_three hsig3 hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
