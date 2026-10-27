module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Beta
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Pre
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Cb

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem s43_Bcomm {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
  congrArg Subtype.val (h4.mono.1.1.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem s43_hbB {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) : b ∈ B :=
  h4.mono.2.1 ▸ Subgroup.subset_closure (by simp)

theorem s43_cenS_of {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) {c : G}
    (hb : c * b = b * c) (h1 : c * b₁ = b₁ * c) (h2 : c * b₂ = b₂ * c) : c ∈ CenS B := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have : B ≤ Cen c := by
    rw [h4.mono.2.1, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact s43_mem_cen hb
    · exact s43_mem_cen h1
    · exact s43_mem_cen h2
  exact (s43_cen_comm (this hx)).symm

theorem s43_gen {z b₁ b₂ : G} (h1 : z * (b₁ * b₂) = (b₁ * b₂) * z)
    (h2 : z * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * z) : z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := by
  have c1 : Commute z (b₁ * b₂) := h1
  have c2 : Commute z (b₁ ^ 2 * b₂) := h2
  have e1 : b₁ = (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ := by group
  have d1 : Commute z b₁ := by rw [e1]; exact c2.mul_right c1.inv_right
  refine ⟨d1.eq, ?_⟩
  have e2 : b₂ = b₁⁻¹ * (b₁ * b₂) := by group
  have d2 : Commute z b₂ := by rw [e2]; exact d1.inv_right.mul_right c1
  exact d2.eq

theorem s43_beta_gamma {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    (b₁ * b₂) ^ 3 = 1 ∧ orderOf (b₁ ^ 2 * b₂) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb₁3, hb₂3, hb₁b₂, hK1, -, -⟩ := sec4_facts h4
  have hc : Commute b₁ b₂ := hb₁b₂
  refine ⟨by rw [hc.mul_pow, hb₁3, hb₂3, one_mul], ?_⟩
  have h3 : (b₁ ^ 2 * b₂) ^ 3 = 1 := by
    rw [(hc.pow_left 2).mul_pow, ← pow_mul, mul_comm, pow_mul, hb₁3, hb₂3, one_pow, one_mul]
  refine orderOf_eq_prime h3 ?_
  intro h
  apply hK1
  have h' : b₂ = (b₁ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
  have : (b₁ ^ 2)⁻¹ = b₁ := by
    rw [inv_eq_of_mul_eq_one_right (a := b₁ ^ 2) (b := b₁)]
    rw [← pow_succ]; exact hb₁3
  rw [h', this]; exact Subgroup.mem_zpowers b₁

theorem good_beta {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hX : Odd (Nat.card (Opp 3 (Cen b)))) (e : J ≃* GL (Fin 5) (ZMod 2))
    (hF5 : FF79KAut5Fix) (hA5 : FF79KO2A5) (hL3 : FF79KO2L3) (h42 : FF79_4_2Pre)
    {σ : G} (hσB : σ ∈ CenS B) (hσo : orderOf σ = 2) : Good43 σ (b₁ * b₂) := by
  have hdvd := two_pow_dvd_cenB h4 hX e hF5
  have h := h42 G b J B b₁ b₂ h4
  dsimp only at h
  obtain ⟨⟨hsup, hinf⟩, -, hK, hL, hbL, hγK, hLay, hKL, hKcL, hdec, -, -⟩ := h
  obtain ⟨eK⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck155.nonempty_mulEquiv_alt5_of_statedClassicalModel hK
  obtain ⟨eL⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two hL
  obtain ⟨hβ3, hγ3⟩ := s43_beta_gamma h4
  have hbB : b ∈ B := s43_hbB h4
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hβB : b₁ * b₂ ∈ B := B.mul_mem hb₁B hb₂B
  have hγB : b₁ ^ 2 * b₂ ∈ B := B.mul_mem (B.pow_mem hb₁B 2) hb₂B
  have hσc : ∀ x ∈ B, x * σ = σ * x := fun x hx => Subgroup.mem_centralizer_iff.mp hσB x hx
  have hσ2 : σ * σ = 1 := by rw [← pow_two]; exact hσo ▸ pow_orderOf_eq_one σ
  have hHβ : OUp 3 (Cen (b₁ * b₂)) ≤ Cen (b₁ * b₂) := Subgroup.map_subtype_le _
  have hσβ : σ ∈ Cen (b₁ * b₂) := s43_mem_cen (hσc _ hβB)
  have hσH : σ ∈ OUp 3 (Cen (b₁ * b₂)) :=
    mem_H_of_2el hβ3 hHβ hsup hinf hσβ ⟨1, by simpa [pow_two] using hσ2⟩
  have hσb : σ * b = b * σ := (hσc b hbB).symm
  have hσγ : σ * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * σ := (hσc _ hγB).symm
  have hDB : OUp 3 (Cen (b₁ * b₂)) ⊓ CenS (Subgroup.closure ({b, b₁ ^ 2 * b₂} : Set G)) ≤
      CenS B := by
    intro c hc
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcb : c * b = b * c :=
      (Subgroup.mem_centralizer_iff.mp hcC b (Subgroup.subset_closure (by simp))).symm
    have hcγ : c * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * c :=
      (Subgroup.mem_centralizer_iff.mp hcC _ (Subgroup.subset_closure (by simp))).symm
    have hcβ : c * (b₁ * b₂) = (b₁ * b₂) * c := (s43_cen_comm (hHβ hcH)).symm
    obtain ⟨hc1, hc2⟩ := s43_gen hcβ hcγ
    exact s43_cenS_of h4 hcb hc1 hc2
  refine good_beta_core (γ := b₁ ^ 2 * b₂) (b := b)
    (D := OUp 3 (Cen (b₁ * b₂)) ⊓ CenS (Subgroup.closure ({b, b₁ ^ 2 * b₂} : Set G))) hβ3 hHβ
    hsup hinf
    ((lay_le _).trans inf_le_left) ((lay_le _).trans inf_le_left) hLay hKL hKcL inf_le_left
    (fun x hx => by
      have hx' : x ∈ (↑(OUp 3 (Cen (b₁ * b₂))) : Set G) := hx
      rw [← hdec] at hx'; exact hx') ?_ eK eL hγK hγ3 hbL h4.hyp.ord hσo hσβ hσγ hσb
    (lay_mem_nor (Subgroup.mem_inf.mpr ⟨hσH, s43_mem_cen hσb.symm⟩))
    (lay_mem_nor (Subgroup.mem_inf.mpr ⟨hσH, s43_mem_cen hσγ.symm⟩)) hA5 hL3
  intro k hk
  exact hdvd k ((hk.trans (Subgroup.card_dvd_of_le hDB)))

end CFSG.RankThree.PartTwo.Sec21.FF79
