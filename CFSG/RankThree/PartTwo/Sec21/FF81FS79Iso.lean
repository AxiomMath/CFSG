module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fix
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Dich
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79KD

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem isPGroup_two_zpowers_of_sq {G : Type} [Group G] {w : G} (hw : w * w = 1) :
    IsPGroup 2 (Subgroup.zpowers w) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨x, hx⟩ := x
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  have hw2 : w ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((2 : ℕ) : ℤ) = 2 from rfl, hw2,
    one_zpow]

theorem fusion_weakly_closed {G : Type} [Group G] [Finite G] {P A : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) (hA2 : IsPGroup 2 A)
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hweak : ∀ g : G, (∀ a ∈ A, g * a * g⁻¹ ∈ P) → g ∈ Nor A) {x g : G} (hx : x ∈ A)
    (hgx : g * x * g⁻¹ ∈ A) : ∃ n ∈ Nor A, n * x * n⁻¹ = g * x * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : G := g * x * g⁻¹ with hu
  have hAu : A ≤ Cen u := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a ha u hgx)
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'2 : IsPGroup 2 A' := hA2.map _
  have hA'u : A' ≤ Cen u := by
    rintro _ ⟨a, ha, rfl⟩
    have hce : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := by simp [MulAut.conj_apply]
    rw [hce, Subgroup.mem_centralizer_singleton_iff, hu]
    calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [hAcomm a ha x hx]
      _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (Cen u)
  obtain ⟨c₁, hc₁, hc₁Q⟩ := exists_conj_le_abg hQ hAu hA2
  obtain ⟨c₂, hc₂, hc₂Q⟩ := exists_conj_le_abg hQ hA'u hA'2
  obtain ⟨y, -, hy⟩ := exists_conj_le_abg hP (le_top : Q ≤ ⊤)
    (CFSG.ABGLocalTools.IsSylowOf.isPGroup hQ)
  have h1 : y * c₁ ∈ Nor A := hweak _ fun a ha => by
    have := hy _ (hc₁Q a ha)
    simpa [mul_assoc] using this
  have h2 : y * c₂ * g ∈ Nor A := hweak _ fun a ha => by
    have hce : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := by simp [MulAut.conj_apply]
    have := hy _ (hc₂Q _ ⟨a, ha, rfl⟩)
    rw [hce] at this
    simpa [mul_assoc] using this
  have hc₁u : c₁ * u = u * c₁ := Subgroup.mem_centralizer_singleton_iff.mp hc₁
  have hc₂u : c₂ * u = u * c₂ := Subgroup.mem_centralizer_singleton_iff.mp hc₂
  refine ⟨c₁⁻¹ * c₂ * g, ?_, ?_⟩
  · have : c₁⁻¹ * c₂ * g = (y * c₁)⁻¹ * (y * c₂ * g) := by group
    rw [this]
    exact (Nor A).mul_mem ((Nor A).inv_mem h1) h2
  · calc c₁⁻¹ * c₂ * g * x * (c₁⁻¹ * c₂ * g)⁻¹ = c₁⁻¹ * (c₂ * (g * x * g⁻¹) * c₂⁻¹) * c₁ := by
          group
      _ = c₁⁻¹ * (c₂ * u * c₂⁻¹) * c₁ := by rw [← hu]
      _ = c₁⁻¹ * u * c₁ := by rw [hc₂u]; group
      _ = c₁⁻¹ * (u * c₁) := by group
      _ = c₁⁻¹ * (c₁ * u) := by rw [hc₁u]
      _ = u := by group


namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem t_mem_Nor_frame (A₁ : Subgroup J6.S6) : t ∈ Nor (S.frame A₁) := by
  refine mem_Nor_of_comm_all fun y hy => ?_
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ y).mp hy
  · exact (S.ι_comm_t s).symm
  · calc t * (t * S.ι s) = t * (S.ι s * t) := by rw [S.ι_comm_t s]
      _ = (t * S.ι s) * t := by group

theorem frame_R_le_Nor_frame {A₁ : Subgroup J6.S6}
    (hRN : ∀ r ∈ J6.R, ∀ s ∈ A₁, r * s * r⁻¹ ∈ A₁) : S.frame J6.R ≤ Nor (S.frame A₁) := by
  have hι : ∀ r ∈ J6.R, S.ι r ∈ Nor (S.frame A₁) := by
    intro r hr
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ y).mp hy
    · rw [← map_mul, ← map_inv, ← map_mul]
      exact S.ι_mem_frame (hRN r hr s hs)
    · have e : S.ι r * (t * S.ι s) * (S.ι r)⁻¹ = t * S.ι (r * s * r⁻¹) := by
        calc S.ι r * (t * S.ι s) * (S.ι r)⁻¹ = (S.ι r * t) * S.ι s * (S.ι r)⁻¹ := by group
          _ = (t * S.ι r) * S.ι s * (S.ι r)⁻¹ := by rw [S.ι_comm_t r]
          _ = t * (S.ι r * S.ι s * (S.ι r)⁻¹) := by group
          _ = t * S.ι (r * s * r⁻¹) := by rw [S.ι_conj]
      rw [e]
      exact S.t_ι_mem_frame (hRN r hr s hs)
  intro x hx
  obtain ⟨r, hr, rfl | rfl⟩ := (S.mem_frame_iff J6.R x).mp hx
  · exact hι r hr
  · exact (Nor (S.frame A₁)).mul_mem (S.t_mem_Nor_frame A₁) (hι r hr)

theorem conj_frame_props {A₁ : Subgroup J6.S6} (hsq : ∀ s ∈ A₁, s * s = 1)
    (hcomm : ∀ a ∈ A₁, ∀ c ∈ A₁, a * c = c * a) (hcard : Nat.card A₁ = 8) (g : H) :
    Nat.card (conjBy g (S.frame A₁)) = 16 ∧ (∀ x ∈ conjBy g (S.frame A₁), x * x = 1) ∧
      (∀ x ∈ conjBy g (S.frame A₁), ∀ y ∈ conjBy g (S.frame A₁), x * y = y * x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_frame, hcard]
  · rintro _ ⟨a, ha, rfl⟩
    rw [conj_hom_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [S.frame_sq hsq a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [conj_hom_apply, conj_hom_apply]
    calc g * a * g⁻¹ * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
      _ = g * (c * a) * g⁻¹ := by rw [S.frame_comm hcomm a ha c hc]
      _ = g * c * g⁻¹ * (g * a * g⁻¹) := by group


theorem isolated_of_frame (A₁ A₁' : Subgroup J6.S6) (hAR : A₁ ≤ J6.R)
    (hsq : ∀ s ∈ A₁, s * s = 1) (hcomm : ∀ a ∈ A₁, ∀ c ∈ A₁, a * c = c * a)
    (hcard : Nat.card A₁ = 8) (hN : Nat.card (Nor A₁) = 48)
    (hRN : ∀ r ∈ J6.R, ∀ s ∈ A₁, r * s * r⁻¹ ∈ A₁)
    (hconj : ∀ r ∈ J6.R, r * r = 1 → ∃ γ : J6.S6, γ * r * γ⁻¹ ∈ A₁)
    (hE16 : ∀ X : Subgroup H, X ≤ S.frame J6.R → Nat.card X = 16 → (∀ x ∈ X, x * x = 1) →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X = S.frame A₁ ∨ X = S.frame A₁')
    (hnc : ∀ g : H, conjBy g (S.frame A₁) ≠ S.frame A₁')
    (hXi : S.Xi A₁) (h38 : R38Stmt b (A₁.map S.ι)) :
    ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := S.hyp
  have hAP : S.frame A₁ ≤ S.frame J6.R := S.frame_mono hAR
  have hAcard : Nat.card (S.frame A₁) = 16 := by rw [S.card_frame, hcard]
  have hA2 : IsPGroup 2 (S.frame A₁) :=
    IsPGroup.of_card (n := 4) (by rw [hAcard]; norm_num)
  have hAcomm := S.frame_comm hcomm
  have hconjA : ∀ g : H, conjBy g (S.frame A₁) ≤ S.frame J6.R →
      conjBy g (S.frame A₁) = S.frame A₁ := by
    intro g hg
    obtain ⟨hc, hs, hco⟩ := S.conj_frame_props hsq hcomm hcard g
    rcases hE16 _ hg hc hs hco with h1 | h1
    · exact h1
    · exact absurd h1 (hnc g)
  have hnorm_of_eq : ∀ g : H, conjBy g (S.frame A₁) = S.frame A₁ → g ∈ Nor (S.frame A₁) := by
    intro g heq
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have : g * a * g⁻¹ ∈ conjBy g (S.frame A₁) := ⟨a, ha, conj_hom_apply g a⟩
    rw [heq] at this
    exact this
  have hweak : ∀ g : H, (∀ a ∈ S.frame A₁, g * a * g⁻¹ ∈ S.frame J6.R) → g ∈ Nor (S.frame A₁) := by
    intro g hg
    refine hnorm_of_eq g (hconjA g ?_)
    rintro _ ⟨a, ha, rfl⟩
    rw [conj_hom_apply]
    exact hg a ha
  have hPN : S.frame J6.R ≤ Nor (S.frame A₁) := S.frame_R_le_Nor_frame hRN
  have hSylNA₁ := S.isSylowOf_Nor_A₁H A₁ hN hRN h38
  have hSylNA : CFSG.ABGLocalTools.IsSylowOf 2 (S.frame J6.R) (Nor (S.frame A₁)) :=
    hSylNA₁.of_le hPN hXi
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 (S.frame J6.R) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (H := Nor (S.frame A₁)) (M := ⊤)
      ?_ ?_
    · rw [inf_top_eq]
      exact hSylNA
    · intro x hx
      refine hnorm_of_eq x (hconjA x ?_)
      rintro _ ⟨a, ha, rfl⟩
      rw [conj_hom_apply]
      exact (Subgroup.mem_normalizer_iff.mp hx.1 a).mp (hAP ha)
  have hfus : ∀ g : H, g * t * g⁻¹ ∈ S.frame A₁ →
      ∃ n ∈ Nor (S.frame A₁), n * t * n⁻¹ = g * t * g⁻¹ := fun g hg =>
    fusion_weakly_closed hPsyl hA2 hAcomm hweak (S.t_mem_frame A₁) hg
  have hF : ∀ x : H, x * t * x⁻¹ ∈ S.frame J6.R → x * t * x⁻¹ = t := by
    intro x hx
    set u : H := x * t * x⁻¹ with hu
    have hu2 : u * u = 1 := by
      rw [hu]
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [h.t_sq]; group
    have key : ∀ γ : J6.S6, ∀ r : J6.S6, γ * r * γ⁻¹ ∈ A₁ →
        (S.ι γ * u * (S.ι γ)⁻¹ ∈ S.frame A₁) → S.ι γ * u * (S.ι γ)⁻¹ = t := by
      intro γ r hγ hvA
      have hvt : S.ι γ * u * (S.ι γ)⁻¹ = (S.ι γ * x) * t * (S.ι γ * x)⁻¹ := by
        rw [hu]
        group
      obtain ⟨n, hn, hnt⟩ := hfus (S.ι γ * x) (by rw [← hvt]; exact hvA)
      have hfix := S.t_fix hsq h38 (hXi n hn) (by rw [hnt, ← hvt]; exact hvA)
      rw [hvt, ← hnt]
      exact hfix
    obtain ⟨r, hr, hur | hur⟩ := (S.mem_frame_iff J6.R u).mp hx
    · exfalso
      have hrr : r * r = 1 := S.ι_injective (by rw [map_mul, ← hur, hu2, map_one])
      obtain ⟨γ, hγ⟩ := hconj r hr hrr
      have hv : S.ι γ * u * (S.ι γ)⁻¹ = S.ι (γ * r * γ⁻¹) := by rw [hur, S.ι_conj]
      have := key γ r hγ (by rw [hv]; exact S.ι_mem_frame hγ)
      apply h.t_not_mem_J
      rw [← this, hv]
      exact S.ι_mem _
    · have hrr : r * r = 1 := by
        apply S.ι_injective
        rw [map_one, ← S.tι_mul_self, ← hur]
        exact hu2
      obtain ⟨γ, hγ⟩ := hconj r hr hrr
      have hv : S.ι γ * u * (S.ι γ)⁻¹ = t * S.ι (γ * r * γ⁻¹) := by
        rw [hur]
        calc S.ι γ * (t * S.ι r) * (S.ι γ)⁻¹ = (S.ι γ * t) * S.ι r * (S.ι γ)⁻¹ := by group
          _ = (t * S.ι γ) * S.ι r * (S.ι γ)⁻¹ := by rw [S.ι_comm_t γ]
          _ = t * (S.ι γ * S.ι r * (S.ι γ)⁻¹) := by group
          _ = t * S.ι (γ * r * γ⁻¹) := by rw [S.ι_conj]
      have h1 := key γ r hγ (by rw [hv]; exact S.t_ι_mem_frame hγ)
      rw [hv] at h1
      have h2 : S.ι (γ * r * γ⁻¹) = 1 := by
        have := mul_left_cancel (a := t) (h1.trans (mul_one t).symm)
        exact this
      have h3 : γ * r * γ⁻¹ = 1 := S.ι_injective (h2.trans (map_one S.ι).symm)
      have h4 : r = 1 := by
        calc r = γ⁻¹ * (γ * r * γ⁻¹) * γ := by group
          _ = 1 := by rw [h3]; group
      rw [hur, h4, map_one, mul_one]
  intro g hgcomm
  set t' : H := g * t * g⁻¹ with ht'
  have ht'2 : t' * t' = 1 := by
    rw [ht']
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_sq]; group
  have hQ2 : IsPGroup 2 (Subgroup.zpowers t ⊔ Subgroup.zpowers t' : Subgroup H) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_two_zpowers_of_sq h.t_sq)
      (isPGroup_two_zpowers_of_sq ht'2)
      (Subgroup.zpowers_le.mpr (mem_Nor_zpowers_of_comm hgcomm))
  obtain ⟨y, -, hy⟩ := exists_conj_le_abg hPsyl le_top hQ2
  have h1 : y * t * y⁻¹ ∈ S.frame J6.R := hy t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have h2 : y * t' * y⁻¹ ∈ S.frame J6.R := hy t' (Subgroup.mem_sup_right (Subgroup.mem_zpowers t'))
  have e1 := hF y h1
  have e2 : (y * g) * t * (y * g)⁻¹ = t := by
    apply hF
    have : (y * g) * t * (y * g)⁻¹ = y * t' * y⁻¹ := by rw [ht']; group
    rw [this]
    exact h2
  have e3 : y * t' * y⁻¹ = t := by
    rw [← e2, ht']
    group
  calc t' = y⁻¹ * (y * t' * y⁻¹) * y := by group
    _ = y⁻¹ * t * y := by rw [e3]
    _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [e1]
    _ = t := by group

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
