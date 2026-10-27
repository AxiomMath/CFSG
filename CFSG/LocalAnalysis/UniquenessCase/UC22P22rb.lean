module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ra
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_isSylowOf_conj {q : ℕ} [Fact q.Prime] {P Y : Subgroup G} (h : IsSylowOf q P Y) (g : G) :
    IsSylowOf q (uniqueFourConj g P) (uniqueFourConj g Y) :=
  CFSG.ABGLocalTools.isSylowOf_of_card (uc22p22r_conj_mono h.le g)
    (by rw [uc22p22r_card_conj, uc22p22r_card_conj]; exact h.card_eq)

theorem uc22p22r_exists_sylow_normalized {q : ℕ} [Fact q.Prime] {P Y E : Subgroup G}
    (hP : IsSylowOf q P Y) (hE : IsPGroup q ↥E) (hEY : E ≤ normalizer (Y : Set G)) :
    ∃ y ∈ Y, E ≤ normalizer ((uniqueFourConj y P : Subgroup G) : Set G) ∧
      ∀ F : Subgroup G, F ≤ E → F ≤ Y → F ≤ uniqueFourConj y P := by
  set K : Subgroup G := E ⊔ Y with hK
  have hYK : Y ≤ K := le_sup_right
  have hKN : K ≤ normalizer (Y : Set G) := sup_le hEY Subgroup.le_normalizer
  obtain ⟨S, hS⟩ := (hE.comap_subtype : IsPGroup q ↥(E.subgroupOf K)).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup ↥K).map K.subtype with hS'
  have hS'syl : IsSylowOf q S' K := ⟨S, rfl⟩
  have hES' : E ≤ S' := by
    intro x hx
    have : (⟨x, le_sup_left (a := E) hx⟩ : ↥K) ∈ E.subgroupOf K := hx
    exact ⟨_, hS this, rfl⟩
  have hW : IsSylowOf q (S' ⊓ Y) Y := hS'syl.inf_of_le_normalizer hYK hKN
  obtain ⟨k, hkY, hk⟩ := hP.exists_mem_conj hW
  have hWeq : S' ⊓ Y = uniqueFourConj k⁻¹ P := by
    ext x
    rw [hk x, uc22p22r_mem_conj_inv]
  refine ⟨k⁻¹, Y.inv_mem hkY, ?_, fun F hFE hFY => ?_⟩
  · rw [← hWeq]
    intro e he
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hES' he), hEY he⟩
  · rw [← hWeq]
    exact le_inf (hFE.trans hES') hFY

theorem uc22p22r_exists_pCore_conj {M P : Subgroup G} {y : G} (hy : y ∈ barPreimage M (barImage M P)) :
    ∃ k ∈ pCoreOf 2 M, uniqueFourConj y P = uniqueFourConj k P := by
  obtain ⟨hyM, hπ⟩ := uc22p21c_mem_barPreimage.1 hy
  obtain ⟨m, hmP, hm⟩ := uc22p21c_mem_barImage.1 hπ
  have hker : m⁻¹ * ⟨y, hyM⟩ ∈ CFSG.pCore 2 ↥M := by
    have h3 : (QuotientGroup.mk m : Bar2 M) = QuotientGroup.mk ⟨y, hyM⟩ := hm
    exact QuotientGroup.eq.1 h3
  obtain ⟨k, hk⟩ : ∃ k : G, k = ((m⁻¹ * ⟨y, hyM⟩ : ↥M) : G) := ⟨_, rfl⟩
  refine ⟨k, ⟨_, hker, hk.symm⟩, ?_⟩
  have hy' : y = (m : G) * k := by
    rw [hk]
    simp
  rw [hy', ← uc22p22r_conj_conj, uc22p22r_conj_self_of_mem P hmP]

theorem uc22p22r_le_normalizer_centralizer {M V : Subgroup G} (h : M ≤ normalizer (V : Set G)) :
    M ≤ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (h (M.inv_mem hm)) v).1 hv
      simpa using this
    have h1 := hx _ hv'
    calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
      _ = (m * x * m⁻¹) * v := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : m * v * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (h hm) v).1 hv
    have h1 := hx _ hv'
    calc v * x = m⁻¹ * ((m * v * m⁻¹) * (m * x * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * x * m⁻¹) * (m * v * m⁻¹)) * m := by rw [h1]
      _ = x * v := by group

theorem uc22p22r_commute_of_le_normalizer {q : ℕ} [hq : Fact q.Prime] {A B : Subgroup G}
    (hA : Nat.card ↥A = q) (hB : Nat.card ↥B = q) (hne : B ≠ A) (hAB : A ≤ normalizer (B : Set G)) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have hAq : IsPGroup q ↥A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hBq : IsPGroup q ↥B := IsPGroup.of_card (n := 1) (by rw [hB, pow_one])
  have hEq : IsPGroup q ↥(A ⊔ B) := hAq.to_sup_of_normal_right' hBq hAB
  have hEmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  have hle : Nat.card ↥(A ⊔ B) ≤ q * q := by
    let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
      ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ (le_sup_left (a := A) p.1.2) (le_sup_right (b := B) p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
      rw [hEmul] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod, hA, hB] at this
  have hAB' : ¬ A ≤ B := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hA, hB])).symm
  have hgt : q < Nat.card ↥(A ⊔ B) := by
    by_contra h
    push Not at h
    have h1 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (h.trans hB.ge)
    exact hAB' (h1 ▸ le_sup_left)
  obtain ⟨k, hk⟩ := hEq.exists_card_eq
  have hcard : Nat.card ↥(A ⊔ B) = q ^ 2 := by
    have h2 := hq.out.two_le
    rw [hk] at hle hgt ⊢
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp at hgt <;> omega
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · exact h'.symm
        · exfalso
          have h3 : q ^ 3 ≤ q ^ k := Nat.pow_le_pow_right hq.out.pos h'
          have h4 : q * q < q ^ 3 := by
            rw [show q ^ 3 = q * q * q by ring]
            nlinarith
          omega
    rw [hk2]
  intro a ha b hb
  have := IsPGroup.commutative_of_card_eq_prime_sq hcard
    (⟨a, le_sup_left (a := A) ha⟩ : ↥(A ⊔ B)) ⟨b, le_sup_right (b := B) hb⟩
  exact congrArg Subtype.val this

theorem uc22p22r_sylow_cent {q : ℕ} [Fact q.Prime] {M P V : Subgroup G}
    (hPsyl : IsSylowOf q P (barPreimage M (barImage M P))) (hMV : M ≤ normalizer (V : Set G))
    (hAcard : Nat.card ↥(P ⊓ centralizer (V : Set G)) = q) :
    IsSylowOf q (P ⊓ centralizer (V : Set G)) (barPreimage M (barImage M P) ⊓ centralizer (V : Set G)) := by
  set A : Subgroup G := P ⊓ centralizer (V : Set G) with hAdef
  set Y₀ : Subgroup G := barPreimage M (barImage M P) with hY₀
  set K' : Subgroup G := Y₀ ⊓ centralizer (V : Set G) with hK'
  have hAq : IsPGroup q ↥A := hPsyl.isPGroup.to_le inf_le_left
  have hAK' : A ≤ K' := le_inf (inf_le_left.trans hPsyl.le) inf_le_right
  obtain ⟨S, hS⟩ := (hAq.comap_subtype : IsPGroup q ↥(A.subgroupOf K')).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup ↥K').map K'.subtype with hS'
  have hS'syl : IsSylowOf q S' K' := ⟨S, rfl⟩
  have hAS' : A ≤ S' := by
    intro x hx
    have : (⟨x, hAK' hx⟩ : ↥K') ∈ A.subgroupOf K' := hx
    exact ⟨_, hS this, rfl⟩
  obtain ⟨y, hyY, -, hS'y⟩ := uc22p22r_exists_sylow_normalized hPsyl hS'syl.isPGroup
    (hS'syl.le.trans (inf_le_left.trans Subgroup.le_normalizer))
  have hS'P := hS'y S' le_rfl (hS'syl.le.trans inf_le_left)
  have hyM : y ∈ M := uc22p21c_barPreimage_le M _ hyY
  have hS'A : S' ≤ uniqueFourConj y A := by
    intro x hx
    rw [uc22p22f_mem_conj]
    have h1 : y * x * y⁻¹ ∈ P := (uc22p22f_mem_conj P y x).1 (hS'P hx)
    have h2 : x ∈ centralizer (V : Set G) := (hS'syl.le hx).2
    have h3 : y * x * y⁻¹ ∈ centralizer (V : Set G) :=
      (Subgroup.mem_normalizer_iff.1 (uc22p22r_le_normalizer_centralizer hMV hyM) x).1 h2
    exact ⟨h1, h3⟩
  have hcard : Nat.card ↥S' ≤ Nat.card ↥A :=
    (Subgroup.card_le_of_le hS'A).trans (uc22p22r_card_conj A y).le
  have hAeq : A = S' := Subgroup.eq_of_le_of_card_ge hAS' hcard
  rw [hAeq]
  exact hS'syl

theorem uc22p22r_sym2210_holds (D : Data G) (Ch : Choice2011 G) :
    H1930 D → ∀ c : Ctx22b D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ P : Subgroup G,
      P ≤ D.M → IsPGroup q ↥P → (barImage D.M P).Normal → rankThreeGamma 1 q P ≤ D.M →
      Nat.card ↥(P ⊓ centralizer (c.V : Set G)) = q →
      ∀ z ∈ c.V, z ≠ 1 → ∀ g₀ ∈ centralizer ({z} : Set G), g₀ ∉ D.M →
        uniqueFourConj g₀ (P ⊓ centralizer (c.V : Set G)) ≤ D.M →
        ∃ g ∈ centralizer ({z} : Set G), g ∉ D.M ∧
          uniqueFourConj g (P ⊓ centralizer (c.V : Set G)) ≤ D.M ∧
          P ⊓ centralizer (c.V : Set G) ≤ uniqueFourConj g D.M ∧
          uniqueFourConj g (P ⊓ centralizer (c.V : Set G)) ≠ P ⊓ centralizer (c.V : Set G) ∧
          (∀ a ∈ P ⊓ centralizer (c.V : Set G), ∀ b ∈ uniqueFourConj g (P ⊓ centralizer (c.V : Set G)),
            a * b = b * a) ∧
          (∃ k ∈ pCoreOf 2 D.M, P ⊓ centralizer (c.V : Set G) ≤ uniqueFourConj k P ∧
            uniqueFourConj g (P ⊓ centralizer (c.V : Set G)) ≤
              normalizer ((uniqueFourConj k P : Subgroup G) : Set G)) ∧
          (∃ k ∈ pCoreOf 2 D.M, P ⊓ centralizer (c.V : Set G) ≤ uniqueFourConj k P ∧
            P ⊓ centralizer (c.V : Set G) ≤
              normalizer ((uniqueFourConj g (uniqueFourConj k P) : Subgroup G) : Set G)) := by
  classical
  intro _h1930 c q hq hq2 P hPM hPq hPn hΓ hAcard z hzV _hz1 g₀ hg₀z hg₀M hAg₀
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hPn
  set A : Subgroup G := P ⊓ centralizer (c.V : Set G) with hAdef
  set Y₀ : Subgroup G := barPreimage D.M (barImage D.M P) with hY₀
  set K' : Subgroup G := Y₀ ⊓ centralizer (c.V : Set G) with hK'
  have hAP : A ≤ P := inf_le_left
  have hAM : A ≤ D.M := hAP.trans hPM
  have hAq : IsPGroup q ↥A := hPq.to_le hAP
  have hNA : normalizer (A : Set G) ≤ D.M := uc22p22r_normalizer_le hq hAP hAcard hΓ
  have hPsyl : IsSylowOf q P Y₀ := (uc22p22f_sylow_in_Y hq hq2 hPM hPq).1
  have hPY₀ : P ≤ Y₀ := hPsyl.le
  have hMY₀ : D.M ≤ normalizer (Y₀ : Set G) := uc22p22f_normalizer_barPreimage D.M _
  have hMC : D.M ≤ normalizer ((centralizer (c.V : Set G) : Subgroup G) : Set G) :=
    uc22p22r_le_normalizer_centralizer c.hVM
  have hMK' : D.M ≤ normalizer (K' : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hMY₀ hm, hMC hm⟩
  have hK'M : K' ≤ D.M := inf_le_left.trans (uc22p21c_barPreimage_le _ _)
  have hK'z : K' ≤ centralizer ({z} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzV))
  have hAsyl : IsSylowOf q A K' := uc22p22r_sylow_cent hPsyl c.hVM hAcard
  obtain ⟨x, hx⟩ : ∃ x : G, x = g₀⁻¹ := ⟨_, rfl⟩
  have hxz : x ∈ centralizer ({z} : Set G) := hx ▸ Subgroup.inv_mem _ hg₀z
  have hxM : x ∉ D.M := fun h => hg₀M (by simpa [hx] using D.M.inv_mem h)
  have hAMx : A ≤ uniqueFourConj x D.M := by
    intro a ha
    rw [hx, uc22p22r_mem_conj_inv]
    apply hAg₀
    rw [uc22p22f_mem_conj, show g₀ * (g₀⁻¹ * a * g₀) * g₀⁻¹ = a by group]
    exact ha
  have hAY : A ≤ normalizer ((uniqueFourConj x K' : Subgroup G) : Set G) :=
    hAMx.trans (uc22p22r_conj_le_normalizer hMK' x)
  obtain ⟨w, hwY, hAw, -⟩ :=
    uc22p22r_exists_sylow_normalized (uc22p22r_isSylowOf_conj hAsyl x) hAq hAY
  rw [uc22p22r_conj_conj] at hAw
  obtain ⟨g, hg⟩ : ∃ g : G, g = x * w := ⟨_, rfl⟩
  rw [← hg] at hAw
  obtain ⟨u, hu⟩ : ∃ u : G, u = x * w * x⁻¹ := ⟨_, rfl⟩
  have huK' : u ∈ K' := hu ▸ (uc22p22f_mem_conj K' x w).1 hwY
  have hgu : g = u * x := by
    rw [hg, hu]
    group
  have huM : u ∈ D.M := hK'M huK'
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [hgu]
    exact Subgroup.mul_mem _ (hK'z huK') hxz
  have hgM : g ∉ D.M := by
    rw [hgu]
    intro h
    apply hxM
    have := D.M.mul_mem (D.M.inv_mem huM) h
    simpa using this
  have hMg : uniqueFourConj g D.M = uniqueFourConj x D.M := by
    rw [hgu, ← uc22p22r_conj_conj, uc22p22r_conj_self_of_mem D.M huM]
  have hAMg : A ≤ uniqueFourConj g D.M := hMg ▸ hAMx
  have hne : uniqueFourConj g A ≠ A := by
    intro h
    apply hgM
    apply hNA
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← uc22p22f_mem_conj, h]
  have hcomm : ∀ a ∈ A, ∀ b ∈ uniqueFourConj g A, a * b = b * a :=
    uc22p22r_commute_of_le_normalizer hAcard ((uc22p22r_card_conj A g).trans hAcard) hne hAw
  have hAgM : uniqueFourConj g A ≤ D.M := by
    intro b hb
    apply hNA
    have : b ∈ centralizer (A : Set G) := Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
    exact Subgroup.centralizer_le_normalizer _ this
  have hE₁q : IsPGroup q ↥(A ⊔ uniqueFourConj g A) :=
    hAq.to_sup_of_normal_right' (uc22p22r_isPGroup_conj hAq g) hAw
  have hE₁M : A ⊔ uniqueFourConj g A ≤ D.M := sup_le hAM hAgM
  obtain ⟨y₁, hy₁, hE₁N, hE₁F⟩ := uc22p22r_exists_sylow_normalized hPsyl hE₁q (hE₁M.trans hMY₀)
  obtain ⟨k₁, hk₁, hk₁eq⟩ := uc22p22r_exists_pCore_conj hy₁
  have hE₁Mg : A ⊔ uniqueFourConj g A ≤ uniqueFourConj g D.M := sup_le hAMg (uc22p22r_conj_mono hAM g)
  obtain ⟨y₂', hy₂', hE₂N, hE₂F⟩ := uc22p22r_exists_sylow_normalized (uc22p22r_isSylowOf_conj hPsyl g) hE₁q
    (hE₁Mg.trans (uc22p22r_conj_le_normalizer hMY₀ g))
  obtain ⟨y₂, hy₂def⟩ : ∃ y₂ : G, y₂ = g * y₂' * g⁻¹ := ⟨_, rfl⟩
  have hy₂ : y₂ ∈ Y₀ := hy₂def ▸ (uc22p22f_mem_conj Y₀ g y₂').1 hy₂'
  obtain ⟨k₂, hk₂, hk₂eq⟩ := uc22p22r_exists_pCore_conj hy₂
  have hconj2 : uniqueFourConj y₂' (uniqueFourConj g P) = uniqueFourConj g (uniqueFourConj k₂ P) := by
    rw [uc22p22r_conj_conj, ← hk₂eq, uc22p22r_conj_conj, show y₂ * g = g * y₂' by rw [hy₂def]; group]
  refine ⟨g, hgz, hgM, hAgM, hAMg, hne, hcomm, ⟨k₁, hk₁, ?_, ?_⟩, ⟨k₂, hk₂, ?_, ?_⟩⟩
  · rw [← hk₁eq]
    exact hE₁F A le_sup_left (hAP.trans hPY₀)
  · rw [← hk₁eq]
    exact le_sup_right.trans hE₁N
  · have h1 : uniqueFourConj g A ≤ uniqueFourConj g (uniqueFourConj k₂ P) := by
      rw [← hconj2]
      exact hE₂F _ le_sup_right (uc22p22r_conj_mono (hAP.trans hPY₀) g)
    intro a ha
    have hb : g⁻¹ * a * g ∈ uniqueFourConj g A := by
      rw [uc22p22f_mem_conj, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
      exact ha
    have h2 := h1 hb
    rw [uc22p22f_mem_conj, show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h2
    exact h2
  · rw [← hconj2]
    exact le_sup_left.trans hE₂N

end CFSG.LocalAnalysis.UniquenessCase.UC22
