module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtFinish
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtBasic
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtSL
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lem1227Lt

section Transfer

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G} {Λ : Type} [Group Λ]

theorem psi_mem_imgK (h : LtHyp G T K Y) (φ : ↥Y →* Λ) (k : ↥K) :
    psi h φ k ∈ imgK K Y φ := by
  rw [imgK_eq_range h φ]
  exact ⟨k, rfl⟩

@[expose] noncomputable def psiΘ (h : LtHyp G T K Y) (φ : ↥Y →* Λ) {X' : Type} [Group X']
    (Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set Λ)) →* X') : ↥K →* X' where
  toFun k := Θ ⟨psi h φ k, Subgroup.le_normalizer (psi_mem_imgK h φ k)⟩
  map_one' := by
    have : (⟨psi h φ 1, Subgroup.le_normalizer (psi_mem_imgK h φ 1)⟩ :
        ↥(Subgroup.normalizer (imgK K Y φ : Set Λ))) = 1 := Subtype.ext (map_one _)
    rw [this, map_one]
  map_mul' k k' := by
    have : (⟨psi h φ (k * k'), Subgroup.le_normalizer (psi_mem_imgK h φ (k * k'))⟩ :
        ↥(Subgroup.normalizer (imgK K Y φ : Set Λ))) =
        ⟨psi h φ k, Subgroup.le_normalizer (psi_mem_imgK h φ k)⟩ *
          ⟨psi h φ k', Subgroup.le_normalizer (psi_mem_imgK h φ k')⟩ :=
      Subtype.ext (map_mul _ _ _)
    rw [this, map_mul]

theorem psiΘ_apply (h : LtHyp G T K Y) (φ : ↥Y →* Λ) {X' : Type} [Group X']
    (Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set Λ)) →* X') (k : ↥K) :
    psiΘ h φ Θ k = Θ ⟨psi h φ k, Subgroup.le_normalizer (psi_mem_imgK h φ k)⟩ := rfl

theorem psiΘ_surjective (h : LtHyp G T K Y) (φ : ↥Y →* Λ) {X' : Type} [Group X']
    (Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set Λ)) →* X')
    (hΘ : ∀ s : X', ∃ b : ↥(imgK K Y φ), Θ ⟨(b : Λ), Subgroup.le_normalizer b.2⟩ = s) :
    Function.Surjective (psiΘ h φ Θ) := by
  intro s
  obtain ⟨b, hb⟩ := hΘ s
  have hb' : (b : Λ) ∈ (psi h φ).range := by
    rw [← imgK_eq_range h φ]
    exact b.2
  obtain ⟨k, hk⟩ := hb'
  refine ⟨k, ?_⟩
  rw [psiΘ_apply]
  rw [← hb]
  congr 1
  exact Subtype.ext hk

theorem psiΘ_inner (h : LtHyp G T K Y) (φ : ↥Y →* Λ) (hφs : Function.Surjective φ)
    (hinv : ∀ t : ↥T, ∀ y : ↥Y, φ y = 1 → φ (conjY h t y) = 1) [Finite Λ] {X' : Type}
    [Group X'] (Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set Λ)) →* X')
    (hΘ : ∀ s : X', ∃ b : ↥(imgK K Y φ), Θ ⟨(b : Λ), Subgroup.le_normalizer b.2⟩ = s)
    (hin : ∀ (t : ↥T) (α : MulAut Λ), (∀ y : ↥Y, α (φ y) = φ (conjY h t y)) →
      (imgK K Y φ).map α.toMonoidHom = imgK K Y φ → ∃ g : Λ, ∀ x : Λ, α x = g * x * g⁻¹)
    (t : ↥T) :
    ∃ k : ↥K, ∀ x : ↥K, psiΘ h φ Θ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) =
      psiΘ h φ Θ (k * x * k⁻¹) := by
  obtain ⟨α, hα, hαB, -⟩ := exists_act_T h φ hφs hinv t
  obtain ⟨g, hg⟩ := hin t α hα hαB
  have hgN : g ∈ Subgroup.normalizer (imgK K Y φ : Set Λ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : α x ∈ (imgK K Y φ).map α.toMonoidHom := ⟨x, hx, rfl⟩
      rw [hαB, hg] at this
      exact this
    · intro hx
      rw [← hg, ← hαB] at hx
      obtain ⟨b, hb, hbx⟩ := hx
      have : b = x := α.injective hbx
      rwa [← this]
  obtain ⟨b, hb⟩ := hΘ (Θ ⟨g, hgN⟩)
  have hb' : (b : Λ) ∈ (psi h φ).range := by
    rw [← imgK_eq_range h φ]
    exact b.2
  obtain ⟨k, hk⟩ := hb'
  refine ⟨k, fun x => ?_⟩
  have hxB : g * psi h φ x * g⁻¹ ∈ imgK K Y φ := by
    rw [← hg]
    have : α (psi h φ x) ∈ (imgK K Y φ).map α.toMonoidHom := ⟨_, psi_mem_imgK h φ x, rfl⟩
    rw [hαB] at this
    exact this
  have hL : psiΘ h φ Θ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) =
      Θ ⟨g, hgN⟩ * psiΘ h φ Θ x * (Θ ⟨g, hgN⟩)⁻¹ := by
    rw [psiΘ_apply, psiΘ_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show psi h φ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) = g * psi h φ x * g⁻¹
    rw [psi_conj h φ t hα x, hg]
  have hR : psiΘ h φ Θ (k * x * k⁻¹) =
      Θ ⟨(b : Λ), Subgroup.le_normalizer b.2⟩ * psiΘ h φ Θ x *
        (Θ ⟨(b : Λ), Subgroup.le_normalizer b.2⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv, psiΘ_apply, psiΘ_apply]
    have e1 : (⟨psi h φ k, Subgroup.le_normalizer (psi_mem_imgK h φ k)⟩ :
        ↥(Subgroup.normalizer (imgK K Y φ : Set Λ))) =
        ⟨(b : Λ), Subgroup.le_normalizer b.2⟩ := Subtype.ext hk
    rw [e1]
  rw [hL, hR, hb]

theorem map_normalizer_eq {Λ' : Type*} [Group Λ'] [Finite Λ'] (α : MulAut Λ') {B : Subgroup Λ'}
    (hB : B.map α.toMonoidHom = B) :
    (Subgroup.normalizer (B : Set Λ')).map α.toMonoidHom = Subgroup.normalizer (B : Set Λ') := by
  have hB' : ∀ c, c ∈ B ↔ α c ∈ B := by
    intro c
    constructor
    · intro hc
      rw [← hB]
      exact ⟨c, hc, rfl⟩
    · intro hc
      rw [← hB] at hc
      obtain ⟨c', hc', hcc⟩ := hc
      have : c' = c := α.injective hcc
      rwa [← this]
  have key : ∀ x ∈ Subgroup.normalizer (B : Set Λ'), α x ∈ Subgroup.normalizer (B : Set Λ') := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have e1 : α x * b * (α x)⁻¹ = α (x * α.symm b * x⁻¹) := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [e1, ← hB', ← Subgroup.mem_normalizer_iff.1 hx, hB' (α.symm b)]
    simp
  have hle : (Subgroup.normalizer (B : Set Λ')).map α.toMonoidHom ≤
      Subgroup.normalizer (B : Set Λ') := by
    rintro _ ⟨x, hx, rfl⟩
    exact key x hx
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective])

end Transfer

section Sylow

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G}

theorem exists_phi_sylow (h : LtHyp G T K Y) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X) (hν : Function.Surjective ν) :
    ∃ φ : ↥Y →* X, Function.Surjective φ ∧
      (∀ y : ↥Y, φ y = 1 ↔
        (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∧
      imgS T Y φ = U₀ := by
  have hS : IsSylowTwoOf (imgS T Y (phiOf Y ν)) ⊤ := isSylow_imgS h _ (phi_surj hν)
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_eq_of_sylow (MulEquiv.refl X) hS hU₀
  have hν' : Function.Surjective (ρ.toMonoidHom.comp ν) := ρ.surjective.comp hν
  refine ⟨phiOf Y (ρ.toMonoidHom.comp ν), phi_surj hν', phi_hkc h hX hν', ?_⟩
  rw [← hρ]
  simp only [imgS, Subgroup.map_map]
  rfl

end Sylow

section SLFamily

variable {G : Type} [Group G] [Finite G] {T K Y H M₀ : Subgroup G}

theorem sl_data (h : LtHyp G T K Y) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (φ : ↥Y →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS : imgS T Y φ = unitriangular n (ZMod 2)) :
    ∃ m : ℕ, (m = 3 ∨ (m = 4 ∧ n = 5)) ∧
      (n = 4 → ∃ d : ℕ, (d = 1 ∨ d = 3) ∧
        Subgroup.normalizer (imgK K Y φ : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) =
          stabilizer (flagSpace n (ZMod 2) d)) ∧
      ∃ Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set (Matrix.SpecialLinearGroup (Fin n)
          (ZMod 2)))) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
        ∀ s, ∃ b : ↥(imgK K Y φ), Θ ⟨(b : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
          Subgroup.le_normalizer b.2⟩ = s := by
  have hperf := imgK_perfect h φ
  have hbot := imgK_ne_bot h φ (fun y hy => (hk y).1 hy)
  have htop := imgK_ne_top h φ (fun y hy => (hk y).1 hy)
  have hU : unitriangular n (ZMod 2) ≤ Subgroup.normalizer (imgK K Y φ : Set _) :=
    hS ▸ imgS_le_normalizer h φ
  exact SL.sl_model hn4 hn5 hperf hbot htop hU

theorem false_of_sl_model (h : LtHyp G T K Y) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (hfam : B69.E22Fam ↥(E2.star M₀ H K)) {n : ℕ}
    (φ : ↥Y →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hφs : Function.Surjective φ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    {m : ℕ} (hm : m = 3 ∨ (m = 4 ∧ n = 5))
    (Θ : ↥(Subgroup.normalizer (imgK K Y φ : Set (Matrix.SpecialLinearGroup (Fin n)
      (ZMod 2)))) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
    (hΘ : ∀ s, ∃ b : ↥(imgK K Y φ), Θ ⟨(b : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
      Subgroup.le_normalizer b.2⟩ = s)
    (hin : ∀ (t : ↥T) (α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))),
      (∀ y : ↥Y, α (φ y) = φ (conjY h t y)) → (imgK K Y φ).map α.toMonoidHom = imgK K Y φ →
        ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), ∀ x, α x = g * x * g⁻¹) :
    False := by
  have hm3 : 3 ≤ m := by omega
  have := sl_isSimple_of_card_two SL.card_zmod_two hm3
  have hnonab := sl_nonabelian_of_card_two SL.card_zmod_two hm3
  have hψ := psiΘ_surjective h φ Θ hΘ
  rcases hm with rfl | ⟨rfl, -⟩
  · exact false_of_card_168 hKH hHK hmin hker hq h.hTK hlist hnonab card_sl_three_zmod_two
      (psiΘ h φ Θ) hψ (psiΘ_inner h φ hφs (hinv_of_hk h φ hk) Θ hΘ hin)
  · exact false_of_card_20160 hKH hHK hmin hker hq hfam hnonab (MulEquiv.refl _) (psiΘ h φ Θ) hψ

end SLFamily

end Lem1227Lt

end CFSG.Quasithin.H13
