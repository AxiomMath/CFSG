module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

variable {G : Type} [Group G]

section Transport

variable {Y : Type} [Group Y] {P : Subgroup G}

abbrev img (ψ : ↥P →* Y) (H : Subgroup G) : Subgroup Y := (H.subgroupOf P).map ψ

theorem img_mono (ψ : ↥P →* Y) {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : img ψ H₁ ≤ img ψ H₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem img_le_normalizer (ψ : ↥P →* Y) {X H : Subgroup G}
    (hXH : X ≤ Subgroup.normalizer (H : Set G)) :
    img ψ X ≤ Subgroup.normalizer (img ψ H : Set Y) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨x * h * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show ((x * h * x⁻¹ : ↥P) : G) ∈ H
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXH hx) h).mp hh
  · rintro ⟨z, hz, hzeq⟩
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · show ((x⁻¹ * z * x : ↥P) : G) ∈ H
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      refine (Subgroup.mem_normalizer_iff.mp (hXH hx) _).mpr ?_
      have e : (x : G) * ((x : G)⁻¹ * (z : G) * x) * (x : G)⁻¹ = z := by group
      show (x : G) * ((x : G)⁻¹ * (z : G) * x) * (x : G)⁻¹ ∈ H
      rw [e]
      exact hz
    · rw [map_mul, map_mul, map_inv, hzeq]
      group

theorem img_le_centralizer (ψ : ↥P →* Y) {X V : Subgroup G}
    (hXV : X ≤ Subgroup.centralizer (V : Set G)) :
    img ψ X ≤ Subgroup.centralizer (img ψ V : Set Y) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hXV hx) v hv))

theorem card_img {ψ : ↥P →* Y} (hψ : Function.Injective ψ) {H : Subgroup G} (hH : H ≤ P) :
    Nat.card ↥(img ψ H) = Nat.card ↥H := by
  rw [Subgroup.card_map_of_injective hψ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv]

theorem mem_of_mem_img {ψ : ↥P →* Y} (hψ : Function.Injective ψ) {H : Subgroup G} {x : ↥P}
    (hx : ψ x ∈ img ψ H) : (x : G) ∈ H := by
  obtain ⟨z, hz, hzx⟩ := hx
  rw [← hψ hzx]
  exact hz

noncomputable def imgEquiv {ψ : ↥P →* Y} (hψ : Function.Injective ψ) {H : Subgroup G}
    (hH : H ≤ P) : ↥H ≃* ↥(img ψ H) :=
  (Subgroup.subgroupOfEquivOfLe hH).symm.trans ((H.subgroupOf P).equivMapOfInjective ψ hψ)

end Transport

theorem false_of_vertex [Finite G] (hG : FactG2FourLongParabolic) {Y : Type} [Group Y] [Finite Y]
    (hY : IsG2Over 2 Y) {T M : Subgroup Y} (hT : QuasithinUnique.IsSylowTwoOf T ⊤)
    (hM : IsMaximalTwoLocal M) (hNM : Subgroup.normalizer (T : Set Y) ≤ M)
    {P : Subgroup G} (e : ↥P ≃* ↥M) {K V A B : Subgroup G} (hKP : K ≤ P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hKp : ⁅K, K⁆ = K)
    (hKsl : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hVP : V ≤ P) (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hV4 : Nat.card ↥V = 4)
    (hKV : K ≤ Subgroup.centralizer (V : Set G)) (hAB : A ≤ B) (hBP : B ≤ pCoreOf 2 P)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hne : A ≠ B) {y : G} (hy : y ∈ K)
    (hy3 : orderOf y = 3) (hfree : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ A → b ∈ A) : False := by
  set ψ : ↥P →* Y := M.subtype.comp e.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hMP : M ≤ img ψ P := fun m hm =>
    ⟨e.symm ⟨m, hm⟩, by simp, by simp [hψdef]⟩
  have himgM : ∀ H : Subgroup G, img ψ H ≤ M := by
    rintro H _ ⟨x, -, rfl⟩
    exact (e x).2
  have hMN : ∀ H : Subgroup G, P ≤ Subgroup.normalizer (H : Set G) →
      M ≤ Subgroup.normalizer (img ψ H : Set Y) := fun H hH =>
    hMP.trans (img_le_normalizer ψ hH)
  have hKp' : ⁅img ψ K, img ψ K⁆ = img ψ K := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
    have : Group.IsPerfect ↥(img ψ K) := Group.IsPerfect.ofSurjective
      (f := (imgEquiv hψ hKP).toMonoidHom) (imgEquiv hψ hKP).surjective
    exact Subgroup.isPerfect_iff.mp this
  have hKsl' : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(img ψ K) ⧸ CFSG.pCore 2 ↥(img ψ K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hKsl
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.congr _ _ (imgEquiv hψ hKP).symm
        (CFSG.pCore_map_iso 2 (imgEquiv hψ hKP).symm)).trans f⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBM : img ψ B ≤ pCoreOf 2 M := by
    refine (img_mono ψ hBP).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (himgM _) (hMN _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)) ?_)
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) P |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).symm).map ψ
  have hne' : img ψ A ≠ img ψ B := by
    intro h
    apply hne
    refine le_antisymm hAB fun b hb => ?_
    have hbP : b ∈ P := (hBP.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)) hb
    have : ψ ⟨b, hbP⟩ ∈ img ψ A := h ▸ ⟨⟨b, hbP⟩, hb, rfl⟩
    exact mem_of_mem_img hψ this
  have hyP : y ∈ P := hKP hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hbA, hcomm⟩ := hG Y hY T M (img ψ K) (img ψ V) (img ψ A) (img ψ B)
    hT hM hNM (himgM K) (hMN K hPK) hKp' hKsl' (himgM V) (hMN V hPV)
    (by rw [card_img hψ hVP, hV4]) (img_le_centralizer ψ hKV) (img_mono ψ hAB) hBM
    (img_le_normalizer ψ hBA) (img_le_normalizer ψ hKA) (img_le_normalizer ψ hKB) hne'
    (ψ ⟨y, hyP⟩) ⟨⟨y, hyP⟩, hy, rfl⟩
    (by rw [orderOf_injective ψ hψ, Subgroup.orderOf_mk, hy3])
  apply hbA
  refine ⟨b, hfree b hb ?_, rfl⟩
  have h2 : ψ (⟨y, hyP⟩ * b * ⟨y, hyP⟩⁻¹ * b⁻¹) ∈ img ψ A := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm
  simpa using mem_of_mem_img hψ h2

omit [Group G] in
theorem finite_of_isG2Over {Y : Type} [Group Y] (hY : IsG2Over 2 Y) : Finite Y := by
  rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
  · omega
  · have hX : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 2 2 := by
      rcases hL with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    obtain ⟨-, K, _, _, _, -, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hX
    have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.G2 K) :=
      CFSG.LieType.Chevalley.finite_modGL
    exact Finite.of_equiv _ e.symm.toEquiv

theorem false_of_g2Amalgam [Finite G] (hG : FactG2FourLongParabolic) {P1 P2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P1 P2) (IsG2Over 2)) {P : Subgroup G}
    (hP : P = P1 ∨ P = P2) {K V A B : Subgroup G} (hKP : K ≤ P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hKp : ⁅K, K⁆ = K)
    (hKsl : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hVP : V ≤ P) (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hV4 : Nat.card ↥V = 4)
    (hKV : K ≤ Subgroup.centralizer (V : Set G)) (hAB : A ≤ B) (hBP : B ≤ pCoreOf 2 P)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hne : A ≠ B) {y : G} (hy : y ∈ K)
    (hy3 : orderOf y = 3) (hfree : ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ A → b ∈ A) : False := by
  obtain ⟨Y, _, hY, T, M₁, M₂, ⟨hT, -, hpair⟩, ⟨iso⟩⟩ := hα
  have : Finite Y := finite_of_isG2Over hY
  have hM₁ := (hpair M₁).mpr (Or.inl rfl)
  have hM₂ := (hpair M₂).mpr (Or.inr rfl)
  rcases hP with rfl | rfl
  · exact false_of_vertex hG hY hT hM₁.1 hM₁.2 iso.φ1 hKP hPK hKp hKsl hVP hPV hV4 hKV hAB hBP
      hBA hKA hKB hne hy hy3 hfree
  · exact false_of_vertex hG hY hT hM₂.1 hM₂.2 iso.φ2 hKP hPK hKp hKsl hVP hPV hV4 hKV hAB hBP
      hBA hKA hKB hne hy hy3 hfree

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
