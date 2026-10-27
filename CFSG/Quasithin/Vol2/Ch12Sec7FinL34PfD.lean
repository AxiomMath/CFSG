module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfA
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.L34Br

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {Y : Type} [Group Y]

theorem oTwoUpper_top_normal' : (oTwoUpper (⊤ : Subgroup Y)).Normal :=
  ⟨fun _ hn g => conj_mem_oTwoUpper (Subgroup.le_normalizer (Subgroup.mem_top g)) hn⟩

@[expose] def ParY (S : Subgroup Y) : Prop :=
  ∃ R₂ R₃ : Subgroup Y, R₂ ≠ R₃ ∧
    (∀ R : Subgroup Y, (R = R₂ ∨ R = R₃) →
      R ≤ S ⊓ oTwoUpper ⊤ ∧
      (∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
        d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
          d ∈ Subgroup.normalizer (R : Set Y)) ∧
      IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
      (∃ π : ↥(Subgroup.normalizer (R : Set Y) ⊓ oTwoUpper ⊤) →*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
        Function.Surjective π ∧
          π.ker = R.subgroupOf (Subgroup.normalizer (R : Set Y) ⊓ oTwoUpper ⊤)) ∧
      ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ n ∈ oTwoUpper (⊤ : Subgroup Y),
        n ∈ Subgroup.normalizer (R : Set Y) ∧ n * r * n⁻¹ = s) ∧
    ∀ E : Subgroup Y, E ≤ S ⊓ oTwoUpper ⊤ → IsElemAbelian 2 E → E ≤ R₂ ∨ E ≤ R₃

@[expose] def OutY (S : Subgroup Y) : Prop :=
  ∃ ψ : Y →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
    (∀ k ∈ oTwoUpper (⊤ : Subgroup Y), ψ k = 1) ∧
    (∀ x : Y, x * x = 1 → ψ x = 1 → x ∈ oTwoUpper (⊤ : Subgroup Y)) ∧
    (∀ b : Y, b * b = 1 → ψ b = (1, Multiplicative.ofAdd 1) →
      IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y))) ∧
    ∀ x ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y),
      (ψ x).1 = Multiplicative.ofAdd 1 → ∃ d ∈ oTwoUpper (⊤ : Subgroup Y),
        d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) ∧
          x * d * x⁻¹ * d⁻¹ ∉ S

section Sub

variable {K : Subgroup Y}

theorem isElemAbelian_map {Z : Type*} [Group Z] (f : Y →* Z) {p : ℕ} {E : Subgroup Y}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_subgroupOf' {p : ℕ} {E : Subgroup Y} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem mem_normalizer_map_subtype {A : Subgroup ↥K} {k : ↥K} :
    (k : Y) ∈ Subgroup.normalizer ((A.map K.subtype : Subgroup Y) : Set Y) ↔
      k ∈ Subgroup.normalizer (A : Set ↥K) := by
  have hmem : ∀ a : ↥K, (a : Y) ∈ A.map K.subtype ↔ a ∈ A := fun a => by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hba⟩
      rwa [show b = a from Subtype.ext hba] at hb
    · exact fun ha => ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    rw [← hmem, ← hmem]
    exact h a
  · intro h y
    by_cases hy : y ∈ K
    · have := h ⟨y, hy⟩
      rw [← hmem, ← hmem] at this
      exact this
    · constructor
      · rintro ⟨b, -, rfl⟩
        exact absurd b.2 hy
      · rintro ⟨b, -, hb⟩
        exfalso
        apply hy
        have h1 : y = (k : Y)⁻¹ * (b : Y) * k := by
          rw [Subgroup.coe_subtype] at hb
          rw [hb]
          group
        rw [h1]
        exact K.mul_mem (K.mul_mem (K.inv_mem k.2) b.2) k.2

theorem normalizer_inf_eq_map {A : Subgroup ↥K} :
    Subgroup.normalizer ((A.map K.subtype : Subgroup Y) : Set Y) ⊓ K =
      (Subgroup.normalizer (A : Set ↥K)).map K.subtype := by
  ext y
  constructor
  · rintro ⟨hyN, hyK⟩
    exact ⟨⟨y, hyK⟩, mem_normalizer_map_subtype.1 hyN, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨mem_normalizer_map_subtype.2 hk, k.2⟩

end Sub

theorem parY_of {S : Subgroup Y}
    (h : L34ParData ↥(oTwoUpper (⊤ : Subgroup Y)) (S.subgroupOf (oTwoUpper ⊤))) : ParY S := by
  set K := oTwoUpper (⊤ : Subgroup Y) with hKdef
  obtain ⟨R₂, R₃, hne, hR, hEA⟩ := h
  have hSK : (S.subgroupOf K).map K.subtype = S ⊓ K := Subgroup.subgroupOf_map_subtype S K
  refine ⟨R₂.map K.subtype, R₃.map K.subtype, ?_, fun R hR' => ?_, fun E hE hEe => ?_⟩
  · intro h
    exact hne (Subgroup.map_injective K.subtype_injective h)
  · obtain ⟨R₀, rfl, hR₀⟩ : ∃ R₀ : Subgroup ↥K, R = R₀.map K.subtype ∧ (R₀ = R₂ ∨ R₀ = R₃) := by
      rcases hR' with rfl | rfl
      · exact ⟨R₂, rfl, Or.inl rfl⟩
      · exact ⟨R₃, rfl, Or.inr rfl⟩
    obtain ⟨hRS, hRN, hRe, hR16, ⟨π, hπs, hπk⟩, htr⟩ := hR R₀ hR₀
    refine ⟨?_, fun d hdK hdN => ?_, isElemAbelian_map _ hRe, ?_, ?_, ?_⟩
    · rw [← hSK]
      exact Subgroup.map_mono hRS
    · have hdN' : (⟨d, hdK⟩ : ↥K) ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
        mem_normalizer_map_subtype.1 (by rw [hSK]; exact hdN)
      exact mem_normalizer_map_subtype.2 (hRN hdN')
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hR16]
    ·
      have hNY := normalizer_inf_eq_map (K := K) (A := R₀)
      let e₁ := Subgroup.equivMapOfInjective (Subgroup.normalizer (R₀ : Set ↥K)) K.subtype
        K.subtype_injective
      let ι : ↥(Subgroup.normalizer ((R₀.map K.subtype : Subgroup Y) : Set Y) ⊓ K) ≃*
          ↥(Subgroup.normalizer (R₀ : Set ↥K)) :=
        (MulEquiv.subgroupCongr hNY).trans e₁.symm
      have hι : ∀ x, (((ι x : ↥(Subgroup.normalizer (R₀ : Set ↥K))) : ↥K) : Y) = (x : Y) := by
        intro x
        have h1 := congrArg Subtype.val (e₁.apply_symm_apply (MulEquiv.subgroupCongr hNY x))
        rw [Subgroup.coe_equivMapOfInjective_apply] at h1
        exact h1
      refine ⟨π.comp ι.toMonoidHom, hπs.comp ι.surjective, ?_⟩
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hx
        exact ⟨_, hx, hι x⟩
      · rintro ⟨r, hr, hrx⟩
        have : r = ((ι x : ↥(Subgroup.normalizer (R₀ : Set ↥K))) : ↥K) :=
          Subtype.ext (by rw [hι]; exact hrx)
        rwa [this] at hr
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ hr1 hs1
      have hr1' : r ≠ 1 := fun h => hr1 (by rw [h]; rfl)
      have hs1' : s ≠ 1 := fun h => hs1 (by rw [h]; rfl)
      obtain ⟨n, hn, hnrs⟩ := htr r hr s hs hr1' hs1'
      refine ⟨n, n.2, mem_normalizer_map_subtype.2 hn, ?_⟩
      have := congrArg Subtype.val hnrs
      simpa using this
  ·
    have hEK : E ≤ K := hE.trans inf_le_right
    have hE' : E.subgroupOf K ≤ S.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hE (Subgroup.mem_subgroupOf.1 hx)).1
    have hEmap : (E.subgroupOf K).map K.subtype = E := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hEK
    rcases hEA _ hE' (isElemAbelian_subgroupOf' hEe) with h | h
    · left
      rw [← hEmap]
      exact Subgroup.map_mono h
    · right
      rw [← hEmap]
      exact Subgroup.map_mono h

theorem outY_of {S : Subgroup Y}
    (hC : Subgroup.centralizer (oTwoUpper (⊤ : Subgroup Y) : Set Y) = ⊥)
    (h : L34OutData ↥(oTwoUpper (⊤ : Subgroup Y)) (S.subgroupOf (oTwoUpper ⊤))) : OutY S := by
  set K := oTwoUpper (⊤ : Subgroup Y) with hKdef
  have : K.Normal := oTwoUpper_top_normal'
  obtain ⟨ψ, h1, h2, h3, h4⟩ := h
  set φ : Y →* MulAut ↥K := MulAut.conjNormal with hφ
  have hφapp : ∀ (y : Y) (k : ↥K), ((φ y k : ↥K) : Y) = y * k * y⁻¹ := fun _ _ => rfl
  have hφK : ∀ k : ↥K, φ (k : Y) = MulAut.conj k := fun k => MulAut.conjNormal_val
  have hSK : (S.subgroupOf K).map K.subtype = S ⊓ K := Subgroup.subgroupOf_map_subtype S K
  refine ⟨ψ.comp φ, fun k hk => ?_, fun x hxx hψx => ?_, fun b hbb hψb => ?_,
    fun x hxN hψx => ?_⟩
  · rw [MonoidHom.comp_apply, show k = ((⟨k, hk⟩ : ↥K) : Y) from rfl, hφK, h1]
  · have hsq : φ x * φ x = 1 := by rw [← map_mul, hxx, map_one]
    obtain ⟨k, hk⟩ := h2 (φ x) hsq hψx
    have hc : (k : Y)⁻¹ * x ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have e := congrArg (fun α : MulAut ↥K => ((α ⟨a, ha⟩ : ↥K) : Y)) hk
      simp only [hφapp, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at e
      calc a * ((k : Y)⁻¹ * x) = (k : Y)⁻¹ * ((k : Y) * a * (k : Y)⁻¹) * x := by group
        _ = (k : Y)⁻¹ * (x * a * x⁻¹) * x := by rw [e]
        _ = (k : Y)⁻¹ * x * a := by group
    rw [hC, Subgroup.mem_bot] at hc
    have : x = (k : Y) := by
      calc x = (k : Y) * ((k : Y)⁻¹ * x) := by group
        _ = k := by rw [hc, mul_one]
    rw [this]
    exact k.2
  · have hsq : φ b * φ b = 1 := by rw [← map_mul, hbb, map_one]
    have hP := h3 (φ b) hsq hψb
    have hmap : (fixSub (φ b)).map K.subtype = K ⊓ Subgroup.centralizer ({b} : Set Y) := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine Subgroup.mem_inf.2 ⟨k.2, ?_⟩
        show (k : Y) ∈ Subgroup.centralizer ({b} : Set Y)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have e := congrArg Subtype.val (mem_fixSub.1 hk)
        rw [hφapp] at e
        calc (k : Y) * b = b * k * b⁻¹ * b := by rw [e]
          _ = b * k := by group
      · intro hy
        obtain ⟨hyK, hyb⟩ := Subgroup.mem_inf.1 hy
        refine ⟨⟨y, hyK⟩, mem_fixSub.2 (Subtype.ext ?_), rfl⟩
        rw [hφapp]
        show b * y * b⁻¹ = y
        rw [Subgroup.mem_centralizer_singleton_iff] at hyb
        calc b * y * b⁻¹ = y * b * b⁻¹ := by rw [hyb]
          _ = y := by group
    exact isPSL_of_mulEquiv hP ((Subgroup.equivMapOfInjective _ _ K.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap))
  ·
    have hS₀ : (S.subgroupOf K).map (φ x).toMonoidHom = S.subgroupOf K := by
      ext k
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hinv : (((φ x).symm k : ↥K) : Y) = x⁻¹ * k * x := MulAut.conjNormal_symm_apply x k
      rw [hinv]
      have hxi : x⁻¹ ∈ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) :=
        Subgroup.inv_mem _ hxN
      have hkK : x⁻¹ * (k : Y) * x ∈ K := by
        have := (inferInstance : K.Normal).conj_mem (k : Y) k.2 x⁻¹
        simpa using this
      have e := Subgroup.mem_normalizer_iff.1 hxi (k : Y)
      rw [inv_inv] at e
      constructor
      · intro hk
        exact (Subgroup.mem_inf.1 (e.2 (Subgroup.mem_inf.2 ⟨hk, hkK⟩))).1
      · intro hk
        exact (Subgroup.mem_inf.1 (e.1 (Subgroup.mem_inf.2 ⟨hk, k.2⟩))).1
    obtain ⟨d, hd, hdS⟩ := h4 (φ x) hS₀ hψx
    refine ⟨(d : Y), d.2, ?_, fun hmem => hdS ?_⟩
    · rw [← hSK]
      exact mem_normalizer_map_subtype.2 hd
    · rw [Subgroup.mem_subgroupOf]
      have : (((φ x d * d⁻¹ : ↥K)) : Y) = x * d * x⁻¹ * (d : Y)⁻¹ := by
        rw [Subgroup.coe_mul, hφapp, Subgroup.coe_inv]
      rw [this]
      exact hmem

end CFSG.Quasithin.H13.L34Br
