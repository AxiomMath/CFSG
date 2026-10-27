module

public import CFSG.Quasithin.Vol2.Ch10SecE9Z
public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2App
public import CFSG.Quasithin.Vol2.Ch10SecE9G
public import CFSG.Quasithin.Vol2.Ch10SecE9I
public import CFSG.Quasithin.Vol2.Ch10SecE9V

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

omit [Finite G] in
theorem psi_mul_inv {a b : G} (ha : a ∈ fsuL0 T L) (hb : b ∈ fsuL0 T L)
    (hab : a * b⁻¹ ∈ fsuL0 T L) : Ψ ⟨a * b⁻¹, hab⟩ = Ψ ⟨a, ha⟩ * (Ψ ⟨b, hb⟩)⁻¹ := by
  rw [← map_inv, ← map_mul]
  rfl

omit [Finite G] in
theorem psi_mul {a b : G} (ha : a ∈ fsuL0 T L) (hb : b ∈ fsuL0 T L)
    (hab : a * b ∈ fsuL0 T L) : Ψ ⟨a * b, hab⟩ = Ψ ⟨a, ha⟩ * Ψ ⟨b, hb⟩ := by
  rw [← map_mul]
  rfl

theorem exists_x1 (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hD2 : ParData2 K E) :
    ∃ x₁ ∈ XOf T L Ψ A, x₁ ^ 3 ∈ pCoreOf 2 (XOf T L Ψ A) ∧ x₁ ∉ pCoreOf 2 (XOf T L Ψ A) ∧
      ∀ τ ∈ T1 T L, τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ pCoreOf 2 (XOf T L Ψ A) ∨
        τ * x₁ * τ⁻¹ * x₁ ∈ pCoreOf 2 (XOf T L Ψ A) := by
  have hXL0 := XOf_le_fsuL0 h hD
  have hEK : ¬ K ≤ E := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hD.cardK, hD.cardE] at this
    omega
  obtain ⟨k₀, hk₀K, hk₀E⟩ := Set.not_subset.mp hEK
  have hmem : (k₀, (1 : L32.Γ)) ∈ imgIn Ψ (XOf T L Ψ A) := by
    rw [imgIn_XOf h hD]
    exact ⟨hk₀K, K.one_mem⟩
  obtain ⟨x₁, hx₁L0, hx₁X, hx₁Ψ⟩ := mem_imgIn.mp hmem
  refine ⟨x₁, hx₁X, pow_three_mem h hD hx₁X, fun hx => ?_, fun τ hτ => ?_⟩
  · rw [pCoreOf_XOf h hD] at hx
    obtain ⟨hL0', h1⟩ := mem_preIn.mp hx.2
    have h1' : (Ψ ⟨x₁, hL0'⟩).1 ∈ E := (Subgroup.mem_prod.mp h1).1
    rw [hx₁Ψ] at h1'
    exact hk₀E h1'
  · obtain ⟨u, v, hu, hv, hact⟩ := h.hC.T1act τ hτ
    have hτX : τ * x₁ * τ⁻¹ ∈ XOf T L Ψ A :=
      (Subgroup.mem_normalizer_iff.mp ((isXi_XOf h hD).2.1 hτ.1) x₁).mp hx₁X
    have hτL0 := hXL0 hτX
    have hΨτ := hact ⟨x₁, hx₁L0⟩ hτL0
    simp only at hΨτ
    rw [hx₁Ψ] at hΨτ
    simp only [mul_one, mul_inv_cancel] at hΨτ
    rw [pCoreOf_XOf h hD]
    rcases hD2.sign u hu with hs | hs
    · left
      have hm : τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ fsuL0 T L :=
        (fsuL0 T L).mul_mem hτL0 ((fsuL0 T L).inv_mem hx₁L0)
      refine ⟨(XOf T L Ψ A).mul_mem hτX ((XOf T L Ψ A).inv_mem hx₁X),
        mem_preIn.mpr ⟨hm, ?_, ?_⟩⟩
      · rw [psi_mul_inv hτL0 hx₁L0 hm, hΨτ, hx₁Ψ]
        exact hs k₀ hk₀K
      · rw [psi_mul_inv hτL0 hx₁L0 hm, hΨτ, hx₁Ψ]
        simp only [Prod.snd_mul, Prod.snd_inv, inv_one, mul_one]
        exact E.one_mem
    · right
      have hm : τ * x₁ * τ⁻¹ * x₁ ∈ fsuL0 T L := (fsuL0 T L).mul_mem hτL0 hx₁L0
      refine ⟨(XOf T L Ψ A).mul_mem hτX hx₁X, mem_preIn.mpr ⟨hm, ?_, ?_⟩⟩
      · rw [psi_mul hτL0 hx₁L0 hm, hΨτ, hx₁Ψ]
        exact hs k₀ hk₀K
      · rw [psi_mul hτL0 hx₁L0 hm, hΨτ, hx₁Ψ]
        simp only [Prod.snd_mul, mul_one]
        exact E.one_mem

theorem core_bundle (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hD2 : ParData2 K E)
    (hA : A = L32.Pa ∨ A = L32.Pb) {K₁ : Subgroup G} {s : G} (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hbad : pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s))
    (hST₁ : T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s) ≤ T1 T L) :
    T1 T L ≤ Subgroup.normalizer (K₁ : Set G) ∧
      T1 T L ≤ Subgroup.normalizer (CFSG.conjugate K₁ s : Set G) ∧
      ⁅K₁, CFSG.conjugate K₁ s⁆ ≤ pCoreOf 2 K₁ ⊓ pCoreOf 2 (CFSG.conjugate K₁ s) ∧
      ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
        ∃ y ∈ K₁ ⊔ CFSG.conjugate K₁ s, y ∈ Subgroup.normalizer (T1 T L : Set G) ∧
          n * y⁻¹ ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := h.hyp.fsu.simple
  have hKl : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  obtain ⟨hXK, hG₀K, hS⟩ := inGzero_data h (A := A)
  have hH2 := pCoreOf_GA_ne_bot h311 h hD hA
  have hsG₀ : s ∈ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right hs)
  have hK₂ : CFSG.conjugate K₁ s ∈
      cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj s⁻¹) hK₁
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ hsG₀))] at h1
  have hne : K₁ ≠ CFSG.conjugate K₁ s := SecA.ne_conjugate hsn
  obtain ⟨e₂⟩ := nonempty_modO2_conjugate K₁ s
  have hc₁ := C10P34.center_eq_bot_of_mulEquiv e
  have hc₂ := C10P34.center_eq_bot_of_mulEquiv (e₂.trans e)
  obtain ⟨φ, hφ, hker, hφ₁, hφ₂⟩ := exists_pair_prod hKl h.h37 hH2 hK₁ hK₂ hne hc₁ hc₂
  rw [hK] at hXK hS hG₀K
  have hc : C10P34.PairCtx (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) K₁
      (CFSG.conjugate K₁ s) φ :=
    ⟨hK₁, hK₂, hne, fun L₁ L₂ h₁ h₂ hne' =>
      (Vol2Native.lemma_1_2_1_two hKl h.h37 hH2 h₁ h₂ hne').1, hG₀K, hφ, hker, hφ₁, hφ₂, hc₁, hc₂⟩
  have hp5 : 5 ≤ p := by
    have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK₁)
    exact C10P34.five_le_of_isPerfect (by rintro rfl; omega) e
  obtain ⟨P3, hP3X, hP3, hP33⟩ := exists_E9_le_XOf h hD
  have hXi := isXi_XOf h hD
  have hTH : T ≤ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    le_sup_right.trans le_sup_right
  have hO : ∀ k : ↥(K₁ ⊔ CFSG.conjugate K₁ s),
      (k : G) ∈ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  obtain ⟨x₁, hx₁X, hx₁3, hx₁O, hτ⟩ := exists_x1 h hD hD2
  have hN₁ := E9.le_normalizer_of_core hc h8 (e₂.trans e) hS hTH inf_le_left hST₁ hXK hbad
    hx₁X hx₁3 hx₁O hτ
  have hN₂ : T1 T L ≤ Subgroup.normalizer (CFSG.conjugate K₁ s : Set G) := by
    intro τ hτ
    rcases hc.fix_or_swap (hTH hτ.1) with ⟨-, h2⟩ | ⟨h12, -⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h2
    · exfalso
      have h1 := hN₁ hτ
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1
      have h2 : K₁.map (MulAut.conj τ).toMonoidHom = K₁ := h1
      rw [h12] at h2
      exact hne h2.symm
  refine ⟨hN₁, hN₂, hc.comm K₁ _ hK₁ hK₂ hne, fun n hnT hodd => ?_⟩
  obtain ⟨y, hyK, hyT, hy⟩ := E9.exists_inner_witness hc h8 e (e₂.trans e) hS
    h.hyp.fsu.sylow.1 hTH inf_le_left hST₁ (Subgroup.mem_sup_left hnT) hnT hodd
  refine ⟨y, hyK, hyT, ?_⟩
  have hnK := hc.normal (Subgroup.mem_sup_left hnT)
  have hyK' : y ∈ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hyK
  refine E9.mem_normalizer_of_inner hc hp5 e (e₂.trans e) hXK hXi.1.symm
    (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1
    (Subgroup.mul_mem _ hnK (Subgroup.inv_mem _ hyK')) (a₁ := 1) (a₂ := 1)
    (fun z hz hz' => ?_) (Subgroup.one_mem _) (Subgroup.one_mem _)
  have h1 : φ ⟨n * y⁻¹ * z * (n * y⁻¹)⁻¹, hz'⟩ * (φ ⟨z, hz⟩)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact hO _ (hy z hz)
  rw [mul_inv_eq_one] at h1
  rw [h1]
  simp

end CFSG.Quasithin.Vol2.Ch10.SecB
