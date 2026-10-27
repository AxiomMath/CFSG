module

public import CFSG.RankThree.GF2n.Stroth80.Sec78CV
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.GF2n.Stroth80.Sec54Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec54_card_Wt_eq (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ 2 * Nat.card ↥(Vt M (LB M Q B) B Z t) := by
  classical
  have hn : n = 2 * m + 1 := sec54_n_eq h34 h51 hc hs hm hV hN
  have hWmul : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
      Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Q * Nat.card Z :=
    hc.card_Wt_mul_card_Vt t
  rw [hs.width, SpMNat.card_V hV, hn] at hWmul
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(Vt M (LB M Q B) B Z t))) ?_
  rw [SpMNat.card_V hV, hWmul]
  calc Nat.card Z ^ (2 * (2 * m + 1) + 1) * Nat.card Z
      = Nat.card Z ^ (2 * (2 * m + 1) + 1 + 1) := (pow_succ _ _).symm
    _ = Nat.card Z ^ (2 + (2 * m + 1) + (2 * m + 1)) := by
        congr 1
        ring
    _ = Nat.card Z ^ 2 * Nat.card Z ^ (2 * m + 1) * Nat.card Z ^ (2 * m + 1) := by
        rw [pow_add, pow_add]

theorem sec54_proj_Wt (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) {A₁ A₂ : Subgroup G}
    (hZA₁ : Z ≤ A₁) (hA₁W : A₁ ≤ Wt Q (Vt M (LB M Q B) B Z t))
    (hZA₂ : Z ≤ A₂) (hA₂W : A₂ ≤ Wt Q (Vt M (LB M Q B) B Z t))
    (hsup : A₁ ⊔ A₂ = Wt Q (Vt M (LB M Q B) B Z t)) (hinf : A₁ ⊓ A₂ = Z)
    (hinv : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A₁ = A₁ ∧ conjSubgroup r A₂ = A₂) :
    Vt M (LB M Q B) B Z t ≤ A₁ ∨ Vt M (LB M Q B) B Z t ≤ A₂ := by
  classical
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  obtain ⟨K, hK, hKf, hKcard, hrep⟩ := hV
  letI := hK
  letI := hKf
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI hchar : CharP K 2 := charP_two_of_card_eq_two_pow (hKcard.trans hZ2)
  have hV' : SpMNat hc t m := ⟨K, hK, hKf, hKcard, hrep⟩
  have hVW : V ≤ W := sec7ctr_Vt_le_Wt h34 hc hs
  have hWQ : W ≤ Q := inf_le_left
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hWW : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ Z := fun x hx y hy =>
    hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy)
  have hinvV : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r V = V := fun r hr =>
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hr)
  have hUinv : ∀ (A : Subgroup G), (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) →
      ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ V ⊓ A, r * u * r⁻¹ ∈ V ⊓ A := by
    intro A hA r hr u hu
    constructor
    · have hmem : r * u * r⁻¹ ∈ conjSubgroup r V := ⟨u, hu.1, rfl⟩
      rwa [hinvV r hr] at hmem
    · have hmem : r * u * r⁻¹ ∈ conjSubgroup r A := ⟨u, hu.2, rfl⟩
      rwa [hA r hr] at hmem
  have hZU₁ : Z ≤ V ⊓ A₁ := le_inf hZV hZA₁
  have hZU₂ : Z ≤ V ⊓ A₂ := le_inf hZV hZA₂
  have hUnat : ∀ (A : Subgroup G), (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) →
      Z ≤ V ⊓ A → V ⊓ A ≤ V → V ⊓ A = Z ∨ V ⊓ A = V := fun A hA hZA hAV =>
    hrep.eq_or_eq_of_invariant natIrred_statedSp addCommutantScalar_statedSp
      (R := Rt M (LB M Q B) t) (V := V) (Z := Z) (N := hc.CN t) (U := V ⊓ A)
      hZA hAV (hUinv A hA)
  rcases hUnat A₁ (fun r hr => (hinv r hr).1) hZU₁ inf_le_left with hU₁ | hU₁
  · rcases hUnat A₂ (fun r hr => (hinv r hr).2) hZU₂ inf_le_left with hU₂ | hU₂
    ·
      exfalso
      have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
      have hWc : Nat.card ↥W = Nat.card Z ^ 2 * Nat.card ↥V :=
        sec54_card_Wt_eq h34 h51 hc hs hm hV' hN
      have hVc : Nat.card ↥V = Nat.card Z ^ (2 * m + 1) := SpMNat.card_V hV'
      have hcommVA : ∀ (A : Subgroup G), A ≤ W → ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := by
        intro A hA v hv a ha
        have hcent : a ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp (hA ha)).2
        exact Subgroup.mem_centralizer_iff.mp hcent v hv
      have hbound : ∀ (A : Subgroup G), A ≤ W → V ⊓ A = Z → Nat.card ↥A ≤ Nat.card Z ^ 3 := by
        intro A hA hVA
        have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V A
          (hcommVA A hA)).1
        rw [hVA] at hprod
        have hsupW : V ⊔ A ≤ W := sup_le hVW hA
        have hleW : Nat.card ↥(V ⊔ A) ≤ Nat.card ↥W :=
          Nat.card_le_card_of_injective (fun x : ↥(V ⊔ A) => (⟨x.1, hsupW x.2⟩ : ↥W))
            (by intro x y hxy; simpa using hxy)
        have h1 : Nat.card ↥V * Nat.card ↥A ≤ Nat.card Z ^ 2 * Nat.card ↥V * Nat.card Z := by
          calc Nat.card ↥V * Nat.card ↥A = Nat.card ↥(V ⊔ A) * Nat.card Z := hprod.symm
            _ ≤ Nat.card ↥W * Nat.card Z := Nat.mul_le_mul_right _ hleW
            _ = Nat.card Z ^ 2 * Nat.card ↥V * Nat.card Z := by rw [hWc]
        have h2 : Nat.card ↥V * Nat.card ↥A ≤ Nat.card ↥V * Nat.card Z ^ 3 := by
          calc Nat.card ↥V * Nat.card ↥A
              ≤ Nat.card Z ^ 2 * Nat.card ↥V * Nat.card Z := h1
            _ = Nat.card ↥V * Nat.card Z ^ 3 := by ring
        exact Nat.le_of_mul_le_mul_left h2 (Nat.card_pos (α := ↥V))
      have hA₁le : Nat.card ↥A₁ ≤ Nat.card Z ^ 3 := hbound A₁ hA₁W hU₁
      have hA₂le : Nat.card ↥A₂ ≤ Nat.card Z ^ 3 := hbound A₂ hA₂W hU₂
      have hA₁N : A₁ ≤ Subgroup.normalizer (A₂ : Set G) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hcomm : ⁅a, x⁆ ∈ Z := hWW a (hA₁W ha) x (hA₂W hx)
          have hmem : ⁅a, x⁆ * x ∈ A₂ := A₂.mul_mem (hZA₂ hcomm) hx
          rwa [show ⁅a, x⁆ * x = a * x * a⁻¹ by rw [commutatorElement_def]; group] at hmem
        · intro hx
          have hy : a * x * a⁻¹ ∈ A₂ := hx
          have hcomm : ⁅a⁻¹, a * x * a⁻¹⁆ ∈ Z :=
            hWW a⁻¹ (W.inv_mem (hA₁W ha)) (a * x * a⁻¹) (hA₂W hy)
          have hmem : ⁅a⁻¹, a * x * a⁻¹⁆ * (a * x * a⁻¹) ∈ A₂ :=
            A₂.mul_mem (hZA₂ hcomm) hy
          rwa [show ⁅a⁻¹, a * x * a⁻¹⁆ * (a * x * a⁻¹) = x by
            rw [commutatorElement_def]; group] at hmem
      have hcardW : Nat.card ↥W * Nat.card Z = Nat.card ↥A₁ * Nat.card ↥A₂ := by
        have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (H := A₁) (K := A₂) hA₁N
        rw [hsup, hinf] at h
        exact h
      have h1 : Nat.card ↥W * Nat.card Z ≤ Nat.card Z ^ 3 * Nat.card Z ^ 3 := by
        rw [hcardW]
        exact Nat.mul_le_mul hA₁le hA₂le
      rw [hWc, hVc] at h1
      have h1' : (Nat.card Z ^ 2 * Nat.card Z ^ (2 * m + 1)) * Nat.card Z ≤
          Nat.card Z ^ 3 * Nat.card Z ^ 3 := h1
      have e : 2 * m + 3 = 2 + (2 * m + 1) := by ring
      have h2 : Nat.card Z ^ (2 * m + 3) * Nat.card Z ≤ Nat.card Z ^ 6 := by
        calc Nat.card Z ^ (2 * m + 3) * Nat.card Z
            = (Nat.card Z ^ 2 * Nat.card Z ^ (2 * m + 1)) * Nat.card Z := by rw [e, pow_add]
          _ ≤ Nat.card Z ^ 3 * Nat.card Z ^ 3 := h1'
          _ = Nat.card Z ^ 6 := by rw [← pow_add]
      have h3 : Nat.card Z ^ (2 * m + 3) * Nat.card Z = Nat.card Z ^ (2 * m + 4) := by
        rw [← pow_succ]
      rw [h3] at h2
      have h4 : Nat.card Z ^ 6 < Nat.card Z ^ (2 * m + 4) :=
        Nat.pow_lt_pow_right hq1 (by omega)
      exact absurd h2 (not_le.mpr h4)
    · exact Or.inr (hU₂ ▸ inf_le_right)
  · exact Or.inl (hU₁ ▸ inf_le_right)

theorem sec54_centralizer_Wt_le_Z (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) {w : G}
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t))
    (hwR : ∀ s ∈ Rt M (LB M Q B) t, ⁅s, w⁆ ∈ Z) : w ∈ Z := by
  classical
  have hsp : SpNat hc t := by
    obtain ⟨K, hK, hKf, hKc, hrep⟩ := hV
    exact ⟨K, hK, hKf, hKc, m, hm, hrep⟩
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hs8 : Sec8Hyp hc n t := ⟨hs, ⟨m, hm, hV⟩⟩
  have hR : Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B) :=
    (sec7A_of_hypPlane h34 hRoot h51 hs8 hr hplane).gen
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have h35C : CQt Q Z (LB M Q (conjSubgroup r B)) =
      ((conjSubgroup r B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hcC hs.width hs.n_gt (hc.noA2_conj hs.noA2 hrM)
      (hs.gen.conj_of_mem hrM)).2.1
  have hwQ : w ∈ Q := (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hw
  have hwB : w ∈ (B ⊔ Z : Subgroup G) := by
    have h1 : w ∈ CQt Q Z (LB M Q B) :=
      ⟨hwQ, fun l hl => hwR l (hR ▸ Subgroup.mem_sup_left hl)⟩
    rwa [h35] at h1
  have hwC : w ∈ (conjSubgroup r B ⊔ Z : Subgroup G) := by
    have h1 : w ∈ CQt Q Z (LB M Q (conjSubgroup r B)) :=
      ⟨hwQ, fun l hl => hwR l (hR ▸ Subgroup.mem_sup_right hl)⟩
    rwa [h35C] at h1
  have hBinf : B ⊓ QB (conjSubgroup r B) = ⊥ :=
    sec53_sp_B_inf_QB_conj_eq_bot h34 hc hs hsp hr hplane
  have hCQ : conjSubgroup r B ⊔ Z ≤ QB (conjSubgroup r B) :=
    sup_le hcC.B_le_QB hcC.Z_le_QB.1
  have hsplit : (B ⊔ Z : Subgroup G) ⊓ (conjSubgroup r B ⊔ Z) ≤ Z := by
    intro x hx
    obtain ⟨hxBZ, hxCZ⟩ := Subgroup.mem_inf.mp hx
    have hBZnorm : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
      hc.hyp.Z_normal.2 (hc.Z_le_QB.2 hb)
    have hx' : x ∈ (B : Set G) * (Z : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B Z hBZnorm]
      exact hxBZ
    obtain ⟨b, hbB, z, hzZ, rfl⟩ := hx'
    have hxCQ : b * z ∈ QB (conjSubgroup r B) := hCQ hxCZ
    have hzCQ : z ∈ QB (conjSubgroup r B) := hcC.Z_le_QB.1 hzZ
    have hbCQ : b ∈ QB (conjSubgroup r B) := by
      have h : b * z * z⁻¹ ∈ QB (conjSubgroup r B) :=
        (QB (conjSubgroup r B)).mul_mem hxCQ ((QB (conjSubgroup r B)).inv_mem hzCQ)
      simpa using h
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hbB, hbCQ⟩
    rw [Subgroup.mem_bot] at hbBot
    simpa [hbBot] using hzZ
  exact hsplit (Subgroup.mem_inf.mpr ⟨hwB, hwC⟩)

theorem stroth54FC_contra (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z)
    (hcomm : ∀ s ∈ Rt M (LB M Q B) t,
      ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t)
    (hNW : ∀ x ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, y⁆ ∈ Z) : False := by
  classical
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set N : Subgroup G := hc.CN t with hNdef
  set R : Subgroup G := Rt M (LB M Q B) t with hRdef
  obtain ⟨K, hK, hKf, hKcard, φ, hφ, hker, hact⟩ := hV
  letI := hK
  letI := hKf
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI hchar : CharP K 2 := charP_two_of_card_eq_two_pow (hKcard.trans hZ2)
  have hrep' : NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hφ, hker, hact⟩
  have hV' : SpMNat hc t m := ⟨K, hK, hKf, hKcard, hrep'⟩
  have hsp : SpNat hc t := ⟨K, hK, hKf, hKcard, m, hm, hrep'⟩
  have hKq : 2 < Nat.card K := by rw [hKcard]; have := hc.hyp.q4; omega
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVP : V ≤ W := sec7ctr_Vt_le_Wt h34 hc hs
  have hWQ : W ≤ Q := inf_le_left
  have hsec : SecHyp R W Z := by
    refine ⟨hZV.trans hVP, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact hc.hyp.toHyp79.comm_mem_V (hWQ hx) (hWQ hy)
    · intro x hx
      exact hc.hyp.toHyp79.sq_mem_V (hWQ hx)
    · intro ρ hρ x hx
      have h1 : ρ ∈ Subgroup.normalizer (Wt Q (Vt M (LB M Q B) B Z t) : Set G) :=
        sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ))
          (hc.Rt_normalizes_Vt hs.mem hρ)
      exact (Subgroup.mem_normalizer_iff.mp h1 x).mp hx
    · intro ρ hρ x hx
      exact (Subgroup.mem_normalizer_iff.mp ((hc.hyp.Z_normal).2 (hc.Rt_le_M t hρ)) x).mp hx
  have hNW' : ∀ x ∈ N, ∀ y ∈ W, ⁅x, y⁆ ∈ Z := by
    simpa [hNdef, hWdef, hVdef] using hNW
  have hcardW : Nat.card ↥W = Nat.card Z ^ 2 * Nat.card ↥V :=
    sec54_card_Wt_eq h34 h51 hc hs hm hV' hN
  have hnotindec : ¬ IsIndecSec R W Z := by
    intro hind
    have hle := stroth_2_2_secSp (m := m) (Z := Z) (V := Vt M (LB M Q B) B Z t)
      (R := Rt M (LB M Q B) t) (N := hc.CN t) (P := Wt Q (Vt M (LB M Q B) B Z t))
      hm hKq φ hφ hker hsec hNW' hZV hVP hact hcomm hind
    rw [hcardW, hKcard] at hle
    have hq2 : Nat.card Z ^ 2 ≤ Nat.card Z :=
      Nat.le_of_mul_le_mul_right hle (Nat.card_pos (α := ↥V))
    have hqle : Nat.card Z ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ Nat.card Z := by omega
      rw [pow_two] at hq2
      have h3 : Nat.card Z * 2 ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _ h2
      have h4 : Nat.card Z * 2 ≤ Nat.card Z := le_trans h3 hq2
      have h5 : 0 < Nat.card Z := Nat.card_pos
      omega
    have := hc.hyp.q4
    omega
  obtain ⟨A₁, A₂, hZA₁, hA₁W, hZA₂, hA₂W, hA₁ne, hA₂ne, hsup, hinf, hinv⟩ :=
    Classical.not_not.mp hnotindec
  have hproj : V ≤ A₁ ∨ V ≤ A₂ :=
    sec54_proj_Wt h34 h51 hc hs hm hV' hN hZA₁ hA₁W hZA₂ hA₂W hsup hinf hinv
  have hfinish : ∀ (A : Subgroup G), Z ≤ A → A ≠ Z → A ≤ W → A ⊓ V = Z →
      (∀ ρ ∈ R, conjSubgroup ρ A = A) → False := by
    intro A hZA hAne hAW hAV hinvA
    have hlt : Z < A := lt_of_le_of_ne hZA (Ne.symm hAne)
    obtain ⟨b, hbA, hbZ⟩ := Set.exists_of_ssubset hlt
    have hbW : b ∈ W := hAW hbA
    have hbR : ∀ s ∈ R, ⁅s, b⁆ ∈ Z := by
      intro s hsR
      have h1 : ⁅s, b⁆ ∈ V := hcomm s hsR b hbW
      have h2 : ⁅s, b⁆ ∈ A := by
        have hconj : conjSubgroup s A = A := hinvA s hsR
        have hmem : s * b * s⁻¹ ∈ A := by
          rw [← hconj]
          exact ⟨b, hbA, rfl⟩
        rw [commutatorElement_def]
        exact A.mul_mem hmem (A.inv_mem hbA)
      rw [← hAV]
      exact ⟨h2, h1⟩
    obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot hs hsp
    exact hbZ (sec54_centralizer_Wt_le_Z h34 hRoot h51 hc hs hm hV' hr hplane hbW hbR)
  rcases hproj with hVA₁ | hVA₂
  · refine hfinish A₂ hZA₂ hA₂ne hA₂W ?_ (fun ρ hρ => (hinv ρ hρ).2)
    refine le_antisymm ?_ (le_inf hZA₂ hZV)
    rintro x ⟨hxA₂, hxV⟩
    rw [← hinf]
    exact ⟨hVA₁ hxV, hxA₂⟩
  · refine hfinish A₁ hZA₁ hA₁ne hA₁W ?_ (fun ρ hρ => (hinv ρ hρ).1)
    refine le_antisymm ?_ (le_inf hZA₁ hZV)
    rintro x ⟨hxA₁, hxV⟩
    rw [← hinf]
    exact ⟨hxA₁, hVA₂ hxV⟩


theorem stroth54Statement_of_contra (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hcomm : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G) (m : ℕ), Sec5Hyp hc n t → 2 ≤ m → SpMNat hc t m →
      Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z →
      ∀ s ∈ Rt M (LB M Q B) t,
        ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t)
    (hNW : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G) (m : ℕ), Sec5Hyp hc n t → 2 ≤ m → SpMNat hc t m →
      Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z →
      ∀ x ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, y⁆ ∈ Z) :
    Stroth54Statement := by
  intro G _ _ M Q Z B hc n t hs hsp hN
  obtain ⟨K, hK, hKf, hKcard, m, hm, hrep⟩ := hsp
  letI := hK
  letI := hKf
  exact stroth54FC_contra h34 hRoot h51 hc hs hm ⟨K, hK, hKf, hKcard, hrep⟩ hN
    (hcomm G M Q Z B hc n t m hs hm ⟨K, hK, hKf, hKcard, hrep⟩ hN)
    (hNW G M Q Z B hc n t m hs hm ⟨K, hK, hKf, hKcard, hrep⟩ hN)
end CFSG.RankThree.GF2n.Stroth80
