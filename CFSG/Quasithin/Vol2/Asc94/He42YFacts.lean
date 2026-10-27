module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42yf_gl2_symm : ∀ h : GL2, h ^ 3 = 1 → Matrix.transpose h.val = h.val := by
  decide +kernel

private theorem he42yf_gl2_left_fpf :
    ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M : M2, g.val * M = M → M = 0 := by
  decide +kernel

private theorem he42yf_gl2_right_fpf :
    ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M : M2, M * g.val = M → M = 0 := by
  decide +kernel

private theorem he42yf_val_comm {a b : GL2} (h : Commute a b) : a.val * b.val = b.val * a.val := by
  have := congrArg Units.val h.eq
  simpa only [Units.val_mul] using this

private theorem he42yf_conj_mem_iff (H : Subgroup G) {n : G} (hn : n ∈ H) (x : G) :
    x ∈ H ↔ n * x * n⁻¹ ∈ H := by
  constructor
  · intro hx
    exact H.mul_mem (H.mul_mem hn hx) (H.inv_mem hn)
  · intro hx
    have h := H.mul_mem (H.mul_mem (H.inv_mem hn) hx) hn
    have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    rwa [e] at h

private theorem he42yf_cent_iff (H : Set G) {n : G} (hH : ∀ b, b ∈ H ↔ n * b * n⁻¹ ∈ H) (x : G) :
    x ∈ centralizer H ↔ n * x * n⁻¹ ∈ centralizer H := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx c hc
    have hc' : n⁻¹ * c * n ∈ H := by
      apply (hH _).mpr
      have e : n * (n⁻¹ * c * n) * n⁻¹ = c := by group
      rw [e]
      exact hc
    have h1 := hx _ hc'
    calc c * (n * x * n⁻¹) = n * ((n⁻¹ * c * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * c * n)) * n⁻¹ := by rw [h1]
      _ = n * x * n⁻¹ * c := by group
  · intro hx b hb
    have hb' : n * b * n⁻¹ ∈ H := (hH b).mp hb
    have h1 := hx _ hb'
    calc b * x = n⁻¹ * ((n * b * n⁻¹) * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * (n * b * n⁻¹)) * n := by rw [h1]
      _ = x * b := by group

namespace HeSetup

variable (S : HeSetup G)

private theorem he42yf_rhoG_inv {n : G} (hn : n ∈ S.N) : S.rhoG n⁻¹ = (S.rhoG n)⁻¹ := by
  have e : (⟨n⁻¹, S.N.inv_mem hn⟩ : ↥S.N) = (⟨n, hn⟩ : ↥S.N)⁻¹ := rfl
  rw [S.rhoG_of_mem (S.N.inv_mem hn), S.rhoG_of_mem hn, e, map_inv]

private theorem he42yf_rhoG_mul {n n' : G} (hn : n ∈ S.N) (hn' : n' ∈ S.N) :
    S.rhoG (n * n') = S.rhoG n * S.rhoG n' := by
  have e : (⟨n * n', S.N.mul_mem hn hn'⟩ : ↥S.N) = (⟨n, hn⟩ : ↥S.N) * ⟨n', hn'⟩ := rfl
  rw [S.rhoG_of_mem (S.N.mul_mem hn hn'), S.rhoG_of_mem hn, S.rhoG_of_mem hn', e, map_mul]

private theorem he42yf_m_conj {n : G} (hn : n ∈ S.N) {x : G} (hx : x ∈ S.A ⊓ S.A') :
    S.m (n * x * n⁻¹) = ((S.rhoG n).1 : M2) * S.m x * ((S.rhoG n).2 : M2)ᵀ := by
  rw [S.rhoG_of_mem hn]
  exact S.hD.hT.m_conj S.N S.hD.hK.norm ⟨n, hn⟩ hx

private theorem he42yf_m_conj' {n : G} (hn : n ∈ S.N) {P Q : GL2} (hρ : S.rhoG n = (P, Q))
    {x : G} (hx : x ∈ S.A ⊓ S.A') : S.m (n * x * n⁻¹) = (P : M2) * S.m x * (Q : M2)ᵀ := by
  rw [S.he42yf_m_conj hn hx, hρ]

private theorem he42yf_u_conj {n : G} (hn : n ∈ S.N) {x : G} (hx : x ∈ S.A) :
    S.u (n * x * n⁻¹) = ((S.rhoG n).1 : M2) *ᵥ S.u x := by
  rw [S.rhoG_of_mem hn]
  exact S.hD.hT.u_conj S.N S.hD.hK.norm ⟨n, hn⟩ hx

private theorem he42yf_w_conj {n : G} (hn : n ∈ S.N) {x : G} (hx : x ∈ S.A') :
    S.w (n * x * n⁻¹) = ((S.rhoG n).2 : M2) *ᵥ S.w x := by
  rw [S.rhoG_of_mem hn]
  exact S.hD.hT.w_conj S.N S.hD.hK.norm ⟨n, hn⟩ hx

private theorem he42yf_B_fwd {n : G} (hn : n ∈ S.N) {P Q : GL2} (hρ : S.rhoG n = (P, Q))
    (hP : Commute S.g P) (hQ : Commute S.g Q) : ∀ b ∈ S.B, n * b * n⁻¹ ∈ S.B := by
  intro b hb
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hb' : b ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G) := hb
  obtain ⟨hbZ, hbc⟩ := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).mp hb'
  have hbc' : S.g.val * S.m b = S.m b * S.g.val := hbc
  have hnbZ : n * b * n⁻¹ ∈ S.A ⊓ S.A' := S.hD.mem_Z_conj hn hbZ
  have hm : S.m (n * b * n⁻¹) = (P : M2) * S.m b * (Q : M2)ᵀ := S.he42yf_m_conj' hn hρ hbZ
  have hgm : S.g.val * P.val = P.val * S.g.val := he42yf_val_comm hP
  have hQm : S.g.val * Q.val = Q.val * S.g.val := he42yf_val_comm hQ
  have hgT : Matrix.transpose S.g.val = S.g.val := he42yf_gl2_symm S.g hg3
  have hQt : S.g.val * (Q.val)ᵀ = (Q.val)ᵀ * S.g.val := by
    have h := congrArg Matrix.transpose hQm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hgT] at h
    exact h.symm
  show n * b * n⁻¹ ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G)
  refine (S.hD.mem_B_iff S.hxN S.hxa S.hx3).mpr ⟨hnbZ, ?_⟩
  rw [hm]
  show S.g.val * ((P : M2) * S.m b * (Q : M2)ᵀ) = ((P : M2) * S.m b * (Q : M2)ᵀ) * S.g.val
  calc S.g.val * ((P : M2) * S.m b * (Q : M2)ᵀ)
      = (S.g.val * (P : M2)) * S.m b * (Q : M2)ᵀ := by simp only [mul_assoc]
    _ = ((P : M2) * S.g.val) * S.m b * (Q : M2)ᵀ := by rw [hgm]
    _ = (P : M2) * (S.g.val * S.m b) * (Q : M2)ᵀ := by simp only [mul_assoc]
    _ = (P : M2) * (S.m b * S.g.val) * (Q : M2)ᵀ := by rw [hbc']
    _ = (P : M2) * S.m b * (S.g.val * (Q : M2)ᵀ) := by simp only [mul_assoc]
    _ = (P : M2) * S.m b * ((Q : M2)ᵀ * S.g.val) := by rw [hQt]
    _ = ((P : M2) * S.m b * (Q : M2)ᵀ) * S.g.val := by simp only [mul_assoc]

private theorem he42yf_B_iff {n : G} (hn : n ∈ S.N) {P Q : GL2} (hρ : S.rhoG n = (P, Q))
    (hP : Commute S.g P) (hQ : Commute S.g Q) : ∀ b : G, b ∈ S.B ↔ n * b * n⁻¹ ∈ S.B := by
  intro b
  refine ⟨S.he42yf_B_fwd hn hρ hP hQ b, fun hb => ?_⟩
  have hρ' : S.rhoG n⁻¹ = (P⁻¹, Q⁻¹) := by
    rw [S.he42yf_rhoG_inv hn, hρ] <;> rfl
  have h := S.he42yf_B_fwd (S.N.inv_mem hn) hρ' hP.inv_right hQ.inv_right (n * b * n⁻¹) hb
  have e : n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b := by group
  rwa [e] at h

end HeSetup

theorem HeSetup.stepYnorm (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepYnorm y₁ y₂ := by
  have hr₁' : (S.rhoG y₁).2 = 1 := by simp only [hY.rho₁]
  have hr₂ : (S.rhoG y₂).1 = 1 := by simp only [hY.rho₂]
  have hBy₁ : ∀ b : G, b ∈ S.B ↔ y₁ * b * y₁⁻¹ ∈ S.B :=
    S.he42yf_B_iff hY.mem₁ hY.rho₁ (Commute.refl _) (Commute.one_right _)
  have hBy₂ : ∀ b : G, b ∈ S.B ↔ y₂ * b * y₂⁻¹ ∈ S.B :=
    S.he42yf_B_iff hY.mem₂ hY.rho₂ (Commute.one_right _) (Commute.refl _)
  have hC₁ : ∀ x : G, x ∈ centralizer (S.B : Set G) ↔ y₁ * x * y₁⁻¹ ∈ centralizer (S.B : Set G) :=
    fun x => he42yf_cent_iff (S.B : Set G) hBy₁ x
  have hC₂ : ∀ x : G, x ∈ centralizer (S.B : Set G) ↔ y₂ * x * y₂⁻¹ ∈ centralizer (S.B : Set G) :=
    fun x => he42yf_cent_iff (S.B : Set G) hBy₂ x
  have hy₁A : y₁ ∈ normalizer (S.A : Set G) := S.hD.N_le_M hY.mem₁
  have hy₂A' : y₂ ∈ normalizer (S.A' : Set G) := S.hD'.N_le_M hY.mem₂
  have hL₁ : ∀ x : G, x ∈ S.L1 ↔ y₁ * x * y₁⁻¹ ∈ S.L1 := by
    intro x
    show x ∈ normalizer (S.A : Set G) ⊓ centralizer (S.B : Set G) ↔
      y₁ * x * y₁⁻¹ ∈ normalizer (S.A : Set G) ⊓ centralizer (S.B : Set G)
    simp only [Subgroup.mem_inf]
    exact and_congr (he42yf_conj_mem_iff _ hy₁A x) (hC₁ x)
  have hL₂ : ∀ x : G, x ∈ S.L2 ↔ y₂ * x * y₂⁻¹ ∈ S.L2 := by
    intro x
    show x ∈ normalizer (S.A' : Set G) ⊓ centralizer (S.B : Set G) ↔
      y₂ * x * y₂⁻¹ ∈ normalizer (S.A' : Set G) ⊓ centralizer (S.B : Set G)
    simp only [Subgroup.mem_inf]
    exact and_congr (he42yf_conj_mem_iff _ hy₂A' x) (hC₂ x)
  have hK₁ : ∀ x : G, x ∈ S.K ↔ y₁ * x * y₁⁻¹ ∈ S.K := by
    intro x
    show x ∈ S.N ⊓ centralizer (S.B : Set G) ↔ y₁ * x * y₁⁻¹ ∈ S.N ⊓ centralizer (S.B : Set G)
    simp only [Subgroup.mem_inf]
    exact and_congr (he42yf_conj_mem_iff S.N hY.mem₁ x) (hC₁ x)
  have hK₂ : ∀ x : G, x ∈ S.K ↔ y₂ * x * y₂⁻¹ ∈ S.K := by
    intro x
    show x ∈ S.N ⊓ centralizer (S.B : Set G) ↔ y₂ * x * y₂⁻¹ ∈ S.N ⊓ centralizer (S.B : Set G)
    simp only [Subgroup.mem_inf]
    exact and_congr (he42yf_conj_mem_iff S.N hY.mem₂ x) (hC₂ x)
  unfold HeSetup.StepYnorm
  refine ⟨⟨mem_normalizer_iff.mpr hL₁, mem_normalizer_iff.mpr hK₁, ?_⟩,
    ⟨mem_normalizer_iff.mpr hL₂, mem_normalizer_iff.mpr hK₂, ?_⟩⟩
  · intro j hj
    have hj' : j ∈ S.A ⊔ S.A' := hj
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := S.hD.exists_mul_of_mem_sup hj'
    have ha₁' : y₁ * a₁ * y₁⁻¹ ∈ S.A := (S.hD.hK.norm y₁ hY.mem₁).1 a₁ ha₁
    have hw : S.w (y₁ * a₂ * y₁⁻¹) = S.w a₂ := by
      rw [S.he42yf_w_conj hY.mem₁ ha₂, hr₁', Units.val_one, Matrix.one_mulVec]
    have hd : y₁ * a₂ * y₁⁻¹ * a₂⁻¹ ∈ S.A :=
      S.hD.hT.cw.mul_inv_mem ((S.hD.hK.norm y₁ hY.mem₁).2 a₂ ha₂) ha₂ hw
    have e : y₁ * (a₁ * a₂) * y₁⁻¹ * (a₁ * a₂)⁻¹ =
        (y₁ * a₁ * y₁⁻¹) * (y₁ * a₂ * y₁⁻¹ * a₂⁻¹) * a₁⁻¹ := by group
    rw [e]
    exact S.A.mul_mem (S.A.mul_mem ha₁' hd) (S.A.inv_mem ha₁)
  · intro j hj
    have hj' : j ∈ S.A' ⊔ S.A := by
      rw [sup_comm]
      exact hj
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := S.hD'.exists_mul_of_mem_sup hj'
    have ha₂' : y₂ * a₂ * y₂⁻¹ ∈ S.A := (S.hD.hK.norm y₂ hY.mem₂).1 a₂ ha₂
    have hu : S.u (y₂ * a₂ * y₂⁻¹) = S.u a₂ := by
      rw [S.he42yf_u_conj hY.mem₂ ha₂, hr₂, Units.val_one, Matrix.one_mulVec]
    have hd : y₂ * a₂ * y₂⁻¹ * a₂⁻¹ ∈ S.A' := S.hD.hT.cu.mul_inv_mem ha₂' ha₂ hu
    have ha₁' : y₂ * a₁ * y₂⁻¹ ∈ S.A' := (S.hD.hK.norm y₂ hY.mem₂).2 a₁ ha₁
    have e : y₂ * (a₁ * a₂) * y₂⁻¹ * (a₁ * a₂)⁻¹ =
        (y₂ * a₁ * y₂⁻¹) * (y₂ * a₂ * y₂⁻¹ * a₂⁻¹) * a₁⁻¹ := by group
    rw [e]
    exact S.A'.mul_mem (S.A'.mul_mem ha₁' hd) (S.A'.inv_mem ha₁)

theorem HeSetup.stepYfpf (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepYfpf y₁ y₂ := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hr₁ : (S.rhoG y₁).1 = S.g := by simp only [hY.rho₁]
  have hr₁' : (S.rhoG y₁).2 = 1 := by simp only [hY.rho₁]
  have hr₂ : (S.rhoG y₂).1 = 1 := by simp only [hY.rho₂]
  have hr₂' : (S.rhoG y₂).2 = S.g := by simp only [hY.rho₂]
  unfold HeSetup.StepYfpf
  refine ⟨?_, ?_⟩
  · intro a ha hcomm
    have hcomm' : y₁ * a * y₁⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    have hu : S.g.val *ᵥ S.u a = S.u a := by
      have h := S.he42yf_u_conj hY.mem₁ ha
      rw [hcomm', hr₁] at h
      exact h.symm
    have hua : S.u a = 0 := gl2_order_three_fpf S.g hg3 hg1 _ hu
    have haA' : a ∈ S.A' := (S.hD.hT.cu.zero a ha).mp hua
    have haZ : a ∈ S.A ⊓ S.A' := ⟨ha, haA'⟩
    have hm : S.g.val * S.m a = S.m a := by
      have h := S.he42yf_m_conj hY.mem₁ haZ
      rw [hcomm', hr₁, hr₁', Units.val_one, Matrix.transpose_one, mul_one] at h
      exact h.symm
    have hma : S.m a = 0 := he42yf_gl2_left_fpf S.g hg3 hg1 _ hm
    exact S.hD.hT.minj a haZ 1 (Subgroup.one_mem _) (by rw [hma, S.hD.hT.m_one])
  · intro a ha hcomm
    have hcomm' : y₂ * a * y₂⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    have hw : S.g.val *ᵥ S.w a = S.w a := by
      have h := S.he42yf_w_conj hY.mem₂ ha
      rw [hcomm', hr₂'] at h
      exact h.symm
    have hwa : S.w a = 0 := gl2_order_three_fpf S.g hg3 hg1 _ hw
    have haA : a ∈ S.A := (S.hD.hT.cw.zero a ha).mp hwa
    have haZ : a ∈ S.A ⊓ S.A' := ⟨haA, ha⟩
    have hm : S.m a * S.g.val = S.m a := by
      have h := S.he42yf_m_conj hY.mem₂ haZ
      rw [hcomm', hr₂, hr₂', Units.val_one, Matrix.one_mul, he42yf_gl2_symm S.g hg3] at h
      exact h.symm
    have hma : S.m a = 0 := he42yf_gl2_right_fpf S.g hg3 hg1 _ hm
    exact S.hD.hT.minj a haZ 1 (Subgroup.one_mem _) (by rw [hma, S.hD.hT.m_one])

theorem HeSetup.stepY0 (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepY0 y₁ y₂ := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hy₂i : y₂⁻¹ ∈ S.N := S.N.inv_mem hY.mem₂
  have hy₀ : y₁ * y₂⁻¹ ∈ S.N := S.N.mul_mem hY.mem₁ hy₂i
  have hρ₀ : S.rhoG (y₁ * y₂⁻¹) = (S.g, S.g⁻¹) := by
    rw [S.he42yf_rhoG_mul hY.mem₁ hy₂i, S.he42yf_rhoG_inv hY.mem₂, hY.rho₁, hY.rho₂]
    ext <;> simp
  have hnJ : y₁ * y₂⁻¹ ∉ S.J := by
    intro hJ
    have h1 : S.rhoG (y₁ * y₂⁻¹) = 1 := by
      rw [S.rhoG_of_mem hy₀]
      exact S.hD.hT.rho_J S.hD.hK ⟨y₁ * y₂⁻¹, hy₀⟩ hJ
    rw [hρ₀] at h1
    exact hg1 (congrArg Prod.fst h1)
  have hne : y₁ * y₂⁻¹ ≠ 1 := fun h => hnJ (by rw [h]; exact Subgroup.one_mem _)
  have hpow : (y₁ * y₂⁻¹) ^ 3 = 1 := by
    have hcom : Commute y₁ y₂ := hY.comm
    have hc : Commute y₁ y₂⁻¹ := hcom.inv_right
    have h1 : y₁ ^ 3 = 1 := by
      rw [← hY.ord₁]
      exact pow_orderOf_eq_one y₁
    have h2 : y₂ ^ 3 = 1 := by
      rw [← hY.ord₂]
      exact pow_orderOf_eq_one y₂
    rw [hc.mul_pow, inv_pow, h1, h2, inv_one, one_mul]
  unfold HeSetup.StepY0
  refine ⟨?_, hnJ, ?_⟩
  · show y₁ * y₂⁻¹ ∈ S.N ⊓ centralizer (S.B : Set G)
    rw [Subgroup.mem_inf]
    refine ⟨hy₀, ?_⟩
    rw [mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G) := hb
    obtain ⟨hbZ, hbc⟩ := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).mp hb'
    have hbc' : S.g.val * S.m b = S.m b * S.g.val := hbc
    have hgi3 : (S.g⁻¹) ^ 3 = 1 := by rw [inv_pow, hg3, inv_one]
    have hgT' : Matrix.transpose (S.g⁻¹ : GL2).val = (S.g⁻¹ : GL2).val :=
      he42yf_gl2_symm _ hgi3
    have hm : S.m (y₁ * y₂⁻¹ * b * (y₁ * y₂⁻¹)⁻¹) = S.m b := by
      rw [S.he42yf_m_conj' hy₀ hρ₀ hbZ, hgT']
      calc S.g.val * S.m b * (S.g⁻¹ : GL2).val
          = (S.m b * S.g.val) * (S.g⁻¹ : GL2).val := by rw [hbc']
        _ = S.m b * (S.g.val * (S.g⁻¹ : GL2).val) := by rw [mul_assoc]
        _ = S.m b := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hconj : y₁ * y₂⁻¹ * b * (y₁ * y₂⁻¹)⁻¹ = b :=
      S.hD.hT.minj _ (S.hD.mem_Z_conj hy₀ hbZ) _ hbZ hm
    have h3 : y₁ * y₂⁻¹ * b = b * (y₁ * y₂⁻¹) := mul_inv_eq_iff_eq_mul.mp hconj
    exact h3.symm
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hpow hne

end CFSG.Quasithin.A94.He42
