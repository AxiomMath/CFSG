module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42r_fix_coset {y a : G} (hy : y ^ 3 = 1) {Q : Subgroup G}
    (hQ : Nat.card Q = 16) (hstab : ∀ q ∈ Q, a⁻¹ * (y * (a * q) * y⁻¹) ∈ Q) :
    ∃ q ∈ Q, y * (a * q) * y⁻¹ = a * q := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f : Q → Q := fun q => ⟨a⁻¹ * (y * (a * q) * y⁻¹), hstab q q.2⟩
  have hit : ∀ (n : ℕ) (q : Q), ((f^[n] q : Q) : G) = a⁻¹ * (y ^ n * (a * q) * (y ^ n)⁻¹) := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply']
      change a⁻¹ * (y * (a * ((f^[n] q : Q) : G)) * y⁻¹) = _
      rw [ih q]
      group
  have hinj : Function.Injective f := by
    intro q q' h
    have h' : a⁻¹ * (y * (a * (q : G)) * y⁻¹) = a⁻¹ * (y * (a * (q' : G)) * y⁻¹) :=
      congrArg Subtype.val h
    have h1 := mul_left_cancel h'
    have h2 := mul_right_cancel h1
    have h3 := mul_left_cancel h2
    exact Subtype.ext (mul_left_cancel h3)
  obtain ⟨σ, hσf⟩ : ∃ σ : Equiv.Perm Q, ⇑σ = f :=
    ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), rfl⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    rw [show (3 : ℕ) ^ 1 = 3 by norm_num]
    refine Equiv.ext fun q => Subtype.ext ?_
    rw [Equiv.Perm.coe_pow, hσf, Equiv.Perm.one_apply, hit 3 q, hy]
    simp
  have hcard : ¬ 3 ∣ Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card, hQ]
    norm_num
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hcard hσ
  have hq' : f q = q := (congrFun hσf q).symm.trans hq
  have hq'' : a⁻¹ * (y * (a * (q : G)) * y⁻¹) = (q : G) := congrArg Subtype.val hq'
  exact ⟨(q : G), q.2, inv_mul_eq_iff_eq_mul.mp hq''⟩

private theorem he42r_gl2_left_fix :
    ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M : M2, g.val * M = M → M = 0 := by
  decide +kernel

private theorem he42r_gl2_right_fix :
    ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M : M2, M * g.val.transpose = M → M = 0 := by
  decide +kernel

private theorem he42r_card_mul_of_decomp {Z R K : Subgroup G} (hZK : Z ≤ K) (hRK : R ≤ K)
    (hinf : Z ⊓ R = ⊥) (hdec : ∀ a ∈ K, ∃ z ∈ Z, ∃ r ∈ R, a = z * r) :
    Nat.card K = Nat.card Z * Nat.card R := by
  let F : Z × R → K := fun p => ⟨(p.1 : G) * (p.2 : G), K.mul_mem (hZK p.1.2) (hRK p.2.2)⟩
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro ⟨z, r⟩ ⟨z', r'⟩ h
      have h' : (z : G) * (r : G) = (z' : G) * (r' : G) := congrArg Subtype.val h
      have hmem : (z' : G)⁻¹ * (z : G) ∈ Z ⊓ R := by
        refine ⟨Z.mul_mem (Z.inv_mem z'.2) z.2, ?_⟩
        have e : (z' : G)⁻¹ * (z : G) = (r' : G) * (r : G)⁻¹ := by
          calc (z' : G)⁻¹ * (z : G) = (z' : G)⁻¹ * ((z : G) * (r : G)) * (r : G)⁻¹ := by group
            _ = (z' : G)⁻¹ * ((z' : G) * (r' : G)) * (r : G)⁻¹ := by rw [h']
            _ = (r' : G) * (r : G)⁻¹ := by group
        rw [e]
        exact R.mul_mem r'.2 (R.inv_mem r.2)
      rw [hinf, Subgroup.mem_bot] at hmem
      have hzz : (z : G) = (z' : G) := (inv_mul_eq_one.mp hmem).symm
      have hrr : (r : G) = (r' : G) := by
        rw [hzz] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext hzz) (Subtype.ext hrr)
    · rintro ⟨a, ha⟩
      obtain ⟨z, hz, r, hr, hEq⟩ := hdec a ha
      exact ⟨(⟨z, hz⟩, ⟨r, hr⟩), Subtype.ext hEq.symm⟩
  have h := Nat.card_congr (Equiv.ofBijective F hF)
  rw [Nat.card_prod] at h
  exact h.symm

private theorem he42r_rhoG_mul (S : HeSetup G) {a b : G} (ha : a ∈ S.N) (hb : b ∈ S.N) :
    S.rhoG (a * b) = S.rhoG a * S.rhoG b := by
  rw [S.rhoG_of_mem ha, S.rhoG_of_mem hb, S.rhoG_of_mem (S.N.mul_mem ha hb)]
  exact map_mul S.rho ⟨a, ha⟩ ⟨b, hb⟩

private theorem he42r_rho_y3 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.rho ⟨y₁ * y₂, S.N.mul_mem hY.mem₁ hY.mem₂⟩ = (S.g, S.g) := by
  rw [← S.rhoG_of_mem (S.N.mul_mem hY.mem₁ hY.mem₂), he42r_rhoG_mul S hY.mem₁ hY.mem₂,
    hY.rho₁, hY.rho₂]
  simp

private theorem he42r_u_conj_y2 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {x : G}
    (hx : x ∈ S.A) : S.u (y₂ * x * y₂⁻¹) = S.u x := by
  have hρ2 : S.rho ⟨y₂, hY.mem₂⟩ = (1, S.g) := by
    rw [← S.rhoG_of_mem hY.mem₂]
    exact hY.rho₂
  have h := S.hD.hT.u_conj S.N S.hD.hK.norm ⟨y₂, hY.mem₂⟩ hx
  change S.u (y₂ * x * y₂⁻¹) = ((S.rho ⟨y₂, hY.mem₂⟩).1 : M2) *ᵥ S.u x at h
  rw [hρ2] at h
  simpa using h

private theorem he42r_w_conj_y1 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {x : G}
    (hx : x ∈ S.A') : S.w (y₁ * x * y₁⁻¹) = S.w x := by
  have hρ1 : S.rho ⟨y₁, hY.mem₁⟩ = (S.g, 1) := by
    rw [← S.rhoG_of_mem hY.mem₁]
    exact hY.rho₁
  have h := S.hD.hT.w_conj S.N S.hD.hK.norm ⟨y₁, hY.mem₁⟩ hx
  change S.w (y₁ * x * y₁⁻¹) = ((S.rho ⟨y₁, hY.mem₁⟩).2 : M2) *ᵥ S.w x at h
  rw [hρ1] at h
  simpa using h

private theorem he42r_u_conj_y3 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {x : G}
    (hx : x ∈ S.A) : S.u (y₁ * y₂ * x * (y₁ * y₂)⁻¹) = (S.g : M2) *ᵥ S.u x := by
  have hy3 : y₁ * y₂ ∈ S.N := S.N.mul_mem hY.mem₁ hY.mem₂
  have hρ3 := he42r_rho_y3 S hY
  have h := S.hD.hT.u_conj S.N S.hD.hK.norm ⟨y₁ * y₂, hy3⟩ hx
  change S.u (y₁ * y₂ * x * (y₁ * y₂)⁻¹) = ((S.rho ⟨y₁ * y₂, hy3⟩).1 : M2) *ᵥ S.u x at h
  rw [hρ3] at h
  exact h

private theorem he42r_w_conj_y3 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {x : G}
    (hx : x ∈ S.A') : S.w (y₁ * y₂ * x * (y₁ * y₂)⁻¹) = (S.g : M2) *ᵥ S.w x := by
  have hy3 : y₁ * y₂ ∈ S.N := S.N.mul_mem hY.mem₁ hY.mem₂
  have hρ3 := he42r_rho_y3 S hY
  have h := S.hD.hT.w_conj S.N S.hD.hK.norm ⟨y₁ * y₂, hy3⟩ hx
  change S.w (y₁ * y₂ * x * (y₁ * y₂)⁻¹) = ((S.rho ⟨y₁ * y₂, hy3⟩).2 : M2) *ᵥ S.w x at h
  rw [hρ3] at h
  exact h

private theorem he42r_Z_comm_y1 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {z : G}
    (hz : z ∈ S.Z) (hc : z * y₁ = y₁ * z) : z = 1 := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hρ1 : S.rho ⟨y₁, hY.mem₁⟩ = (S.g, 1) := by
    rw [← S.rhoG_of_mem hY.mem₁]
    exact hY.rho₁
  have hm := S.hD.hT.m_conj S.N S.hD.hK.norm ⟨y₁, hY.mem₁⟩ hz
  change S.m (y₁ * z * y₁⁻¹) = ((S.rho ⟨y₁, hY.mem₁⟩).1 : M2) * S.m z *
    ((S.rho ⟨y₁, hY.mem₁⟩).2 : M2)ᵀ at hm
  have hconj : y₁ * z * y₁⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hc.symm
  rw [hconj, hρ1] at hm
  simp only [Units.val_one, Matrix.transpose_one, mul_one] at hm
  have h0 : S.m z = 0 := he42r_gl2_left_fix S.g hg3 hg1 (S.m z) hm.symm
  exact S.hD.hT.minj z hz 1 (Subgroup.one_mem _) (by rw [S.hD.hT.m_one, h0])

private theorem he42r_Z_comm_y2 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {z : G}
    (hz : z ∈ S.Z) (hc : z * y₂ = y₂ * z) : z = 1 := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hρ2 : S.rho ⟨y₂, hY.mem₂⟩ = (1, S.g) := by
    rw [← S.rhoG_of_mem hY.mem₂]
    exact hY.rho₂
  have hm := S.hD.hT.m_conj S.N S.hD.hK.norm ⟨y₂, hY.mem₂⟩ hz
  change S.m (y₂ * z * y₂⁻¹) = ((S.rho ⟨y₂, hY.mem₂⟩).1 : M2) * S.m z *
    ((S.rho ⟨y₂, hY.mem₂⟩).2 : M2)ᵀ at hm
  have hconj : y₂ * z * y₂⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hc.symm
  rw [hconj, hρ2] at hm
  simp only [Units.val_one, one_mul] at hm
  have h0 : S.m z = 0 := he42r_gl2_right_fix S.g hg3 hg1 (S.m z) hm.symm
  exact S.hD.hT.minj z hz 1 (Subgroup.one_mem _) (by rw [S.hD.hT.m_one, h0])

private theorem he42r_AZ_fst (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    ∀ a ∈ S.A, ∃ z ∈ S.Z, ∃ r ∈ S.A ⊓ centralizer ({y₂} : Set G), a = z * r := by
  intro a ha
  have hy3 : y₂ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₂
    rwa [hY.ord₂] at h
  have hX : y₂ * a * y₂⁻¹ ∈ S.A := (S.hD.hK.norm y₂ hY.mem₂).1 a ha
  have hu := he42r_u_conj_y2 S hY ha
  have hcZ : (y₂ * a * y₂⁻¹) * a⁻¹ ∈ S.Z :=
    ⟨S.A.mul_mem hX (S.A.inv_mem ha), S.hD.hT.cu.mul_inv_mem hX ha hu⟩
  have hstab : ∀ q ∈ S.Z, a⁻¹ * (y₂ * (a * q) * y₂⁻¹) ∈ S.Z := by
    intro q hq
    have e : a⁻¹ * (y₂ * (a * q) * y₂⁻¹) = (a⁻¹ * (y₂ * a * y₂⁻¹)) * (y₂ * q * y₂⁻¹) := by
      group
    have hc : a⁻¹ * (y₂ * a * y₂⁻¹) = (y₂ * a * y₂⁻¹) * a⁻¹ :=
      hB.A_comm _ (S.A.inv_mem ha) _ hX
    rw [e, hc]
    exact S.Z.mul_mem hcZ (S.hD.mem_Z_conj hY.mem₂ hq)
  obtain ⟨q₀, hq₀, hfix⟩ := he42r_fix_coset hy3 hB.card_Z hstab
  have hq₀A : q₀ ∈ S.A := hB.Z_le_A hq₀
  have hcomm : a * q₀ ∈ centralizer ({y₂} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  refine ⟨q₀⁻¹, S.Z.inv_mem hq₀, a * q₀, ⟨S.A.mul_mem ha hq₀A, hcomm⟩, ?_⟩
  rw [hB.A_comm a ha q₀ hq₀A, inv_mul_cancel_left]

private theorem he42r_AZ_snd (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    ∀ a ∈ S.A', ∃ z ∈ S.Z, ∃ r ∈ S.A' ⊓ centralizer ({y₁} : Set G), a = z * r := by
  intro a ha
  have hy3 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hY.ord₁] at h
  have hX : y₁ * a * y₁⁻¹ ∈ S.A' := (S.hD.hK.norm y₁ hY.mem₁).2 a ha
  have hw := he42r_w_conj_y1 S hY ha
  have hcZ : (y₁ * a * y₁⁻¹) * a⁻¹ ∈ S.Z :=
    ⟨S.hD.hT.cw.mul_inv_mem hX ha hw, S.A'.mul_mem hX (S.A'.inv_mem ha)⟩
  have hstab : ∀ q ∈ S.Z, a⁻¹ * (y₁ * (a * q) * y₁⁻¹) ∈ S.Z := by
    intro q hq
    have e : a⁻¹ * (y₁ * (a * q) * y₁⁻¹) = (a⁻¹ * (y₁ * a * y₁⁻¹)) * (y₁ * q * y₁⁻¹) := by
      group
    have hc : a⁻¹ * (y₁ * a * y₁⁻¹) = (y₁ * a * y₁⁻¹) * a⁻¹ :=
      hB.A'_comm _ (S.A'.inv_mem ha) _ hX
    rw [e, hc]
    exact S.Z.mul_mem hcZ (S.hD.mem_Z_conj hY.mem₁ hq)
  obtain ⟨q₀, hq₀, hfix⟩ := he42r_fix_coset hy3 hB.card_Z hstab
  have hq₀A' : q₀ ∈ S.A' := hB.Z_le_A' hq₀
  have hcomm : a * q₀ ∈ centralizer ({y₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  refine ⟨q₀⁻¹, S.Z.inv_mem hq₀, a * q₀, ⟨S.A'.mul_mem ha hq₀A', hcomm⟩, ?_⟩
  rw [hB.A'_comm a ha q₀ hq₀A', inv_mul_cancel_left]

private theorem he42r_mem_Z_of_comm_A'_y3 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂)
    {x : G} (hx : x ∈ S.A') (hc : x * (y₁ * y₂) = (y₁ * y₂) * x) : x ∈ S.Z := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hconj : y₁ * y₂ * x * (y₁ * y₂)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hc.symm
  have h := he42r_w_conj_y3 S hY hx
  rw [hconj] at h
  have h0 : S.w x = 0 := gl2_order_three_fpf S.g hg3 hg1 (S.w x) h.symm
  exact ⟨(S.hD.hT.cw.zero x hx).mp h0, hx⟩

private theorem he42r_mem_Z_of_comm_A_y3 (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂)
    {x : G} (hx : x ∈ S.A) (hc : x * (y₁ * y₂) = (y₁ * y₂) * x) : x ∈ S.Z := by
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hconj : y₁ * y₂ * x * (y₁ * y₂)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hc.symm
  have h := he42r_u_conj_y3 S hY hx
  rw [hconj] at h
  have h0 : S.u x = 0 := gl2_order_three_fpf S.g hg3 hg1 (S.u x) h.symm
  exact ⟨hx, (S.hD.hT.cu.zero x hx).mp h0⟩

theorem HeSetup.stepR (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepR y₁ y₂ := by
  have hinf1 : S.Z ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hz, -, hc⟩
    exact he42r_Z_comm_y1 S hY hz (mem_centralizer_singleton_iff.mp hc)
  have hinf2 : S.Z ⊓ (S.A ⊓ centralizer ({y₂} : Set G)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hz, -, hc⟩
    exact he42r_Z_comm_y2 S hY hz (mem_centralizer_singleton_iff.mp hc)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := he42r_card_mul_of_decomp (Z := S.Z) (R := S.A' ⊓ centralizer ({y₁} : Set G))
      (K := S.A') hB.Z_le_A' inf_le_left hinf1 (he42r_AZ_snd S hB hY)
    rw [hB.card_A', hB.card_Z] at h
    omega
  · rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hzA, hzA', hc⟩
    exact he42r_Z_comm_y1 S hY ⟨hzA, hzA'⟩ (mem_centralizer_singleton_iff.mp hc)
  · have h := he42r_card_mul_of_decomp (Z := S.Z) (R := S.A ⊓ centralizer ({y₂} : Set G))
      (K := S.A) hB.Z_le_A inf_le_left hinf2 (he42r_AZ_fst S hB hY)
    rw [hB.card_A, hB.card_Z] at h
    omega
  · rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hzA', hzA, hc⟩
    exact he42r_Z_comm_y2 S hY ⟨hzA, hzA'⟩ (mem_centralizer_singleton_iff.mp hc)
  · intro x hx hc
    exact he42r_mem_Z_of_comm_A'_y3 S hY hx hc
  · intro x hx hc
    exact he42r_mem_Z_of_comm_A_y3 S hY hx hc

theorem HeSetup.stepAZ (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepAZ y₁ y₂ :=
  ⟨he42r_AZ_fst S hB hY, he42r_AZ_snd S hB hY⟩

end CFSG.Quasithin.A94.He42
