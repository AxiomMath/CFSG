module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715K

open CFSG.CGT.Timmesfeld75 QuadraticMap
open scoped commutatorElement

section Generic

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem range_conj (f : E ≃ₗ[K] E) (ψ : E →ₗ[K] E) :
    LinearMap.range (f.conj ψ) = (LinearMap.range ψ).map (f : E →ₗ[K] E) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_map.mpr ⟨ψ (f.symm y), LinearMap.mem_range_self ψ _, rfl⟩
  · intro hx
    obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨f y, ?_⟩
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    rfl

theorem map_conj (f : E ≃ₗ[K] E) (ψ : E →ₗ[K] E) (p : Submodule K E) :
    p.map (f.conj ψ) = ((p.map (f.symm : E →ₗ[K] E)).map ψ).map (f : E →ₗ[K] E) := by
  rw [LinearEquiv.conj_apply, Submodule.map_comp, Submodule.map_comp]

theorem map_range_restrict (ψ : E →ₗ[K] E) {p : Submodule K E} (hp : ∀ v ∈ p, ψ v ∈ p) :
    (LinearMap.range (ψ.restrict hp)).map p.subtype = p.map ψ := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact Submodule.mem_map_of_mem v.2
  · rintro ⟨v, hv, rfl⟩
    exact ⟨ψ.restrict hp ⟨v, hv⟩, LinearMap.mem_range_self _ _, rfl⟩

end Generic

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X} {Tt : X → Submodule K E}

private theorem phi_inv_phi (g : X) (x : E) : φ g⁻¹ (φ g x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem symm_phi (g : X) : ((φ g).symm : E →ₗ[K] E) = (φ g⁻¹ : E →ₗ[K] E) := by
  refine LinearMap.ext fun x => ?_
  apply (φ g).injective
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem kappa_of_frame (F : Sec715Frame φ V L Nb Rb Tt) {ψ : E →ₗ[K] E}
    (hpar : ∀ a ∈ V, ∃ c : K, ∀ x, φ a x = x + c • ψ x)
    (hpar' : ∀ c : K, ∃ a ∈ V, ∀ x, φ a x = x + c • ψ x)
    (hψV : LinearMap.range ψ = Tt 1)
    (hRV : ∀ r ∈ Rb, ∀ v ∈ Tt 1, φ r v ∈ Tt 1)
    (hRW : ∀ r ∈ Rb, ∀ w, ψ w = 0 → ψ (φ r w) = 0)
    {h : X} (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)
    (hdim : Module.finrank K (Tt 1) = 8)
    (hP : Module.finrank K ((Tt 1).map ((φ h).conj ψ)) = 2)
    (hS : 12 ≤ Module.finrank K ↥((LinearMap.ker ψ).map ((φ h).conj ψ) ⊔ Tt 1))
    (hYDY : ∀ n ∈ Nb, ∀ w, ψ w = 0 → (φ h).conj ψ (opm (φ n) ((φ h).conj ψ w)) = 0)
    (Qf : QuadraticForm K ↥(Tt 1)) (hQnd : (polarBilin Qf).Nondegenerate)
    (hQ : ∀ r (hr : r ∈ Rb) (v : ↥(Tt 1)), Qf ⟨φ r v, hRV r hr v v.2⟩ = Qf v)
    (hc₀ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1) :
    ∀ b ∈ V, ∀ x ∈ Nb, ∃ z ∈ V, ⁅h * b * h⁻¹, x⁆ * z⁻¹ ∈ conjSubgroup h Nb := by
  classical
  intro b hb x hx
  set Y := (φ h).conj ψ with hYdef
  set ψ' := (φ h⁻¹).conj ψ with hψ'def
  obtain ⟨a₁, ha₁, ha₁x⟩ := hpar' 1
  have ha₁' : ∀ x, φ a₁ x = x + ψ x := fun x => by rw [ha₁x, one_smul]
  have hψ0 : ∃ x, ψ x ≠ 0 := by
    by_contra h0
    push Not at h0
    have hbot : Tt 1 = ⊥ := by
      rw [← hψV]
      exact LinearMap.range_eq_bot.mpr (LinearMap.ext h0)
    rw [hbot, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  have ha₁1 : a₁ ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx0⟩ := hψ0
    have h1 := ha₁' x
    rw [map_one] at h1
    exact hx0 (by simpa using h1.symm)
  have hψψ : ∀ x, ψ (ψ x) = 0 := by
    intro x
    have h1 := F.Nb_fixes a₁ (F.V_le_Nb ha₁) (ψ x) (hψV ▸ LinearMap.mem_range_self ψ x)
    rw [ha₁'] at h1
    simpa using h1
  have hconj : ∀ (g : X) {z : X} {c : K}, (∀ x, φ z x = x + c • ψ x) →
      ∀ x, φ (g * z * g⁻¹) x = x + c • (φ g).conj ψ x :=
    fun g z c hz x => conj_apply_of_eq φ hz g x
  have hY1 : ∀ x, φ (h * a₁ * h⁻¹) x = x + Y x := fun x => by
    rw [hconj h (c := 1) (fun x => by rw [ha₁', one_smul]) x, one_smul]
  have hinvh : h⁻¹⁻¹ = h := inv_inv h
  have hψ'1 : ∀ x, φ (h⁻¹ * a₁ * h) x = x + ψ' x := fun x => by
    have := hconj h⁻¹ (c := 1) (fun x => by rw [ha₁', one_smul]) x
    rw [hinvh, one_smul] at this
    exact this
  have hYsq : ∀ x, Y (Y x) = 0 := by
    intro x
    rw [hYdef, LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply, hψψ, map_zero]
  have hy₁R : h * a₁ * h⁻¹ ∈ Rb := F.L_le_Rb (hL a₁ ha₁)
  have hRconj : ∀ l ∈ L, h⁻¹ * l * h ∈ Rb := F.L_le_conj_Rb h hL
  have hy'R : h⁻¹ * a₁ * h ∈ Rb := hRconj a₁ (F.V_le_L ha₁)
  have hTth : Tt h = (Tt 1).map (φ h : E →ₗ[K] E) := F.Tt_eq_map h ha₁ ha₁1
  have hrangeY : LinearMap.range Y = Tt h := by rw [hYdef, range_conj, hψV, hTth]
  have hYV : ∀ v ∈ Tt 1, Y v ∈ Tt 1 := fun v hv => by
    have h1 := hRV _ hy₁R v hv
    rw [hY1] at h1
    simpa using (Tt 1).sub_mem h1 hv
  have hYW : ∀ w, ψ w = 0 → ψ (Y w) = 0 := fun w hw => by
    have h1 := hRW _ hy₁R w hw
    rw [hY1, map_add, hw, zero_add] at h1
    exact h1
  have hψ'V : ∀ v ∈ Tt 1, ψ' v ∈ Tt 1 := fun v hv => by
    have h1 := hRV _ hy'R v hv
    rw [hψ'1] at h1
    simpa using (Tt 1).sub_mem h1 hv
  have hcomm := F.comm_conj_of_le_L hL
  have hPeq : (Tt 1).map Y = (Tt h).map ψ := by
    have h1 := F.map_opm_eq hcomm ha₁ ha₁1 ha₁ ha₁1
    have e1 : opm (φ (h * a₁ * h⁻¹)) = Y := LinearMap.ext fun x => by
      rw [opm_apply, hY1, add_sub_cancel_left]
    have e2 : opm (φ a₁) = ψ := LinearMap.ext fun x => by
      rw [opm_apply, ha₁', add_sub_cancel_left]
    rw [e1, e2] at h1
    exact h1
  have hdimh : Module.finrank K (Tt h) = 8 := by
    rw [hTth, LinearEquiv.finrank_map_eq, hdim]
  have hP' : Module.finrank K ((Tt 1).map ψ') = 2 := by
    rw [hψ'def, map_conj, symm_phi, inv_inv, ← hTth, ← hPeq, LinearEquiv.finrank_map_eq, hP]
  set C := Tt h ⊓ LinearMap.ker ψ with hC
  have hdimC : Module.finrank K C = 6 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict (Tt h))
    rw [LinearMap.range_domRestrict, ← hPeq, hP, hdimh, LinearMap.ker_domRestrict] at h1
    have h2 : Module.finrank K ↥((LinearMap.ker ψ).comap (Tt h).subtype) = Module.finrank K C := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    omega
  have hPC : (Tt 1).map Y ≤ C ⊓ Tt 1 := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨hrangeY ▸ LinearMap.mem_range_self Y v, LinearMap.mem_ker.mpr ?_⟩, hYV v hv⟩
    obtain ⟨u, hu⟩ := (hψV ▸ hYV v hv : Y v ∈ LinearMap.range ψ)
    rw [← hu, hψψ]
  have hdimCV : Module.finrank K ↥(C ⊔ Tt 1) ≤ 12 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C (Tt 1)
    have h2 := Submodule.finrank_mono hPC
    rw [hP] at h2
    omega
  have hYWC : (LinearMap.ker ψ).map Y ⊔ Tt 1 ≤ C ⊔ Tt 1 := by
    refine sup_le_sup_right ?_ _
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hrangeY ▸ LinearMap.mem_range_self Y w, LinearMap.mem_ker.mpr (hYW w hw)⟩
  have hCle : C ≤ (LinearMap.ker ψ).map Y ⊔ Tt 1 := by
    rw [Submodule.eq_of_le_of_finrank_le hYWC (hdimCV.trans hS)]
    exact le_sup_left
  have hstar : ∀ c ∈ C, ∀ n ∈ Nb, Y (opm (φ n) c) = 0 := by
    intro c hc n hn
    obtain ⟨_, ⟨w, hw, rfl⟩, v₀, hv₀, rfl⟩ := Submodule.mem_sup.mp (hCle hc)
    have hv₀' : opm (φ n) v₀ = 0 := by rw [opm_apply, F.Nb_fixes n hn v₀ hv₀, sub_self]
    rw [map_add, hv₀', add_zero]
    exact hYDY n hn w (LinearMap.mem_ker.mp hw)
  obtain ⟨cb, hcb⟩ := hpar b hb
  have hy : ∀ x, φ (h * b * h⁻¹) x = x + cb • Y x := hconj h hcb
  have hyinv : ∀ x, φ (h * b * h⁻¹)⁻¹ x = x - cb • Y x := inv_apply_of_eq φ hYsq hy
  have hYC : ∀ c ∈ Tt h, Y c = 0 := by
    intro c hc
    obtain ⟨u, rfl⟩ := (hrangeY ▸ hc : c ∈ LinearMap.range Y)
    exact hYsq u
  have hfixC : ∀ c ∈ C, φ ⁅h * b * h⁻¹, x⁆ c = c := by
    intro c hc
    have hxinv : x⁻¹ ∈ Nb := Nb.inv_mem hx
    set c₁ := φ x⁻¹ c with hc₁
    have hYc₁ : Y c₁ = 0 := by
      have e : c₁ = c + opm (φ x⁻¹) c := by rw [opm_apply]; abel
      rw [e, map_add, hYC c hc.1, hstar c hc _ hxinv, add_zero]
    rw [commutatorElement_def, map_mul, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hc₁, hyinv, hYc₁, smul_zero, sub_zero]
    have e2 : φ x c₁ = c := by
      rw [hc₁, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [e2, hy, hYC c hc.1, smul_zero, add_zero]
  set g' := h⁻¹ * ⁅h * b * h⁻¹, x⁆ * h with hg'
  have hyx_L : ⁅h * b * h⁻¹, x⁆ ∈ L := by
    rw [commutatorElement_def]
    have h1 : x * (h * b * h⁻¹)⁻¹ * x⁻¹ ∈ L := F.Nb_norm_L x hx _ (L.inv_mem (hL b hb))
    have e : h * b * h⁻¹ * x * (h * b * h⁻¹)⁻¹ * x⁻¹ =
        (h * b * h⁻¹) * (x * (h * b * h⁻¹)⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem (hL b hb) h1
  have hg'R : g' ∈ Rb := hRconj _ hyx_L
  have hg'fix : ∀ v ∈ Tt 1, ψ' v = 0 → φ g' v = v := by
    intro v hv hψ'v
    have hhv : φ h v ∈ C := by
      refine ⟨hTth ▸ Submodule.mem_map_of_mem hv, LinearMap.mem_ker.mpr ?_⟩
      rw [hψ'def, LinearEquiv.conj_apply_apply] at hψ'v
      have e : (φ h⁻¹).symm v = φ h v := by
        rw [← LinearEquiv.coe_coe, symm_phi, inv_inv]
        rfl
      rw [e] at hψ'v
      exact (LinearEquiv.map_eq_zero_iff _).mp hψ'v
    rw [hg', map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixC _ hhv,
      phi_inv_phi]
  set T := ψ'.restrict hψ'V with hT
  have hT2 : Module.finrank K (LinearMap.range T) = 2 := by
    rw [← Submodule.finrank_map_subtype_eq, hT, map_range_restrict, hP']
  have hroot : ∀ c : K, ∃ r ∈ Rb, ∀ v, φ r v = v + c • ψ' v := by
    intro c
    obtain ⟨a, ha, hax⟩ := hpar' c
    refine ⟨h⁻¹ * a * h, hRconj a (F.V_le_L ha), fun v => ?_⟩
    have := hconj h⁻¹ hax v
    rw [hinvh] at this
    exact this
  have hisoT : ∀ c : K, ∀ v : ↥(Tt 1), Qf (v + c • T v) = Qf v := by
    intro c v
    obtain ⟨r, hr, hrx⟩ := hroot c
    have e : v + c • T v = ⟨φ r v, hRV r hr v v.2⟩ := Subtype.ext (hrx v).symm
    rw [e, hQ r hr v]
  obtain ⟨c₀, hc₀0, hc₀1⟩ := hc₀
  have hTq : ∀ v, Qf (T v) = 0 ∧ polar Qf v (T v) = 0 := fun v =>
    quad_eq_zero_of_isometry (Qf := Qf) (T := T) hc₀0 hc₀1
      (fun v => by simpa using hisoT 1 v) (hisoT c₀) v
  obtain ⟨κ, hκ⟩ := exists_smul_of_fix (Qf := Qf) hQnd hT2 (fun v => (hTq v).1)
    (fun v => (hTq v).2) (g := (φ g' : E →ₗ[K] E).restrict (hRV g' hg'R))
    (fun v => hQ g' hg'R v) (fun v hv => Subtype.ext (hg'fix v v.2 (by
      have := congrArg Subtype.val hv
      simpa [hT] using this)))
  obtain ⟨z, hz, hzx⟩ := hpar' κ
  refine ⟨z, hz, mem_conjSubgroup.mpr ?_⟩
  have hz'R : h⁻¹ * z * h ∈ Rb := hRconj z (F.V_le_L hz)
  have hz' : ∀ v, φ (h⁻¹ * z * h) v = v + κ • ψ' v := by
    intro v
    have := hconj h⁻¹ hzx v
    rw [hinvh] at this
    exact this
  have e : h⁻¹ * (⁅h * b * h⁻¹, x⁆ * z⁻¹) * h = g' * (h⁻¹ * z * h)⁻¹ := by
    rw [hg']
    group
  rw [e]
  refine F.Rb_fix_Nb _ (Rb.mul_mem hg'R (Rb.inv_mem hz'R)) fun v hv => ?_
  have huV : φ (h⁻¹ * z * h)⁻¹ v ∈ Tt 1 := hRV _ (Rb.inv_mem hz'R) v hv
  have hgu : φ g' (φ (h⁻¹ * z * h)⁻¹ v) = φ (h⁻¹ * z * h) (φ (h⁻¹ * z * h)⁻¹ v) := by
    have h1 := congrArg Subtype.val (hκ ⟨_, huV⟩)
    simp only [Submodule.coe_sub, Submodule.coe_smul, LinearMap.coe_restrict_apply, hT,
      LinearEquiv.coe_coe] at h1
    rw [hz']
    exact sub_eq_iff_eq_add'.mp h1
  rw [map_mul, LinearEquiv.mul_apply, hgu, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel,
    map_one]
  rfl

end CFSG.RankThree.GF2n.Stroth80.S715K
