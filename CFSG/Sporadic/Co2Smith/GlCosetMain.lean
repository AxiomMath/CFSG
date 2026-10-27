module

public import CFSG.Sporadic.Co2Smith.GlCosetNorm
public import CFSG.Sporadic.Co2Smith.CCensusCheck
public import CFSG.Sporadic.Co2Smith.GlCosetOrbit

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace SmithMarkedData

variable
  {G : Type*} [Group G] {z : G} (S : SmithMarkedData z)

theorem exists_decomp {Q : Subgroup (Equiv.Perm (Fin 2300))} (hQ : Q ≤ co2P0)
    (hcov : ∀ y ∈ orbit co2P0 (3 : Fin 2300), ∃ x ∈ Native.glWit0Pts 1, ∃ hx : x < 2300,
      y ∈ orbit Q (cPerm ⟨x, hx⟩)) (b : S.G₁) :
    ∃ a : K, ∃ ha : a ∈ C1c, ∃ n m : S.G₁, (S.ψ n : Equiv.Perm (Fin 2300)) ∈ Q ∧
      (S.ψ m : Equiv.Perm (Fin 2300)) 3 = 3 ∧
      b = n * ⟨S.Ψ ⟨a, ha.2⟩, S.Ψ_mem _⟩ * m := by
  have hy : (S.ψ b : Equiv.Perm (Fin 2300)) 3 ∈ orbit co2P0 (3 : Fin 2300) :=
    mem_orbit_subgroup_iff.2 ⟨_, (S.ψ b).2, rfl⟩
  obtain ⟨x, hx, hx', hyx⟩ := hcov _ hy
  obtain ⟨hx'', a, ha, hax⟩ := exists_C1c_of_mem hx
  obtain ⟨q, hq, hqy⟩ := mem_orbit_subgroup_iff.1 hyx
  obtain ⟨n, hn⟩ := S.exists_ψ_eq (hQ hq)
  refine ⟨a, ha, n, (n * ⟨S.Ψ ⟨a, ha.2⟩, S.Ψ_mem _⟩)⁻¹ * b, by rw [hn]; exact hq, ?_,
    by group⟩
  have h1 : co2PermHom a 1172 = ⟨x, hx'⟩ := by
    rw [← co2PermHom_uK, ← Equiv.Perm.mul_apply, ← map_mul, hax]
  have har : psiK a 3 = cPerm ⟨x, hx'⟩ := by
    rw [← cPerm_1172, psiK_apply_cPerm, h1]
  rw [map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, S.ψ_Ψ,
    hn, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply, har]
  exact hqy.symm


theorem ρ_conj_mem_smithX {a : K} (ha : a ∈ C1c) {x y : K}
    (hx : x ∈ C0c) (hy : y ∈ C0c) :
    S.ρ ⟨x, hx⟩ * S.Ψ ⟨a, ha.2⟩ * S.ρ ⟨y, hy⟩ ∈ smithX S.G₁ S.u S.v := by
  have hm : x * a * y ∈ C0c := C0c.mul_mem (C0c.mul_mem hx ha.1) hy
  rw [← S.ρ_eq_Ψ ha.1 ha.2, ← map_mul, ← map_mul]
  exact S.ρ_mem_smithX hm

theorem smithX_mul_u
    {x : G}
    (hx : x ∈ smithX S.G₁ S.u S.v) : x * S.u ∈ smithX S.G₁ S.u S.v := by
  rcases hx with hx | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inr (Or.inl ⟨x, hx, 1, S.G₁.one_mem, by group⟩)
  · obtain ⟨a', ha', n, m, hn, hm, e⟩ := S.exists_decomp co2N_le_P0
      (fun y hy => exists_mem_orbit_co2N hy) ⟨b, hb⟩
    have hn3 : (S.ψ n : Equiv.Perm (Fin 2300)) 3 = 3 :=
      MulAction.mem_stabilizer_iff.1 (co2N_le hn).2
    have hb' : b = n * S.Ψ ⟨a', ha'.2⟩ * m := congrArg Subtype.val e
    have key : S.u * b * S.u⁻¹ = (S.u * n * S.u⁻¹) * (S.u * S.Ψ ⟨a', ha'.2⟩ * S.u⁻¹) *
        (S.u * m * S.u⁻¹) := by
      rw [hb']
      group
    have hmid : S.u * S.Ψ ⟨a', ha'.2⟩ * S.u⁻¹ ∈ smithX S.G₁ S.u S.v := by
      have h := S.ρ_conj_mem_smithX ha' uK_mem_C0c uK_mem_C0c
      rw [S.ρ_uK] at h
      rwa [S.u_inv]
    have h1 : a * S.u * b * S.u = a * (S.u * b * S.u⁻¹) := by
      rw [S.u_inv]
      group
    rw [h1, key]
    exact mul_mem_smithX_left ha
      (mul_mul_mem_smithX (S.compat_u hn3).mem hmid (S.compat_u hm).mem)
  · obtain ⟨a', ha', n, m, hn, hm, e⟩ := S.exists_decomp (Q := co2P01) inf_le_left
      (fun y hy => exists_mem_orbit_co2P01 hy) ⟨b, hb⟩
    have hn1 : (S.ψ n : Equiv.Perm (Fin 2300)) 1 = 1 := MulAction.mem_stabilizer_iff.1 hn.2
    have hb' : b = n * S.Ψ ⟨a', ha'.2⟩ * m := congrArg Subtype.val e
    have key : S.v * b * S.u = (S.v * n * S.v⁻¹) * (S.v * S.Ψ ⟨a', ha'.2⟩ * S.u) *
        (S.u⁻¹ * m * S.u) := by
      rw [hb']
      group
    have hmid := S.ρ_conj_mem_smithX ha' v1K_mem_C0c uK_mem_C0c
    rw [S.ρ_uK] at hmid
    have cm : S.u⁻¹ * (m : G) * S.u ∈ S.G₁ := by
      have h := (S.compat_u hm).mem
      rw [S.u_inv] at h ⊢
      exact h
    rw [show a * S.v * b * S.u = a * (S.v * b * S.u) by group, key]
    exact mul_mem_smithX_left ha (mul_mul_mem_smithX (S.compat_v hn1).mem hmid cm)

theorem centralizer_le_closure :
    centralizer ({z} : Set G) ≤ closure ((S.G₁ : Set G) ∪ {S.u}) := by
  have hle : Subgroup.closure {g | ∃ w ∈ Native.glCzWords, glE w = g} ≤
      ((closure ((S.G₁ : Set G) ∪ {S.u})).comap S.phiInv).map Cz.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨glE w, glCzWords_mem_Cz w hw⟩, ?_, rfl⟩
    change S.phiInv ⟨glE w, _⟩ ∈ closure ((S.G₁ : Set G) ∪ {S.u})
    simp only [Native.glCzWords, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨k, hk, rfl⟩ | rfl
    · rw [← S.Ψ_eq_phiInv z0_mem_G1c (glCzLetters_mem hk).2 (glCzLetters_mem hk).1]
      exact subset_closure (Or.inl (S.Ψ_mem _))
    · exact subset_closure (Or.inr rfl)
  rw [closure_glCzWords] at hle
  intro h hh
  obtain ⟨g, hg, hgh⟩ := hle (S.φ ⟨h, hh⟩).2
  have e : g = S.φ ⟨h, hh⟩ := Subtype.ext hgh
  rw [e] at hg
  have e' : S.phiInv (S.φ ⟨h, hh⟩) = h := by
    rw [phiInv_apply, MulEquiv.symm_apply_apply]
  rw [← e']
  exact hg

end SmithMarkedData

theorem smithG1Input_of_U62
    (h0 : SmithC0Input C0c α3c) (h : SmithU62Input C0c α3c G1c cPerm) : SmithG1Input := by
  intro G _ _ z hsimple hG φ hφ
  obtain ⟨ρ, hρ⟩ := h0 G z hsimple hG φ hφ
  obtain ⟨G₁, ψ, ha, hb⟩ := h G z hsimple hG φ hφ ρ hρ
  let S : SmithMarkedData z := ⟨φ, ρ, G₁, ψ, φ_zC ccCensus_check hG φ, hρ, ha, hb⟩
  exact ⟨G₁, ψ, S.u, S.v, fun _ h3 => (S.compat_u h3).mem, S.u_not_mem_normalizer,
    fun _ h1 => (S.compat_v h1).mem, S.v_not_mem_normalizer, fun _ hx => S.smithX_mul_u hx,
    S.v_mem_closure, S.centralizer_le_closure⟩

end CFSG.Sporadic.Co2Smith
