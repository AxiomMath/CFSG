module

public import CFSG.Quasithin.EmptyFaithful.S153E57G

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section Tilde

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem mem_tilde_conj_iff (cx : Ctx15350 T Mc M V₁ V₂ t) {U₁ : Subgroup G} {g : G} (hg : g ∈ Mc)
    (w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    w ∈ (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ g)).subgroupOf
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ↔
      ∃ v ∈ (tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
        rho cx ⟨g⁻¹, Mc_le_NZ cx (Mc.inv_mem hg)⟩ v = w := by
  have hgN : g ∈ NZ T := Mc_le_NZ cx hg
  have hginv : g⁻¹ ∈ NZ T := Mc_le_NZ cx (Mc.inv_mem hg)
  constructor
  · intro hw
    obtain ⟨y, hy, hyw⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hw)
    have hy' : g * (y : G) * g⁻¹ ∈ U₁ := mem_conjSubgroup_iff.1 hy
    refine ⟨rho cx ⟨g, hgN⟩ w, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [rho_apply_coe, ← hyw]
      have h2 := secMk_mem_secImg (A := NZ T) (B := quasithinOmegaOneCenter T) (X := U₁)
        (x := (⟨g, hgN⟩ : NZ T) * y * (⟨g, hgN⟩ : NZ T)⁻¹) (by simpa using hy')
      rw [map_mul, map_mul, map_inv] at h2
      exact h2
    · rw [← MulAut.mul_apply, ← map_mul]
      have : (⟨g⁻¹, hginv⟩ * ⟨g, hgN⟩ : NZ T) = 1 := Subtype.ext (by simp)
      rw [this, map_one, MulAut.one_apply]
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨x, hx, hxv⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hv)
    refine Subgroup.mem_subgroupOf.mpr (mem_secImg.mpr ⟨(⟨g⁻¹, hginv⟩ : NZ T) * x *
      (⟨g⁻¹, hginv⟩ : NZ T)⁻¹, ?_, ?_⟩)
    · rw [mem_conjSubgroup_iff]
      have : g * (((⟨g⁻¹, hginv⟩ : NZ T) * x * (⟨g⁻¹, hginv⟩ : NZ T)⁻¹ : NZ T) : G) * g⁻¹ = x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact hx
    · rw [← hvw, rho_apply_coe, ← hxv]
      simp only [map_mul, map_inv]

@[expose] noncomputable def preU (cx : Ctx15350 T Mc M V₁ V₂ t)
    (W₀ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : Subgroup G :=
  (W₀.comap (piU cx)).map (UH153 T M V₁ Mc).subtype

theorem Z_le_preU (cx : Ctx15350 T Mc M V₁ V₂ t)
    (W₀ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    quasithinOmegaOneCenter T ≤ preU cx W₀ := by
  intro z hz
  have hzU : z ∈ UH153 T M V₁ Mc := (S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx) hz
  refine Subgroup.mem_map.2 ⟨⟨z, hzU⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, (piU_eq_one_iff cx ⟨z, hzU⟩).2 hz]
  exact W₀.one_mem

theorem preU_le (cx : Ctx15350 T Mc M V₁ V₂ t)
    (W₀ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    preU cx W₀ ≤ UH153 T M V₁ Mc := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem tilde_preU (cx : Ctx15350 T Mc M V₁ V₂ t)
    (W₀ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    (tildeOf (quasithinOmegaOneCenter T) (preU cx W₀)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) = W₀ := by
  ext w
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hw
    obtain ⟨n, hn, hnw⟩ := mem_secImg.1 hw
    obtain ⟨u, hu, hun⟩ := Subgroup.mem_map.1 hn
    rw [Subgroup.mem_comap] at hu
    have h1 : piU cx u = w := by
      apply Subtype.ext
      rw [piU_coe, ← hnw]
      congr 1
      exact Subtype.ext hun
    rwa [← h1]
  · intro hw
    obtain ⟨u, rfl⟩ := piU_surjective cx w
    have hu : (u : G) ∈ preU cx W₀ := Subgroup.mem_map.2 ⟨u, by simpa [Subgroup.mem_comap] using hw, rfl⟩
    have := secMk_mem_secImg (A := NZ T) (B := quasithinOmegaOneCenter T) (X := preU cx W₀)
      (x := ⟨u, U_le_NZ cx u.2⟩) hu
    rw [piU_coe]
    exact this

end Tilde

section Extraspecial

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

omit [Finite G] in
theorem isMulCommutative_of_sq_eq_one {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) :
    IsMulCommutative ↥E := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have h1 : (a : G) * b * ((a : G) * b) = 1 := by
    rw [← pow_two]
    exact h _ (E.mul_mem a.2 b.2)
  have ha : (a : G) * a = 1 := by rw [← pow_two]; exact h _ a.2
  have hb : (b : G) * b = 1 := by rw [← pow_two]; exact h _ b.2
  have e1 : ((a : G) * b)⁻¹ = (a : G) * b := inv_eq_of_mul_eq_one_right h1
  have e2 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have e3 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  apply Subtype.ext
  calc (a : G) * b = ((a : G) * b)⁻¹ := e1.symm
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
    _ = (b : G) * a := by rw [e2, e3]

omit [Finite G] in
theorem card_of_sq_eq_one {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) [Finite G]
    (hZ : Nat.card ↥(quasithinOmegaOneCenter T) = 2) (hZE : quasithinOmegaOneCenter T ≤ E) {r : ℕ}
    (hr : mIdx E (quasithinOmegaOneCenter T) = r) : Nat.card ↥E = 2 ^ (r + 1) := by
  have hEp : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using h x x.2)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) E
  rw [inf_eq_left.2 hZE, hZ] at hmul
  have hdvd : (quasithinOmegaOneCenter T).relIndex E ∣ 2 ^ m := by
    rw [← hm, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [mIdx, hk, padicValNat.prime_pow] at hr
  rw [← hmul, hk, hr, pow_succ]

theorem isExtraspecialPlus_U (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁)
    (hext : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc)) (hs : s = 1) :
    E2.IsExtraspecialPlus 3 (UH153 T M V₁ Mc) := by
  subst hs
  refine ⟨hext, ?_, Egp153 T M V₁ Mc y, ?_, ⟨isMulCommutative_of_sq_eq_one c.h56.E_sing.2.1,
    c.h56.E_sing.2.1⟩, ?_⟩
  · have hmul := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
    have hZU : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
      (S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx)
    rw [inf_eq_left.2 hZU, Z_card cx, ← card_tilde_eq cx, card_tilde cx c] at hmul
    rw [← hmul]
    norm_num
  · exact fun e he => he.1.1
  · exact card_of_sq_eq_one c.h56.E_sing.2.1 (Z_card cx) c.h56.E_sing.1 c.h56.E_sing.2.2

end Extraspecial

end S153E58

end CFSG.Quasithin
