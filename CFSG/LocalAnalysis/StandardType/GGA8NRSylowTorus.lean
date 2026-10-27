module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

open scoped Pointwise

private theorem a8nr_comm_of_mem {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hH : IsElemAbelian p H) {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  letI : IsMulCommutative ↥H := hH.1
  exact Subgroup.mul_comm_of_mem_isMulCommutative H ha hb

private theorem a8nr_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    apply Subtype.ext
    change (u : H) * (v : H) = (v : H) * (u : H)
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, a8nr_comm_of_mem hE hx hy]
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hE.2 x hx, map_one]

private theorem a8nr_sylow_eq_conj_torus
    (P : Sylow 7 (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :
    ∃ g : GGSL9V ≃ₗ[ZMod 2] GGSL9V,
      (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) =
        ggSL9Torus.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    Finite.of_equiv (GL (Fin 9) (ZMod 2)) ggSL9GLEquiv.toEquiv
  have hTp : IsPGroup 7 ↥ggSL9Torus := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : x ^ 7 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact isElemAbelian_ggSL9Torus.2 (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) x.2
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨Q, hTQ⟩ := IsPGroup.exists_le_sylow hTp
  let Qsub : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := Q
  have hQp : IsPGroup 7 ↥Qsub := Sylow.isPGroup' Q
  obtain ⟨k, hQk⟩ := (IsPGroup.iff_card (p := 7) (G := ↥Qsub)).mp hQp
  have hk_le : k ≤ 3 := by
    by_contra h
    push Not at h
    exact not_seven_pow_four_dvd_card_ggSL9
      (dvd_trans (Nat.pow_dvd_pow 7 (Nat.succ_le_of_lt h))
        (by rw [← hQk]; exact Subgroup.card_subgroup_dvd_card Qsub))
  have hQcard : Nat.card Qsub ≤ 7 ^ 3 := by
    rw [hQk]
    exact Nat.pow_le_pow_right (by norm_num) hk_le
  have hQeq : ggSL9Torus = ↑Q :=
    Subgroup.eq_of_le_of_card_ge hTQ (by rw [card_ggSL9Torus]; exact hQcard)
  haveI : MulAction.IsPretransitive (GGSL9V ≃ₗ[ZMod 2] GGSL9V)
      (Sylow 7 (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GGSL9V ≃ₗ[ZMod 2] GGSL9V) Q P
  have hmap : (↑Q : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)).map (MulAut.conj g).toMonoidHom =
      MulAut.conj g • (↑Q : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hcoe : (↑(g • Q) : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) = ↑P :=
    congrArg (fun R : Sylow 7 (GGSL9V ≃ₗ[ZMod 2] GGSL9V) =>
      (R : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) hg
  rw [Sylow.coe_subgroup_smul, ← hmap] at hcoe
  refine ⟨g, ?_⟩
  rw [hQeq]
  exact hcoe.symm

theorem ggA8NR_sylowTorus {G : Type} [Group G] {Bs K : Subgroup G}
    (ρ₀ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hab : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hpow : ∀ b ∈ Bs, b ^ 7 = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    (hdec : ∀ b ∈ Bs, ∃ k ∈ K, k ∈ Bs ∧ k⁻¹ * b ∈ Subgroup.centralizer (K : Set G)) :
    ∃ ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V),
      ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus := by
  classical
  let E : Subgroup ↥K := (Bs ⊓ K).subgroupOf K
  change ∃ ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V), E.map ρ.toMonoidHom = ggSL9Torus
  have hEab : IsElemAbelian 7 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hab (a : G) (Subgroup.mem_inf.mp a.2).1 (b : G) (Subgroup.mem_inf.mp b.2).1
    · apply Subtype.ext
      exact hpow (x : G) (Subgroup.mem_inf.mp hx).1
  have hEab' : IsElemAbelian 7 (E.map ρ₀.toMonoidHom) :=
    a8nr_isElemAbelian_map ρ₀.toMonoidHom hEab
  have hE'p : IsPGroup 7 ↥(E.map ρ₀.toMonoidHom) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : x ^ 7 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hEab'.2 (x : GGSL9V ≃ₗ[ZMod 2] GGSL9V) x.2
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨P, hE'P⟩ := IsPGroup.exists_le_sylow hE'p
  obtain ⟨g, hPg⟩ := a8nr_sylow_eq_conj_torus P
  have hPab : IsElemAbelian 7 (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := by
    rw [hPg]
    exact a8nr_isElemAbelian_map (MulAut.conj g).toMonoidHom isElemAbelian_ggSL9Torus
  let S₀ : Subgroup ↥K := (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)).comap ρ₀.toMonoidHom
  have hS0E : S₀ ≤ E := by
    intro s hs
    have hsP : ρ₀ s ∈ (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) := hs
    have hcent : (s : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨k, hkK, hkB, hc⟩ := hdec b hb
      have hkE : (⟨k, hkK⟩ : ↥K) ∈ E :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hkB, hkK⟩)
      have hkP : ρ₀ (⟨k, hkK⟩ : ↥K) ∈ (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) :=
        hE'P (Subgroup.mem_map.mpr ⟨⟨k, hkK⟩, hkE, rfl⟩)
      have hcommP : ρ₀ s * ρ₀ (⟨k, hkK⟩ : ↥K) = ρ₀ (⟨k, hkK⟩ : ↥K) * ρ₀ s :=
        a8nr_comm_of_mem hPab hsP hkP
      have hsk : s * (⟨k, hkK⟩ : ↥K) = (⟨k, hkK⟩ : ↥K) * s :=
        ρ₀.injective (by rw [map_mul, map_mul, hcommP])
      have hskG : (s : G) * k = k * (s : G) := by
        simpa using congrArg Subtype.val hsk
      have hsc : (s : G) * (k⁻¹ * b) = (k⁻¹ * b) * (s : G) :=
        Subgroup.mem_centralizer_iff.mp hc (s : G) s.2
      have hbc : b = k * (k⁻¹ * b) := by group
      calc b * (s : G) = (k * (k⁻¹ * b)) * (s : G) := by conv_lhs => rw [hbc]
        _ = k * ((k⁻¹ * b) * (s : G)) := by group
        _ = k * ((s : G) * (k⁻¹ * b)) := by rw [← hsc]
        _ = (k * (s : G)) * (k⁻¹ * b) := by group
        _ = ((s : G) * k) * (k⁻¹ * b) := by rw [← hskG]
        _ = (s : G) * (k * (k⁻¹ * b)) := by group
        _ = (s : G) * b := by conv_rhs => rw [hbc]
    have hpow7 : (s : G) ^ 7 = 1 := by
      have hpowP : (ρ₀ s) ^ 7 = 1 := hPab.2 (ρ₀ s) hsP
      have hs7 : s ^ 7 = 1 := ρ₀.injective (by rw [map_pow, hpowP, map_one])
      simpa using congrArg Subtype.val hs7
    exact Subgroup.mem_inf.mpr ⟨hSC (s : G) hcent hpow7, s.2⟩
  have hPleE' : (P : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) ≤ E.map ρ₀.toMonoidHom := by
    intro p hp
    obtain ⟨s, rfl⟩ := ρ₀.surjective p
    exact Subgroup.mem_map.mpr ⟨s, hS0E hp, rfl⟩
  have hE'conj : E.map ρ₀.toMonoidHom =
      ggSL9Torus.map (MulAut.conj g).toMonoidHom :=
    (le_antisymm hE'P hPleE').trans hPg
  refine ⟨ρ₀.trans (MulAut.conj g⁻¹), ?_⟩
  show E.map ((MulAut.conj g⁻¹).toMonoidHom.comp ρ₀.toMonoidHom) = ggSL9Torus
  rw [← Subgroup.map_map, hE'conj, Subgroup.map_map]
  have hconj : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change MulAut.conj g⁻¹ (MulAut.conj g x) = x
    rw [show MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ from map_inv _ _]
    exact (MulAut.conj g).symm_apply_apply x
  rw [hconj, Subgroup.map_id]

end CFSG.StandardType

end
