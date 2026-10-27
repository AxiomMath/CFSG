module

public import CFSG.Quasithin.Vol2.Ch10SecD12L

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isPGroup_sup_of_conj {V1 W : Subgroup G} {y z' z : G}
    (hV1Q : V1 ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hW2 : IsPGroup 2 ↥W)
    (hWz : W ≤ Subgroup.centralizer ({z'} : Set G)) (hyz : y * z' * y⁻¹ = z)
    (hyV : y ∈ Subgroup.normalizer (V1 : Set G)) : IsPGroup 2 ↥(V1 ⊔ W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({z} : Set G))
  have hQN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({z} : Set G))
  have hWz' : conjSubgroup W y⁻¹ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_conjSubgroup_inv_iff] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hWz hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hyz]
    calc x * (y * z' * y⁻¹) = y * ((y⁻¹ * x * y) * z') * y⁻¹ := by group
      _ = y * (z' * (y⁻¹ * x * y)) * y⁻¹ := by rw [h1]
      _ = y * z' * y⁻¹ * x := by group
  have hP := IsPGroup.to_sup_of_normal_left' hQ2 (isPGroup_conjSubgroup hW2 y⁻¹)
    (hWz'.trans hQN)
  have hP' : IsPGroup 2 ↥(V1 ⊔ conjSubgroup W y⁻¹) := hP.to_le (sup_le_sup_right hV1Q _)
  have hV1y : conjSubgroup V1 y = V1 := conjSubgroup_eq_iff_mem_normalizer.2 hyV
  have heq : conjSubgroup (V1 ⊔ conjSubgroup W y⁻¹) y = V1 ⊔ W := by
    rw [show conjSubgroup (V1 ⊔ conjSubgroup W y⁻¹) y =
      conjSubgroup V1 y ⊔ conjSubgroup (conjSubgroup W y⁻¹) y from Subgroup.map_sup _ _ _,
      hV1y, conjSubgroup_inv_conj]
  have := isPGroup_conjSubgroup hP' y
  rwa [heq] at this

theorem isPGroup_sup_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h10211 : Stmt10_2_11) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G}
    (hk : mQuot (conjSubgroup (fsuVM T L I) g) (conjSubgroup (fsuVM T L I) g ⊓ fsuM T L) = 1)
    {X : Subgroup G} (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hUM : fsuUL T L I ⊓ Subgroup.centralizer ((conjSubgroup X g ⊓ fsuM T L : Subgroup G) :
      Set G) ≤ conjSubgroup (fsuM T L) g) {c u : G}
    (hcV : c ∈ conjSubgroup (fsuVM T L I) g ⊓ fsuM T L)
    (hu : u ∈ fsuUL T L I ⊓ Subgroup.centralizer ((conjSubgroup X g ⊓ fsuM T L : Subgroup G) :
      Set G)) (hcu : c * u ≠ u * c) : IsPGroup 2 ↥(fsuUL T L I ⊔ conjSubgroup X g) := by
  have hV := SecA.isElemAbelian_fsuVM h
  have hVg := isElemAbelian_conjSubgroup hV g
  have hu1 : u ≠ 1 := by rintro rfl; exact hcu (by group)
  have hu2 : u * u = 1 := by rw [← pow_two]; exact (B2F.isElemAbelian_mono V1_le_V hV).2 u hu.1
  have huinv : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, hu2]
  have huN : u ∈ Subgroup.normalizer ((conjSubgroup (fsuVM T L I) g : Subgroup G) : Set G) := by
    rw [← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left g (SecA.fsuM_le_normalizer_fsuVM T L I) (hUM hu)
  have hcinvV : u * c⁻¹ * u⁻¹ ∈ conjSubgroup (fsuVM T L I) g :=
    (Subgroup.mem_normalizer_iff.mp huN _).mp ((conjSubgroup _ g).inv_mem hcV.1)
  have hcN : c ∉ Subgroup.normalizer (fsuUL T L I : Set G) := by
    intro hcN
    have hz1 : c * u * c⁻¹ * u⁻¹ ∈ fsuUL T L I :=
      (fsuUL T L I).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN u).mp hu.1)
        ((fsuUL T L I).inv_mem hu.1)
    have hz2 : c * u * c⁻¹ * u⁻¹ ∈ conjSubgroup (fsuVM T L I) g := by
      have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [e]
      exact (conjSubgroup _ g).mul_mem hcV.1 hcinvV
    have hz3 : c * u * c⁻¹ * u⁻¹ ≠ 1 := fun h1 => hcu (by
      calc c * u = (c * u * c⁻¹ * u⁻¹) * u * c := by group
        _ = u * c := by rw [h1]; group)
    have hle : conjSubgroup (fsuVM T L I) g ≤ fsuM T L := fun x hx =>
      (h1029 G T L I h L (Or.inl rfl)).1 _ hz1 hz3 (Subgroup.mem_centralizer_singleton_iff.mpr
        (B2F.isElemAbelian_comm hVg hx hz2))
    rw [inf_eq_left.mpr hle, mQuot_self] at hk
    exact absurd hk (by norm_num)
  obtain ⟨hc1, -⟩ : CFSG.conjugate (fsuUL T L I) c = ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
      CFSG.conjugate ⁅fsuVM T L I, CFSG.conjugate L t⁆ c = fsuUL T L I := by
    rcases mem_normalizer_V12_or h37 h38 h ht htn hcV.2 with h1 | h1
    · exact absurd h1.1 hcN
    · exact h1
  have hu2V : c⁻¹ * u * c ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rw [← hc1, SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hu.1
  have hz'V : u * (c⁻¹ * u * c) ∈ conjSubgroup (fsuVM T L I) g := by
    have e : u * (c⁻¹ * u * c) = (u * c⁻¹ * u⁻¹) * c := by rw [huinv]; group
    rw [e]
    exact (conjSubgroup _ g).mul_mem hcinvV hcV.1
  have hu2ne : c⁻¹ * u * c ≠ 1 := fun h1 => hu1 (by
    calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨t', v1, v2, hd⟩ := exists_isData10_2_11 h37 h38 h h3 hc
  have hLt' : CFSG.conjugate L t' = CFSG.conjugate L t :=
    SecA.conjugate_eq_of_not_mem h37 h38 h ht htn hd.1 hd.2.1
  have hv2 : v2 ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hLt' ▸ hd.2.2.2.2.1.1
  obtain ⟨l1, hl1, hl1u⟩ := exists_conj_V1 h3 hc hu.1 hd.2.2.1.1 hu1 hd.2.2.2.1
  have hV2t : ∀ x, x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ↔ t * x * t⁻¹ ∈ fsuUL T L I := by
    intro x
    rw [V2_eq_conjugate ht, SecA.mem_conjugate_iff]
  have hne1 : ∀ x : G, x ≠ 1 → t * x * t⁻¹ ≠ 1 := fun x hx h1 => hx (by
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨l, hl, hlu⟩ := exists_conj_V1 h3 hc ((hV2t _).mp hu2V) ((hV2t _).mp hv2)
    (hne1 _ hu2ne) (hne1 _ hd.2.2.2.2.2)
  have hl2 : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hl
  have hl2u : (t⁻¹ * l * t) * (c⁻¹ * u * c) * (t⁻¹ * l * t)⁻¹ = v2 := by
    calc (t⁻¹ * l * t) * (c⁻¹ * u * c) * (t⁻¹ * l * t)⁻¹ =
          t⁻¹ * (l * (t * (c⁻¹ * u * c) * t⁻¹) * l⁻¹) * t := by group
      _ = t⁻¹ * (t * v2 * t⁻¹) * t := by rw [hlu]
      _ = v2 := by group
  have hl1V2 : ∀ x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, l1 * x * l1⁻¹ = x := fun x hx => by
    rw [Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hx) l1 hl1]
    group
  have hl2V1 : ∀ x ∈ fsuUL T L I, (t⁻¹ * l * t) * x * (t⁻¹ * l * t)⁻¹ = x := fun x hx => by
    rw [← Subgroup.mem_centralizer_iff.mp (conjugate_le_centralizer_V1 h ht htn hl2) x hx]
    group
  set y := l1 * (t⁻¹ * l * t) with hy
  have hyz : y * (u * (c⁻¹ * u * c)) * y⁻¹ = v1 * v2 := by
    calc y * (u * (c⁻¹ * u * c)) * y⁻¹ =
          l1 * (((t⁻¹ * l * t) * u * (t⁻¹ * l * t)⁻¹) *
            ((t⁻¹ * l * t) * (c⁻¹ * u * c) * (t⁻¹ * l * t)⁻¹)) * l1⁻¹ := by rw [hy]; group
      _ = l1 * (u * v2) * l1⁻¹ := by rw [hl2V1 u hu.1, hl2u]
      _ = (l1 * u * l1⁻¹) * (l1 * v2 * l1⁻¹) := by group
      _ = v1 * v2 := by rw [hl1u, hl1V2 v2 hv2]
  have hyN : y ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
    refine (Subgroup.normalizer _).mul_mem (L_le_normalizer_V1 hl1) ?_
    exact Subgroup.centralizer_le_normalizer _ (conjugate_le_centralizer_V1 h ht htn hl2)
  have hQ := (h10211 G T L I h h3 hc t' v1 v2 hd).2.2
  have hXV : conjSubgroup X g ≤ conjSubgroup (fsuVM T L I) g :=
    conjSubgroup_mono_left g (le_V_of_eq ht hX)
  refine isPGroup_sup_of_conj (V1_le_V.trans hQ)
    ((B2F.isPGroup_of_isElemAbelian hVg).to_le hXV) (fun x hx => ?_) hyz hyN
  exact Subgroup.mem_centralizer_singleton_iff.mpr (B2F.isElemAbelian_comm hVg (hXV hx) hz'V)

end CFSG.Quasithin.Vol2.Ch10.SecD
