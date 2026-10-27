module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure s16h_MixedCfg {G : Type} [Group G] (M B₀ Y Z₁ : Subgroup G) (x : G) : Prop where
  mem : x ∈ M
  le : Y ≤ M
  norm : M ≤ normalizer (Y : Set G)
  elem : IsElemAbelian 2 Y
  sup : Y = Z₁ ⊔ Z₁.map (MulAut.conj x).toMonoidHom
  perm : ∀ m ∈ M,
    (Z₁.map (MulAut.conj m).toMonoidHom = Z₁ ∧
      (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj m).toMonoidHom =
        Z₁.map (MulAut.conj x).toMonoidHom) ∨
    (Z₁.map (MulAut.conj m).toMonoidHom = Z₁.map (MulAut.conj x).toMonoidHom ∧
      (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj m).toMonoidHom = Z₁)
  B₀le : B₀ ≤ M
  stab : ∀ m ∈ M, m ∈ B₀ ↔ Z₁.map (MulAut.conj m).toMonoidHom = Z₁

variable {G : Type} [Group G] [Finite G]

private lemma s16h_mixed_conj_eq_self {K : Subgroup G} {g : G}
    (h : ∀ z ∈ K, g * z = z * g) {z : G} (hz : z ∈ K) :
    g * z * g⁻¹ = z := by
  rw [h z hz]
  group

private lemma s16h_mixed_map_conj_eq_of_centralizes {K : Subgroup G} {g : G}
    (h : ∀ z ∈ K, g * z = z * g) : K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · intro z hz
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.mp hz
    rw [← hz'eq]
    change g * z' * g⁻¹ ∈ K
    rw [s16h_mixed_conj_eq_self h hz']
    exact hz'
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    change g * z * g⁻¹ = z
    exact s16h_mixed_conj_eq_self h hz

private lemma s16h_mixed_Z₁_le {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) : Z₁ ≤ Y := by
  rw [hB.sup]; exact le_sup_left

private lemma s16h_mixed_Z₂_le {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) :
    Z₁.map (MulAut.conj x).toMonoidHom ≤ Y := by
  rw [hB.sup]; exact le_sup_right

private lemma s16h_mixed_Z₂_ne_Z₁ {Z₁ : Subgroup G} {x e : G}
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    Z₁.map (MulAut.conj x).toMonoidHom ≠ Z₁ := by
  intro h
  obtain ⟨z, hz, hne⟩ := heZ₂
  exact hne (heZ₁ z (h ▸ hz))

private lemma s16h_mixed_Z₂_map_conj_e {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      Z₁.map (MulAut.conj x).toMonoidHom := by
  rcases hB.perm e heM with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd (h1 ▸ s16h_mixed_map_conj_eq_of_centralizes heZ₁)
      (s16h_mixed_Z₂_ne_Z₁ heZ₁ heZ₂)

private lemma s16h_mixed_Z₂_map_conj_x {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = Z₁ := by
  rcases hB.perm x hB.mem with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 (s16h_mixed_Z₂_ne_Z₁ heZ₁ heZ₂)
  · exact h2

private lemma s16h_mixed_f_mem_M {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M) : x * e * x⁻¹ ∈ M :=
  M.mul_mem (M.mul_mem hB.mem heM) (M.inv_mem hB.mem)

private lemma s16h_mixed_f_pow {x e : G} {q : ℕ} (heq : e ^ q = 1) :
    (x * e * x⁻¹) ^ q = 1 := by
  have h : ((MulAut.conj x).toMonoidHom e) ^ q = 1 := by
    rw [← map_pow, heq, map_one]
  simpa using h

private lemma s16h_mixed_f_centralizes_Z₂ {Z₁ : Subgroup G} {x e : G}
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e) :
    ∀ z ∈ Z₁.map (MulAut.conj x).toMonoidHom,
      (x * e * x⁻¹) * z = z * (x * e * x⁻¹) := by
  intro z hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  change (MulAut.conj x).toMonoidHom e * (MulAut.conj x).toMonoidHom z' =
    (MulAut.conj x).toMonoidHom z' * (MulAut.conj x).toMonoidHom e
  rw [← map_mul, heZ₁ z' hz', map_mul]

private lemma s16h_mixed_f_moves_Z₁ {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    ∃ z₁ ∈ Z₁, (x * e * x⁻¹) * z₁ * (x * e * x⁻¹)⁻¹ ≠ z₁ := by
  have heZ₂' := heZ₂
  obtain ⟨z₂, hz₂, hne⟩ := heZ₂'
  refine ⟨x * z₂ * x⁻¹, ?_, ?_⟩
  · have hZ₂x : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = Z₁ :=
      s16h_mixed_Z₂_map_conj_x (M := M) (B₀ := B₀) (Y := Y) (Z₁ := Z₁) (x := x) (e := e)
        hB heZ₁ heZ₂
    rw [← hZ₂x]
    exact Subgroup.mem_map_of_mem _ hz₂
  · intro h
    apply hne
    have h' := congrArg (fun t => x⁻¹ * t * x) h
    have hconj : e * z₂ * e⁻¹ = z₂ := by
      rw [show x⁻¹ * ((x * e * x⁻¹) * (x * z₂ * x⁻¹) * (x * e * x⁻¹)⁻¹) * x
            = e * z₂ * e⁻¹ from by group,
          show x⁻¹ * (x * z₂ * x⁻¹) * x = z₂ from by group] at h'
      exact h'
    calc e * z₂ = e * z₂ * e⁻¹ * e := by group
      _ = z₂ * e := by rw [hconj]

private lemma s16h_mixed_f_mem_B₀ {M B₀ Y Z₁ : Subgroup G} {x e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) :
    x * e * x⁻¹ ∈ B₀ := by
  rw [hB.stab _ (s16h_mixed_f_mem_M hB heM)]
  rcases hB.perm (x * e * x⁻¹) (s16h_mixed_f_mem_M hB heM) with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exfalso
    have hZ₂f : (Z₁.map (MulAut.conj x).toMonoidHom).map
        (MulAut.conj (x * e * x⁻¹)).toMonoidHom = Z₁.map (MulAut.conj x).toMonoidHom :=
      s16h_mixed_map_conj_eq_of_centralizes
        (K := Z₁.map (MulAut.conj x).toMonoidHom) (g := x * e * x⁻¹)
        (s16h_mixed_f_centralizes_Z₂ (x := x) heZ₁)
    exact (s16h_mixed_Z₂_ne_Z₁ heZ₁ heZ₂) (h2.symm.trans hZ₂f).symm


theorem s16h_mixed_card_ge_eight {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {e : G} (heM : e ∈ M)
    (heq : e ^ q = 1) (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) : 8 ≤ Nat.card ↥Y := by
  have hZ₁Y : Z₁ ≤ Y := s16h_mixed_Z₁_le hB
  have hZ₂Y : Z₁.map (MulAut.conj x).toMonoidHom ≤ Y := s16h_mixed_Z₂_le hB
  have hZ₂_ne_bot : Z₁.map (MulAut.conj x).toMonoidHom ≠ ⊥ := by
    obtain ⟨z, hz, hne⟩ := heZ₂
    intro h
    rw [h] at hz
    have hz1 : z = 1 := Subgroup.mem_bot.mp hz
    exact hne (by rw [hz1, mul_one, one_mul])
  have hZ₁_ne_bot : Z₁ ≠ ⊥ := by
    obtain ⟨z, hz, hne⟩ := heZ₂
    obtain ⟨z', hz', hzx⟩ := Subgroup.mem_map.mp hz
    intro h
    rw [h] at hz'
    have hz'1 : z' = 1 := Subgroup.mem_bot.mp hz'
    exact hne (by rw [← hzx, hz'1, map_one, mul_one, one_mul])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYP : IsPGroup 2 ↥Y := fun y =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hB.elem.2 y y.2)⟩
  obtain ⟨n, hn⟩ := hYP.exists_card_eq
  suffices h : 3 ≤ n by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      _ = Nat.card ↥Y := hn.symm
  by_contra hlt
  have hn2 : n ≤ 2 := by omega
  interval_cases n
  · have hn1 : Nat.card ↥Y = 1 := by simpa using hn
    have h1 : 1 < Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ₂_ne_bot
    have h2 := Subgroup.card_le_of_le hZ₂Y
    omega
  · have hn2' : Nat.card ↥Y = 2 := by simpa using hn
    have h1 : 1 < Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ₂_ne_bot
    have h2 : 1 < Nat.card ↥Z₁ := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ₁_ne_bot
    have h3 := Subgroup.card_le_of_le hZ₂Y
    have h4 := Subgroup.card_le_of_le hZ₁Y
    have hZY : Z₁.map (MulAut.conj x).toMonoidHom = Y :=
      Subgroup.eq_of_le_of_card_ge hZ₂Y (by omega)
    have hZ₁Y' : Z₁ = Y := Subgroup.eq_of_le_of_card_ge hZ₁Y (by omega)
    exact s16h_mixed_Z₂_ne_Z₁ heZ₁ heZ₂ (hZY.trans hZ₁Y'.symm)
  · norm_num at hn
    have heZ₂' := heZ₂
    obtain ⟨z₀, hz₀, hne₀⟩ := heZ₂'
    have hz₀_ne_one : z₀ ≠ 1 := by
      intro h; exact hne₀ (by rw [h, mul_one, one_mul])
    have hw₀ : e * z₀ * e⁻¹ ∈ Z₁.map (MulAut.conj x).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hz₀
      have hZ₂e : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj e).toMonoidHom =
          Z₁.map (MulAut.conj x).toMonoidHom :=
        s16h_mixed_Z₂_map_conj_e hB heM heZ₁ heZ₂
      rwa [hZ₂e] at h
    have hw₀_ne_one : e * z₀ * e⁻¹ ≠ 1 := by
      intro h
      apply hz₀_ne_one
      have h' := congrArg (fun t => e⁻¹ * t * e) h
      rw [show e⁻¹ * (e * z₀ * e⁻¹) * e = z₀ from by group,
          show e⁻¹ * 1 * e = 1 from by group] at h'
      exact h'
    have hw₀_ne_z₀ : e * z₀ * e⁻¹ ≠ z₀ := by
      intro h
      apply hne₀
      calc e * z₀ = e * z₀ * e⁻¹ * e := by group
        _ = z₀ * e := by rw [h]
    have h3 : 3 ≤ Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) := by
      have hinj : Function.Injective (fun i : Fin 3 =>
          (![⟨1, Subgroup.one_mem _⟩, ⟨z₀, hz₀⟩,
            ⟨e * z₀ * e⁻¹, hw₀⟩] : Fin 3 → ↥(Z₁.map (MulAut.conj x).toMonoidHom)) i) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
      calc 3 = Nat.card (Fin 3) := by simp
        _ ≤ Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) :=
            Nat.card_le_card_of_injective _ hinj
    have hZ₂P : IsPGroup 2 ↥(Z₁.map (MulAut.conj x).toMonoidHom) := fun y =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hB.elem.2 y.1 (hZ₂Y y.2))⟩
    obtain ⟨m, hm⟩ := hZ₂P.exists_card_eq
    have hm2 : 2 ≤ m := by
      by_contra hc
      have hm1 : m ≤ 1 := by omega
      interval_cases m <;> omega
    have h4 : 4 ≤ Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        _ = Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) := hm.symm
    have hZ₂card : Nat.card ↥(Z₁.map (MulAut.conj x).toMonoidHom) = 4 := by
      have h5 := Subgroup.card_le_of_le hZ₂Y
      omega
    have hxN : x ∈ normalizer (Y : Set G) := hB.norm hB.mem
    have hYx : Y.map (MulAut.conj x).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    have hZY : Z₁.map (MulAut.conj x).toMonoidHom = Y :=
      Subgroup.eq_of_le_of_card_ge hZ₂Y (by omega)
    have hZ₁eq : Z₁ = Y := by
      rw [← s16h_mixed_Z₂_map_conj_x hB heZ₁ heZ₂, hZY]
      exact hYx
    exact s16h_mixed_Z₂_ne_Z₁ heZ₁ heZ₂ (hZY.trans hZ₁eq.symm)

private lemma s16h_mixed_conj_kek_normalizes {M B₀ Y Z₁ : Subgroup G} {x k e : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) (heM : e ∈ M)
    (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e)
    (hk2 : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj k).toMonoidHom = Z₁) :
    Z₁.map (MulAut.conj (k * e * k⁻¹)).toMonoidHom = Z₁ := by
  have he2 : (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      Z₁.map (MulAut.conj x).toMonoidHom :=
    s16h_mixed_Z₂_map_conj_e hB heM heZ₁ heZ₂
  apply Subgroup.eq_of_le_of_card_ge
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have hw : k⁻¹ * z' * k ∈ Z₁.map (MulAut.conj x).toMonoidHom := by
      have hz'' : z' ∈ (Z₁.map (MulAut.conj x).toMonoidHom).map
          (MulAut.conj k).toMonoidHom := by rw [hk2]; exact hz'
      obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp hz''
      have : w = k⁻¹ * z' * k := by
        rw [← hweq]
        rw [show (MulAut.conj k).toMonoidHom w = k * w * k⁻¹ from rfl]
        group
      exact this ▸ hw
    have hew : e * (k⁻¹ * z' * k) * e⁻¹ ∈ Z₁.map (MulAut.conj x).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hw
      rwa [he2] at h
    have hkw : k * (e * (k⁻¹ * z' * k) * e⁻¹) * k⁻¹ ∈ Z₁ := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hew
      rwa [hk2] at h
    have hgoal : (MulAut.conj (k * e * k⁻¹)).toMonoidHom z' =
        k * (e * (k⁻¹ * z' * k) * e⁻¹) * k⁻¹ := by
      rw [show (MulAut.conj (k * e * k⁻¹)).toMonoidHom z' =
          k * e * k⁻¹ * z' * (k * e * k⁻¹)⁻¹ from rfl]
      group
    rwa [hgoal]
  · rw [Subgroup.card_map_of_injective (MulAut.conj (k * e * k⁻¹)).injective]

theorem s16h_mixed_stab_of_two_group {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {e : G} (heM : e ∈ M)
    (heq : e ^ q = 1) (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e) {K : Subgroup G}
    (hKM : K ≤ M) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hK2 : ∀ k ∈ K, ∃ n : ℕ, ∀ y ∈ Y, k ^ 2 ^ n * y = y * k ^ 2 ^ n) : K ≤ B₀ := by
  intro k hk
  rw [hB.stab k (hKM hk)]
  by_contra hkZ
  rcases hB.perm k (hKM hk) with ⟨h1, -⟩ | ⟨hk1, hk2⟩
  · exact hkZ h1
  · have hκZ₁ : Z₁.map (MulAut.conj (k * e * k⁻¹)).toMonoidHom = Z₁ :=
      s16h_mixed_conj_kek_normalizes hB heM heZ₁ heZ₂ hk2
    have hc₀K : k * e * k⁻¹ * e⁻¹ ∈ K := by
      have h1 : e * k⁻¹ * e⁻¹ ∈ K := hKn e heM k⁻¹ (K.inv_mem hk)
      have h2 : k * (e * k⁻¹ * e⁻¹) ∈ K := K.mul_mem hk h1
      rwa [show k * (e * k⁻¹ * e⁻¹) = k * e * k⁻¹ * e⁻¹ from by group] at h2
    have hκN : k * e * k⁻¹ ∈ normalizer (Z₁ : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hκZ₁
    have he_inv_N : e⁻¹ ∈ normalizer (Z₁ : Set G) := by
      have heN : e ∈ normalizer (Z₁ : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (s16h_mixed_map_conj_eq_of_centralizes heZ₁)
      exact (normalizer (Z₁ : Set G)).inv_mem heN
    have hc₀N : k * e * k⁻¹ * e⁻¹ ∈ normalizer (Z₁ : Set G) :=
      (normalizer (Z₁ : Set G)).mul_mem hκN he_inv_N
    let σκ : MulAut ↥Z₁ := Z₁.normalizerMonoidHom ⟨k * e * k⁻¹, hκN⟩
    let σc : MulAut ↥Z₁ := Z₁.normalizerMonoidHom ⟨k * e * k⁻¹ * e⁻¹, hc₀N⟩
    have hact : ∀ z ∈ Z₁, (k * e * k⁻¹ * e⁻¹) * z * (k * e * k⁻¹ * e⁻¹)⁻¹ =
        (k * e * k⁻¹) * z * (k * e * k⁻¹)⁻¹ := by
      intro z hz
      have hei : e⁻¹ * z * e = z := by
        rw [mul_assoc, ← heZ₁ z hz]; group
      rw [show (k * e * k⁻¹ * e⁻¹) * z * (k * e * k⁻¹ * e⁻¹)⁻¹ =
          (k * e * k⁻¹) * (e⁻¹ * z * e) * (k * e * k⁻¹)⁻¹ from by group, hei]
    have hσκc : σκ = σc := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      exact (hact z z.2).symm
    have hσκq : σκ ^ q = 1 := by
      change (Z₁.normalizerMonoidHom ⟨k * e * k⁻¹, hκN⟩) ^ q = 1
      rw [← map_pow]
      apply MonoidHom.mem_ker.mp
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa [heq] using Subgroup.one_mem (centralizer (Z₁ : Set G))
    obtain ⟨n, hn⟩ := hK2 (k * e * k⁻¹ * e⁻¹) hc₀K
    have hc₀pow : (k * e * k⁻¹ * e⁻¹) ^ 2 ^ n ∈ centralizer (Z₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hn z (s16h_mixed_Z₁_le hB hz)).symm
    have hσc2 : σc ^ 2 ^ n = 1 := by
      change (Z₁.normalizerMonoidHom ⟨k * e * k⁻¹ * e⁻¹, hc₀N⟩) ^ 2 ^ n = 1
      rw [← map_pow]
      apply MonoidHom.mem_ker.mp
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa using hc₀pow
    have hσκ2 : σκ ^ 2 ^ n = 1 := by rw [hσκc]; exact hσc2
    have hcop' : Nat.Coprime q (2 ^ n) := (hq.coprime_iff_not_dvd).mpr (by
      intro hdiv
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdiv)))
    have hcop : Nat.Coprime (2 ^ n) q := hcop'.symm
    have hdvd2 : orderOf σκ ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hσκ2
    have hdvdq : orderOf σκ ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hσκq
    have horder : orderOf σκ = 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvdq
      rw [hcop.gcd_eq_one] at h
      exact Nat.dvd_one.mp h
    have hσκ1 : σκ = 1 := orderOf_eq_one_iff.mp horder
    have hκC : k * e * k⁻¹ ∈ centralizer (Z₁ : Set G) := by
      have hmem : (⟨k * e * k⁻¹, hκN⟩ : ↥(normalizer (Z₁ : Set G))) ∈
          Z₁.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hσκ1
      rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨z₂, hz₂, hne₂⟩ := heZ₂
    have hz₁ : k * z₂ * k⁻¹ ∈ Z₁ := by
      have h : k * z₂ * k⁻¹ ∈
          (Z₁.map (MulAut.conj x).toMonoidHom).map (MulAut.conj k).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz₂
      rwa [hk2] at h
    have hκz₁ : (k * e * k⁻¹) * (k * z₂ * k⁻¹) * (k * e * k⁻¹)⁻¹ = k * z₂ * k⁻¹ := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hκC) (k * z₂ * k⁻¹) hz₁
      calc (k * e * k⁻¹) * (k * z₂ * k⁻¹) * (k * e * k⁻¹)⁻¹
          = (k * z₂ * k⁻¹) * (k * e * k⁻¹) * (k * e * k⁻¹)⁻¹ := by rw [hcomm]
        _ = k * z₂ * k⁻¹ := by group
    apply hne₂
    have h' := congrArg (fun t => k⁻¹ * t * k) hκz₁
    have : e * z₂ * e⁻¹ = z₂ := by
      rw [show k⁻¹ * ((k * e * k⁻¹) * (k * z₂ * k⁻¹) * (k * e * k⁻¹)⁻¹) * k
            = e * z₂ * e⁻¹ from by group,
          show k⁻¹ * (k * z₂ * k⁻¹) * k = z₂ from by group] at h'
      exact h'
    calc e * z₂ = e * z₂ * e⁻¹ * e := by group
      _ = z₂ * e := by rw [this]

theorem s16h_mixed_two_reduced {M B₀ Y Z₁ : Subgroup G} {x : G}
    (hB : s16h_MixedCfg M B₀ Y Z₁ x) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {e : G} (heM : e ∈ M)
    (heq : e ^ q = 1) (heZ₁ : ∀ z ∈ Z₁, e * z = z * e)
    (heZ₂ : ∃ z ∈ Z₁.map (MulAut.conj x).toMonoidHom, e * z ≠ z * e)
    (hc : ∀ K : Subgroup G, K ≤ B₀ → (∀ g ∈ B₀, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈ centralizer (Z₁ : Set G)) →
      (∃ f ∈ B₀, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ f ∉ centralizer (Z₁ : Set G) ∧
        f ^ r ∈ centralizer (Z₁ : Set G)) → K ≤ centralizer (Z₁ : Set G)) :
    TwoReduced M Y := by
  intro K hKM hKN hCK hexp
  haveI hNorm : ((centralizer (Y : Set G)).subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hcoe : (↑(g * n * g⁻¹) : G) = (↑g : G) * ↑n * (↑g : G)⁻¹ := by simp
      rw [hcoe]
      rw [Subgroup.mem_centralizer_iff] at hn ⊢
      intro y hy
      have hgY : (↑g : G) ∈ normalizer (Y : Set G) := hB.norm (hKM g.2)
      have hginv : (↑g : G)⁻¹ ∈ normalizer (Y : Set G) := (normalizer (Y : Set G)).inv_mem hgY
      have hy' : (↑g : G)⁻¹ * y * ↑g ∈ Y := by
        simpa using ((Subgroup.mem_normalizer_iff.mp hginv) y).1 hy
      have hcomm := hn _ hy'
      calc y * ((↑g : G) * (↑n : G) * ((↑g : G))⁻¹)
          = (↑g : G) * ((((↑g : G))⁻¹ * y * (↑g : G)) * (↑n : G)) * ((↑g : G))⁻¹ := by
            group
        _ = (↑g : G) * ((↑n : G) * (((↑g : G))⁻¹ * y * (↑g : G))) * ((↑g : G))⁻¹ := by
            rw [hcomm]
        _ = ((↑g : G) * (↑n : G) * ((↑g : G))⁻¹) * y := by group⟩
  obtain ⟨n, hn⟩ := hexp
  have hK2 : ∀ k ∈ K, ∃ m : ℕ, ∀ y ∈ Y, k ^ 2 ^ m * y = y * k ^ 2 ^ m := by
    intro k hk
    have hkn : k ^ 2 ^ n ∈ centralizer (Y : Set G) := by
      have h := Subgroup.pow_index_mem ((centralizer (Y : Set G)).subgroupOf K) (⟨k, hk⟩ : ↥K)
      rw [hn] at h
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    exact ⟨n, fun y hy => ((Subgroup.mem_centralizer_iff.mp hkn) y hy).symm⟩
  have hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    exact ((Subgroup.mem_normalizer_iff.mp (hKN hm)) k).1 hk
  have hKB : K ≤ B₀ := s16h_mixed_stab_of_two_group hB hq hq2 heM heq heZ₁ heZ₂ hKM hKn hK2
  have hf_notC : x * e * x⁻¹ ∉ centralizer (Z₁ : Set G) := by
    intro hfC
    obtain ⟨z₁, hz₁, hne₁⟩ := s16h_mixed_f_moves_Z₁ hB heZ₁ heZ₂
    apply hne₁
    have hcomm := (Subgroup.mem_centralizer_iff.mp hfC) z₁ hz₁
    calc (x * e * x⁻¹) * z₁ * (x * e * x⁻¹)⁻¹
        = z₁ * (x * e * x⁻¹) * (x * e * x⁻¹)⁻¹ := by rw [← hcomm]
      _ = z₁ := by group
  have hfqC : (x * e * x⁻¹) ^ q ∈ centralizer (Z₁ : Set G) := by
    rw [s16h_mixed_f_pow heq]
    exact Subgroup.one_mem _
  have hKZ₁ : K ≤ centralizer (Z₁ : Set G) :=
    hc K hKB (fun g hg k hk => hKn g (hB.B₀le hg) k hk)
      (fun k hk => by
        obtain ⟨m, hm⟩ := hK2 k hk
        refine ⟨m, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hm z (s16h_mixed_Z₁_le hB hz)).symm)
      ⟨x * e * x⁻¹, s16h_mixed_f_mem_B₀ hB heM heZ₁ heZ₂, q, hq, hq2, hf_notC, hfqC⟩
  have hKZ₂ : K ≤ centralizer ((Z₁.map (MulAut.conj x).toMonoidHom) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z₂ hz₂
    obtain ⟨z₁, hz₁, rfl⟩ := Subgroup.mem_map.mp hz₂
    have hkx : x⁻¹ * k * x ∈ centralizer (Z₁ : Set G) :=
      hKZ₁ (by simpa using hKn x⁻¹ (M.inv_mem hB.mem) k hk)
    have hcomm := (Subgroup.mem_centralizer_iff.mp hkx) z₁ hz₁
    calc (x * z₁ * x⁻¹) * k = x * (z₁ * (x⁻¹ * k * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * k * x) * z₁) * x⁻¹ := by rw [hcomm]
      _ = k * (x * z₁ * x⁻¹) := by group
  rw [hB.sup]
  rw [Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.le_centralizer_iff.mp hKZ₁) (Subgroup.le_centralizer_iff.mp hKZ₂)

theorem s16h_exists_noncyclic_of_le_range {N H : Type*} [Group N] [Finite N] [Group H]
    (φ : N →* H) {q : ℕ} (hq : q.Prime) {E : Subgroup H} (hE : E ≤ φ.range)
    (hEq : IsPGroup q E) (hEn : ¬ IsCyclic ↥E) :
    ∃ S : Subgroup N, IsPGroup q S ∧ ¬ IsCyclic ↥S := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let P : Subgroup N := E.comap φ
  let ψ : ↥P →* ↥E := (φ.comp P.subtype).codRestrict E (fun x => x.2)
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hE e.2
    exact ⟨⟨x, by change φ x ∈ E; rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow q ↥P) := inferInstance
  have htop : (S₀.mapSurjective hψ : Subgroup ↥E) = ⊤ :=
    ((S₀.mapSurjective hψ).3 (Q := ⊤) (hEq.of_equiv Subgroup.topEquiv.symm) le_top).symm
  refine ⟨(S₀ : Subgroup ↥P).map P.subtype, S₀.isPGroup'.map P.subtype, ?_⟩
  rintro hcyc
  apply hEn
  have hmap : ((S₀ : Subgroup ↥P).map P.subtype).map φ = E := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ (S₀ : Subgroup ↥P).map P.subtype at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact (ψ s).2
    · intro hy
      have hmem : (⟨y, hy⟩ : ↥E) ∈ (S₀.mapSurjective hψ : Subgroup ↥E) := by
        rw [htop]; exact Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective, Subgroup.mem_map] at hmem
      obtain ⟨s, hs, hsy⟩ := hmem
      exact ⟨P.subtype s, Subgroup.mem_map_of_mem P.subtype hs, congrArg Subtype.val hsy⟩
  let φS : ↥((S₀ : Subgroup ↥P).map P.subtype) →* ↥E :=
    (φ.comp (Subgroup.subtype _)).codRestrict E (fun s => hmap ▸ Subgroup.mem_map_of_mem φ s.2)
  have hφS : Function.Surjective φS := by
    intro e
    have he : (e : H) ∈ ((S₀ : Subgroup ↥P).map P.subtype).map φ := hmap.symm ▸ e.2
    rw [Subgroup.mem_map] at he
    obtain ⟨s, hs, hse⟩ := he
    exact ⟨⟨s, hs⟩, Subtype.ext hse⟩
  haveI : IsCyclic ↥((S₀ : Subgroup ↥P).map P.subtype) := hcyc
  exact isCyclic_of_surjective φS hφS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
