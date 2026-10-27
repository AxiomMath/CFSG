module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.ModH.M23a

open Equiv

abbrev S3S3 : Type := Perm (Fin 3) × Perm (Fin 3)

def c3 : Perm (Fin 3) := swap 0 1 * swap 1 2

theorem comm_fst : ∀ a x : S3S3, a ^ 4 = 1 → a.2 = 1 → a ≠ 1 → x ^ 3 = 1 → x.1 ≠ 1 →
    (a * x * a⁻¹ * x⁻¹ = (c3, 1) ∨ a * x * a⁻¹ * x⁻¹ = (c3⁻¹, 1)) := by
  set_option synthInstance.maxSize 4096 in decide

theorem comm_snd : ∀ b x : S3S3, b ^ 4 = 1 → b.1 = 1 → b ≠ 1 → x ^ 3 = 1 → x.2 ≠ 1 →
    (b * x * b⁻¹ * x⁻¹ = (1, c3) ∨ b * x * b⁻¹ * x⁻¹ = (1, c3⁻¹)) := by
  set_option synthInstance.maxSize 4096 in decide

theorem orderOf_c3_one : orderOf ((c3, 1) : S3S3) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_one_c3 : orderOf ((1, c3) : S3S3) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem card_perm_three : Nat.card (Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem card_s3s3 : Nat.card S3S3 = 36 := by
  rw [Nat.card_prod, card_perm_three]

theorem exists_ker_ne_one {P : Subgroup S3S3} (hP : Nat.card P = 4)
    (g : S3S3 →* Perm (Fin 3)) : ∃ a ∈ P, g a = 1 ∧ a ≠ 1 := by
  let f : P →* Perm (Fin 3) := g.comp P.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hP] at h1
  have h2 : Nat.card f.range ∣ 6 := card_perm_three ▸ Subgroup.card_subgroup_dvd_card f.range
  have h3 : Nat.card f.range ∣ 4 := Dvd.intro_left _ h1
  have h4 : Nat.card f.range ≤ 2 := by
    have := Nat.dvd_gcd h2 h3
    exact Nat.le_of_dvd (by norm_num) (by simpa using this)
  have h5 : 0 < Nat.card f.range := Nat.card_pos
  have h6 : f.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h1
    omega
  obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h6
  refine ⟨(k : P), (k : P).2, ?_, fun h => hk (Subtype.ext (Subtype.ext h))⟩
  exact MonoidHom.mem_ker.1 k.2

theorem pow_four_eq_one {P : Subgroup S3S3} (hP : Nat.card P = 4) {a : S3S3} (ha : a ∈ P) :
    a ^ 4 = 1 := by
  have h := pow_card_eq_one' (G := P) (x := ⟨a, ha⟩)
  rw [hP] at h
  simpa using congrArg Subtype.val h

theorem mem_cycle {P B : Subgroup S3S3} (hP : Nat.card P = 4) (hPB : P ≤ B)
    (hB : Nat.card B = 12) : ((c3, 1) : S3S3) ∈ B ∨ ((1, c3) : S3S3) ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hB]; norm_num)
  have hx3 : (x : S3S3) ^ 3 = 1 := by
    have h3 := pow_orderOf_eq_one x
    rw [hx] at h3
    simpa using congrArg Subtype.val h3
  have hx1 : (x : S3S3) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  have hxB : (x : S3S3) ∈ B := x.2
  by_cases h1 : (x : S3S3).1 = 1
  · have h2 : (x : S3S3).2 ≠ 1 := fun h2 => hx1 (Prod.ext h1 h2)
    obtain ⟨b, hbP, hb1, hb0⟩ := exists_ker_ne_one hP (MonoidHom.fst _ _)
    have hbB : b ∈ B := hPB hbP
    have hmem : b * (x : S3S3) * b⁻¹ * (x : S3S3)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem hbB hxB) (B.inv_mem hbB)) (B.inv_mem hxB)
    right
    rcases comm_snd b x (pow_four_eq_one hP hbP) hb1 hb0 hx3 h2 with h | h
    · rwa [h] at hmem
    · rw [h] at hmem
      simpa using B.inv_mem hmem
  · obtain ⟨a, haP, ha1, ha0⟩ := exists_ker_ne_one hP (MonoidHom.snd _ _)
    have haB : a ∈ B := hPB haP
    have hmem : a * (x : S3S3) * a⁻¹ * (x : S3S3)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem haB hxB) (B.inv_mem haB)) (B.inv_mem hxB)
    left
    rcases comm_fst a x (pow_four_eq_one hP haP) ha1 ha0 hx3 h1 with h | h
    · rwa [h] at hmem
    · rw [h] at hmem
      simpa using B.inv_mem hmem

theorem eq_of_mem {P B B' : Subgroup S3S3} (hP : Nat.card P = 4) (hPB : P ≤ B) (hPB' : P ≤ B')
    (hB : Nat.card B = 12) (hB' : Nat.card B' = 12) {c : S3S3} (hc : orderOf c = 3) (h : c ∈ B)
    (h' : c ∈ B') : B = B' := by
  have key : ∀ {D : Subgroup S3S3}, P ≤ D → Nat.card D = 12 → c ∈ D →
      D = P ⊔ Subgroup.zpowers c := by
    intro D hPD hD hcD
    have hle : P ⊔ Subgroup.zpowers c ≤ D := sup_le hPD ((Subgroup.zpowers_le).2 hcD)
    have h4 : 4 ∣ Nat.card ↥(P ⊔ Subgroup.zpowers c) :=
      hP ▸ Subgroup.card_dvd_of_le (le_sup_left : P ≤ P ⊔ Subgroup.zpowers c)
    have h3 : 3 ∣ Nat.card ↥(P ⊔ Subgroup.zpowers c) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers c ≤ P ⊔ Subgroup.zpowers c)
      rwa [Nat.card_zpowers, hc] at this
    have hpos : 0 < Nat.card ↥(P ⊔ Subgroup.zpowers c) := Nat.card_pos
    have hle12 : Nat.card ↥(P ⊔ Subgroup.zpowers c) ≤ 12 := hD ▸ Subgroup.card_le_of_le hle
    have h12 : Nat.card ↥(P ⊔ Subgroup.zpowers c) = 12 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  rw [key hPB hB h, key hPB' hB' h']

theorem not_three {P B₁ B₂ B₃ : Subgroup S3S3} (hP : Nat.card P = 4) (h₁ : P ≤ B₁) (h₂ : P ≤ B₂)
    (h₃ : P ≤ B₃) (c₁ : Nat.card B₁ = 12) (c₂ : Nat.card B₂ = 12) (c₃ : Nat.card B₃ = 12)
    (n₁₂ : B₁ ≠ B₂) (n₁₃ : B₁ ≠ B₃) (n₂₃ : B₂ ≠ B₃) : False := by
  rcases mem_cycle hP h₁ c₁ with m₁ | m₁ <;> rcases mem_cycle hP h₂ c₂ with m₂ | m₂ <;>
    rcases mem_cycle hP h₃ c₃ with m₃ | m₃ <;>
    first
    | exact n₁₂ (eq_of_mem hP h₁ h₂ c₁ c₂ orderOf_c3_one m₁ m₂)
    | exact n₁₂ (eq_of_mem hP h₁ h₂ c₁ c₂ orderOf_one_c3 m₁ m₂)
    | exact n₁₃ (eq_of_mem hP h₁ h₃ c₁ c₃ orderOf_c3_one m₁ m₃)
    | exact n₁₃ (eq_of_mem hP h₁ h₃ c₁ c₃ orderOf_one_c3 m₁ m₃)
    | exact n₂₃ (eq_of_mem hP h₂ h₃ c₂ c₃ orderOf_c3_one m₂ m₃)
    | exact n₂₃ (eq_of_mem hP h₂ h₃ c₂ c₃ orderOf_one_c3 m₂ m₃)

theorem false_of_index_three {Z : Type} [Group Z] [Finite Z] (φ : Z →* S3S3)
    (hφ : Function.Surjective φ) (hZ : Nat.card Z = 1152) {S A₁ A₂ A₃ : Subgroup Z}
    (hS : Nat.card S = 128) (h₁ : S ≤ A₁) (h₂ : S ≤ A₂) (h₃ : S ≤ A₃) (c₁ : Nat.card A₁ = 384)
    (c₂ : Nat.card A₂ = 384) (c₃ : Nat.card A₃ = 384) (n₁₂ : A₁ ≠ A₂) (n₁₃ : A₁ ≠ A₃)
    (n₂₃ : A₂ ≠ A₃) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : Nat.card φ.ker = 32 := by
    have := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.2 hφ, Subgroup.card_top, card_s3s3, hZ] at this
    omega
  have hKp : IsPGroup 2 φ.ker := IsPGroup.of_card (n := 5) (by rw [hker]; norm_num)
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [hS]; norm_num)
  have hSidx : S.index = 9 := by
    have := Subgroup.card_mul_index S
    rw [hS, hZ] at this
    omega
  have hKS : φ.ker ≤ S :=
    hKp.le_sylow_of_normal (hSp.toSylow (by rw [hSidx]; norm_num))
  have hcard : ∀ {A : Subgroup Z}, φ.ker ≤ A → Nat.card (A.map φ) * A.index = 36 := by
    intro A hA
    have h1 := Subgroup.index_map_eq (H := A) hφ hA
    have h2 := Subgroup.card_mul_index (A.map φ)
    rwa [h1, card_s3s3] at h2
  have hidx : ∀ {A : Subgroup Z}, Nat.card A = 384 → A.index = 3 := by
    intro A hA
    have := Subgroup.card_mul_index A
    rw [hA, hZ] at this
    omega
  have hinj : ∀ {A A' : Subgroup Z}, φ.ker ≤ A → φ.ker ≤ A' → A.map φ = A'.map φ → A = A' := by
    intro A A' hA hA' h
    have := congrArg (Subgroup.comap φ) h
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_eq_left.2 hA, sup_eq_left.2 hA'] at this
  have hP : Nat.card (S.map φ) = 4 := by
    have := hcard hKS
    rw [hSidx] at this
    omega
  have hB : ∀ {A : Subgroup Z}, φ.ker ≤ A → Nat.card A = 384 → Nat.card (A.map φ) = 12 := by
    intro A hA hc
    have := hcard hA
    rw [hidx hc] at this
    omega
  exact not_three hP (Subgroup.map_mono h₁) (Subgroup.map_mono h₂) (Subgroup.map_mono h₃)
    (hB (hKS.trans h₁) c₁) (hB (hKS.trans h₂) c₂) (hB (hKS.trans h₃) c₃)
    (fun h => n₁₂ (hinj (hKS.trans h₁) (hKS.trans h₂) h))
    (fun h => n₁₃ (hinj (hKS.trans h₁) (hKS.trans h₃) h))
    (fun h => n₂₃ (hinj (hKS.trans h₂) (hKS.trans h₃) h))

theorem false_of_index_three_of_le {G : Type} [Group G] [Finite G] {Z : Subgroup G}
    (φ : ↥Z →* S3S3) (hφ : Function.Surjective φ) (hZ : Nat.card ↥Z = 1152)
    {S A₁ A₂ A₃ : Subgroup G} (hS : Nat.card ↥S = 128) (hSZ : S ≤ Z) (h₁ : S ≤ A₁) (h₂ : S ≤ A₂)
    (h₃ : S ≤ A₃) (z₁ : A₁ ≤ Z) (z₂ : A₂ ≤ Z) (z₃ : A₃ ≤ Z) (c₁ : Nat.card ↥A₁ = 384)
    (c₂ : Nat.card ↥A₂ = 384) (c₃ : Nat.card ↥A₃ = 384) (n₁₂ : A₁ ≠ A₂) (n₁₃ : A₁ ≠ A₃)
    (n₂₃ : A₂ ≠ A₃) : False := by
  have hcard : ∀ {A : Subgroup G}, A ≤ Z → Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    fun hA => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → A.subgroupOf Z ≤ B.subgroupOf Z :=
    fun h x hx => h hx
  have hne : ∀ {A B : Subgroup G}, A ≤ Z → B ≤ Z → A ≠ B → A.subgroupOf Z ≠ B.subgroupOf Z := by
    intro A B hA hB hAB h
    apply hAB
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hA, inf_eq_left.2 hB] at this
  exact false_of_index_three φ hφ hZ (S := S.subgroupOf Z) (A₁ := A₁.subgroupOf Z)
    (A₂ := A₂.subgroupOf Z) (A₃ := A₃.subgroupOf Z) ((hcard hSZ).trans hS) (hmono h₁) (hmono h₂)
    (hmono h₃) ((hcard z₁).trans c₁) ((hcard z₂).trans c₂) ((hcard z₃).trans c₃)
    (hne z₁ z₂ n₁₂) (hne z₁ z₃ n₁₃) (hne z₂ z₃ n₂₃)

end CFSG.Quasithin.ModH.M23a
