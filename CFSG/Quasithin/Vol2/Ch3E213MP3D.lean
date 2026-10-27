module

public import CFSG.Quasithin.Vol2.Ch3E213MTr
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch3E213MP3B

public section

namespace CFSG.Quasithin.Ch3E213M.P3

open Subgroup CFSG.QuasithinUnique B6

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem conj_mem_inSubgroup_pCore {B : Subgroup Y} {w c : Y} (hw : w ∈ B)
    (hc : c ∈ inSubgroup (CFSG.pCore 2) B) : w * c * w⁻¹ ∈ inSubgroup (CFSG.pCore 2) B := by
  obtain ⟨m, hm, rfl⟩ := hc
  exact ⟨⟨w, hw⟩ * m * ⟨w, hw⟩⁻¹, CFSG.pCore_normal.conj_mem m hm _, rfl⟩

omit [Finite Y] in
theorem pow_eq_one_of_isPGroup {P : Subgroup Y} (hP : IsPGroup 2 P) {y : Y} {n k : ℕ}
    (hn : orderOf y = n) (hodd : Odd n) (hk : y ^ k ∈ P) : y ^ k = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨_, hk⟩
  have h1 : (y ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h2 : orderOf (y ^ k) ∣ n := hn ▸ orderOf_dvd_of_mem_zpowers (pow_mem (mem_zpowers y) k)
  have hcop : Nat.Coprime (2 ^ j) n := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) h2)

omit [Finite Y] in
theorem pow_eq_one_of_pow_two_mul {y : Y} {n k : ℕ} (hn : orderOf y = n) (hodd : Odd n)
    (hk : y ^ (k + k) = 1) : y ^ k = 1 := by
  have h1 : n ∣ 2 * k := hn ▸ orderOf_dvd_of_pow_eq_one (by rwa [two_mul])
  have h2 : n ∣ k := Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hodd)) h1
  exact orderOf_dvd_iff_pow_eq_one.1 (hn ▸ h2)

omit [Finite Y] in
theorem isElementaryAbelian_of {A : Subgroup Y} (hc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x)
    (h2 : ∀ x ∈ A, x * x = 1) : CFSG.IsElementaryAbelian 2 A :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hc h2

theorem dihedral_data {K₁ S B E : Subgroup Y} {a y : Y} {ℓ b : ℕ}
    (hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x) (hE2 : ∀ e ∈ E, e * e = 1) (haE : a ∈ E)
    (haC : a ∉ centralizer (K₁ : Set Y))
    (hEa : E = zpowers a ⊔ (E ⊓ centralizer (K₁ : Set Y))) (hyK : y ∈ K₁) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hb : 1 ≤ b) (hy : orderOf y = ℓ ^ b) (hay : a * y * a = y⁻¹) (hES : E ≤ S)
    (hS2 : IsPGroup 2 S) (hEB : E ≤ inSubgroup (CFSG.pCore 2) B) :
    let F := closure ({a, y} : Set Y)
    let A := E ⊓ centralizer (K₁ : Set Y)
    let x := y ^ ((ℓ ^ b - 1) / 2)
    (∀ f ∈ F, ∀ c ∈ A, f * c = c * f) ∧ F ⊓ A = ⊥ ∧ x ∈ F ⊔ A ∧
      F ⊔ A = E ⊔ CFSG.conjugate E x ∧ Nonempty (F ≃* DihedralGroup (ℓ ^ b)) ∧
      Nat.card ((E ⊔ A) ⊓ F : Subgroup Y) = 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (zpowers a) F ∧ zpowers a ≤ F ∧
      kerIn (zpowers a) F = ⊥ ∧ inSubgroup (CFSG.pCore 2) F = ⊥ ∧
      inSubgroup (CFSG.pCore 2) (zpowers a) = zpowers a ∧
      S ⊓ (F ⊔ A) = zpowers a ⊔ A ∧ B ⊓ (F ⊔ A) = zpowers a ⊔ A := by
  intro F A x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := ℓ ^ b with hn
  have hodd : Odd n := (hℓ.odd_of_ne_two hℓ2).pow
  have hn3 : 3 ≤ n := by
    have h1 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 3 ≤ ℓ := h1
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ b := Nat.pow_le_pow_right hℓ.pos hb
  have : NeZero n := ⟨by omega⟩
  have ha2 := hE2 a haE
  have ha1 : a ≠ 1 := fun h => haC (h ▸ one_mem _)
  have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
  obtain ⟨⟨eD⟩, hcardD, helemD, -, hO2D, hcentD⟩ :=
    SteinbergBS.dihedral_closure_facts ha2 ha1 hay hy hodd hn3
  have haF : a ∈ F := subset_closure (by simp)
  have hyF : y ∈ F := subset_closure (by simp)
  have hAE : A ≤ E := inf_le_left
  have hFA : ∀ f ∈ F, ∀ c ∈ A, f * c = c * f := by
    have hle : F ≤ centralizer (A : Set Y) := by
      rw [closure_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz]
        exact mem_centralizer_iff.mpr fun c hc => hEc c (hAE hc) a haE
      · rw [Set.mem_singleton_iff.mp hz]
        exact mem_centralizer_iff.mpr fun c hc => (mem_centralizer_iff.mp hc.2 y hyK).symm
    exact fun f hf c hc => (mem_centralizer_iff.mp (hle hf) c hc).symm
  have hFAb : F ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzF, hzA⟩
    rcases hcentD z hzF (hEc z (hAE hzA) a haE) with h | h
    · exact mem_bot.mpr h
    · exact absurd (h ▸ hzA.2) haC
  set m := (n - 1) / 2 with hm
  have h2m : m + m = n - 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hyn : y ^ n = 1 := hy ▸ pow_orderOf_eq_one y
  have haxa : a * y ^ m * a = (y ^ m)⁻¹ := by
    have h1 : a * y ^ m * a⁻¹ = (a * y * a⁻¹) ^ m := (conj_pow).symm
    rw [hainv, hay, inv_pow] at h1
    exact h1
  have hconj : (y ^ m)⁻¹ * a * y ^ m = y * a := by
    have h1 : (y ^ m)⁻¹ * a * y ^ m = (y ^ m)⁻¹ * (a * y ^ m * a) * a := by
      calc (y ^ m)⁻¹ * a * y ^ m = (y ^ m)⁻¹ * a * y ^ m * (a * a) := by rw [ha2, mul_one]
        _ = (y ^ m)⁻¹ * (a * y ^ m * a) * a := by group
    have h2 : (y ^ m)⁻¹ * (y ^ m)⁻¹ = y := by
      rw [← mul_inv_rev, ← pow_add, h2m]
      refine inv_eq_of_mul_eq_one_left ?_
      rw [← pow_succ', Nat.sub_add_cancel (by omega), hyn]
    rw [h1, haxa, h2]
  have hxm : x = y ^ m := rfl
  have hxF : x ∈ F := pow_mem hyF m
  have hEFA : E ≤ F ⊔ A := hEa.le.trans (sup_le_sup_right (zpowers_le.mpr haF) A)
  have hL : F ⊔ A = E ⊔ CFSG.conjugate E x := by
    refine le_antisymm (sup_le ?_ (hAE.trans le_sup_left)) (sup_le hEFA ?_)
    · rw [closure_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz]
        exact mem_sup_left haE
      · rw [Set.mem_singleton_iff.mp hz]
        have h1 : y * a ∈ CFSG.conjugate E x := by
          rw [← hconj]
          refine mem_conjugate.mpr ?_
          have e : x * ((y ^ m)⁻¹ * a * y ^ m) * x⁻¹ = a := by rw [hxm]; group
          rw [e]
          exact haE
        have h2 : y = y * a * a := by rw [mul_assoc, ha2, mul_one]
        rw [h2]
        exact mul_mem (mem_sup_right h1) (mem_sup_left haE)
    · intro z hz
      have hz' : x * z * x⁻¹ ∈ E := mem_conjugate.mp hz
      have e : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [e]
      have hxL : x ∈ F ⊔ A := mem_sup_left hxF
      exact mul_mem (mul_mem (inv_mem hxL) (hEFA hz')) hxL
  have hzaF : zpowers a ≤ F := zpowers_le.mpr haF
  have hEF : E ⊓ F = zpowers a := by
    refine le_antisymm (fun z hz => ?_) (le_inf (zpowers_le.mpr haE) hzaF)
    rcases hcentD z hz.2 (hEc z hz.1 a haE) with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers a
  have hza2 : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hcardEAF : Nat.card ((E ⊔ A) ⊓ F : Subgroup Y) = 2 := by
    rw [sup_eq_left.mpr hAE, hEF, hza2]
  have hza2g : IsPGroup 2 (zpowers a) := fun z => ⟨1, Subtype.ext (by
    rcases eq_one_or_eq_of_mem_zpowers ha2 z.2 with h | h <;> simp [h, ha2, pow_two])⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers a) F := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hzaF, hza2g, ?_⟩
    have h1 := relIndex_mul_card (zpowers a) F
    rw [inf_eq_left.mpr hzaF, hza2, hcardD] at h1
    have h2 : (zpowers a).relIndex F = n := by omega
    rw [h2]
    have := Nat.odd_iff.mp hodd
    omega
  have hcore : kerIn (zpowers a) F = ⊥ :=
    hO2D _ (kerIn_le.trans hzaF) (le_normalizer_kerIn _ _) (hza2g.to_le kerIn_le)
  have hO2F : inSubgroup (CFSG.pCore 2) F = ⊥ := by
    refine hO2D _ (map_subtype_le _) ?_ (CFSG.pCore_isPGroup.map F.subtype)
    calc F = (⊤ : Subgroup F).map F.subtype := by
          rw [← MonoidHom.range_eq_map, range_subtype]
      _ = (normalizer (CFSG.pCore 2 F : Set F)).map F.subtype := by
          rw [normalizer_eq_top_iff.mpr CFSG.pCore_normal]
      _ ≤ _ := le_normalizer_map _
  have hO2a : inSubgroup (CFSG.pCore 2) (zpowers a) = zpowers a := by
    have htop : CFSG.pCore 2 (zpowers a) = ⊤ :=
      top_le_iff.mp (le_sSup ⟨inferInstance, hza2g.to_subgroup ⊤⟩)
    rw [inSubgroup, htop, ← MonoidHom.range_eq_map, range_subtype]
  have hsupinf : ∀ X : Subgroup Y, A ≤ X → X ⊓ (F ⊔ A) = (X ⊓ F) ⊔ A := by
    intro X hX
    refine le_antisymm (fun z hz => ?_)
      (sup_le (inf_le_inf_left _ le_sup_left) (le_inf hX le_sup_right))
    obtain ⟨hzX, hzL⟩ := mem_inf.1 hz
    obtain ⟨l, hl, c, hc, rfl⟩ := H13.QRC.exists_mul_of_mem_sup_of_commute hFA hzL
    have hlX : l ∈ X := by
      have := X.mul_mem hzX (X.inv_mem (hX hc))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem_sup ⟨hlX, hl⟩ hc
  have hinfF : ∀ X : Subgroup Y, a ∈ X → (∀ k : ℕ, y ^ k ∈ X → y ^ k = 1) →
      X ⊓ F = zpowers a := by
    intro X haX hX
    refine le_antisymm (fun z hz => ?_) (le_inf (zpowers_le.mpr haX) hzaF)
    obtain ⟨k, hk | hk⟩ := helemD z hz.2
    · rw [hk, hX k (hk ▸ hz.1)]
      exact one_mem _
    · have h1 : y ^ k ∈ X := by
        have := X.mul_mem haX hz.1
        rwa [hk, ← mul_assoc, ha2, one_mul] at this
      rw [hk, hX k h1, mul_one]
      exact mem_zpowers a
  have hSF : S ⊓ F = zpowers a :=
    hinfF S (hES haE) fun k hk => pow_eq_one_of_isPGroup hS2 hy hodd hk
  have hO2B : IsPGroup 2 (inSubgroup (CFSG.pCore 2) B) := CFSG.pCore_isPGroup.map B.subtype
  have hBF : B ⊓ F = zpowers a := by
    refine hinfF B (map_subtype_le _ (hEB haE)) fun k hk => ?_
    have hc : a * y ^ k * a⁻¹ * (y ^ k)⁻¹ ∈ inSubgroup (CFSG.pCore 2) B := by
      have h1 := conj_mem_inSubgroup_pCore hk (inv_mem (hEB haE))
      have e : a * y ^ k * a⁻¹ * (y ^ k)⁻¹ = a * (y ^ k * a⁻¹ * (y ^ k)⁻¹) := by group
      rw [e]
      exact mul_mem (hEB haE) h1
    have hayk : a * y ^ k * a⁻¹ = (y ^ k)⁻¹ := by
      rw [← conj_pow, hainv, hay, inv_pow]
    rw [hayk, ← mul_inv_rev, ← pow_add] at hc
    exact pow_eq_one_of_pow_two_mul hy hodd
      (pow_eq_one_of_isPGroup hO2B hy hodd (by simpa using inv_mem hc))
  refine ⟨hFA, hFAb, mem_sup_left hxF, hL, ⟨eD⟩, hcardEAF, hsyl, hzaF, hcore, hO2F, hO2a, ?_, ?_⟩
  · rw [hsupinf S (hAE.trans hES), hSF]
  · rw [hsupinf B (hAE.trans (hEB.trans (map_subtype_le _))), hBF]

end CFSG.Quasithin.Ch3E213M.P3
