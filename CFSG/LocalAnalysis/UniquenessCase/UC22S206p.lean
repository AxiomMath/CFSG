module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptCore ptHom ptHom_surjective ker_ptHom)

variable {G : Type} [Group G]

@[expose] def uc22s206pPermA : Equiv.Perm (Fin 8) where
  toFun := ![1, 2, 0, 3, 4, 5, 6, 7]
  invFun := ![2, 0, 1, 3, 4, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206pPermB : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 4, 5, 3, 6, 7]
  invFun := ![0, 1, 2, 5, 3, 4, 6, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206pPermH1 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 1, 3, 4, 5, 7, 6]
  invFun := ![0, 2, 1, 3, 4, 5, 7, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206pPermH2 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 5, 4, 7, 6]
  invFun := ![0, 1, 2, 3, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206pA0 : alternatingGroup (Fin 8) :=
  ⟨uc22s206pPermA, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206pB0 : alternatingGroup (Fin 8) :=
  ⟨uc22s206pPermB, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206pH1 : alternatingGroup (Fin 8) :=
  ⟨uc22s206pPermH1, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206pH2 : alternatingGroup (Fin 8) :=
  ⟨uc22s206pPermH2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem uc22s206p_rel :
    uc22s206pA0 * uc22s206pB0 = uc22s206pB0 * uc22s206pA0 ∧ uc22s206pA0 ^ 3 = 1 ∧
      uc22s206pB0 ^ 3 = 1 ∧ uc22s206pA0 ≠ 1 ∧ uc22s206pB0 ≠ 1 ∧
      uc22s206pH1 * uc22s206pA0 * uc22s206pH1⁻¹ = uc22s206pA0⁻¹ ∧
      uc22s206pH1 * uc22s206pB0 * uc22s206pH1⁻¹ = uc22s206pB0 ∧
      uc22s206pH2 * uc22s206pA0 * uc22s206pH2⁻¹ = uc22s206pA0 ∧
      uc22s206pH2 * uc22s206pB0 * uc22s206pH2⁻¹ = uc22s206pB0⁻¹ := by
  decide

theorem uc22s206p_disjoint {Y : Type*} [Group Y] {x y h : Y} (hx : h * x * h⁻¹ = x)
    (hy : h * y * h⁻¹ = y⁻¹) (hy3 : y ^ 3 = 1) : Disjoint (zpowers x) (zpowers y) := by
  rw [Subgroup.disjoint_def]
  intro w hwx hwy
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hwx
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hwy
  have h1 : x ^ m = (x ^ m)⁻¹ := by
    calc x ^ m = h * x ^ m * h⁻¹ := by rw [← conj_zpow, hx]
      _ = (x ^ m)⁻¹ := by rw [← hn, ← conj_zpow, hy, inv_zpow]
  have h3 : (x ^ m) ^ 3 = 1 := by
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have h2 : x ^ m * x ^ m = 1 := mul_eq_one_iff_eq_inv.mpr h1
  calc x ^ m = x ^ m * x ^ m * x ^ m := by rw [h2, one_mul]
    _ = 1 := by rw [← pow_three', h3]

theorem uc22s206p_elemAbelian_sup {Y : Type*} [Group Y] {p : ℕ} {A B : Subgroup Y}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : Disjoint A B) {k l : ℕ} (hk : Nat.card A = p ^ k) (hl : Nat.card B = p ^ l) :
    IsElemAbelian p (A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = p ^ (k + l) := by
  refine ⟨hA.sup_of_commute hB hAB, ?_⟩
  have hN : B ≤ normalizer (A : Set Y) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rwa [← hAB a ha b hb, mul_inv_cancel_right]
    · intro ha
      have hc := hAB _ ha b hb
      have he : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [hc]
          _ = b * a * b⁻¹ := by group
      rw [he]
      exact ha
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B hN hd, hk, hl,
    pow_add]

theorem uc22s206p_E9 :
    IsElemAbelian 3 (zpowers uc22s206pA0 ⊔ zpowers uc22s206pB0) ∧
      Nat.card ↥(zpowers uc22s206pA0 ⊔ zpowers uc22s206pB0) = 3 ^ (1 + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hab, ha3, hb3, ha1, hb1, -, -, h2a, h2b⟩ := uc22s206p_rel
  refine uc22s206p_elemAbelian_sup (isElemAbelian_zpowers ha3) (isElemAbelian_zpowers hb3)
    (fun x hx y hy => ?_) (uc22s206p_disjoint h2a h2b hb3) ?_ ?_
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hab m n
  · rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1, pow_one]
  · rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one]

theorem uc22s206p_conj_mem {Y : Type*} [Group Y] {x y h : Y}
    (hx : h * x * h⁻¹ ∈ zpowers x ⊔ zpowers y) (hy : h * y * h⁻¹ ∈ zpowers x ⊔ zpowers y)
    {w : Y} (hw : w ∈ zpowers x ⊔ zpowers y) : h * w * h⁻¹ ∈ zpowers x ⊔ zpowers y := by
  have hle : zpowers x ⊔ zpowers y ≤
      (zpowers x ⊔ zpowers y).comap (MulAut.conj h).toMonoidHom :=
    sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)
  exact hle hw

theorem uc22s206p_frattini {X Q : Type*} [Group X] [Finite X] [Group Q] (β : X →* Q)
    (hβ : Function.Surjective β) (hβ2 : IsPGroup 2 β.ker) {E : Subgroup X}
    (hE : IsPGroup 3 E) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEi : ∀ x ∈ E, ∀ y ∈ E, β x = β y → x = y) {σ : Q}
    (hσ : ∀ e ∈ E, ∃ e' ∈ E, β e' = σ * β e * σ⁻¹) :
    ∃ h : X, ∀ e ∈ E, ∀ e' ∈ E, β e' = σ * β e * σ⁻¹ → h * e * h⁻¹ = e' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, rfl⟩ := hβ σ
  have hEH : CFSG.ABGLocalTools.IsSylowOf 3 E (E ⊔ β.ker) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_left, hE, fun h3 => ?_⟩
    rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal] at h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hβ2
    have h32 := h3.trans (relIndex_dvd_card E β.ker)
    rw [hn] at h32
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
  have hgE : E.map (MulAut.conj g).toMonoidHom ≤ E ⊔ β.ker := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨e', he', hβe⟩ := hσ e he
    have hk : e'⁻¹ * (g * e * g⁻¹) ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβe, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hmem := mul_mem_sup he' hk
    rwa [mul_inv_cancel_left] at hmem
  have hE' : CFSG.ABGLocalTools.IsSylowOf 3 (E.map (MulAut.conj g).toMonoidHom) (E ⊔ β.ker) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hgE
      (by rw [card_map_of_injective (MulAut.conj g).injective, hEH.card_eq])
  obtain ⟨k, hk, hkE⟩ := hEH.exists_mem_conj hE'
  obtain ⟨e₀, he₀, hβk⟩ : ∃ e₀ ∈ E, β e₀ = β k := by
    have hle : E ⊔ β.ker ≤ (E.map β).comap β :=
      sup_le (le_comap_map β E) fun x hx => by
        rw [mem_comap, MonoidHom.mem_ker.mp hx]
        exact one_mem _
    exact hle hk
  refine ⟨k⁻¹ * g, fun e he e' he' hβe => ?_⟩
  have h1 : k⁻¹ * (g * e * g⁻¹) * k ∈ E := (hkE _).mp ⟨e, he, rfl⟩
  have heq : k⁻¹ * g * e * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * e * g⁻¹) * k := by group
  rw [heq]
  refine hEi _ h1 _ he' ?_
  have hc : β e' * β e₀ = β e₀ * β e' := by rw [← map_mul, ← map_mul, hEc e₀ he₀ e' he']
  simp only [map_mul, map_inv]
  rw [← hβk, ← hβe, mul_assoc, hc, inv_mul_cancel_left]

theorem uc22s206p_elements [Finite G] {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) (i : Fin 9) :
    ∃ a b h₁ h₂ : ↥(ptCore α i), a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      h₁ * a * h₁⁻¹ = a⁻¹ ∧ h₁ * b * h₁⁻¹ = b ∧ h₂ * a * h₂⁻¹ = a ∧ h₂ * b * h₂⁻¹ = b⁻¹ ∧
      ptHom α i a ≠ 1 ∧ ptHom α i b ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, ha3, hb3, ha1, hb1, h1a, h1b, h2a, h2b⟩ := uc22s206p_rel
  obtain ⟨hE₀, hE₀card⟩ := uc22s206p_E9
  set e := uc22s206gEmb i with he
  have hinj : Function.Injective e := uc22s206gEmb_injective i
  set β := ptHom α i with hβdef
  have hβ : Function.Surjective β := ptHom_surjective α hα (by norm_num) i
  have hβ2 : IsPGroup 2 β.ker := by
    rw [hβdef, ker_ptHom α hα hker (by norm_num) i]
    exact CFSG.pCore_isPGroup
  set E₀ := zpowers uc22s206pA0 ⊔ zpowers uc22s206pB0 with hE₀def
  obtain ⟨s, hs⟩ := uc22s206d_section β hβ hβ2 (E₀.map e) (by
    rw [card_map_of_injective hinj, hE₀card]
    exact ⟨4, rfl⟩)
  have hq3 : ∀ q : ↥(E₀.map e), q ^ 3 = 1 := by
    rintro ⟨_, y, hy, rfl⟩
    refine Subtype.ext ?_
    show e y ^ 3 = 1
    rw [← map_pow, hE₀.2 y hy, map_one]
  have hqc : ∀ q q' : ↥(E₀.map e), q * q' = q' * q := by
    rintro ⟨_, y, hy, rfl⟩ ⟨_, y', hy', rfl⟩
    refine Subtype.ext ?_
    show e y * e y' = e y' * e y
    rw [← map_mul, ← map_mul, hE₀.comm hy hy']
  have hs3 : ∀ q, s q ^ 3 = 1 := fun q => by rw [← map_pow, hq3, map_one]
  have hEp : IsPGroup 3 s.range := by
    rintro ⟨_, q, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show s q ^ 3 ^ 1 = 1
    rw [pow_one]
    exact hs3 q
  have hEc : ∀ x ∈ s.range, ∀ y ∈ s.range, x * y = y * x := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
    rw [← map_mul, ← map_mul, hqc]
  have hEi : ∀ x ∈ s.range, ∀ y ∈ s.range, β x = β y → x = y := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ h
    rw [hs, hs] at h
    rw [Subtype.ext h]
  have hσ : ∀ h : alternatingGroup (Fin 8), h * uc22s206pA0 * h⁻¹ ∈ E₀ →
      h * uc22s206pB0 * h⁻¹ ∈ E₀ → ∀ x ∈ s.range, ∃ x' ∈ s.range,
        β x' = e h * β x * (e h)⁻¹ := by
    intro h hA hB
    rintro _ ⟨q, rfl⟩
    obtain ⟨y, hy, hyq⟩ := q.2
    have hmem : e h * ↑q * (e h)⁻¹ ∈ E₀.map e := by
      rw [← hyq, ← map_inv, ← map_mul, ← map_mul]
      exact mem_map_of_mem e (uc22s206p_conj_mem hA hB hy)
    exact ⟨s ⟨_, hmem⟩, ⟨_, rfl⟩, by rw [hs, hs]⟩
  obtain ⟨g₁, hg₁⟩ := uc22s206p_frattini β hβ hβ2 hEp hEc hEi (hσ uc22s206pH1
    (by rw [h1a]; exact inv_mem (mem_sup_left (mem_zpowers _)))
    (by rw [h1b]; exact mem_sup_right (mem_zpowers _)))
  obtain ⟨g₂, hg₂⟩ := uc22s206p_frattini β hβ hβ2 hEp hEc hEi (hσ uc22s206pH2
    (by rw [h2a]; exact mem_sup_left (mem_zpowers _))
    (by rw [h2b]; exact inv_mem (mem_sup_right (mem_zpowers _))))
  let qa : ↥(E₀.map e) := ⟨e uc22s206pA0, mem_map_of_mem e (mem_sup_left (mem_zpowers _))⟩
  let qb : ↥(E₀.map e) := ⟨e uc22s206pB0, mem_map_of_mem e (mem_sup_right (mem_zpowers _))⟩
  have hconj : ∀ {h x : alternatingGroup (Fin 8)} {y : alternatingGroup (Fin 8)},
      h * x * h⁻¹ = y → e h * e x * (e h)⁻¹ = e y := fun hxy => by
    rw [← map_inv, ← map_mul, ← map_mul, hxy]
  refine ⟨s qa, s qb, g₁, g₂, by rw [← map_mul, ← map_mul, hqc], hs3 qa, hs3 qb,
    hg₁ _ ⟨qa, rfl⟩ _ (inv_mem ⟨qa, rfl⟩) ?_, hg₁ _ ⟨qb, rfl⟩ _ ⟨qb, rfl⟩ ?_,
    hg₂ _ ⟨qa, rfl⟩ _ ⟨qa, rfl⟩ ?_, hg₂ _ ⟨qb, rfl⟩ _ (inv_mem ⟨qb, rfl⟩) ?_, ?_, ?_⟩
  · rw [map_inv, hs]
    exact ((hconj h1a).trans (map_inv e _)).symm
  · rw [hs]
    exact (hconj h1b).symm
  · rw [hs]
    exact (hconj h2a).symm
  · rw [map_inv, hs]
    exact ((hconj h2b).trans (map_inv e _)).symm
  · rw [hs]
    exact fun h => ha1 (hinj (h.trans (map_one e).symm))
  · rw [hs]
    exact fun h => hb1 (hinj (h.trans (map_one e).symm))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
