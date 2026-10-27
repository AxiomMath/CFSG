module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Three
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Irr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

variable {Γ : Type*} [Group Γ]

theorem exists_irreducible_pair {S K₁ K₂ : Subgroup Γ} {t z₁ : Γ} (hL₁ : L27 ↥K₁)
    (hL₂ : L27 ↥K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
    (hD₂ : IsSylowTwoOf (S ⊓ K₂) K₂) (htS : t ∈ S) (m1 : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂)
    (m3 : ∀ x ∈ K₁, t⁻¹ * x * t ∈ K₂) (m4 : ∀ x ∈ K₂, t⁻¹ * x * t ∈ K₁)
    (hz₁K : z₁ ∈ K₁) (hz₁S : z₁ ∈ S) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1)
    (hz₁c : ∀ d ∈ S ⊓ K₁, d * z₁ = z₁ * d) (ht₂ : t * (t * z₁ * t⁻¹) * t⁻¹ = z₁) :
    ∃ Ā T₀ : Subgroup Γ, Nat.card Ā = 9 ∧ T₀ ≤ S ∧ T₀ ≤ Subgroup.normalizer (Ā : Set Γ) ∧
      (∀ C : Subgroup Γ, C ≤ Ā → T₀ ≤ Subgroup.normalizer (C : Set Γ) → C = ⊥ ∨ C = Ā) ∧
      z₁ ∈ T₀ ∧ t * z₁ * t⁻¹ ∈ T₀ ∧
      ∀ a ∈ Ā, (z₁ * (t * z₁ * t⁻¹)) * a * (z₁ * (t * z₁ * t⁻¹))⁻¹ * a = 1 := by
  set z₂ := t * z₁ * t⁻¹ with hz₂
  have hz₂K : z₂ ∈ K₂ := m1 z₁ hz₁K
  have hz₂S : z₂ ∈ S := S.mul_mem (S.mul_mem htS hz₁S) (S.inv_mem htS)
  have hz₂2 : z₂ * z₂ = 1 := by
    calc z₂ * z₂ = t * (z₁ * z₁) * t⁻¹ := by rw [hz₂]; group
      _ = 1 := by rw [hz₁2]; group
  have hz₂1 : z₂ ≠ 1 := by
    intro h1
    apply hz₁1
    calc z₁ = t⁻¹ * z₂ * t := by rw [hz₂]; group
      _ = 1 := by rw [h1]; group
  have hz₂t : t⁻¹ * z₁ * t = z₂ := by
    calc t⁻¹ * z₁ * t = t⁻¹ * (t * z₂ * t⁻¹) * t := by rw [ht₂]
      _ = z₂ := by group
  have hz₂c : ∀ d ∈ S ⊓ K₂, d * z₂ = z₂ * d := by
    rintro d ⟨hdS, hdK⟩
    have hd' : t⁻¹ * d * t ∈ S ⊓ K₁ :=
      ⟨S.mul_mem (S.mul_mem (S.inv_mem htS) hdS) htS, m4 d hdK⟩
    have h1 := hz₁c _ hd'
    calc d * z₂ = t * ((t⁻¹ * d * t) * z₁) * t⁻¹ := by rw [hz₂]; group
      _ = t * (z₁ * (t⁻¹ * d * t)) * t⁻¹ := by rw [h1]
      _ = z₂ * d := by rw [hz₂]; group
  obtain ⟨a₁', ha3', ha1', hza'⟩ := hL₁.inv3 ⟨z₁, hz₁K⟩ (Subtype.ext hz₁2)
    (fun h => hz₁1 (congrArg Subtype.val h))
  set a₁ : Γ := (a₁' : Γ) with ha₁
  have ha₁K : a₁ ∈ K₁ := a₁'.2
  have ha₁3 : a₁ ^ 3 = 1 := by simpa using congrArg Subtype.val ha3'
  have ha₁1 : a₁ ≠ 1 := fun h => ha1' (Subtype.ext h)
  have hza₁ : z₁ * a₁ * z₁⁻¹ = a₁⁻¹ := congrArg Subtype.val hza'
  set a₂ : Γ := t * a₁ * t⁻¹ with ha₂
  set a₃ : Γ := t⁻¹ * a₁ * t with ha₃
  have ha₂K : a₂ ∈ K₂ := m1 a₁ ha₁K
  have ha₃K : a₃ ∈ K₂ := m3 a₁ ha₁K
  have hconj3 : ∀ s : Γ, (s * a₁ * s⁻¹) ^ 3 = 1 := fun s => by rw [conj_pow, ha₁3]; group
  have hconj1 : ∀ s : Γ, s * a₁ * s⁻¹ ≠ 1 := fun s h1 => ha₁1 (by
    calc a₁ = s⁻¹ * (s * a₁ * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group)
  have ha₂3 : a₂ ^ 3 = 1 := hconj3 t
  have ha₂1 : a₂ ≠ 1 := hconj1 t
  have ha₃3 : a₃ ^ 3 = 1 := by simpa using hconj3 t⁻¹
  have ha₃1 : a₃ ≠ 1 := by simpa using hconj1 t⁻¹
  have hza₂ : z₂ * a₂ * z₂⁻¹ = a₂⁻¹ := by
    calc z₂ * a₂ * z₂⁻¹ = t * (z₁ * a₁ * z₁⁻¹) * t⁻¹ := by rw [ha₂, hz₂]; group
      _ = a₂⁻¹ := by rw [hza₁, ha₂]; group
  have hza₃ : z₂ * a₃ * z₂⁻¹ = a₃⁻¹ := by
    calc z₂ * a₃ * z₂⁻¹ = t⁻¹ * (z₁ * a₁ * z₁⁻¹) * t := by
          rw [ha₃, ← hz₂t]; group
      _ = a₃⁻¹ := by rw [hza₁, ha₃]; group
  obtain ⟨d, hdD, i, hdi⟩ := transitive_three hL₂ (z := ⟨z₂, hz₂K⟩) (Subtype.ext hz₂2)
    (fun h => hz₂1 (congrArg Subtype.val h)) (D := (S ⊓ K₂).subgroupOf K₂)
    (isSylowTwoOf_subgroupOf_top' hD₂)
    (fun d hd => Subtype.ext (hz₂c d (Subgroup.mem_subgroupOf.1 hd)))
    (a := ⟨a₂, ha₂K⟩) (a' := ⟨a₃, ha₃K⟩) (Subtype.ext (by simpa using ha₂3))
    (fun h => ha₂1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using ha₃3))
    (fun h => ha₃1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hza₂))
    (Subtype.ext (by simpa using hza₃))
  set d₂ : Γ := (d : Γ) with hd₂
  have hd₂SK : d₂ ∈ S ⊓ K₂ := Subgroup.mem_subgroupOf.1 hdD
  have hd₂i : d₂ * a₂ * d₂⁻¹ = a₃ ^ i := by simpa using congrArg Subtype.val hdi
  set t' : Γ := t * d₂ with ht'
  have ht'S : t' ∈ S := S.mul_mem htS hd₂SK.1
  have hd₂c : ∀ x ∈ K₁, d₂ * x = x * d₂ := fun x hx => (hc x hx d₂ hd₂SK.2).symm
  have ht'a₁ : t' * a₁ * t'⁻¹ = a₂ := by
    calc t' * a₁ * t'⁻¹ = t * (d₂ * a₁ * d₂⁻¹) * t⁻¹ := by rw [ht']; group
      _ = a₂ := by rw [hd₂c a₁ ha₁K, ha₂]; group
  have ht'a₂ : t' * a₂ * t'⁻¹ = a₁ ^ i := by
    calc t' * a₂ * t'⁻¹ = t * (d₂ * a₂ * d₂⁻¹) * t⁻¹ := by rw [ht']; group
      _ = t * a₃ ^ i * t⁻¹ := by rw [hd₂i]
      _ = (t * a₃ * t⁻¹) ^ i := by rw [conj_pow]
      _ = a₁ ^ i := by rw [ha₃]; congr 1; group
  have hmap : ∀ (g x : Γ), (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * x * g⁻¹) := fun g x => by
    rw [MonoidHom.map_zpowers]
    rfl
  set P₁ := Subgroup.zpowers a₁ with hP₁
  set P₂ := Subgroup.zpowers a₂ with hP₂
  have hP₁K : P₁ ≤ K₁ := (Subgroup.zpowers_le).2 ha₁K
  have hP₂K : P₂ ≤ K₂ := (Subgroup.zpowers_le).2 ha₂K
  have hai1 : a₁ ^ i ≠ 1 := by
    rw [← ht'a₂]
    intro h1
    apply ha₂1
    calc a₂ = t'⁻¹ * (t' * a₂ * t'⁻¹) * t' := by group
      _ = 1 := by rw [h1]; group
  have hP₁t' : P₁.map (MulAut.conj t').toMonoidHom = P₂ := by
    rw [hP₁, hmap, ht'a₁]
  have hP₂t' : P₂.map (MulAut.conj t').toMonoidHom = P₁ := by
    rw [hP₂, hmap, ht'a₂]
    exact zpowers_eq_of_mem ha₁3 ha₁1 (by rw [← pow_mul, mul_comm, pow_mul, ha₁3, one_pow]) hai1
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers a₁) i)
  set Ā := P₁ ⊔ P₂ with hĀ
  have hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := fun x hx y hy => hc x (hP₁K hx) y (hP₂K hy)
  have hzpow : ∀ (z a : Γ), z * a * z⁻¹ = a⁻¹ → ∀ x ∈ Subgroup.zpowers a, z * x * z⁻¹ = x⁻¹ := by
    intro z a hza x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h := map_zpow (MulAut.conj z).toMonoidHom a k
    calc z * a ^ k * z⁻¹ = (z * a * z⁻¹) ^ k := h
      _ = (a ^ k)⁻¹ := by rw [hza, inv_zpow]
  have hz₁x : ∀ x ∈ P₁, z₁ * x * z₁⁻¹ = x⁻¹ := hzpow z₁ a₁ hza₁
  have hz₂y : ∀ y ∈ P₂, z₂ * y * z₂⁻¹ = y⁻¹ := hzpow z₂ a₂ hza₂
  have hz₁y : ∀ y ∈ P₂, z₁ * y * z₁⁻¹ = y := fun y hy => by
    rw [hc z₁ hz₁K y (hP₂K hy)]
    group
  have hz₂x : ∀ x ∈ P₁, z₂ * x * z₂⁻¹ = x := fun x hx => by
    rw [← hc x (hP₁K hx) z₂ hz₂K]
    group
  have hz₁N : z₁ ∈ Subgroup.normalizer (Ā : Set Γ) := by
    refine mem_normalizer_of_map_eq ?_
    rw [hĀ, Subgroup.map_sup, hP₁, hP₂, hmap, hmap, hza₁, Subgroup.zpowers_inv,
      hz₁y a₂ (Subgroup.mem_zpowers a₂)]
  have hz₂N : z₂ ∈ Subgroup.normalizer (Ā : Set Γ) := by
    refine mem_normalizer_of_map_eq ?_
    rw [hĀ, Subgroup.map_sup, hP₁, hP₂, hmap, hmap, hza₂, Subgroup.zpowers_inv,
      hz₂x a₁ (Subgroup.mem_zpowers a₁)]
  have ht'N : t' ∈ Subgroup.normalizer (Ā : Set Γ) := by
    refine mem_normalizer_of_map_eq ?_
    rw [hĀ, Subgroup.map_sup, hP₁t', hP₂t', sup_comm]
  set T₀ : Subgroup Γ := Subgroup.closure ({z₁, z₂, t'} : Set Γ) with hT₀
  have hT₀S : T₀ ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hz₁S, hz₂S, ht'S]
  have hT₀N : T₀ ≤ Subgroup.normalizer (Ā : Set Γ) := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hz₁N, hz₂N, ht'N]
  have hz₁T₀ : z₁ ∈ T₀ := Subgroup.subset_closure (by simp)
  have hz₂T₀ : z₂ ∈ T₀ := Subgroup.subset_closure (by simp)
  have ht'T₀ : t' ∈ T₀ := Subgroup.subset_closure (by simp)
  have hP₁c : Nat.card P₁ = 3 := by
    rw [hP₁, Nat.card_zpowers]
    exact orderOf_eq_prime ha₁3 ha₁1
  have hP₂c : Nat.card P₂ = 3 := by
    rw [hP₂, Nat.card_zpowers]
    exact orderOf_eq_prime ha₂3 ha₂1
  have hcard : Nat.card Ā = 9 := by
    have hd' : P₁ ⊓ P₂ = ⊥ := eq_bot_iff.2 (hd ▸ inf_le_inf hP₁K hP₂K)
    rw [hĀ, card_sup_eq_mul hcomm hd', hP₁c, hP₂c]
  have hdec : ∀ c ∈ Ā, ∃ x ∈ P₁, ∃ y ∈ P₂, x * y = c := fun c hc' =>
    exists_mul_of_mem_sup hcomm hc'
  have hinv : ∀ a ∈ Ā, (z₁ * z₂) * a * (z₁ * z₂)⁻¹ * a = 1 := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec a ha
    calc z₁ * z₂ * (x * y) * (z₁ * z₂)⁻¹ * (x * y)
        = z₁ * (z₂ * x * z₂⁻¹) * (z₂ * y * z₂⁻¹) * z₁⁻¹ * (x * y) := by group
      _ = z₁ * x * y⁻¹ * z₁⁻¹ * (x * y) := by rw [hz₂x x hx, hz₂y y hy]
      _ = (z₁ * x * z₁⁻¹) * (z₁ * y⁻¹ * z₁⁻¹) * (x * y) := by group
      _ = x⁻¹ * y⁻¹ * (x * y) := by rw [hz₁x x hx, hz₁y y⁻¹ (P₂.inv_mem hy)]
      _ = 1 := by
        rw [show x⁻¹ * y⁻¹ * (x * y) = (y * x)⁻¹ * (x * y) by group, ← hcomm x hx y hy]
        group
  exact ⟨Ā, T₀, hcard, hT₀S, hT₀N, fun C hCĀ hCN => irreducible_of_swap ha₁3 ha₁1 ha₂3 ha₂1 hcomm
    hz₁T₀ ht'T₀ hz₁x hz₁y hP₁t' hP₂t' hCĀ hCN, hz₁T₀, hz₂T₀, hinv⟩

end E217R4

end CFSG.Quasithin
