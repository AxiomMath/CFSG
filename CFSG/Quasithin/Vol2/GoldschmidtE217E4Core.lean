module

public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Z
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Abs
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27Inv
public import CFSG.Quasithin.Vol2.GoldschmidtE217L2Dih

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3
open CFSG.GorensteinWalter (PSL2)

namespace E217R4

theorem e4_core
    {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F] {p : ℕ}
    {K₁ K₂ S E : Subgroup Y} {t : Y} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hF : Nat.card F = p) (θ : K₁ ≃* PSL2 F) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : Y, (∀ k ∈ K₁ ⊔ K₂, a * k = k * a) → a = 1) (hSsyl : IsSylowTwoOf S ⊤)
    (htS : t ∈ S) (hK₂ : K₁.map (MulAut.conj t).toMonoidHom = K₂) (haut : 8 < E2.autCard S K₁)
    (hSE : S ≤ Subgroup.normalizer (E : Set Y)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : 4 ≤ Nat.card E)
    (hcube : E ≤ Subgroup.normalizer (K₁ : Set Y) → ∀ x ∈ E,
      x ∉ E ⊓ Subgroup.centralizer (K₁ : Set Y) →
      (∀ e ∈ E, e ∈ E ⊓ Subgroup.centralizer (K₁ : Set Y) ∨
        x * e ∈ E ⊓ Subgroup.centralizer (K₁ : Set Y)) → ∀ g ∈ K₁, ∀ n : ℕ, Odd n →
      (x * (g * x * g⁻¹)) ^ n = 1 → (x * (g * x * g⁻¹)) ^ 3 = 1) :
    ∃ Ā T₀ : Subgroup Y, Nat.card Ā = 9 ∧ T₀ ≤ S ∧ T₀ ≤ Subgroup.normalizer (Ā : Set Y) ∧
      (∀ C : Subgroup Y, C ≤ Ā → T₀ ≤ Subgroup.normalizer (C : Set Y) → C = ⊥ ∨ C = Ā) ∧
      E ≤ T₀ ∧ ∃ v ∈ E, ∀ a ∈ Ā, v * a * v⁻¹ * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 : 7 ≤ p := P3.seven_le hp hp8
  have h₁ : IsSimpleGroup ↥K₁ := P3.isSimpleGroup_of hp hp8 hF θ
  have hfinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  let θ₂ : ↥K₂ ≃* PSL2 F :=
    ((K₁.equivMapOfInjective _ hfinj).trans (MulEquiv.subgroupCongr hK₂)).symm.trans θ
  have hz₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, y * x = x * y) → x = 1 := fun x hx hxc =>
    P3.eq_one_of_central θ hx fun y hy => (hxc y hy).symm
  have hz₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, y * x = x * y) → x = 1 := fun x hx hxc =>
    P3.eq_one_of_central θ₂ hx fun y hy => (hxc y hy).symm
  have hcard : Nat.card K₂ = Nat.card K₁ := by
    rw [← hK₂]
    exact Subgroup.card_map_of_injective hfinj
  obtain ⟨hEN, a, haE, haC, hEa⟩ :=
    P3.exists_eq_sup hp hp8 hF θ hc hd hKn hCK hSsyl htS hK₂ hSE hEc hE2 hE4 haut
  set A₁ := E ⊓ Subgroup.centralizer (K₁ : Set Y) with hA₁
  have ha2 : a * a = 1 := hE2 a haE
  have ha1 : a ≠ 1 := fun h => haC (h ▸ Subgroup.one_mem _)
  have hza : Subgroup.zpowers a ⊓ A₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, hzA⟩
    rcases P3.eq_one_or_eq_of_mem_zpowers ha2 hz with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hzA.2 haC
  have hza2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hcardE : Nat.card E = 2 * Nat.card A₁ := by
    have := card_sup_eq_mul (fun x hx y hy => hEc x ((Subgroup.zpowers_le).2 haE hx) y
      ((inf_le_left : A₁ ≤ E) hy)) hza
    rw [← hEa, hza2] at this
    exact this
  have hApos : 0 < Nat.card A₁ := Nat.card_pos
  have hr : A₁.relIndex E = 2 := by
    have h1 := Subgroup.relIndex_mul_card A₁ E
    rw [inf_eq_left.mpr (inf_le_left : A₁ ≤ E), hcardE] at h1
    exact Nat.eq_of_mul_eq_mul_right hApos h1
  have hE4' : Nat.card E = 4 := by
    have hsq := P3.card_le_sq (K₂ := K₂) hCK hK₂ (hSE htS)
    rw [hr] at hsq
    omega
  have hA₁2 : Nat.card A₁ = 2 := by omega
  have hA₁ne : A₁ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hA₁2
    omega
  obtain ⟨⟨b₁, hb₁A⟩, hb₁1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA₁ne
  have hb₁1 : b₁ ≠ 1 := fun h => hb₁1' (Subtype.ext h)
  have hb₁E : b₁ ∈ E := hb₁A.1
  have hb₁C : ∀ k ∈ K₁, b₁ * k = k * b₁ := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 hb₁A.2 k hk).symm
  have hb₁2 : b₁ * b₁ = 1 := hE2 b₁ hb₁E
  have hzp : Subgroup.zpowers b₁ = A₁ := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hb₁A) ?_
    have : Nat.card (Subgroup.zpowers b₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb₁2) hb₁1
    omega
  have hA₁' : ∀ e ∈ E, (∀ k ∈ K₁, e * k = k * e) → e = 1 ∨ e = b₁ := fun e he hek => by
    have heA : e ∈ A₁ := ⟨he, Subgroup.mem_centralizer_iff.2 fun k hk => (hek k hk).symm⟩
    rw [← hzp] at heA
    exact P3.eq_one_or_eq_of_mem_zpowers hb₁2 heA
  obtain ⟨hne, hclos, hb₂C, hvS⟩ := e4_pair hKn hc h₁ hz₁ hz₂ hcard hCK hK₂.symm htS hSE hEc hE2
    hE4' hb₁E hb₁C hb₁1 hA₁'
  set b₂ : Y := t * b₁ * t⁻¹ with hb₂
  have hb₂E : b₂ ∈ E := (Subgroup.mem_normalizer_iff.1 (hSE htS) b₁).1 hb₁E
  have hb₂2 : b₂ * b₂ = 1 := hE2 b₂ hb₂E
  have hcomm : b₁ * b₂ = b₂ * b₁ := hEc _ hb₁E _ hb₂E
  have hv2 : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
      _ = b₁ * (b₁ * b₂) * b₂ := by rw [← hcomm]
      _ = (b₁ * b₁) * (b₂ * b₂) := by group
      _ = 1 := by rw [hb₁2, hb₂2, one_mul]
  have hv1 : b₁ * b₂ ≠ 1 := fun h => hne (by
    have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hb₁2)
  have hvN := mem_sup_of_central_involution hp hp8 hF θ hc hd hKn hCK hSsyl htS hK₂ haut hv2 hv1
    hvS
  obtain ⟨hb₂K₁, hb₁K₂⟩ := e4_mem hc hCK hEN hb₂E hb₁C hb₂C hvN
  have hb₂1 : b₂ ≠ 1 := fun h => hb₁1 (by
    calc b₁ = t⁻¹ * b₂ * t := by rw [hb₂]; group
      _ = 1 := by rw [h]; group)
  have hb₂A : b₂ ∉ E ⊓ Subgroup.centralizer (K₁ : Set Y) := fun hmem =>
    hb₂1 (hCK b₂ (commutes_sup (fun k hk => (Subgroup.mem_centralizer_iff.1 hmem.2 k hk).symm)
      hb₂C))
  have hU2 : ∀ e ∈ E, e ∈ A₁ ∨ b₂ * e ∈ A₁ := by
    intro e he
    rw [← hclos] at he
    rcases E217R3.klein_closure hb₁2 hb₂2 hcomm e he with rfl | rfl | rfl | rfl
    · exact Or.inl A₁.one_mem
    · exact Or.inl hb₁A
    · right
      rw [hb₂2]
      exact A₁.one_mem
    · right
      have : b₂ * (b₁ * b₂) = b₁ := by
        calc b₂ * (b₁ * b₂) = (b₂ * b₁) * b₂ := by group
          _ = (b₁ * b₂) * b₂ := by rw [hcomm]
          _ = b₁ := by rw [mul_assoc, hb₂2, mul_one]
      rw [this]
      exact hb₁A
  have hOA : OddCube (⟨b₂, hb₂K₁⟩ : ↥K₁) :=
    OddCube.of_subgroup hb₂K₁ fun g hg n hn h => hcube hEN b₂ hb₂E hb₂A hU2 g hg n hn h
  have hq5 : 5 ≤ Nat.card F := by rw [hF]; omega
  have hF2 : ringChar F ≠ 2 := by
    intro h2
    have : CharP F 2 := h2 ▸ ringChar.charP F
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp2, hn⟩ := FiniteField.card F 2
    have h3 : p = 2 ^ (n : ℕ) := by rw [← hF, Nat.card_eq_fintype_card, hn]
    have h4 : 2 ∣ p := h3 ▸ dvd_pow_self 2 n.ne_zero
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h4
    omega
  have hne' : θ ⟨b₂, hb₂K₁⟩ ≠ 1 := fun h' => hb₂1 (by
    have := θ.injective (h'.trans (map_one θ).symm)
    exact congrArg Subtype.val this)
  have hsq' : θ ⟨b₂, hb₂K₁⟩ * θ ⟨b₂, hb₂K₁⟩ = 1 := by
    rw [← map_mul, show (⟨b₂, hb₂K₁⟩ : ↥K₁) * ⟨b₂, hb₂K₁⟩ = 1 from Subtype.ext hb₂2, map_one]
  have h57 := card_eq_five_or_seven hF2 hq5 hne' hsq' (hOA.map θ)
  have hp7' : p = 7 := by
    rw [hF] at h57
    omega
  subst hp7'
  have : Fintype F := Fintype.ofFinite F
  have hF7 : Fintype.card F = 7 := by rw [← Nat.card_eq_fintype_card, hF]
  have hL₁ : L27 ↥K₁ := L27.of_mulEquiv θ (l27_psl hF7)
  have hL₂ : L27 ↥K₂ := L27.of_mulEquiv θ₂ (l27_psl hF7)
  obtain ⟨Ā, T₀, hA9, hT₀S, hT₀N, hirr, ⟨k₁, hk₁, k₂, hk₂, hvk, hk₁T, hk₂T⟩, -, hvinv⟩ :=
    exists_pair_of_swap hSsyl hKn hc hd hL₁ hL₂ hK₂.symm htS hvS hv2 hv1 hvN
  obtain ⟨hk₁b, hk₂b⟩ := eq_of_mul_eq_of_inf_eq_bot hd hk₁ hb₂K₁ hk₂ hb₁K₂ (hvk.symm.trans hcomm)
  have hb₂T : b₂ ∈ T₀ := hk₁b ▸ hk₁T
  have hb₁T : b₁ ∈ T₀ := hk₂b ▸ hk₂T
  have hET : E ≤ T₀ := by
    rw [← hclos]
    refine (Subgroup.closure_le T₀).2 ?_
    rintro y (rfl | rfl)
    exacts [hb₁T, hb₂T]
  exact ⟨Ā, T₀, hA9, hT₀S, hT₀N, hirr, hET, b₁ * b₂, E.mul_mem hb₁E hb₂E, hvinv⟩

end E217R4

end CFSG.Quasithin
