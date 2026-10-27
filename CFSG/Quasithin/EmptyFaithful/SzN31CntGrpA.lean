module

public import CFSG.Quasithin.Background.G8DihedralBasic
public import CFSG.Quasithin.EmptyFaithful.SzN31CntFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Open

theorem card_le_two_of_sq_eq_one {K : Type*} [Group K] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hK : Nat.card K = 2 * p) (S : Subgroup K) (hS : ∀ x ∈ S, x * x = 1) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (Nat.mul_pos two_pos hp.pos).ne')
  have hP : IsPGroup 2 S := fun x => ⟨1, by
    have h : x * x = 1 := Subtype.ext (hS x.1 x.2)
    simpa [pow_two] using h⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card S ∣ 2 * p := hK ▸ Subgroup.card_subgroup_dvd_card S
  have hcop : Nat.Coprime (2 ^ k) p := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h2 : 2 ^ k ∣ 2 := hcop.dvd_of_dvd_mul_right (hk ▸ hdvd)
  rw [hk]
  exact Nat.le_of_dvd two_pos h2

theorem exists_mulSingle_mem_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ι → Type*}
    [∀ i, Group (K i)] [∀ i, Finite (K i)]
    (hK : ∀ i (S : Subgroup (K i)), (∀ x ∈ S, x * x = 1) → Nat.card S ≤ 2)
    (E : Subgroup (∀ i, K i)) (hE : ∀ u ∈ E, u * u = 1)
    (hcard : Nat.card E = 2 ^ Fintype.card ι) (i : ι) :
    ∃ t : K i, t ≠ 1 ∧ Pi.mulSingle i t ∈ E := by
  set S : ∀ j, Subgroup (K j) := fun j => E.map (Pi.evalMonoidHom K j) with hS
  have hSsq : ∀ j, ∀ x ∈ S j, x * x = 1 := by
    intro j x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    have := congrFun (hE u hu) j
    simpa using this
  have hSc : ∀ j, Nat.card (S j) ≤ 2 := fun j => hK j (S j) (hSsq j)
  let Ψ : E → ∀ j, S j := fun u j => ⟨u.1 j, Subgroup.mem_map.2 ⟨u.1, u.2, rfl⟩⟩
  have hΨ : Function.Injective Ψ := by
    intro u v h
    apply Subtype.ext
    funext j
    exact congrArg (fun f => ((f j : S j) : K j)) h
  have hcardP : Nat.card (∀ j, S j) = ∏ j, Nat.card (S j) := Nat.card_pi
  have hle : 2 ^ Fintype.card ι ≤ ∏ j, Nat.card (S j) := by
    rw [← hcardP, ← hcard]
    exact Nat.card_le_card_of_injective _ hΨ
  have hge : ∏ j, Nat.card (S j) ≤ 2 ^ Fintype.card ι := by
    calc ∏ j, Nat.card (S j) ≤ ∏ _j : ι, 2 := Finset.prod_le_prod (fun j _ => hSc j)
      _ = 2 ^ Fintype.card ι := by simp
  have hbij : Function.Bijective Ψ :=
    hΨ.bijective_of_nat_card_le (by rw [hcardP, hcard]; exact hge)
  have hSi : S i ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (S i) = 1 := by rw [hbot]; exact Subgroup.card_bot
    have hlt : ∏ j, Nat.card (S j) < ∏ _j : ι, 2 :=
      Finset.prod_lt_prod₀ (fun j _ => Nat.card_pos) (fun j _ => hSc j)
        ⟨i, Finset.mem_univ i, by omega⟩
    simp at hlt
    omega
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSi
  obtain ⟨u, hu⟩ := hbij.2 (Pi.mulSingle i t)
  refine ⟨t.1, fun h => ht1 (Subtype.ext h), ?_⟩
  have : u.1 = Pi.mulSingle i t.1 := by
    funext j
    have hj : u.1 j = ((Pi.mulSingle i t : ∀ j, S j) j : K j) :=
      congrArg (fun f => ((f j : S j) : K j)) hu
    by_cases hji : j = i
    · subst hji
      simpa using hj
    · simpa [Pi.mulSingle_eq_of_ne hji] using hj
  rw [← this]
  exact u.2

theorem dihedral_inv_of_orderOf {n : ℕ} (hn : n.Prime) (hodd : Odd n) {a b : DihedralGroup n}
    (ha : orderOf a = 2) (hb : orderOf b = n) : a * b * a⁻¹ = b⁻¹ := by
  have : NeZero n := ⟨hn.ne_zero⟩
  have hn2 : n ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  cases a with
  | r i =>
    exfalso
    rw [DihedralGroup.orderOf_r] at ha
    rcases (Nat.Prime.eq_one_or_self_of_dvd hn _ (Nat.gcd_dvd_left n i.val)) with h | h
    · rw [h, Nat.div_one] at ha
      exact hn2 ha
    · rw [h, Nat.div_self hn.pos] at ha
      omega
  | sr i =>
    cases b with
    | r j =>
      rw [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]
      congr 1
      ring
    | sr j =>
      exfalso
      rw [DihedralGroup.orderOf_sr] at hb
      exact hn2 hb.symm

theorem exists_involution_mem_factor {G : Type*} [Group G] {r : ℕ} {Hs : Fin r → Subgroup G}
    {p : Fin r → ℕ} (hD : IsDihedralFamily Hs p) {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hEle : E ≤ ⨆ i, Hs i) (hcard : Nat.card E = 2 ^ r) (i : Fin r) :
    ∃ e ∈ E, e ∈ Hs i ∧ e * e = 1 ∧ e ≠ 1 ∧
      ∀ x ∈ Hs i, orderOf x = p i → e * x * e⁻¹ = x⁻¹ := by
  have hcomm : Pairwise fun i j => ∀ x y : G, x ∈ Hs i → y ∈ Hs j → Commute x y :=
    fun i j hij x y hx hy => hD.commute i j hij x hx y hy
  set Φ := Subgroup.noncommPiCoprod hcomm with hΦ
  have hinj : Function.Injective Φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hD.independent
  have hrange : Φ.range = ⨆ i, Hs i := Subgroup.noncommPiCoprod_range
  set E' : Subgroup (∀ j, Hs j) := E.comap Φ with hE'
  have hmap : E'.map Φ = E := by
    rw [hE', Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.2 hEle
  have hE'card : Nat.card E' = 2 ^ Fintype.card (Fin r) := by
    rw [Fintype.card_fin, ← hcard, ← hmap, Subgroup.card_map_of_injective hinj]
  have hE'sq : ∀ u ∈ E', u * u = 1 := by
    intro u hu
    apply hinj
    rw [map_mul, map_one]
    have := hE.2 (Φ u) hu
    simpa [pow_two] using this
  have hcardH : ∀ j, Nat.card (Hs j) = 2 * p j := by
    intro j
    obtain ⟨φ⟩ := hD.iso j
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have : ∀ j, Finite (Hs j) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hcardH j]; exact (Nat.mul_pos two_pos (hD.prime j).pos).ne')
  have hfac : ∀ j, ∀ S : Subgroup (Hs j), (∀ x ∈ S, x * x = 1) → Nat.card S ≤ 2 := fun j S hS =>
    card_le_two_of_sq_eq_one (hD.prime j) (hD.odd j) (hcardH j) S hS
  obtain ⟨t, ht1, ht⟩ := exists_mulSingle_mem_of_card_eq hfac E' hE'sq hE'card i
  have hΦt : Φ (Pi.mulSingle i t) = (t : G) := Subgroup.noncommPiCoprod_mulSingle i t
  have hte : (t : G) ∈ E := by
    rw [← hΦt]
    exact ht
  have htt : (t : G) * t = 1 := by
    have := hE.2 _ hte
    simpa [pow_two] using this
  have htne : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
  refine ⟨t, hte, t.2, htt, htne, ?_⟩
  intro x hx hxo
  obtain ⟨φ⟩ := hD.iso i
  have hta : orderOf (φ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_two] at htt
      exact Subtype.ext htt
    · exact ht1
  have hxb : orderOf (φ ⟨x, hx⟩) = p i := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxo]
  have key := dihedral_inv_of_orderOf (hD.prime i) (hD.odd i) hta hxb
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at key
  have := φ.injective key
  have := congrArg Subtype.val this
  simpa using this

theorem isDihedralFamily_comp_injective {G : Type*} [Group G] {ι κ : Type*}
    {Hs : ι → Subgroup G} {p : ι → ℕ} (hD : IsDihedralFamily Hs p) {f : κ → ι}
    (hf : Function.Injective f) : IsDihedralFamily (Hs ∘ f) (p ∘ f) where
  prime k := hD.prime (f k)
  odd k := hD.odd (f k)
  iso k := hD.iso (f k)
  commute k l hkl x hx y hy := hD.commute (f k) (f l) (fun h => hkl (hf h)) x hx y hy
  independent := hD.independent.comp hf

theorem exists_involutions_two_blocks {G : Type*} [Group G] {k n : ℕ}
    {Hs : Fin (k + n) → Subgroup G} {p : Fin (k + n) → ℕ} (hD : IsDihedralFamily Hs p)
    {E₁ E₂ : Subgroup G} (h₁ : IsElemAbelian 2 E₁) (h₂ : IsElemAbelian 2 E₂)
    (hle₁ : E₁ ≤ ⨆ i : Fin k, Hs (Fin.castAdd n i))
    (hle₂ : E₂ ≤ ⨆ j : Fin n, Hs (Fin.natAdd k j))
    (hc₁ : Nat.card E₁ = 2 ^ k) (hc₂ : Nat.card E₂ = 2 ^ n) :
    ∃ a : Fin (k + n) → G, (∀ i, a i ∈ Hs i) ∧ (∀ i, a i * a i = 1) ∧ (∀ i, a i ≠ 1) ∧
      (∀ i, ∀ x ∈ Hs i, orderOf x = p i → a i * x * (a i)⁻¹ = x⁻¹) ∧
      (∀ i : Fin k, a (Fin.castAdd n i) ∈ E₁) ∧ (∀ j : Fin n, a (Fin.natAdd k j) ∈ E₂) := by
  have hD₁ := isDihedralFamily_comp_injective hD (Fin.castAdd_injective k n)
  have hD₂ := isDihedralFamily_comp_injective hD (Fin.natAdd_injective n k)
  choose a₁ ha₁E ha₁H ha₁sq ha₁ne ha₁c using
    fun i => exists_involution_mem_factor hD₁ h₁ hle₁ hc₁ i
  choose a₂ ha₂E ha₂H ha₂sq ha₂ne ha₂c using
    fun j => exists_involution_mem_factor hD₂ h₂ hle₂ hc₂ j
  refine ⟨Fin.addCases a₁ a₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using ha₁H i
    | right j => simpa using ha₂H j
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using ha₁sq i
    | right j => simpa using ha₂sq j
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using ha₁ne i
    | right j => simpa using ha₂ne j
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using ha₁c i
    | right j => simpa using ha₂c j
  · intro i
    simpa using ha₁E i
  · intro j
    simpa using ha₂E j

section Frame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem frame_of_dihedralFamily {r : ℕ} {Hs : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} {p : Fin r → ℕ}
    (hD : IsDihedralFamily Hs p) (x a : Fin r → V ≃ₗ[ZMod 2] V) (hx : ∀ i, x i ∈ Hs i)
    (hxo : ∀ i, orderOf (x i) = p i) (ha : ∀ i, a i ∈ Hs i) (ha2 : ∀ i, a i * a i = 1)
    (hconj : ∀ i, a i * x i * (a i)⁻¹ = (x i)⁻¹) :
    ∃ F : Frame V (Fin r), F.x = x ∧ F.a = a ∧ F.p = p :=
  ⟨{ x := x
     a := a
     p := p
     prime := hD.prime
     odd := fun i h => by
       have := hD.odd i
       rw [h] at this
       exact absurd this (by decide)
     xpow := fun i => by
       rw [← hxo i]
       exact pow_orderOf_eq_one (x i)
     asq := ha2
     conj := hconj
     xx := fun i j hij => hD.commute i j hij (x i) (hx i) (x j) (hx j)
     aa := fun i j hij => hD.commute i j hij (a i) (ha i) (a j) (ha j)
     xa := fun i j hij => hD.commute i j hij (x i) (hx i) (a j) (ha j) }, rfl, rfl, rfl⟩

theorem exists_frame_of_dihedralFamily {r : ℕ} {Hs : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
    {p : Fin r → ℕ} (hD : IsDihedralFamily Hs p) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : IsElemAbelian 2 E) (hEle : E ≤ ⨆ i, Hs i) (hcard : Nat.card E = 2 ^ r)
    (x : Fin r → V ≃ₗ[ZMod 2] V) (hx : ∀ i, x i ∈ Hs i) (hxo : ∀ i, orderOf (x i) = p i) :
    ∃ F : Frame V (Fin r), F.x = x ∧ F.p = p ∧ ∀ i, F.a i ∈ E ∧ F.a i ∈ Hs i := by
  choose a haE haH ha2 _ hconj using fun i => exists_involution_mem_factor hD hE hEle hcard i
  obtain ⟨F, hFx, hFa, hFp⟩ := frame_of_dihedralFamily hD x a hx hxo haH ha2
    (fun i => hconj i (x i) (hx i) (hxo i))
  exact ⟨F, hFx, hFp, fun i => by rw [hFa]; exact ⟨haE i, haH i⟩⟩

theorem exists_frame_two_blocks {k n : ℕ} {Hs : Fin (k + n) → Subgroup (V ≃ₗ[ZMod 2] V)}
    {p : Fin (k + n) → ℕ} (hD : IsDihedralFamily Hs p) {E₁ E₂ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h₁ : IsElemAbelian 2 E₁) (h₂ : IsElemAbelian 2 E₂)
    (hle₁ : E₁ ≤ ⨆ i : Fin k, Hs (Fin.castAdd n i))
    (hle₂ : E₂ ≤ ⨆ j : Fin n, Hs (Fin.natAdd k j))
    (hc₁ : Nat.card E₁ = 2 ^ k) (hc₂ : Nat.card E₂ = 2 ^ n)
    (x : Fin (k + n) → V ≃ₗ[ZMod 2] V) (hx : ∀ i, x i ∈ Hs i) (hxo : ∀ i, orderOf (x i) = p i) :
    ∃ F : Frame V (Fin (k + n)), F.x = x ∧ F.p = p ∧ (∀ i, F.a i ∈ Hs i) ∧
      (∀ i : Fin k, F.a (Fin.castAdd n i) ∈ E₁) ∧ (∀ j : Fin n, F.a (Fin.natAdd k j) ∈ E₂) := by
  obtain ⟨a, haH, ha2, -, hconj, haE₁, haE₂⟩ :=
    exists_involutions_two_blocks hD h₁ h₂ hle₁ hle₂ hc₁ hc₂
  obtain ⟨F, hFx, hFa, hFp⟩ := frame_of_dihedralFamily hD x a hx hxo haH ha2
    (fun i => hconj i (x i) (hx i) (hxo i))
  refine ⟨F, hFx, hFp, fun i => by rw [hFa]; exact haH i,
    fun i => by rw [hFa]; exact haE₁ i, fun j => by rw [hFa]; exact haE₂ j⟩

end Frame

end CFSG.Quasithin.SzN31
