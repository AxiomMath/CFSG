module

public import CFSG.Quasithin.H13.A7Offender

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def cyc016 : Perm (Fin 7) := swap 0 6 * swap 0 1

@[expose] def tcyc (p : Fin 4) (o : Bool) : Perm (Fin 7) :=
  if p = 0 then (if o then swap 3 4 * swap 3 5 else swap 3 5 * swap 3 4)
  else if p = 1 then (if o then swap 2 4 * swap 2 5 else swap 2 5 * swap 2 4)
  else if p = 2 then (if o then swap 2 3 * swap 2 5 else swap 2 5 * swap 2 3)
  else (if o then swap 2 3 * swap 2 4 else swap 2 4 * swap 2 3)

@[expose] def acyc : Option (Fin 4 × Bool) → Perm (Fin 7)
  | none => 1
  | some (p, o) => tcyc p o

@[expose] def fam27 (a : Option (Fin 4 × Bool)) (j : Fin 3) : Perm (Fin 7) :=
  acyc a * cyc016 ^ (j : ℕ)

@[expose] def Cond27 (σ : Perm (Fin 7)) : Prop :=
  permAct7 σ vecFour = vecFour ∧ ∀ i, σ (σ (σ i)) = i

instance : DecidablePred Cond27 := fun σ => by
  unfold Cond27
  infer_instance

theorem card_filter_cond27 : (Finset.univ.filter Cond27).card = 27 := by
  decide +kernel

theorem cond27_fam27 : ∀ a j, Cond27 (fam27 a j) := by
  decide +kernel

theorem fam27_injective : ∀ a j a' j', fam27 a j = fam27 a' j' → a = a' ∧ j = j' := by
  decide +kernel

theorem exists_fam27 {σ : Perm (Fin 7)} (h : Cond27 σ) : ∃ a j, σ = fam27 a j := by
  classical
  have hinj : Function.Injective fun q : Option (Fin 4 × Bool) × Fin 3 => fam27 q.1 q.2 := by
    rintro ⟨a, j⟩ ⟨a', j'⟩ hq
    obtain ⟨rfl, rfl⟩ := fam27_injective a j a' j' hq
    rfl
  have himage : Finset.univ.image (fun q : Option (Fin 4 × Bool) × Fin 3 => fam27 q.1 q.2) =
      Finset.univ.filter Cond27 := by
    refine Finset.eq_of_subset_of_card_le (fun g hg => ?_) ?_
    · obtain ⟨⟨a, j⟩, -, rfl⟩ := Finset.mem_image.1 hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, cond27_fam27 a j⟩
    · rw [card_filter_cond27, Finset.card_image_of_injective _ hinj]
      rfl
  have hmem : σ ∈ Finset.univ.image fun q : Option (Fin 4 × Bool) × Fin 3 => fam27 q.1 q.2 := by
    rw [himage]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
  obtain ⟨⟨a, j⟩, -, hq⟩ := Finset.mem_image.1 hmem
  exact ⟨a, j, hq.symm⟩

@[expose] def vecTwo : Fin 7 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1

theorem fam27_fix_vecTwo : ∀ a j, permAct7 (fam27 a j) vecTwo = vecTwo → j = 0 := by
  decide +kernel

theorem fam27_zero : ∀ a, fam27 a 0 = acyc a := by
  decide +kernel

theorem fam27_none : ∀ j, fam27 none j = cyc016 ^ (j : ℕ) := by
  decide +kernel

theorem fam27_mul_conj :
    ∀ a j, fam27 a j * (swap 0 1 * fam27 a j * swap 0 1) = acyc a * acyc a := by
  decide +kernel

theorem tcyc_mul_self : ∀ p o, tcyc p o * tcyc p o = tcyc p (!o) := by
  decide +kernel

theorem word_tcyc_trans : ∀ p p' : Fin 4, ∀ o : Bool,
    ∃ u : Bool × Bool × Bool × Bool, ∃ o' : Bool, sevenWord u * tcyc p o * (sevenWord u)⁻¹ =
      tcyc p' o' := by
  decide +kernel

theorem cyc016_mem_alternating : cyc016 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem permAct7_cyc016_vecFour : permAct7 cyc016 vecFour = vecFour := by
  decide +kernel

theorem cyc016_pow_three : cyc016 ^ 3 = 1 := by
  decide +kernel

theorem fam27_none_ne_one : ∀ j : Fin 3, j ≠ 0 → cyc016 ^ (j : ℕ) ≠ 1 := by
  decide +kernel

section Coord

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatConfig.lact' (h : A7NatConfig T L V ψ) : ∀ a ∈ L, ∃ σ, IsCoordAct ψ a σ :=
  fun a ha => (h.Lact a ha).imp fun _ hσ => hσ.2

@[expose] noncomputable def A7NatConfig.lamA (h : A7NatConfig T L V ψ) :
    L →* alternatingGroup (Fin 7) :=
  (coordRep ψ h.L_le h.lact').codRestrict _ fun l => by
    obtain ⟨σ, hσA, hσ⟩ := h.Lact l l.2
    rw [IsCoordAct.unique ψ (h.L_le l.2) (coordRep_spec ψ h.L_le h.lact' l) hσ]
    exact hσA

theorem A7NatConfig.lamA_spec (h : A7NatConfig T L V ψ) (l : L) :
    IsCoordAct ψ l (h.lamA l : Perm (Fin 7)) :=
  coordRep_spec ψ h.L_le h.lact' l

theorem A7NatConfig.lamA_eq (h : A7NatConfig T L V ψ) (l : L) {σ : Perm (Fin 7)}
    (hσ : IsCoordAct ψ l σ) : (h.lamA l : Perm (Fin 7)) = σ :=
  IsCoordAct.unique ψ (h.L_le l.2) (h.lamA_spec l) hσ

theorem A7NatConfig.lamA_surjective (h : A7NatConfig T L V ψ) : Function.Surjective h.lamA := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
  exact ⟨⟨l, hl⟩, Subtype.ext (h.lamA_eq ⟨l, hl⟩ hact)⟩

theorem A7NatConfig.lamA_eq_one_iff (h : A7NatConfig T L V ψ) (l : L) :
    h.lamA l = 1 ↔ (l : G) ∈ centralizer (V : Set G) := by
  rw [← coordRep_eq_one_iff ψ h.L_le h.lact' l]
  constructor
  · intro h1
    exact congrArg Subtype.val h1
  · intro h1
    exact Subtype.ext h1

theorem A7NatConfig.mem_centralizer_iff_lamA (h : A7NatConfig T L V ψ) {e : V}
    (he : vec ψ e = vecFour) (l : L) :
    (l : G) ∈ centralizer ({(e : G)} : Set G) ↔ h.lamA l ∈ stabVecFour := by
  have hspec := h.lamA_spec l
  let y : V := ⟨(l : G) * e * (l : G)⁻¹, (mem_normalizer_iff.1 (h.L_le l.2) e).1 e.2⟩
  have hy := hspec e y rfl
  rw [he] at hy
  show _ ↔ permAct7 (h.lamA l : Perm (Fin 7)) vecFour = vecFour
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have hye : y = e := Subtype.ext (show (l : G) * e * (l : G)⁻¹ = e by
      rw [hc, mul_inv_cancel_right])
    rw [← hy, hye, he]
  · intro hf
    rw [hf, ← he] at hy
    have h1 : (l : G) * e * (l : G)⁻¹ = e := congrArg Subtype.val (vec_injective ψ hy)
    calc (l : G) * e = (l : G) * e * (l : G)⁻¹ * l := by group
      _ = e * l := by rw [h1]

theorem A7NatConfig.card_inf_centralizer_e [Finite G] (h : A7NatConfig T L V ψ) {e : V}
    (he : vec ψ e = vecFour) :
    Nat.card (L ⊓ centralizer ({(e : G)} : Set G) : Subgroup G) =
      72 * Nat.card (L ⊓ centralizer (V : Set G) : Subgroup G) := by
  have h1 : (L ⊓ centralizer ({(e : G)} : Set G)).subgroupOf L = stabVecFour.comap h.lamA := by
    ext l
    rw [mem_subgroupOf, Subgroup.mem_comap, mem_inf, ← h.mem_centralizer_iff_lamA he]
    exact ⟨fun hl => hl.2, fun hl => ⟨l.2, hl⟩⟩
  have h2 : h.lamA.ker = (centralizer (V : Set G)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, mem_subgroupOf, h.lamA_eq_one_iff]
  have h3 : (centralizer (V : Set G)).subgroupOf L =
      (L ⊓ centralizer (V : Set G)).subgroupOf L := by
    ext x
    simp [mem_subgroupOf]
  have h4 : Nat.card (L ⊓ centralizer ({(e : G)} : Set G) : Subgroup G) =
      Nat.card ((L ⊓ centralizer ({(e : G)} : Set G)).subgroupOf L) :=
    (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have h5 : Nat.card (L ⊓ centralizer (V : Set G) : Subgroup G) =
      Nat.card ((L ⊓ centralizer (V : Set G)).subgroupOf L) :=
    (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [h4, h5, h1, card_comap_of_surjective' h.lamA_surjective, nat_card_stabVecFour, h2, h3]

end Coord

section X

variable {G : Type} [Group G] [Finite G]

theorem A7NatConfig.exists_x {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (h : A7NatConfig T L V ψ) (hC2 : IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G))
    (hTL : T ≤ normalizer (L : Set G))
    {e : V} (he : vec ψ e = vecFour) (hTe : T ≤ centralizer ({(e : G)} : Set G))
    {K : Subgroup G} (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hCK : centralizer ({(e : G)} : Set G) ≤ normalizer (K : Set G))
    {t₀ : G} (ht₀T : t₀ ∈ T) (ht₀ : IsCoordAct ψ t₀ (swap 0 1))
    (hTall : ∀ u, ∃ t ∈ T, IsCoordAct ψ t (sevenWord u))
    {k : G} (hkK : k ∈ K) (hkL : k ∈ L) (hke : k ∈ centralizer ({(e : G)} : Set G))
    (hk3 : k ^ 3 = 1) (hkO : k ∉ pCoreOf 2 K) {p : Fin 4} {o : Bool}
    (hkl : IsCoordAct ψ k (tcyc p o)) :
    ∃ x : G, x ∈ L ∧ ∃ hxe : x ∈ centralizer ({(e : G)} : Set G),
      kAct eK ⟨x, hCK hxe⟩ = 1 ∧ x ^ 3 = 1 ∧
        ∃ j : Fin 3, j ≠ 0 ∧ IsCoordAct ψ x (cyc016 ^ (j : ℕ)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (V : Set G) with hNdef
  set lamN : N →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  have hspec : ∀ m : N, IsCoordAct ψ m (lamN m) := coordRep_spec ψ le_rfl h.Nact
  have heq : ∀ (m : N) {σ : Perm (Fin 7)}, IsCoordAct ψ m σ → lamN m = σ := fun m σ hσ =>
    IsCoordAct.unique ψ m.2 (hspec m) hσ
  have hTN : T ≤ N := h.T_le
  have hLN : L ≤ N := h.L_le
  set R : Subgroup G := L ⊓ centralizer ({(e : G)} : Set G) with hRdef
  have hRN : R ≤ normalizer (K : Set G) := inf_le_right.trans hCK
  set φ : R →* Perm (Fin 5) := (kAct eK).comp (inclusion hRN) with hφdef
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hC2
  have hRcard : Nat.card R = 9 * (8 * 2 ^ a) := by
    rw [h.card_inf_centralizer_e he, ha]
    ring
  have hcardR := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hRcard] at hcardR
  have hdvd : Nat.card φ.range ∣ 120 := by
    have h1 := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, Nat.card_fin] at h1
  have h3 : 3 ∣ Nat.card φ.ker := by
    by_contra h3
    have hcop : Nat.Coprime (3 ^ 2) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    have h9 : 3 ^ 2 ∣ Nat.card φ.range * Nat.card φ.ker := by
      rw [← hcardR]
      exact Dvd.intro _ rfl
    have h10 := (hcop.dvd_of_dvd_mul_right h9).trans hdvd
    norm_num at h10
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set y : G := ((y₀ : R) : G) with hydef
  have hyR : y ∈ R := (y₀ : R).2
  have hyL : y ∈ L := (mem_inf.1 hyR).1
  have hye : y ∈ centralizer ({(e : G)} : Set G) := (mem_inf.1 hyR).2
  have hyK : kAct eK ⟨y, hCK hye⟩ = 1 := y₀.2
  have hyord : orderOf y = 3 := by
    rw [hydef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy₀]
  have hy3 : y ^ 3 = 1 := by
    rw [← hyord]
    exact pow_orderOf_eq_one y
  set σ : Perm (Fin 7) := lamN ⟨y, hLN hyL⟩ with hσdef
  have hσ : IsCoordAct ψ y σ := hspec ⟨y, hLN hyL⟩
  have hσA : (h.lamA ⟨y, hyL⟩ : Perm (Fin 7)) = σ := h.lamA_eq ⟨y, hyL⟩ hσ
  have hσstab : permAct7 σ vecFour = vecFour := by
    rw [← hσA]
    exact (h.mem_centralizer_iff_lamA he ⟨y, hyL⟩).1 hye
  have hσ3 : ∀ i, σ (σ (σ i)) = i := by
    intro i
    have h1 : σ ^ 3 = 1 := by
      rw [hσdef, ← map_pow]
      have h2 : (⟨y, hLN hyL⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [h2, map_one]
    have h2 := congrArg (fun τ : Perm (Fin 7) => τ i) h1
    simpa [pow_succ, Perm.mul_apply] using h2
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hyC : y ∈ centralizer (V : Set G) := by
      have := (coordRep_eq_one_iff ψ le_rfl h.Nact ⟨y, hLN hyL⟩).1 h1
      exact this
    obtain ⟨n, hn⟩ := hC2 ⟨y, mem_inf.2 ⟨hyL, hyC⟩⟩
    have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 := orderOf_dvd_of_pow_eq_one hn'
    rw [hyord] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  obtain ⟨a', j, hσeq⟩ := exists_fam27 ⟨hσstab, hσ3⟩
  rcases a' with _ | ⟨p₁, o₁⟩
  · rw [fam27_none] at hσeq
    have hj : j ≠ 0 := by
      rintro rfl
      apply hσ1
      rw [hσeq]
      simp
    exact ⟨y, hyL, hye, hyK, hy3, j, hj, hσeq ▸ hσ⟩
  exfalso
  have ht₀N : t₀ ∈ N := hTN ht₀T
  have ht₀e : t₀ ∈ centralizer ({(e : G)} : Set G) := hTe ht₀T
  have hlamt₀ : lamN ⟨t₀, ht₀N⟩ = swap 0 1 := heq _ ht₀
  have hconjL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht l hl =>
    (mem_normalizer_iff.1 (hTL ht) l).1 hl
  have hconje : ∀ t ∈ T, ∀ l ∈ centralizer ({(e : G)} : Set G),
      t * l * t⁻¹ ∈ centralizer ({(e : G)} : Set G) := fun t ht l hl =>
    mul_mem (mul_mem (hTe ht) hl) (inv_mem (hTe ht))
  have hkActconj : ∀ t (ht : t ∈ T) l (hl : l ∈ centralizer ({(e : G)} : Set G)),
      kAct eK ⟨l, hCK hl⟩ = 1 → kAct eK ⟨t * l * t⁻¹, hCK (hconje t ht l hl)⟩ = 1 := by
    intro t ht l hl h1
    rw [show (⟨t * l * t⁻¹, hCK (hconje t ht l hl)⟩ : normalizer (K : Set G)) =
      ⟨t, hCK (hTe ht)⟩ * ⟨l, hCK hl⟩ * ⟨t, hCK (hTe ht)⟩⁻¹ from rfl, map_mul, map_mul, map_inv,
      h1, mul_one, mul_inv_cancel]
  set z : G := y * (t₀ * y * t₀⁻¹) with hzdef
  have hzL : z ∈ L := mul_mem hyL (hconjL t₀ ht₀T y hyL)
  have hze : z ∈ centralizer ({(e : G)} : Set G) := mul_mem hye (hconje t₀ ht₀T y hye)
  have hzK : kAct eK ⟨z, hCK hze⟩ = 1 := by
    rw [show (⟨z, hCK hze⟩ : normalizer (K : Set G)) =
      ⟨y, hCK hye⟩ * ⟨t₀ * y * t₀⁻¹, hCK (hconje t₀ ht₀T y hye)⟩ from rfl, map_mul, hyK,
      hkActconj t₀ ht₀T y hye hyK, mul_one]
  have hlamz : lamN ⟨z, hLN hzL⟩ = tcyc p₁ (!o₁) := by
    rw [show (⟨z, hLN hzL⟩ : N) = ⟨y, hLN hyL⟩ * (⟨t₀, ht₀N⟩ * ⟨y, hLN hyL⟩ * ⟨t₀, ht₀N⟩⁻¹)
      from rfl, map_mul, map_mul, map_mul, map_inv, hlamt₀, ← hσdef, hσeq, swap_inv,
      fam27_mul_conj]
    exact tcyc_mul_self p₁ o₁
  obtain ⟨u, o', hu⟩ := word_tcyc_trans p₁ p (!o₁)
  obtain ⟨t, htT, htu⟩ := hTall u
  have htN : t ∈ N := hTN htT
  set z' : G := t * z * t⁻¹ with hz'def
  have hz'L : z' ∈ L := hconjL t htT z hzL
  have hz'e : z' ∈ centralizer ({(e : G)} : Set G) := hconje t htT z hze
  have hz'K : kAct eK ⟨z', hCK hz'e⟩ = 1 := hkActconj t htT z hze hzK
  have hlamz' : lamN ⟨z', hLN hz'L⟩ = tcyc p o' := by
    rw [show (⟨z', hLN hz'L⟩ : N) = ⟨t, htN⟩ * ⟨z, hLN hzL⟩ * ⟨t, htN⟩⁻¹ from rfl, map_mul,
      map_mul, map_inv, hlamz, heq _ htu, hu]
  have hkN : k ∈ N := hLN hkL
  have hlamk : lamN ⟨k, hkN⟩ = tcyc p o := heq _ hkl
  obtain ⟨m, hm12, hkm⟩ : ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ lamN ⟨k, hkN⟩ ^ m = tcyc p o' := by
    by_cases ho : o' = o
    · exact ⟨1, Or.inl rfl, by rw [pow_one, hlamk, ho]⟩
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [pow_two, hlamk, tcyc_mul_self]
      congr 1
      cases o <;> cases o' <;> simp_all
  set w : G := z'⁻¹ * k ^ m with hwdef
  have hwL : w ∈ L := mul_mem (inv_mem hz'L) (pow_mem hkL m)
  have hwC : w ∈ centralizer (V : Set G) := by
    have h1 : lamN ⟨w, hLN hwL⟩ = 1 := by
      rw [show (⟨w, hLN hwL⟩ : N) = (⟨z', hLN hz'L⟩ : N)⁻¹ * ⟨k, hkN⟩ ^ m from rfl, map_mul,
        map_inv, map_pow, hlamz', hkm, inv_mul_cancel]
    exact (coordRep_eq_one_iff ψ le_rfl h.Nact ⟨w, hLN hwL⟩).1 h1
  obtain ⟨n, hn⟩ := hC2 ⟨w, mem_inf.2 ⟨hwL, hwC⟩⟩
  have hn' : w ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hke' : k ∈ centralizer ({(e : G)} : Set G) := hke
  have hwe : w ∈ centralizer ({(e : G)} : Set G) := mul_mem (inv_mem hz'e) (pow_mem hke' m)
  have hkActw : kAct eK ⟨w, hCK hwe⟩ = kBar eK ⟨k, hkK⟩ ^ m := by
    rw [show (⟨w, hCK hwe⟩ : normalizer (K : Set G)) =
      (⟨z', hCK hz'e⟩ : normalizer (K : Set G))⁻¹ * ⟨k, le_normalizer hkK⟩ ^ m from rfl,
      map_mul, map_inv, hz'K, inv_one, one_mul, map_pow, kAct_of_mem]
  have h1 : (kBar eK ⟨k, hkK⟩) ^ (m * 2 ^ n) = 1 := by
    rw [pow_mul, ← hkActw, ← map_pow]
    have h2 : (⟨w, hCK hwe⟩ : normalizer (K : Set G)) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using hn')
    rw [h2, map_one]
  have h2 : (kBar eK ⟨k, hkK⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨k, hkK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [h3, map_one]
  have h3 : orderOf (kBar eK ⟨k, hkK⟩) ∣ Nat.gcd 3 (m * 2 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  have h4 : Nat.gcd 3 (m * 2 ^ n) = 1 := by
    rcases hm12 with rfl | rfl
    · rw [one_mul]
      exact Nat.Coprime.pow_right _ (by norm_num)
    · rw [← pow_succ']
      exact Nat.Coprime.pow_right _ (by norm_num)
  rw [h4, Nat.dvd_one, orderOf_eq_one_iff, kBar_eq_one_iff] at h3
  exact hkO (by rw [pCoreOf_eq_map_cfsgPCore]; exact ⟨_, h3, rfl⟩)

end X

end CFSG.Quasithin.H13.A7