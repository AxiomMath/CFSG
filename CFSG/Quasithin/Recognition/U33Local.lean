module

public import CFSG.Quasithin.Recognition.U33Defs
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open (WreathedTwoGroup)

private theorem dvd_ncard_of_free {X : Type*} [Finite X] {p n : ℕ} [Fact p.Prime]
    (π : Equiv.Perm X) (hπ : π ^ p ^ n = 1) {A : Set X} (hA : ∀ x, π x ∈ A ↔ x ∈ A)
    (hfree : ∀ x ∈ A, π x ≠ x) : p ∣ A.ncard := by
  classical
  have := Fintype.ofFinite X
  let π' : Equiv.Perm A := π.subtypePerm hA
  have hπ' : π' ^ p ^ n = 1 := by
    ext ⟨g, hg⟩
    simp [π', hπ]
  by_contra h
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime h hπ'
  exact hfree a.1 a.2 (congrArg Subtype.val ha)

private theorem perm_trivial_or_transitive {X : Type*} [Finite X] (π σ : Equiv.Perm X)
    (hπ : π ^ 3 = 1) (hσ : σ ^ 2 = 1) (hcomm : π * σ = σ * π) {A : Set X} (hA : A.ncard = 6)
    (hAπ : ∀ x, π x ∈ A ↔ x ∈ A) (hAσ : ∀ x, σ x ∈ A ↔ x ∈ A) (hfree : ∀ x ∈ A, σ x ≠ x) :
    (∀ x ∈ A, π x = x) ∨ ∀ R : Set X, R ⊆ A → (∀ x, π x ∈ R ↔ x ∈ R) →
      (∀ x, σ x ∈ R ↔ x ∈ R) → R.Nonempty → R = A := by
  classical
  have hσ2 : σ ^ 2 ^ 1 = 1 := by simpa using hσ
  have hπ3 : π ^ 3 ^ 1 = 1 := by simpa using hπ
  have hcomm' : ∀ x, π (σ x) = σ (π x) := fun x => congrArg (fun f => f x) hcomm
  by_cases hfix : ∃ x ∈ A, π x = x
  · left
    obtain ⟨x₀, hx₀A, hx₀⟩ := hfix
    set F : Set X := {x | x ∈ A ∧ π x = x} with hF
    set N : Set X := {x | x ∈ A ∧ π x ≠ x} with hN
    have hFσ : ∀ x, σ x ∈ F ↔ x ∈ F := by
      intro x
      simp only [hF, Set.mem_ofPred_eq, hAσ, hcomm']
      rw [σ.apply_eq_iff_eq]
    have hNπ : ∀ x, π x ∈ N ↔ x ∈ N := by
      intro x
      simp only [hN, Set.mem_ofPred_eq, hAπ, ne_eq]
      rw [π.apply_eq_iff_eq]
    have hdF : 2 ∣ F.ncard :=
      dvd_ncard_of_free (p := 2) (n := 1) σ hσ2 hFσ (fun x hx => hfree x hx.1)
    have hdN : 3 ∣ N.ncard :=
      dvd_ncard_of_free (p := 3) (n := 1) π hπ3 hNπ (fun x hx => hx.2)
    have hunion : A = F ∪ N := by
      ext x
      simp only [hF, hN, Set.mem_union, Set.mem_ofPred_eq]
      by_cases h : π x = x <;> simp [h]
    have hdisj : Disjoint F N := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ ⟨-, hx'⟩
      exact hx' hx
    have hsum : A.ncard = F.ncard + N.ncard := by
      conv_lhs => rw [hunion]
      exact Set.ncard_union_eq hdisj
    have hFpos : 0 < F.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨x₀, hx₀A, hx₀⟩
    have hN0 : N.ncard = 0 := by omega
    have hNe : N = ∅ := (Set.ncard_eq_zero (Set.toFinite N)).mp hN0
    intro x hx
    by_contra hne
    have : x ∈ N := ⟨hx, hne⟩
    rw [hNe] at this
    exact this
  · right
    push Not at hfix
    intro R hRA hRπ hRσ hRne
    have hd3 : 3 ∣ R.ncard :=
      dvd_ncard_of_free (p := 3) (n := 1) π hπ3 hRπ (fun x hx => hfix x (hRA hx))
    have hd2 : 2 ∣ R.ncard :=
      dvd_ncard_of_free (p := 2) (n := 1) σ hσ2 hRσ (fun x hx => hfree x (hRA hx))
    have hpos : 0 < R.ncard := (Set.ncard_pos (Set.toFinite _)).mpr hRne
    have hle : R.ncard ≤ A.ncard := Set.ncard_le_ncard hRA
    exact Set.eq_of_subset_of_ncard_le hRA (by omega)

@[expose] def involutionSet {G : Type*} [Group G] (K : Subgroup G) : Set G :=
  {s | s ∈ K ∧ s * s = 1 ∧ s ≠ 1}

theorem involutionSet_mono {G : Type*} [Group G] {K L : Subgroup G} (h : K ≤ L) :
    involutionSet K ⊆ involutionSet L := fun _ hs => ⟨h hs.1, hs.2.1, hs.2.2⟩

theorem ncard_involutionSet {G : Type*} [Group G] (K : Subgroup G) :
    (involutionSet K).ncard = Nat.card {s : K // s * s = 1 ∧ s ≠ 1} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, s.2.1⟩,
        Subtype.ext (by simpa using s.2.2.1),
        fun h => s.2.2.2 (by simpa using congrArg Subtype.val h)⟩
      invFun := fun t => ⟨t.1.1, t.1.2, by simpa using congrArg Subtype.val t.2.1,
        fun h => t.2.2 (Subtype.ext (by simpa using h))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem ncard_mem_and {G : Type*} [Group G] (K : Subgroup G) (φ : G → Prop) :
    {s : G | s ∈ K ∧ φ s}.ncard = Nat.card {t : K // φ t} := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩
      invFun := fun t => ⟨t.1.1, t.1.2, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section Conjugation

variable {G : Type*} [Group G]

private theorem conj_sq_eq_one {u : G} (g : G) (h : u * u = 1) :
    (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
  calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

private theorem conj_ne_one {u : G} (g : G) (h : u ≠ 1) : g * u * g⁻¹ ≠ 1 := fun h' =>
  h (conj_eq_one_iff.mp h')

private theorem exists_conj_mem_sylow [Finite G] (P : Sylow 2 G) {u : G} (hu : orderOf u = 2) :
    ∃ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) := by
  have hp : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨T₁, hT₁⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T₁ P
  refine ⟨g, ?_⟩
  have hu1 : u ∈ (T₁ : Subgroup G) := hT₁ (Subgroup.mem_zpowers u)
  have h1 : MulAut.conj g • u ∈ MulAut.conj g • (T₁ : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ hu1
  have h2 : (↑(g • T₁) : Subgroup G) = MulAut.conj g • (T₁ : Subgroup G) := rfl
  rw [hg] at h2
  rw [h2]
  simpa [MulAut.smul_def] using h1

end Conjugation

theorem involutions_conj_of_local {G : Type*} [Group G] [Finite G] {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {Q : Subgroup G}
    (hQH : Q ≤ Subgroup.centralizer ({z} : Set G))
    (hQN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hQC : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (h3 : 3 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)))
    (eQ : Q ≃* Z4StarQ8Model) {P : Subgroup G} (hQP : Q ≤ P)
    (hP : (involutionSet P).ncard = 7)
    (hconj : ∀ u : G, u * u = 1 → u ≠ 1 → ∃ g : G, g * u * g⁻¹ ∈ P)
    (hweak : ∃ g : G, g * z * g⁻¹ ∈ Q ∧ g * z * g⁻¹ ≠ z) :
    ∀ u : G, u * u = 1 → u ≠ 1 → ∃ g : G, g * z * g⁻¹ = u := by
  classical
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) with hHdef
  have hzc : ∀ h ∈ H, z * h = h * z := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp hh) z (Set.mem_singleton z)
  have hzH : z ∈ H :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  have hzQ : z ∈ Q :=
    hQC ⟨hzH, Subgroup.mem_centralizer_iff.mpr fun q hq => (hzc q (hQH hq)).symm⟩
  have hzcQ : ∀ q : Q, q * (⟨z, hzQ⟩ : Q) = ⟨z, hzQ⟩ * q := fun q =>
    Subtype.ext (hzc q.1 (hQH q.2)).symm
  have hz2Q : (⟨z, hzQ⟩ : Q) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
  have hz1Q : (⟨z, hzQ⟩ : Q) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hQ7 : (involutionSet Q).ncard = 7 := by
    rw [ncard_involutionSet]
    exact Z4StarQ8.natCard_involutions_of_equiv eQ
  have hPQ : involutionSet Q = involutionSet P :=
    Set.eq_of_subset_of_ncard_le (involutionSet_mono hQP) (by omega)
  set S : Set G := {s | s ∈ Q ∧ (s * s = 1 ∧ s ≠ 1 ∧ s ≠ z)} with hSdef
  have hS6 : S.ncard = 6 := by
    rw [hSdef, ncard_mem_and Q (fun s => s * s = 1 ∧ s ≠ 1 ∧ s ≠ z)]
    rw [← Z4StarQ8.natCard_noncentral_of_equiv eQ hzcQ hz2Q hz1Q]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
    constructor
    · rintro ⟨h2, h1, hz⟩
      exact ⟨Subtype.ext h2, fun h => h1 (congrArg Subtype.val h),
        fun h => hz (congrArg Subtype.val h)⟩
    · rintro ⟨h2, h1, hz⟩
      exact ⟨congrArg Subtype.val h2, fun h => h1 (Subtype.ext h), fun h => hz (Subtype.ext h)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3
  set x₀ : G := (x : G) with hx₀def
  have hx₀H : x₀ ∈ H := x.2
  have hx₀ord : orderOf x₀ = 3 := by rw [hx₀def, Subgroup.orderOf_coe, hx3]
  have hx₀3 : x₀ ^ 3 = 1 := by rw [← hx₀ord]; exact pow_orderOf_eq_one x₀
  have hx₀z : x₀ * z = z * x₀ := (hzc x₀ hx₀H).symm
  have hx₀z' : x₀⁻¹ * z = z * x₀⁻¹ := by
    calc x₀⁻¹ * z = x₀⁻¹ * (z * x₀) * x₀⁻¹ := by group
      _ = x₀⁻¹ * (x₀ * z) * x₀⁻¹ := by rw [hx₀z]
      _ = z * x₀⁻¹ := by group
  have hxQ : ∀ g : G, g ∈ Q ↔ x₀ * g * x₀⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp (hQN hx₀H)
  let π : Equiv.Perm G := MulAut.toPerm G (MulAut.conj x₀)
  let σ : Equiv.Perm G := Equiv.mulRight z
  have hπapp : ∀ g, π g = x₀ * g * x₀⁻¹ := fun g => rfl
  have hσapp : ∀ g, σ g = g * z := fun g => rfl
  have hπ3 : π ^ 3 = 1 := by
    change (MulAut.toPerm G (MulAut.conj x₀)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hx₀3, map_one, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    ext g
    simp [sq, Equiv.Perm.mul_apply, hσapp, mul_assoc, hz2]
  have hcomm : π * σ = σ * π := by
    ext g
    simp only [Equiv.Perm.mul_apply, hπapp, hσapp]
    calc x₀ * (g * z) * x₀⁻¹ = x₀ * g * (z * x₀⁻¹) := by group
      _ = x₀ * g * (x₀⁻¹ * z) := by rw [hx₀z']
      _ = x₀ * g * x₀⁻¹ * z := by group
  have hSπ : ∀ g, π g ∈ S ↔ g ∈ S := by
    intro g
    simp only [hSdef, Set.mem_ofPred_eq, hπapp]
    have hsq : x₀ * g * x₀⁻¹ * (x₀ * g * x₀⁻¹) = 1 ↔ g * g = 1 := by
      constructor
      · intro h
        have : x₀⁻¹ * (x₀ * g * x₀⁻¹ * (x₀ * g * x₀⁻¹)) * x₀ = 1 := by rw [h]; group
        calc g * g = x₀⁻¹ * (x₀ * g * x₀⁻¹ * (x₀ * g * x₀⁻¹)) * x₀ := by group
          _ = 1 := this
      · intro h; exact conj_sq_eq_one x₀ h
    have hn1 : x₀ * g * x₀⁻¹ ≠ 1 ↔ g ≠ 1 := by
      rw [ne_eq, ne_eq, conj_eq_one_iff]
    have hnz : x₀ * g * x₀⁻¹ ≠ z ↔ g ≠ z := by
      rw [ne_eq, ne_eq]
      constructor
      · intro h hg; apply h; rw [hg]; rw [mul_inv_eq_iff_eq_mul, hx₀z]
      · intro h hg; apply h
        have : g = x₀⁻¹ * z * x₀ := by
          rw [← hg]; group
        rw [this, hx₀z']; group
    rw [← hxQ g, hsq, hn1, hnz]
  have hsqz : ∀ g ∈ Q, g * z * (g * z) = g * g := by
    intro g hg
    have hgz := hzc g (hQH hg)
    calc g * z * (g * z) = g * (z * g) * z := by group
      _ = g * (g * z) * z := by rw [hgz]
      _ = g * g * (z * z) := by group
      _ = g * g := by rw [hz2, mul_one]
  have hSσ : ∀ g, σ g ∈ S ↔ g ∈ S := by
    intro g
    simp only [hSdef, Set.mem_ofPred_eq, hσapp]
    rw [Subgroup.mul_mem_cancel_right Q hzQ]
    constructor
    · rintro ⟨hgQ, hsq, h1, h2⟩
      refine ⟨hgQ, by rw [← hsqz g hgQ]; exact hsq, ?_, ?_⟩
      · intro h; apply h2; rw [h, one_mul]
      · intro h; apply h1; rw [h, hz2]
    · rintro ⟨hgQ, hsq, h1, h2⟩
      refine ⟨hgQ, by rw [hsqz g hgQ]; exact hsq, ?_, ?_⟩
      · intro h; apply h2
        calc g = g * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = z := by rw [h, one_mul]
      · intro h; apply h1
        calc g = g * z * z⁻¹ := by group
          _ = z * z⁻¹ := by rw [h]
          _ = 1 := by group
  have hSfree : ∀ g ∈ S, σ g ≠ g := by
    intro g _ h
    rw [hσapp] at h
    exact hz1 (by simpa using h)
  rcases perm_trivial_or_transitive π σ hπ3 hσ2 hcomm hS6 hSπ hSσ hSfree with hall | htrans
  ·
    exfalso
    have hxS : ∀ s ∈ S, x₀ * s = s * x₀ := by
      intro s hs
      have := hall s hs
      rw [hπapp] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    have hcomm_u : ∀ u : Q, u * u = 1 → x₀ * (u : G) = (u : G) * x₀ := by
      intro u hu
      by_cases hu1 : (u : G) = 1
      · rw [hu1]; simp
      · by_cases huz : (u : G) = z
        · rw [huz]; exact hx₀z
        · exact hxS _ ⟨u.2, congrArg Subtype.val hu, hu1, huz⟩
    have hxQc : x₀ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨u₁, u₂, u₃, h₁, h₂, h₃, hq3⟩ := Z4StarQ8.exists_product_of_equiv eQ ⟨q, hq⟩
      have hq3' : q = (u₁ : G) * u₂ * u₃ := congrArg Subtype.val hq3
      have c₁ : Commute x₀ (u₁ : G) := hcomm_u u₁ h₁
      have c₂ : Commute x₀ (u₂ : G) := hcomm_u u₂ h₂
      have c₃ : Commute x₀ (u₃ : G) := hcomm_u u₃ h₃
      have hc : Commute x₀ ((u₁ : G) * u₂ * u₃) := (c₁.mul_right c₂).mul_right c₃
      rw [hq3']
      exact hc.eq.symm
    have hx₀Q : x₀ ∈ Q := hQC ⟨hx₀H, hxQc⟩
    have hdvd : orderOf (⟨x₀, hx₀Q⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx₀ord, Z4StarQ8.natCard_of_equiv eQ] at hdvd
    omega
  ·
    obtain ⟨g₀, hg₀Q, hg₀z⟩ := hweak
    set s₀ : G := g₀ * z * g₀⁻¹ with hs₀def
    have hs₀S : s₀ ∈ S := ⟨hg₀Q, conj_sq_eq_one g₀ hz2, conj_ne_one g₀ hz1, hg₀z⟩
    have hflip : ∀ s ∈ S, ∃ b ∈ Q, b * s * b⁻¹ = s * z := by
      intro s hs
      obtain ⟨hsQ, hs2, hs1, hsz⟩ := hs
      obtain ⟨b, hb⟩ := Z4StarQ8.exists_conj_eq_mul_of_equiv eQ (z := ⟨z, hzQ⟩) (s := ⟨s, hsQ⟩)
        hzcQ hz2Q hz1Q (Subtype.ext hs2) (fun h => hs1 (congrArg Subtype.val h))
        (fun h => hsz (congrArg Subtype.val h))
      exact ⟨b.1, b.2, congrArg Subtype.val hb⟩
    set R : Set G := {s | s ∈ S ∧ ∃ h ∈ H, h * s₀ * h⁻¹ = s} with hRdef
    have hRπ : ∀ g, π g ∈ R ↔ g ∈ R := by
      intro g
      constructor
      · rintro ⟨hgS, h, hhH, hh⟩
        refine ⟨(hSπ g).mp hgS, x₀⁻¹ * h, H.mul_mem (H.inv_mem hx₀H) hhH, ?_⟩
        rw [hπapp] at hh
        calc x₀⁻¹ * h * s₀ * (x₀⁻¹ * h)⁻¹ = x₀⁻¹ * (h * s₀ * h⁻¹) * x₀ := by group
          _ = g := by rw [hh]; group
      · rintro ⟨hgS, h, hhH, hh⟩
        refine ⟨(hSπ g).mpr hgS, x₀ * h, H.mul_mem hx₀H hhH, ?_⟩
        rw [hπapp]
        calc x₀ * h * s₀ * (x₀ * h)⁻¹ = x₀ * (h * s₀ * h⁻¹) * x₀⁻¹ := by group
          _ = x₀ * g * x₀⁻¹ := by rw [hh]
    have hRσ : ∀ g, σ g ∈ R ↔ g ∈ R := by
      intro g
      constructor
      · rintro ⟨hgS, h, hhH, hh⟩
        obtain ⟨b, hbQ, hb⟩ := hflip (σ g) hgS
        refine ⟨(hSσ g).mp hgS, b * h, H.mul_mem (hQH hbQ) hhH, ?_⟩
        rw [hσapp] at hh hb
        calc b * h * s₀ * (b * h)⁻¹ = b * (h * s₀ * h⁻¹) * b⁻¹ := by group
          _ = b * (g * z) * b⁻¹ := by rw [hh]
          _ = g * z * z := hb
          _ = g := by rw [mul_assoc, hz2, mul_one]
      · rintro ⟨hgS, h, hhH, hh⟩
        obtain ⟨b, hbQ, hb⟩ := hflip g hgS
        refine ⟨(hSσ g).mpr hgS, b * h, H.mul_mem (hQH hbQ) hhH, ?_⟩
        rw [hσapp]
        calc b * h * s₀ * (b * h)⁻¹ = b * (h * s₀ * h⁻¹) * b⁻¹ := by group
          _ = b * g * b⁻¹ := by rw [hh]
          _ = g * z := hb
    have hRne : R.Nonempty := ⟨s₀, hs₀S, 1, H.one_mem, by group⟩
    have hReq : R = S := htrans R (fun _ hs => hs.1) hRπ hRσ hRne
    have hSO : ∀ s ∈ S, ∃ h ∈ H, h * s₀ * h⁻¹ = s := by
      intro s hs
      have : s ∈ R := by rw [hReq]; exact hs
      exact this.2
    intro u hu2 hu1
    have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    obtain ⟨g, hg⟩ := hconj u hu2 hu1
    have hu'inv : g * u * g⁻¹ ∈ involutionSet P := ⟨hg, conj_sq_eq_one g hu2, conj_ne_one g hu1⟩
    rw [← hPQ] at hu'inv
    obtain ⟨hu'Q, hu'2, hu'1⟩ := hu'inv
    by_cases hu'z : g * u * g⁻¹ = z
    · exact ⟨g⁻¹, by rw [← hu'z]; group⟩
    · obtain ⟨h, hhH, hh⟩ := hSO _ ⟨hu'Q, hu'2, hu'1, hu'z⟩
      refine ⟨g⁻¹ * h * g₀, ?_⟩
      calc g⁻¹ * h * g₀ * z * (g⁻¹ * h * g₀)⁻¹ = g⁻¹ * (h * (g₀ * z * g₀⁻¹) * h⁻¹) * g := by group
        _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [← hs₀def, hh]
        _ = u := by group

@[expose] def IsSymThreeQuotient {H : Type*} [Group H] (N : Subgroup H) : Prop :=
  ∃ φ : H →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ φ.ker = N

theorem isSymThreeQuotient_of_mulEquiv {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    (e : H ⧸ N ≃* Equiv.Perm (Fin 3)) : IsSymThreeQuotient N := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N),
    e.surjective.comp (QuotientGroup.mk'_surjective N), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    MulEquiv.coe_toMonoidHom]
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

private theorem natCard_centralizer_eq {G : Type*} [Group G] {z : G} {Q : Subgroup G}
    (hQH : Q ≤ Subgroup.centralizer ({z} : Set G)) (hQ16 : Nat.card Q = 16)
    (hsym : IsSymThreeQuotient (Q.subgroupOf (Subgroup.centralizer ({z} : Set G)))) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 96 := by
  obtain ⟨φ, hφ, hker⟩ := hsym
  have h := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ16] at h
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  omega

private theorem exists_sylow_two_involutions {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (T : Sylow 2 G)
    (hT : Nonempty ((T : Subgroup G) ≃* WreathedTwoGroup 2)) :
    ∃ P : Sylow 2 G, Q ≤ (P : Subgroup G) ∧ (involutionSet (P : Subgroup G)).ncard = 7 := by
  obtain ⟨P, hP⟩ := hQ2.exists_le_sylow
  refine ⟨P, hP, ?_⟩
  rw [ncard_involutionSet]
  exact wreathedTwoGroup_natCard_involutions_of_equiv ((Sylow.equiv P T).trans hT.some)

private theorem conjSubgroup_zpowers_eq {G : Type*} [Group G] {z g : G} (h : g * z * g⁻¹ = z) :
    conjSubgroup (Subgroup.zpowers z) g = Subgroup.zpowers z := by
  have hzk : ∀ k : ℤ, g * z ^ k * g⁻¹ = z ^ k := fun k => by rw [← conj_zpow, h]
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc z ^ k = g⁻¹ * (g * z ^ k * g⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hzk k, hk]
      _ = x := by group
  · rintro ⟨k, rfl⟩
    exact ⟨k, (hzk k).symm⟩

theorem u33_local_analysis {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hQ : Nonempty (CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G)) ≃*
      Z4StarQ8))
    (hsym : IsSymThreeQuotient ((CFSG.Open.quasithinGenFitting
      (Subgroup.centralizer ({z} : Set G))).subgroupOf (Subgroup.centralizer ({z} : Set G))))
    (hweak : ¬ IsWeaklyClosedIn (Subgroup.zpowers z)
      (CFSG.Open.quasithinGenFitting (Subgroup.centralizer ({z} : Set G))))
    (T : Sylow 2 G) (hT : Nonempty ((T : Subgroup G) ≃* WreathedTwoGroup 2)) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 96 ∧
      ∀ u : G, u * u = 1 → u ≠ 1 → ∃ g : G, g * z * g⁻¹ = u := by
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) with hHdef
  set Q : Subgroup G := CFSG.Open.quasithinGenFitting H with hQdef
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hQH : Q ≤ H := quasithinGenFitting_le H
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_quasithinGenFitting H
  have hQC : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := centralizer_quasithinGenFitting_le H
  have eQ : Q ≃* Z4StarQ8Model := hQ.some.trans z4StarQ8EquivModel
  have hQ16 : Nat.card Q = 16 := Z4StarQ8.natCard_of_equiv eQ
  have hH96 : Nat.card H = 96 := natCard_centralizer_eq hQH hQ16 hsym
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQ16]; norm_num)
  obtain ⟨P, hQP, hP7⟩ := exists_sylow_two_involutions hQ2 T hT
  have hconj : ∀ u : G, u * u = 1 → u ≠ 1 → ∃ g : G, g * u * g⁻¹ ∈ (P : Subgroup G) := by
    intro u hu2 hu1
    exact exists_conj_mem_sylow P (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1)
  have hweak' : ∃ g : G, g * z * g⁻¹ ∈ Q ∧ g * z * g⁻¹ ≠ z := by
    unfold IsWeaklyClosedIn at hweak
    push Not at hweak
    obtain ⟨g, hg, hne⟩ := hweak
    refine ⟨g⁻¹, ?_, ?_⟩
    · have hmem : g⁻¹ * z * g ∈ conjSubgroup (Subgroup.zpowers z) g := by
        rw [mem_conjSubgroup_iff]
        have : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
        rw [this]
        exact Subgroup.mem_zpowers z
      simpa using hg hmem
    · intro h
      apply hne
      apply conjSubgroup_zpowers_eq
      have h' : g⁻¹ * z * g = z := by simpa using h
      calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h']
        _ = z := by group
  refine ⟨hH96, involutions_conj_of_local hz2 hz1 hQH hQN hQC ?_ eQ hQP hP7 hconj hweak'⟩
  rw [hH96]
  norm_num

end CFSG.Quasithin
