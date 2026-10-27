module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Central

variable {G : Type*} [Group G] {u v z : G}

theorem mul_mul_central (hzc : ∀ w : G, z * w = w * z) (a b : G) : a * (z * b) = z * (a * b) := by
  rw [← mul_assoc, ← hzc a, mul_assoc]

theorem mul_pow_comm_central (hzc : ∀ w : G, z * w = w * z) (huv : u * v = z * (v * u)) (k : ℕ) :
    u * v ^ k = z ^ k * (v ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc u * v ^ (k + 1) = (u * v ^ k) * v := by rw [pow_succ, mul_assoc]
      _ = z ^ k * (v ^ k * u) * v := by rw [ih]
      _ = z ^ k * (v ^ k * (u * v)) := by simp only [mul_assoc]
      _ = z ^ k * (v ^ k * (z * (v * u))) := by rw [huv]
      _ = z ^ k * (z * (v ^ k * (v * u))) := by rw [mul_mul_central hzc]
      _ = z ^ (k + 1) * (v ^ (k + 1) * u) := by
        rw [pow_succ, pow_succ]
        simp only [mul_assoc]

theorem mul_pow_central (hzc : ∀ w : G, z * w = w * z) (huv : u * v = z * (v * u)) (n : ℕ) :
    (u * v) ^ n = z⁻¹ ^ n.choose 2 * (u ^ n * v ^ n) := by
  have hcz : ∀ w : G, Commute z w := fun w => hzc w
  have hpow : ∀ (m : ℕ) (w : G), z⁻¹ ^ m * w = w * z⁻¹ ^ m := fun m w =>
    ((hcz w).inv_left.pow_left m).eq
  have hv : ∀ k : ℕ, v ^ k * u = z⁻¹ ^ k * (u * v ^ k) := fun k => by
    have h := mul_pow_comm_central hzc huv k
    rw [inv_pow]
    exact eq_inv_mul_iff_mul_eq.mpr h.symm
  induction n with
  | zero => simp
  | succ n ih =>
    calc (u * v) ^ (n + 1) = (u * v) ^ n * (u * v) := pow_succ _ _
      _ = z⁻¹ ^ n.choose 2 * (u ^ n * v ^ n) * (u * v) := by rw [ih]
      _ = z⁻¹ ^ n.choose 2 * (u ^ n * (v ^ n * u) * v) := by simp only [mul_assoc]
      _ = z⁻¹ ^ n.choose 2 * (u ^ n * (z⁻¹ ^ n * (u * v ^ n)) * v) := by rw [hv n]
      _ = z⁻¹ ^ n.choose 2 * (z⁻¹ ^ n * (u ^ n * (u * v ^ n)) * v) := by
        rw [mul_mul_central (hpow n)]
      _ = z⁻¹ ^ (n + 1).choose 2 * (u ^ (n + 1) * v ^ (n + 1)) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm n, pow_add]
        simp only [mul_assoc, pow_succ]

theorem mul_pow_three_of_commutator_central (hz : u * v * u⁻¹ * v⁻¹ = z)
    (hzc : ∀ w : G, z * w = w * z) (hz3 : z ^ 3 = 1) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have huv : u * v = z * (v * u) := by rw [← hz]; group
  rw [mul_pow_central hzc huv 3]
  have : (3 : ℕ).choose 2 = 3 := by decide
  rw [this, inv_pow, hz3, inv_one, one_mul]

end Central

structure HatData (L : Type) [Group L] : Prop where
  out : ¬ 3 ∣ Nat.card (Outer L)
  card : ∃ m : ℕ, Nat.card L = 9 * m ∧ ¬ 3 ∣ m
  irr : ∃ P : Subgroup L, Nat.card P = 9 ∧ CFSG.Open.IsElemAbelian 3 P ∧
    ∃ n ∈ Subgroup.normalizer (P : Set L), ∀ Λ : Subgroup L, Λ ≤ P → Nat.card Λ = 3 →
      Λ.map (MulAut.conj n).toMonoidHom ≠ Λ

theorem exists_conj_of_card_nine {L : Type} [Group L] [Finite L] {m : ℕ} (hLm : Nat.card L = 9 * m)
    (hm3 : ¬ 3 ∣ m) {P₀ P : Subgroup L} (h₀ : Nat.card P₀ = 9) (h : Nat.card P = 9) :
    ∃ g : L, P = P₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := L)
    omega
  have hf : (Nat.card L).factorization 3 = 2 := by
    rw [hLm, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm3, add_zero,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hc₀ : Nat.card P₀ = 3 ^ (Nat.card L).factorization 3 := by rw [h₀, hf]; norm_num
  have hc : Nat.card P = 3 ^ (Nat.card L).factorization 3 := by rw [h, hf]; norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L (Sylow.ofCard P₀ hc₀) (Sylow.ofCard P hc)
  refine ⟨g, ?_⟩
  have h1 := congrArg (fun Q : Sylow 3 L => (Q : Subgroup L)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h1
  ext x
  rw [← h1, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  simp [MulAut.conj_apply]

theorem mem_map_conj_iff {G : Type*} [Group G] (P : Subgroup G) (g x : G) :
    x ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem HatData.irr_all {L : Type} [Group L] [Finite L] (hL : HatData L) {P : Subgroup L}
    (hP : Nat.card P = 9) : CFSG.Open.IsElemAbelian 3 P ∧
      ∃ n ∈ Subgroup.normalizer (P : Set L), ∀ Λ : Subgroup L, Λ ≤ P → Nat.card Λ = 3 →
        Λ.map (MulAut.conj n).toMonoidHom ≠ Λ := by
  obtain ⟨m, hLm, hm3⟩ := hL.card
  obtain ⟨P₀, hP₀, hP₀el, n₀, hn₀, hirr⟩ := hL.irr
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine hLm hm3 hP₀ hP
  subst hg
  refine ⟨CFSG.SectionRank.isElemAbelian_map hP₀el _, g * n₀ * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hn₀ ⊢
    intro x
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have h1 : g⁻¹ * (g * n₀ * g⁻¹ * x * (g * n₀ * g⁻¹)⁻¹) * g = n₀ * (g⁻¹ * x * g) * n₀⁻¹ := by
      group
    rw [h1]
    exact hn₀ _
  · intro Λ hΛP hΛ heq
    have hΛ' : Λ.map (MulAut.conj g⁻¹).toMonoidHom ≤ P₀ := by
      rintro _ ⟨y, hy, rfl⟩
      have := (mem_map_conj_iff P₀ g y).1 (hΛP hy)
      simpa [MulAut.conj_apply] using this
    have hc' : Nat.card (Λ.map (MulAut.conj g⁻¹).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hΛ]
    apply hirr _ hΛ' hc'
    rw [Subgroup.map_map]
    have : (MulAut.conj n₀).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj (g * n₀ * g⁻¹)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this, ← Subgroup.map_map, heq]

theorem card_map_mk_mul {S : Type} [Group S] [Finite S] (Z : Subgroup S) [Z.Normal]
    (H : Subgroup S) (hZH : Z ≤ H) :
    Nat.card (H.map (QuotientGroup.mk' Z)) * Nat.card Z = Nat.card H := by
  let φ : H →* S ⧸ Z := (QuotientGroup.mk' Z).comp H.subtype
  have hker : φ.ker = Z.subgroupOf H := by
    ext u
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : φ.range = H.map (QuotientGroup.mk' Z) := by
    simp [φ, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, hrange] at h1
  have h2 : Nat.card (Z.subgroupOf H) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  rw [h2] at h1
  rw [mul_comm]
  exact h1

theorem no_order_nine {S : Type} [Group S] [Finite S] (hZ : Nat.card (Subgroup.center S) = 3)
    (hL : HatData (S ⧸ Subgroup.center S)) {l : S} (hl3 : l ^ 3 ∈ Subgroup.center S)
    (hl : l ^ 3 ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center S with hZdef
  set π : S →* S ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hl9 : l ^ 9 = 1 := by
    have := hZ3 _ hl3
    rw [← pow_mul] at this
    exact this
  obtain ⟨m, hLm, hm3⟩ := hL.card
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := S ⧸ Z)
    omega
  have hS : Nat.card S = 27 * m := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hLm, hZ]
    ring
  have hfS : (Nat.card S).factorization 3 = 3 := by
    rw [hS, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm3, add_zero,
      show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hP3 : IsPGroup 3 (Subgroup.zpowers l) := by
    intro g
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨2, Subtype.ext ?_⟩
    change (g : S) ^ 3 ^ 2 = 1
    rw [← ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hl9]
  obtain ⟨P, hlP⟩ := hP3.exists_le_sylow
  have hl_mem : l ∈ (P : Subgroup S) := hlP (Subgroup.mem_zpowers l)
  have hZP : Z ≤ (P : Subgroup S) := by
    have hZp : IsPGroup 3 Z := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [hZ]; norm_num
    have hsup := IsPGroup.to_sup_of_normal_right P.isPGroup' hZp
    have := P.3 hsup le_sup_left
    rw [← this]
    exact le_sup_right
  have hP27 : Nat.card (P : Subgroup S) = 27 := by
    rw [Sylow.card_eq_multiplicity, hfS]
    norm_num
  set Pb : Subgroup (S ⧸ Z) := (P : Subgroup S).map π with hPb
  have hPb9 : Nat.card Pb = 9 := by
    have h1 : Nat.card Pb * Nat.card Z = Nat.card (P : Subgroup S) :=
      card_map_mk_mul Z (P : Subgroup S) hZP
    rw [hZ, hP27] at h1
    omega
  obtain ⟨hPbel, nb, hnb, hirr⟩ := hL.irr_all hPb9
  obtain ⟨n, hn⟩ := hπs nb
  have hmemP : ∀ x : S, π x ∈ Pb → x ∈ (P : Subgroup S) := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hx
    have h1 : u⁻¹ * x ∈ Z := QuotientGroup.eq.1 hux
    have : x = u * (u⁻¹ * x) := by group
    rw [this]
    exact mul_mem hu (hZP h1)
  have hcommP : ∀ u v : S, u ∈ (P : Subgroup S) → v ∈ (P : Subgroup S) →
      u * v * u⁻¹ * v⁻¹ ∈ Z := by
    intro u v hu hv
    have hcomm : π u * π v = π v * π u := congrArg Subtype.val
      (hPbel.1.is_comm.comm ⟨π u, Subgroup.mem_map_of_mem _ hu⟩ ⟨π v, Subgroup.mem_map_of_mem _ hv⟩)
    rw [← QuotientGroup.eq_one_iff]
    change π (u * v * u⁻¹ * v⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hcube_mem : ∀ u : (P : Subgroup S), (u : S) ^ 3 ∈ Z := by
    intro u
    rw [← QuotientGroup.eq_one_iff]
    change π ((u : S) ^ 3) = 1
    rw [map_pow]
    exact hPbel.2 _ (Subgroup.mem_map_of_mem _ u.2)
  let cube : (P : Subgroup S) →* Z := MonoidHom.mk' (fun u => ⟨(u : S) ^ 3, hcube_mem u⟩) (by
    intro u v
    apply Subtype.ext
    change ((u * v : (P : Subgroup S)) : S) ^ 3 = (u : S) ^ 3 * (v : S) ^ 3
    rw [Subgroup.coe_mul]
    have hz := hcommP u v u.2 v.2
    exact mul_pow_three_of_commutator_central rfl
      (fun w => (Subgroup.mem_center_iff.1 hz w).symm) (hZ3 _ hz))
  have hcube_l : cube ⟨l, hl_mem⟩ ≠ 1 := by
    intro h
    apply hl
    exact congrArg Subtype.val h
  have hrange3 : Nat.card cube.range = 3 := by
    have hdvd : Nat.card cube.range ∣ Nat.card Z := by
      rw [show Nat.card Z = Nat.card (⊤ : Subgroup Z) from (Subgroup.card_top).symm]
      exact Subgroup.card_dvd_of_le le_top
    rw [hZ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exfalso
      apply hcube_l
      have h1 : cube.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h
      have : cube ⟨l, hl_mem⟩ ∈ cube.range := ⟨_, rfl⟩
      rw [h1] at this
      exact this
    · exact h
  have hker9 : Nat.card cube.ker = 9 := by
    have h1 := Subgroup.card_mul_index cube.ker
    rw [Subgroup.index_ker, hrange3, hP27] at h1
    omega
  set Ω : Subgroup S := cube.ker.map (P : Subgroup S).subtype with hΩ
  have hΩ9 : Nat.card Ω = 9 := by
    rw [hΩ, Subgroup.card_map_of_injective (P : Subgroup S).subtype_injective, hker9]
  have hΩP : Ω ≤ (P : Subgroup S) := Subgroup.map_subtype_le _
  have hmemΩ : ∀ x : S, x ∈ Ω ↔ x ∈ (P : Subgroup S) ∧ x ^ 3 = 1 := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 hu)⟩
    · rintro ⟨hx, hx3⟩
      exact ⟨⟨x, hx⟩, (MonoidHom.mem_ker).2 (Subtype.ext hx3), rfl⟩
  have hZΩ : Z ≤ Ω := fun z hz => (hmemΩ z).2 ⟨hZP hz, hZ3 z hz⟩
  set Ωb : Subgroup (S ⧸ Z) := Ω.map π with hΩb
  have hΩb3 : Nat.card Ωb = 3 := by
    have h1 : Nat.card Ωb * Nat.card Z = Nat.card Ω := card_map_mk_mul Z Ω hZΩ
    rw [hZ, hΩ9] at h1
    omega
  have hΩbP : Ωb ≤ Pb := Subgroup.map_mono hΩP
  have hnP : ∀ u ∈ (P : Subgroup S), n * u * n⁻¹ ∈ (P : Subgroup S) := by
    intro u hu
    apply hmemP
    have h1 : π (n * u * n⁻¹) = nb * π u * nb⁻¹ := by
      rw [map_mul, map_mul, map_inv, hn]
    rw [h1]
    exact ((Subgroup.mem_normalizer_iff.1 hnb) (π u)).1 (Subgroup.mem_map_of_mem _ hu)
  have hinv : Ωb.map (MulAut.conj nb).toMonoidHom ≤ Ωb := by
    rintro _ ⟨x, ⟨ω, hω, rfl⟩, rfl⟩
    refine ⟨n * ω * n⁻¹, (hmemΩ _).2 ⟨hnP ω (hΩP hω), ?_⟩, ?_⟩
    · have := ((hmemΩ ω).1 hω).2
      rw [conj_pow, this]
      group
    · simp [MulAut.conj_apply, hn]
  have heq : Ωb.map (MulAut.conj nb).toMonoidHom = Ωb := by
    have hc : Nat.card (Ωb.map (MulAut.conj nb).toMonoidHom) = Nat.card Ωb :=
      Subgroup.card_map_of_injective (f := (MulAut.conj nb).toMonoidHom) (MulAut.conj nb).injective
    exact Subgroup.eq_of_le_of_card_ge hinv hc.ge
  exact hirr Ωb hΩbP hΩb3 heq

end A318P

end CFSG.Quasithin
