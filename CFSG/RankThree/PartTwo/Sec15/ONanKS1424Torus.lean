module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Arith

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {n : ℕ} {T : Type} [Group T]

theorem exists_prime_dvd_qSubPi (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ qSubPi π (2 ^ n) := by
  cases π
  · exact exists_prime_dvd_pow_two_add hn
  · exact exists_prime_dvd_pow_two_sub hn

theorem eq_three_of_dvd {c : ℕ} (h9 : c ∣ 9) (h3 : 3 ∣ c) (hne : c ≠ 9) : c = 3 := by
  have hc : c ≤ 9 := Nat.le_of_dvd (by norm_num) h9
  interval_cases c <;> omega

theorem torus_subgroup (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) (M : LModel π 2 n K T)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrN : r ∣ qSubPi π (2 ^ n)) {y : GL (Fin 3) K}
    (eA : ↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) ≃*
      Multiplicative (ZMod (qSubPi π (2 ^ n))) × Multiplicative (ZMod (qSubPi π (2 ^ n)))) :
    ∃ Ē : Subgroup T, CFSG.Assembly.IsElemAbelian r Ē ∧ Nat.card Ē = r ^ 2 ∧
      (∀ t ∈ Ē, ∃ h : ↥(slPi π 3 (2 ^ n) K), (h : GL (Fin 3) K) ∈ Subgroup.centralizer
        ({y} : Set (GL (Fin 3) K)) ∧ M.μ h = t) ∧
      (∀ ε : ↥(slPi π 3 (2 ^ n) K), (ε : GL (Fin 3) K) ∈ centMod (slPi π 3 (2 ^ n) K) y →
        ∀ t ∈ Ē, M.μ ε * t * (M.μ ε)⁻¹ ∈ Ē) := by
  have := hK.finite
  have hN0 : NeZero (qSubPi π (2 ^ n)) := ⟨qSubPi_ne_zero hK hq⟩
  set N := qSubPi π (2 ^ n) with hN
  set A := slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) with hA
  have hAc : ∀ u v : ↥A, u * v = v * u := fun u v =>
    eA.injective (by rw [map_mul, map_mul, mul_comm])
  have hG₁ : Nat.card (Multiplicative (ZMod N)) = N := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let K₁ : Subgroup (Multiplicative (ZMod N)) :=
    (powMonoidHom r : Multiplicative (ZMod N) →* Multiplicative (ZMod N)).ker
  have hK₁ : Nat.card K₁ = r := by
    have := IsCyclic.card_powMonoidHom_ker (Multiplicative (ZMod N)) r
    rw [hG₁] at this
    rw [this]
    exact Nat.gcd_eq_right hrN
  have hmemK₁ : ∀ x : Multiplicative (ZMod N), x ∈ K₁ ↔ x ^ r = 1 := fun x => Iff.rfl
  let Gr : Subgroup (Multiplicative (ZMod N) × Multiplicative (ZMod N)) := K₁.prod K₁
  have hGr : Nat.card Gr = r * r := by
    rw [Nat.card_congr (Subgroup.prodEquiv K₁ K₁).toEquiv, Nat.card_prod, hK₁]
  let Hr : Subgroup ↥A := Gr.map eA.symm.toMonoidHom
  have hHr : ∀ h : ↥A, h ∈ Hr ↔ h ^ r = 1 := by
    intro h
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hg
      have e1 : g.1 ^ r = 1 := (hmemK₁ _).mp h1
      have e2 : g.2 ^ r = 1 := (hmemK₁ _).mp h2
      have : g ^ r = 1 := Prod.ext e1 e2
      change eA.symm g ^ r = 1
      rw [← map_pow, this, map_one]
    · intro h1
      refine ⟨eA h, Subgroup.mem_prod.mpr ⟨?_, ?_⟩, by simp⟩
      · have : (eA h) ^ r = 1 := by rw [← map_pow, h1, map_one]
        have e1 := congrArg Prod.fst this
        exact (hmemK₁ _).mpr (by simpa using e1)
      · have : (eA h) ^ r = 1 := by rw [← map_pow, h1, map_one]
        have e1 := congrArg Prod.snd this
        exact (hmemK₁ _).mpr (by simpa using e1)
  have hHrcard : Nat.card Hr = r * r := by
    rw [← hGr]
    exact Subgroup.card_map_of_injective eA.symm.injective
  let ι : ↥A →* T := M.μ.comp (Subgroup.inclusion (inf_le_left : A ≤ slPi π 3 (2 ^ n) K))
  have hι : ∀ h : ↥Hr, ι.comp Hr.subtype h = 1 → h = 1 := by
    intro h h1
    by_contra hne
    have hh : (h : ↥A) ^ r = 1 := (hHr _).mp h.2
    refine μ_ne_one hK M hr (by omega) (u := Subgroup.inclusion (inf_le_left : A ≤ _) h)
      ?_ ?_ h1
    · rw [← map_pow, hh, map_one]
    · intro h0
      apply hne
      apply Subtype.ext
      have := Subgroup.inclusion_injective (inf_le_left : A ≤ slPi π 3 (2 ^ n) K)
        (h0.trans (map_one _).symm)
      exact this
  have hinj : Function.Injective (ι.comp Hr.subtype) :=
    (injective_iff_map_eq_one _).mpr hι
  refine ⟨(ι.comp Hr.subtype).range, ⟨⟨⟨fun t₁ t₂ => ?_⟩⟩, fun t ht => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨x₁, hx₁⟩ := t₁.2
    obtain ⟨x₂, hx₂⟩ := t₂.2
    apply Subtype.ext
    show (t₁ : T) * t₂ = t₂ * t₁
    rw [← hx₁, ← hx₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc x₁.1 x₂.1)
  · obtain ⟨x, rfl⟩ := ht
    rw [← map_pow]
    have : x ^ r = 1 := Subtype.ext ((hHr _).mp x.2)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hHrcard, sq]
  · rintro t ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion (inf_le_left : A ≤ slPi π 3 (2 ^ n) K) x.1, x.1.2.2, rfl⟩
  · intro ε hε t ht
    obtain ⟨x, rfl⟩ := ht
    have hg := mul_mem_of_mem_centMod hε x.1.2
    set h' : ↥A := ⟨(ε : GL (Fin 3) K) * (x.1 : GL (Fin 3) K) * (ε : GL (Fin 3) K)⁻¹, hg⟩
      with hh'
    have hh'r : h' ^ r = 1 := by
      apply Subtype.ext
      have hx : (x.1 : GL (Fin 3) K) ^ r = 1 := by
        have : (x : ↥A) ^ r = 1 := (hHr _).mp x.2
        exact congrArg Subtype.val this
      change ((ε : GL (Fin 3) K) * (x.1 : GL (Fin 3) K) * (ε : GL (Fin 3) K)⁻¹) ^ r = 1
      rw [conj_pow, hx]
      group
    refine ⟨⟨h', (hHr _).mpr hh'r⟩, ?_⟩
    change M.μ (Subgroup.inclusion (inf_le_left : A ≤ slPi π 3 (2 ^ n) K) h') =
      M.μ ε * M.μ (Subgroup.inclusion (inf_le_left : A ≤ slPi π 3 (2 ^ n) K) x.1) *
        (M.μ ε)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem exists_noncommuting_lifts (hn : 4 ≤ n) (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (M : LModel π 2 n K T) {E : Subgroup T} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hC : ∀ t : T, (∀ e ∈ E, t * e = e * t) → t ∈ E) :
    ∃ a b : ↥(slPi π 3 (2 ^ n) K), M.μ a ∈ E ∧ M.μ b ∈ E ∧ a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  obtain ⟨r, hr, hr3, hrN⟩ := exists_prime_dvd_qSubPi (π := π) hn
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hE.2
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE9
    omega
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  obtain ⟨a, ha⟩ := M.surjective x₀
  have haE : M.μ a ∈ E := ha ▸ hx₀
  have haZ : (a : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := fun h =>
    hx₀1 (by rw [← ha]; exact (M.ker_iff a).mpr h)
  have ha3 : (a : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
    have : M.μ (a ^ 3) = 1 := by
      rw [map_pow]
      exact hE3 _ haE
    exact (M.ker_iff (a ^ 3)).mp this
  obtain ⟨u, huL, hur, hu1, huc⟩ := exists_centralizing_pElement hK hq hr hrN a.2 haZ ha3
    (S := {e | ∃ ε : ↥(slPi π 3 (2 ^ n) K), (ε : GL (Fin 3) K) = e ∧ M.μ ε ∈ E})
    (by rintro _ ⟨ε, rfl, -⟩; exact ε.2)
    (by
      rintro _ ⟨ε, rfl, hε⟩
      exact congrArg Subtype.val (hno ε a hε haE))
  set u' : ↥(slPi π 3 (2 ^ n) K) := ⟨u, huL⟩ with hu'
  have hu'r : u' ^ r = 1 := Subtype.ext hur
  have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hμ1 := μ_ne_one hK M hr (by omega) hu'r hu'1
  have hμE : M.μ u' ∈ E := by
    apply hC
    intro e he
    obtain ⟨ε, rfl⟩ := M.surjective e
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (huc ε ⟨ε, rfl, he⟩)
  have hord : orderOf (M.μ u') = r := by
    have : Fact r.Prime := ⟨hr⟩
    refine orderOf_eq_prime ?_ hμ1
    rw [← map_pow, hu'r, map_one]
  have hdvd : r ∣ 9 := by
    have := Subgroup.orderOf_dvd_natCard E hμE
    rwa [hord, hE9] at this
  have : r ∣ 3 := hr.dvd_of_dvd_pow (show r ∣ 3 ^ 2 by norm_num; exact hdvd)
  have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp this
  omega

theorem torus_model (hn : 4 ≤ n) (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (M : LModel π 2 n K T) {E : Subgroup T} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hC : ∀ t : T, (∀ e ∈ E, t * e = e * t) → t ∈ E) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ ∃ Ē : Subgroup T, CFSG.Assembly.IsElemAbelian r Ē ∧
      Nat.card Ē = r ^ 2 ∧ E ≤ Subgroup.normalizer (Ē : Set T) ∧ ⁅Ē, E⁆ = Ē ∧
      Nat.card (E ⊓ Subgroup.centralizer (Ē : Set T) : Subgroup T) = 3 := by
  have := hK.finite
  have : Finite T := Finite.of_surjective M.μ M.surjective
  obtain ⟨r, hr, hr3, hrN⟩ := exists_prime_dvd_qSubPi (π := π) hn
  obtain ⟨a, b, haE, hbE, hab⟩ := exists_noncommuting_lifts hn hK hq M hE hE9 hC
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hE.2
  have haZ : (a : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := fun h =>
    hab (Subtype.ext (commute_of_mem_statedScalars h (b : GL (Fin 3) K)).symm)
  have ha3 : (a : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
    have : M.μ (a ^ 3) = 1 := by
      rw [map_pow]
      exact hE3 _ haE
    exact (M.ker_iff (a ^ 3)).mp this
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := type_data hK hq a.2 haZ ha3
  have hzc : ∀ g : GL (Fin 3) K, g * z = z * g := fun g => commute_of_mem_statedScalars hz g
  obtain ⟨⟨eA⟩, -⟩ : (Nonempty (↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer
      ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K))) ≃* Multiplicative
        (ZMod (qSubPi π (2 ^ n))) × Multiplicative (ZMod (qSubPi π (2 ^ n)))) ∧
      (slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K))
        ).relIndex (centMod (slPi π 3 (2 ^ n) K) ((a : GL (Fin 3) K) * z)) = 3) := by
    rcases hy with h | ⟨-, hcent⟩
    · exact h
    · exfalso
      have hbc := mem_centMod_of_commute hK M (a := a) (ε := b) hz (hEc _ hbE _ haE)
      rw [hcent] at hbc
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hbc.2
      apply hab
      apply Subtype.ext
      show (a : GL (Fin 3) K) * b = b * a
      have h2 : ((a : GL (Fin 3) K) * b) * z = ((b : GL (Fin 3) K) * a) * z := by
        calc ((a : GL (Fin 3) K) * b) * z = a * (b * z) := by rw [mul_assoc]
          _ = a * (z * b) := by rw [hzc b]
          _ = (a * z) * b := by rw [mul_assoc]
          _ = b * (a * z) := h1.symm
          _ = (b * a) * z := by rw [mul_assoc]
      exact mul_right_cancel h2
  obtain ⟨Ē, hĒe, hĒcard, hĒlift, hĒconj⟩ := torus_subgroup hK hq M hr hr3 hrN eA
  have hconj : ∀ e ∈ E, ∀ t ∈ Ē, e * t * e⁻¹ ∈ Ē := by
    intro e he t ht
    obtain ⟨ε, rfl⟩ := M.surjective e
    exact hĒconj ε (mem_centMod_of_commute hK M hz (hEc _ he _ haE)) t ht
  have hnorm : E ≤ Subgroup.normalizer (Ē : Set T) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hconj e he t ht, fun ht => ?_⟩
    have := hconj e⁻¹ (inv_mem he) _ ht
    simpa [mul_assoc] using this
  have hEĒ : ∀ w ∈ E, w ∈ Ē → w = 1 := by
    intro w hwE hwĒ
    have h1 : orderOf w ∣ 9 := hE9 ▸ Subgroup.orderOf_dvd_natCard E hwE
    have h2 : orderOf w ∣ r := orderOf_dvd_of_pow_eq_one (hĒe.2 w hwĒ)
    have hcop : Nat.Coprime 9 r := by
      have : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
      simpa using Nat.Coprime.pow_left 2 this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hĒx : ∀ t ∈ Ē, t * M.μ a = M.μ a * t := by
    intro t ht
    obtain ⟨h, hh, rfl⟩ := hĒlift t ht
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hh
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (h : GL (Fin 3) K) * a = a * h
    have h2 : ((h : GL (Fin 3) K) * a) * z = (a * (h : GL (Fin 3) K)) * z := by
      calc ((h : GL (Fin 3) K) * a) * z = h * (a * z) := by rw [mul_assoc]
        _ = (a * z) * h := h1
        _ = a * (z * h) := by rw [mul_assoc]
        _ = a * (h * z) := by rw [hzc h]
        _ = (a * h) * z := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hxE : M.μ a ∈ E := haE
  have hx1 : M.μ a ≠ 1 := fun h => haZ ((M.ker_iff a).mp h)
  have hx3 : M.μ a ^ 3 = 1 := hE3 _ haE
  have hne' : M.μ b ∉ Subgroup.zpowers (M.μ a) := by
    rintro ⟨k, hk⟩
    apply hab
    have hk' : M.μ a ^ k = M.μ b := hk
    have h1 : M.μ (b * (a ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk']
      group
    obtain ⟨c, hc⟩ := (M.ker_iff _).mp h1
    have hc' : GeneralLinearGroup.scalar (Fin 3) c =
        (b : GL (Fin 3) K) * ((a : GL (Fin 3) K) ^ k)⁻¹ := by
      rw [hc]
      simp
    have hb' : (b : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c * (a : GL (Fin 3) K) ^ k := by
      rw [hc']
      group
    apply Subtype.ext
    show (a : GL (Fin 3) K) * b = b * a
    rw [hb']
    have h2 : (a : GL (Fin 3) K) * (a : GL (Fin 3) K) ^ k = (a : GL (Fin 3) K) ^ k * a :=
      (Commute.refl (a : GL (Fin 3) K)).zpow_right k |>.eq
    have h3 : (a : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c =
        GeneralLinearGroup.scalar (Fin 3) c * a :=
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (a : GL (Fin 3) K)).eq
    calc (a : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) c * (a : GL (Fin 3) K) ^ k) =
        (a * GeneralLinearGroup.scalar (Fin 3) c) * (a : GL (Fin 3) K) ^ k := by rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin 3) c * a) * (a : GL (Fin 3) K) ^ k := by rw [h3]
      _ = GeneralLinearGroup.scalar (Fin 3) c * (a * (a : GL (Fin 3) K) ^ k) := by rw [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) c * ((a : GL (Fin 3) K) ^ k * a) := by rw [h2]
      _ = (GeneralLinearGroup.scalar (Fin 3) c * (a : GL (Fin 3) K) ^ k) * a := by rw [mul_assoc]
  have hord_x : orderOf (M.μ a) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hF : Subgroup.zpowers (M.μ a) ⊔ Subgroup.zpowers (M.μ b) = E := by
    set F := Subgroup.zpowers (M.μ a) ⊔ Subgroup.zpowers (M.μ b) with hFdef
    have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr haE) (Subgroup.zpowers_le.mpr hbE)
    have hdvd9 : Nat.card F ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hFE
    have hdvd3 : 3 ∣ Nat.card F := by
      have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers (M.μ a) ≤ F)
      rwa [Nat.card_zpowers, hord_x] at this
    have hF9 : Nat.card F = 9 := by
      by_contra hne9
      have hF3 : Nat.card F = 3 := eq_three_of_dvd hdvd9 hdvd3 hne9
      have hle : Subgroup.zpowers (M.μ a) ≤ F := le_sup_left
      have heq : Subgroup.zpowers (M.μ a) = F :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord_x, hF3])
      apply hne'
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hE9, hF9])
  have hcommE : ∀ v : T, v * M.μ a = M.μ a * v → v * M.μ b = M.μ b * v →
      ∀ t ∈ E, v * t = t * v := by
    intro v hva hvb t ht
    rw [← hF] at ht
    have hle : Subgroup.zpowers (M.μ a) ⊔ Subgroup.zpowers (M.μ b) ≤
        Subgroup.centralizer ({v} : Set T) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hva.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hvb.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ht)).symm
  refine ⟨r, hr, hr3, Ē, hĒe, hĒcard, hnorm, ?_, ?_⟩
  ·
    apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm)
    let φ : ↥Ē → ↥Ē := fun v => ⟨(v : T) * M.μ b * (v : T)⁻¹ * (M.μ b)⁻¹, by
      have := Ē.mul_mem v.2 (hconj _ hbE _ (Ē.inv_mem v.2))
      simpa [mul_assoc] using this⟩
    have hφ : Function.Injective φ := by
      intro v v' hvv
      have h1 : (v : T) * M.μ b * (v : T)⁻¹ * (M.μ b)⁻¹ =
          (v' : T) * M.μ b * (v' : T)⁻¹ * (M.μ b)⁻¹ := congrArg Subtype.val hvv
      set w : T := (v' : T)⁻¹ * v with hw
      have hwĒ : w ∈ Ē := Ē.mul_mem (Ē.inv_mem v'.2) v.2
      have hwb : w * M.μ b = M.μ b * w := by
        have h2 : (v : T) * M.μ b * (v : T)⁻¹ = (v' : T) * M.μ b * (v' : T)⁻¹ :=
          mul_right_cancel h1
        calc w * M.μ b = (v' : T)⁻¹ * ((v : T) * M.μ b * (v : T)⁻¹) * (v : T) := by
              rw [hw]
              group
          _ = (v' : T)⁻¹ * ((v' : T) * M.μ b * (v' : T)⁻¹) * (v : T) := by rw [h2]
          _ = M.μ b * w := by
              rw [hw]
              group
      have hwE : w ∈ E := hC w (hcommE w (hĒx w hwĒ) hwb)
      have hw1 : w = 1 := hEĒ w hwE hwĒ
      apply Subtype.ext
      rw [hw, inv_mul_eq_one] at hw1
      exact hw1.symm
    have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
    intro w hw
    obtain ⟨v, hv⟩ := hφs ⟨w, hw⟩
    have h1 : (v : T) * M.μ b * (v : T)⁻¹ * (M.μ b)⁻¹ = w := congrArg Subtype.val hv
    rw [← h1]
    exact Subgroup.commutator_mem_commutator v.2 hbE
  ·
    set D : Subgroup T := E ⊓ Subgroup.centralizer (Ē : Set T) with hD
    have hxD : M.μ a ∈ D := by
      refine ⟨haE, Subgroup.mem_centralizer_iff.mpr fun t ht => hĒx t ht⟩
    have hdvd9 : Nat.card D ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvd3 : 3 ∣ Nat.card D := by
      have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxD)
      rwa [Nat.card_zpowers, hord_x] at this
    have hD9 : Nat.card D ≠ 9 := by
      intro h9
      have hDE : D = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hE9, h9])
      have hEĒc : ∀ t ∈ Ē, ∀ e ∈ E, t * e = e * t := by
        intro t ht e he
        have : e ∈ D := hDE ▸ he
        exact Subgroup.mem_centralizer_iff.mp this.2 t ht
      have hĒ1 : ∀ t ∈ Ē, t = 1 := fun t ht => hEĒ t (hC t (hEĒc t ht)) ht
      have hbot : Ē = ⊥ := (Subgroup.eq_bot_iff_forall Ē).mpr hĒ1
      rw [hbot, Subgroup.card_bot] at hĒcard
      have : 4 ≤ r ^ 2 := by nlinarith
      omega
    exact eq_three_of_dvd hdvd9 hdvd3 hD9

end CFSG.RankThree.PartTwo.Sec15.KS1424
