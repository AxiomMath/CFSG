module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26b
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26
public import CFSG.Quasithin.Vol2.Ch12Sec6L26k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace S126C

variable {Q : Type} [Group Q] [Finite Q]

theorem false_of_e27 (hsq : CFSG.IsStronglyQuasithin Q) {E : Subgroup Q} (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {c : Q} (hc3 : c ^ 3 = 1) (hcE : c ∉ E)
    (hcomm : ∀ e ∈ E, c * e = e * c) : False := by
  classical
  have hc1 : c ≠ 1 := fun h => hcE (h ▸ E.one_mem)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hαβ : ∀ (a : ↥E) (z : ↥(Subgroup.zpowers c)),
      Commute (E.subtype a) ((Subgroup.zpowers c).subtype z) := by
    intro a z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.2
    show (a : Q) * z = z * a
    rw [← hn]
    exact ((Commute.zpow_left (hcomm a a.2) n).eq).symm
  let Φ := E.subtype.noncommCoprod (Subgroup.zpowers c).subtype hαβ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h1
    have h1' : (a : Q) * z = 1 := h1
    have hzE : (z : Q) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right h1']
      exact E.inv_mem a.2
    by_cases hz1 : (z : Q) = 1
    · have ha1 : (a : Q) = 1 := by rw [hz1, mul_one] at h1'; exact h1'
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext hz1)
    · exfalso
      have hz3 : (z : Q) ^ 3 = 1 := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.2
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
      have hzo : orderOf (z : Q) = 3 := orderOf_eq_prime hz3 hz1
      have hle : Subgroup.zpowers (z : Q) ≤ Subgroup.zpowers c :=
        (Subgroup.zpowers_le).mpr z.2
      have heq : Subgroup.zpowers (z : Q) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hord])
      have hcz : c ∈ Subgroup.zpowers (z : Q) := by rw [heq]; exact Subgroup.mem_zpowers c
      exact hcE ((Subgroup.zpowers_le.mpr hzE) hcz)
  have : IsMulCommutative ↥E := hE.1
  have hcomm3 : ∀ x y : ↥E × ↥(Subgroup.zpowers c), x * y = y * x := by
    rintro ⟨a, z⟩ ⟨a', z'⟩
    refine Prod.ext (hE.1.is_comm.comm a a') ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z'.2
    apply Subtype.ext
    show (z : Q) * z' = z' * z
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self c m n).eq
  have hpow3 : ∀ x : ↥E × ↥(Subgroup.zpowers c), x ^ 3 = 1 := by
    rintro ⟨a, z⟩
    refine Prod.ext (Subtype.ext (by simpa using hE.2 _ a.2)) ?_
    have hc3' : Nat.card ↥(Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hord]
    show z ^ 3 = 1
    rw [← hc3']
    exact pow_card_eq_one'
  have h27 : Nat.card (↥E × ↥(Subgroup.zpowers c)) = 3 ^ 3 := by
    rw [Nat.card_prod, hE9, Nat.card_zpowers, hord]
    norm_num
  have hrk := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm3 hpow3 h27 Φ
    hinj (H := ⊤) le_top
  have h2 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsq) 3 Nat.prime_three (by norm_num)
  omega

omit [Finite Q] in
theorem conjK_apply {K : Subgroup Q} {g : Q} (hg : g ∈ Subgroup.normalizer (K : Set Q)) (x : ↥K) :
    ((K.normalizerMonoidHom ⟨g, hg⟩ x : ↥K) : Q) = g * x * g⁻¹ :=
  K.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ x

omit [Finite Q] in
theorem mem_center_of_conj_eq_one {X : Type} [Group X] {c : X} (h : MulAut.conj c = 1) :
    c ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun α : MulAut X => α x) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * c = c * x * c⁻¹ * c := by rw [this]
    _ = c * x := by group

theorem card_hat {X : Type} [Group X] [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) :
    Nat.card X = 7560 := by
  obtain ⟨e⟩ := hX.2.2
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, hA7, hX.2.1]

theorem pow_three_of_mem_center {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) {z : X} (hz : z ∈ Subgroup.center X) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := ⟨z, hz⟩)
  rw [hX.2.1] at h
  exact congrArg Subtype.val h

theorem exists_E9 (hD : FactHatA7Loc12626) {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ Subgroup.center X ≤ E := by
  have h2 : 2 ∣ Nat.card X := by rw [card_hat hX]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
  have hk2 : k ^ 2 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    exact absurd hk (by norm_num)
  obtain ⟨E, hE, hE9, hodd⟩ := (hD X hX).2.2.1 k hk2 hk1
  refine ⟨E, hE, hE9, fun z hz => hodd z ?_ ?_⟩
  · exact (Subgroup.mem_center_iff.mp hz k).symm
  · have h3 := pow_three_of_mem_center hX hz
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem mem_of_pow_three (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    {K : Subgroup Q} (hK : IsHat ↥K (alternatingGroup (Fin 7))) {p : Q}
    (hpN : p ∈ Subgroup.normalizer (K : Set Q)) (hp3 : p ^ 3 = 1) : p ∈ K := by
  classical
  obtain ⟨d1, d2, -, -⟩ := hD ↥K hK
  set α := K.normalizerMonoidHom ⟨p, hpN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨p, hpN⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hp3)
    rw [this, map_one]
  have hodd : Odd (orderOf α) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα3)
  obtain ⟨k, hk⟩ := d2 α (Or.inl hodd)
  have hkx : ∀ x : ↥K, (k : Q) * x * (k : Q)⁻¹ = p * x * p⁻¹ := by
    intro x
    have h1 := congrArg (fun β : MulAut ↥K => ((β x : ↥K) : Q)) hk
    simp only [MulAut.conj_apply] at h1
    rw [conjK_apply] at h1
    simpa using h1
  have hk3 : k ^ 3 = 1 := by
    apply d1
    apply mem_center_of_conj_eq_one
    rw [map_pow, hk, hα3]
  set c := (k : Q)⁻¹ * p with hc
  have hcK : ∀ x ∈ K, c * x = x * c := by
    intro x hx
    have h1 := hkx ⟨x, hx⟩
    simp only at h1
    calc c * x = (k : Q)⁻¹ * (p * x * p⁻¹) * p := by rw [hc]; group
      _ = (k : Q)⁻¹ * ((k : Q) * x * (k : Q)⁻¹) * p := by rw [h1]
      _ = x * c := by rw [hc]; group
  have hck : c * k = k * c := hcK k k.2
  have hpkc : p = k * c := by rw [hc]; group
  have hc3 : c ^ 3 = 1 := by
    have hkc : Commute (k : Q) c := hck.symm
    have h1 : p ^ 3 = (k : Q) ^ 3 * c ^ 3 := by rw [hpkc, hkc.mul_pow]
    rw [hp3] at h1
    have hk3' : (k : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3
    rw [hk3', one_mul] at h1
    exact h1.symm
  by_contra hpK
  have hcK' : c ∉ K := by
    intro h
    exact hpK (hpkc ▸ K.mul_mem k.2 h)
  obtain ⟨E, hE, hE9, -⟩ := exists_E9 hD hK
  refine false_of_e27 hsq (CFSG.SectionRank.isElemAbelian_map hE K.subtype)
    (by rw [Subgroup.card_map_of_injective K.subtype_injective, hE9]) hc3 ?_ ?_
  · rintro ⟨e, -, he⟩
    apply hcK'
    rw [← he]
    exact e.2
  · rintro _ ⟨e, -, rfl⟩
    exact hcK e e.2


variable {K L P T : Subgroup Q} {v : Q}

theorem L_le_K (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsHat ↥K (alternatingGroup (Fin 7))) : L ≤ K := by
  rw [← hc.L_gen]
  refine (Subgroup.closure_le K).mpr ?_
  rintro x ⟨hxL, hxodd⟩
  exact mem_of_pow_three hsq hD hK (hc.L_norm hxL) (hc.L_three x hxL hxodd)

omit [Finite Q] in
theorem conj_eq_one_of_mem_center {X : Type} [Group X] {ζ : X} (hζ : ζ ∈ Subgroup.center X) :
    MulAut.conj ζ = 1 := by
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hζ x).symm]
  group

theorem exists_inv (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsHat ↥K (alternatingGroup (Fin 7))) :
    ∃ k₀ : ↥K, k₀ ^ 2 = 1 ∧ k₀ ≠ 1 ∧ ∀ x ∈ K, v * x * v⁻¹ = k₀ * x * (k₀ : Q)⁻¹ := by
  classical
  obtain ⟨-, d2, -, -⟩ := hD ↥K hK
  have hLK := L_le_K hsq hD hc hK
  have hPK : P ≤ K := hc.P_le.trans hLK
  set α := K.normalizerMonoidHom ⟨v, hc.v_norm⟩ with hα
  have hfix : ∀ x ∈ P.subgroupOf K, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [hα, conjK_apply, hc.L_cent x (hc.P_le hx)]
    group
  have hP9 : Nat.card (P.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hc.P_card]
  obtain ⟨k, hk⟩ := d2 α (Or.inr ⟨_, hP9, hfix⟩)
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hc.v_norm⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hc.v_sq)
    rw [this, map_one]
  have hζ : k ^ 2 ∈ Subgroup.center ↥K := mem_center_of_conj_eq_one (by rw [map_pow, hk, hα2])
  have hζ3 : (k ^ 2) ^ 3 = 1 := pow_three_of_mem_center hK hζ
  have hkζ : Commute k (k ^ 2) := (Commute.refl k).pow_right 2
  have hconj : MulAut.conj (k * k ^ 2) = α := by
    rw [map_mul, conj_eq_one_of_mem_center hζ, mul_one, hk]
  refine ⟨k * k ^ 2, ?_, ?_, ?_⟩
  · have h6 : k ^ 6 = 1 := by rw [show 6 = 2 * 3 from rfl, pow_mul]; exact hζ3
    rw [hkζ.mul_pow, ← pow_mul, ← pow_add]
    exact h6
  · intro h1
    rw [h1, map_one] at hconj
    obtain ⟨x, hxK, hx⟩ := hc.v_nc
    apply hx
    have h2 := congrArg (fun β : MulAut ↥K => ((β ⟨x, hxK⟩ : ↥K) : Q)) hconj
    simp only [MulAut.one_apply] at h2
    rw [hα, conjK_apply] at h2
    calc v * x = v * x * v⁻¹ * v := by group
      _ = x * v := by rw [← h2]
  · intro x hxK
    have h2 := congrArg (fun β : MulAut ↥K => ((β ⟨x, hxK⟩ : ↥K) : Q)) hconj
    simp only [MulAut.conj_apply] at h2
    rw [hα, conjK_apply] at h2
    rw [← h2]
    simp

omit [Finite Q] in
theorem isElemAbelian_subgroupOf {p : ℕ} (hP : IsElemAbelian p P) (K : Subgroup Q) :
    IsElemAbelian p (P.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hP K

theorem L_eq_P (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsHat ↥K (alternatingGroup (Fin 7))) :
    L = P ∧ (Subgroup.center ↥K).map K.subtype ≤ P := by
  classical
  obtain ⟨-, -, d3, -⟩ := hD ↥K hK
  have hLK := L_le_K hsq hD hc hK
  obtain ⟨k₀, hk₀2, hk₀1, hk₀⟩ := exists_inv hsq hD hc hK
  obtain ⟨E, -, hE9, hodd⟩ := d3 k₀ hk₀2 hk₀1
  have hcomm : ∀ x (hxL : x ∈ L), (⟨x, hLK hxL⟩ : ↥K) * k₀ = k₀ * ⟨x, hLK hxL⟩ := by
    intro x hxL
    apply Subtype.ext
    have h1 := hk₀ x (hLK hxL)
    rw [hc.L_cent x hxL] at h1
    have h2 : x = k₀ * x * (k₀ : Q)⁻¹ := by rw [← h1]; group
    show x * (k₀ : Q) = k₀ * x
    calc x * (k₀ : Q) = k₀ * x * (k₀ : Q)⁻¹ * k₀ := by rw [← h2]
      _ = k₀ * x := by group
  have hLE : L ≤ E.map K.subtype := by
    rw [← hc.L_gen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxL, hxodd⟩
    refine ⟨⟨x, hLK hxL⟩, hodd _ (hcomm x hxL) ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]
  have hE9' : Nat.card (E.map K.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE9]
  have hPE : P = E.map K.subtype :=
    Subgroup.eq_of_le_of_card_ge (hc.P_le.trans hLE) (by rw [hE9', hc.P_card])
  refine ⟨le_antisymm (hLE.trans hPE.ge) hc.P_le, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [hPE]
  refine ⟨z, hodd z (Subgroup.mem_center_iff.mp hz k₀).symm ?_, rfl⟩
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (pow_three_of_mem_center hK hz))

theorem T_le_normalizer (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsHat ↥K (alternatingGroup (Fin 7))) :
    T ≤ Subgroup.normalizer (K : Set Q) := by
  classical
  have hLK := L_le_K hsq hD hc hK
  have hPK : P ≤ K := hc.P_le.trans hLK
  obtain ⟨hLP, -⟩ := L_eq_P hsq hD hc hK
  intro t ht
  have htv : t ∈ Subgroup.centralizer ({v} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc.v_central t ht).symm
  have htP : t ∈ Subgroup.normalizer (P : Set Q) := hLP ▸ hc.L_star htv
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hc.comp
  rcases CFSG.LocalCores.distinct_components_commute hc.comp hK' with heq | hcomm
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [heq]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simpa [MulAut.conj_apply] using hyx
      rwa [← this]
  · exfalso
    have hPK' : P ≤ K.map (MulAut.conj t).toMonoidHom := by
      intro p hp
      have h1 : t⁻¹ * p * t⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htP) p).mp hp
      refine ⟨t⁻¹ * p * t⁻¹⁻¹, hPK h1, ?_⟩
      simp [MulAut.conj_apply]
      group
    have hcen : P.subgroupOf K ≤ Subgroup.center ↥K := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 : ⁅(y : Q), (x : Q)⁆ ∈ ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator y.2 (hPK' hx)
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hcen
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hc.P_card, hK.2.1] at h1
    omega


omit [Finite Q] in
theorem eq_one_of_two_three {x : Q} {n : ℕ} (h2 : x ^ 2 ^ n = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h1')

omit [Finite Q] in
theorem mem_normalizer_of_forall {S : Subgroup Q} {g : Q} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer (S : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

omit [Finite Q] in
theorem le_normalizer_inf (hTP : T ≤ Subgroup.normalizer (P : Set Q)) :
    P ⊔ T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (P : Set Q) : Subgroup Q) : Set Q) := by
  have hconj : ∀ g ∈ T, ∀ y ∈ T ⊓ Subgroup.centralizer (P : Set Q),
      g * y * g⁻¹ ∈ T ⊓ Subgroup.centralizer (P : Set Q) := by
    intro g hg y hy
    refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem hg hy.1) (T.inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTP hg)) p).mp hp
    have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ hp'
    calc p * (g * y * g⁻¹) = g * ((g⁻¹ * p * g⁻¹⁻¹) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * p * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * p := by group
  refine sup_le (fun p hp => mem_normalizer_of_forall (fun y hy => ?_) (fun y hy => ?_))
    (fun g hg => mem_normalizer_of_forall (hconj g hg) (fun y hy => ?_))
  · have h1 := Subgroup.mem_centralizer_iff.mp hy.2 p hp
    have : p * y * p⁻¹ = y := by rw [h1]; group
    rw [this]
    exact hy
  · have h1 := Subgroup.mem_centralizer_iff.mp hy.2 p hp
    have : p⁻¹ * y * p = y := by
      calc p⁻¹ * y * p = p⁻¹ * (p * y) := by rw [h1]; group
        _ = y := by group
    rw [this]
    exact hy
  · have := hconj g⁻¹ (T.inv_mem hg) y hy
    simpa using this

theorem pCoreOf_eq (hc : Conf12626 K L P T v) (hLP : L = P)
    (hTP : T ≤ Subgroup.normalizer (P : Set Q)) :
    pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (P : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hLP]
  have hPN : P ⊔ T ≤ Subgroup.normalizer (P : Set Q) := sup_le Subgroup.le_normalizer hTP
  apply le_antisymm
  · have hO2 : IsPGroup 2 (pCoreOf 2 (P ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hON : P ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (P ⊔ T) : Set Q) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hOT : pCoreOf 2 (P ⊔ T) ≤ T := by
      have h1 : IsPGroup 2 (T ⊔ pCoreOf 2 (P ⊔ T) : Subgroup Q) :=
        IsPGroup.to_sup_of_normal_right' hc.sylow.2.1 hO2 (le_sup_right.trans hON)
      have h2 := hc.sylow.eq_of_le le_sup_left le_top h1
      exact le_sup_right.trans h2.le
    refine le_inf hOT ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hxPT : x ∈ P ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have h1 : x * p * x⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPN hxPT) p).mp hp) (P.inv_mem hp)
    have h2 : x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 (P ⊔ T) := by
      have h3 := (Subgroup.mem_normalizer_iff.mp
        (hON (le_sup_left (a := P) (b := T) hp)) x⁻¹).mp ((pCoreOf 2 (P ⊔ T)).inv_mem hx)
      have e : x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 (P ⊔ T)).mul_mem hx h3
    obtain ⟨n, hn⟩ := hO2 ⟨_, h2⟩
    have h4 := eq_one_of_two_three (by simpa using congrArg Subtype.val hn) (hc.P_elem.2 _ h1)
    calc p * x = (x * p * x⁻¹ * p⁻¹)⁻¹ * x * p := by group
      _ = x * p := by rw [h4, inv_one, one_mul]
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (le_normalizer_inf hTP) (hc.sylow.2.1.to_le inf_le_left)


theorem map_le_T (hc : Conf12626 K L P T v) (hTK : T ≤ Subgroup.normalizer (K : Set Q))
    (hTP : T ≤ Subgroup.normalizer (P : Set Q)) (hPK : P ≤ K) {A : Subgroup ↥K}
    (hA2 : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K))
    (hAmax : ∀ x ∈ Subgroup.centralizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K),
      (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ A) :
    A.map K.subtype ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ t ∈ T, ∀ y ∈ A.map K.subtype, t * y * t⁻¹ ∈ A.map K.subtype := by
    rintro t ht _ ⟨a, ha, rfl⟩
    have hz : t * (a : Q) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ht) a).mp a.2
    refine ⟨⟨_, hz⟩, hAmax _ ?_ ?_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      apply Subtype.ext
      have he' : t⁻¹ * (e : Q) * t⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTP ht)) e).mp he
      have h1 := congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp (hAC ha) ⟨_, hPK he'⟩ (Subgroup.mem_subgroupOf.mpr he'))
      simp only [Subgroup.coe_mul] at h1
      show (e : Q) * (t * a * t⁻¹) = t * a * t⁻¹ * e
      calc (e : Q) * (t * a * t⁻¹) = t * ((t⁻¹ * e * t⁻¹⁻¹) * a) * t⁻¹ := by group
        _ = t * (a * (t⁻¹ * e * t⁻¹⁻¹)) * t⁻¹ := by rw [h1]
        _ = t * a * t⁻¹ * e := by group
    · obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
      refine ⟨n, Subtype.ext ?_⟩
      have h1 : (a : Q) ^ 2 ^ n = 1 := by simpa using congrArg (fun b : ↥A => ((b : ↥K) : Q)) hn
      simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
      rw [conj_pow, h1]
      group
  have hTN : T ≤ Subgroup.normalizer ((A.map K.subtype : Subgroup Q) : Set Q) := fun t ht =>
    mem_normalizer_of_forall (hconj t ht) (fun y hy => by
      simpa using hconj t⁻¹ (T.inv_mem ht) y hy)
  have h1 : IsPGroup 2 (T ⊔ A.map K.subtype : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right' hc.sylow.2.1 (hA2.map K.subtype) hTN
  exact le_sup_right.trans (hc.sylow.eq_of_le le_sup_left le_top h1).le

theorem pow_eq_one_aux {X : Type} [Group X] {ζ : X} (hζ : ζ ^ 3 = 1) (n : ℕ) :
    ζ ^ (1 + 2 * 2 ^ n * 2 ^ n) = 1 := by
  rw [pow_eq_pow_mod _ hζ]
  have h4 : (2 ^ n * 2 ^ n) % 3 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  have : (1 + 2 * 2 ^ n * 2 ^ n) % 3 = 0 := by
    rw [mul_assoc]
    omega
  rw [this, pow_zero]

theorem conj_mem_inf (hD : FactHatA7Loc12626) (hc : Conf12626 K L P T v)
    (hK : IsHat ↥K (alternatingGroup (Fin 7))) (hTK : T ≤ Subgroup.normalizer (K : Set Q))
    (hPK : P ≤ K) {A S : Subgroup ↥K}
    (hAC : A ≤ Subgroup.centralizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K))
    (hAmax : ∀ x ∈ Subgroup.centralizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K),
      (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ A)
    (hSA : S ≤ Subgroup.normalizer (A : Set ↥K)) (hAT : A.map K.subtype ≤ T) {x : ↥K} (hx : x ∈ S)
    {r : Q} (hr : r ∈ T ⊓ Subgroup.centralizer (P : Set Q)) :
    (x : Q) * r * (x : Q)⁻¹ ∈ T ⊓ Subgroup.centralizer (P : Set Q) := by
  classical
  obtain ⟨-, d2, -, -⟩ := hD ↥K hK
  have hrT : r ∈ T := (Subgroup.mem_inf.mp hr).1
  have hrC : r ∈ Subgroup.centralizer (P : Set Q) := (Subgroup.mem_inf.mp hr).2
  have hrN : r ∈ Subgroup.normalizer (K : Set Q) := hTK hrT
  set α := K.normalizerMonoidHom ⟨r, hrN⟩ with hα
  have hfix : ∀ e ∈ P.subgroupOf K, α e = e := by
    intro e he
    apply Subtype.ext
    rw [hα, conjK_apply, ← Subgroup.mem_centralizer_iff.mp hrC e he]
    group
  have hE9 : Nat.card (P.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hc.P_card]
  obtain ⟨κ, hκ⟩ := d2 α (Or.inr ⟨_, hE9, hfix⟩)
  obtain ⟨n, hn⟩ := hc.sylow.2.1 ⟨r, hrT⟩
  have hrn : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hαn : α ^ 2 ^ n = 1 := by
    rw [hα, ← map_pow]
    have : (⟨r, hrN⟩ : ↥(Subgroup.normalizer (K : Set Q))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using hrn)
    rw [this, map_one]
  have hζ : κ ^ 2 ^ n ∈ Subgroup.center ↥K :=
    mem_center_of_conj_eq_one (by rw [map_pow, hκ, hαn])
  have hζ3 : (κ ^ 2 ^ n) ^ 3 = 1 := pow_three_of_mem_center hK hζ
  have hζm : (κ ^ 2 ^ n) ^ (2 * 2 ^ n) ∈ Subgroup.center ↥K := Subgroup.pow_mem _ hζ _
  set κ' := κ * (κ ^ 2 ^ n) ^ (2 * 2 ^ n) with hκ'
  have hκ'α : MulAut.conj κ' = α := by
    rw [hκ', map_mul, conj_eq_one_of_mem_center hζm, mul_one, hκ]
  have hκ'2 : κ' ^ 2 ^ n = 1 := by
    have hcomm : Commute κ ((κ ^ 2 ^ n) ^ (2 * 2 ^ n)) :=
      (Subgroup.mem_center_iff.mp hζm κ)
    rw [hκ', hcomm.mul_pow, ← pow_mul, ← pow_succ' (κ ^ 2 ^ n) (2 * 2 ^ n * 2 ^ n)]
    have := pow_eq_one_aux hζ3 n
    rwa [show 1 + 2 * 2 ^ n * 2 ^ n = 2 * 2 ^ n * 2 ^ n + 1 by ring] at this
  have hκ'C : κ' ∈ Subgroup.centralizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := congrArg (fun β : MulAut ↥K => β e) hκ'α
    simp only [MulAut.conj_apply] at h1
    rw [hfix e he] at h1
    calc e * κ' = κ' * e * κ'⁻¹ * κ' := by rw [h1]
      _ = κ' * e := by group
  have hκ'A : κ' ∈ A := hAmax κ' hκ'C ⟨n, hκ'2⟩
  have hkey : r * (x : Q)⁻¹ * r⁻¹ = κ' * (x : Q)⁻¹ * (κ' : Q)⁻¹ := by
    have h1 := congrArg (fun β : MulAut ↥K => ((β x⁻¹ : ↥K) : Q)) hκ'α
    simp only [MulAut.conj_apply] at h1
    rw [hα, conjK_apply] at h1
    simpa using h1.symm
  have hw : x * κ' * x⁻¹ * κ'⁻¹ ∈ A := by
    have h1 : x * κ' * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hSA hx) κ').mp hκ'A
    exact A.mul_mem h1 (A.inv_mem hκ'A)
  have hwT : ((x * κ' * x⁻¹ * κ'⁻¹ : ↥K) : Q) ∈ T := hAT ⟨_, hw, rfl⟩
  have hwC : ((x * κ' * x⁻¹ * κ'⁻¹ : ↥K) : Q) ∈ Subgroup.centralizer (P : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 := congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hAC hw) ⟨p, hPK hp⟩ (Subgroup.mem_subgroupOf.mpr hp))
    simpa using h1
  have e : (x : Q) * r * (x : Q)⁻¹ = ((x * κ' * x⁻¹ * κ'⁻¹ : ↥K) : Q) * r := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (x : Q) * r * (x : Q)⁻¹ = (x : Q) * (r * (x : Q)⁻¹ * r⁻¹) * r := by group
      _ = (x : Q) * (κ' * (x : Q)⁻¹ * (κ' : Q)⁻¹) * r := by rw [hkey]
      _ = _ := by group
  rw [e]
  exact (T ⊓ Subgroup.centralizer (P : Set Q)).mul_mem (Subgroup.mem_inf.mpr ⟨hwT, hwC⟩) hr

theorem exists_three_normalizer (hsq : CFSG.IsStronglyQuasithin Q) (hD : FactHatA7Loc12626)
    (hc : Conf12626 K L P T v) (hK : IsHat ↥K (alternatingGroup (Fin 7))) :
    ∃ S : Subgroup Q, IsPGroup 3 S ∧ Nat.card S = 27 ∧
      S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set Q) := by
  classical
  obtain ⟨hLP, hZP⟩ := L_eq_P hsq hD hc hK
  have hPK : P ≤ K := hc.P_le.trans (L_le_K hsq hD hc hK)
  have hTK := T_le_normalizer hsq hD hc hK
  have hTP : T ≤ Subgroup.normalizer (P : Set Q) := fun t ht => by
    have htv : t ∈ Subgroup.centralizer ({v} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc.v_central t ht).symm
    exact hLP ▸ hc.L_star htv
  obtain ⟨-, -, -, d4⟩ := hD ↥K hK
  have hE9 : Nat.card (P.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hc.P_card]
  have hZE : Subgroup.center ↥K ≤ P.subgroupOf K := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hZP ⟨z, hz, rfl⟩)
  obtain ⟨A, S, hA2, hAC, hAmax, hS3, hS27, hSA⟩ :=
    d4 _ (isElemAbelian_subgroupOf hc.P_elem K) hE9 hZE
  have hAT := map_le_T hc hTK hTP hPK hA2 hAC hAmax
  refine ⟨S.map K.subtype, hS3.map _, by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hS27], ?_⟩
  rw [pCoreOf_eq hc hLP hTP]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_normalizer_of_forall
    (fun r hr => conj_mem_inf hD hc hK hTK hPK hAC hAmax hSA hAT hx hr) (fun r hr => ?_)
  have := conj_mem_inf hD hc hK hTK hPK hAC hAmax hSA hAT (S.inv_mem hx) hr
  simpa using this

end S126C


namespace S126L26

open S126

variable {G : Type} [Group G] [Finite G]

theorem map_pCoreOf_eq {H X : Subgroup G} (hXH : X ≤ H) :
    ((pCoreOf 2 X).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      pCoreOf 2 ((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hRX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hR2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono fun y hy =>
        Subgroup.mem_subgroupOf.mpr (hRX (Subgroup.mem_subgroupOf.mp hy)))
      ?_ ((hR2.of_equiv (Subgroup.subgroupOfEquivOfLe (hRX.trans hXH)).symm).map π)
    rintro _ ⟨y, hy, rfl⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hXN (Subgroup.mem_subgroupOf.mp hy)
    refine S126C.mem_normalizer_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨y * a * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp hyN a).mp (Subgroup.mem_subgroupOf.mp ha)
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨y⁻¹ * a * y, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) a).mp
        (Subgroup.mem_subgroupOf.mp ha)
      simpa using this
  · set B := pCoreOf 2 ((X.subgroupOf H).map π) with hB
    have hB2 : IsPGroup 2 B := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hBX : B ≤ (X.subgroupOf H).map π := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hBN : (X.subgroupOf H).map π ≤ Subgroup.normalizer (B : Set _) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    set Y : Subgroup G := ((B.comap π) ⊓ X.subgroupOf H).map H.subtype with hY
    have hmemY : ∀ g : G, g ∈ Y ↔ ∃ hg : g ∈ H, π ⟨g, hg⟩ ∈ B ∧ g ∈ X := by
      intro g
      constructor
      · rintro ⟨y, ⟨hyB, hyX⟩, rfl⟩
        exact ⟨y.2, hyB, Subgroup.mem_subgroupOf.mp hyX⟩
      · rintro ⟨hg, hgB, hgX⟩
        exact ⟨⟨g, hg⟩, ⟨hgB, Subgroup.mem_subgroupOf.mpr hgX⟩, rfl⟩
    have hYR : Y ≤ pCoreOf 2 X := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (fun g hg => ((hmemY g).mp hg).2.2) (fun g hgX => ?_) ?_
      · have hgH := hXH hgX
        refine S126C.mem_normalizer_of_forall (fun y hy => ?_) (fun y hy => ?_)
        · obtain ⟨hyH, hyB, hyX⟩ := (hmemY y).mp hy
          refine (hmemY _).mpr ⟨H.mul_mem (H.mul_mem hgH hyH) (H.inv_mem hgH), ?_,
            X.mul_mem (X.mul_mem hgX hyX) (X.inv_mem hgX)⟩
          have h1 := (Subgroup.mem_normalizer_iff.mp
            (hBN ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩) _).mp hyB
          have e : π ⟨g * y * g⁻¹, H.mul_mem (H.mul_mem hgH hyH) (H.inv_mem hgH)⟩ =
              π ⟨g, hgH⟩ * π ⟨y, hyH⟩ * (π ⟨g, hgH⟩)⁻¹ := by
            rw [← map_mul, ← map_inv, ← map_mul]
            rfl
          rw [e]
          exact h1
        · obtain ⟨hyH, hyB, hyX⟩ := (hmemY y).mp hy
          refine (hmemY _).mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hgH) hyH) hgH, ?_,
            X.mul_mem (X.mul_mem (X.inv_mem hgX) hyX) hgX⟩
          have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
            (hBN ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩)) _).mp hyB
          have e : π ⟨g⁻¹ * y * g, H.mul_mem (H.mul_mem (H.inv_mem hgH) hyH) hgH⟩ =
              (π ⟨g, hgH⟩)⁻¹ * π ⟨y, hyH⟩ * (π ⟨g, hgH⟩)⁻¹⁻¹ := by
            rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
            rfl
          rw [e]
          exact h1
      · rintro ⟨g, hg⟩
        obtain ⟨hgH, hgB, -⟩ := (hmemY g).mp hg
        obtain ⟨a, ha⟩ := hB2 ⟨_, hgB⟩
        have h1 : π (⟨g, hgH⟩ ^ 2 ^ a) = 1 := by
          rw [map_pow]
          simpa using congrArg Subtype.val ha
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥H)) ⟨_, h1⟩
        refine ⟨a + b, Subtype.ext ?_⟩
        have h2 : (g ^ 2 ^ a) ^ 2 ^ b = 1 := by
          simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hb
        simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
        rw [pow_add, pow_mul]
        exact h2
    intro b hb
    obtain ⟨x, hx, rfl⟩ := hBX hb
    have hxY : (x : G) ∈ Y := (hmemY _).mpr ⟨x.2, hb, Subgroup.mem_subgroupOf.mp hx⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (hYR hxY), rfl⟩


theorem exists_lift {H R : Subgroup G} (hRH : R ≤ H) (hQR : pCoreOf 2 H ≤ R)
    {S : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hS27 : Nat.card S = 27)
    (hSN : S ≤ Subgroup.normalizer
      (((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) : Subgroup _) : Set _)) :
    ∃ S' : Subgroup G, Nat.card S' = 27 ∧ S' ≤ Subgroup.normalizer (R : Set G) := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set N₁ : Subgroup ↥H := (Subgroup.normalizer (R : Set G)).subgroupOf H with hN₁
  have hconj : ∀ s : ↥H, π s ∈ Subgroup.normalizer
      (((R.subgroupOf H).map π : Subgroup _) : Set _) → ∀ r ∈ R, (s : G) * r * (s : G)⁻¹ ∈ R := by
    intro s hs r hr
    have hrH := hRH hr
    have h1 : π s * π ⟨r, hrH⟩ * (π s)⁻¹ ∈ (R.subgroupOf H).map π :=
      (Subgroup.mem_normalizer_iff.mp hs _).mp ⟨⟨r, hrH⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    obtain ⟨a, ha, hae⟩ := h1
    have h2 : π (a⁻¹ * (s * ⟨r, hrH⟩ * s⁻¹)) = 1 := by
      rw [map_mul, map_inv, hae, map_mul, map_mul, map_inv]
      group
    rw [hπ, QuotientGroup.mk'_apply, mk_eq_one_iff] at h2
    have h3 : (s : G) * r * (s : G)⁻¹ = (a : G) * ((a⁻¹ * (s * ⟨r, hrH⟩ * s⁻¹) : ↥H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact R.mul_mem (Subgroup.mem_subgroupOf.mp ha) (hQR h2)
  have hSle : S ≤ N₁.map π := by
    intro sb hsb
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) sb
    refine ⟨s, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    refine S126C.mem_normalizer_of_forall (hconj s (hSN hsb)) (fun r hr => ?_)
    have := hconj s⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ (hSN hsb)) r hr
    simpa using this
  have hdvd : 3 ^ 3 ∣ Nat.card N₁ := by
    have h1 := Subgroup.card_dvd_of_le hSle
    have h2 := Subgroup.card_map_dvd (H := N₁) π
    rw [hS27] at h1
    exact h1.trans h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨(S₀.map N₁.subtype).map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective N₁.subtype_injective, hS₀]
    norm_num
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp x.2

theorem false_of_a7 (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (h1261 : Lemma12_6_1)
    (hD : FactHatA7Loc12626) {T L V : Subgroup G} [IsMulCommutative ↥V] (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) (hsq : CFSG.IsStronglyQuasithin (↥H ⧸ CFSG.pCore 2 ↥H))
    {K P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {v : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hc : S126C.Conf12626 K
      (((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) P
      ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) v)
    (hK : IsHat ↥K (alternatingGroup (Fin 7))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, -, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hL1H : L₁Of L F.V1 ≤ H := le_sup_left.trans hHz.1.1
  have hXH : L₁Of L F.V1 ⊔ T ≤ H := hHz.1.1
  obtain ⟨Sb, -, hSb27, hSbN⟩ := S126C.exists_three_normalizer hsq hD hc hK
  have hsup : ((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⊔
      (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      ((L₁Of L F.V1 ⊔ T).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.subgroupOf_sup hL1H hTH, Subgroup.map_sup]
  rw [hsup, ← map_pCoreOf_eq hXH] at hSbN
  have hQR : pCoreOf 2 H ≤ S126.Ri T L F.V1 := by
    have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h.sylow hTH)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hXH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hRH : S126.Ri T L F.V1 ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXH
  obtain ⟨S, hS27, hSN⟩ := exists_lift hRH hQR hSb27 hSbN
  have h61 := h1261 G T L V F hH
  have hSL : S ≤ L := by
    rw [← h61.2.2.2.2.1]
    intro x hx
    refine Subgroup.subset_closure ⟨h61.2.2.2.1.2 (hSN hx), 3, ?_⟩
    have := pow_card_eq_one' (G := ↥S) (x := ⟨x, hx⟩)
    rw [hS27] at this
    simpa using congrArg Subtype.val this
  let f : ↥S →* ↥(alternatingGroup (Fin 8)) := (S126L19a.psi F hH).comp (Subgroup.inclusion hSL)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hC := (S126L19a.psi_eq_one_iff F hH _).1 hs
    obtain ⟨n, hn⟩ := S126T2.isPGroup_CL h1222 hH ⟨(s : G), hSL s.2, hC⟩
    have h2 : (s : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : (s : G) ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥S) (x := s)
      rw [hS27] at this
      simpa using congrArg Subtype.val this
    have h4 : orderOf (s : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf (s : G) ∣ 27 := orderOf_dvd_of_pow_eq_one h3
    have hc : Nat.Coprime (2 ^ n) 27 := Nat.Coprime.pow_left n (by norm_num)
    have h6 : orderOf (s : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 hc) h5
    exact Subtype.ext (orderOf_eq_one_iff.mp h6)
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [hS27, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
  norm_num [Nat.factorial] at hdvd

end S126L26

end CFSG.Quasithin.H13
