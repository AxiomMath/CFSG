module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81
open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise

namespace OddCoreLiftF

theorem odd_card_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem map_conjSubgroup {G H : Type*} [Group G] [Group H] (f : G →* H) (A : Subgroup G)
    (g : G) : (conjSubgroup A g).map f = conjSubgroup (A.map f) (f g) := by
  unfold conjSubgroup
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem conjSubgroup_zpowers {G : Type*} [Group G] (x g : G) :
    conjSubgroup (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold conjSubgroup
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem perm3a : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    (a * b) ^ 3 = 1 := by
  decide

theorem perm3b : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    (a * b) ^ 2 ≠ 1 := by
  decide

set_option synthInstance.maxSize 1024 in
theorem perm3c : ∀ a b c : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b ∨ c = b * a ∨ c = a * b * a := by
  decide

theorem perm3 (a b : Equiv.Perm (Fin 3)) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    (a * b) ^ 3 = 1 ∧ (a * b) ^ 2 ≠ 1 ∧ ∀ c : Equiv.Perm (Fin 3),
      c = 1 ∨ c = a ∨ c = b ∨ c = a * b ∨ c = b * a ∨ c = a * b * a :=
  ⟨perm3a a b ha hb ha1 hb1 hab, perm3b a b ha hb ha1 hb1 hab,
    fun c => perm3c a b c ha hb ha1 hb1 hab⟩

theorem perm3' : ∀ a : Equiv.Perm (Fin 3), ∃ c : Equiv.Perm (Fin 3), c ≠ 1 ∧ c ≠ a := by
  decide

theorem sym3_facts {Y : Type} [Group Y] (eY : Y ≃* Equiv.Perm (Fin 3)) {a b : Y}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    (a * b) ^ 3 = 1 ∧ (a * b) ^ 2 ≠ 1 ∧
      ∀ c : Y, c = 1 ∨ c = a ∨ c = b ∨ c = a * b ∨ c = b * a ∨ c = a * b * a := by
  obtain ⟨h1, h2, h3⟩ := perm3 (eY a) (eY b) (by rw [← map_mul, ha, map_one])
    (by rw [← map_mul, hb, map_one])
    (fun h => ha1 (eY.injective (h.trans (map_one eY).symm)))
    (fun h => hb1 (eY.injective (h.trans (map_one eY).symm)))
    (fun h => hab (eY.injective h))
  refine ⟨eY.injective ?_, fun h => h2 ?_, fun c => ?_⟩
  · rw [map_pow, map_mul, h1, map_one]
  · rw [← map_mul, ← map_pow, h, map_one]
  · rcases h3 (eY c) with h | h | h | h | h | h
    · exact Or.inl (eY.injective (by rw [h, map_one]))
    · exact Or.inr (Or.inl (eY.injective h))
    · exact Or.inr (Or.inr (Or.inl (eY.injective h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eY.injective (by rw [h, map_mul])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eY.injective (by rw [h, map_mul]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (eY.injective (by rw [h, map_mul, map_mul]))))))

theorem mem_zpowers_sq {G : Type*} [Group G] {σ x : G} (h : σ * σ = 1)
    (hx : x ∈ Subgroup.zpowers σ) : x = 1 ∨ x = σ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, h]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_one_of_pow_two_pow_of_odd {G : Type*} [Group G] {z : G} {i n : ℕ}
    (h1 : z ^ (2 ^ i) = 1) (hn : Odd n) (h2 : z ^ n = 1) : z = 1 := by
  have hc : Nat.Coprime (2 ^ i) n := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
  have := Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp this

theorem pow_card_eq_one_of_mem {G : Type*} [Group G] {N : Subgroup G} {z : G} (hz : z ∈ N) :
    z ^ Nat.card N = 1 := by
  exact congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨z, hz⟩))

theorem eq_one_of_two_elem_mem {G : Type*} [Group G] {N : Subgroup G}
    (hodd : Odd (Nat.card N)) {z : G} (hz : z ∈ N) {i : ℕ} (h : z ^ (2 ^ i) = 1) : z = 1 :=
  eq_one_of_pow_two_pow_of_odd h hodd (pow_card_eq_one_of_mem hz)

theorem two_elem_of_isPGroup {G : Type*} [Group G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {z : G} (hz : z ∈ Q) : ∃ i : ℕ, z ^ (2 ^ i) = 1 := by
  obtain ⟨i, hi⟩ := hQ ⟨z, hz⟩
  exact ⟨i, by simpa using congrArg Subtype.val hi⟩

theorem isConj_of_eq {G : Type*} [Group G] {t d c : G} (h : d = c⁻¹ * t * c) : IsConj t d :=
  isConj_iff.mpr ⟨c⁻¹, by rw [h]; group⟩

theorem dihedral_conj {G : Type*} [Group G] {t d : G} (ht : t * t = 1) (hd : d * d = 1)
    {n : ℕ} (hn : Odd n) (hr : (t * d) ^ n = 1) :
    ∃ j : ℕ, d = ((t * d) ^ j)⁻¹ * t * (t * d) ^ j := by
  obtain ⟨m, rfl⟩ := hn
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have h1 : t * (t * d) * t⁻¹ = (t * d)⁻¹ := by
    rw [htinv, mul_inv_rev, hdinv, htinv, ← mul_assoc, ht, one_mul]
  have h2 : ∀ k : ℕ, t * (t * d) ^ k * t⁻¹ = ((t * d) ^ k)⁻¹ := by
    intro k
    rw [← conj_pow, h1, inv_pow]
  refine ⟨m + 1, ?_⟩
  have h3 : ((t * d) ^ (m + 1))⁻¹ * t = t * (t * d) ^ (m + 1) := by
    rw [← h2]; group
  rw [h3, mul_assoc, ← pow_add]
  have : m + 1 + (m + 1) = (2 * m + 1) + 1 := by ring
  rw [this, pow_succ, hr, one_mul, ← mul_assoc, ht, one_mul]

theorem eq_one_of_commute_two_odd {G : Type*} [Group G] {N : Subgroup G}
    (hodd : Odd (Nat.card N)) {c y : G} {i : ℕ} (hc : c ^ (2 ^ i) = 1) (hc1 : c ≠ 1)
    (hy : y ∈ N) (hcy : c * y = y * c)
    (h : orderOf (c * y) ∣ 2 ∨ Odd (orderOf (c * y))) : y = 1 := by
  have hcomm : Commute c y := hcy
  rcases h with h | h
  · have h2 : (c * y) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hcomm.mul_pow] at h2
    have hc2 : c ^ 2 = (y ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have hc2N : c ^ 2 ∈ N := by rw [hc2]; exact N.inv_mem (N.pow_mem hy 2)
    have hc2' : (c ^ 2) ^ (2 ^ i) = 1 := by
      rw [← pow_mul, mul_comm 2, pow_mul, hc, one_pow]
    have hc21 : c ^ 2 = 1 := eq_one_of_two_elem_mem hodd hc2N hc2'
    rw [hc21, one_mul] at h2
    exact eq_one_of_two_elem_mem (i := 1) hodd hy (by simpa using h2)
  · have h2 : (c * y) ^ orderOf (c * y) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at h2
    have hcn : c ^ orderOf (c * y) = (y ^ orderOf (c * y))⁻¹ := eq_inv_of_mul_eq_one_left h2
    have hcnN : c ^ orderOf (c * y) ∈ N := by
      rw [hcn]; exact N.inv_mem (N.pow_mem hy _)
    have hcn' : (c ^ orderOf (c * y)) ^ (2 ^ i) = 1 := by
      rw [← pow_mul, mul_comm (orderOf (c * y)), pow_mul, hc, one_pow]
    have := eq_one_of_two_elem_mem hodd hcnN hcn'
    exact absurd (eq_one_of_pow_two_pow_of_odd hc h this) hc1

theorem mem_normalizer_conj {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (b : G) :
    b * g * b⁻¹ ∈ Subgroup.normalizer (conjSubgroup A b⁻¹ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, CFSG.Quasithin.mem_conjSubgroup_iff]
  have : b⁻¹ * (b * g * b⁻¹ * h * (b * g * b⁻¹)⁻¹) * b⁻¹⁻¹ = g * (b⁻¹ * h * b⁻¹⁻¹) * g⁻¹ := by
    group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp hg) _

section Quot

variable {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

theorem conj_of_mk_eq (hodd : Odd (Nat.card N)) {t d : X} (ht : t * t = 1) (hd : d * d = 1)
    (h : QuotientGroup.mk' N t = QuotientGroup.mk' N d) : ∃ c ∈ N, t = c⁻¹ * d * c := by
  have hmem : d * t ∈ N := by
    have : QuotientGroup.mk' N (d * t) = 1 := by rw [map_mul, h, ← map_mul, hd, map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨j, hj⟩ := dihedral_conj hd ht hodd (pow_card_eq_one_of_mem hmem)
  exact ⟨(d * t) ^ j, N.pow_mem hmem j, hj⟩

theorem lift_inv (hodd : Odd (Nat.card N)) {m d : X} (hd : d * d = 1)
    (h : QuotientGroup.mk' N m = QuotientGroup.mk' N d) :
    m ^ Nat.card N * m ^ Nat.card N = 1 ∧
      QuotientGroup.mk' N (m ^ Nat.card N) = QuotientGroup.mk' N d := by
  have hdd : QuotientGroup.mk' N d * QuotientGroup.mk' N d = 1 := by
    rw [← map_mul, hd, map_one]
  have hmem : m * m ∈ N := by
    have : QuotientGroup.mk' N (m * m) = 1 := by rw [map_mul, h, hdd]
    exact (QuotientGroup.eq_one_iff _).mp this
  constructor
  · rw [← pow_add, ← two_mul, pow_mul, sq]; exact pow_card_eq_one_of_mem hmem
  · obtain ⟨j, hj⟩ := hodd
    rw [map_pow, h, hj, pow_succ, pow_mul, sq, hdd, one_pow, one_mul]

theorem exists_full (Qh : Subgroup (X ⧸ N)) (hQh : IsPGroup 2 Qh) :
    ∃ Q : Subgroup X, IsPGroup 2 Q ∧ Q.map (QuotientGroup.mk' N) = Qh := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Qh.comap (QuotientGroup.mk' N)
  let ρ : R →* Qh := ((QuotientGroup.mk' N).comp R.subtype).codRestrict Qh (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 R) := inferInstance
  have hidx : ((S : Subgroup R).map ρ).index = 1 := by
    obtain ⟨k, hk⟩ := hQh.index ((S : Subgroup R).map ρ)
    have h1 : ((S : Subgroup R).map ρ).index ∣ (S : Subgroup R).index :=
      Subgroup.index_map_dvd _ hρ
    have h2 := S.not_dvd_index
    rcases k with _ | k
    · simpa using hk
    · exfalso; apply h2; rw [hk] at h1; exact (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1
  rw [Subgroup.index_eq_one] at hidx
  refine ⟨(S : Subgroup R).map R.subtype, S.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact x.2
  · intro y hy
    obtain ⟨x, hx, hxy⟩ : (⟨y, hy⟩ : Qh) ∈ (S : Subgroup R).map ρ := by
      rw [hidx]; exact Subgroup.mem_top _
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩

theorem full_conj (Qh : Subgroup (X ⧸ N)) (hodd : Odd (Nat.card N)) {Q₁ Q₂ : Subgroup X}
    (h₁ : IsPGroup 2 Q₁) (h₁' : Q₁.map (QuotientGroup.mk' N) = Qh)
    (h₂ : IsPGroup 2 Q₂) (h₂' : Q₂.map (QuotientGroup.mk' N) = Qh) :
    ∃ r : X, QuotientGroup.mk' N r ∈ Qh ∧ Q₂ = conjSubgroup Q₁ r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Qh.comap (QuotientGroup.mk' N) with hR
  have hmemR : ∀ {Q : Subgroup X}, Q.map (QuotientGroup.mk' N) = Qh → ∀ {x}, x ∈ Q → x ∈ R := by
    intro Q hQ x hx
    show QuotientGroup.mk' N x ∈ Qh
    rw [← hQ]; exact Subgroup.mem_map_of_mem _ hx
  have mkS : ∀ Q : Subgroup X, IsPGroup 2 Q → Q.map (QuotientGroup.mk' N) = Qh →
      ∃ S : Sylow 2 R, (S : Subgroup R) = Q.subgroupOf R := by
    intro Q hQ hQ'
    refine ⟨⟨Q.subgroupOf R, hQ.comap_of_injective R.subtype R.subtype_injective, ?_⟩, rfl⟩
    intro K hK hle
    refine le_antisymm (fun k hk => ?_) hle
    have hkQh : QuotientGroup.mk' N (k : X) ∈ Q.map (QuotientGroup.mk' N) := by
      rw [hQ']; exact k.2
    obtain ⟨q, hq, hqk⟩ := hkQh
    have hqK : (⟨q, hmemR hQ' hq⟩ : R) ∈ K := hle (Subgroup.mem_subgroupOf.mpr hq)
    have hz := K.mul_mem (K.inv_mem hqK) hk
    obtain ⟨i, hi⟩ := hK ⟨_, hz⟩
    have hi' : (q⁻¹ * (k : X)) ^ (2 ^ i) = 1 := by
      have := congrArg (fun z : K => ((z : R) : X)) hi
      simpa using this
    have hzN : q⁻¹ * (k : X) ∈ N := QuotientGroup.eq.mp hqk
    have h1 := eq_one_of_two_elem_mem hodd hzN hi'
    have hkq : (k : X) = q := (inv_mul_eq_one.mp h1).symm
    exact Subgroup.mem_subgroupOf.mpr (hkq ▸ hq)
  obtain ⟨S₁, hS₁⟩ := mkS Q₁ h₁ h₁'
  obtain ⟨S₂, hS₂⟩ := mkS Q₂ h₂ h₂'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S₁ S₂
  have key : ∀ y : R, y ∈ (S₂ : Subgroup R) ↔ g⁻¹ * y * g ∈ (S₁ : Subgroup R) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_apply]
  refine ⟨(g : X)⁻¹, by rw [map_inv]; exact Qh.inv_mem g.2, ?_⟩
  ext x
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, inv_inv]
  constructor
  · intro hx
    have hxR := hmemR h₂' hx
    have := (key ⟨x, hxR⟩).mp (by rw [hS₂]; exact Subgroup.mem_subgroupOf.mpr hx)
    rw [hS₁, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hx
    have hxR : x ∈ R := by
      have h := hmemR h₁' hx
      have : x = (g : X) * ((g : X)⁻¹ * x * g) * (g : X)⁻¹ := by group
      rw [this]; exact R.mul_mem (R.mul_mem g.2 h) (R.inv_mem g.2)
    have := (key ⟨x, hxR⟩).mpr (by
      rw [hS₁]; exact Subgroup.mem_subgroupOf.mpr (by simpa using hx))
    rw [hS₂] at this
    exact Subgroup.mem_subgroupOf.mp this

theorem frattini (hodd : Odd (Nat.card N)) (Lh Qh : Subgroup (X ⧸ N))
    (hn : ∀ h ∈ Lh, ∀ x ∈ Qh, h * x * h⁻¹ ∈ Qh)
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hQ' : Q.map (QuotientGroup.mk' N) = Qh) {g : X}
    (hg : QuotientGroup.mk' N g ∈ Lh) :
    ∃ m ∈ Subgroup.normalizer (Q : Set X), QuotientGroup.mk' N m = QuotientGroup.mk' N g := by
  have hconjQh : conjSubgroup Qh (QuotientGroup.mk' N g) = Qh := by
    ext x
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    constructor
    · intro hx
      have := hn _ (Lh.inv_mem hg) _ hx
      have e : (QuotientGroup.mk' N g)⁻¹ * (QuotientGroup.mk' N g * x *
          (QuotientGroup.mk' N g)⁻¹) * (QuotientGroup.mk' N g)⁻¹⁻¹ = x := by group
      rwa [e] at this
    · intro hx; exact hn _ hg _ hx
  have hQg2 : IsPGroup 2 (conjSubgroup Q g) := hQ.map _
  obtain ⟨r, hr, hQr⟩ := full_conj N Qh hodd hQ hQ' hQg2
    (by rw [map_conjSubgroup, hQ', hconjQh])
  have hnorm : r * g⁻¹ ∈ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hQeq : Q = conjSubgroup Q (r * g⁻¹) := by
      rw [← conjSubgroup_conjSubgroup, ← hQr, conjSubgroup_conjSubgroup, mul_inv_cancel,
        CFSG.Quasithin.conjSubgroup_one]
    conv_lhs => rw [hQeq]
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
  rw [← hQ'] at hr
  obtain ⟨q, hq, hqr⟩ := hr
  refine ⟨(r * g⁻¹)⁻¹ * q, mul_mem (inv_mem hnorm) (Subgroup.le_normalizer hq), ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv, hqr]; group

end Quot

end OddCoreLiftF

open OddCoreLiftF in
theorem oddCoreLiftFischer :
    ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
      CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
      (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) →
      ∃ L : Subgroup X, Subgroup.zpowers s ≤ L ∧
        (⨆ (x : X) (_ : conjSubgroup (Subgroup.zpowers s) x ≤ L),
          conjSubgroup (Subgroup.zpowers s) x) = L ∧
        HasQuotShape L (pCoreOf 2 L : Set X) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard
          {W : Subgroup X | ∃ x ∈ pCoreOf 2 L, W = conjSubgroup (Subgroup.zpowers s) x} := by
  rintro X _ _ s hs hD ⟨Lh, hsZ, hsQ, hgenLh, ⟨Y, hYg, φ, hφs, hφk, ⟨eY⟩⟩, h4⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (fusionOddCore X)) := odd_card_fusionOddCore X
  set π := QuotientGroup.mk' (fusionOddCore X) with hπ
  have hss : s * s = 1 := by rw [← pow_two, ← hs]; exact pow_orderOf_eq_one s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsD : IsConj s s := IsConj.refl s
  have hQhLh : pCoreOf 2 Lh ≤ Lh := openPCoreOf_le 2 Lh
  have hQh2 : IsPGroup 2 (pCoreOf 2 Lh) := by
    rw [openPCoreOf_eq_map_pCore]; exact CFSG.pCore_isPGroup.map _
  have hn : ∀ h ∈ Lh, ∀ x ∈ pCoreOf 2 Lh, h * x * h⁻¹ ∈ pCoreOf 2 Lh := by
    intro h hh x hx
    have hxL : x ∈ Lh := hQhLh hx
    have hk : (⟨x, hxL⟩ : Lh) ∈ CFSG.pCore 2 Lh := (mem_openPCoreOf_iff ⟨x, hxL⟩).mp hx
    have := (CFSG.pCore_normal (p := 2) (G := Lh)).conj_mem _ hk ⟨h, hh⟩
    exact (mem_openPCoreOf_iff (⟨h, hh⟩ * ⟨x, hxL⟩ * (⟨h, hh⟩ : Lh)⁻¹)).mpr this
  have hsLh : π s ∈ Lh := hsZ (Subgroup.mem_zpowers _)
  set P := Lh.comap π with hPdef
  let ψ : P →* Y := φ.comp ((π.comp P.subtype).codRestrict Lh (fun x => x.2))
  have hψ : ∀ (x : X) (hx : x ∈ P), ψ ⟨x, hx⟩ = φ ⟨π x, hx⟩ := fun _ _ => rfl
  have hψk : ∀ (x : X) (hx : x ∈ P), ψ ⟨x, hx⟩ = 1 ↔ π x ∈ pCoreOf 2 Lh :=
    fun x hx => hφk ⟨π x, hx⟩
  have hψeq : ∀ (x y : X) (hx : x ∈ P) (hy : y ∈ P), π x = π y → ψ ⟨x, hx⟩ = ψ ⟨y, hy⟩ := by
    intro x y hx hy h
    rw [hψ, hψ]
    congr 1
    exact Subtype.ext h
  have hsP : s ∈ P := hsLh
  set σ := ψ ⟨s, hsP⟩ with hσ
  have hσ1 : σ ≠ 1 := fun h => hsQ ((Subgroup.zpowers_le).mpr ((hψk s hsP).mp h))
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨s, hsP⟩ : P) * ⟨s, hsP⟩ = 1 := Subtype.ext hss
    rw [this, map_one]
  obtain ⟨g, hdP, hτ⟩ : ∃ g : X, ∃ hdP : g⁻¹ * s * g ∈ P,
      ψ ⟨_, hdP⟩ ∉ Subgroup.zpowers σ := by
    by_contra hcon
    push Not at hcon
    set K := ((Subgroup.zpowers σ).comap φ).map Lh.subtype with hK
    have hLK : Lh ≤ K := by
      conv_lhs => rw [← hgenLh]
      refine iSup₂_le fun y hy => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore X) y
      rw [conjSubgroup_zpowers,
        show (π g)⁻¹ * π s * π g = π (g⁻¹ * s * g) by simp [map_mul, map_inv]] at hy ⊢
      have hdP : g⁻¹ * s * g ∈ P := hy (Subgroup.mem_zpowers _)
      rw [Subgroup.zpowers_le]
      exact ⟨⟨_, hdP⟩, hcon g hdP, rfl⟩
    have hall : ∀ y : Y, y = 1 ∨ y = σ := by
      intro y
      obtain ⟨ℓ, rfl⟩ := hφs y
      obtain ⟨ℓ', hℓ', hℓℓ'⟩ := hLK ℓ.2
      have : ℓ' = ℓ := Subtype.ext hℓℓ'
      subst this
      exact mem_zpowers_sq hσσ hℓ'
    obtain ⟨c, hc1, hcσ⟩ := perm3' (eY σ)
    rcases hall (eY.symm c) with h | h
    · apply hc1; rw [← eY.apply_symm_apply c, h, map_one]
    · apply hcσ; rw [← eY.apply_symm_apply c, h]
  set d := g⁻¹ * s * g with hd
  set τ := ψ ⟨d, hdP⟩ with hτdef
  have hdd : d * d = 1 := by
    calc d * d = g⁻¹ * (s * s) * g := by rw [hd]; group
      _ = 1 := by rw [hss]; group
  have hττ : τ * τ = 1 := by
    rw [hτdef, ← map_mul]
    have : (⟨d, hdP⟩ : P) * ⟨d, hdP⟩ = 1 := Subtype.ext hdd
    rw [this, map_one]
  have hτ1 : τ ≠ 1 := fun h => hτ (h ▸ Subgroup.one_mem _)
  have hτσ : σ ≠ τ := fun h => hτ (h ▸ Subgroup.mem_zpowers _)
  obtain ⟨h3, h2, hwords⟩ := sym3_facts eY hσσ hττ hσ1 hτ1 hτσ
  obtain ⟨Q₀, hQ₀2, hQ₀π⟩ := exists_full (fusionOddCore X) (pCoreOf 2 Lh) hQh2
  obtain ⟨ms, hms, hmsπ⟩ := frattini (fusionOddCore X) hodd Lh (pCoreOf 2 Lh) hn hQ₀2 hQ₀π hsLh
  obtain ⟨hkk, hkπ⟩ := lift_inv (fusionOddCore X) hodd hss hmsπ
  obtain ⟨c, hcN, hcs⟩ := conj_of_mk_eq (fusionOddCore X) hodd hkk hss hkπ
  set Q := conjSubgroup Q₀ c⁻¹ with hQdef
  have hcπ : π c = 1 := (QuotientGroup.eq_one_iff c).mpr hcN
  have hQ2 : IsPGroup 2 Q := hQ₀2.map _
  have hQπ : Q.map π = pCoreOf 2 Lh := by
    rw [hQdef, map_conjSubgroup, hQ₀π, map_inv, hcπ, inv_one, CFSG.Quasithin.conjSubgroup_one]
  have hsN : s ∈ Subgroup.normalizer (Q : Set X) := by
    have h1 : ms ^ Nat.card (fusionOddCore X) ∈ Subgroup.normalizer (Q₀ : Set X) :=
      Subgroup.pow_mem _ hms _
    have h2 := mem_normalizer_conj h1 c
    rw [hcs] at h2
    convert h2 using 1
    group
  obtain ⟨m, hm, hmπ⟩ := frattini (fusionOddCore X) hodd Lh (pCoreOf 2 Lh) hn hQ2 hQπ hdP
  obtain ⟨hkk', hk'π⟩ := lift_inv (fusionOddCore X) hodd hdd hmπ
  obtain ⟨c', -, hc'⟩ := conj_of_mk_eq (fusionOddCore X) hodd hkk' hdd hk'π
  set a := m ^ Nat.card (fusionOddCore X) with ha
  have haa : a * a = 1 := hkk'
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haD : IsConj s a := isConj_of_eq (c := g * c') (by rw [hc', hd]; group)
  have haN : a ∈ Subgroup.normalizer (Q : Set X) := Subgroup.pow_mem _ hm _
  have haP : a ∈ P := by show π a ∈ Lh; rw [hk'π]; exact hdP
  have hτ' : ψ ⟨a, haP⟩ = τ := hψeq a d haP hdP hk'π
  set r := s * a with hr
  have hrP : r ∈ P := P.mul_mem hsP haP
  have hψr : ψ ⟨r, hrP⟩ = σ * τ := by rw [← hτ']; exact map_mul ψ ⟨s, hsP⟩ ⟨a, haP⟩
  have hodd_r : Odd (orderOf r) := by
    rcases hD.2 s hsD a haD with h | h
    · exfalso; apply h2
      rw [← hψr, ← map_pow]
      have hr2 : r ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
      have : (⟨r, hrP⟩ : P) ^ 2 = 1 := Subtype.ext (by simpa using hr2)
      rw [this, map_one]
    · exact h
  have hrn : r ^ orderOf r = 1 := pow_orderOf_eq_one r
  set y := r ^ 3 with hy
  have hyN : y ∈ fusionOddCore X := by
    have hy3P : y ∈ P := P.pow_mem hrP 3
    have hy3 : π y ∈ pCoreOf 2 Lh := by
      refine (hψk y hy3P).mp ?_
      have : (⟨y, hy3P⟩ : P) = (⟨r, hrP⟩ : P) ^ 3 := Subtype.ext (by simp [hy])
      rw [this, map_pow, hψr, h3]
    obtain ⟨i, hi⟩ := two_elem_of_isPGroup hQh2 hy3
    have : π y = 1 := eq_one_of_pow_two_pow_of_odd hi hodd_r (by
      rw [← map_pow, hy, ← pow_mul, mul_comm, pow_mul, hrn, one_pow, map_one])
    exact (QuotientGroup.eq_one_iff y).mp this
  have hyNorm : y ∈ Subgroup.normalizer (Q : Set X) :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hsN haN) 3
  have hycomm : ∀ q ∈ Q, y * q = q * y := by
    intro q hq
    have h1 : y * q * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyNorm q).mp hq
    have hz1 : y * q * y⁻¹ * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
    have hz2 : y * q * y⁻¹ * q⁻¹ ∈ fusionOddCore X := by
      have : y * q * y⁻¹ * q⁻¹ = y * (q * y⁻¹ * q⁻¹) := by group
      rw [this]
      exact (fusionOddCore X).mul_mem hyN
        ((fusionOddCore_normal X).conj_mem _ ((fusionOddCore X).inv_mem hyN) q)
    obtain ⟨i, hi⟩ := two_elem_of_isPGroup hQ2 hz1
    have h0 := eq_one_of_two_elem_mem hodd hz2 hi
    calc y * q = y * q * y⁻¹ * q⁻¹ * (q * y) := by group
      _ = q * y := by rw [h0, one_mul]
  have hsrs : s * r * s⁻¹ = r⁻¹ := by
    rw [hr, hsinv, mul_inv_rev, hainv, hsinv, ← mul_assoc, hss, one_mul]
  have hsyD : IsConj s (s * y) := by
    have hsys : s * y * s⁻¹ = y⁻¹ := by rw [hy, ← conj_pow, hsrs, inv_pow]
    have hsy2 : s * y * (s * y) = 1 := by
      calc s * y * (s * y) = (s * y * s⁻¹) * y := by rw [hsinv]; group
        _ = 1 := by rw [hsys, inv_mul_cancel]
    have hpow : (s * (s * y)) ^ orderOf r = 1 := by
      rw [← mul_assoc, hss, one_mul, hy, ← pow_mul, mul_comm, pow_mul, hrn, one_pow]
    obtain ⟨j, hj⟩ := dihedral_conj hss hsy2 hodd_r hpow
    exact isConj_of_eq hj
  obtain ⟨q, hq, hqs⟩ : ∃ q ∈ Q, q⁻¹ * s * q ≠ s := by
    by_contra hcon
    push Not at hcon
    have hsub : {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
        W = conjSubgroup (Subgroup.zpowers (π s)) x} ⊆ {Subgroup.zpowers (π s)} := by
      rintro W ⟨x, hx, rfl⟩
      rw [← hQπ] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [Set.mem_singleton_iff, conjSubgroup_zpowers, ← map_inv, ← map_mul, ← map_mul,
        hcon q hq]
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at this
    omega
  have hc0Q : s * (q⁻¹ * s * q) ∈ Q := by
    have h1 : s * q⁻¹ * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hsN _).mp (Q.inv_mem hq)
    have : s * (q⁻¹ * s * q) = s * q⁻¹ * s⁻¹ * q := by rw [hsinv]; group
    rw [this]; exact Q.mul_mem h1 hq
  have hc01 : s * (q⁻¹ * s * q) ≠ 1 := by
    intro h; apply hqs
    rw [eq_inv_of_mul_eq_one_right h, hsinv]
  have hd2D : IsConj s (q⁻¹ * s * q * y) := by
    refine hsyD.trans (isConj_iff.mpr ⟨q⁻¹, ?_⟩)
    have := hycomm q hq
    calc q⁻¹ * (s * y) * q⁻¹⁻¹ = q⁻¹ * s * (y * q) := by group
      _ = q⁻¹ * s * (q * y) := by rw [this]
      _ = q⁻¹ * s * q * y := by group
  have hy1 : y = 1 := by
    obtain ⟨i, hi⟩ := two_elem_of_isPGroup hQ2 hc0Q
    have hcomm : s * (q⁻¹ * s * q) * y = y * (s * (q⁻¹ * s * q)) := (hycomm _ hc0Q).symm
    have hor := hD.2 s hsD _ hd2D
    have heq : s * (q⁻¹ * s * q * y) = s * (q⁻¹ * s * q) * y := by group
    rw [heq] at hor
    exact eq_one_of_commute_two_odd hodd hi hc01 hyN hcomm hor
  have hr3 : r ^ 3 = 1 := by rw [← hy, hy1]
  set H := Subgroup.zpowers r ⊔ Subgroup.zpowers s with hH
  set L := Q ⊔ H with hL
  have hHnorm : H ≤ Subgroup.normalizer (Q : Set X) :=
    sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mul_mem _ hsN haN))
      ((Subgroup.zpowers_le).mpr hsN)
  have hsnr : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers r : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Subgroup.mem_zpowers_iff.mpr ⟨-k, by rw [zpow_neg, ← conj_zpow, hsrs, inv_zpow]⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      have e1 : h = s * (r ^ k) * s⁻¹ := by
        calc h = (s * s) * h * (s * s) := by rw [hss]; group
          _ = s * (s * h * s⁻¹) * s⁻¹ := by rw [hsinv]; group
          _ = s * (r ^ k) * s⁻¹ := by rw [hk]
      rw [e1, zpow_neg, ← conj_zpow, hsrs, inv_zpow]
  have hcardH : Nat.card H ≤ 3 * 2 := by
    have h := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers r)
      (Subgroup.zpowers s) hsnr
    calc Nat.card H = Nat.card ((Subgroup.zpowers r : Set X) * (Subgroup.zpowers s : Set X)) := by
          rw [← h]; rfl
      _ ≤ Nat.card (Subgroup.zpowers r : Set X) * Nat.card (Subgroup.zpowers s : Set X) :=
          Set.natCard_mul_le
      _ ≤ 3 * 2 := by
          apply Nat.mul_le_mul
          · show Nat.card (Subgroup.zpowers r) ≤ 3
            rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) hr3
          · show Nat.card (Subgroup.zpowers s) ≤ 2
            rw [Nat.card_zpowers, hs]
  have hcardL : Nat.card L ≤ Nat.card Q * 6 := by
    have h := Subgroup.coe_mul_of_right_le_normalizer_left Q H hHnorm
    calc Nat.card L = Nat.card ((Q : Set X) * (H : Set X)) := by rw [← h]; rfl
      _ ≤ Nat.card (Q : Set X) * Nat.card (H : Set X) := Set.natCard_mul_le
      _ ≤ Nat.card Q * 6 := Nat.mul_le_mul le_rfl hcardH
  have hcardLh : Nat.card Lh = Nat.card (pCoreOf 2 Lh) * 6 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hφs
    have hY : Nat.card Y = 6 := by
      rw [Nat.card_congr eY.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hker : φ.ker = CFSG.pCore 2 Lh := by
      ext k
      rw [MonoidHom.mem_ker, hφk, SetLike.mem_coe, mem_openPCoreOf_iff]
    have hker' : Nat.card φ.ker = Nat.card (pCoreOf 2 Lh) := by
      rw [hker, openPCoreOf_eq_map_pCore, Subgroup.card_map_of_injective Lh.subtype_injective]
    rw [← h1, hker', hY]
  have hcardQ : Nat.card Q ≤ Nat.card (pCoreOf 2 Lh) := by
    have hf : ∀ x : Q, π x ∈ pCoreOf 2 Lh := by
      intro x; rw [← hQπ]; exact Subgroup.mem_map_of_mem π x.2
    refine Nat.card_le_card_of_injective (fun x : Q => (⟨π x, hf x⟩ : pCoreOf 2 Lh)) ?_
    intro x x' hxx
    have h1 : π x = π x' := congrArg Subtype.val hxx
    have hz : (x : X)⁻¹ * x' ∈ fusionOddCore X := QuotientGroup.eq.mp h1
    obtain ⟨i, hi⟩ := two_elem_of_isPGroup hQ2 (Q.mul_mem (Q.inv_mem x.2) x'.2)
    have := eq_one_of_two_elem_mem hodd hz hi
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have hQP : Q ≤ P := by
    intro x hx
    show π x ∈ Lh
    apply hQhLh; rw [← hQπ]; exact Subgroup.mem_map_of_mem π hx
  have hLP : L ≤ P :=
    sup_le hQP (sup_le ((Subgroup.zpowers_le).mpr hrP) ((Subgroup.zpowers_le).mpr hsP))
  have hsL : s ∈ L := (le_sup_right : H ≤ L) ((le_sup_right : _ ≤ H) (Subgroup.mem_zpowers s))
  have hrL : r ∈ L := (le_sup_right : H ≤ L) ((le_sup_left : _ ≤ H) (Subgroup.mem_zpowers r))
  have haL : a ∈ L := by
    have : a = s⁻¹ * r := by rw [hr]; group
    rw [this]; exact L.mul_mem (L.inv_mem hsL) hrL
  have hQL : Q ≤ L := le_sup_left
  have hlift : ∀ (w : X) (hw : w ∈ L) (ℓ : X ⧸ fusionOddCore X) (hℓ : ℓ ∈ Lh),
      ψ ⟨w, hLP hw⟩ = φ ⟨ℓ, hℓ⟩ → ∃ x ∈ L, π x = ℓ := by
    intro w hw ℓ hℓ h
    have hk : (π w)⁻¹ * ℓ ∈ pCoreOf 2 Lh := by
      have := (hφk ((⟨π w, hLP hw⟩ : Lh)⁻¹ * ⟨ℓ, hℓ⟩)).mp
        (by rw [map_mul, map_inv, ← hψ, h, inv_mul_cancel])
      simpa using this
    rw [← hQπ] at hk
    obtain ⟨q, hq, hqe⟩ := hk
    refine ⟨w * q, L.mul_mem hw (hQL hq), ?_⟩
    rw [map_mul, hqe, mul_inv_cancel_left]
  have hsurj : ∀ ℓ ∈ Lh, ∃ x ∈ L, π x = ℓ := by
    intro ℓ hℓ
    rcases hwords (φ ⟨ℓ, hℓ⟩) with h | h | h | h | h | h
    · exact hlift 1 L.one_mem ℓ hℓ (by rw [h]; exact map_one ψ)
    · exact hlift s hsL ℓ hℓ (by rw [h])
    · exact hlift a haL ℓ hℓ (by rw [h, ← hτ'])
    · exact hlift (s * a) (L.mul_mem hsL haL) ℓ hℓ
        (by rw [h, ← hτ']; exact map_mul ψ ⟨s, hsP⟩ ⟨a, haP⟩)
    · exact hlift (a * s) (L.mul_mem haL hsL) ℓ hℓ
        (by rw [h, ← hτ']; exact map_mul ψ ⟨a, haP⟩ ⟨s, hsP⟩)
    · exact hlift (s * a * s) (L.mul_mem (L.mul_mem hsL haL) hsL) ℓ hℓ
        (by rw [h, ← hτ', ← map_mul, ← map_mul]; rfl)
  let πL : L →* Lh := (π.comp L.subtype).codRestrict Lh (fun x => hLP x.2)
  have hπLs : Function.Surjective πL := by
    rintro ⟨ℓ, hℓ⟩
    obtain ⟨x, hx, hxℓ⟩ := hsurj ℓ hℓ
    exact ⟨⟨x, hx⟩, Subtype.ext hxℓ⟩
  have hbij : Function.Bijective πL :=
    hπLs.bijective_of_nat_card_le (by rw [hcardLh]; exact hcardL.trans (by omega))
  let e : L ≃* Lh := MulEquiv.ofBijective πL hbij
  have he : ∀ x : L, ((e x : Lh) : X ⧸ fusionOddCore X) = π x := fun _ => rfl
  have hpc : ∀ k : L, (k : X) ∈ pCoreOf 2 L ↔
      ((e k : Lh) : X ⧸ fusionOddCore X) ∈ pCoreOf 2 Lh := by
    intro k
    rw [mem_openPCoreOf_iff, mem_openPCoreOf_iff, ← CFSG.pCore_map_iso 2 e]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hgen : (⨆ (x : X) (_ : conjSubgroup (Subgroup.zpowers s) x ≤ L),
      conjSubgroup (Subgroup.zpowers s) x) = L := by
    set S := ⨆ (x : X) (_ : conjSubgroup (Subgroup.zpowers s) x ≤ L),
      conjSubgroup (Subgroup.zpowers s) x with hS
    have hSL : S ≤ L := iSup₂_le fun _ h => h
    have hLhS : Lh ≤ S.map π := by
      conv_lhs => rw [← hgenLh]
      refine iSup₂_le fun yh hyh => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore X) yh
      rw [conjSubgroup_zpowers,
        show (π g)⁻¹ * π s * π g = π (g⁻¹ * s * g) by simp [map_mul, map_inv]] at hyh ⊢
      have hdP' : π (g⁻¹ * s * g) ∈ Lh := hyh (Subgroup.mem_zpowers _)
      have hdd' : g⁻¹ * s * g * (g⁻¹ * s * g) = 1 := by
        calc g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
          _ = 1 := by rw [hss]; group
      set t := e.symm ⟨π (g⁻¹ * s * g), hdP'⟩ with ht
      have het : e t = ⟨π (g⁻¹ * s * g), hdP'⟩ := e.apply_symm_apply _
      have htπ : π t = π (g⁻¹ * s * g) := congrArg Subtype.val het
      have htt : (t : X) * t = 1 := by
        have h1 : e (t * t) = e 1 := by
          rw [map_mul, het, map_one]
          exact Subtype.ext (by
            show π (g⁻¹ * s * g) * π (g⁻¹ * s * g) = 1
            rw [← map_mul, hdd', map_one])
        exact congrArg Subtype.val (e.injective h1)
      obtain ⟨c, -, hc⟩ := conj_of_mk_eq (fusionOddCore X) hodd htt hdd' htπ
      have hgt : (g * c)⁻¹ * s * (g * c) = t := by rw [hc]; group
      have hCL : conjSubgroup (Subgroup.zpowers s) (g * c) ≤ L := by
        rw [conjSubgroup_zpowers, Subgroup.zpowers_le, hgt]; exact t.2
      have htS : (t : X) ∈ S := by
        have := le_iSup₂ (f := fun x (_ : conjSubgroup (Subgroup.zpowers s) x ≤ L) =>
          conjSubgroup (Subgroup.zpowers s) x) (g * c) hCL
        apply this
        rw [conjSubgroup_zpowers, hgt]
        exact Subgroup.mem_zpowers _
      rw [Subgroup.zpowers_le]
      exact ⟨t, htS, htπ⟩
    apply le_antisymm hSL
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hLhS (hLP hx)
    have : (⟨z, hSL hz⟩ : L) = ⟨x, hx⟩ := e.injective (Subtype.ext hzx)
    have hxz : z = x := congrArg Subtype.val this
    rw [← hxz]; exact hz
  have h4L : 4 ≤ Set.ncard
      {W : Subgroup X | ∃ x ∈ pCoreOf 2 L, W = conjSubgroup (Subgroup.zpowers s) x} := by
    refine h4.trans ?_
    set A := {W : Subgroup X | ∃ x ∈ pCoreOf 2 L, W = conjSubgroup (Subgroup.zpowers s) x}
      with hA
    have hAfin : A.Finite := (Set.finite_range fun x : X =>
      conjSubgroup (Subgroup.zpowers s) x).subset (by rintro W ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
    have hsub : {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
        W = conjSubgroup (Subgroup.zpowers (π s)) x} ⊆ (fun W => W.map π) '' A := by
      rintro W ⟨xh, hxh, rfl⟩
      have hxhL : xh ∈ Lh := hQhLh hxh
      set k := e.symm ⟨xh, hxhL⟩ with hkdef
      have hek : e k = ⟨xh, hxhL⟩ := e.apply_symm_apply _
      have hkπ : π k = xh := congrArg Subtype.val hek
      have hkL : (k : X) ∈ pCoreOf 2 L := (hpc k).mpr (by rw [hek]; exact hxh)
      refine ⟨conjSubgroup (Subgroup.zpowers s) k, ⟨k, hkL, rfl⟩, ?_⟩
      show (conjSubgroup (Subgroup.zpowers s) k).map π = _
      rw [map_conjSubgroup, MonoidHom.map_zpowers, hkπ]
    calc _ ≤ ((fun W => W.map π) '' A).ncard := Set.ncard_le_ncard hsub (hAfin.image _)
      _ ≤ A.ncard := Set.ncard_image_le hAfin
  refine ⟨L, (Subgroup.zpowers_le).mpr hsL, hgen,
    ⟨Y, hYg, φ.comp e.toMonoidHom, hφs.comp e.surjective, fun k => ?_, ⟨eY⟩⟩, h4L⟩
  exact (hφk (e k)).trans (hpc k).symm

end CFSG.LocalAnalysis.WeakClosure81
