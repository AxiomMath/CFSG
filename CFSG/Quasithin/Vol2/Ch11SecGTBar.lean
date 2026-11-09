module

public import CFSG.Quasithin.Vol2.Ch11SecGTCore
public import CFSG.Quasithin.Vol2.Ch11SecGTransv

section

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open

variable {G : Type} [Group G]

theorem inv_pow_mem_centralizer {Y : Subgroup G} {a x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) (k : ℕ) :
    a * x ^ k * a⁻¹ * x ^ k ∈ Subgroup.centralizer (Y : Set G) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := conj_mem_centralizer (inv_mem (pow_mem hx k)) hinv
    have e : a * x ^ (k + 1) * a⁻¹ * x ^ (k + 1) = (a * x ^ k * a⁻¹ * x ^ k) *
        ((x ^ k)⁻¹ * (a * x * a⁻¹ * x) * ((x ^ k)⁻¹)⁻¹) := by
      rw [pow_succ]
      group
    rw [e]
    exact mul_mem ih h1

theorem inv_inv_mem_centralizer {Y : Subgroup G} {a w : G}
    (hw : w ∈ Subgroup.normalizer (Y : Set G))
    (hinv : a * w * a⁻¹ * w ∈ Subgroup.centralizer (Y : Set G)) :
    a * w⁻¹ * a⁻¹ * w⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
  have h1 := conj_mem_centralizer hw hinv
  have e : a * w⁻¹ * a⁻¹ * w⁻¹ = (w * (a * w * a⁻¹ * w) * w⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

theorem inv_mem_centralizer_commutator' {Y : Subgroup G} {a z : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hz : z ∈ Subgroup.normalizer (Y : Set G))
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) :
    a * (a * z * a⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) ∈
      Subgroup.centralizer (Y : Set G) := by
  have hw : z * a * z⁻¹ * a⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    mul_mem (mul_mem (mul_mem hz ha) (inv_mem hz)) (inv_mem ha)
  have h := inv_inv_mem_centralizer hw (inv_mem_centralizer_commutator ha hz ha2)
  have e : a * z * a⁻¹ * z⁻¹ = (z * a * z⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact h

theorem mem_centralizer_of_inv_of_primes {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) {m : ℕ} (hm : 0 < m)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ m → 5 ≤ r) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hxm : x ^ m ∈ Subgroup.centralizer (Y : Set G))
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) :
    x ∈ Subgroup.centralizer (Y : Set G) := by
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases h1 : m = 1
    · rw [h1, pow_one] at hxm
      exact hxm
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨m', rfl⟩ := hrm
    have hm' : 0 < m' := Nat.pos_of_mul_pos_left hm
    have hu : x ^ m' ∈ Subgroup.centralizer (Y : Set G) := by
      refine mem_centralizer_of_inv hY ha (pow_mem hx m') hy₀ htr hr (hprimes r hr
        (dvd_mul_right r m')) ?_ (inv_pow_mem_centralizer hx hinv m')
      rwa [← pow_mul, mul_comm]
    have hlt : m' < r * m' := by
      have := hr.two_le
      nlinarith
    exact ih m' hlt hm' (fun s hs hsm => hprimes s hs (dvd_mul_of_dvd_right hsm r)) hx hu hinv

theorem exists_two_pow_mem_centralizer {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) {m : ℕ} (hm : 0 < m)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ m → 5 ≤ r) {O : Subgroup G} (hO : IsPGroup 2 O) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hxm : x ^ m ∈ O)
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) :
    ∃ e : ℕ, x ^ 2 ^ e ∈ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨e, he⟩ := hO ⟨x ^ m, hxm⟩
  have he' : (x ^ m) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  refine ⟨e, mem_centralizer_of_inv_of_primes hY ha hy₀ htr hm hprimes (pow_mem hx _) ?_
    (inv_pow_mem_centralizer hx hinv _)⟩
  rw [← pow_mul, mul_comm, pow_mul, he']
  exact one_mem _

end CFSG.Quasithin.Vol2.Ch11.SecG

end

end

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG.Bar

open CFSG.Open

variable {G : Type} [Group G]

abbrev KBar (K : Subgroup G) : Type := ↥K ⧸ CFSG.pCore 2 ↥K

@[expose] noncomputable def autFun (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) :
    MulAut (KBar K) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) (conjK K g)
    (CFSG.pCore_map_iso 2 (conjK K g))

theorem autFun_mk (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    autFun K g (k : KBar K) = ((conjK K g k : ↥K) : KBar K) :=
  QuotientGroup.congr_mk _ _ _ _ k

@[expose] noncomputable def aut (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (KBar K) where
  toFun := autFun K
  map_one' := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [autFun_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' g₁ g₂ := by
    ext x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, autFun_mk, autFun_mk, autFun_mk, map_mul, MulAut.mul_apply]

theorem aut_mk (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    aut K g (k : KBar K) = ((conjK K g k : ↥K) : KBar K) :=
  autFun_mk K g k

theorem commK_mem {K : Subgroup G} {a z : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hz : z ∈ K) : a * z * a⁻¹ * z⁻¹ ∈ K :=
  K.mul_mem ((Subgroup.mem_normalizer_iff.mp ha z).mp hz) (K.inv_mem hz)

theorem mk_commK {K : Subgroup G} {a z : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hz : z ∈ K) :
    (((⟨a * z * a⁻¹ * z⁻¹, commK_mem ha hz⟩ : ↥K)) : KBar K) =
      aut K ⟨a, ha⟩ ((⟨z, hz⟩ : ↥K) : KBar K) * (((⟨z, hz⟩ : ↥K) : KBar K))⁻¹ := by
  rw [aut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

theorem comm_mem_of_aut_eq_one {K : Subgroup G} {g : ↥(Subgroup.normalizer (K : Set G))}
    (h : aut K g = 1) (k : G) (hk : k ∈ K) :
    (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ (CFSG.pCore 2 ↥K).map K.subtype := by
  have h1 := congrArg (fun α : MulAut (KBar K) => α ((⟨k, hk⟩ : ↥K) : KBar K)) h
  simp only [aut_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq_iff_div_mem] at h1
  exact ⟨_, h1, by simp [div_eq_mul_inv]⟩

theorem commutator_top_eq_top {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅(⊤ : Subgroup (KBar K)), (⊤ : Subgroup (KBar K))⁆ = ⊤ := by
  have hsub : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK' : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hsub, hK]
  have hsurj := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)
  rw [← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator, hK']

theorem le_center_of_commute {K L₁ : Subgroup G} (hL : L₁ ≤ K)
    (hcl : CFSG.Quasithin.conjClosure L₁ K = K) {N : Subgroup (KBar K)} [N.Normal]
    (hN : ∀ n ∈ N, ∀ l (hl : l ∈ L₁), n * ((⟨l, hL hl⟩ : ↥K) : KBar K) =
      ((⟨l, hL hl⟩ : ↥K) : KBar K) * n) :
    N ≤ Subgroup.center (KBar K) := by
  set D : Subgroup G := ((Subgroup.centralizer (N : Set (KBar K))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype with hD
  have hLD : ∀ l (hl : l ∈ L₁), ((⟨l, hL hl⟩ : ↥K) : KBar K) ∈
      Subgroup.centralizer (N : Set (KBar K)) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact hN n hn l hl
  have hKD : K ≤ D := by
    rw [← hcl]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨h, hh, z, hz, rfl⟩
    refine ⟨⟨h, hh⟩ * ⟨z, hL hz⟩ * (⟨h, hh⟩ : ↥K)⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.normal_centralizer (H := N)).conj_mem _ (hLD z hz) _
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k', hk', hkk'⟩ := hKD k.2
  have hk'' : k' = k := Subtype.ext hkk'
  subst hk''
  exact ((Subgroup.mem_centralizer_iff.mp hk') n hn).symm

@[expose] def cBar (K Y : Subgroup G) : Subgroup (KBar K) :=
  ((K ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

theorem mk_mem_cBar {K Y : Subgroup G} {k : ↥K}
    (hk : (k : G) ∈ Subgroup.centralizer (Y : Set G)) : (k : KBar K) ∈ cBar K Y :=
  ⟨k, ⟨k.2, hk⟩, rfl⟩

theorem cBar_normal {K Y : Subgroup G} (hKY : K ≤ Subgroup.normalizer (Y : Set G)) :
    (cBar K Y).Normal := by
  apply Subgroup.Normal.map _ _ (QuotientGroup.mk'_surjective _)
  constructor
  intro c hc k
  rw [Subgroup.mem_subgroupOf] at hc ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact ⟨K.mul_mem (K.mul_mem k.2 hc.1) (K.inv_mem k.2), conj_mem_centralizer (hKY k.2) hc.2⟩

theorem commK_mem_cBar [Finite G] {K Y : Subgroup G} (hY : IsElemAbelian 2 Y)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) {a y₀ : G}
    (haY : a ∈ Subgroup.normalizer (Y : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hy₀ : y₀ ∈ Y) (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀)
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) {z : G} (hz : z ∈ K) {m : ℕ} (hm : 0 < m)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ m → 5 ≤ r)
    (hxm : (((⟨a * z * a⁻¹ * z⁻¹, commK_mem haK hz⟩ : ↥K)) : KBar K) ^ m = 1) :
    (((⟨a * z * a⁻¹ * z⁻¹, commK_mem haK hz⟩ : ↥K)) : KBar K) ∈ cBar K Y := by
  set x : ↥K := ⟨a * z * a⁻¹ * z⁻¹, commK_mem haK hz⟩ with hxdef
  have hxP : x ^ m ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.mk_pow] at hxm
    exact (QuotientGroup.eq_one_iff _).mp hxm
  have hxO : (x : G) ^ m ∈ (CFSG.pCore 2 ↥K).map K.subtype := ⟨x ^ m, hxP, by simp⟩
  have hO : IsPGroup 2 ((CFSG.pCore 2 ↥K).map K.subtype) := CFSG.pCore_isPGroup.map K.subtype
  have hinv : a * (x : G) * a⁻¹ * (x : G) ∈ Subgroup.centralizer (Y : Set G) :=
    inv_mem_centralizer_commutator' haY (hKY hz) ha2
  obtain ⟨e, he⟩ := exists_two_pow_mem_centralizer hY haY hy₀ htr hm hprimes hO (hKY x.2) hxO hinv
  have h1 : (x : KBar K) ^ 2 ^ e ∈ cBar K Y := by
    rw [← QuotientGroup.mk_pow]
    exact mk_mem_cBar (by simpa using he)
  have h2 : (x : KBar K) ^ m ∈ cBar K Y := by
    rw [hxm]
    exact one_mem _
  have hodd : Odd m := by
    rcases Nat.even_or_odd m with h | h
    · have := hprimes 2 Nat.prime_two (even_iff_two_dvd.mp h)
      omega
    · exact h
  have h3 := pow_gcd_mem h1 h2
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)),
    pow_one] at h3

end CFSG.Quasithin.Vol2.Ch11.SecG.Bar
