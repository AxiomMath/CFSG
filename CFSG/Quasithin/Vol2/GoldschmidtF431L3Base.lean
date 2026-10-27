module

public import CFSG.Quasithin.Recognition.F4Local
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem centerOf_conjSub (g : G) (S : Subgroup G) :
    centerOf (conjSub g S) = conjSub g (centerOf S) := by
  unfold centerOf
  rw [conjSub_inf, conjSub_centralizer]

theorem card_conjSub (g : G) (K : Subgroup G) : Nat.card (conjSub g K) = Nat.card K :=
  Nat.card_congr (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.toEquiv

theorem conj_sq (g x : G) : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
  simp only [pow_two]; group

theorem conj_ne_one' {g x : G} (h : x ≠ 1) : g⁻¹ * x * g ≠ 1 := by
  intro h1; apply h
  have := congrArg (fun y => g * y * g⁻¹) h1
  simpa [mul_assoc] using this

theorem conj_commute {g x y : G} (h : x * y = y * x) :
    (g⁻¹ * x * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * x * g) := by
  have e1 : (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
  have e2 : (g⁻¹ * y * g) * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
  rw [e1, e2, h]

theorem isSylowTwoOf_top_of_centralizer_le [Finite G] {S M : Subgroup G} (hS : IsSylowTwoOf S M)
    (hw : ∃ w ∈ centerOf S, w ≠ 1)
    (hZ : ∀ w ∈ centerOf S, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ M) :
    IsSylowTwoOf S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := hS.2.1
  by_contra hnot
  obtain ⟨S', hSS'⟩ := hSp.exists_le_sylow
  have hne : S ≠ (S' : Subgroup G) := by
    intro h
    apply hnot
    refine F7.isSylowTwoOf_of_relIndex le_top hSp ?_
    rw [Subgroup.relIndex_top_right, h]
    exact S'.not_dvd_index
  obtain ⟨n, hnS', hnN, hnS⟩ := exists_mem_normalizer_not_mem_of_isPGroup S'.isPGroup' hSS' hne
  set N : Subgroup G := S ⊔ Subgroup.zpowers n with hN
  have hNS' : N ≤ S' := sup_le hSS' (Subgroup.zpowers_le.2 hnS')
  have hNp : IsPGroup 2 N := S'.isPGroup'.to_le hNS'
  have hNnorm : N ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hnN)
  have hnN' : n ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hSN : S ≤ N := le_sup_left
  have : Group.IsNilpotent N := hNp.isNilpotent
  set Z0 : Subgroup N := (centerOf S).subgroupOf N with hZ0
  have hZ0n : Z0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
    have hgn : (g : G) ∈ Subgroup.normalizer (S : Set G) := hNnorm g.2
    have hgn' : (g : G)⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normalizer (S : Set G)).inv_mem hgn
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp hgn _).mp hxS
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (g : G)⁻¹ * y * (g : G) ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp hgn' y).mp hy
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hy'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc y * ((g : G) * (x : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * y * (g : G)) * (x : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((x : G) * ((g : G)⁻¹ * y * (g : G))) * (g : G)⁻¹ := by rw [hcomm]
        _ = (g : G) * (x : G) * (g : G)⁻¹ * y := by group
  obtain ⟨w0, hw0S, hw01⟩ := hw
  have hZ0ne : Z0 ≠ ⊥ := by
    intro h
    have hmem : (⟨w0, hSN (Subgroup.mem_inf.mp hw0S).1⟩ : N) ∈ Z0 :=
      Subgroup.mem_subgroupOf.mpr hw0S
    rw [h, Subgroup.mem_bot] at hmem
    exact hw01 (congrArg Subtype.val hmem)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ0ne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have haC : (a : N) ∈ Subgroup.center N := a.2.2
  have haZ : ((a : N) : G) ∈ centerOf S := Subgroup.mem_subgroupOf.mp (a.2.1 : (a : N) ∈ Z0)
  have ha1 : ((a : N) : G) ≠ 1 := by
    intro h
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hcent : ∀ x ∈ N, x * ((a : N) : G) = ((a : N) : G) * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp haC ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hNM : N ≤ M := fun x hx =>
    hZ _ haZ ha1 (by rw [Subgroup.mem_centralizer_singleton_iff]; exact hcent x hx)
  have hNeq := eq_of_isSylowTwoOf_of_isPGroup hS hSN hNM hNp
  exact hnS (hNeq ▸ hnN')

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext x; simp [mem_conjSub]

theorem conjSub_eq_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : conjSub g K = K := by
  ext x
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg)) x
  simpa using this.symm

theorem mem_normalizer_of_conjSub_eq {g : G} {K : Subgroup G} (h : conjSub g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ conjSub g K := mul_mem_conjSub hx
    rwa [h] at this
  · intro hx
    have h' : g * x * g⁻¹ ∈ conjSub g K := by rw [h]; exact hx
    have h2 := mem_conjSub.mp h'
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2

theorem normal_sylow_fusion [Finite G] {T A B : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hA : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hB : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) {x : G}
    (hx : conjSub x A = B) : ∃ n ∈ Subgroup.normalizer (T : Set G), conjSub n A = B := by
  set N : Subgroup G := Subgroup.normalizer (B : Set G) with hN
  have hTN : T ≤ N := by
    intro t ht
    rw [hN, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hB t ht y hy, fun hy => ?_⟩
    have := hB t⁻¹ (T.inv_mem ht) _ hy
    simpa [mul_assoc] using this
  have hPN : conjSub x T ≤ N := by
    intro p hp
    rw [mem_conjSub] at hp
    rw [hN, Subgroup.mem_normalizer_iff]
    intro y
    have e : x⁻¹ * (p * y * p⁻¹) * x = (x⁻¹ * p * x) * (x⁻¹ * y * x) * (x⁻¹ * p * x)⁻¹ := by group
    rw [← hx, mem_conjSub, mem_conjSub, e]
    refine ⟨fun hy => hA _ hp _ hy, fun hy => ?_⟩
    have := hA _ (T.inv_mem hp) _ hy
    simpa [mul_assoc] using this
  have hTsyl : IsSylowTwoOf T N := F7.isSylowTwoOf_mono_right hT hTN le_top
  have hPsyl : IsSylowTwoOf (conjSub x T) ⊤ := by
    have := F7.isSylowTwoOf_conj hT x
    rwa [conjSub_top] at this
  obtain ⟨y, hyN, hy⟩ := F7.isSylowTwoOf_exists_conj_le hTsyl hPN hPsyl.2.1
  have hyeq : conjSub y T = conjSub x T :=
    eq_of_isSylowTwoOf_of_isPGroup hPsyl hy le_top (F7.isPGroup_conjSub hT.2.1)
  refine ⟨y⁻¹ * x, ?_, ?_⟩
  · apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, ← hyeq, conjSub_conjSub_inv]
  · rw [conjSub_mul, hx,
      conjSub_eq_of_mem_normalizer ((Subgroup.normalizer (B : Set G)).inv_mem hyN)]

theorem exists_klein_four [Finite G] {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (h4 : 4 ≤ Nat.card Q) : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 Q := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h2 : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (F7.isElemAbelian_pow_eq_one hQ g.2)
    have h2' : orderOf (g : G) ∣ 2 ^ 1 := by simpa using h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2'
    exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m ≤ 1 := by omega
    have h2m : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
    rw [← hm] at h2m
    norm_num at h2m
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card Q := by rw [hm]; exact pow_dvd_pow 2 hm2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q) 2 hdvd
  refine ⟨K.map Q.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hK]; norm_num
  · rintro _ ⟨y, -, rfl⟩
    exact F7.isElemAbelian_pow_eq_one hQ y.2

theorem exists_involution_of_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ x ∈ P, x ≠ 1 ∧ x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    rw [Subgroup.eq_bot_iff_card]
    simpa using hm
  have hdvd : 2 ∣ Nat.card P := by
    rw [hm]; exact dvd_pow_self 2 hm0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hdvd
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    have h2 := congrArg Subtype.val this
    simpa using h2

theorem exists_mul_eq_of_card [Finite G] {N B H : Subgroup G} (hNH : N ≤ H) (hBH : B ≤ H)
    (hdisj : ∀ x ∈ N, x ∈ B → x = 1) (hcard : Nat.card H = Nat.card N * Nat.card B) :
    ∀ h ∈ H, ∃ n ∈ N, ∃ b ∈ B, h = n * b := by
  let f : N × B → H := fun p => ⟨p.1 * p.2, H.mul_mem (hNH p.1.2) (hBH p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨n, hn⟩, ⟨b, hb⟩⟩ ⟨⟨n', hn'⟩, ⟨b', hb'⟩⟩ h
    have h1 : n * b = n' * b' := congrArg Subtype.val h
    have h2 : n'⁻¹ * n = b' * b⁻¹ := by
      calc n'⁻¹ * n = n'⁻¹ * (n * b) * b⁻¹ := by group
        _ = n'⁻¹ * (n' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : n'⁻¹ * n = 1 := hdisj _ (N.mul_mem (N.inv_mem hn') hn)
      (by rw [h2]; exact B.mul_mem hb' (B.inv_mem hb))
    have h4 : n = n' := by
      have : n = n' * (n'⁻¹ * n) := by group
      rw [this, h3, mul_one]
    subst h4
    have h5 : b = b' := by
      have : n⁻¹ * (n * b) = n⁻¹ * (n * b') := by rw [h1]
      simpa using this
    subst h5
    rfl
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hcard])
  intro h hh
  obtain ⟨⟨n, b⟩, hnb⟩ := hbij.2 ⟨h, hh⟩
  exact ⟨n.1, n.2, b.1, b.2, (congrArg Subtype.val hnb).symm⟩

theorem eq_one_of_pgroup_of_odd [Finite G] {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hQ : Odd (Nat.card Q)) {x : G} (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxP]; exact hk
  have h2 : orderOf x ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨x, hxQ⟩ : Q)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf x) := hQ.of_dvd_nat h2
  have hk0 : k = 0 := by
    by_contra hk0
    have : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [← h1] at this
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [hk0, pow_zero] at h1
  exact orderOf_eq_one_iff.mp h1

theorem sq_of_conj_sq {g x : G} (h : (g⁻¹ * x * g) ^ 2 = 1) : x ^ 2 = 1 := by
  have e := conj_sq g x
  rw [h] at e
  have : x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
  rw [this, ← e]; group

theorem exists_pow_two_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
  refine ⟨k, ?_⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx]; exact hk
  rw [← h1]; exact pow_orderOf_eq_one x

theorem no_even_of_rot [Finite G] {r : G} {B : Subgroup G}
    (hrW : r ∈ Subgroup.normalizer (B : Set G))
    (hrot : ∃ b₃ ∈ B, ∀ x ∈ B, r ^ 3 * x * (r ^ 3)⁻¹ = b₃ * x * b₃⁻¹)
    {n : ℕ} (hn : 0 < n) (hnB : r ^ n ∈ B) (hmin : ∀ k, 0 < k → k < n → r ^ k ∉ B) (hn4 : n ≤ 4)
    (hev : Even n)
    (hno : ∀ y : G, y * y = 1 → y ≠ 1 → (∀ b ∈ B, y * b = b * y) → False) : False := by
  obtain ⟨b₃, hb₃, hrot'⟩ := hrot
  have hn24 : n = 2 ∨ n = 4 := by obtain ⟨m, hm⟩ := hev; omega
  have hinner : ∃ b₀ ∈ B, ∀ x ∈ B, r * x * r⁻¹ = b₀ * x * b₀⁻¹ := by
    rcases hn24 with rfl | rfl
    · refine ⟨b₃ * (r ^ 2)⁻¹, B.mul_mem hb₃ (B.inv_mem hnB), fun x hx => ?_⟩
      have hx' : (r ^ 2)⁻¹ * x * r ^ 2 ∈ B := B.mul_mem (B.mul_mem (B.inv_mem hnB) hx) hnB
      have := hrot' _ hx'
      calc r * x * r⁻¹ = r ^ 3 * ((r ^ 2)⁻¹ * x * r ^ 2) * (r ^ 3)⁻¹ := by group
        _ = b₃ * ((r ^ 2)⁻¹ * x * r ^ 2) * b₃⁻¹ := this
        _ = (b₃ * (r ^ 2)⁻¹) * x * (b₃ * (r ^ 2)⁻¹)⁻¹ := by group
    · refine ⟨b₃⁻¹ * r ^ 4, B.mul_mem (B.inv_mem hb₃) hnB, fun x hx => ?_⟩
      have hy : r * x * r⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hrW x).mp hx
      have := hrot' _ hy
      calc r * x * r⁻¹ = b₃⁻¹ * (b₃ * (r * x * r⁻¹) * b₃⁻¹) * b₃ := by group
        _ = b₃⁻¹ * (r ^ 3 * (r * x * r⁻¹) * (r ^ 3)⁻¹) * b₃ := by rw [this]
        _ = (b₃⁻¹ * r ^ 4) * x * (b₃⁻¹ * r ^ 4)⁻¹ := by group
  obtain ⟨b₀, hb₀, hinn⟩ := hinner
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀, c₀ = b₀⁻¹ * r := ⟨_, rfl⟩
  have hc₀ : ∀ x ∈ B, c₀ * x = x * c₀ := by
    intro x hx
    have h1 := hinn x hx
    calc c₀ * x = (b₀⁻¹ * (r * x * r⁻¹) * b₀) * c₀ := by rw [hc₀def]; group
      _ = x * c₀ := by rw [h1]; group
  have hrc : r = b₀ * c₀ := by rw [hc₀def]; group
  have hcomm : Commute b₀ c₀ := (hc₀ b₀ hb₀).symm
  have hrk : ∀ k : ℕ, r ^ k = b₀ ^ k * c₀ ^ k := fun k => by rw [hrc]; exact hcomm.mul_pow k
  obtain ⟨m, hm⟩ := hev
  have hy₀B : ∀ b ∈ B, c₀ ^ m * b = b * c₀ ^ m := fun b hb =>
    ((Commute.pow_left (show Commute c₀ b from hc₀ b hb) m))
  have hy₀notB : c₀ ^ m ∉ B := by
    intro h
    apply hmin m (by omega) (by omega)
    rw [hrk m]; exact B.mul_mem (B.pow_mem hb₀ m) h
  have hy₀sq : c₀ ^ m * c₀ ^ m ∈ B := by
    have e1 : c₀ ^ m * c₀ ^ m = c₀ ^ n := by rw [← pow_add, hm]
    have e2 : c₀ ^ n = (b₀ ^ n)⁻¹ * r ^ n := by
      have := hrk n
      rw [this]; group
    rw [e1, e2]
    exact B.mul_mem (B.inv_mem (B.pow_mem hb₀ n)) hnB
  obtain ⟨N, hN⟩ : ∃ N, N = orderOf (c₀ ^ m) := ⟨_, rfl⟩
  have hNpos : 0 < N := by rw [hN]; exact orderOf_pos _
  have hNeven : Even N := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    apply hy₀notB
    have h1 : (c₀ ^ m) ^ N = 1 := by rw [hN]; exact pow_orderOf_eq_one _
    have : c₀ ^ m = (c₀ ^ m * c₀ ^ m) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (k + 1) = N + 1 := by omega
      rw [this, pow_succ, h1, one_mul]
    rw [this]
    exact B.pow_mem hy₀sq _
  obtain ⟨N', hN'⟩ := hNeven
  have hN'pos : 0 < N' := by omega
  refine hno ((c₀ ^ m) ^ N') ?_ ?_ ?_
  · rw [← pow_add, ← hN']
    rw [hN]; exact pow_orderOf_eq_one _
  · exact pow_ne_one_of_lt_orderOf (by omega) (by rw [← hN]; omega)
  · intro b hb
    exact Commute.pow_left (show Commute (c₀ ^ m) b from hy₀B b hb) N'

theorem exists_min_pow [Finite G] (r : G) (B : Subgroup G) :
    ∃ n : ℕ, 0 < n ∧ r ^ n ∈ B ∧ ∀ k, 0 < k → k < n → r ^ k ∉ B := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ r ^ n ∈ B :=
    ⟨orderOf r, orderOf_pos r, by rw [pow_orderOf_eq_one]; exact B.one_mem⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hkn hmem => ?_⟩
  exact Nat.find_min hex hkn ⟨hk, hmem⟩

theorem pow_mem_iff_dvd {r : G} {B : Subgroup G} {n : ℕ} (hn : 0 < n) (hnB : r ^ n ∈ B)
    (hmin : ∀ k, 0 < k → k < n → r ^ k ∉ B) (k : ℕ) : r ^ k ∈ B ↔ n ∣ k := by
  constructor
  · intro hk
    have hdiv := Nat.div_add_mod k n
    have h1 : r ^ (k % n) ∈ B := by
      have e : r ^ (k % n) = ((r ^ n) ^ (k / n))⁻¹ * r ^ k := by
        have : r ^ k = (r ^ n) ^ (k / n) * r ^ (k % n) := by
          rw [← pow_mul, ← pow_add, hdiv]
        rw [this]; group
      rw [e]; exact B.mul_mem (B.inv_mem (B.pow_mem hnB _)) hk
    by_contra hnd
    have hpos : 0 < k % n := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
    exact hmin _ hpos (Nat.mod_lt _ hn) h1
  · rintro ⟨m, rfl⟩
    rw [pow_mul]
    exact B.pow_mem hnB m

end CFSG.Quasithin.H13.F431.L3
