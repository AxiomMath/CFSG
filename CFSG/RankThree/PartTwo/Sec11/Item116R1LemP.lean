module

public import CFSG.RankThree.PartTwo.KFacts.KS116

public section

open Subgroup CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec11

theorem lemPc_card_closure_le_pow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 0 < p)
    (s : Finset G) (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hpow : ∀ x ∈ s, x ^ p = 1) :
    Nat.card ↥(Subgroup.closure (s : Set G)) ≤ p ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hc' : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
      hc x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have hpow' : ∀ x ∈ s, x ^ p = 1 := fun x hx => hpow x (Finset.mem_insert_of_mem hx)
    have ih' := ih hc' hpow'
    have hcent : Subgroup.closure (s : Set G) ≤
        Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hay : Commute a y :=
        hc a (Finset.mem_insert_self a s) y (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy))
      exact (hay.zpow_left n).eq
    have hle : Subgroup.closure (s : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hins : Subgroup.closure ((insert a s : Finset G) : Set G) =
        Subgroup.closure (s : Set G) ⊔ Subgroup.zpowers a := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, sup_comm,
        ← Subgroup.zpowers_eq_closure]
    have hmul := Set.natCard_mul_le (s := (Subgroup.closure (s : Set G) : Set G))
      (t := (Subgroup.zpowers a : Set G))
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hmul
    have hB : Nat.card (Subgroup.zpowers a) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (hpow a (Finset.mem_insert_self a s)))
    rw [Finset.card_insert_of_notMem ha, pow_succ, hins]
    exact hmul.trans (Nat.mul_le_mul ih' hB)

theorem lemPc_quot_mul_comm {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hc : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) (a b : G ⧸ N) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h := hc y⁻¹ x⁻¹
  simpa [mul_assoc] using h

theorem lemPc_card_quot_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 0 < p) (N : Subgroup G)
    [N.Normal] (hpow : ∀ x : G, x ^ p ∈ N) (hc : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N)
    {s : Finset G} (hs : Subgroup.closure (s : Set G) = ⊤) :
    Nat.card (G ⧸ N) ≤ p ^ s.card := by
  classical
  have hcomm : ∀ a ∈ s.image (QuotientGroup.mk' N), ∀ b ∈ s.image (QuotientGroup.mk' N),
      a * b = b * a := fun a _ b _ => lemPc_quot_mul_comm N hc a b
  have hpow' : ∀ a ∈ s.image (QuotientGroup.mk' N), a ^ p = 1 := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpow x)
  have hgen : Subgroup.closure ((s.image (QuotientGroup.mk' N) : Finset (G ⧸ N)) : Set (G ⧸ N))
      = ⊤ := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, hs]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
  have h := lemPc_card_closure_le_pow hp _ hcomm hpow'
  rw [hgen, Subgroup.card_top] at h
  exact h.trans (Nat.pow_le_pow_right hp Finset.card_image_le)

theorem lemPc_frattini_eq_bot {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hc : ∀ a b : Q, a * b = b * a) (hexp : ∀ x : Q, x ^ p = 1) : frattini Q = ⊥ := by
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hc }
  haveI : Finite (Subgroup Q) :=
    Finite.of_injective (fun H : Subgroup Q => (H : Set Q)) SetLike.coe_injective
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  have hne : (⊥ : Subgroup Q) ∈ {W : Subgroup Q | v ∉ W} := by
    show v ∉ (⊥ : Subgroup Q)
    rw [Subgroup.mem_bot]
    exact hv1
  obtain ⟨W, hWS, hWmax⟩ :=
    Set.Finite.exists_maximal (Set.toFinite {W : Subgroup Q | v ∉ W}) ⟨⊥, hne⟩
  have hvW : v ∉ W := hWS
  have hmax : ∀ W' : Subgroup Q, W ≤ W' → v ∉ W' → W' = W := fun W' hle hvW' =>
    le_antisymm (hWmax hvW' hle) hle
  have hcover : ∀ q : Q, q ∈ W ⊔ Subgroup.zpowers v := by
    intro q
    by_cases hq : q ∈ W
    · exact Subgroup.mem_sup_left hq
    have hvq : v ∈ W ⊔ Subgroup.zpowers q := by
      by_contra hvq
      have heq := hmax (W ⊔ Subgroup.zpowers q) le_sup_left hvq
      apply hq
      rw [← heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
    obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup.mp hvq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hndvd : ¬ ((p : ℤ) ∣ i) := by
      rintro ⟨k, rfl⟩
      apply hvW
      have hqk : q ^ ((p : ℤ) * k) = 1 := by
        rw [zpow_mul, zpow_natCast, hexp, one_zpow]
      rw [← huz, hqk, mul_one]
      exact hu
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) i := (hprime.irreducible.coprime_iff_not_dvd).mpr hndvd
    obtain ⟨a, b, hab⟩ := hcop
    have hq' : q = (q ^ i) ^ b := by
      calc q = q ^ (a * (p : ℤ) + b * i) := by rw [hab, zpow_one]
        _ = (q ^ (p : ℤ)) ^ a * (q ^ i) ^ b := by rw [zpow_add, zpow_mul', zpow_mul']
        _ = (q ^ i) ^ b := by rw [zpow_natCast, hexp, one_zpow, one_mul]
    have hqi : q ^ i = u⁻¹ * v := by rw [← huz, inv_mul_cancel_left]
    have hu' : u⁻¹ ∈ W ⊔ Subgroup.zpowers v := Subgroup.mem_sup_left (W.inv_mem hu)
    have hv' : v ∈ W ⊔ Subgroup.zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    have hprod : u⁻¹ * v ∈ W ⊔ Subgroup.zpowers v := (W ⊔ Subgroup.zpowers v).mul_mem hu' hv'
    rw [hq', hqi]
    exact (W ⊔ Subgroup.zpowers v).zpow_mem hprod b
  have hcoat : IsCoatom W := by
    show W ≠ ⊤ ∧ ∀ b : Subgroup Q, W < b → b = ⊤
    refine ⟨fun htop => hvW (by rw [htop]; exact Subgroup.mem_top v), fun b hWb => ?_⟩
    have hvb : v ∈ b := by
      by_contra hvb
      exact hWb.ne (hmax b hWb.le hvb).symm
    have hle : W ⊔ Subgroup.zpowers v ≤ b := sup_le hWb.le (Subgroup.zpowers_le.mpr hvb)
    apply eq_top_iff.mpr
    intro x _
    exact hle (hcover x)
  exact hvW (frattini_le_coatom hcoat hv)

theorem lemPc_mem_frattini {G : Type*} [Group G] (x : G)
    (h : ∀ K : Subgroup G, IsCoatom K → x ∈ K) : x ∈ frattini G := by
  unfold frattini Order.radical
  exact Subgroup.mem_iInf.2 fun K => Subgroup.mem_iInf.2 fun hK => h K hK

theorem lemPc_coatom {P : Type} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (K : Subgroup P) (hK : IsCoatom K) :
    (∀ x : P, x ^ p ∈ K) ∧ (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ K) := by
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  haveI : K.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom K hK
  have hidx : K.index = p := (IsPGroup.isCoatom_iff_index_eq_prime hP).mp hK
  have hcard : Nat.card (P ⧸ K) = p := by rw [← Subgroup.index_eq_card, hidx]
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have h1 : ((x : P) : P ⧸ K) ^ p = 1 := by
      have h2 := pow_card_eq_one' (G := P ⧸ K) (x := ((x : P) : P ⧸ K))
      rwa [hcard] at h2
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  · haveI : IsCyclic (P ⧸ K) := isCyclic_of_prime_card hcard
    have hcomm : ∀ a b : P ⧸ K, a * b = b * a := by
      letI : CommGroup (P ⧸ K) := IsCyclic.commGroup
      exact mul_comm
    have hxy := hcomm ((x⁻¹ : P) : P ⧸ K) ((y⁻¹ : P) : P ⧸ K)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hxy
    have hid : x * y * x⁻¹ * y⁻¹ = ((x⁻¹ * y⁻¹)⁻¹ * (y⁻¹ * x⁻¹))⁻¹ := by group
    rw [hid]
    exact K.inv_mem hxy

theorem exists_elemAbelian_of_irreducible (hB : KFacts.BlackburnRankTwo) {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) {P : Type} [Group P] [Finite P] (hP : IsPGroup p P) (M : Subgroup P) [M.Normal]
    (hpow : ∀ x : P, x ^ p ∈ M) (hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ M)
    (hidx : M.index = p ^ 3) (h : P ≃* P) (hM : M.map h.toMonoidHom = M)
    (hirr : ∀ N : Subgroup P, M ≤ N → N.map h.toMonoidHom = N → N = M ∨ N = ⊤) :
    ∃ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  by_contra hno
  have hp0 : 0 < p := by omega
  have hpp : p.Prime := Fact.out
  have hE : ∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
    intro E hEel
    have hlt : Nat.card E < p ^ 3 := by
      by_contra hge
      exact hno ⟨E, hEel, not_lt.mp hge⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_subgroup E)
    rw [hn] at hlt ⊢
    have hn2 : n ≤ 2 := by
      by_contra h3
      have h3' : 3 ≤ n := by omega
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp0 h3'))
    exact Nat.pow_le_pow_right hp0 hn2
  obtain ⟨⟨s3, hs3card, hs3gen⟩, hB2⟩ := hB p hp P hP hE
  have h2 : ∀ s : Finset P, s.card ≤ 2 → Subgroup.closure (s : Set P) ≠ ⊤ := by
    intro s hs htop
    have hq := lemPc_card_quot_le hp0 M hpow hcomm htop
    rw [← Subgroup.index_eq_card, hidx] at hq
    have h22 : p ^ s.card ≤ p ^ 2 := Nat.pow_le_pow_right hp0 hs
    have h23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    exact absurd (hq.trans h22) (not_le.mpr h23)
  obtain ⟨Z₀, hZchar, hFZ, hrel⟩ := hB2 h2
  have hF_pow : ∀ x : P, x ^ p ∈ frattini P := fun x =>
    lemPc_mem_frattini _ fun K hK => (lemPc_coatom hP K hK).1 x
  have hF_comm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ frattini P := fun x y =>
    lemPc_mem_frattini _ fun K hK => (lemPc_coatom hP K hK).2 x y
  have hexpQ : ∀ a : P ⧸ M, a ^ p = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpow x)
  have hFM : frattini P ≤ M := by
    have hbot := lemPc_frattini_eq_bot hpp (lemPc_quot_mul_comm M hcomm) hexpQ
    have hle := frattini_le_comap_frattini_of_surjective (φ := QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M)
    rw [hbot] at hle
    intro x hx
    have hx' := hle hx
    rw [Subgroup.mem_comap, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  have hMF : M ≤ frattini P := by
    haveI : (frattini P).Normal := inferInstance
    have hrel1 : (frattini P).relIndex M = 1 := by
      have hcount := lemPc_card_quot_le hp0 (frattini P) hF_pow hF_comm hs3gen
      rw [← Subgroup.index_eq_card] at hcount
      have hle3 : (frattini P).index ≤ p ^ 3 := hcount.trans (Nat.pow_le_pow_right hp0 hs3card)
      have hmul := Subgroup.relIndex_mul_index hFM
      rw [hidx] at hmul
      have hne : (frattini P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrpos : 0 < (frattini P).relIndex M := by
        rcases Nat.eq_zero_or_pos ((frattini P).relIndex M) with h0 | h0
        · rw [h0, zero_mul] at hmul
          exact absurd hmul.symm hne
        · exact h0
      have hr : (frattini P).relIndex M ≤ 1 := by
        have hmul' : (frattini P).relIndex M * p ^ 3 ≤ 1 * p ^ 3 := by
          rw [one_mul, hmul]
          exact hle3
        exact Nat.le_of_mul_le_mul_right hmul' (pow_pos hp0 3)
      omega
    exact Subgroup.relIndex_eq_one.mp hrel1
  have hFeq : frattini P = M := le_antisymm hFM hMF
  have hMZ : M ≤ Z₀ := by
    rw [← hFeq]
    exact hFZ
  rw [hFeq] at hrel
  have hZmap : Z₀.map h.toMonoidHom = Z₀ := Subgroup.characteristic_iff_map_eq.mp hZchar h
  rcases hirr Z₀ hMZ hZmap with hZM | hZT
  · rw [hZM, Subgroup.relIndex_self] at hrel
    omega
  · rw [hZT, Subgroup.relIndex_top_right, hidx] at hrel
    have h3 : p < p ^ 3 := by nlinarith [Nat.mul_le_mul hp hp]
    exact absurd hrel (ne_of_gt h3)

end CFSG.RankThree.PartTwo.Sec11
