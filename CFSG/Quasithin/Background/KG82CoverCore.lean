module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H.L34Cov

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

structure ParData {S : Type*} [Group S] (Q E V F : Subgroup S) : Prop where
  le : E ≤ Q
  normal : Q ≤ Subgroup.normalizer (E : Set S)
  sq : ∀ e ∈ E, e * e = 1
  core : ∀ N : Subgroup S, N ≤ Q → Q ≤ Subgroup.normalizer (N : Set S) → IsPGroup 2 N → N ≤ E
  comm : E ≤ ⁅E, Q⁆
  sqV : ∀ v ∈ V, v * v = 1
  leF : F ≤ Q
  mulF : ∀ f ∈ F, ∃ e ∈ E, ∃ v ∈ V, f = e * v
  oddF : Odd F.index

theorem ParData.map_equiv {S S' : Type*} [Group S] [Group S'] {Q E V F : Subgroup S}
    (hd : ParData Q E V F) (φ : S ≃* S') :
    ParData (Q.map φ.toMonoidHom) (E.map φ.toMonoidHom) (V.map φ.toMonoidHom)
      (F.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hd.le, ?_, ?_, ?_, ?_, ?_, Subgroup.map_mono hd.leF, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hd.normal
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hd.sq e he, map_one]
  · intro N hNQ hQN hN2
    have h1 : N.map φ.symm.toMonoidHom ≤ Q := by
      rintro _ ⟨n, hn, rfl⟩
      have := hNQ hn
      rw [Subgroup.mem_map_equiv] at this
      exact this
    have h2 : Q ≤ Subgroup.normalizer ((N.map φ.symm.toMonoidHom : Subgroup S) : Set S) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      intro q hq
      refine ⟨φ q, hQN ⟨q, hq, rfl⟩, ?_⟩
      simp
    have h3 := hd.core _ h1 h2 (hN2.map _)
    intro n hn
    rw [Subgroup.mem_map_equiv]
    exact h3 ⟨n, hn, rfl⟩
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hd.comm
  · rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, hd.sqV v hv, map_one]
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨e, he, v, hv, rfl⟩ := hd.mulF f hf
    exact ⟨φ e, ⟨e, he, rfl⟩, φ v, ⟨v, hv, rfl⟩, map_mul _ _ _⟩
  · rw [show φ.toMonoidHom = (φ : S →* S') from rfl, Subgroup.index_map_equiv]
    exact hd.oddF

@[expose] def Triple (S : Type*) [Group S] : Prop :=
  ∃ a b c : S, a * a = 1 ∧ b * b = 1 ∧ c * c = 1 ∧ a * b = b * a ∧ a * c = c * a ∧
    b * c = c * b ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b ≠ 1 ∧ a * c ≠ 1 ∧ b * c ≠ 1 ∧ a * (b * c) ≠ 1

structure Dbl {G S : Type*} [Group G] [Group S] (π : G →* S) (z : G) : Prop where
  surj : Function.Surjective π
  central : z ∈ Subgroup.center G
  ne_one : z ≠ 1
  sq : z * z = 1
  map : π z = 1
  ker : ∀ x, π x = 1 → x = 1 ∨ x = z

namespace Dbl

variable {G S : Type*} [Group G] [Group S] {π : G →* S} {z : G}

theorem comm (h : Dbl π z) (x : G) : z * x = x * z :=
  (Subgroup.mem_center_iff.1 h.central x).symm

theorem eq_or_eq_mul (h : Dbl π z) {x y : G} (hxy : π x = π y) : y = x ∨ y = x * z := by
  have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rcases h.ker _ h1 with h2 | h2
  · left
    rw [← mul_inv_cancel_left x y, h2, mul_one]
  · right
    rw [← mul_inv_cancel_left x y, h2]

theorem mul_self_eq (h : Dbl π z) {x y : G} (hxy : π x = π y) : y * y = x * x := by
  rcases h.eq_or_eq_mul hxy with rfl | rfl
  · rfl
  · calc x * z * (x * z) = x * x * (z * z) := by
          rw [mul_assoc, ← mul_assoc z, h.comm x]
          simp only [mul_assoc]
      _ = x * x := by rw [h.sq, mul_one]

theorem mul_self_cases (h : Dbl π z) {x : G} (hx : π x * π x = 1) : x * x = 1 ∨ x * x = z :=
  h.ker _ (by rw [map_mul, hx])

theorem mem_of_map_mem (h : Dbl π z) {P : Subgroup G} (hzP : z ∈ P) {x : G}
    (hx : π x ∈ P.map π) : x ∈ P := by
  obtain ⟨p, hp, hpx⟩ := hx
  rcases h.eq_or_eq_mul hpx with rfl | rfl
  · exact hp
  · exact P.mul_mem hp hzP

theorem commutator_eq (h : Dbl π z) {u v : G} (hu : u * u = z) (hv : v * v = z)
    (huv : u * v * (u * v) = z) (hc : π u * π v = π v * π u) : u⁻¹ * v⁻¹ * u * v = z := by
  have h1 : π (u⁻¹ * v⁻¹ * u * v) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_assoc ((π u)⁻¹ * (π v)⁻¹), hc]
    group
  rcases h.ker _ h1 with h2 | h2
  · exfalso
    have h3 : u * v = v * u := by
      calc u * v = v * u * (u⁻¹ * v⁻¹ * u * v) := by group
        _ = v * u := by rw [h2, mul_one]
    have h4 : u * v * (u * v) = u * u * (v * v) := by
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [← h3]
        _ = u * u * (v * v) := by group
    rw [h4, hu, hv, h.sq] at huv
    exact h.ne_one huv.symm
  · exact h2

theorem exists_lift (h : Dbl π z) (htri : Triple S) :
    ∃ y : S, y ≠ 1 ∧ y * y = 1 ∧ ∀ x, π x = y → x * x = 1 := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, ha1, hb1, hc1, hab1, hac1, hbc1, habc1⟩ := htri
  by_contra hne
  push Not at hne
  have key : ∀ u : G, π u ≠ 1 → π u * π u = 1 → u * u = z := by
    intro u hu1 hu2
    obtain ⟨u', hu', hne'⟩ := hne _ hu1 hu2
    rcases h.mul_self_cases hu2 with h1 | h1
    · exact absurd ((h.mul_self_eq hu'.symm).trans h1) hne'
    · exact h1
  have sq2 : ∀ s t : S, s * s = 1 → t * t = 1 → s * t = t * s → s * t * (s * t) = 1 :=
    fun s t hs ht hst => by
      calc s * t * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [← hst]
        _ = s * s * (t * t) := by group
        _ = 1 := by rw [hs, ht, mul_one]
  obtain ⟨x, rfl⟩ := h.surj a
  obtain ⟨y, rfl⟩ := h.surj b
  obtain ⟨w, rfl⟩ := h.surj c
  have hbc' : π y * π w * (π y * π w) = 1 := sq2 _ _ hb hc hbc
  have hx := key x ha1 ha
  have hy := key y hb1 hb
  have hw := key w hc1 hc
  have hxy := key (x * y) (by rwa [map_mul]) (by rw [map_mul]; exact sq2 _ _ ha hb hab)
  have hxw := key (x * w) (by rwa [map_mul]) (by rw [map_mul]; exact sq2 _ _ ha hc hac)
  have hyw := key (y * w) (by rwa [map_mul]) (by rw [map_mul]; exact hbc')
  have hcomm : π x * π (y * w) = π (y * w) * π x := by
    rw [map_mul, ← mul_assoc, hab, mul_assoc, hac, ← mul_assoc]
  have hxyw := key (x * (y * w)) (by rwa [map_mul, map_mul])
    (by rw [map_mul]; exact sq2 _ _ ha (by rwa [map_mul]) hcomm)
  have c1 := h.commutator_eq hx hy hxy (by rw [hab])
  have c2 := h.commutator_eq hx hw hxw (by rw [hac])
  have c3 := h.commutator_eq hx hyw hxyw hcomm
  have e : x⁻¹ * (y * w)⁻¹ * x * (y * w) =
      (x⁻¹ * w⁻¹ * x * w) * (w⁻¹ * (x⁻¹ * y⁻¹ * x * y) * w) := by group
  have hzw : w⁻¹ * z * w = z := by rw [mul_assoc, h.comm w, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [c3, c2, c1, hzw, h.sq] at e
  exact h.ne_one e

theorem mul_self_eq_one (h : Dbl π z) (htri : Triple S)
    (hcls : ∀ u v : S, orderOf u = 2 → orderOf v = 2 → IsConj u v) {x : G}
    (hx : π x * π x = 1) : x * x = 1 := by
  by_cases h1 : π x = 1
  · rcases h.ker x h1 with rfl | rfl
    · rw [mul_one]
    · exact h.sq
  obtain ⟨y, hy1, hy2, hy⟩ := h.exists_lift htri
  have hord : ∀ s : S, s ≠ 1 → s * s = 1 → orderOf s = 2 := fun s hs1 hs2 =>
    orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  obtain ⟨c, hc⟩ := isConj_iff.1 (hcls y (π x) (hord y hy1 hy2) (hord _ h1 hx))
  obtain ⟨c', rfl⟩ := h.surj c
  obtain ⟨y', rfl⟩ := h.surj y
  have h2 : π (c' * y' * c'⁻¹) = π x := by rw [map_mul, map_mul, map_inv, hc]
  rw [h.mul_self_eq h2]
  calc c' * y' * c'⁻¹ * (c' * y' * c'⁻¹) = c' * (y' * y') * c'⁻¹ := by group
    _ = 1 := by rw [hy y' rfl, mul_one, mul_inv_cancel]

end Dbl

theorem mem_commutator_of_odd_index {G : Type*} [Group G] [Finite G] {z : G}
    (hz : z ∈ Subgroup.center G) (hzc : z ∈ commutator G) (hz2 : z * z = 1) {H : Subgroup G}
    (hzH : z ∈ H) (hodd : Odd H.index) : z ∈ ⁅H, H⁆ := by
  let ϕ : ↥H →* Abelianization ↥H := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k :=
    fun k g₀ _ => by
      have hc : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
      rw [Subgroup.mem_center_iff.1 hc g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have h2 : MonoidHom.transfer ϕ z = 1 := Abelianization.commutator_subset_ker _ hzc
  have hzi : z ^ H.index = z := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]
  rw [h2] at h1
  have h3 : ϕ ⟨z, hzH⟩ = 1 := by
    have e : (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : ↥H) = ⟨z, hzH⟩ :=
      Subtype.ext hzi
    rw [← e]
    exact h1.symm
  have h4 : (⟨z, hzH⟩ : ↥H) ∈ commutator ↥H := by
    rw [← Abelianization.ker_of]
    exact h3
  have h5 := Subgroup.mem_map_of_mem H.subtype h4
  rwa [Subgroup.map_subtype_commutator] at h5

theorem pCore_eq_comap {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    pCore 2 A = (pCore 2 B).comap f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  refine le_antisymm (Subgroup.map_le_iff_le_comap.1 (map_pCore_le 2 f hf)) ?_
  exact le_pCore 2 ((pCore_normal 2).comap f) ((pCore_isPGroup 2).comap_of_ker_isPGroup f hk)

variable {G S : Type*} [Group G] [Group S] {π : G →* S} {z : G}

theorem mem_pCoreOf_iff [Finite G] (h : Dbl π z) {P : Subgroup G} {E V F : Subgroup S}
    (hd : ParData (P.map π) E V F) (x : G) :
    x ∈ pCoreOf 2 P ↔ x ∈ P ∧ π x ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := P.map π
  set f := π.subgroupMap P
  have hk : IsPGroup 2 f.ker := by
    intro k
    refine ⟨1, ?_⟩
    have hk1 : π (k : G) = 1 := by
      have := k.2
      rw [MonoidHom.mem_ker] at this
      exact congrArg Subtype.val this
    rw [pow_one, sq]
    apply Subtype.ext
    apply Subtype.ext
    show (k : G) * k = 1
    rcases h.ker _ hk1 with h1 | h1
    · rw [h1, mul_one]
    · rw [h1, h.sq]
  have hcore := pCore_eq_comap f (π.subgroupMap_surjective P) hk
  have : Finite ↥Q := Finite.of_surjective f (π.subgroupMap_surjective P)
  have hEQ : pCore 2 ↥Q = E.subgroupOf Q := by
    refine le_antisymm ?_ ?_
    · intro q hq
      have hN := hd.core ((pCore 2 ↥Q).map Q.subtype) (Subgroup.map_subtype_le _)
        (fun g hg => by
          rw [Subgroup.mem_normalizer_iff]
          intro n
          constructor
          · rintro ⟨n', hn', rfl⟩
            refine ⟨⟨g, hg⟩ * n' * ⟨g, hg⟩⁻¹, (pCore_normal 2).conj_mem _ hn' _, rfl⟩
          · rintro ⟨n', hn', hn⟩
            refine ⟨⟨g, hg⟩⁻¹ * n' * ⟨g, hg⟩, ?_, ?_⟩
            · have := (pCore_normal 2 (G := ↥Q)).conj_mem _ hn' ⟨g, hg⟩⁻¹
              simpa using this
            · have hn2 : (n' : S) = g * n * g⁻¹ := hn
              simp [hn2, mul_assoc])
        ((pCore_isPGroup 2).map Q.subtype)
      exact hN ⟨q, hq, rfl⟩
    · refine le_pCore 2 ((Subgroup.normal_subgroupOf_iff_le_normalizer hd.le).2 hd.normal) ?_
      intro e
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rw [pow_one, sq]
      exact hd.sq _ e.2
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [hcore, hEQ] at hp
    exact ⟨p.2, hp⟩
  · rintro ⟨hxP, hxE⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [hcore, hEQ]
    exact hxE

theorem commutator_pCoreOf_eq [Finite G] (h : Dbl π z) (hzc : z ∈ commutator G)
    (htri : Triple S) (hcls : ∀ u v : S, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {P : Subgroup G} (hzP : z ∈ P) {E V F : Subgroup S} (hd : ParData (P.map π) E V F) :
    ⁅pCoreOf 2 P, P⁆ = pCoreOf 2 P := by
  set R := pCoreOf 2 P
  set Q := P.map π
  have hR := mem_pCoreOf_iff h hd
  have hlift : ∀ x : G, π x * π x = 1 → x * x = 1 := fun x hx =>
    h.mul_self_eq_one htri hcls hx
  have hRsq : ∀ r ∈ R, r * r = 1 := fun r hr => hlift r (hd.sq _ ((hR r).1 hr).2)
  have hNR : ⁅R, P⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr p hp
    have hr' := (hR r).1 hr
    rw [hR]
    refine ⟨P.mul_mem (P.mul_mem (P.mul_mem hr'.1 hp) (P.inv_mem hr'.1)) (P.inv_mem hp), ?_⟩
    have h1 : π p * (π r)⁻¹ * (π p)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (hd.normal ⟨p, hp, rfl⟩) _).1 (E.inv_mem hr'.2)
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc,
      mul_assoc, ← mul_assoc (π p)]
    exact E.mul_mem hr'.2 h1
  have hRE : R.map π = E := by
    refine le_antisymm ?_ fun e he => ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact ((hR r).1 hr).2
    · obtain ⟨p, hp, rfl⟩ := hd.le he
      exact ⟨p, (hR p).2 ⟨hp, he⟩, rfl⟩
  have hcov : ∀ r ∈ R, ∃ n ∈ ⁅R, P⁆, r = n ∨ r = n * z := by
    intro r hr
    have h1 : π r ∈ ⁅R, P⁆.map π := by
      rw [Subgroup.map_commutator, hRE]
      exact hd.comm (by rw [← hRE]; exact ⟨r, hr, rfl⟩)
    obtain ⟨n, hn, hnr⟩ := h1
    exact ⟨n, hn, h.eq_or_eq_mul hnr⟩
  set H := F.comap π
  have hzH : z ∈ H := by
    show π z ∈ F
    rw [h.map]
    exact F.one_mem
  have hHP : ∀ x ∈ H, x ∈ P := fun x hx => h.mem_of_map_mem hzP (hd.leF hx)
  have hsq : ∀ x ∈ H, x * x ∈ ⁅R, P⁆ := by
    intro x hx
    obtain ⟨e, he, v, hv, hxev⟩ := hd.mulF _ hx
    obtain ⟨v', rfl⟩ := h.surj v
    have hvQ : π v' ∈ Q := by
      have : π v' = e⁻¹ * π x := by rw [hxev, inv_mul_cancel_left]
      rw [this]
      exact Q.mul_mem (Q.inv_mem (hd.le he)) (hd.leF hx)
    have hv'P : v' ∈ P := h.mem_of_map_mem hzP hvQ
    have hv2 : v' * v' = 1 := hlift v' (hd.sqV _ hv)
    have hrR : x * v'⁻¹ ∈ R := by
      rw [hR]
      refine ⟨P.mul_mem (hHP x hx) (P.inv_mem hv'P), ?_⟩
      rw [map_mul, map_inv, hxev, mul_inv_cancel_right]
      exact he
    have hr2 := hRsq _ hrR
    have hvi : v'⁻¹ = v' := inv_eq_of_mul_eq_one_right hv2
    have hri : (x * v'⁻¹)⁻¹ = x * v'⁻¹ := inv_eq_of_mul_eq_one_right hr2
    have e1 : x * x = ⁅(x * v'⁻¹)⁻¹, v'⁆ := by
      rw [commutatorElement_def, inv_inv, hri, hvi]
      simp only [mul_assoc]
      rw [hv2, mul_one, ← mul_assoc v', hv2, one_mul]
    rw [e1]
    exact Subgroup.commutator_mem_commutator (R.inv_mem hrR) hv'P
  have hHH : ⁅H, H⁆ ≤ ⁅R, P⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have e1 : ⁅a, b⁆ = a * b * (a * b) * ((b⁻¹ * a⁻¹ * b) * (b⁻¹ * a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsq _ (H.mul_mem ha hb)) (hsq _ ?_))
      (hsq _ (H.inv_mem hb))
    exact H.mul_mem (H.mul_mem (H.inv_mem hb) (H.inv_mem ha)) hb
  have hodd : Odd H.index := by
    rw [Subgroup.index_comap_of_surjective F h.surj]
    exact hd.oddF
  have hzN : z ∈ ⁅R, P⁆ :=
    hHH (mem_commutator_of_odd_index h.central hzc h.sq hzH hodd)
  refine le_antisymm hNR fun r hr => ?_
  obtain ⟨n, hn, rfl | rfl⟩ := hcov r hr
  · exact hn
  · exact Subgroup.mul_mem _ hn hzN

end CFSG.Quasithin.H.L34Cov
