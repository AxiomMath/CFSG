module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.OrderOfElement.PPart
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC

open Subgroup
open scoped Pointwise

theorem exists_inner_of_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N R : Subgroup G) (hRN : R ≤ N) (hRn : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (hR : IsPGroup p R) (hSyl : ¬ p ∣ (R.subgroupOf N).index)
    (j k : G) (hj : IsPGroup p (zpowers j)) (hk : k ∈ N)
    (hjk : ∀ r ∈ R, j * r * j⁻¹ = k * r * k⁻¹) :
    ∃ θ ∈ R, ∀ r ∈ R, j * r * j⁻¹ = θ * r * θ⁻¹ := by
  have hpp : p.Prime := Fact.out
  have hit : ∀ n : ℕ, ∀ r ∈ R, j ^ n * r * (j ^ n)⁻¹ = k ^ n * r * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro r _; simp
    | succ n ih =>
      intro r hr
      have hkr : k * r * k⁻¹ ∈ R := hRn k hk r hr
      have := ih _ hkr
      calc j ^ (n + 1) * r * (j ^ (n + 1))⁻¹
          = j ^ n * (j * r * j⁻¹) * (j ^ n)⁻¹ := by group
        _ = j ^ n * (k * r * k⁻¹) * (j ^ n)⁻¹ := by rw [hjk r hr]
        _ = k ^ n * (k * r * k⁻¹) * (k ^ n)⁻¹ := this
        _ = k ^ (n + 1) * r * (k ^ (n + 1))⁻¹ := by group
  set s := TauCeti.pFreePart p k with hs
  set θ := TauCeti.pPart p k with hθ
  have hsθ : s * θ = k := TauCeti.pFreePart_mul_pPart p k
  have hkfin : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨a, ha⟩ : ∃ a : ℕ, j ^ (p ^ a) = 1 := by
    have h := (IsPGroup.iff_orderOf.1 hj) ⟨j, mem_zpowers j⟩
    obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    rw [Subgroup.orderOf_mk] at ha
    rw [← ha]
    exact pow_orderOf_eq_one j
  have hscomm : ∀ r ∈ R, s * r * s⁻¹ = r := by
    intro r hr
    obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).1 (TauCeti.pFreePart_mem_powers p k)
    have he' : k ^ e = s := he
    have hs0 : orderOf s ≠ 0 := (orderOf_pos s).ne'
    have hφ : (orderOf s).totient ≠ 0 := (Nat.totient_pos.2 (Nat.pos_of_ne_zero hs0)).ne'
    have hcop : Nat.Coprime (p ^ a) (orderOf s) := by
      apply Nat.Coprime.pow_left
      rw [hpp.coprime_iff_not_dvd]
      rw [hs, TauCeti.orderOf_pFreePart hpp hkfin]
      exact Nat.not_dvd_ordCompl hpp hkfin
    have hmod : (p ^ a) ^ (orderOf s).totient ≡ 1 [MOD orderOf s] := Nat.ModEq.pow_totient hcop
    set M := (p ^ a) ^ (orderOf s).totient with hM
    have hsp : s ^ M = s := by
      calc s ^ M = s ^ 1 := (pow_eq_pow_iff_modEq).2 (by simpa using hmod)
        _ = s := pow_one s
    have hjM : j ^ M = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.1
      exact (orderOf_dvd_of_pow_eq_one ha).trans (dvd_pow_self _ hφ)
    have hn := hit (e * M) r hr
    have hk1 : k ^ (e * M) = s := by rw [pow_mul, he', hsp]
    have hj1 : j ^ (e * M) = 1 := by rw [mul_comm, pow_mul, hjM, one_pow]
    rw [hk1, hj1] at hn
    simpa using hn.symm
  have hθN : θ ∈ N := by
    have : θ ∈ zpowers k := TauCeti.pPart_mem_zpowers p k
    exact (zpowers_le.2 hk) this
  have hθR : θ ∈ R := by
    let θN : N := ⟨θ, hθN⟩
    let R' : Subgroup N := R.subgroupOf N
    have hR' : IsPGroup p R' := hR.comap_subtype
    haveI hnorm : R'.Normal := ⟨fun x hx g => by
      show (g * x * g⁻¹ : N).1 ∈ R
      exact hRn g.1 g.2 x.1 hx⟩
    let S : Sylow p N := hR'.toSylow hSyl
    haveI hSn : S.Normal := hnorm
    haveI := Sylow.unique_of_normal S hSn
    have hzp : IsPGroup p (zpowers θN) := by
      have hord : orderOf θN = orderOf θ := Subgroup.orderOf_mk _ _
      refine IsPGroup.of_card (n := (orderOf k).factorization p) ?_
      rw [Nat.card_zpowers, hord, hθ, TauCeti.orderOf_pPart hpp hkfin]
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    have hQS : Q = S := Subsingleton.elim _ _
    rw [hQS] at hQ
    exact hQ (mem_zpowers θN)
  refine ⟨θ, hθR, fun r hr => ?_⟩
  have hθr : θ * r * θ⁻¹ ∈ R := hRn θ hθN r hr
  calc j * r * j⁻¹ = k * r * k⁻¹ := hjk r hr
    _ = s * (θ * r * θ⁻¹) * s⁻¹ := by rw [← hsθ]; group
    _ = θ * r * θ⁻¹ := hscomm _ hθr

theorem mem_zpowers_or_mem_zpowers_of_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (C : Subgroup G) [IsCyclic C] (hC : IsPGroup p C) (x z : G) (hx : x ∈ C)
    (hz : z ∈ C) : z ∈ zpowers x ∨ x ∈ zpowers z := by
  have hpp : p.Prime := Fact.out
  let x' : C := ⟨x, hx⟩
  let z' : C := ⟨z, hz⟩
  obtain ⟨a, ha⟩ := (hC.to_subgroup (zpowers x')).exists_card_eq
  obtain ⟨b, hb⟩ := (hC.to_subgroup (zpowers z')).exists_card_eq
  rcases le_total b a with hab | hab
  · left
    have hle : zpowers z' ≤ zpowers x' := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
      exact Nat.pow_dvd_pow p hab
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hle (mem_zpowers z'))
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  · right
    have hle : zpowers x' ≤ zpowers z' := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
      exact Nat.pow_dvd_pow p hab
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hle (mem_zpowers x'))
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem lemma438_shape {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Subgroup G) (hR : IsPGroup p R) (hRne : R ≠ ⊥) (θ j : G) (hθ : θ ∈ R)
    (hθZ : ¬ R ≤ centralizer {θ}) (hj : j ^ p = 1) (hy : R ≤ centralizer {θ * j})
    (hcyc : IsCyclic (R ⊓ centralizer {θ} : Subgroup G)) :
    Commute θ j ∧ (θ * j) ^ p = θ ^ p ∧ θ ^ p ≠ 1 ∧
      ∀ z ∈ R, R ≤ centralizer {z} → z ∈ zpowers (θ ^ p) := by
  have hpp : p.Prime := Fact.out
  have hcomm : Commute θ j := by
    have h := hy hθ
    rw [mem_centralizer_singleton_iff] at h
    have : θ * (j * θ) = θ * (θ * j) := by
      simpa [mul_assoc] using h.symm
    exact (mul_left_cancel this).symm
  have hpow : (θ * j) ^ p = θ ^ p := by rw [hcomm.mul_pow, hj, mul_one]
  have hcent_pow : ∀ n : ℕ, R ≤ centralizer {(θ * j) ^ n} := by
    intro n r hr
    rw [mem_centralizer_singleton_iff]
    have h : Commute r (θ * j) := by
      have := hy hr
      rw [mem_centralizer_singleton_iff] at this
      exact this
    exact (h.pow_right n).eq
  have hθp : R ≤ centralizer {θ ^ p} := hpow ▸ hcent_pow p
  have hcentral : ∀ z ∈ R, R ≤ centralizer {z} → z ∈ zpowers (θ ^ p) := by
    intro z hz hzc
    set C : Subgroup G := R ⊓ centralizer {θ}
    have hCp : IsPGroup p C := hR.to_inf_left
    have hθC : θ ∈ C := mem_inf.2 ⟨hθ, mem_centralizer_singleton_iff.2 rfl⟩
    have hzC : z ∈ C := mem_inf.2 ⟨hz, mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (hzc hθ)).symm⟩
    have hcz : ∀ g ∈ zpowers z, R ≤ centralizer {g} := by
      rintro g ⟨k, rfl⟩ r hr
      have := hzc hr
      rw [mem_centralizer_singleton_iff] at this ⊢
      exact ((Commute.zpow_right (this : Commute r z) k)).eq
    rcases mem_zpowers_or_mem_zpowers_of_isCyclic C hCp θ z hθC hzC with h | h
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 h
      have hgcd : i.gcd (orderOf θ) ≠ 1 := by
        intro hg
        exact hθZ (hcz θ (mem_zpowers_zpow_iff.2 hg))
      obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨θ, hθ⟩
      rw [Subgroup.orderOf_mk] at he
      have hpi : (p : ℤ) ∣ i := by
        have hd : i.gcd (orderOf θ : ℤ) ∣ p ^ e := by
          rw [← he]; exact_mod_cast Int.gcd_dvd_right i (orderOf θ : ℤ)
        obtain ⟨c, hc, hc'⟩ := (Nat.dvd_prime_pow hpp).1 hd
        have hc0 : c ≠ 0 := by rintro rfl; exact hgcd (by simpa using hc')
        have : (p : ℤ) ∣ (i.gcd (orderOf θ : ℤ) : ℤ) := by
          rw [hc']; exact_mod_cast dvd_pow_self p hc0
        exact this.trans (Int.gcd_dvd_left _ _)
      obtain ⟨m, rfl⟩ := hpi
      refine ⟨m, ?_⟩
      show (θ ^ p) ^ m = θ ^ ((p : ℤ) * m)
      rw [zpow_mul, zpow_natCast]
    · exact absurd (hcz θ h) hθZ
  refine ⟨hcomm, hpow, ?_, hcentral⟩
  intro h1
  obtain ⟨z, hzR, hz1, hzc⟩ := hR.exists_ne_one_le_centralizer hRne
  have := hcentral z hzR hzc
  rw [h1, zpowers_one_eq_bot, mem_bot] at this
  exact hz1 this

theorem exists_conj_mem_of_card_max {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B S T : Subgroup G) (hSB : S ≤ B) (hTB : T ≤ B) (hS : IsPGroup p S) (hT : IsPGroup p T)
    (hSmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → Nat.card X ≤ Nat.card S) :
    ∃ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ S := by
  let SB : Sylow p B :=
    { toSubgroup := S.subgroupOf B
      isPGroup' := hS.comap_subtype
      is_maximal' := fun {Q} hQ hle => by
        refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
        have h := hSmax (Q.map B.subtype) (map_subtype_le Q) (hQ.map _)
        rw [Subgroup.card_map_of_injective B.subtype_injective] at h
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv] }
  obtain ⟨Q, hQ⟩ := (hT.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B Q SB
  refine ⟨b, b.2, fun t ht => ?_⟩
  have h1 : (⟨t, hTB ht⟩ : B) ∈ (Q : Subgroup B) := hQ ht
  have h2 : MulAut.conj b • (⟨t, hTB ht⟩ : B) ∈ MulAut.conj b • (Q : Subgroup B) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [← Sylow.coe_subgroup_smul, hb] at h2
  simpa [SB, mem_subgroupOf] using h2

theorem exists_mul_normalizes_of_card_max {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (A B S : Subgroup G) (hBA : B ≤ A)
    (hBn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) (hSB : S ≤ B) (hS : IsPGroup p S)
    (hSmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → Nat.card X ≤ Nat.card S)
    (g : G) (hg : g ∈ A) :
    ∃ b ∈ B, ∃ w ∈ A, (∀ s ∈ S, w * s * w⁻¹ ∈ S) ∧ g = b * w := by
  have hTB : S.map (MulAut.conj g).toMonoidHom ≤ B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hBn g hg s (hSB hs)
  obtain ⟨b, hb, hbS⟩ := exists_conj_mem_of_card_max B S _ hSB hTB hS (hS.map _) hSmax
  refine ⟨b⁻¹, B.inv_mem hb, b * g, A.mul_mem (hBA hb) hg, fun s hs => ?_, by group⟩
  have := hbS (g * s * g⁻¹) ⟨s, hs, rfl⟩
  simpa [mul_assoc] using this

theorem lemma438_centralizer_le_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (R P : Subgroup G) (hR : IsPGroup p R) (hRne : R ≠ ⊥) (θ j : G)
    (hθ : θ ∈ R) (hθZ : ¬ R ≤ centralizer {θ}) (hj : j ^ p = 1)
    (hy : R ≤ centralizer {θ * j}) (hcyc : IsCyclic (R ⊓ centralizer {θ} : Subgroup G))
    (hP : ∀ x ∈ P, ∃ r ∈ R, ∃ i : ℤ, x = r * j ^ i) :
    ∀ x ∈ P, R ≤ centralizer {x} → x ∈ zpowers (θ * j) := by
  obtain ⟨hcomm, hpow, -, hcentral⟩ := lemma438_shape R hR hRne θ j hθ hθZ hj hy hcyc
  intro x hx hxc
  obtain ⟨r, hr, i, rfl⟩ := hP x hx
  have hji : j ^ i = θ ^ (-i) * (θ * j) ^ i := by
    rw [hcomm.mul_zpow, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  have hyi : R ≤ centralizer {(θ * j) ^ i} := by
    intro s hs
    have := hy hs
    rw [mem_centralizer_singleton_iff] at this ⊢
    exact (Commute.zpow_right (a := s) this i).eq
  have hrθ : r * θ ^ (-i) ∈ R := R.mul_mem hr (R.zpow_mem hθ _)
  have hc : R ≤ centralizer {r * θ ^ (-i)} := by
    intro s hs
    have h1 := hxc hs
    have h2 := hyi hs
    rw [mem_centralizer_singleton_iff] at h1 h2 ⊢
    have e : r * j ^ i = r * θ ^ (-i) * (θ * j) ^ i := by rw [hji, mul_assoc]
    rw [e] at h1
    have : Commute s (r * θ ^ (-i) * (θ * j) ^ i * ((θ * j) ^ i)⁻¹) :=
      Commute.mul_right (a := s) h1 (Commute.inv_right (a := s) h2)
    simpa using this.eq
  have hz := hcentral _ hrθ hc
  have hθp : θ ^ p ∈ zpowers (θ * j) := by
    rw [← hpow]; exact pow_mem (mem_zpowers _) p
  rw [hji, ← mul_assoc]
  exact mul_mem ((zpowers_le.2 hθp) hz) (zpow_mem (mem_zpowers _) i)

theorem lemma438_card_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K Θ R P : Subgroup G) (hΘK : Θ ≤ K) (hΘn : ∀ k ∈ K, ∀ x ∈ Θ, k * x * k⁻¹ ∈ Θ)
    (hRΘ : R ≤ Θ) (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup G, X ≤ Θ → IsPGroup p X → R ≤ X → X = R)
    (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hPmax : ∀ X : Subgroup G, X ≤ K → IsPGroup p X → Nat.card X ≤ Nat.card P) (hRP : R ≤ P)
    (hRne : R ≠ ⊥) (θ j : G) (hθ : θ ∈ R) (hθZ : ¬ R ≤ centralizer {θ}) (hj : j ^ p = 1)
    (hy : R ≤ centralizer {θ * j}) (hcyc : IsCyclic (R ⊓ centralizer {θ} : Subgroup G))
    (hP : ∀ x ∈ P, ∃ r ∈ R, ∃ i : ℤ, x = r * j ^ i)
    (X : Subgroup G) (hXK : X ≤ K) (hXc : X ≤ centralizer R) (hX : IsPGroup p X) :
    Nat.card X ≤ orderOf (θ * j) := by
  have hXn : X ≤ normalizer (R : Set G) := hXc.trans (centralizer_le_normalizer _)
  have hRX : IsPGroup p (R ⊔ X : Subgroup G) := hR.to_sup_of_normal_left' hX hXn
  obtain ⟨g, hg, hgP⟩ := exists_conj_mem_of_card_max K P (R ⊔ X) hPK
    (sup_le (hRP.trans hPK) hXK) hPp hRX hPmax
  have hPΘ : P ⊓ Θ = R :=
    hRmax _ inf_le_right hPp.to_inf_left (le_inf hRP hRΘ)
  set f := (MulAut.conj g).toMonoidHom
  have hfR : R.map f = R := by
    have hle : R.map f ≤ R := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← hPΘ]
      exact ⟨hgP r (mem_sup_left hr), hΘn g hg r (hRΘ hr)⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
  have hconj : ∀ x ∈ X, g * x * g⁻¹ ∈ zpowers (θ * j) := by
    intro x hx
    refine lemma438_centralizer_le_zpowers R P hR hRne θ j hθ hθZ hj hy hcyc hP _
      (hgP x (mem_sup_right hx)) ?_
    intro r hr
    rw [← hfR] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_iff.1 (hXc hx) r' hr'
    show g * r' * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * r' * g⁻¹)
    calc g * r' * g⁻¹ * (g * x * g⁻¹) = g * (r' * x) * g⁻¹ := by group
      _ = g * (x * r') * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * r' * g⁻¹) := by group
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ zpowers (θ * j) := by
    rintro _ ⟨x, hx, rfl⟩; exact hconj x hx
  rw [← Nat.card_zpowers, ← Subgroup.card_map_of_injective (K := X)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact Subgroup.card_le_of_le hle

theorem false_of_invert_of_centralize_pow {G H : Type*} [Group G] [Group H] (ρ : G →* H)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (y w : G) (k : ℤ) (a : ℕ)
    (hy : y ^ (p ^ a) = 1) (hyp : y ^ p ≠ 1)
    (hconj : w * y * w⁻¹ = y ^ k) (hcomm : w * y ^ p * w⁻¹ = y ^ p)
    (hρy : orderOf (ρ y) = p) (hρw : ρ w * ρ y * (ρ w)⁻¹ = (ρ y)⁻¹) : False := by
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have h1 : (p : ℤ) ∣ k + 1 := by
    have h : (ρ y) ^ (k + 1) = 1 := by
      have e : (ρ y) ^ k = (ρ y)⁻¹ := by
        rw [← map_zpow, ← hconj, map_mul, map_mul, map_inv, hρw]
      rw [zpow_add_one, e, inv_mul_cancel]
    have := (orderOf_dvd_iff_zpow_eq_one (x := ρ y) (i := k + 1)).2 h
    rwa [hρy] at this
  have h2 : y ^ ((p : ℤ) * (k - 1)) = 1 := by
    have e1 : w * y ^ p * w⁻¹ = y ^ (k * (p : ℤ)) := by
      rw [← conj_pow, hconj, ← zpow_natCast, ← zpow_mul]
    have e2 : y ^ (k * (p : ℤ)) = y ^ (p : ℤ) := by
      rw [← e1, zpow_natCast, hcomm]
    have e3 : y ^ (k * (p : ℤ) - p) = 1 := by
      rw [zpow_sub, e2, mul_inv_cancel]
    have : (p : ℤ) * (k - 1) = k * (p : ℤ) - p := by ring
    rwa [this]
  have h3 : (orderOf y : ℤ) ∣ (p : ℤ) * (k - 1) := orderOf_dvd_iff_zpow_eq_one.2 h2
  obtain ⟨b, hb, hb'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hy)
  have hb2 : 2 ≤ b := by
    by_contra hlt
    apply hyp
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hb']
    exact pow_dvd_pow p (by omega : b ≤ 1) |>.trans (by simp)
  have h4 : ((p : ℤ) * p) ∣ (p : ℤ) * (k - 1) := by
    refine Dvd.dvd.trans ?_ h3
    rw [hb']
    push_cast
    rw [← pow_two]
    exact pow_dvd_pow _ hb2
  have h5 : (p : ℤ) ∣ k - 1 :=
    (mul_dvd_mul_iff_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).1 h4
  have h6 : (p : ℤ) ∣ 2 := by
    have := dvd_sub h1 h5
    simpa using this
  have h7 : p ∣ 2 := by exact_mod_cast h6
  rcases (Nat.prime_two.eq_one_or_self_of_dvd p h7) with h | h
  · exact hp1 h
  · exact hp2 h

theorem lemma438 {G H : Type*} [Group G] [Group H] [Finite G] (ρ : G →* H) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (K Θ R P Y : Subgroup G) (hΘK : Θ ≤ K) (hΘn : ∀ k ∈ K, ∀ x ∈ Θ, k * x * k⁻¹ ∈ Θ)
    (hRΘ : R ≤ Θ) (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup G, X ≤ Θ → IsPGroup p X → R ≤ X → X = R)
    (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hPmax : ∀ X : Subgroup G, X ≤ K → IsPGroup p X → Nat.card X ≤ Nat.card P) (hRP : R ≤ P)
    (hRne : R ≠ ⊥) (hRker : R ≤ ρ.ker) (θ j : G) (hθ : θ ∈ R) (hθZ : ¬ R ≤ centralizer {θ})
    (hjP : j ∈ P) (hj : j ^ p = 1) (hρj : ρ j ≠ 1)
    (hy : R ≤ centralizer {θ * j}) (hcyc : IsCyclic (R ⊓ centralizer {θ} : Subgroup G))
    (hP : ∀ x ∈ P, ∃ r ∈ R, ∃ i : ℤ, x = r * j ^ i)
    (hKY : K ≤ Y) (hKn : ∀ a ∈ Y, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hab : ∀ x ∈ K ⊓ centralizer R, ∀ x' ∈ K ⊓ centralizer R, Commute (ρ x) (ρ x'))
    (g : G) (hgY : g ∈ Y) (hgc : g ∈ centralizer R)
    (hinv : ∀ x ∈ K ⊓ centralizer R, ρ g * ρ x * (ρ g)⁻¹ = (ρ x)⁻¹) : False := by
  have hpp : p.Prime := Fact.out
  obtain ⟨hcomm, hpow, hθp1, -⟩ := lemma438_shape R hR hRne θ j hθ hθZ hj hy hcyc
  set y := θ * j with hydef
  have hyP : y ∈ P := P.mul_mem (hRP hθ) hjP
  have hyc : y ∈ centralizer R := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.1 (hy hr)
  have hyB : y ∈ K ⊓ centralizer R := ⟨hPK hyP, hyc⟩
  have hSp : IsPGroup p (zpowers y) := hPp.to_le (zpowers_le.2 hyP)
  have hSmax : ∀ X : Subgroup G, X ≤ K ⊓ centralizer R → IsPGroup p X →
      Nat.card X ≤ Nat.card (zpowers y) := by
    intro X hX hXp
    rw [Nat.card_zpowers]
    exact lemma438_card_le K Θ R P hΘK hΘn hRΘ hR hRmax hPK hPp hPmax hRP hRne θ j hθ hθZ hj
      hy hcyc hP X (hX.trans inf_le_left) (hX.trans inf_le_right) hXp
  have hBA : K ⊓ centralizer R ≤ Y ⊓ centralizer R := inf_le_inf_right _ hKY
  have hBn : ∀ a ∈ Y ⊓ centralizer R, ∀ b ∈ K ⊓ centralizer R,
      a * b * a⁻¹ ∈ K ⊓ centralizer R := fun a ha b hb =>
    ⟨hKn a (mem_inf.1 ha).1 b (mem_inf.1 hb).1, (centralizer (R : Set G)).mul_mem
      ((centralizer (R : Set G)).mul_mem (mem_inf.1 ha).2 (mem_inf.1 hb).2)
      ((centralizer (R : Set G)).inv_mem (mem_inf.1 ha).2)⟩
  obtain ⟨b, hb, w, hw, hwS, rfl⟩ := exists_mul_normalizes_of_card_max _ _ (zpowers y) hBA hBn
    (zpowers_le.2 hyB) hSp hSmax g ⟨hgY, hgc⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hwS y (mem_zpowers y))
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hPp) ⟨y, hyP⟩
  rw [Subgroup.orderOf_mk] at ha
  have hya : y ^ (p ^ a) = 1 := by rw [← ha]; exact pow_orderOf_eq_one y
  have hyp : y ^ p ≠ 1 := by rw [hydef, hpow]; exact hθp1
  have hθpR : θ ^ p ∈ R := R.pow_mem hθ p
  have hcommw : w * y ^ p * w⁻¹ = y ^ p := by
    rw [hydef, hpow]
    have := mem_centralizer_iff.1 (mem_inf.1 hw).2 _ hθpR
    rw [← this]; group
  have hρθ : ρ θ = 1 := hRker hθ
  have hρy : orderOf (ρ y) = p := by
    rw [hydef, map_mul, hρθ, one_mul]
    exact orderOf_eq_prime (by rw [← map_pow, hj, map_one]) hρj
  have hρw : ρ w * ρ y * (ρ w)⁻¹ = (ρ y)⁻¹ := by
    have h1 := hinv y hyB
    have h2 := hab b hb y hyB
    rw [map_mul] at h1
    have : ρ w = (ρ b)⁻¹ * (ρ b * ρ w) := by group
    rw [this, mul_inv_rev, inv_inv]
    calc (ρ b)⁻¹ * (ρ b * ρ w) * ρ y * ((ρ b * ρ w)⁻¹ * ρ b)
        = (ρ b)⁻¹ * (ρ b * ρ w * ρ y * (ρ b * ρ w)⁻¹) * ρ b := by group
      _ = (ρ b)⁻¹ * (ρ y)⁻¹ * ρ b := by rw [h1]
      _ = (ρ y)⁻¹ := by
        rw [mul_assoc, ← (h2.inv_right).eq]; group
  exact false_of_invert_of_centralize_pow ρ hp2 y w k a hya hyp hk.symm hcommw hρy hρw

end CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC
