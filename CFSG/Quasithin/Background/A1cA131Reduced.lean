module

public import CFSG.Quasithin.Background.A1cRankLemmas
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.ThompsonAxB
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace A1c

variable {G Q : Type*} [Group G] [Group Q] {p : ℕ}

@[expose] def preCore (p : ℕ) (φ : G →* Q) : Subgroup G := (pCore p Q).comap φ

theorem mem_preCore {φ : G →* Q} {x : G} : x ∈ preCore p φ ↔ φ x ∈ pCore p Q := Iff.rfl

theorem preCore_normal (φ : G →* Q) : (preCore p φ).Normal :=
  (CFSG.pCore_normal (G := Q) (p := p)).comap φ

theorem ker_le_preCore (φ : G →* Q) : φ.ker ≤ preCore p φ := fun x hx => by
  rw [mem_preCore, MonoidHom.mem_ker.1 hx]
  exact (pCore p Q).one_mem

theorem map_preCore [Finite Q] {φ : G →* Q} (hφ : Function.Surjective φ) :
    (preCore p φ).map φ = pCore p Q :=
  Subgroup.map_comap_eq_self_of_surjective hφ _

theorem isPGroup_preCore [Fact p.Prime] [Finite Q] {φ : G →* Q} (hker : IsPGroup p φ.ker) :
    IsPGroup p (preCore p φ) := by
  intro x
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := Q) (p := p) ⟨φ x.1, x.2⟩
  have hk' : φ (x.1 ^ p ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  obtain ⟨l, hl⟩ := hker ⟨x.1 ^ p ^ k, hk'⟩
  refine ⟨k + l, Subtype.ext ?_⟩
  have hl' : (x.1 ^ p ^ k) ^ p ^ l = 1 := congrArg Subtype.val hl
  rw [← pow_mul, ← pow_add] at hl'
  simpa using hl'

theorem centralizer_preCore_le [Finite Q] {φ : G →* Q} (hφ : Function.Surjective φ)
    (hF : Subgroup.centralizer (pCore p Q : Set Q) ≤ pCore p Q) :
    Subgroup.centralizer (preCore p φ : Set G) ≤ preCore p φ := by
  intro x hx
  rw [mem_preCore]
  apply hF
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨z, rfl⟩ := hφ y
  have hz : z ∈ preCore p φ := hy
  have := Subgroup.mem_centralizer_iff.1 hx z hz
  rw [← map_mul, ← map_mul, this]

theorem mem_normalizer_of_normal {P : Subgroup G} [P.Normal] (t : G) :
    t ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => Subgroup.Normal.conj_mem ‹P.Normal› x hx t, fun hx => by
    have := Subgroup.Normal.conj_mem ‹P.Normal› _ hx t⁻¹
    simpa [mul_assoc] using this⟩

theorem not_mem_of_orderOf_eq_two [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) (hp2 : p ≠ 2) {t : G}
    (ht : orderOf t = 2) : t ∉ P := by
  intro htP
  obtain ⟨k, hk⟩ := hP ⟨t, htP⟩
  have hk' : t ^ p ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 2 ∣ p ^ k := ht ▸ orderOf_dvd_of_pow_eq_one hk'
  have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 h2p).symm


section InvolutionCentralizer

variable [Finite G]

omit [Finite G] in
theorem conjAut_apply_coe' {N K : Subgroup G} (h : K ≤ Subgroup.normalizer (N : Set G)) (k : K)
    (n : N) : ((conjAut h k n : N) : G) = (k : G) * n * (k : G)⁻¹ := by
  rw [conjAut_apply_coe]; simp

theorem isCyclic_centralizer_of_involution [Fact p.Prime] (hp2 : p ≠ 2)
    (hrk : pRank p (⊤ : Subgroup G) ≤ 2) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    (hC : Subgroup.centralizer (P : Set G) ≤ P) {t : G} (ht : orderOf t = 2) :
    IsCyclic ↥(P ⊓ Subgroup.centralizer ({t} : Set G)) := by
  by_contra hnc
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set B : Subgroup G := P ⊓ Subgroup.centralizer ({t} : Set G) with hB
  have hBp : IsPGroup p B := hP.to_le inf_le_left
  obtain ⟨E, hEB, hE, hEcard⟩ := exists_isElemAbelian_card_sq hp2 hBp hnc
  have htP : t ∉ P := not_mem_of_orderOf_eq_two hP hp2 ht
  have hnt : ∃ r ∈ P, r * t ≠ t * r := by
    by_contra hcon
    push Not at hcon
    exact htP (hC (Subgroup.mem_centralizer_iff.2 hcon))
  have hAn : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]; exact mem_normalizer_of_normal t
  have hBn : B ≤ Subgroup.normalizer (P : Set G) := fun b _ => mem_normalizer_of_normal b
  have hAcard : ¬ p ∣ Nat.card ↥(Subgroup.zpowers t) := by
    rw [Nat.card_zpowers, ht]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h)
  have hbt : ∀ b : B, Commute (b : G) t := fun b =>
    (Subgroup.mem_centralizer_iff.1 b.2.2 t (Set.mem_singleton t)).symm
  have hba : ∀ (b : B) (a : ↥(Subgroup.zpowers t)), (b : G) * a = a * b := fun b a => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    rw [← hk]
    exact ((hbt b).zpow_right k).eq
  have hcomm : ∀ (a : ↥(Subgroup.zpowers t)) (b : B),
      conjAut hAn a * conjAut hBn b = conjAut hBn b * conjAut hAn a := by
    intro a b
    ext r
    simp only [MulAut.mul_apply]
    rw [conjAut_apply_coe', conjAut_apply_coe', conjAut_apply_coe', conjAut_apply_coe']
    have h1 : (a : G) * (b : G) = (b : G) * a := (hba b a).symm
    calc (a : G) * ((b : G) * r * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * r * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * r * ((b : G) * a)⁻¹ := by rw [h1]
      _ = (b : G) * ((a : G) * r * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have key : ∃ z : P, (∀ b : B, conjAut hBn b z = z) ∧ t * (z : G) * t⁻¹ ≠ z := by
    by_contra hno
    push Not at hno
    have h1 := CFSG.GroupTheory.thompson_A_times_B (p := p) (R := ↥P) hP hAcard hBp
      (conjAut hAn) (conjAut hBn) hcomm (by
        intro a r hr
        have h2 : t * (r : G) * t⁻¹ = r := hno r hr
        have h3 : Commute t (r : G) := by
          have : t * (r : G) = r * t := by
            rw [mul_inv_eq_iff_eq_mul] at h2; exact h2
          exact this
        apply Subtype.ext
        rw [conjAut_apply_coe']
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
        have h4 : Commute ((a : G)) (r : G) := by rw [← hk]; exact h3.zpow_left k
        rw [h4.eq]; group)
    obtain ⟨r, hr, hrt⟩ := hnt
    have h5 := h1 ⟨t, Subgroup.mem_zpowers t⟩
    have h6 := congrArg (fun m : MulAut ↥P => ((m ⟨r, hr⟩ : ↥P) : G)) h5
    simp only [conjAut_apply_coe', MulAut.one_apply] at h6
    apply hrt
    have : t * r * t⁻¹ = r := h6
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨z, hz1, hz2⟩ := key
  have hzB : ∀ b ∈ B, b * (z : G) * b⁻¹ = z := fun b hb => by
    have := congrArg Subtype.val (hz1 ⟨b, hb⟩)
    rwa [conjAut_apply_coe'] at this
  set u : G := (z : G)⁻¹ * (t * z * t⁻¹) with hu
  have huP : u ∈ P := P.mul_mem (P.inv_mem z.2)
    (Subgroup.Normal.conj_mem ‹P.Normal› _ z.2 t)
  have hu1 : u ≠ 1 := by
    intro h
    apply hz2
    rw [hu, inv_mul_eq_one] at h
    exact h.symm
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [htinv, htt]
  have hu_inv : t * u * t⁻¹ = u⁻¹ := by
    calc t * u * t⁻¹ = t * (z : G)⁻¹ * t * z * (t⁻¹ * t⁻¹) := by rw [hu]; group
      _ = t * (z : G)⁻¹ * t * z := by rw [hti, mul_one]
      _ = t * (z : G)⁻¹ * t⁻¹ * z := by rw [htinv]
      _ = u⁻¹ := by rw [hu]; group
  have huB : ∀ b ∈ B, b * u = u * b := by
    intro b hb
    have hbtc : (b : G) * t = t * b := (hbt ⟨b, hb⟩).eq
    have e1 := hzB b hb
    have e2 : b * (t * (z : G) * t⁻¹) * b⁻¹ = t * z * t⁻¹ := by
      calc b * (t * (z : G) * t⁻¹) * b⁻¹ = (b * t) * z * (b * t)⁻¹ := by group
        _ = (t * b) * z * (t * b)⁻¹ := by rw [hbtc]
        _ = t * (b * z * b⁻¹) * t⁻¹ := by group
        _ = t * z * t⁻¹ := by rw [e1]
    have e1' : b * (z : G)⁻¹ * b⁻¹ = (z : G)⁻¹ := by
      have : b * (z : G)⁻¹ * b⁻¹ = (b * z * b⁻¹)⁻¹ := by group
      rw [this, e1]
    have : b * u * b⁻¹ = u := by
      calc b * u * b⁻¹ = (b * (z : G)⁻¹ * b⁻¹) * (b * (t * z * t⁻¹) * b⁻¹) := by rw [hu]; group
        _ = u := by rw [e1', e2, hu]
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have huPg : IsPGroup p (Subgroup.zpowers u) := hP.to_le ((Subgroup.zpowers_le).2 huP)
  have hdvd : p ∣ Nat.card ↥(Subgroup.zpowers u) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 huPg
    rw [hm]
    rcases m with _ | m
    · exfalso
      have h0 : Nat.card ↥(Subgroup.zpowers u) = 1 := by simpa using hm
      have h1 := Subgroup.card_eq_one.1 h0
      apply hu1
      have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
      rw [h1] at this
      exact Subgroup.mem_bot.1 this
    · exact dvd_pow_self p (Nat.succ_ne_zero m)
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers u)) p hdvd
  set y : G := (y' : G) with hy
  have hyord : orderOf y = p := by rw [hy, Subgroup.orderOf_coe, hy']
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y'.2
  have hyinv : t * y * t⁻¹ = y⁻¹ := by
    rw [hy, ← hk, ← conj_zpow, hu_inv, inv_zpow]
  have hycomm : ∀ b ∈ B, Commute b y := by
    intro b hb
    rw [hy, ← hk]
    exact (Commute.zpow_right (show Commute b u from huB b hb) k)
  have hyB : y ∉ B := by
    intro hyB'
    have h1 : t * y * t⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.1 hyB'.2 t (Set.mem_singleton t)
      rw [mul_inv_eq_iff_eq_mul]; exact this
    rw [h1] at hyinv
    have h2 : y * y = 1 := mul_eq_one_iff_eq_inv.2 hyinv
    have h3 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hyord] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h3)
  have hyE : y ∉ E := fun h => hyB (hEB h)
  obtain ⟨hA, hAcard'⟩ := exists_elemAbelian_sup_zpowers hE hyord
    (fun e he => hycomm e (hEB he)) hyE
  have h3 : 3 ≤ pRank p (⊤ : Subgroup G) :=
    le_pRank (Fact.out : p.Prime) le_top hA (k := 3) (by rw [hAcard', hEcard]; ring)
  omega

end InvolutionCentralizer

section Reduced

variable [Finite G] [Finite Q]

omit [Finite Q] in
theorem pCore_inf_centralizer_le_map [Fact p.Prime] {φ : G →* Q} (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) (hp2 : p ≠ 2) {t : G} (ht : t ^ 2 = 1) :
    pCore p Q ⊓ Subgroup.centralizer ({φ t} : Set Q) ≤
      (preCore p φ ⊓ Subgroup.centralizer ({t} : Set G)).map φ := by
  rintro q ⟨hq, hqc⟩
  obtain ⟨x, rfl⟩ := hφ q
  have hcomm : φ t * φ x = φ x * φ t :=
    Subgroup.mem_centralizer_iff.1 hqc (φ t) (Set.mem_singleton _)
  obtain ⟨w, hw, htw⟩ := exists_lift_fixed hker hp2 ht hcomm
  refine ⟨w, ⟨?_, ?_⟩, hw⟩
  · show w ∈ preCore p φ
    rw [mem_preCore, hw]; exact hq
  · show w ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact htw

theorem exists_orderOf_eq_two_of_isPGroup {T : Subgroup Q} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ q ∈ T, orderOf q = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hT1 (Subgroup.card_eq_one.1 (by simpa using hk))
  have hdvd : 2 ∣ Nat.card T := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem reduced_isCyclic_centralizer [Fact p.Prime] (hp2 : p ≠ 2) {φ : G →* Q}
    (hφ : Function.Surjective φ) (hker : IsPGroup p φ.ker)
    (hrk : pRank p (⊤ : Subgroup G) ≤ 2)
    (hF : Subgroup.centralizer (pCore p Q : Set Q) ≤ pCore p Q) {T : Subgroup Q}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    IsCyclic ↥(pCore p Q ⊓ Subgroup.centralizer (T : Set Q)) := by
  obtain ⟨q, hqT, hq⟩ := exists_orderOf_eq_two_of_isPGroup hT hT1
  obtain ⟨t, ht, rfl⟩ := exists_involution_lift hφ hker hp2 hq
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have := preCore_normal (p := p) φ
  have hcyc : IsCyclic ↥(preCore p φ ⊓ Subgroup.centralizer ({t} : Set G)) :=
    isCyclic_centralizer_of_involution hp2 hrk (isPGroup_preCore hker)
      (centralizer_preCore_le hφ hF) ht
  have : IsCyclic ↥((preCore p φ ⊓ Subgroup.centralizer ({t} : Set G)).map φ) :=
    isCyclic_of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)
  have hle : pCore p Q ⊓ Subgroup.centralizer (T : Set Q) ≤
      (preCore p φ ⊓ Subgroup.centralizer ({t} : Set G)).map φ :=
    le_trans (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hqT)))
      (pCore_inf_centralizer_le_map hφ hker hp2 ht2)
  exact Subgroup.isCyclic_of_le hle

omit [Finite Q] in
theorem isElemAbelian_of_le' {A B : Subgroup Q} (h : A ≤ B) (hB : IsElemAbelian p B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB h

omit [Finite Q] in
theorem isElementaryAbelian_of_isElemAbelian {A : Subgroup Q} (h : IsElemAbelian p A) :
    CFSG.IsElementaryAbelian p ↥A :=
  CFSG.Open.IsElemAbelian.isElementaryAbelian h

theorem exists_isElemAbelian_card_pow {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n ≤ pRank p (⊤ : Subgroup Q)) :
    ∃ E : Subgroup Q, IsElemAbelian p E ∧ Nat.card E = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, -, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup Q)
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (p := p) hp
    (isPGroup_of_isElemAbelian hE₀) (n := n) (by rw [hcard]; exact Nat.pow_le_pow_right hp.pos hn)
  refine ⟨S.map E₀.subtype, ?_, ?_⟩
  · exact isElemAbelian_of_le' (Subgroup.map_subtype_le S) hE₀
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hS]

omit [Finite G] [Finite Q] in
theorem eq_one_of_sq_eq_one_of_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : Q} (hx2 : x ^ 2 = 1)
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hxp
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (Ne.symm hp2))
  have := pow_gcd_eq_one.2 ⟨hx2, hk⟩
  rwa [hcop, pow_one] at this

theorem reduced_pRank_two_le [Fact p.Prime] (hp2 : p ≠ 2) {φ : G →* Q}
    (hφ : Function.Surjective φ) (hker : IsPGroup p φ.ker)
    (hrk : pRank p (⊤ : Subgroup G) ≤ 2)
    (hF : Subgroup.centralizer (pCore p Q : Set Q) ≤ pCore p Q) :
    pRank 2 (⊤ : Subgroup Q) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hAcard⟩ := exists_isElemAbelian_card_pow Nat.prime_two (n := 3) (by omega)
  have hPn : (pCore p Q).Normal := CFSG.pCore_normal (G := Q) (p := p)
  have hAn : A ≤ Subgroup.normalizer (pCore p Q : Set Q) := fun a _ =>
    mem_normalizer_of_normal a
  let _ : MulDistribMulAction ↥A ↥(pCore p Q) :=
    MulDistribMulAction.compHom ↥(pCore p Q) (conjAut hAn)
  have _ : CFSG.IsElementaryAbelian 2 ↥A := isElementaryAbelian_of_isElemAbelian hA
  have hAP : A ⊓ pCore p Q = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxP⟩
    have hx2 : x ^ 2 = 1 := hA.2 x hxA
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := Q) (p := p) ⟨x, hxP⟩
    exact Subgroup.mem_bot.2 (eq_one_of_sq_eq_one_of_pow hp2 hx2 ⟨k, congrArg Subtype.val hk⟩)
  have hfaith : ∀ a : ↥A, (∀ x : ↥(pCore p Q), a • x = x) → a = 1 := by
    intro a ha
    have hac : (a : Q) ∈ Subgroup.centralizer (pCore p Q : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := congrArg Subtype.val (ha ⟨y, hy⟩)
      change (a : Q) * y * (a : Q)⁻¹ = y at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hmem : (a : Q) ∈ A ⊓ pCore p Q := ⟨a.2, hF hac⟩
    rw [hAP] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  obtain ⟨a, ha1, hacyc⟩ := exists_not_isCyclic_fixedPoints hp2 (CFSG.pCore_isPGroup (G := Q) (p := p))
    (by rw [hAcard]; norm_num) hfaith
  have ha2 : (a : Q) ^ 2 = 1 := hA.2 a a.2
  have hT : IsPGroup 2 (Subgroup.zpowers (a : Q)) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow]
  have hT1 : Subgroup.zpowers (a : Q) ≠ ⊥ := by
    intro h
    apply ha1
    apply Subtype.ext
    have : (a : Q) ∈ Subgroup.zpowers (a : Q) := Subgroup.mem_zpowers _
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hcyc := reduced_isCyclic_centralizer hp2 hφ hker hrk hF hT hT1
  apply hacyc
  set F := CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥(pCore p Q) with hFdef
  have hle : F.map (pCore p Q).subtype ≤
      pCore p Q ⊓ Subgroup.centralizer ((Subgroup.zpowers (a : Q) : Subgroup Q) : Set Q) := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 : a • y = y := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a y).1 hy
    have h2 : (a : Q) * y * (a : Q)⁻¹ = y := congrArg Subtype.val h1
    have h3 : Commute (a : Q) (y : Q) := by
      rw [mul_inv_eq_iff_eq_mul] at h2; exact h2
    show (y : Q) ∈ Subgroup.centralizer ((Subgroup.zpowers (a : Q) : Subgroup Q) : Set Q)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← hk]
    exact (h3.zpow_left k).eq
  have hcycmap : IsCyclic ↥(F.map (pCore p Q).subtype) := Subgroup.isCyclic_of_le hle
  exact isCyclic_of_surjective (F.equivMapOfInjective (pCore p Q).subtype
    (pCore p Q).subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)

end Reduced

end A1c

end CFSG.Quasithin
