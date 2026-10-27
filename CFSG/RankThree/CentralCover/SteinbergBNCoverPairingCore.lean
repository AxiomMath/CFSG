module

public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2 CFSG.Assembly CFSG.Assembly.RankThreeEven

section Closure

variable {T : Type*} [Group T]

theorem commute_of_mem_closure {S : Set T} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) {x y : T}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : Commute x y := by
  have hyS : ∀ s ∈ S, Commute s y := by
    intro s hs
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {s} :=
      (Subgroup.closure_le _).2 fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.2 (hS t ht s hs).eq
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hyS s hs).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem pow_eq_one_of_mem_closure {S : Set T} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) {n : ℕ}
    (hSn : ∀ s ∈ S, s ^ n = 1) {x : T} (hx : x ∈ Subgroup.closure S) : x ^ n = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hSn s hs
  | one => exact one_pow n
  | mul a b ha hb iha ihb =>
    rw [(commute_of_mem_closure hS ha hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end Closure

section Lift

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem liftComm_eq_one_of_conj_inv (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : Odd p) {s t : T} (h : Commute s t)
    (hs : s ^ p = 1) (g : T) (hgs : g * s * g⁻¹ = s⁻¹) (hgt : g * t * g⁻¹ = t) :
    liftComm φ hφ s t = 1 := by
  have hc := liftComm_conj hφ hker h g
  rw [hgs, hgt, liftComm_inv_left hφ hker h] at hc
  have h2 : liftComm φ hφ s t ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hc]
    exact inv_mul_cancel _
  have hp1 : liftComm φ hφ s t ^ p = 1 := by
    rw [← liftComm_pow_left hφ hker h, hs, liftComm_one_left hφ hker]
  exact eq_one_of_sq_eq_one_of_pow_eq_one hp h2 hp1

theorem liftComm_eq_one_of_mem_closure (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {S : Set T} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (h : ∀ s ∈ S, ∀ t ∈ S, liftComm φ hφ s t = 1) {x y : T} (hx : x ∈ Subgroup.closure S)
    (hy : y ∈ Subgroup.closure S) : liftComm φ hφ x y = 1 := by
  have h1 : ∀ t ∈ S, ∀ x ∈ Subgroup.closure S, liftComm φ hφ x t = 1 := by
    intro t ht x hx
    have htc : t ∈ Subgroup.closure S := Subgroup.subset_closure ht
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact h s hs t ht
    | one => exact liftComm_one_left hφ hker t
    | mul a b ha hb iha ihb =>
      rw [liftComm_mul_left hφ hker (commute_of_mem_closure hS hb htc), iha, ihb, one_mul]
    | inv a ha iha =>
      rw [liftComm_inv_left hφ hker (commute_of_mem_closure hS ha htc), iha, inv_one]
  induction hy using Subgroup.closure_induction with
  | mem t ht => exact h1 t ht x hx
  | one => exact liftComm_one_right hφ hker x
  | mul a b ha hb iha ihb =>
    rw [liftComm_mul_right hφ hker (commute_of_mem_closure hS hx hb), iha, ihb, one_mul]
  | inv a ha iha =>
    rw [liftComm_swap, liftComm_inv_left hφ hker (commute_of_mem_closure hS ha hx),
      liftComm_swap, iha, inv_one, inv_one, inv_one]

theorem comap_closure_comm (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {S : Set T} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (h : ∀ s ∈ S, ∀ t ∈ S, liftComm φ hφ s t = 1) :
    ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ, x * y = y * x :=
  fun _ hx _ hy => mul_comm_of_liftComm_eq_one hφ hker
    (fun _ hs _ ht => liftComm_eq_one_of_mem_closure hφ hker hS h hs ht) hx hy

end Lift

section Card

variable {T : Type*} [Group T]

theorem card_iSup_eq_prod {ι : Type*} [Fintype ι] {H : ι → Subgroup T}
    (hcomm : Pairwise fun i j => ∀ x y : T, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) : Nat.card (⨆ i, H i : Subgroup T) = ∏ i, Nat.card (H i) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), ← Nat.card_pi]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_closure_of_inversions {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : Odd r)
    (h w : ι → T) (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = r)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) :
    Nat.card (Subgroup.closure (Set.range h)) = r ^ Fintype.card ι := by
  have hcl : Subgroup.closure (Set.range h) = ⨆ i, Subgroup.zpowers (h i) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp only [Subgroup.zpowers_eq_closure]
  have hcommH : Pairwise fun i j => ∀ x y : T, x ∈ Subgroup.zpowers (h i) →
      y ∈ Subgroup.zpowers (h j) → Commute x y := by
    intro i j _ x y hx hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((hcomm i j).zpow_left a).zpow_right b
  have hind : iSupIndep fun i => Subgroup.zpowers (h i) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    have hle : (⨆ (j) (_ : j ≠ i), Subgroup.zpowers (h j)) ≤ Subgroup.centralizer {w i} :=
      iSup₂_le fun j hj => Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (by
        have := hfix i j (Ne.symm hj)
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm))
    have hfixy : w i * y * (w i)⁻¹ = y := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
      rw [← this, mul_inv_cancel_right]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hinvy : w i * h i ^ k * (w i)⁻¹ = (h i ^ k)⁻¹ := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hinv i, inv_zpow]
    rw [hinvy] at hfixy
    have h2 : (h i ^ k) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hfixy]
      exact inv_mul_cancel _
    have hr1 : (h i ^ k) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hord i,
        pow_orderOf_eq_one, one_zpow]
    exact eq_one_of_sq_eq_one_of_pow_eq_one hr h2 hr1
  rw [hcl, card_iSup_eq_prod hcommH hind]
  simp only [Nat.card_zpowers, hord, Finset.prod_const, Finset.card_univ]

end Card

section Package

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem inversion_basis_package (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h w : ι → T)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = r)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) :
    IsElemAbelian r (Subgroup.closure (Set.range h)) ∧
      Nat.card (Subgroup.closure (Set.range h)) = r ^ Fintype.card ι ∧
      ∀ x ∈ (Subgroup.closure (Set.range h)).comap φ,
        ∀ y ∈ (Subgroup.closure (Set.range h)).comap φ, x * y = y * x := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hS : ∀ s ∈ Set.range h, ∀ t ∈ Set.range h, Commute s t := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hpow : ∀ i, h i ^ r = 1 := fun i => by rw [← hord i, pow_orderOf_eq_one]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (commute_of_mem_closure hS a.2 b.2).eq⟩⟩, fun x hx =>
    pow_eq_one_of_mem_closure hS (by rintro _ ⟨i, rfl⟩; exact hpow i) hx⟩,
    card_closure_of_inversions hodd h w hcomm hord hinv hfix, ?_⟩
  refine comap_closure_comm hφ hker hS ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  by_cases hij : i = j
  · rw [hij]
    exact liftComm_self hφ (h j)
  · exact liftComm_eq_one_of_conj_inv hφ hker hodd (hcomm i j) (hpow i) (w i) (hinv i)
      (hfix i j hij)

end Package

section Witness

theorem centralizer_le_normalizer_zpowers {G : Type*} [Group G] (u : G) :
    Subgroup.centralizer {u} ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

theorem isTwoLocal_normalizer_zpowers {G : Type*} [Group G] {u : G} (hu : orderOf u = 2) :
    IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) := by
  refine ⟨Subgroup.zpowers u, fun h => ?_, IsPGroup.of_card (n := 1) ?_, rfl⟩
  · rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hu
    omega
  · rw [Nat.card_zpowers, hu, pow_one]

variable {G : Type*} [Group G] [Finite G] (Y : Subgroup G) {T : Type*} [Group T] {φ : Y →* T}

theorem central_cover_involution_witness (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup T}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x)
    {r : ℕ} (hr : p ^ r ≤ Nat.card D) {z : T} (hz : orderOf z = 2)
    (hzD : ∀ x ∈ D, Commute z x) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ r ∧
      A ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) ∧
      IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) ∧ r ≤ localRank p G := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard⟩ :=
    exists_involution_elemAbelian_of_cover Y hφ hker hp hp2 hDp hF hr hz1 hz2 hzD
  exact ⟨u, huY, hu, A, hA, hAab, hAcard,
    (le_inf_iff.1 hA).2.trans (centralizer_le_normalizer_zpowers u),
    isTwoLocal_normalizer_zpowers hu,
    le_localRank_of_involution_elemAbelian hp hu (le_inf_iff.1 hA).2 hAab hAcard⟩

omit [Finite G] in
theorem exists_two_subgroup_normalized_of_cover {Y : Type*} [Group Y] [Finite Y] {φ : Y →* T}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {U : Subgroup T}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) {S : Subgroup Y}
    (hSU : ∀ x ∈ S, ∀ u ∈ U, φ x * u * (φ x)⁻¹ ∈ U) :
    ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup 2 R ∧ S ≤ Subgroup.normalizer (R : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup Y := U.comap φ with hB
  let ψ : B →* U := (φ.comp B.subtype).codRestrict U (fun b => b.2)
  have hψ : Function.Surjective ψ := by
    intro u
    obtain ⟨y, hy⟩ := hφ u
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    change φ y ∈ U
    rw [hy]
    exact u.2
  obtain ⟨P⟩ : Nonempty (Sylow 2 B) := inferInstance
  have hPU : (P : Subgroup B).map ψ = ⊤ :=
    ((P.mapSurjective hψ).is_maximal' (hU2.to_subgroup ⊤) le_top).symm
  have hcentral : ∀ g : B, ∃ x ∈ (P : Subgroup B), ∀ b : B, b * (x⁻¹ * g) = (x⁻¹ * g) * b := by
    intro g
    have hg : ψ g ∈ (P : Subgroup B).map ψ := by
      rw [hPU]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hg
    refine ⟨x, hx, fun b => Subtype.ext ?_⟩
    have hk : ((x⁻¹ * g : B) : Y) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : ψ (x⁻¹ * g) = 1 := by rw [map_mul, map_inv, hxg, inv_mul_cancel]
      exact congrArg Subtype.val h1
    exact Subgroup.mem_center_iff.1 (hker hk) b
  have hnormal : (P : Subgroup B).Normal := by
    constructor
    intro n hn g
    obtain ⟨x, hx, hc⟩ := hcentral g
    have : g * n * g⁻¹ = x * n * x⁻¹ := by
      calc g * n * g⁻¹ = x * ((x⁻¹ * g) * n) * (x⁻¹ * g)⁻¹ * x⁻¹ := by group
        _ = x * (n * (x⁻¹ * g)) * (x⁻¹ * g)⁻¹ * x⁻¹ := by rw [hc n]
        _ = x * n * x⁻¹ := by group
    rw [this]
    exact (P : Subgroup B).mul_mem ((P : Subgroup B).mul_mem hx hn) ((P : Subgroup B).inv_mem hx)
  have huniq : ∀ Q : Sylow 2 B, Q = P := by
    have := Sylow.unique_of_normal P hnormal
    exact fun Q => Subsingleton.elim Q P
  have hmemP : ∀ b : B, (∃ k : ℕ, b ^ 2 ^ k = 1) → b ∈ (P : Subgroup B) := by
    rintro b ⟨k, hk⟩
    have hz : IsPGroup 2 (Subgroup.zpowers b) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
    rw [huniq Q] at hQ
    exact hQ (Subgroup.mem_zpowers b)
  have key : ∀ s ∈ S, ∀ y ∈ (P : Subgroup B).map B.subtype,
      s * y * s⁻¹ ∈ (P : Subgroup B).map B.subtype := by
    intro s hs y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨b, hb⟩
    have hmemB : s * (b : Y) * s⁻¹ ∈ B := by
      change φ (s * b * s⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv]
      exact hSU s hs _ b.2
    refine ⟨⟨s * b * s⁻¹, hmemB⟩, hmemP _ ⟨k, Subtype.ext ?_⟩, rfl⟩
    have hk' : (b : Y) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : (P : Subgroup B) => ((x : B) : Y)) hk
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, hk', mul_one, mul_inv_cancel]
  refine ⟨(P : Subgroup B).map B.subtype, fun hR => hU1 ?_, P.isPGroup'.map B.subtype, ?_⟩
  · have hP : (P : Subgroup B) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have : (b : Y) ∈ (P : Subgroup B).map B.subtype := ⟨b, hb, rfl⟩
      rw [hR, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    rw [hP, Subgroup.map_bot] at hPU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := by
      rw [hPU]
      exact Subgroup.mem_top _
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 this))
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key s hs y, fun h => ?_⟩
    have := key s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this

theorem central_cover_normalizer_witness (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup T}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x)
    {r : ℕ} (hr : p ^ r ≤ Nat.card D) {U : Subgroup T} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hDU : ∀ d ∈ D, ∀ u ∈ U, d * u * d⁻¹ ∈ U) :
    ∃ R : Subgroup G, R ≤ Y ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ A : Subgroup G,
      A ≤ Y ⊓ Subgroup.normalizer (R : Set G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ r ∧
      IsTwoLocal (Subgroup.normalizer (R : Set G)) ∧ r ≤ localRank p G := by
  obtain ⟨V, hVF, hVab, hVcard, -⟩ := exists_elemAbelian_le_centralizer hφ hker hp hp2 hDp hF hr
    (u := 1) (one_pow 2) (fun x _ => by rw [map_one]; exact Commute.one_left x)
  obtain ⟨R₀, hR₀, hR₀2, hSR⟩ := exists_two_subgroup_normalized_of_cover hφ hker hU1 hU2
    (S := D.comap φ) (fun x hx u hu => hDU _ hx u hu)
  have hR1 : R₀.map Y.subtype ≠ ⊥ := fun h =>
    hR₀ ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h)
  have hAN : V.map Y.subtype ≤ Subgroup.normalizer ((R₀.map Y.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono (hVF.trans hSR)).trans (Subgroup.le_normalizer_map Y.subtype)
  have hAab : IsElemAbelian p (V.map Y.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨va, hva, rfl⟩⟩ := a
      obtain ⟨_, ⟨vb, hvb, rfl⟩⟩ := b
      apply Subtype.ext
      change (va : G) * vb = vb * va
      exact congrArg Subtype.val
        (congrArg Subtype.val (hVab.1.is_comm.comm ⟨va, hva⟩ ⟨vb, hvb⟩))
    · rintro _ ⟨v, hv, rfl⟩
      change (v : G) ^ p = 1
      rw [← Subgroup.coe_pow, hVab.2 v hv, OneMemClass.coe_one]
  have hAcard : Nat.card (V.map Y.subtype) = p ^ r := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hVcard]
  have hloc : IsTwoLocal (Subgroup.normalizer ((R₀.map Y.subtype : Subgroup G) : Set G)) :=
    ⟨_, hR1, hR₀2.map Y.subtype, rfl⟩
  refine ⟨R₀.map Y.subtype, Subgroup.map_subtype_le R₀, hR1, hR₀2.map Y.subtype,
    V.map Y.subtype, le_inf (Subgroup.map_subtype_le V) hAN, hAab, hAcard, hloc, ?_⟩
  exact (CFSG.SectionRank.le_pRank hp.one_lt hAN hAab hAcard).trans
    (le_csSup (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_bddAbove p hp G)
      ⟨_, hloc, rfl⟩)

end Witness

end CFSG.RankThree.CentralCover
