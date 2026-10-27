module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_eq_of_ne_one_of_card_le_two {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ≤ 2) {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcase : Nat.card H = 1 ∨ Nat.card H = 2 := by omega
  rcases hcase with h1 | h2
  · haveI : Subsingleton H := (Finite.card_le_one_iff_subsingleton (α := H)).mp (le_of_eq h1)
    exact absurd (Subsingleton.elim a 1) ha
  · obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    exact (huniq a ha).trans (huniq b hb).symm

private theorem s16h_perm_fin3_pow_six :
    ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 → σ ^ 3 = 1 ∨ σ ^ 2 = 1 := by
  decide +kernel

private theorem s16h_normal_two_subgroup_perm_fin3_eq_bot {G : Type*} [Group G] [Finite G]
    (ψ : G →* Equiv.Perm (Fin 3)) (hψ : Function.Injective ψ)
    (hodd : ∃ u : G, orderOf u = 3) {T : Subgroup G} [T.Normal]
    (hT2 : ∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n = 1) : T = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hpg : IsPGroup 2 ↥T := fun x => by
    obtain ⟨n, hn⟩ := hT2 x.1 x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hdvd6 : Nat.card ↥T ∣ 6 := by
    have h1 : Nat.card (T.map ψ) ∣ Nat.card (Equiv.Perm (Fin 3)) :=
      Subgroup.card_subgroup_dvd_card (T.map ψ)
    rw [Subgroup.card_map_of_injective hψ, hcard6] at h1
    exact h1
  have hk_le : k ≤ 1 := by
    rw [hk] at hdvd6
    by_contra h
    have h2 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h4 : (4 : ℕ) ∣ 6 := by
      have h1 : (4 : ℕ) ∣ 2 ^ k := by simpa using h2
      exact h1.trans hdvd6
    norm_num at h4
  have hcardT : Nat.card ↥T ∣ 2 := by
    rw [hk]
    exact pow_dvd_pow 2 hk_le
  have hcardTle : Nat.card ↥T ≤ 2 := Nat.le_of_dvd (by norm_num) hcardT
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  by_contra ht1
  obtain ⟨u, hu⟩ := hodd
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have ht2 : t ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard T ht).trans hcardT)
  have hconj_mem : u * t * u⁻¹ ∈ T := (inferInstance : T.Normal).conj_mem t ht u
  have hcentral : u * t * u⁻¹ = t := by
    have ha : (⟨t, ht⟩ : ↥T) ≠ 1 := fun h1 => ht1 (Subtype.ext_iff.mp h1)
    have hb : (⟨u * t * u⁻¹, hconj_mem⟩ : ↥T) ≠ 1 := by
      intro h1
      apply ha
      have h1' : u * t * u⁻¹ = 1 := Subtype.ext_iff.mp h1
      refine Subtype.ext ?_
      calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
        _ = u⁻¹ * 1 * u := by rw [h1']
        _ = 1 := by group
    exact (Subtype.ext_iff.mp
      (s16h_eq_of_ne_one_of_card_le_two hcardTle ha hb)).symm
  have hu3 : u ^ 3 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have hu2ne : u ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hu] at hdvd
    norm_num at hdvd
  have htu : t * u = u * t := by
    have h1 : u * t = t * u := by
      calc u * t = (u * t * u⁻¹) * u := by group
        _ = t * u := by rw [hcentral]
    exact h1.symm
  have hψt2 : (ψ t) ^ 2 = 1 := by
    calc (ψ t) ^ 2 = ψ (t ^ 2) := (map_pow ψ t 2).symm
      _ = ψ 1 := by rw [ht2]
      _ = 1 := map_one ψ
  have hψu3 : (ψ u) ^ 3 = 1 := by
    calc (ψ u) ^ 3 = ψ (u ^ 3) := (map_pow ψ u 3).symm
      _ = ψ 1 := by rw [hu3]
      _ = 1 := map_one ψ
  have htu3 : (t * u) ^ 3 = t := by
    rw [Commute.mul_pow htu 3]
    rw [show t ^ 3 = t by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, ht2, one_mul],
      hu3, mul_one]
  have htu6 : (t * u) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, htu3, ht2]
  have hcomm_ψ : Commute (ψ t) (ψ u) := by
    show ψ t * ψ u = ψ u * ψ t
    rw [(map_mul ψ t u).symm, ← map_mul, htu]
  have hσ6 : (ψ t * ψ u) ^ 6 = 1 := by
    calc (ψ t * ψ u) ^ 6 = (ψ (t * u)) ^ 6 := by rw [map_mul]
      _ = ψ ((t * u) ^ 6) := (map_pow ψ (t * u) 6).symm
      _ = ψ 1 := by rw [htu6]
      _ = 1 := map_one ψ
  rcases s16h_perm_fin3_pow_six (ψ t * ψ u) hσ6 with h3 | h2
  · have h3' : (ψ t) ^ 3 = 1 := by
      have h := h3
      rw [hcomm_ψ.mul_pow 3] at h
      rw [hψu3, mul_one] at h
      exact h
    have hψt : ψ t = 1 := by
      calc ψ t = (ψ t) ^ 2 * ψ t := by rw [hψt2, one_mul]
        _ = (ψ t) ^ 3 := (pow_succ (ψ t) 2).symm
        _ = 1 := h3'
    exact ht1 (hψ (by rw [hψt, map_one]))
  · have h2' : (ψ u) ^ 2 = 1 := by
      have h := h2
      rw [hcomm_ψ.mul_pow 2] at h
      rw [hψt2, one_mul] at h
      exact h
    exact hu2ne (hψ (by rw [map_pow, h2', map_one]))

private theorem s16h_le_stabSub_commSub_fixV {L : Subgroup (MulAut W)} :
    normalizer (L : Set (MulAut W)) ≤ stabSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hx
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxnorm u hu.1, ?_⟩
    intro l hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.mp hu.2 (x⁻¹ * l * x) (by simpa using hxinvnorm l hl)]
  have hxinvZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x⁻¹ u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxinvnorm u hu.1, ?_⟩
    intro l hl
    calc l (x⁻¹ u) = x⁻¹ ((x * l * x⁻¹) u) := by simp [MulAut.mul_apply]
      _ = x⁻¹ u := by rw [mem_fixV.mp hu.2 (x * l * x⁻¹) (hxnorm l hl)]
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by have := hxinvZ (x u) hu; simpa using this, hxZ u⟩

private noncomputable def s16h_mulAutPermNeOneHom (G : Type*) [Group G] :
    MulAut G →* Equiv.Perm {x : G // x ≠ 1} where
  toFun e := Equiv.Perm.subtypePerm (e : Equiv.Perm G) fun x => e.map_ne_one_iff
  map_one' := by ext x; rfl
  map_mul' e f := by ext x; rfl

@[simp] private theorem s16h_mulAutPermNeOneHom_apply (G : Type*) [Group G] (e : MulAut G)
    (x : {x : G // x ≠ 1}) :
    ((s16h_mulAutPermNeOneHom G e) x : G) = e x := rfl

private theorem s16h_mulAutPermNeOneHom_injective (G : Type*) [Group G] :
    Function.Injective (s16h_mulAutPermNeOneHom G) := by
  intro e f h
  ext x
  by_cases hx : x = 1
  · subst hx; simp
  · have h2 := congrArg
      (fun σ : Equiv.Perm {x : G // x ≠ 1} => ((σ ⟨x, hx⟩ : {x : G // x ≠ 1}) : G)) h
    simpa using h2

private theorem s16h_mulAut_embeds_perm_fin3 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : ∃ ψ : MulAut G →* Equiv.Perm (Fin 3), Function.Injective ψ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hcardNe : Fintype.card {x : G // x ≠ 1} ≤ 3 := by
    rw [Fintype.card_subtype_compl (fun x : G => x = 1), Fintype.card_subtype_eq (1 : G)]
    have hfc : Fintype.card G = Nat.card G := Fintype.card_eq_nat_card
    omega
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (α := {x : G // x ≠ 1}) (β := Fin 3)
    (by simpa using hcardNe)
  refine ⟨(Equiv.Perm.viaEmbeddingHom ι).comp (s16h_mulAutPermNeOneHom G), ?_⟩
  exact (Equiv.Perm.viaEmbeddingHom_injective ι).comp (s16h_mulAutPermNeOneHom_injective G)

theorem s16h_H5_zcond_SL4_induced_embed [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hZ : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∃ ψ : ↥(autSub (A ⊓ normalizer (L : Set (MulAut W)))
        (commSub ⊤ L ⊓ fixV L)) →* Equiv.Perm (Fin 3), Function.Injective ψ := by
  classical
  have hemb : ∃ ψ : MulAut ↥(commSub ⊤ L ⊓ fixV L) →* Equiv.Perm (Fin 3),
      Function.Injective ψ := by
    refine s16h_mulAut_embeds_perm_fin3 (G := ↥(commSub ⊤ L ⊓ fixV L)) ?_
    rw [CFSG.Quasithin.card_eq_two_pow hc.elem (commSub ⊤ L ⊓ fixV L)]
    calc 2 ^ rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) hZ
      _ = 4 := by norm_num
  obtain ⟨ψ, hψ⟩ := hemb
  refine ⟨ψ.comp (Subgroup.subtype (autSub (A ⊓ normalizer (L : Set (MulAut W)))
        (commSub ⊤ L ⊓ fixV L))), ?_⟩
  intro a b hab
  exact Subgroup.subtype_injective _ (hψ hab)

theorem s16h_H5_zcond_SL4 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hZ : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    s16h_H5ZCond A L := by
  classical
  refine Or.inr ?_
  intro T hTN hTnorm hT2 hf
  set N : Subgroup (MulAut W) := A ⊓ normalizer (L : Set (MulAut W)) with hN
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hTN' : T ≤ N := hTN
  have hNZ : N ≤ stabSub Z := by
    rw [hN, hZdef]
    exact inf_le_right.trans s16h_le_stabSub_commSub_fixV
  let g : ↥N →* MulAut Z := (resHom Z).comp (Subgroup.inclusion hNZ)
  have hgrange : g.range = autSub N Z := by
    change ((resHom Z).comp (Subgroup.inclusion hNZ)).range = autSub N Z
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let hcod : ∀ n : ↥N, g n ∈ autSub N Z :=
    fun n => hgrange ▸ (show g n ∈ g.range from ⟨n, rfl⟩)
  let ρ : ↥N →* ↥(autSub N Z) := g.codRestrict (autSub N Z) hcod
  have hρker : ρ.ker = g.ker := MonoidHom.ker_codRestrict g (autSub N Z) hcod
  have hker_g : ∀ n : ↥N, g n = 1 ↔ (n : MulAut W) ∈ centSub Z := by
    intro n
    constructor
    · intro hn
      have hmem : (Subgroup.inclusion hNZ n : stabSub Z) ∈ (resHom Z).ker := by
        rw [MonoidHom.mem_ker]
        change g n = 1
        exact hn
      rw [ker_resHom Z, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · intro hn
      have hmem : (Subgroup.inclusion hNZ n : stabSub Z) ∈ (resHom Z).ker := by
        rw [ker_resHom Z, Subgroup.mem_subgroupOf]
        exact hn
      rw [MonoidHom.mem_ker] at hmem
      change g n = 1
      exact hmem
  have hker_ρ : ∀ n : ↥N, ρ n = 1 ↔ (n : MulAut W) ∈ centSub Z := by
    intro n
    have hρn : ρ n = 1 ↔ g n = 1 :=
      ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    rw [hρn, hker_g n]
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : MulAut Z) ∈ g.range := by
      rw [hgrange]
      exact y.2
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, Subtype.ext hn⟩
  obtain ⟨ψ, hψ⟩ := s16h_H5_zcond_SL4_induced_embed hc hZ
  set T' : Subgroup ↥(autSub N Z) := (T.subgroupOf N).map ρ with hT'def
  haveI hT'norm : T'.Normal := by
    haveI hTNnorm : (T.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff hTN').mpr (fun h k hh hk => hTnorm k hk h hh)
    rw [hT'def]
    exact hTNnorm.map ρ hρsurj
  have hT'2 : ∀ y ∈ T', ∃ m : ℕ, y ^ 2 ^ m = 1 := by
    intro y hy
    rw [hT'def] at hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnT : (n : MulAut W) ∈ T := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨m, hm⟩ := hT2 (n : MulAut W) hnT
    refine ⟨m, ?_⟩
    calc (ρ n) ^ 2 ^ m = ρ (n ^ 2 ^ m) := (map_pow ρ n (2 ^ m)).symm
      _ = 1 := by rw [hker_ρ]; simpa using hm
  obtain ⟨f, hfN, q, hq, hq2, hfZ, hfq⟩ := hf
  have hfρ : ρ ⟨f, hfN⟩ ≠ 1 := fun h1 => hfZ ((hker_ρ ⟨f, hfN⟩).mp h1)
  have hfqρ : (ρ ⟨f, hfN⟩) ^ q = 1 := by
    rw [← map_pow, hker_ρ]
    simpa using hfq
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : orderOf (ρ ⟨f, hfN⟩) = q := orderOf_eq_prime hfqρ hfρ
  have hq_dvd : q ∣ 6 := by
    have hψq : (ψ (ρ ⟨f, hfN⟩)) ^ q = 1 := by rw [← map_pow, hfqρ, map_one]
    have hψne : ψ (ρ ⟨f, hfN⟩) ≠ 1 := fun h1 => hfρ (hψ (by rw [h1, map_one]))
    have hordψ : orderOf (ψ (ρ ⟨f, hfN⟩)) = q := orderOf_eq_prime hψq hψne
    have hdvd : orderOf (ψ (ρ ⟨f, hfN⟩)) ∣ Nat.card (Equiv.Perm (Fin 3)) :=
      orderOf_dvd_natCard _
    have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rwa [hordψ, hcard6] at hdvd
  have hq3 : q = 3 := by
    have h' : q ∣ 2 * 3 := by
      rw [show (2 * 3 : ℕ) = 6 by norm_num]
      exact hq_dvd
    rcases hq.dvd_mul.mp h' with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2) hq2
    · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
  have hodd : ∃ u : ↥(autSub N Z), orderOf u = 3 :=
    ⟨ρ ⟨f, hfN⟩, by rw [hord, hq3]⟩
  have hT'bot : T' = ⊥ :=
    s16h_normal_two_subgroup_perm_fin3_eq_bot ψ hψ hodd hT'2
  intro x hx
  have hxN : x ∈ N := hTN' hx
  have hρx : ρ ⟨x, hxN⟩ = 1 := by
    have hmem : ρ ⟨x, hxN⟩ ∈ T' := by
      rw [hT'def]
      exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hT'bot, Subgroup.mem_bot] at hmem
    exact hmem
  exact (hker_ρ ⟨x, hxN⟩).mp hρx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
