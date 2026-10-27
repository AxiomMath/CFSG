module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzBranch
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzHe
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G]

@[expose] def kzConjK_kz2 (K : Subgroup G) (t : G) (ht : t ∈ Subgroup.normalizer (K : Set G)) : ↥K →* ↥K where
  toFun k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht k).mp k.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem kzConjK_val_kz2 {K : Subgroup G} {t : G} {ht : t ∈ Subgroup.normalizer (K : Set G)} (k : ↥K) :
    ((kzConjK_kz2 K t ht k : ↥K) : G) = t * k * t⁻¹ := rfl

@[expose] noncomputable def kzQmap_kz2 (K : Subgroup G) (t : G) (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    (↥K ⧸ CFSG.pCore 2 ↥K) →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
  QuotientGroup.map (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) (kzConjK_kz2 K t ht) (by
    intro n hn
    rw [Subgroup.mem_comap]
    rw [mem_pCore_iff_kz2] at hn ⊢
    rw [kzConjK_val_kz2]
    have hN : t ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 K ht
    exact (Subgroup.mem_normalizer_iff.mp hN (n : G)).mp hn)

theorem kzQmap_mk_kz2 {K : Subgroup G} {t : G} {ht : t ∈ Subgroup.normalizer (K : Set G)} (x : ↥K) :
    kzQmap_kz2 K t ht (QuotientGroup.mk x) = QuotientGroup.mk (kzConjK_kz2 K t ht x) := rfl

theorem kzQmap_inv_comp_kz2 {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (ht' : t⁻¹ ∈ Subgroup.normalizer (K : Set G)) (q : ↥K ⧸ CFSG.pCore 2 ↥K) :
    kzQmap_kz2 K t⁻¹ ht' (kzQmap_kz2 K t ht q) = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [kzQmap_mk_kz2, kzQmap_mk_kz2]
    congr 1
    apply Subtype.ext
    simp [kzConjK_val_kz2, mul_assoc]

theorem kzQmap_comp_inv_kz2 {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (ht' : t⁻¹ ∈ Subgroup.normalizer (K : Set G)) (q : ↥K ⧸ CFSG.pCore 2 ↥K) :
    kzQmap_kz2 K t ht (kzQmap_kz2 K t⁻¹ ht' q) = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [kzQmap_mk_kz2, kzQmap_mk_kz2]
    congr 1
    apply Subtype.ext
    simp [kzConjK_val_kz2, mul_assoc]

theorem kzQmap_bijective_kz2 {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    Function.Bijective (kzQmap_kz2 K t ht) := by
  have ht' : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ ht
  exact ⟨fun a b hab => by
      rw [← kzQmap_inv_comp_kz2 ht ht' a, ← kzQmap_inv_comp_kz2 ht ht' b, hab],
    fun q => ⟨kzQmap_kz2 K t⁻¹ ht' q, kzQmap_comp_inv_kz2 ht ht' q⟩⟩

theorem kzQmap_mul_kz2 {K : Subgroup G} {t s : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hs : s ∈ Subgroup.normalizer (K : Set G)) (hts : t * s ∈ Subgroup.normalizer (K : Set G))
    (q : ↥K ⧸ CFSG.pCore 2 ↥K) :
    kzQmap_kz2 K (t * s) hts q = kzQmap_kz2 K t ht (kzQmap_kz2 K s hs q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [kzQmap_mk_kz2, kzQmap_mk_kz2, kzQmap_mk_kz2]
    congr 1
    apply Subtype.ext
    simp [kzConjK_val_kz2, mul_assoc]

theorem center_bot_of_he_kz2 {Q : Type} [Group Q] [Finite Q]
    (hQe : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    Subgroup.center Q = ⊥ := by
  obtain ⟨e⟩ := hQe
  haveI : IsSimpleGroup Q := by
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
      CFSG.Sporadic.He.isSimpleGroup_He
    exact MulEquiv.isSimpleGroup e
  have hcard : Nat.card Q = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  exact res822_center_bot_of_simple (res822_nonabelian_of_not_prime (by rw [hcard]; norm_num))


@[expose] def HeAutInner_kz2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
    ∀ (S B : Subgroup Q), IsPGroup 2 S → Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set Q) →
      Nat.card B = 69120 → ⁅B, B⁆ = B → ∀ f : Q →* Q, Function.Bijective f → B.map f = B →
        ∃ k : Q, ∀ x : Q, f x = k * x * k⁻¹

theorem false_of_heCore_gen_kz2 (hHe : HeSubO2_kz) {Q : Type} [Group Q] [Finite Q]
    (hQe : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    (hQ : Nat.card Q = 4030387200)
    {X S O : Subgroup Q} (hS2 : IsPGroup 2 S) (hSc : Nat.card S = 2 ^ 10)
    (hSX : S ≤ Subgroup.normalizer (X : Set Q)) (hOp : IsPGroup 2 O) (hOX : O ≤ X)
    (hXO : X ≤ Subgroup.normalizer (O : Set Q)) (hSO : S ≤ Subgroup.normalizer (O : Set Q))
    (hrel : O.relIndex X = 9)
    (hirr : ∀ W : Subgroup Q, O ≤ W → W ≤ X → S ≤ Subgroup.normalizer (W : Set Q) → W = O ∨ W = X) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hOp.exists_card_eq
  have hXcard : Nat.card X = 9 * Nat.card O := by
    have h := Subgroup.relIndex_mul_card (H := O) (K := X)
    rw [inf_eq_left.mpr hOX, hrel] at h
    exact h.symm
  have hOS : O ≤ S := by
    have h2 : IsPGroup 2 ((O ⊔ S : Subgroup Q)) := IsPGroup.to_sup_of_normal_left' hOp hS2 hSO
    have hle : Nat.card ((O ⊔ S : Subgroup Q)) ≤ 2 ^ 10 :=
      Nat.le_of_dvd (by norm_num) (card_dvd_two_pow_ten_of_isPGroup_kz hQ _ h2)
    have hEq : S = O ⊔ S :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hSc]; exact hle)
    calc O ≤ O ⊔ S := le_sup_left
      _ = S := hEq.symm
  have hSXO : (S ⊓ X : Subgroup Q) = O := by
    apply le_antisymm _ (le_inf hOS hOX)
    have hR2 : IsPGroup 2 ((O ⊔ (S ⊓ X) : Subgroup Q)) :=
      IsPGroup.to_sup_of_normal_left' hOp (hS2.to_le inf_le_left) (inf_le_right.trans hXO)
    have hsub : O ⊔ (S ⊓ X) ≤ X := sup_le hOX inf_le_right
    have hdvd : Nat.card ((O ⊔ (S ⊓ X) : Subgroup Q)) ∣ 9 * Nat.card O := by
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le hsub
    have hR2card : Nat.card ((O ⊔ (S ⊓ X) : Subgroup Q)) ≤ Nat.card O := by
      obtain ⟨b, hb⟩ := hR2.exists_card_eq
      rw [hb, ha] at hdvd ⊢
      exact card_le_of_two_pow_dvd_nine_mul_kz (hb ▸ hdvd)
    have hOeq : O = O ⊔ (S ⊓ X) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left hR2card
    calc S ⊓ X ≤ O ⊔ (S ⊓ X) := le_sup_right
      _ = O := hOeq.symm
  set U : Subgroup Q := (X ⊔ S : Subgroup Q) with hUdef
  have hXU : X ≤ U := le_sup_left
  have hSU : S ≤ U := le_sup_right
  have hUN : U ≤ Subgroup.normalizer (X : Set Q) := sup_le (Subgroup.le_normalizer) hSX
  have hUO : U ≤ Subgroup.normalizer (O : Set Q) := sup_le hXO hSO
  haveI hXUn : (X.subgroupOf U).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hUN g.2) x).mp hx⟩
  have hidx : (X.subgroupOf U).index = (O.subgroupOf S).index := by
    let f : ↥S →* ↥U ⧸ X.subgroupOf U :=
      (QuotientGroup.mk' (X.subgroupOf U)).comp (Subgroup.inclusion hSU)
    have hsurj : Function.Surjective f := by
      intro q
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, hy, z, hz, hyz⟩ := (mem_sup_of_le_normalizer_he_kz hSX).mp u.2
      refine ⟨⟨z, hz⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hSU ⟨z, hz⟩) : ↥U ⧸ X.subgroupOf U) =
        QuotientGroup.mk u
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 : z⁻¹ * (u : Q) = z⁻¹ * y * z := by rw [← hyz]; group
      show z⁻¹ * (u : Q) ∈ X
      rw [h1]
      have h2 := (Subgroup.mem_normalizer_iff.mp (hSX (S.inv_mem hz)) y).mp hy
      simpa using h2
    have hker : f.ker = O.subgroupOf S := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have h1 : f s = 1 ↔ (s : Q) ∈ X := by
        rw [show f s = QuotientGroup.mk (Subgroup.inclusion hSU s) from rfl, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        rfl
      rw [h1]
      constructor
      · intro hx
        have hmem : (s : Q) ∈ (S ⊓ X : Subgroup Q) := ⟨s.2, hx⟩
        rw [hSXO] at hmem
        exact hmem
      · intro hx
        have hmem : (s : Q) ∈ (S ⊓ X : Subgroup Q) := hSXO ▸ hx
        exact hmem.2
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Subgroup.index_eq_card]
  have hUcard : Nat.card U = 2 ^ 10 * 3 ^ 2 := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf U)
    have h2 : Nat.card ↥(X.subgroupOf U) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv
    have h3 := Subgroup.card_mul_index (O.subgroupOf S)
    have h4 : Nat.card ↥(O.subgroupOf S) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOS).toEquiv
    rw [h2, hidx] at h1
    rw [h4] at h3
    have key : Nat.card U = 9 * (Nat.card O * (O.subgroupOf S).index) := by
      rw [← h1, hXcard]
      ring
    rw [key, h3, hSc]
    norm_num
  obtain ⟨j, hj⟩ : ∃ j, (X.subgroupOf U).index = 2 ^ j := by
    have hd : (O.subgroupOf S).index ∣ 2 ^ 10 := hSc ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨j, by rw [hidx, hj]⟩
  have hoddU : ∀ x ∈ U, Odd (orderOf x) → x ∈ X := by
    intro x hxU hodd
    set xU : ↥U := ⟨x, hxU⟩ with hxUdef
    have h1 : orderOf (QuotientGroup.mk xU : ↥U ⧸ X.subgroupOf U) ∣ orderOf xU :=
      orderOf_map_dvd (QuotientGroup.mk' (X.subgroupOf U)) xU
    have h2 : orderOf (QuotientGroup.mk xU : ↥U ⧸ X.subgroupOf U) ∣ 2 ^ j := by
      rw [← hj, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hxo : orderOf xU = orderOf x := (Subgroup.orderOf_coe xU).symm
    have hodd' : Odd (orderOf (QuotientGroup.mk xU : ↥U ⧸ X.subgroupOf U)) :=
      Odd.of_dvd_nat (hxo ▸ hodd) h1
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk xU : ↥U ⧸ X.subgroupOf U)) (2 ^ j) :=
      Nat.Coprime.pow_right j
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd'.not_two_dvd_nat))
    have h1' := Nat.Coprime.eq_one_of_dvd hcop h2
    have hmk : (QuotientGroup.mk xU : ↥U ⧸ X.subgroupOf U) = 1 := orderOf_eq_one_iff.mp h1'
    exact (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq_one_iff _ |>.mp hmk))
  have hoT : oTwoUpper U ≤ X := by
    unfold oTwoUpper
    rw [Subgroup.closure_le]
    rintro x ⟨hxU, hodd⟩
    exact hoddU x hxU hodd
  obtain ⟨Y, hYU, hYn, hYcard, hYO⟩ := hHe Q hQe U hUcard
  have hYX : Y ≤ X := hYO.trans hoT
  have hYUnorm : ∀ g ∈ U, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    have h := hYn.conj_mem ⟨y, hYU hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using h
  have hYN : U ≤ Subgroup.normalizer (Y : Set Q) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hYUnorm g hg y hy
    · intro hy
      have := hYUnorm g⁻¹ (U.inv_mem hg) _ hy
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  have hOUnorm : ∀ g ∈ U, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (hUO hg) o).mp ho
  have hON : O ≤ Subgroup.normalizer (Y : Set Q) := (hOX.trans hXU).trans hYN
  set W : Subgroup Q := (Y ⊔ O : Subgroup Q) with hWdef
  have hUW : U ≤ Subgroup.normalizer (W : Set Q) := by
    have key : ∀ g ∈ U, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨y, hy, o, ho, rfl⟩ := (mem_sup_of_le_normalizer_he_kz hON).mp hw
      have e : g * (y * o) * g⁻¹ = (g * y * g⁻¹) * (g * o * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (hYUnorm g hg y hy) (hOUnorm g hg o ho)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact key g hg w
    · intro hw
      have := key g⁻¹ (U.inv_mem hg) (g * w * g⁻¹) hw
      rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this
  have hSW : S ≤ Subgroup.normalizer (W : Set Q) := hSU.trans hUW
  have hWX : W ≤ X := sup_le hYX hOX
  have hOW : O ≤ W := le_sup_right
  haveI hOXn : (O.subgroupOf X).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXO g.2) x).mp hx⟩
  let g : ↥Y →* ↥X ⧸ O.subgroupOf X :=
    (QuotientGroup.mk' (O.subgroupOf X)).comp (Subgroup.inclusion hYX)
  have hquot : Nat.card (↥X ⧸ O.subgroupOf X) = 9 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  have hrange9 : Nat.card g.range ∣ 9 := by
    have h := Subgroup.card_subgroup_dvd_card g.range
    rw [hquot] at h
    exact h
  have hgker : Nat.card g.ker * Nat.card g.range = 2 ^ 6 * 3 := by
    rw [← hYcard]
    exact Subgroup.card_ker_mul_card_range g
  obtain ⟨c, hc⟩ : ∃ c, Nat.card g.ker = 2 ^ c := by
    have hmapO : g.ker.map Y.subtype ≤ O := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : g y = 1 := hy
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    have hP2 : IsPGroup 2 ↥(g.ker.map Y.subtype) := hOp.to_le hmapO
    obtain ⟨c, hc⟩ := hP2.exists_card_eq
    refine ⟨c, ?_⟩
    rw [Subgroup.card_map_of_injective Subtype.val_injective] at hc
    exact hc
  have hr3 : Nat.card g.range = 3 := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card g.range = r := ⟨_, rfl⟩
    rw [hr] at hrange9 hgker ⊢
    rw [hc] at hgker
    have hmem : r ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hrange9, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exfalso
      have h3 : (3 : ℕ) ∣ 2 ^ c := by
        have : (3 : ℕ) ∣ 2 ^ c * 1 := by
          rw [hgker]
          exact Dvd.intro_left _ rfl
        simpa using this
      have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h2
    · rfl
    · exfalso
      generalize 2 ^ c = t at hgker
      omega
  rcases hirr W hOW hWX hSW with hWO | hWXeq
  ·
    have hYO' : Y ≤ O := le_sup_left.trans hWO.le
    obtain ⟨b, hb⟩ := (hOp.to_le hYO').exists_card_eq
    rw [hYcard] at hb
    have h3 : (3 : ℕ) ∣ 2 ^ b := by rw [← hb]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  ·
    have hsurjg : Function.Surjective g := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hxW : (x : Q) ∈ W := by rw [hWXeq]; exact x.2
      obtain ⟨y, hy, o, ho, hyo⟩ := (mem_sup_of_le_normalizer_he_kz hON).mp hxW
      refine ⟨⟨y, hy⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hYX ⟨y, hy⟩) : ↥X ⧸ O.subgroupOf X) =
        QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (y : Q)⁻¹ * (x : Q) ∈ O
      rw [← hyo]
      simpa using ho
    have hrt : g.range = ⊤ := MonoidHom.range_eq_top.mpr hsurjg
    have h9 : Nat.card g.range = 9 := by rw [hrt, Subgroup.card_top, hquot]
    omega


theorem kzQmap_eq_conj_kz2 {K : Subgroup G} (t : ↥K) (ht : (t : G) ∈ Subgroup.normalizer (K : Set G))
    (q : ↥K ⧸ CFSG.pCore 2 ↥K) :
    kzQmap_kz2 K (t : G) ht q = QuotientGroup.mk t * q * (QuotientGroup.mk t)⁻¹ := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [kzQmap_mk_kz2, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1

theorem card_range_mul_kz2 [Finite G] (K : Subgroup G) {S : Subgroup ↥K} (hNS : CFSG.pCore 2 ↥K ≤ S) :
    Nat.card ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp S.subtype).range * Nat.card (CFSG.pCore 2 ↥K) =
      Nat.card S := by
  classical
  let g := (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp S.subtype
  have hker : g.ker = (CFSG.pCore 2 ↥K).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hc : Nat.card g.ker = Nat.card (CFSG.pCore 2 ↥K) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  have h := Subgroup.card_ker_mul_card_range g
  rw [hc] at h
  rw [← h, mul_comm]

theorem card_map_mul_kz2 [Finite G] (K : Subgroup G) {S : Subgroup ↥K} (hNS : CFSG.pCore 2 ↥K ≤ S) :
    Nat.card (S.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) * Nat.card (CFSG.pCore 2 ↥K) = Nat.card S := by
  have h := card_range_mul_kz2 K hNS
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h

theorem pCore_le_inf_kz2 [Finite G] {Gz T K : Subgroup G} (hT : IsSylowTwoOf T Gz) (hKG : K ≤ Gz)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.pCore 2 ↥K ≤ (T ⊓ K).subgroupOf K := by
  intro n hn
  rw [Subgroup.mem_subgroupOf]
  exact ⟨pCoreOf_le_of_sylow_kz2 hT hKG hTK ((mem_pCore_iff_kz2 n).mp hn), n.2⟩

theorem two_part_eq_kz2 (c m r a b e : ℕ) (hc : ¬ 2 ∣ c) (hm : ¬ 2 ∣ m) (h1 : c * 2 ^ a = 2 ^ e * m * 2 ^ b)
    (h2 : r * 2 ^ b = 2 ^ a) : r = 2 ^ e := by
  have hd1 : 2 ^ (b + e) ∣ c * 2 ^ a := ⟨m, by rw [h1]; ring⟩
  have hcop1 : Nat.Coprime (2 ^ (b + e)) c :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hc)
  have hd2 : 2 ^ (b + e) ∣ 2 ^ a := Nat.Coprime.dvd_of_dvd_mul_left hcop1 hd1
  have hba : b + e ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2
  have hd3 : 2 ^ a ∣ 2 ^ (b + e) * m := ⟨c, by rw [pow_add, mul_comm (2 ^ a) c, h1]; ring⟩
  have hcop2 : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have hd4 : 2 ^ a ∣ 2 ^ (b + e) := Nat.Coprime.dvd_of_dvd_mul_right hcop2 hd3
  have hab : a ≤ b + e := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd4
  have hae : a = b + e := le_antisymm hab hba
  rw [hae] at h2
  have hpos : 0 < 2 ^ b := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h2, pow_add]
  ring

theorem eq_of_conj_eq_kz2 {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) {k k' : Q}
    (h : ∀ x : Q, k * x * k⁻¹ = k' * x * k'⁻¹) : k = k' := by
  have hc : k'⁻¹ * k ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := h g
    calc g * (k'⁻¹ * k) = k'⁻¹ * (k * g * k⁻¹) * k' * (k'⁻¹ * k) := by
          rw [hg]; group
      _ = k'⁻¹ * k * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  have : k = k' := by
    have hk : k = k' * (k'⁻¹ * k) := by group
    rw [hk, hc, mul_one]
  exact this



end CFSG.Quasithin.H13
