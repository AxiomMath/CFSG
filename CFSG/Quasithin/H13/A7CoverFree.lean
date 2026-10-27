module

public import CFSG.Quasithin.H13.A7KLocal
public import CFSG.Quasithin.H13.A7SharedCubicSylow
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.H13.A7EscapeInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

theorem card_comap_of_surjective' {X Y : Type*} [Group X] [Group Y] [Finite X] {f : X →* Y}
    (hf : Function.Surjective f) (H : Subgroup Y) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  have : Finite Y := Finite.of_surjective f hf
  have h1 := (H.comap f).card_mul_index
  have h2 := H.card_mul_index
  have h3 : Nat.card X = Nat.card Y * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  rw [index_comap_of_surjective H hf] at h1
  have hpos : 0 < H.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
  have h4 : Nat.card (H.comap f) * H.index = Nat.card H * Nat.card f.ker * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem nat_card_sylow_three_of_card {X : Type*} [Group X] [Finite X] {a : ℕ}
    (hX : Nat.card X = 27 * 2 ^ a) (P : Sylow 3 X) : Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hX, Nat.factorization_mul (by norm_num) (by positivity),
    Finsupp.add_apply, show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow
      Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)), add_zero]

theorem card_filter_stab_vecFour : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ permAct7 σ vecFour = vecFour).card = 72 := by
  decide +kernel

@[expose] def stabVecFour : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {σ | permAct7 (σ : Perm (Fin 7)) vecFour = vecFour}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul] at ha hb ⊢
    rw [permAct7_mul, hb, ha]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_one, permAct7_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
    conv_lhs => rw [← ha]
    exact permAct7_inv_apply _ _

theorem nat_card_stabVecFour : Nat.card stabVecFour = 72 := by
  rw [← card_filter_stab_vecFour, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun x => ⟨(x : alternatingGroup (Fin 7)), ?_⟩,
    fun x => ⟨⟨(x : Perm (Fin 7)), mem_alternatingGroup.2 (x.2).1⟩, (x.2).2⟩,
    fun x => rfl, fun x => rfl⟩
  exact ⟨mem_alternatingGroup.1 (x : alternatingGroup (Fin 7)).2, x.2⟩

theorem eq_one_of_isPGroup_two_three {X : Type*} [Group X] {A B : Subgroup X} (hA : IsPGroup 2 A)
    (hB : IsPGroup 3 B) {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨m, hm⟩ := hA ⟨x, hxA⟩
  obtain ⟨n, hn⟩ := hB ⟨x, hxB⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hn' : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 := orderOf_dvd_of_pow_eq_one hm'
  have h2 := orderOf_dvd_of_pow_eq_one hn'
  have hcop : Nat.Coprime (2 ^ m) (3 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
  have h3 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem commute_of_mem_closure_of_pairwise {X : Type*} [Group X] {S : Set X}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x y : X} (hx : x ∈ closure S) (hy : y ∈ closure S) :
    x * y = y * x := by
  have h1 : closure S ≤ centralizer S := by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact hS b hb a ha
  have h2 : closure S ≤ centralizer (closure S : Set X) := by
    rw [centralizer_closure]
    exact h1
  exact (mem_centralizer_iff.1 (h2 hy) x hx)

section Cover

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_inf_centralizer {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (h : A7NatConfig T L V ψ) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {e : V} (he : vec ψ e = vecFour) {K : Subgroup G}
    (hCK : centralizer ({(e : G)} : Set G) ≤ normalizer (K : Set G))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    {k : G} (hkK : k ∈ K) (hkL : k ∈ L) (hke : k ∈ centralizer ({(e : G)} : Set G))
    (hk3 : k ^ 3 = 1) (hkO : k ∉ pCoreOf 2 K) :
    IsPGroup 2 (L ⊓ centralizer (V : Set G) : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLact' : ∀ a ∈ L, ∃ σ, IsCoordAct ψ a σ := fun a ha => by
    obtain ⟨σ, -, hσ⟩ := h.Lact a ha
    exact ⟨σ, hσ⟩
  set lamL : L →* Perm (Fin 7) := coordRep ψ h.L_le hLact' with hlamL
  have hlam_spec : ∀ l : L, IsCoordAct ψ l (lamL l) := coordRep_spec ψ h.L_le hLact'
  have hlam_eq : ∀ (l : L) {σ : Perm (Fin 7)}, IsCoordAct ψ l σ → lamL l = σ := fun l σ hσ =>
    IsCoordAct.unique ψ (h.L_le l.2) (hlam_spec l) hσ
  have hlam_mem : ∀ l : L, lamL l ∈ alternatingGroup (Fin 7) := by
    intro l
    obtain ⟨σ, hσA, hσ⟩ := h.Lact l l.2
    rw [hlam_eq l hσ]
    exact hσA
  set lamA : L →* alternatingGroup (Fin 7) := lamL.codRestrict _ hlam_mem with hlamA
  have hlamA_coe : ∀ l : L, ((lamA l : alternatingGroup (Fin 7)) : Perm (Fin 7)) = lamL l :=
    fun _ => rfl
  have hlamA_surj : Function.Surjective lamA := by
    rintro ⟨σ, hσ⟩
    obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
    exact ⟨⟨l, hl⟩, Subtype.ext (hlam_eq ⟨l, hl⟩ hact)⟩
  have hlamA_ker : ∀ l : L, lamA l = 1 ↔ (l : G) ∈ centralizer (V : Set G) := by
    intro l
    rw [← coordRep_eq_one_iff ψ h.L_le hLact' l]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hRV : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_coord h.L_le ψ h.Lact h.Lonto
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := by
    rw [pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := L)).map L.subtype
  have hOker : CFSG.pCore 2 L ≤ lamA.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hlamA_ker]
    apply hRV
    rw [pCoreOf_eq_map_cfsgPCore]
    exact ⟨x, hx, rfl⟩
  set π : ↥L ⧸ CFSG.pCore 2 ↥L →* alternatingGroup (Fin 7) :=
    QuotientGroup.lift (CFSG.pCore 2 L) lamA hOker with hπdef
  have hπ_mk : ∀ l : L, π (QuotientGroup.mk l) = lamA l := fun _ => rfl
  have hπ_surj : Function.Surjective π := by
    intro σ
    obtain ⟨l, hl⟩ := hlamA_surj σ
    exact ⟨QuotientGroup.mk l, hl⟩
  have hcomm := commutator_mem_pCoreOf_of_mem_centralizer h.L_le ψ h.Lonto hLq hRV
  have hπC : π.ker ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hπ_mk, hlamA_ker] at hq
    rw [mem_center_iff]
    intro q'
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q'
    have h1 := hcomm l (mem_inf.2 ⟨l.2, hq⟩) l' l'.2
    rw [pCoreOf_eq_map_cfsgPCore] at h1
    obtain ⟨c, hc, hce⟩ := h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h2 : (l' * l)⁻¹ * (l * l') = (l' * l)⁻¹ * c * (l' * l)⁻¹⁻¹ := by
      apply Subtype.ext
      have hce' : (c : G) = (l : G) * l' * (l : G)⁻¹ * (l' : G)⁻¹ := by
        rw [← commutatorElement_def]
        exact hce
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hce']
      group
    rw [h2]
    exact (CFSG.pCore_normal (p := 2) (G := L)).conj_mem c hc _
  have hodd : Odd (Nat.card π.ker) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card π.ker := by omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    set y : ↥L ⧸ CFSG.pCore 2 ↥L := (x : ↥L ⧸ CFSG.pCore 2 ↥L) with hy
    have hyc : y ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := hπC x.2
    have hyo : orderOf y = 2 := by rw [hy, Subgroup.orderOf_coe, hx]
    have hZc : zpowers y ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := (zpowers_le).2 hyc
    have hZn : (zpowers y).Normal := by
      constructor
      intro a ha g
      rw [mem_center_iff.1 (hZc ha) g, mul_inv_cancel_right]
      exact ha
    have hZ2 : IsPGroup 2 (zpowers y) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hyo, pow_one]
    have hle : zpowers y ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) := le_sSup ⟨hZn, hZ2⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    have : y = 1 := (Subgroup.mem_bot).1 (hle (mem_zpowers y))
    rw [this, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hLq.1
  by_contra hnot
  have hne : π.ker ≠ ⊥ := by
    intro hbot
    apply hnot
    refine hO2.to_le fun x hx => ?_
    obtain ⟨hxL, hxC⟩ := mem_inf.1 hx
    have h1 : (QuotientGroup.mk (⟨x, hxL⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπ_mk, hlamA_ker]
      exact hxC
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at h1
    rw [pCoreOf_eq_map_cfsgPCore]
    exact ⟨_, h1, rfl⟩
  obtain ⟨hcard3, hsyl⟩ :=
    A7_alternating_six_seven_odd_cover_cubic_Sylow (Or.inr rfl) π hπ_surj hπC hodd hne
  have hQcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 27 * 280 := by
    rw [card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).toEquiv,
      nat_card_alternating_seven, hcard3]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := L))
  have hkerA : Nat.card lamA.ker = 3 * 2 ^ a := by
    have hk : lamA.ker = π.ker.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
      ext l
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker, QuotientGroup.mk'_apply,
        hπ_mk]
    rw [hk, card_comap_of_surjective' (QuotientGroup.mk'_surjective _), QuotientGroup.ker_mk',
      hcard3, ha]
  set R : Subgroup G := L ⊓ centralizer ({(e : G)} : Set G) with hRdef
  have hmemR : ∀ l : L, (l : G) ∈ centralizer ({(e : G)} : Set G) ↔ lamA l ∈ stabVecFour := by
    intro l
    have hspec := hlam_spec l
    let y : V := ⟨(l : G) * e * (l : G)⁻¹, (mem_normalizer_iff.1 (h.L_le l.2) e).1 e.2⟩
    have hy := hspec e y rfl
    rw [he] at hy
    show _ ↔ permAct7 (lamL l) vecFour = vecFour
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hc
      have hye : y = e := Subtype.ext (show (l : G) * e * (l : G)⁻¹ = e by
        rw [hc, mul_inv_cancel_right])
      rw [← hy, hye, he]
    · intro hf
      rw [hf, ← he] at hy
      have h1 : (l : G) * e * (l : G)⁻¹ = e := congrArg Subtype.val (vec_injective ψ hy)
      calc (l : G) * e = (l : G) * e * (l : G)⁻¹ * l := by group
        _ = e * l := by rw [h1]
  have hRcard : Nat.card R = 27 * 2 ^ (a + 3) := by
    have h1 : R.subgroupOf L = stabVecFour.comap lamA := by
      ext l
      rw [mem_subgroupOf, Subgroup.mem_comap, hRdef, mem_inf, ← hmemR]
      exact ⟨fun hl => hl.2, fun hl => ⟨l.2, hl⟩⟩
    have h2 : Nat.card R = Nat.card (R.subgroupOf L) :=
      (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    rw [h2, h1, card_comap_of_surjective' hlamA_surj, nat_card_stabVecFour, hkerA]
    ring
  have hk1 : k ≠ 1 := fun h1 => hkO (h1 ▸ one_mem _)
  have hkR : k ∈ R := mem_inf.2 ⟨hkL, hke⟩
  have hk3R : IsPGroup 3 (zpowers (⟨k, hkR⟩ : R)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_eq_prime hk3 hk1, pow_one]
  obtain ⟨P, hP⟩ := hk3R.exists_le_sylow
  have hPcard : Nat.card P = 27 := nat_card_sylow_three_of_card hRcard P
  set PG : Subgroup G := (P : Subgroup R).map R.subtype with hPGdef
  have hPGcard : Nat.card PG = 27 := by
    rw [hPGdef, card_map_of_injective (subtype_injective _), hPcard]
  have hPGR : PG ≤ R := map_subtype_le _
  have hPG3 : IsPGroup 3 PG := P.isPGroup'.map _
  have hkPG : k ∈ PG := ⟨⟨k, hkR⟩, hP (mem_zpowers _), rfl⟩
  have hPGnc : ¬ ∀ x ∈ PG, ∀ y ∈ PG, x * y = y * x := by
    intro hc
    set Pbar : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (PG.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) with hPbardef
    have hinj : ∀ x ∈ PG.subgroupOf L, QuotientGroup.mk' (CFSG.pCore 2 L) x = 1 → x = 1 := by
      intro x hx h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      apply Subtype.ext
      refine eq_one_of_isPGroup_two_three hO2 hPG3 ?_ (mem_subgroupOf.1 hx)
      rw [pCoreOf_eq_map_cfsgPCore]
      exact ⟨x, h1, rfl⟩
    have hPbarcard : Nat.card Pbar = 27 := by
      rw [← hPGcard, ← Nat.card_congr (subgroupOfEquivOfLe (hPGR.trans inf_le_left)).toEquiv]
      refine (Nat.card_congr (Equiv.ofBijective (fun x : PG.subgroupOf L =>
        (⟨QuotientGroup.mk' _ x, mem_map_of_mem _ x.2⟩ : Pbar)) ⟨?_, ?_⟩)).symm
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        have h2 : QuotientGroup.mk' (CFSG.pCore 2 L) ((x : L)⁻¹ * y) = 1 := by
          rw [map_mul, map_inv]
          exact inv_mul_eq_one.2 h1
        have h3 := hinj _ (mul_mem (inv_mem x.2) y.2) h2
        exact Subtype.ext (inv_mul_eq_one.1 h3)
      · rintro ⟨z, hz⟩
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hz
        exact ⟨⟨x, hx⟩, rfl⟩
    have hPbar3 : IsPGroup 3 Pbar := IsPGroup.of_card (n := 3) (by rw [hPbarcard]; norm_num)
    have hPbaridx : ¬ 3 ∣ Pbar.index := by
      have h1 := Pbar.card_mul_index
      rw [hPbarcard, hQcard] at h1
      omega
    have h1 := (hsyl (hPbar3.toSylow hPbaridx)).2.2.2
    rw [IsPGroup.toSylow_coe] at h1
    apply hne
    rw [← h1, eq_bot_iff, commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hb
    rw [mem_bot, ← map_commutatorElement]
    have hxy : x * y = y * x := Subtype.ext (hc _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy))
    rw [commutatorElement_def, hxy, mul_inv_cancel_right, mul_inv_cancel, map_one]
  have hOK2 : IsPGroup 2 (pCoreOf 2 K) := by
    rw [pCoreOf_eq_map_cfsgPCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := K)).map K.subtype
  have hPGN : PG ≤ normalizer (K : Set G) := hPGR.trans (inf_le_right.trans hCK)
  set φ : PG →* Perm (Fin 5) := (kAct eK).comp (inclusion hPGN) with hφdef
  have hrange3 : IsPGroup 3 φ.range :=
    hPG3.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hrange3
  have hj1 : j ≤ 1 := by
    have hdvd : Nat.card φ.range ∣ 120 := by
      have h1 := Subgroup.card_subgroup_dvd_card φ.range
      rwa [Nat.card_perm, Nat.card_fin] at h1
    rw [hj] at hdvd
    by_contra hlt
    have h2 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
    have h3 := h2.trans hdvd
    norm_num at h3
  have hcardPG := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hj, hPGcard] at hcardPG
  set C' : Subgroup G := φ.ker.map PG.subtype with hC'def
  have hC'card : Nat.card C' = Nat.card φ.ker := card_map_of_injective (subtype_injective _)
  have hkC' : k ∉ C' := by
    rintro ⟨x, hx, hxk⟩
    have hx : φ x = 1 := hx
    have h1 : kAct eK ⟨k, le_normalizer hkK⟩ = 1 := by
      have h2 : (inclusion hPGN x : normalizer (K : Set G)) = ⟨k, le_normalizer hkK⟩ :=
        Subtype.ext hxk
      rw [← h2]
      exact hx
    exact hkO (mem_pCoreOf_of_kAct_eq_one eK hkK h1)
  have hC'9 : Nat.card C' = 9 := by
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exfalso
      have hker : Nat.card φ.ker = 27 := by omega
      have htop : φ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hker, hPGcard])
      apply hkC'
      exact ⟨⟨k, hkPG⟩, htop ▸ mem_top _, rfl⟩
    · rw [hC'card]
      omega
  have hC'comm : ∀ x ∈ C', ∀ y ∈ C', x * y = y * x := by
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := C')
      (by rw [hC'9]; norm_num)
    intro x hx y hy
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hC'k : ∀ x ∈ C', x * k = k * x := by
    rintro _ ⟨x', hx', rfl⟩
    have hφ : kAct eK ⟨(x' : G), hPGN x'.2⟩ = 1 := hx'
    have h1 := comm_mem_of_kAct_eq_one eK (hPGN x'.2) hφ hkK
    have h2 : (x' : G) * k * (x' : G)⁻¹ * k⁻¹ ∈ PG :=
      mul_mem (mul_mem (mul_mem x'.2 hkPG) (inv_mem x'.2)) (inv_mem hkPG)
    have h3 := eq_one_of_isPGroup_two_three hOK2 hPG3 h1 h2
    show (x' : G) * k = k * x'
    calc (x' : G) * k = ((x' : G) * k * (x' : G)⁻¹ * k⁻¹) * k * x' := by group
      _ = k * x' := by rw [h3, one_mul]
  have hsup : C' ⊔ zpowers k = PG := by
    have hle : C' ⊔ zpowers k ≤ PG := sup_le (map_subtype_le _) ((zpowers_le).2 hkPG)
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hPGcard]
    have h1 : Nat.card C' ∣ Nat.card (C' ⊔ zpowers k : Subgroup G) := card_dvd_of_le le_sup_left
    have h2 : Nat.card (C' ⊔ zpowers k : Subgroup G) ∣ 27 := hPGcard ▸ card_dvd_of_le hle
    have h3 : Nat.card (C' ⊔ zpowers k : Subgroup G) ≠ 9 := by
      intro h9
      apply hkC'
      have h4 : C' = C' ⊔ zpowers k :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, hC'9])
      rw [h4]
      exact mem_sup_right (mem_zpowers k)
    rw [hC'9] at h1
    have h5 : Nat.card (C' ⊔ zpowers k : Subgroup G) ≤ 27 := Nat.le_of_dvd (by norm_num) h2
    interval_cases hn : Nat.card (C' ⊔ zpowers k : Subgroup G) <;> omega
  apply hPGnc
  intro x hx y hy
  rw [← hsup, sup_eq_closure] at hx hy
  refine commute_of_mem_closure_of_pairwise ?_ hx hy
  rintro a (ha | ha) b (hb | hb)
  · exact hC'comm a ha b hb
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (hC'k a ha) m)).eq
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    exact ((Commute.zpow_left (hC'k b hb).symm m)).eq
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self k m n).eq

end Cover

end CFSG.Quasithin.H13.A7
