module

public import CFSG.Quasithin.H13.A7NatSix
public import CFSG.Quasithin.H13.A7SharedCubicSylow
public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd
public import CFSG.Quasithin.Background.B6Sections

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

theorem exists_odd_order_preimage {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (x : A) (hz : Odd (orderOf (f x))) : ∃ y : A, Odd (orderOf y) ∧ f y = f x := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : (2 ^ a).Coprime (orderOf (f x)) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hz)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(x ^ 2 ^ a) ^ m, ?_, by rw [map_pow, map_pow, hm]⟩
  have h1 : ((x ^ 2 ^ a) ^ m) ^ b = 1 := by
    rw [← pow_mul, ← pow_mul, show 2 ^ a * (m * b) = orderOf x * m by rw [hab]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  exact hb.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem oTwoUpper_eq_self_of_simple {Y : Type*} [Group Y] {S : Subgroup Y}
    (hS : IsSimpleGroup S) {s : Y} (hsS : s ∈ S) (hs1 : s ≠ 1) (hso : Odd (orderOf s)) :
    oTwoUpper S = S := by
  refine le_antisymm (oTwoUpper_le S) ?_
  have hN : ((oTwoUpper S).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le S)).2 (le_normalizer_oTwoUpper S)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS _ hN with h | h
  · exfalso
    have h1 : (⟨s, hsS⟩ : S) ∈ (oTwoUpper S).subgroupOf S := mem_oTwoUpper_of_odd hsS hso
    rw [h, mem_bot] at h1
    exact hs1 (congrArg Subtype.val h1)
  · intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ (oTwoUpper S).subgroupOf S := h ▸ mem_top _
    exact h1

theorem oTwoUpper_subgroupOf {G : Type*} [Group G] [Finite G] {X L : Subgroup G} (hXL : X ≤ L) :
    (oTwoUpper X).subgroupOf L = oTwoUpper (X.subgroupOf L) := by
  have h1 := oTwoUpper_map L.subtype (X.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hXL] at h1
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem oTwoUpper_eq_top_of_isPGroup_quotient {G : Type*} [Group G] (X : Subgroup G)
    (N : Subgroup ↥(oTwoUpper X)) [N.Normal] (hN : IsPGroup 2 (↥(oTwoUpper X) ⧸ N)) :
    N = ⊤ := by
  have key : ∀ x (hx : x ∈ oTwoUpper X), (⟨x, hx⟩ : ↥(oTwoUpper X)) ∈ N := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y hy => (⟨y, hy⟩ : ↥(oTwoUpper X)) ∈ N)
      ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hy' : y ∈ oTwoUpper X := Subgroup.subset_closure hy
      obtain ⟨n, hn⟩ := hN (QuotientGroup.mk' N ⟨y, hy'⟩)
      have h1 : orderOf (QuotientGroup.mk' N ⟨y, hy'⟩) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
      have h2 : orderOf (QuotientGroup.mk' N ⟨y, hy'⟩) ∣ orderOf y := by
        have := orderOf_map_dvd (QuotientGroup.mk' N) (⟨y, hy'⟩ : ↥(oTwoUpper X))
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (2 ^ n) (orderOf y) :=
        Nat.Coprime.pow_left n ((Nat.coprime_two_left).2 hy.2)
      have h3 : orderOf (QuotientGroup.mk' N ⟨y, hy'⟩) = 1 := by
        have := Nat.dvd_gcd h1 h2
        rw [hcop] at this
        exact Nat.dvd_one.1 this
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact h3
    · exact one_mem N
    · intro a b ha hb hNa hNb
      exact mul_mem hNa hNb
    · intro a ha hNa
      exact inv_mem hNa
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  exact key x hx

theorem isSimpleGroup_stabA7_vecSix : IsSimpleGroup (stabA7 vecSix) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  exact altSixEquiv.symm.isSimpleGroup

theorem threeCycle_mem_stabA7_vecSix :
    ((⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩ :
      alternatingGroup (Fin 7)) ∈ stabA7 vecSix) := by
  rw [mem_stabA7, permAct7_vecSix_iff]
  decide

theorem oTwoUpper_stabA7_vecSix : oTwoUpper (stabA7 vecSix) = stabA7 vecSix := by
  refine oTwoUpper_eq_self_of_simple isSimpleGroup_stabA7_vecSix threeCycle_mem_stabA7_vecSix ?_
    ?_
  · intro h
    have := congrArg (fun σ : alternatingGroup (Fin 7) => (σ : Perm (Fin 7)) 0) h
    exact absurd this (by decide)
  · have h3 : orderOf (⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩ :
        alternatingGroup (Fin 7)) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by decide) (by decide)
    rw [h3]
    decide

theorem le_cfsgPCore_of_normal {X : Type*} [Group X] {p : ℕ} {N : Subgroup X} (hN : N.Normal)
    (hNp : IsPGroup p N) : N ≤ CFSG.pCore p X := by
  unfold CFSG.pCore
  exact le_sSup ⟨hN, hNp⟩

section Le

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem natLam_map_Le_six (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    {e : V} (he : vec ψ e = vecSix) :
    ((oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G))).subgroupOf L).map
      (natLam hLV hLact) = stabA7 vecSix := by
  rw [oTwoUpper_subgroupOf inf_le_left, ← oTwoUpper_map,
    natLam_map_inf_centralizer hLV hLact hLonto e, he, oTwoUpper_stabA7_vecSix]

omit [Finite G] in
theorem stabA7_vecSix_nonabelian : ∃ a b : stabA7 vecSix, a * b ≠ b * a :=
  ⟨⟨⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩,
      by rw [mem_stabA7, permAct7_vecSix_iff]; decide⟩,
    ⟨⟨swap 1 2 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩,
      by rw [mem_stabA7, permAct7_vecSix_iff]; decide⟩, fun h => by
    have h2 := congrArg (fun x : stabA7 vecSix => ((x : alternatingGroup (Fin 7)) :
      Perm (Fin 7))) h
    exact absurd h2 (by decide)⟩

omit [Finite G] in
theorem isPerfect_stabA7_vecSix : Group.IsPerfect (stabA7 vecSix) := by
  have hs := isSimpleGroup_stabA7_vecSix
  rw [Group.isPerfect_def]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (commutator (stabA7 vecSix))
      inferInstance with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := stabA7_vecSix_nonabelian
    apply hab
    have h1 : ⁅a, b⁆ = 1 := by
      have := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [← _root_.commutator_def, h, mem_bot] at this
      exact this
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  · exact h

omit [Finite G] in
theorem center_stabA7_vecSix : center (stabA7 vecSix) = ⊥ := by
  have hs := isSimpleGroup_stabA7_vecSix
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (center (stabA7 vecSix))
      inferInstance with h | h
  · exact h
  · exfalso
    set a : stabA7 vecSix := ⟨⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩,
      by rw [mem_stabA7, permAct7_vecSix_iff]; decide⟩
    set b : stabA7 vecSix := ⟨⟨swap 1 2 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩,
      by rw [mem_stabA7, permAct7_vecSix_iff]; decide⟩
    have h1 : a * b = b * a := (mem_center_iff.1 (h ▸ mem_top a) b).symm
    have h2 := congrArg (fun x : stabA7 vecSix => ((x : alternatingGroup (Fin 7)) :
      Perm (Fin 7))) h1
    exact absurd h2 (by decide)

theorem quasisimple_Le_six (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {e : V} (he : vec ψ e = vecSix) {Le : Subgroup G}
    (hLe : Le = oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G))) :
    CFSG.IsQuasisimple (↥Le ⧸ CFSG.pCore 2 ↥Le) ∧
      Nonempty ((↥Le ⧸ CFSG.pCore 2 ↥Le) ⧸ center (↥Le ⧸ CFSG.pCore 2 ↥Le) ≃*
        alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set lam := natLam hLV hLact with hlam
  have hlams := natLam_surjective hLV hLact hLonto
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hF1 : CFSG.pCore 2 ↥L ≤ lam.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : ((CFSG.pCore 2 ↥L).map lam).Normal := CFSG.pCore_normal.map lam hlams
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hA7s _ hN with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).map lam) := CFSG.pCore_isPGroup.map lam
      rw [h] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, coord_card_alternating_seven] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  set lam' : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin 7) :=
    QuotientGroup.lift _ lam hF1 with hlam'
  have hlam'π : ∀ l, lam' (π l) = lam l := fun l => rfl
  have hlam's : Function.Surjective lam' := fun a => by
    obtain ⟨l, rfl⟩ := hlams a
    exact ⟨π l, rfl⟩
  have hK : lam'.ker ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq lam'.normal_ker with h | h
    · exfalso
      have h1 : ∀ a, a = (1 : alternatingGroup (Fin 7)) := by
        intro a
        obtain ⟨x, rfl⟩ := hlam's a
        exact (MonoidHom.mem_ker).1 (h ▸ mem_top x)
      have h2 : Nat.card (alternatingGroup (Fin 7)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
      rw [coord_card_alternating_seven] at h2
      norm_num at h2
    · exact h
  obtain ⟨hQperf, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hLq
  have hKodd : Odd (Nat.card lam'.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hK)
  have hLeL : Le ≤ L := hLe ▸ (oTwoUpper_le _).trans inf_le_left
  have hL1 : (Le.subgroupOf L).map lam = stabA7 vecSix := by
    rw [hLe]
    exact natLam_map_Le_six hLV hLact hLonto he
  set R : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (Le.subgroupOf L).map π with hR
  have hRstab : R.map lam' = stabA7 vecSix := by
    rw [hR, Subgroup.map_map]
    exact hL1
  have hKR : lam'.ker ≤ R := by
    intro z hz
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
    have hzo : Odd (orderOf (π l)) := by
      have h1 : orderOf (⟨π l, hz⟩ : lam'.ker) = orderOf (π l) := Subgroup.orderOf_mk _ _
      rw [← h1]
      exact hKodd.of_dvd_nat (orderOf_dvd_natCard _)
    obtain ⟨l', hl'o, hl'⟩ := exists_odd_order_preimage π l hzo
    have hl'C : (l' : G) ∈ centralizer (V : Set G) := by
      rw [← natLam_eq_one_iff hLV hLact, ← hlam'π, hl']
      exact hz
    have hl'e : (l' : G) ∈ centralizer ({(e : G)} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.2 e.2) hl'C
    have hl'Le : (l' : G) ∈ Le := by
      rw [hLe]
      exact mem_oTwoUpper_of_odd ⟨l'.2, hl'e⟩ (by rwa [Subgroup.orderOf_coe])
    exact ⟨l', hl'Le, hl'⟩
  set fR : ↥R →* ↥(stabA7 vecSix) := (lam'.comp R.subtype).codRestrict (stabA7 vecSix)
    (fun r => by rw [← hRstab]; exact ⟨r, r.2, rfl⟩) with hfR
  have hfRs : Function.Surjective fR := by
    rintro ⟨σ, hσ⟩
    rw [← hRstab] at hσ
    obtain ⟨r, hr, rfl⟩ := hσ
    exact ⟨⟨r, hr⟩, rfl⟩
  have hfRker : ∀ r : R, r ∈ fR.ker ↔ (r : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ lam'.ker := by
    intro r
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hfRcen : fR.ker ≤ center R := by
    intro r hr
    rw [mem_center_iff]
    intro s
    apply Subtype.ext
    exact mem_center_iff.1 (hK ((hfRker r).1 hr)) (s : _)
  have hRperf : Group.IsPerfect R := by
    rw [Group.isPerfect_def]
    have hkerD : fR.ker ≤ commutator R := by
      by_cases hK1 : lam'.ker = ⊥
      · intro r hr
        rw [hfRker, hK1, mem_bot] at hr
        have : r = 1 := Subtype.ext hr
        rw [this]
        exact one_mem _
      · obtain ⟨hK3, hsyl⟩ := A7_alternating_six_seven_odd_cover_cubic_Sylow (n := 7)
          (Or.inr rfl) (E := ↥L ⧸ CFSG.pCore 2 ↥L) lam' hlam's hK hKodd hK1
        have hcardQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 ^ 3 * 280 := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup lam'.ker,
            Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective lam' hlam's).toEquiv,
            coord_card_alternating_seven, hK3]
          norm_num
        have hkerR : Nat.card fR.ker = 3 := by
          rw [← hK3]
          refine Nat.card_congr ⟨fun r => ⟨r.1, (hfRker r.1).1 r.2⟩,
            fun z => ⟨⟨z.1, hKR z.2⟩, (hfRker _).2 z.2⟩, fun r => rfl, fun z => rfl⟩
        have hcardR : Nat.card R = 3 ^ 3 * 40 := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fR.ker,
            Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fR hfRs).toEquiv,
            nat_card_stabA7_vecSix, hkerR]
          norm_num
        obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 3 R))
        have hP₀ : Nat.card P₀ = 3 ^ 3 := card_sylow_eq_of_card P₀ hcardR (by norm_num)
        set P₁ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (P₀ : Subgroup R).map R.subtype with hP₁
        have hP₁card : Nat.card P₁ = 3 ^ 3 := by
          rw [hP₁, Subgroup.card_map_of_injective R.subtype_injective, hP₀]
        have hP₁3 : IsPGroup 3 P₁ := P₀.isPGroup'.map R.subtype
        have hP₁idx : ¬ 3 ∣ P₁.index := by
          have h1 := P₁.index_mul_card
          rw [hP₁card, hcardQ] at h1
          have h2 : P₁.index = 280 := by
            have := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 3)
              (h1.trans (mul_comm _ _))
            exact this
          rw [h2]
          norm_num
        obtain ⟨-, -, -, hP₁comm⟩ := hsyl (hP₁3.toSylow hP₁idx)
        rw [IsPGroup.toSylow_coe] at hP₁comm
        intro r hr
        have hrK := (hfRker r).1 hr
        rw [← hP₁comm, hP₁, ← Subgroup.map_commutator] at hrK
        obtain ⟨d, hd, hdr⟩ := hrK
        have hdr' : d = r := Subtype.ext hdr
        rw [← hdr']
        exact commutator_mono le_top le_top hd
    have hsurjD : (commutator R).map fR = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 hfRs, ← _root_.commutator_def]
      exact Group.isPerfect_def.1 isPerfect_stabA7_vecSix
    rw [eq_top_iff]
    intro r _
    have h1 : fR r ∈ (commutator R).map fR := by rw [hsurjD]; exact mem_top _
    obtain ⟨d, hd, hdr⟩ := h1
    have h2 : d⁻¹ * r ∈ fR.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdr, inv_mul_cancel]
    have h3 := mul_mem hd (hkerD h2)
    rwa [mul_inv_cancel_left] at h3
  have hstabq : CFSG.IsQuasisimple (stabA7 vecSix) := by
    have := isSimpleGroup_stabA7_vecSix
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup stabA7_vecSix_nonabelian).1
  have hRq : CFSG.IsQuasisimple R :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hRperf fR hfRs hfRcen).2 hstabq
  set θ : ↥Le →* (↥L ⧸ CFSG.pCore 2 ↥L) := π.comp (Subgroup.inclusion hLeL) with hθ
  have hθrange : θ.range = R := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLeL x, x.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  have hθR : ∀ x, θ x ∈ R := fun x => hθrange ▸ ⟨x, rfl⟩
  set θR : ↥Le →* ↥R := θ.codRestrict R hθR with hθRdef
  have hθRs : Function.Surjective θR := by
    rintro ⟨z, hz⟩
    rw [← hθrange] at hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨x, rfl⟩
  have hθker : θR.ker = CFSG.pCore 2 ↥Le := by
    have hker1 : θR.ker = θ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    apply le_antisymm
    · rw [hker1]
      apply le_cfsgPCore_of_normal θ.normal_ker
      have h1 : θ.ker = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hLeL) := by
        rw [hθ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
      rw [h1]
      exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hLeL)
    ·
      have hsurj : Function.Surjective (fR.comp θR) := hfRs.comp hθRs
      have hP : (CFSG.pCore 2 ↥Le).map (fR.comp θR) = ⊥ := by
        have hs := isSimpleGroup_stabA7_vecSix
        have hN := (CFSG.pCore_normal (p := 2) (G := ↥Le)).map _ hsurj
        rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hN with h | h
        · exact h
        · exfalso
          have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥Le).map (fR.comp θR)) :=
            CFSG.pCore_isPGroup.map _
          rw [h] at h2
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
          rw [Subgroup.card_top, nat_card_stabA7_vecSix] at hk
          have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
          exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
      intro x hx
      have hx1 : θR x ∈ fR.ker := by
        have : (fR.comp θR) x ∈ (CFSG.pCore 2 ↥Le).map (fR.comp θR) := mem_map_of_mem _ hx
        rw [hP, mem_bot] at this
        exact this
      have hxK : θ x ∈ lam'.ker := (hfRker (θR x)).1 hx1
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥Le).map θ) := CFSG.pCore_isPGroup.map θ
      obtain ⟨n, hn⟩ := h2 ⟨θ x, mem_map_of_mem _ hx⟩
      have hord : orderOf (⟨θ x, hxK⟩ : lam'.ker) ∣ 2 ^ n := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simpa using congrArg Subtype.val hn
      have hodd' : Odd (orderOf (⟨θ x, hxK⟩ : lam'.ker)) :=
        hKodd.of_dvd_nat (orderOf_dvd_natCard _)
      have h1 : orderOf (⟨θ x, hxK⟩ : lam'.ker) = 1 := by
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hord with ⟨j, -, hjeq⟩
        rw [hjeq] at hodd' ⊢
        rcases j with _ | j
        · rfl
        · exfalso
          rw [pow_succ] at hodd'
          exact Nat.not_even_iff_odd.2 hodd' (even_two.mul_left _)
      rw [orderOf_eq_one_iff] at h1
      have h2 : θ x = 1 := congrArg Subtype.val h1
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h2
  set e₁ : (↥Le ⧸ CFSG.pCore 2 ↥Le) ≃* ↥R :=
    (QuotientGroup.quotientMulEquivOfEq hθker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θR hθRs) with he₁
  have hP₀perf : Group.IsPerfect (↥Le ⧸ CFSG.pCore 2 ↥Le) := by
    have := hRperf
    exact Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  have hP₀q : CFSG.IsQuasisimple (↥Le ⧸ CFSG.pCore 2 ↥Le) := by
    refine (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP₀perf e₁.toMonoidHom
      e₁.surjective ?_).2 hRq
    intro x hx
    have : x = 1 := e₁.injective (by rw [map_one]; exact hx)
    rw [this]
    exact one_mem _
  set g : (↥Le ⧸ CFSG.pCore 2 ↥Le) →* ↥(stabA7 vecSix) := fR.comp e₁.toMonoidHom with hg
  have hgs : Function.Surjective g := hfRs.comp e₁.surjective
  have hgker : g.ker ≤ center (↥Le ⧸ CFSG.pCore 2 ↥Le) := by
    intro x hx
    have h1 : e₁ x ∈ center R := hfRcen hx
    rw [mem_center_iff] at h1 ⊢
    intro y
    apply e₁.injective
    rw [map_mul, map_mul]
    exact h1 (e₁ y)
  have hcen : center (↥Le ⧸ CFSG.pCore 2 ↥Le) = g.ker := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hP₀perf g hgs hgker, center_stabA7_vecSix]
    rfl
  exact ⟨hP₀q, ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)).trans altSixEquiv.symm⟩⟩

end Le

end CFSG.Quasithin.H13.A7
