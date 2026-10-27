module

public import CFSG.Sporadic.Recognition.McLASThreeLocal
public import CFSG.Sporadic.Recognition.McLASThreeCentral
public import CFSG.Sporadic.Recognition.McLASTransport

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem le_of_abelian_card_ge {G : Type*} [Group G] [Finite G] {T A : Subgroup G}
    (hAT : A ≤ T) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcardT : Nat.card ↥T = 729) (hcardA : Nat.card ↥A = 81)
    (hC : ∀ t ∈ T, t ∉ A → Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ≤ 9)
    (hZ : Nat.card ↥(T ⊓ centralizer (T : Set G)) ≤ 3) {B : Subgroup G} (hBT : B ≤ T)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB : 81 ≤ Nat.card ↥B) : B ≤ A := by
  by_contra hBA
  obtain ⟨b, hbB, hbA⟩ := IsConcreteLE.not_le_iff_exists.1 hBA
  have hDle : A ⊓ B ≤ A ⊓ centralizer ({b} : Set G) := by
    intro d hd
    exact mem_inf.2 ⟨(mem_inf.1 hd).1,
      mem_centralizer_singleton_iff.2 (hBab d (mem_inf.1 hd).2 b hbB)⟩
  have hD9 : Nat.card ↥(A ⊓ B) ≤ 9 := (card_le_of_le hDle).trans (hC b (hBT hbB) hbA)
  have hAC : A ≤ T ⊓ centralizer ((A ⊓ B : Subgroup G) : Set G) := fun a ha =>
    mem_inf.2 ⟨hAT ha, mem_centralizer_iff.2 fun d hd => hAab d (mem_inf.1 hd).1 a ha⟩
  have hBC : B ≤ T ⊓ centralizer ((A ⊓ B : Subgroup G) : Set G) := fun c hc =>
    mem_inf.2 ⟨hBT hc, mem_centralizer_iff.2 fun d hd => hBab d (mem_inf.1 hd).2 c hc⟩
  set C : Subgroup G := T ⊓ centralizer ((A ⊓ B : Subgroup G) : Set G) with hCdef
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := C)
  rw [inf_of_le_left hBC] at h2
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hne : B.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    omega
  have hle := Subgroup.relIndex_le_of_le_right hAC hne
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm] at h1
  have hkey : Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥C * Nat.card ↥(A ⊓ B) := by
    calc Nat.card ↥A * Nat.card ↥B
        = (B.relIndex A * Nat.card ↥(A ⊓ B)) * Nat.card ↥B := by rw [h1]
      _ ≤ (B.relIndex C * Nat.card ↥(A ⊓ B)) * Nat.card ↥B := by gcongr
      _ = (B.relIndex C * Nat.card ↥B) * Nat.card ↥(A ⊓ B) := by ring
      _ = Nat.card ↥C * Nat.card ↥(A ⊓ B) := by rw [h2]
  have hC729 : Nat.card ↥C ≤ 729 := hcardT ▸ card_le_of_le (inf_le_left : C ≤ T)
  have h6561 : 6561 ≤ Nat.card ↥C * Nat.card ↥(A ⊓ B) := by
    calc 6561 = 81 * 81 := by norm_num
      _ ≤ Nat.card ↥A * Nat.card ↥B := by rw [hcardA]; exact Nat.mul_le_mul_left 81 hB
      _ ≤ _ := hkey
  have hCeq : Nat.card ↥C = 729 := by
    by_contra hne'
    have h728 : Nat.card ↥C ≤ 728 := by omega
    have := Nat.mul_le_mul h728 hD9
    omega
  have hDeq : Nat.card ↥(A ⊓ B) = 9 := by
    by_contra hne'
    have h8 : Nat.card ↥(A ⊓ B) ≤ 8 := by omega
    have := Nat.mul_le_mul hC729 h8
    omega
  have hCT : C = T :=
    Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ T) (by rw [hCeq, hcardT])
  have hDZ : A ⊓ B ≤ T ⊓ centralizer (T : Set G) := by
    intro d hd
    refine mem_inf.2 ⟨hAT (mem_inf.1 hd).1, mem_centralizer_iff.2 fun t ht => ?_⟩
    have htC : t ∈ C := hCT ▸ ht
    exact (mem_centralizer_iff.1 (mem_inf.1 htC).2 d hd).symm
  have := card_le_of_le hDZ
  omega

structure ThreeLocal (G : Type*) [Group G] (x : G) (R T A : Subgroup G) : Prop where
  order_x : orderOf x = 3
  card_centralizer : Nat.card ↥(centralizer ({x} : Set G)) = 29160
  card_normalizer : Nat.card ↥(normalizer (zpowers x : Set G)) = 58320
  pCore_eq : CFSG.inSubgroup (CFSG.pCore 3) (normalizer (zpowers x : Set G)) = R
  extraspecial_R : CFSG.IsExtraspecialPGroup 3 ↥R
  card_R : Nat.card ↥R = 243
  exponent_R : ∀ r ∈ R, r ^ 3 = 1
  center_R : R ⊓ centralizer (R : Set G) = zpowers x
  commutator_R : ⁅R, R⁆ = zpowers x
  T_le : T ≤ normalizer (zpowers x : Set G)
  T_sylow : Nat.card ↥T = 3 ^ (Nat.card ↥(normalizer (zpowers x : Set G))).factorization 3
  card_T : Nat.card ↥T = 729
  R_le_T : R ≤ T
  A_le_T : A ≤ T
  A_elementaryAbelian : CFSG.IsElementaryAbelian 3 ↥A
  card_A : Nat.card ↥A = 81
  card_inf : Nat.card ↥(R ⊓ A) = 27
  sup_eq : R ⊔ A = T
  order_three : ∀ y ∈ T, orderOf y = 3 → y ∈ R ∨ y ∈ A
  A_eq : A = closure ((T : Set G) ∩ {y | IsConj x y})
  card_class_inter : ((T : Set G) ∩ {y | IsConj x y}).ncard = 20
  weakly_closed : ∀ r ∈ R, IsConj x r → r = x ∨ r = x⁻¹
  abelian_subgroups : ∀ B : Subgroup G, B ≤ T → IsMulCommutative ↥B →
    Nat.card ↥B ≤ 81 ∧ (Nat.card ↥B = 81 → B = A)

theorem threeLocal_of_embedding
    {G : Type*} [Group G] (ι : G →* Equiv.Perm (Fin 275))
    (hι : Function.Injective ι) (hrange : ι.range = mclP) (hrows : ThreeFacts)
    (h : threeLocalCheck = true) :
    ∃ (x : G) (R T A : Subgroup G), ι x = three₁ ∧ R = subR3.comap ι ∧ T = sylowT.comap ι ∧
      A = subA3.comap ι ∧ ThreeLocal G x R T A := by
  have : Finite G := Finite.of_injective ι hι
  simp only [threeLocalCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, hg⟩, hin⟩, hnorm⟩, hsyl⟩, hstruct⟩, hA⟩, -⟩, hweak⟩, hth⟩ := h
  obtain ⟨hxP, hx3, hcent, -⟩ := three₁_facts hrows
  obtain ⟨hcardgx, -⟩ := card_gx hrows hg
  have hpc := pCore_gx hrows he hg hin hnorm hsyl
  obtain ⟨hRexp, hRcenter, hRcomm⟩ := rStructCheck_spec hrows he hin hstruct
  obtain ⟨hAel, hRA, hsup, hord3, hAcl, hAn⟩ := aStructCheck_spec hrows he hin hA
  obtain ⟨hT, hR, hAe, -, -, -⟩ := threeEnumCheck_spec hrows he
  obtain ⟨hRT, hAT, -, -⟩ := rInTCheck_spec hrows he hin
  obtain ⟨hTgx, hRgx⟩ := sylowT_le_gx hrows he hin
  have hweak' := weakCheck_spec hrows he hweak
  obtain ⟨hC9, hZ3⟩ := thompsonCheck_spec hrows he hth
  obtain ⟨x, hxι⟩ : ∃ x, ι x = three₁ := by
    have : three₁ ∈ ι.range := hrange ▸ hxP
    exact this
  have hRr : subR3 ≤ ι.range := hrange ▸ hR.le
  have hTr : sylowT ≤ ι.range := hrange ▸ hT.le
  have hAr : subA3 ≤ ι.range := hrange ▸ hAe.le
  have hmapR : (subR3.comap ι).map ι = subR3 := Subgroup.map_comap_eq_self hRr
  have hmapT : (sylowT.comap ι).map ι = sylowT := Subgroup.map_comap_eq_self hTr
  have hmapA : (subA3.comap ι).map ι = subA3 := Subgroup.map_comap_eq_self hAr
  have hmapN : (normalizer (zpowers x : Set G)).map ι = gx := by
    rw [map_normalizer_eq_inf_of_injective hι, hrange, MonoidHom.map_zpowers, hxι]
  have hmapC : (centralizer ({x} : Set G)).map ι =
      mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := by
    rw [map_centralizer_eq_inf_of_injective hι, hrange, Set.image_singleton, hxι]
  have hcardN : Nat.card ↥(normalizer (zpowers x : Set G)) = 58320 := by
    rw [← Subgroup.card_map_of_injective hι, hmapN]
    exact hcardgx
  have hconj : ∀ y : G, IsConj x y ↔ ι y ∈ conjClass mclP three₁ := by
    intro y
    rw [isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨ι c, hrange ▸ ⟨c, rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hxι]
    · rintro ⟨c, hc, hy⟩
      obtain ⟨g, rfl⟩ : c ∈ ι.range := hrange ▸ hc
      refine ⟨g, hι ?_⟩
      rw [map_mul, map_mul, map_inv, hxι, ← hy]
  have hordx : orderOf x = 3 := by
    rw [← orderOf_injective ι hι x, hxι]
    exact hx3
  have hRexp' : ∀ r ∈ subR3.comap ι, r ^ 3 = 1 := fun r hr =>
    hι (by rw [map_pow, map_one]; exact hRexp _ hr)
  have hRcard : Nat.card ↥(subR3.comap ι) = 243 := by
    rw [← Subgroup.card_map_of_injective hι, hmapR]
    exact hR.card
  have hcentR : (subR3.comap ι) ⊓ centralizer ((subR3.comap ι : Subgroup G) : Set G) =
      zpowers x := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_inf _ _ _ hι, map_centralizer_eq_inf_of_injective hι, hmapR,
      MonoidHom.map_zpowers, hxι, ← Subgroup.coe_map, hmapR, ← hRcenter]
    ext y
    simp only [mem_inf, MonoidHom.mem_range]
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hRr a, c⟩⟩
  have hcommR : ⁅subR3.comap ι, subR3.comap ι⁆ = zpowers x := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmapR, hRcomm, MonoidHom.map_zpowers, hxι]
  refine ⟨x, subR3.comap ι, sylowT.comap ι, subA3.comap ι, hxι, rfl, rfl, rfl, ?_⟩
  have hTle : sylowT.comap ι ≤ normalizer (zpowers x : Set G) := by
    rw [← map_le_map_iff_of_injective hι, hmapT, hmapN]
    exact hTgx
  have hcardT : Nat.card ↥(sylowT.comap ι) = 729 := by
    rw [← Subgroup.card_map_of_injective hι, hmapT]
    exact hT.card
  have hfac : (Nat.card ↥(normalizer (zpowers x : Set G))).factorization 3 = 6 := by
    rw [hcardN, show (58320 : ℕ) = 3 ^ 6 * 80 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hext : CFSG.IsExtraspecialPGroup 3 ↥(subR3.comap ι) :=
    isExtraspecialPGroup_of_invariants hRexp' hcentR hcommR hordx (by rw [hRcard]; norm_num)
  have hAcomm : ∀ a ∈ subA3, ∀ b ∈ subA3, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥subA3)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAexp : ∀ a ∈ subA3, a ^ 3 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian a ha
  have hSimage : ι '' (((sylowT.comap ι : Subgroup G) : Set G) ∩ {y | IsConj x y}) =
      (sylowT : Set (Equiv.Perm (Fin 275))) ∩ conjClass mclP three₁ := by
    ext m
    constructor
    · rintro ⟨y, ⟨hyT, hyc⟩, rfl⟩
      exact ⟨hyT, (hconj y).1 hyc⟩
    · rintro ⟨hmT, hmc⟩
      obtain ⟨y, rfl⟩ : m ∈ ι.range := hTr hmT
      exact ⟨y, ⟨hmT, (hconj y).2 hmc⟩, rfl⟩
  have hAT' : subA3.comap ι ≤ sylowT.comap ι :=
    (map_le_map_iff_of_injective hι).1 (by rw [hmapA, hmapT]; exact hAT)
  have hcardA : Nat.card ↥(subA3.comap ι) = 81 := by
    rw [← Subgroup.card_map_of_injective hι, hmapA]
    exact hAe.card
  have hC_G : ∀ t ∈ sylowT.comap ι, t ∉ subA3.comap ι →
      Nat.card ↥(subA3.comap ι ⊓ centralizer ({t} : Set G)) ≤ 9 := by
    intro t ht htA
    have hmap : (subA3.comap ι ⊓ centralizer ({t} : Set G)).map ι =
        subA3 ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 275))) := by
      rw [Subgroup.map_inf _ _ _ hι, map_centralizer_eq_inf_of_injective hι, hmapA,
        Set.image_singleton]
      ext y
      simp only [mem_inf, MonoidHom.mem_range]
      exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hAr a, c⟩⟩
    rw [← Subgroup.card_map_of_injective hι, hmap]
    exact hC9 (ι t) ht htA
  have hZ_G : Nat.card ↥(sylowT.comap ι ⊓ centralizer ((sylowT.comap ι : Subgroup G) : Set G)) ≤
      3 := by
    have hmap : (sylowT.comap ι ⊓ centralizer ((sylowT.comap ι : Subgroup G) : Set G)).map ι =
        sylowT ⊓ centralizer (sylowT : Set (Equiv.Perm (Fin 275))) := by
      rw [Subgroup.map_inf _ _ _ hι, map_centralizer_eq_inf_of_injective hι, hmapT,
        ← Subgroup.coe_map, hmapT]
      ext y
      simp only [mem_inf, MonoidHom.mem_range]
      exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hTr a, c⟩⟩
    rw [← Subgroup.card_map_of_injective hι, hmap]
    exact hZ3.le
  have hA' : ∀ a ∈ subA3.comap ι, ∀ b ∈ subA3.comap ι, a * b = b * a := fun a ha b hb =>
    hι (by rw [map_mul, map_mul]; exact hAcomm _ ha _ hb)
  refine
    { order_x := hordx
      card_centralizer := ?_
      card_normalizer := hcardN
      pCore_eq := ?_
      extraspecial_R := hext
      card_R := hRcard
      exponent_R := hRexp'
      center_R := hcentR
      commutator_R := hcommR
      T_le := hTle
      T_sylow := by rw [hcardT, hfac]; norm_num
      card_T := hcardT
      R_le_T := ?_
      A_le_T := ?_
      A_elementaryAbelian := ?_
      card_A := ?_
      card_inf := ?_
      sup_eq := ?_
      order_three := ?_
      A_eq := ?_
      card_class_inter := ?_
      weakly_closed := ?_
      abelian_subgroups := ?_ }
  · rw [← Subgroup.card_map_of_injective hι, hmapC]
    exact hcent
  · apply Subgroup.map_injective hι
    rw [map_inSubgroup_pCore hι, hmapN, hpc, hmapR]
  · exact (map_le_map_iff_of_injective hι).1 (by rw [hmapR, hmapT]; exact hRT)
  · exact (map_le_map_iff_of_injective hι).1 (by rw [hmapA, hmapT]; exact hAT)
  · exact
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hι (by
          simp only [Subgroup.coe_mul, map_mul]
          exact hAcomm (ι a.1) a.2 (ι b.1) b.2))⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (hι (by
            simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
            exact hAexp (ι a.1) a.2)) }
  · rw [← Subgroup.card_map_of_injective hι, hmapA]
    exact hAe.card
  · rw [← Subgroup.card_map_of_injective hι, Subgroup.map_inf _ _ _ hι, hmapR, hmapA]
    exact hRA
  · apply Subgroup.map_injective hι
    rw [Subgroup.map_sup, hmapR, hmapA, hmapT]
    exact hsup
  · exact fun y hy hy3 => hord3 (ι y) hy ((orderOf_injective ι hι y).trans hy3)
  · apply Subgroup.map_injective hι
    rw [hmapA, MonoidHom.map_closure, hSimage, hAcl]
  · rw [← Set.ncard_image_of_injective _ hι, hSimage]
    exact hAn
  · intro r hr hrc
    rcases hweak' (ι r) hr ((hconj r).1 hrc) with h1 | h1
    · exact Or.inl (hι (h1.trans hxι.symm))
    · exact Or.inr (hι (by rw [h1, map_inv, hxι]))
  · intro B hBT hBab
    have hBab' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥B)).comm ⟨a, ha⟩ ⟨b, hb⟩)
    by_cases hB : 81 ≤ Nat.card ↥B
    · have hBA := le_of_abelian_card_ge hAT' hA' hcardT hcardA hC_G hZ_G hBT hBab' hB
      have hle : Nat.card ↥B ≤ 81 := hcardA ▸ card_le_of_le hBA
      exact ⟨hle, fun h81 => Subgroup.eq_of_le_of_card_ge hBA (by rw [hcardA, h81])⟩
    · exact ⟨by omega, fun h81 => absurd (by omega) hB⟩

theorem ne_inv_of_orderOf_eq_three {G : Type*} [Group G] {y : G} (hy : orderOf y = 3) :
    y ≠ y⁻¹ := by
  intro h
  have h2 : y ^ 2 = 1 := by
    rw [pow_two]
    calc y * y = y * y⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel y
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hy] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)

theorem ncard_eq_two_mul_ncard_zpowers {G : Type*} [Group G] [Finite G] {S : Set G}
    (hS3 : ∀ y ∈ S, orderOf y = 3) (hSinv : ∀ y ∈ S, y⁻¹ ∈ S) :
    S.ncard = 2 * ((fun y => zpowers y) '' S).ncard := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hS : S.Finite := Set.toFinite S
  let Sf : Finset G := hS.toFinset
  have hmem : ∀ y, y ∈ Sf ↔ y ∈ S := fun y => hS.mem_toFinset
  have e1 : S.ncard = Sf.card := Set.ncard_eq_toFinset_card S hS
  have e2 : ((fun y => zpowers y) '' S) =
      ((Sf.image (fun y => zpowers y) : Finset (Subgroup G)) : Set (Subgroup G)) := by
    ext H
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe, hmem]
  have hfib : ∀ H ∈ Sf.image (fun y => zpowers y),
      (Sf.filter fun y => zpowers y = H).card = 2 := by
    intro H hH
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.1 hH
    have hy : y ∈ S := (hmem y).1 hyS
    have hy3 := hS3 y hy
    have : Sf.filter (fun z => zpowers z = zpowers y) = {y, y⁻¹} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hzy⟩
        have hzS : z ∈ S := (hmem z).1 hz
        have hzm : z ∈ zpowers y := hzy ▸ mem_zpowers z
        exact eq_or_eq_inv_of_mem_zpowers hy3 hzm (hS3 z hzS)
      · rintro (rfl | rfl)
        · exact ⟨hyS, rfl⟩
        · exact ⟨(hmem _).2 (hSinv _ hy), by simp⟩
    rw [this, Finset.card_pair (ne_inv_of_orderOf_eq_three hy3)]
  rw [e1, e2, Set.ncard_coe_finset, Finset.card_eq_sum_card_image (fun y => zpowers y) Sf,
    Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

theorem delta_inter_eq_image {G : Type*} [Group G] {x : G}
    (hΔ : ∀ H : Subgroup G, IsPCentralSubgroup 3 H ↔
      ∃ g : G, H = (zpowers x).map (MulAut.conj g).toMonoidHom) (T : Subgroup G) :
    {H : Subgroup G | IsPCentralSubgroup 3 H ∧ H ≤ T} =
      (fun y => zpowers y) '' ((T : Set G) ∩ {y | IsConj x y}) := by
  ext H
  constructor
  · rintro ⟨hH, hHT⟩
    obtain ⟨g, rfl⟩ := (hΔ H).1 hH
    rw [MonoidHom.map_zpowers] at hHT ⊢
    refine ⟨_, ⟨hHT (mem_zpowers _), ?_⟩, rfl⟩
    exact isConj_iff.2 ⟨g, by simp⟩
  · rintro ⟨y, ⟨hyT, hyc⟩, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hyc
    refine ⟨(hΔ _).2 ⟨c, ?_⟩, zpowers_le.2 hyT⟩
    rw [MonoidHom.map_zpowers]
    simp

theorem closure_delta_eq {G : Type*} [Group G] {x : G}
    (hΔ : ∀ H : Subgroup G, IsPCentralSubgroup 3 H ↔
      ∃ g : G, H = (zpowers x).map (MulAut.conj g).toMonoidHom) (T : Subgroup G) :
    closure {y : G | ∃ H : Subgroup G, IsPCentralSubgroup 3 H ∧ H ≤ T ∧ y ∈ H} =
      closure ((T : Set G) ∩ {y | IsConj x y}) := by
  apply le_antisymm
  · rw [closure_le]
    rintro y ⟨H, hH, hHT, hy⟩
    have : H ∈ {H : Subgroup G | IsPCentralSubgroup 3 H ∧ H ≤ T} := ⟨hH, hHT⟩
    rw [delta_inter_eq_image hΔ T] at this
    obtain ⟨z, hz, rfl⟩ := this
    exact (zpowers_le.2 (subset_closure hz)) hy
  · rw [closure_le]
    intro z hz
    refine subset_closure ⟨zpowers z, ?_, zpowers_le.2 hz.1, mem_zpowers z⟩
    have : zpowers z ∈ (fun y => zpowers y) '' ((T : Set G) ∩ {y | IsConj x y}) := ⟨z, hz, rfl⟩
    rw [← delta_inter_eq_image hΔ T] at this
    exact this.1

theorem delta_of_embedding
    {G : Type*} [Group G] (ι : G →* Equiv.Perm (Fin 275))
    (hι : Function.Injective ι) (hrange : ι.range = mclP) (hrows : ThreeFacts)
    (hsyl : sylowThreeOK = true) (h : threeLocalCheck = true) :
    ∃ (x : G) (R T A : Subgroup G), ι x = three₁ ∧ A = subA3.comap ι ∧ ThreeLocal G x R T A ∧
      (∀ H : Subgroup G, IsPCentralSubgroup 3 H ↔
        ∃ g : G, H = (zpowers x).map (MulAut.conj g).toMonoidHom) ∧
      A = closure {y : G | ∃ H : Subgroup G, IsPCentralSubgroup 3 H ∧ H ≤ T ∧ y ∈ H} ∧
      {H : Subgroup G | IsPCentralSubgroup 3 H ∧ H ≤ T}.ncard = 10 := by
  have : Finite G := Finite.of_injective ι hι
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, R, T, A, hxι, hR, hT, hA, hL⟩ := threeLocal_of_embedding ι hι hrange hrows h
  have h' := h
  simp only [threeLocalCheck, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hg⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
  obtain ⟨⟨hh₀, hinvh, -, -⟩, -⟩ := gxCheck_spec hg
  obtain ⟨T₀, hT₀P, hT₀card, hT₀Z, hxZ⟩ := sylowThreeOK_spec hsyl
  have hT₀r : T₀ ≤ ι.range := hrange ▸ hT₀P
  have hmapT₀ : (T₀.comap ι).map ι = T₀ := Subgroup.map_comap_eq_self hT₀r
  have hcenmap : (T₀.comap ι ⊓ centralizer ((T₀.comap ι : Subgroup G) : Set G)).map ι =
      T₀ ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.map_inf _ _ _ hι, map_centralizer_eq_inf_of_injective hι, hmapT₀,
      ← Subgroup.coe_map, hmapT₀]
    ext y
    simp only [mem_inf, MonoidHom.mem_range]
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hT₀r a, c⟩⟩
  have hcardG : Nat.card G = 898128000 := by
    have h1 := congrArg (fun K : Subgroup (Equiv.Perm (Fin 275)) => Nat.card ↥K) hrange
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, h1]
    exact card_mclP
  have hfacG : (Nat.card G).factorization 3 = 6 := by
    rw [hcardG, show (898128000 : ℕ) = 3 ^ 6 * 1232000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hT₀' : Nat.card ↥(T₀.comap ι) = 3 ^ (Nat.card G).factorization 3 := by
    rw [← Subgroup.card_map_of_injective hι, hmapT₀, hT₀card, hfacG]
    norm_num
  have hZ' : Nat.card ↥(T₀.comap ι ⊓ centralizer ((T₀.comap ι : Subgroup G) : Set G)) = 3 := by
    rw [← Subgroup.card_map_of_injective hι, hcenmap]
    exact hT₀Z
  have hx' : x ∈ T₀.comap ι ⊓ centralizer ((T₀.comap ι : Subgroup G) : Set G) := by
    rw [← Subgroup.mem_map_iff_mem hι, hcenmap, hxι]
    exact hxZ
  have hΔ := isPCentralSubgroup_iff_exists_conj (T₀.comap ι) hT₀' hZ' hx' hL.order_x
  have hinv : IsConj x x⁻¹ := by
    obtain ⟨g, hg1⟩ : tp 275 invHTab ∈ ι.range := hrange ▸ hh₀
    refine isConj_iff.2 ⟨g, hι ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, hxι, hg1]
    exact hinvh
  have hS3 : ∀ y ∈ (T : Set G) ∩ {y | IsConj x y}, orderOf y = 3 := by
    rintro y ⟨-, hy⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hL.order_x
  have hSinv : ∀ y ∈ (T : Set G) ∩ {y | IsConj x y}, y⁻¹ ∈ (T : Set G) ∩ {y | IsConj x y} := by
    rintro y ⟨hyT, hy⟩
    refine ⟨T.inv_mem hyT, ?_⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    obtain ⟨d, hd⟩ := isConj_iff.1 hinv
    refine isConj_iff.2 ⟨c * d, ?_⟩
    calc c * d * x * (c * d)⁻¹ = c * (d * x * d⁻¹) * c⁻¹ := by group
      _ = c * x⁻¹ * c⁻¹ := by rw [hd]
      _ = (c * x * c⁻¹)⁻¹ := by group
  refine ⟨x, R, T, A, hxι, hA, hL, hΔ, ?_, ?_⟩
  · rw [closure_delta_eq hΔ T]
    exact hL.A_eq ▸ rfl
  · rw [delta_inter_eq_image hΔ T]
    have h2 := ncard_eq_two_mul_ncard_zpowers hS3 hSinv
    rw [hL.card_class_inter] at h2
    omega

end CFSG.Sporadic.Recognition.McLAS
