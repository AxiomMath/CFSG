module

public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.Quasithin.SteinbergBSConjugateOrbits

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Open CFSG.Quasithin.SteinbergBS CFSG.ShultStronglyClosedTI

section BenderCore

variable {G : Type*} [Group G] [Finite G]

theorem not_odd_card_of_le {E Y : Subgroup G} (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥)
    (hEY : E ≤ Y) : ¬ Odd (Nat.card Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hY
  obtain ⟨m, hm⟩ := hE.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hm
    exact hE1 hm
  have h2 : 2 ∣ Nat.card Y := (dvd_pow_self 2 hm0).trans (hm ▸ Subgroup.card_dvd_of_le hEY)
  exact (Nat.not_even_iff_odd.2 hY) (even_iff_two_dvd.2 h2)

omit [Finite G] in
theorem eq_one_of_mem_odd {Y : Subgroup G} (hY : Odd (Nat.card Y)) {y : G} (hy : y ∈ Y)
    {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf (⟨y, hy⟩ : Y) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [hk]))
  have h2 : orderOf (⟨y, hy⟩ : Y) ∣ Nat.card Y := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hY)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

omit [Finite G] in
theorem conjugate_ne_bot {X : Subgroup G} (hX : X ≠ ⊥) (g : G) : conjugate X g ≠ ⊥ := fun h =>
  hX ((map_eq_bot_iff_of_injective X (f := (MulAut.conj g⁻¹).toMonoidHom)
    (fun _ _ hab => (MulAut.conj g⁻¹).injective hab)).1 h)

theorem mem_of_le_inf_conjugate {N X : Subgroup G} (hN : fusionStronglyEmbedded N)
    (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) {g : G} (hXg : X ≤ N ⊓ conjugate N g) : g ∈ N := by
  by_contra hg
  exact not_odd_card_of_le hX hX1 hXg (hN.2.2 g hg)

theorem conjugate_not_le {N E : Subgroup G} (hN : fusionStronglyEmbedded N) (hEN : E ≤ N)
    (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥) {x : G} (hx : x ∉ N) : ¬ conjugate E x ≤ N :=
  fun h => hx (mem_of_le_inf_conjugate hN (hE.map _) (conjugate_ne_bot hE1 x)
    (le_inf h (map_mono hEN)))

theorem isSylowOf_inf_of_stronglyEmbedded {U E L : Subgroup G} (hU : IsPGroup 2 U)
    (hUi : ¬ 2 ∣ U.index) (hN : fusionStronglyEmbedded (normalizer (U : Set G)))
    (hEU : E ≤ U) (hEL : E ≤ L) (hE1 : E ≠ ⊥) : IsSylowOf 2 (U ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUL : IsPGroup 2 ((U ⊓ L).subgroupOf L) := hU.to_inf_left.comap_subtype
  obtain ⟨Q, hQ⟩ := hUL.exists_le_sylow
  have hPsyl : IsSylowOf 2 ((Q : Subgroup L).map L.subtype) L := ⟨Q, rfl⟩
  have hUP : U ⊓ L ≤ (Q : Subgroup L).map L.subtype := fun y hy => ⟨⟨y, hy.2⟩, hQ hy, rfl⟩
  obtain ⟨R, hPR⟩ := hPsyl.isPGroup.exists_le_sylow
  have hUsyl : IsSylowOf 2 U ⊤ := isSylowOf_iff.2 ⟨le_top, hU, by rwa [relIndex_top_right]⟩
  have hRsyl : IsSylowOf 2 (R : Subgroup G) ⊤ :=
    isSylowOf_iff.2 ⟨le_top, R.isPGroup', by rw [relIndex_top_right]; exact R.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hUsyl.exists_mem_conj hRsyl
  have hEk : E ≤ normalizer (U : Set G) ⊓ conjugate (normalizer (U : Set G)) k⁻¹ := by
    intro e he
    refine ⟨le_normalizer (hEU he), mem_conjugate_iff.2 ?_⟩
    rw [inv_inv]
    exact le_normalizer ((hk e).1 (hPR (hUP ⟨hEU he, hEL he⟩)))
  have hkN : k⁻¹ ∈ normalizer (U : Set G) :=
    mem_of_le_inf_conjugate hN (hU.to_le hEU) hE1 hEk
  have hRU : (R : Subgroup G) ≤ U := by
    intro y hy
    have h1 := (hk y).1 hy
    have h2 := (mem_normalizer_iff.1 hkN y).2
    rw [inv_inv] at h2
    exact h2 h1
  have hPeq : (Q : Subgroup L).map L.subtype = U ⊓ L :=
    le_antisymm (le_inf (hPR.trans hRU) (map_subtype_le _)) hUP
  rw [← hPeq]
  exact hPsyl

theorem inf_normalizer_eq {U E L : Subgroup G} (hU : IsPGroup 2 U)
    (hN : fusionStronglyEmbedded (normalizer (U : Set G)))
    (hEU : E ≤ U) (hEL : E ≤ L) (hE1 : E ≠ ⊥) :
    L ⊓ normalizer ((U ⊓ L : Subgroup G) : Set G) = L ⊓ normalizer (U : Set G) := by
  apply le_antisymm
  · rintro y ⟨hyL, hy⟩
    refine ⟨hyL, mem_of_le_inf_conjugate (X := U ⊓ L) hN hU.to_inf_left ?_ ?_⟩
    · exact fun h => hE1 (eq_bot_iff.2 fun e he => h ▸ (⟨hEU he, hEL he⟩ : e ∈ U ⊓ L))
    · intro z hz
      exact ⟨le_normalizer hz.1, mem_conjugate_iff.2
        (le_normalizer ((mem_normalizer_iff.1 hy z).1 hz).1)⟩
  · rintro y ⟨hyL, hy⟩
    refine ⟨hyL, mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · rintro ⟨hzU, hzL⟩
      exact ⟨(mem_normalizer_iff.1 hy z).1 hzU, L.mul_mem (L.mul_mem hyL hzL) (L.inv_mem hyL)⟩
    · rintro ⟨hzU, hzL⟩
      refine ⟨(mem_normalizer_iff.1 hy z).2 hzU, ?_⟩
      have h1 : z = y⁻¹ * (y * z * y⁻¹) * y := by group
      rw [h1]
      exact L.mul_mem (L.mul_mem (L.inv_mem hyL) hzL) hyL

omit [Finite G] in
theorem inf_normalizer_subgroupOf {X L : Subgroup G} (hXL : X ≤ L) :
    (L ⊓ normalizer (X : Set G)).subgroupOf L =
      normalizer ((X.subgroupOf L : Subgroup L) : Set L) := by
  ext y
  rw [mem_subgroupOf, mem_normalizer_iff]
  constructor
  · rintro ⟨-, hy⟩ z
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.1 hy z
  · intro hy
    refine ⟨y.2, mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · intro hz
      have h1 := (hy ⟨z, hXL hz⟩).1 hz
      exact h1
    · intro hz
      have hzL : z ∈ L := by
        have h1 : z = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * y := by group
        rw [h1]
        exact L.mul_mem (L.mul_mem (L.inv_mem y.2) (hXL hz)) y.2
      exact (hy ⟨z, hzL⟩).2 hz

omit [Finite G] in
theorem fusionStronglyEmbedded_subgroupOf {L P : Subgroup G} (hPL : P ≤ L) (hne : ¬ L ≤ P)
    (heven : Even (Nat.card P))
    (hodd : ∀ y ∈ L, y ∉ P → Odd (Nat.card ↥(P ⊓ conjugate P y))) :
    fusionStronglyEmbedded (P.subgroupOf L) := by
  refine ⟨fun h => hne (subgroupOf_eq_top.1 h), ?_, fun y hy => ?_⟩
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv]
  · have hle : (P.subgroupOf L ⊓ (P.subgroupOf L).map (MulAut.conj y⁻¹).toMonoidHom).map
        L.subtype ≤ P ⊓ conjugate P y := by
      rintro _ ⟨z, ⟨hz1, w, hw, hwz⟩, rfl⟩
      refine ⟨hz1, mem_conjugate_iff.2 ?_⟩
      rw [← hwz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, coe_subtype, coe_mul,
        coe_inv]
      have h1 : (y : G) * ((y : G)⁻¹ * w * y) * (y : G)⁻¹ = w := by group
      rw [h1]
      exact hw
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Odd.of_dvd_nat (hodd y y.2 hy) h1

theorem eq_bot_of_four_group {R : Subgroup G} {e f : G}
    (he : e * e = 1) (hf : f * f = 1)
    (heR : e ∈ normalizer (R : Set G)) (hfR : f ∈ normalizer (R : Set G))
    (hfix : ∀ a ∈ ({e, f, e * f} : Set G), ∀ r ∈ R, a * r * a⁻¹ = r → r = 1) : R = ⊥ := by
  have hinv : ∀ a ∈ ({e, f} : Set G), a * a = 1 → a ∈ normalizer (R : Set G) →
      (∀ r ∈ R, a * r * a⁻¹ = r → r = 1) → ∀ r ∈ R, a * r * a⁻¹ = r⁻¹ := by
    intro a _ ha2 haR hfa
    let φ : R →* R := ((MulAut.conj a).toMonoidHom.comp R.subtype).codRestrict R fun r =>
      (mem_normalizer_iff.1 haR r).1 r.2
    have hφ : MonoidHom.FixedPointFree φ := fun r hr =>
      Subtype.ext (hfa r r.2 (congrArg Subtype.val hr))
    have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hφ2 : Function.Involutive φ := fun r => Subtype.ext (by
      change a * (a * (r : G) * a⁻¹) * a⁻¹ = r
      rw [ha1]
      calc a * (a * (r : G) * a) * a = (a * a) * r * (a * a) := by group
        _ = r := by rw [ha2, one_mul, mul_one])
    intro r hr
    have h1 := congrFun (hφ.coe_eq_inv_of_involutive hφ2) ⟨r, hr⟩
    exact congrArg Subtype.val h1
  have he' := hinv e (by simp) he heR (hfix e (by simp))
  have hf' := hinv f (by simp) hf hfR (hfix f (by simp))
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  refine hfix (e * f) (by simp) r hr ?_
  have hfr : f * r * f⁻¹ ∈ R := by rw [hf' r hr]; exact R.inv_mem hr
  calc e * f * r * (e * f)⁻¹ = e * (f * r * f⁻¹) * e⁻¹ := by group
    _ = (e * r * e⁻¹)⁻¹ := by rw [hf' r hr]; group
    _ = r := by rw [he' r hr, inv_inv]

theorem oddCore_eq_bot_of_four_group {L E : Subgroup G} (hEL : E ≤ L) [IsElementaryAbelian 2 E]
    (hE4 : 4 ≤ Nat.card E) (hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G))) :
    oddCore L = ⊥ := by
  set R : Subgroup G := (oddCore L).map L.subtype with hRdef
  have hRodd : Odd (Nat.card R) := by
    rw [hRdef, Subgroup.card_map_of_injective L.subtype_injective]
    exact odd_card_oddCore
  have hRn : ∀ l ∈ L, l ∈ normalizer (R : Set G) := by
    intro l hl
    have hn : (oddCore L).Normal := by
      unfold oddCore
      exact sSup_normal _ fun _ h => h.1
    refine mem_normalizer_iff.2 fun r => ⟨?_, ?_⟩
    · rintro ⟨r', hr', rfl⟩
      exact ⟨⟨l, hl⟩ * r' * ⟨l, hl⟩⁻¹, hn.conj_mem r' hr' _, rfl⟩
    · rintro ⟨r', hr', hr'r⟩
      have hrL : r ∈ L := by
        have h1 : r = l⁻¹ * (l * r * l⁻¹) * l := by group
        rw [h1, ← hr'r]
        exact L.mul_mem (L.mul_mem (L.inv_mem hl) r'.2) hl
      refine ⟨⟨r, hrL⟩, ?_, rfl⟩
      have h1 := hn.conj_mem r' hr' ⟨l, hl⟩⁻¹
      have h2 : (⟨l, hl⟩ : L)⁻¹ * r' * (⟨l, hl⟩⁻¹)⁻¹ = ⟨r, hrL⟩ := Subtype.ext (by
        simp only [coe_mul, coe_inv, inv_inv]
        rw [show (r' : G) = l * r * l⁻¹ from hr'r]
        group)
      rw [h2] at h1
      exact h1
  have hfix : ∀ a ∈ E, a ≠ 1 → ∀ r ∈ R, a * r * a⁻¹ = r → r = 1 := by
    intro a ha ha1 r hr har
    have hrc : r ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc r * a = a * r * a⁻¹ * a := by rw [har]
        _ = a * r := by group
    obtain ⟨k, hk⟩ := hC a ha ha1 ⟨r, hrc⟩
    exact eq_one_of_mem_odd hRodd hr (k := k) (congrArg Subtype.val hk)
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  obtain ⟨e, f, he, hf, he1, hf1, hef⟩ : ∃ e f : G, e ∈ E ∧ f ∈ E ∧ e ≠ 1 ∧ f ≠ 1 ∧ e ≠ f := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set G) ⊆ {1} ∪ {x | x ∈ E ∧ x ≠ 1} := fun x hx => by
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra h
      push Not at h
      have : E = ⊥ := eq_bot_iff.2 fun x hx => h x hx
      rw [this, Subgroup.card_bot] at hE4
      omega
    have hEsub : (E : Set G) ⊆ {1, e} := fun x hx => by
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr (hcon e x he hx he1 h).symm
    have hcard := Set.ncard_le_ncard hEsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at hcard
    have h2 := Set.ncard_insert_le (1 : G) {e}
    rw [Set.ncard_singleton] at h2
    omega
  have hmem : e * f ∈ E := E.mul_mem he hf
  have hef1 : e * f ≠ 1 := by
    intro h
    apply hef
    calc e = e * (f * f) := by rw [hE2 f hf, mul_one]
      _ = e * f * f := by group
      _ = f := by rw [h, one_mul]
  have hR : R = ⊥ := eq_bot_of_four_group (hE2 e he) (hE2 f hf)
    (hRn e (hEL he)) (hRn f (hEL hf)) (by
      rintro a ha r hr har
      rcases ha with rfl | rfl | rfl
      · exact hfix _ he he1 r hr har
      · exact hfix _ hf hf1 r hr har
      · exact hfix _ hmem hef1 r hr har)
  exact (map_eq_bot_iff_of_injective _ L.subtype_injective).1 hR

omit [Finite G] in
theorem le_of_normal_of_odd_index [Finite G] {N X : Subgroup G} (hN : N.Normal)
    (hodd : Odd N.index) (hX : IsPGroup 2 X) : X ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk x : G ⧸ N) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk x : G ⧸ N) ∣ Nat.card (G ⧸ N) := orderOf_dvd_natCard _
  rw [← Subgroup.index_eq_card] at h2
  have hcop : Nat.Coprime (2 ^ k) N.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem fusionIsBenderGroup_of_r1Full {L : Type*} [Group L] [Finite L] (hR : R1Full L)
    (hO : oddCore L = ⊥) (htop : ∀ N : Subgroup L, N.Normal → Odd N.index → N = ⊤) :
    fusionIsBenderGroup L := by
  obtain ⟨⟨N, hN, -, hodd, hmodel⟩, -⟩ := hR
  have hNtop : N = ⊤ := htop N hN hodd
  have hsub : (oddCore L).subgroupOf N = ⊥ := by rw [hO, bot_subgroupOf]
  let e : L ≃* (N ⧸ (oddCore L).subgroupOf N) :=
    ((Subgroup.topEquiv (G := L)).symm.trans (MulEquiv.subgroupCongr hNtop.symm)).trans
      ((QuotientGroup.quotientBot (G := N)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hsub.symm))
  exact rankOneModel_of_equiv e hmodel

omit [Finite G] in
theorem kerIn_eq_bot_of_odd_inter {L P : Subgroup G} (hPL : P ≤ L) (hne : ¬ L ≤ P)
    (hodd : ∀ y ∈ L, y ∉ P → Odd (Nat.card ↥(P ⊓ conjugate P y))) (hO : oddCore L = ⊥) :
    kerIn P L = ⊥ := by
  have hCP : kerIn P L ≤ P := fun c hc => by simpa using hc 1 (one_mem L)
  have hCL : kerIn P L ≤ L := hCP.trans hPL
  obtain ⟨y, hyL, hyP⟩ := IsConcreteLE.not_le_iff_exists.1 hne
  have hCy : kerIn P L ≤ P ⊓ conjugate P y := fun c hc => ⟨hCP hc, mem_conjugate_iff.2 (hc y hyL)⟩
  have hCodd : Odd (Nat.card (kerIn P L)) := Odd.of_dvd_nat (hodd y hyL hyP) (card_dvd_of_le hCy)
  have hCn : ((kerIn P L).subgroupOf L).Normal := ⟨fun c hc l => by
    rw [mem_subgroupOf] at hc ⊢
    intro b hb
    have h1 := hc (b * l) (L.mul_mem hb l.2)
    have h2 : b * ((l : G) * c * (l : G)⁻¹) * b⁻¹ = b * l * c * (b * l)⁻¹ := by group
    simp only [coe_mul, coe_inv]
    rw [h2]
    exact h1⟩
  have hle := le_oddCore_of_normal hCn
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hCL).toEquiv])
  rw [hO, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro c hc
  have h1 : (⟨c, hCL hc⟩ : L) ∈ (kerIn P L).subgroupOf L := hc
  rw [hle, mem_bot] at h1
  rw [mem_bot]
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem inSubgroup_pCore_eq_bot_of_kerIn {L P S : Subgroup G} (hSL : IsSylowOf 2 S L)
    (hSP : S ≤ P) (hcore : kerIn P L = ⊥) : inSubgroup (pCore 2) L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hSL
  have hOQ : pCore 2 L ≤ (Q : Subgroup L) :=
    (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal Q
  have hn : (pCore 2 L).Normal := pCore_normal
  rw [eq_bot_iff, ← hcore]
  rintro _ ⟨o, ho, rfl⟩ b hb
  have h1 : (⟨b, hb⟩ : L) * o * (⟨b, hb⟩ : L)⁻¹ ∈ pCore 2 L := hn.conj_mem o ho _
  have h2 : (((⟨b, hb⟩ : L) * o * (⟨b, hb⟩ : L)⁻¹ : L) : G) ∈ S := by
    rw [← hQ]
    exact ⟨_, hOQ h1, rfl⟩
  exact hSP (by simpa using h2)

theorem inSubgroup_pCore_eq_of_isSylowOf {L P S : Subgroup G} (hSL : IsSylowOf 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hPN : P ≤ normalizer (S : Set G)) :
    inSubgroup (pCore 2) P = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · obtain ⟨S', hS'⟩ := hSL.of_le hSP hPL
    rw [← hS']
    exact map_mono ((pCore_isPGroup (p := 2) (G := ↥P)).le_sylow_of_normal S')
  · exact le_inSubgroup_pCore hSP hPN hSL.isPGroup

theorem exists_mem_sup_conjugate {N E : Subgroup G} (hN : fusionStronglyEmbedded N)
    (hEN : E ≤ N) (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥) : ∃ x : G, x ∉ N ∧ x ∈ E ⊔ conjugate E x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x : G, x ∉ N := by
    by_contra h
    push Not at h
    exact hN.1 (eq_top_iff.2 fun x _ => h x)
  obtain ⟨x₁, hx₁, hmin⟩ := Set.exists_min_image {x : G | x ∉ N}
    (fun x => Nat.card ↥(E ⊔ conjugate E x)) (Set.toFinite _) ⟨x₀, hx₀⟩
  obtain ⟨y, hyL, hyN⟩ := IsConcreteLE.not_le_iff_exists.1 fun h : E ⊔ conjugate E x₁ ≤ N =>
    conjugate_not_le hN hEN hE hE1 hx₁ (le_sup_right.trans h)
  have hle : E ⊔ conjugate E y ≤ E ⊔ conjugate E x₁ := by
    refine sup_le le_sup_left fun z hz => ?_
    have h1 := mem_conjugate_iff.1 hz
    have h2 : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [h2]
    exact (E ⊔ conjugate E x₁).mul_mem ((E ⊔ conjugate E x₁).mul_mem
      ((E ⊔ conjugate E x₁).inv_mem hyL) (le_sup_left (a := E) h1)) hyL
  have heq : E ⊔ conjugate E y = E ⊔ conjugate E x₁ :=
    Subgroup.eq_of_le_of_card_ge hle (hmin y hyN)
  exact ⟨y, hyN, heq ▸ hyL⟩

theorem bender_pair_props
    {U E : Subgroup G} (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hN : fusionStronglyEmbedded (normalizer (U : Set G)))
    (hC : ∀ e ∈ E, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set G)))
    (hEU : E ≤ U) [IsElementaryAbelian 2 E] (hE4 : 4 ≤ Nat.card E) {x : G}
    (hx : x ∉ normalizer (U : Set G)) :
    fusionIsBenderGroup ↥(E ⊔ conjugate E x) ∧
      IsSylowOf 2 (U ⊓ (E ⊔ conjugate E x)) (E ⊔ conjugate E x) ∧
      ((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)).subgroupOf (E ⊔ conjugate E x) =
        normalizer (((U ⊓ (E ⊔ conjugate E x)).subgroupOf (E ⊔ conjugate E x) :
          Subgroup ↥(E ⊔ conjugate E x)) : Set ↥(E ⊔ conjugate E x)) ∧
      fusionStronglyEmbedded
        (((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)).subgroupOf (E ⊔ conjugate E x)) ∧
      kerIn ((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)) (E ⊔ conjugate E x) = ⊥ ∧
      inSubgroup (pCore 2) (E ⊔ conjugate E x) = ⊥ ∧
      inSubgroup (pCore 2) ((E ⊔ conjugate E x) ⊓ normalizer (U : Set G)) =
        U ⊓ (E ⊔ conjugate E x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (U : Set G) with hNdef
  set L := E ⊔ conjugate E x with hLdef
  set P := L ⊓ N with hPdef
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hE4
    omega
  have hEN : E ≤ N := hEU.trans le_normalizer
  have hEL : E ≤ L := le_sup_left
  have hneP : ¬ L ≤ P := fun h =>
    conjugate_not_le hN hEN hE2 hE1 hx
      ((le_sup_right : conjugate E x ≤ L).trans (h.trans inf_le_right))
  have hPL : P ≤ L := inf_le_left
  have hodd : ∀ y ∈ L, y ∉ P → Odd (Nat.card ↥(P ⊓ conjugate P y)) := by
    intro y hyL hyP
    have hyN : y ∉ N := fun h => hyP ⟨hyL, h⟩
    exact Odd.of_dvd_nat (hN.2.2 y hyN) (card_dvd_of_le (inf_le_inf inf_le_right
      (map_mono inf_le_right)))
  have heven : Even (Nat.card P) := by
    obtain ⟨m, hm⟩ := hE2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      omega
    exact even_iff_two_dvd.2 ((dvd_pow_self 2 hm0).trans
      (hm ▸ card_dvd_of_le (le_inf hEL hEN)))
  have hSE : fusionStronglyEmbedded (P.subgroupOf L) :=
    fusionStronglyEmbedded_subgroupOf hPL hneP heven hodd
  have hsyl : IsSylowOf 2 (U ⊓ L) L := isSylowOf_inf_of_stronglyEmbedded hU hUi hN hEU hEL hE1
  have hPeq : L ⊓ normalizer ((U ⊓ L : Subgroup G) : Set G) = P :=
    inf_normalizer_eq hU hN hEU hEL hE1
  have hnorm : P.subgroupOf L =
      normalizer (((U ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
    rw [← hPeq]
    exact inf_normalizer_subgroupOf inf_le_right
  have hO : oddCore L = ⊥ := oddCore_eq_bot_of_four_group hEL hE4 hC
  have hrank : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo L := by
    have hEab : IsElemAbelian 2 E :=
      ⟨inferInstance, fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy⟩
    exact CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective (inclusion hEL)
      (inclusion_injective hEL) (twoRankAtLeastTwo_of_elementary_card_ge_four E hEab hE4)
  have hR1 : R1Full L := rank_two_strongEmbedding_r1Full hrank (P.subgroupOf L) hSE
  have htop : ∀ N' : Subgroup L, N'.Normal → Odd N'.index → N' = ⊤ := by
    intro N' hN' hodd'
    have h1 : E.subgroupOf L ≤ N' := le_of_normal_of_odd_index hN' hodd' hE2.comap_subtype
    have h2 : (conjugate E x).subgroupOf L ≤ N' :=
      le_of_normal_of_odd_index hN' hodd' (hE2.map _).comap_subtype
    have h3 : E.subgroupOf L ⊔ (conjugate E x).subgroupOf L = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right]
      exact subgroupOf_self L
    rw [eq_top_iff, ← h3]
    exact sup_le h1 h2
  have hcore : kerIn P L = ⊥ := kerIn_eq_bot_of_odd_inter hPL hneP hodd hO
  have hSP : U ⊓ L ≤ P := le_inf inf_le_right (inf_le_left.trans le_normalizer)
  refine ⟨fusionIsBenderGroup_of_r1Full hR1 hO htop, hsyl, hnorm, hSE, hcore,
    inSubgroup_pCore_eq_bot_of_kerIn hsyl hSP hcore, ?_⟩
  exact inSubgroup_pCore_eq_of_isSylowOf hsyl hSP hPL (hPeq ▸ inf_le_right)

end BenderCore

end CFSG.Quasithin.H13.QRC
