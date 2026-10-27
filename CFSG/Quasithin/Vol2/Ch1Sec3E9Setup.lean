module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.Ch1Sec3

variable {G : Type} [Group G] [Finite G] {H S X P : Subgroup G}

section G

theorem pCoreOf_X_le (hS : IsSylowTwoOf S H) (hXH : X ≤ H) (hX : IsXi S X) :
    pCoreOf 2 X ≤ S :=
  pCoreOf_le_of_isSylowTwoOf hS hXH hX.2.1

omit [Finite G] in
theorem three_dvd_card_X (hPX : P ≤ X) (hP9 : Nat.card P = 9) : 3 ∣ Nat.card X :=
  (show (3 : ℕ) ∣ 9 by norm_num).trans (hP9 ▸ Subgroup.card_dvd_of_le hPX)

variable (hS : IsSylowTwoOf S H) (hXH : X ≤ H) (hX : IsXi S X)
  (h9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)

include hX h9 hPX hP3 hP9 in
theorem exp_of_setup : ∀ a ∈ P, a ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro a ha
  exact hX.pow_eq_one (by norm_num) (three_dvd_card_X hPX hP9)
    (isSylowIn_of_card_nine h9 hPX hP3 hP9) ha

include hS hXH hX h9 hPX hP3 hP9 in
theorem irr_of_setup : ∀ U : Subgroup G, U ≤ P →
    S ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hUP hNU
  have hSyl := isSylowIn_of_card_nine h9 hPX hP3 hP9
  have hpX := three_dvd_card_X hPX hP9
  have hΦ : frattiniIn P = ⊥ := by
    rw [(hX.frattiniIn_eq (by norm_num) hpX hSyl).1]
    exact commutator_eq_bot_of_card_nine hP9
  have h := (irreducible (pCoreOf_X_le hS hXH hX) hX (by norm_num) hpX hSyl).2 U
    (hΦ ▸ bot_le) hUP hNU
  rwa [hΦ] at h

include hS hXH hX h9 hPX hP3 hP9 in
theorem comm_of_setup : P = ⁅P, S ⊓ Subgroup.normalizer (P : Set G)⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact eq_commutator_normalizer (pCoreOf_X_le hS hXH hX) hS.2.1 hX
    (by norm_num) (three_dvd_card_X hPX hP9) (isSylowIn_of_card_nine h9 hPX hP3 hP9)

include hS hXH hX h9 hPX hP3 hP9 in
theorem frat_of_setup : S = pCoreOf 2 X ⊔ (S ⊓ Subgroup.normalizer (P : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact eq_pCoreOf_sup_normalizer (pCoreOf_X_le hS hXH hX) hX (by norm_num)
    (three_dvd_card_X hPX hP9) (isSylowIn_of_card_nine h9 hPX hP3 hP9)

include hX h9 hPX hP3 hP9 in
theorem sup_of_setup : pCoreOf 2 X ⊔ P = X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hX.pCoreOf_sup_eq (by norm_num) (three_dvd_card_X hPX hP9)
    (isSylowIn_of_card_nine h9 hPX hP3 hP9)

include hX h9 hPX hP3 hP9 in
theorem cl_of_setup : X = conjClosure P X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (hX.eq_conjClosure (by norm_num) (three_dvd_card_X hPX hP9)
    (isSylowIn_of_card_nine h9 hPX hP3 hP9)).1

include hS hXH hX h9 hPX hP3 hP9 in
theorem mul_subset : ∀ t ∈ S, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ S, t * x = y * s := by
  intro t ht x hx
  have hQS := pCoreOf_X_le hS hXH hX
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hPX.trans (le_normalizer_pCoreOf 2 X)
  have h1 : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hX.2.1 ht) x).mp (hPX hx)
  rw [← sup_of_setup hX h9 hPX hP3 hP9] at h1
  obtain ⟨o, ho, y, hy, he⟩ := (mem_sup_iff_of_le_normalizer hPQ).1 h1
  have ho' : y⁻¹ * o * y ∈ pCoreOf 2 X := by
    have := (Subgroup.mem_normalizer_iff.mp (hPQ (P.inv_mem hy)) o).mp ho
    simpa using this
  refine ⟨y, hy, y⁻¹ * o * y * t, S.mul_mem (hQS ho') ht, ?_⟩
  calc t * x = (t * x * t⁻¹) * t := by group
    _ = y * (y⁻¹ * o * y * t) := by rw [he]; group

end G

omit [Finite G] in
theorem modO2Image_le_normalizer {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    modO2Image H A ≤ Subgroup.normalizer (modO2Image H B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    fun a ha => Subgroup.le_normalizer_comap H.subtype (hAB ha)
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

omit [Finite G] in
theorem irr_modO2Image {P N : Subgroup G} (hPH : P ≤ H) (hNH : N ≤ H)
    (hNP : N ≤ Subgroup.normalizer (P : Set G))
    (hirr : ∀ U : Subgroup G, U ≤ P → N ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = P) :
    ∀ U : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), U ≤ modO2Image H P →
      modO2Image H N ≤ Subgroup.normalizer (U : Set (↥H ⧸ CFSG.pCore 2 ↥H)) →
      U = ⊥ ∨ U = modO2Image H P := by
  intro U hUP hNU
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  let V : Subgroup G := P ⊓ (U.comap π).map H.subtype
  have hVP : V ≤ P := inf_le_left
  have hmemV : ∀ a (ha : a ∈ H), a ∈ P → (a ∈ V ↔ π ⟨a, ha⟩ ∈ U) := by
    intro a ha haP
    constructor
    · rintro ⟨-, ⟨b, hb, hba⟩⟩
      have : b = ⟨a, ha⟩ := Subtype.ext hba
      rw [← this]
      exact hb
    · intro h
      exact ⟨haP, ⟨⟨a, ha⟩, h, rfl⟩⟩
  have hNV : N ≤ Subgroup.normalizer (V : Set G) := by
    intro n hn
    have hnH := hNH hn
    have key : ∀ m ∈ N, ∀ a ∈ V, m * a * m⁻¹ ∈ V := by
      intro m hm a haV
      have hmH := hNH hm
      have haH := hPH haV.1
      have hconjP : m * a * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hNP hm) a).mp haV.1
      refine (hmemV _ (hPH hconjP) hconjP).mpr ?_
      have hU := (hmemV a haH haV.1).mp haV
      have hmU : π ⟨m, hmH⟩ ∈ Subgroup.normalizer (U : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
        hNU ⟨⟨m, hmH⟩, hm, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hmU _).mp hU
      have e : π ⟨m * a * m⁻¹, hPH hconjP⟩ = π ⟨m, hmH⟩ * π ⟨a, haH⟩ * (π ⟨m, hmH⟩)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      rw [e]
      exact h2
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨key n hn a, fun h => ?_⟩
    have := key n⁻¹ (N.inv_mem hn) _ h
    simpa [mul_assoc] using this
  rcases hirr V hVP hNV with h | h
  · left
    refine eq_bot_iff.mpr fun u hu => ?_
    obtain ⟨⟨a, haH⟩, haP, rfl⟩ := hUP hu
    have haV : a ∈ V := (hmemV a haH haP).mpr hu
    rw [h, Subgroup.mem_bot] at haV
    subst haV
    exact Subgroup.mem_bot.mpr (map_one π)
  · right
    refine le_antisymm hUP fun u hu => ?_
    obtain ⟨⟨a, haH⟩, haP, rfl⟩ := hu
    have haV : a ∈ V := h ▸ haP
    exact (hmemV a haH haP).mp haV

section Bar

variable (hS : IsSylowTwoOf S H) (hXH : X ≤ H) (hX : IsXi S X)
  (h9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)

omit [Finite G] in
theorem sylow_bar (hS : IsSylowTwoOf S H) : IsSylowTwoOf (modO2Image H S) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)

include hXH hX h9 hPX hP3 hP9 in
theorem card_bar : Nat.card (modO2Image H P) = 9 := by
  rw [card_modO2Image (hPX.trans hXH) (inf_pCoreOf_eq_bot (exp_of_setup hX h9 hPX hP3 hP9)),
    hP9]

include hX h9 hPX hP3 hP9 in
theorem exp_bar : ∀ x ∈ modO2Image H P, x ^ 3 = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  have h1 : y ^ 3 = 1 := Subtype.ext (by simpa using exp_of_setup hX h9 hPX hP3 hP9 _ hy)
  rw [← map_pow, h1, map_one]

include hS hXH hX h9 hPX hP3 hP9 in
theorem mul_bar : ∀ t ∈ modO2Image H S, ∀ x ∈ modO2Image H P,
    ∃ y ∈ modO2Image H P, ∃ s ∈ modO2Image H S, t * x = y * s := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, s, hs, he⟩ := mul_subset hS hXH hX h9 hPX hP3 hP9 t ht x hx
  have hyH : y ∈ H := hPX.trans hXH hy
  have hsH : s ∈ H := hS.1 hs
  refine ⟨_, ⟨⟨y, hyH⟩, hy, rfl⟩, _, ⟨⟨s, hsH⟩, hs, rfl⟩, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext he

include hS hXH hX h9 hPX hP3 hP9 in
theorem sup_bar : modO2Image H S ≤
    modO2Image H (pCoreOf 2 X) ⊔ modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) := by
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (t : G) ∈ pCoreOf 2 X ⊔ (S ⊓ Subgroup.normalizer (P : Set G)) := by
    rw [← frat_of_setup hS hXH hX h9 hPX hP3 hP9]
    exact ht
  have hNQ : S ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    inf_le_left.trans (hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X))
  obtain ⟨o, ho, n, hn, he⟩ := (mem_sup_iff_of_le_normalizer hNQ).1 ht'
  have hoH : o ∈ H := (pCoreOf_le 2 X).trans hXH ho
  have hnH : n ∈ H := hS.1 hn.1
  have e : t = ⟨o, hoH⟩ * ⟨n, hnH⟩ := Subtype.ext he
  rw [e, map_mul]
  exact Subgroup.mul_mem_sup ⟨⟨o, hoH⟩, ho, rfl⟩ ⟨⟨n, hnH⟩, hn, rfl⟩

include hXH hX h9 hPX hP3 hP9 in
theorem oX_bar : ∀ K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), K.Normal → modO2Image H P ≤ K →
    modO2Image H (pCoreOf 2 X) ≤ K := by
  intro K hK hPK
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  let K' : Subgroup G := (K.comap π).map H.subtype
  have hPK' : P ≤ K' := fun a ha => ⟨⟨a, hPX.trans hXH ha⟩, hPK ⟨_, ha, rfl⟩, rfl⟩
  have hXK' : X ≤ K' := by
    rw [cl_of_setup hX h9 hPX hP3 hP9]
    refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨w, hw, hwz⟩ := hPK' hz
    have hhH : h ∈ H := hXH hh
    refine ⟨⟨h, hhH⟩ * w * ⟨h, hhH⟩⁻¹, ?_, ?_⟩
    · show π (⟨h, hhH⟩ * w * ⟨h, hhH⟩⁻¹) ∈ K
      rw [map_mul, map_mul, map_inv]
      exact hK.conj_mem _ hw _
    · have hwz' : (w : G) = z := hwz
      simp [hwz']
  rintro _ ⟨o, ho, rfl⟩
  obtain ⟨w, hw, hwo⟩ := hXK' ((pCoreOf_le 2 X) ho)
  have : w = o := Subtype.ext hwo
  rw [← this]
  exact hw

include hS hXH hX h9 hPX hP3 hP9 in
theorem comm_bar : modO2Image H P ≤ commutator (↥H ⧸ CFSG.pCore 2 ↥H) := by
  set N := S ⊓ Subgroup.normalizer (P : Set G)
  have hPH : P ≤ H := hPX.trans hXH
  have hNH : N ≤ H := inf_le_left.trans hS.1
  have hP₁ : (P.subgroupOf H).map H.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPH
  have hN₁ : (N.subgroupOf H).map H.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNH
  have h1 : P.subgroupOf H ≤ ⁅P.subgroupOf H, N.subgroupOf H⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_commutator, hP₁,
      hN₁]
    exact (comm_of_setup hS hXH hX h9 hPX hP3 hP9).le
  calc modO2Image H P ≤ ⁅P.subgroupOf H, N.subgroupOf H⁆.map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := Subgroup.map_mono h1
    _ = ⁅modO2Image H P, modO2Image H N⁆ := Subgroup.map_commutator _ _ _
    _ ≤ commutator (↥H ⧸ CFSG.pCore 2 ↥H) := Subgroup.commutator_mono le_top le_top

include hS hXH hX h9 hPX hP3 hP9 in
theorem le_normalizer_of_normal (hn : (modO2Image H P).Normal) :
    H ≤ Subgroup.normalizer (X : Set G) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hPH : P ≤ H := hPX.trans hXH
  set B := pCoreOf 2 H with hB
  set M := B ⊔ P with hM
  have hconjP : ∀ h ∈ H, ∀ z ∈ P, h * z * h⁻¹ ∈ M := by
    intro h hh z hz
    have hmem : π (⟨h, hh⟩ * ⟨z, hPH hz⟩ * (⟨h, hh⟩ : H)⁻¹) ∈ modO2Image H P := by
      rw [map_mul, map_mul, map_inv]
      exact hn.conj_mem _ ⟨_, hz, rfl⟩ _
    have hzH : h * z * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh (hPH hz)) (H.inv_mem hh)
    have := mem_sup_of_mem_modO2Image hzH (by convert hmem using 1)
    rw [sup_comm] at this
    exact this
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := by
    have key : ∀ {h : G}, h ∈ H → M.map (MulAut.conj h).toMonoidHom ≤ M := by
      intro h hh
      rw [hM, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [map_conj_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hh)]
        exact le_sup_left
      · rintro _ ⟨z, hz, rfl⟩
        exact hconjP h hh z hz
    exact fun h hh => mem_normalizer_of_map_conj_le (key hh) (key (H.inv_mem hh))
  have hXM : X ≤ M := by
    rw [cl_of_setup hX h9 hPX hP3 hP9]
    exact conjClosure_le fun x hx z hz => hconjP x (hXH hx) z hz
  have hBX : B ⊔ X = M := le_antisymm (sup_le le_sup_left hXM) (sup_le_sup_left hPX B)
  have hBS : B ≤ S := le_of_isSylowTwoOf hS le_sup_left
    (sup_le hS.1 (pCoreOf_le 2 H)) (IsPGroup.to_sup_of_normal_right' hS.2.1
      (pCoreOf_isPGroup 2 H) (hS.1.trans (le_normalizer_pCoreOf 2 H))) |> le_trans le_sup_right
  have h5 : oTwoUpper (B ⊔ X) = X :=
    oTwoUpper_sup_eq_of_isPGroup (pCoreOf_isPGroup 2 H) (hBS.trans hX.2.1) hX.1
  calc H ≤ Subgroup.normalizer (oTwoUpper M : Set G) :=
        hHM.trans (normalizer_le_normalizer_oTwoUpper M)
    _ = Subgroup.normalizer (X : Set G) := by rw [← hBX, h5]

include hS hXH hX h9 hPX hP3 hP9 in
theorem autCyclic_of_bar
    (h : EmptyFaithfulMultiple.AutCyclic (modO2Image H S) (modO2Image H P)) :
    EmptyFaithfulMultiple.AutCyclic S P := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hPH : P ≤ H := hPX.trans hXH
  have hexp := exp_of_setup hX h9 hPX hP3 hP9
  have hexpb := exp_bar (H := H) hX h9 hPX hP3 hP9
  set Nb := modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) with hNb
  set Ob := modO2Image H (pCoreOf 2 X) with hOb
  set Pb := modO2Image H P with hPb
  have hNO : Nb ≤ Subgroup.normalizer (Ob : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer
      (inf_le_left.trans (hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X)))
  have hPO : Pb ≤ Subgroup.normalizer (Ob : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer (hPX.trans (le_normalizer_pCoreOf 2 X))
  have hO2 : IsPGroup 2 Ob := (pCoreOf_isPGroup 2 X).of_equiv
      (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 X).trans hXH)).symm |>.map _
  have hPOb : Pb ⊓ Ob = ⊥ := by
    have hP3b : IsPGroup 3 Pb := fun x => ⟨1, Subtype.ext (by simpa using hexpb x x.2)⟩
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Pb Ob hP3b hO2).eq_bot
  obtain ⟨cb, ⟨hcbT, hcbN⟩, hcb⟩ := h
  obtain ⟨ob, hob, nb, hnb, hcbe⟩ := (mem_sup_iff_of_le_normalizer hNO).1
    (sup_bar hS hXH hX h9 hPX hP3 hP9 hcbT)
  obtain ⟨c, hc, rfl⟩ := hnb
  replace hcbe : cb = ob * π c := hcbe
  have hcN : (c : G) ∈ S ⊓ Subgroup.normalizer (P : Set G) := hc
  have hnbN : π c ∈ Subgroup.normalizer (Pb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_le_normalizer inf_le_right ⟨c, hc, rfl⟩
  have hobN : ob ∈ Subgroup.normalizer (Pb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have e : ob = cb * (π c)⁻¹ := by rw [hcbe]; group
    rw [e]
    exact Subgroup.mul_mem _ hcbN (Subgroup.inv_mem _ hnbN)
  have hobC : ∀ x ∈ Pb, ob * x * ob⁻¹ = x := by
    intro x hx
    have h1 : ob * x * ob⁻¹ * x⁻¹ ∈ Pb :=
      Pb.mul_mem ((Subgroup.mem_normalizer_iff.mp hobN x).mp hx) (Pb.inv_mem hx)
    have h2 : ob * x * ob⁻¹ * x⁻¹ ∈ Ob := by
      have : x * ob⁻¹ * x⁻¹ ∈ Ob :=
        (Subgroup.mem_normalizer_iff.mp (hPO hx) ob⁻¹).mp (Ob.inv_mem hob)
      have e : ob * x * ob⁻¹ * x⁻¹ = ob * (x * ob⁻¹ * x⁻¹) := by group
      rw [e]
      exact Ob.mul_mem hob this
    have h3 : ob * x * ob⁻¹ * x⁻¹ ∈ Pb ⊓ Ob := ⟨h1, h2⟩
    rw [hPOb, Subgroup.mem_bot] at h3
    calc ob * x * ob⁻¹ = ob * x * ob⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [h3, one_mul]
  have hpow : ∀ k : ℕ, ∀ x ∈ Pb, cb ^ k * x * (cb ^ k)⁻¹ = π c ^ k * x * (π c ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hxc : π c * x * (π c)⁻¹ ∈ Pb := (Subgroup.mem_normalizer_iff.mp hnbN x).mp hx
      calc cb ^ (k + 1) * x * (cb ^ (k + 1))⁻¹ = cb ^ k * (cb * x * cb⁻¹) * (cb ^ k)⁻¹ := by
            group
        _ = cb ^ k * (π c * x * (π c)⁻¹) * (cb ^ k)⁻¹ := by
            rw [hcbe]
            congr 2
            calc ob * π c * x * (ob * π c)⁻¹ = ob * (π c * x * (π c)⁻¹) * ob⁻¹ := by group
              _ = π c * x * (π c)⁻¹ := hobC _ hxc
        _ = π c ^ k * (π c * x * (π c)⁻¹) * (π c ^ k)⁻¹ := ih _ hxc
        _ = π c ^ (k + 1) * x * (π c ^ (k + 1))⁻¹ := by group
  refine ⟨c, hcN, fun s hs => ?_⟩
  have hsH : s ∈ H := hS.1 hs.1
  have hsb : π ⟨s, hsH⟩ ∈ modO2Image H S ⊓
      Subgroup.normalizer (Pb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    ⟨⟨⟨s, hsH⟩, hs.1, rfl⟩, modO2Image_le_normalizer inf_le_right ⟨⟨s, hsH⟩, hs, rfl⟩⟩
  obtain ⟨k, hk⟩ := hcb _ hsb
  refine ⟨k, fun x hx => ?_⟩
  have hxH : x ∈ H := hPH hx
  have h1 : s * x * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx
  have hck : (c : G) ^ k ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.pow_mem _ hcN.2 k
  have h2 : (c : G) ^ k * x * ((c : G) ^ k)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hck x).mp hx
  refine eq_of_mk_eq (inf_pCoreOf_eq_bot hexp) h1 h2 (hPH h1) (hPH h2) ?_
  have e1 : π ⟨s * x * s⁻¹, hPH h1⟩ = π ⟨s, hsH⟩ * π ⟨x, hxH⟩ * (π ⟨s, hsH⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have e2 : π ⟨(c : G) ^ k * x * ((c : G) ^ k)⁻¹, hPH h2⟩ =
      π c ^ k * π ⟨x, hxH⟩ * (π c ^ k)⁻¹ := by
    rw [← map_pow, ← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [e1, e2, hk _ ⟨⟨x, hxH⟩, hx, rfl⟩, hpow k _ ⟨⟨x, hxH⟩, hx, rfl⟩]

end Bar

end CFSG.Quasithin.P134
