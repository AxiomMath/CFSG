module

public import CFSG.Quasithin.EmptyFaithful.E111L2A
public import CFSG.Quasithin.EmptyFaithful.E111RSub
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsDihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem sub_dihedral (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {D T : Subgroup G}
    (hD : IsPSL 2 p 1 ↥D) (hTD : IsSylowIn 2 (T ⊓ D) D) :
    ∃ m, 2 ≤ m ∧ Nonempty (↥(T ⊓ D) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have hS : IsSylowIn 2 ((T ⊓ D).subgroupOf D) ⊤ := by
    have := (E1.isSylowIn_subgroupOf_iff (inf_le_right : T ⊓ D ≤ D) le_rfl).mpr hTD
    rwa [Subgroup.subgroupOf_self] at this
  obtain ⟨m, hm, ⟨eP⟩⟩ := sylow_dihedral_of_equiv e (by omega) hp8 hS
  exact ⟨m, hm, ⟨(Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans eP⟩⟩

theorem central_unique {P : Subgroup G} {m : ℕ} (hm : 2 ≤ m) (eP : ↥P ≃* DihedralGroup (2 ^ m))
    {z z' : G} (hz : z ∈ P) (hz' : z' ∈ P) (hz1 : z ≠ 1) (hz'1 : z' ≠ 1)
    (hzc : ∀ x ∈ P, z * x = x * z) (hz'c : ∀ x ∈ P, z' * x = x * z') : z = z' := by
  have hcen : ∀ y (hy : y ∈ P), (∀ x ∈ P, y * x = x * y) →
      eP ⟨y, hy⟩ ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
    intro y hy hyc
    rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨x, rfl⟩ := eP.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc x x.2).symm
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have heven : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hcard := CFSG.ComponentClassification.AutL2Facts.card_center_dihedral h4 heven
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center (DihedralGroup (2 ^ m))))).mp
    hcard
  have hne : ∀ y (hy : y ∈ P), y ≠ 1 → eP ⟨y, hy⟩ ≠ 1 := by
    intro y hy hy1 h
    apply hy1
    have := eP.injective (h.trans (map_one eP).symm)
    exact congrArg Subtype.val this
  have e1 := hc ⟨_, hcen z hz hzc⟩ (fun h => hne z hz hz1 (congrArg Subtype.val h))
  have e2 := hc ⟨_, hcen z' hz' hz'c⟩ (fun h => hne z' hz' hz'1 (congrArg Subtype.val h))
  have e3 : eP ⟨z, hz⟩ = eP ⟨z', hz'⟩ := congrArg Subtype.val (e1.trans e2.symm)
  exact congrArg Subtype.val (eP.injective e3)

theorem eq_of_le_of_isPGroup [Finite G] {P Q D : Subgroup G} (hP : IsSylowIn 2 P D)
    (hPQ : P ≤ Q) (hQD : Q ≤ D) (hQ : IsPGroup 2 Q) : P = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hidx := Subgroup.relIndex_mul_relIndex P Q D hPQ hQD
  have h1 : P.relIndex Q = 1 := by
    have hdvd : P.relIndex Q ∣ Nat.card Q := (P.subgroupOf Q).index_dvd_card
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ hdvd) with ⟨j, -, hj⟩
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hP.not_dvd_relIndex
      rw [← hidx, hj, pow_succ]
      exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  exact le_antisymm hPQ (Subgroup.relIndex_eq_one.mp h1)


theorem sub_centralizer (hp7 : 7 ≤ p) {D V : Subgroup G} (hD : IsPSL 2 p 1 ↥D) (hVD : V ≤ D)
    (hV : IsKleinFour ↥V) : Subgroup.centralizer (V : Set G) ⊓ D = V := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have hV' : IsKleinFour ↥(V.subgroupOf D) :=
    isKleinFour_of_equiv (Subgroup.subgroupOfEquivOfLe hVD) hV
  have hc := centralizer_kleinFour_of_equiv e (by omega) hV'
  apply le_antisymm
  · rintro x ⟨hx, hxD⟩
    have hx' : (⟨x, hxD⟩ : ↥D) ∈ Subgroup.centralizer ((V.subgroupOf D : Subgroup ↥D) : Set ↥D) :=
      (E111R.mem_centralizer_subgroupOf_iff hVD).mpr hx
    rw [hc] at hx'
    exact hx'
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨?_, hVD hv⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact kleinFour_comm hV hw hv

theorem sub_normalizer_eq {D V : Subgroup G} (hVD : V ≤ D) :
    Subgroup.normalizer ((V.subgroupOf D : Subgroup ↥D) : Set ↥D) =
      (Subgroup.normalizer (V : Set G) ⊓ D).subgroupOf D := by
  ext k
  rw [E111R.mem_normalizer_subgroupOf_iff, Subgroup.mem_subgroupOf, inf_eq_left.mpr hVD]
  exact ⟨fun h => ⟨h, k.2⟩, fun h => h.1⟩

theorem sub_card_normalizer [Finite G] (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    {D V : Subgroup G} (hD : IsPSL 2 p 1 ↥D) (hVD : V ≤ D) (hV : IsKleinFour ↥V) :
    Nat.card ↥(Subgroup.normalizer (V : Set G) ⊓ D) = 24 := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have hV' : IsKleinFour ↥(V.subgroupOf D) :=
    isKleinFour_of_equiv (Subgroup.subgroupOfEquivOfLe hVD) hV
  have h24 := card_normalizer_of_equiv e hp7 hp8 hV'
  rw [sub_normalizer_eq hVD] at h24
  rw [← h24]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem sub_moves [Finite G] (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {D V : Subgroup G}
    (hD : IsPSL 2 p 1 ↥D) (hVD : V ≤ D) (hV : IsKleinFour ↥V) {z : G} (hzV : z ∈ V)
    (hz1 : z ≠ 1) : ∃ g ∈ Subgroup.normalizer (V : Set G) ⊓ D, g * z ≠ z * g := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have hV' : IsKleinFour ↥(V.subgroupOf D) :=
    isKleinFour_of_equiv (Subgroup.subgroupOfEquivOfLe hVD) hV
  have hsurj := normalizer_surjective_of_equiv e hp7 hp8 hV'
  have hn := CFSG.Quasithin.E22L2.not_normalizer_le_centralizer hV' hsurj
    (z := ⟨z, hVD hzV⟩) (Subgroup.mem_subgroupOf.mpr hzV)
    (fun h => hz1 (congrArg Subtype.val h))
  obtain ⟨k, hk, hkz⟩ : ∃ k ∈ Subgroup.normalizer ((V.subgroupOf D : Subgroup ↥D) : Set ↥D),
      k ∉ Subgroup.centralizer ({⟨z, hVD hzV⟩} : Set ↥D) := by
    by_contra hall
    push Not at hall
    exact hn fun k hk => hall k hk
  refine ⟨k, ?_, ?_⟩
  · rw [sub_normalizer_eq hVD, Subgroup.mem_subgroupOf] at hk
    exact hk
  · intro h
    apply hkz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h

theorem sub_og [Finite G] (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {D T L : Subgroup G}
    (hD : IsPSL 2 p 1 ↥D) (hTD : IsSylowIn 2 (T ⊓ D) D) {m : ℕ} (hm : 2 ≤ m)
    (eP : ↥(T ⊓ D) ≃* DihedralGroup (2 ^ m)) {z : G} (hz : z ∈ T ⊓ D) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ T ⊓ D, z * x = x * z) (hTL : T ⊓ D ≤ L) (hLD : L ≤ D) :
    L = D ∨ L ≤ Subgroup.centralizer ({z} : Set G) ∨
      ∃ W : Subgroup G, W ≤ T ⊓ D ∧ IsKleinFour ↥W ∧
        L = Subgroup.normalizer (W : Set G) ⊓ D := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have eP' : ↥((T ⊓ D).subgroupOf D) ≃* DihedralGroup (2 ^ m) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_right).trans eP
  have hzc' : ∀ x ∈ (T ⊓ D).subgroupOf D, (⟨z, hz.2⟩ : ↥D) * x = x * ⟨z, hz.2⟩ :=
    fun x hx => Subtype.ext (hzc x hx)
  have hz2' : orderOf (⟨z, hz.2⟩ : ↥D) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  rcases og_of_equiv e (by omega) hm eP' (Subgroup.subgroupOf_mono D hTL)
      (Subgroup.mem_subgroupOf.mpr hz) hz2' hzc' with h | h | h
  · left
    refine le_antisymm hLD fun x hx => ?_
    have : (⟨x, hx⟩ : ↥D) ∈ L.subgroupOf D := h ▸ Subgroup.mem_top _
    exact this
  · right; left
    intro x hx
    have := h (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hLD hx⟩ : ↥D) ∈ L.subgroupOf D)
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    exact congrArg Subtype.val this
  · right; right
    obtain ⟨eH⟩ := h
    obtain ⟨W', hW'H, hW', hHN⟩ := exists_normal_kleinFour_of_perm4 eH
    set W : Subgroup G := W'.map D.subtype with hWdef
    have hWD : W ≤ D := Subgroup.map_subtype_le W'
    have hsub : W.subgroupOf D = W' :=
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective W'
    have hWL : W ≤ L := by
      rintro _ ⟨w, hw, rfl⟩
      exact hW'H hw
    have hWK : IsKleinFour ↥W :=
      isKleinFour_of_equiv (W'.equivMapOfInjective _ D.subtype_injective).symm hW'
    have hLN : L ≤ Subgroup.normalizer (W : Set G) ⊓ D := by
      intro x hx
      have h1 := hHN (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hLD hx⟩ : ↥D) ∈ L.subgroupOf D)
      rw [← hsub, E111R.mem_normalizer_subgroupOf_iff, inf_eq_left.mpr hWD] at h1
      exact ⟨h1, hLD hx⟩
    have hcardL : Nat.card L = 24 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLD).toEquiv, Nat.card_congr eH.toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have hcardP : Nat.card ↥(T ⊓ D) = 2 * 2 ^ m := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
    have hm2 : m = 2 := by
      have hdvd : Nat.card ↥(T ⊓ D) ∣ Nat.card L := Subgroup.card_dvd_of_le hTL
      rw [hcardP, hcardL] at hdvd
      have h3 : 2 ^ m ∣ 12 :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using hdvd)
      have h4 : 2 ^ m ≤ 12 := Nat.le_of_dvd (by norm_num) h3
      have h5 : m < 4 := by
        by_contra hc
        push Not at hc
        have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hc
        omega
      interval_cases m <;> simp_all
    subst hm2
    have hSylL : IsSylowIn 2 (T ⊓ D) L := by
      refine ⟨hTL, hTD.isPGroup, fun h2 => ?_⟩
      have hidx : (T ⊓ D).relIndex L * 8 = 24 := by
        have := ((T ⊓ D).subgroupOf L).card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hcardP, hcardL] at this
        rw [Subgroup.relIndex]
        norm_num at this
        omega
      omega
    have hWT : W ≤ T ⊓ D := by
      have hWn : (W.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr (hLN.trans inf_le_left)
      have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hWK.card_four]; norm_num)
      exact hSylL.le_of_normal hWL hWn hW2
    refine ⟨W, hWT, hWK, ?_⟩
    apply Subgroup.eq_of_le_of_card_ge hLN
    rw [hcardL, sub_card_normalizer hp7 hp8 hD hWD hWK]

end CFSG.Quasithin.E2.E22N.E111L
