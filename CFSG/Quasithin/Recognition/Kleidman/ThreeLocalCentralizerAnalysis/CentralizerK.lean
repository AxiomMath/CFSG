module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerInH
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.DihedralCentralizers
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.QuotientCentralizer

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

abbrev CK {G : Type} [Group G] (y : G) : Subgroup G := Subgroup.centralizer ({y} : Set G)

theorem mem_CK_self {G : Type} [Group G] (y : G) : y ∈ CK y :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

@[expose] def NY {G : Type} [Group G] (y : G) : Subgroup ↥(CK y) := Subgroup.zpowers ⟨y, mem_CK_self y⟩

theorem NY_le_center {G : Type} [Group G] (y : G) : NY y ≤ Subgroup.center ↥(CK y) := by
  rw [NY, Subgroup.zpowers_le]
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

instance NY_normal {G : Type} [Group G] (y : G) : (NY y).Normal :=
  Subgroup.normal_of_le_center (NY_le_center y)

theorem NY_card {G : Type} [Group G] {y : G} (hy3 : orderOf y = 3) : Nat.card (NY y) = 3 := by
  rw [NY, Nat.card_zpowers, Subgroup.orderOf_mk, hy3]

theorem map_conj_centralizer_inf {G : Type} [Group G] (c a b : G) :
    ((Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)).map
        (MulAut.conj c).toMonoidHom) =
      Subgroup.centralizer ({c * a * c⁻¹} : Set G) ⊓ Subgroup.centralizer ({c * b * c⁻¹} : Set G) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc c * x * c⁻¹ * (c * a * c⁻¹) = c * (x * a) * c⁻¹ := by group
        _ = c * (a * x) * c⁻¹ := by rw [hxa]
        _ = c * a * c⁻¹ * (c * x * c⁻¹) := by group
    · calc c * x * c⁻¹ * (c * b * c⁻¹) = c * (x * b) * c⁻¹ := by group
        _ = c * (b * x) * c⁻¹ := by rw [hxb]
        _ = c * b * c⁻¹ * (c * x * c⁻¹) := by group
  · rintro ⟨hga, hgb⟩
    refine ⟨c⁻¹ * g * c, ⟨?_, ?_⟩, by group⟩
    · have : c⁻¹ * (g * (c * a * c⁻¹)) * c = c⁻¹ * ((c * a * c⁻¹) * g) * c := by rw [hga]
      calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * g) * c := this
        _ = a * (c⁻¹ * g * c) := by group
    · have : c⁻¹ * (g * (c * b * c⁻¹)) * c = c⁻¹ * ((c * b * c⁻¹) * g) * c := by rw [hgb]
      calc c⁻¹ * g * c * b = c⁻¹ * (g * (c * b * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * b * c⁻¹) * g) * c := this
        _ = b * (c⁻¹ * g * c) := by group

theorem exists_conj_of_one_class {G : Type} [Group G] [Finite G] {z : G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hone : involutionClassCount G = 1) {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ c : G, c * z * c⁻¹ = t := by
  have hset : Set.ncard {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c} = 1 :=
    hone
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hset
  have hzmem : ConjClasses.mk z ∈ {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧
      ConjClasses.mk x = c} := ⟨z, by rw [pow_two]; exact hz2, hz1, rfl⟩
  have htmem : ConjClasses.mk t ∈ {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧
      ConjClasses.mk x = c} := ⟨t, by rw [pow_two]; exact ht2, ht1, rfl⟩
  rw [ha] at hzmem htmem
  have : ConjClasses.mk z = ConjClasses.mk t := (Set.mem_singleton_iff.mp hzmem).trans
    (Set.mem_singleton_iff.mp htmem).symm
  have hconj : IsConj z t := ConjClasses.mk_eq_mk_iff_isConj.mp this
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact ⟨c, hc⟩

theorem _root_.CFSG.Quasithin.IsTypeH2.centralizer_involution_data {G : Type} [Group G] [Finite G]
    {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf y = 3)
    {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) (hty : t ∈ CK y) :
    Nat.card ↥(Subgroup.centralizer ({(⟨t, hty⟩ : ↥(CK y))} : Set ↥(CK y))) = 24 ∧
      ∃ R : Subgroup ↥(CK y),
        R ≤ Subgroup.centralizer ({(⟨t, hty⟩ : ↥(CK y))} : Set ↥(CK y)) ∧
          Nonempty (↥R ≃* DihedralGroup 4) := by
  classical
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  obtain ⟨c, hc⟩ := exists_conj_of_one_class hz2 h.ne_one hone ht2 ht1
  set y' : G := c⁻¹ * y * c with hy'
  have hty' : t * y = y * t := Subgroup.mem_centralizer_singleton_iff.mp hty
  have hy'H : y' ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzc : z = c⁻¹ * t * c := by rw [← hc]; group
    calc y' * z = c⁻¹ * (y * t) * c := by rw [hy', hzc]; group
      _ = c⁻¹ * (t * y) * c := by rw [hty']
      _ = z * y' := by rw [hy', hzc]; group
  have hy'3 : orderOf y' = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) y
    simpa [MulAut.conj_apply, hy', hy3] using this
  obtain ⟨hQ8, ⟨eD⟩⟩ := h.card_and_dihedral_pCoreOf_inf_centralizer hy'H hy'3
  have h24 := h.card_centralizer_inf_centralizer hy'H hy'3
  have hcy : c * y' * c⁻¹ = y := by rw [hy']; group
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hA : (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({y'} : Set G)).map
      (MulAut.conj c).toMonoidHom = Subgroup.centralizer ({t} : Set G) ⊓ CK y := by
    rw [map_conj_centralizer_inf, hc, hcy]
  set A : Subgroup G := Subgroup.centralizer ({t} : Set G) ⊓ CK y with hAdef
  have hAcard : Nat.card A = 24 := by
    rw [← hA, Subgroup.card_map_of_injective hinj, h24]
  have hAK : A ≤ CK y := inf_le_right
  have hCK : Nat.card ↥(Subgroup.centralizer ({(⟨t, hty⟩ : ↥(CK y))} : Set ↥(CK y))) = 24 := by
    rw [← hAcard]
    refine Nat.card_congr
      { toFun := fun k => ⟨k.1.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
          have := Subgroup.mem_centralizer_singleton_iff.mp k.2
          exact congrArg Subtype.val this), k.1.2⟩
        invFun := fun a => ⟨⟨a.1, a.2.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (by
          exact Subgroup.mem_centralizer_singleton_iff.mp a.2.1))⟩
        left_inv := fun k => rfl
        right_inv := fun a => rfl }
  refine ⟨hCK, ?_⟩
  set B : Subgroup G := ((pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ⊓
      Subgroup.centralizer ({y'} : Set G)).map (MulAut.conj c).toMonoidHom with hB
  have hBA : B ≤ A := by
    rw [← hA]
    exact Subgroup.map_mono (inf_le_inf_right _ (pCoreOf_le 2 _))
  have hBK : B ≤ CK y := hBA.trans hAK
  have hBt : B ≤ Subgroup.centralizer ({t} : Set G) := hBA.trans inf_le_left
  refine ⟨B.subgroupOf (CK y), ?_, ⟨?_⟩⟩
  · intro r hr
    have hrB : (r : G) ∈ B := hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hBt hrB))
  · exact ((Subgroup.subgroupOfEquivOfLe hBK).trans
      (Subgroup.equivMapOfInjective _ _ hinj).symm).trans eD

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_psl2_of_centralizer_quotient
    {G : Type} [Group G] [Finite G] {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf y = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      (Fintype.card F = 7 ∨ Fintype.card F = 9) ∧
        Nonempty ((↥(CK y) ⧸ NY y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  classical
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hzK : z ∈ CK y := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hN3 := NY_card hy3
  have hNcube : ∀ n ∈ NY y, n ^ 3 = 1 := by
    intro n hn
    have hd : orderOf n ∣ 3 := by
      rw [← hN3]; exact Subgroup.orderOf_dvd_natCard (NY y) hn
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  refine exists_psl2_of_dihedral_centralizers (X := ↥(CK y) ⧸ NY y) ?_ ?_
  ·
    refine ⟨((⟨z, hzK⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y), ?_⟩
    have hsq : ((⟨z, hzK⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨z, hzK⟩ : ↥(CK y)) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hz2)
      rw [this]; rfl
    have hne : ((⟨z, hzK⟩ : ↥(CK y)) : ↥(CK y) ⧸ NY y) ≠ 1 := by
      intro h1
      have hmem : (⟨z, hzK⟩ : ↥(CK y)) ∈ NY y := (QuotientGroup.eq_one_iff _).mp h1
      have hd : orderOf (⟨z, hzK⟩ : ↥(CK y)) ∣ 3 := by
        rw [← hN3]; exact Subgroup.orderOf_dvd_natCard (NY y) hmem
      have hzo : orderOf (⟨z, hzK⟩ : ↥(CK y)) = 2 := by
        rw [Subgroup.orderOf_mk]; exact h.orderOf_eq
      rw [hzo] at hd
      omega
    exact orderOf_eq_prime hsq hne
  · intro tbar htbar
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective tbar
    have hk2 : ((k : ↥(CK y) ⧸ NY y)) ^ 2 = 1 := by
      rw [← htbar]; exact pow_orderOf_eq_one _
    have hk2N : k ^ 2 ∈ NY y := by
      rw [← QuotientGroup.mk_pow] at hk2
      exact (QuotientGroup.eq_one_iff _).mp hk2
    have hk6 : k ^ 6 = 1 := by
      have := hNcube _ hk2N
      rw [← pow_mul] at this
      exact this
    set t : ↥(CK y) := k ^ 3 with ht
    have htt : t * t = 1 := by rw [ht, ← pow_add]; exact hk6
    have htbar' : ((t : ↥(CK y)) : ↥(CK y) ⧸ NY y) = k := by
      rw [ht, QuotientGroup.mk_pow]
      calc (k : ↥(CK y) ⧸ NY y) ^ 3 = (k : ↥(CK y) ⧸ NY y) ^ 2 * (k : ↥(CK y) ⧸ NY y) := pow_succ _ _
        _ = k := by rw [hk2, one_mul]
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1] at htbar'
      have : (1 : ↥(CK y) ⧸ NY y) = k := by simpa using htbar'
      rw [← this] at htbar
      simp at htbar
    obtain ⟨hC24, R, hRle, hR⟩ := h.centralizer_involution_data hone hy hy3
      (t := (t : G)) (by simpa using congrArg Subtype.val htt)
      (fun h1 => ht1 (Subtype.ext h1)) t.2
    obtain ⟨eR⟩ := hR
    have key := nonempty_mulEquiv_dihedral_centralizer_quotient (NY y) (NY_le_center y) hN3
      htt (by simpa using hC24) hRle eR
    rw [htbar'] at key
    exact key

end CFSG.Quasithin.Kleidman.ThreeLocal
