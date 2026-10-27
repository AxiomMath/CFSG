module

public import CFSG.Quasithin.Vol2.Ch8Sec2Step13Transfer
public import CFSG.Quasithin.Vol2.Ch8Sec2InspVzL34
public import CFSG.Quasithin.Vol2.Ch8Sec2InspVzA
public import CFSG.Quasithin.Vol2.Ch8Sec2L8211Grp
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace L8211M

variable {G : Type} [Group G]

noncomputable def actTo {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P) : ↥X →* ↥P :=
  (A4.actionOn V X hX).codRestrict P fun l => by
    rw [← hP]
    exact (A4.mem_autOn_iff hX).mpr ⟨l, rfl⟩

theorem actTo_apply_coe {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P) (x : ↥X) (v : ↥V) :
    (((actTo hX hP x : ↥P) : MulAut V) v : G) = (x : G) * v * (x : G)⁻¹ :=
  A4.actionOn_apply_coe hX x v

theorem actTo_surjective {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P) :
    Function.Surjective (actTo hX hP) := by
  rintro ⟨a, ha⟩
  have ha' : a ∈ autOn X V := by
    rw [hP]
    exact ha
  obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hX).mp ha'
  exact ⟨l, rfl⟩

theorem mem_ker_actTo {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P) (x : ↥X) :
    x ∈ (actTo hX hP).ker ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : A4.actionOn V X hX x = 1 := by
      have h2 := congrArg Subtype.val h
      simpa [actTo] using h2
    exact (A4.actionOn_eq_one_iff hX x).mp h1
  · intro h
    apply Subtype.ext
    simpa [actTo] using (A4.actionOn_eq_one_iff hX x).mpr h

theorem ker_actTo_eq {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P) :
    (actTo hX hP).ker = (X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X := by
  ext x
  rw [mem_ker_actTo hX hP x, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem isPGroup_ker_actTo {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P)
    (hXC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    IsPGroup 2 ↥((actTo hX hP).ker) := by
  rw [ker_actTo_eq hX hP]
  exact hXC.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm

theorem ker_actTo_le_pCore [Fact (Nat.Prime 2)] {X V : Subgroup G} {P : Subgroup (MulAut V)}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P)
    (hXC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    (actTo hX hP).ker ≤ CFSG.pCore 2 ↥X :=
  CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker _)
    (isPGroup_ker_actTo hX hP hXC)

theorem transfer_pCore [Fact (Nat.Prime 2)] [Finite G] {X V : Subgroup G}
    {P : Subgroup (MulAut V)} (hX : X ≤ Subgroup.normalizer (V : Set G)) (hP : autOn X V = P)
    (hXC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    (CFSG.pCore 2 ↥X).map (actTo hX hP) = CFSG.pCore 2 ↥P ∧
      (CFSG.pCore 2 ↥P).comap (actTo hX hP) = CFSG.pCore 2 ↥X ∧
      Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hk := ker_actTo_le_pCore hX hP hXC
  have hsurj := actTo_surjective hX hP
  have hmap : (CFSG.pCore 2 ↥X).map (actTo hX hP) = CFSG.pCore 2 ↥P :=
    CFSG.GroupTheory.FT63ChII.pCore_map_of_surjective hsurj
      (isPGroup_ker_actTo hX hP hXC)
  have hcomap := L8211G.comap_pCore_eq_of_surj hsurj hk hmap
  exact ⟨hmap, hcomap, L8211G.card_quot_pCore_eq_of_surj hsurj hk hmap⟩

theorem subgroupOf_pCoreOf {V : Subgroup G} (P : Subgroup (MulAut V)) :
    (pCoreOf 2 P).subgroupOf P = CFSG.pCore 2 ↥P := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    unfold pCoreOf at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  · intro hx
    unfold pCoreOf
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem card_pCore_eq_card_pCoreOf {V : Subgroup G} (P : Subgroup (MulAut V)) :
    Nat.card (CFSG.pCore 2 ↥P) = Nat.card ↥(pCoreOf 2 P) :=
  Nat.card_congr
    (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥P) P.subtype P.subtype_injective).toEquiv

end L8211M

theorem mem_and_ne_one {G : Type} [Group G] {T V : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hzV : V ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    z ∈ V ∧ z ∈ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
  have hmem : z ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro h1
  rw [h1, orderOf_one] at hz
  norm_num at hz

section Parts

variable (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (hcovL : KG82CoverL34)
    (hcovM : KG82CoverM22) (hm24 : SchurMult2M24)
include h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24

theorem common_82 {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) :
    IsElemAbelian 2 (fsuV T I) ∧ T ≤ Subgroup.normalizer (L : Set G) ∧
      L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      fsuV T I ≤ T ∧ fsuV T I ≤ L ∧
      L ⊓ Subgroup.centralizer (fsuV T I : Set G) = fsuV T I ∧
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ fsuL0 T L = L ∧
      IsModel82 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ∧
      (∀ n : ℕ, Row711L3Nine T L I n → n = 1) :=
  setup_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hSimple82_holds hCent82_holds
    hType82_holds hParab82_holds hcovL hcovM hm24 hyp h731 h821 hrow

theorem row_setup {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) (z : G)
    (hzV' : z ∈ fsuV T I) (hzT : z ∈ Subgroup.centralizer (T : Set G)) :
    (∀ v : ↥(fsuV T I), v ^ 2 = 1) ∧
      ch8Lz L z ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      autOn (ch8Lz L z) (fsuV T I) = parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ ∧
      IsPGroup 2 ↥(ch8Lz L z ⊓ Subgroup.centralizer (fsuV T I : Set G)) ∧
      IsSylowVec82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ ∧
      vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I) ∧
      (Row711L3Nine T L I 1 → BinaryNineTensor (autOn L (fsuV T I)) ⊤ ⊥ 1) ∧
      (Row711M22Code T L I → MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥) ∧
      (Row711M24Cocode T L I → MathieuCocode24 (autOn L (fsuV T I)) ⊤ ⊥) := by
  obtain ⟨hV, hTL, hLN, hTV, -, -, hCLV, -, hL0, -, -⟩ :=
    common_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24 hyp h731 h821
      hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : ∀ v : ↥(fsuV T I), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hcentC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [hCLV]
    exact fun g => ⟨1, by simpa using hV2 g⟩
  have hLzL : ch8Lz L z ≤ L := (perfectCore_le _).trans inf_le_left
  have hLzN : ch8Lz L z ≤ Subgroup.normalizer (fsuV T I : Set G) := hLzL.trans hLN
  have hXC : IsPGroup 2 ↥(ch8Lz L z ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    hcentC.to_le (inf_le_inf_right _ hLzL)
  have hPz : autOn (ch8Lz L z) (fsuV T I) = parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ :=
    autOn_ch8Lz_82 hLN ⟨z, hzV'⟩
  have hSc := card_autOn_inf_of_sylow (isSylowIn_top_of_fsu hyp.fsu) hTL hTV
  have hconj : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (fsuV T I : Set G),
      conjAct (fsuV T I) ⟨t, ht⟩ ⟨z, hzV'⟩ = ⟨z, hzV'⟩ := by
    intro t ht htN
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_iff.mp hzT t ht, mul_inv_cancel_right]
  have hSz : (⟨z, hzV'⟩ : ↥(fsuV T I)) ∈ fixV (autOn (T ⊓ L) (fsuV T I)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hconj t ht.1 t.2
  have hSH : autOn (T ⊓ L) (fsuV T I) ≤ autOn L (fsuV T I) :=
    Subgroup.map_mono fun x hx => hx.2
  have hSV : IsSylowVec82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ := ⟨_, hSH, hSc, hSz⟩
  have hVz := vz82_eq_82 hzV' hLN hcentC
  refine ⟨hV2, hLzN, hPz, hXC, hSV, hVz, ?_, ?_, ?_⟩
  · intro h
    have h' := h.2
    rw [hL0] at h'
    exact h'
  · intro h
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  · intro h
    unfold Row711M24Cocode at h
    rw [hL0] at h
    exact h

theorem stmt8_2_11_tnorm_of : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    Hyp7_0_2 G T L I → Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
    Case8_2 T L I → ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      T ≤ Subgroup.normalizer (ch8Lz L z : Set G) := by
  intro G _ _ T L I hyp h731 h821 hc hrow _ z hz hzV
  obtain ⟨-, hzT, -⟩ := mem_and_ne_one (T := T) hz hzV
  obtain ⟨-, hTL, -⟩ := common_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL
    hcovM hm24 hyp h731 h821 hrow
  have hTN : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
      Set G) := by
    intro t ht
    have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT t ht)
    have htLN : t ∈ Subgroup.normalizer (L : Set G) := hTL ht
    have htCN : t ∈ Subgroup.normalizer ((Subgroup.centralizer ({z} : Set G) : Subgroup G) :
        Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_centralizer_singleton htC)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxL, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp htLN x).mp hxL,
        (Subgroup.mem_normalizer_iff.mp htCN x).mp hxC⟩
    · rintro ⟨hxL, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp htLN x).mpr hxL,
        (Subgroup.mem_normalizer_iff.mp htCN x).mpr hxC⟩
  exact hTN.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)

theorem stmt8_2_11_n1_of : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    Hyp7_0_2 G T L I → Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
    Case8_2 T L I → ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ∀ n : ℕ, Row711L3Nine T L I n → n = 1 := by
  intro G _ _ T L I hyp h731 h821 hc hrow _ z _ _ n hn
  exact (common_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24 hyp h731
    h821 hrow).2.2.2.2.2.2.2.2.2.2 n hn

theorem stmt8_2_11_L34_of : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    Hyp7_0_2 G T L I → Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
    Case8_2 T L I → ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (Row711L3Nine T L I 1 →
        ∃ (α : ↥(ch8Lz L z) →* alternatingGroup (Fin 5))
          (β : ↥(fsuV T I) →* Multiplicative (evenWeight 5)),
          Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(ch8Lz L z) ∧
          Function.Surjective β ∧ β.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I) ∧
          ∀ (x : ↥(ch8Lz L z)) (v w : ↥(fsuV T I)), (x : G) * (v : G) * (x : G)⁻¹ = (w : G) →
            ∀ i : Fin 5, ((Multiplicative.toAdd (β w) : evenWeight 5) : Fin 5 → ZMod 2) i =
              ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2)
                (((α x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i)) := by
  intro G _ _ T L I hyp h731 h821 hc hrow _ z hz hzV hR1
  obtain ⟨hzV', hzT, hz1G⟩ := mem_and_ne_one (T := T) hz hzV
  have hz1 : (⟨z, hzV'⟩ : ↥(fsuV T I)) ≠ 1 := fun h => hz1G (congrArg Subtype.val h)
  obtain ⟨-, hLzN, hPz, hXC, hSV, hVz, hBN, -, -⟩ :=
    row_setup h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24 hyp h731 h821
      hrow z hzV' hzT
  obtain ⟨α', β', hα's, hα'k, hβ's, hβ'k, hequiv⟩ :=
    vzModL34_holds (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⟨z, hzV'⟩ (hBN hR1) hz1 hSV
  have hrad : radz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ =
      pCoreOf 2 (parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) := rfl
  refine ⟨α'.comp (L8211M.actTo hLzN hPz), β', ?_, ?_, hβ's, ?_, ?_⟩
  · exact hα's.comp (L8211M.actTo_surjective hLzN hPz)
  · rw [← MonoidHom.comap_ker, hα'k, hrad, L8211M.subgroupOf_pCoreOf]
    exact (L8211M.transfer_pCore hLzN hPz hXC).2.1
  · rw [hβ'k, hVz]
  · intro x v w hvw i
    have hp : ((L8211M.actTo hLzN hPz x : ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)) :
        MulAut ↥(fsuV T I)) v = w := by
      apply Subtype.ext
      rw [L8211M.actTo_apply_coe]
      exact hvw
    have h := hequiv (L8211M.actTo hLzN hPz x) v i
    rw [hp] at h
    exact h

theorem stmt8_2_11_M22_of : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    Hyp7_0_2 G T L I → Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
    Case8_2 T L I → ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (Row711M22Code T L I →
        Nat.card (↥(ch8Lz L z) ⧸ CFSG.pCore 2 ↥(ch8Lz L z)) = 360 ∧
        ∃ θ : ↥(fsuV T I) →* Multiplicative (Fin 5 → ZMod 2),
          Function.Surjective θ ∧ θ.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I)) := by
  intro G _ _ T L I hyp h731 h821 hc hrow _ z hz hzV hR22
  obtain ⟨hzV', hzT, hz1G⟩ := mem_and_ne_one (T := T) hz hzV
  have hz1 : (⟨z, hzV'⟩ : ↥(fsuV T I)) ≠ 1 := fun h => hz1G (congrArg Subtype.val h)
  obtain ⟨hV2, hLzN, hPz, hXC, hSV, hVz, -, hM22, -⟩ :=
    row_setup h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24 hyp h731 h821
      hrow z hzV' hzT
  have hmod := hM22 hR22
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPcard, hVcard⟩ :=
    vzModCode22_holds (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⟨z, hzV'⟩ hmod hz1 hSV
  obtain ⟨hWcard, hRcard, -⟩ :=
    hZ82_holds (V := ↥(fsuV T I)) (autOn L (fsuV T I)) 4 ⟨z, hzV'⟩
      (Or.inr (Or.inl ⟨hmod, rfl⟩)) hz1 hSV
  have hrad : radz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ =
      pCoreOf 2 (parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) := rfl
  have hRc : Nat.card ↥(CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)) = 2 ^ 4 := by
    rw [L8211M.card_pCore_eq_card_pCoreOf, ← hrad]
    exact hRcard
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨-, -, hquot⟩ := L8211M.transfer_pCore hLzN hPz hXC
    rw [hquot]
    have h := (CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)).card_eq_card_quotient_mul_card_subgroup
    rw [hPcard, hRc] at h
    have h2 : Nat.card (↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) ⧸
        CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)) * 2 ^ 4 = 360 * 2 ^ 4 := by
      rw [← h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 4) h2
  ·
    have hWc : Nat.card ↥(vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) = 2 ^ 5 := by
      rw [hWcard]
    have hq := L8211G.card_quot_eq_two_pow (vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) hVcard hWc
      (by norm_num)
    have hQ : ∀ q : ↥(fsuV T I) ⧸ vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩, q ^ 2 = 1 := by
      intro q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_pow, hV2 v]
      rfl
    obtain ⟨e⟩ := L8211G.nonempty_mulEquiv_fin_of_card_two_pow hQ (n := 5) (by rw [hq])
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
    · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
    · rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom (MulEquiv.injective e),
        QuotientGroup.ker_mk']
      exact hVz

theorem stmt8_2_11_M24_of : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    Hyp7_0_2 G T L I → Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I),
    Case8_2 T L I → ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (Row711M24Cocode T L I →
        Nat.card (↥(ch8Lz L z) ⧸ CFSG.pCore 2 ↥(ch8Lz L z)) = 1080 ∧
        ∃ θ : ↥(fsuV T I) →* Multiplicative (Fin 4 → ZMod 2),
          Function.Surjective θ ∧ θ.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I)) := by
  intro G _ _ T L I hyp h731 h821 hc hrow _ z hz hzV hR24
  obtain ⟨hzV', hzT, hz1G⟩ := mem_and_ne_one (T := T) hz hzV
  have hz1 : (⟨z, hzV'⟩ : ↥(fsuV T I)) ≠ 1 := fun h => hz1G (congrArg Subtype.val h)
  obtain ⟨hV2, hLzN, hPz, hXC, hSV, hVz, -, -, hM24⟩ :=
    row_setup h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24 hyp h731 h821
      hrow z hzV' hzT
  have hmod := hM24 hR24
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPcard, hVcard⟩ :=
    vzModCocode24_holds (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⟨z, hzV'⟩ hmod hz1 hSV
  obtain ⟨hWcard, hRcard, -⟩ :=
    hZ82_holds (V := ↥(fsuV T I)) (autOn L (fsuV T I)) 6 ⟨z, hzV'⟩
      (Or.inr (Or.inr ⟨hmod, rfl⟩)) hz1 hSV
  have hrad : radz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩ =
      pCoreOf 2 (parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) := rfl
  have hRc : Nat.card ↥(CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)) = 2 ^ 6 := by
    rw [L8211M.card_pCore_eq_card_pCoreOf, ← hrad]
    exact hRcard
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨-, -, hquot⟩ := L8211M.transfer_pCore hLzN hPz hXC
    rw [hquot]
    have h := (CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)).card_eq_card_quotient_mul_card_subgroup
    rw [hPcard, hRc] at h
    have h2 : Nat.card (↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) ⧸
        CFSG.pCore 2 ↥(parz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩)) * 2 ^ 6 = 1080 * 2 ^ 6 := by
      rw [← h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 6) h2
  ·
    have hWc : Nat.card ↥(vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) = 2 ^ 7 := by
      rw [hWcard]
    have hq := L8211G.card_quot_eq_two_pow (vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩) hVcard hWc
      (by norm_num)
    have hQ : ∀ q : ↥(fsuV T I) ⧸ vz82 (autOn L (fsuV T I)) ⟨z, hzV'⟩, q ^ 2 = 1 := by
      intro q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_pow, hV2 v]
      rfl
    obtain ⟨e⟩ := L8211G.nonempty_mulEquiv_fin_of_card_two_pow hQ (n := 4) (by rw [hq])
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
    · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
    · rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom (MulEquiv.injective e),
        QuotientGroup.ker_mk']
      exact hVz

theorem stmt8_2_11_modules_of_comp
    (h1 : ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
      Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
        fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
        ch8Lz L z ∈ cComp (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G))) :
    Stmt8_2_11_modules := by
  intro G _ _ T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  exact ⟨h1 G T L I hyp h731 h821 hc hrow hnot24 z hz hzV,
    stmt8_2_11_tnorm_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
      G T L I hyp h731 h821 hc hrow hnot24 z hz hzV,
    stmt8_2_11_n1_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
      G T L I hyp h731 h821 hc hrow hnot24 z hz hzV,
    stmt8_2_11_L34_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
      G T L I hyp h731 h821 hc hrow hnot24 z hz hzV,
    stmt8_2_11_M22_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
      G T L I hyp h731 h821 hc hrow hnot24 z hz hzV,
    stmt8_2_11_M24_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
      G T L I hyp h731 h821 hc hrow hnot24 z hz hzV⟩

end Parts

end CFSG.Quasithin.H13
