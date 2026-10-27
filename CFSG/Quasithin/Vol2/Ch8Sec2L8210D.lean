module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210C
public import CFSG.Quasithin.Vol2.Ch8Sec2KG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8210D

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_index_two_of_lt_82 {V Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hVQ : V < Q) :
    ∃ W : Subgroup G, V ≤ W ∧ W ≤ Q ∧ Nat.card ↥Q = 2 * Nat.card ↥W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have hVp : IsPGroup 2 ↥V := hQ.to_le hVQ.le
  obtain ⟨a, ha⟩ := hVp.exists_card_eq
  have hab : a < b := by
    have h1 : Nat.card ↥V < Nat.card ↥Q := Subgroup.card_lt_of_lt hVQ
    rw [ha, hb] at h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  obtain ⟨W, hW, hVW, hWQ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (n := b - 1)
    Nat.prime_two (by rw [ha]; exact Nat.pow_dvd_pow 2 (by omega))
    (by rw [hb]; exact Nat.pow_dvd_pow 2 (by omega)) hVQ.le
  refine ⟨W, hVW, hWQ, ?_⟩
  rw [hb, hW, ← pow_succ']
  congr 1
  omega

omit [Finite G] in
theorem map_actHom82 {V X : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hXL : X ≤ L) :
    ((X.subgroupOf L).map (actHom82 hLN)).map (autOn L V).subtype = autOn X V := by
  ext φ
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion hLN x, hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    have hgL : (g : G) ∈ L := hXL hg
    refine ⟨actHom82 hLN ⟨g, hgL⟩, ⟨⟨g, hgL⟩, hg, rfl⟩, rfl⟩

theorem card_eq_card_map_mul_82 {K H : Type*} [Group K] [Group H] [Finite K] (ψ : K →* H)
    (P : Subgroup K) : Nat.card ↥P = Nat.card ↥(P.map ψ) * Nat.card ↥(P ⊓ ψ.ker) := by
  set f : ↥P →* H := ψ.comp P.subtype with hf
  have hrange : f.range = P.map ψ := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ↥f.ker = Nat.card ↥(P ⊓ ψ.ker) := by
    have h1 : f.ker = (ψ.ker).subgroupOf P := by
      ext x
      simp [hf, Subgroup.mem_subgroupOf]
    have h2 : (ψ.ker).subgroupOf P = (P ⊓ ψ.ker).subgroupOf P := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ ψ.ker ≤ P)).toEquiv]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker]

theorem ker_lift_actHom82_eq_center (hsimp : HSimple82) {V W : Subgroup G}
    [hc : IsMulCommutative ↥V] (hmod : IsModel82 (V := ↥V) (autOn L V))
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hVW : V ≤ W)
    (hQL : ⁅pCoreOf 2 L, L⁆ ≤ V) (hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L)
    [hWn : (W.subgroupOf L).Normal] (hWker : W.subgroupOf L ≤ (actHom82 hLN).ker) :
    (QuotientGroup.lift (W.subgroupOf L) (actHom82 hLN) hWker).ker =
      Subgroup.center (↥L ⧸ W.subgroupOf L) := by
  obtain ⟨hS, a₀, b₀, hab⟩ := hsimp ↥V (autOn L V) hmod
  set ψ := QuotientGroup.lift (W.subgroupOf L) (actHom82 hLN) hWker with hψ
  have hψs : Function.Surjective ψ := by
    intro h
    obtain ⟨l, rfl⟩ := actHom82_surjective hLN h
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hZH : Subgroup.center ↥(autOn L V) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L V)) with hc0 | hc0
    · exact hc0
    · exact absurd (Subgroup.mem_center_iff.mp (hc0 ▸ Subgroup.mem_top b₀) a₀) hab
  apply le_antisymm
  · intro c hc
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
    have hl : l ∈ (actHom82 hLN).ker := by
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.mem_ker] at hc
      exact hc
    rw [mem_ker_actHom82] at hl
    have hlQ : (l : G) ∈ pCoreOf 2 L := hCQ ▸ ⟨l.2, hl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective k
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : ⁅(l : G)⁻¹, (m : G)⁻¹⁆ ∈ V :=
      hQL (Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem hlQ) (L.inv_mem m.2))
    have h2 : (((m * l)⁻¹ * (l * m) : ↥L) : G) = ⁅(l : G)⁻¹, (m : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h2]
    exact hVW h1
  · intro c hc
    have h1 : ψ c ∈ Subgroup.center ↥(autOn L V) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨k, rfl⟩ := hψs h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc k]
    rw [hZH, Subgroup.mem_bot] at h1
    exact h1

theorem pCoreOf_eq_of_cover_82 (hsimp : HSimple82) (hcovL : KG82CoverL34)
    (hcovM : KG82CoverM22) {V Y LU : Subgroup G} [hc : IsMulCommutative ↥V]
    (hmod : IsModel82 (V := ↥V) (autOn L V)) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : ⁅L, L⁆ = L) (hVQ : V ≤ pCoreOf 2 L) (hQL : ⁅pCoreOf 2 L, L⁆ ≤ V)
    (hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L)
    (hLU : LU ≤ L) (hYO : Y ≤ pCoreOf 2 LU) (hYN : LU ≤ Subgroup.normalizer (Y : Set G))
    (hYQ : Y ⊓ pCoreOf 2 L ≤ V) (hLUc : Nat.card ↥(autOn LU V) = 960)
    (hYimg : pCoreOf 2 (autOn LU V) ≤ autOn Y V)
    (htype : IsPSL 3 2 2 ↥(autOn L V) ∨
      (IsSporadic .M22 ↥(autOn L V) ∧
        ∃ X : Subgroup G, LU ≤ X ∧ X ≤ L ∧ IsPSL 3 2 2 ↥(autOn X V))) :
    pCoreOf 2 L = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL' : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hYLU : Y ≤ LU := hYO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 LU)
  have hYL : Y ≤ L := hYLU.trans hLU
  by_contra hne
  obtain ⟨W, hVW, hWQ, hcardW⟩ := exists_index_two_of_lt_82 hQp (lt_of_le_of_ne hVQ (Ne.symm hne))
  have hconjW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    intro l hl w hw
    have h1 : ⁅w⁻¹, l⁆ ∈ V :=
      hQL (Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem (hWQ hw)) hl)
    have h2 : l * w * l⁻¹ = w * ⁅w⁻¹, l⁆ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact W.mul_mem hw (hVW h1)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconjW l hl w, fun hw => ?_⟩
    have := hconjW l⁻¹ (L.inv_mem hl) _ hw
    simpa [mul_assoc] using this
  have hWn : (W.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLW
  obtain ⟨hq, hZ, ⟨e⟩⟩ := quot_structure_of_82 hsimp hmod hLN hperf hVW hWQ hQL hCQ
  have hWker : W.subgroupOf L ≤ (actHom82 hLN).ker := by
    intro x hx
    rw [mem_ker_actHom82]
    have hxQ : (x : G) ∈ pCoreOf 2 L := hWQ hx
    rw [← hCQ] at hxQ
    exact hxQ.2
  set ψ := QuotientGroup.lift (W.subgroupOf L) (actHom82 hLN) hWker with hψ
  have hψk : ψ.ker = Subgroup.center (↥L ⧸ W.subgroupOf L) :=
    ker_lift_actHom82_eq_center hsimp hmod hLN hVW hQL hCQ hWker
  have hψmk : ∀ l : ↥L, ψ (QuotientGroup.mk l) = actHom82 hLN l := fun l => rfl
  set mk := QuotientGroup.mk' (W.subgroupOf L) with hmk
  set Z := Subgroup.center (↥L ⧸ W.subgroupOf L) with hZdef
  have hZc : Nat.card ↥Z = 2 := by
    rw [hZ]
    have h1 := card_eq_card_map_mul_82 mk ((pCoreOf 2 L).subgroupOf L)
    have h2 : (pCoreOf 2 L).subgroupOf L ⊓ mk.ker = W.subgroupOf L := by
      rw [hmk, QuotientGroup.ker_mk']
      exact inf_eq_right.mpr fun x hx => hWQ hx
    rw [h2] at h1
    have h3 : Nat.card ↥((pCoreOf 2 L).subgroupOf L) = Nat.card ↥(pCoreOf 2 L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL').toEquiv
    have h4 : Nat.card ↥(W.subgroupOf L) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWQ.trans hQL')).toEquiv
    rw [h3, h4, hcardW] at h1
    have hpos : 0 < Nat.card ↥W := Nat.card_pos
    have h5 : 2 * Nat.card ↥W = Nat.card ↥(((pCoreOf 2 L).subgroupOf L).map mk) * Nat.card ↥W :=
      h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h5).symm
  have hψmk' : ψ.comp mk = actHom82 hLN := by
    ext l
    rfl
  have hψmap : ∀ X : Subgroup G, X ≤ L →
      ((((X.subgroupOf L).map mk).map ψ).map (autOn L V).subtype = autOn X V) := by
    intro X hXL
    have h := map_actHom82 hLN hXL
    rw [← hψmk', ← Subgroup.map_map] at h
    exact h
  have hZψ : Z.map ψ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hψk]
  set P := (LU.subgroupOf L).map mk ⊔ Z with hPdef
  have hZP : Z ≤ P := le_sup_right
  have hψP : (P.map ψ).map (autOn L V).subtype = autOn LU V := by
    rw [hPdef, Subgroup.map_sup, hZψ, sup_bot_eq]
    exact hψmap LU hLU
  have hPc : Nat.card ↥P = 2 * 960 := by
    have h1 := card_eq_card_map_mul_82 ψ P
    rw [hψk, inf_eq_right.mpr hZP, hZc] at h1
    have h2 : Nat.card ↥(P.map ψ) = 960 := by
      rw [← hLUc, ← hψP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [h1, h2]
  set Yb := (Y.subgroupOf L).map mk with hYbdef
  have hYbP : Yb ≤ P :=
    le_sup_of_le_left (Subgroup.map_mono fun x (hx : (x : G) ∈ Y) => hYLU hx)
  have hZc' : ∀ z ∈ Z, ∀ k : ↥L ⧸ W.subgroupOf L, k * z = z * k := fun z hz k =>
    Subgroup.mem_center_iff.mp hz k
  have hYbN : P ≤ Subgroup.normalizer (Yb : Set (↥L ⧸ W.subgroupOf L)) := by
    rw [hPdef, sup_le_iff]
    constructor
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : (u : G) ∈ LU := hu
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have hcl : ∀ (g : ↥L), (g : G) ∈ LU → ∀ x ∈ Yb, mk g * x * (mk g)⁻¹ ∈ Yb := by
        rintro g hg _ ⟨y, hy, rfl⟩
        have hy' : (y : G) ∈ Y := hy
        refine ⟨g * y * g⁻¹, ?_, by simp⟩
        show ((g : G) * y * (g : G)⁻¹) ∈ Y
        exact (Subgroup.mem_normalizer_iff.mp (hYN hg) y).mp hy'
      constructor
      · exact hcl u hu' k
      · intro hk
        have := hcl u⁻¹ (LU.inv_mem hu') _ hk
        simpa [mul_assoc] using this
    · intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [← hZc' z hz k, mul_inv_cancel_right]
  have hYbp : IsPGroup 2 ↥Yb := by
    have h1 : IsPGroup 2 ↥(Y.subgroupOf L) :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU).to_le hYO).of_equiv
        (Subgroup.subgroupOfEquivOfLe hYL).symm
    exact h1.map _
  have hYbR : Yb ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYbP hYbN hYbp
  have hYbZ : ∀ x ∈ Yb, x ∈ Z → x = 1 := by
    rintro _ ⟨y, hy, rfl⟩ hz
    rw [hZ] at hz
    obtain ⟨q, hq, hqy⟩ := hz
    have hqy' : q⁻¹ * y ∈ W.subgroupOf L := by
      rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]
      exact hqy
    have hyQ : (y : G) ∈ pCoreOf 2 L := by
      have h1 : ((q⁻¹ * y : ↥L) : G) ∈ pCoreOf 2 L := hWQ hqy'
      have h2 : (y : G) = (q : G) * ((q⁻¹ * y : ↥L) : G) := by simp
      rw [h2]
      exact (pCoreOf 2 L).mul_mem (Subgroup.mem_subgroupOf.mp hq) h1
    have hyW : (y : G) ∈ W := hVW (hYQ ⟨hy, hyQ⟩)
    exact (QuotientGroup.eq_one_iff y).mpr hyW
  have hYbψ : (Yb.map ψ).map (autOn L V).subtype = autOn Y V := hψmap Y hYL
  have hRY : pCoreOf 2 P ≤ Yb ⊔ Z := by
    intro r hr
    have hS : ((pCoreOf 2 P).map ψ).map (autOn L V).subtype ≤ pCoreOf 2 (autOn LU V) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
      · rw [← hψP]
        exact Subgroup.map_mono (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 P))
      · rw [← hψP]
        rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        rw [Subgroup.mem_normalizer_iff]
        intro φ
        have hpN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨ψ (p * x * p⁻¹), ⟨p * x * p⁻¹,
            (Subgroup.mem_normalizer_iff.mp hpN x).mp hx, rfl⟩, by simp⟩
        · intro hφ
          obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := hφ
          refine ⟨ψ (p⁻¹ * x * p), ⟨p⁻¹ * x * p, ?_, rfl⟩, ?_⟩
          · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpN) x).mp hx
            simpa using this
          · have h1 : (((autOn L V).subtype (ψ p) * φ * ((autOn L V).subtype (ψ p))⁻¹ :
                MulAut ↥V)) = (autOn L V).subtype (ψ x) := hx'.symm
            have h2 : φ = ((autOn L V).subtype (ψ p))⁻¹ * (autOn L V).subtype (ψ x) *
                (autOn L V).subtype (ψ p) := by
              rw [← h1]
              group
            rw [h2]
            simp
      · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).map ψ).map _
    have h1 : (autOn L V).subtype (ψ r) ∈ autOn Y V :=
      hYimg (hS ⟨ψ r, ⟨r, hr, rfl⟩, rfl⟩)
    rw [← hYbψ] at h1
    obtain ⟨_, ⟨yb, hyb, rfl⟩, hyr⟩ := h1
    have hyr' : ψ yb = ψ r := Subgroup.subtype_injective _ hyr
    have hz : yb⁻¹ * r ∈ Z := by
      rw [← hψk, MonoidHom.mem_ker, map_mul, map_inv, hyr', inv_mul_cancel]
    have h2 : r = yb * (yb⁻¹ * r) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup hyb hz
  have hKG : ⁅pCoreOf 2 P, P⁆ = pCoreOf 2 P := by
    rcases htype with hL3 | ⟨hM22, X, hLUX, hXL, hX3⟩
    · have hiso : IsPSL 3 2 2 ((↥L ⧸ W.subgroupOf L) ⧸ Z) := by
        obtain ⟨a, K', k1, k2, hK', ⟨f⟩⟩ := hL3
        exact ⟨a, K', k1, k2, hK', ⟨e.trans f⟩⟩
      exact hcovL _ hq hZc hiso P hZP hPc
    · have hiso : IsSporadic .M22 ((↥L ⧸ W.subgroupOf L) ⧸ Z) := by
        obtain ⟨f⟩ := hM22
        exact ⟨e.trans f⟩
      set XK := (X.subgroupOf L).map mk ⊔ Z with hXKdef
      have hZX : Z ≤ XK := le_sup_right
      have hLUXs : LU.subgroupOf L ≤ X.subgroupOf L := fun x hx => hLUX hx
      have hPX : P ≤ XK := by
        rw [hPdef, hXKdef]
        exact sup_le_sup_right (Subgroup.map_mono hLUXs) Z
      have hXiso : IsPSL 3 2 2 (↥XK ⧸ Z.subgroupOf XK) := by
        set f : ↥XK →* ↥(autOn L V) := ψ.comp XK.subtype with hf
        have hfker : f.ker = Z.subgroupOf XK := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hψk, MonoidHom.mem_ker]
          rfl
        have hfr : f.range.map (autOn L V).subtype = autOn X V := by
          rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hXKdef, Subgroup.map_sup, hZψ,
            sup_bot_eq]
          exact hψmap X hXL
        have e1 : ↥XK ⧸ Z.subgroupOf XK ≃* ↥f.range :=
          (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
            (QuotientGroup.quotientKerEquivRange f)
        have e2 : ↥f.range ≃* ↥(autOn X V) :=
          (Subgroup.equivMapOfInjective f.range _ (Subgroup.subtype_injective _)).trans
            (MulEquiv.subgroupCongr hfr)
        obtain ⟨a, K', k1, k2, hK', ⟨g⟩⟩ := hX3
        exact ⟨a, K', k1, k2, hK', ⟨(e1.trans e2).trans g⟩⟩
      exact hcovM _ hq hZc hiso XK hZX hXiso P hZP hPX hPc
  have hZN : Z ≤ Subgroup.normalizer (Yb : Set (↥L ⧸ W.subgroupOf L)) := fun z hz =>
    hYbN (hZP hz)
  have hcomm : ⁅pCoreOf 2 P, P⁆ ≤ Yb := by
    rw [Subgroup.commutator_le]
    intro r hr p hp
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_le_normalizer_82 hZN (hRY hr)
    have hzp : z * p = p * z := (hZc' z hz p).symm
    have h1 : ⁅y * z, p⁆ = y * (p * y⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      calc y * z * p * (y * z)⁻¹ * p⁻¹ = y * (z * p) * z⁻¹ * y⁻¹ * p⁻¹ := by group
        _ = y * (p * z) * z⁻¹ * y⁻¹ * p⁻¹ := by rw [hzp]
        _ = y * (p * y⁻¹ * p⁻¹) := by group
    rw [h1]
    exact Yb.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hYbN hp) y⁻¹).mp (Yb.inv_mem hy))
  have hZp : IsPGroup 2 ↥Z := IsPGroup.of_card (n := 1) (by rw [hZc, pow_one])
  have hZR : Z ≤ pCoreOf 2 P := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZP ?_ hZp
    intro p _
    have hZn : Z.Normal := by rw [hZdef]; infer_instance
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hZn.conj_mem z hz p, fun hz => ?_⟩
    have := hZn.conj_mem _ hz p⁻¹
    simpa [mul_assoc] using this
  have hZY : Z ≤ Yb := hZR.trans (hKG.symm.le.trans hcomm)
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hZc
    omega
  exact hz1 (hYbZ z (hZY hz) hz)
end L8210D

end CFSG.Quasithin.H13
