module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts2
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_of_card_two {X : Type*} [Group X] (h : Nat.card X = 2) {a b : X} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : X)).mp h
  rw [huniq a ha, huniq b hb]

theorem commutator_le_of_le_normalizer {V D : Subgroup G}
    (hD : D ≤ Subgroup.normalizer (V : Set G)) : ⁅V, D⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv d hd
  have h1 : d * v⁻¹ * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hD hd) _).mp (V.inv_mem hv)
  have : ⁅v, d⁆ = v * (d * v⁻¹ * d⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact V.mul_mem hv h1

theorem le_centralizer_commutator_of_card_two {V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hDN : D ≤ Subgroup.normalizer (V : Set G))
    (hsq : ∀ d ∈ D, d ^ 2 ∈ Subgroup.centralizer (V : Set G))
    (hid : ∀ d ∈ D, ∀ d' ∈ D, d ∉ Subgroup.centralizer (V : Set G) →
      d' ∉ Subgroup.centralizer (V : Set G) → ∀ x ∈ V, d' * x * d'⁻¹ = d * x * d⁻¹) :
    D ≤ Subgroup.centralizer ((⁅V, D⁆ : Subgroup G) : Set G) := by
  intro d' hd'
  have key : ⁅V, D⁆ ≤ Subgroup.centralizer ({d'} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have hcV : ⁅v, d⁆ ∈ V := commutator_le_of_le_normalizer hDN
      (Subgroup.commutator_mem_commutator hv hd)
    have hc : ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    have hcomm : d' * ⁅v, d⁆ * d'⁻¹ = ⁅v, d⁆ := by
      by_cases hd0 : d ∈ Subgroup.centralizer (V : Set G)
      · have h1 : v * d = d * v := Subgroup.mem_centralizer_iff.mp hd0 v hv
        have : ⁅v, d⁆ = 1 := by
          rw [commutatorElement_def, h1]; group
        rw [this]; group
      by_cases hd'0 : d' ∈ Subgroup.centralizer (V : Set G)
      · have h1 : ⁅v, d⁆ * d' = d' * ⁅v, d⁆ := Subgroup.mem_centralizer_iff.mp hd'0 _ hcV
        calc d' * ⁅v, d⁆ * d'⁻¹ = ⁅v, d⁆ * d' * d'⁻¹ := by rw [← h1]
          _ = ⁅v, d⁆ := by group
      have hb : d * v * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hDN hd) v).mp hv
      have h1 : d' * v * d'⁻¹ = d * v * d⁻¹ := hid d hd d' hd' hd0 hd'0 v hv
      have h2 : d' * (d * v * d⁻¹) * d'⁻¹ = d * (d * v * d⁻¹) * d⁻¹ :=
        hid d hd d' hd' hd0 hd'0 _ hb
      have hd2 : v * d ^ 2 = d ^ 2 * v := Subgroup.mem_centralizer_iff.mp (hsq d hd) v hv
      have h3 : d * (d * v * d⁻¹) * d⁻¹ = v := by
        calc d * (d * v * d⁻¹) * d⁻¹ = d ^ 2 * v * (d ^ 2)⁻¹ := by simp only [pow_two]; group
          _ = v * d ^ 2 * (d ^ 2)⁻¹ := by rw [hd2]
          _ = v := by group
      have hv2 : v⁻¹ = v := by
        have := F7.isElemAbelian_pow_eq_one hV hv
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      have hb2 : (d * v * d⁻¹)⁻¹ = d * v * d⁻¹ := by
        have := F7.isElemAbelian_pow_eq_one hV hb
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      have hbv : (d * v * d⁻¹) * v = v * (d * v * d⁻¹) := F7.isElemAbelian_comm hV hb hv
      calc d' * ⁅v, d⁆ * d'⁻¹ = d' * (v * (d * v * d⁻¹)⁻¹) * d'⁻¹ := by rw [hc]
        _ = (d' * v * d'⁻¹) * (d' * (d * v * d⁻¹) * d'⁻¹)⁻¹ := by group
        _ = (d * v * d⁻¹) * v⁻¹ := by rw [h1, h2, h3]
        _ = (d * v * d⁻¹) * v := by rw [hv2]
        _ = v * (d * v * d⁻¹) := hbv
        _ = v * (d * v * d⁻¹)⁻¹ := by rw [hb2]
        _ = ⁅v, d⁆ := hc.symm
    calc d' * ⁅v, d⁆ = d' * ⁅v, d⁆ * d'⁻¹ * d' := by group
      _ = ⁅v, d⁆ * d' := by rw [hcomm]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (key hw) d' (Set.mem_singleton d')).symm

variable [Finite G]

theorem le_mc_of_isUniqueM {Mc X I : Subgroup G} (hU : IsUniqueM X Mc) (hXI : X ≤ I)
    (hI : pCoreOf 2 I ≠ ⊥) : I ≤ Mc := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hI
  have hM'c : M' = Mc := hU.2 M' ⟨hM'.1, hXI.trans hM'.2⟩
  rw [← hM'c]
  exact hM'.2

theorem zSOf_le_V {T Mc M : Subgroup G} (hTM : T ≤ M) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    zSOf T Mc M B₀ ≤ V154 T Mc M :=
  commutator_le_of_le_normalizer
    ((preOn_le T (V154 T Mc M) B₀).trans (hTM.trans (le_normalizer_V154 T Mc M)))

theorem barStab_le_barT_of_isUniqueM {T Mc M : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h14 : Lemma15214Concl T Mc M B₀)
    (h15 : IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc)
    {z : G} (hz : z ∈ zSOf T Mc M B₀) (hz1 : z ≠ 1) :
    autOn (M ⊓ Subgroup.centralizer ({z} : Set G)) (V154 T Mc M) ≤
      autOn T (V154 T Mc M) := by
  have hMT : InM T M := hM.1.1
  have hTM : T ≤ M := hMT.2
  have hMV := le_normalizer_V154 T Mc M
  have hVE : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hMT)
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by simpa using hVE.2 x x.2)⟩
  have hzV : z ∈ V154 T Mc M := zSOf_le_V hTM B₀ hz
  have hXI : Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hx.2 z hz
  have hzI : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (hVp.to_le (Subgroup.zpowers_le.mpr hzV))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by rw [Set.mem_singleton_iff.mp hy]
    · intro g hg
      have hgz : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
      have hgc : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := hy
        exact (Commute.zpow_left (show Commute z g from hgz) k).eq
      exact Subgroup.centralizer_le_normalizer _ hgc
  have hI2 : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun hb =>
    hz1 (by
      have := hzI (Subgroup.mem_zpowers z)
      rw [hb, Subgroup.mem_bot] at this
      exact this)
  have hIle : Subgroup.centralizer ({z} : Set G) ≤ Mc := le_mc_of_isUniqueM h15 hXI hI2
  have hMI : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T :=
    (inf_le_inf_left M hIle).trans (h14.inf_eq.1.le.trans h14.inf_eq.2.le)
  have hC : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
      Subgroup.normalizer (V154 T Mc M : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hbot : autOn (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) (V154 T Mc M) = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
    rw [Subgroup.mem_bot]
    exact A4.conjAct_eq_one_iff.mpr hxX.2
  calc autOn (M ⊓ Subgroup.centralizer ({z} : Set G)) (V154 T Mc M)
      ≤ autOn ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T) (V154 T Mc M) :=
        A4.autOn_mono hMI
    _ = autOn (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) (V154 T Mc M) ⊔
          autOn T (V154 T Mc M) := autOn_sup hC (hTM.trans hMV)
    _ = autOn T (V154 T Mc M) := by rw [hbot, bot_sup_eq]

theorem isElemAbelian_V154 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    IsElemAbelian 2 (V154 T Mc M) :=
  isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hM.1.1)

theorem eq_one_of_pow_mul_eq_six {r k : ℕ} (hodd : ¬ 2 ∣ r) (h : r * 2 ^ k = 6) : k = 1 := by
  have hk : k ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    nlinarith
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exfalso
    have : r = 6 := by simpa using h
    omega
  · rfl
  · exfalso
    omega

variable {T Mc M : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}

theorem barT_cases (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hc : Case15213i T Mc M) :
    Nat.card (autOn T (V154 T Mc M)) = 2 ∨
      (Nat.card (autOn T (V154 T Mc M)) = 4 ∧
        Nonempty (↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod 4))) := by
  have hMT : InM T M := hM.1.1
  have hMV := le_normalizer_V154 T Mc M
  have hVE := isElemAbelian_V154 h hM
  rcases hc.1 with h1 | h5
  · left
    obtain ⟨-, hMA, ⟨e⟩⟩ := h1
    have h6 : Nat.card (autOn M (V154 T Mc M)) = 6 := by
      rw [hMA, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M)) :=
      B2F.isSylowTwoOf_autI hVE hMV (isSylowTwoOf_of_le151 h.sylow hMT.2)
    obtain ⟨hle, hp, hodd⟩ := hsyl
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hrel := Subgroup.relIndex_mul_card (H := autOn T (V154 T Mc M))
      (K := autOn M (V154 T Mc M))
    rw [inf_eq_left.mpr hle, h6, hk] at hrel
    rw [hk, eq_one_of_pow_mul_eq_six hodd hrel, pow_one]
  · obtain ⟨-, -, hT, -⟩ := h5
    rcases hT with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]
    · right
      refine ⟨?_, ⟨e⟩⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]

theorem mem_B0_of_sq_eq_one (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hc : Case15213i T Mc M) (hB₀ : IsB0 T Mc M B₀) {x : MulAut (V154 T Mc M)}
    (hx : x ∈ autOn T (V154 T Mc M)) (hx2 : x ^ 2 = 1) : x ∈ B₀ := by
  have hB₀le : B₀ ≤ autOn T (V154 T Mc M) := hB₀.1
  rcases barT_cases h hM hc with hcard | ⟨-, ⟨e⟩⟩
  · have heq : B₀ = autOn T (V154 T Mc M) :=
      Subgroup.eq_of_le_of_card_ge hB₀le (by rw [hcard, hB₀.2.1])
    rw [heq]; exact hx
  · have hcardB' : Nat.card ↥(B₀.subgroupOf (autOn T (V154 T Mc M))) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀le).toEquiv]
      exact hB₀.2.1
    have hB'ne : B₀.subgroupOf (autOn T (V154 T Mc M)) ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hcardB'
      omega
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB'ne
    have hb2 : b ^ 2 = 1 := by
      have : orderOf b ∣ 2 := hcardB' ▸ orderOf_dvd_natCard b
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hb1' : (b : ↥(autOn T (V154 T Mc M))) ≠ 1 := fun h' => hb1 (Subtype.ext h')
    have hb2' : (b : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := by
      have := congrArg (fun y : ↥(B₀.subgroupOf (autOn T (V154 T Mc M))) =>
        (y : ↥(autOn T (V154 T Mc M)))) hb2
      simpa using this
    have hX2 : (⟨x, hx⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    have key : ∀ y z : Multiplicative (ZMod 4), y ^ 2 = 1 → z ^ 2 = 1 → z ≠ 1 → y = 1 ∨ y = z := by
      decide
    rcases key (e ⟨x, hx⟩) (e b) (by rw [← map_pow, hX2, map_one]) (by rw [← map_pow, hb2', map_one])
      (fun h' => hb1' (e.injective (by rw [h', map_one]))) with h' | h'
    · have : (⟨x, hx⟩ : ↥(autOn T (V154 T Mc M))) = 1 := e.injective (by rw [h', map_one])
      have hx1 : x = 1 := congrArg Subtype.val this
      rw [hx1]; exact B₀.one_mem
    · have : (⟨x, hx⟩ : ↥(autOn T (V154 T Mc M))) = b := e.injective h'
      have hxb : (⟨x, hx⟩ : ↥(autOn T (V154 T Mc M))) ∈ B₀.subgroupOf (autOn T (V154 T Mc M)) := by
        rw [this]; exact b.2
      exact Subgroup.mem_subgroupOf.mp hxb

theorem omegaOneOf_autOn_eq (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hc : Case15213i T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    omegaOneOf (autOn T (V154 T Mc M)) = B₀ := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => ?_) ?_
  · exact mem_B0_of_sq_eq_one h hM hc hB₀ hx.1 hx.2
  · intro b hb
    refine Subgroup.subset_closure ⟨hB₀.1 hb, ?_⟩
    have hord : orderOf (⟨b, hb⟩ : B₀) ∣ 2 := hB₀.2.1 ▸ orderOf_dvd_natCard _
    have h2 : (⟨b, hb⟩ : B₀) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    simpa using congrArg Subtype.val h2

theorem autOn_preOn_B0 (hB₀ : IsB0 T Mc M B₀) :
    autOn (preOn T (V154 T Mc M) B₀) (V154 T Mc M) = B₀ :=
  autOn_preOn hB₀.1

theorem preOn_le_sOf152 (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hB₀ : IsB0 T Mc M B₀) :
    preOn T (V154 T Mc M) B₀ ≤ sOf152 T Mc M B₀ := by
  have hTM : T ≤ M := hM.1.1.2
  have hMV := le_normalizer_V154 T Mc M
  have hVE := isElemAbelian_V154 h hM
  have hDN : preOn T (V154 T Mc M) B₀ ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (preOn_le T _ B₀).trans (hTM.trans hMV)
  have hbar := autOn_preOn_B0 hB₀
  have hsq : ∀ d ∈ preOn T (V154 T Mc M) B₀, d ^ 2 ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
    intro d hd
    obtain ⟨-, hdN, hdB⟩ := mem_preOn.mp hd
    have h2 : conjAct (V154 T Mc M) ⟨d, hdN⟩ ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥B₀) (x := ⟨_, hdB⟩)
      rw [hB₀.2.1] at this
      simpa using congrArg Subtype.val this
    have h3 : conjAct (V154 T Mc M) ⟨d ^ 2, Subgroup.pow_mem _ hdN 2⟩ = 1 := by
      rw [← h2, ← map_pow]
      rfl
    exact A4.conjAct_eq_one_iff.mp h3
  have hid : ∀ d ∈ preOn T (V154 T Mc M) B₀, ∀ d' ∈ preOn T (V154 T Mc M) B₀,
      d ∉ Subgroup.centralizer (V154 T Mc M : Set G) →
      d' ∉ Subgroup.centralizer (V154 T Mc M : Set G) →
      ∀ x ∈ V154 T Mc M, d' * x * d'⁻¹ = d * x * d⁻¹ := by
    intro d hd d' hd' hd0 hd'0 x hx
    obtain ⟨-, hdN, hdB⟩ := mem_preOn.mp hd
    obtain ⟨-, hdN', hdB'⟩ := mem_preOn.mp hd'
    have hne : conjAct (V154 T Mc M) ⟨d, hdN⟩ ≠ 1 := fun h1 => hd0 (A4.conjAct_eq_one_iff.mp h1)
    have hne' : conjAct (V154 T Mc M) ⟨d', hdN'⟩ ≠ 1 :=
      fun h1 => hd'0 (A4.conjAct_eq_one_iff.mp h1)
    have heq : (⟨conjAct (V154 T Mc M) ⟨d', hdN'⟩, hdB'⟩ : ↥B₀) =
        ⟨conjAct (V154 T Mc M) ⟨d, hdN⟩, hdB⟩ :=
      eq_of_card_two hB₀.2.1 (fun h1 => hne' (congrArg Subtype.val h1))
        (fun h1 => hne (congrArg Subtype.val h1))
    have heq' : conjAct (V154 T Mc M) ⟨d', hdN'⟩ = conjAct (V154 T Mc M) ⟨d, hdN⟩ :=
      congrArg Subtype.val heq
    have := congrArg (fun a : MulAut (V154 T Mc M) => ((a ⟨x, hx⟩ : V154 T Mc M) : G)) heq'
    simpa [conjAct_apply_coe'] using this
  refine le_inf (preOn_le _ _ _) ?_
  exact le_centralizer_commutator_of_card_two hVE hDN hsq hid

theorem autOn_sOf152_eq (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hc : Case15213i T Mc M)
    (hB₀ : IsB0 T Mc M B₀) (h14 : Lemma15214Concl T Mc M B₀) :
    autOn (sOf152 T Mc M B₀) (V154 T Mc M) = B₀ := by
  have hTM : T ≤ M := hM.1.1.2
  have hMV := le_normalizer_V154 T Mc M
  have hVE := isElemAbelian_V154 h hM
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  have hSle : sOf152 T Mc M B₀ ≤ T := inf_le_left
  have hSN : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hSle.trans hTN
  have hD := preOn_le_sOf152 h hM hB₀
  have hge : B₀ ≤ autOn (sOf152 T Mc M B₀) (V154 T Mc M) := by
    calc B₀ = autOn (preOn T (V154 T Mc M) B₀) (V154 T Mc M) := (autOn_preOn_B0 hB₀).symm
      _ ≤ autOn (sOf152 T Mc M B₀) (V154 T Mc M) := A4.autOn_mono hD
  have hle2 : Nat.card (autOn (sOf152 T Mc M B₀) (V154 T Mc M)) ≤ 2 := by
    rcases h14.cases with ⟨hST, -⟩ | ⟨-, -, hrel⟩
    · have h2 := h14.bar_T hST
      rw [hST]
      exact h2.le
    · have hCV : T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ sOf152 T Mc M B₀ :=
        le_inf inf_le_left
          (inf_le_right.trans (Subgroup.centralizer_le (zSOf_le_V hTM B₀)))
      have hCeq : sOf152 T Mc M B₀ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
          T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
        le_antisymm (inf_le_inf_right _ hSle) (le_inf hCV inf_le_right)
      have hT1 : Nat.card (autOn T (V154 T Mc M)) *
          Nat.card ↥(T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) = Nat.card T :=
        card_autI_mul_card_inf hVE hTN
      have hS1 : Nat.card (autOn (sOf152 T Mc M B₀) (V154 T Mc M)) *
          Nat.card ↥(T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) =
            Nat.card (sOf152 T Mc M B₀) := by
        have := card_autI_mul_card_inf hVE hSN
        rw [hCeq] at this
        exact this
      have hrel2 := Subgroup.relIndex_mul_card (H := sOf152 T Mc M B₀) (K := T)
      rw [inf_eq_left.mpr hSle, hrel] at hrel2
      have hc0 : 0 < Nat.card ↥(T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := Nat.card_pos
      have hmul : Nat.card (autOn T (V154 T Mc M)) *
          Nat.card ↥(T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) =
          (2 * Nat.card (autOn (sOf152 T Mc M B₀) (V154 T Mc M))) *
            Nat.card ↥(T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
        rw [hT1, ← hrel2, ← hS1]; ring
      have hTS := Nat.eq_of_mul_eq_mul_right hc0 hmul
      rcases barT_cases h hM hc with hT2 | ⟨hT4, -⟩
      · omega
      · omega
  exact (Subgroup.eq_of_le_of_card_ge hge (by rw [hB₀.2.1]; exact hle2)).symm

theorem lemma_15_2_25_of_cases (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hc : Case15213i T Mc M)
    (h14 : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → Lemma15214Concl T Mc M B₀) :
    Lemma15225Concl T Mc M := by
  have hTM : T ≤ M := hM.1.1.2
  have hMV := le_normalizer_V154 T Mc M
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  refine ⟨hc, fun B₀ hB₀ => (autOn_sOf152_eq h hM hc hB₀ (h14 B₀ hB₀)).trans
      (omegaOneOf_autOn_eq h hM hc hB₀).symm, fun B₀ hB₀ => ?_, fun B₀ hB₀ => ?_⟩
  ·
    have hS := autOn_sOf152_eq h hM hc hB₀ (h14 B₀ hB₀)
    have hSD : sOf152 T Mc M B₀ ≤ preOn T (V154 T Mc M) B₀ := by
      intro x hx
      have hxT : x ∈ T := (inf_le_left : sOf152 T Mc M B₀ ≤ T) hx
      have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hTN hxT
      refine mem_preOn.mpr ⟨hxT, hxN, ?_⟩
      have : conjAct (V154 T Mc M) ⟨x, hxN⟩ ∈ autOn (sOf152 T Mc M B₀) (V154 T Mc M) :=
        mem_autOn_iff_exists.mpr ⟨x, hxN, hx, rfl⟩
      rwa [hS] at this
    exact Subgroup.commutator_mono le_rfl hSD
  ·
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    obtain ⟨htT, hto⟩ := ht
    have htN : t ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hTN htT
    have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
    have ha2 : conjAct (V154 T Mc M) ⟨t, htN⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨t, htN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) ^ 2 = 1 :=
        Subtype.ext (by simpa using ht2)
      rw [this, map_one]
    have haT : conjAct (V154 T Mc M) ⟨t, htN⟩ ∈ autOn T (V154 T Mc M) :=
      mem_autOn_iff_exists.mpr ⟨t, htN, htT, rfl⟩
    have haB := mem_B0_of_sq_eq_one h hM hc hB₀ haT ha2
    exact preOn_le_sOf152 h hM hB₀ (mem_preOn.mpr ⟨htT, htN, haB⟩)

theorem case15213i_of_claim {H : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h13 : Lemma15213Concl T Mc M H)
    (h14 : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → Lemma15214Concl T Mc M B₀)
    (h15 : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc)
    (hF : Case15213ii T Mc M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∃ z ∈ zSOf T Mc M B₀, z ≠ 1 ∧
        ¬ autOn (M ⊓ Subgroup.centralizer ({z} : Set G)) (V154 T Mc M) ≤
          autOn T (V154 T Mc M)) :
    Case15213i T Mc M := by
  rcases h13.cases with hc | hii
  · exact hc
  · exfalso
    obtain ⟨B₀, hB₀, -, -⟩ := h13.exists_B0
    obtain ⟨z, hz, hz1, hzn⟩ := hF hii B₀ hB₀
    exact hzn (barStab_le_barT_of_isUniqueM h hM (h14 B₀ hB₀) (h15 B₀ hB₀) hz hz1)

theorem stageLemma15225_of (h13 : StageLemma15213) (h14 : StageLemma15214)
    (h15 : StageTheorem15215) (hF : Claim15225F) : StageLemma15225 := by
  intro G _ _ T Mc M hs
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  have hc : Case15213i T Mc M :=
    case15213i_of_claim hs.qtfe hs.mf (h13 G T Mc M hs H hH)
      (fun B₀ hB₀ => h14 G T Mc M hs B₀ hB₀) (fun B₀ hB₀ => h15 G T Mc M hs B₀ hB₀)
      (fun hii B₀ hB₀ => hF G T Mc M hs H hH hii B₀ hB₀)
  exact lemma_15_2_25_of_cases hs.qtfe hs.mf hc (fun B₀ hB₀ => h14 G T Mc M hs B₀ hB₀)

end CFSG.Quasithin
