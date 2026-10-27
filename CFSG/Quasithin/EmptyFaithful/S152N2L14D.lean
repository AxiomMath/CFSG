module

public import CFSG.Quasithin.EmptyFaithful.S152N2Cases
public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152N2L14A
public import CFSG.Quasithin.EmptyFaithful.S152N2L14B
public import CFSG.Quasithin.EmptyFaithful.S152N2L14C
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.Background.E4Solv
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.S152N2Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N2
open scoped commutatorElement

@[expose] def Om4Z152 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X Tb B₀ : Subgroup (MulAut V)), IsOmegaFourPlus X →
    IsSylowTwoOf Tb X → B₀ ≤ Tb → Nat.card B₀ = 2 → oddCoreIn X = ⁅oddCoreIn X, B₀⁆ →
    (¬ ∀ t ∈ Tb, ∀ z ∈ commV B₀, t z = z) ∧
      ∀ y ∈ X, y ^ 3 = 1 → (∀ z ∈ fixV Tb, y z = z) → y = 1

variable {G : Type} [Group G] [Finite G]

structure Data14 (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Prop where
  pgroup : IsPGroup 2 T
  elemAbelian : IsElemAbelian 2 (V154 T Mc M)
  card_V : Nat.card (V154 T Mc M) = 16
  V_le_T : V154 T Mc M ≤ T
  T_le_M : T ≤ M
  M_le_normalizer : M ≤ Subgroup.normalizer (V154 T Mc M : Set G)
  Z_le_V : quasithinOmegaOneCenter T ≤ V154 T Mc M
  zS_eq : zSOf T Mc M B₀ =
    V154 T Mc M ⊓ Subgroup.centralizer (preOn T (V154 T Mc M) B₀ : Set G)
  card_zS : Nat.card (zSOf T Mc M B₀) = 4
  normal_zS : T ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G)
  isB0 : IsB0 T Mc M B₀
  T_le_Mc : T ≤ Mc
  sylow_bar : IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M))
  centralizer_V_le : Subgroup.centralizer (V154 T Mc M : Set G) ≤ Mc
  not_M_le : ¬ M ≤ Mc
  ord : OrdLE T Mc M
  baum_eq : baum T = baum (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
  three_centralizes : ∀ g ∈ Mc, (∃ a : ℕ, g ^ (3 ^ a) = 1) →
    g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  centralizer_Z_le : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc
  shape : Case15213i T Mc M ∨ IsOmegaFourPlusOn M (V154 T Mc M)
  q_eq : ∀ hV : IsElemAbelian 2 (V154 T Mc M),
    @qOf ↥(V154 T Mc M) (commGroupOfElemAbelian hV) inferInstance (autOn M (V154 T Mc M)) = 2

namespace S152N2

variable {T Mc M : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}

omit [Finite G] in
theorem Z_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.2

omit [Finite G] in
theorem mem_Z_of {T : Subgroup G} {z : G} (hzT : z ∈ T) (hzc : z ∈ Subgroup.centralizer (T : Set G))
    (hz2 : z * z = 1) : z ∈ quasithinOmegaOneCenter T :=
  Subgroup.subset_closure ⟨⟨hzT, hzc⟩, by rw [sq]; exact hz2⟩

omit [Finite G] in
theorem sq_eq_one_of_V {V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G} (hx : x ∈ V) :
    x * x = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hV hx

theorem zS_le_V (hD : Data14 T Mc M B₀) : zSOf T Mc M B₀ ≤ V154 T Mc M := by
  rw [hD.zS_eq]; exact inf_le_left

theorem P_le_T (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    preOn T (V154 T Mc M) B₀ ≤ T := preOn_le T _ _

theorem Z_le_zS (hD : Data14 T Mc M B₀) : quasithinOmegaOneCenter T ≤ zSOf T Mc M B₀ := by
  rw [hD.zS_eq]
  refine le_inf hD.Z_le_V ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact Subgroup.mem_centralizer_iff.mp (Z_le_center T hz) p (P_le_T T Mc M B₀ hp)

theorem zS_le_T (hD : Data14 T Mc M B₀) : zSOf T Mc M B₀ ≤ T := (zS_le_V hD).trans hD.V_le_T

theorem zS_sq (hD : Data14 T Mc M B₀) : ∀ k ∈ zSOf T Mc M B₀, k * k = 1 := fun _ hk =>
  sq_eq_one_of_V hD.elemAbelian (zS_le_V hD hk)

theorem zS_elemAbelian (hD : Data14 T Mc M B₀) : IsElemAbelian 2 (zSOf T Mc M B₀) :=
  isElemAbelian_mono151 (zS_le_V hD) hD.elemAbelian

theorem Z_eq_inf (hD : Data14 T Mc M B₀) :
    quasithinOmegaOneCenter T = zSOf T Mc M B₀ ⊓ Subgroup.centralizer (T : Set G) := by
  apply le_antisymm
  · exact le_inf (Z_le_zS hD) (Z_le_center T)
  · rintro z ⟨hzS, hzc⟩
    exact mem_Z_of (zS_le_T hD hzS) hzc (zS_sq hD z hzS)

theorem Z_eq_zS_of_S_eq (hD : Data14 T Mc M B₀) (hST : sOf152 T Mc M B₀ = T) :
    quasithinOmegaOneCenter T = zSOf T Mc M B₀ := by
  apply le_antisymm (Z_le_zS hD)
  intro z hz
  have hT : T ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := inf_eq_left.mp hST
  refine mem_Z_of (zS_le_T hD hz) (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_) (zS_sq hD z hz)
  exact (Subgroup.mem_centralizer_iff.mp (hT ht) z hz).symm

theorem Z_card_of_ne (hD : Data14 T Mc M B₀) (hne : sOf152 T Mc M B₀ ≠ T) :
    Nat.card (quasithinOmegaOneCenter T) = 2 := by
  obtain ⟨-, hfix⟩ := klein_action hD.pgroup (zS_le_T hD) hD.normal_zS (zS_sq hD) hD.card_zS
  rw [Z_eq_inf hD]
  exact hfix hne

theorem relIndex_S_of_ne (hD : Data14 T Mc M B₀) (hne : sOf152 T Mc M B₀ ≠ T) :
    (sOf152 T Mc M B₀).relIndex T = 2 := by
  obtain ⟨hidx, -⟩ := klein_action hD.pgroup (zS_le_T hD) hD.normal_zS (zS_sq hD) hD.card_zS
  have h1 : (sOf152 T Mc M B₀).relIndex T ≠ 1 := fun h =>
    hne (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h))
  have h0 : (sOf152 T Mc M B₀).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx' : (sOf152 T Mc M B₀).relIndex T ≤ 2 := hidx
  omega

theorem syl_card_facts {Γ : Type*} [Group Γ] [Finite Γ] {T' X : Subgroup Γ}
    (hs : IsSylowTwoOf T' X) :
    ∃ (a idx : ℕ), Nat.card T' = 2 ^ a ∧ idx * 2 ^ a = Nat.card X ∧ ¬ 2 ∣ idx := by
  obtain ⟨a, ha⟩ := hs.2.1.exists_card_eq
  refine ⟨a, (T'.subgroupOf X).index, ha, ?_, hs.2.2⟩
  have h1 := Subgroup.index_mul_card (T'.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.1).toEquiv, ha] at h1
  exact h1

theorem le_of_pow_dvd {n a : ℕ} (hn : n ≠ 0) (hd : 2 ^ a ∣ n) : a ≤ n := by
  have h1 : 2 ^ a ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : a < 2 ^ a := Nat.lt_two_pow_self
  omega

theorem card_Tbar_two {Γ : Type*} [Group Γ] [Finite Γ] {T' X : Subgroup Γ} (hs : IsSylowTwoOf T' X)
    (h : Nat.card X = 6 ∨ Nat.card X = 10) : Nat.card T' = 2 := by
  obtain ⟨a, idx, ha, hidx, h2⟩ := syl_card_facts hs
  have hn0 : Nat.card X ≠ 0 := by rcases h with h | h <;> omega
  have hd : 2 ^ a ∣ Nat.card X := ⟨idx, by rw [← hidx, mul_comm]⟩
  have hale : a ≤ Nat.card X := le_of_pow_dvd hn0 hd
  have hle : Nat.card X ≤ 10 := by rcases h with h | h <;> omega
  have ha10 : a ≤ 10 := hale.trans hle
  rw [ha]
  interval_cases a <;> simp_all <;> omega

theorem card_Tbar_four {Γ : Type*} [Group Γ] [Finite Γ] {T' X : Subgroup Γ} (hs : IsSylowTwoOf T' X)
    (h : Nat.card X = 20 ∨ Nat.card X = 36) : Nat.card T' = 4 := by
  obtain ⟨a, idx, ha, hidx, h2⟩ := syl_card_facts hs
  have hn0 : Nat.card X ≠ 0 := by rcases h with h | h <;> omega
  have hd : 2 ^ a ∣ Nat.card X := ⟨idx, by rw [← hidx, mul_comm]⟩
  have hale : a ≤ Nat.card X := le_of_pow_dvd hn0 hd
  have hle : Nat.card X ≤ 36 := by rcases h with h | h <;> omega
  have ha36 : a ≤ 36 := hale.trans hle
  rw [ha]
  interval_cases a <;> simp_all <;> omega

theorem S_eq_T_of_card_two (hD : Data14 T Mc M B₀) (h2 : Nat.card (autOn T (V154 T Mc M)) = 2) :
    sOf152 T Mc M B₀ = T := by
  have hB₀ : B₀ = autOn T (V154 T Mc M) :=
    Subgroup.eq_of_le_of_card_ge hD.isB0.1 (by rw [h2, hD.isB0.2.1])
  have hPT : preOn T (V154 T Mc M) B₀ = T := by
    apply le_antisymm (P_le_T T Mc M B₀)
    intro x hx
    have hxN := hD.M_le_normalizer (hD.T_le_M hx)
    rw [hB₀]
    exact mem_preOn.mpr ⟨hx, hxN, mem_autOn_of_mem hxN hx⟩
  have : T ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hD.zS_eq] at hz
    have := Subgroup.mem_centralizer_iff.mp hz.2 t (hPT.ge ht)
    exact this.symm
  exact inf_eq_left.mpr this

theorem card_six_of_equiv {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) : Nat.card X = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm]
  simp [Nat.factorial]

theorem card_ten_of_equiv {X : Type*} [Group X] (e : X ≃* DihedralGroup 5) : Nat.card X = 10 := by
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_twenty_of_equiv {X : Type*} [Group X] (e : X ≃* ↥(CFSG.Open.Sz 0)) :
    Nat.card X = 20 := by
  rw [Nat.card_congr e.toEquiv]
  exact card_sz_zero_eq_twenty

theorem shape_of_ne (hD : Data14 T Mc M B₀) (hne : sOf152 T Mc M B₀ ≠ T) :
    Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
      IsOmegaFourPlusOn M (V154 T Mc M) := by
  rcases hD.shape with ⟨-, hsmall⟩ | hΩ
  · rcases hsmall with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact absurd (S_eq_T_of_card_two hD
        (card_Tbar_two hD.sylow_bar (Or.inl (card_six_of_equiv e)))) hne
    · exact absurd (S_eq_T_of_card_two hD
        (card_Tbar_two hD.sylow_bar (Or.inr (card_ten_of_equiv e)))) hne
    · exact Or.inl ⟨e⟩
  · exact Or.inr hΩ

theorem cases14 (hD : Data14 T Mc M B₀) :
    (sOf152 T Mc M B₀ = T ∧ quasithinOmegaOneCenter T = zSOf T Mc M B₀ ∧
        Nat.card (zSOf T Mc M B₀) = 4 ∧ IsElemAbelian 2 (zSOf T Mc M B₀)) ∨
      ((Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
          IsOmegaFourPlusOn M (V154 T Mc M)) ∧
        Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2) := by
  by_cases hST : sOf152 T Mc M B₀ = T
  · exact Or.inl ⟨hST, Z_eq_zS_of_S_eq hD hST, hD.card_zS, zS_elemAbelian hD⟩
  · exact Or.inr ⟨shape_of_ne hD hST, Z_card_of_ne hD hST, relIndex_S_of_ne hD hST⟩

theorem baum_le14 (hD : Data14 T Mc M B₀) : baum T ≤ sOf152 T Mc M B₀ := by
  rw [hD.baum_eq]
  refine (inf_le_left : baum (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ≤ _).trans
    (le_inf inf_le_left ?_)
  intro x hx
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (zS_le_V hD)) hx.2

theorem zS_eq14 (hD : Data14 T Mc M B₀) :
    zSOf T Mc M B₀ = omegaOneCenterOf (sOf152 T Mc M B₀) := by
  by_cases hST : sOf152 T Mc M B₀ = T
  · rw [hST]
    exact (Z_eq_zS_of_S_eq hD hST).symm
  · have hSc : ∀ s ∈ sOf152 T Mc M B₀, ∀ z ∈ zSOf T Mc M B₀, s * z = z * s := by
      intro s hs z hz
      exact (Subgroup.mem_centralizer_iff.mp hs.2 z hz).symm
    refine omegaOneCenter_eq_of_relIndex_two inf_le_left (relIndex_S_of_ne hD hST) ?_ (zS_sq hD)
      hSc (Z_card_of_ne hD hST) hD.card_zS
    intro z hz
    refine ⟨zS_le_T hD hz, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact F7.isElemAbelian_comm hD.elemAbelian (zS_le_V hD hy) (zS_le_V hD hz)

omit [Finite G] in
theorem le_sup_of_autOn_le {M V T R : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hTM : T ≤ M) (hRM : R ≤ M) (hRT : autOn R V ≤ autOn T V) :
    R ≤ (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T := by
  have hNM : (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T ≤ M := sup_le inf_le_left hTM
  intro x hx
  refine mem_of_conjAct_mem_autOn hMV hNM le_sup_left (hRM hx) ?_
  exact A4.autOn_mono (le_sup_right : T ≤ (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T)
    (hRT (mem_autOn_of_mem (hMV (hRM hx)) hx))

omit [Finite G] in
theorem le_of_autOn_le {M V R : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hRM : R ≤ M) (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ R) (h : autOn M V ≤ autOn R V) :
    M ≤ R := fun _ hx =>
  mem_of_conjAct_mem_autOn hMV hRM hC hx (h (mem_autOn_of_mem (hMV hx) hx))

theorem relIndex_Tbar_prime (hD : Data14 T Mc M B₀)
    (hsmall : IsSmallGroup152 ↥(autOn M (V154 T Mc M))) :
    ((autOn T (V154 T Mc M)).relIndex (autOn M (V154 T Mc M))).Prime := by
  have hmul := Subgroup.relIndex_mul_card (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M))
  rw [inf_of_le_left (A4.autOn_mono hD.T_le_M)] at hmul
  rcases card_of_isSmallGroup152 hsmall with h | h | h
  · have h2 := card_Tbar_two hD.sylow_bar (Or.inl h)
    rw [h2, h] at hmul
    have : (autOn T (V154 T Mc M)).relIndex (autOn M (V154 T Mc M)) = 3 := by omega
    rw [this]; norm_num
  · have h2 := card_Tbar_two hD.sylow_bar (Or.inr h)
    rw [h2, h] at hmul
    have : (autOn T (V154 T Mc M)).relIndex (autOn M (V154 T Mc M)) = 5 := by omega
    rw [this]; norm_num
  · have h2 := card_Tbar_four hD.sylow_bar (Or.inl h)
    rw [h2, h] at hmul
    have : (autOn T (V154 T Mc M)).relIndex (autOn M (V154 T Mc M)) = 5 := by omega
    rw [this]; norm_num

theorem eq_of_le_of_no_three {Γ : Type*} [Group Γ] [Finite Γ] {X T' R' : Subgroup Γ}
    (hX : Nat.card X = 36) (hT : Nat.card T' = 4) (hTR : T' ≤ R') (hRX : R' ≤ X)
    (h3 : ∀ y ∈ R', y ^ 3 = 1 → y = 1) : R' = T' := by
  apply le_antisymm _ hTR
  have hdvdX : Nat.card R' ∣ 36 := hX ▸ Subgroup.card_dvd_of_le hRX
  have hdvdT : 4 ∣ Nat.card R' := hT ▸ Subgroup.card_dvd_of_le hTR
  have h3n : ¬ 3 ∣ Nat.card R' := by
    intro h
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥R') 3 h
    have hy3 : (y : Γ) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (y : Γ)
      rwa [Subgroup.orderOf_coe, hy] at this
    have hy1 : y = 1 := Subtype.ext (h3 y y.2 hy3)
    have h1 : orderOf y = 1 := by rw [hy1]; exact orderOf_one
    rw [hy] at h1
    omega
  have h4 : Nat.card R' = 4 := by
    have hle : Nat.card R' ≤ 36 := Nat.le_of_dvd (by norm_num) hdvdX
    interval_cases hR : Nat.card R' <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hTR (by rw [h4, hT])).symm.le

theorem coe_mem_Z_of_mem_fixV (hD : Data14 T Mc M B₀) (hV' : IsElemAbelian 2 (V154 T Mc M))
    {z : ↥(V154 T Mc M)}
    (hz : z ∈ @fixV ↥(V154 T Mc M) (commGroupOfElemAbelian hV') (autOn T (V154 T Mc M))) :
    (z : G) ∈ quasithinOmegaOneCenter T := by
  have h := map_fixV_autOn hV' (hD.T_le_M.trans hD.M_le_normalizer)
  have hz' : (z : G) ∈ (@fixV ↥(V154 T Mc M) (commGroupOfElemAbelian hV')
      (autOn T (V154 T Mc M))).map (V154 T Mc M).subtype := ⟨z, hz, rfl⟩
  rw [h] at hz'
  exact mem_Z_of (hD.V_le_T z.2) hz'.2 (sq_eq_one_of_V hD.elemAbelian z.2)

theorem no_three_autOn (hD : Data14 T Mc M B₀) (hV' : IsElemAbelian 2 (V154 T Mc M))
    (hom : ∀ y ∈ autOn M (V154 T Mc M), y ^ 3 = 1 →
      (∀ z ∈ @fixV ↥(V154 T Mc M) (commGroupOfElemAbelian hV') (autOn T (V154 T Mc M)),
        y z = z) → y = 1) :
    ∀ y ∈ autOn (M ⊓ Mc) (V154 T Mc M), y ^ 3 = 1 → y = 1 := by
  intro y hy hy3
  by_contra hy1
  have hRN : M ⊓ Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    inf_le_left.trans hD.M_le_normalizer
  obtain ⟨g₀, hg₀N, hg₀R, hg₀⟩ := mem_autOn_iff_exists.mp hy
  let φ : ↥(M ⊓ Mc) →* MulAut ↥(V154 T Mc M) := (conjAct (V154 T Mc M)).comp (Subgroup.inclusion hRN)
  have hφ : φ ⟨g₀, hg₀R⟩ = y := hg₀
  obtain ⟨g, a, hga, hφg⟩ := exists_three_power_lift φ ⟨g₀, hg₀R⟩ (isOfFinOrder_of_finite _)
    (by rw [hφ]; exact hy3) (by rw [hφ]; exact hy1)
  have hgMc : (g : G) ∈ Mc := g.2.2
  have hg3 : ∃ a : ℕ, (g : G) ^ (3 ^ a) = 1 := ⟨a, by simpa using congrArg Subtype.val hga⟩
  have hgZ := hD.three_centralizes (g : G) hgMc hg3
  have hyM : y ∈ autOn M (V154 T Mc M) := A4.autOn_mono (inf_le_left : M ⊓ Mc ≤ M) hy
  refine hy1 (hom y hyM hy3 fun z hz => ?_)
  have hzZ := coe_mem_Z_of_mem_fixV hD hV' hz
  have hcomm : (z : G) * (g : G) = (g : G) * (z : G) := Subgroup.mem_centralizer_iff.mp hgZ _ hzZ
  rw [← hφ, ← hφg]
  apply Subtype.ext
  show ((conjAct (V154 T Mc M) ⟨(g : G), hRN g.2⟩ z : ↥(V154 T Mc M)) : G) = (z : G)
  rw [conj_coe_apply]
  calc (g : G) * (z : G) * (g : G)⁻¹ = (z : G) * (g : G) * (g : G)⁻¹ := by rw [hcomm]
    _ = (z : G) := by group

theorem autOn_inf_Mc_eq (hD : Data14 T Mc M B₀) (hΩ : Omega4PlusIsS3xS3) (hOm : Om4Z152) :
    autOn (M ⊓ Mc) (V154 T Mc M) = autOn T (V154 T Mc M) := by
  have hTR : T ≤ M ⊓ Mc := le_inf hD.T_le_M hD.T_le_Mc
  have hCR : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ Mc :=
    fun x hx => ⟨hx.1, hD.centralizer_V_le hx.2⟩
  have hRM : M ⊓ Mc ≤ M := inf_le_left
  have hTRb : autOn T (V154 T Mc M) ≤ autOn (M ⊓ Mc) (V154 T Mc M) := A4.autOn_mono hTR
  have hRMb : autOn (M ⊓ Mc) (V154 T Mc M) ≤ autOn M (V154 T Mc M) := A4.autOn_mono hRM
  rcases hD.shape with ⟨-, hsmall⟩ | hΩ4
  · rcases eq_or_eq_of_relIndex_prime hTRb hRMb (relIndex_Tbar_prime hD hsmall) with h | h
    · exact h
    · exfalso
      exact hD.not_M_le ((le_of_autOn_le hD.M_le_normalizer hRM hCR h.symm.le).trans inf_le_right)
  · obtain ⟨hV', hΩ'⟩ := hΩ4
    obtain ⟨e⟩ := @hΩ ↥(V154 T Mc M) (commGroupOfElemAbelian hV') inferInstance _ hΩ'
    have h36 : Nat.card (autOn M (V154 T Mc M)) = 36 := card_of_equiv_D33 e
    have h4 : Nat.card (autOn T (V154 T Mc M)) = 4 := card_Tbar_four hD.sylow_bar (Or.inr h36)
    have hOm' := (@hOm ↥(V154 T Mc M) (commGroupOfElemAbelian hV') inferInstance
      (autOn M (V154 T Mc M)) (autOn T (V154 T Mc M)) B₀ hΩ' hD.sylow_bar hD.isB0.1
      hD.isB0.2.1 hD.isB0.2.2).2
    exact eq_of_le_of_no_three h36 h4 hTRb hRMb (no_three_autOn hD hV' hOm')

theorem inf_eq14 (hD : Data14 T Mc M B₀) (hΩ : Omega4PlusIsS3xS3) (hOm : Om4Z152) :
    M ⊓ Mc = M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T := by
  have h1 : M ⊓ Mc ≤ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T :=
    le_sup_of_autOn_le hD.M_le_normalizer hD.T_le_M inf_le_left (autOn_inf_Mc_eq hD hΩ hOm).le
  have h2 : (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T ≤
      M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine sup_le (le_inf inf_le_left ?_) (le_inf hD.T_le_M ?_)
    · intro x hx
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hD.Z_le_V) hx.2
    · exact Subgroup.le_centralizer_iff.mpr (Z_le_center T)
  have h3 : M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M ⊓ Mc :=
    inf_le_inf_left M hD.centralizer_Z_le
  exact ⟨le_antisymm (h1.trans h2) h3, le_antisymm (h3.trans h1) h2⟩

theorem mc_eq14 (hD : Data14 T Mc M B₀)
    (hinf : M ⊓ Mc = M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Mc = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  apply le_antisymm _ hD.centralizer_Z_le
  intro h hh
  obtain ⟨a, ha, c, hc, rfl⟩ := hD.ord h hh
  have haZ : a ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    have : a ∈ M ⊓ Mc := ⟨ha.2, ha.1⟩
    rw [hinf] at this
    exact this.2
  have hcZ : c ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ _)) hc.2
  exact Subgroup.mul_mem _ haZ hcZ

section Params

variable {W : Type*} [CommGroup W] [Finite W]

theorem two_le_rkIdx_of_qOf (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hq : qOf X = 2)
    {t : MulAut W} (htX : t ∈ X) (ht2 : orderOf t = 2) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; omega
  have hle : ((2 : ℚ) : WithTop ℚ) ≤ kq X 2 := by
    have h2 : (2 : WithTop ℚ) ≤ kq X 2 := le_of_eq hq.symm
    simpa using h2
  have hA : IsA2 X (Subgroup.zpowers t) :=
    ⟨Subgroup.zpowers_le.mpr htX, fun h => ht1 (Subgroup.zpowers_eq_bot.mp h),
      E3.isElemAbelian2_zpowers ht⟩
  have hcs : commSeries (Subgroup.zpowers t) 2 = ⊥ :=
    (isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hW ht)
  have h2 := le_kq_iff.mp hle (Subgroup.zpowers t) hA hcs
  unfold rAV at h2
  have hrk : rk (Subgroup.zpowers t) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, ht2]
    exact padicValNat_self
  rw [hrk] at h2
  have h3 : (2 : ℚ) ≤ (rkIdx (fixV (Subgroup.zpowers t)) : ℚ) := by simpa using h2
  exact_mod_cast h3

theorem mParam_eq_two (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hq : qOf X = 2)
    (hev : Even (Nat.card X)) {b : MulAut W} (hbX : b ∈ X) (hb2 : orderOf b = 2)
    (hbr : rkIdx (fixV (Subgroup.zpowers b)) = 2) : E3.mParam X = 2 := by
  unfold E3.mParam
  simp only [hev, ↓reduceIte]
  have hne : {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty :=
    ⟨2, b, hbX, hb2, hbr.symm⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨b, hbX, hb2, hbr.symm⟩
  · obtain ⟨t, htX, ht2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    exact two_le_rkIdx_of_qOf hW hq htX ht2

end Params

theorem card_fixV_autI_P (hD : Data14 T Mc M B₀) :
    Nat.card (fixV (autI hD.elemAbelian (preOn T (V154 T Mc M) B₀))) = 4 := by
  have hP : preOn T (V154 T Mc M) B₀ ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (P_le_T T Mc M B₀).trans (hD.T_le_M.trans hD.M_le_normalizer)
  rw [card_fixV_autI hD.elemAbelian hP, ← hD.zS_eq]
  exact hD.card_zS

theorem params14 (hD : Data14 T Mc M B₀) (hΩ : Omega4PlusIsS3xS3) :
    ∃ hV : IsElemAbelian 2 (V154 T Mc M),
      E3.mParam (autI hV M) = 2 ∧ E3.aParam (autI hV M) = 1 := by
  have hV := hD.elemAbelian
  refine ⟨hV, ?_⟩
  have hsolv : Group.IsSolvable ↥(autOn M (V154 T Mc M)) ∧
      CFSG.Open.pCore 2 ↥(autOn M (V154 T Mc M)) = ⊥ := by
    rcases hD.shape with ⟨-, hsmall⟩ | ⟨hV', hΩ'⟩
    · exact ⟨isSolvable_of_isSmallGroup152 hsmall, pCore_eq_bot_of_isSmallGroup152 hsmall⟩
    · obtain ⟨e⟩ := @hΩ ↥(V154 T Mc M) (commGroupOfElemAbelian hV') inferInstance _ hΩ'
      exact ⟨isSolvable_of_equiv_D33 e, pCore_eq_bot_of_equiv_D33 e⟩
  have hBM : B₀ ≤ autOn M (V154 T Mc M) := hD.isB0.1.trans (A4.autOn_mono hD.T_le_M)
  have hev : Even (Nat.card ↥(autOn M (V154 T Mc M))) := by
    have : Nat.card B₀ ∣ Nat.card ↥(autOn M (V154 T Mc M)) := Subgroup.card_dvd_of_le hBM
    rw [hD.isB0.2.1] at this
    exact even_iff_two_dvd.mpr this
  have hW : ∀ w : IntMod (V154 T Mc M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  refine ⟨?_, E3.e4_1 hW hsolv.1 hsolv.2 hev⟩
  obtain ⟨b, hb1, hb2, hB₀b⟩ := exists_zpowers_eq_of_card_two hD.isB0.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbord : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hbB : b ∈ B₀ := hB₀b ▸ Subgroup.mem_zpowers b
  have hbX : b ∈ autOn M (V154 T Mc M) := hBM hbB
  set b' : MulAut (IntMod (V154 T Mc M) hV) := b with hb'
  have hbord' : orderOf b' = 2 := hbord
  have hbX' : b' ∈ autI hV M := hbX
  have hautI : autI hV (preOn T (V154 T Mc M) B₀) = Subgroup.zpowers b' :=
    (autOn_preOn hD.isB0.1).trans hB₀b
  have hfc : Nat.card (fixV (Subgroup.zpowers b')) = 4 := by
    rw [← hautI]
    exact card_fixV_autI_P hD
  have hidx : (fixV (Subgroup.zpowers b')).index = 4 := by
    have h := Subgroup.index_mul_card (fixV (Subgroup.zpowers b'))
    rw [hfc] at h
    have hc : Nat.card (IntMod (V154 T Mc M) hV) = 16 := hD.card_V
    omega
  have hbr : rkIdx (fixV (Subgroup.zpowers b')) = 2 := by
    unfold rkIdx
    rw [hidx, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  exact mParam_eq_two hW (hD.q_eq hV) hev hbX' hbord' hbr

theorem Tbar_fixes_zS (hST : sOf152 T Mc M B₀ = T) :
    ∀ t ∈ autOn T (V154 T Mc M), ∀ z : ↥(V154 T Mc M), (z : G) ∈ zSOf T Mc M B₀ → t z = z := by
  intro t ht z hz
  obtain ⟨g, hgN, hgT, rfl⟩ := mem_autOn_iff_exists.mp ht
  have hT : T ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := inf_eq_left.mp hST
  have hcomm : (z : G) * g = g * (z : G) := Subgroup.mem_centralizer_iff.mp (hT hgT) z hz
  apply Subtype.ext
  rw [conj_coe_apply]
  calc g * (z : G) * g⁻¹ = (z : G) * g * g⁻¹ := by rw [← hcomm]
    _ = (z : G) := by group

theorem comm_of_sq_one {Γ : Type*} [Group Γ] {x y : Γ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have h1 : x⁻¹ = x := by
    have : x * x = 1 := by rw [← sq]; exact hx
    exact inv_eq_of_mul_eq_one_right this
  have h2 : y⁻¹ = y := by
    have : y * y = 1 := by rw [← sq]; exact hy
    exact inv_eq_of_mul_eq_one_right this
  have h3 : (x * y)⁻¹ = x * y := by
    have : (x * y) * (x * y) = 1 := by rw [← sq]; exact hxy
    exact inv_eq_of_mul_eq_one_right this
  calc x * y = (x * y)⁻¹ := h3.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [h1, h2]

theorem false_of_sz (hD : Data14 T Mc M B₀) (hST : sOf152 T Mc M B₀ = T)
    (e : ↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) : False := by
  have hV := hD.elemAbelian
  have h20 : Nat.card ↥(autOn M (V154 T Mc M)) = 20 := card_twenty_of_equiv e
  have h4 : Nat.card ↥(autOn T (V154 T Mc M)) = 4 := card_Tbar_four hD.sylow_bar (Or.inl h20)
  have hTM' : autOn T (V154 T Mc M) ≤ autOn M (V154 T Mc M) := A4.autOn_mono hD.T_le_M
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcT, hc2⟩ : ∃ c ∈ autOn T (V154 T Mc M), c ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsmall : IsSmallGroup152 ↥(autOn M (V154 T Mc M)) := Or.inr (Or.inr ⟨e⟩)
    have hle := S152Fin.card_le_two_of_isSmallGroup152 hsmall
      (E := (autOn T (V154 T Mc M)).subgroupOf (autOn M (V154 T Mc M)))
      (fun a ha b hb => by
        apply Subtype.ext
        have hax : (a : MulAut ↥(V154 T Mc M)) ∈ autOn T (V154 T Mc M) := ha
        have hbx : (b : MulAut ↥(V154 T Mc M)) ∈ autOn T (V154 T Mc M) := hb
        exact comm_of_sq_one (hall _ hax) (hall _ hbx)
          (hall _ ((autOn T (V154 T Mc M)).mul_mem hax hbx)))
      (fun a ha => by
        apply Subtype.ext
        exact hall _ ha)
    have hcard : Nat.card ↥((autOn T (V154 T Mc M)).subgroupOf (autOn M (V154 T Mc M))) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM').toEquiv, h4]
    omega
  have hc4 : c ^ 4 = 1 := by
    have h1 : (⟨c, hcT⟩ : ↥(autOn T (V154 T Mc M))) ^ Nat.card ↥(autOn T (V154 T Mc M)) = 1 :=
      pow_card_eq_one'
    rw [h4] at h1
    exact congrArg Subtype.val h1
  have hord : orderOf c = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c) (by simpa using hc2) (by simpa using hc4)
    simpa using this
  have hTz : autOn T (V154 T Mc M) = Subgroup.zpowers c := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcT)
    rw [Nat.card_zpowers, hord, h4]
  obtain ⟨b, hb1, hb2, hB₀b⟩ := exists_zpowers_eq_of_card_two hD.isB0.2.1
  have hbT : b ∈ Subgroup.zpowers c := hTz ▸ hD.isB0.1 (hB₀b ▸ Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbT
  have hb : b = c ^ 2 := by
    have hmod : c ^ (k % (orderOf c : ℤ)) = c ^ k := zpow_mod_orderOf c k
    rw [hord] at hmod
    have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h4' : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hcases : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨ k % ((4 : ℕ) : ℤ) = 2 ∨
        k % ((4 : ℕ) : ℤ) = 3 := by omega
    rcases hcases with h | h | h | h
    · rw [h, zpow_zero] at hmod
      exact absurd (hk ▸ hmod.symm) hb1
    · rw [h, zpow_one] at hmod
      have : b = c := hk ▸ hmod.symm
      rw [this] at hb2
      exact absurd (by rw [sq]; exact hb2) hc2
    · rw [h] at hmod
      have : b = c ^ (2 : ℤ) := hk ▸ hmod.symm
      simpa using this
    · rw [h] at hmod
      have h3 : b = c ^ (3 : ℤ) := hk ▸ hmod.symm
      rw [h3] at hb2
      exfalso
      apply hc2
      have : c ^ 6 = 1 := by
        calc c ^ 6 = (c ^ (3 : ℤ) * c ^ (3 : ℤ)) := by
              rw [← zpow_add]; norm_num
          _ = 1 := hb2
      calc c ^ 2 = c ^ 6 * (c ^ 4)⁻¹ := by group
        _ = 1 := by rw [this, hc4]; simp
  set c' : MulAut (IntMod (V154 T Mc M) hV) := c with hc'
  have hc4' : c' ^ 4 = 1 := hc4
  have hc2' : c' ^ 2 ≠ 1 := hc2
  have hautI : autI hV (preOn T (V154 T Mc M) B₀) = Subgroup.zpowers (c' ^ 2) :=
    (autOn_preOn hD.isB0.1).trans (hB₀b.trans (congrArg Subgroup.zpowers hb))
  have hW : Nat.card (fixV (Subgroup.zpowers (c' ^ 2))) = 4 := by
    rw [← hautI]
    exact card_fixV_autI_P hD
  refine not_centralizes_fixV_sq (fun w => IntMod.sq_eq_one w) hD.card_V hc4' hc2' hW ?_
  intro w hw
  have hP : preOn T (V154 T Mc M) B₀ ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (P_le_T T Mc M B₀).trans (hD.T_le_M.trans hD.M_le_normalizer)
  rw [← hautI] at hw
  have hw' := (mem_fixV_autI hV hP w).mp hw
  have hwS : (w.val : G) ∈ zSOf T Mc M B₀ := by
    rw [hD.zS_eq]
    exact ⟨w.val_mem, hw'⟩
  exact Tbar_fixes_zS hST c hcT w hwS

theorem Tbar_fixes_commV (hD : Data14 T Mc M B₀) (hV' : IsElemAbelian 2 (V154 T Mc M))
    (hST : sOf152 T Mc M B₀ = T) :
    ∀ t ∈ autOn T (V154 T Mc M), ∀ z ∈ @commV ↥(V154 T Mc M) (commGroupOfElemAbelian hV') B₀,
      t z = z := by
  intro t ht z hz
  refine Tbar_fixes_zS hST t ht z ?_
  exact coe_mem_commutator_of_mem_commV hV' hD.isB0.1 hz

theorem barT14 (hD : Data14 T Mc M B₀) (hOm : Om4Z152) :
    sOf152 T Mc M B₀ = T → Nat.card (autOn T (V154 T Mc M)) = 2 := by
  intro hST
  rcases hD.shape with ⟨-, hsmall⟩ | ⟨hV', hΩ'⟩
  · rcases hsmall with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact card_Tbar_two hD.sylow_bar (Or.inl (card_six_of_equiv e))
    · exact card_Tbar_two hD.sylow_bar (Or.inr (card_ten_of_equiv e))
    · exact (false_of_sz hD hST e).elim
  · exfalso
    have := (@hOm ↥(V154 T Mc M) (commGroupOfElemAbelian hV') inferInstance
      (autOn M (V154 T Mc M)) (autOn T (V154 T Mc M)) B₀ hΩ' hD.sylow_bar hD.isB0.1
      hD.isB0.2.1 hD.isB0.2.2).1
    exact this (Tbar_fixes_commV hD hV' hST)

end S152N2

end CFSG.Quasithin
