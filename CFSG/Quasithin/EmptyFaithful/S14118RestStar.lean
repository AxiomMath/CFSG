module

public import CFSG.Quasithin.EmptyFaithful.S14118RestBasic
public import CFSG.Quasithin.EmptyFaithful.S14118RestAbs
public import CFSG.Quasithin.EmptyFaithful.S14117Rank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem zpow_eq_one_or_self_of_mul_self_eq_one {Q : Type*} [Group Q] {s : Q} (hs2 : s * s = 1)
    (k : ℤ) : s ^ k = 1 ∨ s ^ k = s := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, show s ^ (2 : ℤ) = 1 by rw [zpow_two, hs2], one_zpow]
  · right
    rw [zpow_add, zpow_mul, show s ^ (2 : ℤ) = 1 by rw [zpow_two, hs2], one_zpow, one_mul,
      zpow_one]

theorem nonempty_mulEquiv_zmod_three {P : Type*} [Group P] (h : Nat.card P = 3) :
    Nonempty (P ≃* Multiplicative (ZMod 3)) := by
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic P := isCyclic_of_prime_card h
  exact ⟨mulEquivOfCyclicCardEq (by rw [h]; simp)⟩

variable {G : Type} [Group G] [Finite G]

section StarAct

omit [Finite G] in
@[expose] noncomputable def starAct (M V : Subgroup G) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hOC : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G)) : OTwoQuot M →* MulAut ↥V :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥M) (A4.actionOn V M hMV) (by
    intro x hx
    rw [MonoidHom.mem_ker, A4.actionOn_eq_one_iff hMV]
    apply hOC
    unfold pCoreOf
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

variable {M V X : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
  (hOC : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G))

omit [Finite G] in
theorem starAct_mk (m : M) :
    starAct M V hMV hOC (QuotientGroup.mk m) = A4.actionOn V M hMV m := rfl

omit [Finite G] in
theorem ker_starAct :
    (starAct M V hMV hOC).ker = imageOTwoQuot M (M ⊓ Subgroup.centralizer (V : Set G)) := by
  ext x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, mem_imageOTwoQuot_iff]
  constructor
  · intro h
    refine ⟨m, m.2, ⟨m.2, (A4.actionOn_eq_one_iff hMV m).mp ?_⟩, rfl⟩
    rw [← starAct_mk hMV hOC]
    exact h
  · rintro ⟨y, hy, ⟨-, hyc⟩, hym⟩
    rw [← hym, starAct_mk]
    exact (A4.actionOn_eq_one_iff hMV ⟨y, hy⟩).mpr hyc

omit [Finite G] in
theorem map_starAct (hX : X ≤ M) :
    (imageOTwoQuot M X).map (starAct M V hMV hOC) = autOn X V := by
  ext a
  rw [Subgroup.mem_map, mem_autOn_iff_exists]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact ⟨x, hMV hx, hxX, rfl⟩
  · rintro ⟨x, hxV, hxX, rfl⟩
    exact ⟨QuotientGroup.mk ⟨x, hX hxX⟩, mem_imageOTwoQuot_iff.mpr ⟨x, hX hxX, hxX, rfl⟩, rfl⟩

omit [Finite G] in
theorem starAct_surjective (htop : autOn M V = ⊤) :
    Function.Surjective (starAct M V hMV hOC) := by
  intro a
  have ha : a ∈ autOn M V := by rw [htop]; trivial
  obtain ⟨x, hxV, hxM, rfl⟩ := mem_autOn_iff_exists.mp ha
  exact ⟨QuotientGroup.mk ⟨x, hxM⟩, rfl⟩

end StarAct

section Image

omit [Finite G] in
theorem subgroupOf_conjClosure {R M : Subgroup G} (hR : R ≤ M) :
    (conjClosure R M).subgroupOf M = conjClosure (R.subgroupOf M) ⊤ := by
  have hle : conjClosure R M ≤ M :=
    conjClosure_le fun h hh z hz => M.mul_mem (M.mul_mem hh (hR hz)) (M.inv_mem hh)
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle, map_conjClosure_eq,
    Subgroup.map_subgroupOf_eq_of_le hR, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite G] in
theorem imageOTwoQuot_conjClosure {R M : Subgroup G} (hR : R ≤ M) :
    imageOTwoQuot M (conjClosure R M) = conjClosure (imageOTwoQuot M R) ⊤ := by
  unfold imageOTwoQuot
  rw [subgroupOf_conjClosure hR, map_conjClosure_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem subgroupOf_oTwoUpper {X M : Subgroup G} (hX : X ≤ M) :
    (oTwoUpper X).subgroupOf M = oTwoUpper (X.subgroupOf M) := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le X).trans hX), ← oTwoUpper_map,
    Subgroup.map_subgroupOf_eq_of_le hX]

theorem imageOTwoQuot_oTwoUpper {X M : Subgroup G} (hX : X ≤ M) :
    imageOTwoQuot M (oTwoUpper X) = oTwoUpper (imageOTwoQuot M X) := by
  unfold imageOTwoQuot
  rw [subgroupOf_oTwoUpper hX, oTwoUpper_map]

omit [Finite G] in
theorem oTwoUpper_conjClosure_le {R M : Subgroup G} (hR : R ≤ M) :
    oTwoUpper (conjClosure R M) ≤ M :=
  (oTwoUpper_le _).trans
    (conjClosure_le fun _ hh _ hz => M.mul_mem (M.mul_mem hh (hR hz)) (M.inv_mem hh))

omit [Finite G] in
theorem le_normalizer_oTwoUpper_conjClosure (R M : Subgroup G) :
    M ≤ Subgroup.normalizer (oTwoUpper (conjClosure R M) : Set G) :=
  (le_normalizer_conjClosure R M).trans (normalizer_le_normalizer_oTwoUpper _)

end Image

theorem pCoreOf_eq_inf_centralizer_of_le {Y M V : Subgroup G} (hYM : Y ≤ M)
    (hMY : M ≤ Subgroup.normalizer (Y : Set G))
    (hOC : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G))
    (hCY : ∀ y ∈ Y, y ∈ Subgroup.centralizer (V : Set G) → y ∈ pCoreOf 2 M) :
    pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G) := by
  refine le_antisymm ?_ ?_
  · have hKM : pCoreOf 2 Y ≤ pCoreOf 2 M := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYM) ?_ (pCoreOf_isPGroup 2 Y)
      exact fun m hm => normalizer_le_normalizer_pCoreOf 2 Y (hMY hm)
    exact _root_.le_inf (pCoreOf_le 2 Y) (hKM.trans hOC)
  · have hRp : IsPGroup 2 (Y ⊓ pCoreOf 2 M : Subgroup G) :=
      (pCoreOf_isPGroup 2 M).to_le inf_le_right
    have hYN : Y ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hMY (hYM hy), le_normalizer_pCoreOf 2 M (hYM hy)⟩
    have hle : Y ⊓ pCoreOf 2 M ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hYN hRp
    exact fun y hy => hle ⟨hy.1, hCY y hy.1 hy.2⟩

section Product

variable {Q A : Type} [Group Q] [Finite Q] [Group A] [Finite A]

theorem s3_product (hQ : CFSG.pCore 2 Q = ⊥) (ρ : Q →* A) (hρ : Function.Surjective ρ)
    {P T' : Subgroup A} (hA6 : Nat.card A = 6) (hPn : P.Normal) (hP3 : Nat.card P = 3)
    (hT2 : Nat.card T' = 2) (hPT : P ⊔ T' = ⊤) (hcomm : ¬ T' ≤ Subgroup.centralizer (P : Set A))
    {S : Subgroup Q} (hSinj : ∀ x ∈ S, ρ x = 1 → x = 1) (hSimg : S.map ρ = T')
    (hker : ∀ w ∈ conjClosure S ⊤, ∀ c ∈ ρ.ker, c * w = w * c) :
    oTwoUpper (conjClosure S ⊤) ⊔ S ≤ Subgroup.centralizer (ρ.ker : Set Q) ∧
      Disjoint (oTwoUpper (conjClosure S ⊤) ⊔ S) ρ.ker ∧
      (oTwoUpper (conjClosure S ⊤) ⊔ S) ⊔ ρ.ker = ⊤ ∧
      Nonempty (↥(oTwoUpper (conjClosure S ⊤) ⊔ S) ≃* A) := by
  obtain ⟨hρY, hinjY, -, _, -, -, -, -, -⟩ :=
    s3_extension hQ ρ hρ hA6 hPn hP3 hT2 hPT hcomm hSinj hSimg hker
  set Wh : Subgroup Q := conjClosure S ⊤ with hWh
  set Yh : Subgroup Q := oTwoUpper Wh with hYh
  have hSW : S ≤ Wh := le_conjClosure S ⊤
  have hYW : Yh ≤ Wh := oTwoUpper_le Wh
  have hSN : S ≤ Subgroup.normalizer (Yh : Set Q) := hSW.trans (le_normalizer_oTwoUpper Wh)
  have hmemYS : ∀ x ∈ Yh ⊔ S, ∃ y ∈ Yh, ∃ t ∈ S, x = y * t := by
    intro x hx
    have hx' : x ∈ ((Yh ⊔ S : Subgroup Q) : Set Q) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Yh S hSN] at hx'
    obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨y, hy, t, ht, rfl⟩
  have hPT' : P ⊓ T' = ⊥ := by
    have h1 : Nat.card (P ⊓ T' : Subgroup A) ∣ 3 := hP3 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (P ⊓ T' : Subgroup A) ∣ 2 := hT2 ▸ Subgroup.card_dvd_of_le inf_le_right
    have h : Nat.card (P ⊓ T' : Subgroup A) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    have h' : Nat.card (P ⊓ T' : Subgroup A) = 1 := by simpa using h
    exact Subgroup.card_eq_one.mp h'
  have hinj : ∀ x ∈ Yh ⊔ S, ρ x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨y, hy, t, ht, rfl⟩ := hmemYS x hx
    have hρy : ρ y ∈ P := hρY ▸ Subgroup.mem_map_of_mem ρ hy
    have hρt : ρ t ∈ T' := hSimg ▸ Subgroup.mem_map_of_mem ρ ht
    have hmul : ρ y * ρ t = 1 := by rw [← map_mul]; exact hρx
    have hρt' : ρ t = (ρ y)⁻¹ := eq_inv_of_mul_eq_one_right hmul
    have hmem : ρ t ∈ P ⊓ T' := ⟨by rw [hρt']; exact P.inv_mem hρy, hρt⟩
    rw [hPT', Subgroup.mem_bot] at hmem
    have ht1 : t = 1 := hSinj t ht hmem
    have hρy1 : ρ y = 1 := by
      rw [ht1, map_one, mul_one] at hmul
      exact hmul
    rw [hinjY y hy hρy1, ht1, one_mul]
  have hdisj : Disjoint (Yh ⊔ S) ρ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact hinj x hx (MonoidHom.mem_ker.mp hxk)
  have hρYS : (Yh ⊔ S).map ρ = ⊤ := by rw [Subgroup.map_sup, hρY, hSimg, hPT]
  have hsup : (Yh ⊔ S) ⊔ ρ.ker = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : ρ g ∈ (Yh ⊔ S).map ρ := by rw [hρYS]; trivial
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
    have hk : x⁻¹ * g ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
    have e : g = x * (x⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hk)
  have hcent : Yh ⊔ S ≤ Subgroup.centralizer (ρ.ker : Set Q) := by
    refine sup_le (fun y hy => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hker y (hYW hy) c hc
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hker t (hSW ht) c hc
  have hinjH : Function.Injective (ρ.comp (Yh ⊔ S).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hsurjH : Function.Surjective (ρ.comp (Yh ⊔ S).subtype) := by
    intro a
    have ha : a ∈ (Yh ⊔ S).map ρ := by rw [hρYS]; trivial
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨hcent, hdisj, hsup, ⟨MulEquiv.ofBijective _ ⟨hinjH, hsurjH⟩⟩⟩

end Product

namespace Hyp14118

variable {T Mc M : Subgroup G}

theorem commutator_conjClosure_le (hyp : Hyp14118 T Mc M) :
    ⁅M ⊓ Subgroup.centralizer (VZ T M : Set G), conjClosure (pCoreOf 2 (M ⊓ Mc)) M⁆ ≤
      pCoreOf 2 M := by
  have := hyp.hyp1417.commutator_conjClosure_le hyp.qtfe (Y₀ := M) le_rfl
  rwa [sup_eq_left.mpr hyp.inM.2, inf_comm Mc M] at this

theorem cov_of_autOn_sup (hyp : Hyp14118 T Mc M) {Y₁ : Subgroup G} (hY₁M : Y₁ ≤ M)
    {P : Subgroup (MulAut ↥(VZ T M))} (hPn : P.Normal) (hYP : autOn Y₁ (VZ T M) = P)
    (hPT : P ⊔ autOn T (VZ T M) = ⊤) :
    ∀ m ∈ M, ∃ x ∈ Y₁ ⊔ T, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G), m = x * c := by
  intro m hm
  have hMV := hyp.le_normalizer
  have hTM : T ≤ M := hyp.inM.2
  have ha : conjAct (VZ T M) ⟨m, hMV hm⟩ ∈ P ⊔ autOn T (VZ T M) := by
    rw [hPT]
    trivial
  obtain ⟨p, hp, tb, htb, hptb⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  have hp' : p ∈ autOn Y₁ (VZ T M) := by
    rw [hYP]
    exact hp
  obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp hp'
  obtain ⟨t, htV, htT, rfl⟩ := mem_autOn_iff_exists.mp htb
  have hyM : y ∈ M := hY₁M hyY
  have htM : t ∈ M := hTM htT
  have hcM : (y * t)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (M.mul_mem hyM htM)) hm
  have hcV : (y * t)⁻¹ * m ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hcM
  have hcC : (y * t)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) := by
    refine (A4.conjAct_eq_one_iff (g := ⟨(y * t)⁻¹ * m, hcV⟩)).mp ?_
    have e : conjAct (VZ T M) ⟨(y * t)⁻¹ * m, hcV⟩ =
        (conjAct (VZ T M) ⟨y, hyV⟩ * conjAct (VZ T M) ⟨t, htV⟩)⁻¹ *
          conjAct (VZ T M) ⟨m, hMV hm⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e, hptb]
    exact inv_mul_cancel _
  exact ⟨y * t, (Y₁ ⊔ T).mul_mem (Subgroup.mem_sup_left hyY) (Subgroup.mem_sup_right htT),
    (y * t)⁻¹ * m, ⟨hcM, hcC⟩, by group⟩

theorem s3_data (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) {Rc Y : Subgroup G}
    (hRc : Rc = pCoreOf 2 (M ⊓ Mc)) (hY : Y = oTwoUpper (conjClosure Rc M)) :
    ∃ P : Subgroup (MulAut ↥(VZ T M)),
      P = oTwoUpper (autOn M (VZ T M)) ∧ P.Normal ∧ Nat.card P = 3 ∧
      P ⊔ autOn T (VZ T M) = ⊤ ∧ autOn Y (VZ T M) = P ∧
      (∀ y ∈ Y, y ∈ Subgroup.centralizer (VZ T M : Set G) → y ∈ pCoreOf 2 M) ∧
      (imageOTwoQuot M (Y ⊔ Rc) ≤ Subgroup.centralizer
          (imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) : Set (OTwoQuot M)) ∧
        Disjoint (imageOTwoQuot M (Y ⊔ Rc))
          (imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G))) ∧
        imageOTwoQuot M (Y ⊔ Rc) ⊔ imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) =
          ⊤ ∧
        Nonempty (↥(imageOTwoQuot M (Y ⊔ Rc)) ≃* MulAut ↥(VZ T M))) ∧
      Nat.card (imageOTwoQuot M Y) = 3 ∧
      ∃ s ∈ imageOTwoQuot M Rc, s * s = 1 ∧ s ≠ 1 ∧
        ∀ y ∈ imageOTwoQuot M Y, s * y * s⁻¹ = y⁻¹ := by
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    hyp.hyp1417.pCoreOf_le_centralizer
  have hRcM : Rc ≤ M := by
    rw [hRc]
    exact (pCoreOf_le 2 _).trans inf_le_left
  have hconj : conjClosure Rc M ≤ M :=
    conjClosure_le fun h hh z hz => M.mul_mem (M.mul_mem hh (hRcM hz)) (M.inv_mem hh)
  have hYM : Y ≤ M := by
    rw [hY]
    exact (oTwoUpper_le _).trans hconj
  have hA6 : Nat.card (MulAut ↥(VZ T M)) = 6 :=
    card_mulAut_of_card_four hyp.twoReduced.2.2.1 hyp.rank_two
  have : Finite (MulAut ↥(VZ T M)) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨_, P, hPn, hP3, -, -, -, -, hPT, -⟩ := hyp.exists_Y₀
  have hker : (starAct M (VZ T M) hMV hOC).ker =
      imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := ker_starAct hMV hOC
  have hsurj : Function.Surjective (starAct M (VZ T M) hMV hOC) :=
    starAct_surjective hMV hOC hyp.autOn_eq_top
  have hinf : pCoreOf 2 (M ⊓ Mc) ⊓ Subgroup.centralizer (VZ T M : Set G) = pCoreOf 2 M := by
    have := hyp.hyp1417.inf_centralizer_eq hyp.qtfe
    rwa [inf_comm Mc M] at this
  have hSinj : ∀ x ∈ imageOTwoQuot M Rc, starAct M (VZ T M) hMV hOC x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨r, hrM, hrR, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    have hrC : r ∈ Subgroup.centralizer (VZ T M : Set G) := by
      refine (A4.actionOn_eq_one_iff hMV ⟨r, hrM⟩).mp ?_
      rw [← starAct_mk hMV hOC]
      exact hρx
    have hrO : r ∈ pCoreOf 2 M := by
      rw [← hinf]
      exact ⟨by rw [← hRc]; exact hrR, hrC⟩
    exact (mk_eq_one_iff_mem_pCoreOf ⟨r, hrM⟩).mpr hrO
  have hSimg : (imageOTwoQuot M Rc).map (starAct M (VZ T M) hMV hOC) = autOn T (VZ T M) := by
    rw [map_starAct hMV hOC hRcM, hRc]
    exact hyp.autOn_Rc_eq h113
  have hcomm : ⁅M ⊓ Subgroup.centralizer (VZ T M : Set G), conjClosure Rc M⁆ ≤ pCoreOf 2 M := by
    rw [hRc]
    exact hyp.commutator_conjClosure_le
  have hkerc : ∀ w ∈ conjClosure (imageOTwoQuot M Rc) ⊤,
      ∀ c ∈ (starAct M (VZ T M) hMV hOC).ker, c * w = w * c := by
    intro w hw c hc
    rw [hker] at hc
    rw [← imageOTwoQuot_conjClosure hRcM] at hw
    have hle : imageOTwoQuot M (conjClosure Rc M) ≤ Subgroup.centralizer
        (imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) : Set (OTwoQuot M)) := by
      refine imageOTwoQuot_le_centralizer fun x hx c hc => ?_
      have := Subgroup.commutator_mem_commutator hx hc
      rw [Subgroup.commutator_comm] at this
      exact hcomm this
    exact Subgroup.mem_centralizer_iff.mp (hle hw) c hc
  have hext := s3_extension (pCore_two_quot_eq_bot M) (starAct M (VZ T M) hMV hOC) hsurj hA6 hPn
    hP3 hyp.card_autOn_T hPT (hyp.not_le_centralizer_P hPT) hSinj hSimg hkerc
  have hprod := s3_product (pCore_two_quot_eq_bot M) (starAct M (VZ T M) hMV hOC) hsurj hA6 hPn
    hP3 hyp.card_autOn_T hPT (hyp.not_le_centralizer_P hPT) hSinj hSimg hkerc
  obtain ⟨hρY, hinjY, hY3, s, hsS, -, hs2, hs1, hinv⟩ := hext
  obtain ⟨hcent, hdisj, hsup, hiso⟩ := hprod
  have hYq : imageOTwoQuot M Y = oTwoUpper (conjClosure (imageOTwoQuot M Rc) ⊤) := by
    rw [hY, imageOTwoQuot_oTwoUpper hconj, imageOTwoQuot_conjClosure hRcM]
  refine ⟨P, ?_, hPn, hP3, hPT, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hyp.autOn_eq_top]
    have hidx : P.index = 2 := by
      have := P.card_mul_index
      rw [hP3, hA6] at this
      omega
    exact (oTwoUpper_top_eq hPn (by rw [hP3]; decide) hidx).symm
  · rw [← map_starAct hMV hOC hYM, hYq]
    exact hρY
  · intro y hyY hyC
    have hyM := hYM hyY
    have hu : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ imageOTwoQuot M Y :=
      mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hyY, rfl⟩
    rw [hYq] at hu
    have h1 : starAct M (VZ T M) hMV hOC (QuotientGroup.mk ⟨y, hyM⟩) = 1 := by
      rw [starAct_mk]
      exact (A4.actionOn_eq_one_iff hMV ⟨y, hyM⟩).mpr hyC
    exact (mk_eq_one_iff_mem_pCoreOf ⟨y, hyM⟩).mp (hinjY _ hu h1)
  · rw [imageOTwoQuot_sup hYM hRcM, hYq, ← hker]
    exact hcent
  · rw [imageOTwoQuot_sup hYM hRcM, hYq, ← hker]
    exact hdisj
  · rw [imageOTwoQuot_sup hYM hRcM, hYq, ← hker]
    exact hsup
  · rw [imageOTwoQuot_sup hYM hRcM, hYq]
    exact hiso
  · rw [hYq]
    exact hY3
  · exact ⟨s, hsS, hs2, hs1, fun y hy => hinv y (by rwa [hYq] at hy)⟩

end Hyp14118

variable {T Mc M : Subgroup G}

theorem lemma_14_1_18_three (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) {Rc Y : Subgroup G}
    (hRc : Rc = pCoreOf 2 (M ⊓ Mc)) (hY : Y = oTwoUpper (conjClosure Rc M)) :
    autOn Y (VZ T M) = oTwoUpper (autOn M (VZ T M)) ∧
      Nonempty (↥(autOn Y (VZ T M)) ≃* Multiplicative (ZMod 3)) ∧
      pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨_, hPO, -, hP3, -, hYP, hYC, -⟩ := hyp.s3_data h113 hRc hY
  have hRcM : Rc ≤ M := by
    rw [hRc]
    exact (pCoreOf_le 2 _).trans inf_le_left
  have hYM : Y ≤ M := by
    rw [hY]
    exact oTwoUpper_conjClosure_le hRcM
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hY]
    exact le_normalizer_oTwoUpper_conjClosure Rc M
  refine ⟨by rw [hYP]; exact hPO, ?_,
    pCoreOf_eq_inf_centralizer_of_le hYM hMY hyp.hyp1417.pCoreOf_le_centralizer hYC⟩
  rw [hYP]
  exact nonempty_mulEquiv_zmod_three hP3

theorem lemma_14_1_18_four (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) {Rc Y : Subgroup G}
    (hRc : Rc = pCoreOf 2 (M ⊓ Mc)) (hY : Y = oTwoUpper (conjClosure Rc M)) :
    IsUniqueM (Y ⊔ T) M := by
  obtain ⟨_, -, hPn, -, hPT, hYP, -⟩ := hyp.s3_data h113 hRc hY
  have hTM : T ≤ M := hyp.inM.2
  have hRcM : Rc ≤ M := by
    rw [hRc]
    exact (pCoreOf_le 2 _).trans inf_le_left
  have hYM : Y ≤ M := by
    rw [hY]
    exact oTwoUpper_conjClosure_le hRcM
  have hXM : Y ⊔ T ≤ M := sup_le hYM hTM
  have hO2 : pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
    intro hb
    have hle : VZ T M ≤ pCoreOf 2 (Y ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 (hyp.VZ_le.trans le_sup_right) (hXM.trans hyp.le_normalizer)
        (hyp.qtfe.sylow.1.to_le hyp.VZ_le)
    exact (VZ_ne_bot hyp.qtfe.omegaOneCenter_ne_bot : VZ T M ≠ ⊥) (le_bot_iff.mp (hb ▸ hle))
  exact isUniqueM_of_isOrdMaximalIn hyp.isMf.1 ⟨le_sup_right, hO2⟩ hXM
    (hyp.cov_of_autOn_sup hYM hPn hYP hPT)

theorem lemma_14_1_18_five (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) {Rc Y : Subgroup G}
    (hRc : Rc = pCoreOf 2 (M ⊓ Mc)) (hY : Y = oTwoUpper (conjClosure Rc M)) :
    imageOTwoQuot M (Y ⊔ Rc) ≤ Subgroup.centralizer
        (imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) : Set (OTwoQuot M)) ∧
      Disjoint (imageOTwoQuot M (Y ⊔ Rc))
        (imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G))) ∧
      imageOTwoQuot M (Y ⊔ Rc) ⊔ imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) =
        ⊤ ∧
      Nonempty (↥(imageOTwoQuot M (Y ⊔ Rc)) ≃* Equiv.Perm (Fin 3)) ∧
      CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤ 1 := by
  obtain ⟨_, -, -, -, -, -, -, ⟨hcent, hdisj, hsup, hiso⟩, hY3, s, hsR, hs2, hs1, hinv⟩ :=
    hyp.s3_data h113 hRc hY
  have hRcM : Rc ≤ M := by
    rw [hRc]
    exact (pCoreOf_le 2 _).trans inf_le_left
  have hYM : Y ≤ M := by
    rw [hY]
    exact oTwoUpper_conjClosure_le hRcM
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hY]
    exact le_normalizer_oTwoUpper_conjClosure Rc M
  have hYn : (imageOTwoQuot M Y).Normal := by
    have : (Y.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMY
    exact Subgroup.Normal.map this (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hY3p : IsPGroup 3 (imageOTwoQuot M Y) := IsPGroup.of_card (n := 1) (by rw [hY3]; rfl)
  have hYle : imageOTwoQuot M Y ≤ CFSG.Open.pCore 3 (OTwoQuot M) := le_pCore 3 hYn hY3p
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ imageOTwoQuot M Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (imageOTwoQuot M Y) = 1 :=
      Subgroup.card_eq_one.mpr (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
    omega
  have h3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(imageOTwoQuot M Y)) (x := ⟨y, hy⟩)
    rw [hY3] at this
    exact congrArg Subtype.val this
  have hs_not : s ∉ Subgroup.centralizer (CFSG.Open.pCore 3 (OTwoQuot M) : Set (OTwoQuot M)) := by
    intro hs
    have h1 : y * s = s * y := Subgroup.mem_centralizer_iff.mp hs y (hYle hy)
    have h2 : s * y * s⁻¹ = y := by
      rw [← h1]
      group
    have h4 := hinv y hy
    rw [h2] at h4
    have h5 : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [← h4]
        _ = 1 := mul_inv_cancel y
    apply hy1
    calc y = y * (y * y) := by rw [h5, mul_one]
      _ = y ^ 3 := (pow_three y).symm
      _ = 1 := h3
  have hfaith : Subgroup.zpowers s ⊓
      Subgroup.centralizer (CFSG.Open.pCore 3 (OTwoQuot M) : Set (OTwoQuot M)) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxz, hxc⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    rw [Subgroup.mem_bot]
    rcases zpow_eq_one_or_self_of_mul_self_eq_one hs2 k with h1 | h1
    · exact h1
    · rw [h1] at hxc
      exact absurd hxc hs_not
  refine ⟨hcent, hdisj, hsup, ?_, ?_⟩
  · obtain ⟨e⟩ := hiso
    obtain ⟨f⟩ := nonempty_mulAut_mulEquiv_perm_three hyp.twoReduced.2.2.1 hyp.rank_two
    exact ⟨e.trans f⟩
  · have hsR' : s ∈ imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)) := by
      rw [inf_comm Mc M, ← hRc]
      exact hsR
    exact (lemma_14_1_17_four hyp.qtfe hyp.hyp1417 Nat.prime_three (by norm_num) hsR' hs1 hfaith).2

end CFSG.Quasithin
