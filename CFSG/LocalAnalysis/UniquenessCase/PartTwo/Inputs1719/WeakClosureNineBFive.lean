module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

section X

variable {X : Type} [Group X]

structure FiveUse (L1b L2b Tb A H R : Subgroup X) : Prop where
  le : A ≤ H
  R_le : R ≤ H
  R_norm : H ≤ normalizer (R : Set X)
  R_le_T : R ≤ Tb
  idx : R.relIndex A = 2
  core : coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ H
  cY : ∀ Y : Subgroup X, Y ≤ H → H ≤ normalizer (Y : Set X) →
    (∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ R) → Y ≤ R
  cP : ∀ P : Subgroup X, P ≤ H → H ≤ normalizer (P : Set X) → IsPGroup 2 P → P ≤ R
  cD : ∀ D : Subgroup X, D ≤ H → H ≤ normalizer (D : Set X) → A ≤ D →
    ∃ y ∈ D, IsGood915 L1b L2b y
  pair : ∃ n ∈ H, IsPGroup 2 ↥(A ⊔ A.map (MulAut.conj n).toMonoidHom) ∧
    ∃ a ∈ A, ∃ b ∈ A, a * (n * b * n⁻¹) ≠ n * b * n⁻¹ * a

namespace NGW

theorem orderOf_ne_three_of_isPGroup {P : Subgroup X} (hP : IsPGroup 2 P) {y : X} (hy : y ∈ P) :
    orderOf y ≠ 3 := by
  intro h3
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hdvd : orderOf (⟨y, hy⟩ : P) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  rw [Subgroup.orderOf_mk, h3] at hdvd
  have := Nat.prime_three.dvd_of_dvd_pow hdvd
  norm_num at this

theorem not_le_of_relIndex_eq_two {R A : Subgroup X} (h : R.relIndex A = 2) : ¬ A ≤ R := by
  intro hle
  rw [Subgroup.relIndex_eq_one.2 hle] at h
  exact absurd h (by norm_num)

end NGW

namespace FiveWit

variable {L1b L2b Tb A H R Lh : Subgroup X} (w : FiveWit L1b L2b Tb A H R Lh)
include w

theorem minimal {K : Subgroup X} (hKH : K ≤ H) (hK : H ≤ normalizer (K : Set X))
    (hKR : ¬ K ≤ R) : Lh ≤ K := by
  obtain ⟨k, hkK, hkR⟩ := Set.not_subset.1 hKR
  have hkH : k ∈ H := hKH hkK
  have hkC : k ∉ centralizer (Lh : Set X) := fun hkC => hkR (w.cent ⟨hkH, hkC⟩)
  rw [Subgroup.mem_centralizer_iff] at hkC
  push Not at hkC
  obtain ⟨l, hlL, hlk⟩ := hkC
  have hlH : l ∈ H := w.Lh_le hlL
  have hcL : k * l * k⁻¹ * l⁻¹ ∈ Lh :=
    Lh.mul_mem ((Subgroup.mem_normalizer_iff.1 (w.Lh_norm hkH) l).1 hlL) (Lh.inv_mem hlL)
  have hcK : k * l * k⁻¹ * l⁻¹ ∈ K := by
    have h1 : l * k⁻¹ * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hK hlH) k⁻¹).1 (K.inv_mem hkK)
    have := K.mul_mem hkK h1
    simpa [mul_assoc] using this
  have hc1 : k * l * k⁻¹ * l⁻¹ ≠ 1 := by
    intro h1
    apply hlk
    calc l * k = (k * l * k⁻¹ * l⁻¹)⁻¹ * (k * l) := by group
      _ = k * l := by rw [h1, inv_one, one_mul]
  have : IsSimpleGroup ↥Lh := w.simple
  have hn : ((K ⊓ Lh).subgroupOf Lh).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgH : (g : X) ∈ H := w.Lh_le g.2
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 (hK hgH) x).1 hx.1
    · simpa using (Subgroup.mem_normalizer_iff.1 (w.Lh_norm hgH) x).1 hx.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ Lh).subgroupOf Lh) with h | h
  · exfalso
    have hmem : (⟨_, hcL⟩ : ↥Lh) ∈ (K ⊓ Lh).subgroupOf Lh := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hcK, hcL⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hc1 (congrArg Subtype.val hmem)
  · intro l' hl'
    have hmem : (⟨l', hl'⟩ : ↥Lh) ∈ (K ⊓ Lh).subgroupOf Lh := by rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hmem.1

theorem not_le : ¬ A ≤ R := NGW.not_le_of_relIndex_eq_two w.idx

theorem toFiveUse [Finite X] : FiveUse L1b L2b Tb A H R where
  le := w.le
  R_le := w.R_le
  R_norm := w.R_norm
  R_le_T := w.R_le_T
  idx := w.idx
  core := w.core
  cY := by
    intro Y hYH hY hYA
    by_contra hYR
    have hLY : Lh ≤ Y := w.minimal hYH hY hYR
    apply w.not_le
    intro a ha
    have haH : a ∈ H := w.le ha
    refine w.cent ⟨haH, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hR : l * a * l⁻¹ * a⁻¹ ∈ R := hYA l (hLY hl) a ha
    have hL : l * a * l⁻¹ * a⁻¹ ∈ Lh := by
      have h1 : a * l⁻¹ * a⁻¹ ∈ Lh :=
        (Subgroup.mem_normalizer_iff.1 (w.Lh_norm haH) l⁻¹).1 (Lh.inv_mem hl)
      have := Lh.mul_mem hl h1
      simpa [mul_assoc] using this
    have h1 : l * a * l⁻¹ * a⁻¹ ∈ Lh ⊓ R := ⟨hL, hR⟩
    rw [w.inter, Subgroup.mem_bot] at h1
    calc l * a = (l * a * l⁻¹ * a⁻¹) * (a * l) := by group
      _ = a * l := by rw [h1, one_mul]
  cP := by
    intro P hPH hP h2
    by_contra hPR
    obtain ⟨y, hyL, hy3, -⟩ := w.good
    exact NGW.orderOf_ne_three_of_isPGroup h2 (w.minimal hPH hP hPR hyL) hy3
  cD := by
    intro D hDH hD hAD
    obtain ⟨y, hyL, hy⟩ := w.good
    exact ⟨y, w.minimal hDH hD (fun hDR => w.not_le (hAD.trans hDR)) hyL, hy⟩
  pair := w.pair

end FiveWit

namespace NineFifteenBarFacts

variable [Finite X] {L1b L2b Tb : Subgroup X} (F : NineFifteenBarFacts X L1b L2b Tb)
include F

theorem fiveUse_top {A : Subgroup X} (hA2 : Nat.card A = 2) :
    FiveUse L1b L2b Tb A ⊤ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' 2 (dvd_of_eq hA2.symm)
  have ha2 : orderOf (a₀ : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ha₀
  have haA : (a₀ : X) ∈ A := a₀.2
  generalize (a₀ : X) = a at ha2 haA
  have hAa : A = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact haA
    · rw [Nat.card_zpowers, ha2, hA2]
  have hnorm : ∀ K : Subgroup X, ⊤ ≤ normalizer (K : Set X) → K.Normal := fun K hK =>
    Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hK)
  refine ⟨le_top, bot_le, ?_, bot_le, ?_, le_top, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup X).Normal)).ge
  · rw [Subgroup.relIndex_bot_left]
    exact hA2
  · intro Y _ hY hYA
    have : Y.Normal := hnorm Y hY
    have hC : (centralizer (Y : Set X)).Normal := Subgroup.normal_centralizer
    have haC : (a : X) ∈ centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hYA y hy a haA
      rw [Subgroup.mem_bot] at h1
      calc y * a = (y * a * y⁻¹ * a⁻¹) * (a * y) := by group
        _ = a * y := by rw [h1, one_mul]
    have hL := F.le_of_normal _ hC ⟨a, haC, ha2⟩
    have hYc : Y ≤ centralizer ((L1b ⊔ L2b : Subgroup X) : Set X) :=
      Subgroup.le_centralizer_iff.1 hL
    rw [F.cent] at hYc
    exact hYc
  · intro P _ hP h2
    by_contra hPb
    have hPne : P ≠ ⊥ := fun h => hPb (le_of_eq h)
    obtain ⟨x, hxP, hx2⟩ := exists_orderOf_eq_of_isPGroup h2 hPne
    have hL := F.le_of_normal P (hnorm P hP) ⟨x, hxP, hx2⟩
    obtain ⟨y, hy, hy3⟩ := F.three
    exact NGW.orderOf_ne_three_of_isPGroup h2 (hL (Subgroup.mem_sup_left hy)) hy3
  · intro D _ hD hAD
    have hL := F.le_of_normal D (hnorm D hD) ⟨a, hAD haA, ha2⟩
    obtain ⟨y, hy, hy3⟩ := F.three
    exact ⟨y, hL (Subgroup.mem_sup_left hy), hy3, Or.inl hy⟩
  · obtain ⟨n, hP, hnc⟩ := F.pair a ha2
    refine ⟨n, Subgroup.mem_top n, hP.to_le ?_, a, haA, a, haA, hnc⟩
    rw [hAa]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end NineFifteenBarFacts

end X

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.WeakClosure81.NGW

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

section Lift

variable {G : Type} [Group G] {N : Subgroup G} {X : Type} [Group X] {π : ↥N →* X}

theorem mem_liftSub_iff {K : Subgroup X} (x : ↥N) : (x : G) ∈ liftSub π K ↔ π x ∈ K := by
  rw [mem_liftSub]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem relIndex_liftSub_left {A : Subgroup G} (hAN : A ≤ N) (K : Subgroup X) :
    (liftSub π K).relIndex A = K.relIndex (barSub π A) := by
  unfold liftSub barSub
  rw [← Subgroup.map_subgroupOf_eq_of_le hAN,
    Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective,
    Subgroup.relIndex_comap, Subgroup.map_subgroupOf_eq_of_le hAN]

theorem barSub_sup {A B : Subgroup G} (hAN : A ≤ N) (hBN : B ≤ N) :
    barSub π (A ⊔ B) = barSub π A ⊔ barSub π B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hAN hBN, Subgroup.map_sup]

theorem barSub_conj_le {A : Subgroup G} (n : ↥N) :
    barSub π (conjSubgroup A (n : G)⁻¹) ≤
      (barSub π A).map (MulAut.conj (π n)).toMonoidHom := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ((n⁻¹ * z * n : ↥N) : G) ∈ A := by
    have := mem_conjSubgroup_iff.1 hz
    simpa [mul_assoc] using this
  refine ⟨π (n⁻¹ * z * n), mem_barSub_of_mem' hz', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

end Lift

variable {G : Type} [Group G] [Finite G]

namespace Ctx15

variable {V T N L₁ L₂ : Subgroup G} {X : Type} [Group X] [Finite X] {π : ↥N →* X}
variable (c : Ctx15 V T N L₁ L₂ π)
include c

theorem false_of_fiveUse {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUse (barSub π L₁) (barSub π L₂) (barSub π T) (barSub π (conjSubgroup V g)) Hb Rb) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := w.conj
  set A := conjSubgroup V g with hAdef
  set H := liftSub π Hb with hHdef
  set R := liftSub π Rb with hRdef
  have hAN : A ≤ N := hAT.trans c.TN
  have hHN : H ≤ N := liftSub_le Hb
  have hRH : R ≤ H := liftSub_mono hF.R_le
  have hAH : A ≤ H := (barSub_le_iff hAN).1 hF.le
  have hRT : R ≤ T := by
    have := liftSub_mono (π := π) hF.R_le_T
    rwa [c.liftSub_barSub_T] at this
  have hHb : barSub π H = Hb := barSub_liftSub c.surj Hb
  have hHR : H ≤ normalizer (R : Set G) := by
    intro x hx
    obtain ⟨hxN, hxH⟩ := mem_liftSub.1 hx
    exact mem_normalizer_liftSub hxN (hF.R_norm hxH)
  have hAel : IsElemAbelian 2 A := isElemAbelian_conjSubgroup' c.elem g
  have hUM : conjSubgroup V h ≤ normalizer (V : Set G) := w.le_T.trans c.T_le_M
  have hrel : R.relIndex A = 2 := by rw [relIndex_liftSub_left hAN]; exact hF.idx
  have hcardA0 : 4 ≤ Nat.card ↥(R ⊓ A) := by
    have h1 := Subgroup.relIndex_mul_card R A
    rw [hrel] at h1
    have h3 : 8 ≤ Nat.card A := c.card_conj g
    omega
  have hA0ne : R ⊓ A ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardA0
    omega
  obtain ⟨⟨a₀, ha₀RA⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA0ne
  have ha₀1' : a₀ ≠ 1 := fun h0 => ha₀1 (Subtype.ext h0)
  set W1R := E3.wClos V 1 R with hW1R
  have hA0W : R ⊓ A ≤ W1R := by
    refine E3.le_wClos_of_mQuot_le c.elem g inf_le_left inf_le_right ?_ c.one_lt_rk
    show padicValNat 2 ((R ⊓ A).relIndex A) ≤ 1
    rw [Subgroup.inf_relIndex_right, hrel, padicValNat_self]
  have hHW1R : H ≤ normalizer (W1R : Set G) := hHR.trans (E3.normalizer_le_normalizer_wClos R)
  set Y := H ⊓ centralizer (W1R : Set G) with hY
  have hHY : H ≤ normalizer (Y : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hHW1R hn))
  have hYA : Y ≤ normalizer (A : Set G) := by
    intro y hy
    refine centralizer_le_normalizer_conj c.ti g ha₀RA.2 ha₀1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 hy.2) a₀ (hA0W ha₀RA)).symm
  have hO2H : pCoreOf 2 H ≤ R := by
    have hle : pCoreOf 2 H ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHN
    refine (barSub_le_iff hle).1 (hF.cP _ ?_ ?_ (isPGroup_barSub
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)))
    · rw [← hHb]
      exact barSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    · rw [← hHb]
      exact barSub_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hYAR : Y ⊓ A ≤ R := by
    have h1 : Y ⊓ A ≤ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (E1.le_normalizer_inf_of_le_normalizer hYA) (hAel.isPGroup.to_le inf_le_right)
    have h2 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans inf_le_left)
        (hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    exact h1.trans (h2.trans hO2H)
  have hcommR : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ R := by
    intro y hy a ha
    apply hYAR
    refine ⟨?_, ?_⟩
    · have h1 : a * y⁻¹ * a⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hHY (hAH ha)) y⁻¹).1 (Y.inv_mem hy)
      have := Y.mul_mem hy h1
      simpa [mul_assoc] using this
    · have h1 : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hYA hy) a).1 ha
      exact A.mul_mem h1 (A.inv_mem ha)
  have hYN : Y ≤ N := inf_le_left.trans hHN
  have hYR : Y ≤ R := by
    refine (barSub_le_iff hYN).1 (hF.cY _ ?_ ?_ ?_)
    · rw [← hHb]
      exact barSub_mono inf_le_left
    · rw [← hHb]
      exact barSub_le_normalizer hHY
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨a, ha, rfl⟩
      have h1 := hcommR y hy a ha
      have e : (y : G) * a * (y : G)⁻¹ * (a : G)⁻¹ = ((y * a * y⁻¹ * a⁻¹ : ↥N) : G) := rfl
      rw [e, mem_liftSub_iff] at h1
      simpa only [map_mul, map_inv] using h1
  have hC1TH : E3.cClos V 1 T ≤ H := c.cClos_le_liftSub hAT hF.core
  have huC1T : u ∈ E3.cClos V 1 T := ⟨w.le_T w.mem, w.cent_W1⟩
  have huH : u ∈ H := hC1TH huC1T
  have huY : u ∈ Y := by
    refine ⟨huH, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono hRT hz)
  set C1R := E3.cClos V 1 R with hC1R
  have huC1 : u ∈ C1R := ⟨hYR huY, huY.2⟩
  have hHC1R : H ≤ normalizer (C1R : Set G) :=
    hHR.trans (E3.normalizer_le_normalizer_cClos R)
  have hAC : ¬ A ≤ centralizer (C1R : Set G) := by
    intro hle
    set D := H ⊓ centralizer (C1R : Set G) with hD
    have hHD : H ≤ normalizer (D : Set G) := fun n hn =>
      mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hHC1R hn))
    obtain ⟨y, hy, hgood⟩ := hF.cD (barSub π D)
      (by rw [← hHb]; exact barSub_mono inf_le_left)
      (by rw [← hHb]; exact barSub_le_normalizer hHD)
      (barSub_mono (le_inf hAH hle))
    exact c.false_of_good_commute hy hgood hUM w.ne w.mem w.ne_one fun x hx =>
      ((Subgroup.mem_centralizer_iff.1 hx.2) u huC1).symm
  have hex : ∃ a ∈ A, ∃ cc ∈ C1R, cc * a ≠ a * cc := by
    by_contra hcon
    apply hAC
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro cc hcc
    by_contra hne
    exact hcon ⟨a, ha, cc, hcc, hne⟩
  obtain ⟨a, haA, cc, hcc, hne⟩ := hex
  have hccA : cc ∈ normalizer (A : Set G) := by
    refine centralizer_le_normalizer_conj c.ti g ha₀RA.2 ha₀1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 hcc.2) a₀ (hA0W ha₀RA)).symm
  set x := cc * a * cc⁻¹ * a⁻¹ with hx
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hne
    calc cc * a = (cc * a * cc⁻¹ * a⁻¹) * (a * cc) := by group
      _ = a * cc := by rw [← hx, hx1, one_mul]
  have hxA : x ∈ A := A.mul_mem ((Subgroup.mem_normalizer_iff.1 hccA a).1 haA) (A.inv_mem haA)
  have hxC : x ∈ C1R := by
    have h1 : a * cc⁻¹ * a⁻¹ ∈ C1R :=
      (Subgroup.mem_normalizer_iff.1 (hHC1R (hAH haA)) cc⁻¹).1 (C1R.inv_mem hcc)
    have := C1R.mul_mem hcc h1
    simpa [hx, mul_assoc] using this
  have hxW : x ∈ W1R := hA0W ⟨hxC.1, hxA⟩
  have hxZ : x ∈ centralizer (W1R : Set G) := hxC.2
  obtain ⟨nb, hnbH, hP, a₁b, ha₁b, b₁b, hb₁b, hnc⟩ := hF.pair
  obtain ⟨n, rfl⟩ := c.surj nb
  have hnH : (n : G) ∈ H := (mem_liftSub_iff n).2 hnbH
  set A' := conjSubgroup A (n : G)⁻¹ with hA'
  have hA'conj : A' = conjSubgroup V (g * (n : G)⁻¹) := conjSubgroup_conjSubgroup V g _
  have hx'A' : (n : G) * x * (n : G)⁻¹ ∈ A' := by
    rw [hA', mem_conjSubgroup_iff]
    simpa [mul_assoc] using hxA
  have hx'1 : (n : G) * x * (n : G)⁻¹ ≠ 1 := by
    intro h0
    apply hx1
    have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h0
    simpa [mul_assoc] using this
  have hx'W : (n : G) * x * (n : G)⁻¹ ∈ W1R :=
    (Subgroup.mem_normalizer_iff.1 (hHW1R hnH) x).1 hxW
  have hxx' : x * ((n : G) * x * (n : G)⁻¹) = ((n : G) * x * (n : G)⁻¹) * x :=
    ((Subgroup.mem_centralizer_iff.1 hxZ) _ hx'W).symm
  have hxNA' : x ∈ normalizer (A' : Set G) := by
    rw [hA'conj]
    exact centralizer_le_normalizer_conj c.ti (g * (n : G)⁻¹) (hA'conj ▸ hx'A') hx'1
      (Subgroup.mem_centralizer_singleton_iff.2 hxx')
  have hNA' : A ⊓ normalizer (A' : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ A ⊓ normalizer (A' : Set G) := ⟨hxA, hxNA'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hA'N : A' ≤ N := by
    intro z hz
    have h1 : (n : G)⁻¹ * z * (n : G) ∈ N := by
      have := hAN (mem_conjSubgroup_iff.1 hz)
      simpa using this
    have := N.mul_mem (N.mul_mem n.2 h1) (N.inv_mem n.2)
    simpa [mul_assoc] using this
  have hP2 : IsPGroup 2 ↥(A ⊔ A') := by
    refine isPGroup_of_barSub c.ker (sup_le hAN hA'N) (hP.to_le ?_)
    rw [barSub_sup hAN hA'N]
    exact sup_le_sup le_rfl (barSub_conj_le n)
  have hcomm := commute_of_isPGroup_sup c.elem c.ti ⟨g, hAdef⟩ ⟨g * (n : G)⁻¹, hA'conj⟩ hNA' hP2
  obtain ⟨a₁, ha₁, rfl⟩ := ha₁b
  obtain ⟨b₁, hb₁, rfl⟩ := hb₁b
  have hb₁' : (b₁ : G) ∈ A := hb₁
  have hb' : ((n * b₁ * n⁻¹ : ↥N) : G) ∈ A' := by
    rw [hA', mem_conjSubgroup_iff]
    simpa [mul_assoc] using hb₁'
  have h1 := hcomm (a₁ : G) ha₁ _ hb'
  apply hnc
  have h1' : a₁ * (n * b₁ * n⁻¹) = (n * b₁ * n⁻¹) * a₁ := Subtype.ext h1
  have := congrArg π h1'
  simpa only [map_mul, map_inv] using this

theorem four_le_card_barSub {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) (hAQ : ¬ conjSubgroup V g ≤ pCoreOf 2 N) :
    4 ≤ Nat.card (barSub π (conjSubgroup V g)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Nat.card (barSub π (conjSubgroup V g)) ≠ 2 := fun h2 =>
    c.false_of_fiveUse w hAT (c.facts.fiveUse_top h2)
  have h1 : Nat.card (barSub π (conjSubgroup V g)) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one, barSub_eq_bot_iff c.ker (hAT.trans c.TN)]
    exact hAQ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
    (isPGroup_barSub (π := π) (isElemAbelian_conjSubgroup' c.elem g).isPGroup)
  rw [hk] at h1 h2 ⊢
  rcases k with _ | _ | k
  · simp at h1
  · simp at h2
  · calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Ctx15

end CFSG.LocalAnalysis.WeakClosure81.NGW
