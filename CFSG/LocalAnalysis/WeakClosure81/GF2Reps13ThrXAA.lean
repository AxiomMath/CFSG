module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsSec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsXMod
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.A1cModuleSub
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

theorem w16g_le_s13IsoSum_self {X : Subgroup (MulAut W)} {U₀ : Subgroup W}
    (hU₀ : IsIrrOn X U₀ ⊥) : U₀ ≤ s13IsoSum X U₀ := by
  unfold s13IsoSum
  exact le_iSup₂ (f := fun V₁ (_ : IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥) => V₁) U₀
    ⟨hU₀, secIsoOn_refl hU₀.2.1 w16g_stableUnder_bot bot_le⟩

theorem w16g_s13IsoSum_stable (X : Subgroup (MulAut W)) (U₀ : Subgroup W) :
    StableUnder X (s13IsoSum X U₀) := by
  rw [s13IsoSum]
  refine stableUnder_iSup fun V₁ => stableUnder_iSup fun hV => hV.1.2.1

private theorem w16g_fix_of_secIsoOn_of_fixes {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) {y : MulAut W} (hy : y ∈ X)
    (hA : ∀ a ∈ A, y a = a) : ∀ b ∈ B, y b = b := by
  obtain ⟨-, -, -, -, -, -, β, -, -, hβsurj, hβeq⟩ := h
  intro b hb
  obtain ⟨a, ha⟩ := hβsurj b hb
  have hβa : β a = b := by
    rw [Subgroup.mem_bot, mul_inv_eq_one] at ha
    exact ha
  have h3 : β a * (y (β a))⁻¹ ∈ (⊥ : Subgroup W) :=
    hβeq y hy a a (hA (a : W) a.2).symm
  have h4 : y (β a) = β a := by
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3.symm
  rw [← hβa, h4]

private theorem w16g_le_fixV_of_secIsoOn {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) (hA : A ≤ fixV X) : B ≤ fixV X :=
  fun b hb x hx => w16g_fix_of_secIsoOn_of_fixes h hx (fun a ha => hA ha x hx) b hb

private theorem w16g_commSub_eq_self_of_irr (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} (hX : Odd (Nat.card X)) {V : Subgroup W}
    (hV : IsIrrOn X V ⊥) (hfix : V ⊓ fixV X = ⊥) : commSub V X = V := by
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hdec := (B1.coprime_decomp hW2 hX (M := V) hV.2.1).1
  rw [hfix, bot_sup_eq] at hdec
  exact hdec

theorem w16g_irr_le_commSub (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) {U₀ V : Subgroup W} (hIrr₀ : IsIrrOn X U₀ ⊥)
    (hne₀ : commSub U₀ X ≠ ⊥) (hIrrV : IsIrrOn X V ⊥) (hsec : SecIsoOn X V ⊥ U₀ ⊥) :
    V ≤ commSub ⊤ X := by
  have hstab : StableUnder X (fixV X) :=
    stableUnder_fixV (fun y hy h hh => X.mul_mem (X.mul_mem hy hh) (X.inv_mem hy))
  have hfixV : V ⊓ fixV X = ⊥ := by
    rcases hIrrV.2.2.2 (V ⊓ fixV X) (stableUnder_inf hIrrV.2.1 hstab) bot_le inf_le_left
      with h | h
    · exact h
    · exfalso
      have hle : V ≤ fixV X := by rw [← h]; exact inf_le_right
      exact hne₀ (commSub_eq_bot_iff.mpr (w16g_le_fixV_of_secIsoOn hsec hle))
  have hVcomm : commSub V X = V := w16g_commSub_eq_self_of_irr hW hX hIrrV hfixV
  calc V = commSub V X := hVcomm.symm
    _ ≤ commSub ⊤ X := commSub_mono le_top le_rfl

private theorem w16g_exists_irrOn_le_of_stable {X : Subgroup (MulAut W)} {C A : Subgroup W}
    (hCA : C < A) (hA : StableUnder X A) (hC : StableUnder X C) :
    ∃ J : Subgroup W, J ≤ A ∧ IsIrrOn X J C := by
  classical
  have hex : ∃ n, ∃ J : Subgroup W, J ≤ A ∧ C < J ∧ StableUnder X J ∧ Nat.card J = n :=
    ⟨_, A, le_rfl, hCA, hA, rfl⟩
  obtain ⟨J, hJA, hCJ, hJs, hJn⟩ := Nat.find_spec hex
  refine ⟨J, hJA, hCJ, hJs, hC, fun J' hJ's hCJ' hJ'J => ?_⟩
  by_cases h : J' = C
  · exact Or.inl h
  · right
    have hlt : C < J' := lt_of_le_of_ne hCJ' (Ne.symm h)
    have hmin := Nat.find_min' hex ⟨J', hJ'J.trans hJA, hlt, hJ's, rfl⟩
    rw [← hJn] at hmin
    exact Subgroup.eq_of_le_of_card_ge hJ'J hmin

private theorem w16g_exists_secIsoOn_of_le_s13IsoSum (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} {U₀ V : Subgroup W} (hV : IsIrrOn X V ⊥)
    (hle : V ≤ s13IsoSum X U₀) : SecIsoOn X V ⊥ U₀ ⊥ := by
  classical
  let P : Subgroup W → Prop := fun V₁ => IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥
  haveI : Finite (Subgroup W) := Finite.of_injective (fun S : Subgroup W => (S : Set W))
    SetLike.coe_injective
  have hsum : s13IsoSum X U₀ = ⨆ i : {V₁ : Subgroup W // P V₁}, (i.1 : Subgroup W) := by
    unfold s13IsoSum
    exact iSup_subtype' (p := P) (f := fun V₁ (_ : P V₁) => (V₁ : Subgroup W))
  have hle' : V ≤ ⊥ ⊔ ⨆ i : {V₁ : Subgroup W // P V₁}, (i.1 : Subgroup W) := by
    rw [bot_sup_eq, ← hsum]
    exact hle
  obtain ⟨i, hsec, -⟩ := exists_secIsoOn_of_le_iSup
    (hW := fun w => by rw [pow_two]; exact hW w) hV (fun i => i.2.1) hle'
  exact secIsoOn_trans hsec i.2.2

theorem w16g_inf_fixV_zpowers_eq_bot (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} (hXc : IsMulCommutative X) {U₀ : Subgroup W}
    (hIrr₀ : IsIrrOn X U₀ ⊥) {x : MulAut W} (hxX : x ∈ X)
    (hxnt : ∃ u ∈ U₀, x u ≠ u) :
    s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
  by_contra hne
  have hnorm : ∀ y ∈ X, ∀ h ∈ Subgroup.zpowers x, y * h * y⁻¹ ∈ Subgroup.zpowers x := by
    intro y hy h hh
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨n, rfl⟩ := hh
    refine ⟨n, ?_⟩
    symm
    have hyx : y * x * y⁻¹ = x := by
      have hc : y * x = x * y :=
        congrArg Subtype.val (hXc.is_comm.comm ⟨y, hy⟩ ⟨x, hxX⟩)
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [show y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n from (conj_zpow).symm, hyx]
  have hKstab : StableUnder X (s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers x)) :=
    stableUnder_inf (w16g_s13IsoSum_stable X U₀) (stableUnder_fixV hnorm)
  obtain ⟨J, hJK, hJirr⟩ := w16g_exists_irrOn_le_of_stable (X := X)
    (C := ⊥) (A := s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers x))
    (bot_lt_iff_ne_bot.mpr hne) hKstab w16g_stableUnder_bot
  have hsec : SecIsoOn X J ⊥ U₀ ⊥ :=
    w16g_exists_secIsoOn_of_le_s13IsoSum hW hJirr (hJK.trans inf_le_left)
  have hJfix : ∀ a ∈ J, x a = a := fun a ha => (hJK ha).2 x (Subgroup.mem_zpowers x)
  obtain ⟨u, hu, hxu⟩ := hxnt
  exact hxu (w16g_fix_of_secIsoOn_of_fixes hsec hxX hJfix u hu)

private theorem w16g_fixes_of_secIsoOn_of_fixes {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) {x : MulAut W} (hx : x ∈ X) (hB : ∀ b ∈ B, x b = b) :
    ∀ a ∈ A, x a = a := by
  obtain ⟨-, -, hSA, -, -, -, β, hβB, hβiff, -, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥A) : W) = 1 := (hβone _).mp h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  intro a ha
  have hxa : x a ∈ A := hSA x hx a ha
  have h3 : β ⟨x a, hxa⟩ * (x (β ⟨a, ha⟩))⁻¹ ∈ (⊥ : Subgroup W) :=
    hβeq x hx ⟨a, ha⟩ ⟨x a, hxa⟩ rfl
  have h4 : β ⟨x a, hxa⟩ = x (β ⟨a, ha⟩) := by
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  have h6 : β ⟨x a, hxa⟩ = β ⟨a, ha⟩ :=
    h4.trans (hB (β ⟨a, ha⟩) (hβB ⟨a, ha⟩))
  exact congrArg Subtype.val (hβinj h6)

theorem w16g_inf_centSub_s13IsoSum_eq {X : Subgroup (MulAut W)} {U₀ : Subgroup W}
    (hIrr : IsIrrOn X U₀ ⊥) :
    X ⊓ centSub (s13IsoSum X U₀) = X ⊓ centSub U₀ := by
  apply le_antisymm
  · rintro x ⟨hxX, hxcent⟩
    exact ⟨hxX, fun u hu => hxcent u (w16g_le_s13IsoSum_self hIrr hu)⟩
  · rintro x ⟨hxX, hxcent⟩
    refine ⟨hxX, ?_⟩
    change x ∈ centSub (s13IsoSum X U₀)
    rw [mem_centSub]
    intro w hw
    rw [s13IsoSum] at hw
    refine Subgroup.iSup_induction _ (C := fun w => x w = w) hw ?_ ?_ ?_
    · intro V₁ y hy
      refine Subgroup.iSup_induction _ (C := fun w => x w = w) hy ?_ ?_ ?_
      · intro hsec z hz
        exact w16g_fixes_of_secIsoOn_of_fixes hsec.2 hxX hxcent z hz
      · exact map_one x
      · intro a b ha hb; rw [map_mul, ha, hb]
    · exact map_one x
    · intro a b ha hb; rw [map_mul, ha, hb]

theorem w16g_index_kerOn_eq_prime (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {U₀ : Subgroup W}
    (hIrr : IsIrrOn X U₀ ⊥) (hne : commSub U₀ X ≠ ⊥) :
    (X ⊓ centSub U₀).relIndex X = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hne
    rw [hbot, commSub]
    simp
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
  haveI : Nontrivial ↥U₀ :=
    (Subgroup.nontrivial_iff_ne_bot U₀).mpr (bot_lt_iff_ne_bot.mp hIrr.1)
  haveI : IsElementaryAbelian p ↥X := IsElemAbelian.isElementaryAbelian hX
  have hInv : XMod.IsInv ↥X U₀ := ((isIrrOn_bot_iff_isIrr).mp hIrr).1
  letI : MulDistribMulAction ↥X ↥U₀ := XMod.subAction hInv
  have hirr : ∀ J : Subgroup ↥U₀, (∀ a : ↥X, ∀ x ∈ J, a • x ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJ'stab : StableUnder X (J.map (Subgroup.subtype U₀)) := by
      intro x hx j hj
      obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
      exact Subgroup.mem_map.mpr
        ⟨(⟨x, hx⟩ : ↥X) • j₀, hJ ⟨x, hx⟩ j₀ hj₀, rfl⟩
    rcases hIrr.2.2.2 (J.map (Subgroup.subtype U₀)) hJ'stab bot_le
      (Subgroup.map_subtype_le J) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective J (Subgroup.subtype_injective U₀)).mp h
    · right
      have htop : (⊤ : Subgroup ↥U₀).map (Subgroup.subtype U₀) = U₀ := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      exact (Subgroup.map_injective (Subgroup.subtype_injective U₀)) (h.trans htop.symm)
  obtain ⟨B, hBindex, hBtriv⟩ :=
    CFSG.SolvableHall.exists_hyperplane_acting_trivially_of_irreducible (p := p) hirr
  have hBle : B ≤ (X ⊓ centSub U₀).subgroupOf X := by
    intro b hb
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨b.2, ?_⟩
    rw [mem_centSub]
    intro u hu
    have h1 := congrArg Subtype.val (hBtriv b hb ⟨u, hu⟩)
    exact h1
  have hDsub_ne : (X ⊓ centSub U₀).subgroupOf X ≠ ⊤ := by
    intro htop
    apply hne
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro x hx
    have hxsub : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ centSub U₀).subgroupOf X := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf] at hxsub
    exact (mem_centSub.mp hxsub.2) u hu
  have hDvd : ((X ⊓ centSub U₀).subgroupOf X).index ∣ p := by
    rw [← hBindex]
    exact Subgroup.index_dvd_of_le hBle
  have hDne1 : ((X ⊓ centSub U₀).subgroupOf X).index ≠ 1 := fun h1 =>
    hDsub_ne ((Subgroup.index_eq_one).mp h1)
  have hDp : ((X ⊓ centSub U₀).subgroupOf X).index = p := by
    rcases hp.eq_one_or_self_of_dvd _ hDvd with h | h
    · exact absurd h hDne1
    · exact h
  exact hDp

end CFSG.LocalAnalysis.WeakClosure81
