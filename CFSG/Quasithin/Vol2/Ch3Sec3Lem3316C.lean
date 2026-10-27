module

public import CFSG.Quasithin.EmptyFaithful.SzN15Out
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SzN15Br1
public import CFSG.Quasithin.EmptyFaithful.SzN2Main
public import CFSG.Quasithin.Vol2.Ch3Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SzN15
open scoped IsMulCommutative

namespace L3316

section TwoZ

variable {V : Type} [CommGroup V] {I₀ I₁ Z : Subgroup V} {S X : Subgroup (MulAut V)}

theorem comm_mul_eq (s : MulAut V) (u v : V) :
    s (u * v) * (u * v)⁻¹ = (s u * u⁻¹) * (s v * v⁻¹) := by
  rw [map_mul, mul_inv_rev, mul_comm v⁻¹ u⁻¹, mul_mul_mul_comm]

theorem fixMod_two_mem (hSX : S ≤ X) (hZ₁ : Z ≤ I₁) (hint : I₀ ⊓ I₁ ≤ Z) (hZ₀ : Z ≤ I₀)
    (hI₀ : ∀ x : ↥X, ∀ u ∈ I₀, (x : MulAut V) u ∈ I₀)
    (hI₁ : ∀ x : ↥X, ∀ u ∈ I₁, (x : MulAut V) u ∈ I₁) {u : V}
    (hu : u ∈ fixMod S (I₀ ⊔ I₁) Z) :
    ∃ u₀ u₁, u₀ ∈ fixMod S I₀ Z ∧ u₁ ∈ fixMod S I₁ Z ∧ u₀ * u₁ = u := by
  obtain ⟨hU, hs⟩ := hu
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := Subgroup.mem_sup.1 hU
  have key : ∀ s ∈ S, s u₀ * u₀⁻¹ ∈ Z ∧ s u₁ * u₁⁻¹ ∈ Z := by
    intro s hsS
    have e := hs s hsS
    rw [comm_mul_eq] at e
    have p₀ : s u₀ * u₀⁻¹ ∈ I₀ := I₀.mul_mem (hI₀ ⟨s, hSX hsS⟩ u₀ h₀) (I₀.inv_mem h₀)
    have p₁ : s u₁ * u₁⁻¹ ∈ I₁ := I₁.mul_mem (hI₁ ⟨s, hSX hsS⟩ u₁ h₁) (I₁.inv_mem h₁)
    have q₀ : s u₀ * u₀⁻¹ ∈ I₁ := by
      have := I₁.mul_mem (hZ₁ e) (I₁.inv_mem p₁)
      rwa [mul_inv_cancel_right] at this
    have q₁ : s u₁ * u₁⁻¹ ∈ I₀ := by
      have := I₀.mul_mem (I₀.inv_mem p₀) (hZ₀ e)
      rwa [inv_mul_cancel_left] at this
    exact ⟨hint ⟨p₀, q₀⟩, hint ⟨q₁, p₁⟩⟩
  exact ⟨u₀, u₁, ⟨h₀, fun s hs => (key s hs).1⟩, ⟨h₁, fun s hs => (key s hs).2⟩, rfl⟩

theorem fixMod_two_stable (x : ↥X) (hSX : S ≤ X) (hZ₁ : Z ≤ I₁) (hint : I₀ ⊓ I₁ ≤ Z)
    (hZ₀ : Z ≤ I₀) (hI₀ : ∀ x : ↥X, ∀ u ∈ I₀, (x : MulAut V) u ∈ I₀)
    (hI₁ : ∀ x : ↥X, ∀ u ∈ I₁, (x : MulAut V) u ∈ I₁)
    (h₀ : ∀ w ∈ fixMod S I₀ Z, (x : MulAut V) w ∈ fixMod S I₀ Z)
    (h₁ : ∀ w ∈ fixMod S I₁ Z, (x : MulAut V) w ∈ fixMod S I₁ Z) :
    ∀ u ∈ fixMod S (I₀ ⊔ I₁) Z, (x : MulAut V) u ∈ fixMod S (I₀ ⊔ I₁) Z := by
  intro u hu
  obtain ⟨u₀, u₁, hu₀, hu₁, rfl⟩ := fixMod_two_mem hSX hZ₁ hint hZ₀ hI₀ hI₁ hu
  obtain ⟨a₀, b₀⟩ := h₀ u₀ hu₀
  obtain ⟨a₁, b₁⟩ := h₁ u₁ hu₁
  refine ⟨?_, fun s hs => ?_⟩
  · rw [map_mul]
    exact Subgroup.mul_mem_sup a₀ a₁
  · rw [map_mul, comm_mul_eq]
    exact Z.mul_mem (b₀ s hs) (b₁ s hs)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥X}

theorem goodCoatom_of_two [Finite Γ] {I : Fin 2 → Subgroup V} (hZ : ∀ i, Z ≤ I i)
    (hint : I 0 ⊓ I 1 ≤ Z) (hreal : ∀ i, NatReal X (I i) Z Γ π)
    (hcov : ∀ T : Subgroup ↥Γ, IsSylowTwoOf T ⊤ → Qt Γ T ⋖ ⊤)
    (hUa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ I 0 ⊔ I 1 ↔ a u ∈ I 0 ⊔ I 1)
    (hZa : ∀ a ∈ Subgroup.normalizer (X : Set (MulAut V)), ∀ u, u ∈ Z ↔ a u ∈ Z)
    (hS : IsSylowTwoOf S X) : GoodCoatom X S := by
  have hsurj := (hreal 0).surj
  obtain ⟨T, hTs, hT⟩ := exists_cover_data π hsurj hS
  have hSX : S ≤ X := hS.1
  have hXn : ∀ x : ↥X, (x : MulAut V) ∈ Subgroup.normalizer (X : Set (MulAut V)) := fun x =>
    Subgroup.le_normalizer x.2
  have hIinv : ∀ i, ∀ x : ↥X, ∀ u, u ∈ I i ↔ (x : MulAut V) u ∈ I i := by
    intro i x u
    refine ⟨(hreal i).U_inv x u, fun h => ?_⟩
    have := (hreal i).U_inv x⁻¹ _ h
    simpa using this
  have hcomap : ∀ i, ((setStab (fixMod S (I i) Z)).comap X.subtype).comap π = Qt Γ T :=
    fun i => (hreal i).comap_eq hT
  have hQ01 : (setStab (fixMod S (I 0) Z)).comap X.subtype =
      (setStab (fixMod S (I 1) Z)).comap X.subtype :=
    Subgroup.comap_injective hsurj (by rw [hcomap 0, hcomap 1])
  have hstab : ∀ x : ↥X, x ∈ (setStab (fixMod S (I 0) Z)).comap X.subtype →
      x ∈ (setStab (fixMod S (I 1) Z)).comap X.subtype →
      ∀ w ∈ fixMod S (I 0 ⊔ I 1) Z, (x : MulAut V) w ∈ fixMod S (I 0 ⊔ I 1) Z :=
    fun x h0 h1 => fixMod_two_stable x hSX (hZ 1) hint (hZ 0)
      (fun y u hu => (hIinv 0 y u).1 hu) (fun y u hu => (hIinv 1 y u).1 hu)
      (fun w hw => (h0 w).1 hw) (fun w hw => (h1 w).1 hw)
  have hQ : (setStab (fixMod S (I 0 ⊔ I 1) Z)).comap X.subtype =
      (setStab (fixMod S (I 0) Z)).comap X.subtype := by
    ext x
    constructor
    · intro hx w
      have hΛ : ∀ w, w ∈ fixMod S (I 0) Z ↔ w ∈ I 0 ∧ w ∈ fixMod S (I 0 ⊔ I 1) Z := by
        intro w
        rw [mem_fixMod, mem_fixMod]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Subgroup.mem_sup_left h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      show w ∈ fixMod S (I 0) Z ↔ (x : MulAut V) w ∈ fixMod S (I 0) Z
      have hx' : ∀ u, u ∈ fixMod S (I 0 ⊔ I 1) Z ↔
          (x : MulAut V) u ∈ fixMod S (I 0 ⊔ I 1) Z := hx
      rw [hΛ, hΛ, ← hx' w, ← hIinv 0 x w]
    · intro hx
      have hx1 : x ∈ (setStab (fixMod S (I 1) Z)).comap X.subtype := hQ01 ▸ hx
      have f1 := hstab x hx hx1
      have f2 := hstab x⁻¹ (inv_mem hx) (inv_mem hx1)
      intro u
      refine ⟨f1 u, fun hxu => ?_⟩
      have := f2 _ hxu
      simpa using this
  refine ⟨(setStab (fixMod S (I 0 ⊔ I 1) Z)).comap X.subtype, ?_, fun x hx => ?_,
    fun a haX haS x y hy hx => ?_⟩
  · rw [hQ]
    exact covBy_top_of_comap π hsurj _ (by rw [hcomap 0]; exact hcov T hTs)
  · exact fixMod_inv hx (hUa _ (hXn x)) (hZa _ (hXn x))
  · have h1 := conj_mem_setStab (fixMod_inv haS (hUa a haX) (hZa a haX)) hx
    show (y : MulAut V) ∈ setStab (fixMod S (I 0 ⊔ I 1) Z)
    rw [hy]
    exact h1

end TwoZ

theorem sup_iff_apply {V : Type} [CommGroup V] {A B : Subgroup V} {a : MulAut V}
    (hA : ∀ u, u ∈ A ↔ a u ∈ A) (hB : ∀ u, u ∈ B ↔ a u ∈ B) :
    ∀ u, u ∈ A ⊔ B ↔ a u ∈ A ⊔ B := by
  have hmap : ∀ C : Subgroup V, (∀ u, u ∈ C ↔ a u ∈ C) → C.map a.toMonoidHom = C := by
    intro C hC
    ext x
    rw [Subgroup.mem_map_equiv, hC (a.symm x), MulEquiv.apply_symm_apply]
  have h1 : (A ⊔ B).map a.toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmap A hA, hmap B hB]
  intro u
  constructor
  · intro hu
    rw [← h1]
    exact ⟨u, hu, rfl⟩
  · intro hu
    rw [← h1] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    have : w = u := a.injective hwu
    rwa [← this]

variable {G : Type} [Group G]

theorem fixV_autOn_eq {L W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    fixV (autOn L W) = (Subgroup.centralizer (L : Set G)).subgroupOf W :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hLW

section Module

variable {L T : Subgroup G} [IsMulCommutative ↥(vPlus L T)]

theorem cvPlus_eq (hML : mPlus L T = L) (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G)) :
    cvPlus L T = fixV (autOn L (vPlus L T)) := by
  rw [fixV_autOn_eq hLV]
  show (Subgroup.centralizer (mPlus L T : Set G)).subgroupOf (vPlus L T) = _
  rw [hML]

theorem tildeComm_eq (hML : mPlus L T = L)
    (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G)) :
    tildeComm L T L = commV (autOn L (vPlus L T)) ⊔ fixV (autOn L (vPlus L T)) := by
  show commVPlus L T L ⊔ cvPlus L T = _
  rw [cvPlus_eq hML hLV, commV_autOn_eq1527d hLV]

theorem tildeComm_iff_apply (hML : mPlus L T = L)
    (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G)) :
    ∀ a ∈ Subgroup.normalizer (autOn L (vPlus L T) : Set (MulAut ↥(vPlus L T))),
      ∀ u, u ∈ tildeComm L T L ↔ a u ∈ tildeComm L T L := by
  intro a ha
  rw [tildeComm_eq hML hLV]
  exact sup_iff_apply (commV_iff_apply ha) (fixV_iff_apply ha)

theorem cvPlus_iff_apply (hML : mPlus L T = L)
    (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G)) :
    ∀ a ∈ Subgroup.normalizer (autOn L (vPlus L T) : Set (MulAut ↥(vPlus L T))),
      ∀ u, u ∈ cvPlus L T ↔ a u ∈ cvPlus L T := by
  intro a ha
  rw [cvPlus_eq hML hLV]
  exact fixV_iff_apply ha

theorem goodCoatom_sl3 (hML : mPlus L T = L)
    (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G))
    {S : Subgroup (MulAut ↥(vPlus L T))} (hS : IsSylowTwoOf S (autOn L (vPlus L T)))
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hmod : BinaryNaturalSL (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) 3 n ∨
      DirectSumOfCopies (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T)
        (FFModel.nat (StatedSL 3 K)) 2) :
    GoodCoatom (autOn L (vPlus L T)) S := by
  have hUa := tildeComm_iff_apply hML hLV
  have hZa := cvPlus_iff_apply hML hLV
  rcases hmod with ⟨F, _, _, hF, π, hπ⟩ | ⟨I, π, hZI, hind, hsup, hreal⟩
  · have := charP_two_of_card hF
    exact (NatReal.of_realizesVia hπ).goodCoatom (fun T hT => sl3_Qt_covBy ⟨n, hF⟩ hT) hUa hZa
      hS
  · have := charP_two_of_card hK
    have hint : I 0 ⊓ I 1 ≤ cvPlus L T := by
      rw [← hind 0]
      exact inf_le_inf_left _ (le_sup_of_le_right (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl))
    have hsup' : I 0 ⊔ I 1 = tildeComm L T L := by
      rw [← hsup]
      have h1 : (⨆ i, I i) = I 0 ⊔ I 1 :=
        le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
          (sup_le (le_iSup I 0) (le_iSup I 1))
      rw [h1, sup_eq_right.mpr ((hZI 0).trans le_sup_left)]
    refine goodCoatom_of_two hZI hint (fun i => NatReal.of_realizesVia (hreal i))
      (fun T hT => sl3_Qt_covBy ⟨n, hK⟩ hT) (fun a ha u => ?_) hZa hS
    rw [hsup']
    exact hUa a ha u

theorem goodCoatom_sp4 (hML : mPlus L T = L)
    (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G))
    {S : Subgroup (MulAut ↥(vPlus L T))} (hS : IsSylowTwoOf S (autOn L (vPlus L T))) {n : ℕ}
    (hmod : BinaryNaturalSp4 (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) n) :
    GoodCoatom (autOn L (vPlus L T)) S := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hmod
  have := charP_two_of_card hF
  exact (NatReal.of_realizesVia hπ).goodCoatom (fun T hT => sp4_Qt_covBy ⟨n, hF⟩ hT)
    (tildeComm_iff_apply hML hLV) (cvPlus_iff_apply hML hLV) hS

end Module

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

variable [Finite G]

theorem le_normalizer_parabolic {L T W : Subgroup G} [IsMulCommutative ↥W]
    (hlie : IsSL3Quot L ∨ IsSp4Quot L) (hS₀ : IsSylowTwoOf (T ⊓ L) L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hgood : GoodCoatom (autOn L W) (autOn (T ⊓ L) W)) {P : Subgroup G}
    (hP : IsMaxParabolic2 L P)
    (hBP : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ P) :
    T ≤ Subgroup.normalizer (P : Set G) := by
  have hTS : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer ht) (hTL ht)
  obtain ⟨P₀, hP₀, hBP₀, hAP₀⟩ := exists_good_parabolic hLW hS₀ hTL hTW hTS hgood
  obtain ⟨P₁, P₂, hP₁, hP₂, hne, hB₁, hB₂, huniq⟩ :=
    rankTwoMaxParabolics_holds G L (T ⊓ L) hlie hS₀
  have hyB : ∀ g ∈ T, B6.conjSub g (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) =
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro g hg
    rw [OrderIso.map_inf, B6.conjSub_eq_self (hTL hg),
      B6.conjSub_eq_self (Subgroup.le_normalizer (hTS hg))]
  have hmem : ∀ g ∈ T, ∀ Q : Subgroup G, IsMaxParabolic2 L Q →
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ Q →
      B6.conjSub g Q = P₁ ∨ B6.conjSub g Q = P₂ := by
    intro g hg Q hQ hBQ
    refine huniq _ (S153D.isMaxParabolic2_conjSub (hTL hg) hQ) ?_
    have := (B6.conjSub g).monotone hBQ
    rwa [hyB g hg] at this
  have hfix : ∀ g ∈ T, B6.conjSub g P₁ = P₁ ∧ B6.conjSub g P₂ = P₂ := by
    intro g hg
    have h0 : B6.conjSub g P₀ = P₀ := B6.conjSub_eq_self (hAP₀ hg)
    have h1 := hmem g hg P₁ hP₁ hB₁
    have h2 := hmem g hg P₂ hP₂ hB₂
    rcases huniq P₀ hP₀ hBP₀ with he | he
    · rw [he] at h0
      refine ⟨h0, ?_⟩
      rcases h2 with h | h
      · exact absurd ((B6.conjSub g).injective (h.trans h0.symm)) hne.symm
      · exact h
    · rw [he] at h0
      refine ⟨?_, h0⟩
      rcases h1 with h | h
      · exact h
      · exact absurd ((B6.conjSub g).injective (h.trans h0.symm)) hne
  rcases huniq P hP hBP with he | he
  · intro g hg
    rw [he]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg).1
  · intro g hg
    rw [he]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg).2

end L3316

end CFSG.Quasithin.H13
