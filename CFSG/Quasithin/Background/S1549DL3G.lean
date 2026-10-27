module

public import CFSG.Quasithin.Background.S1549DGen
public import CFSG.Quasithin.Background.S1549DL3F
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.QuasithinUnique

theorem vec_sq (v : Multiplicative L3.Vec) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  have : (Multiplicative.toAdd v i) + Multiplicative.toAdd v i = 0 := by
    generalize Multiplicative.toAdd v i = a
    revert a
    decide
  simpa [pow_two] using this

@[expose] def fixΓ (A' : Subgroup L3.Γ) : Subgroup (Multiplicative L3.Vec) where
  carrier := {c | ∀ γ ∈ A', L3.act γ (Multiplicative.toAdd c) = Multiplicative.toAdd c}
  one_mem' := fun γ _ => by
    show L3.act γ (Multiplicative.toAdd (1 : Multiplicative L3.Vec)) = _
    simp [L3.act_zero]
  mul_mem' := fun {a b} ha hb γ hγ => by
    show L3.act γ (Multiplicative.toAdd (a * b)) = Multiplicative.toAdd (a * b)
    rw [toAdd_mul, L3.act_add, ha γ hγ, hb γ hγ]
  inv_mem' := fun {a} ha γ hγ => by
    have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact vec_sq a)
    exact (congrArg (L3.act γ) (congrArg Multiplicative.toAdd h)).trans
      ((ha γ hγ).trans (congrArg Multiplicative.toAdd h).symm)

theorem mem_fixΓ {A' : Subgroup L3.Γ} {c : Multiplicative L3.Vec} :
    c ∈ fixΓ A' ↔ ∀ γ ∈ A', L3.act γ (Multiplicative.toAdd c) = Multiplicative.toAdd c := Iff.rfl

variable {V : Type} [CommGroup V] [Finite V]

theorem rkIdx_fixΓ_le {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data L U Z)
    (A : Subgroup (MulAut V)) : rkIdx (fixΓ (A.comap D.rho)) ≤ rkIdx (fixV A) := by
  set K := fixΓ (A.comap D.rho) with hK
  set Cs : Subgroup ↥U := (fixV A).subgroupOf U with hCs
  have hle : Cs ≤ K.comap D.β := by
    intro u hu
    rw [Subgroup.mem_comap, hK, mem_fixΓ]
    intro γ hγ
    have hu' : (u : V) ∈ fixV A := Subgroup.mem_subgroupOf.mp hu
    have hργ : D.rho γ ∈ A := hγ
    have hfix : D.rho γ (u : V) = u := hu' _ hργ
    have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h1 := D.β_rho γ (u : V) u.2 hmem
    have h2 : (⟨D.rho γ (u : V), hmem⟩ : ↥U) = u := Subtype.ext hfix
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa using h3.symm
  have h1 : (K.comap D.β).index = K.index := Subgroup.index_comap_of_surjective K D.β_surj
  have h2 : (K.comap D.β).index ∣ Cs.index := Subgroup.index_dvd_of_le hle
  have h3 : Cs.index ∣ (fixV A).index := Subgroup.relIndex_dvd_index_of_normal (fixV A) U
  have h4 : K.index ∣ (fixV A).index := h1 ▸ h2.trans h3
  exact padicValNat_two_le_of_dvd (Subgroup.index_ne_zero_of_finite) h4

theorem exists_plane_of_strong {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (D : L3Data L U Z) {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hst : rkIdx (fixV A) < rk A) :
    ∃ S : Finset L3.Vec, L3.IsPlane S ∧ A = (L3.bsSub S).map D.rho := by
  classical
  have hrk : rk A ≤ 2 := by
    have h4 := D.elemAbelian_card_le_four hAL hA
    rw [B1.card_elemAbelian hA] at h4
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) h
    omega
  set A' : Subgroup L3.Γ := A.comap D.rho with hA'
  set K := fixΓ A' with hK
  have hKle : rkIdx K ≤ rkIdx (fixV A) := rkIdx_fixΓ_le D A
  have hAmap : A'.map D.rho = A := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact hγ
    · intro hx
      obtain ⟨γ, hγ⟩ := D.exists_rho (hAL hx)
      exact ⟨γ, by show D.rho γ ∈ A; rw [hγ]; exact hx, hγ⟩
  have hcardA' : Nat.card A' = Nat.card A :=
    calc Nat.card A' = Nat.card (A'.map D.rho) :=
          (Subgroup.card_map_of_injective D.rho_injective).symm
      _ = Nat.card A := by rw [hAmap]
  have hKtop : K ≠ ⊤ := by
    intro hKt
    apply hA1
    rw [← hAmap, eq_bot_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    have h1 : γ = 1 := L3.act_injective γ fun v => by
      have := (mem_fixΓ.mp (hKt ▸ Subgroup.mem_top (Multiplicative.ofAdd v))) γ hγ
      simpa using this
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hVec : ∀ v : Multiplicative L3.Vec, v ^ 2 = 1 := vec_sq
  have hidx : K.index = 2 ^ rkIdx K := B1.index_eq_two_pow hVec K
  have hidx1 : K.index ≠ 1 := fun h => hKtop (Subgroup.index_eq_one.mp h)
  have hrkK1 : rkIdx K = 1 := by
    have h1 : 1 ≤ rkIdx K := by
      by_contra h
      push Not at h
      have : rkIdx K = 0 := by omega
      rw [this, pow_zero] at hidx
      exact hidx1 hidx
    omega
  have hrkA : rk A = 2 := by omega
  have hcardA : Nat.card A = 4 := by
    rw [B1.card_elemAbelian hA, hrkA]
    norm_num
  have hcardK : Nat.card K = 4 := by
    have h1 := Subgroup.index_mul_card K
    rw [hidx, hrkK1] at h1
    have h8 : Nat.card (Multiplicative L3.Vec) = 8 := L3Data.card_vec
    rw [h8] at h1
    omega
  set S : Finset L3.Vec := Finset.univ.filter fun v => Multiplicative.ofAdd v ∈ K with hS
  have hSmem : ∀ v, v ∈ S ↔ Multiplicative.ofAdd v ∈ K := fun v => by simp [hS]
  have hSplane : L3.IsPlane S := by
    refine ⟨?_, ?_, ?_⟩
    · have hc : S.card = Nat.card K := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact Finset.card_bij (fun v _ => Multiplicative.ofAdd v)
          (fun v hv => by simpa [hS] using hv)
          (fun a _ b _ h => Multiplicative.ofAdd.injective h)
          (fun c hc => ⟨Multiplicative.toAdd c, by simpa [hS] using hc, by simp⟩)
      rw [hc, hcardK]
    · rw [hSmem]
      exact K.one_mem
    · intro x hx y hy
      rw [hSmem] at hx hy ⊢
      have := K.mul_mem hx hy
      simpa using this
  refine ⟨S, hSplane, ?_⟩
  have hle : A' ≤ L3.bsSub S := by
    intro γ hγ v hv
    have := (mem_fixΓ.mp ((hSmem v).mp hv)) γ hγ
    simpa using this
  have heq : A' = L3.bsSub S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [L3.card_bsSub hSplane, hcardA', hcardA])
  rw [← heq, hAmap]

omit [Finite V] in
theorem le_map_stabSub_of_normalizes {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data L U Z)
    {S : Finset L3.Vec} (hS : L3.IsPlane S) {P : Subgroup (MulAut V)} (hPL : P ≤ L)
    (hP : P ≤ Subgroup.normalizer (((L3.bsSub S).map D.rho : Subgroup (MulAut V)) : Set (MulAut V))) :
    P ≤ (L3.stabSub S).map D.rho := by
  intro p hp
  obtain ⟨γ, hγ⟩ := D.exists_rho (hPL hp)
  refine ⟨γ, L3.mem_stabSub_of_normalizes hS fun k hk => ?_, hγ⟩
  have hk' : D.rho k ∈ (L3.bsSub S).map D.rho := ⟨k, hk, rfl⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp (hP hp) (D.rho k)).mp hk'
  obtain ⟨k', hk'S, hk'eq⟩ := hconj
  have h1 : D.rho (γ * k * γ⁻¹) = D.rho k' := by
    rw [map_mul, map_mul, map_inv, hγ, hk'eq]
  rw [D.rho_injective h1]
  exact hk'S

omit [Finite V] in
theorem isSylowTwoOf_of_le' {S X Y : Subgroup (MulAut V)} (hS : IsSylowTwoOf S X) (hSY : S ≤ Y)
    (hYX : Y ≤ X) : IsSylowTwoOf S Y := by
  refine ⟨hSY, hS.2.1, fun hd => hS.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S Y X hSY hYX
  exact hd.trans (Dvd.intro _ h)

open CFSG.Open CFSG.LieType.BorelTits in
theorem l3_geometry (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (D : L3Data L U Z) (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z)
    {S P M' A : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (hPL : P ≤ L) (hSP : S ≤ P) (hSne : S ≠ P)
    (hSn : ¬ P ≤ Subgroup.normalizer (S : Set (MulAut V))) (hPM : P ≤ M')
    (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hAL : A ≤ L) (hAP : A ≤ pCoreOf 2 P)
    (hst : rkIdx (fixV A) < rk A)
    {u c : V} (hu : u ∈ U) (hu0 : D.β ⟨u, hu⟩ ≠ 1) (hSu : ∀ s ∈ S, s u = u) (hc : c ∈ fixV L)
    (hM : ∀ g ∈ L, g (u * c) = u * c → g ∈ M') : L ≤ M' := by
  classical
  obtain ⟨S₀, hS₀, hAS₀⟩ := exists_plane_of_strong D hAL hA hA1 hst
  have hSP' : IsSylowTwoOf S P := isSylowTwoOf_of_le' hS hSP hPL
  have hR₀S : pCoreOf 2 P ≤ S := IsSylowTwoOf.pCoreOf_le hSP'
  have hR₀ne : pCoreOf 2 P ≠ S := fun h => hSn (h ▸ le_normalizer_pCoreOf 2 P)
  have hS8 : Nat.card S = 8 := D.card_sylow hS
  have hcardA : Nat.card A = 4 := by
    rw [hAS₀, Subgroup.card_map_of_injective D.rho_injective, L3.card_bsSub hS₀]
  have hR₀card : Nat.card (pCoreOf 2 P) ≤ 4 := by
    have hdvd : Nat.card (pCoreOf 2 P) ∣ 8 := hS8 ▸ Subgroup.card_dvd_of_le hR₀S
    have hne : Nat.card (pCoreOf 2 P) ≠ 8 := fun h8 =>
      hR₀ne (Subgroup.eq_of_le_of_card_ge hR₀S (by rw [hS8, h8]))
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have key : ∀ n : ℕ, n ≤ 8 → n ∣ 8 → n ≠ 8 → n ≤ 4 := by decide
    exact key _ hle hdvd hne
  have hAR : A = pCoreOf 2 P := Subgroup.eq_of_le_of_card_ge hAP (by rw [hcardA]; exact hR₀card)
  have hPN : P ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
    rw [hAR]
    exact le_normalizer_pCoreOf 2 P
  have hPstab : P ≤ (L3.stabSub S₀).map D.rho :=
    le_map_stabSub_of_normalizes D hS₀ hPL (by rw [← hAS₀]; exact hPN)
  have hcardstab : Nat.card ((L3.stabSub S₀).map D.rho) = 24 := by
    rw [Subgroup.card_map_of_injective D.rho_injective, L3.card_stabSub hS₀]
  have hPeq : P = (L3.stabSub S₀).map D.rho := by
    have hdvd1 : Nat.card S ∣ Nat.card P := Subgroup.card_dvd_of_le hSP
    have hdvd2 : Nat.card P ∣ 24 := hcardstab ▸ Subgroup.card_dvd_of_le hPstab
    rw [hS8] at hdvd1
    have hP24 : Nat.card P = 24 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd2
      have hne8 : Nat.card P ≠ 8 := fun h8 =>
        hSne (Subgroup.eq_of_le_of_card_ge hSP (by rw [hS8, h8]))
      have key : ∀ n : ℕ, n ≤ 24 → 8 ∣ n → n ∣ 24 → n ≠ 8 → n = 24 := by decide
      exact key _ hle hdvd1 hdvd2 hne8
    exact Subgroup.eq_of_le_of_card_ge hPstab (by rw [hcardstab, hP24])
  set x₀ : L3.Vec := Multiplicative.toAdd (D.β ⟨u, hu⟩) with hx₀
  have hx₀ne : x₀ ≠ 0 := fun h => hu0 (by
    apply Multiplicative.toAdd.injective
    simpa [hx₀] using h)
  set Pt : Subgroup (MulAut V) := (L3.ptSub x₀).map D.rho with hPt
  have hPtL : Pt ≤ L := by
    rintro _ ⟨γ, -, rfl⟩
    exact D.rho_mem γ
  have hSPt : S ≤ Pt := by
    intro s hs
    obtain ⟨γ, hγ⟩ := D.exists_rho (hS.le hs)
    refine ⟨γ, ?_, hγ⟩
    show L3.act γ x₀ = x₀
    have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) _ hu
    have h1 := D.β_rho γ u hu hmem
    have h2 : (⟨D.rho γ u, hmem⟩ : ↥U) = ⟨u, hu⟩ := by
      apply Subtype.ext
      show D.rho γ u = u
      rw [hγ]
      exact hSu s hs
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa [hx₀] using h3.symm
  have hSPt' : IsSylowTwoOf S Pt := isSylowTwoOf_of_le' hS hSPt hPtL
  have hZPt : Z ≤ fixV Pt := fun z hz p hp => hZ p (hPtL hp) z hz
  have hPtu : ∀ p ∈ Pt, p u * u⁻¹ ∈ Z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ' : L3.act γ x₀ = x₀ := hγ
    have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) _ hu
    have h1 := D.β_rho γ u hu hmem
    have h2 : D.β ⟨D.rho γ u, hmem⟩ = D.β ⟨u, hu⟩ := by
      rw [h1]
      apply Multiplicative.toAdd.injective
      simpa [hx₀] using hγ'
    have hmem2 : D.rho γ u * u⁻¹ ∈ U := U.mul_mem hmem (U.inv_mem hu)
    have h3 : D.β ⟨D.rho γ u * u⁻¹, hmem2⟩ = 1 := by
      have : (⟨D.rho γ u * u⁻¹, hmem2⟩ : ↥U) = ⟨D.rho γ u, hmem⟩ * ⟨u, hu⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, h2]
      exact mul_inv_cancel _
    exact (D.ker_β _).mp h3
  have hufix : u ∈ fixV Pt := mem_fixV_of_sylow hV hSPt' hSu hZPt hPtu
  have hPtM : Pt ≤ M' := by
    intro p hp
    have hpL := hPtL hp
    refine hM p hpL ?_
    rw [map_mul, hufix p hp, hc p hpL]
  have htop := L3.ptSub_sup_stabSub_eq_top hx₀ne hS₀
  have hle : (L3.ptSub x₀ ⊔ L3.stabSub S₀).map D.rho ≤ M' := by
    rw [Subgroup.map_sup]
    exact sup_le hPtM (hPeq ▸ hPM)
  intro l hl
  obtain ⟨γ, rfl⟩ := D.exists_rho hl
  exact hle ⟨γ, by rw [htop]; exact Subgroup.mem_top γ, rfl⟩

@[expose] def kerSec (X : Subgroup (MulAut V)) (U Z : Subgroup V)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) : Subgroup (MulAut V) where
  carrier := {y | y ∈ X ∧ ∀ u ∈ U, y u * u⁻¹ ∈ Z}
  one_mem' := ⟨X.one_mem, fun u _ => by simp⟩
  mul_mem' := fun {y y'} hy hy' => by
    refine ⟨X.mul_mem hy.1 hy'.1, fun u hu => ?_⟩
    have h1 := hy.2 (y' u) (hXU y' hy'.1 u hu)
    have h2 := hy'.2 u hu
    have := Z.mul_mem h1 h2
    have e : y (y' u) * (y' u)⁻¹ * (y' u * u⁻¹) = (y * y') u * u⁻¹ := by
      simp only [MulAut.mul_apply]
      group
    rwa [e] at this
  inv_mem' := fun {y} hy => by
    refine ⟨X.inv_mem hy.1, fun u hu => ?_⟩
    have hw : y⁻¹ u ∈ U := hXU y⁻¹ (X.inv_mem hy.1) u hu
    have h1 := hy.2 (y⁻¹ u) hw
    have e1 : y (y⁻¹ u) = u := by simp
    rw [e1] at h1
    have := Z.inv_mem h1
    simpa using this

omit [Finite V] in
theorem kerSec_normal {X : Subgroup (MulAut V)} {U Z : Subgroup V} (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U)
    (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x z ∈ Z) {g n : MulAut V} (hg : g ∈ X) (hn : n ∈ kerSec X U Z hXU) :
    g * n * g⁻¹ ∈ kerSec X U Z hXU := by
  refine ⟨X.mul_mem (X.mul_mem hg hn.1) (X.inv_mem hg), fun u hu => ?_⟩
  have hw : g⁻¹ u ∈ U := hXU g⁻¹ (X.inv_mem hg) u hu
  have h1 := hn.2 (g⁻¹ u) hw
  have h2 := hXZ g hg _ h1
  have e : g (n (g⁻¹ u) * (g⁻¹ u)⁻¹) = (g * n * g⁻¹) u * u⁻¹ := by
    rw [map_mul, map_inv]
    simp
  rwa [e] at h2

omit [Finite V] in
open CFSG.Open CFSG.LieType.BorelTits in
theorem kerSec_le_pCoreOf {L X : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data L U Z)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x z ∈ Z)
    (hX2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L) : kerSec X U Z hXU ≤ pCoreOf 2 X := by
  have hNX : kerSec X U Z hXU ≤ X := fun y hy => hy.1
  have hNnormal : ((kerSec X U Z hXU).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hNX).2 fun n g hn hg => kerSec_normal hXU hXZ hg hn
  have hNL : ∀ l ∈ L, l ∈ kerSec X U Z hXU → l = 1 := by
    intro l hl hlk
    obtain ⟨γ, rfl⟩ := D.exists_rho hl
    have h1 : γ = 1 := by
      apply L3.act_injective
      intro v
      obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd v)
      have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
      have h2 := D.β_rho γ u u.2 hmem
      have h3 := hlk.2 u u.2
      have h4 : D.β ⟨D.rho γ u * (u : V)⁻¹, U.mul_mem hmem (U.inv_mem u.2)⟩ = 1 :=
        (D.ker_β _).mpr h3
      have h5 : D.β ⟨D.rho γ u, hmem⟩ = D.β u := by
        have : (⟨D.rho γ u * (u : V)⁻¹, U.mul_mem hmem (U.inv_mem u.2)⟩ : ↥U) =
            ⟨D.rho γ u, hmem⟩ * u⁻¹ := rfl
        rw [this, map_mul, map_inv] at h4
        exact mul_inv_eq_one.mp h4
      rw [h2, hu] at h5
      simpa using congrArg Multiplicative.toAdd h5
    rw [h1, map_one]
  have hN2 : IsPGroup 2 ↥(kerSec X U Z hXU) := by
    intro n
    obtain ⟨e, he⟩ := hX2 (n : MulAut V) (hNX n.2)
    refine ⟨e, ?_⟩
    have hmem : (n : MulAut V) ^ 2 ^ e ∈ kerSec X U Z hXU := Subgroup.pow_mem _ n.2 _
    have := hNL _ he hmem
    exact Subtype.ext (by simpa using this)
  exact le_pCoreOf 2 hNX hNnormal hN2

omit [Finite V] in
open CFSG.Open CFSG.LieType.BorelTits in
theorem le_of_two_quotient {L X : Subgroup (MulAut V)} {U Z : Subgroup V}
    (D : L3Data L U Z) (hZL : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hLX : L ≤ X)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U) (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x z ∈ Z)
    (hX2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L) (hO2 : pCoreOf 2 X = ⊥) : X ≤ L := by
  classical
  intro x hx
  let xU : ↥U →* ↥U := ((x : V ≃* V).toMonoidHom.comp U.subtype).codRestrict U
    (fun u => hXU x hx u u.2)
  let ψ : ↥U →* Multiplicative L3.Vec := D.β.comp xU
  have hψker : D.β.ker ≤ ψ.ker := by
    intro u hu
    have hu' : (u : V) ∈ Z := (D.ker_β u).mp hu
    exact (D.ker_β (xU u)).mpr (hXZ x hx _ hu')
  let Φ : Multiplicative L3.Vec →* Multiplicative L3.Vec :=
    MonoidHom.liftOfSurjective D.β D.β_surj ⟨ψ, hψker⟩
  have hΦ : ∀ u : ↥U, Φ (D.β u) = ψ u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply D.β _ (Function.rightInverse_surjInv D.β_surj)
      ⟨ψ, hψker⟩ u
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    obtain ⟨u, rfl⟩ := D.β_surj c
    rw [hΦ] at hc
    have h1 : (xU u : V) ∈ Z := (D.ker_β (xU u)).mp hc
    have h2 : (u : V) ∈ Z := by
      have := hXZ x⁻¹ (X.inv_mem hx) _ h1
      simpa [xU] using this
    exact (D.ker_β u).mpr h2
  let Φ'' : L3.Vec → L3.Vec := fun v => Multiplicative.toAdd (Φ (Multiplicative.ofAdd v))
  have hΦ''add : ∀ v w, Φ'' (v + w) = Φ'' v + Φ'' w := fun v w => by
    show Multiplicative.toAdd (Φ (Multiplicative.ofAdd (v + w))) = _
    rw [ofAdd_add, map_mul, toAdd_mul]
  have hΦ''zero : Φ'' 0 = 0 := by
    show Multiplicative.toAdd (Φ (Multiplicative.ofAdd 0)) = 0
    rw [ofAdd_zero, map_one, toAdd_one]
  let lin : L3.Vec →ₗ[ZMod 2] L3.Vec :=
    { toFun := Φ''
      map_add' := hΦ''add
      map_smul' := fun c v => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simp [hΦ''zero]
        · simp }
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' lin
  have hMapply : ∀ v, M.mulVec v = Φ'' v := fun v => LinearMap.toMatrix'_mulVec lin v
  have hMinj : Function.Injective M.mulVec := by
    intro v w hvw
    rw [hMapply, hMapply] at hvw
    have := hΦinj (Multiplicative.toAdd.injective hvw)
    exact Multiplicative.ofAdd.injective this
  have hMunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hMinj
  have hdet : M.det = 1 := by
    have h1 : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hMunit).ne_zero
    generalize M.det = a at h1 ⊢
    revert a
    decide
  let γ : L3.Γ := ⟨M, hdet⟩
  have hγact : ∀ v, L3.act γ v = Φ'' v := fun v => hMapply v
  have hxγ : ∀ u : ↥U, (x u * (D.rho γ u)⁻¹) ∈ Z := by
    intro u
    have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h1 := D.β_rho γ u u.2 hmem
    have h2 : D.β ⟨D.rho γ u, hmem⟩ = D.β (xU u) := by
      rw [h1]
      have : D.β (xU u) = ψ u := rfl
      rw [this, ← hΦ]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd]
      rw [hγact]
      rfl
    have h3 : D.β (xU u * ⟨D.rho γ u, hmem⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h2]
      exact mul_inv_cancel _
    have := (D.ker_β _).mp h3
    simpa [xU] using this
  set y : MulAut V := (D.rho γ)⁻¹ * x with hy
  have hyX : y ∈ X := X.mul_mem (X.inv_mem (hLX (D.rho_mem γ))) hx
  have hyker : y ∈ kerSec X U Z hXU := by
    refine ⟨hyX, fun u hu => ?_⟩
    have h1 := hxγ ⟨u, hu⟩
    have hinvL : (D.rho γ)⁻¹ ∈ L := L.inv_mem (D.rho_mem γ)
    have h2 := hZL _ hinvL _ h1
    have e : (D.rho γ)⁻¹ (x u * (D.rho γ u)⁻¹) = y u * u⁻¹ := by
      rw [map_mul, map_inv]
      simp [hy]
    rw [← e, h2]
    exact h1
  have hy1 : y = 1 := by
    have hle := kerSec_le_pCoreOf D hXU hXZ hX2
    have := hle hyker
    rw [hO2] at this
    exact Subgroup.mem_bot.mp this
  have hxy : x = D.rho γ := by
    have : (D.rho γ)⁻¹ * x = 1 := hy1
    exact (inv_mul_eq_one.mp this).symm
  rw [hxy]
  exact D.rho_mem γ

end S1549D

end CFSG.Quasithin
