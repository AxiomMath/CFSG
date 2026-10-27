module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlusCoords
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlusElems
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlusPermute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlusSylow
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

local notation "ιP" => Fin 2 ⊕ Fin 2

theorem kOmPlus_holds : KOmPlus := by
  intro W _ _ H n S Tstar hF
  obtain ⟨hn, hN, hTN, hT2, hST, hTfix⟩ := hF
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, e, hH, hfix⟩ := KOm.exists_plusCoords hn hN S
  letI := hKfield
  letI := hKfin
  letI := hKchar
  classical
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hrprime, hrne2, hrdvd, a₀, ha₀, b₀, hb₀, w₀, hw₀, horda, hordb, hcomm,
    ha₀e1, ⟨ν, hν1, hb₀e1⟩, hw₀sq, hw₀a, hw₀b, hw₀e1⟩ :=
    KOm.exists_torus_weyl (K := K) hK4
  set Γ : Subgroup (GL ιP K) := StatedOmega (StatedQuadPlus 2 K) with hΓ
  have ha₀Γ : a₀ ∈ Γ := by rw [hΓ]; exact ha₀
  have hb₀Γ : b₀ ∈ Γ := by rw [hΓ]; exact hb₀
  have hw₀Γ : w₀ ∈ Γ := by rw [hΓ]; exact hw₀
  let Φ : MulAut W ≃* MulAut (Multiplicative (ιP → K)) := MulAut.congr e
  let τ : GL ιP K →* MulAut W := (Φ.symm).toMonoidHom.comp (s16gNatHom ιP K)
  have hτinj : Function.Injective τ := by
    intro A B hAB
    have h : Φ.symm (s16gNatHom ιP K A) = Φ.symm (s16gNatHom ιP K B) := hAB
    exact s16gNatHom_injective (Φ.symm.injective h)
  have hτmem : ∀ A ∈ Γ, τ A ∈ H := by
    intro A hA
    refine KOm.congr_symm_natHom_mem (e := e) (H := H) (Γ := Γ) ?_ hA
    rw [hΓ]
    exact hH
  have hτcoord : ∀ (A : GL ιP K) (x : W),
      Multiplicative.toAdd (e (τ A x)) = (A : Matrix ιP ιP K) *ᵥ Multiplicative.toAdd (e x) :=
    fun A x => KOm.toAdd_congr_symm_natHom (e := e) A x
  have hΦτ : ∀ A : GL ιP K, Φ (τ A) = s16gNatHom ιP K A := fun A => Φ.apply_symm_apply _
  set ℓ : Subgroup W := CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) with hℓ
  have hfix' : ∀ x : W, x ∈ ℓ ↔ ∃ c' : K, Multiplicative.toAdd (e x) = c' • KTabC.e1P K :=
    fun x => hℓ ▸ hfix x
  have he1ne : KTabC.e1P K ≠ 0 := by
    intro h0
    have h := congrFun h0 (Sum.inl 0)
    simp [KTabC.e1P] at h
  have hxl₀ : e.symm (Multiplicative.ofAdd (KTabC.e1P K)) ∈ ℓ := by
    refine (hfix' _).mpr ⟨1, ?_⟩
    rw [MulEquiv.apply_symm_apply, one_smul]
    rfl
  have hxcoord : Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd (KTabC.e1P K)))) =
      KTabC.e1P K := by
    rw [MulEquiv.apply_symm_apply]
    rfl
  set a : MulAut W := τ a₀ with ha
  set b : MulAut W := τ b₀ with hb
  set w : MulAut W := τ w₀ with hw
  have haH : a ∈ H := hτmem a₀ ha₀Γ
  have hbH : b ∈ H := hτmem b₀ hb₀Γ
  have hwH : w ∈ H := hτmem w₀ hw₀Γ
  have hordA : orderOf a = r := by
    rw [ha, orderOf_injective τ hτinj a₀, horda]
  have hordB : orderOf b = r := by
    rw [hb, orderOf_injective τ hτinj b₀, hordb]
  have hrdvd' : r ∣ 2 ^ n - 1 := by
    rw [← hKcard]
    exact hrdvd
  have hcomm' : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul, hcomm]
  have hafix : ∀ x ∈ ℓ, a x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := (hfix' x).mp hx
    have h1 : Multiplicative.toAdd (e (a x)) = Multiplicative.toAdd (e x) := by
      rw [ha, hτcoord, hc, Matrix.mulVec_smul, ha₀e1]
    exact e.injective (by simpa using h1)
  have hbmap : ℓ.map (b : MulAut W).toMonoidHom = ℓ := by
    have hle : ℓ.map (b : MulAut W).toMonoidHom ≤ ℓ := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hfix' x).mp hx
      refine (hfix' (b x)).mpr ⟨c * ν, ?_⟩
      rw [hb, hτcoord, hc, Matrix.mulVec_smul, hb₀e1, smul_smul]
    have hcard : Nat.card ↥(ℓ.map (b : MulAut W).toMonoidHom) = Nat.card ↥ℓ :=
      Subgroup.card_map_of_injective (f := (b : MulAut W).toMonoidHom) b.injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hbne : ∃ x ∈ ℓ, b x ≠ x := by
    refine ⟨e.symm (Multiplicative.ofAdd (KTabC.e1P K)), ?_, ?_⟩
    · refine (hfix' _).mpr ⟨1, ?_⟩
      simpa using hxcoord
    · intro hbx
      have h3 : Multiplicative.toAdd (e (b (e.symm (Multiplicative.ofAdd (KTabC.e1P K))))) =
          Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd (KTabC.e1P K)))) := by
        rw [hbx]
      rw [hb, hτcoord] at h3
      have h2 : ν • KTabC.e1P K = KTabC.e1P K := by
        simpa [hb₀e1] using h3
      have hz : (ν - 1) • KTabC.e1P K = 0 := by
        rw [sub_smul, h2, one_smul, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact hν1 (sub_eq_zero.mp h)
      · exact he1ne h
  have hw2 : w * w = 1 := by
    have h := map_mul τ w₀ w₀
    rw [hw₀sq, map_one] at h
    rw [hw]
    exact h.symm
  have hwa : w * a * w⁻¹ = a⁻¹ := by
    have h := congrArg τ hw₀a
    simp only [map_mul, map_inv] at h
    rw [hw, ha]
    exact h
  have hwb : w * b * w⁻¹ = b⁻¹ := by
    have h := congrArg τ hw₀b
    simp only [map_mul, map_inv] at h
    rw [hw, hb]
    exact h
  have hwmove : ℓ.map (w : MulAut W).toMonoidHom ≠ ℓ := by
    intro hwmap
    have hmem : w (e.symm (Multiplicative.ofAdd (KTabC.e1P K))) ∈ ℓ := by
      rw [← hwmap]
      exact Subgroup.mem_map_of_mem _ hxl₀
    obtain ⟨c, hc⟩ := (hfix' _).mp hmem
    have h1 : Multiplicative.toAdd (e (w (e.symm (Multiplicative.ofAdd (KTabC.e1P K))))) =
        (w₀ : Matrix ιP ιP K) *ᵥ KTabC.e1P K := by
      rw [hw, hτcoord, hxcoord]
    exact hw₀e1 c (h1.symm.trans hc)

  have hcoord : ∀ (g : MulAut W) (A : GL ιP K), Φ g = s16gNatHom ιP K A → ∀ x : W,
      Multiplicative.toAdd (e (g x)) = (A : Matrix ιP ιP K) *ᵥ
        Multiplicative.toAdd (e x) := by
    intro g A hgA x
    have hg : τ A = g := by
      show Φ.symm (s16gNatHom ιP K A) = g
      rw [← hgA, MulEquiv.symm_apply_apply]
    have h := hτcoord A x
    rw [hg] at h
    exact h
  have hcomp : (Φ.symm).toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id (MulAut W) :=
    MonoidHom.ext fun x => Φ.symm_apply_apply x
  have hΦτ' : Φ.toMonoidHom.comp τ = s16gNatHom ιP K :=
    MonoidHom.ext fun A => hΦτ A
  have hτdef : τ = (Φ.symm).toMonoidHom.comp (s16gNatHom ιP K) := rfl
  have hTL : Tstar ≤ fixingSubgroup (MulAut W) (ℓ : Set W) := by
    intro t ht
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rw [MulAut.smul_def]
    exact hTfix t ht x hx
  have hS2 : IsPGroup 2 ↥((S : Subgroup ↥H).map H.subtype) := S.isPGroup'.map H.subtype
  have hSmax : ∀ P : Subgroup (MulAut W), P ≤ H → IsPGroup 2 ↥P →
      (S : Subgroup ↥H).map H.subtype ≤ P → P = (S : Subgroup ↥H).map H.subtype := by
    intro P hPH hP2 hSP
    have hP2' : IsPGroup 2 ↥(P.subgroupOf H) := hP2.comap_subtype
    have hle : (S : Subgroup ↥H) ≤ P.subgroupOf H := by
      intro x hx
      exact hSP (Subgroup.mem_map_of_mem H.subtype hx)
    have hSe : P.subgroupOf H = (S : Subgroup ↥H) := S.is_maximal' hP2' hle
    calc P = (P.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hPH).symm
      _ = (S : Subgroup ↥H).map H.subtype := by rw [hSe]
  have hcyc : ∀ B : Subgroup (MulAut W), B ≤ H ⊓ fixingSubgroup (MulAut W) (ℓ : Set W) →
      Odd (Nat.card ↥B) → IsCyclic ↥B := by
    intro B hB hBodd
    have hBH : B ≤ H := fun x hx => (Subgroup.mem_inf.mp (hB hx)).1
    have hBL : B ≤ fixingSubgroup (MulAut W) (ℓ : Set W) :=
      fun x hx => (Subgroup.mem_inf.mp (hB hx)).2
    set B' : Subgroup (GL ιP K) := (B.map Φ.toMonoidHom).comap (s16gNatHom ιP K) with hB'def
    have hBΓ : B.map Φ.toMonoidHom ≤ Γ.map (s16gNatHom ιP K) := by
      calc B.map Φ.toMonoidHom ≤ H.map Φ.toMonoidHom := Subgroup.map_mono hBH
        _ = Γ.map (s16gNatHom ιP K) := hH
    have hB'Γ : B' ≤ Γ := by
      intro A hA
      exact (Subgroup.mem_map_iff_mem s16gNatHom_injective).mp (hBΓ (Subgroup.mem_comap.mp hA))
    have hB'map : B'.map (s16gNatHom ιP K) = B.map Φ.toMonoidHom := by
      refine le_antisymm (Subgroup.map_comap_le _ _) ?_
      intro y hy
      obtain ⟨A, -, hAy⟩ := Subgroup.mem_map.mp (hBΓ hy)
      exact hAy ▸ Subgroup.mem_map_of_mem (s16gNatHom ιP K)
        (Subgroup.mem_comap.mpr (hAy ▸ hy))
    have hcardB1 : Nat.card ↥(B'.map (s16gNatHom ιP K)) = Nat.card ↥B' :=
      Subgroup.card_map_of_injective s16gNatHom_injective
    have hcardB2 : Nat.card ↥(B.map Φ.toMonoidHom) = Nat.card ↥B :=
      Subgroup.card_map_of_injective Φ.injective
    have hBcard : Nat.card ↥B' = Nat.card ↥B := by
      rw [← hcardB1, hB'map, hcardB2]
    have hB'odd : Odd (Nat.card ↥B') := by rw [hBcard]; exact hBodd
    have hB'iso : ∀ A ∈ B', ∀ v : ιP → K,
        StatedQuadPlus 2 K ((A : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v :=
      fun A hA => CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
        (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore _ (hB'Γ hA))
    have hB'fix : ∀ A ∈ B', (A : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K := by
      intro A hA
      obtain ⟨g, hgB, hgA⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hA)
      have hgx : g (e.symm (Multiplicative.ofAdd (KTabC.e1P K))) =
          e.symm (Multiplicative.ofAdd (KTabC.e1P K)) := by
        have h := hBL hgB
        rw [mem_fixingSubgroup_iff] at h
        simpa [MulAut.smul_def] using h _ hxl₀
      have h1 := hcoord g A hgA (e.symm (Multiplicative.ofAdd (KTabC.e1P K)))
      rw [hgx, hxcoord] at h1
      simpa using h1.symm
    have hB'cyc : IsCyclic ↥B' := KTabC.isCyclic_of_odd_of_fix hB'iso hB'odd hB'fix
    have heq : ↥B ≃* ↥B' :=
      (B.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
        ((MulEquiv.subgroupCongr hB'map.symm).trans
          (B'.equivMapOfInjective (s16gNatHom ιP K) s16gNatHom_injective).symm)
    exact (MulEquiv.isCyclic heq).mpr hB'cyc
  have haS : a ∈ Subgroup.normalizer ((S : Subgroup ↥H).map H.subtype : Set (MulAut W)) := by
    set P'' : Subgroup (GL ιP K) :=
      (((S : Subgroup ↥H).map H.subtype).map Φ.toMonoidHom).comap (s16gNatHom ιP K) with hP''def
    have hSΓ : ((S : Subgroup ↥H).map H.subtype).map Φ.toMonoidHom ≤
        Γ.map (s16gNatHom ιP K) := by
      calc ((S : Subgroup ↥H).map H.subtype).map Φ.toMonoidHom ≤ H.map Φ.toMonoidHom :=
            Subgroup.map_mono (Subgroup.map_subtype_le _)
        _ = Γ.map (s16gNatHom ιP K) := hH
    have hP''Γ : P'' ≤ Γ := by
      intro A hA
      exact (Subgroup.mem_map_iff_mem s16gNatHom_injective).mp (hSΓ (Subgroup.mem_comap.mp hA))
    have hP''map : P''.map (s16gNatHom ιP K) =
        ((S : Subgroup ↥H).map H.subtype).map Φ.toMonoidHom := by
      refine le_antisymm (Subgroup.map_comap_le _ _) ?_
      intro y hy
      obtain ⟨A, -, hAy⟩ := Subgroup.mem_map.mp (hSΓ hy)
      exact hAy ▸ Subgroup.mem_map_of_mem (s16gNatHom ιP K)
        (Subgroup.mem_comap.mpr (hAy ▸ hy))
    have hP''2 : IsPGroup 2 ↥P'' := by
      have hS2' : IsPGroup 2 ↥(((S : Subgroup ↥H).map H.subtype).map Φ.toMonoidHom) :=
        hS2.map Φ.toMonoidHom
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2'
      refine IsPGroup.iff_card.mpr ⟨k, ?_⟩
      have hcardP : Nat.card ↥(P''.map (s16gNatHom ιP K)) = Nat.card ↥P'' :=
        Subgroup.card_map_of_injective s16gNatHom_injective
      rw [← hcardP, hP''map]
      exact hk
    have hP''τ : P''.map τ = (S : Subgroup ↥H).map H.subtype := by
      rw [hτdef, ← Subgroup.map_map, hP''map, Subgroup.map_map, hcomp, Subgroup.map_id]
    have hP''max : ∀ P' : Subgroup (GL ιP K), P' ≤ Γ → IsPGroup 2 ↥P' → P'' ≤ P' →
        P' = P'' := by
      intro P' hP'Γ hP'2 hle
      have hP'eH : P'.map τ ≤ H := by
        rintro _ ⟨A, hA, rfl⟩
        exact hτmem A (hP'Γ hA)
      have hP'e2 : IsPGroup 2 ↥(P'.map τ) := hP'2.map τ
      have hSe : (S : Subgroup ↥H).map H.subtype ≤ P'.map τ := by
        rw [← hP''τ]
        exact Subgroup.map_mono hle
      have heq : P'.map τ = (S : Subgroup ↥H).map H.subtype := hSmax _ hP'eH hP'e2 hSe
      have hmap : P'.map (s16gNatHom ιP K) = P''.map (s16gNatHom ιP K) := by
        rw [show P'.map (s16gNatHom ιP K) = P'.map (Φ.toMonoidHom.comp τ) from by
            rw [hΦτ'],
          ← Subgroup.map_map, heq, hP''map]
      exact Subgroup.map_injective s16gNatHom_injective hmap
    have hP''fix : ∀ g ∈ P'', (g : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K := by
      intro g hg
      obtain ⟨g', hg'S, hg'g⟩ := Subgroup.mem_map.mp
        (hP''map ▸ Subgroup.mem_map_of_mem (s16gNatHom ιP K) hg)
      have h1 := hcoord g' g hg'g (e.symm (Multiplicative.ofAdd (KTabC.e1P K)))
      rw [hTfix g' (hST hg'S) _ hxl₀, hxcoord] at h1
      simpa using h1.symm
    have ha₀norm : a₀ ∈ Subgroup.normalizer (P'' : Set (GL ιP K)) :=
      KOm.mem_normalizer_of_fix_e1P hK4 hP''Γ hP''2 hP''max hP''fix ha₀Γ ha₀e1
    have key : ∀ (g : MulAut W) (A : GL ιP K), g = τ A →
        A ∈ Subgroup.normalizer (P'' : Set (GL ιP K)) →
        ∀ z ∈ (S : Subgroup ↥H).map H.subtype, g * z * g⁻¹ ∈ (S : Subgroup ↥H).map H.subtype := by
      intro g A hgA hAnorm z hz
      have hz' : Φ z ∈ P''.map (s16gNatHom ιP K) := by
        rw [hP''map]
        exact Subgroup.mem_map_of_mem Φ.toMonoidHom hz
      obtain ⟨C, hC, hCz⟩ := Subgroup.mem_map.mp hz'
      have hconj : A * C * A⁻¹ ∈ P'' := by
        have h := (Subgroup.mem_normalizer_iff.mp hAnorm C).mp hC
        simpa using h
      have hΦgz : Φ (g * z * g⁻¹) = s16gNatHom ιP K (A * C * A⁻¹) := by
        rw [map_mul, map_mul, map_inv, hgA, hΦτ, ← hCz, map_mul, map_mul, map_inv]
      have hmem : s16gNatHom ιP K (A * C * A⁻¹) ∈ P''.map (s16gNatHom ιP K) :=
        Subgroup.mem_map_of_mem _ hconj
      rw [hP''map, ← hΦgz] at hmem
      exact (Subgroup.mem_map_iff_mem Φ.injective).mp hmem
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact key a a₀ ha.symm ha₀norm z hz
    · intro hz
      have h := key a⁻¹ a₀⁻¹ (by rw [map_inv, ha]) (Subgroup.inv_mem _ ha₀norm) _ hz
      rwa [show a⁻¹ * (a * z * a⁻¹) * (a⁻¹)⁻¹ = z from by group] at h
  have haodd : Odd (orderOf a) := by
    rw [hordA]
    exact hrprime.odd_iff.mpr (by have h := hrprime.two_le; omega)
  have haL : a ∈ fixingSubgroup (MulAut W) (ℓ : Set W) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rw [MulAut.smul_def]
    exact hafix x hx
  have hperm : (Subgroup.zpowers a : Set (MulAut W)) * (Tstar : Set (MulAut W)) =
      (Tstar : Set (MulAut W)) * (Subgroup.zpowers a : Set (MulAut W)) :=
    KOm.zpowers_mul_eq_mul_zpowers (H := H) (S := (S : Subgroup ↥H).map H.subtype)
      (T := Tstar) (L := fixingSubgroup (MulAut W) (ℓ : Set W))
      (Subgroup.map_subtype_le _) hS2 hSmax hTN hT2 hST hTL hcyc haH haL haS haodd
  exact ⟨r, hrprime, hrdvd', a, haH, b, hbH, w, hwH, hordA, hordB, hcomm', hafix, hbmap,
    hbne, hw2, hwa, hwb, hwmove, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
