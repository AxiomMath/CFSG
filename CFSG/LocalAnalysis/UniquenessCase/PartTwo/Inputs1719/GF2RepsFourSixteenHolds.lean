module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourFiveDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixE
import CFSG.Quasithin.Background.RonanE111MemE1
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.Quasithin.Background.F918M0
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourFive
import CFSG.Quasithin.Background.FFC4Tr1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def WkGenSet (k : ℕ) (X : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) :
    Set (Subgroup (MulAut W)) :=
  {U | U ≤ X ∧ ∃ V ∈ Ω, U ≤ V ∧ E3.mQuot V U = k}

theorem Wk_le (k : ℕ) (X : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) :
    Wk k X Ω ≤ X := by
  unfold Wk
  exact iSup_le fun _ => iSup_le fun hUX => iSup_le fun _ => hUX

theorem le_Wk_of {k : ℕ} {X U V : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    (hUX : U ≤ X) (hV : V ∈ Ω) (hUV : U ≤ V) (hm : E3.mQuot V U = k) :
    U ≤ Wk k X Ω := by
  unfold Wk
  exact le_iSup_of_le U (le_iSup_of_le hUX (le_iSup_of_le ⟨V, hV, hUV, hm⟩ le_rfl))

theorem le_Wk_genSet {k : ℕ} {X : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    {U : Subgroup (MulAut W)} (hU : U ∈ WkGenSet k X Ω) : U ≤ Wk k X Ω := by
  obtain ⟨hUX, V, hVΩ, hUV, hm⟩ := hU
  exact le_Wk_of hUX hVΩ hUV hm

theorem Wk_eq_iSup (k : ℕ) (X : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))) :
    Wk k X Ω = ⨆ U ∈ WkGenSet k X Ω, U := by
  apply le_antisymm
  · unfold Wk
    refine iSup_le fun U => iSup_le fun hUX => iSup_le fun h => ?_
    exact le_iSup₂_of_le U ⟨hUX, h⟩ le_rfl
  · exact iSup₂_le fun U hU => le_Wk_genSet hU

theorem Wk_map_conj_le {k : ℕ} {T Y : Subgroup (MulAut W)}
    {Ω : Set (Subgroup (MulAut W))}
    (hTY : T ≤ Y) (hΩ : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    {t : MulAut W} (ht : t ∈ T) :
    (Wk k T Ω).map (MulAut.conj t).toMonoidHom ≤ Wk k T Ω := by
  conv_lhs => rw [Wk_eq_iSup]
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUT, V, hVΩ, hUV, hm⟩ := hU
  have hmapT : U.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro _ ⟨u, hu, rfl⟩
    exact T.mul_mem (T.mul_mem ht (hUT hu)) (T.inv_mem ht)
  exact le_Wk_of hmapT (hΩ V hVΩ t (hTY ht)) (Subgroup.map_mono hUV) (by
    have h := E3.mQuot_conjSubgroup V U t⁻¹
    simpa [conjSubgroup, inv_inv] using h.trans hm)

theorem Wk_map_conj_eq {k : ℕ} {T Y : Subgroup (MulAut W)}
    {Ω : Set (Subgroup (MulAut W))}
    (hTY : T ≤ Y) (hΩ : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    {t : MulAut W} (ht : t ∈ T) :
    (Wk k T Ω).map (MulAut.conj t).toMonoidHom = Wk k T Ω := by
  apply le_antisymm (Wk_map_conj_le hTY hΩ ht)
  intro w hw
  have h1 : (MulAut.conj t⁻¹) w ∈ Wk k T Ω :=
    Wk_map_conj_le (t := t⁻¹) hTY hΩ (T.inv_mem ht) (Subgroup.mem_map_of_mem _ hw)
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj t⁻¹) w, h1, ?_⟩
  ext v
  simp [MulAut.conj_apply, mul_assoc]

@[expose] def corankSet (Ω : Set (Subgroup (MulAut W))) (j : ℕ) :
    Set (Subgroup (MulAut W)) :=
  {B | ∃ A ∈ Ω, B ≤ A ∧ E3.mQuot A B = j}

theorem corankSet_subset_aSet {Y : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    {k j : ℕ} (hΩ : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) (hj : j ≤ k) :
    corankSet Ω j ⊆ E3.aSet (k + 1 - j) Y := by
  rintro B ⟨A, hAΩ, hBA, hm⟩
  have hA := hΩ A hAΩ
  have hAelem : IsElemAbelian2 A := hA.2.2.1
  have hfix := hA.2.2.2
  have hrank : k + 1 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot] at hm
    omega
  have hBelem : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAelem.1 a (hBA ha) b (hBA hb),
      fun a ha => hAelem.2 a (hBA ha)⟩
  refine ⟨hBA.trans hA.1, hBne, hBelem, ?_⟩
  intro B' hB'B hmB'
  have hadd := E3.mQuot_add (V := A) hB'B hBA
  have hlt : E3.mQuot A B' < k + 1 := by
    rw [hadd]
    omega
  have hlt' : E3.mQuot A B < k + 1 := by omega
  rw [hfix B' (hB'B.trans hBA) hlt, hfix B hBA hlt']

theorem corankSet_conj {Y : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))} {j : ℕ}
    (hΩ : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    {B : Subgroup (MulAut W)} (hB : B ∈ corankSet Ω j)
    {g : MulAut W} (hg : g ∈ Y) :
    B.map (MulAut.conj g).toMonoidHom ∈ corankSet Ω j := by
  obtain ⟨A, hAΩ, hBA, hm⟩ := hB
  refine ⟨A.map (MulAut.conj g).toMonoidHom, hΩ A hAΩ g hg, Subgroup.map_mono hBA, ?_⟩
  have h := E3.mQuot_conjSubgroup A B g⁻¹
  simpa [conjSubgroup, inv_inv] using h.trans hm

theorem Wk_mono {k j j' : ℕ} {Y T : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    (hΩ : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) (hjj' : j ≤ j') (hj'k : j' ≤ k) :
    Wk j T Ω ≤ Wk j' T Ω := by
  conv_lhs => rw [Wk_eq_iSup]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUT, V, hVΩ, hUV, hmVU⟩ := hU
  have hV := hΩ V hVΩ
  have hUab : IsElemAbelian2 U :=
    ⟨fun a ha b hb => hV.2.2.1.1 a (hUV ha) b (hUV hb),
      fun a ha => hV.2.2.1.2 a (hUV ha)⟩
  have hrank : k + 1 ≤ E3.mQuot V ⊥ := E3.le_mQuot_bot_of_mem_aSet hV
  have hadd := E3.mQuot_add (V := V) (U := ⊥) (U' := U) bot_le hUV
  have hb : k + 1 ≤ E3.mQuot U ⊥ + j := by
    have h1 : E3.mQuot V ⊥ = E3.mQuot U ⊥ + j := by rw [hadd, hmVU]
    rwa [h1] at hrank
  have hc : j' - j < rk ↥U := by
    rw [← H.mQuot_bot_eq_rk U]
    omega
  intro u hu
  obtain ⟨D, hDU, huD, hmD⟩ := E3.exists_mem_le_mQuot_eq (H.isElemAbelian2_iff.mp hUab) hc hu
  have hmVD : E3.mQuot V D = j' := by
    have h1 := E3.mQuot_add hDU hUV
    rw [hmD, hmVU] at h1
    rw [h1]
    omega
  exact le_Wk_genSet ⟨hDU.trans hUT, V, hVΩ, hDU.trans hUV, hmVD⟩ huD

theorem Wk_shift {i j : ℕ} {T : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))} :
    Wk i T (corankSet Ω j) ≤ Wk (j + i) T Ω := by
  rw [Wk_eq_iSup]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUT, B, hB, hUB, hmB⟩ := hU
  obtain ⟨A, hAΩ, hBA, hmAB⟩ := hB
  have hm : E3.mQuot A U = j + i := by
    have h1 := E3.mQuot_add hUB hBA
    rw [hmB, hmAB] at h1
    rw [h1]
    omega
  exact le_Wk_of hUT hAΩ (hUB.trans hBA) hm

theorem Wk_ne_bot {k j : ℕ} {Y T : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    (hTY : T ≤ Y) (hsyl : IsSylowIn 2 T Y) (hΩne : Ω.Nonempty)
    (hΩinv : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hΩa : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) (hj : j ≤ k) :
    Wk j T Ω ≠ ⊥ := by
  obtain ⟨A, hAΩ⟩ := hΩne
  have hA := hΩa A hAΩ
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  obtain ⟨g, hgY, hgA⟩ := exists_conj_le_of_quasithin_isSylowIn hsyl hA.1 hA2
  have hBΩ : A.map (MulAut.conj g).toMonoidHom ∈ Ω := hΩinv A hAΩ g hgY
  have hrank : k + 1 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  obtain ⟨b, hbne⟩ := ne_bot_iff_exists_ne_one.mp hA.2.1
  have hc : j < rk ↥A := by
    rw [← H.mQuot_bot_eq_rk A]
    omega
  obtain ⟨D, hDA, hbD, hmD⟩ := E3.exists_mem_le_mQuot_eq (H.isElemAbelian2_iff.mp hA.2.2.1) hc b.2
  have hDne : D ≠ ⊥ := by
    intro h
    exact hbne (Subtype.ext (Subgroup.mem_bot.mp (h ▸ hbD)))
  have hD'le : D.map (MulAut.conj g).toMonoidHom ≤ Wk j T Ω := by
    refine le_Wk_of (Subgroup.map_mono hDA |>.trans hgA) hBΩ
      (Subgroup.map_mono hDA) ?_
    have h := E3.mQuot_conjSubgroup A D g⁻¹
    simpa [conjSubgroup, inv_inv] using h.trans hmD
  have hD'ne : D.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hDne ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) D
      (MulAut.conj g).injective).mp hbot)
  intro hbot
  exact hD'ne (le_bot_iff.mp (hbot ▸ hD'le))

theorem fIndexSum_subset_le {G : Type} [Group G] [Finite G]
    {Γ Δ : Set (Subgroup G)} (h : Γ ⊆ Δ) (hfin : Δ.Finite) :
    fIndexSum Γ ≤ fIndexSum Δ := by
  rw [fIndexSum, fIndexSum, finsum_mem_eq_finite_toFinset_sum fIndex (hfin.subset h),
    finsum_mem_eq_finite_toFinset_sum fIndex hfin]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact h hx
  · intro x _ _
    exact zero_le

theorem fIndexSum_le_of_mem {G : Type} [Group G] [Finite G]
    {Δ : Set (Subgroup G)} (hfin : Δ.Finite) {H : Subgroup G} (hH : H ∈ Δ) :
    fIndex H ≤ fIndexSum Δ := by
  have h1 : fIndexSum ({H} : Set (Subgroup G)) ≤ fIndexSum Δ :=
    fIndexSum_subset_le (by intro x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ hH) hfin
  rwa [fIndexSum, finsum_mem_singleton] at h1

theorem fIndexSum_insert_of_not_mem {G : Type} [Group G] {Γ : Set (Subgroup G)}
    {H : Subgroup G} (hH : H ∉ Γ) (hfin : Γ.Finite) :
    fIndexSum (insert H Γ) = fIndex H + fIndexSum Γ := by
  unfold fIndexSum
  rw [finsum_mem_insert fIndex hH hfin]

theorem fIndex_ne_top_of_mem {G : Type} [Group G] [Finite G]
    {Δ : Set (Subgroup G)} {k : ℕ} (hfin : Δ.Finite) (hk : fIndexSum Δ = (k : ℕ∞))
    {H : Subgroup G} (hH : H ∈ Δ) : fIndex H ≠ ⊤ := by
  have hle : fIndex H ≤ fIndexSum Δ := fIndexSum_le_of_mem hfin hH
  rw [hk] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top k) hle

theorem add_toNat_fIndex_le {G : Type} [Group G] [Finite G] {Γ Δ : Set (Subgroup G)}
    {H : Subgroup G} {j k : ℕ} (hΓΔ : Γ ⊆ Δ) (hΔfin : Δ.Finite)
    (hΓsum : fIndexSum Γ = (j : ℕ∞)) (hkSum : fIndexSum Δ = (k : ℕ∞))
    (hHΔ : H ∈ Δ) (hHΓ : H ∉ Γ) :
    (fIndexSum (insert H Γ)).toNat = j + (fIndex H).toNat ∧
      j + (fIndex H).toNat ≤ k := by
  have hHfin : fIndex H ≠ ⊤ := fIndex_ne_top_of_mem hΔfin hkSum hHΔ
  have hi : fIndex H = ((fIndex H).toNat : ℕ∞) := (ENat.coe_toNat hHfin).symm
  have hins : fIndexSum (insert H Γ) = fIndex H + fIndexSum Γ :=
    fIndexSum_insert_of_not_mem hHΓ (hΔfin.subset hΓΔ)
  have hsub : insert H Γ ⊆ Δ := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact hHΔ
    · exact hΓΔ hX
  have hle : fIndexSum (insert H Γ) ≤ (k : ℕ∞) := by
    rw [← hkSum]
    exact fIndexSum_subset_le hsub hΔfin
  have h1 : ((fIndex H).toNat : ℕ∞) + (j : ℕ∞) ≤ (k : ℕ∞) := by
    rw [← hi, ← hΓsum, ← hins]
    exact hle
  have h2 : (fIndex H).toNat + j ≤ k := by
    have h3 : (((fIndex H).toNat + j : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
      simpa only [Nat.cast_add] using h1
    exact ENat.coe_le_coe.mp h3
  have hid : fIndexSum (insert H Γ) = ((j + (fIndex H).toNat : ℕ) : ℕ∞) := by
    rw [hins, hi, hΓsum, Nat.cast_add]
    exact add_comm _ _
  exact ⟨by rw [hid]; exact ENat.toNat_coe _, by omega⟩

theorem w4Lem4_16_case_one {Y L T : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))}
    {Δ Γ : Set (Subgroup (MulAut W))} {k j : ℕ}
    (hTY : T ≤ Y) (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y)
    (hΔT : ∀ H ∈ Δ, H ≤ Y ∧ T ≤ H) (hgen : ⨆ H ∈ Δ, H = Y)
    (hP : ∀ H ∈ Γ, commSub (fixV (Wk j T Ω)) (twoResidual H) = ⊥)
    (hcase : ∀ H ∈ Δ, H ∉ Γ → H ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)))
    (hΩinv : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hΩne : Ω.Nonempty) (hΩa : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) (hjk : j ≤ k) :
    commSub (fixV (Wk j T Ω)) L = ⊥ := by
  classical
  have hWkT : Wk j T Ω ≤ T := Wk_le j T Ω
  have hWkY : Wk j T Ω ≤ Y := hWkT.trans hTY
  have hTnorm : T ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht w hw
    exact Wk_map_conj_le hTY hΩinv ht (Subgroup.mem_map_of_mem _ hw)
  have hTstab : T ≤ stabSub (fixV (Wk j T Ω)) := by
    intro t ht
    rw [mem_stabSub_iff_map_eq]
    have h' := fixV_map_conj_eq (Wk j T Ω) t
    rw [Wk_map_conj_eq hTY hΩinv ht] at h'
    exact h'.symm
  have hCentSub : ∀ H ∈ Γ, twoResidual H ≤ centSub (fixV (Wk j T Ω)) := by
    intro H hH
    have h := (commSub_eq_bot_iff).mp (hP H hH)
    exact fun x hx => mem_centSub.mpr fun v hv => mem_fixV.mp (h hv) x hx
  have hΔstab : ∀ H ∈ Δ, H ≤ stabSub (fixV (Wk j T Ω)) := by
    intro H hHΔ
    by_cases hHΓ : H ∈ Γ
    · have hTH : T ≤ H := (hΔT H hHΔ).2
      have hHY : H ≤ Y := (hΔT H hHΔ).1
      have hTsylH : IsSylowIn 2 T H := by
        refine ⟨hTH, hsyl.isPGroup, fun hd => hsyl.not_dvd_relIndex ?_⟩
        exact hd.trans ⟨H.relIndex Y, (Subgroup.relIndex_mul_relIndex T H Y hTH hHY).symm⟩
      have hsup : T ⊔ twoResidual H = H :=
        sup_twoResidual_eq (E1.isSylowIn_two_iff.mp hTsylH)
      rw [← hsup]
      exact sup_le hTstab ((hCentSub H hHΓ).trans (centSub_le_stabSub _))
    · intro h hh
      rw [mem_stabSub_iff_map_eq]
      have hWh : (Wk j T Ω).map (MulAut.conj h).toMonoidHom = Wk j T Ω :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hcase H hHΔ hHΓ hh)
      have h' := fixV_map_conj_eq (Wk j T Ω) h
      rw [hWh] at h'
      exact h'.symm
  have hYstab : Y ≤ stabSub (fixV (Wk j T Ω)) := by
    rw [← hgen]
    exact iSup₂_le fun H hH => hΔstab H hH
  set F : Subgroup W := fixV (Wk j T Ω) with hF
  set N₀ : Subgroup (MulAut W) := Y ⊓ centSub F with hN₀
  have hN₀le : N₀ ≤ Y := by rw [hN₀]; exact inf_le_left
  have hN₀sub : (N₀.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN₀le, Subgroup.le_normalizer_iff]
    intro y hy c hc
    refine ⟨Y.mul_mem (Y.mul_mem hy hc.1) (Y.inv_mem hy), ?_⟩
    exact CFSG.Quasithin.conj_mem_centSub (hYstab hy) hc.2
  have hcompA : CFSG.Assembly.IsComponentOf L Y :=
    (CFSG.Assembly.isComponentOf_iff_open (L := L) (K := Y)).mpr hcomp
  have hNsubA : CFSG.Assembly.IsSubnormal N₀ Y :=
    CFSG.Assembly.IsSubnormal.step hN₀le hN₀sub (CFSG.Assembly.IsSubnormal.refl Y)
  rcases CFSG.StandardType.isComponentOf_le_or_commutator_eq_bot hcompA hNsubA with
    hLle | hcomm
  · rw [commSub_eq_bot_iff]
    intro v hv l hl
    exact mem_centSub.mp (hLle hl).2 v hv
  · exfalso
    have hWleN : Wk j T Ω ≤ N₀ := by
      rw [hN₀]
      refine le_inf hWkY ?_
      exact fun w hw => mem_centSub.mpr fun v hv => mem_fixV.mp hv w hw
    have hLcent : L ≤ Subgroup.centralizer (Wk j T Ω : Set (MulAut W)) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans ?_
      exact Subgroup.centralizer_le (by intro x hx; exact hWleN hx)
    have hLnorm : L ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)) := by
      rw [Subgroup.le_normalizer_iff]
      intro l hl w hw
      have hcw : l * w = w * l :=
        ((Subgroup.mem_centralizer_iff.mp (hLcent hl)) w hw).symm
      have heq : l * w * l⁻¹ = w := by
        rw [hcw]
        simp
      rwa [heq]
    have hYnorm : Y ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)) := by
      rw [← hLT]
      exact sup_le hLnorm hTnorm
    have hWnormal : ((Wk j T Ω).subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWkY).mpr hYnorm
    have hW2 : IsPGroup 2 (Wk j T Ω) := hsyl.isPGroup.to_le hWkT
    exact Wk_ne_bot hTY hsyl hΩne hΩinv hΩa hjk (hO2 _ hWkY hWnormal hW2)

theorem w4Lem4_16_case_two_core (h45 : W4Lem4_5K)
    {Y T : Subgroup (MulAut W)} {Ω Δ Γ : Set (Subgroup (MulAut W))} {k j : ℕ}
    (hw : ∀ w : W, w ^ 2 = 1) (hTY : T ≤ Y) (hsyl : IsSylowIn 2 T Y)
    (hΔT : ∀ H ∈ Δ, H ≤ Y ∧ T ≤ H)
    (hΩinv : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hΩa : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y)
    (hΓΔ : Γ ⊆ Δ) (hΓsum : fIndexSum Γ = (j : ℕ∞))
    (hP : ∀ H' ∈ Γ, commSub (fixV (Wk j T Ω)) (twoResidual H') = ⊥)
    {H : Subgroup (MulAut W)} (hHΔ : H ∈ Δ) (hHΓ : H ∉ Γ)
    (hHnot : ¬ H ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)))
    (hΔfin : Δ.Finite) (hkSum : fIndexSum Δ = (k : ℕ∞)) :
    twoResidual H ≤ centSub (fixV (Wk (j + (fIndex H).toNat) T Ω)) := by
  classical
  set i : ℕ := (fIndex H).toNat with hi
  have hHfin : fIndex H ≠ ⊤ := fIndex_ne_top_of_mem hΔfin hkSum hHΔ
  have hInFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq i H := by
    rw [hi]; exact inFSq_toNat_fIndex hHfin
  have hji_le : j + i ≤ k := by
    rw [hi]
    exact (add_toNat_fIndex_le hΓΔ hΔfin hΓsum hkSum hHΔ hHΓ).2
  have hjk : j ≤ k := by omega
  have hTH : T ≤ H := (hΔT H hHΔ).2
  have hHY : H ≤ Y := (hΔT H hHΔ).1
  have hTsylH : IsSylowIn 2 T H := by
    refine ⟨hTH, hsyl.isPGroup, fun hd => hsyl.not_dvd_relIndex ?_⟩
    exact hd.trans ⟨H.relIndex Y, (Subgroup.relIndex_mul_relIndex T H Y hTH hHY).symm⟩
  set Ω'' : Set (Subgroup (MulAut W)) := {B | B ∈ corankSet Ω j ∧ B ≤ H} with hΩ''
  have hΩ''inv : E1.IsInvColl H Ω'' := by
    refine ⟨fun B hB => hB.2, ?_, ?_⟩
    · intro B hB
      exact CFSG.Quasithin.H.isElemAbelian2_iff.mp (((corankSet_subset_aSet hΩa hjk) hB.1).2.2.1)
    · intro B hB h hh
      refine ⟨?_, ?_⟩
      · exact corankSet_conj hΩinv hB.1 (hHY hh)
      · rintro x ⟨b, hb, rfl⟩
        exact H.mul_mem (H.mul_mem hh (hB.2 hb)) (H.inv_mem hh)
  have hO2T : pCoreOf 2 H ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsylH
  have hPnorm : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set (MulAut W)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hex : ∃ A ∈ Ω'', ¬ A ≤ pCoreOf 2 H := by
    by_contra hall
    push Not at hall
    apply hHnot
    rw [Subgroup.le_normalizer_iff]
    intro h hh w hw
    have hWle : Wk j T Ω ≤
        Subgroup.comap (MulAut.conj h).toMonoidHom (Wk j T Ω) := by
      rw [← Subgroup.map_le_iff_le_comap]
      conv_lhs => rw [Wk_eq_iSup]
      simp only [Subgroup.map_iSup]
      refine iSup₂_le fun U hU => ?_
      obtain ⟨hUT, V, hVΩ, hUV, hm⟩ := hU
      have hUcor : U ∈ corankSet Ω j := ⟨V, hVΩ, hUV, hm⟩
      have hUΩ'' : U ∈ Ω'' := ⟨hUcor, hUT.trans hTH⟩
      have hUO : U ≤ pCoreOf 2 H := hall U hUΩ''
      have hmapT : U.map (MulAut.conj h).toMonoidHom ≤ T := by
        rintro _ ⟨u, hu, rfl⟩
        exact hO2T ((Subgroup.le_normalizer_iff.mp hPnorm) h hh u (hUO hu))
      exact le_Wk_of hmapT (hΩinv V hVΩ h (hHY hh)) (Subgroup.map_mono hUV) (by
        have hq := E3.mQuot_conjSubgroup V U h⁻¹
        simpa [conjSubgroup, inv_inv] using hq.trans hm)
    rw [← Subgroup.map_le_iff_le_comap] at hWle
    exact hWle (Subgroup.mem_map_of_mem _ hw)
  generalize hF0 : fixV (Wk (j + i) T Ω) = F
  have hF : F = fixV (Wk (j + i) T Ω) := hF0.symm
  generalize hM₀0 : centSub F ⊔ T = M₀
  have hM₀ : M₀ = centSub F ⊔ T := hM₀0.symm
  have hTM₀ : T ≤ M₀ := by rw [hM₀]; exact le_sup_right
  have hHM : H ≤ M₀ := by
    by_contra hHnotM
    obtain ⟨A, hAΩ'', hAT, K, hKE, hKnot⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSix.exists_isE_not_le_of_inFSq
        (j := i) hTsylH hInFSq hTM₀ hHnotM hΩ''inv hex
    have hΩ''a : ∀ B ∈ Ω'', B ∈ E3.aSet (i + 1) Y := by
      intro B hB
      have h1 : B ∈ E3.aSet (k + 1 - j) Y := (corankSet_subset_aSet hΩa hjk) hB.1
      exact E3.aSet_anti (by omega) Y h1
    have hΩjinv : ∀ B ∈ corankSet Ω j, ∀ g ∈ Y,
        B.map (MulAut.conj g).toMonoidHom ∈ corankSet Ω j :=
      fun B hB g hg => corankSet_conj hΩinv hB hg
    have hΩja : ∀ B ∈ corankSet Ω j, B ∈ E3.aSet (i + 1) Y := by
      intro B hB
      exact E3.aSet_anti (by omega) Y ((corankSet_subset_aSet hΩa hjk) hB)
    have h45' := h45 W hw Y H T A K (corankSet Ω j) i hHY hTsylH hΩjinv hΩja
      hAΩ''.1 hAT hKE
    have hFle : F ≤ fixV (Wk i T (corankSet Ω j)) := by
      rw [hF]
      exact B1.fixV_le_fixV Wk_shift
    have hO2K : twoResidual K ≤ centSub F := by
      have h1 : fixV (Wk i T (corankSet Ω j)) ≤ fixV (twoResidual K) :=
        (commSub_eq_bot_iff).mp h45'
      exact fun x hx => mem_centSub.mpr fun v hv => mem_fixV.mp (h1 (hFle hv)) x hx
    have hKle : K ≤ M₀ := by
      have hsylK : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K := hKE.2.2.1
      have hsup : (T ⊓ K) ⊔ twoResidual K = K := sup_twoResidual_eq hsylK
      rw [← hsup, hM₀]
      exact sup_le (inf_le_left.trans le_sup_right) (hO2K.trans le_sup_left)
    exact hKnot hKle
  have hFmap : ∀ t ∈ T, F.map t.toMonoidHom = F := by
    intro t ht
    rw [hF]
    have h' := fixV_map_conj_eq (Wk (j + i) T Ω) t
    rw [Wk_map_conj_eq hTY hΩinv ht] at h'
    exact h'.symm
  have hTnormF : T ≤ Subgroup.normalizer (centSub F : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht
    have hstab : t ∈ stabSub F := (mem_stabSub_iff_map_eq (g := t) (J := F)).mpr (hFmap t ht)
    intro c hc
    exact CFSG.Quasithin.conj_mem_centSub hstab hc
  have hO2H : twoResidual H ≤ centSub F :=
    RonanE111.twoResidual_le_of_le_sup_two hTnormF hsyl.isPGroup (by simpa [hM₀] using hHM)
  exact hF.symm ▸ hO2H

theorem w4Lem4_16_case_two (h45 : W4Lem4_5K)
    {Y T : Subgroup (MulAut W)} {Ω Δ Γ : Set (Subgroup (MulAut W))} {k j : ℕ}
    (hw : ∀ w : W, w ^ 2 = 1) (hTY : T ≤ Y) (hsyl : IsSylowIn 2 T Y)
    (hΔT : ∀ H ∈ Δ, H ≤ Y ∧ T ≤ H)
    (hΩinv : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hΩa : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y)
    (hΓΔ : Γ ⊆ Δ) (hΓsum : fIndexSum Γ = (j : ℕ∞))
    (hP : ∀ H' ∈ Γ, commSub (fixV (Wk j T Ω)) (twoResidual H') = ⊥)
    {H : Subgroup (MulAut W)} (hHΔ : H ∈ Δ) (hHΓ : H ∉ Γ)
    (hHnot : ¬ H ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W)))
    (hΔfin : Δ.Finite) (hkSum : fIndexSum Δ = (k : ℕ∞)) :
    (∀ H' ∈ Γ, commSub (fixV (Wk (j + (fIndex H).toNat) T Ω)) (twoResidual H') = ⊥) ∧
      commSub (fixV (Wk (j + (fIndex H).toNat) T Ω)) (twoResidual H) = ⊥ := by
  have hO2H := w4Lem4_16_case_two_core h45 hw hTY hsyl hΔT hΩinv hΩa hΓΔ hΓsum hP hHΔ hHΓ
    hHnot hΔfin hkSum
  have hji_le : j + (fIndex H).toNat ≤ k :=
    (add_toNat_fIndex_le hΓΔ hΔfin hΓsum hkSum hHΔ hHΓ).2
  refine ⟨?_, ?_⟩
  · intro H' hH'
    have hle : Wk j T Ω ≤ Wk (j + (fIndex H).toNat) T Ω :=
      Wk_mono hΩa (Nat.le_add_right j _) hji_le
    have hfix : fixV (Wk (j + (fIndex H).toNat) T Ω) ≤ fixV (Wk j T Ω) :=
      B1.fixV_le_fixV hle
    have hmono : commSub (fixV (Wk (j + (fIndex H).toNat) T Ω)) (twoResidual H') ≤
        commSub (fixV (Wk j T Ω)) (twoResidual H') := commSub_mono hfix le_rfl
    rw [hP H' hH'] at hmono
    exact le_bot_iff.mp hmono
  · rw [commSub_eq_bot_iff]
    intro v hv x hx
    exact mem_centSub.mp (hO2H hx) v hv

theorem w4Lem4_16_part_one (h45 : W4Lem4_5K) (hw : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {Δ : Set (Subgroup (MulAut W))} {k : ℕ}
    (hTY : T ≤ Y) (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y)
    (hΔfin : Δ.Finite) (hΔT : ∀ H ∈ Δ, H ≤ Y ∧ T ≤ H)
    (hgen : ⨆ H ∈ Δ, H = Y) (hkSum : fIndexSum Δ = (k : ℕ∞))
    {Ω : Set (Subgroup (MulAut W))} (hΩne : Ω.Nonempty)
    (hΩinv : ∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hΩa : ∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) :
    commSub (fixV (Wk k T Ω)) L = ⊥ := by
  classical
  let P : Set (Subgroup (MulAut W)) → Prop := fun Γ =>
    ∀ H ∈ Γ, commSub (fixV (Wk (fIndexSum Γ).toNat T Ω)) (twoResidual H) = ⊥
  let C : Finset (Finset (Subgroup (MulAut W))) :=
    hΔfin.toFinset.powerset.filter
      (fun s : Finset (Subgroup (MulAut W)) => P (s : Set (Subgroup (MulAut W))))
  have hCne : C.Nonempty := by
    refine ⟨∅, ?_⟩
    show (∅ : Finset (Subgroup (MulAut W))) ∈
      hΔfin.toFinset.powerset.filter
        (fun s : Finset (Subgroup (MulAut W)) => P (s : Set (Subgroup (MulAut W))))
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by intro H hH; simp at hH⟩
  obtain ⟨s, hsC, hsmax⟩ := Finset.exists_max_image C Finset.card hCne
  have hsSub : (↑s : Set (Subgroup (MulAut W))) ⊆ Δ := by
    have h1 := (Finset.mem_filter.mp hsC).1
    rw [Finset.mem_powerset] at h1
    intro H hH
    have h2 : H ∈ hΔfin.toFinset := h1 (by simpa using hH)
    rwa [Set.Finite.mem_toFinset] at h2
  have hsP : P (↑s) := (Finset.mem_filter.mp hsC).2
  set Γ : Set (Subgroup (MulAut W)) := ↑s with hΓ
  let j : ℕ := (fIndexSum Γ).toNat
  have hjle : fIndexSum Γ ≤ (k : ℕ∞) := by
    rw [← hkSum]
    exact fIndexSum_subset_le hsSub hΔfin
  have hjtop : fIndexSum Γ ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top k) hjle
  have hjcoo : fIndexSum Γ = (j : ℕ∞) := (ENat.coe_toNat hjtop).symm
  have hjk : j ≤ k := by
    have h1 : ((j : ℕ∞)) ≤ (k : ℕ∞) := hjcoo ▸ hjle
    exact ENat.coe_le_coe.mp h1
  by_contra hne
  by_cases hcase : ∀ H ∈ Δ, H ∉ Γ →
      H ≤ Subgroup.normalizer (Wk j T Ω : Set (MulAut W))
  · have h1 : commSub (fixV (Wk j T Ω)) L = ⊥ :=
      w4Lem4_16_case_one hTY hLT hcomp hsyl hO2 hΔT hgen hsP hcase hΩinv hΩne hΩa hjk
    have hle : Wk j T Ω ≤ Wk k T Ω := Wk_mono hΩa hjk le_rfl
    have hfixle : fixV (Wk k T Ω) ≤ fixV (Wk j T Ω) := B1.fixV_le_fixV hle
    have hmono : commSub (fixV (Wk k T Ω)) L ≤ commSub (fixV (Wk j T Ω)) L :=
      commSub_mono hfixle le_rfl
    rw [h1] at hmono
    exact hne (le_bot_iff.mp hmono)
  · push Not at hcase
    obtain ⟨H, hHΔ, hHΓ, hHnot⟩ := hcase
    have hres := w4Lem4_16_case_two h45 hw hTY hsyl hΔT hΩinv hΩa hsSub hjcoo hsP hHΔ hHΓ hHnot
      hΔfin hkSum
    have hins_toNat : (fIndexSum (insert H Γ)).toNat = j + (fIndex H).toNat :=
      (add_toNat_fIndex_le hsSub hΔfin hjcoo hkSum hHΔ hHΓ).1
    have hPθ : P (insert H Γ) := by
      intro H' hH'
      rw [hins_toNat]
      rcases Set.mem_insert_iff.mp hH' with rfl | hH'Γ
      · exact hres.2
      · exact hres.1 H' hH'Γ
    have hθC : insert H s ∈ C := by
      show insert H s ∈ hΔfin.toFinset.powerset.filter
        (fun t : Finset (Subgroup (MulAut W)) => P (t : Set (Subgroup (MulAut W))))
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Set.Finite.mem_toFinset]
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hHΔ
        · exact hsSub (Finset.mem_coe.mpr hx)
      · rw [Finset.coe_insert]
        simpa [hΓ] using hPθ
    have hHs : H ∉ s := by
      intro hmem
      exact hHΓ (by rw [hΓ]; exact Finset.mem_coe.mpr hmem)
    have hmax := hsmax (insert H s) hθC
    rw [Finset.card_insert_of_notMem hHs] at hmax
    omega

theorem aParam_le_of_part_one {Y L T : Subgroup (MulAut W)} {k : ℕ}
    (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (h1 : ∀ Ω : Set (Subgroup (MulAut W)), Ω.Nonempty →
      (∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω) →
      (∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) →
      commSub (fixV (Wk k T Ω)) L = ⊥)
    (hfix : fixV T ≠ fixV Y) : E3.aParam Y ≤ k := by
  classical
  by_cases hempty : E3.aSet (k + 1) Y = ∅
  · apply RonanE42.aParam_le_of_aSet_empty
    intro A hA
    rw [hempty] at hA
    exact hA
  · have hne : (E3.aSet (k + 1) Y).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    have hinv : ∀ A ∈ E3.aSet (k + 1) Y, ∀ g ∈ Y,
        A.map (MulAut.conj g).toMonoidHom ∈ E3.aSet (k + 1) Y := by
      intro A hA g hg
      have hX : conjAutSub g A ∈ E3.aSet (k + 1) (conjAutSub g Y) := aSet_conjAutSub hA
      have hYeq : conjAutSub g Y = Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
      rw [hYeq] at hX
      simpa [conjAutSub] using hX
    have hcomm := h1 (E3.aSet (k + 1) Y) hne hinv (fun A hA => hA)
    set F : Subgroup W := fixV (Wk k T (E3.aSet (k + 1) Y)) with hF
    have hF' : fixV T ≤ F := by
      rw [hF]
      exact B1.fixV_le_fixV (Wk_le k T _)
    have hLcent : L ≤ centSub F := by
      have h := (commSub_eq_bot_iff).mp hcomm
      exact fun l hl => mem_centSub.mpr fun v hv => mem_fixV.mp (h hv) l hl
    have hle : fixV T ≤ fixV Y := by
      rw [← hLT, FFC.fixV_sup]
      refine le_inf ?_ le_rfl
      intro v hv l hl
      exact mem_centSub.mp (hLcent hl) v (hF' hv)
    exact absurd (le_antisymm hle (B1.fixV_le_fixV hTY)) hfix

end

theorem w4Lem4_16_of_w4Lem4_5K (h45 : W4Lem4_5K) : W4Lem4_16 := by
  intro W _ _ hw Y L T Δ k hLY hTY hLT hcomp hsyl hO2 hΔfin hΔT hgen hkSum
  classical
  have hpart : ∀ (Ω : Set (Subgroup (MulAut W))), Ω.Nonempty →
      (∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω) →
      (∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) →
      commSub (fixV (Wk k T Ω)) L = ⊥ := by
    intro Ω hΩne hΩinv hΩa
    exact w4Lem4_16_part_one (Ω := Ω) h45 hw hTY hLT hcomp hsyl hO2 hΔfin hΔT hgen hkSum
      hΩne hΩinv hΩa
  refine ⟨?_, ?_⟩
  · intro Ω hΩne hΩinv hΩa
    exact hpart Ω hΩne hΩinv hΩa
  · intro hfix
    exact aParam_le_of_part_one hTY hLT hpart hfix

theorem w4Lem4_16_holds : W4Lem4_16 := w4Lem4_16_of_w4Lem4_5K w4Lem4_5K_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719