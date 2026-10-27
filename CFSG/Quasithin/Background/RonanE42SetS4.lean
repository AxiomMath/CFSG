module
public import CFSG.Quasithin.Background.RonanE42SetS3
public section
namespace CFSG.Quasithin.RonanE42.Gen
open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
variable {G : Type} [Group G] [Finite G]

open Classical in
theorem exists_level_of_lt (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v)
    (κ : ℕ) (hκ : (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) = κ)
    (hbig : ¬ aParam ρ.range ≤ κ) :
    ∃ c ≤ κ, (∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      (∀ H ∈ Δ, H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
        H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      ∃ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∧
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) := by
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin] at hκ
  set Ω : Set (Subgroup G) := {A | Om ρ (κ + 1) A} with hΩ
  obtain ⟨A', hA'⟩ : ∃ A', A' ∈ aSet (κ + 1) ρ.range := by
    by_contra h
    push Not at h
    exact hbig (aParam_le_of_aSet_empty _ _ h)
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hΩc : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω := fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  let spl : Subgroup G → Prop := fun H =>
    H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  let piece : Subgroup G → Subgroup G := fun H => if spl H then H else xt T H
  let bad : Subgroup G → Finset ℕ := fun H =>
    (Finset.range (κ + 1)).filter (fun c => ¬ piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
  have hbad : ∀ H ∈ Δf, (bad H).card ≤ iRank H := by
    intro H hH
    obtain ⟨hTH, hF⟩ := hΔT H ((hmemΔ H).1 hH)
    by_cases hspl : spl H
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_pos hspl]
      rw [this]
      exact card_bad_le_of_split hΩc hel hfx hT hTH hF hspl
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_neg hspl]
      rw [this]
      exact card_bad_xt_le hΩc hel hfx hT hTH hF
  have hcard : (Δf.biUnion bad).card < (Finset.range (κ + 1)).card := by
    have h2 : (Δf.biUnion bad).card ≤ κ :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum hbad).trans hκ.le)
    rw [Finset.card_range]
    omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hc)
  have hmem : ∀ H ∈ Δ, piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hHΔ
    by_contra hn
    exact hcn (Finset.mem_biUnion.2 ⟨H, (hmemΔ H).2 hHΔ, Finset.mem_filter.2 ⟨hc, hn⟩⟩)
  have hsplit : ∀ H ∈ Δ, spl H → H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun H hH hs => by
    simpa only [piece, if_pos hs] using hmem H hH
  have hxt : ∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hH
    by_cases hs : spl H
    · exact (sup_le (Subgroup.map_subtype_le _) (hΔT H hH).1).trans (hsplit H hH hs)
    · simpa only [piece, if_neg hs] using hmem H hH
  refine ⟨c, hcκ, hxt, hsplit, ?_⟩
  by_contra hno
  push Not at hno
  have hall : ∀ g : G, g ∈ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro g
    have hle : (⨆ H ∈ Δ, H) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := iSup₂_le fun H hH => by
      by_cases hs : spl H
      · exact hsplit H hH hs
      · exact hno H hH hs
    rw [hΔ] at hle
    exact hle (Subgroup.mem_top g)
  have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
    commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
  have hcore := fix_of_level hΩc (fun A hA => (hel A hA).1) (fun A hA => hA.1) hT hA₀ hall hL
  obtain ⟨v, hv, l, hl, hne⟩ := hfix
  exact hne (hcore v hv l hl)

theorem cen_le_fStarPre_of_stab {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hidx : (T ⊓ fStarPre K).relIndex T = 2) {c : ℕ}
    (hXS : fStarPre K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    (hbad : ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    {U : Subgroup V} (hKU : K ≤ stabV ρ U) (hVU : Fx ρ (Wcl Ω c T) ≤ U) :
    T ⊓ cenV ρ U ≤ fStarPre K := by
  set X : Subgroup G := fStarPre K with hX
  set C : Subgroup G := K ⊓ cenV ρ U with hC
  have hXK : X ≤ K := Subgroup.map_subtype_le _
  have hCS : C ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun y hy =>
    cenV_le_stabV ρ _ (fun u hu => hy.2 u (hVU hu))
  have hNS : Subgroup.normalizer (T : Set G) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) :=
    normalizer_le_stabV hΩ c
  rintro t ⟨htT, htC⟩
  by_contra htX
  apply hbad
  have htC' : t ∈ C := ⟨hTK htT, htC⟩
  have hTCX : T ≤ C ⊔ X := by
    intro s hs
    by_cases hsX : s ∈ X
    · exact Subgroup.mem_sup_right hsX
    · have hidx' : ((T ⊓ X).subgroupOf T).index = 2 := hidx
      have hm := (Subgroup.mul_mem_iff_of_index_two hidx' (a := (⟨s, hs⟩ : T))
        (b := (⟨t, htT⟩ : T)⁻¹))
      have hst : s * t⁻¹ ∈ T ⊓ X := by
        have h1 : (⟨s, hs⟩ : T) * (⟨t, htT⟩ : T)⁻¹ ∈ (T ⊓ X).subgroupOf T := by
          refine hm.2 ⟨fun h => absurd (Subgroup.mem_subgroupOf.1 h).2 hsX, fun h => ?_⟩
          exact absurd (by simpa using (Subgroup.mem_subgroupOf.1 h).2) htX
        simpa using Subgroup.mem_subgroupOf.1 h1
      have : s = (s * t⁻¹) * t := by group
      rw [this]
      exact (C ⊔ X).mul_mem (Subgroup.mem_sup_right hst.2) (Subgroup.mem_sup_left htC')
  have hn : K ≤ Subgroup.normalizer (((C ⊔ X) ⊔ T : Subgroup G) : Set G) := by
    rw [sup_eq_left.2 hTCX]
    intro g hg
    refine mem_normalizer_of_conj_mem (K := K) (fun h hh y hy => ?_) hg
    have hle : C ⊔ X ≤ (C ⊔ X).comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_comap]
        show h * y * h⁻¹ ∈ C ⊔ X
        refine Subgroup.mem_sup_left ⟨K.mul_mem (K.mul_mem hh hy.1) (K.inv_mem hh),
          fun u hu => ?_⟩
        have hu' : ρ h⁻¹ u ∈ U := (hKU (K.inv_mem hh) u).2 hu
        have hy' : ρ y (ρ h⁻¹ u) = ρ h⁻¹ u := hy.2 _ hu'
        calc ρ (h * y * h⁻¹) u = ρ h (ρ y (ρ h⁻¹ u)) := by
              simp only [map_mul, MulAut.mul_apply]
          _ = ρ h (ρ h⁻¹ u) := by rw [hy']
          _ = u := by
              rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right (fStarPre_conj_mem K h hh y hy)
    have := hle hy
    rwa [Subgroup.mem_comap] at this
  exact (le_normalizer_sup_of_normal hT hTK (sup_le inf_le_left hXK) hn).trans
    (sup_le hNS (sup_le hCS hXS))

theorem e4_2_of_coatom_or_rank (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  by_cases hr : ∃ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H
  · obtain ⟨H, hH, hle⟩ := hr
    have hΔfin : Δ.Finite := Set.toFinite Δ
    rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin]
    exact (aParam_le_pRank hρ).trans (hle.trans
      (Finset.single_le_sum (f := iRank) (fun _ _ => Nat.zero_le _) (hΔfin.mem_toFinset.2 hH)))
  · push Not at hr
    exact e4_2_of_coatom G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT
      (fun H hH hns => (hcov H hH hns).resolve_right (Nat.not_le.2 (hr H hH))) hfix

theorem le_stabV_of_Wcl_le_fStarPre {V : Type} [CommGroup V] {ρ : G →* MulAut V}
    {T : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    {H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) {c : ℕ}
    (hXS : fStarPre H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) (hW : Wcl Ω c T ≤ fStarPre H) :
    H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
  have heq : Wcl Ω c T = Wcl Ω c (T ⊓ fStarPre H) :=
    Wcl_eq_of_le inf_le_left (le_inf (Wcl_le_self Ω c T) hW)
  refine (le_sup_bk hT hTH).trans (sup_le hXS fun g hg => mem_stabV_Fx_of_conj ?_)
  rw [heq]
  exact conjSubgroup_Wcl_eq hΩ c (conjSubgroup_eq_iff_mem_normalizer.2 hg.2)

open Classical in
theorem exists_level_of_lt' (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v)
    (κ : ℕ) (hκ : (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) = κ)
    (hbig : ¬ aParam ρ.range ≤ κ) :
    ∃ c ≤ κ, (∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      (∀ H ∈ Δ, H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
        H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      ∃ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∧
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) ∧
        ¬ Wcl {A | Om ρ (κ + 1) A} c T ≤ fStarPre H := by
  obtain ⟨c, hc, hxt, hspl, H, hH, hns, hst⟩ :=
    exists_level_of_lt G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT hfix κ hκ hbig
  refine ⟨c, hc, hxt, hspl, H, hH, hns, hst, fun hW => hst ?_⟩
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  exact le_stabV_of_Wcl_le_fStarPre hΩc hT (hΔT H hH).1
    (le_sup_left.trans (hxt H hH)) hW

open Classical in
theorem e4_2_of_coatom_rank_or_top (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V]
    [Finite V] (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H)
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  by_cases hr : ∃ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H
  · obtain ⟨H, hH, hle⟩ := hr
    have hΔfin : Δ.Finite := Set.toFinite Δ
    rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin]
    exact (aParam_le_pRank hρ).trans (hle.trans
      (Finset.single_le_sum (f := iRank) (fun _ _ => Nat.zero_le _) (hΔfin.mem_toFinset.2 hH)))
  push Not at hr
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  by_contra hbig
  obtain ⟨c, hcκ, hxt, hspl, H₀, hH₀, -, hst₀⟩ :=
    exists_level_of_lt G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT hfix κ hκ.symm hbig
  set N := stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) with hN
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  rcases IsCoatomic.eq_top_or_exists_le_coatom N with hNt | ⟨M, hM, hNM⟩
  · exact hst₀ (hNt ▸ le_top)
  apply hM.1
  rw [eq_top_iff, ← hΔ]
  refine iSup₂_le fun H hH => ?_
  by_cases hs : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  · exact (hspl H hH hs).trans hNM
  rcases hcov H hH hs with hco | hrk | htop
  · exact hco M hM ((hxt H hH).trans hNM)
  · exact absurd hrk (Nat.not_le.2 (hr H hH))
  · exact (le_stabV_of_Wcl_le_fStarPre hΩc hT (hΔT H hH).1 (le_sup_left.trans (hxt H hH))
      ((Wcl_mono_level hcκ T).trans htop)).trans hNM

open Classical in
theorem exists_level_of_lt_rk (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v)
    (κ : ℕ) (hκ : (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) = κ)
    (hbig : ¬ aParam ρ.range ≤ κ) :
    ∃ c ≤ κ, (∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      (∀ H ∈ Δ, (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
          ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H)) →
        H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      ∃ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∧
        ¬ ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H) ∧
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) ∧
        ¬ Wcl {A | Om ρ (κ + 1) A} c T ≤ fStarPre H := by
  have hΔfin : Δ.Finite := Set.toFinite Δ
  set Δf : Finset (Subgroup G) := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ H, H ∈ Δf ↔ H ∈ Δ := fun H => hΔfin.mem_toFinset
  rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin] at hκ
  set Ω : Set (Subgroup G) := {A | Om ρ (κ + 1) A} with hΩ
  obtain ⟨A', hA'⟩ : ∃ A', A' ∈ aSet (κ + 1) ρ.range := by
    by_contra h
    push Not at h
    exact hbig (aParam_le_of_aSet_empty _ _ h)
  have hA₀ : A'.comap ρ ∈ Ω := Om_comap_of_mem_aSet hρ hA'
  have hΩc : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω := fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  let spl : Subgroup G → Prop := fun H =>
    H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  let rk : Subgroup G → Prop := fun H =>
    (T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H
  let piece : Subgroup G → Subgroup G := fun H => if spl H ∨ rk H then H else xt T H
  let bad : Subgroup G → Finset ℕ := fun H =>
    (Finset.range (κ + 1)).filter (fun c => ¬ piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
  have hbad : ∀ H ∈ Δf, (bad H).card ≤ iRank H := by
    intro H hH
    obtain ⟨hTH, hF⟩ := hΔT H ((hmemΔ H).1 hH)
    by_cases hsr : spl H ∨ rk H
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_pos hsr]
      rw [this]
      by_cases hspl : spl H
      · exact card_bad_le_of_split hΩc hel hfx hT hTH hF hspl
      · obtain ⟨hidx, hrk⟩ := hsr.resolve_left hspl
        exact card_bad_le_of_rank hΩc hel hfx hT hTH hF hidx hspl hrk
    · have : bad H = (Finset.range (κ + 1)).filter
          (fun c => ¬ xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T))) := by
        simp only [bad, piece, if_neg hsr]
      rw [this]
      exact card_bad_xt_le hΩc hel hfx hT hTH hF
  have hcard : (Δf.biUnion bad).card < (Finset.range (κ + 1)).card := by
    have h2 : (Δf.biUnion bad).card ≤ κ :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum hbad).trans hκ.le)
    rw [Finset.card_range]
    omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hc)
  have hmem : ∀ H ∈ Δ, piece H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hHΔ
    by_contra hn
    exact hcn (Finset.mem_biUnion.2 ⟨H, (hmemΔ H).2 hHΔ, Finset.mem_filter.2 ⟨hc, hn⟩⟩)
  have hsr : ∀ H ∈ Δ, spl H ∨ rk H → H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun H hH hs => by
    simpa only [piece, if_pos hs] using hmem H hH
  have hxt : ∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hH
    by_cases hs : spl H ∨ rk H
    · exact (sup_le (Subgroup.map_subtype_le _) (hΔT H hH).1).trans (hsr H hH hs)
    · simpa only [piece, if_neg hs] using hmem H hH
  refine ⟨c, hcκ, hxt, hsr, ?_⟩
  by_contra hno
  have hno' : ∀ H ∈ Δ, H ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro H hH
    by_cases hs : spl H ∨ rk H
    · exact hsr H hH hs
    push Not at hs
    by_contra hst
    by_cases hW : Wcl Ω c T ≤ fStarPre H
    · exact hst (le_stabV_of_Wcl_le_fStarPre hΩc hT (hΔT H hH).1
        (le_sup_left.trans (hxt H hH)) hW)
    · exact hno ⟨H, hH, hs.1, hs.2, hst, hW⟩
  have hall : ∀ g : G, g ∈ stabV ρ (Fx ρ (Wcl Ω c T)) := by
    intro g
    have hle : (⨆ H ∈ Δ, H) ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := iSup₂_le hno'
    rw [hΔ] at hle
    exact hle (Subgroup.mem_top g)
  have hL : ∀ W : Subgroup G, W ≤ T → W ≠ ⊥ → ⁅L, W⁆ = L := fun W hWT hW =>
    commutator_eq_of_quasisimple_fitting hLF hLq hO2 (hT.isPGroup.to_le hWT) hW
  have hcore := fix_of_level hΩc (fun A hA => (hel A hA).1) (fun A hA => hA.1) hT hA₀ hall hL
  obtain ⟨v, hv, l, hl, hne⟩ := hfix
  exact hne (hcore v hv l hl)

open Classical in
theorem e4_2_of_coatom_rank_top_or_index_two (G : Type) [Group G] [Finite G] (V : Type)
    [CommGroup V] [Finite V] (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hcov : ∀ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) →
      (∀ M : Subgroup G, IsCoatom M → xt T H ≤ M → H ≤ M) ∨
        CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H ∨
        Wcl {A | Om ρ ((∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) + 1) A}
          (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) T ≤ fStarPre H ∨
        ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) :
    aParam ρ.range ≤ ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H := by
  by_cases hr : ∃ H ∈ Δ, CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ iRank H
  · obtain ⟨H, hH, hle⟩ := hr
    have hΔfin : Δ.Finite := Set.toFinite Δ
    rw [finsum_mem_eq_finite_toFinset_sum _ hΔfin]
    exact (aParam_le_pRank hρ).trans (hle.trans
      (Finset.single_le_sum (f := iRank) (fun _ _ => Nat.zero_le _) (hΔfin.mem_toFinset.2 hH)))
  push Not at hr
  set κ := ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H with hκ
  by_contra hbig
  obtain ⟨c, hcκ, hxt, hsr, H₀, hH₀, -, -, hst₀, -⟩ :=
    exists_level_of_lt_rk G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT hfix κ hκ.symm hbig
  set N := stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) with hN
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  rcases IsCoatomic.eq_top_or_exists_le_coatom N with hNt | ⟨M, hM, hNM⟩
  · exact hst₀ (hNt ▸ le_top)
  apply hM.1
  rw [eq_top_iff, ← hΔ]
  refine iSup₂_le fun H hH => ?_
  by_cases hs : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)
  · exact (hsr H hH (Or.inl hs)).trans hNM
  rcases hcov H hH hs with hco | hrk | htop | hix
  · exact hco M hM ((hxt H hH).trans hNM)
  · exact absurd hrk (Nat.not_le.2 (hr H hH))
  · exact (le_stabV_of_Wcl_le_fStarPre hΩc hT (hΔT H hH).1 (le_sup_left.trans (hxt H hH))
      ((Wcl_mono_level hcκ T).trans htop)).trans hNM
  · exact (hsr H hH (Or.inr hix)).trans hNM

theorem eq_level_of_index_two {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hidx : (T ⊓ fStarPre K).relIndex T = 2)
    (hns : ¬ K ≤ Subgroup.normalizer ((fStarPre K ⊔ T : Subgroup G) : Set G)) {c : ℕ}
    (hcκ : c ≤ κ) (hXc : xt T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    (hKc : ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T))) :
    ¬ Wcl Ω c T ≤ fStarPre K ∧ ∀ j < c, Wcl Ω j T ≤ fStarPre K := by
  set B := bk T K with hB
  have hTB : T ≤ B := le_bk hTK
  have hBc : ¬ B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun h =>
    hKc ((le_sup_bk hT hTK).trans (sup_le (le_sup_left.trans hXc) h))
  have hSB' : T ⊓ fStarPre K ≤ pCoreOf 2 B := inf_le_pCoreOf_bk hT hTK
  have hBS : pCoreOf 2 B ≤ T ⊓ fStarPre K := pCoreOf_bk_le hT hTK hidx hns
  have hrB : ∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ 1 :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (bk_rank hT hTK hidx)
  have hgB : ∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => bk_good hT hTK hidx hY hYn hYT
  refine ⟨fun hW => hBc (le_stabV_of_le_pCore hΩ hT hTB
    ((le_inf (Wcl_le_self Ω c T) hW).trans hSB')), fun j hj => ?_⟩
  by_contra hjX
  refine hBc (le_stabV_of_good hΩ hel hfix hT hTB hrB hgB (by omega : j + 1 ≤ c) hcκ ?_)
  exact fun h => hjX ((h.trans hBS).trans inf_le_right)

open Classical in
theorem exists_level_of_lt_rk' (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (T L : Subgroup G) (Δ : Set (Subgroup G))
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hΔ : (⨆ H ∈ Δ, H) = ⊤)
    (hΔT : ∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarMod H) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p))
    (hfix : ∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v)
    (κ : ℕ) (hκ : (∑ᶠ (H : Subgroup G) (_ : H ∈ Δ), iRank H) = κ)
    (hbig : ¬ aParam ρ.range ≤ κ) :
    ∃ c ≤ κ, (∀ H ∈ Δ, xt T H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      (∀ H ∈ Δ, (H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∨
          ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H)) →
        H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T))) ∧
      (∀ H ∈ Δ, (T ⊓ fStarPre H).relIndex T = 2 →
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) →
        ¬ Wcl {A | Om ρ (κ + 1) A} c T ≤ fStarPre H ∧
          ∀ j < c, Wcl {A | Om ρ (κ + 1) A} j T ≤ fStarPre H) ∧
      ∃ H ∈ Δ, ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) ∧
        ¬ ((T ⊓ fStarPre H).relIndex T = 2 ∧ CFSG.Open.pRank 2 (fStarMod H) < iRank H) ∧
        ¬ H ≤ stabV ρ (Fx ρ (Wcl {A | Om ρ (κ + 1) A} c T)) ∧
        ¬ Wcl {A | Om ρ (κ + 1) A} c T ≤ fStarPre H := by
  obtain ⟨c, hcκ, hxt, hsr, hex⟩ :=
    exists_level_of_lt_rk G V ρ hρ hO2 T L Δ hT hLF hLq hΔ hΔT hfix κ hκ hbig
  refine ⟨c, hcκ, hxt, hsr, fun H hH hidx hst => ?_, hex⟩
  have hns : ¬ H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G) :=
    fun hs => hst (hsr H hH (Or.inl hs))
  have hΩc : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ g : G,
      conjSubgroup A g ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)) :=
    fun A hA g => Om_conjSubgroup hA g
  have hel : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)),
      (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun A hA => ⟨hA.2.1, hA.2.2.1⟩
  have hfx : ∀ A ∈ ({A | Om ρ (κ + 1) A} : Set (Subgroup G)), ∀ B : Subgroup G, B ≤ A →
      mQuot A B ≤ κ → Fx ρ B = Fx ρ A :=
    fun A hA B hBA hm => hA.2.2.2 B hBA (Nat.lt_succ_of_le hm)
  exact eq_level_of_index_two hΩc hel hfx hT (hΔT H hH).1 hidx hns hcκ (hxt H hH) hst

end CFSG.Quasithin.RonanE42.Gen
