module

public import CFSG.Quasithin.H13.A6S13816h

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pCoreOf_L1_le {H : Subgroup G} (hH : H ∈ S.Hz)
    (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) : pCoreOf 2 S.L1 ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (le_sup_left.trans hH.1.1))
    (hn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem UH_le_commutator_L1 {H : Subgroup G} (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) :
    conjClosure S.V3 H ≤ ⁅conjClosure S.V3 H, S.L1⁆ := by
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  have hN := A5.le_normalizer_commutator (A := conjClosure S.V3 H) (B := S.L1) hUN hn
  refine conjClosure_le fun h hh x hx => ?_
  have hx' : x ∈ ⁅conjClosure S.V3 H, S.L1⁆ :=
    Subgroup.commutator_mono (le_conjClosure _ _) le_rfl (S.commutator_V3_L1.ge hx)
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) x).mp hx'

theorem UH_le_closure_c (hS : S.Hyp138) (hhat : ¬ IsHatA6 L)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) :
    conjClosure S.V3 H ≤ Subgroup.closure
      ({w | ∃ u ∈ conjClosure S.V3 H, (S.cL1 hhat : G) * u * (S.cL1 hhat : G)⁻¹ * u⁻¹ = w} ∪
        (fsuV1 T V : Set G)) := by
  set c : G := (S.cL1 hhat : G) with hc
  set R := Subgroup.closure
    ({w | ∃ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ = w} ∪ (fsuV1 T V : Set G)) with hR
  have hF := (hS.hF H hH).toHypF91
  have hcH : c ∈ H := (le_sup_left.trans hH.1.1) (S.cL1_mem hhat)
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) := le_normalizer_conjClosure _ _
  have hcV : ∀ v ∈ fsuV1 T V, ∀ x ∈ H, x * v * x⁻¹ = v := fun v hv x hx => by
    have := Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hx) v hv
    rw [← this, mul_inv_cancel_right]
  have hV1R : ∀ v ∈ fsuV1 T V, v ∈ R := fun v hv => Subgroup.subset_closure (Or.inr hv)
  have hgen : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ R := fun u hu =>
    Subgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩)
  have hO := S.pCoreOf_L1_le hH hn
  refine (S.UH_le_commutator_L1 hn).trans ((Subgroup.commutator_le).mpr ?_)
  intro u hu x hx
  rw [commutatorElement_def]
  rcases S.L1_decomp hhat hx with hy | hy | hy
  · exact hV1R _ (hF.commutator_conjClosure_le u hu x (hO hy))
  ·
    set y := c * c * x with hy'
    have hv := hF.commutator_conjClosure_le u hu y (hO hy)
    have hx' : x = c * y := by
      rw [hy']
      calc x = c ^ 3 * x := by rw [hc3, one_mul]
        _ = c * (c * c * x) := by rw [pow_three']; group
    have e : u * x * u⁻¹ * x⁻¹ = (c * u * c⁻¹ * u⁻¹)⁻¹ * (c * (u * y * u⁻¹ * y⁻¹) * c⁻¹) := by
      rw [hx']
      group
    rw [e]
    exact R.mul_mem (R.inv_mem (hgen u hu)) (hV1R _ (by rw [hcV _ hv c hcH]; exact hv))
  ·
    set y := c * x with hy'
    have hv := hF.commutator_conjClosure_le u hu y (hO hy)
    have hw : c⁻¹ * u * c ∈ conjClosure S.V3 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem hcH)) u).mp hu
      simpa using this
    have e : u * x * u⁻¹ * x⁻¹ =
        (c * (c⁻¹ * u * c) * c⁻¹ * (c⁻¹ * u * c)⁻¹) * (c⁻¹ * (u * y * u⁻¹ * y⁻¹) * c) := by
      rw [hy']
      group
    have hv' : c⁻¹ * (u * y * u⁻¹ * y⁻¹) * c ∈ fsuV1 T V := by
      have := hcV _ hv c⁻¹ (H.inv_mem hcH)
      rw [inv_inv] at this
      rw [this]
      exact hv
    rw [e]
    exact R.mul_mem (hgen _ hw) (hV1R _ hv')

theorem mem_V1_of_fix_c (hS : S.Hyp138) (hhat : ¬ IsHatA6 L)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) {a : G}
    (ha : a ∈ conjClosure S.V3 H)
    (hfix : ((S.cL1 hhat : G) * a * (S.cL1 hhat : G)⁻¹)⁻¹ * a ∈ fsuV1 T V) :
    a ∈ fsuV1 T V := by
  set c : G := (S.cL1 hhat : G) with hc
  have hF := (hS.hF H hH).toHypF91
  have hcH : c ∈ H := (le_sup_left.trans hH.1.1) (S.cL1_mem hhat)
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hUN : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUV : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  set k := actH hV₁ hUN ⟨c, hcH⟩ with hk
  have hk3 : k ^ 3 = 1 := by
    rw [hk, ← map_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
    rw [this, map_one]
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (Fact.out : IsElemAbelian 2 _).2 w.1 w.2)
  have hmk : ∀ b (hb : b ∈ conjClosure S.V3 H),
      modMk hUV b hb ∈ commV (Subgroup.zpowers k) := by
    let P : Subgroup G :=
      { carrier := {b | ∃ hb : b ∈ conjClosure S.V3 H,
          modMk hUV b hb ∈ commV (Subgroup.zpowers k)}
        one_mem' := ⟨Subgroup.one_mem _, by rw [modMk_one]; exact Subgroup.one_mem _⟩
        mul_mem' := fun {x y} ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨Subgroup.mul_mem _ hx hy, by
          rw [modMk_mul hUV hx hy]
          exact Subgroup.mul_mem _ hx' hy'⟩
        inv_mem' := fun {x} ⟨hx, hx'⟩ => ⟨Subgroup.inv_mem _ hx, by
          rw [modMk_inv hUV hx]
          exact Subgroup.inv_mem _ hx'⟩ }
    have hle : Subgroup.closure ({w | ∃ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ = w} ∪
        (fsuV1 T V : Set G)) ≤ P := by
      rw [Subgroup.closure_le]
      rintro _ (⟨u, hu, rfl⟩ | hv)
      · have hcu : c * u * c⁻¹ ∈ conjClosure S.V3 H :=
          (Subgroup.mem_normalizer_iff.mp (hUN hcH) u).mp hu
        refine ⟨Subgroup.mul_mem _ hcu (Subgroup.inv_mem _ hu), ?_⟩
        rw [modMk_mul hUV hcu (Subgroup.inv_mem _ hu), modMk_inv hUV hu]
        have e := actH_modMk hV₁ hUV hUN ⟨c, hcH⟩ hu
        rw [← hk] at e
        rw [show modMk hUV (c * u * c⁻¹) hcu = k (modMk hUV u hu) from e.symm]
        exact G6.mem_commV_of_mem (Subgroup.mem_zpowers k) _
      · have hvU : _ ∈ conjClosure S.V3 H := (hF.V₁_le_Vp.trans (le_conjClosure _ _)) hv
        refine ⟨hvU, ?_⟩
        have : modMk hUV _ hvU = 1 := Subtype.ext ((secMk_eq_one_iff).mpr hv)
        rw [this]
        exact Subgroup.one_mem _
    intro b hb
    obtain ⟨_, h⟩ := hle (S.UH_le_closure_c hS hhat hH hn hb)
    exact h
  have hcaU : c * a * c⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (hUN hcH) a).mp ha
  have hka : k (modMk hUV a ha) = modMk hUV a ha := by
    rw [hk, actH_modMk hV₁ hUV hUN ⟨c, hcH⟩ ha]
    exact Subtype.ext ((secMk_eq_secMk_iff).mpr hfix)
  have hbot := G64.commV_inf_fixV_of_pow_three hW2 hk3
  have h1 : modMk hUV a ha ∈ commV (Subgroup.zpowers k) ⊓ fixV (Subgroup.zpowers k) :=
    ⟨hmk a ha, G64.fixV_zpowers_iff.mpr hka⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (secMk_eq_one_iff).mp (congrArg Subtype.val h1)

end Setting4

theorem case13816SzPairMod_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (hSzE : SzEnd) :
    Case13816SzPairMod := by
  intro G _ _ T L V S hS hhat H hH K hK hne hHeq hHN hcomm ⟨n, hSz⟩
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36 h37 h38 h139 h1334 h13 hS hH hK
  rw [← hHeq] at hF
  have hHq : SQTKGroup ↥H := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨I, hV₁I, hIU, Wa, hWa, hirr⟩ := exists_isIrrPlusTildeU hF
  have hFI := factElem hF hIU
  have hIT := isIrrPlusTildeT_of_ambient hF hIU Wa hWa hirr
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hIT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨hA38K, -⟩ := five_group_data hF hHq h37 h38 hne
  have hsimple := CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
  have hneL : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI hF hIU hsimple hneL
  have hLSz : IsSz n ↥(autIH (fsuV1 T V) I H K) := isSz_congr eL hSz
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨-, hFive⟩ := F918_5' hF hHq hne hV₁I hIU Wa hWa hirr hD36 hD37 hD321 hI5 h37 h38
  have h5 := hFive t htT htK
  obtain ⟨-, -, hprelim⟩ := five_prelim hF hHq hne hIU hnt h37 h38
  obtain ⟨htT', -, hMp, -⟩ := hprelim t htT htK
  have htMp := autIH_T_le_normalizer hF I htT'
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hcL1 : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hcH : (S.cL1 hhat : G) ∈ H := (le_sup_left.trans hH.1.1) hcL1
  set σ := φ ⟨S.cL1 hhat, hcH⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨S.cL1 hhat, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
    rw [this, map_one]
  have hσMp : ∀ m ∈ autIH (fsuV1 T V) I H (conjClosure K T), σ * m = m * σ := by
    intro m hm
    rw [autIH_eq_map hF hF.K₀_le_H] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    have hx : (((⟨S.cL1 hhat, hcH⟩ : ↥H) * y * (⟨S.cL1 hhat, hcH⟩ : ↥H)⁻¹ * y⁻¹ : ↥H) : G) ∈
        pCoreOf 2 H := hcomm _ hcL1 _ (Subgroup.mem_subgroupOf.mp hy)
    have h2 := hF.actH_eq_one_of_mem_pCoreOf hIU hx
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le_conjClosure_U hIU le_rfl
  have hfpf : ∀ w, σ w = w → w = 1 := by
    intro w hw
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    rw [hwa, hσ, actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) _ haIH]
      at hw
    have hfix := (secMk_eq_secMk_iff).mp (congrArg Subtype.val hw)
    have haV := S.mem_V1_of_fix_c hS hhat hH hHN (hIHU haIH) hfix
    rw [hwa]
    exact Subtype.ext ((secMk_eq_one_iff).mpr haV)
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hFI.out.2 w.1 w.2)
  exact SzMod.false_of_modFive hW2 hSzE hLSz hσ3 hfpf hσMp hMp htMp h5

end CFSG.Quasithin.H13.A6
