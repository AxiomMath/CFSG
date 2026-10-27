module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoice
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeS4FrameBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_conjSubgroup_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nine3_commutator_mem_nineI (hc : Nine3Choice V T A K S X p g x)
    {i w : G} (hi : i ∈ nineI V K) (hw : w ∈ K) : ⁅i, w⁆ ∈ nineI V K := by
  have hwi : w * i * w⁻¹ ∈ nineI V K := by
    have hconj := Nine3Core.conjSubgroup_nineI (V := V) (K := K) (K.inv_mem hw)
    rw [← hconj]
    exact CFSG.Quasithin.mem_conjSubgroup_iff.mpr (by
      have h : w⁻¹ * (w * i * w⁻¹) * (w⁻¹)⁻¹ = i := by group
      rw [h]; exact hi)
  have hcomm : ⁅w, i⁆ ∈ nineI V K :=
    (nineI V K).mul_mem hwi ((nineI V K).inv_mem hi)
  have heq : ⁅i, w⁆ = ⁅w, i⁆⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [heq]
  exact (nineI V K).inv_mem hcomm

theorem nine3_conj_inf_nineW (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    conjSubgroup A x ⊓ centralizer (A : Set G) = ⊥ ∧ conjSubgroup A x ⊓ nineW V S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTI := hc.core.hyp7.2.2
  have hAx_eq : conjSubgroup A x = conjSubgroup V (g * x) := by
    rw [← hc.V_g, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  have hbot : conjSubgroup A x ⊓ centralizer (A : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    by_contra hb1
    have hbVx : b ∈ conjSubgroup V (g * x) := hAx_eq ▸ hb.1
    have hbC : b ∈ centralizer (A : Set G) := hb.2
    have hA_cent : A ≤ centralizer ({b} : Set G) := by
      intro aa haa
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.mp hbC aa haa).symm)
    have hA_N : A ≤ normalizer (conjSubgroup V (g * x) : Set G) :=
      hA_cent.trans (centralizer_le_normalizer_conj hTI (g * x) hbVx hb1)
    obtain ⟨aa, P, haa, haaR, hPK, hPcard, hXP, hPclosure, hinv⟩ :=
      nine3_exists_inverted_P hc hI
    have hda : aa ∈ conjSubgroup V g := hc.V_g ▸ haa
    have hde : x⁻¹ * aa * x ∈ conjSubgroup V (g * x) := by
      rw [← hAx_eq]
      exact CFSG.Quasithin.mem_conjSubgroup_iff.mpr (by
        have h : x * (x⁻¹ * aa * x) * x⁻¹ = aa := by group
        rw [h]; exact haa)
    have hdN : aa ∈ normalizer (conjSubgroup V (g * x) : Set G) := hA_N haa
    have h2 : IsPGroup 2 (Subgroup.closure ({aa, x⁻¹ * aa * x} : Set G)) :=
      isPGroup_closure_pair_of_mem_normalizer hc.core.hyp7.1 hda hde hdN
    have hP2 : IsPGroup 2 ↥P := h2.to_le hPclosure
    have hPne : P ≠ ⊥ := by
      intro hbotP
      rw [hbotP, Subgroup.card_bot] at hPcard
      exact hc.core.hyp.base.prime.ne_one hPcard.symm
    obtain ⟨yp, hyp⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    have h2dvd : 2 ∣ orderOf yp := hP2.dvd_orderOf hyp
    have hpdvd : orderOf yp ∣ p := by
      rw [← hPcard]
      exact orderOf_dvd_natCard yp
    have h2p : 2 ∣ p := h2dvd.trans hpdvd
    exact hc.core.hyp.base.odd
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hc.core.hyp.base.prime).mp h2p).symm
  refine ⟨hbot, ?_⟩
  have hAW : A ≤ nineW V S := le_iSup₂_of_le A hc.core.A_mem_nineDelta le_rfl
  have hW_cent : nineW V S ≤ centralizer (A : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr (fun aa haa =>
      hc.core.nineW_mul_comm (hAW haa) hz)
  apply le_bot_iff.mp
  calc conjSubgroup A x ⊓ nineW V S ≤ conjSubgroup A x ⊓ centralizer (A : Set G) :=
        inf_le_inf le_rfl hW_cent
    _ = ⊥ := hbot

theorem nine3_card_nineI (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    Nat.card ↥(nineI V K) =
      Nat.card ↥(nineI V K ⊓ centralizer (U : Set G)) * Nat.card ↥(U ⊓ pCoreOf 2 K) := by
  classical
  obtain ⟨g₀, -, -, hnotR⟩ := mem_omegaSet.mp hU.1
  have hex : ∃ u ∈ U, u ∉ pCoreOf 2 K := by
    by_contra hcon
    exact hnotR (fun u hu => by_contra (fun huc => hcon ⟨u, hu, huc⟩))
  obtain ⟨u, huU, huR⟩ := hex
  have huK : u ∈ K := hU.2 huU
  have hcm : ∀ i : ↥(nineI V K), ⁅(i : G), u⁆ ∈ nineI V K :=
    fun i => nine3_commutator_mem_nineI hc i.2 huK
  let f : ↥(nineI V K) →* ↥(nineI V K) :=
    { toFun := fun i => ⟨⁅(i : G), u⁆, hcm i⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro i j
        apply Subtype.ext
        change ⁅((i : G) * (j : G)), u⁆ = ⁅(i : G), u⁆ * ⁅(j : G), u⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hconj : (i : G) * ⁅(j : G), u⁆ * (i : G)⁻¹ = ⁅(j : G), u⁆ := by
          rw [CFSG.Open.IsElemAbelian.comm hI.abelian i.2 (hcm j)]
          group
        rw [hconj]
        exact (CFSG.Open.IsElemAbelian.comm hI.abelian (hcm i) (hcm j)).symm }
  have hf_val : ∀ i : ↥(nineI V K), (f i : G) = ⁅(i : G), u⁆ := fun _ => rfl
  have hUR_le_I : U ⊓ pCoreOf 2 K ≤ nineI V K := by
    rw [← nine3_comm_of_mem_omegaIn hc hI hU]
    exact Subgroup.commutator_le.mpr fun i hi w hw =>
      nine3_commutator_mem_nineI hc hi (hU.2 hw)
  have hker : f.ker =
      (nineI V K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf (nineI V K) := by
    ext xx
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : ⁅(xx : G), u⁆ = 1 := by
        have := congrArg Subtype.val hx
        simpa [hf_val] using this
      have hcomm : (xx : G) * u = u * (xx : G) :=
        commutatorElement_eq_one_iff_mul_comm.mp hx'
      have hUle : U ≤ Subgroup.centralizer ({(xx : G)} : Set G) := by
        rw [nine3_eq_sup_inf_zpowers hc hU huU huR]
        apply sup_le
        · intro t ht
          exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact (CFSG.Open.IsElemAbelian.comm hI.abelian (hUR_le_I ht) xx.2).symm)
        · refine Subgroup.zpowers_le.mpr ?_
          exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact hcomm)
      refine ⟨xx.2, Subgroup.mem_centralizer_iff.mpr (fun w hw => ?_)⟩
      exact ((Subgroup.mem_centralizer_iff.mp (hUle hw)) (xx : G)
        (Set.mem_singleton (xx : G))).symm
    · intro hx
      have hcomm : u * (xx : G) = (xx : G) * u :=
        Subgroup.mem_centralizer_iff.mp hx.2 u huU
      apply Subtype.ext
      have h1 : ⁅(xx : G), u⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
      simpa [hf_val] using h1
  have hrange : f.range = (U ⊓ pCoreOf 2 K).subgroupOf (nineI V K) := by
    apply le_antisymm
    · rintro y hy
      obtain ⟨xx, rfl⟩ := MonoidHom.mem_range.mp hy
      exact Subgroup.mem_subgroupOf.mpr (by
        have hmem : ⁅(xx : G), u⁆ ∈ U ⊓ pCoreOf 2 K := by
          rw [← nine3_comm_of_mem_omegaIn hc hI hU]
          exact Subgroup.commutator_mem_commutator xx.2 huU
        simpa [hf_val] using hmem)
    · intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      have hrel : (U ⊓ pCoreOf 2 K).relIndex U = 2 := nine3_relIndex_of_mem_omegaIn hc hU
      have hUR_le_M : U ⊓ pCoreOf 2 K ≤ f.range.map (nineI V K).subtype := by
        rw [← nine3_comm_of_mem_omegaIn hc hI hU]
        refine Subgroup.commutator_le.mpr ?_
        intro i hi w hw
        by_cases hwL : w ∈ U ⊓ pCoreOf 2 K
        · have h1 : ⁅i, w⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact CFSG.Open.IsElemAbelian.comm hI.abelian hi (hUR_le_I hwL)
          rw [h1]
          exact (f.range.map (nineI V K).subtype).one_mem
        · have htL : u⁻¹ * w ∈ U ⊓ pCoreOf 2 K := by
            have key := (Subgroup.mul_mem_iff_of_index_two
              (H := (U ⊓ pCoreOf 2 K).subgroupOf U) hrel
              (a := (⟨u, huU⟩ : ↥U)⁻¹) (b := ⟨w, hw⟩)).2 (by
                rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
                exact iff_of_false (fun h => huR h.2) hwL)
            exact Subgroup.mem_subgroupOf.1 key
          have hw_eq : w = u * (u⁻¹ * w) := by group
          rw [hw_eq, commutatorElement_mul_right_eq_mul_conj]
          have h2 : ⁅i, u⁻¹ * w⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact CFSG.Open.IsElemAbelian.comm hI.abelian hi (hUR_le_I htL)
          rw [h2, mul_one]
          have hmem : (f ⟨i, hi⟩ : G) ∈ f.range.map (nineI V K).subtype :=
            ⟨f ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
          simpa [hf_val] using hmem
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hUR_le_M hy)
      have hzy' : z = y := Subtype.ext hzy
      simpa [hzy'] using hz
  have hcard_ker : Nat.card ↥f.ker =
      Nat.card ↥(nineI V K ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard_range : Nat.card ↥f.range = Nat.card ↥(U ⊓ pCoreOf 2 K) := by
    rw [hrange]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR_le_I).toEquiv
  calc Nat.card ↥(nineI V K) = Nat.card ↥f.ker * Nat.card ↥f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ↥(nineI V K ⊓ Subgroup.centralizer (U : Set G)) *
          Nat.card ↥(U ⊓ pCoreOf 2 K) := by rw [hcard_ker, hcard_range]

theorem nine3_nineI_eq_J_sup (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineI V K = (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ⊔ conjSubgroup (A ⊓ pCoreOf 2 K) x ∧
      (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ⊓ conjSubgroup (A ⊓ pCoreOf 2 K) x = ⊥ := by
  classical
  set J : Subgroup G := ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K with hJ
  have hbot := (nine3_conj_inf_nineW hc hI).1
  have hxK : x ∈ K := hc.core.hyp.base.toTwoPTwo.sylowP.le hc.x_mem
  have hAΩ : A ∈ omegaIn V K (nineE V K) := nine3_A_mem_omega hc
  have hJ_centA : J = nineI V K ⊓ Subgroup.centralizer (A : Set G) :=
    hJ.trans (nine3_centralizer_A_eq_J hc hI).symm
  have hJ_le_I : J ≤ nineI V K := hJ_centA ▸ inf_le_left
  have hA0_le_I : A ⊓ pCoreOf 2 K ≤ nineI V K :=
    hc.inf_pCoreOf_le_nineI hc.core.A_mem_nineOmegaIn
  have hA0x_le_I : conjSubgroup (A ⊓ pCoreOf 2 K) x ≤ nineI V K :=
    (E3.conjSubgroup_mono_left x hA0_le_I).trans
      (le_of_eq (Nine3Core.conjSubgroup_nineI hxK))
  have hdisj : J ⊓ conjSubgroup (A ⊓ pCoreOf 2 K) x = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ conjSubgroup A x ⊓ centralizer (A : Set G) :=
      ⟨E3.conjSubgroup_mono_left x inf_le_left hz.2,
        (hJ_centA ▸ hz.1 : z ∈ nineI V K ⊓ Subgroup.centralizer (A : Set G)).2⟩
    rw [hbot] at h1
    exact Subgroup.mem_bot.mp h1
  have hJ_le_centA : J ≤ Subgroup.centralizer (A : Set G) := hJ_centA ▸ inf_le_right
  have hA0x_le_centJ : conjSubgroup (A ⊓ pCoreOf 2 K) x ≤
      Subgroup.centralizer (J : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr (fun w hw =>
      (CFSG.Open.IsElemAbelian.comm hI.abelian (hA0x_le_I hz) (hJ_le_I hw)).symm)
  have hcard_sup : Nat.card ↥(J ⊔ conjSubgroup (A ⊓ pCoreOf 2 K) x) =
      Nat.card ↥J * Nat.card ↥(conjSubgroup (A ⊓ pCoreOf 2 K) x) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer J
      (conjSubgroup (A ⊓ pCoreOf 2 K) x)
      (hA0x_le_centJ.trans (Subgroup.centralizer_le_normalizer (J : Set G)))
      (disjoint_iff.mpr hdisj)
  have hcard_sup_I : Nat.card ↥(J ⊔ conjSubgroup (A ⊓ pCoreOf 2 K) x) = Nat.card ↥(nineI V K) := by
    calc Nat.card ↥(J ⊔ conjSubgroup (A ⊓ pCoreOf 2 K) x)
        = Nat.card ↥J * Nat.card ↥(conjSubgroup (A ⊓ pCoreOf 2 K) x) := hcard_sup
      _ = Nat.card ↥J * Nat.card ↥(A ⊓ pCoreOf 2 K) := by
            rw [card_conjSubgroup' x (A ⊓ pCoreOf 2 K)]
      _ = Nat.card ↥(nineI V K ⊓ Subgroup.centralizer (A : Set G)) *
            Nat.card ↥(A ⊓ pCoreOf 2 K) := by rw [hJ_centA]
      _ = Nat.card ↥(nineI V K) := (nine3_card_nineI hc hI hAΩ).symm
  have hsup_le : J ⊔ conjSubgroup (A ⊓ pCoreOf 2 K) x ≤ nineI V K :=
    sup_le hJ_le_I hA0x_le_I
  exact ⟨(Subgroup.eq_of_le_of_card_ge hsup_le (le_of_eq hcard_sup_I.symm)).symm, hdisj⟩

end CFSG.LocalAnalysis.WeakClosure81
