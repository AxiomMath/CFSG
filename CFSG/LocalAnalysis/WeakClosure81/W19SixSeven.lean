module

public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Five
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comm_cClos_le_V₀ {M V₀ V H S A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hMnorm : normalizer (V : Set G) = M)
    (hS : IsSylowIn 2 S H) {i k n : ℕ} (hn : n = k + i)
    (hA : A ∈ E3.gammaSet V i S) (hAV : A ≤ V) (hK : E1.IsE k H S A H) (hkV : n < rk ↥V)
    (hr : (n : ℕ∞) < E3.rParam V) (hmbar : n < mBar M V₀ V hV) :
    ⁅A, E3.cClos V n (pCoreOf 2 H)⁆ ≤ V₀ := by
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hAi : E3.mQuot V A ≤ i := (E3.mQuot_conj_eq hV hAV hAx).trans_le hmx.le
  have hijk : i + k ≤ n := by omega
  set Q := E3.cClos V n (pCoreOf 2 H) with hQ
  set W := E3.wClos V n (pCoreOf 2 H) with hW
  set B := A ⊓ pCoreOf 2 H with hB
  have hBW : B ≤ W := E3.e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  have hmB : E3.mQuot V B ≤ n := by
    have h := E3.e3_17_mQuot hV hS hAS hAV hAi hK
    rw [hB]
    omega
  have hcentle : Subgroup.centralizer (W : Set G) ≤ M := by
    rw [← hMnorm]
    exact E3.e3_17_cent_le hV hS hijk hr hkV hAS hAV hAi hK
  have hQM : Q ≤ M := (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans hcentle
  have hQW : Q ≤ centralizer (B : Set G) :=
    (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hBW)
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hQct : Q ≤ F11.CTilde M V₀ V :=
    le_cTilde_of_lt_mBar hV hV₀ hM hM₀ hmbar (inf_le_left.trans hAV : B ≤ V) hQM hQ2 hQW hmB
  refine Subgroup.commutator_le.2 ?_
  intro a ha q hq
  have hmem : q * a * q⁻¹ * a⁻¹ ∈ V₀ :=
    centralizesMod_of_mem_cTilde hV hM hM₀ (hQct hq) a (hAV ha)
  have e : ⁅a, q⁆ = (q * a * q⁻¹ * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact V₀.inv_mem hmem

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem two_lt_mBar (c : MinCex193 D V₀ V p X) :
    2 < mBar D.M V₀ V c.setting.isElemAbelian :=
  (c.setting.pair.mBarGT_iff_lt_mBar 2).1 c.mbar

theorem one_lt_rParam (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) :
    (1 : ℕ∞) < E3.rParam V := by
  have h1 : 2 < mBar D.M V₀ V c.setting.isElemAbelian := by have := c.two_lt_mBar; omega
  have h2 := h162 D V₀ V c.setting c.ne_bot h1
  rw [rMV_eq_rParam c.setting.normalizer_eq] at h2
  refine lt_of_lt_of_le ?_ h2
  have h3 := c.two_lt_mBar
  exact_mod_cast (by omega : 1 < mBar D.M V₀ V c.setting.isElemAbelian +
    mSub V₀)

end MinCex193

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem isE_self (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    E1.IsE 1 K (D.T ⊓ K) (conjSubgroup V g) K := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · exact (E1.tauOf_le _ _ _).trans (by rw [inf_eq_left.2 inf_le_right])
  · rw [inf_eq_left.2 inf_le_right]
    exact hc.isE.2.2.1
  · exact Or.inl (E1.isE_eOne_of_isSolvable hc.isE (hc.isSolvable_K c))

theorem cClos_le_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) (h162 : W3Thm162Gt2 G) :
    E3.cClos V 1 D.T ≤ D.T ⊓ K := by
  have hAT := hc.le_T
  have hVg := E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g
  have hkV : 1 < rk ↥(conjSubgroup V g) := by rw [E3.rk_conjSubgroup]; have := c.three_le_rk; omega
  have hAW : conjSubgroup V g ≤ E3.wClos (conjSubgroup V g) 1 D.T :=
    E3.le_wClos_of_mQuot_le_self hVg hAT le_rfl (by rw [E3.mQuot_self]; exact Nat.zero_le _) hkV
  rw [E3.wClos_conjV] at hAW
  have hCA : E3.cClos V 1 D.T ≤ D.T ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hAW))
  have hτ : D.T ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ≤
      E1.tauOf (X ⊔ D.T) D.T (conjSubgroup V g) := by
    intro t ht
    refine ⟨ht.1, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (Subgroup.mem_sup_right ht.1), fun a ha => ?_⟩
    have h1 : a * t = t * a := Subgroup.mem_centralizer_iff.1 ht.2 a ha
    rw [commutatorElement_eq_one_iff_mul_comm.2 h1.symm]
    exact Subgroup.one_mem _
  exact fun x hx => hc.isE.2.1 (hτ (hCA hx))

theorem cClos_le_cClos_inf (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) : E3.cClos V 1 D.T ≤ E3.cClos V 1 (D.T ⊓ K) :=
  le_inf (hc.cClos_le_K c h162)
    (inf_le_right.trans (Subgroup.centralizer_le (E3.wClos_mono (V := V) (i := 1) inf_le_left)))

theorem comm_twoResidual_ne_bot (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) : ⁅twoResidual K, E3.cClos V 1 (D.T ⊓ K)⁆ ≠ ⊥ := by
  intro h
  obtain ⟨x, hxK, hxp⟩ := hc.exists_orderOf_eq c
  have hx2 : x ∈ twoResidual K := Conf196.mem_twoResidual c hxK hxp
  have hxH : x ∈ X ⊔ D.T := hc.le_H hxK
  have hxC : x ∈ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' := hc.cClos_le_cClos_inf c h162 hy
    have h1 : ⁅x, y⁆ ∈ ⁅twoResidual K, E3.cClos V 1 (D.T ⊓ K)⁆ :=
      Subgroup.commutator_mem_commutator hx2 hy'
    rw [h, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  apply c.not_dvd_card_inf_centralizer_cClos
  have hmem : x ∈ (X ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) := ⟨hxH, hxC⟩
  have hdvd := orderOf_dvd_natCard
    (⟨x, hmem⟩ : ↥((X ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)))
  rw [← Subgroup.orderOf_coe] at hdvd
  simpa [hxp] using hdvd

theorem cClos_comm (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) (h162 : W3Thm162Gt2 G) :
    Z193 D V ≤ E3.cClos V 1 (pCoreOf 2 K) ∧
    ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ ≠ ⊥ ∧
    ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ ≤ conjSubgroup V₀ g := by
  have hVg := hc.isElemAbelian_A c
  have hSyl : IsSylowIn 2 (D.T ⊓ K) K := hc.isE.2.2.1
  have hAS : conjSubgroup V g ≤ D.T ⊓ K := le_inf hc.le_T (hc.A_le_K c)
  have hkV : 1 < rk ↥(conjSubgroup V g) := by
    rw [E3.rk_conjSubgroup]
    have := c.three_le_rk
    omega
  have hr : ((1 : ℕ) : ℕ∞) < E3.rParam (conjSubgroup V g) := by
    rw [E3.rParam_conj]
    exact_mod_cast c.one_lt_rParam h162
  have hA : conjSubgroup V g ∈ E3.gammaSet (conjSubgroup V g) 0 (D.T ⊓ K) :=
    ⟨hAS, 1, by rw [conjSubgroup_one], by rw [conjSubgroup_one, E3.mQuot_self]⟩
  have hAi : E3.mQuot (conjSubgroup V g) (conjSubgroup V g) ≤ 0 := (E3.mQuot_self _).le
  have hK : E1.IsE 1 K (D.T ⊓ K) (conjSubgroup V g) K := hc.isE_self c
  have hne : ⁅twoResidual K, E3.cClos (conjSubgroup V g) 1 (D.T ⊓ K)⁆ ≠ ⊥ := by
    rw [E3.cClos_conjV]
    exact hc.comm_twoResidual_ne_bot c h162
  have hle := E3.e3_17_le hVg hSyl (i := 0) (j := 1) (k := 1) (by omega) hr hkV hAS le_rfl
    hAi hK
  obtain ⟨-, h2⟩ := E3.e3_17_comm_ne hVg hSyl (i := 0) (j := 1) (k := 1) (by omega) hr hkV hAS
    le_rfl hAi hK hne
  rw [E3.cClos_conjV, E3.cClos_conjV] at hle
  rw [E3.cClos_conjV] at h2
  refine ⟨c.Z193_le_cClos.trans ((hc.cClos_le_cClos_inf c h162).trans hle), h2, ?_⟩
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g c.V₀_le_V
  have hMnormg : normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]
  have hM₀g : conjSubgroup D.M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g c.setting.pair.le_normalizer₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hmbar : 1 < mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg := by
    rw [mBar_conj D.M V₀ V c.setting.isElemAbelian c.V₀_le_V c.setting.pair.le_normalizer
      c.setting.pair.le_normalizer₀ g]
    have := c.two_lt_mBar
    omega
  have h3 := comm_cClos_le_V₀ (M := conjSubgroup D.M g) (V₀ := conjSubgroup V₀ g)
    (V := conjSubgroup V g) (H := K) (S := D.T ⊓ K) (A := conjSubgroup V g) hVg hV₀g
    hMnormg.ge hM₀g hMnormg hSyl (i := 0) (k := 1) (n := 1) rfl hA le_rfl hK hkV hr hmbar
  rwa [E3.cClos_conjV] at h3

theorem V_le_conj_M (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) (h162 : W3Thm162Gt2 G) :
    V ≤ conjSubgroup D.M g ∧ ⁅conjSubgroup V g, V⁆ ≤ conjSubgroup V g ⊓ V := by
  obtain ⟨-, hne, hle⟩ := hc.cClos_comm c h162
  set C := E3.cClos V 1 (pCoreOf 2 K) with hC
  have hAK : conjSubgroup V g ≤ K := hc.A_le_K c
  have hKC : K ≤ normalizer (C : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans (E3.normalizer_le_normalizer_cClos _)
  have hAC : ⁅conjSubgroup V g, C⁆ ≤ C := by
    refine Subgroup.commutator_le.2 fun a ha y hy => ?_
    have h1 : a * y * a⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hKC (hAK ha)) y).1 hy
    have e : ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact C.mul_mem h1 (C.inv_mem hy)
  have hkV : 1 < rk ↥V := by
    have := c.three_le_rk
    omega
  have hVW : V ≤ E3.wClos V 1 (pCoreOf 2 K) :=
    E3.le_wClos_of_mQuot_le_self c.setting.isElemAbelian (hc.V_le_pCoreOf c) le_rfl
      (by rw [E3.mQuot_self]; exact Nat.zero_le _) hkV
  have hVC : ∀ v ∈ V, ∀ y ∈ C, v * y = y * v := fun v hv y hy =>
    Subgroup.mem_centralizer_iff.1 (inf_le_right (a := pCoreOf 2 K) hy) v (hVW hv)
  obtain ⟨⟨w, hwE⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwC : w ∈ C := hAC hwE
  have hwV₀ : w ∈ conjSubgroup V₀ g := hle hwE
  have hcent := centralizer_le_conj_M c.setting c.ne_bot g hwV₀ hw1'
  have hVM : V ≤ conjSubgroup D.M g := by
    intro v hv
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hVC v hv y hwC).symm
  refine ⟨hVM, Subgroup.commutator_le.2 fun a ha v hv => Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · have hvN : v ∈ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]
      exact hVM hv
    have h1 : v * a⁻¹ * v⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN _).1 ((conjSubgroup V g).inv_mem ha)
    have e : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (conjSubgroup V g).mul_mem ha h1
  · have haN : a ∈ normalizer (V : Set G) := by
      rw [c.setting.normalizer_eq]
      exact D.sylowM.le (hc.le_T ha)
    have h1 : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 haN v).1 hv
    have e : ⁅a, v⁆ = (a * v * a⁻¹) * v⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact V.mul_mem h1 (V.inv_mem hv)

end Conf196

end CFSG.LocalAnalysis.WeakClosure81
