module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_sup (P Q : Subgroup G) (g : G) :
    conjSubgroup (P ⊔ Q) g = conjSubgroup P g ⊔ conjSubgroup Q g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_sup _ _ _

private theorem nineThree_conj_iSup' {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

namespace Nine3Choice

theorem nineH_le_K : nineH V K ≤ K := iSup₂_le fun _ hU => hU.2

theorem inf_pCoreOf_le_nineI (hc : Nine3Choice V T A K S X p g x) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : B ⊓ pCoreOf 2 K ≤ nineI V K := by
  rw [← hc.core.nineI_inf_eq hB]
  exact inf_le_right

theorem nineV1_eq_conj (hc : Nine3Choice V T A K S X p g x) :
    nineV1 V K g = conjSubgroup (A ⊓ pCoreOf 2 K) g := by
  rw [E3.conjSubgroup_inf, hc.A_g]
  rfl

theorem nineW0_le_nineI0 (hc : Nine3Choice V T A K S X p g x) :
    nineW0 V K S g ≤ nineI0 V K g := by
  refine sup_le ?_ (iSup₂_le fun B hB => ?_)
  · rw [hc.nineV1_eq_conj]
    exact (E3.conjSubgroup_mono_left g
      (hc.inf_pCoreOf_le_nineI hc.core.A_mem_nineOmegaIn)).trans le_sup_right
  · exact (hc.inf_pCoreOf_le_nineI hB).trans le_sup_left

theorem conj_inv_nineW0_le (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    conjSubgroup (nineW0 V K S g) g⁻¹ ≤ nineI V K ⊔ V := by
  unfold nineW0
  rw [nineThree_conj_sup, nineThree_conj_iSup']
  refine sup_le ?_ (iSup_le fun B => ?_)
  · rw [hc.nineV1_eq_conj, E3.conjSubgroup_conj_inv]
    exact (hc.inf_pCoreOf_le_nineI hc.core.A_mem_nineOmegaIn).trans le_sup_left
  · rw [nineThree_conj_iSup']
    refine iSup_le fun hB => ?_
    by_cases hBA : B = A
    · rw [hBA]
      have hAV : conjSubgroup A g⁻¹ = V := by
        rw [← hc.V_g, E3.conjSubgroup_conj_inv]
      calc conjSubgroup (A ⊓ pCoreOf 2 K) g⁻¹ ≤ conjSubgroup A g⁻¹ :=
            E3.conjSubgroup_mono_left _ inf_le_left
        _ = V := hAV
        _ ≤ nineI V K ⊔ V := le_sup_right
    · rw [hc.inf_pCoreOf_eq_inf_conj hI hB hBA, E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv]
      have hB' : conjSubgroup B g⁻¹ ∈ nineDelta V S :=
        hc.conj_inv_mem_nineDelta (hc.core.mem_nineDelta_iff.mpr (Or.inr hB))
      have hB'V : conjSubgroup B g⁻¹ ≠ V := by
        intro e
        apply hBA
        have h1 := congrArg (fun C => conjSubgroup C g) e
        simp only [E3.conjSubgroup_inv_conj] at h1
        rw [h1, hc.V_g]
      have hB'Ω : conjSubgroup B g⁻¹ ∈ nineOmegaIn V K S :=
        (hc.core.mem_nineDelta_iff.mp hB').resolve_left hB'V
      exact (hc.inf_pCoreOf_le_nineI hB'Ω).trans le_sup_left

theorem nineW0_le_centralizer_conj (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) :
    nineW0 V K S g ≤ centralizer (conjSubgroup (nineI V K) g : Set G) := by
  have hP : IsElemAbelian 2 (nineI V K ⊔ V) :=
    hI.abelian.sup_of_commute hc.core.hyp7.1 (fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hc.core.nineI_le_centralizer ha) b hb).symm)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : g * z * g⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hz
  have hy' : g * y * g⁻¹ ∈ nineI V K ⊔ V := by
    refine hc.conj_inv_nineW0_le hI ?_
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e]
    exact hy
  have hcomm := hP.comm hy' (Subgroup.mem_sup_left hz')
  have e1 : (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
  have e2 : (g * z * g⁻¹) * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
  rw [e1, e2] at hcomm
  exact (mul_left_cancel (mul_right_cancel hcomm)).symm

theorem nineW0_le_centralizer_nineI0 (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) : nineW0 V K S g ≤ centralizer (nineI0 V K g : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  have h1 := Subgroup.mem_centralizer_iff.mp (hc.nineW0_le_centralizer hI hy)
  have h2 := Subgroup.mem_centralizer_iff.mp (hc.nineW0_le_centralizer_conj hI hy)
  have hle : nineI0 V K g ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (h1 z hz).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (h2 z hz).symm
  intro z hz
  have := Subgroup.mem_centralizer_iff.mp (hle hz) y (Set.mem_singleton y)
  exact this.symm

theorem nineW0_le_center_nineI0 (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    nineW0 V K S g ≤ nineI0 V K g ⊓ centralizer (nineI0 V K g : Set G) :=
  le_inf hc.nineW0_le_nineI0 (hc.nineW0_le_centralizer_nineI0 hI)

private theorem nineThree_A_mem_omegaIn (hc : Nine3Choice V T A K S X p g x) :
    A ∈ omegaIn V K (nineE V K) :=
  ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.A_mem_nineOmegaIn.2.trans hc.core.S_le_K⟩

private theorem nineThree_le_normalizer_nineH {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.normalizer (nineH V K : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hmap : ∀ j : G, conjSubgroup (nineH V K) j =
      ⨆ U ∈ omegaIn V K (nineE V K), conjSubgroup U j := by
    intro j
    unfold nineH
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  apply le_antisymm
  · rw [hmap k]
    exact iSup₂_le fun U hU =>
      le_iSup₂_of_le (conjSubgroup U k) (conjSubgroup_mem_omegaIn hU hk) le_rfl
  · have hle_inv : conjSubgroup (nineH V K) k⁻¹ ≤ nineH V K := by
      rw [hmap k⁻¹]
      exact iSup₂_le fun U hU =>
        le_iSup₂_of_le (conjSubgroup U k⁻¹) (conjSubgroup_mem_omegaIn hU (K.inv_mem hk)) le_rfl
    calc nineH V K = conjSubgroup (conjSubgroup (nineH V K) k⁻¹) k :=
          (E3.conjSubgroup_inv_conj (nineH V K) k).symm
      _ ≤ conjSubgroup (nineH V K) k := E3.conjSubgroup_mono_left k hle_inv

private theorem nineThree_sylow_nineH (hc : Nine3Choice V T A K S X p g x) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ nineH V K) (nineH V K) := by
  have hHK : nineH V K ≤ K := nineH_le_K
  have hHnorm : K ≤ Subgroup.normalizer (nineH V K : Set G) :=
    fun k hk => nineThree_le_normalizer_nineH hk
  have hHnormal : ((nineH V K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr hHnorm
  exact E1.isSylowIn_two_iff.mp
    (hc.core.hyp.base.toTwoPTwo.sylowTwo.inf_normal hHK hHnormal)

private theorem nineThree_nineD_le_nineH (hc : Nine3Choice V T A K S X p g x) :
    nineD K A x ≤ nineH V K := by
  have hxK : x ∈ K := hc.core.hyp.base.toTwoPTwo.sylowP.le hc.x_mem
  refine inf_le_left.trans ?_
  refine iSup₂_le fun r hr => ?_
  have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
  exact le_iSup₂_of_le (conjSubgroup A (x * r))
    (conjSubgroup_mem_omegaIn (nineThree_A_mem_omegaIn hc) (K.mul_mem hxK hrK)) le_rfl

private theorem nineThree_exists_conj_le_S (hc : Nine3Choice V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ∃ h ∈ nineH V K, conjSubgroup U h ≤ S := by
  have hUle : U ≤ nineH V K := le_iSup₂_of_le U hU le_rfl
  have hU2 : IsPGroup 2 U := by
    obtain ⟨y, hy, -, -⟩ := mem_omegaSet.mp hU.1
    rw [hy]
    exact CFSG.Open.IsElemAbelian.isPGroup
      (E3.isElemAbelian_conjSubgroup hc.core.hyp7.1 y)
  obtain ⟨T, hT, hUT⟩ := A4.exists_isSylowTwoOf_ge (P := U) (H := nineH V K) hUle hU2
  obtain ⟨k, hkH, hk⟩ := A4.exists_conj_of_isSylowTwoOf (nineThree_sylow_nineH hc) hT
  refine ⟨k, hkH, ?_⟩
  have hUX : U ≤ conjSubgroup (S ⊓ nineH V K) k⁻¹ := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    simpa using (hk x).mp (hUT hx)
  calc conjSubgroup U k ≤ conjSubgroup (conjSubgroup (S ⊓ nineH V K) k⁻¹) k :=
        E3.conjSubgroup_mono_left k hUX
    _ = S ⊓ nineH V K := E3.conjSubgroup_inv_conj (S ⊓ nineH V K) k
    _ ≤ S := inf_le_left

theorem nineH_transitive (hc : Nine3Choice V T A K S X p g x) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) : ∃ h ∈ nineH V K, U = conjSubgroup A h := by
  obtain ⟨h₀, hh₀, hh₀S⟩ := nineThree_exists_conj_le_S hc hU
  have hh₀K : h₀ ∈ K := nineH_le_K hh₀
  have hBΩ : conjSubgroup U h₀ ∈ nineOmegaIn V K S :=
    ⟨(conjSubgroup_mem_omegaIn hU hh₀K).1, hh₀S⟩
  obtain ⟨d, hdD, hdA⟩ :=
    hc.core.nineD_transitive hc.x_mem hc.x_ne_one hBΩ hc.core.A_mem_nineOmegaIn
  have hdH : d ∈ nineH V K := nineThree_nineD_le_nineH hc hdD
  refine ⟨(h₀ * d)⁻¹, (nineH V K).inv_mem ((nineH V K).mul_mem hh₀ hdH), ?_⟩
  have hconj : A = conjSubgroup U (h₀ * d) :=
    hdA.trans (CFSG.Quasithin.conjSubgroup_conjSubgroup U h₀ d)
  rw [hconj, E3.conjSubgroup_conj_inv]

theorem nineI_le_iSup_conj (hc : Nine3Choice V T A K S X p g x) :
    nineI V K ≤ ⨆ h ∈ nineH V K, conjSubgroup (A ⊓ pCoreOf 2 K) h := by
  refine iSup₂_le fun U hU => ?_
  obtain ⟨h, hh, rfl⟩ := hc.nineH_transitive hU
  have hhK : h ∈ K := nineH_le_K hh
  have e : conjSubgroup A h ⊓ pCoreOf 2 K = conjSubgroup (A ⊓ pCoreOf 2 K) h := by
    rw [E3.conjSubgroup_inf, Nine3Core.conjSubgroup_pCoreOf K hhK]
  rw [e]
  exact le_iSup₂_of_le h hh le_rfl

theorem nineI0_isElemAbelian (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    (hN : nineH0 V K g ≤ normalizer (nineI0 V K g : Set G)) :
    IsElemAbelian 2 (nineI0 V K g) := by
  set Z : Subgroup G := nineI0 V K g ⊓ centralizer (nineI0 V K g : Set G) with hZ
  have hZconj : ∀ h ∈ nineH0 V K g, conjSubgroup Z h = Z := by
    intro h hh
    have hn : conjSubgroup (nineI0 V K g) h = nineI0 V K g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hN hh)
    rw [hZ, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hn]
  have hW : nineW0 V K S g ≤ Z := hc.nineW0_le_center_nineI0 hI
  have hA₀W : A ⊓ pCoreOf 2 K ≤ nineW0 V K S g :=
    le_trans (le_iSup₂_of_le A hc.core.A_mem_nineOmegaIn le_rfl :
      A ⊓ pCoreOf 2 K ≤ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) le_sup_right
  have hV₁W : nineV1 V K g ≤ nineW0 V K S g := le_sup_left
  have hIZ : nineI V K ≤ Z := by
    refine hc.nineI_le_iSup_conj.trans (iSup₂_le fun h hh => ?_)
    have hh0 : h ∈ nineH0 V K g := (le_sup_left : nineH V K ≤ nineH0 V K g) hh
    calc conjSubgroup (A ⊓ pCoreOf 2 K) h ≤ conjSubgroup Z h :=
          E3.conjSubgroup_mono_left h (hA₀W.trans hW)
      _ = Z := hZconj h hh0
  have hIgZ : conjSubgroup (nineI V K) g ≤ Z := by
    refine (E3.conjSubgroup_mono_left g hc.nineI_le_iSup_conj).trans ?_
    rw [nineThree_conj_iSup']
    refine iSup_le fun h => ?_
    rw [nineThree_conj_iSup']
    refine iSup_le fun hh => ?_
    have e : conjSubgroup (conjSubgroup (A ⊓ pCoreOf 2 K) h) g =
        conjSubgroup (nineV1 V K g) (g⁻¹ * h * g) := by
      rw [hc.nineV1_eq_conj, CFSG.Quasithin.conjSubgroup_conjSubgroup,
        CFSG.Quasithin.conjSubgroup_conjSubgroup]
      congr 1
      group
    have hhg : g⁻¹ * h * g ∈ nineH0 V K g := by
      refine (le_sup_right : conjSubgroup (nineH V K) g ≤ nineH0 V K g)
        (mem_conjSubgroup_iff.mpr ?_)
      have e' : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [e']
      exact hh
    rw [e]
    calc conjSubgroup (nineV1 V K g) (g⁻¹ * h * g) ≤ conjSubgroup Z (g⁻¹ * h * g) :=
          E3.conjSubgroup_mono_left _ (hV₁W.trans hW)
      _ = Z := hZconj _ hhg
  have hcomm : ∀ a ∈ nineI0 V K g, ∀ b ∈ nineI0 V K g, a * b = b * a := by
    intro a ha b hb
    have hbZ : b ∈ Z := (sup_le hIZ hIgZ) hb
    exact Subgroup.mem_centralizer_iff.mp hbZ.2 a ha
  exact hI.abelian.sup_of_commute (E3.isElemAbelian_conjSubgroup hI.abelian g)
    (fun a ha b hb => hcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb))

theorem nine_not_exists (hc : Nine3Choice V T A K S X p g x) :
    ¬ ∃ h : G, h ∉ normalizer (V : Set G) ∧ ⁅X, conjSubgroup V h⁆ = ⊥ := by
  rintro ⟨h, hhM, hcomm⟩
  obtain ⟨q, hq, -, hXq, -, hΓ, hcond⟩ := hc.core.hyp.mem
  haveI : Fact q.Prime := ⟨hq⟩
  have hp : p.Prime := hc.core.hyp.base.prime
  have hXcard : Nat.card ↥X = p := hc.core.card
  obtain ⟨n, hn⟩ := hXq.exists_card_eq
  have hqp : q = p := ((Nat.Prime.pow_eq_iff hp).mp (hn.symm.trans hXcard)).1
  rw [hqp] at hΓ
  have hxp : x ^ p = 1 := by
    have h1 : Nat.card ↥(Subgroup.zpowers x) = p := by
      rw [← hc.x_gen]
      exact hXcard
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact pow_orderOf_eq_one x
  have hXel : IsElemAbelian p X := by
    rw [hc.x_gen]
    exact isElemAbelian_zpowers hxp
  have hrank : 1 ≤ CFSG.Open.pRank p X :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hXel (by rw [pow_one]; exact hXcard)
  have hNX : normalizer (X : Set G) ≤ normalizer (V : Set G) := by
    have hle : normalizer (X : Set G) ≤ rankThreeGamma 1 p X := by
      rw [rankThreeGamma, GLBCore]
      exact le_sSup ⟨X, le_rfl, hrank, rfl⟩
    exact hle.trans hΓ
  have hXC : X ≤ centralizer (conjSubgroup V h : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hVX : conjSubgroup V h ≤ centralizer (X : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hcomm)
  have hVh : conjSubgroup V h ≤ normalizer (V : Set G) := fun y hy =>
    hNX (Subgroup.centralizer_le_normalizer _ (hVX hy))
  have hbot := hcond h hhM hVh
  have hXle : X ≤ conjSubgroup (normalizer (V : Set G)) h := by
    rw [E3.conjSubgroup_normalizer]
    exact fun y hy => Subgroup.centralizer_le_normalizer _ (hXC hy)
  have hXbot : X = ⊥ := by
    rw [← inf_eq_left.mpr hXle]
    exact hbot
  have hcard := hXcard
  rw [hXbot, Subgroup.card_bot] at hcard
  exact hp.one_lt.ne hcard

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
