module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Open.StatedAPI
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace P22x

section Basic

theorem proofS_le_M (D : Data G) : proofS D ≤ D.M := inf_le_left.trans D.sylowM.le

theorem jOf_T_le_M (D : Data G) : jOf D.T ≤ D.M :=
  (uc22p22e_jOf_le_self D.T).trans D.sylowM.le

theorem jOf_T_le_proofS (D : Data G) : jOf D.T ≤ proofS D := by
  refine le_inf (uc22p22e_jOf_le_self D.T) (fun j hj => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((uc22p22e_mem_omegaZJ'.1 hz).2.1 j hj).symm

end Basic

section Module

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.conj_natPi (d : NatDec ρ Nbar Nb) (f : ∀ j, ↥(Nb j)) (i : Fin m) {g : X}
    (hg : g ∈ Nb i) : d.natPi f * g * (d.natPi f)⁻¹ = (f i : X) * g * (f i : X)⁻¹ := by
  classical
  let S : Submonoid (∀ j, ↥(Nb j)) :=
    { carrier := {f | ∀ g ∈ Nb i, d.natPi f * g * (d.natPi f)⁻¹ = (f i : X) * g * (f i : X)⁻¹}
      one_mem' := by
        intro g hg
        simp
      mul_mem' := by
        intro f f' hf hf' g hg
        have hg' : (f' i : X) * g * (f' i : X)⁻¹ ∈ Nb i :=
          (Nb i).mul_mem ((Nb i).mul_mem (f' i).2 hg) ((Nb i).inv_mem (f' i).2)
        have h1 := hf _ hg'
        have h2 := hf' g hg
        have e1 : d.natPi (f * f') * g * (d.natPi (f * f'))⁻¹ =
            d.natPi f * (d.natPi f' * g * (d.natPi f')⁻¹) * (d.natPi f)⁻¹ := by
          rw [map_mul]; group
        rw [e1, h2, h1, Pi.mul_apply, Subgroup.coe_mul]
        group }
  have hsingle : ∀ (k : Fin m) (y : ↥(Nb k)), (Pi.mulSingle k y : ∀ j, ↥(Nb j)) ∈ S := by
    intro k y g hg
    rw [d.natPi_mulSingle k y]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Pi.mulSingle_eq_of_ne hik, Subgroup.coe_one, one_mul, inv_one, mul_one]
      have := d.comm (Ne.symm hik) y.2 hg
      rw [this]
      group
  have hS : ∀ f : (∀ j, ↥(Nb j)), f ∈ S := by
    intro f
    rw [← Finset.noncommProd_mulSingle f]
    exact Submonoid.noncommProd_mem S _ _ _ fun k _ => hsingle k (f k)
  exact hS f g hg

theorem NatDec.natPi_decomp (d : NatDec ρ Nbar Nb) (f : ∀ j, ↥(Nb j)) (i : Fin m) :
    ∃ r ∈ (⨆ j ∈ {j | j ≠ i}, Nb j), d.natPi f = (f i : X) * r := by
  classical
  refine ⟨d.natPi (Function.update f i 1), ?_, ?_⟩
  · let S : Subgroup (∀ j, ↥(Nb j)) := (⨆ j ∈ {j | j ≠ i}, Nb j).comap d.natPi
    have hmem : ∀ f' : (∀ j, ↥(Nb j)), f' i = 1 → f' ∈ S := by
      intro f' hf'
      rw [← Finset.noncommProd_mulSingle f']
      refine Subgroup.noncommProd_mem S _ fun k _ => ?_
      by_cases hki : k = i
      · subst hki
        rw [hf', Pi.mulSingle_one]
        exact S.one_mem
      · show d.natPi (Pi.mulSingle k (f' k)) ∈ (⨆ j ∈ {j | j ≠ i}, Nb j)
        rw [d.natPi_mulSingle]
        exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem hki (f' k).2)
    exact hmem _ (by simp)
  · have hf : f = Pi.mulSingle i (f i) * Function.update f i 1 := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    calc d.natPi f = d.natPi (Pi.mulSingle i (f i) * Function.update f i 1) := by rw [← hf]
      _ = (f i : X) * d.natPi (Function.update f i 1) := by rw [map_mul, d.natPi_mulSingle]

end Module

section Data

variable {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]

theorem proj_relIndex_odd (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (d : NatDec ρ (mbarImage D.M D.U (proofN D)) Nb)
    (i : Fin m) : ¬ 2 ∣ (d.proj i (mbarImage D.M D.U (jOf D.T))).relIndex (Nb i) := by
  intro hdvd
  have hV := uc22p22xf_hV D
  obtain ⟨A', hmax, hne⟩ := NatDec.exists_isMax_proj_ne_bot D d i
  have hA'M : A' ≤ D.M := hmax.1.trans D.sylowM.le
  have hA'J := le_jOf_of_isMax hmax
  have hA'N : A' ≤ proofN D := hA'J.trans (uc22p22e_jOf_le D.sylowM)
  have hAb : mbarImage D.M D.U A' ≤ mbarImage D.M D.U (proofN D) := mbarImage_mono D.M D.U hA'N
  have hAbp : IsPGroup 2 (mbarImage D.M D.U A') :=
    ((uc22p22e_isPGroup_of_elem hmax.2.1).comap_subtype (K := D.M)).map _
  have hoff : Nat.card Umod ≤ Nat.card (mbarImage D.M D.U A') *
      Nat.card (fixSub ρ (mbarImage D.M D.U A')) := by
    rw [← relIndex_mul_card_fixSub D e ρ hc hA'M, uc22br4_card_mbarImage D.M D.U _ hV hA'M]
    exact Nat.mul_le_mul_right _
      (uc22p22xf_relIndex_le (uc22p22xf_UleT D) (uc22p22xf_hel D) hmax)
  obtain ⟨-, hsyl⟩ := d.offender_eq hAb hAbp hoff
  have hP : ¬ 2 ∣ (d.proj i (mbarImage D.M D.U A')).relIndex (Nb i) :=
    (hsyl i).resolve_left hne
  exact hP (hdvd.trans (Subgroup.relIndex_dvd_of_le_left (Nb i)
    (d.proj_mono i (mbarImage_mono D.M D.U hA'J))))

theorem fix_of_centralizes_E (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ) {x : G}
    (hxM : x ∈ D.M) (hxE : ∀ z ∈ proofE D, x * z * x⁻¹ = z) {v : Umod}
    (hv : v ∈ fixSub ρ (mbarImage D.M D.U (jOf D.T))) :
    ρ (QuotientGroup.mk ⟨x, hxM⟩) v = v := by
  have hV := uc22p22xf_hV D
  rw [fixSub_mbarImage hV e ρ hc (jOf_T_le_M D)] at hv
  have hz : iota e v ∈ centralizer ((jOf D.T : Subgroup G) : Set G) := mem_bsub.1 hv
  have hzE : iota e v ∈ proofE D :=
    uc22p22e_mem_omegaZJ'.2 ⟨uc22p22xf_UleT D (iota_mem e v),
      fun j hj => Subgroup.mem_centralizer_iff.1 hz j hj, (uc22p22xf_hel D).2 _ (iota_mem e v)⟩
  apply iota_injective e
  rw [iota_rho hV e ρ hc ⟨x, hxM⟩ v]
  exact hxE _ hzE

theorem core25 (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (d : NatDec ρ (mbarImage D.M D.U (proofN D)) Nb)
    (i : Fin m) {s : G} (hs : s ∈ proofS D) (hsM : s ∈ D.M) :
    (∀ h ∈ Nb i, (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) * h *
        (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U)⁻¹ ∈ Nb i) ∧
      ∃ f : ∀ j, ↥(Nb j), d.natPi f ∈ mbarImage D.M D.U (jOf D.T) ∧
        (∀ y ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i),
          ρ (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) y = ρ (d.natPi f) y) ∧
        ∀ g ∈ Nb i, (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) * g *
          (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U)⁻¹ = d.natPi f * g * (d.natPi f)⁻¹ := by
  classical
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  have hQN : Q ≤ Nbar := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hQ2 : IsPGroup 2 Q :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  have himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w :=
    fun w hw hwC a ha => uc22p22xf_imgEI_of D Ch h2 h3 h51 hH c Umod e ρ hc w hw hwC a ha
  have ht := mem_normalizer_mbarImage D hsM
  have hsE : ∀ z ∈ proofE D, s * z * s⁻¹ = z := fun z hz => by
    have h := Subgroup.mem_centralizer_iff.1 hs.2 z hz
    calc s * z * s⁻¹ = z * s * s⁻¹ := by rw [h]
      _ = z := by group
  have hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) v = v :=
    fun v hv => fix_of_centralizes_E D e ρ hc hsM hsE hv.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup ⟨s, hs.1⟩
    refine ⟨k, ?_⟩
    have h1 : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (⟨s, hsM⟩ : ↥D.M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using h1)
    rw [← QuotientGroup.mk_pow, h2]
    rfl
  obtain ⟨hA, q, hqP, hqI, hqN⟩ :=
    d.lemma25 i hQN hQ2 (proj_relIndex_odd D e ρ hc d i) himg ht hfix hk
  obtain ⟨f, hfQ, hfq⟩ := (d.mem_proj i).1 hqP
  refine ⟨hA, f, hfQ, fun y hy => ?_, fun g hg => ?_⟩
  · rw [hqI y hy, ← hfq, ← d.pi_act f i hy]
  · rw [hqN g hg, ← hfq]
    exact (d.conj_natPi f i hg).symm

end Data

end P22x

open P22x

theorem uc22p22x_lemma25 (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) {s : G}
    (hs : s ∈ proofS D) :
    (∀ h ∈ Nb i, (QuotientGroup.mk ⟨s, proofS_le_M D hs⟩ : MBar D.M D.U) * h *
        (QuotientGroup.mk ⟨s, proofS_le_M D hs⟩ : MBar D.M D.U)⁻¹ ∈ Nb i) ∧
      ∃ (a : G) (ha : a ∈ jOf D.T) (q r : MBar D.M D.U), q ∈ Nb i ∧ r ∈ (⨆ j ∈ {j | j ≠ i}, Nb j) ∧
        (QuotientGroup.mk ⟨a, jOf_T_le_M D ha⟩ : MBar D.M D.U) = q * r ∧
        (∀ y ∈ proofIi D (preN D (Nb i)), s * y * s⁻¹ = a * y * a⁻¹) ∧
        ∀ g ∈ Nb i, (QuotientGroup.mk ⟨s, proofS_le_M D hs⟩ : MBar D.M D.U) * g *
          (QuotientGroup.mk ⟨s, proofS_le_M D hs⟩ : MBar D.M D.U)⁻¹ = q * g * q⁻¹ := by
  classical
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  obtain ⟨hA, f, hfQ, hfI, hfN⟩ := core25 D Ch h2 h3 h51 hH c e ρ hc d i hs (proofS_le_M D hs)
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hfQ
  have hae : (QuotientGroup.mk ⟨(a₀ : G), jOf_T_le_M D ha₀⟩ : MBar D.M D.U) = d.natPi f := ha₀eq
  obtain ⟨r, hr, hqr⟩ := d.natPi_decomp f i
  refine ⟨hA, (a₀ : G), ha₀, ((f i : ↥(Nb i)) : MBar D.M D.U), r, (f i).2, hr, hae.trans hqr,
    fun y hy => ?_, fun g hg => ?_⟩
  · have hyU : y ∈ D.U := proofIi_le D (preN_le_M D (Nb i)) hy
    obtain ⟨u, rfl⟩ := exists_iota e hyU
    have hu : u ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i) := by
      have := mem_bsub.2 hy
      rwa [bsub_proofIi D e ρ hc (d.le i)] at this
    have h1 := iota_rho hV e ρ hc ⟨s, proofS_le_M D hs⟩ u
    have h2 := iota_rho hV e ρ hc a₀ u
    rw [← h1, ← h2]
    congr 1
    rw [hfI u hu]
    exact congrArg (fun z => ρ z u) hae.symm
  · rw [hfN g hg]
    exact d.conj_natPi f i hg

theorem uc22p22x_S_normalizes (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) {s : G}
    (hs : s ∈ proofS D) :
    (QuotientGroup.mk ⟨s, proofS_le_M D hs⟩ : MBar D.M D.U) ∈
        normalizer ((Nb i : Subgroup (MBar D.M D.U)) : Set (MBar D.M D.U)) ∧
      s ∈ normalizer ((preN D (Nb i) : Subgroup G) : Set G) ∧
      s ∈ normalizer ((proofIi D (preN D (Nb i)) : Subgroup G) : Set G) := by
  have hsM := proofS_le_M D hs
  have hs' : s⁻¹ ∈ proofS D := (proofS D).inv_mem hs
  have hfwd := (uc22p22x_lemma25 D Ch h2 h3 h51 hH c m Nb hNb i hs).1
  have hbwd := (uc22p22x_lemma25 D Ch h2 h3 h51 hH c m Nb hNb i hs').1
  have h1 : (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U) ∈
      normalizer ((Nb i : Subgroup (MBar D.M D.U)) : Set (MBar D.M D.U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have := hbwd _ hh
    have e : (QuotientGroup.mk ⟨s⁻¹, proofS_le_M D hs'⟩ : MBar D.M D.U) =
        (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U)⁻¹ := rfl
    rw [e] at this
    simpa [mul_assoc] using this
  have hU : s ∈ normalizer (D.U : Set G) := uc22p22xf_hV D hsM
  have hN : s ∈ normalizer ((proofN D : Subgroup G) : Set G) :=
    uc22p22t_M_le_normalizer_jOf D hsM
  have hNi : s ∈ normalizer ((preN D (Nb i) : Subgroup G) : Set G) :=
    mem_normalizer_inf hN (mem_normalizer_preMbar D hsM h1)
  exact ⟨h1, hNi, mem_normalizer_commutator (mem_normalizer_commutator hU hN) hNi⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
