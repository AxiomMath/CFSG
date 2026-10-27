module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenHyp139N3Faithful

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.lemmaD (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    (hC : DNormComp G D) {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    (hKD : ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W))) :
    ⁅K, D⁆ = K ∧ ∀ e ∈ D, (∀ k ∈ K, e * k = k * e) → e = 1 := by
  have hnot : ¬ ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := by
    intro h
    apply hKD
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (h k hk d hd).symm
  obtain ⟨k, hkimp⟩ := not_forall.mp hnot
  obtain ⟨hkK, hnotd⟩ := not_imp.mp hkimp
  obtain ⟨d₀, hdimp⟩ := not_forall.mp hnotd
  obtain ⟨hd₀, hne⟩ := not_imp.mp hdimp
  have hcomm_ne : ⁅k, d₀⁆ ≠ 1 := by
    intro h
    exact hne (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hmem : ⁅k, d₀⁆ ∈ ⁅K, Subgroup.zpowers d₀⁆ :=
    Subgroup.commutator_mem_commutator (H₁ := K) (H₂ := Subgroup.zpowers d₀)
      hkK (Subgroup.mem_zpowers d₀)
  have hNne : ⁅K, Subgroup.zpowers d₀⁆ ≠ ⊥ := by
    intro hbot
    exact hcomm_ne (Subgroup.mem_bot.mp (hbot ▸ hmem))
  have hLinv : ∀ d ∈ D, K.map (MulAut.conj d).toMonoidHom = K := hC K hK
  have hKcomm : ⁅K, Subgroup.zpowers d₀⁆ = K :=
    comm_eq_self_of_component hK (hLinv d₀ hd₀) hNne
  have hmono : ⁅K, Subgroup.zpowers d₀⁆ ≤ ⁅K, D⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hd₀)
  have hle : K ≤ ⁅K, D⁆ := (le_of_eq hKcomm.symm).trans hmono
  have hDnorm : D ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    fun d hd => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLinv d hd)
  have hge : ⁅K, D⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hDnorm
  have hcomm : ⁅K, D⁆ = K := le_antisymm hge hle
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  haveI : Nontrivial ↥K :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  have hKne : K ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥K := by rw [hbot]; infer_instance
    exact false_of_nontrivial_of_subsingleton ↥K
  have hfaith : ∀ e ∈ D, (∀ k ∈ K, e * k = k * e) → e = 1 :=
    sixfourteen_n3_D_faithful_on_L_rel hw2 S.isK S.o2 S.irr S.cost S.XG S.Xnorm S.Xcard
      S.sG S.s2 S.s_not_cent S.Yinv S.Yrk S.card S.DG S.DX S.Dcs S.elem S.Dcard S.YD
      (by omega) K hK.1 hKne hK.2.1 hcomm hLinv
  exact ⟨hcomm, hfaith⟩

theorem transvectionBound (hw2 : ∀ w : W, w ^ 2 = 1) (D : Subgroup (MulAut W))
    (U₀ A : Subgroup W) (hAU : A ≤ U₀) (hidx : E3.mQuot U₀ A = 1)
    (hU : ∀ e ∈ D, ∀ u ∈ U₀, e u ∈ U₀) (hfaith : ∀ e ∈ D, (∀ u ∈ U₀, e u = u) → e = 1)
    (h1 : ∀ e ∈ D, ∀ u ∈ U₀, e u * u⁻¹ ∈ A) (h2 : ∀ e ∈ D, ∀ a ∈ A, e a = a) :
    Nat.card D ≤ Nat.card A := by
  have hV : IsPGroup 2 U₀ := (isPGroup_two_of_sq_eq_one hw2).to_subgroup U₀
  have hrel : A.relIndex U₀ = 2 := by
    rw [E3.relIndex_eq_two_pow hV A, hidx, pow_one]
  have hI : (A.subgroupOf U₀).index = 2 := hrel
  have hAUne : A ≠ U₀ := by
    intro h
    have h0 : E3.mQuot U₀ A = 0 := by rw [h, E3.mQuot_self]
    omega
  have hAlt : A < U₀ := lt_of_le_of_ne hAU hAUne
  have hnot : ¬ (U₀ : Set W) ⊆ (A : Set W) := by
    intro hsub
    exact hAUne (le_antisymm hAU (fun x hx => hsub hx))
  obtain ⟨u₀, hu₀U, hu₀A⟩ := Set.not_subset.mp hnot
  let f : ↥D → ↥A := fun e => ⟨e.1 u₀ * u₀⁻¹, h1 e.1 e.2 u₀ hu₀U⟩
  have hf : Function.Injective f := by
    intro e e' hee
    have hval : e.1 u₀ * u₀⁻¹ = e'.1 u₀ * u₀⁻¹ := by
      simpa [f] using congrArg Subtype.val hee
    have huu : e.1 u₀ = e'.1 u₀ := mul_right_cancel hval
    have hfixu : (e.1⁻¹ * e'.1) u₀ = u₀ := by
      simp only [MulAut.mul_apply]
      rw [← huu, MulAut.inv_apply_self]
    have hfixA : ∀ a ∈ A, (e.1⁻¹ * e'.1) a = a := by
      intro a ha
      calc (e.1⁻¹ * e'.1) a = e.1⁻¹ (e'.1 a) := rfl
        _ = e.1⁻¹ a := by rw [h2 e'.1 e'.2 a ha]
        _ = e.1⁻¹ (e.1 a) := by rw [h2 e.1 e.2 a ha]
        _ = a := MulAut.inv_apply_self W e.1 a
    have hfixU0 : ∀ u ∈ U₀, (e.1⁻¹ * e'.1) u = u := by
      intro u hu
      by_cases huA : u ∈ A
      · exact hfixA u huA
      · have hprod : u * u₀⁻¹ ∈ A := by
          have hiff : ((⟨u, hu⟩ : ↥U₀) ∈ A.subgroupOf U₀ ↔
              (⟨u₀⁻¹, U₀.inv_mem hu₀U⟩ : ↥U₀) ∈ A.subgroupOf U₀) := by
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            exact iff_of_false huA (fun h => hu₀A (by simpa using A.inv_mem h))
          have hmem : (⟨u, hu⟩ : ↥U₀) * (⟨u₀⁻¹, U₀.inv_mem hu₀U⟩ : ↥U₀) ∈
              A.subgroupOf U₀ :=
            (Subgroup.mul_mem_iff_of_index_two (H := A.subgroupOf U₀) hI).mpr hiff
          exact Subgroup.mem_subgroupOf.mp hmem
        calc (e.1⁻¹ * e'.1) u
            = (e.1⁻¹ * e'.1) ((u * u₀⁻¹) * u₀) := by
              rw [show (u * u₀⁻¹) * u₀ = u from by group]
          _ = (e.1⁻¹ * e'.1) (u * u₀⁻¹) * (e.1⁻¹ * e'.1) u₀ := by rw [map_mul]
          _ = (u * u₀⁻¹) * u₀ := by rw [hfixA (u * u₀⁻¹) hprod, hfixu]
          _ = u := by group
    have hm : e.1⁻¹ * e'.1 = 1 :=
      hfaith (e.1⁻¹ * e'.1) (D.mul_mem (D.inv_mem e.2) e'.2) hfixU0
    have heq : e'.1 = e.1 := by
      have h := congrArg (fun g : MulAut W => e.1 * g) hm
      simpa [mul_assoc] using h
    exact Subtype.ext heq.symm
  exact Nat.card_le_card_of_injective f hf

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
