module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Helpers

private theorem s15_semiBot_conj_perfect {W : Type*} [Group W] {K : Subgroup W}
    (hK : Group.IsPerfect ↥K) (n : W) :
    Group.IsPerfect ↥(K.map (MulAut.conj n).toMonoidHom) := by
  haveI := hK
  exact Group.IsPerfect.map (H := K) (f := (MulAut.conj n).toMonoidHom)

private theorem s15_semiBot_no_two_quotient_of_perfect {W : Type*} [CommGroup W] [Finite W]
    {Q : Subgroup (MulAut W)} (hQ : Group.IsPerfect ↥Q) :
    ∀ N : Subgroup Q, N.Normal → (∃ k : ℕ, N.index = 2 ^ k) → N = ⊤ := by
  intro N hN hk
  obtain ⟨k, hk⟩ := hk
  haveI := hN
  haveI := hQ
  by_contra hNtop
  haveI : Nontrivial (↥Q ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (↥Q ⧸ N) = 2 ^ k := by
    rw [← Subgroup.index_eq_card, hk]
  have hpg : IsPGroup 2 (↥Q ⧸ N) := IsPGroup.of_card (p := 2) hcard
  haveI : Group.IsNilpotent (↥Q ⧸ N) := hpg.isNilpotent
  exact (Group.IsPerfect.not_isSolvable (↥Q ⧸ N))
    (inferInstance : Group.IsSolvable (↥Q ⧸ N))

end Helpers

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_commSub_top_iSup_component (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {K : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hK : IsComponentOf K (barSub V₀ V h.isElemAbelian L)) :
    commSub ⊤ (⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      K.map (MulAut.conj φ).toMonoidHom) = ⊤ := by
  have hV := h.isElemAbelian
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  have hKM : K ≤ Mb := hK.1.trans (barSub_mono V₀ V hV h.le)
  have hKne : K ≠ ⊥ := by
    intro hKbot
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
    haveI : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by rw [hKbot]; infer_instance
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (↥K ⧸ Subgroup.center ↥K))
    exact hab (Subsingleton.elim a b)
  let X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ φ ∈ Mb, K.map (MulAut.conj φ).toMonoidHom
  change commSub ⊤ X = ⊤
  have hKX : K ≤ X := by
    have h1 : K.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom ≤ X :=
      le_iSup₂ (f := fun φ (_ : φ ∈ Mb) => K.map (MulAut.conj φ).toMonoidHom)
        (1 : MulAut (Vtil V₀ V hV)) (Subgroup.one_mem Mb)
    have h2 : K.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom = K := by
      rw [map_one MulAut.conj]
      exact Subgroup.map_id K
    rwa [h2] at h1
  have hXne : X ≠ ⊥ := fun hbot => hKne (le_bot_iff.mp (hKX.trans (le_of_eq hbot)))
  have hXM : X ≤ Mb := by
    refine iSup₂_le fun φ hφ => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    rw [Subgroup.mem_comap]
    have hkMb : k ∈ Mb := hKM hk
    have hm : φ * k * φ⁻¹ ∈ Mb := Mb.mul_mem (Mb.mul_mem hφ hkMb) (Mb.inv_mem hφ)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hm
  have hXnorm : (X.subgroupOf Mb).Normal := by
    have h1 := s15_semiBot_iSup_map_conj_normal (K := K) (B := Mb) hKM
    rw [show X =
      ⨆ φ : Mb, K.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom
      from (iSup_subtype'' (Mb : Set (MulAut (Vtil V₀ V hV)))
        (fun φ => K.map (MulAut.conj φ).toMonoidHom)).symm]
    exact h1
  have hKcomp : K ∈ compBar D.M V₀ V hV := s15_semiBot_mem_compBar_of_isComponentOf h hK
  have hspan := h1217 V₀ V h.hyp125 X hXne hXM hXnorm (Or.inr ⟨K, hKcomp, rfl⟩)
  refine le_antisymm le_top ?_
  conv_lhs => rw [← hspan]
  refine iSup₂_le fun I hI => ?_
  rw [← hI.1]
  exact commSub_mono le_top le_rfl

theorem s15_semiBot_commSub_wTil_classSum (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {K : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hK : IsComponentOf K (barSub V₀ V h.isElemAbelian L)) :
    commSub (wTil V₀ V h.isElemAbelian L)
        (⨆ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
            normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
          K.map (MulAut.conj n).toMonoidHom) =
      wTil V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let Nb : Subgroup (MulAut (Vtil V₀ V hV)) := Mb ⊓ normalizer (Lb : Set _)
  let Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
  let B : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ n ∈ Nb, K.map (MulAut.conj n).toMonoidHom
  change commSub Wt B = Wt
  have hKperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.2.2.1
  have hspan := s15_semiBot_commSub_top_iSup_component h1217 h hK
  have hwit : Wt = ⨆ n ∈ Nb, commSub ⊤ (K.map (MulAut.conj n).toMonoidHom) :=
    s15_semiBot_wTil_eq_iSup_of_span (h := h) (Y := K) hK.1 hspan
  have hmapLb : ∀ n : MulAut (Vtil V₀ V hV), n ∈ normalizer (Lb : Set _) →
      K.map (MulAut.conj n).toMonoidHom ≤ Lb := by
    intro n hn
    rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    rw [Subgroup.mem_comap]
    have hkL : k ∈ Lb := hK.1 hk
    have hm : n * k * n⁻¹ ∈ Lb := (Subgroup.mem_set_normalizer_iff.1 hn k).mp hkL
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hm
  have hBL : B ≤ Lb := by
    refine iSup₂_le fun n hn => ?_
    exact hmapLb n hn.2
  have hle : commSub Wt B ≤ Wt := by
    calc commSub Wt B ≤ commSub Wt Lb := commSub_mono le_rfl hBL
      _ ≤ Wt := by
        rw [show Wt = commSub ⊤ Lb from rfl]
        exact commSub_le_of_invariant fun x hx w hw =>
          commSub_top_stable151b (X := Lb) (g := x)
            (fun θ hθ => Lb.mul_mem (Lb.mul_mem hx hθ) (Lb.inv_mem hx)) w hw
  refine le_antisymm hle ?_
  rw [hwit]
  refine iSup₂_le fun n hn => ?_
  have hUn : commSub ⊤ (K.map (MulAut.conj n).toMonoidHom) ≤
      ⨆ m ∈ Nb, commSub ⊤ (K.map (MulAut.conj m).toMonoidHom) :=
    le_iSup₂ (f := fun m (_ : m ∈ Nb) => commSub ⊤ (K.map (MulAut.conj m).toMonoidHom)) n hn
  have hQleL : K.map (MulAut.conj n).toMonoidHom ≤ Lb := hmapLb n hn.2
  have hQleB : K.map (MulAut.conj n).toMonoidHom ≤ B :=
    le_iSup₂ (f := fun m (_ : m ∈ Nb) => K.map (MulAut.conj m).toMonoidHom) n hn
  have hperf : commSub (commSub ⊤ (K.map (MulAut.conj n).toMonoidHom))
        (K.map (MulAut.conj n).toMonoidHom) =
      commSub ⊤ (K.map (MulAut.conj n).toMonoidHom) :=
    s15_Lin_commSub_commSub_eq_of_no_two_quotient (W := Vtil V₀ V hV)
      (X := K.map (MulAut.conj n).toMonoidHom)
      (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (s15_semiBot_no_two_quotient_of_perfect (W := Vtil V₀ V hV)
        (Q := K.map (MulAut.conj n).toMonoidHom)
        (s15_semiBot_conj_perfect (W := MulAut (Vtil V₀ V hV)) (K := K) hKperf n))
  calc commSub ⊤ (K.map (MulAut.conj n).toMonoidHom)
      = commSub (commSub ⊤ (K.map (MulAut.conj n).toMonoidHom))
          (K.map (MulAut.conj n).toMonoidHom) := hperf.symm
    _ ≤ commSub (⨆ m ∈ Nb, commSub ⊤ (K.map (MulAut.conj m).toMonoidHom)) B :=
        commSub_mono hUn hQleB

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
