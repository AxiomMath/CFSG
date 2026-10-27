module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGPZMultD4
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_ggAutomizer_le_of_innerDiagOn_D4
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p = 3) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs) (hInn : GGInnerDiagOn Bs J)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJlabel : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .D) (hrank : labJ.rank = 4)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hA3 : p ^ 3 ≤ Nat.card ↥(ggGamma J hN).range) :
    Nat.card ↥(ggAutomizer J Bs) ≤ 384 := by
  classical
  subst hp
  have hJperf : commutator ↥J = ⊤ := hInn.1
  have hJfin : Finite ↥J := Subtype.finite
  obtain ⟨-, lab1, hΛ1, hraw1legacy⟩ := hInn
  have hraw1 : LargeEvenRawDatum lab1 _ := (largeEvenRawDatum_legacy lab1 _).mpr hraw1legacy
  have hlab1 : GGHasLabel lab1 (↥J ⧸ Subgroup.center ↥J) :=
    largeEvenRawDatum_mono (fun R _ _ _ h => ⟨h.2.2.choose⟩) hraw1
  have hiso : GGLabelIso lab1 labJ := hRig lab1 labJ (↥J ⧸ Subgroup.center ↥J) hΛ1 hJΛ hlab1 hJlabel
  have hlab1eq : lab1 = labJ := by
    obtain ⟨t, r, n⟩ := lab1
    obtain ⟨t', r', n'⟩ := labJ
    simp only at htag hrank
    subst htag
    subst hrank
    unfold GGLabelIso at hiso
    rcases hiso with h | h | h | h | h | h | h | h <;> simp_all
  subst lab1
  unfold LargeEvenRawDatum at hraw1
  simp only [htag, hrank] at hraw1
  obtain ⟨K, hfield, hfinite, hKcard, hQraw⟩ := hraw1
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : CharP K 2 := charP_two_of_card hKcard
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))
  letI : Group R := inferInstance
  letI : Finite R := inferInstance
  rcases hQraw with ⟨hsimple, hnonab, θ, hBN, h3⟩
  have hZ : Subgroup.center R = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hI : LargeEvenInnSet R ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
    intro φ hφ
    exact hφ
  have hthree : 3 ∣ 2 ^ labJ.n - 1 ∨ 3 ∣ 2 ^ labJ.n + 1 := by
    have h2 : (2 : ZMod 3) = -1 := by
      have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      calc (2 : ZMod 3) = (3 : ZMod 3) - 1 := by ring
        _ = 0 - 1 := by rw [h3]
        _ = -1 := by ring
    have hpar : (2 : ZMod 3) ^ labJ.n = 1 ∨ (2 : ZMod 3) ^ labJ.n = -1 := by
      rcases Nat.even_or_odd labJ.n with hn | hn
      · left; simpa [h2] using hn.neg_one_pow
      · right; simpa [h2] using hn.neg_one_pow
    rcases hpar with h | h
    · left
      have hcast : ((2 ^ labJ.n : ℕ) : ZMod 3) = 1 := by
        simpa [Nat.cast_pow] using h
      have hmod : 2 ^ labJ.n ≡ 1 [MOD 3] :=
        (ZMod.natCast_eq_natCast_iff (2 ^ labJ.n) 1 3).mp hcast
      exact (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt
        (pow_pos (by norm_num : 0 < 2) labJ.n))).mp hmod.symm
    · right
      have hcast : ((2 ^ labJ.n : ℕ) : ZMod 3) = -1 := by
        simpa [Nat.cast_pow] using h
      have hzero : ((2 ^ labJ.n + 1 : ℕ) : ZMod 3) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hcast]
        ring
      exact (ZMod.natCast_eq_zero_iff (2 ^ labJ.n + 1) 3).mp hzero
  have hcond : 3 ∣ Nat.card K - 1 ∨ (Even 4 ∧ 3 ∣ Nat.card K + 1) := by
    rw [hKcard]
    rcases hthree with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by norm_num, h⟩
  have hT : GGTorusEvenSignedPermEltSC 3 R (fun k => k = 4) := by
    have hT0 := ggOrthEvenTorusInput_holds.1 K 4 3 (by norm_num) Nat.prime_three hcond
    simpa [R, OrthRest.RPlus] using hT0
  have hcp : GGCenterPrime 3 R := by
    simpa [R, OrthRest.RPlus] using
      (CorFourTwoOpen.ggCenterPrime_omegaPlus (p := 3) (m := 4)
        Nat.prime_three (by norm_num) (by norm_num))
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let H : Subgroup (MulAut ↥J) := (MulAut.conj : ↥J →* MulAut ↥J).range
  have hA : IsElemAbelian 3 A :=
    isElemAbelian_range_of_isElemAbelian hBs (ggGamma J hN)
  have hscA : GGTorusSelfCent 3 A := ggTorusSelfCent_ggGamma hN hSC
  have hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenInnSet R, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN h3 b,
      fun l => ggBeta_ggQuotHom (L := J) (B := Bs) (hBN := hN) (θ := θ) b l⟩
  obtain ⟨k, Θ, hk3, hk4, -, -, -, -, hsigned⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC (p := 3) (R := R)
      (I := LargeEvenInnSet R) Nat.prime_three (by norm_num) hI hZ hcp hT
      (ψ := ggQuotHom θ) (ggQuotHom_surjective θ) (le_of_eq (ker_ggQuotHom θ)) hJperf
      hA hAI hA3 hscA
  subst hk4
  let e : MulAut A ≃* MulAut (Fin 4 → Multiplicative (ZMod 3)) :=
    (MulAut.congr Θ).symm
  have hgen : ∀ φ ∈ ggInduced H A, SpCoord.IsSignedPerm (⇑(e φ)) := by
    rintro φ ⟨g, hg, hgN, hφeq⟩
    obtain ⟨n, rfl⟩ := hg
    have hφconj : φ = ggConjAut A hgN := by
      ext b : 1
      exact Subtype.ext (by simpa [ggConjAut_apply] using hφeq b)
    rw [hφconj]
    exact hsigned n hgN
  have hmap_le : (ggAutomizer H A).map e.toMonoidHom ≤
      SignedPermCount.signedPermSubgroup 3 4 := by
    rw [ggAutomizer, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, rfl⟩
    exact hgen φ hφ
  have hcard_map : Nat.card ↥((ggAutomizer H A).map e.toMonoidHom) =
      Nat.card ↥(ggAutomizer H A) :=
    Subgroup.card_map_of_injective e.injective
  have hcard_le : Nat.card ↥(ggAutomizer H A) ≤ 384 := by
    calc Nat.card ↥(ggAutomizer H A)
        = Nat.card ↥((ggAutomizer H A).map e.toMonoidHom) := hcard_map.symm
      _ ≤ Nat.card ↥(SignedPermCount.signedPermSubgroup 3 4) :=
          Subgroup.card_le_of_le hmap_le
      _ = 384 := by
          rw [SignedPermCount.card_signedPermSubgroup (p := 3) (k := 4)
            Nat.prime_three (by norm_num)]
          norm_num
  have hZcenter : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
    have hlabJ : labJ = ⟨.D, 4, labJ.n⟩ := by
      rcases labJ with ⟨t, r, n⟩
      simp only at htag hrank
      subst htag
      subst hrank
      rfl
    have hJΛD : LargeEvenInLambda2 ⟨.D, 4, labJ.n⟩ := hlabJ ▸ hJΛ
    have hJlabelD : GGHasLabel ⟨.D, 4, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) :=
      hlabJ ▸ hJlabel
    have hZJ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥J) :=
      ggPZMult_D4 hJΛD hJperf hJlabelD
    have hle : (Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ J :=
      inf_le_left.trans inf_le_right
    let E : Subgroup ↥J := (Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)).subgroupOf J
    have hEcenter : E ≤ Subgroup.center ↥J := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hxC : ((x : ↥J) : G) ∈ Subgroup.centralizer (J : Set G) :=
        (Subgroup.mem_subgroupOf.mp hx).2
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2
      simpa using hcomm
    have hE3 : IsPGroup 3 E := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (((x : E) : ↥J) : G) ^ 3 = 1
      exact hBs.2 (((x : E) : ↥J) : G)
        (Subgroup.mem_subgroupOf.mp x.2).1.1
    have hcardE : Nat.card E = Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [← hcardE]
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hE3
    have hnot3 : ¬ 3 ∣ Nat.card E := fun hd =>
      hZJ (hd.trans (Subgroup.card_dvd_of_le hEcenter))
    have hk0 : k = 0 := by
      by_contra hk0
      exact hnot3 (by rw [hk]; exact dvd_pow_self 3 hk0)
    rw [hk, hk0]
    norm_num
  have hdiv : Nat.card ↥(ggAutomizer J Bs) ∣ Nat.card ↥(ggAutomizer H A) :=
    card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN hZcenter
  exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hcard_le

end CFSG.StandardType

end
