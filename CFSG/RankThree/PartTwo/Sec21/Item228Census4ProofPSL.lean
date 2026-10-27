module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofLin
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofStar
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSL projImage)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars)

open Matrix

namespace Item228Census4Proof

section TypeTwo

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem type2_of_le_centMod (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K}
    (hxH : x ∈ Sec4.glPi π 3 (p ^ f) K) (hxZ : x ∉ Sec4.zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ Sec4.zPi π 3 (p ^ f) K) {M : Subgroup (GL (Fin 3) K)}
    (hM : M ≤ Sec4.centMod (Sec4.slPi π 3 (p ^ f) K) x) {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (ψ : M →* Q) (hψ : Function.Surjective ψ) (hQ : ∃ a b : Q, a * b ≠ b * a) :
    Sec4.Type123 π (p ^ f) K x 2 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by
    subst h
    exact hq
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := Sec4.rank3II_4_10_one hK hq hτ hτ1 hxH hxZ hx3
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    have hz' := hz
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz'
    exact hz'.2
  rw [← centMod_mul_scalar _ x hzS] at hM
  set C := Sec4.slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {x * z} with hC
  have hder : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ C := fun a ha b hb =>
    commutator_mem_of_mem_centMod (hM ha) (hM hb)
  rcases hcase with ⟨-, ⟨φ⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, -⟩ | ⟨-, -, -, hcyc, -⟩
  · exfalso
    refine false_of_commutator_mem (C := C) (fun a ha b hb => ?_) hder ψ hψ hQ
    have h := φ.injective (show φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) by
      rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  · have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        have hτ0 : τ ≠ 0 := by
          rintro rfl
          simp at hτ
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    exact ⟨e, he3, he1, z, hz, g, hg, hD⟩
  · exfalso
    refine false_of_commutator_mem (C := C) (fun a ha b hb => ?_) hder ψ hψ hQ
    have h := (@IsCyclic.commGroup C _ hcyc).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h

end TypeTwo

variable {F : Type} [Field F]

theorem type2_of_fix_projectiveSL {p f : ℕ} (hK : Sec4.PiField true p f F)
    (hq : Sec4.ModThree true (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x : GL (Fin 3) F} (hxZ : x ∉ Sec4.zPi true 3 (p ^ f) F)
    (hx3 : x ^ 3 ∈ Sec4.zPi true 3 (p ^ f) F) {Qs : Subgroup (projectiveSL 3 F)} {m : ℕ}
    (eQ : Qs ≃* projSL 2 (GaloisField 2 m)) (hm : 2 ≤ m)
    (hfix : ∀ q ∈ Qs, conjAut 3 F x q = q) : Sec4.Type123 true (p ^ f) F x 2 := by
  set M₀ : Subgroup (SpecialLinearGroup (Fin 3) F) := Qs.comap (proj 3 F) with hM₀
  set M : Subgroup (GL (Fin 3) F) := M₀.map SpecialLinearGroup.toGL with hMdef
  let ι : M₀ ≃* M := M₀.equivMapOfInjective _ SpecialLinearGroup.toGL_injective
  let ψ₀ : M₀ →* Qs := ((proj 3 F).comp M₀.subtype).codRestrict Qs fun g => g.2
  let ψ : M →* Qs := ψ₀.comp ι.symm.toMonoidHom
  have hψι : ∀ g : M₀, ψ (ι g) = ψ₀ g := fun g => by
    change ψ₀ (ι.symm (ι g)) = ψ₀ g
    rw [MulEquiv.symm_apply_apply]
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨g, hg⟩ := proj_surjective 3 F (q : projectiveSL 3 F)
    have hgM : g ∈ M₀ := by
      change proj 3 F g ∈ Qs
      rw [hg]
      exact q.2
    refine ⟨ι ⟨g, hgM⟩, ?_⟩
    rw [hψι]
    exact Subtype.ext hg
  have hMle : M ≤ Sec4.centMod (Sec4.slPi true 3 (p ^ f) F) x := by
    rintro _ ⟨g, hg, rfl⟩
    exact toGL_mem_centMod_of_conjAut_fix (p ^ f) (hfix _ hg)
  have : IsSimpleGroup Qs := isSimpleGroup_of_mulEquiv hm eQ
  exact type2_of_le_centMod hK hq hτ hτ1 (Sec4.mem_glPi_true _ x) hxZ hx3 hMle ψ hψ
    (exists_not_commute_of_mulEquiv_projSL eQ)

@[expose] noncomputable def pglConj (F : Type) [Field F] [Finite F] :
    GL (Fin 3) F ⧸ StatedScalars (Fin 3) F →* MulAut (projectiveSL 3 F) :=
  QuotientGroup.lift _ (conjAut 3 F) fun z hz => by
    obtain ⟨c, rfl⟩ := hz
    exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl _).mpr ⟨c, rfl⟩

theorem pglConj_mk [Finite F] (y : GL (Fin 3) F) :
    pglConj F (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) = conjAut 3 F y :=
  rfl

theorem pglConj_injective [Finite F] : Function.Injective (pglConj F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [MonoidHom.mem_ker, pglConj_mk] at hw
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl y).mp hw
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact ⟨c, hc⟩

theorem exists_typeC_conj [Finite F] {p f : ℕ} (hK : Sec4.PiField true p f F)
    (hq : Sec4.ModThree true (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3F : (3 : F) ≠ 0)
    {E' : Subgroup (MulAut (projectiveSL 3 F))} (hE'e : IsElemAbelian 3 E')
    (hE'9 : Nat.card E' = 9) (hE'L : E' ≤ linearAutGroup 3 F) {x : GL (Fin 3) F}
    (hxE : conjAut 3 F x ∈ E') (hx2 : Sec4.Type123 true (p ^ f) F x 2)
    (hxZ : x ∉ Sec4.zPi true 3 (p ^ f) F) (hx3 : x ^ 3 ∈ Sec4.zPi true 3 (p ^ f) F) :
    ∃ g : GL (Fin 3) F,
      (∀ y : GL (Fin 3) F, conjAut 3 F y ∈ E' → ∃ l s t : Fˣ, s ∈ rootsOfUnity 3 F ∧
        t ∈ rootsOfUnity 3 F ∧
          g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * Sec4.diagUnits 1 s t) ∧
      (∀ s ∈ rootsOfUnity 3 F, ∀ t ∈ rootsOfUnity 3 F, ∃ y : GL (Fin 3) F,
        conjAut 3 F y ∈ E' ∧ ∃ l : Fˣ,
          g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * Sec4.diagUnits 1 s t) := by
  set Eb : Subgroup (GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) := E'.comap (pglConj F) with hEb
  have hmem : ∀ y : GL (Fin 3) F,
      (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ∈ Eb ↔ conjAut 3 F y ∈ E' := fun y =>
    Iff.rfl
  have hinj := pglConj_injective (F := F)
  have hcomm : ∀ u ∈ Eb, ∀ v ∈ Eb, u * v = v * u := by
    intro u hu v hv
    apply hinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE'e.1.is_comm.comm ⟨_, hu⟩ ⟨_, hv⟩)
  have hexp : ∀ u ∈ Eb, u ^ 3 = 1 := by
    intro u hu
    apply hinj
    rw [map_pow, map_one]
    exact hE'e.2 _ hu
  have hcard : Nat.card Eb = 9 := by
    have hmap : Eb.map (pglConj F) = E' := by
      refine Subgroup.map_comap_eq_self (fun σ hσ => ?_)
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp (hE'L hσ)
      exact ⟨(A : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F), hA⟩
    rw [← hE'9, ← hmap, Subgroup.card_map_of_injective hinj]
  rcases Sec4.frame_or_heis h3F hτ hτ1 Eb hcomm hexp (by omega) with ⟨b, hb, hd, -⟩ |
      ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · set D : Subgroup (GL (Fin 3) F) := Eb.comap (QuotientGroup.mk' (StatedScalars (Fin 3) F))
      with hD
    have hDC : Sec4.IsTypeC true (p ^ f) F D := by
      refine ⟨fun y _ => Sec4.mem_glPi_true _ y, fun a ha => ?_, ?_, b, hb, fun a ha => hd a ha⟩
      · have h1 := hexp _ ha
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
        exact hcard
    obtain ⟨g, -, h1, h2⟩ := Sec4.isTypeC_conj_std hK hq hDC
    exact ⟨g, fun y hy => h1 y ((hmem y).mpr hy), fun s hs t ht => by
      obtain ⟨y, hyD, l, hl⟩ := h2 s hs t ht
      exact ⟨y, (hmem y).mp hyD, l, hl⟩⟩
  · exfalso
    rcases Sec4.type13_of_heisP hK hq hcomm hy₁ hy₂ hζ1 hζ (Sec4.mem_glPi_true _ x) hxZ hx3
        ((hmem x).mpr hxE) with h1 | h3
    · exact Sec4.not_type123_one_two hK hq h1 hx2
    · exact Sec4.not_type123_three_of_two hK hq hx2 h3

theorem coe_e₂_apply {Y : Type*} [Group Y] (e : Y ≃* projectiveSL 3 F) (q : ℕ) {β : MulAut Y}
    {y : GL (Fin 3) F} (hβ : MulAut.congr e β = conjAut 3 F y) (z : Y) :
    ((e.trans (Sec4.pslEquivProjective q F).symm (β z) : projImage (Sec4.slPi true 3 q F)) :
        ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk y * ((e.trans (Sec4.pslEquivProjective q F).symm z :
        projImage (Sec4.slPi true 3 q F)) : ProjGenLinGroup (Fin 3) F) *
          (ProjGenLinGroup.mk y)⁻¹ := by
  have hsymm : ∀ t : SpecialLinearGroup (Fin 3) F,
      (Sec4.pslEquivProjective q F).symm (proj 3 F t) = Sec4.slToPsl q F t := fun t => by
    rw [MulEquiv.symm_apply_eq, Sec4.pslEquivProjective_slToPsl]
  obtain ⟨s, hs⟩ := proj_surjective 3 F (e z)
  have h1 : e (β z) = proj 3 F (slConjugation 3 F y s) := by
    have := congrArg (fun σ : MulAut (projectiveSL 3 F) => σ (e z)) hβ
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    rw [this, ← hs, conjAut_proj]
  simp only [MulEquiv.trans_apply]
  rw [h1, ← hs, hsymm, hsymm, Sec4.coe_slToPsl, Sec4.coe_slToPsl, toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem mk_diagUnits_ne_one {t : Fˣ} (ht : t ≠ 1) :
    ProjGenLinGroup.mk (Sec4.diagUnits t 1⁻¹ (1 * t⁻¹)) ≠ 1 := by
  intro h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨c, hc⟩ := h
  have e0 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) hc
  have e1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 1) hc
  simp [Sec4.coe_diagUnits] at e0 e1
  apply ht
  apply Units.ext
  rw [← e0, e1, Units.val_one]

end Item228Census4Proof

open Item228Census4Proof

section Certs


theorem census228L3TypePSLEven_holds : Census228L3TypePSLEven := by
  intro G _ _ X A K K₀ m hL hP hAmax hA27 hAN hAC hdiag hmono _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm
    hm0 hme
  obtain ⟨F, _, _, h3, heven, ⟨e⟩⟩ := hP
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := X ⧸ aschbacherSolvableCore 3 X with hY
  set θG := inSubgroup (aschbacherSolvableCore 3) X with hθG
  have hAe : IsElemAbelian 3 A := hAmax.prop
  have hAp : IsPGroup 3 A := Item22Res4Proof.isPGroup_of_elemAbelian hAe
  have hEmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A :=
    fun B hB hAB => le_antisymm (hAmax.2 hB hAB) hAB
  have hAθ : ∀ w ∈ A, w ∈ θG → w = 1 := fun w hwA hwθ =>
    Item22Res4Proof.eq_one_of_mem_theta hAe hwA hwθ
  have : CharP F 2 := charP_two_of_even_card heven
  have h3F : (3 : F) ≠ 0 := by
    have h1 : (3 : F) = 1 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      linear_combination h2
    rw [h1]
    exact one_ne_zero
  obtain ⟨b, hbA, hbN, hβ1, N, Kb, hcfg⟩ := Item228Census2Proof.config228Aut_of hAmax hA27 hAN
    hAC hρ hρr hKK hK0X hK0C hnorm hU hKm hm0 hme
  have hm2 := two_le_of_even hm0 hme
  obtain ⟨eK⟩ := hcfg.equiv
  have hlin : ∀ (a : G) (ha : a ∈ A), MulAut.congr e (Sec4.thetaQuotMulAut X
      (Sec4.compAction X ⟨a, hAN ha⟩)) ∈ linearAutGroup 3 F := by
    intro a ha
    have ha3 : a ^ 3 = 1 := hAe.2 a ha
    by_cases ho : Sec4.InducesOuterTheta a X
    · have := (outer223Cross_holds G X a hL ha3 (hdiag a ha ho)).1 F h3 e (hAN ha)
      rwa [inducedAutHom_apply] at this
    · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta (hAN ha) ho
      rw [← hy, congr_mulAutConj]
      exact innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
  set E' : Subgroup (MulAut (projectiveSL 3 F)) :=
    (Sec4.thetaAct hAN).range.map (MulAut.congr e).toMonoidHom with hE'
  have hE'e : IsElemAbelian 3 E' :=
    Sec4.isElemAbelian_map _ (Sec4.isElemAbelian_range_thetaAct hAN hAe)
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr e).injective]
    have h1 := Item223CensusProof.card_range_thetaAct hAN
    rw [hAC, hA27] at h1
    omega
  have hmemE' : ∀ (a : G) (ha : a ∈ A), MulAut.congr e (Sec4.thetaQuotMulAut X
      (Sec4.compAction X ⟨a, hAN ha⟩)) ∈ E' :=
    fun a ha => ⟨Sec4.thetaAct hAN ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hE'L : E' ≤ linearAutGroup 3 F := by
    rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact hlin a ha
  have hE'mem : ∀ σ ∈ E', ∃ (a : G) (ha : a ∈ A),
      σ = MulAut.congr e (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨a, hAN ha⟩)) := by
    rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨x, hx⟩ := mem_linearAutGroup_iff.mp (hlin b hbA)
  have hβ3 := thetaQuotMulAut_pow_three hbN (hAe.2 b hbA)
  have hxZ : x ∉ StatedScalars (Fin 3) F := by
    rintro ⟨c, hc⟩
    apply hβ1
    have h1 := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl x).mpr ⟨c, hc⟩
    rw [hx] at h1
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  have hx3 : x ^ 3 ∈ StatedScalars (Fin 3) F := by
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff le_rfl (x ^ 3)).mp
      (by rw [map_pow, hx, ← map_pow, hβ3, map_one])
    exact ⟨c, hc⟩
  obtain ⟨p, f, hK, hq, τ, hτ, hτ1, -, hxZ', hx3'⟩ := exists_data_true h3 hxZ hx3
  have hx2 : Sec4.Type123 true (p ^ f) F x 2 := by
    refine type2_of_fix_projectiveSL hK hq hτ hτ1 hxZ' hx3' (Qs := Kb.map e.toMonoidHom)
      ((Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK) hm2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hx]
    simp [MulAut.congr_apply, hcfg.fix k (hcfg.le hk)]
  obtain ⟨g, hgD, hgS⟩ := exists_typeC_conj hK hq hτ hτ1 h3F hE'e hE'9 hE'L
    (by rw [hx]; exact hmemE' b hbA) hx2 hxZ' hx3'
  set e₂ : Y ≃* projImage (Sec4.slPi true 3 (p ^ f) F) :=
    e.trans (Sec4.pslEquivProjective (p ^ f) F).symm with he₂
  have hreal : ∀ (a : G) (ha : a ∈ A), ∃ y : GL (Fin 3) F, conjAut 3 F y ∈ E' ∧ ∀ z : Y,
      ((e₂ (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨a, hAN ha⟩) z) :
        projImage (Sec4.slPi true 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk y * ((e₂ z : projImage (Sec4.slPi true 3 (p ^ f) F)) :
          ProjGenLinGroup (Fin 3) F) * (ProjGenLinGroup.mk y)⁻¹ := by
    intro a ha
    obtain ⟨y, hy⟩ := mem_linearAutGroup_iff.mp (hlin a ha)
    exact ⟨y, hy ▸ hmemE' a ha, fun z => coe_e₂_apply e (p ^ f) hy.symm z⟩
  have hq2 : 2 < p ^ f := by
    have hc := hK.card
    change Nat.card F = p ^ f at hc
    have hev : Nat.card F % 2 = 0 := Nat.even_iff.mp heven
    have h31 : (p ^ f) % 3 = 1 := hq
    have : 0 < Nat.card F := Nat.card_pos
    omega
  have hZ : Subgroup.center Y = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv e₂ (Sec13.center_projImage_slPi hK hq hq2)
  have hπ : true = false → UnitaryFieldData p f F := fun h => absurd h (by decide)
  have hq' : true = false → Sec4.ModThree false (p ^ f) := fun h => absurd h (by decide)
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hgG : g ∈ Sec4.glPi true 3 (p ^ f) F := Sec4.mem_glPi_true _ g
  have hd₁ : g * Sec4.diagTau hτ * g⁻¹ ∈ Sec4.slPi true 3 (p ^ f) F :=
    Sec4.conj_mem_slPi hπ hgG (Sec4.diagTau_mem_slPi hπ hq' hτ)
  have hd₂ : g * Sec4.cycThree * g⁻¹ ∈ Sec4.slPi true 3 (p ^ f) F :=
    Sec4.conj_mem_slPi hπ hgG (Sec4.cycThree_mem_slPi hπ)
  set P₁ : projImage (Sec4.slPi true 3 (p ^ f) F) := Sec4.projOf _ ⟨_, hd₁⟩ with hP₁
  set P₂ : projImage (Sec4.slPi true 3 (p ^ f) F) := Sec4.projOf _ ⟨_, hd₂⟩ with hP₂
  set y₁ : Y := e₂.symm P₁ with hy₁
  set y₂ : Y := e₂.symm P₂ with hy₂
  have he₁ : ((e₂ y₁ : projImage (Sec4.slPi true 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹) := by
    rw [hy₁, MulEquiv.apply_symm_apply, hP₁, Sec4.coe_projOf]
  have he₂' : ((e₂ y₂ : projImage (Sec4.slPi true 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹) := by
    rw [hy₂, MulEquiv.apply_symm_apply, hP₂, Sec4.coe_projOf]
  have hfixDiag : ∀ (z : Y) (a₀ b₀ c₀ : Fˣ),
      ((e₂ z : projImage (Sec4.slPi true 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk (g * Sec4.diagUnits a₀ b₀ c₀ * g⁻¹) →
      ∀ (x' : G) (hx' : x' ∈ A),
        Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x', hAN hx'⟩) z = z := by
    intro z a₀ b₀ c₀ hz x' hx'
    obtain ⟨y, hyE, hyz⟩ := hreal x' hx'
    obtain ⟨l, s, t, -, -, hl⟩ := hgD y hyE
    apply e₂.injective
    apply Subtype.ext
    rw [hyz z, hz, ← map_inv, ← map_mul, ← map_mul, Sec13.Item138Proof.conj_diag_comm hl]
  have hfix₁ := hfixDiag y₁ (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1
    (by rw [he₁, Sec4.diagTau_eq_diagUnits hτ hτ0])
  have hy₁3 : y₁ ^ 3 = 1 := by
    apply e₂.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, he₁, ← map_pow, conj_pow,
      Sec4.diagTau_pow_three, mul_one, mul_inv_cancel, map_one]
  have hy₂3 : y₂ ^ 3 = 1 := by
    apply e₂.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, he₂', ← map_pow, conj_pow,
      Sec4.cycThree_pow_three, mul_one, mul_inv_cancel, map_one]
  have hy12 : y₁ * y₂ = y₂ * y₁ := by
    apply e₂.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂']
    simp only [map_mul, map_inv]
    have hc := Sec4.mk_diagTau_cycThree hτ
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (Sec4.diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk Sec4.cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (Sec4.diagTau hτ) *
          ProjGenLinGroup.mk Sec4.cycThree) * (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk Sec4.cycThree *
          ProjGenLinGroup.mk (Sec4.diagTau hτ)) * (ProjGenLinGroup.mk g)⁻¹ := by rw [hc]
      _ = _ := by group
  have hy₁1 : y₁ ≠ 1 := by
    intro h1
    have h2 : ((e₂ y₁ : projImage (Sec4.slPi true 3 (p ^ f) F)) :
        ProjGenLinGroup (Fin 3) F) = 1 := by
      rw [h1, map_one, Subgroup.coe_one]
    rw [he₁, map_mul, map_mul, map_inv] at h2
    apply Sec13.Item138Proof.mk_diagTau_ne_one hτ hτ1
    calc ProjGenLinGroup.mk (Sec4.diagTau hτ) = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (Sec4.diagTau hτ) *
            (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨n₁, hn₁A, hn₁⟩ := Sec13.Item138Proof.exists_mem_of_fixed hAN hAe hEmax hy₁3 hfix₁
  obtain ⟨w₂, hw₂⟩ := QuotientGroup.mk_surjective y₂
  have hw₂E : ∀ x' ∈ A, (w₂ : G) * x' * (w₂ : G)⁻¹ ∈ A ⊔ θG := by
    intro x' hx'
    set σ := Sec4.compAction X ⟨x', hAN hx'⟩ with hσ
    set k : X := w₂ * (σ w₂)⁻¹ with hk
    have hkG : (k : G) = (w₂ : G) * (x' * (w₂ : G) * x'⁻¹)⁻¹ := rfl
    obtain ⟨y, hyE, hyz⟩ := hreal x' hx'
    obtain ⟨l, s, t, hs, ht, hl⟩ := hgD y hyE
    have hs3 : s ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs
    have ht3 : t ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht
    have hmk : (k : Y) = y₂ * (Sec4.thetaQuotMulAut X σ y₂)⁻¹ := by
      rw [hk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← Sec4.thetaQuotMulAut_mk, hw₂]
    have hek : ((e₂ (k : Y) : projImage (Sec4.slPi true 3 (p ^ f) F)) :
        ProjGenLinGroup (Fin 3) F) =
          ProjGenLinGroup.mk (g * Sec4.diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹) := by
      rw [hmk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyz y₂, he₂',
        ← Sec13.Item138Proof.comm_cycThree_conj hl]
      simp only [map_mul, map_inv]
      group
    have hk3 : (k : Y) ^ 3 = 1 := by
      apply e₂.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hek, ← map_pow, conj_pow,
        Sec13.Item138Proof.diagUnits_pow_three ht3 (by rw [inv_pow, hs3, inv_one])
          (by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul]),
        mul_one, mul_inv_cancel, map_one]
    obtain ⟨n, hnE, hnk⟩ := Sec13.Item138Proof.exists_mem_of_fixed hAN hAe hEmax hk3
      (hfixDiag _ _ _ _ hek)
    have hnk' : (n : G)⁻¹ * (k : G) ∈ θG := (Sec13.Item138Proof.mk_eq_mk_iff n k).mp hnk
    have hθx : x'⁻¹ * ((n : G)⁻¹ * (k : G)) * x'⁻¹⁻¹ ∈ θG :=
      Sec13.Item138Proof.conj_mem_theta_of_normalizer (inv_mem (hAN hx')) hnk'
    have heq : (w₂ : G) * x' * (w₂ : G)⁻¹ =
        ((n : G) * x') * (x'⁻¹ * ((n : G)⁻¹ * (k : G)) * x'⁻¹⁻¹) := by
      rw [hkG]
      group
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hnE hx')) (Subgroup.mem_sup_right hθx)
  obtain ⟨mm, hmX, hmN, hmw⟩ :=
    Sec13.Item138Proof.exists_mem_normalizer_of_conj_mem hAN hAp w₂.2 hw₂E
  have hmk : ((⟨mm, hmX⟩ : X) : Y) = y₂ := by
    rw [← hw₂, Sec13.Item138Proof.mk_eq_mk_iff]
    refine Sec13.Item138Proof.inv_mul_mem_theta_of_mul_inv_mem hmX ?_
    have := inv_mem hmw
    rwa [_root_.mul_inv_rev, inv_inv] at this
  set nm : Subgroup.normalizer (A : Set G) := ⟨mm, hmN⟩ with hnm
  set ρm : MulAut A := A.normalizerMonoidHom nm with hρmdef
  have hρmX : ρm ∈ starOf A X := ⟨nm, hmX, rfl⟩
  have hρa : ∀ a : A, ((ρm a : A) : G) = mm * a * mm⁻¹ := fun a => rfl
  have hmn₁ : mm * (n₁ : G) * mm⁻¹ = n₁ := by
    have hdA : mm * (n₁ : G) * mm⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hmN _).mp hn₁A
    have hdX : mm * (n₁ : G) * mm⁻¹ ∈ X := X.mul_mem (X.mul_mem hmX n₁.2) (X.inv_mem hmX)
    have hmkd : ((⟨_, hdX⟩ : X) : Y) = (n₁ : Y) := by
      have h1 : (⟨_, hdX⟩ : X) = ⟨mm, hmX⟩ * n₁ * (⟨mm, hmX⟩)⁻¹ := rfl
      rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, hn₁,
        ← hy12, mul_inv_cancel_right]
    have h2 := (Sec13.Item138Proof.mk_eq_mk_iff _ _).mp hmkd.symm
    have h3 : (n₁ : G)⁻¹ * (mm * (n₁ : G) * mm⁻¹) = 1 :=
      hAθ _ (A.mul_mem (A.inv_mem hn₁A) hdA) h2
    calc mm * (n₁ : G) * mm⁻¹ = (n₁ : G) * ((n₁ : G)⁻¹ * (mm * (n₁ : G) * mm⁻¹)) := by group
      _ = n₁ := by rw [h3, mul_one]
  have hm3θ : mm ^ 3 ∈ θG := by
    have h1 : (((⟨mm, hmX⟩ : X) ^ 3 : X) : Y) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, hy₂3]
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact (Sec13.Item138Proof.mem_theta_iff _).mp h2
  have hρm3 : ρm ^ 3 = 1 := by
    ext a
    rw [MulAut.one_apply, hρmdef, ← map_pow]
    change ((nm ^ 3 : Subgroup.normalizer (A : Set G)) : G) * a *
      ((nm ^ 3 : Subgroup.normalizer (A : Set G)) : G)⁻¹ = a
    rw [Subgroup.coe_pow]
    change mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ = a
    have hc : mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ * (a : G)⁻¹ = 1 := by
      refine hAθ _ ?_ ?_
      · have : mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hmN 3) _).mp a.2
        exact A.mul_mem this (A.inv_mem a.2)
      · have h1 : (a : G) * (mm ^ 3)⁻¹ * (a : G)⁻¹ ∈ θG :=
          Sec13.Item138Proof.conj_mem_theta_of_normalizer (hAN a.2) (inv_mem hm3θ)
        have h2 : mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ * (a : G)⁻¹ =
            mm ^ 3 * ((a : G) * (mm ^ 3)⁻¹ * (a : G)⁻¹) := by group
        rw [h2]
        exact mul_mem hm3θ h1
    calc mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ =
        mm ^ 3 * (a : G) * (mm ^ 3)⁻¹ * (a : G)⁻¹ * (a : G) := by group
      _ = (a : G) := by rw [hc, one_mul]
  have hρm1 : ρm ≠ 1 := by
    intro h1
    set τu : Fˣ := Units.mk0 τ hτ0 with hτu
    have hτu3 : τu ∈ rootsOfUnity 3 F := by
      rw [mem_rootsOfUnity]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one]
    obtain ⟨y, hyE, l, hl⟩ := hgS 1 (Subgroup.one_mem _) τu hτu3
    obtain ⟨a, ha, hya⟩ := hE'mem _ hyE
    have hma : mm * a * mm⁻¹ = a := congrArg Subtype.val
      (show ρm ⟨a, ha⟩ = ⟨a, ha⟩ by rw [h1, MulAut.one_apply])
    have ham : a * mm * a⁻¹ = mm := by
      calc a * mm * a⁻¹ = (mm * a * mm⁻¹) * mm * a⁻¹ := by rw [hma]
        _ = mm := by group
    have hfix₂ : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨a, hAN ha⟩) y₂ = y₂ := by
      rw [← hmk, Sec4.thetaQuotMulAut_mk]
      congr 1
      exact Subtype.ext ham
    have h2 := coe_e₂_apply e (p ^ f) hya.symm y₂
    rw [hfix₂, he₂'] at h2
    have h3 : ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹ * y * (g * Sec4.cycThree * g⁻¹)⁻¹ *
        y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹) * ProjGenLinGroup.mk y *
            (ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹))⁻¹ * (ProjGenLinGroup.mk y)⁻¹ =
          (ProjGenLinGroup.mk y * ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹) *
            (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk y *
            (ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹))⁻¹ * (ProjGenLinGroup.mk y)⁻¹ := by
            rw [← h2]
        _ = 1 := by group
    rw [Sec13.Item138Proof.comm_cycThree_conj hl, map_mul, map_mul, map_inv] at h3
    apply mk_diagUnits_ne_one (show τu ≠ 1 by
      intro h
      apply hτ1
      have := congrArg Units.val h
      rwa [Units.val_mk0, Units.val_one] at this)
    calc ProjGenLinGroup.mk (Sec4.diagUnits τu 1⁻¹ (1 * τu⁻¹)) =
        (ProjGenLinGroup.mk g)⁻¹ * (ProjGenLinGroup.mk g *
          ProjGenLinGroup.mk (Sec4.diagUnits τu 1⁻¹ (1 * τu⁻¹)) * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h3]; group
  set C₀ : Subgroup A := (Sec4.thetaQuotCentralizer X).subgroupOf A with hC₀
  have hC₀F : C₀ ≤ fixedSubgroupOf ρm := fun c hc =>
    (mem_fixedSubgroupOf ρm c).mpr
      (Item22Res4Proof.fix_of_mem_starOf hAe hρmX c.2 (Subgroup.mem_subgroupOf.mp hc))
  have hn₁F : (⟨n₁, hn₁A⟩ : A) ∈ fixedSubgroupOf ρm :=
    (mem_fixedSubgroupOf ρm _).mpr (Subtype.ext hmn₁)
  have hn₁C : (⟨n₁, hn₁A⟩ : A) ∉ C₀ := by
    intro hc
    have hc' : (n₁ : G) ∈ Sec4.thetaQuotCentralizer X := Subgroup.mem_subgroupOf.mp hc
    have h1 := (Item223CensusProof.mem_thetaQuotCentralizer_iff_of_mem (hAN hn₁A)).mp hc'
    have h2 : MulAut.conj (n₁ : Y) = 1 := by
      rw [← Item22Res4Proof.thetaAct_eq_conj hAN hn₁A]
      exact h1
    have h3 : (n₁ : Y) = 1 := Item22Res4Proof.conj_injective_of_center_eq_bot hZ
      (by rw [h2, map_one])
    exact hy₁1 (hn₁ ▸ h3)
  have hlt : C₀ < fixedSubgroupOf ρm :=
    lt_of_le_of_ne hC₀F (fun h => hn₁C (h ▸ hn₁F))
  have hcard : 3 < Nat.card (fixedSubgroupOf ρm) := by
    have h1 : Nat.card C₀ = 3 := by
      rw [← hAC, hC₀, ← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
          Sec4.thetaQuotCentralizer X ⊓ A ≤ A)).toEquiv, inf_comm]
    rw [← h1]
    exact Subgroup.card_lt_of_lt hlt
  obtain ⟨fc, hfc⟩ := hmono
  have hM := hfc ⟨ρm, hρmX, rfl⟩
  have hM3 : coordGL fc ρm ^ 3 = 1 := by rw [← map_pow, hρm3, map_one]
  have hM1 : coordGL fc ρm ≠ 1 := fun h =>
    hρm1 (coordGL_injective fc (h.trans (map_one _).symm))
  have hle := Item22Res4Proof.monomial_fixed_le_three hM hM3 hM1
  have hinj : Nat.card (fixedSubgroupOf ρm) ≤ (Finset.univ.filter fun v : Fin 3 → ZMod 3 =>
      ((coordGL fc ρm : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective
      (fun a => ⟨Multiplicative.toAdd (fc.symm (a : A)), ?_⟩) ?_
    · rw [coordGL_mulVec, coordLin3_apply]
      simp only [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rw [(mem_fixedSubgroupOf ρm a).mp a.2]
    · intro a b hab
      apply Subtype.ext
      exact fc.symm.injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))
  omega

end Certs

end CFSG.RankThree.PartTwo.Sec21
