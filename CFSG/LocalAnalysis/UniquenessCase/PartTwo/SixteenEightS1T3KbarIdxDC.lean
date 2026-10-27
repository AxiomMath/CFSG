module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxDA
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mk altAct_mul altAct_one altAct_inv_apply altAct_apply_inv)

variable {W : Type} [CommGroup W]

private noncomputable def s16t3_altActEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    altHeart n ≃+ altHeart n where
  toFun := altAct σ
  invFun := altAct σ⁻¹
  left_inv v := altAct_inv_apply σ v
  right_inv v := altAct_apply_inv σ v
  map_add' v w := map_add (altAct σ) v w

private noncomputable def s16t3_altActHom (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Multiplicative (altHeart n)) where
  toFun σ := AddEquiv.toMultiplicative (s16t3_altActEquiv σ)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (altAct 1 (Multiplicative.toAdd x)) = x
    rw [altAct_one, ofAdd_toAdd]
  map_mul' σ τ := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (altAct (σ * τ) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (altAct σ (altAct τ (Multiplicative.toAdd x)))
    rw [altAct_mul]

private theorem s16t3_altActHom_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Multiplicative (altHeart n)) :
    s16t3_altActHom n σ x =
      Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd x)) := rfl

private theorem s16t3_constWeight_eq_evenWeightOnes (m : ℕ) :
    CFSG.Quasithin.constWeight m = CFSG.RankThree.PartTwo.evenWeightOnes m := by
  ext x
  rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨i₀⟩ := hm
      refine ⟨((x : Fin m → ZMod 2) i₀).val, funext fun i => ?_⟩
      simp [CFSG.RankThree.PartTwo.allOnes, hx i i₀]
    · refine ⟨0, funext fun i => ?_⟩
      exact absurd ⟨i⟩ hm
  · rintro ⟨k, hk⟩
    have hi : ∀ i, (x : Fin m → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [CFSG.RankThree.PartTwo.allOnes]
    intro i j
    exact (hi i).trans (hi j).symm

private noncomputable def s16t3_heartEquivAlt (m : ℕ) :
    CFSG.Quasithin.AltHeart m ≃+ CFSG.RankThree.PartTwo.altHeart m :=
  QuotientAddGroup.quotientAddEquivOfEq (s16t3_constWeight_eq_evenWeightOnes m)

private theorem s16t3_heartEquivAlt_mk {m : ℕ} (x : ↥(CFSG.QuasithinUnique.evenWeight m)) :
    s16t3_heartEquivAlt m (QuotientAddGroup.mk x : CFSG.Quasithin.AltHeart m) =
      (QuotientAddGroup.mk x : CFSG.RankThree.PartTwo.altHeart m) :=
  QuotientAddGroup.quotientAddEquivOfEq_mk _ x

private theorem s16t3_heartEquivAlt_hAct {m : ℕ} (σ : Equiv.Perm (Fin m))
    (y : CFSG.Quasithin.AltHeart m) :
    s16t3_heartEquivAlt m (CFSG.Quasithin.C41Pf.AltN.hAct m σ y) =
      altAct σ (s16t3_heartEquivAlt m y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [CFSG.Quasithin.C41Pf.AltN.hAct_mk]
  simp only [s16t3_heartEquivAlt_mk, altAct_mk]
  rw [show CFSG.Quasithin.permWeight m σ x =
      CFSG.RankThree.PartTwo.evenWeightPerm σ x from Subtype.ext (funext fun _ => rfl)]

private theorem s16t3_altAct_normalizer_le {n : ℕ} (hn : 5 ≤ n) :
    Subgroup.normalizer (((alternatingGroup (Fin n)).map (s16t3_altActHom n) :
      Subgroup (MulAut (Multiplicative (altHeart n))))) ≤
      (⊤ : Subgroup (Equiv.Perm (Fin n))).map (s16t3_altActHom n) := by
  intro M hM
  let γ : altHeart n ≃+ altHeart n :=
    Multiplicative.toAdd (MulAutMultiplicative (altHeart n) M)
  have hγ : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, γ (altAct σ v) = altAct σ' (γ v) := by
    intro σ hσ
    have hσmem : s16t3_altActHom n σ ∈
        (alternatingGroup (Fin n)).map (s16t3_altActHom n) :=
      Subgroup.mem_map_of_mem _ hσ
    have hconj := (Subgroup.mem_normalizer_iff.mp hM (s16t3_altActHom n σ)).1 hσmem
    obtain ⟨σ', hσ', hσ'eq⟩ := hconj
    refine ⟨σ', hσ', fun v => ?_⟩
    have happ : s16t3_altActHom n σ' (M (Multiplicative.ofAdd v)) =
        M (s16t3_altActHom n σ (Multiplicative.ofAdd v)) := by
      have h := congrArg (fun g : MulAut (Multiplicative (altHeart n)) =>
        g (M (Multiplicative.ofAdd v))) hσ'eq
      simpa using h
    have h1 : Multiplicative.toAdd (s16t3_altActHom n σ' (M (Multiplicative.ofAdd v))) =
        Multiplicative.toAdd (M (s16t3_altActHom n σ (Multiplicative.ofAdd v))) := by
      rw [happ]
    rw [s16t3_altActHom_apply, s16t3_altActHom_apply, toAdd_ofAdd, toAdd_ofAdd] at h1
    rw [show γ v = Multiplicative.toAdd (M (Multiplicative.ofAdd v)) from rfl,
      show γ (altAct σ v) =
        Multiplicative.toAdd (M (Multiplicative.ofAdd (altAct σ v))) from rfl]
    exact h1.symm
  obtain ⟨π, hπ⟩ := s16c167_normalizerIsSym hn γ hγ
  refine Subgroup.mem_map.mpr ⟨π, Subgroup.mem_top π, ?_⟩
  refine MulEquiv.ext fun x => ?_
  obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = x :=
    ⟨Multiplicative.toAdd x, ofAdd_toAdd x⟩
  rw [s16t3_altActHom_apply, toAdd_ofAdd, ← hπ v,
    show γ v = Multiplicative.toAdd (M (Multiplicative.ofAdd v)) from rfl, ofAdd_toAdd]

private theorem s16t3_normIdx_altAct {n : ℕ} (hn : 5 ≤ n) :
    s16t3_normIdx ((alternatingGroup (Fin n)).map (s16t3_altActHom n)) := by
  intro M₁ M₂ M₃ hM₁ hM₂ hM₃
  have hle := s16t3_altAct_normalizer_le hn
  obtain ⟨π₁, -, hπ₁⟩ := hle hM₁
  obtain ⟨π₂, -, hπ₂⟩ := hle hM₂
  obtain ⟨π₃, -, hπ₃⟩ := hle hM₃
  have hnorm : ∀ π : Equiv.Perm (Fin n),
      π ∈ Subgroup.normalizer (alternatingGroup (Fin n) : Set (Equiv.Perm (Fin n))) :=
    fun π => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top π
  rcases s16t3_normIdx_alt hn π₁ π₂ π₃ (hnorm π₁) (hnorm π₂) (hnorm π₃) with h12 | h13 | h23
  · left
    rw [← hπ₁, ← hπ₂, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ h12
  · right; left
    rw [← hπ₁, ← hπ₃, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ h13
  · right; right
    rw [← hπ₂, ← hπ₃, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ h23

theorem s16t3_normIdx_altDn {n : ℕ} (hn : 5 ≤ n) {L : Subgroup (MulAut W)} {J₀ Z : Subgroup W}
    {π : ↥(alternatingGroup (Fin n)) →* ↥L}
    (hR : (FFModel.altDn n).RealizesVia L J₀ Z π)
    (gL : ↥L →* MulAut (↥J₀ ⧸ Z.subgroupOf J₀))
    (hgL : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
      ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
      gL (π γ) (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) :
    s16t3_normIdx ((⊤ : Subgroup ↥L).map gL) := by
  classical
  obtain ⟨hπsurj, -, -, hJinv, -, hsecinv, -, β, hβsurj, hβker, hβeq⟩ := hR
  have hπsurj' : Function.Surjective (π : ↥(alternatingGroup (Fin n)) →* ↥L) := hπsurj
  have hker : β.ker = Z.subgroupOf J₀ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβker u
  let e : (↥(FFModel.altDn n).sec ⧸
      (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Multiplicative (AltHeart n) := CFSG.Quasithin.C124.altQuotEquiv n (by omega)
  let βe : ↥J₀ →* Multiplicative (AltHeart n) := e.toMonoidHom.comp β
  have hker' : βe.ker = Z.subgroupOf J₀ := by
    ext u
    rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
    exact e.map_eq_one_iff
  have hβesurj : Function.Surjective βe := e.surjective.comp hβsurj
  let βe' : (↥J₀ ⧸ Z.subgroupOf J₀) ≃* Multiplicative (AltHeart n) :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective βe hβesurj)
  have hβe' : ∀ u : ↥J₀, βe' (QuotientGroup.mk u) = βe u := by
    intro u
    show (QuotientGroup.quotientKerEquivOfSurjective βe hβesurj)
      ((QuotientGroup.quotientMulEquivOfEq hker'.symm) (QuotientGroup.mk u)) = βe u
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk βe u
  have hβe_eq : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
      βe ⟨((π γ : ↥L) : MulAut W) (u : W), hJinv (π γ) u u.2⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (βe u))) := by
    intro γ u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m (hJinv (π γ) u u.2) hsec hmu
    calc e (β ⟨((π γ : ↥L) : MulAut W) (u : W), hJinv (π γ) u u.2⟩)
        = e (QuotientGroup.mk ⟨(FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb), hsec⟩) :=
          congrArg e h1
      _ = Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (e (β u)))) := by
          rw [hmu]
          rfl
  let c : Multiplicative (AltHeart n) ≃* Multiplicative (altHeart n) :=
    AddEquiv.toMultiplicative (s16t3_heartEquivAlt n)
  let ψ : (↥J₀ ⧸ Z.subgroupOf J₀) ≃* Multiplicative (altHeart n) := βe'.trans c
  have hψ_mk : ∀ u : ↥J₀, ψ (QuotientGroup.mk u) = c (βe u) := by
    intro u
    show (βe'.trans c) (QuotientGroup.mk u) = c (βe u)
    rw [MulEquiv.trans_apply, hβe']
  have hψ_eq : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
      Multiplicative.toAdd (ψ (gL (π γ) (QuotientGroup.mk u))) =
        altAct (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (ψ (QuotientGroup.mk u))) := by
    intro γ u
    have hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀ := hJinv (π γ) u u.2
    have h1 : ψ (gL (π γ) (QuotientGroup.mk u)) =
        c (βe ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) := by
      rw [hgL γ u hu, hψ_mk]
    rw [h1, hψ_mk u]
    show s16t3_heartEquivAlt n
        (Multiplicative.toAdd (βe ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩)) =
      altAct (γ : Equiv.Perm (Fin n))
        (s16t3_heartEquivAlt n (Multiplicative.toAdd (βe u)))
    rw [hβe_eq γ u, toAdd_ofAdd]
    exact s16t3_heartEquivAlt_hAct (γ : Equiv.Perm (Fin n))
      (Multiplicative.toAdd (βe u))
  let actA : ↥(alternatingGroup (Fin n)) →* MulAut (Multiplicative (altHeart n)) :=
    (s16t3_altActHom n).comp (alternatingGroup (Fin n)).subtype
  let gL' : ↥L →* MulAut (Multiplicative (altHeart n)) :=
    (MulAut.congr ψ).toMonoidHom.comp gL
  have hcongr : ∀ γ : ↥(alternatingGroup (Fin n)), gL' (π γ) = actA γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ψ.symm x)
    have hx : x = ψ (QuotientGroup.mk u) := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hx]
    show (MulAut.congr ψ (gL (π γ))) (ψ (QuotientGroup.mk u)) =
      s16t3_altActHom n (γ : Equiv.Perm (Fin n)) (ψ (QuotientGroup.mk u))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      s16t3_altActHom_apply, toAdd_ofAdd]
    rw [← hψ_eq γ u, ofAdd_toAdd]
  have hmap : (⊤ : Subgroup ↥L).map gL' =
      (⊤ : Subgroup ↥(alternatingGroup (Fin n))).map actA := by
    ext M
    constructor
    · rintro ⟨l, -, rfl⟩
      obtain ⟨γ, rfl⟩ := hπsurj' l
      rw [hcongr γ]
      exact Subgroup.mem_map_of_mem actA (Subgroup.mem_top γ)
    · rintro ⟨γ, -, rfl⟩
      rw [← hcongr γ]
      exact Subgroup.mem_map_of_mem gL' (Subgroup.mem_top (π γ))
  have hmapA : (⊤ : Subgroup ↥(alternatingGroup (Fin n))).map actA =
      (alternatingGroup (Fin n)).map (s16t3_altActHom n) := by
    dsimp only [actA]
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfin : s16t3_normIdx ((⊤ : Subgroup ↥L).map gL') := by
    rw [hmap, hmapA]
    exact s16t3_normIdx_altAct hn
  have hfin' : s16t3_normIdx (((⊤ : Subgroup ↥L).map gL).map
      (MulAut.congr ψ).toMonoidHom) := by
    dsimp only [gL'] at hfin
    rw [← Subgroup.map_map] at hfin
    exact hfin
  have hcancel : (((⊤ : Subgroup ↥L).map gL).map (MulAut.congr ψ).toMonoidHom).map
      (MulAut.congr ψ).symm.toMonoidHom = (⊤ : Subgroup ↥L).map gL := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id ((⊤ : Subgroup ↥L).map gL) using 2
    ext x
    simp
  rw [← hcancel]
  exact s16t3_normIdx_map_mulEquiv (MulAut.congr ψ).symm hfin'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
