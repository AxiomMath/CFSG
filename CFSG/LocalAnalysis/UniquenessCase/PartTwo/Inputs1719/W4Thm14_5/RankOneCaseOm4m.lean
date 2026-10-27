module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Om4mSummand
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Om4mTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2Transfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {W : Type} [CommGroup W]

theorem realizesVia_transfer {V V' : Type*} [CommGroup V] [CommGroup V'] {D : FFModel}
    {H : Subgroup (MulAut V)} {H' : Subgroup (MulAut V')} {U : Subgroup V} {U' : Subgroup V'}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) (ρ : ↥H →* ↥H')
    (hρ : Function.Surjective ρ) (hU' : ∀ x : ↥H', ∀ u ∈ U', (x : MulAut V') u ∈ U')
    (f : ↥U' ≃* ↥U)
    (hf : ∀ (x : ↥H) (u : ↥U'),
      ((f ⟨(ρ x : MulAut V') u, hU' (ρ x) u u.2⟩ : ↥U) : V) = (x : MulAut V) (f u)) :
    D.RealizesVia H' U' ⊥ (ρ.comp π) := by
  obtain ⟨hπs, -, hkerle, hUinv, -, hsec, hkinv, β, hβs, hβk, hβe⟩ := h
  refine ⟨hρ.comp hπs, bot_le, hkerle, hU', fun x z hz => ?_, hsec, hkinv,
    β.comp f.toMonoidHom, hβs.comp f.surjective, fun u => ?_, fun γ u m hu hm hβu => ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · change β (f u) = 1 ↔ _
    rw [hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      have : f u = 1 := Subtype.ext h1
      rw [(map_eq_one_iff f f.injective).mp this]
      rfl
    · intro h1
      have : u = 1 := Subtype.ext h1
      rw [this, map_one]
      rfl
  · change β (f ⟨((ρ (π γ) : ↥H') : MulAut V') (u : V'), hu⟩) = _
    have he : f ⟨((ρ (π γ) : ↥H') : MulAut V') (u : V'), hu⟩ =
        ⟨((π γ : ↥H) : MulAut V) (f u), hUinv _ _ (f u).2⟩ := Subtype.ext (hf (π γ) u)
    rw [he]
    exact hβe γ (f u) m _ hm hβu

theorem natOmegaMinus_transfer {V V' : Type} [CommGroup V] [CommGroup V']
    {H : Subgroup (MulAut V)} {H' : Subgroup (MulAut V')} {U : Subgroup V} {U' : Subgroup V'}
    {m a : ℕ} (h : NatOmegaMinus H U ⊥ m a) (ρ : ↥H →* ↥H') (hρ : Function.Surjective ρ)
    (hU' : ∀ x : ↥H', ∀ u ∈ U', (x : MulAut V') u ∈ U') (f : ↥U' ≃* ↥U)
    (hf : ∀ (x : ↥H) (u : ↥U'),
      ((f ⟨(ρ x : MulAut V') u, hU' (ρ x) u u.2⟩ : ↥U) : V) = (x : MulAut V) (f u)) :
    NatOmegaMinus H' U' ⊥ m a := by
  obtain ⟨hm, K, hKf, hKfin, b, c, hcard, hirr, π, hπ⟩ := h
  exact ⟨hm, K, hKf, hKfin, b, c, hcard, hirr, ρ.comp π, realizesVia_transfer hπ ρ hρ hU' f hf⟩

section Sum

variable {L : Subgroup (MulAut W)} {I J : Subgroup W} {k : ℕ}

private theorem inf_fixV_eq_bot_of_natOmegaMinus (hΩ : IsOmegaMinus ↥L 4 k)
    (hI : NatOmegaMinus L I ⊥ 4 k) : I ⊓ fixV L = ⊥ := by
  have hk : 1 ≤ k := one_le_of_natOmegaMinus_sec hI
  have := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) (isL2_two_mul_of_isOmegaMinus_four hk hΩ)
  have hst : StableUnder L (I ⊓ fixV L) := by
    intro x hx v hv
    refine ⟨stableUnder_of_natOmegaMinus hI x hx v hv.1, fun y hy => ?_⟩
    rw [hv.2 x hx]
    exact hv.2 y hy
  rcases eq_bot_or_eq_of_natOmegaMinus hI _ hst inf_le_left with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    apply hx1
    apply Subtype.ext
    refine eq_one_of_natOmegaMinus hI x x.2 fun v hv => ?_
    have hv' : v ∈ I ⊓ fixV L := by rw [h]; exact hv
    exact hv'.2 x x.2

private theorem sup_inf_fixV_eq_bot (hIJ : I ⊓ J = ⊥) (hIs : StableUnder L I)
    (hJs : StableUnder L J) (hI : I ⊓ fixV L = ⊥) (hJ : J ⊓ fixV L = ⊥) :
    (I ⊔ J) ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw, hwf⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  have hfa : ∀ x ∈ L, x a = a := by
    intro x hx
    have h := hwf x hx
    rw [map_mul] at h
    have hmem : x a * a⁻¹ ∈ I ⊓ J := by
      refine ⟨I.mul_mem (hIs x hx a ha) (I.inv_mem ha), ?_⟩
      have he : x a * a⁻¹ = b * (x b)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        have h' : x a = a * b * (x b)⁻¹ := by
          rw [← h]
          group
        rw [h']
        ac_rfl
      rw [he]
      exact J.mul_mem hb (J.inv_mem (hJs x hx b hb))
    rw [hIJ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hfb : ∀ x ∈ L, x b = b := by
    intro x hx
    have h := hwf x hx
    rw [map_mul, hfa x hx] at h
    exact mul_left_cancel h
  have ha1 : a = 1 := by
    have : a ∈ I ⊓ fixV L := ⟨ha, hfa⟩
    rwa [hI, Subgroup.mem_bot] at this
  have hb1 : b = 1 := by
    have : b ∈ J ⊓ fixV L := ⟨hb, hfb⟩
    rwa [hJ, Subgroup.mem_bot] at this
  rw [ha1, hb1, mul_one]
  exact one_mem _

private theorem eq_or_isCompl_of_le_sup (hI : NatOmegaMinus L I ⊥ 4 k)
    (hJ : NatOmegaMinus L J ⊥ 4 k) {M : Subgroup W} (hM : StableUnder L M) (hMle : M ≤ I ⊔ J) :
    M = ⊥ ∨ M = J ∨ M = I ⊔ J ∨ (M ⊓ J = ⊥ ∧ M ⊔ J = I ⊔ J) := by
  have hIs := stableUnder_of_natOmegaMinus hI
  have hJs := stableUnder_of_natOmegaMinus hJ
  have hinfst : ∀ {A B : Subgroup W}, StableUnder L A → StableUnder L B → StableUnder L (A ⊓ B) :=
    fun hA hB x hx v hv => ⟨hA x hx v hv.1, hB x hx v hv.2⟩
  have hsupst : ∀ {A B : Subgroup W}, StableUnder L A → StableUnder L B → StableUnder L (A ⊔ B) := by
    intro A B hA hB x hx v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hA x hx a ha) (hB x hx b hb)
  rcases eq_bot_or_eq_of_natOmegaMinus hJ _ (hinfst hM hJs) inf_le_right with hMJ | hMJ
  ·
    rcases eq_bot_or_eq_of_natOmegaMinus hI _ (hinfst (hsupst hM hJs) hIs) inf_le_right with
      hMI | hMI
    · left
      have h := sup_inf_assoc_of_le I (le_sup_right : J ≤ M ⊔ J)
      rw [sup_comm J I, inf_eq_right.mpr (sup_le hMle le_sup_right), inf_comm I, hMI,
        sup_bot_eq] at h
      rw [eq_bot_iff, ← hMJ]
      exact le_inf le_rfl (le_sup_left.trans h.le)
    · right; right; right
      refine ⟨hMJ, le_antisymm (sup_le hMle le_sup_right) (sup_le ?_ le_sup_right)⟩
      rw [← hMI]
      exact inf_le_left
  ·
    have hJM : J ≤ M := hMJ ▸ inf_le_left
    rcases eq_bot_or_eq_of_natOmegaMinus hI _ (hinfst hM hIs) inf_le_right with hMI | hMI
    · right; left
      have h := sup_inf_assoc_of_le I hJM
      rw [sup_comm J I, inf_eq_right.mpr hMle, inf_comm I, hMI, sup_bot_eq] at h
      exact h
    · right; right; left
      refine le_antisymm hMle (sup_le ?_ hJM)
      rw [← hMI]
      exact inf_le_left

private theorem exists_mulEquiv_of_isCompl {M : Subgroup W} (hIJ : I ⊓ J = ⊥) (hMJ : M ⊓ J = ⊥)
    (hMIJ : M ⊔ J = I ⊔ J) :
    ∃ f : ↥M ≃* ↥I, ∀ (x : MulAut W), x ∈ stabSub I → x ∈ stabSub J → ∀ (u : ↥M)
      (hu : x (u : W) ∈ M), ((f ⟨x u, hu⟩ : ↥I) : W) = x (f u) := by
  let q : W →* W ⧸ J := QuotientGroup.mk' J
  have hinj : ∀ {A : Subgroup W}, A ⊓ J = ⊥ → Function.Injective (q.comp A.subtype) := by
    intro A hA
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have : (a : W) ∈ A ⊓ J := ⟨a.2, ha⟩
    rw [hA, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : (q.comp M.subtype).range = (q.comp I.subtype).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.range_subtype]
    have hJ0 : J.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    calc M.map q = (M ⊔ J).map q := by rw [Subgroup.map_sup, hJ0, sup_bot_eq]
      _ = (I ⊔ J).map q := by rw [hMIJ]
      _ = I.map q := by rw [Subgroup.map_sup, hJ0, sup_bot_eq]
  let f : ↥M ≃* ↥I := (MonoidHom.ofInjective (hinj hMJ)).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective (hinj hIJ)).symm)
  have hf : ∀ u : ↥M, q (f u : W) = q (u : W) := by
    intro u
    have h := (MonoidHom.ofInjective (hinj hIJ)).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective (hinj hMJ) u))
    exact congrArg Subtype.val h
  refine ⟨f, fun x hxI hxJ u hu => ?_⟩
  have hxI' : x (f u : W) ∈ I := (hxI (f u : W)).2 (f u).2
  have hq : q ((f ⟨x u, hu⟩ : ↥I) : W) = q (x (f u : W)) := by
    rw [hf]
    have h1 := hf u
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1 ⊢
    have h2 : x ((f u : W)⁻¹ * (u : W)) ∈ J := (hxJ _).2 h1
    rw [map_mul, map_inv] at h2
    have h3 : (x u)⁻¹ * x (f u : W) ∈ J := by
      have := J.inv_mem h2
      simpa [mul_comm] using this
    exact h3
  have hdiff : ((f ⟨x u, hu⟩ : ↥I) : W) * (x (f u : W))⁻¹ ∈ I ⊓ J := by
    refine ⟨I.mul_mem (f _).2 (I.inv_mem hxI'), ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    have := J.inv_mem hq
    simpa [mul_comm] using this
  rw [hIJ, Subgroup.mem_bot, mul_inv_eq_one] at hdiff
  exact hdiff

private theorem natOmegaMinus_of_isCompl (hI : NatOmegaMinus L I ⊥ 4 k)
    (hJ : NatOmegaMinus L J ⊥ 4 k) (hIJ : I ⊓ J = ⊥) {M : Subgroup W} (hM : StableUnder L M)
    (hMJ : M ⊓ J = ⊥) (hMIJ : M ⊔ J = I ⊔ J) : NatOmegaMinus L M ⊥ 4 k := by
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_isCompl hIJ hMJ hMIJ
  have hIs := stableUnder_of_natOmegaMinus hI
  have hJs := stableUnder_of_natOmegaMinus hJ
  exact natOmegaMinus_transfer hI (MonoidHom.id ↥L) Function.surjective_id
    (fun x u hu => hM x x.2 u hu) f fun x u =>
      hf x (le_stabSub_of_stableUnder hIs x.2) (le_stabSub_of_stableUnder hJs x.2) u _

private theorem autSub_le_normalizer {L X : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : X ⊓ stabSub U ≤ normalizer (L : Set (MulAut W))) :
    autSub X U ≤ normalizer ((autSub L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
  intro φ hφ
  obtain ⟨g, hgX, rfl⟩ := mem_autSub.mp hφ
  have hgN := hX ⟨hgX, g.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨l, hlL, rfl⟩ := mem_autSub.mp hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_autSub.mpr ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN _).mp hlL, rfl⟩
  · intro hψ
    obtain ⟨l, hlL, hl⟩ := mem_autSub.mp hψ
    have hψ' : ψ = resHom U (g⁻¹ * l * g) := by
      rw [map_mul, map_mul, hl, map_inv]
      group
    rw [hψ']
    refine mem_autSub.mpr ⟨g⁻¹ * l * g, ?_, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN ((g⁻¹ * l * g : stabSub U) : MulAut W)).mpr
    apply h1
    simpa [mul_assoc] using hlL

theorem aParam_autSub_le_of_natOmegaMinus_sum [Finite W]
    {L X : Subgroup (MulAut W)} {I J M : Subgroup W} {k : ℕ}
    (hΩ : IsOmegaMinus ↥L 4 k) (hI : NatOmegaMinus L I ⊥ 4 k) (hJ : NatOmegaMinus L J ⊥ 4 k)
    (hIJ : I ⊓ J = ⊥) (hM : StableUnder L M) (hMle : M ≤ I ⊔ J)
    (hXN : X ⊓ stabSub M ≤ normalizer (L : Set (MulAut W))) :
    E3.aParam (autSub X M) ≤ k := by
  have hXM : autSub X M ≤ autSub (normalizer (L : Set (MulAut W))) M := by
    intro φ hφ
    obtain ⟨g, hgX, rfl⟩ := mem_autSub.mp hφ
    exact mem_autSub.mpr ⟨g, hXN ⟨hgX, g.2⟩, rfl⟩
  have hnat : NatOmegaMinus L M ⊥ 4 k → E3.aParam (autSub X M) ≤ k := fun h =>
    (E3.aParam_mono hXM).trans (aParam_autSub_normalizer_le_of_natOmegaMinus hΩ h)
  rcases eq_or_isCompl_of_le_sup hI hJ hM hMle with hM0 | hMJ' | hMIJ' | ⟨hMJ, hMIJ⟩
  ·
    subst hM0
    have : Subsingleton (MulAut ↥(⊥ : Subgroup W)) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    rw [E3.aParam_of_odd]
    · exact Nat.zero_le _
    · rw [Subgroup.eq_bot_of_subsingleton (autSub X ⊥), Subgroup.card_bot]
      decide
  · exact hnat (hMJ' ▸ hJ)
  ·
    subst hMIJ'
    have hLM : L ≤ stabSub (I ⊔ J) := le_stabSub_of_stableUnder hM
    have hinj : ∀ l ∈ L, (∀ u ∈ I ⊔ J, l u = u) → l = 1 := fun l hl h =>
      eq_one_of_natOmegaMinus hI l hl fun v hv => h v ((le_sup_left : I ≤ I ⊔ J) hv)
    let eL : ↥L ≃* ↥(autSub L (I ⊔ J)) := FFC.resEquiv hLM hinj
    have hst : ∀ {A : Subgroup W}, StableUnder L A →
        ∀ x : ↥(autSub L (I ⊔ J)), ∀ u ∈ A.subgroupOf (I ⊔ J),
          (x : MulAut ↥(I ⊔ J)) u ∈ A.subgroupOf (I ⊔ J) := by
      intro A hA x u hu
      obtain ⟨g, hgL, hg⟩ := mem_autSub.mp x.2
      rw [Subgroup.mem_subgroupOf, ← hg]
      exact hA g hgL u (Subgroup.mem_subgroupOf.mp hu)
    have htr : ∀ {A : Subgroup W} (hAle : A ≤ I ⊔ J) (hA : StableUnder L A),
        NatOmegaMinus L A ⊥ 4 k → NatOmegaMinus (autSub L (I ⊔ J)) (A.subgroupOf (I ⊔ J)) ⊥ 4 k :=
      fun hAle hA h => natOmegaMinus_transfer h eL.toMonoidHom eL.surjective (hst hA)
        (Subgroup.subgroupOfEquivOfLe hAle) fun _ _ => rfl
    have hI' := htr le_sup_left (stableUnder_of_natOmegaMinus hI) hI
    have hJ' := htr le_sup_right (stableUnder_of_natOmegaMinus hJ) hJ
    have hIJ' : I.subgroupOf (I ⊔ J) ⊓ J.subgroupOf (I ⊔ J) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : W) ∈ I ⊓ J := ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
      rw [hIJ, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
    have htop' : I.subgroupOf (I ⊔ J) ⊔ J.subgroupOf (I ⊔ J) = ⊤ := by
      apply Subgroup.map_injective (I ⊔ J).subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.mpr le_sup_left,
        inf_eq_left.mpr le_sup_right]
    have hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 k) (autSub L (I ⊔ J)) ⊤ ⊥ 2 := by
      refine ⟨![I.subgroupOf (I ⊔ J), J.subgroupOf (I ⊔ J)], fun _ => bot_le, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, bot_sup_eq]
          rw [← hIJ']
          refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
          fin_cases j
          · exact absurd rfl hj
          · exact le_rfl
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            bot_sup_eq]
          rw [← hIJ', inf_comm]
          refine inf_le_inf_right _ (iSup₂_le fun j hj => ?_)
          fin_cases j
          · exact le_rfl
          · exact absurd rfl hj
      · rw [bot_sup_eq, ← htop']
        refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup_of_le 0 le_rfl)
          (le_iSup_of_le 1 le_rfl))
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      · intro i
        fin_cases i
        · exact hI'
        · exact hJ'
    have hΩ' : IsOmegaMinus ↥(autSub L (I ⊔ J)) 4 k := IsOmegaMinus.of_mulEquiv eL hΩ
    have hN : autSub X (I ⊔ J) ⊔ autSub L (I ⊔ J) ≤
        normalizer ((autSub L (I ⊔ J) : Subgroup (MulAut ↥(I ⊔ J))) : Set (MulAut ↥(I ⊔ J))) :=
      sup_le (autSub_le_normalizer hXN) Subgroup.le_normalizer
    exact (E3.aParam_mono le_sup_left).trans
      (kNatOm4mATwo_holds ↥(I ⊔ J) _ _ k hΩ' hsum le_sup_right hN)
  · exact hnat (natOmegaMinus_of_isCompl hI hJ hIJ hM hMJ hMIJ)

theorem exists_compl_of_natOmegaMinus_sum {L : Subgroup (MulAut W)} {I J M : Subgroup W}
    {k : ℕ} (hΩ : IsOmegaMinus ↥L 4 k) (hI : NatOmegaMinus L I ⊥ 4 k)
    (hJ : NatOmegaMinus L J ⊥ 4 k) (hIJ : I ⊓ J = ⊥) (hM : StableUnder L M)
    (hMle : M ≤ I ⊔ J) :
    ∃ M' : Subgroup W, StableUnder L M' ∧ M ⊓ M' = ⊥ ∧ M ⊔ M' = I ⊔ J ∧ M' ⊓ fixV L = ⊥ := by
  have hIs := stableUnder_of_natOmegaMinus hI
  have hJs := stableUnder_of_natOmegaMinus hJ
  have hIf := inf_fixV_eq_bot_of_natOmegaMinus hΩ hI
  have hJf := inf_fixV_eq_bot_of_natOmegaMinus hΩ hJ
  rcases eq_or_isCompl_of_le_sup hI hJ hM hMle with hM0 | hMJ' | hMIJ' | ⟨hMJ, hMIJ⟩
  · subst hM0
    refine ⟨I ⊔ J, ?_, bot_inf_eq _, bot_sup_eq _, sup_inf_fixV_eq_bot hIJ hIs hJs hIf hJf⟩
    intro x hx v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hIs x hx a ha) (hJs x hx b hb)
  · subst hMJ'
    exact ⟨I, hIs, by rw [inf_comm, hIJ], sup_comm _ _, hIf⟩
  · subst hMIJ'
    exact ⟨⊥, fun x _ v hv => by rw [Subgroup.mem_bot] at hv ⊢; rw [hv, map_one], inf_bot_eq _,
      sup_bot_eq _, bot_inf_eq _⟩
  · exact ⟨J, hJs, hMJ, hMIJ, hJf⟩

end Sum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
