module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Near.AssocSup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm33Transport
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaLInf
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm311bAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma25
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemmas
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {Y : Subgroup G}

namespace Thm311b

omit [Finite G] in
theorem le_normalizer_of_mem_pairsP {P : Subgroup G × Subgroup G} (hP : P ∈ pairsP p A θ) :
    P.1 ≤ Subgroup.normalizer (P.2 : Set G) :=
  le_sup_left.trans (le_sup_left.trans hP.2.2.1.1.2)

omit [Finite G] in
theorem snd_le_fst_of_mem_pairsP {P : Subgroup G × Subgroup G} (hP : P ∈ pairsP p A θ) :
    P.2 ≤ P.1 :=
  hP.2.2.1.2.2.1.le

theorem sup_dsub_mem_cset (hθ : NearFunctor p A θ) {P : Subgroup G × Subgroup G}
    (hP : P ∈ pairsY p A θ Y) : P.1 ⊔ dsub A θ ∈ cset p A θ Y :=
  ⟨sup_dsub_mem_mtil hθ hP.1.1, P, hP, le_sup_left⟩

theorem le_thetaMG_of_mem (hθ : NearFunctor p A θ) {P : Subgroup G × Subgroup G}
    (hP : P ∈ pairsY p A θ Y) : P.1 ≤ thetaMG p A θ Y :=
  le_iSup₂_of_le (P.1 ⊔ dsub A θ) (sup_dsub_mem_cset hθ hP)
    (le_iSup₂_of_le P ⟨hP, le_sup_left⟩ le_rfl)

theorem le_thetaLG_of_mem (hθ : NearFunctor p A θ) {P : Subgroup G × Subgroup G}
    (hP : P ∈ pairsY p A θ Y) : P.2 ≤ thetaLG p A θ Y :=
  le_iSup₂_of_le (P.1 ⊔ dsub A θ) (sup_dsub_mem_cset hθ hP)
    (le_iSup₂_of_le P ⟨hP, le_sup_left⟩ le_rfl)

omit [Finite G] in
theorem thetaLG_le_of_forall {N : Subgroup G}
    (h : ∀ P ∈ pairsY p A θ Y, P.2 ≤ N) : thetaLG p A θ Y ≤ N :=
  iSup₂_le fun _ _ => iSup₂_le fun P hP => h P hP.1

omit [Finite G] in
theorem thetaMG_le_of_forall {N : Subgroup G}
    (h : ∀ P ∈ pairsY p A θ Y, P.1 ≤ N) : thetaMG p A θ Y ≤ N :=
  iSup₂_le fun _ _ => iSup₂_le fun P hP => h P hP.1

omit [Finite G] in
theorem thetaM_mono {X X' : Subgroup G} (h : X ≤ X') :
    thetaM p A θ Y X ≤ thetaM p A θ Y X' :=
  iSup₂_le fun P hP => le_iSup₂_of_le P ⟨hP.1, hP.2.trans h⟩ le_rfl

omit [Finite G] in
theorem thetaL_le_self (X : Subgroup G) : thetaL p A θ Y X ≤ X :=
  iSup₂_le fun _ hP => (snd_le_fst_of_mem_pairsP hP.1.1).trans hP.2

omit [Finite G] in
theorem admits_thetaL (X : Subgroup G) : Admits A (thetaL p A θ Y X) :=
  Admits.iSup fun _ => Admits.iSup fun hP => hP.1.1.2.1.1.1

omit [Finite G] in
theorem mem_cset_of_le {X X' : Subgroup G} (hX : X ∈ cset p A θ Y) (h : X ≤ X')
    (hX' : X' ∈ mtil p A θ) : X' ∈ cset p A θ Y := by
  obtain ⟨-, P, hP⟩ := hX
  exact ⟨hX', P, hP.1, hP.2.trans h⟩

theorem thetaM_le_normalizer_thetaL
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    {X : Subgroup G} (hX : X ∈ cset p A θ Y) :
    thetaM p A θ Y X ≤ Subgroup.normalizer (thetaL p A θ Y X : Set G) :=
  le_normalizer_of_mem_pairsP (thetaM_thetaL_mem_pairsYX' hθ hY hX).1.1

def wB (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (Y B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), thetaL p A θ Y (θ b)

def vT (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (Y : Subgroup G) : Subgroup G :=
  ⨆ (t : G) (_ : t ∈ A) (_ : t ≠ 1) (_ : θ t ∈ cset p A θ Y), thetaL p A θ Y (θ t)

omit [Finite G] in
theorem apply_mem_cset (hθ : NearFunctor p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : thetaOf θ B ∈ cset p A θ Y) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    θ b ∈ cset p A θ Y :=
  mem_cset_of_le hB (thetaOf_le_apply hb hb1) (apply_mem_mtil hθ (hBA hb) hb1)

theorem thetaL_le_wB
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hBcard : p ^ 2 ≤ Nat.card B)
    (hB : ∀ b ∈ B, b ≠ 1 → θ b ∈ cset p A θ Y) {t : G} (ht : t ∈ A) (ht1 : t ≠ 1)
    (hT : θ t ∈ cset p A θ Y) : thetaL p A θ Y (θ t) ≤ wB p A θ Y B := by
  set L := thetaL p A θ Y (θ t) with hL
  have hLt : L ≤ θ t := thetaL_le_self _
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans (admits_thetaL (θ t))
  have hLcop : Nat.Coprime p (Nat.card L) :=
    (hθ.isFunctor.coprime t ht ht1).coprime_dvd_right (Subgroup.card_dvd_of_le hLt)
  have hgen := iSup_centralizer_nonidentity hθ.prime
    (Thm32.isElemAbelian_of_le hθ.elemAbelian hBA) hBcard hBL hLcop
  calc L = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), L ⊓ Subgroup.centralizer ({b} : Set G) := hgen.symm
    _ ≤ wB p A θ Y B := by
      refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
      refine le_trans ?_ (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl))
      have hbA : b ∈ A := hBA hb
      have hh := thetaL_inf' hθ hY ht ht1 hbA hb1 hT (hB b hb hb1)
      intro x hx
      obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxb : x ∈ θ b := hθ.isFunctor.balance t ht ht1 b hbA hb1
        (Subgroup.mem_inf.mpr ⟨hLt hxL, hxC⟩)
      have : x ∈ thetaL p A θ Y (θ t) ⊓ θ b := Subgroup.mem_inf.mpr ⟨hxL, hxb⟩
      rw [hh] at this
      exact (Subgroup.mem_inf.mp this).2

theorem vT_le_wB
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hBcard : p ^ 2 ≤ Nat.card B)
    (hB : ∀ b ∈ B, b ≠ 1 → θ b ∈ cset p A θ Y) : vT p A θ Y ≤ wB p A θ Y B :=
  iSup_le fun _ => iSup_le fun ht => iSup_le fun ht1 => iSup_le fun hT =>
    thetaL_le_wB hθ hY hBA hBcard hB ht ht1 hT

omit [Finite G] in
theorem wB_le_thetaLG {B : Subgroup G} (hB : ∀ b ∈ B, b ≠ 1 → θ b ∈ cset p A θ Y) :
    wB p A θ Y B ≤ thetaLG p A θ Y :=
  iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
    le_iSup₂_of_le (θ b) (hB b hb hb1) le_rfl

omit [Finite G] in
theorem vT_le_thetaLG : vT p A θ Y ≤ thetaLG p A θ Y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hT =>
    le_iSup₂_of_le _ hT le_rfl

theorem thetaM_le_normalizer_wB
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    {B : Subgroup G} (hBA : B ≤ A) (hB : thetaOf θ B ∈ cset p A θ Y) :
    thetaM p A θ Y (thetaOf θ B) ≤ Subgroup.normalizer (wB p A θ Y B : Set G) := by
  have : Admits (thetaM p A θ Y (thetaOf θ B)) (wB p A θ Y B) :=
    Admits.iSup fun b => Admits.iSup fun hb => Admits.iSup fun hb1 =>
      (thetaM_mono (thetaOf_le_apply hb hb1)).trans
        (thetaM_le_normalizer_thetaL hθ hY (apply_mem_cset hθ hBA hB hb hb1))
  exact this

theorem exists_family_theta
    (hθ : NearFunctor p A θ) {X₁ X₂ : Subgroup G}
    (hP : (X₁, X₂) ∈ pairsY p A θ Y) :
    ∃ 𝒰 : Set (Subgroup G), 𝒰.Nonempty ∧
      (∀ B ∈ 𝒰, B ≤ A ∧ Nat.card A = p * Nat.card B ∧
        (cenIn X₁ (B : Set G), cenIn X₂ (B : Set G)) ∈ pairsY p A θ Y ∧
        cenIn X₁ (B : Set G) ≤ thetaOf θ B ∧
        ∀ d ∈ B, d ≠ 1 → (cenIn X₁ ({d} : Set G), cenIn X₂ ({d} : Set G)) ∈ pairsY p A θ Y ∧
          cenIn X₁ ({d} : Set G) ≤ θ d) ∧
      X₁ ≤ X₂ ⊔ ⨆ B ∈ 𝒰, cenIn X₁ (B : Set G) := by
  set X := X₁ ⊔ dsub A θ with hX
  have hXm : X ∈ mtil p A θ := sup_dsub_mem_mtil hθ hP.1.1
  have hact := Thm33a.nearAsolvAction_of_mem_mtil hθ hXm
  have hPi : (X₁, X₂) ∈ iPairsY A X Y := by
    rw [← pairsYX_eq_iPairsY hθ hXm]
    exact ⟨hP, le_sup_left⟩
  obtain ⟨𝒰, hne, hspec, hgen⟩ := exists_family hact hPi
  have hX₁ : X₁ ∈ assoc p A θ := hP.1.1.1
  refine ⟨𝒰, hne, fun B hB => ?_, hgen⟩
  obtain ⟨hBA, hcard, hpair, hd⟩ := hspec B hB
  refine ⟨hBA, hcard, ?_, inf_centralizer_le_thetaOf hX₁ hBA, fun d hdB hd1 => ?_⟩
  · have := hpair
    rw [← pairsYX_eq_iPairsY hθ hXm] at this
    exact this.1
  · have := hd d hdB hd1
    rw [← pairsYX_eq_iPairsY hθ hXm] at this
    exact ⟨this.1, hX₁.2.2.1 d (hBA hdB) hd1⟩

theorem thetaLG_le_vT
    (hθ : NearFunctor p A θ) (hrank : Nat.card A = p ^ 3) :
    thetaLG p A θ Y ≤ vT p A θ Y := by
  refine thetaLG_le_of_forall fun P hP => ?_
  obtain ⟨X₁, X₂⟩ := P
  obtain ⟨𝒰, ⟨B, hB⟩, hspec, -⟩ := exists_family_theta hθ hP
  obtain ⟨hBA, hcard, -, -, hd⟩ := hspec B hB
  have hp : p.Prime := hθ.prime
  have hBc : Nat.card B = p ^ 2 :=
    Nat.eq_of_mul_eq_mul_left hp.pos (by rw [← hcard, hrank]; ring)
  have hX₂ : X₂ ∈ assoc p A θ := hP.1.2.1.1
  have hBX₂ : B ≤ Subgroup.normalizer (X₂ : Set G) := hBA.trans hX₂.1
  have hgen := iSup_centralizer_nonidentity hp (Thm32.isElemAbelian_of_le hθ.elemAbelian hBA)
    (hBc ▸ le_rfl) hBX₂ hX₂.2.1
  show X₂ ≤ vT p A θ Y
  calc X₂ = ⨆ (d : G) (_ : d ∈ B) (_ : d ≠ 1), X₂ ⊓ Subgroup.centralizer ({d} : Set G) :=
        hgen.symm
    _ ≤ vT p A θ Y := by
      refine iSup₂_le fun d hdB => iSup_le fun hd1 => ?_
      obtain ⟨hpair, hX₁d⟩ := hd d hdB hd1
      have hdA : d ∈ A := hBA hdB
      have hpairX : (cenIn X₁ ({d} : Set G), cenIn X₂ ({d} : Set G)) ∈ pairsYX p A θ Y (θ d) :=
        ⟨hpair, hX₁d⟩
      have hcset : θ d ∈ cset p A θ Y := ⟨apply_mem_mtil hθ hdA hd1, _, hpairX⟩
      exact le_iSup₂_of_le d hdA (le_iSup₂_of_le hd1 hcset
        (le_iSup₂_of_le _ hpairX le_rfl))

end Thm311b

theorem thetaMG_le_normalizer_thetaLG'
    (hθ : NearFunctor p A θ) (hrank : Nat.card A = p ^ 3)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ)
    (_hc : IsCompleteIn (signalizers p A (thetaYFun p A θ Y) (NearASolvable p A))) :
    thetaMG p A θ Y ≤ Subgroup.normalizer (thetaLG p A θ Y : Set G) := by
  have hp : p.Prime := hθ.prime
  have hWV : thetaLG p A θ Y = Thm311b.vT p A θ Y :=
    le_antisymm (Thm311b.thetaLG_le_vT hθ hrank) Thm311b.vT_le_thetaLG
  refine Thm311b.thetaMG_le_of_forall fun P hP => ?_
  obtain ⟨X₁, X₂⟩ := P
  obtain ⟨𝒰, -, hspec, hgen⟩ := Thm311b.exists_family_theta hθ hP
  show X₁ ≤ Subgroup.normalizer (thetaLG p A θ Y : Set G)
  refine hgen.trans (sup_le ((Thm311b.le_thetaLG_of_mem hθ hP).trans Subgroup.le_normalizer)
    (iSup₂_le fun B hB => ?_))
  obtain ⟨hBA, hcard, hpair, hle, -⟩ := hspec B hB
  have hBc : Nat.card B = p ^ 2 :=
    Nat.eq_of_mul_eq_mul_left hp.pos (by rw [← hcard, hrank]; ring)
  have hB1 : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hBc
    exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hBc
  have hHm : thetaOf θ B ∈ mtil p A θ := thetaOf_mem_mtil hθ hBA hB1
  have hpairX : (cenIn X₁ (B : Set G), cenIn X₂ (B : Set G)) ∈ pairsYX p A θ Y (thetaOf θ B) :=
    ⟨hpair, hle⟩
  have hHc : thetaOf θ B ∈ cset p A θ Y := ⟨hHm, _, hpairX⟩
  have hall : ∀ b ∈ B, b ≠ 1 → θ b ∈ cset p A θ Y := fun b hb hb1 =>
    Thm311b.apply_mem_cset hθ hBA hHc hb hb1
  have hWB : Thm311b.wB p A θ Y B = thetaLG p A θ Y :=
    le_antisymm (Thm311b.wB_le_thetaLG hall)
      (hWV ▸ Thm311b.vT_le_wB hθ hY hBA (hBc ▸ le_rfl) hall)
  have hM := Thm311b.thetaM_le_normalizer_wB hθ hY hBA hHc
  rw [hWB] at hM
  exact (le_iSup₂_of_le _ hpairX le_rfl).trans hM

end CFSG.SignalizerFunctorTheorem.McBride.Near
