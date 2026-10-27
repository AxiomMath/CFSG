module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210j
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

variable {Γ : Type u} [Group Γ]

theorem scalJoin_semisimple
    [Finite Γ] {p : ℕ} {A G : Subgroup Γ} (h : NearAsolvAction p A G)
    (hss : IsSemisimple G) :
    scalJoin G A (cenIn G A) = mOf A G ∧ Group.IsSolvable (scalJoin G A (cenIn G A)) := by
  by_cases hG : G = ⊥
  · subst hG
    have h1 : scalJoin ⊥ A (cenIn ⊥ A) = ⊥ := scalJoin_bot _ _
    have h2 : mOf A ⊥ = ⊥ := le_bot_iff.mp inf_le_left
    rw [h1, h2]
    exact ⟨rfl, inferInstance⟩
  · have hSA : SemisimpleAction p A G := ⟨h, hss, hG⟩
    have hb := thm210b hSA
    have hDG : cenIn G A ≤ G := inf_le_left
    have hDA : cenIn G A ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
    have hnorm : cenIn G A ⊔ A ≤ Subgroup.normalizer (mOf A G : Set Γ) :=
      sup_le (le_normalizer_mOf (hDG.trans Subgroup.le_normalizer)
        (hDA.trans (Subgroup.centralizer_le_normalizer _)))
        (le_normalizer_mOf h.admits Subgroup.le_normalizer)
    have hGD : G ⊓ cenIn G A = cenIn G A := inf_eq_right.mpr hDG
    have hmem : mOf A G ∈ scalSet G A (cenIn G A) := by
      refine ⟨inf_le_left, ?_, hb.1.2.2⟩
      rw [hGD]
      exact hnorm
    have heq : scalJoin G A (cenIn G A) = mOf A G := by
      refine le_antisymm (scalJoin_le fun S hS => ?_) (le_scalJoin hmem)
      obtain ⟨hSG, hSE, hSs⟩ := hS
      rw [hGD] at hSE
      have hDS : cenIn G A ≤ Subgroup.normalizer (S : Set Γ) := le_sup_left.trans hSE
      have hsol : Group.IsSolvable (S ⊔ cenIn G A : Subgroup Γ) :=
        isSolvable_sup hDS h.solvable_cen hSs
      exact le_sup_left.trans (hb.2 ⟨sup_le hSG hDG, le_sup_right, hsol⟩)
    exact ⟨heq, heq ▸ hb.1.2.2⟩

@[expose] def Frattini211 (A G N : Subgroup Γ) : Prop :=
  ((N : Set Γ) * (norIn G (scalJoin N A (cenIn G A) : Set Γ) : Set Γ) = G) ∧
    ∀ X : Subgroup Γ, X ≤ G → Admits (cenIn G A ⊔ A) X → Group.IsSolvable (X ⊓ N : Subgroup Γ) →
      X ≤ Subgroup.normalizer (scalJoin N A (cenIn G A) : Set Γ)

@[expose] def IH211.{v} (p n : ℕ) : Prop :=
  ∀ m < n, ∀ {Γ : Type v} [Group Γ] [Finite Γ] (A G N : Subgroup Γ), Nat.card G = m →
    NearAsolvAction p A G → N ≤ G → IsNormalIn N (G ⊔ A) → Frattini211 A G N

theorem frattini211_bot (A G : Subgroup Γ) : Frattini211 A G ⊥ := by
  have hT : scalJoin ⊥ A (cenIn G A) = ⊥ := scalJoin_bot _ _
  rw [Frattini211, hT]
  refine ⟨?_, fun X _ _ _ => ?_⟩
  · have h1 : norIn G (((⊥ : Subgroup Γ) : Set Γ)) = G := by
      unfold norIn
      rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot, inf_top_eq]
    rw [h1]
    simp
  · rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
    exact le_top

theorem frattini211_of_sol_ne_bot [Finite Γ] {p : ℕ} {A G N : Subgroup Γ}
    (ih : IH211.{u} p (Nat.card G)) (h : NearAsolvAction p A G) (hNG : N ≤ G)
    (hN : IsNormalIn N (G ⊔ A)) (hsol : sol N ≠ ⊥) : Frattini211 A G N := by
  set R := sol N with hR
  have hRs : Group.IsSolvable R := isSolvable_sol N
  have hRN : R ≤ N := sol_le N
  have hnorm : G ⊔ A ≤ AChief.nrm R := hN.2.trans (SolQuot.normalizer_le_nrm_sol N)
  have hG : G ≤ AChief.nrm R := le_sup_left.trans hnorm
  have hA : A ≤ AChief.nrm R := le_sup_right.trans hnorm
  have hRG : R ≤ G := hRN.trans hNG
  have hNn : N ≤ AChief.nrm R := hNG.trans hG
  have hD : cenIn G A ≤ AChief.nrm R := inf_le_left.trans hG
  have hnear : NearAsolvAction p (AChief.qimg R A) (AChief.qimg R G) := nearAsolvAction_qimg h hG hA
  have hNb : AChief.qimg R N ≤ AChief.qimg R G := SolQuot.qimg_mono hNG
  have hNnorm : IsNormalIn (AChief.qimg R N) (AChief.qimg R G ⊔ AChief.qimg R A) := by
    refine ⟨hNb.trans le_sup_left, ?_⟩
    rw [← SolQuot.qimg_sup hG hA]
    exact AChief.qimg_le_normalizer hN.2
  have hcard := card_qimg_lt hRG hG hsol
  obtain ⟨key1, key2⟩ :=
    ih _ hcard (AChief.qimg R A) (AChief.qimg R G) (AChief.qimg R N) rfl hnear hNb hNnorm
  have hDbar : cenIn (AChief.qimg R G) ((AChief.qimg R A : Subgroup (AChief.QG R)) :
      Set (AChief.QG R)) = AChief.qimg R (cenIn G A) :=
    (AChief.qimg_inf_centralizer h.prime h.elemAbelian h.admits hA hG h.nearPSolvable.1).symm
  have hT : scalJoin (AChief.qimg R N) (AChief.qimg R A) (cenIn (AChief.qimg R G)
      ((AChief.qimg R A : Subgroup (AChief.QG R)) : Set (AChief.QG R))) =
        AChief.qimg R (scalJoin N A (cenIn G A)) := by
    rw [hDbar]
    exact (qimg_scalJoin hRs hRN hNn hA).symm
  have hRT : R ≤ scalJoin N A (cenIn G A) :=
    le_scalJoin_of_admits hRN (sup_le (inf_le_left.trans hNn) hA) hRs
  have hTG : scalJoin N A (cenIn G A) ≤ G := (scalJoin_le_left _ _ _).trans hNG
  have hGR : G ⊓ R ≤ scalJoin N A (cenIn G A) := inf_le_right.trans hRT
  rw [hT] at key1 key2
  refine ⟨?_, fun X hXG hX hXN => ?_⟩
  · refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨n, hn, m, hm, rfl⟩
      exact mul_mem (hNG hn) (Subgroup.mem_inf.mp hm).1
    · intro g hg
      have hgb : AChief.qmap R ⟨g, hG hg⟩ ∈ ((AChief.qimg R G : Subgroup (AChief.QG R)) :
          Set (AChief.QG R)) := (AChief.mem_qimg_iff R G _).mpr ⟨⟨g, hG hg⟩, hg, rfl⟩
      rw [← key1] at hgb
      obtain ⟨nb, hnb, mb, hmb, hnm⟩ := hgb
      obtain ⟨n, hn, rfl⟩ := (AChief.mem_qimg_iff R N nb).mp hnb
      obtain ⟨hmbG, hmbT⟩ := Subgroup.mem_inf.mp hmb
      obtain ⟨m', hm', rfl⟩ := (AChief.mem_qimg_iff R G mb).mp hmbG
      have hnm' : AChief.qmap R (n * m') = AChief.qmap R ⟨g, hG hg⟩ := by
        rw [map_mul]
        exact hnm
      obtain ⟨r, hr, hgr⟩ := exists_mem_of_qmap_eq hnm'
      have hm'T : (m' : Γ) ∈ Subgroup.normalizer (scalJoin N A (cenIn G A) : Set Γ) :=
        (SolQuot.mem_normalizer_qimg_iff hTG hGR hG hm').mp hmbT
      have hrT : r ∈ Subgroup.normalizer (scalJoin N A (cenIn G A) : Set Γ) :=
        Subgroup.le_normalizer (hRT hr)
      refine ⟨n, hn, (m' : Γ) * r, Subgroup.mem_inf.mpr ⟨mul_mem hm' (hRG hr),
        mul_mem hm'T hrT⟩, ?_⟩
      simp only [Subgroup.coe_mul] at hgr
      exact (mul_assoc (n : Γ) (m' : Γ) r).symm.trans hgr.symm
  · have hX' : AChief.qimg R X ≤ AChief.qimg R G := SolQuot.qimg_mono hXG
    have hXadm : Admits (cenIn (AChief.qimg R G) ((AChief.qimg R A : Subgroup (AChief.QG R)) :
        Set (AChief.QG R)) ⊔ AChief.qimg R A) (AChief.qimg R X) := by
      rw [hDbar, ← SolQuot.qimg_sup hD hA]
      exact AChief.qimg_le_normalizer hX
    have hXN' : Group.IsSolvable (AChief.qimg R X ⊓ AChief.qimg R N :
        Subgroup (AChief.QG R)) := by
      rw [← SolQuot.qimg_inf_of_le hNn hRN]
      exact (SolQuot.isSolvable_qimg_iff hRs (inf_le_left.trans (hXG.trans hG))).mpr hXN
    have := key2 _ hX' hXadm hXN'
    exact (SolQuot.qimg_le_normalizer_iff hTG hGR hG hXG).mp this

theorem le_normalizer_mOf_of_solvable_inf
    [Finite Γ] {p : ℕ} {A K V : Subgroup Γ}
    (hKss : SemisimpleAction p A K) (hVK : V ≤ Subgroup.normalizer (K : Set Γ))
    (hDV : cenIn K A ≤ V) (hV : Group.IsSolvable (V ⊓ K : Subgroup Γ)) :
    V ≤ Subgroup.normalizer (mOf A K : Set Γ) := by
  obtain ⟨hMe, -⟩ := thm210e hKss (inf_le_right : V ⊓ K ≤ K) hV
    (le_inf hDV inf_le_left)
  intro v hv
  rw [hMe]
  refine inf_normalizer_le_normalizer_norIn_cenIn K (CFSG.fittingSubgroupOf (V ⊓ K))
    ⟨hVK hv, normalizer_le_normalizer_fitting _ ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hv, hVK hv⟩

theorem frattini211_of_sol_eq_bot
    [Finite Γ] {p : ℕ} {A G N : Subgroup Γ}
    (ih : IH211.{u} p (Nat.card G)) (h : NearAsolvAction p A G) (hNG : N ≤ G)
    (hN : IsNormalIn N (G ⊔ A)) (hsol : sol N = ⊥) (hbot : N ≠ ⊥) : Frattini211 A G N := by
  set D := cenIn G A with hD
  set K := kOf N with hK
  have hKN : K ≤ N := kOf_le N
  have hKne : K ≠ ⊥ := kOf_ne_bot hsol hbot
  have hKss : IsSemisimple K := isSemisimple_kOf hsol
  have hGAK : G ⊔ A ≤ Subgroup.normalizer (K : Set Γ) :=
    hN.2.trans (normalizer_le_normalizer_kOf N)
  have hGK : G ≤ Subgroup.normalizer (K : Set Γ) := le_sup_left.trans hGAK
  have hAK : A ≤ Subgroup.normalizer (K : Set Γ) := le_sup_right.trans hGAK
  have hKG : K ≤ G := hKN.trans hNG
  have hSA : SemisimpleAction p A K := ⟨nearAsolvAction_of_le h hKG hAK, hKss, hKne⟩
  set M := mOf A K with hM
  have hMK : M ≤ K := inf_le_left
  have hDG : D ≤ G := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hKD : K ⊓ D = cenIn K A := inf_cenIn_eq hKG
  have hDs : Group.IsSolvable D := h.solvable_cen
  have hDM : D ≤ Subgroup.normalizer (M : Set Γ) :=
    le_normalizer_mOf (hDG.trans hGK) (hDA.trans (Subgroup.centralizer_le_normalizer _))
  have hAM : A ≤ Subgroup.normalizer (M : Set Γ) := le_normalizer_mOf hAK Subgroup.le_normalizer
  have hP : ∀ V : Subgroup Γ, V ≤ G → K ⊓ D ≤ V → Group.IsSolvable (V ⊓ K : Subgroup Γ) →
      V ≤ Subgroup.normalizer (M : Set Γ) := fun V hVG hKV hV =>
    le_normalizer_mOf_of_solvable_inf hSA (hVG.trans hGK) (hKD ▸ hKV) hV
  set G₁ := norIn G (M : Set Γ) with hG₁
  have hG₁G : G₁ ≤ G := inf_le_left
  have hDG₁ : D ≤ G₁ := le_inf hDG hDM
  have hAG₁ : Admits A G₁ := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.admits ha, Subgroup.le_normalizer (hAM ha)⟩
  have hnear₁ : NearAsolvAction p A G₁ := nearAsolvAction_of_le h hG₁G hAG₁
  have hcen₁ : cenIn G₁ A = D := cenIn_eq_of_le hG₁G hDG₁
  have hG₁ne : G₁ ≠ G := by
    intro heq
    have hGM : G ≤ Subgroup.normalizer (M : Set Γ) := by
      rw [← heq]
      exact inf_le_right
    have hMs : Group.IsSolvable M := (thm210b hSA).1.2.2
    have h1 : N ⊓ M ≤ sol N := SolQuot.inf_le_sol hMs (hNG.trans hGM)
    have hM0 : M = ⊥ := by
      rw [eq_bot_iff, ← hsol]
      exact (le_inf (hMK.trans hKN) le_rfl : M ≤ N ⊓ M).trans h1
    exact mOf_ne_bot hSA hM0
  have hcard : Nat.card G₁ < Nat.card G := card_lt_of_ne hG₁G hG₁ne
  set N₁ := N ⊓ G₁ with hN₁
  have hN₁G₁ : N₁ ≤ G₁ := inf_le_right
  have hN₁N : N₁ ≤ N := inf_le_left
  have hN₁norm : IsNormalIn N₁ (G₁ ⊔ A) := by
    refine ⟨hN₁G₁.trans le_sup_left, fun g hg => ?_⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hN.2 (sup_le_sup_right hG₁G A hg), (sup_le Subgroup.le_normalizer hAG₁) hg⟩
  have hN₁D : N₁ ⊓ D = N ⊓ D := by
    rw [hN₁, inf_assoc, inf_eq_right.mpr hDG₁]
  obtain ⟨key1, key2⟩ := ih _ hcard A G₁ N₁ rfl hnear₁ hN₁G₁ hN₁norm
  rw [hcen₁] at key1 key2
  have hscal : scalSet N A D = scalSet N₁ A D := by
    ext S
    constructor
    · rintro ⟨hSN, hSE, hSs⟩
      have hDKN : D ⊓ K ≤ Subgroup.normalizer (S : Set Γ) :=
        ((le_inf (inf_le_right.trans hKN) inf_le_left : D ⊓ K ≤ N ⊓ D).trans le_sup_left).trans hSE
      have hsolV : Group.IsSolvable ((S ⊔ (D ⊓ K)) ⊓ K : Subgroup Γ) :=
        isSolvable_sup_inf hDKN (isSolvable_of_le inf_le_left hDs)
          (isSolvable_of_le inf_le_left hSs)
      have hVnorm := hP (S ⊔ (D ⊓ K)) (sup_le (hSN.trans hNG) (inf_le_left.trans hDG))
        ((inf_comm K D).le.trans le_sup_right) hsolV
      refine ⟨le_inf hSN (le_inf (hSN.trans hNG) (le_sup_left.trans hVnorm)), ?_, hSs⟩
      rw [hN₁D]
      exact hSE
    · rintro ⟨hSN₁, hSE, hSs⟩
      refine ⟨hSN₁.trans hN₁N, ?_, hSs⟩
      rw [hN₁D] at hSE
      exact hSE
  have hTeq : scalJoin N A D = scalJoin N₁ A D := by
    unfold scalJoin
    rw [hscal]
  rw [← hTeq] at key1 key2
  refine ⟨?_, fun X hXG hX hXN => ?_⟩
  ·
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨n, hn, m, hm, rfl⟩
      exact mul_mem (hNG hn) (Subgroup.mem_inf.mp hm).1
    · intro g hg
      have hgK : g ∈ Subgroup.normalizer (K : Set Γ) := hGK hg
      obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥K, ∀ t : K, ((φ t : K) : Γ) = g * t * g⁻¹ :=
        ⟨K.normalizerMonoidHom ⟨g, hgK⟩, fun t =>
          Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hgK⟩ t⟩
      obtain ⟨k, hk⟩ := thm210d hSA φ
      have hkg : (k : Γ) * g ∈ Subgroup.normalizer (M : Set Γ) := by
        refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        have hxK : x ∈ K := hMK hx
        have h1 : (MulAut.conj k) (φ ⟨x, hxK⟩) ∈
            ((M.subgroupOf K).map φ.toMonoidHom).map (MulAut.conj k).toMonoidHom :=
          ⟨φ ⟨x, hxK⟩, ⟨⟨x, hxK⟩, hx, rfl⟩, rfl⟩
        rw [hk] at h1
        have h2 := Subgroup.mem_subgroupOf.mp h1
        have h3 : (((MulAut.conj k) (φ ⟨x, hxK⟩) : K) : Γ) =
            (k : Γ) * (g * x * g⁻¹) * (k : Γ)⁻¹ := by
          rw [MulAut.conj_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
        rw [h3] at h2
        have h4 : (k : Γ) * g * x * ((k : Γ) * g)⁻¹ = (k : Γ) * (g * x * g⁻¹) * (k : Γ)⁻¹ := by
          group
        rw [h4]
        exact h2
      have hkg1 : (k : Γ) * g ∈ G₁ := Subgroup.mem_inf.mpr ⟨mul_mem (hKG k.2) hg, hkg⟩
      have hmem : (k : Γ) * g ∈ ((N₁ : Set Γ) *
          (norIn G₁ (scalJoin N A D : Set Γ) : Set Γ)) := by
        rw [key1]
        exact hkg1
      obtain ⟨n₁, hn₁, m, hm, hnm⟩ := hmem
      have hmG₁ := Subgroup.mem_inf.mp hm
      refine ⟨(k : Γ)⁻¹ * n₁, mul_mem (inv_mem (hKN k.2)) (hN₁N hn₁), m,
        Subgroup.mem_inf.mpr ⟨hG₁G hmG₁.1, hmG₁.2⟩, ?_⟩
      have hnm' : n₁ * m = (k : Γ) * g := hnm
      show (k : Γ)⁻¹ * n₁ * m = g
      rw [mul_assoc, hnm']
      group
  · have hDX : D ≤ Subgroup.normalizer (X : Set Γ) := le_sup_left.trans hX
    have hXK : Group.IsSolvable (X ⊓ K : Subgroup Γ) :=
      isSolvable_of_le (inf_le_inf_left _ hKN) hXN
    have hsolV : Group.IsSolvable ((X ⊔ D) ⊓ K : Subgroup Γ) := isSolvable_sup_inf hDX hDs hXK
    have hVnorm := hP (X ⊔ D) (sup_le hXG hDG) (inf_le_right.trans le_sup_right)
      hsolV
    have hXG₁ : X ≤ G₁ := le_inf hXG (le_sup_left.trans hVnorm)
    exact key2 X hXG₁ hX (isSolvable_of_le (inf_le_inf_left _ hN₁N) hXN)

theorem frattini211 {p : ℕ} (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] (A G N : Subgroup Γ), Nat.card G = n →
      NearAsolvAction p A G → N ≤ G → IsNormalIn N (G ⊔ A) → Frattini211 A G N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ _ _ A G N hn h hNG hN
    subst hn
    by_cases hb : N = ⊥
    · subst hb
      exact frattini211_bot A G
    · by_cases hs : sol N = ⊥
      · exact frattini211_of_sol_eq_bot ih h hNG hN hs hb
      · exact frattini211_of_sol_ne_bot ih h hNG hN hs

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211
