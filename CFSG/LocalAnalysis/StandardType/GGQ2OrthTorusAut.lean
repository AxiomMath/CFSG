module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutBasic
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutCoord
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneMoveExp
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutExt
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent
import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {δ : Fin 2}

private theorem ota_card_extSupport_liftV (e : PlaneRaw.V t) :
    (PlaneRaw.Code.extSupport (liftV t δ e)).card = (PlaneRaw.Code.extSupport e).card := by
  refine (Finset.card_bij (s := PlaneRaw.Code.extSupport e)
    (t := PlaneRaw.Code.extSupport (liftV t δ e))
    (fun j _ => Fin.castAdd δ.val j) ?_ ?_ ?_).symm
  · intro j hj
    rw [PlaneRaw.mem_extSupport] at hj ⊢
    simpa [liftV, Fin.append_left] using hj
  · intro a _ b _ hab
    exact Fin.castAdd_inj.mp hab
  · intro b hb
    rw [PlaneRaw.mem_extSupport] at hb
    revert hb
    refine Fin.addCases (motive := fun b => liftV t δ e b ≠ 0 →
      ∃ a, ∃ _ : a ∈ PlaneRaw.Code.extSupport e, Fin.castAdd δ.val a = b) ?_ ?_ b
    · intro a ha
      exact ⟨a, (PlaneRaw.mem_extSupport e a).mpr
        (by simpa [liftV, Fin.append_left] using ha), rfl⟩
    · intro j hzero
      exact False.elim (hzero (by simp [liftV, Fin.append_right]))

private theorem ota_exists_eq_castAdd_of_not_mem_liftSupport {S : Finset (Fin t)}
    {k : Fin (t + δ.val)} (hk : k ∉ liftSupport t δ S) :
    ∃ j : Fin t, k = Fin.castAdd δ.val j ∧ j ∉ S := by
  revert hk
  refine Fin.addCases (motive := fun k => k ∉ liftSupport t δ S →
    ∃ j : Fin t, k = Fin.castAdd δ.val j ∧ j ∉ S) ?_ ?_ k
  · intro j hk
    refine ⟨j, rfl, fun hj => hk ?_⟩
    rw [liftSupport]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_map_of_mem (Fin.castAddEmb δ.val) hj))
  · intro j hk
    refine absurd ?_ hk
    rw [liftSupport]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_map_of_mem (Fin.natAddEmb t) (Finset.mem_univ j)))

private theorem ota_moveExp_mem_oTorusAut (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (ht : 3 ≤ t + δ.val)
    {X : Subgroup ↥(omegaQ (K := K) t δ)} {π : Equiv.Perm (Fin t)} {η : Fin t → Bool}
    (hpar : δ.val = 0 → Even (Finset.univ.filter fun i => η i = true).card)
    (hX : ∀ y : ↥(omegaQ (K := K) t δ),
      (∀ u, (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u *
        (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)⁻¹ =
          otau ζ t δ (ChoiceTwo.moveExp π η u)) →
      (∀ j : Fin t, π j = j → η j = false →
        ∀ k : Fin (t + δ.val) ⊕ Fin (t + δ.val), Sum.elim id id k = Fin.castAdd δ.val j →
          ((y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ Pi.single k 1 = Pi.single k 1) →
      y ∈ X)
    {ψ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hψ : ⇑ψ = ChoiceTwo.moveExp π η) :
    ψ ∈ oTorusAut ζ t δ X := by
  obtain ⟨y, hy, hconj, hfix⟩ := exists_omegaQ_conj_otau_moveExp hK hζ hQ hnd ht π η hpar
  refine ⟨⟨y, hy⟩, hX ⟨y, hy⟩ hconj hfix, fun u => ?_⟩
  rw [hψ]
  exact hconj u

omit [Finite K] [CharP K 2] in
private theorem ota_mem_oBlockGroup_zero_of_fix {S : Finset (Fin t)}
    (hSp : omegaQ (K := K) t δ ≤ StatedSp (t + δ.val) K)
    {y : ↥(omegaQ (K := K) t δ)}
    (hfix : ∀ j : Fin t, j ∉ S → ∀ k : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      Sum.elim id id k = Fin.castAdd δ.val j →
        ((y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ Pi.single k 1 = Pi.single k 1) :
    y ∈ oBlockGroup ζ t δ (.zero S) := by
  rw [oBlockGroup, Subgroup.mem_comap]
  refine Subgroup.mem_map.mpr
    ⟨⟨(y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hSp y.2⟩, ?_, rfl⟩
  change (⟨(y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hSp y.2⟩ :
    ↥(StatedSp (t + δ.val) K)) ∈ SpBlocks.levi (t + δ.val) (liftSupport t δ S)
  refine SpBlocks.mem_levi_of_col fun x k hk => ?_
  obtain ⟨j, hkj, hjS⟩ := ota_exists_eq_castAdd_of_not_mem_liftSupport hk
  have hcol := hfix j hjS k hkj
  rw [Matrix.mulVec_single_one] at hcol
  have hx := congrFun hcol x
  rw [Matrix.col_apply] at hx
  rw [Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using hx

private theorem ota_swapEquiv_mem_oBlockGroup_zero_aut (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (ht : 3 ≤ t + δ.val)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hSp : omegaQ (K := K) t δ ≤ StatedSp (t + δ.val) K)
    {S : Finset (Fin t)} {i j : Fin t} (hi : i ∈ S) (hj : j ∈ S) :
    PlaneRaw.swapEquiv t i j ∈ oTorusAut ζ t δ (oBlockGroup ζ t δ (.zero S)) := by
  refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd ht (X := oBlockGroup ζ t δ (.zero S))
    (π := Equiv.swap i j) (η := fun _ => false) ?_ ?_ (PlaneRaw.coe_swapEquiv i j)
  · intro _
    simp
  · intro y _ hfix
    exact ota_mem_oBlockGroup_zero_of_fix hSp (y := y) fun l hl k hk =>
      hfix l (Equiv.swap_apply_of_ne_of_ne (fun h => hl (h ▸ hi)) (fun h => hl (h ▸ hj)))
        (by simp) k hk

theorem oTorusAut_top_eq (hK : Nat.card K = 2) (hζ : Function.Injective ζ) (ht : 4 ≤ t)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    oTorusAut ζ t δ ⊤ = ((PlaneRaw.ambientNormalizer (.orthogonal δ) t : Subgroup _) : Set _) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    rw [oTorusAut] at hφ
    obtain ⟨y, -, hconj⟩ := hφ
    obtain ⟨π, η, hpar, hφeq⟩ := exists_moveExp_of_conj_otau hK hζ hQ hnd y.2 hconj
    exact PlaneRaw.mem_ambientNormalizer_orthogonal_of_coe_eq_moveExp δ hφeq hpar
  · change ((if δ.val = 0 then PlaneRaw.evenSignedPermGroup t
      else PlaneRaw.signedPermGroup t : Subgroup _) : Set _) ⊆ oTorusAut ζ t δ ⊤
    split_ifs with hδ
    · intro φ hφ
      simp only [PlaneRaw.evenSignedPermGroup] at hφ
      refine closure_subset_oTorusAut (X := ⊤) ?_ hφ
      rintro T (⟨i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)
      · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd (by omega) (X := ⊤)
          (π := Equiv.swap i j) (η := fun _ => false) ?_ (fun _ _ _ => Subgroup.mem_top _)
          (PlaneRaw.coe_swapEquiv i j)
        intro _
        simp
      · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd (by omega) (X := ⊤)
          (π := 1) (η := fun k => decide (k = i ∨ k = j)) ?_
          (fun _ _ _ => Subgroup.mem_top _) (PlaneRaw.coe_negEquiv_mul_negEquiv hij)
        intro _
        rw [PlaneRaw.card_filter_decide_eq_or_eq hij]
        exact ⟨1, rfl⟩
    · intro φ hφ
      simp only [PlaneRaw.signedPermGroup] at hφ
      refine closure_subset_oTorusAut (X := ⊤) ?_ hφ
      rintro T (⟨i, j, rfl⟩ | ⟨i, rfl⟩)
      · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd (by omega) (X := ⊤)
          (π := Equiv.swap i j) (η := fun _ => false) ?_ (fun _ _ _ => Subgroup.mem_top _)
          (PlaneRaw.coe_swapEquiv i j)
        intro _
        simp
      · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd (by omega) (X := ⊤)
          (π := 1) (η := fun k => decide (k = i)) ?_
          (fun _ _ _ => Subgroup.mem_top _) (PlaneRaw.coe_negEquiv i)
        intro h0
        exact absurd h0 hδ

theorem oTorusAut_oBlockGroup_zero_subset (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (S : Finset (Fin t)) :
    oTorusAut ζ t δ (oBlockGroup ζ t δ (.zero S)) ⊆
      ((PlaneRaw.normalizerOf (.orthogonal δ) t (.zero S) : Subgroup _) : Set _) := by
  intro φ hφ
  rw [oTorusAut] at hφ
  obtain ⟨y, hy, hconj⟩ := hφ
  obtain ⟨π, η, hpar, hφeq⟩ := exists_moveExp_of_conj_otau hK hζ hQ hnd y.2 hconj
  have hfix : ∀ j : Fin t, j ∉ S → π j = j ∧ η j = false := by
    intro j hj
    have hu : ∀ i ∈ S, (Pi.single j 1 : PlaneRaw.V t) i = 0 := by
      intro i hi
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [hne]
    have hcomm := commute_otau_of_mem_oBlockGroup (c := .zero S) hy hu
    have happ := apply_eq_self_of_commute hζ hconj hcomm
    rw [hφeq] at happ
    exact (PlaneRaw.moveExp_single_eq_single_iff π η j).mp happ
  exact PlaneRaw.mem_normalizerOf_orthogonal_zero_of_coe_eq_moveExp δ S hφeq
    (fun j hj => (hfix j hj).1) (fun j hj => (hfix j hj).2) hpar

theorem normalizerOf_zero_subset_oTorusAut_oBlockGroup (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (ht : 3 ≤ t + δ.val)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hSp : omegaQ (K := K) t δ ≤ StatedSp (t + δ.val) K) (S : Finset (Fin t)) :
    ((PlaneRaw.normalizerOf (.orthogonal δ) t (.zero S) : Subgroup _) : Set _) ⊆
      oTorusAut ζ t δ (oBlockGroup ζ t δ (.zero S)) := by
  change ((if δ.val = 0 then PlaneRaw.evenSignedPermGroupOn t S
    else PlaneRaw.signedPermGroupOn t S : Subgroup _) : Set _) ⊆
      oTorusAut ζ t δ (oBlockGroup ζ t δ (.zero S))
  split_ifs with hδ
  · intro φ hφ
    simp only [PlaneRaw.evenSignedPermGroupOn] at hφ
    refine closure_subset_oTorusAut (X := oBlockGroup ζ t δ (.zero S)) ?_ hφ
    rintro T (⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, hij, rfl⟩)
    · exact ota_swapEquiv_mem_oBlockGroup_zero_aut hK hζ ht hQ hnd hSp hi hj
    · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd ht (X := oBlockGroup ζ t δ (.zero S))
        (π := 1) (η := fun k => decide (k = i ∨ k = j)) ?_ ?_
        (PlaneRaw.coe_negEquiv_mul_negEquiv hij)
      · intro _
        rw [PlaneRaw.card_filter_decide_eq_or_eq hij]
        exact ⟨1, rfl⟩
      · intro y _ hfix
        exact ota_mem_oBlockGroup_zero_of_fix hSp (y := y) fun l hl k hk =>
          hfix l rfl (by
            rw [decide_eq_false_iff_not]
            rintro (h | h)
            · exact hl (h ▸ hi)
            · exact hl (h ▸ hj)) k hk
  · intro φ hφ
    simp only [PlaneRaw.signedPermGroupOn] at hφ
    refine closure_subset_oTorusAut (X := oBlockGroup ζ t δ (.zero S)) ?_ hφ
    rintro T (⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ota_swapEquiv_mem_oBlockGroup_zero_aut hK hζ ht hQ hnd hSp hi hj
    · refine ota_moveExp_mem_oTorusAut hK hζ hQ hnd ht (X := oBlockGroup ζ t δ (.zero S))
        (π := 1) (η := fun k => decide (k = i)) ?_ ?_ (PlaneRaw.coe_negEquiv i)
      · intro h0
        exact absurd h0 hδ
      · intro y _ hfix
        exact ota_mem_oBlockGroup_zero_of_fix hSp (y := y) fun l hl k hk =>
          hfix l rfl (by rw [decide_eq_false_iff_not]; exact fun h => hl (h ▸ hi)) k hk

theorem oTorusAut_oBlockGroup_extension_subset (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (e : PlaneRaw.V t) :
    oTorusAut ζ t δ (oBlockGroup ζ t δ (.extension e)) ⊆
      ((PlaneRaw.twistedPermGroupOn t e : Subgroup _) : Set _) := by
  intro φ hφ
  rw [oTorusAut] at hφ
  obtain ⟨y, hy, hconj⟩ := hφ
  obtain ⟨π, η, hpar, hφeq⟩ := exists_moveExp_of_conj_otau hK hζ hQ hnd y.2 hconj
  have hsigned : φ ∈ PlaneRaw.signedPermGroup t :=
    PlaneRaw.mem_signedPermGroup_of_coe_eq_moveExp hφeq
  have he : φ e = e := apply_eq_self_of_commute hζ hconj
    (commute_otau_self_of_mem_oBlockGroup_extension hy)
  have hoff : ∀ l, e l = 0 → φ (Pi.single l 1) = Pi.single l 1 := by
    intro l hl
    have hu : ∀ i ∈ PlaneRaw.Code.extSupport e, (Pi.single l 1 : PlaneRaw.V t) i = 0 := by
      intro i hi
      have hne : i ≠ l := fun h => (PlaneRaw.mem_extSupport e i).mp hi (h ▸ hl)
      simp [hne]
    exact apply_eq_self_of_commute hζ hconj (commute_otau_of_mem_oBlockGroup hy hu)
  exact PlaneRaw.mem_twistedPermGroupOn_of_mem_signedPermGroup hsigned he hoff

theorem twistedPermGroupOn_subset_oTorusAut_oYcode (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (e : PlaneRaw.V t)
    (he : 4 ≤ (PlaneRaw.Code.extSupport e).card)
    (hle : (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))).map
        (StatedSp (t + δ.val) K).subtype ≤
      (oYcode ζ t δ (.extension e)).map (omegaQ (K := K) t δ).subtype) :
    ((PlaneRaw.twistedPermGroupOn t e : Subgroup _) : Set _) ⊆
      oTorusAut ζ t δ (oYcode ζ t δ (.extension e)) := by
  intro φ hφ
  simp only [PlaneRaw.twistedPermGroupOn] at hφ
  refine closure_subset_oTorusAut (X := oYcode ζ t δ (.extension e)) ?_ hφ
  rintro T ⟨i, j, hi, hj, rfl⟩
  have hcard : 4 ≤ (PlaneRaw.Code.extSupport (liftV t δ e)).card := by
    rw [ota_card_extSupport_liftV e]
    exact he
  have hgen : PlaneRaw.swapTwist (t + δ.val) (liftV t δ e) (Fin.castAdd δ.val i)
      (Fin.castAdd δ.val j) ∈ SpBlocks.torusAut ζ (t + δ.val)
        (SpBlocks.Ycode ζ (t + δ.val) (.extension (liftV t δ e))) := by
    rw [SpBlocks.spExtTorusAut_holds (K := K) (ζ := ζ) (m := t + δ.val) hK hζ
      (liftV t δ e) hcard]
    refine Subgroup.subset_closure ⟨Fin.castAdd δ.val i, Fin.castAdd δ.val j, ?_, ?_, rfl⟩
    · simpa [liftV, Fin.append_left] using hi
    · simpa [liftV, Fin.append_left] using hj
  obtain ⟨g, hg, hgconj⟩ := hgen
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp
    (hle (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩))
  have hyg : (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
    simpa using hyeq
  refine ⟨y, hy, fun u => ?_⟩
  have h1 : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
      (SpBlocks.tau ζ (t + δ.val) (liftV t δ u) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)⁻¹ =
      (SpBlocks.tau ζ (t + δ.val) (PlaneRaw.swapTwist (t + δ.val) (liftV t δ e)
        (Fin.castAdd δ.val i) (Fin.castAdd δ.val j) (liftV t δ u)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
    simpa using congrArg (fun z : ↥(StatedSp (t + δ.val) K) =>
      (z : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) (hgconj (liftV t δ u))
  rw [hyg]
  simpa [otau, swapTwist_liftV] using h1

theorem orthAmbientTorusAut_holds : OrthAmbientTorusAut := by
  intro K _ _ _ ζ t δ hK hζ ht
  exact oTorusAut_top_eq hK hζ ht (coe_planeQForm K t δ) nondegenerate_planeQForm

end CFSG.StandardType.GGQ2Frame.OrthBlocks
