module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Loc
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Move
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Sum
public import CFSG.Quasithin.Background.B1More13B

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W]

@[expose] def liftSub (C : Subgroup W) (S : Subgroup (MulAut (W ⧸ C))) : Subgroup (MulAut W) :=
  (S.comap (quotHom C)).map (stabSub C).subtype

theorem mem_liftSub {C : Subgroup W} {S : Subgroup (MulAut (W ⧸ C))} {g : MulAut W} :
    g ∈ liftSub C S ↔ ∃ h : g ∈ stabSub C, quotHom C ⟨g, h⟩ ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hS⟩
    exact ⟨⟨g, h⟩, hS, rfl⟩

theorem autQuot_le_iff {X : Subgroup (MulAut W)} {C : Subgroup W} {S : Subgroup (MulAut (W ⧸ C))}
    (hX : X ≤ stabSub C) : autQuot X C ≤ S ↔ X ≤ liftSub C S := by
  constructor
  · intro h x hx
    exact mem_liftSub.mpr ⟨hX hx, h (mem_autQuot.mpr ⟨⟨x, hX hx⟩, hx, rfl⟩)⟩
  · intro h φ hφ
    obtain ⟨g, hgX, rfl⟩ := mem_autQuot.mp hφ
    obtain ⟨_, hS⟩ := mem_liftSub.mp (h hgX)
    exact hS

theorem autQuot_commute {X X' : Subgroup (MulAut W)} {C : Subgroup W}
    (h : ∀ x ∈ X, ∀ x' ∈ X', x * x' = x' * x) :
    ∀ φ ∈ autQuot X C, ∀ φ' ∈ autQuot X' C, φ * φ' = φ' * φ := by
  intro φ hφ φ' hφ'
  obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
  obtain ⟨g', hg', rfl⟩ := mem_autQuot.mp hφ'
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h _ hg _ hg')

theorem mem_stabSub_of_forall_mem [Finite W] {A : Subgroup W} {g : MulAut W}
    (hg : ∀ u ∈ A, g u ∈ A) : g ∈ stabSub A := by
  intro u
  refine ⟨fun hu => ?_, hg u⟩
  have hinj : Function.Injective (fun a : ↥A => (⟨g a, hg a a.2⟩ : ↥A)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨g u, hu⟩
  have h1 : g a = g u := congrArg Subtype.val ha
  rw [← g.injective h1]
  exact a.2

theorem forall_zpowers_conj_mem {K : Subgroup (MulAut W)} {t : MulAut W}
    (hKt : K.map (MulAut.conj t).toMonoidHom = K) :
    ∀ b ∈ Subgroup.zpowers t, ∀ k ∈ K, b * k * b⁻¹ ∈ K := by
  have htn : t ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have : t * l * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
      rwa [hKt] at this
    · intro hl
      rw [← hKt] at hl
      obtain ⟨l', hl', hll'⟩ := hl
      have h2 : t * l' * t⁻¹ = t * l * t⁻¹ := hll'
      have : l' = l := by simpa using h2
      rw [← this]
      exact hl'
  intro b hb l hl
  exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr htn) hb) l).mp hl

variable [Finite W]

theorem dMinDeg_le_autQuot {X : Subgroup (MulAut W)} {C : Subgroup W} (hX : X ≤ stabSub C)
    (hne : autQuot X C ≠ ⊥) : dMinDeg ↥X ≤ dMinDeg ↥(autQuot X C) := by
  have : Finite (MulAut (W ⧸ C)) := MulEquiv.finite_left
  rw [dMinDeg_congr (Subgroup.subgroupOfEquivOfLe hX).symm]
  exact dMinDeg_le_dMinDeg_map (quotHom C) (X.subgroupOf (stabSub C)) hne

theorem sup_inf_trivMod_eq {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {U : Subgroup W} (hU : U ∈ irrSet H)
    {X : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hXU : ¬ commSub U X ≤ fixV H) :
    (U ⊔ fixV H) ⊓ trivMod X (fixV H) = fixV H := by
  obtain ⟨-, hXH, hXn⟩ := conjSet_facts hL hH hX
  have hirr := isIrrOn_sup_fixV hU
  set C := fixV H with hC
  have hT : StableUnder H (trivMod X C) := by
    intro h hh w hw x hx
    have h1 : h⁻¹ * x * h ∈ X := by
      have := hXn h⁻¹ (H.inv_mem hh) x hx
      simpa using this
    have h2 := hw _ h1
    have e : x (h w) * (h w)⁻¹ = h ((h⁻¹ * x * h) w * w⁻¹) := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [e, h2 h hh]
    exact h2
  have hCF : C ≤ (U ⊔ C) ⊓ trivMod X C := by
    intro c hc
    refine ⟨le_sup_right (α := Subgroup W) hc, fun x hx => ?_⟩
    rw [hc x (hXH hx), mul_inv_cancel]
    exact C.one_mem
  rcases hirr.2.2.2 _ (stableUnder_inf hirr.2.1 hT) hCF inf_le_left with h | h
  · exact h
  · exfalso
    apply hXU
    rw [commSub_le_iff_le_trivMod]
    exact le_sup_left.trans (h.ge.trans inf_le_right)

theorem not_commute_of_not_commSub_le (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (ht : t ∈ Y)
    (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L) {U : Subgroup W} (hU : U ∈ irrSet H)
    (hUt : U.map t.toMonoidHom = U) (htU : ¬ commSub U (Subgroup.zpowers t) ≤ fixV H)
    {X : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hXU : ¬ commSub U X ≤ fixV H) :
    ¬ ∀ x ∈ X, t * x = x * t := by
  intro hc
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH hX
  have hA := sup_inf_trivMod_eq hL hH hU hX hXU
  have hirr := isIrrOn_sup_fixV hU
  have htC : ∀ c ∈ fixV H, t c ∈ fixV H := fun c hc => stableUnder_fixV hn t ht c hc
  set C := fixV H with hC
  have hUCX : StableUnder X (U ⊔ C) := fun x hx u hu => hirr.2.1 x (hXH hx) u hu
  have hCX : StableUnder X C := fun x hx c hc => by rw [hc x (hXH hx)]; exact hc
  have hcz : ∀ x ∈ X, ∀ s ∈ Subgroup.zpowers t, x * s * x⁻¹ = s := by
    intro x hx s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hxt : Commute x t := (hc x hx).symm
    rw [(hxt.zpow_right k).eq, mul_inv_cancel_right]
  set T := commSub (U ⊔ C) (Subgroup.zpowers t) with hT
  have hTX : StableUnder X T :=
    stableUnder_commSub (fun x hx s hs => by rw [hcz x hx s hs]; exact hs) hUCX
  have hTCX : StableUnder X (T ⊔ C) := stableUnder_sup hTX hCX
  have hrkT : rk ↥T ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    have h1 : T ≤ commV (Subgroup.zpowers t) := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    have h2 := rk_commV_add_rk_fixV t
    have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
    have h4 := rk_mono h1
    omega
  have hdX : dMinDeg ↥X = dMinDeg ↥L := by
    obtain ⟨y, -, rfl⟩ := hX
    exact (dMinDeg_congr (L.equivMapOfInjective _ (MulAut.conj y).injective)).symm
  have hlt : rk ↥(T ⊔ C) < rk ↥C + dMinDeg ↥X := by
    have h1 := rk_sup_add_rk_inf T C
    omega
  have hle := Inputs1719.commSub_le_of_rk_lt_dMinDeg hW le_sup_right hTCX hCX hlt
  have htUC : ∀ u ∈ U ⊔ C, t u ∈ U ⊔ C := by
    intro u hu
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    refine Subgroup.mul_mem_sup ?_ (htC c hc')
    rw [← hUt]
    exact ⟨a, ha, rfl⟩
  have hstab : Subgroup.zpowers t ≤ stabSub (U ⊔ C) :=
    Subgroup.zpowers_le.mpr (mem_stabSub_of_forall_mem htUC)
  have hTle : T ≤ (U ⊔ C) ⊓ trivMod X C := by
    refine le_inf (commSub_le_of_invariant fun s hs u hu => ((hstab hs) u).mpr hu) ?_
    rw [← commSub_le_iff_le_trivMod]
    exact (commSub_mono le_sup_left le_rfl).trans hle
  rw [hA] at hTle
  exact htU ((commSub_mono le_sup_left le_rfl).trans hTle)

theorem le_commutator_sup_conj {Y K : Subgroup (MulAut W)} (hK : IsComponentOf K Y)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : t * t = 1) (hKt : ¬ ∀ k ∈ K, t * k = k * t) :
    K ≤ ⁅K ⊔ K.map (MulAut.conj t).toMonoidHom, Subgroup.zpowers t⁆ := by
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hmemK' : ∀ k ∈ K, t * k * t⁻¹ ∈ K' := fun k hk => ⟨k, hk, rfl⟩
  have hmemK : ∀ k ∈ K', t * k * t⁻¹ ∈ K := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ := by group
    rw [e, ht2, inv_one, one_mul, mul_one]
    exact hk
  have hnc : ¬ Subgroup.zpowers t ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    intro h
    apply hKt
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers t)) k hk).symm
  by_cases hKK : K' = K
  · have hc := CFSG.Quasithin.B113.commutator_comp_eq_of_normalizes hK.2.2
      (forall_zpowers_conj_mem hKK) hnc
    calc K = ⁅K, Subgroup.zpowers t⁆ := hc.symm
      _ ≤ ⁅K ⊔ K', Subgroup.zpowers t⁆ := Subgroup.commutator_mono le_sup_left le_rfl
  · have hK'c : IsComponentOf K' Y := isComponentOf_map_conj_of_mem hK ht
    have hcomm : ∀ k' ∈ K', ∀ k ∈ K, k' * k = k * k' :=
      B69.components_mul_comm_of_ne hK hK'c (Ne.symm hKK)
    set M := K ⊔ K' with hM
    set B := ⁅M, Subgroup.zpowers t⁆ with hB
    have htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M := by
      have hle : M ≤ M.comap (MulAut.conj t).toMonoidHom := by
        refine sup_le (fun k hk => ?_) (fun k hk => ?_)
        · exact le_sup_right (α := Subgroup (MulAut W)) (hmemK' k hk)
        · exact le_sup_left (α := Subgroup (MulAut W)) (hmemK k hk)
      intro m hm
      exact hle hm
    have htnM : t ∈ Subgroup.normalizer (M : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro m
      refine ⟨htM m, fun h => ?_⟩
      have h2 := htM _ h
      have e : t * (t * m * t⁻¹) * t⁻¹ = m := by
        rw [htinv]
        have e2 : t * (t * m * t) * t = (t * t) * m * (t * t) := by group
        rw [e2, ht2, one_mul, mul_one]
      rwa [e] at h2
    have hzM : ∀ s ∈ Subgroup.zpowers t, ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
      intro s hs m hm
      exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr htnM) hs) m).mp hm
    have hBM : B ≤ M := by
      rw [hB, Subgroup.commutator_le]
      intro m hm s hs
      have e : ⁅m, s⁆ = m * (s * m⁻¹ * s⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact M.mul_mem hm (hzM s hs _ (M.inv_mem hm))
    have hMK : M ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
      refine sup_le Subgroup.le_normalizer (fun k' hk' => ?_)
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have e : ∀ k : MulAut W, k ∈ K → k' * k * k'⁻¹ = k := fun k hk => by
        rw [hcomm k' hk' k hk, mul_inv_cancel_right]
      constructor
      · intro hk
        rw [e k hk]
        exact hk
      · intro hk
        have h1 : k' * k * k'⁻¹ * k'⁻¹⁻¹ = k' * k := by group
        have hk1 : k = k'⁻¹ * (k' * k * k'⁻¹) * k' := by group
        rw [hk1]
        have h3 : k'⁻¹ * (k' * k * k'⁻¹) * k' = k' * k * k'⁻¹ := by
          have hk2 := hcomm k'⁻¹ (K'.inv_mem hk') _ hk
          calc k'⁻¹ * (k' * k * k'⁻¹) * k' = (k' * k * k'⁻¹) * k'⁻¹ * k' := by rw [hk2]
            _ = k' * k * k'⁻¹ := by group
        rw [h3]
        exact hk
    have hBK : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
      (Subgroup.mem_normalizer_iff.mp (hMK (hBM hb)) k).mp hk
    have hBnc : ¬ B ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
      intro h
      apply not_commute_of_isQuasisimple hK.2.2
      intro a ha b hb
      have hbt : ⁅b, t⁆ ∈ B :=
        Subgroup.commutator_mem_commutator (le_sup_left (α := Subgroup (MulAut W)) hb)
          (Subgroup.mem_zpowers t)
      have h1 := Subgroup.mem_centralizer_iff.mp (h hbt) a ha
      have h2 : (t * b⁻¹ * t⁻¹) * a = a * (t * b⁻¹ * t⁻¹) := hcomm _ (hmemK' _ (K.inv_mem hb)) a ha
      rw [commutatorElement_def] at h1
      have h3 : a * b * (t * b⁻¹ * t⁻¹) = b * a * (t * b⁻¹ * t⁻¹) := by
        calc a * b * (t * b⁻¹ * t⁻¹) = a * (b * t * b⁻¹ * t⁻¹) := by group
          _ = b * t * b⁻¹ * t⁻¹ * a := h1
          _ = b * ((t * b⁻¹ * t⁻¹) * a) := by group
          _ = b * (a * (t * b⁻¹ * t⁻¹)) := by rw [h2]
          _ = b * a * (t * b⁻¹ * t⁻¹) := by group
      exact mul_right_cancel h3
    have hc := CFSG.Quasithin.B113.commutator_comp_eq_of_normalizes hK.2.2 hBK hBnc
    calc K = ⁅K, B⁆ := hc.symm
      _ ≤ B := by
        rw [Subgroup.commutator_le]
        intro k hk b hb
        rw [commutatorElement_def]
        exact B.mul_mem (conj_mem_commutator (le_sup_left (α := Subgroup (MulAut W)) hk) hb)
          (B.inv_mem hb)

end CFSG.LocalAnalysis.WeakClosure81
