module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_commSub_map_conj (U : Subgroup W) (X : Subgroup (MulAut W))
    (g : MulAut W) :
    commSub (U.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) =
      (commSub U X).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj g x₀, ⟨x₀, hx₀, rfl⟩, g w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

private theorem w1369_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc x a * x b * (b⁻¹ * a⁻¹)
          = x a * x b * (a⁻¹ * b⁻¹) := by rw [mul_comm (b⁻¹) (a⁻¹)]
        _ = x a * (x b * (a⁻¹ * b⁻¹)) := by rw [mul_assoc]
        _ = x a * (a⁻¹ * (x b * b⁻¹)) := by
              rw [← mul_assoc (x b) (a⁻¹) (b⁻¹), mul_comm (x b) (a⁻¹), mul_assoc]
        _ = (x a * a⁻¹) * (x b * b⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w1369_stableUnder_commSub {L : Subgroup (MulAut W)} {M : Subgroup W}
    (hM : StableUnder L M) : StableUnder L (commSub M L) := by
  intro l hl u hu
  have hMmap : M.map l.toMonoidHom = M := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      exact hM l hl m hm
    · intro m hm
      exact Subgroup.mem_map.mpr ⟨(l⁻¹ : MulAut W) m, hM l⁻¹ (L.inv_mem hl) m hm, by simp⟩
  have hLmap : L.map (MulAut.conj l).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl)
  have h := w1369_commSub_map_conj M L l
  rw [hMmap, hLmap] at h
  have : l u ∈ (commSub M L).map l.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  rwa [← h] at this

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx a ha) (hB x hx b hb)

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) := by
  intro x hx u hu
  obtain ⟨huA, huB⟩ := Subgroup.mem_inf.mp hu
  exact Subgroup.mem_inf.mpr ⟨hA x hx u huA, hB x hx u huB⟩

private theorem w1369_stableUnder_fixV (L : Subgroup (MulAut W)) : StableUnder L (fixV L) := by
  intro x hx u hu
  rw [mem_fixV] at hu ⊢
  intro z hz
  calc z (x u) = (z * x) u := rfl
    _ = u := hu (z * x) (L.mul_mem hz hx)
    _ = x u := (hu x hx).symm

private theorem w1369_inf_lt_iff_lt_sup {a b : Subgroup W} : a ⊓ b < b ↔ a < a ⊔ b := by
  constructor
  · intro h
    refine lt_of_le_of_ne le_sup_left fun hEq => ?_
    exact (ne_of_lt h) (inf_eq_right.mpr (hEq.symm ▸ le_sup_right))
  · intro h
    refine lt_of_le_of_ne inf_le_right fun hEq => ?_
    exact (ne_of_lt h) (sup_eq_left.mpr (inf_eq_right.mp hEq)).symm

private theorem w1369_map_mul_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have hcomp : (g⁻¹).toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
    ext v
    simp
  rw [hcomp, Subgroup.map_id]

private theorem w1369_map_inv_mul (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have hcomp : g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
    ext v
    simp
  rw [hcomp, Subgroup.map_id]

private theorem w1369_isIrrOn_map_conj_iff (X : Subgroup (MulAut W)) (I N : Subgroup W)
    (g : MulAut W) :
    IsIrrOn (X.map (MulAut.conj g).toMonoidHom) (I.map g.toMonoidHom) (N.map g.toMonoidHom) ↔
      IsIrrOn X I N := by
  constructor
  · rintro ⟨hlt, hIstab, hNstab, hirr⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective g.injective).mp hlt, ?_, ?_, ?_⟩
    · intro x hx u hu
      have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      have hu' : g u ∈ I.map g.toMonoidHom := ⟨u, hu, rfl⟩
      obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp (hIstab _ hx' _ hu')
      have hwu : w = x u := g.injective (by
        simpa [MulAut.conj_apply, MulAut.mul_apply] using hw')
      exact hwu ▸ hw
    · intro x hx u hu
      have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      have hu' : g u ∈ N.map g.toMonoidHom := ⟨u, hu, rfl⟩
      obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp (hNstab _ hx' _ hu')
      have hwu : w = x u := g.injective (by
        simpa [MulAut.conj_apply, MulAut.mul_apply] using hw')
      exact hwu ▸ hw
    · intro J hJstab hNJ hJI
      have hJ'stab : StableUnder (X.map (MulAut.conj g).toMonoidHom) (J.map g.toMonoidHom) := by
        intro x' hx' u' hu'
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
        exact Subgroup.mem_map.mpr ⟨x u, hJstab x hx u hu,
          by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
      rcases hirr (J.map g.toMonoidHom) hJ'stab (Subgroup.map_mono hNJ)
        (Subgroup.map_mono hJI) with h | h
      · left
        have h' := congrArg (Subgroup.map (g⁻¹).toMonoidHom) h
        rwa [w1369_map_mul_inv, w1369_map_mul_inv] at h'
      · right
        have h' := congrArg (Subgroup.map (g⁻¹).toMonoidHom) h
        rwa [w1369_map_mul_inv, w1369_map_mul_inv] at h'
  · rintro ⟨hlt, hIstab, hNstab, hirr⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective g.injective).mpr hlt, ?_, ?_, ?_⟩
    · intro x' hx' u' hu'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
      exact Subgroup.mem_map.mpr ⟨x u, hIstab x hx u hu,
        by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
    · intro x' hx' u' hu'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
      exact Subgroup.mem_map.mpr ⟨x u, hNstab x hx u hu,
        by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
    · intro J' hJ'stab hNJ' hJ'I
      have hJstab : StableUnder X (J'.map (g⁻¹).toMonoidHom) := by
        intro x hx v hv
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hv
        have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
        have hmem := hJ'stab _ hx' _ hu'
        exact Subgroup.mem_map.mpr ⟨(g * x * g⁻¹) u', hmem,
          by simp [MulAut.conj_apply, MulAut.mul_apply]⟩
      have hNJ : N ≤ J'.map (g⁻¹).toMonoidHom := by
        have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hNJ'
        rwa [w1369_map_mul_inv] at h
      have hJI : J'.map (g⁻¹).toMonoidHom ≤ I := by
        have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hJ'I
        rwa [w1369_map_mul_inv] at h
      rcases hirr (J'.map (g⁻¹).toMonoidHom) hJstab hNJ hJI with h | h
      · left
        have h' := congrArg (Subgroup.map g.toMonoidHom) h
        rwa [w1369_map_inv_mul] at h'
      · right
        have h' := congrArg (Subgroup.map g.toMonoidHom) h
        rwa [w1369_map_inv_mul] at h'

private theorem w1369_mem_perfect_chain (R : Subgroup (MulAut W)) (hR : ⁅R, R⁆ = R)
    (Y₀ Y₁ Y : Subgroup W) (h1 : commSub Y₁ R ≤ Y₀) (h2 : commSub Y R ≤ Y₁)
    {r : MulAut W} (hr : r ∈ R) {y : W} (hy : y ∈ Y) : r y * y⁻¹ ∈ Y₀ := by
  haveI : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  let θ : ↥R →* W ⧸ Y₀ :=
    { toFun := fun s => QuotientGroup.mk ((s : MulAut W) y * y⁻¹)
      map_one' := by simp
      map_mul' := by
        intro s t
        have ht : (t : MulAut W) y * y⁻¹ ∈ Y₁ :=
          h2 (Subgroup.subset_closure ⟨(t : MulAut W), t.2, y, hy, rfl⟩)
        have hs : (s : MulAut W) ((t : MulAut W) y * y⁻¹) *
            ((t : MulAut W) y * y⁻¹)⁻¹ ∈ Y₀ :=
          h1 (Subgroup.subset_closure ⟨(s : MulAut W), s.2, _, ht, rfl⟩)
        have hquot : ((s : MulAut W) ((t : MulAut W) y * y⁻¹) : W ⧸ Y₀) =
            (((t : MulAut W) y * y⁻¹ : W) : W ⧸ Y₀) := by
          rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
          exact hs
        have hEq1 : ((s * t : ↥R) : MulAut W) y * y⁻¹ =
            (s : MulAut W) ((t : MulAut W) y * y⁻¹) *
              ((s : MulAut W) y * y⁻¹) := by
          rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          group
        show QuotientGroup.mk (((s * t : ↥R) : MulAut W) y * y⁻¹) =
          QuotientGroup.mk ((s : MulAut W) y * y⁻¹) *
            QuotientGroup.mk ((t : MulAut W) y * y⁻¹)
        rw [hEq1, QuotientGroup.mk_mul, hquot]
        exact mul_comm _ _ }
  have hmem : (⟨r, hr⟩ : ↥R) ∈ θ.ker :=
    Abelianization.commutator_subset_ker θ Group.IsPerfect.mem_commutator
  have hθ : θ ⟨r, hr⟩ = 1 := MonoidHom.mem_ker.mp hmem
  have h1' : QuotientGroup.mk (r y * y⁻¹) = (1 : W ⧸ Y₀) := by
    show θ ⟨r, hr⟩ = 1
    exact hθ
  exact (QuotientGroup.eq_one_iff (r y * y⁻¹)).mp h1'

private theorem w1369_perfect_chain (R : Subgroup (MulAut W)) (hR : ⁅R, R⁆ = R)
    (Y₀ Y₁ Y : Subgroup W) (h1 : commSub Y₁ R ≤ Y₀) (h2 : commSub Y R ≤ Y₁) :
    commSub Y R ≤ Y₀ := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨r, hr, y, hy, rfl⟩
  exact w1369_mem_perfect_chain R hR Y₀ Y₁ Y h1 h2 hr hy

theorem irr_stab {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (Wd L).map g.toMonoidHom = Wd L ∧ (Cd L).map g.toMonoidHom = Cd L ∧
      ∀ I ∈ irrSet L, I.map g.toMonoidHom ∈ irrSet L := by
  have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hWd : (Wd L).map g.toMonoidHom = Wd L := by
    have h := w1369_commSub_map_conj (⊤ : Subgroup W) L g
    rw [Subgroup.map_top_of_surjective g.toMonoidHom g.surjective, hLmap] at h
    exact h.symm
  have hCd : (Cd L).map g.toMonoidHom = Cd L := by
    show (commSub ⊤ L ⊓ fixV L).map g.toMonoidHom = commSub ⊤ L ⊓ fixV L
    rw [Subgroup.map_inf _ _ _ g.injective, hWd, ← fixV_map_conj_eq L g, hLmap]
  refine ⟨hWd, hCd, fun I hI => ?_⟩
  obtain ⟨hIcomm, hIirr⟩ := hI
  refine ⟨?_, ?_⟩
  · have h := w1369_commSub_map_conj I L g
    rw [hLmap] at h
    rw [h, hIcomm]
  · have h := (w1369_isIrrOn_map_conj_iff L I (I ⊓ fixV L) g).mpr hIirr
    rw [hLmap, Subgroup.map_inf _ _ _ g.injective, ← fixV_map_conj_eq L g, hLmap] at h
    exact h

theorem irr_to_sect (hw2 : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) {I : Subgroup W}
    (hI : I ∈ irrSet L) :
    I ≤ Wd L ∧ Cd L ≤ I ⊔ Cd L ∧ I ⊔ Cd L ≤ Wd L ∧ IsIrrOn L (I ⊔ Cd L) (Cd L) ∧
      commSub (I ⊔ Cd L) L = I := by
  obtain ⟨hIcomm, hCI, hIstab, _, hirr⟩ := hI
  have hIleWd : I ≤ Wd L := by
    have h := commSub_mono (le_top : I ≤ ⊤) (le_rfl : L ≤ L)
    rwa [hIcomm] at h
  have hIfix : I ⊓ Cd L = I ⊓ fixV L := by
    show I ⊓ (commSub ⊤ L ⊓ fixV L) = I ⊓ fixV L
    rw [← inf_assoc, inf_eq_left.mpr hIleWd]
  have hCdstab : StableUnder L (Cd L) := by
    show StableUnder L (commSub ⊤ L ⊓ fixV L)
    exact w1369_stableUnder_inf
      (w1369_stableUnder_commSub (M := ⊤) (by intro x hx u hu; trivial))
      (w1369_stableUnder_fixV L)
  have hCd_bot : commSub (Cd L) L = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
  have hCd_lt : Cd L < I ⊔ Cd L := by
    have h : Cd L ⊓ I < I := by
      rw [inf_comm, hIfix]
      exact hCI
    have h' := (w1369_inf_lt_iff_lt_sup (a := Cd L) (b := I)).mp h
    rwa [sup_comm] at h'
  refine ⟨hIleWd, le_sup_right, sup_le hIleWd inf_le_left, ?_, ?_⟩
  · refine ⟨hCd_lt, w1369_stableUnder_sup hIstab hCdstab, hCdstab, ?_⟩
    intro J hJstab hCdJ hJle
    have hJstab' : StableUnder L (J ⊓ I) := w1369_stableUnder_inf hJstab hIstab
    have hle : I ⊓ fixV L ≤ J ⊓ I := by
      rw [← hIfix]
      exact le_inf (inf_le_right.trans hCdJ) inf_le_left
    rcases hirr (J ⊓ I) hJstab' hle inf_le_right with h | h
    · left
      have hinf : J ⊓ I ≤ Cd L := by
        rw [h, ← hIfix]
        exact inf_le_right
      have hsup' : J ≤ Cd L ⊔ I := by
        rw [sup_comm]
        exact hJle
      exact (eq_of_le_of_inf_le_of_le_sup hCdJ hinf hsup').symm
    · right
      have hIleJ : I ≤ J := by
        rw [← h]
        exact inf_le_left
      exact le_antisymm hJle (sup_le hIleJ hCdJ)
  · have h1 := w1369_commSub_sup I (Cd L) L
    rw [hCd_bot, sup_bot_eq] at h1
    exact h1.trans hIcomm

theorem sect_to_irr (hw2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hLp : ⁅L, L⁆ = L)
    {M : Subgroup W} (hCM : Cd L ≤ M) (hMW : M ≤ Wd L) (hM : IsIrrOn L M (Cd L)) :
    commSub M L ∈ irrSet L ∧ commSub M L ⊔ Cd L = M := by
  obtain ⟨hCdM, hMstab, hCdstab, hirr⟩ := hM
  have hI'leM : commSub M L ≤ M := commSub_le_of_invariant hMstab
  have hI'stab : StableUnder L (commSub M L) := w1369_stableUnder_commSub hMstab
  have hCd_bot : commSub (Cd L) L = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
  have hsup : commSub M L ⊔ Cd L = M := by
    have hstable : StableUnder L (commSub M L ⊔ Cd L) :=
      w1369_stableUnder_sup hI'stab hCdstab
    have hle : commSub M L ⊔ Cd L ≤ M := sup_le hI'leM hCM
    rcases hirr (commSub M L ⊔ Cd L) hstable le_sup_right hle with h | h
    · exfalso
      have hI'leCd : commSub M L ≤ Cd L := by rw [← h]; exact le_sup_left
      have hbot : commSub (commSub M L) L = ⊥ :=
        commSub_eq_bot_iff.mpr (hI'leCd.trans inf_le_right)
      have hI'bot : commSub M L = ⊥ :=
        le_bot_iff.mp (w1369_perfect_chain L hLp ⊥ (commSub M L) M (le_of_eq hbot) le_rfl)
      have hMfix : M ≤ fixV L := commSub_eq_bot_iff.mp hI'bot
      exact (not_lt_of_ge (le_inf hMW hMfix)) hCdM
    · exact h
  have hI'eq : commSub (commSub M L) L = commSub M L := by
    have h1 := w1369_commSub_sup (commSub M L) (Cd L) L
    rw [hsup, hCd_bot, sup_bot_eq] at h1
    exact h1.symm
  have hI'leWd : commSub M L ≤ Wd L := hI'leM.trans hMW
  have hI'fix : commSub M L ⊓ Cd L = commSub M L ⊓ fixV L := by
    show commSub M L ⊓ (commSub ⊤ L ⊓ fixV L) = commSub M L ⊓ fixV L
    rw [← inf_assoc, inf_eq_left.mpr hI'leWd]
  have hlt : commSub M L ⊓ Cd L < commSub M L := by
    have hCdlt : Cd L < Cd L ⊔ commSub M L := by
      rw [sup_comm, hsup]
      exact hCdM
    have h := (w1369_inf_lt_iff_lt_sup (a := Cd L) (b := commSub M L)).mpr hCdlt
    rwa [inf_comm] at h
  have hI'irr : IsIrrOn L (commSub M L) (commSub M L ⊓ fixV L) := by
    refine ⟨hI'fix ▸ hlt, hI'stab,
      w1369_stableUnder_inf hI'stab (w1369_stableUnder_fixV L), ?_⟩
    intro J hJstab hI'fixJ hJI'
    have hJsup_stab : StableUnder L (J ⊔ Cd L) := w1369_stableUnder_sup hJstab hCdstab
    have hJsup_le : J ⊔ Cd L ≤ M := sup_le (hJI'.trans hI'leM) hCM
    rcases hirr (J ⊔ Cd L) hJsup_stab le_sup_right hJsup_le with h | h
    · left
      have hJleCd : J ≤ Cd L := by rw [← h]; exact le_sup_left
      exact le_antisymm (hI'fix ▸ le_inf hJI' hJleCd) hI'fixJ
    · right
      have hinf : commSub M L ⊓ Cd L ≤ J := by
        rw [hI'fix]
        exact hI'fixJ
      have hsup' : commSub M L ≤ J ⊔ Cd L := by
        rw [h]
        exact hI'leM
      exact eq_of_le_of_inf_le_of_le_sup hJI' hinf hsup'
  exact ⟨⟨hI'eq, hI'irr⟩, hsup⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
