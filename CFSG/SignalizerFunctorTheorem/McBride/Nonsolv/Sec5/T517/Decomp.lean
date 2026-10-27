module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Complete

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

theorem mulSingle_eq_one_of_ne {ι N : Type*} [DecidableEq ι] [Group N] {i i' : ι} (a : N)
    (h : i' ≠ i) : (Pi.mulSingle i a : ι → N) i' = 1 :=
  Pi.mulSingle_eq_of_ne (M := fun _ => N) h a

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

namespace Setting

variable (S : Setting p H B θ)

include S

theorem mem_jTilde_iff {J : Subgroup Γ} (hJ : J ∈ lcal H) {x : Γ} :
    x ∈ jTilde H J ↔ x ∈ H ∧ ∀ J' ∈ lcal H, J' ≠ J → ∀ j ∈ J', x * j = j * x := by
  have hK := kOf_inf_centralizer_eq_sSup_diff S.sol_eq_bot hJ
  unfold jTilde
  rw [hK, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxH, hx⟩
    refine ⟨hxH, fun J' hJ' hne j hj => ?_⟩
    have hmem : j ∈ sSup (lcal H \ {J}) := (le_sSup ⟨hJ', hne⟩ : J' ≤ sSup (lcal H \ {J})) hj
    exact (Subgroup.mem_centralizer_iff.mp hx j hmem).symm
  · rintro ⟨hxH, hx⟩
    exact ⟨hxH, mem_centralizer_sSup fun J' hJ' j hj => hx J' hJ'.1 hJ'.2 j hj⟩

theorem jTilde_ne {J J' : Subgroup Γ} (hJ : J ∈ lcal H) (hJ' : J' ∈ lcal H) (hne : J ≠ J') :
    jTilde H J ≠ jTilde H J' := by
  intro h
  have hle : J ≤ jTilde H J := fun j hj => by
    refine (S.mem_jTilde_iff hJ).mpr ⟨(mem_lcal_iff.mp hJ).1 hj, fun J'' hJ'' hne'' j'' hj'' => ?_⟩
    exact (S.hK.commute J hJ J'' hJ'' (Ne.symm hne'') j hj j'' hj'').eq
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := fun x hx y hy =>
    ((S.mem_jTilde_iff hJ').mp (h ▸ hle hx)).2 J hJ hne y hy
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  exact hnc (isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2 b b.2))

theorem exists_pi_of_mem {x : Γ} (hx : x ∈ thetaSup B θ) :
    ∃ (hxH : x ∈ H) (w : ↥(lcal H) → ↥(thetaOf θ B)),
      autH H ⟨x, hxH⟩ = S.thetaAut w := by
  obtain ⟨hxH, w, hw⟩ := S.mem_thetaSup_iff.mp hx
  exact ⟨hxH, w, hw.symm⟩

theorem mem_jTilde_iff_of_eq {J : Subgroup Γ} (hJ : J ∈ lcal H) {x : ↥H}
    {w : ↥(lcal H) → ↥(thetaOf θ B)} (hxw : autH H x = S.thetaAut w) :
    (x : Γ) ∈ jTilde H J ↔ ∀ J' (hJ' : J' ∈ lcal H), J' ≠ J → w ⟨J', hJ'⟩ = 1 := by
  rw [S.mem_jTilde_iff hJ]
  constructor
  · rintro ⟨-, hx⟩ J' hJ' hne
    have h1 := S.actsOn_thetaAut w hJ'
    rw [← hxw] at h1
    refine Subtype.ext (S.eq_one_of_centralizes_one (S.thetaOf_le_H (w ⟨J', hJ'⟩).2)
      (S.thetaOf_le_centralizer (w ⟨J', hJ'⟩).2) hJ' fun j hj => ?_)
    have h2 := h1 ⟨j, S.hK.le hJ' hj⟩ hj
    have h3 : (x : Γ) * j * (x : Γ)⁻¹ = j := by rw [hx J' hJ' hne j hj]; group
    have h4 : (x : Γ) * j * (x : Γ)⁻¹ = (w ⟨J', hJ'⟩ : Γ) * j * (w ⟨J', hJ'⟩ : Γ)⁻¹ := h2
    rw [h3] at h4
    calc (w ⟨J', hJ'⟩ : Γ) * j = (w ⟨J', hJ'⟩ : Γ) * j * (w ⟨J', hJ'⟩ : Γ)⁻¹ *
          (w ⟨J', hJ'⟩ : Γ) := by group
      _ = j * (w ⟨J', hJ'⟩ : Γ) := by rw [← h4]
  · intro h
    refine ⟨x.2, fun J' hJ' hne j hj => ?_⟩
    have h1 := S.actsOn_thetaAut w hJ'
    rw [← hxw] at h1
    have h2 := h1 ⟨j, S.hK.le hJ' hj⟩ hj
    have h3 : (x : Γ) * j * (x : Γ)⁻¹ = (w ⟨J', hJ'⟩ : Γ) * j * (w ⟨J', hJ'⟩ : Γ)⁻¹ := h2
    rw [h J' hJ' hne] at h3
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h3
    calc (x : Γ) * j = (x : Γ) * j * (x : Γ)⁻¹ * (x : Γ) := by group
      _ = j * (x : Γ) := by rw [h3]

open Classical in
theorem autH_eq_thetaAut_single {J : Subgroup Γ} (hJ : J ∈ lcal H) {x : ↥H}
    {a : ↥(thetaOf θ B)}
    (hJx : ∀ j ∈ J, (x : Γ) * j * (x : Γ)⁻¹ = (a : Γ) * j * (a : Γ)⁻¹)
    (hother : ∀ J' ∈ lcal H, J' ≠ J → ∀ j ∈ J', (x : Γ) * j = j * x) :
    autH H x = S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ a) := by
  apply S.hK.ext_of_forall_mem
  intro J' hJ' j hj
  apply Subtype.ext
  rw [autH_apply, S.actsOn_thetaAut (Pi.mulSingle ⟨J, hJ⟩ a) hJ' ⟨j, S.hK.le hJ' hj⟩ hj]
  by_cases h : J' = J
  · subst h
    simp only [Pi.mulSingle_eq_same]
    exact hJx j hj
  · have h1 : (Pi.mulSingle (⟨J, hJ⟩ : ↥(lcal H)) a : ↥(lcal H) → ↥(thetaOf θ B)) ⟨J', hJ'⟩ = 1 :=
      mulSingle_eq_one_of_ne a (fun h' => h (congrArg Subtype.val h'))
    rw [h1, hother J' hJ' h j hj]
    simp

open Classical in
theorem exists_single {J : Subgroup Γ} (hJ : J ∈ lcal H) (a : ↥(thetaOf θ B)) :
    ∃ y : ↥H, (y : Γ) ∈ thetaSup B θ ∧ autH H y = S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ a) := by
  have hmem : S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ a) ∈ S.thetaAut.range := ⟨_, rfl⟩
  obtain ⟨y, hy, hyw⟩ := mem_autImage_iff.mp (S.range_le_autImage_thetaSup hmem)
  exact ⟨y, hy, hyw⟩

open Classical in
theorem single_mem_jTilde {J : Subgroup Γ} (hJ : J ∈ lcal H) {a : ↥(thetaOf θ B)} {y : ↥H}
    (hy : autH H y = S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ a)) : (y : Γ) ∈ jTilde H J := by
  rw [S.mem_jTilde_iff_of_eq hJ hy]
  intro J' hJ' hne
  exact mulSingle_eq_one_of_ne a (fun h' => hne (congrArg Subtype.val h'))

open Classical in
theorem single_acts {J : Subgroup Γ} (hJ : J ∈ lcal H) {a : ↥(thetaOf θ B)} {y : ↥H}
    (hy : autH H y = S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ a)) :
    ∀ j ∈ J, (y : Γ) * j * (y : Γ)⁻¹ = (a : Γ) * j * (a : Γ)⁻¹ := by
  intro j hj
  have h1 := S.actsOn_thetaAut (Pi.mulSingle ⟨J, hJ⟩ a) hJ
  rw [← hy] at h1
  have h2 := h1 ⟨j, S.hK.le hJ hj⟩ hj
  rw [Pi.mulSingle_eq_same] at h2
  exact h2

theorem sSup_Y_diff_le_centralizer {J : Subgroup Γ} (hJ : J ∈ lcal H) :
    sSup ({Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} \
        ({thetaSup B θ ⊓ jTilde H J} : Set (Subgroup Γ))) ≤
      Subgroup.centralizer (J : Set Γ) := by
  refine sSup_le ?_
  rintro Y' ⟨⟨J', hJ', rfl⟩, hne⟩ y hy
  have hJJ' : J' ≠ J := fun h => hne (by rw [h]; rfl)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact (((S.mem_jTilde_iff hJ').mp (Subgroup.mem_inf.mp hy).2).2 J hJ (Ne.symm hJJ') j hj).symm

theorem sSupIndep_Y :
    sSupIndep {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} := by
  rintro _ ⟨J, hJ, rfl⟩
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxY, hxT⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxW, hxJ⟩ := Subgroup.mem_inf.mp hxY
  have hxH : x ∈ H := S.thetaSup_le_H hxW
  have hxc := S.sSup_Y_diff_le_centralizer hJ hxT
  rw [Subgroup.mem_bot]
  refine S.eq_one_of_centralizes hxH fun J' hJ' j' hj' => ?_
  by_cases h : J' = J
  · subst h
    exact (Subgroup.mem_centralizer_iff.mp hxc j' hj').symm
  · exact ((S.mem_jTilde_iff hJ).mp hxJ).2 J' hJ' h j' hj'

theorem sSup_Y_eq : sSup {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} = thetaSup B θ := by
  classical
  apply le_antisymm
  · exact sSup_le (by rintro _ ⟨J, hJ, rfl⟩; exact inf_le_left)
  · intro x hx
    set U := sSup {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} with hU
    obtain ⟨hxH, w, hw⟩ := S.exists_pi_of_mem hx
    let Q : Subgroup (↥(lcal H) → ↥(thetaOf θ B)) := (autImage H U).comap S.thetaAut
    have hQ : w ∈ Q := by
      refine Subgroup.pi_mem_of_mulSingle_mem w fun J => ?_
      obtain ⟨y, hyW, hyw⟩ := S.exists_single J.2 (w J)
      have hmemY : thetaSup B θ ⊓ jTilde H J.1 ∈
          {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} := ⟨J.1, J.2, rfl⟩
      have hyU : (y : Γ) ∈ U :=
        le_sSup hmemY (Subgroup.mem_inf.mpr ⟨hyW, S.single_mem_jTilde J.2 hyw⟩)
      show S.thetaAut (Pi.mulSingle J (w J)) ∈ autImage H U
      rw [← hyw]
      exact mem_autImage_iff.mpr ⟨y, hyU, rfl⟩
    obtain ⟨u, hu, huw⟩ := mem_autImage_iff.mp hQ
    have : u = ⟨x, hxH⟩ := autH_injective S.sol_eq_bot (huw.trans hw.symm)
    rw [this] at hu
    exact hu

theorem isDirectProduct_Y :
    IsDirectProduct {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} (thetaSup B θ) where
  commute := by
    classical
    rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩ hne x hx y hy
    have hJ12 : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨hxW, hxJ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyW, hyJ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hxH, w, hw⟩ := S.exists_pi_of_mem hxW
    obtain ⟨hyH, w', hw'⟩ := S.exists_pi_of_mem hyW
    have hs := (S.mem_jTilde_iff_of_eq hJ₁ hw).mp hxJ
    have hs' := (S.mem_jTilde_iff_of_eq hJ₂ hw').mp hyJ
    have hcomm : w * w' = w' * w := by
      funext J'
      by_cases h1 : J'.1 = J₁
      · have : w' J' = 1 := hs' J'.1 J'.2 (h1 ▸ hJ12)
        rw [Pi.mul_apply, Pi.mul_apply, this, mul_one, one_mul]
      · have : w J' = 1 := hs J'.1 J'.2 h1
        rw [Pi.mul_apply, Pi.mul_apply, this, mul_one, one_mul]
    have : autH H (⟨x, hxH⟩ * ⟨y, hyH⟩) = autH H (⟨y, hyH⟩ * ⟨x, hxH⟩) := by
      rw [map_mul, map_mul, hw, hw', ← map_mul, ← map_mul, hcomm]
    exact congrArg Subtype.val (autH_injective S.sol_eq_bot this)
  indep := S.sSupIndep_Y
  sSup_eq := S.sSup_Y_eq

theorem inf_jTilde_eq_projIn {J : Subgroup Γ} (hJ : J ∈ lcal H) :
    thetaSup B θ ⊓ jTilde H J =
      projIn (jTilde H '' lcal H) (jTilde H J) (thetaOf θ B) := by
  classical
  have hcentr : sSup (jTilde H '' lcal H \ ({jTilde H J} : Set (Subgroup Γ))) ≤
      Subgroup.centralizer (J : Set Γ) := by
    refine sSup_le ?_
    rintro K ⟨⟨J', hJ', rfl⟩, hne⟩ y hy
    have hJJ' : J' ≠ J := fun h => hne (by rw [h]; rfl)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (((S.mem_jTilde_iff hJ').mp hy).2 J hJ (Ne.symm hJJ') j hj).symm
  apply le_antisymm
  · intro h hh
    obtain ⟨hhW, hhJ⟩ := Subgroup.mem_inf.mp hh
    obtain ⟨hhH, w, hw⟩ := S.exists_pi_of_mem hhW
    have hYJ : thetaSup B θ ⊓ jTilde H J ∈
        {Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} := ⟨J, hJ, rfl⟩
    have hdp := S.isDirectProduct_Y.isDirectPair hYJ
    have haW : ((w ⟨J, hJ⟩ : ↥(thetaOf θ B)) : Γ) ∈ thetaSup B θ := by
      obtain ⟨b, hb, hb1⟩ := S.exists_ne_one
      exact le_thetaSup hb hb1 (thetaOf_le_apply hb hb1 (w ⟨J, hJ⟩).2)
    have hsup := hdp.sup_eq ▸ haW
    obtain ⟨y, hy, l, hl, hyl⟩ := (mem_sup_iff_of_commute hdp.commute).mp hsup
    have hlcJ := S.sSup_Y_diff_le_centralizer hJ hl
    have hyH : y ∈ H := S.thetaSup_le_H (Subgroup.mem_inf.mp hy).1
    have hyJ : y ∈ jTilde H J := (Subgroup.mem_inf.mp hy).2
    have heq : y = h := by
      have hauto : autH H ⟨y, hyH⟩ = autH H ⟨h, hhH⟩ := by
        apply S.hK.ext_of_forall_mem
        intro J' hJ' x hx
        apply Subtype.ext
        rw [autH_apply, autH_apply]
        by_cases hJJ : J' = J
        · subst hJJ
          have h1 : h * x * h⁻¹ = (w ⟨J', hJ'⟩ : Γ) * x * (w ⟨J', hJ'⟩ : Γ)⁻¹ := by
            have := S.actsOn_thetaAut w hJ'
            rw [← hw] at this
            exact this ⟨x, S.hK.le hJ' hx⟩ hx
          have hlx : x * l = l * x := Subgroup.mem_centralizer_iff.mp hlcJ x hx
          show y * x * y⁻¹ = h * x * h⁻¹
          rw [h1, ← hyl]
          calc y * x * y⁻¹ = y * (l * x * l⁻¹) * y⁻¹ := by rw [← hlx]; group
            _ = y * l * x * (y * l)⁻¹ := by group
        · have hy' := ((S.mem_jTilde_iff hJ).mp hyJ).2 J' hJ' hJJ x hx
          have hh' := ((S.mem_jTilde_iff hJ).mp hhJ).2 J' hJ' hJJ x hx
          show y * x * y⁻¹ = h * x * h⁻¹
          rw [hy', hh']
          group
      exact congrArg Subtype.val (autH_injective S.sol_eq_bot hauto)
    have hl' : l ∈ sSup (jTilde H '' lcal H \ ({jTilde H J} : Set (Subgroup Γ))) := by
      refine (sSup_le ?_ : sSup ({Y | ∃ J ∈ lcal H, Y = thetaSup B θ ⊓ jTilde H J} \
        ({thetaSup B θ ⊓ jTilde H J} : Set (Subgroup Γ))) ≤
          sSup (jTilde H '' lcal H \ ({jTilde H J} : Set (Subgroup Γ)))) hl
      rintro Y' ⟨⟨J', hJ', rfl⟩, hne⟩
      have hJJ' : J' ≠ J := fun h => hne (by rw [h]; rfl)
      have hmem : jTilde H J' ∈ jTilde H '' lcal H \ ({jTilde H J} : Set (Subgroup Γ)) :=
        ⟨⟨J', hJ', rfl⟩, fun h => S.jTilde_ne hJ' hJ hJJ' h⟩
      exact inf_le_right.trans (le_sSup hmem)
    rw [heq] at hyl
    exact Subgroup.subset_closure ⟨hhJ, l, hl', hyl ▸ (w ⟨J, hJ⟩).2⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro j ⟨hjJ, l, hl, hjl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hjJ⟩
    have hjH : j ∈ H := ((S.mem_jTilde_iff hJ).mp hjJ).1
    have hlc := Subgroup.mem_centralizer_iff.mp (hcentr hl)
    have hjother := ((S.mem_jTilde_iff hJ).mp hjJ).2
    have hsingle : autH H ⟨j, hjH⟩ =
        S.thetaAut (Pi.mulSingle ⟨J, hJ⟩ (⟨j * l, hjl⟩ : ↥(thetaOf θ B))) := by
      refine S.autH_eq_thetaAut_single hJ (fun x hx => ?_) hjother
      have hxl : x * l = l * x := hlc x hx
      have h3 : l * x * l⁻¹ = x := by rw [← hxl]; group
      show j * x * j⁻¹ = j * l * x * (j * l)⁻¹
      calc j * x * j⁻¹ = j * (l * x * l⁻¹) * j⁻¹ := by rw [h3]
        _ = j * l * x * (j * l)⁻¹ := by group
    exact S.mem_thetaSup_iff.mpr ⟨hjH, ⟨_, hsingle.symm⟩⟩

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
