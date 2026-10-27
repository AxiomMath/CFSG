module

public import CFSG.Quasithin.Background.F918V2BB
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Free
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Swap
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

theorem realizes_of_autQuot (D : FFModel) {L : Subgroup (MulAut W)}
    (hfaith : ∀ y : stabSub (fixV L), (y : MulAut W) ∈ L → quotHom (fixV L) y = 1 →
      (y : MulAut W) = 1)
    (h : D.Realizes (autQuot L (fixV L)) ⊤ ⊥) : D.Realizes L ⊤ (fixV L) := by
  have hLstab : L ≤ stabSub (fixV L) := RonanF918.le_stabSub_fixV L
  let r : ↥L →* ↥(autQuot L (fixV L)) :=
    ((quotHom (fixV L)).comp (Subgroup.inclusion hLstab)).codRestrict (autQuot L (fixV L))
      fun x => mem_autQuot.mpr ⟨Subgroup.inclusion hLstab x, x.2, rfl⟩
  have hr : ∀ x : ↥L, (r x : MulAut (W ⧸ fixV L)) =
      quotHom (fixV L) ⟨x.1, hLstab x.2⟩ := fun _ => rfl
  have hrker : r.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hquot : quotHom (fixV L) ⟨x.1, hLstab x.2⟩ = 1 := congrArg Subtype.val hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfaith ⟨x.1, hLstab x.2⟩ x.2 hquot)
  have hsurj : Function.Surjective r := by
    rintro ⟨φ, hφ⟩
    obtain ⟨y, hy, rfl⟩ := mem_autQuot.mp hφ
    exact ⟨⟨y.1, hy⟩, Subtype.ext rfl⟩
  let e : ↥L ≃* ↥(autQuot L (fixV L)) :=
    MulEquiv.ofBijective r ⟨(MonoidHom.ker_eq_bot_iff r).mp hrker, hsurj⟩
  let π : D.Gam →* ↥(autQuot L (fixV L)) := h.choose
  have hπ : D.RealizesVia (autQuot L (fixV L)) ⊤ ⊥ π := h.choose_spec
  let βspec := hπ.2.2.2.2.2.2.2
  let β : ↥(⊤ : Subgroup (W ⧸ fixV L)) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := βspec.choose
  have hβs : Function.Surjective β := βspec.choose_spec.1
  have hβk : ∀ u : ↥(⊤ : Subgroup (W ⧸ fixV L)), β u = 1 ↔ (u : W ⧸ fixV L) ∈ ⊥ :=
    βspec.choose_spec.2.1
  have hβe : ∀ (γ : D.Gam) (u : ↥(⊤ : Subgroup (W ⧸ fixV L))) (m : ↥D.sec)
      (hu : ((π γ : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) u ∈
        (⊤ : Subgroup (W ⧸ fixV L)))
      (hm : D.act γ (m : D.Amb) ∈ D.sec),
      β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) u, hu⟩ =
          QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ :=
    βspec.choose_spec.2.2
  let q : ↥(⊤ : Subgroup W) →* (W ⧸ fixV L) :=
    (QuotientGroup.mk' (fixV L)).comp (Subgroup.topEquiv).toMonoidHom
  let q' : ↥(⊤ : Subgroup W) →* ↥(⊤ : Subgroup (W ⧸ fixV L)) :=
    q.codRestrict ⊤ fun _ => Subgroup.mem_top _
  have hq_apply : ∀ u : ↥(⊤ : Subgroup W),
      q u = QuotientGroup.mk' (fixV L) (u : W) := fun _ => rfl
  have hq'_apply : ∀ u : ↥(⊤ : Subgroup W), (q' u : W ⧸ fixV L) = q u := fun _ => rfl
  have hq'_surj : Function.Surjective q' := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (fixV L) (x : W ⧸ fixV L)
    exact ⟨⟨u, Subgroup.mem_top u⟩, Subtype.ext hu⟩
  refine ⟨e.symm.toMonoidHom.comp π, e.symm.surjective.comp hπ.1, le_top, hπ.2.2.1,
    fun _ _ _ => Subgroup.mem_top _, ?_, hπ.2.2.2.2.2.1, hπ.2.2.2.2.2.2.1,
    β.comp q', hβs.comp hq'_surj, ?_, ?_⟩
  · intro l z hz
    rw [mem_fixV] at hz ⊢
    intro k hk
    rw [← MulAut.mul_apply, hz (k * l) (L.mul_mem hk l.2), hz l l.2]
  · intro u
    dsimp only [β]
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, hq'_apply, hq_apply,
      QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff (u : W)
  · intro γ u m hu hm hβ
    have h1 := hβe γ (q' u) m (Subgroup.mem_top _) hm (by
      dsimp only [β]
      rw [MonoidHom.comp_apply] at hβ
      exact hβ)
    have he_apply : ∀ x : ↥L, ((e x : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) =
        quotHom (fixV L) ⟨x.1, hLstab x.2⟩ := fun _ => rfl
    have hqeq : q' ⟨(((e.symm.toMonoidHom.comp π) γ : ↥L) : MulAut W) (u : W),
        Subgroup.mem_top _⟩ = ⟨((π γ : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) (q' u),
          Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      rw [hq'_apply, hq_apply]
      conv_rhs =>
        rw [show ((π γ : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) =
            ((e (e.symm (π γ)) : ↥(autQuot L (fixV L))) : MulAut (W ⧸ fixV L)) from
          congrArg Subtype.val (MulEquiv.apply_symm_apply e (π γ)).symm,
          he_apply (e.symm (π γ))]
      rw [show ((q' u : ↥(⊤ : Subgroup (W ⧸ fixV L))) : W ⧸ fixV L) =
          QuotientGroup.mk' (fixV L) (u : W) by rw [hq'_apply, hq_apply]]
      rfl
    rw [MonoidHom.comp_apply, hqeq]
    dsimp only [β] at ⊢
    exact h1

theorem binaryNaturalSL_of_autQuot {L : Subgroup (MulAut W)} {d a : ℕ}
    (hfaith : ∀ y : stabSub (fixV L), (y : MulAut W) ∈ L → quotHom (fixV L) y = 1 →
      (y : MulAut W) = 1)
    (h : BinaryNaturalSL (autQuot L (fixV L)) ⊤ ⊥ d a) :
    BinaryNaturalSL L ⊤ (fixV L) d a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard, realizes_of_autQuot (FFModel.nat (StatedSL d K)) hfaith hreal⟩

theorem secIsoOn_autQuot {L : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn L (A ⊔ fixV L) (fixV L) (B ⊔ fixV L) (fixV L)) :
    SecIsoOn (autQuot L (fixV L)) (A.map (QuotientGroup.mk' (fixV L))) ⊥
      (B.map (QuotientGroup.mk' (fixV L))) ⊥ := by
  set C := fixV L with hC
  obtain ⟨hCA, hCB, hLA, hLC, hLB, hLC', β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hAeq : (A ⊔ C).map (QuotientGroup.mk' C) = A.map (QuotientGroup.mk' C) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hBeq : (B ⊔ C).map (QuotientGroup.mk' C) = B.map (QuotientGroup.mk' C) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rw [← hAeq, ← hBeq]
  let φA : ↥(A ⊔ C) →* ↥((A ⊔ C).map (QuotientGroup.mk' C)) :=
    ((QuotientGroup.mk' C).comp (A ⊔ C).subtype).codRestrict
      ((A ⊔ C).map (QuotientGroup.mk' C)) fun a => ⟨a, a.2, rfl⟩
  have hφAsurj : Function.Surjective φA := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
  have hφAker : φA.ker = C.subgroupOf (A ⊔ C) := by
    ext a
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change (QuotientGroup.mk' C (a : W) : W ⧸ C) = 1 ↔ a ∈ C.subgroupOf (A ⊔ C)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let φA_inv : ↥((A ⊔ C).map (QuotientGroup.mk' C)) → ↥(A ⊔ C) :=
    fun x => Classical.choose (hφAsurj x)
  have hφA_inv : Function.RightInverse φA_inv φA :=
    fun x => Classical.choose_spec (hφAsurj x)
  let f : ↥(A ⊔ C) →* (W ⧸ C) := (QuotientGroup.mk' C).comp β
  have hfker : C.subgroupOf (A ⊔ C) ≤ f.ker := by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact (hβiff a).mpr (Subgroup.mem_subgroupOf.mp ha)
  have hfker' : φA.ker ≤ f.ker := hφAker ▸ hfker
  let βstar : ↥((A ⊔ C).map (QuotientGroup.mk' C)) →* (W ⧸ C) :=
    (MonoidHom.liftOfRightInverse φA φA_inv hφA_inv) ⟨f, hfker'⟩
  have hβstar_apply : ∀ a : ↥(A ⊔ C), βstar (φA a) = QuotientGroup.mk' C (β a) :=
    fun a => MonoidHom.liftOfRightInverse_comp_apply φA φA_inv hφA_inv ⟨f, hfker'⟩ a
  have hφA_one : ∀ x : ↥(A ⊔ C), φA x = 1 ↔ (x : W) ∈ C := by
    intro x
    rw [← MonoidHom.mem_ker, hφAker, Subgroup.mem_subgroupOf]
  have hφA_one' : ∀ x : ↥(A ⊔ C),
      ((φA x : ↥((A ⊔ C).map (QuotientGroup.mk' C))) : W ⧸ C) = 1 ↔ (x : W) ∈ C := by
    intro x
    exact Subtype.ext_iff.symm.trans (hφA_one x)
  refine ⟨bot_le, bot_le, ?_, ?_, ?_, ?_, βstar, ?_, ?_, ?_, ?_⟩
  · intro x hx a ha
    obtain ⟨g, hgL, hφ⟩ := mem_autQuot.mp hx
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨g.1 a₀, hLA g.1 hgL a₀ ha₀, ?_⟩
    rw [← hφ]
    change (QuotientGroup.mk' C ((g : MulAut W) a₀) : W ⧸ C) =
      quotHom C g (QuotientGroup.mk a₀)
    rw [quotHom_mk, QuotientGroup.mk'_apply]
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro x hx b hb
    obtain ⟨g, hgL, hφ⟩ := mem_autQuot.mp hx
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    refine Subgroup.mem_map.mpr ⟨g.1 b₀, hLB g.1 hgL b₀ hb₀, ?_⟩
    rw [← hφ]
    change (QuotientGroup.mk' C ((g : MulAut W) b₀) : W ⧸ C) =
      quotHom C g (QuotientGroup.mk b₀)
    rw [quotHom_mk, QuotientGroup.mk'_apply]
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro a
    refine Subgroup.mem_map.mpr ⟨β (φA_inv a), hβB (φA_inv a), ?_⟩
    rw [← hβstar_apply (φA_inv a), hφA_inv a]
  · intro a
    rw [Subgroup.mem_bot, Subgroup.mem_bot, ← hφA_inv a, hβstar_apply (φA_inv a),
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hφA_one' (φA_inv a)]
    exact hβiff (φA_inv a)
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨a₀, ha₀⟩ := hβsurj b₀ hb₀
    refine ⟨φA a₀, ?_⟩
    rw [hβstar_apply]
    rw [Subgroup.mem_bot, ← map_inv, ← map_mul]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha₀
  · intro x hx a a' haa'
    obtain ⟨g, hgL, hφ⟩ := mem_autQuot.mp hx
    let a₀ : ↥(A ⊔ C) := φA_inv a
    let a₁ : ↥(A ⊔ C) := φA_inv a'
    have ha : a = φA a₀ := (hφA_inv a).symm
    have ha' : a' = φA a₁ := (hφA_inv a').symm
    rw [ha, ha'] at haa'
    have hxlift : (a₁ : W) * ((g : MulAut W) (a₀ : W))⁻¹ ∈ C := by
      have h1 : (QuotientGroup.mk' C (a₁ : W) : W ⧸ C) =
          QuotientGroup.mk' C ((g : MulAut W) (a₀ : W)) := by
        have h2 := haa'
        rw [← hφ] at h2
        change (QuotientGroup.mk' C (a₁ : W) : W ⧸ C) =
          (quotHom C g) (QuotientGroup.mk' C (a₀ : W)) at h2
        change (QuotientGroup.mk (a₁ : W) : W ⧸ C) =
          (quotHom C g) (QuotientGroup.mk (a₀ : W)) at h2
        rw [quotHom_mk] at h2
        exact h2
      exact (mk_eq_mk_iff (U := C) _ _).mp h1
    have hg₁ : (g : MulAut W)⁻¹ (a₁ : W) ∈ A ⊔ C :=
      hLA g⁻¹ (L.inv_mem hgL) a₁ a₁.2
    have hCg : ((g : MulAut W)⁻¹) ((a₁ : W) * ((g : MulAut W) (a₀ : W))⁻¹) ∈ C :=
      hLC g⁻¹ (L.inv_mem hgL) _ hxlift
    have hlt : ((g : MulAut W)⁻¹ (a₁ : W)) * (a₀ : W)⁻¹ ∈ C := by
      simpa [map_mul, map_inv] using hCg
    have hβlt : β (⟨(g : MulAut W)⁻¹ (a₁ : W), hg₁⟩ : ↥(A ⊔ C)) * (β a₀)⁻¹ ∈ C := by
      have h := (hβiff (⟨(g : MulAut W)⁻¹ (a₁ : W), hg₁⟩ * a₀⁻¹)).mpr hlt
      simpa [map_mul, map_inv] using h
    have heq := hβeq (g : MulAut W) hgL ⟨(g : MulAut W)⁻¹ (a₁ : W), hg₁⟩ a₁ (by simp)
    have hconj : (g : MulAut W) (β ⟨(g : MulAut W)⁻¹ (a₁ : W), hg₁⟩) *
        ((g : MulAut W) (β a₀))⁻¹ ∈ C := by
      have h := hLC (g : MulAut W) hgL _ hβlt
      simpa [map_mul, map_inv] using h
    have hgoal : β a₁ * ((g : MulAut W) (β a₀))⁻¹ ∈ C := by
      have h := C.mul_mem heq hconj
      simpa [mul_assoc] using h
    rw [Subgroup.mem_bot, ha, ha', hβstar_apply, hβstar_apply, ← hφ]
    change (QuotientGroup.mk' C (β a₁) : W ⧸ C) *
      (((quotHom C g) : MulAut (W ⧸ C)) (QuotientGroup.mk (β a₀)))⁻¹ = 1
    rw [quotHom_mk]
    rw [← QuotientGroup.mk'_apply (N := C) ((g : MulAut W) (β a₀))]
    rw [← map_inv, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hgoal

theorem isNaturalClassicalModule_autSub_autQuot {L : Subgroup (MulAut W)} {J : Subgroup W} {n : ℕ}
    (hL : IsL2 ↥L n) (hJ : J ∈ irrSet L) (hnat : BinaryNaturalSL L J (J ⊓ fixV L) 2 n) :
    IsNaturalClassicalModule
      (autSub (autQuot L (fixV L)) (J.map (QuotientGroup.mk' (fixV L)))) n := by
  obtain ⟨K, hK, hfin, hcard, hreal⟩ := hnat
  have hreal' := hreal
  obtain ⟨π, hπ⟩ := hreal'
  have hLC : L ≤ stabSub (fixV L) := RonanF918.le_stabSub_fixV L
  have hLS : ∀ x (hx : x ∈ L),
      (⟨x, hLC hx⟩ : stabSub (fixV L)) ∈ secStab (fixV L) (J.map (QuotientGroup.mk' (fixV L))) := by
    intro x hx
    refine mem_stabSub_of_invariant ?_ ?_
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hu
      exact Subgroup.mem_map.mpr ⟨x j, hJ.2.2.1 x hx j hj, rfl⟩
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hu
      exact Subgroup.mem_map.mpr ⟨x⁻¹ j, hJ.2.2.1 x⁻¹ (L.inv_mem hx) j hj, rfl⟩
  let e : ↥L →* ↥(autSub (autQuot L (fixV L)) (J.map (QuotientGroup.mk' (fixV L)))) :=
    secRes hLC hLS
  have he : Function.Surjective e := secRes_surjective hLC hLS
  let q : ↥J →* ↥(J.map (QuotientGroup.mk' (fixV L))) :=
    (QuotientGroup.mk' (fixV L)).subgroupMap J
  have hq : Function.Surjective q :=
    (QuotientGroup.mk' (fixV L)).subgroupMap_surjective J
  have hqk : ∀ u : ↥J, q u = 1 ↔ (u : W) ∈ J ⊓ fixV L := by
    intro u
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk' (fixV L) (u : W) : W ⧸ fixV L) = 1 :=
        congrArg Subtype.val h1
      exact ⟨u.2, (QuotientGroup.eq_one_iff (u : W)).mp h2⟩
    · rintro ⟨-, huC⟩
      exact Subtype.ext ((QuotientGroup.eq_one_iff (u : W)).mpr huC)
  have heq : ∀ (h : ↥L) (u : ↥J) (hu : ((h : ↥L) : MulAut W) (u : W) ∈ J),
      q ⟨((h : ↥L) : MulAut W) (u : W), hu⟩ =
        ((e h : ↥(autSub (autQuot L (fixV L)) (J.map (QuotientGroup.mk' (fixV L))))) :
          MulAut ↥(J.map (QuotientGroup.mk' (fixV L)))) (q u) := by
    intro h u hu
    apply Subtype.ext
    rw [secRes_apply]
    rfl
  have hrealH : (FFModel.nat (StatedSL 2 K)).RealizesVia
      (autSub (autQuot L (fixV L)) (J.map (QuotientGroup.mk' (fixV L)))) ⊤ ⊥ (e.comp π) :=
    Z391.realizesVia_descend e he q hq hqk heq hπ
  have hnatH : BinaryNaturalSL
      (autSub (autQuot L (fixV L)) (J.map (QuotientGroup.mk' (fixV L)))) ⊤ ⊥ 2 n :=
    ⟨K, hK, hfin, hcard, ⟨_, hrealH⟩⟩
  have hLiso : Nonempty (↥L ≃* ↥(StatedSL 2 K)) :=
    H13.nonempty_mulEquiv_of_realizes_nat hreal
  have hHiso : Nonempty (↥(autSub (autQuot L (fixV L))
      (J.map (QuotientGroup.mk' (fixV L)))) ≃* ↥(StatedSL 2 K)) :=
    H13.nonempty_mulEquiv_of_realizes_nat ⟨_, hrealH⟩
  obtain ⟨eL⟩ := hLiso
  obtain ⟨eH⟩ := hHiso
  exact Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv (eH.trans eL.symm).symm hL, hnatH⟩

theorem exists_mem_irrSet_inf_fixV_ne_bot (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hsum : (⨆ I ∈ irrSet L, I) = ⊤) (hC : fixV L ≠ ⊥) :
    ∃ I ∈ irrSet L, I ⊓ fixV L ≠ ⊥ := by
  by_contra h
  push Not at h
  have hbot : (⨆ I ∈ irrSet L, I) ⊓ fixV L = ⊥ := by
    refine iSup_inf_fixV_eq_bot hW L (irrSet L) ?_
    intro S hS
    have hfix : S ⊓ fixV L = ⊥ := h S hS
    refine ⟨hS.2.2.1, ?_, hfix⟩
    intro J hJ hJS
    rcases hS.2.2.2.2 J hJ (hfix.le.trans bot_le) hJS with h | h
    · exact Or.inl (h.trans hfix)
    · exact Or.inr h
  rw [hsum, top_inf_eq] at hbot
  exact hC hbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot
