module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

private theorem commutator_top {G : Type} [Group G] {J : Subgroup G} (hJ : ⁅J, J⁆ = J) :
    commutator ↥J = ⊤ :=
  Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJ)

private theorem map_perfect {J : Subgroup L'} (hJ : ⁅J, J⁆ = J) :
    ⁅J.map ψ, J.map ψ⁆ = J.map ψ := by
  rw [← Subgroup.map_commutator, hJ]

theorem centerQuotMap_ker (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'}
    (hJ : ⁅J, J⁆ = J) : Subgroup.center ↥J =
      ((QuotientGroup.mk' (Subgroup.center ↥(J.map ψ))).comp (ψ.subgroupMap J)).ker := by
  have hk : (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hx' : (x : L') ∈ ψ.ker := congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact (CFSG.LocalCores.comap_center_eq_of_perfect (Subgroup.isPerfect_iff.2 hJ) _
    (ψ.subgroupMap_surjective J) hk).symm

@[expose] noncomputable def centerQuotMap (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'}
    (hJ : ⁅J, J⁆ = J) : ↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ) :=
  QuotientGroup.liftEquiv (Subgroup.center ↥J)
    ((QuotientGroup.mk'_surjective _).comp (ψ.subgroupMap_surjective J))
    (centerQuotMap_ker hker hJ)

theorem largeEvenMarking_centerQuot {X Y : Type*} [Group X] [Group Y]
    (e : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) (hX : commutator X = ⊤)
    {P : LargeEvenMarkProp X} {P' : LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ → P lab R I F (e.trans θ))
    (h : LargeEvenMarking Y P') : LargeEvenMarking X P := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.trans θ, hPP' lab R I F θ hθ⟩

theorem ggMarkingAll_centerQuot {X Y : Type*} [Group X] [Group Y]
    (e : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) (hX : commutator X = ⊤)
    {Q : LargeEvenMarkProp X} {Q' : LargeEvenMarkProp Y}
    (hQQ' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), Q lab R I F (e.trans θ) → Q' lab R I F θ)
    (h : GGMarkingAll Q) : GGMarkingAll Q' := by
  intro P hP
  have hP' : LargeEvenMarking X (fun lab R _ I F θX => P lab R I F (e.symm.trans θX)) :=
    largeEvenMarking_centerQuot e hX (fun _ _ _ _ _ θ hθ => by
      rw [show e.symm.trans (e.trans θ) = θ from MulEquiv.ext fun q => by simp]
      exact hθ) hP
  refine largeEvenMarking_centerQuot e.symm hP.1 (fun _ _ _ _ _ θX hθX => ⟨hθX.1, ?_⟩)
    (h _ hP')
  apply hQQ'
  rw [show e.trans (e.symm.trans θX) = θX from MulEquiv.ext fun q => by simp]
  exact hθX.2

theorem largeEvenMarking_map_iff (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'}
    (hJ : ⁅J, J⁆ = J) (Q : LargeEvenLabel → Prop) :
    LargeEvenMarking ↥J (fun lab _ _ _ _ _ => Q lab) ↔
      LargeEvenMarking ↥(J.map ψ) (fun lab _ _ _ _ _ => Q lab) :=
  ⟨largeEvenMarking_centerQuot (centerQuotMap hker hJ).symm (commutator_top (map_perfect hJ))
      fun _ _ _ _ _ _ h => h,
    largeEvenMarking_centerQuot (centerQuotMap hker hJ) (commutator_top hJ)
      fun _ _ _ _ _ _ h => h⟩

theorem largeEvenInduces_map_iff (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'}
    {φ : MulAut R} (hφ : ∀ l, φ (ψ l) = ψ (a l)) {J : Subgroup L'} (hJ : ⁅J, J⁆ = J)
    (ha : ∀ l ∈ J, a l ∈ J) {R' : Type} [Group R']
    (θ : ↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ) ≃* R') (φ' : MulAut R') :
    LargeEvenInduces ((centerQuotMap hker hJ).trans θ) (fun l l' : ↥J => (l' : L') = a l) φ' ↔
      LargeEvenInduces θ (fun m m' : ↥(J.map ψ) => (m' : R) = φ m) φ' := by
  have key : ∀ l : ↥J, ((centerQuotMap hker hJ).trans θ) (QuotientGroup.mk l) =
      θ (QuotientGroup.mk (ψ.subgroupMap J l)) := fun _ => rfl
  constructor
  · intro h m m' hm
    obtain ⟨l, hl, hlm⟩ := Subgroup.mem_map.1 m.2
    have hm1 : ψ.subgroupMap J ⟨l, hl⟩ = m := Subtype.ext hlm
    have hm2 : ψ.subgroupMap J ⟨a l, ha l hl⟩ = m' :=
      Subtype.ext (by rw [hm, ← hm1]; exact (hφ l).symm)
    have h1 := h ⟨l, hl⟩ ⟨a l, ha l hl⟩ rfl
    rwa [key, key, hm1, hm2] at h1
  · intro h l l' hl
    rw [key, key]
    apply h
    change ψ (l' : L') = φ (ψ (l : L'))
    rw [hl, hφ]

theorem ggOutsideInndiag_map_iff (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'}
    {φ : MulAut R} (hφ : ∀ l, φ (ψ l) = ψ (a l)) {J : Subgroup L'} (hJ : ⁅J, J⁆ = J) :
    GGOutsideInndiag J a ↔ GGOutsideInndiag (J.map ψ) φ := by
  have hN := mapsTo_map_iff hker hφ hJ
  constructor
  · rintro ⟨ha, hall⟩
    refine ⟨hN.1 ha, ggMarkingAll_centerQuot (centerQuotMap hker hJ) (commutator_top hJ)
      (fun _ _ _ _ _ θ hQ ⟨φ', hφ', hind⟩ => hQ ⟨φ', hφ', ?_⟩) hall⟩
    exact (largeEvenInduces_map_iff hker hφ hJ ha θ φ').2 hind
  · rintro ⟨hb, hall⟩
    have ha := hN.2 hb
    refine ⟨ha, ggMarkingAll_centerQuot (centerQuotMap hker hJ).symm
      (commutator_top (map_perfect hJ))
      (fun _ _ _ _ _ θ hQ ⟨φ', hφ', hind⟩ => hQ ⟨φ', hφ', ?_⟩) hall⟩
    refine (largeEvenInduces_map_iff hker hφ hJ ha _ φ').1 ?_
    rwa [show (centerQuotMap hker hJ).trans ((centerQuotMap hker hJ).symm.trans θ) = θ from
      MulEquiv.ext fun q => by simp]

theorem ggUnitaryCommLifts_map_iff (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'}
    (hJ : ⁅J, J⁆ = J) (n d : ℕ) {A : Subgroup (MulAut L')}
    (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l)) :
    GGUnitaryCommLifts J n d (A : Set (MulAut L')) ↔
      GGUnitaryCommLifts (J.map ψ) n d (TypeA.inducedSub ψ A : Set (MulAut R)) := by
  set e := centerQuotMap hker hJ
  constructor
  · intro h K _ _ hK θ φ₁ hφ₁ φ₂ hφ₂ hn₁ hn₂ A₁ hA₁ A₂ hA₂ hi₁ hi₂
    obtain ⟨a₁, ha₁, hc₁⟩ := TypeA.mem_inducedSub.1 hφ₁
    obtain ⟨a₂, ha₂, hc₂⟩ := TypeA.mem_inducedSub.1 hφ₂
    have hm₁ := (mapsTo_map_iff hker hc₁ hJ).2 hn₁
    have hm₂ := (mapsTo_map_iff hker hc₂ hJ).2 hn₂
    obtain ⟨χ₁, hχ₁, hind₁⟩ := hi₁
    obtain ⟨χ₂, hχ₂, hind₂⟩ := hi₂
    exact h K hK (e.trans θ) a₁ ha₁ a₂ ha₂ hm₁ hm₂ A₁ hA₁ A₂ hA₂
      ⟨χ₁, hχ₁, (largeEvenInduces_map_iff hker hc₁ hJ hm₁ θ χ₁).2 hind₁⟩
      ⟨χ₂, hχ₂, (largeEvenInduces_map_iff hker hc₂ hJ hm₂ θ χ₂).2 hind₂⟩
  · intro h K _ _ hK θ a₁ ha₁ a₂ ha₂ hn₁ hn₂ A₁ hA₁ A₂ hA₂ hi₁ hi₂
    obtain ⟨φ₁, hc₁⟩ := hA a₁ ha₁
    obtain ⟨φ₂, hc₂⟩ := hA a₂ ha₂
    have hθ : e.trans (e.symm.trans θ) = θ := MulEquiv.ext fun q => by simp
    obtain ⟨χ₁, hχ₁, hind₁⟩ := hi₁
    obtain ⟨χ₂, hχ₂, hind₂⟩ := hi₂
    exact h K hK (e.symm.trans θ) φ₁ (TypeA.mem_inducedSub.2 ⟨a₁, ha₁, hc₁⟩) φ₂
      (TypeA.mem_inducedSub.2 ⟨a₂, ha₂, hc₂⟩) ((mapsTo_map_iff hker hc₁ hJ).1 hn₁)
      ((mapsTo_map_iff hker hc₂ hJ).1 hn₂) A₁ hA₁ A₂ hA₂
      ⟨χ₁, hχ₁, (largeEvenInduces_map_iff hker hc₁ hJ hn₁ _ χ₁).1 (by rwa [hθ])⟩
      ⟨χ₂, hχ₂, (largeEvenInduces_map_iff hker hc₂ hJ hn₂ _ χ₂).1 (by rwa [hθ])⟩

end CFSG.StandardType.SCFourCover

end
