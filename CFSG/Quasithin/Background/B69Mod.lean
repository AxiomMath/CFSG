module

public import CFSG.Quasithin.Background.B69Main
public import CFSG.Quasithin.Background.B69SL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_surj_autSub {X : Subgroup (MulAut V)} {W : Subgroup V} (h : X ≤ stabSub W) :
    ∃ f : ↥X →* ↥(autSub X W), Function.Surjective f := by
  refine ⟨((resHom W).subgroupMap (X.subgroupOf (stabSub W))).comp
    (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom, ?_⟩
  exact ((resHom W).subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe h).symm.surjective

omit [Finite V] in
theorem exists_surj_autQuot {A : Subgroup (MulAut V)} {U : Subgroup V} (h : A ≤ stabSub U) :
    ∃ f : ↥A →* ↥(autQuot A U), Function.Surjective f := by
  refine ⟨((quotHom U).subgroupMap (A.subgroupOf (stabSub U))).comp
    (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom, ?_⟩
  exact ((quotHom U).subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe h).symm.surjective

omit [Finite V] in
theorem le_stabSub_redU (L A : Subgroup (MulAut V)) : L ≤ stabSub (redU L A) :=
  le_sup_left.trans (B1Red.le_stabSub_fixV_pCoreOf (L ⊔ A))

omit [Finite V] in
theorem exists_surj_secL {L A : Subgroup (MulAut V)} {I : Subgroup ↥(redU L A)}
    (hI : I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A))) :
    ∃ f : ↥L →* ↥(secL L A I), Function.Surjective f := by
  obtain ⟨f₁, h₁⟩ := exists_surj_autSub (le_stabSub_redU L A)
  have hinv := (mem_irrPlus_top_iff.1 hI).1
  have hXI : autSub L (redU L A) ≤ stabSub I := B1.le_stabSub_of_invariant hinv
  have hC : ∀ x ∈ autSub L (redU L A), ∀ w ∈ I ⊓ fixV (autSub L (redU L A)),
      x w ∈ I ⊓ fixV (autSub L (redU L A)) := isInv_inf hinv (isInv_fixV _)
  have hXC : autSub L (redU L A) ≤ stabSub (I ⊓ fixV (autSub L (redU L A))) :=
    B1.le_stabSub_of_invariant hC
  obtain ⟨f₂, h₂⟩ := exists_surj_autSub hXI
  obtain ⟨f₃, h₃⟩ := exists_surj_autQuot (autSub_le_stabSub_subgroupOf hXC (W := I))
  exact ⟨f₃.comp (f₂.comp f₁), h₃.comp (h₂.comp h₁)⟩

omit [Finite V] in
theorem secL_nontrivial {L A : Subgroup (MulAut V)} {I : Subgroup ↥(redU L A)}
    (hI : I ∈ IrrPlus (autSub L (redU L A)) (⊤ : Subgroup ↥(redU L A))) :
    Nontrivial ↥(secL L A I) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨hinv, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hI
  have hXI : autSub L (redU L A) ≤ stabSub I := B1.le_stabSub_of_invariant hinv
  have hC : ∀ x ∈ autSub L (redU L A), ∀ w ∈ I ⊓ fixV (autSub L (redU L A)),
      x w ∈ I ⊓ fixV (autSub L (redU L A)) := isInv_inf hinv (isInv_fixV _)
  have hXC : autSub L (redU L A) ≤ stabSub (I ⊓ fixV (autSub L (redU L A))) :=
    B1.le_stabSub_of_invariant hC
  have hgens : commSub I (autSub L (redU L A)) ≤ I ⊓ fixV (autSub L (redU L A)) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hfix : (QuotientGroup.mk (⟨w, hw⟩ : ↥I) :
        Sec I (I ⊓ fixV (autSub L (redU L A)))) ∈ fixV (secL L A I) := by
      intro φ hφ
      have : (⟨φ, hφ⟩ : ↥(secL L A I)) = ⟨1, (secL L A I).one_mem⟩ := Subsingleton.elim _ _
      have h1 : φ = 1 := congrArg Subtype.val this
      rw [h1]
      rfl
    have key := (mk_mem_fixV_autQuot (X := autSub (autSub L (redU L A)) I)
      (U := (I ⊓ fixV (autSub L (redU L A))).subgroupOf I)).1 hfix
    have hg : resHom I ⟨x, hXI hx⟩ ∈ autSub (autSub L (redU L A)) I :=
      mem_autSub.2 ⟨⟨x, hXI hx⟩, hx, rfl⟩
    have hgs : resHom I ⟨x, hXI hx⟩ ∈ stabSub ((I ⊓ fixV (autSub L (redU L A))).subgroupOf I) :=
      autSub_le_stabSub_subgroupOf hXC hg
    have := key _ hg hgs
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  rw [hcomm] at hgens
  exact absurd (le_antisymm inf_le_left hgens ▸ hlt) (lt_irrefl _)

theorem natRealizes_injective {W : Type*} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)}
    {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) : Function.Injective π := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, -, hβ⟩ := h
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hall : ∀ x : Multiplicative (ι → K), natAct Γ γ x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ :
      ↥(⊤ : Subgroup (Multiplicative (ι → K)))))
    have hπu : (((π γ : ↥H) : MulAut W) (u : W) ∈ (⊤ : Subgroup W)) := Subgroup.mem_top _
    have h2 := hβ γ u ⟨x, Subgroup.mem_top x⟩ hπu (Subgroup.mem_top _) hu
    have h3 : (⟨((π γ : ↥H) : MulAut W) (u : W), hπu⟩ : ↥(⊤ : Subgroup W)) = u := by
      apply Subtype.ext
      simp [hγ]
    have h4 := ((congrArg β h3).symm.trans h2).symm.trans hu
    have h5 := QuotientGroup.eq.1 h4
    rw [Subgroup.mem_subgroupOf] at h5
    have h6 : (natAct Γ γ x)⁻¹ * x = 1 := (Subgroup.mem_bot).1 h5
    exact inv_mul_eq_one.1 h6
  have hall' : ∀ x : ι → K,
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x = x := fun x =>
    Multiplicative.ofAdd.injective (hall (Multiplicative.ofAdd x))
  have hM : ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = 1 := by
    ext i j
    have := congrFun (hall' (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  exact Subtype.ext (Units.ext (by simpa using hM))

theorem sectionHas_case9 {L A : Subgroup (MulAut V)}
    (h : SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case9 G L')) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (Q : Type) (_ : Group Q) (ℓ : ↥L →* Q),
      Function.Surjective ℓ ∧ (n = 4 ∨ n = 5) ∧ Nat.card K = 2 ∧
        Nonempty (Q ≃* ↥(StatedSL n K)) := by
  obtain ⟨I, hI, -, n, hn, ⟨K, hKf, hKfin, hK, π, hπ⟩, -⟩ := h
  obtain ⟨ℓ, hℓ⟩ := exists_surj_secL hI
  have hinj := natRealizes_injective hπ
  exact ⟨n, K, hKf, hKfin, ↥(secL L A I), inferInstance, ℓ, hℓ, hn, by simpa using hK,
    ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩

theorem sectionHas_case10ii {L A : Subgroup (MulAut V)}
    (h : SectionHas L A (fun {_ : Type} [CommGroup _] [Finite _] G L' => B42Case10ii G L')) :
    ∃ (Q : Type) (_ : Group Q) (ℓ : ↥L →* Q), Function.Surjective ℓ ∧
      Nonempty (Q ≃* ↥(StatedSL 4 (ZMod 2))) := by
  obtain ⟨I, hI, ⟨π, hπ⟩, -⟩ := h
  obtain ⟨ℓ, hℓ⟩ := exists_surj_secL hI
  have hnt : Nontrivial ↥(secL L A I) := secL_nontrivial hI
  have hs : IsSimpleGroup (FFModel.extSq (ZMod 2) 4).Gam :=
    isSimpleGroup_statedSL_two (K := ZMod 2) (by simp) (by norm_num)
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have := hs
    rcases CFSG.eq_bot_or_eq_top_of_normal π.ker (MonoidHom.normal_ker π) with hbot | htop
    · have : g ∈ π.ker := MonoidHom.mem_ker.2 hg
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ.1 a
      obtain ⟨y, rfl⟩ := hπ.1 b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  exact ⟨↥(secL L A I), inferInstance, ℓ, hℓ, ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩

end B69

end CFSG.Quasithin
