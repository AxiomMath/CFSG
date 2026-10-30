module

public import CFSG.RankThree.PartTwo.Sec12.Hering129SPNine
public import CFSG.RankThree.PartTwo.Sec12.Hering129SPLocal
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYa
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129SP

open CFSG CFSG.RankThree.LocalRank

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_fixed_lift (U : Subgroup Y) [U.Normal] (hU3 : ¬ 3 ∣ Nat.card U)
    (hUchar : ∀ (γ : MulAut Y) (u : Y), γ u ∈ U ↔ u ∈ U) (β : MulAut Y) (hβ3 : β ^ 3 = 1)
    (y₀ : Y) (h : y₀⁻¹ * β y₀ ∈ U) : ∃ c : Y, β c = c ∧ y₀⁻¹ * c ∈ U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := Subgroup.zpowers β
  have hA : IsPGroup 3 A := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨g, k, rfl⟩ := g
    apply Subtype.ext
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp only [Nat.cast_ofNat]
    rw [show β ^ (3 : ℤ) = 1 from by exact_mod_cast hβ3, one_zpow]
  let α : A →* MulAut Y := A.subtype
  have hstep : ∀ x : Y, y₀⁻¹ * x ∈ U → y₀⁻¹ * β x ∈ U := by
    intro x hx
    have h1 : y₀⁻¹ * β x = (y₀⁻¹ * β y₀) * β (y₀⁻¹ * x) := by
      rw [map_mul, map_inv]; group
    rw [h1]
    exact U.mul_mem h ((hUchar β _).2 hx)
  have hinv : ∀ (a : A) (x : Y), y₀⁻¹ * x ∈ U → y₀⁻¹ * α a x ∈ U := by
    rintro ⟨a, ha⟩ x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hk : β ^ k = β ^ (k % 3) := zpow_eq_zpow_emod' k hβ3
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    show y₀⁻¹ * (β ^ k) x ∈ U
    rw [hk]
    rcases hk3 with h0 | h1 | h2
    · rw [h0]; simpa using hx
    · rw [h1]; simpa using hstep x hx
    · rw [h2]
      have : (β ^ (2 : ℤ)) x = β (β x) := by
        rw [zpow_two]; rfl
      rw [this]
      exact hstep _ (hstep x hx)
  obtain ⟨c, hc, hfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA α U hU3 y₀).2 hinv
  exact ⟨c, hfix ⟨β, Subgroup.mem_zpowers β⟩, hc⟩

variable {W : Type} [Group W]

theorem exists_inner_of_aut (hW : SporLocal W) (U : Subgroup Y) [U.Normal]
    (hUchar : ∀ (γ : MulAut Y) (u : Y), γ u ∈ U ↔ u ∈ U) (φ : (Y ⧸ U) ≃* W) (β : MulAut Y)
    (hβ3 : β ^ 3 = 1) (hβnt : ∃ y : Y, y⁻¹ * β y ∉ U) :
    ∃ w : W, orderOf w = 3 ∧
      ∀ y : Y, φ (QuotientGroup.mk (β y)) = w * φ (QuotientGroup.mk y) * w⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let α : MulAut Y →* MulAut Y := MonoidHom.id _
  have hN : ∀ (a : MulAut Y), ∀ n ∈ U, α a n ∈ U := fun a n hn => (hUchar a n).2 hn
  let θ := CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α U hN
  have hθ : ∀ (γ : MulAut Y) (y : Y), θ γ (QuotientGroup.mk y) = QuotientGroup.mk (γ y) :=
    fun γ y => rfl
  let γ : MulAut W := MulAut.congr φ (θ β)
  have hγ3 : γ ^ 3 = 1 := by
    show (MulAut.congr φ) (θ β) ^ 3 = 1
    rw [← map_pow, ← map_pow, hβ3, map_one, map_one]
  obtain ⟨w, hw⟩ := hW.inner3 γ hγ3
  have hrel : ∀ y : Y, φ (QuotientGroup.mk (β y)) = w * φ (QuotientGroup.mk y) * w⁻¹ := by
    intro y
    have h1 : γ (φ (QuotientGroup.mk y)) = φ (QuotientGroup.mk (β y)) := by
      show φ (θ β (φ.symm (φ (QuotientGroup.mk y)))) = _
      rw [MulEquiv.symm_apply_apply, hθ]
    rw [← h1, hw]
    rfl
  have hcenter : Subgroup.center W = ⊥ :=
    center_eq_bot_of_simple_nonabelian hW.simple hW.nonabelian
  have hw1 : w ≠ 1 := by
    intro h1
    obtain ⟨y, hy⟩ := hβnt
    apply hy
    have h2 := hrel y
    rw [h1, one_mul, inv_one, mul_one] at h2
    have h3 : (QuotientGroup.mk (β y) : Y ⧸ U) = QuotientGroup.mk y := φ.injective h2
    exact (QuotientGroup.eq.mp h3.symm)
  have hw3 : w ^ 3 = 1 := by
    have h1 : (MulAut.conj (w ^ 3) : MulAut W) = 1 := by rw [map_pow, ← hw, hγ3]
    have h2 : w ^ 3 ∈ Subgroup.center W := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun f : MulAut W => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcenter, Subgroup.mem_bot] at h2
    exact h2
  exact ⟨w, orderOf_eq_prime hw3 hw1, hrel⟩


theorem exists_fixed_preimage (U : Subgroup Y) [U.Normal] (hU3 : ¬ 3 ∣ Nat.card U)
    (hUchar : ∀ (γ : MulAut Y) (u : Y), γ u ∈ U ↔ u ∈ U) (φ : (Y ⧸ U) ≃* W) (β : MulAut Y)
    (hβ3 : β ^ 3 = 1) {w : W}
    (hrel : ∀ y : Y, φ (QuotientGroup.mk (β y)) = w * φ (QuotientGroup.mk y) * w⁻¹) {t : W}
    (ht : w * t = t * w) : ∃ c : Y, β c = c ∧ φ (QuotientGroup.mk c) = t := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (φ.symm t)
  have hy₀t : φ (QuotientGroup.mk y₀) = t := by rw [hy₀]; exact φ.apply_symm_apply t
  have h1 : φ (QuotientGroup.mk (β y₀)) = φ (QuotientGroup.mk y₀) := by
    rw [hrel, hy₀t, mul_inv_eq_iff_eq_mul]; exact ht
  have h2 : (QuotientGroup.mk (β y₀) : Y ⧸ U) = QuotientGroup.mk y₀ := φ.injective h1
  obtain ⟨c, hc, hcU⟩ := exists_fixed_lift U hU3 hUchar β hβ3 y₀ (QuotientGroup.eq.mp h2.symm)
  refine ⟨c, hc, ?_⟩
  rw [← hy₀t]
  congr 1
  exact (QuotientGroup.eq.mpr hcU).symm

theorem isSubnormal_map_subgroupOf {M : Type} [Group M] (ρ : M →* W) (C : Subgroup W)
    (hρ : ∀ m, ρ m ∈ C) (hsurj : ∀ c ∈ C, ∃ m, ρ m = c) {N : Subgroup M} (hN : N.IsSubnormal) :
    ((N.map ρ).subgroupOf C).IsSubnormal := by
  let ρ' : M →* C := ρ.codRestrict C hρ
  have hρ' : Function.Surjective ρ' := fun c => by
    obtain ⟨m, hm⟩ := hsurj c c.2
    exact ⟨m, Subtype.ext hm⟩
  have h := hN.map hρ'
  have heq : N.map ρ' = (N.map ρ).subgroupOf C := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, hnz⟩
      exact ⟨n, hn, Subtype.ext hnz⟩
  rw [← heq]
  exact h


theorem mem_theta_iff (γ : MulAut Y) (u : Y) :
    γ u ∈ aschbacherSolvableCore 3 Y ↔ u ∈ aschbacherSolvableCore 3 Y := by
  have hchar := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.1
  have h := Subgroup.characteristic_iff_comap_eq.mp hchar γ
  show γ.toMonoidHom u ∈ aschbacherSolvableCore 3 Y ↔ _
  rw [← Subgroup.mem_comap, h]

end Lift

theorem no_sporadic_cover {Y : Type} [Group Y] [Finite Y] (hYp : Group.IsPerfect Y)
    {W : Type} [Group W] (hW : SporLocal W)
    (φ : (Y ⧸ aschbacherSolvableCore 3 Y) ≃* W)
    (β : MulAut Y) (hβ3 : β ^ 3 = 1)
    (hβnt : ∃ y : Y, y⁻¹ * β y ∉ aschbacherSolvableCore 3 Y)
    (R : Subgroup Y) (hRU : R ≤ aschbacherSolvableCore 3 Y)
    (hRn : ∀ u ∈ aschbacherSolvableCore 3 Y, ∀ r ∈ R, u * r * u⁻¹ ∈ R)
    (hRodd : Odd (Nat.card R)) (hR : ∀ u ∈ aschbacherSolvableCore 3 Y, u⁻¹ * β u ∈ R)
    (Mfix : Subgroup Y) (hMfix : ∀ y, y ∈ Mfix ↔ β y = y)
    (X : Subgroup Y) (hXp : Group.IsPerfect X) (hXM : X ≤ Mfix)
    (hXsub : (X.subgroupOf Mfix).IsSubnormal)
    {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) (hF3 : ¬ 3 ∣ Nat.card F)
    (φK : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφK : Function.Surjective φK)
    (hkerK : φK.ker ≤ aschbacherSolvableCore 3 X) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite W := Finite.of_equiv _ φ.toEquiv
  set U : Subgroup Y := aschbacherSolvableCore 3 Y with hU
  obtain ⟨hUs, -, hU3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  haveI : Group.IsSolvable U := hUs
  have hUc : ∀ (γ : MulAut Y) (u : Y), γ u ∈ U ↔ u ∈ U := mem_theta_iff
  obtain ⟨w, hw3, hrel⟩ := exists_inner_of_aut hW U hUc φ β hβ3 hβnt
  set π : Y →* W := φ.toMonoidHom.comp (QuotientGroup.mk' U) with hπdef
  have hπ : ∀ y, π y = φ (QuotientGroup.mk y) := fun y => rfl
  have hπsurj : Function.Surjective π := fun t => by
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm t)
    exact ⟨y, by rw [hπ, hy]; exact φ.apply_symm_apply t⟩
  have hπker : π.ker = U := by
    ext y
    rw [MonoidHom.mem_ker, hπ]
    constructor
    · intro h
      have : (QuotientGroup.mk y : Y ⧸ U) = 1 := φ.injective (by rw [h, map_one])
      exact (QuotientGroup.eq_one_iff y).mp this
    · intro h
      rw [(QuotientGroup.eq_one_iff y).mpr h, map_one]
  have hodd : Odd (Nat.card U) :=
    odd_card_of_perfect_cover hYp U hUs hW.simple hW.noDouble π hπsurj hπker β
      (fun u => (hUc β u).symm) hβnt R hRU hRn hRodd hR
  let ρX : X →* W := π.comp X.subtype
  have hρX : ∀ x : X, ρX x = π (x : Y) := fun x => rfl
  have hmem : ∀ n : ρX.ker, ((n : X) : Y) ∈ U := by
    intro n
    rw [← hπker, MonoidHom.mem_ker]
    exact n.2
  let g : ρX.ker →* U := (X.subtype.comp ρX.ker.subtype).codRestrict U hmem
  have hginj : Function.Injective g := by
    intro a b h
    have h1 : ((g a : U) : Y) = ((g b : U) : Y) := congrArg (fun z : U => (z : Y)) h
    exact Subtype.ext (Subtype.ext h1)
  have hkerU : Nat.card ρX.ker ∣ Nat.card U := Subgroup.card_dvd_of_injective g hginj
  set P : Subgroup W := ρX.range with hP
  have hPC : P ≤ Subgroup.centralizer ({w} : Set W) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : β (x : Y) = x := (hMfix _).1 (hXM x.2)
    have h := hrel (x : Y)
    rw [hfix] at h
    have h' : π x = w * π x * w⁻¹ := h
    rw [eq_mul_inv_iff_mul_eq] at h'
    exact h'
  have hPp : Group.IsPerfect P := by
    haveI := hXp
    exact Group.IsPerfect.range ρX
  have hPsub : (P.subgroupOf (Subgroup.centralizer ({w} : Set W))).IsSubnormal := by
    let ρM : Mfix →* W := π.comp Mfix.subtype
    have hρM : ∀ m : Mfix, ρM m ∈ Subgroup.centralizer ({w} : Set W) := by
      intro m
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : β (m : Y) = m := (hMfix _).1 m.2
      have h := hrel (m : Y)
      rw [hfix] at h
      have h' : π m = w * π m * w⁻¹ := h
      rw [eq_mul_inv_iff_mul_eq] at h'
      exact h'
    have hsurj : ∀ c ∈ Subgroup.centralizer ({w} : Set W), ∃ m : Mfix, ρM m = c := by
      intro c hc
      have hc' : w * c = c * w := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
      obtain ⟨y, hy, hyc⟩ := exists_fixed_preimage U hU3 hUc φ β hβ3 hrel hc'
      exact ⟨⟨y, (hMfix y).2 hy⟩, hyc⟩
    have h := isSubnormal_map_subgroupOf ρM _ hρM hsurj hXsub
    have heq : (X.subgroupOf Mfix).map ρM = P := by
      ext t
      constructor
      · rintro ⟨⟨m, hm⟩, hmX, rfl⟩
        exact ⟨⟨m, hmX⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨x, hXM x.2⟩, x.2, rfl⟩
    rw [heq] at h
    exact h
  obtain ⟨eQ⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL_of_four_le hF4 φK hφK hkerK
  set θX : Subgroup X := aschbacherSolvableCore 3 X with hθX
  obtain ⟨-, -, hθ3X, hmaxX, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hQs : IsSimpleGroup (X ⧸ θX) := by
    haveI : IsSimpleGroup (CFSG.PGLModel.projSL 2 F) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 2) F le_rfl (Or.inr (by omega))
        (Or.inr (by omega))
    exact eQ.isSimpleGroup
  have hQn : ∃ a b : X ⧸ θX, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative (X ⧸ θX) := ⟨⟨hcon⟩⟩
    haveI : Group.IsPerfect X := hXp
    haveI : Nontrivial (X ⧸ θX) := hQs.toNontrivial
    exact Group.IsPerfect.not_isMulCommutative (X ⧸ θX) inferInstance
  have hQcard : Nat.card (X ⧸ θX) * Nat.gcd 2 (Nat.card F - 1) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact Sec11.KSListsProof.card_projSL_two_mul F
  have hker_θ : ρX.ker ≤ θX :=
    hmaxX ρX.ker (MonoidHom.normal_ker ρX) (Group.isSolvable_of_isSolvable_injective hginj)
      (fun h3 => hU3 (h3.trans hkerU))
  let ρ' : X →* P := ρX.rangeRestrict
  have hρ' : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective ρX
  have hkerρ' : ρ'.ker = ρX.ker := MonoidHom.ker_rangeRestrict ρX
  let ψ : P →* X ⧸ θX := (MonoidHom.liftOfSurjective ρ' hρ')
    ⟨QuotientGroup.mk' θX, by rw [hkerρ', QuotientGroup.ker_mk']; exact hker_θ⟩
  have hψρ : ∀ x : X, ψ (ρ' x) = (x : X ⧸ θX) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ρ' _ _ _ x
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨ρ' x, hψρ x⟩
  have hψker : ¬ 3 ∣ Nat.card ψ.ker := by
    let h : θX →* ψ.ker := (ρ'.comp θX.subtype).codRestrict ψ.ker (fun z => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply, hψρ]
      exact (QuotientGroup.eq_one_iff (z : X)).mpr z.2)
    have hh : Function.Surjective h := by
      intro z
      obtain ⟨x, hx⟩ := hρ' z
      have hxθ : x ∈ θX := by
        have := z.2
        rw [MonoidHom.mem_ker, ← hx, hψρ] at this
        exact (QuotientGroup.eq_one_iff x).mp this
      exact ⟨⟨x, hxθ⟩, Subtype.ext hx⟩
    exact fun h3 => hθ3X (h3.trans (Subgroup.card_dvd_of_surjective hh))
  obtain ⟨hs7, hP168⟩ :=
    spor_local_lemma hW hw3 hPC hPsub hPp hQs hQn ψ hψsurj hψker hF4 hF3 hQcard
  have hPX : Nat.card X = Nat.card ρX.ker * Nat.card P := by
    have := card_eq_ker_mul ρ' hρ'
    rwa [hkerρ'] at this
  have hXK : Nat.card X = Nat.card φK.ker * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    card_eq_ker_mul φK hφK
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL]
    exact CFSG.Open.StatedAPI.card_statedSL_two F
  rw [hs7] at hSL
  rw [hP168] at hPX
  rw [hSL] at hXK
  have hcnt : Nat.card ρX.ker * 168 = Nat.card φK.ker * (7 * (7 ^ 2 - 1)) :=
    hPX.symm.trans hXK
  norm_num at hcnt
  have h2ker : 2 ∣ Nat.card ρX.ker := ⟨Nat.card φK.ker, by omega⟩
  have h2U : 2 ∣ Nat.card U := h2ker.trans hkerU
  obtain ⟨k, hk⟩ := h2U
  rw [Nat.odd_iff] at hodd
  omega

end CFSG.RankThree.PartTwo.Sec12.Hering129SP
