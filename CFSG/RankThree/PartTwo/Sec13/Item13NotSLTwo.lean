module

public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Lift

variable {T Y : Type*} [Group T] [Finite T] [Group Y]

theorem exists_lift_normalizing (φ : T →* Y) (hφ : Function.Surjective φ)
    (hker : Nat.Coprime 3 (Nat.card φ.ker)) {A : Subgroup T} (hA : IsPGroup 3 A)
    {EY : Subgroup Y} (hEN : EY ≤ Subgroup.normalizer ((A.map φ : Subgroup Y) : Set Y))
    (hEp : IsPGroup 3 EY) :
    ∃ E : Subgroup T, E.map φ = EY ∧ Function.Injective (φ.comp E.subtype) ∧
      E ≤ Subgroup.normalizer (A : Set T) ∧ ∀ x ∈ A, ∀ y ∈ E, φ x = φ y → x = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := EY ⊔ A.map φ with hQ
  have hQp : IsPGroup 3 Q := hEp.to_sup_of_normal_right' (hA.map φ) hEN
  set M := Q.comap φ with hM
  have hAM : A ≤ M := fun a ha => Subgroup.mem_sup_right (Subgroup.mem_map_of_mem φ ha)
  have hAMp : IsPGroup 3 (A.subgroupOf M) := hA.comap_subtype
  obtain ⟨S, hAS⟩ := hAMp.exists_le_sylow
  set S' := (S : Subgroup M).map M.subtype with hS'
  have hAS' : A ≤ S' := fun a ha => ⟨⟨a, hAM ha⟩, hAS (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hS'M : S' ≤ M := Subgroup.map_subtype_le _
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map M.subtype
  have hinj := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 3
    Nat.prime_three φ hker S' hS'p
  have hinj' : ∀ x ∈ S', ∀ y ∈ S', φ x = φ y → x = y := fun x hx y hy h =>
    congrArg Subtype.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  let ψ : M →* Q := (φ.comp M.subtype).codRestrict Q fun x => x.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨t, rfl⟩ := hφ q
    exact ⟨⟨t, hq⟩, rfl⟩
  have hSQ : ∀ q ∈ Q, ∃ s ∈ S', φ s = q := by
    intro q hq
    set P := S.mapSurjective hψ
    have hPtop : (P : Subgroup Q) = ⊤ :=
      (P.is_maximal' (IsPGroup.of_equiv hQp Subgroup.topEquiv.symm) le_top).symm
    have hmem : (⟨q, hq⟩ : Q) ∈ (P : Subgroup Q) := hPtop ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsq⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsq⟩
  set E := S' ⊓ EY.comap φ with hE
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := hSQ y (Subgroup.mem_sup_left hy)
      exact ⟨s, ⟨hs, hy⟩, rfl⟩
  · intro x y hxy
    exact Subtype.ext (hinj' x x.2.1 y y.2.1 hxy)
  · intro x hx
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 : φ (x * a * x⁻¹) ∈ A.map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hEN hx.2) _).mp (Subgroup.mem_map_of_mem φ ha)
    obtain ⟨a', ha', hea⟩ := h1
    have h2 : x * a * x⁻¹ ∈ S' :=
      S'.mul_mem (S'.mul_mem hx.1 (hAS' ha)) (S'.inv_mem hx.1)
    rw [← hinj' a' (hAS' ha') _ h2 hea]
    exact ha'
  · intro x hx y hy h
    exact hinj' x (hAS' hx) y hy.1 h

end Lift

theorem not_isHeisCentral_of_isSLThreePiTwo {X : Type} [Group X] [Finite X] {M : Type}
    [Group M] [Group.IsPerfect M] [Nontrivial M] (hSL : IsSLThreePiTwo X)
    (hH : IsHeisCentral X M) : False := by
  obtain ⟨U, V, hUV, hcomm, -, ⟨eV⟩, -⟩ := hH
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  have hVp : Group.IsPerfect V :=
    Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
  have hVnt : Nontrivial V := eV.toEquiv.nontrivial
  have hV1 : V ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot V).mp hVnt
  by_cases hq2 : 2 < p ^ f
  · have hVn : V.Normal := by
      have hN : Subgroup.normalizer (V : Set X) = ⊤ := by
        rw [eq_top_iff, ← hUV]
        refine sup_le (fun u hu => Subgroup.mem_normalizer_fintype fun v hv => ?_)
          Subgroup.le_normalizer
        rw [hcomm u hu v hv, mul_inv_cancel_right]
        exact hv
      exact Subgroup.normalizer_eq_top_iff.mp hN
    have hL₀V : D.L₀ ≤ V := D.le_of_normal hq2 hVn hVp hV1
    apply D.a_not_mem_sup
    have hle : (⊤ : Subgroup X) ≤ D.L₀ ⊔ Subgroup.centralizer (D.L₀ : Set X) := by
      rw [← hUV]
      refine sup_le (fun u hu => Subgroup.mem_sup_right
        (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_))
        ((D.le_of_isPerfect hVp).trans le_sup_left)
      exact (hcomm u hu l (hL₀V hl)).symm
    exact hle (Subgroup.mem_top _)
  · have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable V := Group.isSolvable_of_isSolvable_injective V.subtype_injective
    exact Group.IsPerfect.not_isSolvable V inferInstance

section Sec13

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

omit [Finite G] in
theorem not_isCyclic_of_mem {P : Subgroup G} (hexp : ∀ x ∈ P, x ^ 3 = 1) {x y : G}
    (hx : x ∈ P) (hx1 : x ≠ 1) (hy : y ∈ P) (hyx : y ∉ Subgroup.zpowers x) : ¬ IsCyclic P := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg3 : (g : G) ^ 3 = 1 := hexp g g.2
  have hmem : ∀ z ∈ P, z ∈ Subgroup.zpowers (g : G) := fun z hz => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgx : (g : G) ∈ Subgroup.zpowers x := by
    rcases eq_of_mem_zpowers_of_pow_three hg3 (hmem x hx) with h | h | h
    · exact absurd h hx1
    · rw [h]
      exact Subgroup.mem_zpowers _
    · have e : (g : G) = x ^ 2 := by
        rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3, one_mul, pow_one]
      rw [e]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  exact hyx (Subgroup.zpowers_le.mpr hgx (hmem y hy))

theorem mem_theta_of_mk_eq_one (hL : L ∈ thetaComponentsAt 3 c) {g : G} (hg : g ∈ L)
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
      (⟨g, le_normalizer_zpowers_of_mem hL hg⟩ : Subgroup.normalizer (Subgroup.zpowers c : Set G)) =
        1) : g ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨η, hη⟩ := exists_lBarEquiv hL
  have h1 : η ((⟨g, hg⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 := by
    apply Subtype.ext
    rw [hη]
    exact h
  rw [map_eq_one_iff _ η.injective, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem exists_E_of_isSLThreePiTwo (hD : Sec13Data G A c L)
    (hSL : IsSLThreePiTwo (lBarA c L A)) :
    ∃ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      ¬ IsCyclic (E ⊓ thetaQuotCentralizer L : Subgroup G) ∧ ¬ IsCyclic (E ⊓ L : Subgroup G) := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θH := aschbacherSolvableCore 3 H with hθH
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hLAN : L ⊔ A ≤ Subgroup.normalizer (L : Set G) := sup_le hLN hD.le_normalizer
  have hLAH : L ⊔ A ≤ H :=
    sup_le (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt) hD.A_le_normalizer_zpowers
  let ι : (L ⊔ A : Subgroup G) →* H := Subgroup.inclusion hLAH
  let φ : (L ⊔ A : Subgroup G) →* lBarA c L A :=
    ((QuotientGroup.mk' θH).comp ι).codRestrict (lBarA c L A) fun x =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
  have hφv : ∀ x : (L ⊔ A : Subgroup G), ((φ x : lBarA c L A) : H ⧸ θH) =
      QuotientGroup.mk' θH ⟨(x : G), hLAH x.2⟩ := fun x => rfl
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hker : Nat.Coprime 3 (Nat.card φ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
    let j : φ.ker →* θH :=
      { toFun := fun x => ⟨ι x, by
          have h1 : ((φ x : lBarA c L A) : H ⧸ θH) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
          rw [hφv, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
          exact h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun x y hxy => by
      have h1 : ((ι x : H) : G) = ((ι y : H) : G) := by
        have := congrArg (fun z : θH => ((z : H) : G)) hxy
        exact this
      exact Subtype.ext (Subtype.ext h1)
    exact h3.trans (Subgroup.card_dvd_of_injective j hj)
  set A_T := A.subgroupOf (L ⊔ A) with hA_T
  have hA_Tp : IsPGroup 3 A_T := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hĀ : A_T.map φ = (aBarHom hD).range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_right a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hĀe : CFSG.Assembly.IsElemAbelian 3 (A_T.map φ) := by
    rw [hĀ]
    refine ⟨⟨⟨fun y y' => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := y
      obtain ⟨_, a', rfl⟩ := y'
      apply Subtype.ext
      change aBarHom hD a * aBarHom hD a' = aBarHom hD a' * aBarHom hD a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hD.commute a.2 a'.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 _ a.2)
      rw [this, map_one]
  have hĀ27 : Nat.card (A_T.map φ) = 27 := by
    rw [hĀ, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective hD)).toEquiv, hD.card_eq]
  have hsup : D.L₀ ⊔ A_T.map φ = ⊤ := by
    rw [hL₀, hĀ]
    exact lBar_sup_range_aBarHom hD
  set cbar := mkC (L := L) hD.mem_A with hcbar
  have hcT : (⟨c, Subgroup.mem_sup_right hD.mem_A⟩ : (L ⊔ A : Subgroup G)) ∈ A_T :=
    Subgroup.mem_subgroupOf.mpr hD.mem_A
  have hφc : φ ⟨c, Subgroup.mem_sup_right hD.mem_A⟩ = cbar := rfl
  have hcbarL : cbar ∈ D.L₀ := by
    rw [hL₀]
    exact Subgroup.mem_subgroupOf.mpr ⟨⟨c, le_normalizer_zpowers_of_mem
      hD.mem_thetaComponentsAt hcL⟩, Subgroup.mem_subgroupOf.mpr hcL, rfl⟩
  have hcbarĀ : cbar ∈ A_T.map φ := ⟨_, hcT, hφc⟩
  have hC : A_T.map φ ⊓ Subgroup.centralizer (D.L₀ : Set (lBarA c L A)) ≤
      Subgroup.zpowers cbar := by
    rintro y ⟨⟨x, hxA, rfl⟩, hyC⟩
    have hxA' : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hxA
    have hsc : (x : G) ∈ Late.sectionCentralizer A L
        ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨hxA', fun l hl => ?_⟩
      have hg : (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hxA') l).mp hl)
          (L.inv_mem hl)
      refine mem_theta_of_mk_eq_one hD.mem_thetaComponentsAt hg ?_
      set lT : (L ⊔ A : Subgroup G) := ⟨l, Subgroup.mem_sup_left hl⟩
      have hlΛ : φ lT ∈ D.L₀ := by
        rw [hL₀]
        exact Subgroup.mem_subgroupOf.mpr ⟨⟨l, le_normalizer_zpowers_of_mem
          hD.mem_thetaComponentsAt hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have h1 : φ x * φ lT = φ lT * φ x :=
        (Subgroup.mem_centralizer_iff.mp hyC _ hlΛ).symm
      have h2 : φ (x * lT * x⁻¹ * lT⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h3 := congrArg (fun z : lBarA c L A => (z : H ⧸ θH)) h2
      simp only [hφv] at h3
      exact h3
    rw [hD.sectionCentralizer_eq] at hsc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsc
    have hxe : x = (⟨c, Subgroup.mem_sup_right hD.mem_A⟩ : (L ⊔ A : Subgroup G)) ^ k :=
      Subtype.ext (by simp [hk])
    rw [hxe, map_zpow, hφc]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨EY, hEN, hEe, hE27, hcE, huE, v, hvE, hvL, hvc⟩ := D.exists_E hĀe hĀ27 hsup hcbarL
    (mkC_mem_center hD) (mkC_ne_one hD) hcbarĀ hC
  have hEp : IsPGroup 3 EY := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 _ x.2)⟩
  obtain ⟨ET, hmap, hinj, hETN, hAE⟩ := exists_lift_normalizing φ hφ hker hA_Tp hEN hEp
  have hlift : ∀ y ∈ EY, ∃ x ∈ ET, φ x = y := fun y hy => by
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  have hinj' : ∀ x ∈ ET, ∀ y ∈ ET, φ x = φ y → x = y := fun x hx y hy h =>
    congrArg Subtype.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hETmem : ∀ x ∈ ET, φ x ∈ EY := fun x hx => hmap ▸ Subgroup.mem_map_of_mem φ hx
  have hET3 : ∀ x ∈ ET, x ^ 3 = 1 := fun x hx => hinj' _ (ET.pow_mem hx 3) _ ET.one_mem
    (by rw [map_pow, map_one]; exact hEe.2 _ (hETmem x hx))
  set E := ET.map (L ⊔ A).subtype with hEdef
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Subtype.val (hET3 x hx)
  obtain ⟨xc, hxc, hφxc⟩ := hlift cbar hcE
  have hcE' : c ∈ E := by
    have h1 := hAE _ hcT xc hxc (by rw [hφc, hφxc])
    exact ⟨_, h1 ▸ hxc, rfl⟩
  obtain ⟨xu, hxu, hφxu⟩ := hlift D.u huE
  have hxuC : (xu : G) ∈ thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hLAN xu.2, fun l hl => ?_⟩
    have hg : l⁻¹ * ((xu : G) * l * (xu : G)⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp (hLAN xu.2) l).mp hl)
    refine mem_theta_of_mk_eq_one hD.mem_thetaComponentsAt hg ?_
    set lT : (L ⊔ A : Subgroup G) := ⟨l, Subgroup.mem_sup_left hl⟩
    have hlΛ : φ lT ∈ D.L₀ := by
      rw [hL₀]
      exact Subgroup.mem_subgroupOf.mpr ⟨⟨l, le_normalizer_zpowers_of_mem
        hD.mem_thetaComponentsAt hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have h1 : φ xu * φ lT = φ lT * φ xu := by
      rw [hφxu]
      exact (Subgroup.mem_centralizer_iff.mp D.mem_centralizer _ hlΛ).symm
    have h2 : φ (lT⁻¹ * (xu * lT * xu⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := congrArg (fun z : lBarA c L A => (z : H ⧸ θH)) h2
    simp only [hφv] at h3
    exact h3
  have hxuc : (xu : G) ∉ Subgroup.zpowers c := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hxe : xu = (⟨c, Subgroup.mem_sup_right hD.mem_A⟩ : (L ⊔ A : Subgroup G)) ^ k :=
      Subtype.ext (by simp [hk])
    apply D.not_mem
    rw [← hφxu, hxe, map_zpow, hφc]
    exact D.L₀.zpow_mem hcbarL k
  obtain ⟨xv, hxv, hφxv⟩ := hlift v hvE
  have hxvL : (xv : G) ∈ L := by
    have h1 : QuotientGroup.mk' θH (ι xv) ∈ Sec12.lBar c L := by
      have := hvL
      rw [← hφxv, hL₀] at this
      exact Subgroup.mem_subgroupOf.mp this
    refine mem_of_mk_mem_lBar hD.mem_thetaComponentsAt (k := 1) ?_ h1
    have := hET3 xv hxv
    rw [pow_one, ← map_pow, this, map_one]
  have hxvc : (xv : G) ∉ Subgroup.zpowers c := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hxe : xv = (⟨c, Subgroup.mem_sup_right hD.mem_A⟩ : (L ⊔ A : Subgroup G)) ^ k :=
      Subtype.ext (by simp [hk])
    apply hvc
    rw [← hφxv, hxe, map_zpow, hφc]
    exact Subgroup.zpow_mem_zpowers _ _
  refine ⟨E, le_inf (Subgroup.map_subtype_le _) ?_, ⟨⟨⟨fun y y' => ?_⟩⟩, hE3⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hETN hx) ⟨a, Subgroup.mem_sup_right ha⟩).mp
      (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp h1
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := y
    obtain ⟨_, ⟨x', hx', rfl⟩⟩ := y'
    apply Subtype.ext
    change ((x * x' : (L ⊔ A : Subgroup G)) : G) = ((x' * x : (L ⊔ A : Subgroup G)) : G)
    congr 1
    refine hinj' _ (ET.mul_mem hx hx') _ (ET.mul_mem hx' hx) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨φ x, hETmem x hx⟩ ⟨φ x', hETmem x' hx'⟩)
  · rw [hEdef, Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, ← hE27, ← hmap]
    have hrange : (φ.comp ET.subtype).range = ET.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  · exact not_isCyclic_of_mem (fun x hx => hE3 x hx.1) ⟨hcE',
      Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt⟩
      hD.ne_one ⟨⟨xu, hxu, rfl⟩, hxuC⟩ hxuc
  · exact not_isCyclic_of_mem (fun x hx => hE3 x hx.1) ⟨hcE', hcL⟩ hD.ne_one
      ⟨⟨xv, hxv, rfl⟩, hxvL⟩ hxvc

theorem not_mem_of_center_eq_bot_prod (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) : c ∉ L :=
  not_mem_of_center_inf_commutator h φ (by rw [hZ, bot_inf_eq])

theorem item131_seven_of_mem (h131 : Item131) (hspor : SporadicModels131)
    (h : Sec13Data G A c L) (hcL : c ∈ L) :
    (Sec4.IsSLThreePiTwo (lBarA c L A) ∨
          (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
              Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
              Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
                CFSG.Blueprint.NativeSporadic.M22))) ∧
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
          CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
          ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
          ¬ IsCyclic (E ⊓ L : Subgroup G) →
            E ∈ partTwoF G ∧ (E ∉ partTwoT G →
              Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
              (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
                Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
              ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
                omegaA E = orbitIn A (Subgroup.zpowers e) ∧
                ∃ I : Subgroup G, lA E e = {I} ∧
                  Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := hspor
  rcases h131 G A c L h with ⟨hL3, -⟩ | ⟨hPGL, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | h7
  · exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact not_mem_of_center_eq_bot_prod h (isPerfect_center_projSL p e he hq).2 φ hcL
    · by_cases hq2 : 2 < p ^ e
      · exact not_mem_of_center_eq_bot_prod h (isPerfect_center_projSU p e he hq hq2).2 φ hcL
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  · exfalso
    obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_eq_bot_prod h (center_projImage_glPi hK hq hq2) φ hcL
    · have hf : f ≠ 0 := by have := hK.one_le; omega
      have h2 : p ^ f = 2 := by
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h isPerfect_center_alt7.2 φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hM22z φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hM12z φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hJ2z φ)
  · exact h7

theorem notSLTwoOfHypT_of (h131 : Item131) (hspor : SporadicModels131) : NotSLTwoOfHypT := by
  intro G _ _ A c L hD hT hSL
  have hcL := mem_of_isSLThreePiTwo slTwoCenter hD hSL
  obtain ⟨-, -, hE⟩ := item131_seven_of_mem h131 hspor hD hcL
  obtain ⟨E, hEle, hEe, hE27, hEC, hEL⟩ := exists_E_of_isSLThreePiTwo hD hSL
  obtain ⟨-, hET⟩ := hE E hEle hEe hE27 hEC hEL
  have hEnT : E ∉ partTwoT G := by
    intro hET'
    have hEC' : E ≤ Subgroup.centralizer ({c} : Set G) :=
      hEle.trans (inf_le_left.trans (sup_le hD.le_centralizer hD.A_le_centralizer))
    have hmem : E ∈ collectionIn (partTwoT G) (Subgroup.centralizer ({c} : Set G)) :=
      ⟨hET', hEC'⟩
    rw [hT.2.2 c hD.zpowers_mem_omegaA] at hmem
    exact hmem
  obtain ⟨hHeis, -⟩ := hET hEnT
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq.1
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hq.2.1
  have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  exact not_isHeisCentral_of_isSLThreePiTwo hSL hHeis

end Sec13

end CFSG.RankThree.PartTwo.Sec13
