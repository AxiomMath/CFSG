module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFK
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFacts
public import CFSG.RankThree.PartTwo.Sec12.KS128BCensus

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KS129ThreeLocalFix : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r : TauCeti.PrimePower) (δ : ℕ), IsG2D4 X r δ →
    4 ≤ r.card → r.p ≠ 3 → (δ = 3 → r.p = 2) →
    (∀ z : X, orderOf z = 3 → IsThreeA z r.card ∨ IsThreeB z (r.card ^ δ)) ∧
    (∀ z : X, IsThreeA z r.card → ∀ t : X, IsThreeB t (r.card ^ δ) →
      z ∈ resCent (⊤ : Subgroup X) t → t ∈ resCent (⊤ : Subgroup X) z) ∧
    (∀ z : X, IsThreeA z r.card → ∀ t ∈ resCent (⊤ : Subgroup X) z, t ^ 3 = 1 →
      t ∉ Subgroup.zpowers z → IsThreeB t (r.card ^ δ)) ∧
    (∀ t : X, IsThreeB t (r.card ^ δ) →
      (∀ g ∈ resCent (⊤ : Subgroup X) t, orderOf g = 3 → IsThreeA g r.card) ∧
        ∀ z : X, IsThreeA z r.card → t ∈ resCent (⊤ : Subgroup X) z →
          z ∈ resCent (⊤ : Subgroup X) t)

theorem exists_sl2_quotient_of_fix (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus)
    (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G) (cfg : Cfg129 G A c L b a K S) (q : TauCeti.PrimePower)
    (hq : GTwoType129At L K q)
    (x : G) (hxD : x ∈ D129 a b) (hxb : x ∉ Subgroup.zpowers b) :
    c ∈ resCent K x ∧ S ≤ resCent K x ∧
      ∃ δ : ℕ, IsG2D4 (K ⧸ CFSG.pCore 2 K) q δ ∧ (δ = 1 ∨ δ = 3) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q.card ^ δ ∧
          ∃ φ : ↥(resCent K x) →* Matrix.SpecialLinearGroup (Fin 2) F,
            Function.Surjective φ ∧ φ.ker ≤ aschbacherSolvableCore 3 ↥(resCent K x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hq4, hq3D, hq3A⟩ := hCen.2 G A c L b a K S cfg q hq
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hcA : c ∈ A := hstd.mem_A
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hc1 : c ≠ 1 := hstd.ne_one
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  have hAL : A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    BCensus.inf_le_residual hstd hbA hbB
  have haI := hAL ⟨haA, haL⟩
  have hcI := hAL ⟨hcA, hstd.mem_L⟩
  have haK : a ∈ K := cfg.hIK haI
  have hcK : c ∈ K := cfg.hIK hcI
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt
  have hxa : K ⊓ Subgroup.centralizer ({x} : Set G) = K ⊓ Subgroup.centralizer ({a} : Set G) :=
    inf_centralizer_eq_of_mem_D hAe haA hbA hKb hxD hxb
  have hresx : resCent K x = resCent K a := by
    unfold resCent
    rw [hxa]
  suffices h : c ∈ resCent K a ∧ S ≤ resCent K a ∧
      ∃ δ : ℕ, IsG2D4 (K ⧸ CFSG.pCore 2 K) q δ ∧ (δ = 1 ∨ δ = 3) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q.card ^ δ ∧
          ∃ φ : ↥(resCent K a) →* Matrix.SpecialLinearGroup (Fin 2) F,
            Function.Surjective φ ∧ φ.ker ≤ aschbacherSolvableCore 3 ↥(resCent K a) by
    rw [hresx]
    exact h
  set N : Subgroup K := CFSG.pCore 2 K with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_pCore_two K
  set at' : K := ⟨a, haK⟩ with hat
  set ct : K := ⟨c, hcK⟩ with hct
  have hat3 : at' ^ 3 = 1 := Subtype.ext ha3
  have hct3 : ct ^ 3 = 1 := Subtype.ext hc3
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hq3 : q.p ≠ 3 := by
    obtain ⟨F, _, _, h⟩ := hq.1
    have hmod : q.card % 3 = 1 ∨ q.card % 3 = 2 := by
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    intro hp3
    have : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hp3]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    omega
  obtain ⟨δ, hδ13, hG2D4, hδ3⟩ :
      ∃ δ : ℕ, (δ = 1 ∨ δ = 3) ∧ IsG2D4 (K ⧸ N) q δ ∧ (δ = 3 → q.p = 2) := by
    rcases hq.2 with h | ⟨hq', h⟩
    · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, h⟩, fun h => absurd h (by norm_num)⟩
    · exact ⟨3, Or.inr rfl, Or.inr ⟨rfl, hq', h⟩, fun _ => hq3D ⟨hq', h⟩⟩
  obtain ⟨-, -, hcl, hd⟩ := hTL (K ⧸ N) q δ hG2D4 hq4 hq3 hδ3
  have hct3A : IsThreeA (π ct) q.card := hq3A hcK
  have haRes : a ∈ resCent K c := by
    have hle : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
        resCent K c := by
      apply le_inSubgroup_perfectResidual_of_isPerfect
      · exact le_inf cfg.hIK (((Subgroup.map_subtype_le _ :
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ _)).trans
            (inf_le_left.trans hLc))
      · exact Sec6.isPerfect_inSubgroup_perfectResidual _
    exact hle haI
  have hat_mem : π at' ∈ resCent (⊤ : Subgroup (K ⧸ N)) (π ct) := by
    rw [resCent_eq_map K hcK] at haRes
    obtain ⟨y, hy, hya⟩ := haRes
    have hy' : y = at' := Subtype.ext hya
    rw [← map_resCent_quot N hN3 hct3]
    exact ⟨y, hy, by rw [hy']⟩
  have hat_ne : π at' ∉ Subgroup.zpowers (π ct) := by
    intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    have hcomm : ct * at' = at' * ct := Subtype.ext (hAc c hcA a haA)
    have h1 : (ct ^ m)⁻¹ * at' ∈ N := by
      have : π (ct ^ m) = π at' := by rw [map_zpow]; exact hm
      exact QuotientGroup.eq.mp this
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one (Y := K) h1
    have hz3 : ((ct ^ m)⁻¹ * at') ^ 3 = 1 := by
      have hc' : Commute (ct ^ m)⁻¹ at' := ((Commute.zpow_left hcomm m).inv_left)
      rw [hc'.mul_pow, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hct3, one_zpow, inv_one, one_mul]
      exact hat3
    have hz := eq_one_of_pow_three_of_pow_two_pow hz3 hk
    have : at' = ct ^ m := by
      have := mul_eq_one_iff_eq_inv.mp hz
      simpa using this.symm
    apply cfg.ha_not
    have h2 := congrArg Subtype.val this
    rw [Subgroup.coe_zpow] at h2
    exact ⟨m, h2.symm⟩
  have hat3B : IsThreeB (π at') (q.card ^ δ) :=
    hcl (π ct) hct3A (π at') hat_mem (by rw [← map_pow, hat3, map_one]) hat_ne
  have hct_in : π ct ∈ resCent (⊤ : Subgroup (K ⧸ N)) (π at') :=
    (hd (π at') hat3B).2 (π ct) hct3A hat_mem
  set T : Subgroup K := Subgroup.centralizer ({at'} : Set K) with hT
  have hctT : ct ∈ T :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hAc c hcA a haA))
  set P : Subgroup T := perfectResidual T with hP
  haveI : P.Characteristic := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  haveI : P.Normal := inferInstance
  have hct_X : ct ∈ inSubgroup perfectResidual T := by
    rw [← map_resCent_quot N hN3 hat3] at hct_in
    obtain ⟨y, hy, hyc⟩ := hct_in
    obtain ⟨p, hpP, hpy⟩ := hy
    let cT : T := ⟨ct, hctT⟩
    let nT : T := cT * p⁻¹
    have hnN : (nT : K) ∈ N := by
      have h1 : π ((nT : K)) = 1 := by
        change π (ct * (p : K)⁻¹) = 1
        rw [map_mul, map_inv]
        have : π (p : K) = π ct := by
          rw [show (p : K) = y from hpy]
          exact hyc
        rw [this, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one (Y := K) hnN
    have hnk : nT ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hc3T : cT ^ 3 = 1 := Subtype.ext (by simpa using hct3)
    have hcT : cT = nT * p := by
      change cT = cT * p⁻¹ * p
      group
    have := Hering129HLift.mem_of_mul_mem_of_pow_three P hpP hcT hc3T ⟨k, hnk⟩
    exact ⟨cT, this, rfl⟩
  have hcX : c ∈ resCent K a := by
    rw [resCent_eq_map K haK]
    exact ⟨ct, hct_X, rfl⟩
  have hSX : S ≤ resCent K a := by
    have hnorm : ∀ s ∈ K ⊓ Subgroup.centralizer ({a} : Set G),
        s ∈ Subgroup.normalizer (resCent K a : Set G) := fun s hs =>
      CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
        (K ⊓ Subgroup.centralizer ({a} : Set G)) (Subgroup.le_normalizer hs)
    calc S = ⁅S, Subgroup.zpowers c⁆ := cfg.hS_comm.symm
      _ ≤ resCent K a := by
        apply Subgroup.commutator_le.mpr
        intro s hs g hg
        have hsK : s ∈ K := cfg.hS_le hs
        have hsa : s ∈ Subgroup.centralizer ({a} : Set G) :=
          Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD) (cfg.hS_cent hs)
        have hgX : g ∈ resCent K a := (Subgroup.zpowers_le.mpr hcX) hg
        have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm s ⟨hsK, hsa⟩) g).mp hgX
        exact (resCent K a).mul_mem h1 ((resCent K a).inv_mem hgX)
  refine ⟨hcX, hSX, δ, hG2D4, hδ13, ?_⟩
  obtain ⟨-, F, hFf, hFfin, hFcard, ⟨e⟩⟩ := hat3B
  have hle : resCent K a ≤ K := (resCent_le K a).trans inf_le_left
  let φ0 : ↥(resCent K a) →* K ⧸ N := π.comp (Subgroup.inclusion hle)
  have hφ0mem : ∀ y : ↥(resCent K a), φ0 y ∈ resCent (⊤ : Subgroup (K ⧸ N)) (π at') := by
    intro y
    have hy := (SetLike.ext_iff.mp (resCent_eq_map K haK) (y : G)).mp y.2
    obtain ⟨y', hy', hyy⟩ := hy
    rw [← map_resCent_quot N hN3 hat3]
    refine ⟨y', hy', ?_⟩
    change π y' = π (Subgroup.inclusion hle y)
    congr 1
    exact Subtype.ext hyy
  let φ1 : ↥(resCent K a) →* ↥(resCent (⊤ : Subgroup (K ⧸ N)) (π at')) :=
    φ0.codRestrict _ hφ0mem
  have hφ1 : Function.Surjective φ1 := by
    rintro ⟨w, hw⟩
    rw [← map_resCent_quot N hN3 hat3] at hw
    obtain ⟨y', hy', rfl⟩ := hw
    have : (y' : G) ∈ resCent K a :=
      (SetLike.ext_iff.mp (resCent_eq_map K haK) _).mpr ⟨y', hy', rfl⟩
    exact ⟨⟨y', this⟩, Subtype.ext rfl⟩
  let φ : ↥(resCent K a) →* Matrix.SpecialLinearGroup (Fin 2) F := e.toMonoidHom.comp φ1
  have hφ : Function.Surjective φ := e.surjective.comp hφ1
  have hkerθ : φ.ker ≤ aschbacherSolvableCore 3 ↥(resCent K a) := by
    obtain ⟨-, -, -, -, -, -, hpc⟩ :=
      solvable_prime_complement_core_characterization (H := ↥(resCent K a)) Nat.prime_three
    refine le_trans ?_ (hpc 2 Nat.prime_two (by norm_num))
    have hker : ∀ y : ↥(resCent K a), φ y = 1 → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
      intro y hy
      have h1 : φ1 y = 1 := by
        have : e (φ1 y) = 1 := hy
        exact (MulEquiv.map_eq_one_iff e).mp this
      have h2 : π (Subgroup.inclusion hle y) = 1 := by
        have := congrArg Subtype.val h1
        exact this
      have h3 : Subgroup.inclusion hle y ∈ N := (QuotientGroup.eq_one_iff _).mp h2
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one (Y := K) h3
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    refine le_sSup ⟨inferInstance, ?_⟩
    refine IsPGroup.iff_orderOf.mpr fun r => ?_
    obtain ⟨k, hk⟩ := hker r.1 r.2
    have hdvd : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  exact ⟨F, hFf, hFfin, hFcard, φ, hφ, hkerθ⟩

theorem gap129KFKStrong_of_fix (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus) :
    Gap129KFKStrong := by
  intro G _ _ A c L b a K S cfg hty x hxD hxb
  obtain ⟨q, hq⟩ := hty
  obtain ⟨hcX, hSX, δ, -, hδ, F, hFf, hFfin, hFcard, φ, hφ, hker⟩ :=
    exists_sl2_quotient_of_fix hTL hCen G A c L b a K S cfg q hq x hxD hxb
  obtain ⟨hq4, -, -⟩ := hCen.2 G A c L b a K S cfg q hq
  have hQ : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
    haveI : Finite F := Finite.of_fintype F
    have h4 : 4 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hFcard]
      exact hq4.trans (Nat.le_self_pow (by omega) _)
    exact CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour.isQuasisimple_sl2 h4
  have hQ2 : ∀ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F), z ^ 2 = 1 := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow]
    have hr2 : r ^ 2 = 1 := by simpa using hr
    rw [hr2, map_one]
    rfl
  exact ⟨hcX, hSX, Hering129HLift.isQuasisimple_quot_theta (isPerfect_resCent K x) φ hφ hQ hker,
    Hering129HLift.center_sq_quot_theta φ hφ hQ hker hQ2⟩

theorem gap129KFK_of_fix (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus) : Gap129KFK :=
  fun G _ _ A c L b a K S cfg hty x hxD hxb =>
    let h := gap129KFKStrong_of_fix hTL hCen G A c L b a K S cfg hty x hxD hxb
    ⟨h.1, h.2.1, h.2.2.1⟩

end CFSG.RankThree.PartTwo.Sec12
