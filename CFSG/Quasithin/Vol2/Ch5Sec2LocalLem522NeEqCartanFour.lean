module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113C2
public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

section General

variable {X : Type} [Group X] [Finite X]

theorem elemAbelian_nine_of_hom {A : Type} [CommGroup A] [Finite A] (hA9 : Nat.card A = 9)
    (hA3 : ∀ a : A, a ^ 3 = 1) {N : Subgroup X} (φ : ↥N →* A)
    (hker : ∀ x : ↥N, φ x = 1 → ∃ m : ℕ, x ^ 2 ^ m = 1) (h9 : 9 ∣ Nat.card ↥N)
    {C : Subgroup X} (hC : Lin2.IsHallTwoPrimeOf C N) :
    IsElemAbelian 3 C ∧ Nat.card ↥C = 9 := by
  obtain ⟨hCN, hCodd, k, hk⟩ := hC
  set ψ : ↥C →* A := φ.comp (Subgroup.inclusion hCN) with hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    obtain ⟨m, hm⟩ := hker _ hc
    have hm' : c ^ 2 ^ m = 1 := by
      apply Subgroup.inclusion_injective hCN
      rw [map_pow, hm, map_one]
    have hcop : Nat.Coprime (2 ^ m) (Nat.card ↥C) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hCodd)
    have h1 : orderOf c ∣ Nat.gcd (2 ^ m) (Nat.card ↥C) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_natCard c)
    rw [hcop] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hdvd : Nat.card ↥C ∣ 9 := by
    rw [← hA9]
    exact Subgroup.card_dvd_of_injective ψ hinj
  have hdvd' : 9 ∣ Nat.card ↥C := by
    have h1 := C5.card_eq_card_mul_relIndex hCN
    rw [hk] at h1
    rw [h1] at h9
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ (by norm_num)) h9
  refine ⟨⟨⟨⟨fun a b => hinj (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun c hc => ?_⟩,
    Nat.dvd_antisymm hdvd hdvd'⟩
  have h1 : ψ ((⟨c, hc⟩ : ↥C) ^ 3) = 1 := by rw [map_pow, hA3]
  have h2 : (⟨c, hc⟩ : ↥C) ^ 3 = 1 := hinj (h1.trans (map_one ψ).symm)
  exact congrArg Subtype.val h2

theorem elemAbelian_nine_of_model {Y : Type} [Group Y] [Finite Y] {A : Type} [CommGroup A]
    [Finite A] (hA9 : Nat.card A = 9) (hA3 : ∀ a : A, a ^ 3 = 1) {U₀ : Subgroup Y}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (φ : ↥(Subgroup.normalizer (U₀ : Set Y)) →* A)
    (hker : ∀ x, φ x = 1 → ∃ m : ℕ, x ^ 2 ^ m = 1)
    (h9 : 9 ∣ Nat.card ↥(Subgroup.normalizer (U₀ : Set Y))) (e : X ≃* Y) {U C : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) :
    IsElemAbelian 3 C ∧ Nat.card ↥C = 9 := by
  have hU₁ : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    have h1 := hU.2.2
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at h1
    rwa [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  obtain ⟨g, hg⟩ := NQCat.exists_conj_map_eq hU₁ hU₀
  set f : X ≃* Y := e.trans (MulAut.conj g) with hf
  have hUf : U.map f.toMonoidHom = U₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hN : (Subgroup.normalizer (U : Set X)).map f.toMonoidHom =
      Subgroup.normalizer (U₀ : Set Y) := by
    rw [Subgroup.map_equiv_normalizer_eq, hUf]
  let ψ : ↥(Subgroup.normalizer (U : Set X)) ≃* ↥(Subgroup.normalizer (U₀ : Set Y)) :=
    (f.subgroupMap _).trans (MulEquiv.subgroupCongr hN)
  refine elemAbelian_nine_of_hom hA9 hA3 (φ.comp ψ.toMonoidHom) (fun x hx => ?_) ?_ hC
  · obtain ⟨m, hm⟩ := hker (ψ x) hx
    exact ⟨m, ψ.injective (by rw [map_pow, hm, map_one])⟩
  · rw [Nat.card_congr ψ.toEquiv]
    exact h9

end General

section SL3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem dHom_mem_upperTriangular (p : Fˣ × Fˣ) :
    LinearThreeFourFixedNine.dHom p ∈ upperTriangular 3 F := by
  intro i j hij
  rw [LinearThreeFourFixedNine.coe_dHom, diagonal_apply_ne _ (ne_of_gt hij)]

omit [Finite F] [CharP F 2] in
theorem dHom_injective : Function.Injective (LinearThreeFourFixedNine.dHom (k := F)) := by
  intro p q h
  have h0 := congrArg
    (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  have h1 := congrArg
    (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp only [LinearThreeFourFixedNine.coe_dHom, diagonal_apply_eq] at h0 h1
  exact Prod.ext (Units.ext (by simpa using h0)) (Units.ext (by simpa using h1))

theorem elemAbelian_nine_sl3 (hF : Nat.card F = 4) {X : Type} [Group X] [Finite X]
    (e : X ≃* SpecialLinearGroup (Fin 3) F) {U C : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) :
    IsElemAbelian 3 C ∧ Nat.card ↥C = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hu3 : ∀ u : Fˣ, u ^ 3 = 1 := fun u => by
    rw [← hu]
    exact pow_card_eq_one'
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (unitriangular 3 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hU2 : IsPGroup 2 ↥(unitriangular 3 F) := hU₀.2.1
  have hN : Subgroup.normalizer ((unitriangular 3 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) = upperTriangular 3 F := normalizer_unitriangular
  refine elemAbelian_nine_of_model (A := Fˣ × Fˣ) ?_
    (fun a => Prod.ext ((Prod.pow_fst a 3).trans (hu3 a.1)) ((Prod.pow_snd a 3).trans (hu3 a.2)))
    hU₀ (diagTwo.comp (MulEquiv.subgroupCongr hN).toMonoidHom) (fun x hx => ?_) ?_ e hU hC
  · rw [Nat.card_prod, hu]
  · have hxU := mem_unitriangular_of_diagTwo_eq_one (A := MulEquiv.subgroupCongr hN x) hx
    obtain ⟨m, hm⟩ := hU2 ⟨_, hxU⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hm
    simpa using h1
  · rw [hN]
    have h1 : Nat.card ↥(LinearThreeFourFixedNine.dHom (k := F)).range = 9 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective dHom_injective).toEquiv, Nat.card_prod, hu]
    rw [← h1]
    exact Subgroup.card_dvd_of_le (by
      rintro _ ⟨p, rfl⟩
      exact dHom_mem_upperTriangular p)

end SL3

section Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem elemAbelian_nine_sp4 (hK : Nat.card K = 4) {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))
    {U C : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) :
    IsElemAbelian 3 C ∧ Nat.card ↥C = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hu3 : ∀ u : Kˣ, u ^ 3 = 1 := fun u => by
    rw [← hu]
    exact pow_card_eq_one'
  let π : CFSG.Assembly.LowTwoRank.StatedSp 2 K ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 2 K)
      ⟨Vol2Native.A312L.proj_injective_charTwo, QuotientGroup.mk'_surjective _⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  have hU₀ : IsSylowTwoOf (SymplecticFlag.unipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hU2 : IsPGroup 2 ↥(SymplecticFlag.unipotent 2 K) := hU₀.2.1
  have hN := SymplecticHigher.normalizer_unipotent (r := 2) (K := K)
  refine elemAbelian_nine_of_model (A := Fin 2 → Kˣ) ?_ (fun a => funext fun i => by
      rw [Pi.pow_apply, hu3, Pi.one_apply])
    hU₀ ((SymplecticFlag.diagHom 2 K).comp (MulEquiv.subgroupCongr hN).toMonoidHom)
    (fun x hx => ?_) ?_ (e.trans π.symm) hU hC
  · rw [Nat.card_fun, hu, Nat.card_fin]
    norm_num
  · have hx' : MulEquiv.subgroupCongr hN x ∈ (SymplecticFlag.diagHom 2 K).ker := hx
    rw [SymplecticFlag.ker_diagHom, Subgroup.mem_subgroupOf] at hx'
    obtain ⟨m, hm⟩ := hU2 ⟨_, hx'⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hm
    simpa using h1
  · rw [hN, SymplecticFlag.card_borelSubgroup, hK]
    norm_num

end Sp4

theorem factRank2CartanFour_holds :
    ∀ (X : Type) [Group X] [Finite X], (IsSL3Ch5 2 X ∨ LieModel X .PSp 2 2 2) →
      ¬ LieModel X .PSL 3 2 2 → ∀ U C : Subgroup X, IsSylowTwoOf U ⊤ →
        Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X)) →
          IsElemAbelian 3 C ∧ Nat.card ↥C = 9 := by
  intro X _ _ htype hnot U C hU hC
  rcases htype with (hL | ⟨F, _, _, hcard, ⟨e⟩⟩) | hSp
  · exact absurd hL hnot
  · have : CharP F 2 :=
      finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    exact elemAbelian_nine_sl3 (by rw [hcard]; norm_num) e hU hC
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hSp
    have : CharP K 2 :=
      finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    exact elemAbelian_nine_sp4 (by rw [hcard]; norm_num) e hU hC

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_modO2Image {K B : Subgroup G} (hBK : B ≤ K) (hB : Odd (Nat.card ↥B))
    {p : ℕ} (h : IsElemAbelian p (modO2Image K B)) : IsElemAbelian p B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := barMap hBK with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, hm⟩ := isPGroup_ker_barMap hBK ⟨x, MonoidHom.mem_ker.mpr hx⟩
    have hm' : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hcop : Nat.Coprime (2 ^ m) (Nat.card ↥B) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hB)
    have h1 : orderOf x ∣ Nat.gcd (2 ^ m) (Nat.card ↥B) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_natCard x)
    rw [hcop] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  obtain ⟨hcomm, hpow⟩ := h
  refine ⟨⟨⟨fun a b => hinj ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hcomm.is_comm.comm _ _
  · have h1 : f ((⟨x, hx⟩ : ↥B) ^ p) = 1 := by
      rw [map_pow]
      exact Subtype.ext (hpow _ (f ⟨x, hx⟩).2)
    exact congrArg Subtype.val (hinj (h1.trans (map_one f).symm))

theorem isHallTwoPrimeOf_inf_borelOf {T K L₀ B : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B (K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)))
    (hL₀K : L₀ ≤ K)
    (hYN : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L₀ : Set G))
    (hYi : borelOf L₀ T ≤ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    Lin2.IsHallTwoPrimeOf (B ⊓ L₀) (borelOf L₀ T) := by
  have h2 : (K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) ⊓ L₀ = borelOf L₀ T :=
    le_antisymm (inf_le_borelOf hL₀K) (le_inf hYi inf_le_left)
  have hYN' : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((borelOf L₀ T : Subgroup G) : Set G) := by
    intro y hy
    have h1 : y ∈ Subgroup.normalizer
        (((K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) ⊓ L₀ : Subgroup G) :
          Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hYN hy⟩
    rwa [h2] at h1
  have h := isHallTwoPrimeOf_inf_of_le_normalizer hB hYi hYN'
  have h3 : B ⊓ borelOf L₀ T = B ⊓ L₀ := by
    refine le_antisymm (inf_le_inf_left B inf_le_left) fun x hx => ⟨hx.1, ?_⟩
    rw [← h2]
    exact ⟨hB.1 hx.1, hx.2⟩
  rwa [h3] at h

end Transfer

theorem stmt5_2_2_eq_cartan_rank2_of (h510 : Stmt5_1_10) (hF : FactL2LieParabolic)
    (hL2 : Stmt5_2_L2) : Stmt5_2_2_eq_cartan_rank2 := by
  have hC4 := factRank2CartanFour_holds
  intro G _ _ T M L V H B D L₂ Dp n p hyp hL₂K hL4 hKC hnb P hP hL₂P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, -, hMK⟩ :=
    nonBender_type h510 hyp.toHyp5_1_8 hyp.notation59 hKC hnb rfl
  obtain ⟨hL₂eq, hpsl, hborel, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  have hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂ :=
    (hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice).1
  obtain ⟨D₀, hD₀, -, -⟩ := F1.exists_cartan hSL₂
  have h1 := (isCyclic_card_of_isHall_borelOf hk (Or.inl ⟨by simp [classicalTags], hpsl⟩) hSL₂
    hD₀).2
  have h2 := (isCyclic_card_of_isHall_borelOf le_rfl hL4 hSL₂ hD₀).2
  have hk2 : k = 2 := by
    have h3 : 2 ^ k - 1 = 3 := h1.symm.trans (h2.trans (by norm_num))
    have h4 := Nat.one_le_two_pow (n := k)
    generalize hq : 2 ^ k = q at h3 h4
    have h5 : 2 ^ k = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h5
  subst hk2
  obtain ⟨-, -, -, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  rw [hMK] at hBH
  have hOT : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hBK : B ≤ oTwoUpper H := hBH.1.trans inf_le_left
  have hBodd : Odd (Nat.card ↥B) := hBH.2.1
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image (oTwoUpper H) B)
      (Subgroup.normalizer ((modO2Image (oTwoUpper H) (T ⊓ oTwoUpper H) :
        Subgroup (O2Q (oTwoUpper H))) : Set (O2Q (oTwoUpper H)))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := oTwoUpper H) inf_le_left hBH
    rwa [modO2Image_inf_normalizer le_rfl inf_le_right (fun x hx => hOT hx.2),
      Vol2.Ch11.SecS.modO2Image_self, top_inf_eq] at h1
  obtain ⟨hEA, hcard⟩ := hC4 (O2Q (oTwoUpper H)) htype hyp.notL34 _ _
    (Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK) hBb
  have hL₂K' : L₂ ≤ oTwoUpper H := hL₂eq ▸ (perfectCore_le P).trans hP.1
  have hYN : oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L₂ : Set G) := by
    rw [hL₂eq]
    exact hP.2.1.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))
  have hYi : borelOf L₂ T ≤
      oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hMK]
    exact le_inf hborel (inf_le_left.trans hL₂K')
  refine ⟨isElemAbelian_of_modO2Image hBK hBodd hEA,
    (Vol2.Ch11.SecS.card_modO2Image_of_odd hBK hBodd).symm.trans hcard,
    isHallTwoPrimeOf_inf_borelOf hBH hL₂K' hYN hYi⟩

end CFSG.Quasithin.H13
