module

public import CFSG.Quasithin.H13.QRCPairLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Quasithin.H13.QRCBenderModels

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup

section Setup

variable {H : Type} [Group H] [Finite H]

theorem bender_section_setup (hns : ¬ Group.IsSolvable H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} (hVT : V ≤ T) (hVM : V ≤ inSubgroup (pCore 2) M) :
    pCore 2 H ≤ kerIn M ⊤ ∧ Odd ((pCore 2 H).relIndex (kerIn M ⊤)) ∧
    kerIn M ⊤ ≤ oddResidualPreimage H ∧
    ((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))).Normal ∧
    (∀ a : H ⧸ kerIn M ⊤,
      (∀ k ∈ (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)), a * k = k * a) →
        a = 1) ∧
    (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
      (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) = ⊤ ∧
    ((T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤ M.map (QuotientGroup.mk' (kerIn M ⊤)) ∧
      M.map (QuotientGroup.mk' (kerIn M ⊤)) < ⊤ ∧
      ∀ Y : Subgroup (H ⧸ kerIn M ⊤), (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ≤ Y →
        Y < ⊤ → Y ≤ M.map (QuotientGroup.mk' (kerIn M ⊤))) ∧
    V ⊓ kerIn M ⊤ = V ⊓ pCore 2 H ∧
    Nat.card ↥(V.map (QuotientGroup.mk' (kerIn M ⊤))) = (V ⊓ pCore 2 H).relIndex V ∧
    V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤
      inSubgroup (pCore 2) (M.map (QuotientGroup.mk' (kerIn M ⊤))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (T : Subgroup H) ⊤ := ⟨le_top, T.isPGroup', by
    show ¬ 2 ∣ (T : Subgroup H).relIndex ⊤
    rw [relIndex_top_right]
    exact T.not_dvd_index⟩
  obtain ⟨⟨hRJ, hJK⟩, ⟨-, hodd, -⟩, hHKT, ⟨hKn₀, -⟩, hcomp, hsimp⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hTsyl hTn hTM hMH hmax
  set Q := pCore 2 H with hQdef
  set J := kerIn M ⊤ with hJdef
  set π := QuotientGroup.mk' J with hπdef
  set K₀ := oddResidualPreimage H with hK₀def
  set K := K₀.map π with hKdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hπker : π.ker = J := QuotientGroup.ker_mk' J
  have hQR : Q = CFSG.Open.pCore 2 H := CFSG.pCore_eq_open H 2
  have hQJ : Q ≤ J := hQR ▸ hRJ
  have hDQ : Q.relIndex J = Nat.card (J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) := by
    rw [hQR]
    exact (card_map_mk'_eq_relIndex _ _).symm
  have hKn : K.Normal := hKn₀.map π hπs
  have hmin : ∀ N : Subgroup (H ⧸ J), N.Normal → N ≠ ⊥ → K ≤ N := by
    intro N hN hN1
    have hN' : (N.comap π).Normal := hN.comap π
    have hRN : CFSG.Open.pCore 2 H ≤ N.comap π := fun x hx => by
      have h : x ∈ π.ker := by
        rw [hπker]
        exact hRJ hx
      rw [mem_comap, MonoidHom.mem_ker.1 h]
      exact one_mem N
    have hNJ : ¬ N.comap π ≤ J := by
      intro hle
      apply hN1
      rw [← map_comap_eq_self_of_surjective hπs N, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_bot, ← MonoidHom.mem_ker, hπker]
      exact hle hx
    rw [← map_comap_eq_self_of_surjective hπs N]
    exact map_mono (hcomp _ hN' hRN hNJ)
  have hKnab : ¬ ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    obtain ⟨L, -, hLnc, hLK, -⟩ := hsimp hns
    intro hc
    apply hLnc
    exact ⟨⟨fun a b => Subtype.ext (hc _ (hLK a.2) _ (hLK b.2))⟩⟩
  have hCK : ∀ a : H ⧸ J, (∀ k ∈ K, a * k = k * a) → a = 1 := by
    intro a ha
    by_contra ha1
    set C := centralizer (K : Set (H ⧸ J)) with hCdef
    have hCn : C.Normal := ⟨fun c hc g k hk => by
      have hk' : g⁻¹ * k * g ∈ K := by
        have h1 := hKn.conj_mem k hk g⁻¹
        rwa [inv_inv] at h1
      have h1 := mem_centralizer_iff.1 hc _ hk'
      calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * k := by group⟩
    have haC : a ∈ C := mem_centralizer_iff.2 fun k hk => (ha k hk).symm
    have hne : C ≠ ⊥ := fun h => ha1 (by rw [h] at haC; exact haC)
    have hKC := hmin C hCn hne
    exact hKnab fun x hx y hy => mem_centralizer_iff.1 (hKC hy) x hx
  have hKS : K ⊔ (T : Subgroup H).map π = ⊤ := by
    rw [hKdef, ← Subgroup.map_sup, hHKT, Subgroup.map_top_of_surjective π hπs]
  have hJM : J ≤ M := kerIn_le
  have hcomapB : (M.map π).comap π = M := by
    rw [comap_map_eq, hπker, sup_eq_left.2 hJM]
  have hBtop : M.map π < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hMH.ne ?_
    rw [← hcomapB, h, comap_top]
  have hBmax : ∀ Y : Subgroup (H ⧸ J), (T : Subgroup H).map π ≤ Y → Y < ⊤ → Y ≤ M.map π := by
    intro Y hTY hY
    have h1 : (T : Subgroup H) ≤ Y.comap π := map_le_iff_le_comap.1 hTY
    have h2 : Y.comap π < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hY.ne ?_
      rw [← map_comap_eq_self_of_surjective hπs Y, h, map_top_of_surjective π hπs]
    rw [← map_comap_eq_self_of_surjective hπs Y]
    exact map_mono (hmax _ h1 h2)
  have hVDQ : V ⊓ J = V ⊓ Q := by
    refine le_antisymm (fun v hv => ?_) (inf_le_inf_left V hQJ)
    obtain ⟨hvV, hvJ⟩ := mem_inf.1 hv
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨v, hVT hvV⟩
    have hvn : v ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 H) v = 1 :=
      eq_one_of_mem_odd (Y := J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) hodd
        (mem_map_of_mem _ hvJ) (k := n) (by rw [← map_pow, hvn, map_one])
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_inf.2 ⟨hvV, hQR ▸ h1⟩
  have hEcard : Nat.card ↥(V.map π) = (V ⊓ Q).relIndex V := by
    rw [card_map_mk'_eq_relIndex, ← hVDQ, inf_comm, inf_relIndex_right]
  have hMO : M ≤ normalizer (inSubgroup (pCore 2) M : Set H) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic M (pCore 2 M))
  have hEO : V.map π ≤ inSubgroup (pCore 2) (M.map π) := by
    refine (map_mono hVM).trans (le_inSubgroup_pCore (map_mono (map_subtype_le _)) ?_ ?_)
    · refine le_normalizer_of_forall_conj_mem ?_
      rintro _ ⟨m, hm, rfl⟩ _ ⟨o, ho, rfl⟩
      refine ⟨m * o * m⁻¹, (mem_normalizer_iff.mp (hMO hm) o).mp ho, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · exact ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).map π
  have hJK0 : J ≤ K₀ := hJK.le
  refine ⟨hQJ, ?_, hJK0, hKn, hCK, hKS, ⟨map_mono hTM, hBtop, hBmax⟩, hVDQ, hEcard, hEO⟩
  rw [hDQ]
  exact hodd

end Setup

section Semilinear

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {k : Type} [Field k]

theorem sl2_map_upperUnipotent (σ : RingAut k) (x : k) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (sl2UpperUnipotent x) =
      sl2UpperUnipotent (σ x) := by
  ext i j
  change σ ((!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) k) i j) =
    (!![1, σ x; 0, 1] : Matrix (Fin 2) (Fin 2) k) i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_splitTorusSLHom (a : kˣ) :
    ((splitTorusSLHom k a : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![(a : k), 0; 0, (a : k)⁻¹] :=
  rfl

theorem sl2_map_splitTorus (σ : RingAut k) (a : kˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (splitTorusSLHom k a) =
      splitTorusSLHom k (Units.map σ.toRingHom.toMonoidHom a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem sl2_map_mem_upperUnipotent (σ : RingAut k) {g : SL(2, k)}
    (hg : g ∈ sl2UpperUnipotentSubgroup k) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ sl2UpperUnipotentSubgroup k := by
  obtain ⟨x, rfl⟩ := hg
  exact ⟨Multiplicative.ofAdd (σ x.toAdd), (sl2_map_upperUnipotent σ x.toAdd).symm⟩

theorem splitTorusSLHom_injective : Function.Injective (splitTorusSLHom k) := by
  intro a b h
  have h1 := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [coe_splitTorusSLHom] at h1
  exact Units.ext (by simpa using h1)

theorem commutator_mem_of_sup_abelian {G : Type*} [Group G] {U T : Subgroup G}
    (hTN : T ≤ normalizer (U : Set G)) (hT : ∀ t ∈ T, ∀ s ∈ T, t * s = s * t)
    {b c : G} (hb : b ∈ U ⊔ T) (hc : c ∈ U ⊔ T) : b * c * b⁻¹ * c⁻¹ ∈ U := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left U T hTN] at hb hc
  obtain ⟨u, hu, t, ht, rfl⟩ := hb
  obtain ⟨v, hv, s, hs, rfl⟩ := hc
  have hts : t * s * t⁻¹ * s⁻¹ = 1 := by rw [hT t ht s hs]; group
  have h1 : u * t * (v * s) * (u * t)⁻¹ * (v * s)⁻¹ =
      u * (t * v * t⁻¹) * (t * s * t⁻¹ * s⁻¹) * (s * u⁻¹ * s⁻¹) * v⁻¹ := by group
  rw [h1, hts, mul_one]
  refine U.mul_mem (U.mul_mem (U.mul_mem hu ((mem_normalizer_iff.1 (hTN ht) v).1 hv)) ?_)
    (U.inv_mem hv)
  have h2 := (mem_normalizer_iff.1 (hTN hs) u⁻¹).1 (U.inv_mem hu)
  exact h2

variable [CharP k 2]

theorem sl2EquivPSL2_upperUnipotent :
    (sl2UpperUnipotentSubgroup k).map (sl2EquivPSL2 (F := k)).toMonoidHom =
      psl2UpperUnipotentSubgroup k := by
  rw [psl2UpperUnipotentSubgroup, psl2UpperUnipotentHom, MonoidHom.range_comp]
  rfl

theorem sl2EquivPSL2_borel :
    (sl2Borel k).map (sl2EquivPSL2 (F := k)).toMonoidHom = psl2Borel k := by
  rw [psl2Borel_eq_map]
  rfl

theorem sl2EquivPSL2_torus :
    (splitTorusSLHom k).range.map (sl2EquivPSL2 (F := k)).toMonoidHom = LinearModel.torus k := by
  rw [LinearModel.torus, LinearModel.torusHom, MonoidHom.range_comp]
  rfl

theorem sl2_normalizer_upperUnipotent :
    normalizer (sl2UpperUnipotentSubgroup k : Set SL(2, k)) = sl2Borel k := by
  apply map_injective (f := (sl2EquivPSL2 (F := k)).toMonoidHom) sl2EquivPSL2.injective
  rw [map_equiv_normalizer_eq, sl2EquivPSL2_upperUnipotent, sl2EquivPSL2_borel,
    psl2_normalizer_rootGroup]

theorem sl2_upperUnipotent_inf_torus :
    sl2UpperUnipotentSubgroup k ⊓ (splitTorusSLHom k).range = ⊥ := by
  apply map_injective (f := (sl2EquivPSL2 (F := k)).toMonoidHom) sl2EquivPSL2.injective
  rw [map_inf_eq _ _ (sl2EquivPSL2 (F := k)).toMonoidHom sl2EquivPSL2.injective,
    sl2EquivPSL2_upperUnipotent, sl2EquivPSL2_torus,
    LinearModel.rootGroup_inf_torus, Subgroup.map_bot]

theorem sl2_upperUnipotent_sup_torus :
    sl2UpperUnipotentSubgroup k ⊔ (splitTorusSLHom k).range = sl2Borel k := by
  apply map_injective (f := (sl2EquivPSL2 (F := k)).toMonoidHom) sl2EquivPSL2.injective
  rw [Subgroup.map_sup, sl2EquivPSL2_upperUnipotent, sl2EquivPSL2_torus,
    LinearModel.rootGroup_sup_torus, sl2EquivPSL2_borel]

variable [Finite k]

theorem benderData_sl2 {n : ℕ} (hcard : Nat.card k = 2 ^ n) :
    BenderData SL(2, k) (sl2UpperUnipotentSubgroup k) n := by
  have h := (benderData_psl2 hcard).map (sl2EquivPSL2 (F := k)).symm
  have he : ((sl2UpperUnipotentSubgroup k).map (sl2EquivPSL2 (F := k)).toMonoidHom).map
      (sl2EquivPSL2 (F := k)).symm.toMonoidHom = sl2UpperUnipotentSubgroup k := by
    rw [map_map]
    convert map_id (sl2UpperUnipotentSubgroup k)
    ext g
    simp
  rw [← sl2EquivPSL2_upperUnipotent, he] at h
  exact h

end Semilinear

section FieldAction

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson
open scoped MatrixGroups

variable {A : Type*} [Group A] {K : Subgroup A} [K.Normal] {k : Type} [Field k] {n : ℕ}

noncomputable def semilinearCoord (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k)) :
    A →* Gamma k :=
  (MulEquiv.ofBijective (gammaToMulAut k)
    (gammaToMulAut_bijective_of_card hcard)).symm.toMonoidHom.comp
    ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)

theorem semilinearCoord_spec (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k)) (a : A) (g : K) :
    θ (MulAut.conjNormal a g) = (semilinearCoord hcard θ a).left *
      Matrix.SpecialLinearGroup.map (semilinearCoord hcard θ a).right.toRingHom (θ g) *
        (semilinearCoord hcard θ a).left⁻¹ := by
  set e := MulEquiv.ofBijective (gammaToMulAut k) (gammaToMulAut_bijective_of_card hcard)
  have h1 : gammaToMulAut k (semilinearCoord hcard θ a) = MulAut.congr θ (MulAut.conjNormal a) :=
    e.apply_symm_apply _
  have h2 := congrArg (fun φ : MulAut SL(2, k) => φ (θ g)) h1
  simp only [gammaToMulAut_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  exact h2.symm

theorem semilinearCoord_of_mem (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k)) (x : K) :
    semilinearCoord hcard θ (x : A) = SemidirectProduct.inl (θ x) := by
  apply (gammaToMulAut_bijective_of_card hcard).1
  have h1 : gammaToMulAut k (semilinearCoord hcard θ x) =
      MulAut.congr θ (MulAut.conjNormal (x : A)) :=
    (MulEquiv.ofBijective (gammaToMulAut k)
      (gammaToMulAut_bijective_of_card hcard)).apply_symm_apply _
  rw [h1, gammaToMulAut_inl]
  ext g : 1
  have h2 : MulAut.conjNormal (x : A) (θ.symm g) = x * θ.symm g * x⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; simp)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
  rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem semilinearCoord_injective (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k))
    (hCK : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) :
    Function.Injective (semilinearCoord hcard θ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  rw [mem_bot]
  refine hCK a fun x hx => ?_
  have h1 := semilinearCoord_spec hcard θ a ⟨x, hx⟩
  rw [ha] at h1
  have h2 : θ (MulAut.conjNormal a ⟨x, hx⟩) = θ ⟨x, hx⟩ := by
    rw [h1]
    ext i j
    simp
  have h3 := congrArg Subtype.val (θ.injective h2)
  rw [MulAut.conjNormal_apply] at h3
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [h3]

theorem mem_of_semilinearCoord_right (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k))
    (hCK : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) {r : A}
    (hr : (semilinearCoord hcard θ r).right = 1) : r ∈ K := by
  have h1 : semilinearCoord hcard θ r =
      semilinearCoord hcard θ (θ.symm (semilinearCoord hcard θ r).left : A) := by
    rw [semilinearCoord_of_mem, MulEquiv.apply_symm_apply]
    exact SemidirectProduct.ext (by simp) (by simp [hr])
  rw [semilinearCoord_injective hcard θ hCK h1]
  exact (θ.symm _).2

variable [Finite k] [CharP k 2]

omit [Finite k] in
theorem semilinearCoord_right_eq_one (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k)) {r : A}
    (hU : ∀ g : K, θ g ∈ sl2UpperUnipotentSubgroup k →
      θ (MulAut.conjNormal r g) ∈ sl2UpperUnipotentSubgroup k)
    (hU' : ∀ g : K, θ g ∈ sl2UpperUnipotentSubgroup k →
      θ (MulAut.conjNormal r⁻¹ g) ∈ sl2UpperUnipotentSubgroup k)
    (hB : ∀ g : K, θ g ∈ sl2Borel k →
      θ (MulAut.conjNormal r g * g⁻¹) ∈ sl2UpperUnipotentSubgroup k) :
    (semilinearCoord hcard θ r).right = 1 := by
  set h := (semilinearCoord hcard θ r).left with hhdef
  set σ := (semilinearCoord hcard θ r).right with hσdef
  have hspec := semilinearCoord_spec hcard θ r
  have hσσ : ∀ g : SL(2, k), Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map σ.symm.toRingHom g) = g := fun g => by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hN : h ∈ normalizer (sl2UpperUnipotentSubgroup k : Set SL(2, k)) := by
    refine mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
    · have hg₀ := sl2_map_mem_upperUnipotent σ.symm hg
      have h1 := hU (θ.symm (Matrix.SpecialLinearGroup.map σ.symm.toRingHom g))
        (by rwa [MulEquiv.apply_symm_apply])
      rwa [hspec, MulEquiv.apply_symm_apply, hσσ] at h1
    · set x := θ.symm (Matrix.SpecialLinearGroup.map σ.symm.toRingHom g)
      have h1 : θ (MulAut.conjNormal r x) ∈ sl2UpperUnipotentSubgroup k := by
        rwa [hspec, MulEquiv.apply_symm_apply, hσσ]
      have h2 := hU' _ h1
      have h3 : MulAut.conjNormal r⁻¹ (MulAut.conjNormal r x) = x := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      rw [h3, MulEquiv.apply_symm_apply] at h2
      have h4 := sl2_map_mem_upperUnipotent σ h2
      rwa [hσσ] at h4
  rw [sl2_normalizer_upperUnipotent (k := k)] at hN
  have hfix : ∀ a : kˣ, σ a = a := by
    intro a
    set t := splitTorusSLHom k a with htdef
    have htB : t ∈ sl2Borel k := by
      rw [← sl2_upperUnipotent_sup_torus (k := k)]
      exact mem_sup_right ⟨a, rfl⟩
    have h1 := hB (θ.symm t) (by rwa [MulEquiv.apply_symm_apply])
    rw [map_mul, map_inv, hspec, MulEquiv.apply_symm_apply] at h1
    have hσt : Matrix.SpecialLinearGroup.map σ.toRingHom t ∈ sl2Borel k := by
      rw [htdef, sl2_map_splitTorus, ← sl2_upperUnipotent_sup_torus (k := k)]
      exact mem_sup_right ⟨_, rfl⟩
    have h2 := commutator_mem_of_sup_abelian (U := sl2UpperUnipotentSubgroup k)
      (T := (splitTorusSLHom k).range)
      (by
        rw [sl2_normalizer_upperUnipotent (k := k), ← sl2_upperUnipotent_sup_torus (k := k)]
        exact le_sup_right)
      (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm])
      (sl2_upperUnipotent_sup_torus (k := k) ▸ hN) (sl2_upperUnipotent_sup_torus (k := k) ▸ hσt)
    have h3 := (sl2UpperUnipotentSubgroup k).mul_mem
      ((sl2UpperUnipotentSubgroup k).inv_mem h2) h1
    have h4 : (h * Matrix.SpecialLinearGroup.map σ.toRingHom t * h⁻¹ *
        (Matrix.SpecialLinearGroup.map σ.toRingHom t)⁻¹)⁻¹ *
        (h * Matrix.SpecialLinearGroup.map σ.toRingHom t * h⁻¹ * t⁻¹) =
        splitTorusSLHom k (Units.map σ.toRingHom.toMonoidHom a * a⁻¹) := by
      rw [map_mul, map_inv, ← sl2_map_splitTorus, ← htdef]
      group
    rw [h4] at h3
    have h5 : splitTorusSLHom k (Units.map σ.toRingHom.toMonoidHom a * a⁻¹) ∈
        sl2UpperUnipotentSubgroup k ⊓ (splitTorusSLHom k).range := ⟨h3, _, rfl⟩
    rw [sl2_upperUnipotent_inf_torus (k := k), mem_bot, ← map_one (splitTorusSLHom k)] at h5
    have h6 := mul_inv_eq_one.1 (splitTorusSLHom_injective h5)
    exact congrArg Units.val h6
  apply RingEquiv.ext
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero]
    rfl
  · exact hfix (Units.mk0 y hy)

end FieldAction

section Transport

variable {A : Type*} [Group A] {K : Subgroup A}

theorem kerIn_map_subtype {P L : Subgroup K} :
    kerIn (P.map K.subtype) (L.map K.subtype) = (kerIn P L).map K.subtype := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ P.map K.subtype := by simpa using hx 1 (one_mem _)
    obtain ⟨y, hy, rfl⟩ := hxP
    refine ⟨y, fun b hb => ?_, rfl⟩
    obtain ⟨z, hz, hzb⟩ := hx (b : A) ⟨b, hb, rfl⟩
    have : z = b * y * b⁻¹ := Subtype.ext (by simpa using hzb)
    rw [← this]
    exact hz
  · rintro ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨b * y * b⁻¹, hy b hb, by simp⟩

theorem inSubgroup_pCore_map_subtype (p : ℕ) (L : Subgroup K) :
    inSubgroup (pCore p) (L.map K.subtype) = (inSubgroup (pCore p) L).map K.subtype := by
  have h1 := CFSG.pCore_map_iso p (L.equivMapOfInjective K.subtype K.subtype_injective)
  rw [inSubgroup, inSubgroup, ← h1, map_map, map_map]
  rfl

theorem map_subgroupOf_equivMapOfInjective {X L : Subgroup K} :
    ((X.map K.subtype).subgroupOf (L.map K.subtype)).map
      (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom =
        X.subgroupOf L := by
  ext y
  rw [mem_map_equiv, MulEquiv.symm_symm, mem_subgroupOf, mem_subgroupOf]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y := K.subtype_injective hzy
    rwa [← this]
  · intro hy
    exact ⟨y, hy, rfl⟩

end Transport

section Borel

variable {A : Type*} [Group A] [Finite A]

theorem bender_borel_eq {K S B : Subgroup A} [K.Normal] {n : ℕ} {U' : Subgroup K}
    (hU' : U' = (S ⊓ K).subgroupOf K) (hD : BenderData K U' n) (hKS : K ⊔ S = ⊤)
    (hSB : S ≤ B) (hBtop : B < ⊤) (hBmax : ∀ Y : Subgroup A, S ≤ Y → Y < ⊤ → Y ≤ B) :
    B ⊓ K = (normalizer (U' : Set K)).map K.subtype ∧
      B ≤ normalizer ((S ⊓ K : Subgroup A) : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ K with hUdef
  have hUK : U ≤ K := inf_le_right
  have hNmap : (normalizer (U' : Set K)).map K.subtype = K ⊓ normalizer (U : Set A) := by
    rw [hU', ← inf_normalizer_subgroupOf hUK, map_subgroupOf_eq_of_le inf_le_left]
  have hSN : S ≤ normalizer (U : Set A) := by
    intro s hs
    refine mem_normalizer_iff.2 fun y => ⟨fun hy => ⟨?_, ?_⟩, fun hy => ⟨?_, ?_⟩⟩
    · exact S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs)
    · exact (‹K.Normal›).conj_mem y hy.2 s
    · have h1 := S.mul_mem (S.mul_mem (S.inv_mem hs) hy.1) hs
      rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h1
    · have h1 := (‹K.Normal›).conj_mem _ hy.2 s⁻¹
      rwa [show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at h1
  have hNtop : normalizer (U : Set A) ≠ ⊤ := by
    intro htop
    apply hD.stronglyEmbedded.1
    rw [eq_top_iff]
    intro y _
    have h1 : (y : A) ∈ K ⊓ normalizer (U : Set A) := ⟨y.2, htop ▸ mem_top _⟩
    rw [← hNmap] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    rwa [← K.subtype_injective hzy]
  have hNB : normalizer (U : Set A) ≤ B := hBmax _ hSN (lt_top_iff_ne_top.2 hNtop)
  have hle : normalizer (U' : Set K) ≤ (B ⊓ K).subgroupOf K := by
    intro y hy
    have h1 : (y : A) ∈ (normalizer (U' : Set K)).map K.subtype := ⟨y, hy, rfl⟩
    rw [hNmap] at h1
    exact ⟨hNB h1.2, y.2⟩
  have hne : (B ⊓ K).subgroupOf K ≠ ⊤ := by
    intro h
    have hKB : K ≤ B := fun y hy => by
      have : (⟨y, hy⟩ : K) ∈ (B ⊓ K).subgroupOf K := h ▸ mem_top _
      exact this.1
    exact hBtop.ne (eq_top_iff.2 (hKS ▸ sup_le hKB hSB))
  have hBK : (B ⊓ K).subgroupOf K = normalizer (U' : Set K) := by
    rcases hD.isCoatom.le_iff.1 hle with h | h
    · exact absurd h hne
    · exact h
  have hBKeq : B ⊓ K = (normalizer (U' : Set K)).map K.subtype := by
    rw [← hBK, subgroupOf_map_subtype, inf_assoc, inf_idem]
  refine ⟨hBKeq, fun b hb => ?_⟩
  have hU2 : IsPGroup 2 U := by
    have h1 := hD.isPGroup.map K.subtype
    rwa [hU', map_subgroupOf_eq_of_le hUK] at h1
  have hUidx : ¬ 2 ∣ U.relIndex K := by
    have h1 := hD.not_dvd_index
    rwa [hU', ← relIndex] at h1
  set P := U.map (MulAut.conj b).toMonoidHom with hPdef
  have hPBK : P ≤ K ⊓ normalizer (U : Set A) := by
    rw [← hNmap, ← hBKeq]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨B.mul_mem (B.mul_mem hb (hSB hu.1)) (B.inv_mem hb), (‹K.Normal›).conj_mem u hu.2 b⟩
  have hUle : U ≤ K ⊓ normalizer (U : Set A) := le_inf hUK le_normalizer
  have hidx : ¬ 2 ∣ U.relIndex (K ⊓ normalizer (U : Set A)) := fun h => hUidx
    (h.trans (Dvd.intro _ (relIndex_mul_relIndex U _ K hUle inf_le_left)))
  have hPU : P ≤ U := le_of_isPGroup_of_not_dvd_relIndex hU2 hUle hidx (hU2.map _) hPBK
    (hPBK.trans inf_le_right)
  have hPeq : P = U := eq_of_le_of_card_ge hPU (by
    rw [hPdef, card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (MulAut.conj b).injective])
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← hPeq]
    exact ⟨y, hy, rfl⟩
  · rw [← hPeq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have h1 := congrArg (fun w => b⁻¹ * w * b) hzy
      simpa [mul_assoc] using h1
    rwa [← this]

end Borel

end CFSG.Quasithin.H13.QRC
