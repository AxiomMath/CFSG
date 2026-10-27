module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalU3
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalSz2
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.Quasithin.Recognition.Stroth.SubconstNaturalU3

public section

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GorensteinWalter
open CFSG.RankThree.PartOne.CTP
open UnitaryPointStructure
open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem stabilizer_map_mulEquiv {G Ω G' Ω' : Type*} [Group G] [MulAction G Ω] [Group G']
    [MulAction G' Ω'] (e : G ≃* G') (φ : Ω ≃ Ω')
    (he : ∀ (g : G) (x : Ω), φ (g • x) = e.toMonoidHom g • φ x) (α : Ω) :
    (MulAction.stabilizer G α).map e.toMonoidHom = MulAction.stabilizer G' (φ α) := by
  ext g'
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← he g α, hg]
  · intro hg
    refine ⟨e.symm g', ?_, e.apply_symm_apply g'⟩
    have h := he (e.symm g') α
    have h' : e.toMonoidHom (e.symm g') = g' := e.apply_symm_apply g'
    rw [h'] at h
    exact φ.injective (h.trans hg)

theorem UnitaryPointStructure.map {G Ω G' Ω' : Type*} [Group G] [MulAction G Ω]
    [Group G'] [MulAction G' Ω'] (e : G ≃* G') (φ : Ω ≃ Ω')
    (he : ∀ (g : G) (x : Ω), φ (g • x) = e.toMonoidHom g • φ x)
    {α β : Ω} {U T B : Subgroup G} (h : UnitaryPointStructure G Ω α β U T B) :
    UnitaryPointStructure G' Ω' (φ α) (φ β) (U.map e.toMonoidHom) (T.map e.toMonoidHom)
      (B.map e.toMonoidHom) where
  isMultiplyPretransitive := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := MulAction.is_two_pretransitive_iff.mp h.isMultiplyPretransitive
      (φ.symm.injective.ne hab) (φ.symm.injective.ne hcd)
    refine ⟨e g, ?_, ?_⟩
    · have h := congrArg φ hg1
      simpa [he g (φ.symm a)] using h
    · have h := congrArg φ hg2
      simpa [he g (φ.symm b)] using h
  ne := fun h' => h.ne (φ.injective h')
  sup_eq_stabilizer := by
    rw [← Subgroup.map_sup U T e.toMonoidHom, h.sup_eq_stabilizer,
      stabilizer_map_mulEquiv e φ he α]
  eq_stabilizer := by
    rw [h.eq_stabilizer, stabilizer_map_mulEquiv e φ he α]
  root_normal := by
    have hUleB : U ≤ B := by
      rw [h.eq_stabilizer, ← h.sup_eq_stabilizer]
      exact le_sup_left
    have hBnorm : B ≤ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUleB).mp h.root_normal
    have hconj : ∀ b' ∈ B.map e.toMonoidHom, ∀ u' ∈ U.map e.toMonoidHom,
        b' * u' * b'⁻¹ ∈ U.map e.toMonoidHom := by
      intro b' hb' u' hu'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
      have hmem : b * u * b⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hBnorm hb) u).mp hu
      exact Subgroup.mem_map.mpr ⟨b * u * b⁻¹, hmem, by simp [mul_assoc]⟩
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hUleB)]
    intro u b hu hb
    exact hconj b hb u hu
  inf_eq_bot := by
    rw [← Subgroup.map_inf U T e.toMonoidHom e.injective, h.inf_eq_bot, Subgroup.map_bot]
  stabilizer_inf_stabilizer := by
    rw [← stabilizer_map_mulEquiv e φ he α, ← stabilizer_map_mulEquiv e φ he β,
      ← Subgroup.map_inf _ _ _ e.injective, h.stabilizer_inf_stabilizer]
  isCyclic_T := by
    haveI := h.isCyclic_T
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective T e.toMonoidHom e.injective).toMonoidHom
      (Equiv.surjective _)
  odd_T := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact h.odd_T
  regular := by
    intro x y hx hy
    have hx' : φ.symm x ≠ α := fun h' => hx (by rw [← h', Equiv.apply_symm_apply])
    have hy' : φ.symm y ≠ α := fun h' => hy (by rw [← h', Equiv.apply_symm_apply])
    obtain ⟨u, hu, huniq⟩ := h.regular _ _ hx' hy'
    refine ⟨⟨e u, Subgroup.mem_map_of_mem _ u.2⟩, ?_, ?_⟩
    · show e u • x = y
      have h := congrArg φ hu
      simpa [he (u : G) (φ.symm x)] using h
    · intro v hv
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp v.2
      have hv' : w • φ.symm x = φ.symm y := by
        have h : e w • x = y := hwv ▸ hv
        have h2 : φ (w • φ.symm x) = φ (φ.symm y) := by
          simpa [he w (φ.symm x)] using h
        exact φ.injective h2
      have hwu : w = (u : G) := congrArg Subtype.val (huniq ⟨w, hw⟩ hv')
      exact Subtype.ext (by rw [← hwv, hwu]; rfl)
  fix_T := by
    intro x hx
    have hfix : ∀ t ∈ T, t • (φ.symm x) = φ.symm x := by
      intro t ht
      have h1 : e t • x = x := hx (e t) (Subgroup.mem_map_of_mem _ ht)
      have h2 : φ (t • φ.symm x) = φ (φ.symm x) := by
        simpa [he t (φ.symm x)] using h1
      exact φ.injective h2
    rcases h.fix_T _ hfix with h' | h'
    · left
      rw [← h', Equiv.apply_symm_apply]
    · right
      rw [← h', Equiv.apply_symm_apply]
  exists_ne_ne := by
    intro a b
    obtain ⟨c, hca, hcb⟩ := h.exists_ne_ne (φ.symm a) (φ.symm b)
    refine ⟨φ c, ?_, ?_⟩
    · intro h'
      exact hca (by rw [← h', Equiv.symm_apply_apply])
    · intro h'
      exact hcb (by rw [← h', Equiv.symm_apply_apply])

theorem isCyclic_sylow_of_odd_inf_normal {X : Type} [Group X] [Finite X]
    {N H T : Subgroup X} [N.Normal] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hT : T = H ⊓ N) (hTodd : Odd (Nat.card T))
    (hOut : ∀ Q : Sylow 2 (Outer N), IsCyclic (Q : Subgroup (Outer N))) :
    ∀ P : Sylow 2 H, IsCyclic (P : Subgroup H) := by
  classical
  let f : H →* Outer N := (outerHom N).comp H.subtype
  have hker : f.ker = T.subgroupOf H := by
    ext x
    constructor
    · intro hx
      have hxX : (x : X) ∈ (outerHom N).ker := hx
      rw [ker_outerHom N hC] at hxX
      rw [hT]
      exact ⟨x.2, hxX⟩
    · intro hx
      rw [hT] at hx
      change outerHom N (x : X) = 1
      rw [← MonoidHom.mem_ker, ker_outerHom N hC]
      exact hx.2
  intro P
  let g : ↥P →* Outer N := f.comp (P : Subgroup H).subtype
  have hg_inj : Function.Injective g := by
    intro a b hab
    have h1 : g (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hxT : (((a * b⁻¹ : ↥P) : ↥H) : X) ∈ T := by
      have h2 : ((a * b⁻¹ : ↥P) : ↥H) ∈ f.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact h2
    have hdvd1 : orderOf ((a * b⁻¹ : ↥P) : ↥H) ∣ Nat.card ↥P :=
      Subgroup.orderOf_dvd_natCard (P : Subgroup H) (a * b⁻¹).2
    have hdvd2 : orderOf (((a * b⁻¹ : ↥P) : ↥H) : X) ∣ Nat.card T :=
      Subgroup.orderOf_dvd_natCard T hxT
    obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
    have hdvd1' : orderOf ((a * b⁻¹ : ↥P) : ↥H) ∣ 2 ^ m := by
      rw [← hm]
      exact hdvd1
    have hdvd2' : orderOf ((a * b⁻¹ : ↥P) : ↥H) ∣ Nat.card T := by
      rw [← Subgroup.orderOf_coe]
      exact hdvd2
    have hcop : Nat.Coprime (2 ^ m) (Nat.card T) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hTodd)
    have hone : orderOf ((a * b⁻¹ : ↥P) : ↥H) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd1' hdvd2'
    have hab1 : (a * b⁻¹ : ↥P) = 1 := Subtype.ext (orderOf_eq_one_iff.mp hone)
    calc a = (a * b⁻¹) * b := by group
      _ = 1 * b := by rw [hab1]
      _ = b := one_mul b
  have hmapcyc : IsCyclic ↥((P : Subgroup ↥H).map f) := by
    obtain ⟨Q, hQ⟩ := (P.isPGroup'.map f).exists_le_sylow
    haveI : IsCyclic ↥(Q : Subgroup (Outer N)) := hOut Q
    exact Subgroup.isCyclic_of_le hQ
  have hrange : (⊤ : Subgroup ↥P).map g = (P : Subgroup ↥H).map f := by
    ext y
    constructor
    · rintro ⟨p, -, rfl⟩
      exact Subgroup.mem_map_of_mem f p.2
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  let e : ↥P ≃* ↥((P : Subgroup ↥H).map f) :=
    (Subgroup.topEquiv.symm.trans
      (Subgroup.equivMapOfInjective ⊤ g hg_inj)).trans (MulEquiv.subgroupCongr hrange)
  exact e.isCyclic.mpr hmapcyc

structure PSU3IsotropicModel (X Ω : Type) [Group X] [MulAction X Ω] [Fintype Ω]
    (F : Type) [Field F] (N : Subgroup X) (k : ℕ) where
  J : HermitianForm 3 F
  hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  hconj : ∀ z : F, J.conj z = z ^ (2 ^ k)
  hfixed : Nat.card {z : F // J.conj z = z} = 2 ^ k
  eN : ↥N ≃* ProjectiveSpecialUnitaryMatrixGroup J
  φ : Ω ≃ unitaryIsotropicPoints J
  hequiv : ∀ (g : ↥N) (x : Ω), φ (g • x) = eN g • φ x
  U' : Subgroup ↥N
  T' : Subgroup ↥N
  B' : Subgroup ↥N
  hU' : U' = (hermitianUnipotentPSU J hJ).range.map eN.symm.toMonoidHom
  hT' : T' = (torusPSU J hJ).range.map eN.symm.toMonoidHom
  hB' : B' = (unitaryCoordinateStabilizer J 0).map eN.symm.toMonoidHom
  hP : UnitaryPointStructure ↥N Ω
    (φ.symm (unitaryOuterIsotropicPoint J hJ 0 (by decide)))
    (φ.symm (unitaryOuterIsotropicPoint J hJ 2 (by decide))) U' T' B'
  hdata : RankOneData ↥N U' B'
  hcardU' : Nat.card U' = (2 ^ k) ^ 3
  hNbot : N ≠ ⊥
  hcardL4 : Fintype.card Ω = 1 + Nat.card U'
  hstab_sub : ∀ y : Ω,
    (MulAction.stabilizer X y).subgroupOf N = MulAction.stabilizer ↥N y
  hT'cyc : IsCyclic T'
  hT'odd : Odd (Nat.card T')
  hT'card : Nat.card T' = ((2 ^ k) ^ 2 - 1) / Nat.gcd 3 (2 ^ k + 1)

theorem exists_psu3_isotropicModel {X Ω : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    Nonempty (PSU3IsotropicModel X Ω F N k) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  obtain ⟨J, hJ, hconj, hfixed⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := F) 2 k hF
  obtain ⟨e₀⟩ :=
    CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J (2 ^ k) hF hfixed
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω₀ := unitaryIsotropicPoints J
  let α : Ω₀ := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let β₀ : Ω₀ := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  let U₀ : Subgroup G := (hermitianUnipotentPSU J hJ).range
  let T₀ : Subgroup G := (torusPSU J hJ).range
  let B₀ : Subgroup G := unitaryCoordinateStabilizer J 0
  have hUP : UnitaryPointStructure G Ω₀ α β₀ U₀ T₀ B₀ :=
    unitaryPointStructure J hJ k hk hF hfixed
  letI : MulAction G Ω₀ := instMulActionUnitaryIsotropicPoints (J := J)
  haveI : MulAction.IsMultiplyPretransitive G Ω₀ 2 := hUP.isMultiplyPretransitive
  haveI : MulAction.IsPretransitive G Ω₀ :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hdata : RankOneData G U₀ B₀ := (rankOneData_psu3 J k hk hF hfixed hJ).1
  have hcardU₀ : Nat.card U₀ = (2 ^ k) ^ 3 :=
    (rankOneData_psu3 J k hk hF hfixed hJ).2
  let eN : ↥N ≃* G := e.trans e₀.symm
  let U' : Subgroup ↥N := U₀.map eN.symm.toMonoidHom
  let B' : Subgroup ↥N := B₀.map eN.symm.toMonoidHom
  let T' : Subgroup ↥N := T₀.map eN.symm.toMonoidHom
  have hB'def : B' = B₀.map eN.symm.toMonoidHom := rfl
  have hT'def : T' = T₀.map eN.symm.toMonoidHom := rfl
  have hcompN : eN.toMonoidHom.comp eN.symm.toMonoidHom = MonoidHom.id G := by
    ext z
    simp
  have hB'map : B'.map eN.toMonoidHom = B₀ := by
    rw [hB'def, Subgroup.map_map, hcompN, Subgroup.map_id]
  have hdata' : RankOneData ↥N U' B' := hdata.map eN.symm
  have hcardU' : Nat.card U' = (2 ^ k) ^ 3 := by
    change Nat.card (U₀.map eN.symm.toMonoidHom) = (2 ^ k) ^ 3
    rw [Subgroup.card_map_of_injective eN.symm.injective, hcardU₀]
  have hNbot : N ≠ ⊥ := by
    intro hbot
    apply hdata'.ne_bot
    rw [eq_bot_iff]
    intro x _
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx' : (x : X) ∈ (⊥ : Subgroup X) := hbot ▸ x.2
    simpa using hx'
  have hcardL4 : Fintype.card Ω = 1 + Nat.card U' := by
    rw [hΩ, hcardU', ← pow_mul, mul_comm k 3]
    omega
  haveI : MulAction.IsPreprimitive X Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive X Ω := inferInstance
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩ]; positivity)
  have hfixedN : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    have hfixall : ∀ x : Ω, n • x = x := fun x => by
      have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
      exact hx n
    have h1 : n = 1 := FaithfulSMul.eq_of_smul_eq_smul (fun x => by rw [hfixall x, one_smul])
    exact hn1 h1
  haveI : MulAction.IsPretransitive ↥N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixedN
  let ω₀ : Ω := Classical.arbitrary Ω
  obtain ⟨x₀, hx₀⟩ :=
    exists_stabilizer_eq_conj_of_rankOneData (Y := X) N hNbot h2 hdata' hcardL4 ω₀
  have hstab_sub : ∀ y : Ω, (MulAction.stabilizer X y).subgroupOf N =
      MulAction.stabilizer ↥N y := by
    intro y
    ext n
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  have hstabN : (MulAction.stabilizer ↥N ω₀).map eN.toMonoidHom =
      MulAction.stabilizer G (eN x₀ • α) := by
    rw [← hstab_sub ω₀, hx₀, UnitaryPointStructure.map_conj_map eN B' x₀, hB'map,
      hUP.eq_stabilizer]
    exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj (eN x₀) α).symm
  obtain ⟨φ₀, hφ₀⟩ :=
    CFSG.BenderSuzuki.PFchapter4section1.exists_equivariant_equiv_of_stabilizer_map_eq
      (L := ↥N) (X := Ω) (L' := G) (X' := Ω₀) eN ω₀ (eN x₀ • α) hstabN
  let ω : Ω := φ₀.symm α
  let β : Ω := φ₀.symm β₀
  have hP : UnitaryPointStructure ↥N Ω ω β U' T' B' :=
    UnitaryPointStructure.map eN.symm φ₀.symm (fun g y => by
      apply φ₀.injective
      calc φ₀ (φ₀.symm (g • y)) = g • y := Equiv.apply_symm_apply φ₀ (g • y)
        _ = eN (eN.symm g) • y := by rw [eN.apply_symm_apply]
        _ = eN (eN.symm g) • φ₀ (φ₀.symm y) := by rw [Equiv.apply_symm_apply]
        _ = φ₀ (eN.symm g • φ₀.symm y) := (hφ₀ (eN.symm g) (φ₀.symm y)).symm) hUP
  have hT'cyc : IsCyclic T' := by
    rw [hT'def]
    haveI : IsCyclic T₀ := hUP.isCyclic_T
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective T₀ eN.symm.toMonoidHom eN.symm.injective).toMonoidHom
      (Equiv.surjective _)
  have hT'odd : Odd (Nat.card T') := by
    rw [hT'def, Subgroup.card_map_of_injective eN.symm.injective]
    exact hUP.odd_T
  have hT'card : Nat.card T' = ((2 ^ k) ^ 2 - 1) / Nat.gcd 3 (2 ^ k + 1) := by
    rw [hT'def, Subgroup.card_map_of_injective eN.symm.injective]
    exact (range_torusPSU_card_isCyclic J (2 ^ k) hF hfixed hJ).1
  exact ⟨
    { J := J
      hJ := hJ
      hconj := hconj
      hfixed := hfixed
      eN := eN
      φ := φ₀
      hequiv := hφ₀
      U' := U'
      T' := T'
      B' := B'
      hU' := rfl
      hT' := rfl
      hB' := rfl
      hP := hP
      hdata := hdata'
      hcardU' := hcardU'
      hNbot := hNbot
      hcardL4 := hcardL4
      hstab_sub := hstab_sub
      hT'cyc := hT'cyc
      hT'odd := hT'odd
      hT'card := hT'card }⟩

theorem rankOneLocal_psu3 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    RankOneLocal X Ω N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  let M := Classical.choice (exists_psu3_isotropicModel h2 k hk F hF N hN e hΩ)
  let U' : Subgroup ↥N := M.U'
  let T' : Subgroup ↥N := M.T'
  let B' : Subgroup ↥N := M.B'
  let ω : Ω := M.φ.symm (unitaryOuterIsotropicPoint M.J M.hJ 0 (by decide))
  let β : Ω := M.φ.symm (unitaryOuterIsotropicPoint M.J M.hJ 2 (by decide))
  have hP : UnitaryPointStructure ↥N Ω ω β U' T' B' := M.hP
  have hdata' : RankOneData ↥N U' B' := M.hdata
  have hstab_sub : ∀ y : Ω, (MulAction.stabilizer X y).subgroupOf N =
      MulAction.stabilizer ↥N y := M.hstab_sub
  have hT'cyc : IsCyclic T' := M.hT'cyc
  have hT'odd : Odd (Nat.card T') := M.hT'odd
  have hne32 : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
    rintro h
    have h2k : 2 ^ k = 2 := (Prod.mk.inj h).2
    have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hPerfectProj : Group.IsPerfect (StatedProj (StatedSU 3 (2 ^ k) F)) := by
    haveI : Group.IsPerfect (StatedSU 3 (2 ^ k) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) (by norm_num) hne32
    exact Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)))
      (QuotientGroup.mk'_surjective _)
  have hPerfectN : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr M.hNbot
  haveI : Group.IsPerfect ↥N := hPerfectN
  have hNcomm : ¬ IsMulCommutative ↥N := Group.IsPerfect.not_isMulCommutative ↥N
  have hcent : Subgroup.centralizer (N : Set X) = ⊥ :=
    centralizer_eq_bot_of_isMultiplyPretransitive (N := N) hNcomm h2
  obtain ⟨eB, hB⟩ := benderType_statedProj (n := k) hk hF
  obtain ⟨Dd, hDdn, hDdcyc, hDdcard, hDdquot, -⟩ :=
    CFSG.GH74.Uniqueness.Bender.outerStructure_of_mulEquiv e hB.outer_unitary
  letI : Dd.Normal := hDdn
  have hDdodd : Odd (Nat.card Dd) := by
    rw [hDdcard]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  have houterCyc : ∀ Q : Sylow 2 (Outer ↥N), IsCyclic (Q : Subgroup (Outer ↥N)) :=
    fun Q => CFSG.GH74.Uniqueness.Bender.isCyclic_sylow_of_quotient Dd hDdodd hDdquot Q
  have hOutSolv : Group.IsSolvable (Outer ↥N) := by
    have hsolvDd : Group.IsSolvable Dd := by
      haveI : IsCyclic Dd := hDdcyc
      letI : CommGroup Dd := IsCyclic.commGroup
      infer_instance
    have hsolvQuot : Group.IsSolvable (Outer ↥N ⧸ Dd) := by
      haveI : IsCyclic (Outer ↥N ⧸ Dd) := hDdquot
      letI : CommGroup (Outer ↥N ⧸ Dd) := IsCyclic.commGroup
      infer_instance
    haveI := hsolvDd
    haveI := hsolvQuot
    exact Group.isSolvable_of_ker_le_range Dd.subtype (QuotientGroup.mk' Dd) (by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩)
  haveI : MulAction.IsPreprimitive X Ω := MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive X Ω := inferInstance
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩ]; positivity)
  have hfixedN : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp M.hNbot
    have hfixall : ∀ x : Ω, n • x = x := fun x => by
      have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
      exact hx n
    have h1 : n = 1 := FaithfulSMul.eq_of_smul_eq_smul (fun x => by rw [hfixall x, one_smul])
    exact hn1 h1
  haveI : MulAction.IsPretransitive ↥N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixedN
  have hU'le : U' ≤ MulAction.stabilizer ↥N ω := by
    rw [← hP.sup_eq_stabilizer]; exact le_sup_left
  have hU'leB' : U' ≤ B' := by
    rw [hP.eq_stabilizer, ← hP.sup_eq_stabilizer]; exact le_sup_left
  have hB'norm : B' ≤ Subgroup.normalizer (U' : Set ↥N) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU'leB').mp hP.root_normal
  have torusOdd : ∀ x y : Ω, x ≠ y →
      Odd (Nat.card ↥(N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y)) := by
    intro x y hxy
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y =
        (MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y).map N.subtype :=
      inf_stabilizer_eq_map_subtype rfl
    have hcard1 : Nat.card ↥(N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y) =
        Nat.card ↥((MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y).map N.subtype) :=
      Nat.card_congr
        { toFun := fun t => ⟨t.1, hfield.le t.2⟩
          invFun := fun t => ⟨t.1, hfield.ge t.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hcard1, Subgroup.card_map_of_injective N.subtype_injective]
    obtain ⟨n, -, -, hTxy⟩ := UnitaryPointStructure.exists_conj_torus hP hxy.symm
    rw [hTxy, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hT'odd
  have torusFix : ∀ x y z : Ω, x ≠ y →
      (∀ t ∈ N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y, t • z = z) →
        z = x ∨ z = y := by
    intro x y z hxy hfix
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y =
        (MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y).map N.subtype :=
      inf_stabilizer_eq_map_subtype rfl
    apply UnitaryPointStructure.fix_stabilizer_inf' hP hxy.symm
    intro s hs
    exact hfix (s : X) (hfield.ge (Subgroup.mem_map_of_mem _ hs))
  have torusCyclic : ∀ x y : Ω, x ≠ y →
      IsCyclic ↥(N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y) := by
    intro x y hxy
    have hfield : N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y =
        (MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y).map N.subtype :=
      inf_stabilizer_eq_map_subtype rfl
    obtain ⟨n, -, -, hTxy⟩ := UnitaryPointStructure.exists_conj_torus hP hxy.symm
    have hcyc : IsCyclic ↥(T'.map (MulAut.conj n).toMonoidHom) :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective T' (MulAut.conj n).toMonoidHom
          (MulAut.conj n).injective).toMonoidHom (Equiv.surjective _)
    have hcycN : IsCyclic ↥(MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y) := by
      rw [hTxy]
      exact hcyc
    have hcycMap : IsCyclic ↥((MulAction.stabilizer ↥N x ⊓
        MulAction.stabilizer ↥N y).map N.subtype) :=
      (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).isCyclic.mp hcycN
    have e2 : ↥(N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y) ≃*
        ↥((MulAction.stabilizer ↥N x ⊓ MulAction.stabilizer ↥N y).map N.subtype) :=
      { toFun := fun t => ⟨t.1, hfield.le t.2⟩
        invFun := fun t => ⟨t.1, hfield.ge t.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact e2.isCyclic.mpr hcycMap
  have rootField : ∀ x : Ω, ∃ R : Subgroup X, R ≤ MulAction.stabilizer X x ∧
      (R.subgroupOf (MulAction.stabilizer X x)).Normal ∧ IsPGroup 2 R ∧
      ∀ a b : Ω, a ≠ x → b ≠ x → ∃! r : R, (r : X) • a = b := by
    intro x
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥N ω x
    rw [← hn]
    let Q : Subgroup ↥N := U'.map (MulAut.conj n).toMonoidHom
    let R : Subgroup X := Q.map N.subtype
    have hQ2 : IsPGroup 2 Q := hdata'.isPGroup.map _
    obtain ⟨S₀, hS₀⟩ := hdata'.isSylow
    have hQsyl : ∃ S : Sylow 2 ↥N, (S : Subgroup ↥N) = Q := by
      refine ⟨S₀.mapSurjective (f := (MulAut.conj n).toMonoidHom)
        (MulAut.conj n).surjective, ?_⟩
      rw [Sylow.coe_mapSurjective (MulAut.conj n).surjective S₀, hS₀]
    have hQle : Q ≤ MulAction.stabilizer ↥N (n • ω) :=
      (Subgroup.map_mono hU'le).trans
        (le_of_eq (MulAction.stabilizer_smul_eq_stabilizer_map_conj n ω).symm)
    have hQnormal : MulAction.stabilizer ↥N (n • ω) ≤ Subgroup.normalizer (Q : Set ↥N) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj n ω, ← hP.eq_stabilizer]
      exact (Subgroup.map_mono hB'norm).trans (Subgroup.le_normalizer_map _)
    have hRnorm : MulAction.stabilizer X (n • ω) ≤ Subgroup.normalizer (R : Set X) :=
      root_normal_in_pointStabilizer hQ2 hQsyl hQle hQnormal
    have hRle : R ≤ MulAction.stabilizer X (n • ω) := by
      calc R = Q.map N.subtype := rfl
        _ ≤ (MulAction.stabilizer ↥N (n • ω)).map N.subtype := Subgroup.map_mono hQle
        _ = ((MulAction.stabilizer X (n • ω)).subgroupOf N).map N.subtype := by
            rw [hstab_sub (n • ω)]
        _ = MulAction.stabilizer X (n • ω) ⊓ N := Subgroup.subgroupOf_map_subtype _ _
        _ ≤ MulAction.stabilizer X (n • ω) := inf_le_left
    refine ⟨R, hRle, (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).mpr hRnorm,
      hQ2.map N.subtype, ?_⟩
    intro a b ha hb
    obtain ⟨u, hu, huniq⟩ :=
      UnitaryPointStructure.regular_map_conj hP.regular n a b ha hb
    refine ⟨⟨(u : X), Subgroup.mem_map_of_mem N.subtype u.2⟩, ?_, ?_⟩
    · show (u : X) • a = b
      exact hu
    · intro r hr
      obtain ⟨v, hv, hvr⟩ := Subgroup.mem_map.mp r.2
      have hvb : (v : ↥N) • a = b := by
        have h : (r : X) • a = b := hr
        rw [← hvr] at h
        exact h
      have hvu : v = (u : ↥N) := congrArg Subtype.val (huniq ⟨v, hv⟩ hvb)
      exact Subtype.ext (by
        show (r : X) = (u : X)
        rw [← hvr]
        exact Subtype.ext_iff.mp hvu)
  have oddClosure : ∀ x y : Ω, x ≠ y → ∀ S : Set X,
      S ⊆ ↑(MulAction.stabilizer X x ⊓ MulAction.stabilizer X y) →
      (∀ s ∈ S, Odd (orderOf s)) → Odd (Nat.card ↥(Subgroup.closure S)) := by
    intro x y hxy S hSsub hSodd
    let H : Subgroup X := MulAction.stabilizer X x ⊓ MulAction.stabilizer X y
    let T : Subgroup X := N ⊓ H
    have hTeq : T = H ⊓ N := by rw [show T = N ⊓ H from rfl, inf_comm]
    have hTeqN : T = N ⊓ MulAction.stabilizer X x ⊓ MulAction.stabilizer X y := by
      rw [show T = N ⊓ H from rfl]
      exact (inf_assoc N _ _).symm
    have hTodd : Odd (Nat.card T) := by
      rw [hTeqN]
      exact torusOdd x y hxy
    have hcyc := isCyclic_sylow_of_odd_inf_normal hcent hTeq hTodd houterCyc
    obtain ⟨K, hKodd, hKmem⟩ := CFSG.OddStandard.SmallF3.Omega.exists_subgroup_odd_elems H hcyc
    have hcl : Subgroup.closure S ≤ K := by
      rw [Subgroup.closure_le]
      intro s hs
      exact (hKmem s).mpr ⟨hSsub hs, hSodd s hs⟩
    exact Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le hcl)
  have perfectEq : CFSG.perfectResidual X = N :=
    perfectResidual_eq_of_normal_perfect_outer hPerfectN hOutSolv hcent
  exact
    { root := rootField
      torus_odd := torusOdd
      torus_fix := torusFix
      torus_cyclic := torusCyclic
      odd_closure := oddClosure
      perfectResidual_eq := perfectEq }

end CFSG.Quasithin.Stroth.WeissDelta

