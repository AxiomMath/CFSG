module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleTransport

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.CGT.PushingUpLit.SolKNA
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem isSzNaturalSection_of_isSzNatural {H L N : Subgroup G} {a : ℕ}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* ↥(suzukiGroup a (GaloisField 2 (2 * a + 1))))
    (hnat : letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
      IsSzNatural (sectionRep hHL hHN hNL hE hO e)) :
    IsSzNaturalSection H N L a := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  obtain ⟨c, φ, hφ⟩ := hnat
  let K := GaloisField 2 (2 * a + 1)
  let J : Matrix (Fin 4) (Fin 4) K := CFSG.LinearAlgebra.exteriorSquareJ K
  have hJJ : J * J = 1 := exteriorSquareJ_mul_self K
  let ι : ↥N →* Ch3z.chiefMod L N := Ch3z.chiefIota hNL
  let ψ : ↥N →* Multiplicative (Fin 4 → K) :=
    MonoidHom.mk' (fun n => Multiplicative.ofAdd (J *ᵥ φ (Additive.ofMul (ι n)))) (by
      intro n m
      have hι : Additive.ofMul (ι (n * m)) =
          Additive.ofMul (ι n) + Additive.ofMul (ι m) := by
        rw [map_mul]
        rfl
      rw [hι, map_add, Matrix.mulVec_add]
      rfl)
  have hsurj : Function.Surjective ψ := by
    intro v
    obtain ⟨w, hw⟩ := φ.surjective (J *ᵥ Multiplicative.toAdd v)
    obtain ⟨n, hn⟩ := Ch3z.chiefIota_surjective hNL (Additive.toMul w)
    have hn' : Additive.ofMul (ι n) = w := by
      rw [hn]
      rfl
    refine ⟨n, ?_⟩
    have h1 : J *ᵥ φ (Additive.ofMul (ι n)) = Multiplicative.toAdd v := by
      rw [hn', hw, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
    have h2 : ψ n = Multiplicative.ofAdd (Multiplicative.toAdd v) := by
      show Multiplicative.ofAdd (J *ᵥ φ (Additive.ofMul (ι n))) = _
      rw [h1]
    rw [h2]
    rfl
  have hker : ψ.ker = L.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : J *ᵥ φ (Additive.ofMul (ι n)) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [ψ] using this
      have h2 : φ (Additive.ofMul (ι n)) = 0 := by
        have := congrArg (fun v => J *ᵥ v) h1
        rwa [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      have h3 : Additive.ofMul (ι n) = 0 := (AddEquiv.map_eq_zero_iff φ).mp h2
      exact (Ch3z.chiefIota_eq_one_iff hNL n).mp (by simpa using h3)
    · intro h
      have h3 : ι n = 1 := (Ch3z.chiefIota_eq_one_iff hNL n).mpr h
      have h2 : φ (Additive.ofMul (ι n)) = 0 := by
        rw [h3]
        simpa using map_zero φ
      show ψ n = 1
      show Multiplicative.ofAdd (J *ᵥ φ (Additive.ofMul (ι n))) = 1
      rw [h2, Matrix.mulVec_zero]
      rfl
  have hJmap : J.map (· ^ 2 ^ c) = J := by
    ext i j
    dsimp only [J]
    rw [Matrix.map_apply, CFSG.LinearAlgebra.exteriorSquareJ_apply]
    split_ifs with h
    · simp [h]
    · simp [h, zero_pow (pow_ne_zero c two_ne_zero)]
  have heq : ∀ (h : ↥H) (x y : ↥N),
      (y : G) = (h : G) * (x : G) * (h : G)⁻¹ →
      Multiplicative.toAdd (ψ y) =
        (((((e.trans (szEquiv a)) (QuotientGroup.mk h) : ↥(Sz a)) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ Multiplicative.toAdd (ψ x) := by
    intro h x y hy
    let g : ↥(suzukiGroup a K) := e (QuotientGroup.mk h)
    let τ : ↥(Sz a) := szEquiv a g
    have hyn : (h : G) * (x : G) * (h : G)⁻¹ ∈ N := hy ▸ y.2
    have hy' : (⟨(h : G) * (x : G) * (h : G)⁻¹, hyn⟩ : ↥N) = y := Subtype.ext hy.symm
    have hι : Additive.ofMul (ι y) =
        sectionRep hHL hHN hNL hE hO e g (Additive.ofMul (ι x)) := by
      have h := sectionRep_chiefIota hHL hHN hNL hE hO e h x hyn
      rw [← hy']
      exact h.symm
    have hJg : J * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) =
        ((((τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) * J) := by
      have h := szEquiv_mul_J a g
      have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map (· ^ 2 ^ c)) h
      rw [matrix_map_pow_mul, matrix_map_pow_mul, hJmap] at h'
      exact h'.symm
    have hφg := hφ g (Additive.ofMul (ι x))
    calc Multiplicative.toAdd (ψ y)
        = J *ᵥ φ (Additive.ofMul (ι y)) := rfl
      _ = J *ᵥ φ (sectionRep hHL hHN hNL hE hO e g (Additive.ofMul (ι x))) := by rw [hι]
      _ = J *ᵥ ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ
            φ (Additive.ofMul (ι x))) := by rw [hφg]
      _ = (J * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c))) *ᵥ
            φ (Additive.ofMul (ι x)) := by rw [Matrix.mulVec_mulVec]
      _ = (((((τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) * J) *ᵥ
            φ (Additive.ofMul (ι x))) := by rw [hJg]
      _ = ((((τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ
            (J *ᵥ φ (Additive.ofMul (ι x)))) := by rw [Matrix.mulVec_mulVec]
      _ = (((((e.trans (szEquiv a)) (QuotientGroup.mk h) : ↥(Sz a)) : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ Multiplicative.toAdd (ψ x) := rfl
  exact ⟨e.trans (szEquiv a), c, ψ, hsurj, hker, heq⟩

theorem str83G4_exists_mem_of_mem_suzukiZ0
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K)
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K) :
    ∀ z ∈ suzukiZ0 a K, ∃ c : ↥(L1 ⊔ S), (c : G) ∈ C ∧ e (QuotientGroup.mk c) = z := by
  classical
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hpc : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  have hCS : C ≤ S := fun s hs =>
    ((hC s).mp ((le_sup_left : C ≤ C ⊔ Q1 L1 L2 S) hs)).1
  have hCH : C ≤ L1 ⊔ S := hCS.trans le_sup_right
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  intro z hz
  have hzU : z ∈ suzukiU a K := suzukiZ0_le_suzukiU hz
  have hzS : z ∈ (szSbar L1 L2 S).map e.toMonoidHom := by rw [he]; exact hzU
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzS
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hyz' : e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) s) = z := hyz
  have hz2 : z * z = 1 := by
    have := (mem_suzukiZ0_iff_sq_eq_one hK).mp hz
    simpa [pow_two] using this.2
  have hs2 : (s : G) ^ 2 ∈ Q1 L1 L2 S := by
    have hqm : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) (s * s) =
        QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) s *
          QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) s := map_mul _ s s
    have hsq : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) (s * s) = 1 := by
      apply e.injective
      rw [hqm, map_mul, hyz', hz2, map_one]
    have hmem : s * s ∈ pCore 2 ↥(L1 ⊔ S) :=
      (QuotientGroup.eq_one_iff (s * s)).mp hsq
    have hmemG : ((s * s : ↥(L1 ⊔ S)) : G) ∈ pCoreOf 2 (L1 ⊔ S) :=
      (F1.mem_pCore_iff_coe (s * s)).mp hmem
    rw [hpc] at hmemG
    simpa [pow_two] using hmemG
  have hsmem : (s : G) ∈ C ⊔ Q1 L1 L2 S := (hC (s : G)).mpr ⟨hsS, hs2⟩
  have hsmem' : s ∈ (C ⊔ Q1 L1 L2 S).subgroupOf (L1 ⊔ S) :=
    Subgroup.mem_subgroupOf.mpr hsmem
  have hmapC : ((C ⊔ Q1 L1 L2 S).subgroupOf (L1 ⊔ S)).map
        (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) =
      (C.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) := by
    rw [Subgroup.subgroupOf_sup hCH hQ1H, Subgroup.map_sup]
    have hbot : ((Q1 L1 L2 S).subgroupOf (L1 ⊔ S)).map
        (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      change QuotientGroup.mk q = 1
      rw [QuotientGroup.eq_one_iff]
      exact (F1.mem_pCore_iff_coe q).mpr (hpc ▸ Subgroup.mem_subgroupOf.mp hq)
    rw [hbot, sup_bot_eq]
  have hπs : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) s ∈
      (C.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) := by
    rw [← hmapC]
    exact Subgroup.mem_map_of_mem _ hsmem'
  obtain ⟨c, hcC, hcπ⟩ := Subgroup.mem_map.mp hπs
  refine ⟨c, Subgroup.mem_subgroupOf.mp hcC, ?_⟩
  change e (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) c) = z
  rw [hcπ]
  exact hyz'

theorem str83G4_exists_sectionSetup
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) L N)
    (hZ1L : Z1 L1 L2 S ≤ L)
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N) :
    ∃ (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
      (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
      (hNL : N ≤ Subgroup.normalizer (L : Set G))
      (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
      (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
      (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1))),
      (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1)) ∧
      (letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
       letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
       ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1) := by
  classical
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := hXQ1.trans (hQ1S.trans le_sup_right)
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hXH).trans hHL
  have hXp : IsPGroup 2 (str83X L1 L2 S) :=
    (str83G4_isSylowTwoOf_sup_left hfr).2.1.to_le (hXQ1.trans hQ1S)
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hXH hXp
  have hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
    rw [str83G4_pCoreOf_sup_left hfr]
    intro q hq
    have hqH : q ∈ L1 ⊔ S := (hQ1S.trans le_sup_right) hq
    refine ⟨hqH, hHL hqH, fun n hn => hZ1L ?_⟩
    have h1 : ⁅q, n⁆ ∈ ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ :=
      Subgroup.commutator_mem_commutator hq (hstep.1.1 hn)
    rw [Subgroup.commutator_comm] at h1
    exact str83G4_commutator_x_q1_le hfr h1
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  have hnt : ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1 := by
    obtain ⟨y, hyR, hyC⟩ := SetLike.not_le_iff_exists.mp hnc
    have hyH : y ∈ L1 ⊔ S := twoResidual_le _ hyR
    obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, y * n * y⁻¹ * n⁻¹ ∉ L := by
      by_contra hall
      push Not at hall
      exact hyC ⟨hyH, hHL hyH, hall⟩
    refine ⟨e (QuotientGroup.mk ⟨y, hyH⟩), fun h1 => hn ?_⟩
    have hyn : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hyH) n).mp hnN
    have h2 := LinearMap.congr_fun h1 (Additive.ofMul (Ch3z.chiefIota hNL ⟨n, hnN⟩))
    rw [sectionRep_chiefIota _ _ _ _ _ _ ⟨y, hyH⟩ ⟨n, hnN⟩ hyn, Module.End.one_apply] at h2
    have h3 : Ch3z.chiefIota hNL (⟨y * n * y⁻¹, hyn⟩ * (⟨n, hnN⟩ : ↥N)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Additive.ofMul.injective h2
    exact (Ch3z.chiefIota_eq_one_iff hNL _).1 h3
  exact ⟨hHL, hHN, hNL, hE, hO, e, he, hnt⟩

theorem sectionRep_isSzNatural_of_quadratic_chiefStep
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    {U L N : Subgroup G} (hUH : U ≤ L1 ⊔ S)
    (hquad : ⁅⁅N, C⁆, C⁆ ≤ L)
    (hstep : IsChiefStep (L1 ⊔ S) U L N)
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1)))
    (hnt : letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
      ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    IsSzNatural (sectionRep hHL hHN hNL hE hO e) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  have ha : 1 ≤ a := hfr.2.2.1
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod L N)) :=
    sectionRep hHL hHN hNL hE hO e
  haveI : Fact ρ.IsIrreducible :=
    ⟨sectionRep_isIrreducible hstep hUH hHL hHN hNL hE hO e⟩
  have hZ0lift := str83G4_exists_mem_of_mem_suzukiZ0 hfr hC hK e he
  have hZ0quad : ∀ z' ∈ suzukiZ0 a K, ∀ z ∈ suzukiZ0 a K,
      (ρ z' - 1) ∘ₗ (ρ z - 1) = 0 := by
    intro z' hz' z hz
    obtain ⟨s, hsC, hse⟩ := hZ0lift z' hz'
    obtain ⟨c, hcC, hce⟩ := hZ0lift z hz
    have hqc : ∀ n ∈ N, (c : G) * n * (c : G)⁻¹ * n⁻¹ ∈ ⁅N, C⁆ := by
      intro n hn
      have h1 : ⁅(c : G), n⁆ ∈ ⁅C, N⁆ :=
        Subgroup.commutator_mem_commutator hcC hn
      rwa [Subgroup.commutator_comm] at h1
    have hqs : ∀ y ∈ ⁅N, C⁆, (s : G) * y * (s : G)⁻¹ * y⁻¹ ∈ L := by
      intro y hy
      have h1 : ⁅(s : G), y⁆ ∈ ⁅C, ⁅N, C⁆⁆ :=
        Subgroup.commutator_mem_commutator hsC hy
      rw [Subgroup.commutator_comm] at h1
      exact hquad h1
    have h := sectionRep_comp_sub_one_eq_zero (Y := ⁅N, C⁆)
      hHL hHN hNL hE hO e c s hqc hqs
    simpa [ρ, hse, hce] using h
  have hquad' : CFSG.QuasithinUnique.Setup.X7.commSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) ≤
      CFSG.QuasithinUnique.Setup.X7.fixedSub ρ
        (CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (szZ a K)) := by
    rw [conjSubgroup_weyl_szZ]
    exact CFSG.QuasithinUnique.Setup.X7.commSub_le_fixedSub hZ0quad
  exact isSzNatural_of_commSub_le_fixedSub hK ha ρ hnt (suzukiWElt a K) hquad'

theorem sectionRep_isSzNatural_of_quadratic
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    (hquad : ⁅⁅str83X L1 L2 S, C⁆, C⁆ = ⊥)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) L N)
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1)))
    (hnt : letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
      ∃ g, sectionRep hHL hHN hNL hE hO e g ≠ 1) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    IsSzNatural (sectionRep hHL hHN hNL hE hO e) := by
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S :=
    (str83X_le_q1 hfr).trans ((str83G4_q1_le_s hfr).trans le_sup_right)
  have hquadN : ⁅⁅N, C⁆, C⁆ ≤ L := by
    have h : ⁅⁅N, C⁆, C⁆ ≤ ⁅⁅str83X L1 L2 S, C⁆, C⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hstep.1.1 le_rfl) le_rfl
    rw [hquad] at h
    exact h.trans bot_le
  exact sectionRep_isSzNatural_of_quadratic_chiefStep hfr hC hXH hquadN hstep hHL hHN hNL hE hO
    e he hnt

theorem str83G4_isSzNaturalSection_of_quadratic
    {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {C : Subgroup G}
    (hC : ∀ s : G, s ∈ C ⊔ Q1 L1 L2 S ↔ s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S)
    (hquad : ⁅⁅str83X L1 L2 S, C⁆, C⁆ = ⊥)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) L N)
    (hZ1L : Z1 L1 L2 S ≤ L)
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N) :
    IsSzNaturalSection (L1 ⊔ S) N L a := by
  obtain ⟨hHL, hHN, hNL, hE, hO, e, he, hnt⟩ :=
    str83G4_exists_sectionSetup hfr hstep hZ1L hnc
  have hnat := sectionRep_isSzNatural_of_quadratic hfr hC hquad hstep hHL hHN hNL hE hO e he hnt
  exact isSzNaturalSection_of_isSzNatural hHL hHN hNL hE hO e hnat

end CFSG.Quasithin.Stroth

end
