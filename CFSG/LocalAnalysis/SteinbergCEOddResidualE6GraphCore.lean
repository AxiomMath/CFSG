module

public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LocalAnalysis.SteinbergCAOddResidualOrderFacts

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace E6GraphCoset

open E6SignedGraph

abbrev e4 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩

theorem perm_e4 : TwistTag.E6.perm e4 = e4 := by decide

variable {K : Type} [Field K]

theorem xUnit_e4_commute_diagramMap
    (c : K) :
    xUnit TwistTag.E6.tag K e4 c * diagramMap TwistTag.E6 K =
      diagramMap TwistTag.E6 K * xUnit TwistTag.E6.tag K e4 c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_xUnit, diagramMap_mul_xOp, perm_e4]

theorem yUnit_e4_commute_diagramMap
    (c : K) :
    yUnit TwistTag.E6.tag K e4 c * diagramMap TwistTag.E6 K =
      diagramMap TwistTag.E6 K * yUnit TwistTag.E6.tag K e4 c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_yUnit, diagramMap_mul_yOp, perm_e4]

theorem signTuple_e4 : signTuple K e4 = 1 :=
  rfl

theorem xUnit_e4_commute_signDiag
    (c : K) :
    xUnit TwistTag.E6.tag K e4 c * rootDiagUnit TwistTag.E6.tag (signTuple K) =
      rootDiagUnit TwistTag.E6.tag (signTuple K) * xUnit TwistTag.E6.tag K e4 c := by
  refine Units.ext ?_
  change xOp TwistTag.E6.tag K e4 c * rootDiag (signTuple K) =
    rootDiag (signTuple K) * xOp TwistTag.E6.tag K e4 c
  rw [rootDiag_mul_xOp, signTuple_e4, Units.val_one, one_mul]

theorem yUnit_e4_commute_signDiag
    (c : K) :
    yUnit TwistTag.E6.tag K e4 c * rootDiagUnit TwistTag.E6.tag (signTuple K) =
      rootDiagUnit TwistTag.E6.tag (signTuple K) * yUnit TwistTag.E6.tag K e4 c := by
  refine Units.ext ?_
  change yOp TwistTag.E6.tag K e4 c * rootDiag (signTuple K) =
    rootDiag (signTuple K) * yOp TwistTag.E6.tag K e4 c
  rw [rootDiag_mul_yOp, signTuple_e4, inv_one, Units.val_one, one_mul]

theorem simpleRootSL2_e4_mem
    {A : ModGL TwistTag.E6.tag K}
    (hA : A = diagramMap TwistTag.E6 K ∨
      A = rootDiagUnit TwistTag.E6.tag (signTuple K) * diagramMap TwistTag.E6 K) (s : SL2 K) :
    simpleRootSL2 TwistTag.E6.tag K e4 s ∈
      (posUnipotent TwistTag.E6.tag K ⊓ graphCentralizer TwistTag.E6.tag K A) ⊔
        (negUnipotent TwistTag.E6.tag K ⊓ graphCentralizer TwistTag.E6.tag K A) := by
  have hcomm : ∀ u : ModGL TwistTag.E6.tag K, u * diagramMap TwistTag.E6 K =
      diagramMap TwistTag.E6 K * u → u * rootDiagUnit TwistTag.E6.tag (signTuple K) =
        rootDiagUnit TwistTag.E6.tag (signTuple K) * u → u * A = A * u := by
    intro u hP hd
    rcases hA with rfl | rfl
    · exact hP
    · rw [← mul_assoc, hd, mul_assoc, hP, mul_assoc]
  have h : (simpleRootSL2 TwistTag.E6.tag K e4).range ≤
      (posUnipotent TwistTag.E6.tag K ⊓ graphCentralizer TwistTag.E6.tag K A) ⊔
        (negUnipotent TwistTag.E6.tag K ⊓ graphCentralizer TwistTag.E6.tag K A) := by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨xUnit_mem_posUnipotent e4 c,
        Subgroup.mem_inf.2 ⟨xUnit_mem_adjointGroup e4 c, ?_⟩⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm _ (xUnit_e4_commute_diagramMap c) (xUnit_e4_commute_signDiag c)
    · refine Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨yUnit_mem_negUnipotent e4 c,
        Subgroup.mem_inf.2 ⟨yUnit_mem_adjointGroup e4 c, ?_⟩⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm _ (yUnit_e4_commute_diagramMap c) (yUnit_e4_commute_signDiag c)
  exact h ⟨s, rfl⟩

theorem map_conj_map_conj {G : Type*} [Group G] (L : Subgroup G) (u w : G) :
    (L.map (MulAut.conj w).toMonoidHom).map (MulAut.conj u).toMonoidHom =
      L.map (MulAut.conj (u * w)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

abbrev graphRational (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (e ε : ℕ) :
    Subgroup (ModGL TwistTag.E6.tag k) :=
  fixedPointsIn (adjointGroup TwistTag.E6.tag k)
    (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))

abbrev graphCosetFixed (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (e ε : ℕ)
    (x : ModGL TwistTag.E6.tag k) : Subgroup (ModGL TwistTag.E6.tag k) :=
  ⁅graphRational k p e ε, graphRational k p e ε⁆ ⊓
    Subgroup.centralizer {x * diagramMap TwistTag.E6 k}

theorem exists_conj_eq_rationalRootGroup
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (ε : ℕ)
    (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {r : ℕ} (hr : r.Prime)
    {L : Subgroup (ModGL TwistTag.E6.tag k)} (hLX : L ≤ graphCosetFixed k p e ε x)
    (hL : CFSG.IsPComponent r (L.subgroupOf (graphCosetFixed k p e ε x))) :
    ∃ (AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)))
      (c : ModGL TwistTag.E6.tag k),
      (AK = diagramMap TwistTag.E6 _ ∨
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) ∧
      L.map (MulAut.conj c).toMonoidHom = rationalRootGroup (iterateFrobeniusEquiv k p e) AK := by
  classical
  set P := diagramMap TwistTag.E6 k with hPdef
  set F := frobTwistGL TwistTag.E6.tag k p e (P ^ ε) with hFdef
  set G := adjointGroup TwistTag.E6.tag k with hGdef
  set R := graphRational k p e ε with hRdef
  obtain ⟨hfin, -, -, hnode⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  obtain ⟨⟨y, hyR, hyA⟩, -⟩ := hnode x hx hx2
  obtain ⟨A, hAdef⟩ : ∃ A, y * (x * P) * y⁻¹ = A := ⟨_, rfl⟩
  have hAform : A = P ∨ A = rootDiagUnit TwistTag.E6.tag (signTuple k) * P := hAdef ▸ hyA
  have hyA' : y * (x * P) * y⁻¹ = A := hAdef
  obtain ⟨hyG, hFy⟩ := Subgroup.mem_inf.1 hyR
  have hFy' : F y = y := hFy
  set B := R ⊓ Subgroup.centralizer {x * P} with hBdef
  set J := frobFixedCentralizer TwistTag.E6.tag p e A (P ^ ε) with hJdef
  have hHR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_self R
  have hBR : B ≤ R := inf_le_left
  have : Finite R := hfin
  have : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective hBR)
  have : (⁅R, R⁆.subgroupOf R).Normal := commutator_subgroupOf_normal R
  have : Group.IsSolvable (R ⧸ ⁅R, R⁆.subgroupOf R) := isSolvable_quotient_commutator_subgroupOf R
  have : ((⁅R, R⁆ ⊓ B).subgroupOf B).Normal := normal_inf_subgroupOf hBR
  have : Group.IsSolvable (B ⧸ (⁅R, R⁆ ⊓ B).subgroupOf B) := isSolvable_quotient_inf_subgroupOf hBR
  have hHB : ⁅R, R⁆ ⊓ B = graphCosetFixed k p e ε x := by
    rw [hBdef, ← inf_assoc, inf_eq_left.2 hHR]
  have hBJ : B.map (MulAut.conj y).toMonoidHom = J := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨hbR, hbc⟩ := Subgroup.mem_inf.1 hb
      obtain ⟨hbG, hbF⟩ := Subgroup.mem_inf.1 hbR
      have hbF' : F b = b := hbF
      rw [Subgroup.mem_centralizer_singleton_iff] at hbc
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hyG hbG) (inv_mem hyG), ?_⟩,
        ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hyA']
        calc y * b * y⁻¹ * (y * (x * P) * y⁻¹) = y * (b * (x * P)) * y⁻¹ := by group
          _ = y * ((x * P) * b) * y⁻¹ := by rw [hbc]
          _ = y * (x * P) * y⁻¹ * (y * b * y⁻¹) := by group
      · change F (y * b * y⁻¹) = y * b * y⁻¹
        rw [map_mul, map_mul, map_inv, hFy', hbF']
    · intro hw
      obtain ⟨hwZ, hwF⟩ := Subgroup.mem_inf.1 hw
      obtain ⟨hwG, hwc⟩ := Subgroup.mem_inf.1 hwZ
      have hwF' : F w = w := hwF
      rw [Subgroup.mem_centralizer_singleton_iff] at hwc
      refine ⟨y⁻¹ * w * y, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
        ⟨mul_mem (mul_mem (inv_mem hyG) hwG) hyG, ?_⟩, ?_⟩, ?_⟩
      · change F (y⁻¹ * w * y) = y⁻¹ * w * y
        rw [map_mul, map_mul, map_inv, hFy', hwF']
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hxP : x * P = y⁻¹ * A * y := by rw [← hyA']; group
        rw [hxP]
        calc y⁻¹ * w * y * (y⁻¹ * A * y) = y⁻¹ * (w * A) * y := by group
          _ = y⁻¹ * (A * w) * y := by rw [hwc]
          _ = y⁻¹ * A * y * (y⁻¹ * w * y) := by group
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have h1 : L ≤ ⁅R, R⁆ ⊓ B ∧ CFSG.IsPComponent r (L.subgroupOf (⁅R, R⁆ ⊓ B)) := by
    rw [hHB]
    exact ⟨hLX, hL⟩
  have h2 := (isPComponent_subgroupOf_iff_of_isSolvable inf_le_right r hr L).2 h1
  have h3 := (isPComponent_subgroupOf_map_conj_iff y hBJ r hr L).1 h2
  obtain ⟨AK, hAK⟩ : ∃ AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)),
      (A = diagramMap TwistTag.E6 k ∧ AK = diagramMap TwistTag.E6 _) ∨
      (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k ∧
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) := by
    rcases hAform with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  have hAKform : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _ := by
    rcases hAK with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨-, hfinJ, hSle, hSn, hab, hSq, hP1, hD1⟩ :=
    E6_canonical_graph_centralizer_rational_fixed_components p hp he k A AK hAK
  set J₀ := frobFixedCentralizer TwistTag.E6.tag p e A (P ^ 0) with hJ₀def
  set S := rationalRootGroup (iterateFrobeniusEquiv k p e) AK with hSdef
  have : Finite J₀ := (hfinJ 0 (by simp)).1
  obtain ⟨c, hc⟩ : ∃ c : ModGL TwistTag.E6.tag k, L.map (MulAut.conj c).toMonoidHom ≤ J₀ ∧
      CFSG.IsPComponent r ((L.map (MulAut.conj c).toMonoidHom).subgroupOf J₀) := by
    rcases hε with rfl | rfl
    · exact ⟨y, h3⟩
    · rcases hAK with ⟨hA, -⟩ | ⟨hA, -⟩
      · have hJJ : J = J₀ := hP1 hA
        rw [hJJ] at h3
        exact ⟨y, h3⟩
      · obtain ⟨v, -, hv⟩ := hD1 hA
        have : Finite J := (hfinJ 1 (by simp)).1
        have h4 := (isPComponent_subgroupOf_map_conj_iff v hv r hr _).1 h3
        rw [map_conj_map_conj] at h4
        exact ⟨v * y, h4⟩
  have : (S.subgroupOf J₀).Normal := hSn
  have : Group.IsSolvable (J₀ ⧸ S.subgroupOf J₀) := Group.isSolvable_of_comm fun a b => hab a b
  have hNq : CFSG.IsQuasisimple (S.subgroupOf J₀) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hSle)).2 hSq
  have heq := (pComponent_eq_of_quasisimple_normal r hr (S.subgroupOf J₀) hNq _ hc.2).1
  refine ⟨AK, c, hAKform, ?_⟩
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hc.1, inf_eq_left.2 hSle] at heq
  exact heq

theorem neg_one_ne_one_SL2 {K : Type} [Field K] (hK : ringChar K ≠ 2) : (-1 : SL2 K) ≠ 1 :=
  fun h => by
    have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp at h1
    exact Ring.neg_one_ne_one_of_char_ne_two hK h1

@[expose] def e4RootSL2
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : ℕ) :
    SL2 (fixSubfield (iterateFrobeniusEquiv k p e)) →* ModGL TwistTag.E6.tag k :=
  (baseChangeGL (fixSubfield (iterateFrobeniusEquiv k p e)).subtype).comp
    (simpleRootSL2 TwistTag.E6.tag _ e4)

theorem e4RootSL2_injective
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectRing k p] (hp : p ≠ 2) (e : ℕ) : Function.Injective (e4RootSL2 k p e) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  exact (baseChangeGL_injective _).comp
    (simpleRootSL2_injective (ringChar_fixSubfield_ne_two hk _) e4)

theorem e4RootSL2_mem_rationalRootGroup
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectRing k p] (e : ℕ)
    {AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e))}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _)
    (s : SL2 (fixSubfield (iterateFrobeniusEquiv k p e))) :
    e4RootSL2 k p e s ∈ rationalRootGroup (iterateFrobeniusEquiv k p e) AK :=
  ⟨_, simpleRootSL2_e4_mem hAK s, rfl⟩

end E6GraphCoset

open E6GraphCoset in
theorem E6_graph_coset_fixed_no_normal_even_SL2
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (ε : ℕ)
    (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) (S : Subgroup (graphCosetFixed k p e ε x))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (K : Type)
    [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  obtain ⟨hfin, -⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  have : Finite (graphRational k p e ε) := hfin
  have hXR : graphCosetFixed k p e ε x ≤ graphRational k p e ε :=
    inf_le_left.trans (Subgroup.commutator_le_self _)
  have : Finite (graphCosetFixed k p e ε x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hXR)
  have hS2 := SteinbergCA.isPComponent_two_of_mulEquiv_SL2 S hSn hSs hSnab eS
  set L := S.map (graphCosetFixed k p e ε x).subtype with hLdef
  have hLX : L ≤ graphCosetFixed k p e ε x := Subgroup.map_subtype_le S
  have hLsub : L.subgroupOf (graphCosetFixed k p e ε x) = S :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) S
  obtain ⟨AK, c, hAK, hc⟩ := exists_conj_eq_rationalRootGroup p hp he k halg ε hε hx hx2
    Nat.prime_two hLX (hLsub ▸ hS2)
  have : CharP (fixSubfield (iterateFrobeniusEquiv k p e)) p :=
    (fixSubfield (iterateFrobeniusEquiv k p e)).subtype.charP Subtype.val_injective p
  have hinj := e4RootSL2_injective k p hp e
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  let e₁ : S ≃* L := S.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L ≃* L.map (MulAut.conj c).toMonoidHom :=
    L.equivMapOfInjective _ (MulAut.conj c).injective
  refine SteinbergCA.false_of_mulEquiv_SL2_of_hom ((e₁.trans e₂).symm.trans eS) hp
    (e4RootSL2 k p e) (fun s => hc ▸ e4RootSL2_mem_rationalRootGroup k p e hAK s) ?_ ?_
  · rw [← map_one (e4RootSL2 k p e)]
    exact fun h => neg_one_ne_one_SL2 (ringChar_fixSubfield_ne_two hk _) (hinj h)
  · rw [← map_one (e4RootSL2 k p e)]
    exact fun h => SteinbergCA.uSL_one_ne_one_and_ne_neg_one.1 (hinj h)

end CFSG.LocalAnalysis.SteinbergCE
