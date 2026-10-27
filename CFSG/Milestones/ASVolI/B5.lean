module

public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Vol2.Ch3B513NHolds
public import CFSG.Quasithin.Background.SmithD321SQ
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.Quasithin.EmptyFaithful.S14113bFStar

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

@[expose] def IsB55Group (L : Type) [Group L] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥(StatedSL 2 K))) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥(StatedSL 3 K))) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥⁅StatedSp 2 K, StatedSp 2 K⁆)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆)) ∨
  IsAlt 7 L ∨ IsHat L ↥(alternatingGroup (Fin 6)) ∨
  Nonempty (L ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (L ≃* ↥(StatedSL 5 (ZMod 2)))

section MinimalCounterexample

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B56PieceOnU (Gi : Subgroup (MulAut V)) (U Wi C : Subgroup V) : Prop :=
  (Wi = modComm Gi U ⊔ C ∧
    ((∃ n, BinaryNaturalSL Gi Wi C 2 n) ∨ SymmetricNatural Gi Wi C 5 ∨
      (∃ m, BinaryNaturalSL Gi Wi C 3 m))) ∨
  (Wi = modComm Gi U ⊔ C ∧ ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      DirectSumOfCopies Gi Wi C (FFModel.nat (StatedSL 3 K)) 2) ∨
  (Nonempty (↥Gi ≃* ↥(StatedSL 3 (ZMod 2))) ∧ modComm Gi U ≤ Wi ∧
    Nat.card ↥Wi = 2 ^ 4 * Nat.card ↥C ∧
    (¬ ∃ A B : Subgroup V, C < A ∧ C < B ∧ XMod.IsInv ↥Gi A ∧ XMod.IsInv ↥Gi B ∧
      A ⊔ B = Wi ∧ A ⊓ B = C) ∧
    BinaryNaturalSL Gi (modComm Gi Wi ⊔ C) C 3 1)

@[expose] def IsG1 (A L G₁ : Subgroup (MulAut V)) : Prop :=
  (B59Case2 A L ∧ G₁ = L ⊔ A) ∨ (¬ B59Case2 A L ∧ G₁ = L)

@[expose] def IsExceptionalG1 (L G₁ : Subgroup (MulAut V)) : Prop :=
  BinaryNaturalSL G₁ (commV L) ⊥ 3 1 ∧ (commV L ⊔ fixV G₁).index = 2

end MinimalCounterexample

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsQuotientOfSQTK G →
    ∃ (Gh : Type) (_ : Group Gh) (_ : Finite Gh) (α : Gh →* G),
      Function.Surjective α ∧ CFSG.SectionRank.IsSQTKCat Gh ∧
      Group.IsNilpotent ↥((CFSG.fittingSubgroup G).comap α) ∧
      (Group.IsNilpotent ↥α.ker ∧ Odd (Nat.card ↥α.ker)) ∧
      (∀ L : Subgroup G, IsComponentOf L ⊤ → ∃ Lh : Subgroup Gh, IsComponentOf Lh ⊤ ∧ L = Lh.map α) ∧
      genFittingFStar G = (genFittingFStar Gh).map α

section BurnsideB5b2

private theorem burnsideB5b_eq_top_of_sup_le_frattini {H : Type*} [Group H] [Finite H] {A K :
    Subgroup H}
    (hK : K ≤ frattini H) (h : A ⊔ K = ⊤) : A = ⊤ :=
  frattini_nongenerating (top_le_iff.mp (h ▸ sup_le_sup_left hK A))

private theorem burnsideB5b_nilpotent_comap_of_ker_le_frattini {H Q : Type*} [Group H] [Finite H]
    [Group Q] (ψ : H →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ frattini H)
    {F : Subgroup Q} [F.Normal] (hF : Group.IsNilpotent ↥F) :
    Group.IsNilpotent ↥(F.comap ψ) := by
  classical
  haveI := hF
  haveI : Finite Q := Finite.of_surjective ψ hψ
  set M := F.comap ψ with hM
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance ψ
  refine ((Group.isNilpotent_of_finite_tfae (G := ↥M)).out 1 4).mpr ?_
  intro p hp P
  let f : ↥M →* ↥F :=
    { toFun := fun x => ⟨ψ x, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, hh⟩ := hψ y
    refine ⟨⟨h, ?_⟩, ?_⟩
    · rw [hM, Subgroup.mem_comap, hh]; exact y.2
    · apply Subtype.ext
      simpa [f] using hh
  have hPbar : (P.mapSurjective hf : Subgroup ↥F).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := ↥F)).out 1 4 rfl rfl).mp hF p hp (P.mapSurjective hf)
  have hN₂ : ((P : Subgroup ↥M).map f).comap f |>.Normal := by
    rw [← Sylow.coe_mapSurjective hf P]
    exact Subgroup.Normal.comap hPbar f
  have hPN₂ : (P : Subgroup ↥M) ≤ ((P : Subgroup ↥M).map f).comap f := Subgroup.le_comap_map f _
  haveI := hN₂
  have h1 := Sylow.normalizer_sup_eq_top' P hPN₂
  have h1' := Sylow.normalizer_sup_eq_top P
  have h2 : Subgroup.normalizer (P : Set ↥M) ⊔ f.ker = ⊤ := by
    have hle : ((P : Subgroup ↥M).map f).comap f ≤ Subgroup.normalizer (P : Set ↥M) ⊔ f.ker := by
      rw [Subgroup.comap_map_eq]
      exact sup_le (le_sup_of_le_left Subgroup.le_normalizer) le_sup_right
    exact top_le_iff.mp (h1 ▸ sup_le le_sup_left hle)
  have h3 : Subgroup.normalizer (((P : Subgroup ↥M).map M.subtype : Subgroup H) : Set H) ⊔
      ψ.ker = ⊤ := by
    refine top_le_iff.mp fun h _ => ?_
    have hmem : h ∈ Subgroup.normalizer (((P : Subgroup ↥M).map M.subtype : Subgroup H) : Set H) ⊔
        M := by
      rw [h1']
      exact Subgroup.mem_top h
    obtain ⟨n, hn, m, hm, hnm⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hmem2 : (⟨m, hm⟩ : ↥M) ∈ Subgroup.normalizer (P : Set ↥M) ⊔ f.ker := by
      rw [h2]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, k, hk, hak⟩ := Subgroup.mem_sup_of_normal_right.mp hmem2
    have hkψ : (k : H) ∈ ψ.ker := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      simpa [f] using this
    have haN : (a : H) ∈ Subgroup.normalizer
        (((P : Subgroup ↥M).map M.subtype : Subgroup H) : Set H) :=
      Subgroup.le_normalizer_map M.subtype (Subgroup.mem_map_of_mem _ ha)
    have hh : h = (n * a) * k := by
      rw [← hnm, mul_assoc]
      congr 1
      exact (congrArg Subtype.val hak).symm
    rw [hh]
    exact Subgroup.mul_mem_sup (mul_mem hn haN) hkψ
  have h4 := burnsideB5b_eq_top_of_sup_le_frattini hker h3
  have hP'n : ((P : Subgroup ↥M).map M.subtype).Normal := Subgroup.normalizer_eq_top_iff.mp h4
  exact hP'n.of_map_subtype

private theorem burnsideB5b_odd_card_map_mk {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    [K.Normal]
    [Group.IsNilpotent K] :
    Odd (Nat.card ↥(K.map (QuotientGroup.mk' (K ⊓ CFSG.pCore 2 H)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  obtain ⟨x, hx, hxz⟩ := z.2
  have hz2 : (z : H ⧸ (K ⊓ CFSG.pCore 2 H)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hz1 : (z : H ⧸ (K ⊓ CFSG.pCore 2 H)) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hxP : x ∉ K ⊓ CFSG.pCore 2 H := by
    intro h
    apply hz1
    rw [← hxz]
    exact (QuotientGroup.eq_one_iff x).2 h
  have hx2 : x ^ 2 ∈ K ⊓ CFSG.pCore 2 H := by
    have h1 : (QuotientGroup.mk' (K ⊓ CFSG.pCore 2 H)) (x ^ 2) = 1 := by
      rw [map_pow, hxz, hz2]
    exact (QuotientGroup.eq_one_iff (x ^ 2)).1 h1
  have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨x ^ 2, hx2.2⟩
  rw [Subgroup.orderOf_mk] at hk
  set y : ↥K := ⟨x, hx⟩ with hy
  have hyx : orderOf y = orderOf x := Subgroup.orderOf_mk x hx
  have hdvd : orderOf x ∣ 2 ^ (k + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    have := pow_orderOf_eq_one (x ^ 2)
    rw [hk, ← pow_mul] at this
    rw [pow_succ, mul_comm]
    exact this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hyx, hm])
  obtain ⟨T, hT⟩ := hZ.exists_le_sylow
  have hTc := Sylow.characteristic_of_normal T inferInstance
  have hle : (T : Subgroup ↥K).map K.subtype ≤ CFSG.pCore 2 H :=
    le_sSup ⟨inferInstance, T.isPGroup'.map _⟩
  have hxT : x ∈ (T : Subgroup ↥K).map K.subtype :=
    Subgroup.mem_map_of_mem K.subtype (hT (Subgroup.mem_zpowers y))
  exact hxP ⟨hx, hle hxT⟩

private theorem burnsideB5b_ker_le_frattini {T Q : Type*} [Group T] [Group Q] (ψ : T →* Q)
    (hψ : Function.Surjective ψ) (hmin : ∀ H : Subgroup T, H.map ψ = ⊤ → H = ⊤) :
    ψ.ker ≤ frattini T := by
  refine le_iInf₂ fun H hH => ?_
  have hH' : IsCoatom H := hH
  by_contra hKH
  have hsup : H ⊔ ψ.ker = ⊤ := hH'.2 _ (left_lt_sup.mpr hKH)
  refine hH'.1 (hmin H (eq_top_iff.mpr fun q _ => ?_))
  obtain ⟨t, rfl⟩ := hψ q
  have ht : t ∈ H ⊔ ψ.ker := hsup ▸ Subgroup.mem_top t
  rw [← Subgroup.comap_map_eq] at ht
  exact ht

private theorem burnsideB5b_exists_cover {G : Type} [Group G] [Finite G]
    (hG : CFSG.Quasithin.IsQuotientOfSQTK G) :
    ∃ (Gh : Type) (_ : Group Gh) (_ : Finite Gh) (α : Gh →* G), Function.Surjective α ∧
      CFSG.SectionRank.IsSQTKCat Gh ∧ Group.IsNilpotent ↥α.ker ∧ Odd (Nat.card ↥α.ker) ∧
      Group.IsNilpotent ↥((CFSG.fittingSubgroup G).comap α) := by
  classical
  obtain ⟨S, _, _, hS, φ₀, hφ₀⟩ := hG
  obtain ⟨S₁, hS₁⟩ := (Set.toFinite {H : Subgroup S | H.map φ₀ = ⊤}).exists_minimal
    ⟨⊤, Subgroup.map_top_of_surjective φ₀ hφ₀⟩
  set ψ : ↥S₁ →* G := φ₀.comp S₁.subtype with hψdef
  have hψ : Function.Surjective ψ := by
    intro q
    have hq : q ∈ S₁.map φ₀ := by rw [hS₁.prop]; exact Subgroup.mem_top q
    obtain ⟨s, hs, rfl⟩ := hq
    exact ⟨⟨s, hs⟩, rfl⟩
  have hmin : ∀ H : Subgroup ↥S₁, H.map ψ = ⊤ → H = ⊤ := by
    intro H hH
    have h1 : (H.map S₁.subtype).map φ₀ = ⊤ := by rw [Subgroup.map_map]; exact hH
    have h2 : H.map S₁.subtype = S₁ := hS₁.eq_of_le h1 (Subgroup.map_subtype_le H)
    refine Subgroup.map_injective S₁.subtype_injective ?_
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfr : ψ.ker ≤ frattini ↥S₁ := burnsideB5b_ker_le_frattini ψ hψ hmin
  have hKnil : Group.IsNilpotent ↥ψ.ker := by
    have : Group.IsNilpotent ↥(frattini ↥S₁) := frattini_nilpotent
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hfr)
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  haveI := hKnil
  set P := ψ.ker ⊓ CFSG.pCore 2 ↥S₁ with hP
  have hPK : P ≤ ψ.ker := inf_le_left
  have hP2 : IsPGroup 2 ↥P := (CFSG.pCore_isPGroup (p := 2) (G := ↥S₁)).to_le inf_le_right
  let α : (↥S₁ ⧸ P) →* G := QuotientGroup.lift P ψ hPK
  have hα : Function.Surjective α := by
    intro q
    obtain ⟨s, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk s, rfl⟩
  have hαker : α.ker = ψ.ker.map (QuotientGroup.mk' P) := QuotientGroup.ker_lift P ψ hPK
  refine ⟨↥S₁ ⧸ P, inferInstance, inferInstance, α, hα, ?_, ?_, ?_, ?_⟩
  · exact ⟨(CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff P hP2).2
      (hS.subgroup S₁).1, (hS.subgroup S₁).2.quotient P⟩
  · rw [hαker]
    exact Group.nilpotent_of_surjective ((QuotientGroup.mk' P).subgroupMap ψ.ker)
      (MonoidHom.subgroupMap_surjective _ _)
  · rw [hαker]
    exact burnsideB5b_odd_card_map_mk ψ.ker
  · have hF : Group.IsNilpotent ↥((CFSG.fittingSubgroup G).comap ψ) :=
      burnsideB5b_nilpotent_comap_of_ker_le_frattini ψ hψ hfr (inferInstance)
    have hψα : ψ = α.comp (QuotientGroup.mk' P) := by ext x; rfl
    have hcomap : ((CFSG.fittingSubgroup G).comap ψ).map (QuotientGroup.mk' P) =
        (CFSG.fittingSubgroup G).comap α := by
      have h1 : (CFSG.fittingSubgroup G).comap ψ =
          ((CFSG.fittingSubgroup G).comap α).comap (QuotientGroup.mk' P) := by
        rw [Subgroup.comap_comap]
        exact congrArg (fun f : ↥S₁ →* G => (CFSG.fittingSubgroup G).comap f) hψα
      rw [h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective P)]
    rw [← hcomap]
    exact Group.nilpotent_of_surjective
      ((QuotientGroup.mk' P).subgroupMap ((CFSG.fittingSubgroup G).comap ψ))
      (MonoidHom.subgroupMap_surjective _ _)

private theorem burnsideB5b_component_mod_fitting {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.IsComponent L) :
    (∀ x ∈ L ⊓ CFSG.fittingSubgroup G, ∀ l ∈ L, x * l = l * x) ∧
      IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.fittingSubgroup G))) ∧
      ∃ a b : ↥(L.map (QuotientGroup.mk' (CFSG.fittingSubgroup G))), a * b ≠ b * a := by
  classical
  set F := CFSG.fittingSubgroup G with hF
  have hLle : L ≤ CFSG.layer G := CFSG.LocalCores.component_le_layer hL
  have ha : ∀ x ∈ L ⊓ F, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    have h1 : F ≤ Subgroup.centralizer (CFSG.layer G : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LocalCores.fitting_layer_commute (G := G))
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx.2) l (hLle hl)).symm
  have hb : ∀ x ∈ L, (∀ l ∈ L, l * x = x * l) → x ∈ F := by
    intro x hx hcen
    have hxc : x ∈ Subgroup.centralizer (CFSG.layer G : Set G) :=
      CFSG.WholeGroup.mem_centralizer_layer_of_mem_component hL hx hcen
    refine CFSG.WholeGroup.center_layer_le_fittingSubgroup ⟨⟨x, hLle hx⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (g : G) g.2)
  let π : G →* G ⧸ F := QuotientGroup.mk' F
  let f : ↥L →* ↥(L.map π) := π.subgroupMap L
  have hf : Function.Surjective f := π.subgroupMap_surjective L
  have hker : f.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h l
      have hxF : (x : G) ∈ F := (QuotientGroup.eq_one_iff (x : G)).1 (congrArg Subtype.val h)
      exact Subtype.ext (ha x ⟨x.2, hxF⟩ l l.2).symm
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : G)).2
        (hb x x.2 fun l hl => congrArg Subtype.val (h ⟨l, hl⟩))
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥(L.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨ha, ?_, ?_⟩
  · have := hL.1.2.1
    exact MulEquiv.isSimpleGroup e.symm
  · obtain ⟨a, b, hab⟩ := hL.1.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

open scoped commutatorElement in
private theorem burnsideB5b_lift_component {G Gh : Type} [Group G] [Finite G] [Group Gh] [Finite Gh]
    (α : Gh →* G) (hα : Function.Surjective α) (hSQT : CFSG.IsStronglyQuasithin Gh)
    (hnil : Group.IsNilpotent ↥α.ker) (hodd : Odd (Nat.card ↥α.ker))
    (hM : Group.IsNilpotent ↥((CFSG.fittingSubgroup G).comap α))
    {L : Subgroup G} (hL : IsComponentOf L ⊤) :
    ∃ Lh : Subgroup Gh, IsComponentOf Lh ⊤ ∧ Lh.map α = L := by
  classical
  have hLC : CFSG.IsComponent L :=
    ⟨CFSG.Quasithin.B1Red.isQuasisimple_of_open hL.2.2,
      CFSG.Quasithin.A3.subnormal_top_iff.mp hL.2.1⟩
  have hLc : L ∈ CFSG.Quasithin.cComp (⊤ : Subgroup G) :=
    CFSG.Quasithin.mem_cComp_top_of_isComponent hLC
  have hsolv : Group.IsSolvable ↥α.ker := by
    have := hnil
    infer_instance
  obtain ⟨Lh, hLh, hmap⟩ := CFSG.Quasithin.map_surjOn_cComp_top α hα hsolv hLc
  refine ⟨Lh, ?_, hmap⟩
  set F := CFSG.fittingSubgroup G with hF
  obtain ⟨hcentL, hsimpL, hnabL⟩ := burnsideB5b_component_mod_fitting hLC
  let π : G →* G ⧸ F := QuotientGroup.mk' F
  let ρ : Gh →* G ⧸ F := π.comp α
  have hρker : ρ.ker = F.comap α := by
    ext x
    simp [ρ, π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  haveI hMn : (F.comap α).Normal := Subgroup.Normal.comap inferInstance α
  haveI := hM
  set N := (F.comap α) ⊓ CFSG.pCore 2 Gh with hN
  have hNM : N ≤ ρ.ker := by rw [hρker]; exact inf_le_left
  have hN2 : IsPGroup 2 ↥N := (CFSG.pCore_isPGroup (p := 2) (G := Gh)).to_le inf_le_right
  haveI : N.Normal := inferInstance
  let ρ' : (Gh ⧸ N) →* G ⧸ F := QuotientGroup.lift N ρ hNM
  have hρ'ker : ρ'.ker = (F.comap α).map (QuotientGroup.mk' N) := by
    rw [QuotientGroup.ker_lift N ρ hNM, hρker]
  have hnil' : Group.IsNilpotent ↥ρ'.ker := by
    rw [hρ'ker]
    exact Group.nilpotent_of_surjective ((QuotientGroup.mk' N).subgroupMap (F.comap α))
      (MonoidHom.subgroupMap_surjective _ _)
  have hodd' : Odd (Nat.card ↥ρ'.ker) := by
    rw [hρ'ker]
    exact burnsideB5b_odd_card_map_mk (F.comap α)
  have hSQT' : CFSG.IsStronglyQuasithin (Gh ⧸ N) :=
    (CFSG.SectionRank.isStronglyQuasithin_quotient_two_group_iff N hN2).2 hSQT
  have hperf : Group.IsPerfect ↥Lh :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfect_of_mem_cComp hLh)
  have hperf' : Group.IsPerfect ↥(Lh.map (QuotientGroup.mk' N)) := by
    refine Subgroup.isPerfect_iff.2 ?_
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]
  have hLρ : Lh.map ρ = L.map π := by
    show Lh.map (π.comp α) = _
    rw [← Subgroup.map_map, hmap]
  have hcomp : ρ'.comp (QuotientGroup.mk' N) = ρ := QuotientGroup.lift_comp_mk' N ρ hNM
  have hmapρ : (Lh.map (QuotientGroup.mk' N)).map ρ' = L.map π := by
    rw [Subgroup.map_map, hcomp, hLρ]
  have hsimp' : IsSimpleGroup ↥((Lh.map (QuotientGroup.mk' N)).map ρ') := by
    rw [hmapρ]; exact hsimpL
  have hcent' := CFSG.Quasithin.SmithD321.comm_of_mem_inf_ker hSQT' ρ' hnil' hodd' hperf' hsimp'
  have hcent : ∀ k ∈ Lh ⊓ ρ.ker, ∀ l ∈ Lh, k * l = l * k := by
    intro k hk l hl
    have hk1 : (QuotientGroup.mk' N k) ∈ Lh.map (QuotientGroup.mk' N) ⊓ ρ'.ker :=
      ⟨Subgroup.mem_map_of_mem _ hk.1, hk.2⟩
    have h2 := hcent' _ hk1 _ (Subgroup.mem_map_of_mem _ hl)
    have hcN : ⁅k, l⁆ ∈ N := by
      have h3 : (QuotientGroup.mk' N) ⁅k, l⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 h2
      exact (QuotientGroup.eq_one_iff _).1 h3
    have hαk : α k ∈ L ⊓ F := by
      refine ⟨hmap ▸ Subgroup.mem_map_of_mem α hk.1, ?_⟩
      have h4 : π (α k) = 1 := hk.2
      exact (QuotientGroup.eq_one_iff _).1 h4
    have hαl : α l ∈ L := hmap ▸ Subgroup.mem_map_of_mem α hl
    have hcα : ⁅k, l⁆ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcentL _ hαk _ hαl)
    have hc1 : ⁅k, l⁆ = 1 := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := Gh)))
        ⟨⁅k, l⁆, hcN.2⟩
      rw [Subgroup.orderOf_mk] at hj
      have hd : orderOf ⁅k, l⁆ ∣ Nat.card α.ker := by
        have := orderOf_dvd_natCard (⟨⁅k, l⁆, hcα⟩ : ↥α.ker)
        rwa [Subgroup.orderOf_mk] at this
      have hoddc : Odd (orderOf ⁅k, l⁆) := Odd.of_dvd_nat hodd hd
      rw [hj] at hoddc
      rcases j with _ | j
      · rw [pow_zero] at hj
        exact orderOf_eq_one_iff.1 hj
      · exact absurd hoddc (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, j.succ_ne_zero⟩))
    exact commutatorElement_eq_one_iff_mul_comm.1 hc1
  have hnab : ∃ a b : ↥(Lh.map ρ), a * b ≠ b * a := by
    rw [hLρ]; exact hnabL
  have hsimp : IsSimpleGroup ↥(Lh.map ρ) := by
    rw [hLρ]; exact hsimpL
  have hLq : CFSG.IsQuasisimple ↥Lh :=
    CFSG.Quasithin.SmithD321.isQuasisimple_of_comm_ker ρ hperf hsimp hnab hcent
  exact ⟨le_top, CFSG.Quasithin.subnormal_of_mem_cComp hLh,
    CFSG.Quasithin.B1Red.isQuasisimple_to_open hLq⟩

private theorem burnsideB5b_genFitting_map {G Gh : Type} [Group G] [Finite G] [Group Gh] [Finite Gh]
    (α : Gh →* G) (hα : Function.Surjective α)
    (hM : Group.IsNilpotent ↥((CFSG.fittingSubgroup G).comap α))
    (hlift : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ∃ Lh : Subgroup Gh, IsComponentOf Lh ⊤ ∧ Lh.map α = L) :
    genFittingFStar G = (genFittingFStar Gh).map α := by
  classical
  rw [genFittingFStar.eq_sup, genFittingFStar.eq_sup, Subgroup.map_sup]
  have hF : genFittingFitting G = (genFittingFitting Gh).map α := by
    show CFSG.fittingSubgroup G = (CFSG.fittingSubgroup Gh).map α
    apply le_antisymm
    · have hnorm : ((CFSG.fittingSubgroup G).comap α).Normal :=
        Subgroup.Normal.comap inferInstance α
      have h1 : (CFSG.fittingSubgroup G).comap α ≤ CFSG.fittingSubgroup Gh :=
        (CFSG.LocalCores.fitting_characteristic).2.2 _ hnorm hM
      calc CFSG.fittingSubgroup G = ((CFSG.fittingSubgroup G).comap α).map α :=
            (Subgroup.map_comap_eq_self_of_surjective hα _).symm
        _ ≤ _ := Subgroup.map_mono h1
    · have hn : ((CFSG.fittingSubgroup Gh).map α).Normal :=
        Subgroup.Normal.map inferInstance α hα
      have hnil : Group.IsNilpotent ↥((CFSG.fittingSubgroup Gh).map α) :=
        Group.nilpotent_of_surjective (α.subgroupMap (CFSG.fittingSubgroup Gh))
          (MonoidHom.subgroupMap_surjective _ _)
      exact (CFSG.LocalCores.fitting_characteristic).2.2 _ hn hnil
  have hE : genFittingLayer G = (genFittingLayer Gh).map α := by
    have hEG : genFittingLayer G = sSup {L : Subgroup G | IsComponentOf L ⊤} := rfl
    have hEGh : genFittingLayer Gh = sSup {L : Subgroup Gh | IsComponentOf L ⊤} := rfl
    apply le_antisymm
    · rw [hEG]
      refine sSup_le fun L hL => ?_
      obtain ⟨Lh, hLh, rfl⟩ := hlift L hL
      exact Subgroup.map_mono (hEGh ▸ le_sSup hLh)
    · rw [hEGh, Subgroup.map_le_iff_le_comap]
      refine sSup_le fun Lh hLh => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      by_cases hker : Lh ≤ α.ker
      · rw [(Subgroup.map_eq_bot_iff Lh).2 hker]
        exact bot_le
      · have hq : CFSG.IsQuasisimple ↥(Lh.map α) :=
          CFSG.LocalCores.isQuasisimple_map
            (CFSG.Quasithin.B1Red.isQuasisimple_of_open hLh.2.2) α hker
        exact hEG ▸ le_sSup ⟨le_top, CFSG.Quasithin.A3.subnormal_top_map hα hLh.2.1,
          CFSG.Quasithin.B1Red.isQuasisimple_to_open hq⟩
  rw [hF, hE]

end BurnsideB5b2

theorem as_B_5_2 : B_5_2 := by
  intro G _ _ hG
  obtain ⟨Gh, _, _, α, hα, hSQTK, hnil, hodd, hM⟩ := burnsideB5b_exists_cover hG
  have hlift : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ∃ Lh : Subgroup Gh, IsComponentOf Lh ⊤ ∧ Lh.map α = L := fun L hL =>
    burnsideB5b_lift_component α hα hSQTK.1 hnil hodd hM hL
  refine ⟨Gh, inferInstance, inferInstance, α, hα, hSQTK, hM, ⟨hnil, hodd⟩, ?_, ?_⟩
  · intro L hL
    obtain ⟨Lh, hLh, hmap⟩ := hlift L hL
    exact ⟨Lh, hLh, hmap.symm⟩
  · exact burnsideB5b_genFitting_map α hα hM hlift

@[expose] def B_5_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), B53Hyp G →
      (∀ L : Subgroup (MulAut V), IsComponentOf L G →
        (L.subgroupOf G).Normal ∧
        ((∃ A, IsFFStarOffender G A ∧ ⁅L, A⁆ = L) ∧
          ∀ A, IsFFStarOffender G A → ⁅L, A⁆ = L →
            L ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = ⊥ ∧
            A ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = A ⊓ Subgroup.centralizer (L : Set (MulAut V)) ∧
            IsFFStarOffender (autSub G (fixV (pCoreOf 2 (L ⊔ A))))
              (autSub A (fixV (pCoreOf 2 (L ⊔ A))))) ∧
        (∃ A, IsFFStarOffender G A ∧ ⁅L, A⁆ = L ∧ ∃ X Y : Subgroup V, Y < X ∧
          (∀ a ∈ A, a ∈ stabSub X ∧ a ∈ stabSub Y) ∧ (∀ l ∈ L, l ∈ stabSub X ∧ l ∈ stabSub Y) ∧
          XMod.IsIrrSec ↥L Y X ∧ (∀ l ∈ L, ActsTrivOnSection l X Y → l = 1) ∧
          quasithinGenFitting (ChB.autSec (L ⊔ A) X Y) = ChB.autSec L X Y ∧
          (∃ B, B ≤ ChB.autSec A X Y ∧ IsFFStarOffender (ChB.autSec (L ⊔ A) X Y) B) ∧
          B42ModulePair L X Y) ∧
        IsB55Group ↥L) ∧
      ((∀ p : ℕ, p.Prime → p ≠ 3 → pCoreOf p G ≤ centerOf G) ∧
        quasithinGenFitting G = layerOf G ⊔ pCoreOf 3 G ⊔ centerOf G)

section BurnsideB55

open CFSG.Quasithin in
open scoped commutatorElement in
private theorem burnsideB55_B55_i_ii {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} (hB : B53Hyp G) {L : Subgroup (MulAut V)}
    (hL : IsComponentOf L G) :
    (L.subgroupOf G).Normal ∧
      ((∃ A, IsFFStarOffender G A ∧ ⁅L, A⁆ = L) ∧
        ∀ A, IsFFStarOffender G A → ⁅L, A⁆ = L →
          L ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = ⊥ ∧
          A ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = A ⊓ Subgroup.centralizer (L : Set (MulAut V)) ∧
          IsFFStarOffender (autSub G (fixV (pCoreOf 2 (L ⊔ A))))
            (autSub A (fixV (pCoreOf 2 (L ⊔ A))))) := by
  have hP4 := B15P4.asB15Part4
  have hn := B55.normalizes_comp hP4 hV hB.2.1 hL
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).mpr hn,
    B55.exists_offender hP4 hV hB.2.1 hL, fun A hA hLA => ?_⟩
  exact B55.faithful_on_fixV hV hB.1 hL hA hLA

private theorem burnsideB55_fit_eq_map {M : Type*} [Group M] [Finite M] (G : Subgroup M) :
    sSup {N : Subgroup M | N ≤ G ∧ (N.subgroupOf G).Normal ∧ Group.IsNilpotent N} =
      (CFSG.fittingSubgroup ↥G).map G.subtype := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNY, hNn, hNnil⟩ := hN
    have hnil : Group.IsNilpotent (N.subgroupOf G) :=
      (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNY)).mpr hNnil
    calc N = (N.subgroupOf G).map G.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
      _ ≤ _ := Subgroup.map_mono (le_sSup (show N.subgroupOf G ∈
          {c : Subgroup G | c.Normal ∧ Group.IsNilpotent c} from ⟨hNn, hnil⟩))
  · show Subgroup.map G.subtype (sSup {N : Subgroup ↥G | N.Normal ∧ Group.IsNilpotent N}) ≤ _
    rw [(Subgroup.gc_map_comap G.subtype).l_sSup]
    refine iSup₂_le fun c hc => ?_
    obtain ⟨hcn, hcnil⟩ := hc
    refine le_sSup ?_
    refine ⟨Subgroup.map_subtype_le c, ?_, ?_⟩
    · have e : (c.map G.subtype).subgroupOf G = c :=
        Subgroup.comap_map_eq_self_of_injective G.subtype_injective c
      rw [e]
      exact hcn
    · exact (Group.isNilpotent_congr (c.equivMapOfInjective G.subtype G.subtype_injective)).mp
        hcnil

open CFSG.Quasithin in
private theorem burnsideB55_B55_two {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} (hB : B53Hyp G) :
    (∀ p : ℕ, p.Prime → p ≠ 3 → pCoreOf p G ≤ centerOf G) ∧
      quasithinGenFitting G = ChB.layerOf G ⊔ pCoreOf 3 G ⊔ centerOf G := by
  have h1 : ∀ p : ℕ, p.Prime → p ≠ 3 → pCoreOf p G ≤ centerOf G := by
    intro p hp hp3
    by_cases hp2 : p = 2
    · subst hp2
      rw [hB.1]
      exact bot_le
    · haveI : Fact p.Prime := ⟨hp⟩
      exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le p G)
        (B55.pCoreOf_le_centralizer hV hB.2.1 hp2 hp3)
  refine ⟨h1, ?_⟩
  have hfit := burnsideB55_fit_eq_map G
  have hF3 : pCoreOf 3 G ≤ (CFSG.fittingSubgroup ↥G).map G.subtype := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Subgroup.map_mono (CFSG.pCore_le_fitting ↥G 3)
  have hFZ : centerOf G ≤ (CFSG.fittingSubgroup ↥G).map G.subtype := by
    intro x hx
    have hcN : Subgroup.center ↥G ≤ CFSG.fittingSubgroup ↥G :=
      le_sSup (show Subgroup.center ↥G ∈ {N : Subgroup ↥G | N.Normal ∧ Group.IsNilpotent N} from
        ⟨inferInstance, inferInstance⟩)
    refine ⟨⟨x, hx.1⟩, hcN (Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp hx.2) (g : MulAut V) g.2)), rfl⟩
  have hFle : (CFSG.fittingSubgroup ↥G).map G.subtype ≤ pCoreOf 3 G ⊔ centerOf G := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp3 : (p : ℕ) = 3
    · have : (CFSG.pCore (p : ℕ) ↥G).map G.subtype = pCoreOf 3 G := by rw [hp3]; rfl
      exact this ▸ le_sup_left
    · exact (h1 p hp hp3).trans le_sup_right
  unfold quasithinGenFitting
  rw [hfit]
  have hE : ChB.layerOf G = sSup {K | IsComponentOf K G} := rfl
  rw [hE]
  apply le_antisymm
  · exact sup_le (hFle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
      (le_sup_left.trans le_sup_left)
  · exact sup_le (sup_le le_sup_right (hF3.trans le_sup_left)) (hFZ.trans le_sup_left)

private theorem burnsideB55_equiv_commutator {X M : Type*} [Group X] [Group M] (hX :
    Group.IsPerfect X)
    (S : Subgroup M) (e : X ≃* ↥S) : Nonempty (X ≃* ↥⁅S, S⁆) := by
  have hS : Group.IsPerfect ↥S := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.1 hS
  exact ⟨e.trans (MulEquiv.subgroupCongr h.symm)⟩

noncomputable def burnsideB55_commutatorEquiv {M : Type*} [Group M] (S : Subgroup M) :
    commutator ↥S ≃* ↥⁅S, S⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥S) S.subtype S.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]))

private theorem burnsideB55_isB55Group_of_list {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : CFSG.Quasithin.B56QuasisimpleList X) : ChB.IsB55Group X := by
  rcases h with ⟨n, K, hK, hf, hc, he⟩ | ⟨n, K, hK, hf, hc, he⟩ | ⟨n, K, hK, hf, hc, ⟨e⟩⟩ |
    ⟨n, K, hK, hf, hc, ⟨e⟩⟩ | h5 | h6 | h7 | ⟨K, hK, hf, hc, ⟨e⟩⟩ | h9 | h10
  · exact Or.inl ⟨n, K, hK, hf, hc, he⟩
  · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc,
      burnsideB55_equiv_commutator hq.1 (StatedSp 2 K) e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc,
      burnsideB55_equiv_commutator hq.1 (CFSG.Open.quasithinG2 K) e⟩)))
  · obtain ⟨e⟩ := h5
    have hk : Nat.card (ZMod 2) = 2 := by simp
    exact Or.inr (Or.inr (Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, by simpa using hk,
      ⟨e.trans ((CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hk).symm.trans
        (burnsideB55_commutatorEquiv (StatedSp 2 (ZMod 2))))⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1, K, hK, hf, by simpa using hc, ⟨e⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h10))))))

open CFSG.Quasithin in
private theorem burnsideB55_B55_iv (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} (hb : B53Hyp G) {K : Subgroup (MulAut V)}
    (hK : IsComponentOf K G) : ChB.IsB55Group ↥K := by
  obtain ⟨A, hA, hKA⟩ := B55.exists_offender hP4 hV hb.2.1 hK
  obtain ⟨-, -, -, hst, -, -⟩ := FFC.B59.red_basic hV hK hA hKA
  have hKU : K ≤ stabSub (FFC.B59.W0 K A) := le_sup_left.trans hst
  have hfaith : ∀ g ∈ K, (∀ v ∈ FFC.B59.W0 K A, g v = v) → g = 1 := by
    have h0 : K ⊓ centSub (FFC.B59.W0 K A) = ⊥ := (B55.faithful_on_fixV hV hb.1 hK hA hKA).1
    intro g hg hgW
    have hmem : g ∈ K ⊓ centSub (FFC.B59.W0 K A) := ⟨hg, hgW⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  have hb51 := FFC.B59.b51Hyp_red hA21 hV hb.1 hb hK hA hKA
  have hVM : ∀ v : ↥(FFC.B59.W0 K A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  have hc := hB51 ↥(FFC.B59.W0 K A) hVM (FFC.B59.Xr K A) (FFC.B59.Kr K A) hb51
  have hlist := FFC.b56List_of_b51 hc
  have hlistK := FFC.B56QuasisimpleList.of_mulEquiv (FFC.resEquiv hKU hfaith) hlist
  exact burnsideB55_isB55Group_of_list (B1Red.isQuasisimple_of_open hK.2.2) hlistK

open CFSG.Quasithin in
private theorem burnsideB55_isIrrSec_iff {V : Type*} [CommGroup V] {K : Subgroup (MulAut V)}
    {U W : Subgroup V} :
    XMod.IsIrrSec ↥K U W ↔ U < W ∧ ∀ J : Subgroup V, (∀ x ∈ K, ∀ w ∈ J, x w ∈ J) →
      U ≤ J → J ≤ W → J = U ∨ J = W := by
  unfold XMod.IsIrrSec XMod.IsInv
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun J hJ => h2 J (fun a l hl => hJ a a.2 l hl)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun J hJ => h2 J (fun x hx w hw => hJ ⟨x, hx⟩ w hw)⟩

@[expose] noncomputable def burnsideB55_transvection {d : ℕ} {K : Type} [Field K]
    (i j : Fin d) (hij : i ≠ j) (c : K) : ↥(StatedSL d K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero),
    Subgroup.subset_closure (by
      show (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c) _ :
        Matrix.GeneralLinearGroup (Fin d) K).val.det = 1
      simp [Matrix.det_transvection_of_ne i j hij])⟩

private theorem burnsideB55_transvection_val {d : ℕ} {K : Type} [Field K] (i j : Fin d) (hij :
    i ≠ j)
    (c : K) :
    (((burnsideB55_transvection i j hij c : ↥(StatedSL d K)) :
      Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.transvection i j c := rfl

private theorem burnsideB55_nat_irr_core {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
    (J : AddSubgroup (Fin d → K))
    (hJ : ∀ g : ↥(StatedSL d K), ∀ x ∈ J,
      (((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec x) ∈ J)
    {x₀ : Fin d → K} (hx₀ : x₀ ∈ J) (hne : x₀ ≠ 0) (y : Fin d → K) : y ∈ J := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x₀ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have key : ∀ (i j : Fin d) (hij : i ≠ j) (c : K) (x : Fin d → K), x ∈ J →
      (Pi.single i (c * x j) : Fin d → K) ∈ J := by
    intro i j hij c x hx
    have h1 := hJ (burnsideB55_transvection i j hij c) x hx
    rw [burnsideB55_transvection_val] at h1
    have h2 : (Matrix.transvection i j c).mulVec x = x + Pi.single i (c * x j) := by
      rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
      congr 1
    rw [h2] at h1
    simpa using J.sub_mem h1 hx
  have hne_j : ∀ i, i ≠ j → ∀ c : K, (Pi.single i c : Fin d → K) ∈ J := by
    intro i hij c
    have := key i j hij (c / x₀ j) x₀ hx₀
    rwa [div_mul_cancel₀ _ hj] at this
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨i', hi'⟩ := exists_ne j
  have hj_single : ∀ c : K, (Pi.single j c : Fin d → K) ∈ J := by
    intro c
    have := key j i' hi'.symm c (Pi.single i' 1) (hne_j i' hi' 1)
    simpa using this
  have hsingle : ∀ (k : Fin d) (c : K), (Pi.single k c : Fin d → K) ∈ J := by
    intro k c
    by_cases hk : k = j
    · subst hk; exact hj_single c
    · exact hne_j k hk c
  have hy : y = ∑ k, (Pi.single k (y k) : Fin d → K) := (Finset.univ_sum_single y).symm
  rw [hy]
  exact AddSubgroup.sum_mem _ (fun k _ => hsingle k (y k))

open CFSG.Quasithin in
private theorem burnsideB55_nat_section {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {W : Subgroup V} {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
    {π : ↥(StatedSL d K) →* ↥H}
    (h : (FFModel.nat (StatedSL d K)).RealizesVia H W ⊥ π) :
    ⊥ < W ∧ (∀ J : Subgroup V, (∀ x ∈ H, ∀ w ∈ J, x w ∈ J) → ⊥ ≤ J → J ≤ W → J = ⊥ ∨ J = W) ∧
      ∀ l ∈ H, (∀ w ∈ W, l w = w) → l = 1 := by
  classical
  obtain ⟨hsurj, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let q : (Fin d → K) → (↥(FFModel.nat (StatedSL d K)).sec ⧸
      (FFModel.nat (StatedSL d K)).ker.subgroupOf (FFModel.nat (StatedSL d K)).sec) :=
    fun x => QuotientGroup.mk ⟨Multiplicative.ofAdd x, trivial⟩
  have hq1 : ∀ x : Fin d → K, q x = 1 ↔ x = 0 := by
    intro x
    show (QuotientGroup.mk _ : _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd x ∈ (⊥ : Subgroup (Multiplicative (Fin d → K))) ↔ _
    rw [Subgroup.mem_bot]
    exact ofAdd_eq_one
  have hqmul : ∀ x y : Fin d → K, q x * q y = q (x + y) := by
    intro x y
    show (QuotientGroup.mk _ : _) * QuotientGroup.mk _ = QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul]
    rfl
  have hqinv : ∀ x : Fin d → K, (q x)⁻¹ = q (-x) := by
    intro x
    show (QuotientGroup.mk _ : _)⁻¹ = QuotientGroup.mk _
    rw [← QuotientGroup.mk_inv]
    rfl
  have hq0 : q 0 = 1 := (hq1 0).2 rfl
  have hqsurj : ∀ s : (↥(FFModel.nat (StatedSL d K)).sec ⧸
      (FFModel.nat (StatedSL d K)).ker.subgroupOf (FFModel.nat (StatedSL d K)).sec),
      ∃ x, q x = s := by
    intro s
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨Multiplicative.toAdd m.1, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    refine lt_of_le_of_ne bot_le fun hW => ?_
    obtain ⟨u, hu⟩ := hβs (q (Pi.single ⟨0, by omega⟩ 1))
    have hu1 : u = 1 := by
      apply Subtype.ext
      have h1 : (u : V) ∈ (⊥ : Subgroup V) := (SetLike.ext_iff.1 hW (u : V)).2 u.2
      exact Subgroup.mem_bot.1 h1
    rw [hu1, map_one] at hu
    have h2 := congrFun ((hq1 _).1 hu.symm) ⟨0, by omega⟩
    simp at h2
  · intro J hJ hbot hJW
    let J₀ : AddSubgroup (Fin d → K) :=
      { carrier := {x | ∃ u : ↥W, (u : V) ∈ J ∧ β u = q x}
        zero_mem' := ⟨1, J.one_mem, by rw [map_one, hq0]⟩
        add_mem' := by
          rintro x y ⟨u, hu, hux⟩ ⟨u', hu', hu'y⟩
          exact ⟨u * u', J.mul_mem hu hu', by rw [map_mul, hux, hu'y, hqmul]⟩
        neg_mem' := by
          rintro x ⟨u, hu, hux⟩
          exact ⟨u⁻¹, J.inv_mem hu, by rw [map_inv, hux, hqinv]⟩ }
    have hJ₀ : ∀ g : ↥(StatedSL d K), ∀ x ∈ J₀,
        (((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec x) ∈ J₀ := by
      rintro g x ⟨u, hu, hux⟩
      have hu' : ((π g : ↥H) : MulAut V) (u : V) ∈ W := hUinv (π g) (u : V) u.2
      refine ⟨⟨((π g : ↥H) : MulAut V) (u : V), hu'⟩, hJ _ (π g).2 _ hu, ?_⟩
      exact hβe g u ⟨Multiplicative.ofAdd x, trivial⟩ hu' (hsec g _ trivial) hux
    by_cases hnz : ∃ x₀ ∈ J₀, x₀ ≠ 0
    · right
      obtain ⟨x₀, hx₀, hne⟩ := hnz
      refine le_antisymm hJW fun w hw => ?_
      obtain ⟨y, hy⟩ := hqsurj (β ⟨w, hw⟩)
      obtain ⟨u, hu, hβu⟩ := burnsideB55_nat_irr_core hd J₀ hJ₀ hx₀ hne y
      have h1 : β (u⁻¹ * ⟨w, hw⟩) = 1 := by
        rw [map_mul, map_inv, hβu, hy, inv_mul_cancel]
      have h2 := (hβk _).1 h1
      have h3 : (u : V)⁻¹ * w = 1 := Subgroup.mem_bot.1 h2
      have h4 : (u : V) = w := by
        have := mul_eq_one_iff_eq_inv.1 h3
        simpa using this
      rw [← h4]
      exact hu
    · left
      push Not at hnz
      refine le_antisymm (fun v hv => ?_) hbot
      obtain ⟨y, hy⟩ := hqsurj (β ⟨v, hJW hv⟩)
      have hy0 : y = 0 := hnz y ⟨⟨v, hJW hv⟩, hv, hy.symm⟩
      rw [hy0, hq0] at hy
      exact (hβk _).1 hy.symm
  · intro l hl hlW
    obtain ⟨γ, hγ⟩ := hsurj ⟨l, hl⟩
    have hπl : ((π γ : ↥H) : MulAut V) = l := congrArg Subtype.val hγ
    have hγ1 : γ = (1 : ↥(StatedSL d K)) := by
      refine FFModel.nat_faithful _ γ fun m hm => ?_
      obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
      have hmem : ((π γ : ↥H) : MulAut V) (u : V) ∈ W := hUinv (π γ) (u : V) u.2
      have h1 := hβe γ u ⟨m, hm⟩ hmem (hsec γ m hm) hu
      have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ : ↥W) = u := by
        apply Subtype.ext
        show ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
        rw [hπl]
        exact hlW _ u.2
      have e : β ⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ = β u := congrArg β h2
      have h5 := hu.symm.trans (e.symm.trans h1)
      have h3 := QuotientGroup.eq.1 h5
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : (m⁻¹ * (FFModel.nat (StatedSL d K)).act γ m) = 1 := by
        exact Subgroup.mem_bot.1 h3
      rw [mul_comm] at h4
      exact Subgroup.mem_bot.2 h4
    have h1 : π γ = π 1 := congrArg π hγ1
    exact congrArg Subtype.val (hγ.symm.trans (h1.trans π.map_one))

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideB55_nat_case {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
    {W : Subgroup V} {d : ℕ} (hd : 2 ≤ d) {F : Type} [Field F] {π : ↥(StatedSL d F) →* ↥K}
    (h : (FFModel.nat (StatedSL d F)).RealizesVia K W ⊥ π) :
    ⊥ < W ∧ K ≤ stabSub W ∧ XMod.IsIrrSec ↥K ⊥ W ∧ K ⊓ centSec W ⊥ = ⊥ := by
  obtain ⟨hne, hirr, hfaith⟩ := burnsideB55_nat_section hd h
  have hUinv := h.2.2.2.1
  refine ⟨hne, ?_, burnsideB55_isIrrSec_iff.2 ⟨hne, hirr⟩, ?_⟩
  · intro g hg
    exact B5.mem_stabSub_of_inv (fun w hw => hUinv ⟨g, hg⟩ w hw)
      (fun w hw => hUinv ⟨g⁻¹, K.inv_mem hg⟩ w hw)
  · rw [eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.2 (hfaith g hg.1 fun w hw => ?_)
    have := hg.2.2 w hw
    rw [Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideB55_core {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hB51 : AsB51) {M K A : Subgroup (MulAut V)} (hH : B51Hyp M K) (hA : IsFFStarOffender M A) :
    ∃ W U : Subgroup V, U < W ∧ M ≤ stabSub W ∧ M ≤ stabSub U ∧ XMod.IsIrrSec ↥K U W ∧
      K ⊓ centSec W U = ⊥ ∧
      (∃ B, B ≤ CFSG.Quasithin.autSec A W U ∧
        IsFFStarOffender (CFSG.Quasithin.autSec M W U) B) ∧
      quasithinGenFitting (CFSG.Quasithin.autSec M W U) = CFSG.Quasithin.autSec K W U ∧
      B42ModulePair K W U := by
  have hc := hB51 V hV M K hH
  obtain ⟨⟨hF, hcases⟩, -⟩ := hc
  have hKM : K ≤ M := B5.le_G hH
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting M) := by rw [hF]; exact B5.quasi_L hH
  have hO2 : pCoreOf 2 M = ⊥ := B5.o2_G hH
  have hnt : Nontrivial ↥K :=
    CFSG.ComponentClassification.Quasisimple.nontrivial
      (B1Red.isQuasisimple_to_open (B5.quasi_L hH))
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 hnt
  suffices hsec : ∃ W U : Subgroup V, U < W ∧ M ≤ stabSub W ∧ M ≤ stabSub U ∧
      XMod.IsIrrSec ↥K U W ∧ K ⊓ centSec W U = ⊥ ∧ B42ModulePair K W U by
    obtain ⟨W, U, hUW, hMW, hMU, hirr, hfaith, hpair⟩ := hsec
    have hS : ¬ commSub W (quasithinGenFitting M) ≤ U := by
      rw [hF]
      intro hle
      have hKc : K ≤ centSec W U := fun k hk =>
        ⟨hMW (hKM hk), fun w hw => hle (Subgroup.subset_closure ⟨k, hk, w, hw, rfl⟩)⟩
      exact hKne (by rw [← hfaith]; exact (inf_eq_left.2 hKc).symm)
    have hfM : M ⊓ centSec W U = ⊥ := by
      have hNK : ¬ quasithinGenFitting M ≤ M ⊓ centSec W U := by
        intro hle
        rw [hF] at hle
        have hKc : K ≤ centSec W U := fun k hk => (hle hk).2
        exact hKne (by rw [← hfaith]; exact (inf_eq_left.2 hKc).symm)
      obtain ⟨h1, -⟩ := B1More.normal_le_center_genFitting (G := M) (N := M ⊓ centSec W U)
        inf_le_left (fun g hg n hn => ⟨M.mul_mem (M.mul_mem hg hn.1) (M.inv_mem hg),
          conj_mem_centSec (hMW hg) (hMU hg) hn.2⟩) hq hNK
      rw [hF] at h1
      rw [eq_bot_iff, ← hfaith]
      exact fun x hx => ⟨h1 hx, hx.2⟩
    refine ⟨W, U, hUW, hMW, hMU, hirr, hfaith, ?_, ?_, hpair⟩
    · obtain ⟨-, hex, -⟩ := B1_5_8 hV hA hUW.le hMW hMU hq hO2 hS
      exact hex
    · exact B5.genFitting_autSec hKM hMW hMU hfM hF
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨hU, hpair, -⟩ := hi
    obtain ⟨-, -, hlt, hirr⟩ := B5.irr_data hU
    have hn := B5.normal_L hH
    rw [inf_comm] at hlt hirr
    refine ⟨commV K, fixV K ⊓ commV K, hlt, B5.le_stabSub_commV hn (fun g hg => M.inv_mem hg),
      B5.le_stabSub_fixV_inf_commV hn (fun g hg => M.inv_mem hg),
      burnsideB55_isIrrSec_iff.2 ⟨hlt, hirr⟩, B5.L_inf_centSec_eq_bot hH hV, hpair⟩
  · obtain ⟨hMK, a, F, hFld, hFfin, hFa, I, π, -, -, hI, -⟩ := hii
    obtain ⟨hne, hKW, hirr, hfaith⟩ := burnsideB55_nat_case (by norm_num : 2 ≤ 3) (hI 0)
    exact ⟨I 0, ⊥, hne, hMK ▸ hKW, fun g _ u => by simp, hirr, hfaith,
      Or.inr (Or.inl ⟨a, F, hFld, hFfin, hFa, π, hI 0⟩)⟩
  · obtain ⟨hMK, hn45, π, U₁, U₂, -, hnat, -⟩ := hiii
    obtain ⟨hne, hKW, hirr, hfaith⟩ := burnsideB55_nat_case
      (by rcases hn45 with rfl | rfl <;> norm_num) hnat
    refine ⟨U₁, ⊥, hne, hMK ▸ hKW, fun g _ u => by simp, hirr, hfaith, ?_⟩
    have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by simp
    rcases hn45 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨ZMod 2, inferInstance, inferInstance, hcard, π, hnat⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, hcard, π, hnat⟩)))))))))))
  · obtain ⟨hMK, n, hn45, k, hk1, -, I, π, -, -, -, hI⟩ := hiv
    obtain ⟨hne, hKW, hirr, hfaith⟩ := burnsideB55_nat_case
      (by rcases hn45 with rfl | rfl <;> norm_num) (hI ⟨0, by omega⟩)
    refine ⟨I ⟨0, by omega⟩, ⊥, hne, hMK ▸ hKW, fun g _ u => by simp, hirr, hfaith, ?_⟩
    have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by simp
    rcases hn45 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨ZMod 2, inferInstance, inferInstance, hcard, π,
          hI ⟨0, by omega⟩⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, hcard, π,
          hI ⟨0, by omega⟩⟩)))))))))))

private theorem burnsideB55_autSec_eq {V : Type*} [CommGroup V] (X : Subgroup (MulAut V))
    {W U : Subgroup V} (hUW : U ≤ W) :
    CFSG.ASVolI.ChB.autSec X W U = CFSG.Quasithin.autSec X W U := by
  ext φ
  constructor
  · rintro ⟨g, hgX, hgW, hgU, h⟩
    rw [CFSG.Quasithin.autSec, CFSG.Quasithin.mem_autQuot]
    have hK : CFSG.Quasithin.resHom W ⟨g, hgW⟩ ∈ CFSG.Quasithin.stabSub (U.subgroupOf W) := by
      rw [CFSG.Quasithin.mem_stabSub]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply]
      exact CFSG.Quasithin.mem_stabSub.1 hgU x
    refine ⟨⟨CFSG.Quasithin.resHom W ⟨g, hgW⟩, hK⟩,
      CFSG.Quasithin.mem_autSub.2 ⟨⟨g, hgW⟩, hgX, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [CFSG.Quasithin.quotHom_mk]
      exact (h w ⟨g w, (CFSG.Quasithin.mem_stabSub.1 hgW w).2 w.2⟩ rfl).symm
  · intro hφ
    obtain ⟨g', hg', rfl⟩ := CFSG.Quasithin.mem_autQuot.1 hφ
    obtain ⟨g₁, hgX, hg₁⟩ := CFSG.Quasithin.mem_autSub.1 hg'
    have hK : ∀ x : W, CFSG.Quasithin.resHom W g₁ x ∈ U.subgroupOf W ↔ x ∈ U.subgroupOf W := by
      intro x
      have := CFSG.Quasithin.mem_stabSub.1 g'.2 x
      rw [← hg₁] at this
      exact this
    have hgU : (g₁ : MulAut V) ∈ CFSG.Quasithin.stabSub U := by
      rw [CFSG.Quasithin.mem_stabSub]
      intro v
      constructor
      · intro hv
        have hvW : v ∈ W := (CFSG.Quasithin.mem_stabSub.1 g₁.2 v).1 (hUW hv)
        have hmem := (hK ⟨v, hvW⟩).1
          (by rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply]; exact hv)
        exact Subgroup.mem_subgroupOf.1 hmem
      · intro hv
        have hvW : v ∈ W := hUW hv
        have hmem := (hK ⟨v, hvW⟩).2 (Subgroup.mem_subgroupOf.2 hv)
        rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply] at hmem
        exact hmem
    refine ⟨g₁, hgX, g₁.2, hgU, ?_⟩
    intro w w' hw
    rw [CFSG.Quasithin.quotHom_mk]
    congr 1
    apply Subtype.ext
    rw [← hg₁, CFSG.Quasithin.resHom_apply]
    exact hw.symm

private theorem burnsideB55_mem_map_subtype {V : Type*} [CommGroup V] {W₀ : Subgroup V}
    (W : Subgroup ↥W₀) (w : ↥W₀) : (w : V) ∈ W.map W₀.subtype ↔ w ∈ W :=
  Subgroup.mem_map_iff_mem W₀.subtype_injective

open CFSG.Quasithin in
private theorem burnsideB55_stabSub_map_iff {V : Type*} [CommGroup V] {W₀ : Subgroup V}
    (W : Subgroup ↥W₀) {g : MulAut V} (hg : g ∈ stabSub W₀) :
    g ∈ stabSub (W.map W₀.subtype) ↔ resHom W₀ ⟨g, hg⟩ ∈ stabSub W := by
  constructor
  · intro h w
    have e1 : ((resHom W₀ ⟨g, hg⟩ w : ↥W₀) : V) = g (w : V) := rfl
    rw [← burnsideB55_mem_map_subtype, e1, h (w : V), burnsideB55_mem_map_subtype]
  · intro h v
    by_cases hv : v ∈ W₀
    · have h1 := h ⟨v, hv⟩
      have e1 : ((resHom W₀ ⟨g, hg⟩ ⟨v, hv⟩ : ↥W₀) : V) = g v := rfl
      have e2 := burnsideB55_mem_map_subtype W (resHom W₀ ⟨g, hg⟩ ⟨v, hv⟩)
      have e3 := burnsideB55_mem_map_subtype W ⟨v, hv⟩
      rw [e1] at e2
      exact e2.trans (h1.trans e3.symm)
    · have hgv : g v ∉ W₀ := fun hh => hv ((hg v).1 hh)
      have hX : ∀ x : V, x ∈ W.map W₀.subtype → x ∈ W₀ := by
        rintro _ ⟨w, -, rfl⟩
        exact w.2
      exact ⟨fun hh => absurd (hX _ hh) hgv, fun hh => absurd (hX _ hh) hv⟩

@[expose] noncomputable def burnsideB55_secEquiv {V : Type*} [CommGroup V] {W₀ : Subgroup V}
    (W U : Subgroup ↥W₀) :
    ↥W ⧸ U.subgroupOf W ≃*
      ↥(W.map W₀.subtype) ⧸ (U.map W₀.subtype).subgroupOf (W.map W₀.subtype) :=
  QuotientGroup.congr (U.subgroupOf W) ((U.map W₀.subtype).subgroupOf (W.map W₀.subtype))
    (W.equivMapOfInjective W₀.subtype W₀.subtype_injective) (by
      ext x
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(w : ↥W₀), hw, rfl⟩
      · intro hx
        obtain ⟨u, hu, hux⟩ := hx
        obtain ⟨w, hw, hwx⟩ := x.2
        have : u = w := W₀.subtype_injective (hux.trans hwx.symm)
        refine ⟨⟨w, hw⟩, ?_, Subtype.ext hwx⟩
        rw [Subgroup.mem_subgroupOf]
        exact this ▸ hu)

open CFSG.Quasithin in
private theorem burnsideB55_autSec_map {V : Type*} [CommGroup V] {W₀ : Subgroup V} (W U :
    Subgroup ↥W₀)
    {N : Subgroup (MulAut V)} (hN : N ≤ stabSub W₀) :
    CFSG.ASVolI.ChB.autSec N (W.map W₀.subtype) (U.map W₀.subtype) =
      (CFSG.ASVolI.ChB.autSec (autSub N W₀) W U).map
        (MulAut.congr (burnsideB55_secEquiv W U)).toMonoidHom := by
  ext φ
  set e := burnsideB55_secEquiv W U with he
  set e₁ := W.equivMapOfInjective W₀.subtype W₀.subtype_injective with he₁
  have hcoe : ∀ w : ↥W, ((e₁ w : ↥(W.map W₀.subtype)) : V) = ((w : ↥W₀) : V) := fun w => rfl
  have hmk : ∀ w : ↥W, e (QuotientGroup.mk w) = QuotientGroup.mk (e₁ w) := fun w => rfl
  constructor
  · rintro ⟨g, hgN, hgX, hgY, hφ⟩
    have hg0 : g ∈ stabSub W₀ := hN hgN
    have hrW := (burnsideB55_stabSub_map_iff W hg0).1 hgX
    have hrU := (burnsideB55_stabSub_map_iff U hg0).1 hgY
    refine ⟨(MulAut.congr e).symm φ, ⟨resHom W₀ ⟨g, hg0⟩, mem_autSub.2 ⟨⟨g, hg0⟩, hgN, rfl⟩,
      hrW, hrU, ?_⟩, ?_⟩
    · intro w w' hww'
      have h1 : ((e₁ w' : ↥(W.map W₀.subtype)) : V) = g ((e₁ w : ↥(W.map W₀.subtype)) : V) := by
        rw [hcoe, hcoe]
        exact congrArg (fun x : ↥W₀ => (x : V)) hww'
      have h2 := hφ (e₁ w) (e₁ w') h1
      show e.symm (φ (e (QuotientGroup.mk w))) = QuotientGroup.mk w'
      rw [hmk, h2, MulEquiv.symm_apply_eq, hmk]
    · exact (MulAut.congr e).apply_symm_apply φ
  · rintro ⟨ψ, ⟨r, hrR, hrW, hrU, hψ⟩, rfl⟩
    obtain ⟨g', hgN, rfl⟩ := mem_autSub.1 hrR
    have hgX : (g' : MulAut V) ∈ stabSub (W.map W₀.subtype) :=
      (burnsideB55_stabSub_map_iff W g'.2).2 hrW
    have hgY : (g' : MulAut V) ∈ stabSub (U.map W₀.subtype) :=
      (burnsideB55_stabSub_map_iff U g'.2).2 hrU
    refine ⟨(g' : MulAut V), hgN, hgX, hgY, ?_⟩
    intro x x' hxx'
    obtain ⟨w, rfl⟩ := e₁.surjective x
    obtain ⟨w', rfl⟩ := e₁.surjective x'
    have hww' : (w' : ↥W₀) = resHom W₀ g' (w : ↥W₀) := by
      apply Subtype.ext
      have := hxx'
      rw [hcoe, hcoe] at this
      exact this
    have h2 := hψ w w' hww'
    show e (ψ (e.symm (QuotientGroup.mk (e₁ w)))) = QuotientGroup.mk (e₁ w')
    have h3 : e.symm (QuotientGroup.mk (e₁ w)) = QuotientGroup.mk w := by
      rw [MulEquiv.symm_apply_eq, hmk]
    rw [h3, h2, hmk]

open CFSG.Quasithin in
private theorem burnsideB55_genFitting_map_equiv {G G' : Type*} [Group G] [Group G'] (σ : G ≃* G')
    (Y : Subgroup G) :
    quasithinGenFitting (Y.map σ.toMonoidHom) = (quasithinGenFitting Y).map σ.toMonoidHom := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype,
    CFSG.Quasithin.quasithinGenFitting_eq_map_subtype]
  set e := Y.equivMapOfInjective σ.toMonoidHom σ.injective
  rw [← CFSG.Quasithin.B5.genFitting_map_equiv e, Subgroup.map_map, Subgroup.map_map]
  congr 1

open CFSG.Quasithin in
private theorem burnsideB55_realizes_transport {V₁ V₂ : Type*} [CommGroup V₁] [CommGroup V₂] {D
    : FFModel}
    {H₁ : Subgroup (MulAut V₁)} {H₂ : Subgroup (MulAut V₂)} {U₁ Z₁ : Subgroup V₁}
    {U₂ Z₂ : Subgroup V₂} (θ : ↥H₁ ≃* ↥H₂) (φ : ↥U₁ →* ↥U₂) (hφs : Function.Surjective φ)
    (hφk : ∀ u : ↥U₁, ((φ u : ↥U₂) : V₂) ∈ Z₂ ↔ (u : V₁) ∈ Z₁)
    (hφe : ∀ (h : ↥H₁) (u : ↥U₁) (hu : (h : MulAut V₁) (u : V₁) ∈ U₁),
      ((φ ⟨(h : MulAut V₁) (u : V₁), hu⟩ : ↥U₂) : V₂) =
        ((θ h : ↥H₂) : MulAut V₂) ((φ u : ↥U₂) : V₂))
    (hZU : Z₁ ≤ U₁) (hU₁ : ∀ h : ↥H₁, ∀ u ∈ U₁, (h : MulAut V₁) u ∈ U₁)
    (hZ₁ : ∀ h : ↥H₁, ∀ z ∈ Z₁, (h : MulAut V₁) z ∈ Z₁) :
    D.Realizes H₂ U₂ Z₂ → D.Realizes H₁ U₁ Z₁ := by
  rintro ⟨π₂, hsurj, hZU₂, hkerle, hU₂, hZ₂, hsec, hkerinv, β₂, hβs, hβk, hβe⟩
  refine ⟨θ.symm.toMonoidHom.comp π₂, θ.symm.surjective.comp hsurj, hZU, hkerle, hU₁, hZ₁, hsec,
    hkerinv, β₂.comp φ, hβs.comp hφs, fun u => ?_, ?_⟩
  · rw [MonoidHom.comp_apply, hβk]
    exact hφk u
  · intro γ u m hu hm hum
    set h : ↥H₁ := θ.symm (π₂ γ) with hh
    have hθh : θ h = π₂ γ := by rw [hh]; exact θ.apply_symm_apply _
    have hu₂ : ((π₂ γ : ↥H₂) : MulAut V₂) ((φ u : ↥U₂) : V₂) ∈ U₂ :=
      hU₂ (π₂ γ) _ (φ u).2
    have hφ' : (φ ⟨(h : MulAut V₁) (u : V₁), hu⟩ : ↥U₂) = ⟨((π₂ γ : ↥H₂) : MulAut V₂)
        ((φ u : ↥U₂) : V₂), hu₂⟩ := by
      apply Subtype.ext
      rw [hφe h u hu, hθh]
    have := hβe γ (φ u) m hu₂ hm hum
    show β₂ (φ ⟨(h : MulAut V₁) (u : V₁), hu⟩) = _
    rw [hφ']
    exact this

open CFSG.Quasithin in
private theorem burnsideB55_b42_transport {V₁ V₂ : Type} [CommGroup V₁] [CommGroup V₂]
    {H₁ : Subgroup (MulAut V₁)} {H₂ : Subgroup (MulAut V₂)} {U₁ Z₁ : Subgroup V₁}
    {U₂ Z₂ : Subgroup V₂}
    (hT : ∀ D : FFModel, D.Realizes H₂ U₂ Z₂ → D.Realizes H₁ U₁ Z₁)
    (h : B42ModulePair H₂ U₂ Z₂) : B42ModulePair H₁ U₁ Z₁ := by
  have tSL : ∀ {d a : ℕ}, BinaryNaturalSL H₂ U₂ Z₂ d a → BinaryNaturalSL H₁ U₁ Z₁ d a := by
    rintro d a ⟨K, hK, hf, hc, hr⟩
    exact ⟨K, hK, hf, hc, hT _ hr⟩
  have tSp : ∀ {a : ℕ}, BinaryNaturalSp4 H₂ U₂ Z₂ a → BinaryNaturalSp4 H₁ U₁ Z₁ a := by
    rintro a ⟨K, hK, hf, hc, hr⟩
    exact ⟨K, hK, hf, hc, hT _ hr⟩
  have tG2 : ∀ {a : ℕ}, G2Natural H₂ U₂ Z₂ a → G2Natural H₁ U₁ Z₁ a := by
    rintro a ⟨K, hK, hf, hc, hr⟩
    exact ⟨K, hK, hf, hc, hT _ hr⟩
  have tG2d : ∀ {a : ℕ}, G2NaturalDerived H₂ U₂ Z₂ a → G2NaturalDerived H₁ U₁ Z₁ a := by
    rintro a ⟨K, hK, hf, hc, hr⟩
    exact ⟨K, hK, hf, hc, hT _ hr⟩
  have tAlt : ∀ {n : ℕ}, AlternatingNatural H₂ U₂ Z₂ n → AlternatingNatural H₁ U₁ Z₁ n :=
    fun h => hT _ h
  have tA7 : A7Four H₂ U₂ Z₂ → A7Four H₁ U₁ Z₁ := by
    rintro ⟨α, hr⟩
    exact ⟨α, hT _ hr⟩
  have tTr : TripleA6Six H₂ U₂ Z₂ → TripleA6Six H₁ U₁ Z₁ := by
    rintro ⟨K, hK, hf, Γ₀, h1, h2, h3, h4, hr⟩
    exact ⟨K, hK, hf, Γ₀, h1, h2, h3, h4, hT _ hr⟩
  have tExt : ∀ {d : ℕ}, SLExteriorTwo H₂ U₂ Z₂ d → SLExteriorTwo H₁ U₁ Z₁ d :=
    fun h => hT _ h
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨n, tSL h⟩
  · exact Or.inr (Or.inl ⟨n, tSL h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, tSp h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, tG2 h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tG2d h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tAlt h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tAlt h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tAlt h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tA7 h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (tTr h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (tSL h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (tSL h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl (tExt h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (tExt h)))))))))))))

open CFSG.Quasithin in
private theorem burnsideB55_isIrrSec_map {V : Type*} [CommGroup V] {W₀ : Subgroup V}
    {L : Subgroup (MulAut V)} {W U : Subgroup ↥W₀}
    (h : XMod.IsIrrSec ↥(autSub L W₀) U W) :
    XMod.IsIrrSec ↥L (U.map W₀.subtype) (W.map W₀.subtype) := by
  rw [burnsideB55_isIrrSec_iff] at h ⊢
  obtain ⟨hlt, hirr⟩ := h
  refine ⟨(Subgroup.map_lt_map_iff_of_injective W₀.subtype_injective).2 hlt,
    fun J hJ hUJ hJW => ?_⟩
  have hJ₀ : J ≤ W₀ := hJW.trans (by rintro _ ⟨w, -, rfl⟩; exact w.2)
  have hJeq : (J.comap W₀.subtype).map W₀.subtype = J :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hJ₀)
  have hU : U ≤ J.comap W₀.subtype := fun u hu => hUJ ⟨u, hu, rfl⟩
  have hW : J.comap W₀.subtype ≤ W := fun j hj => (burnsideB55_mem_map_subtype W j).1 (hJW hj)
  have hinv : ∀ x ∈ autSub L W₀, ∀ w ∈ J.comap W₀.subtype, x w ∈ J.comap W₀.subtype := by
    intro x hx w hw
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.1 hx
    exact hJ g hgL (w : V) hw
  rcases hirr _ hinv hU hW with h1 | h1
  · left
    rw [← hJeq, h1]
  · right
    rw [← hJeq, h1]

open CFSG.Quasithin in
private theorem burnsideB55_transport {V : Type} [CommGroup V] {W₀ : Subgroup V}
    {L A : Subgroup (MulAut V)} (hst : L ⊔ A ≤ stabSub W₀)
    (hfaith : ∀ l ∈ L, (∀ v ∈ W₀, l v = v) → l = 1) {W U : Subgroup ↥W₀} (hUW : U < W)
    (hMW : autSub (L ⊔ A) W₀ ≤ stabSub W) (hMU : autSub (L ⊔ A) W₀ ≤ stabSub U)
    (hirr : XMod.IsIrrSec ↥(autSub L W₀) U W) (hf : autSub L W₀ ⊓ centSec W U = ⊥)
    (hex : ∃ B, B ≤ CFSG.Quasithin.autSec (autSub A W₀) W U ∧
      IsFFStarOffender (CFSG.Quasithin.autSec (autSub (L ⊔ A) W₀) W U) B)
    (hF : quasithinGenFitting (CFSG.Quasithin.autSec (autSub (L ⊔ A) W₀) W U) =
      CFSG.Quasithin.autSec (autSub L W₀) W U)
    (hpair : B42ModulePair (autSub L W₀) W U) :
    ∃ X Y : Subgroup V, Y < X ∧ (∀ a ∈ A, a ∈ stabSub X ∧ a ∈ stabSub Y) ∧
      (∀ l ∈ L, l ∈ stabSub X ∧ l ∈ stabSub Y) ∧ XMod.IsIrrSec ↥L Y X ∧
      (∀ l ∈ L, CFSG.ASVolI.ChB.ActsTrivOnSection l X Y → l = 1) ∧
      quasithinGenFitting (CFSG.ASVolI.ChB.autSec (L ⊔ A) X Y) = CFSG.ASVolI.ChB.autSec L X Y ∧
      (∃ B, B ≤ CFSG.ASVolI.ChB.autSec A X Y ∧
        IsFFStarOffender (CFSG.ASVolI.ChB.autSec (L ⊔ A) X Y) B) ∧ B42ModulePair L X Y := by
  have hL0 : L ≤ stabSub W₀ := le_sup_left.trans hst
  have hA0 : A ≤ stabSub W₀ := le_sup_right.trans hst
  have hUW' := hUW.le
  have hstab : ∀ g ∈ L ⊔ A, g ∈ stabSub (W.map W₀.subtype) ∧ g ∈ stabSub (U.map W₀.subtype) := by
    intro g hg
    have hg0 : g ∈ stabSub W₀ := hst hg
    have hr : resHom W₀ ⟨g, hg0⟩ ∈ autSub (L ⊔ A) W₀ := mem_autSub.2 ⟨⟨g, hg0⟩, hg, rfl⟩
    exact ⟨(burnsideB55_stabSub_map_iff W hg0).2 (hMW hr),
      (burnsideB55_stabSub_map_iff U hg0).2 (hMU hr)⟩
  refine ⟨W.map W₀.subtype, U.map W₀.subtype,
    (Subgroup.map_lt_map_iff_of_injective W₀.subtype_injective).2 hUW,
    fun a ha => hstab a (Subgroup.mem_sup_right ha), fun l hl => hstab l (Subgroup.mem_sup_left hl),
    burnsideB55_isIrrSec_map hirr, ?_, ?_, ?_, ?_⟩
  ·
    intro l hl hact
    have hl0 : l ∈ stabSub W₀ := hL0 hl
    have hrK : resHom W₀ ⟨l, hl0⟩ ∈ autSub L W₀ := mem_autSub.2 ⟨⟨l, hl0⟩, hl, rfl⟩
    have hrW : resHom W₀ ⟨l, hl0⟩ ∈ stabSub W := hMW (autSub_mono le_sup_left W₀ hrK)
    have hrc : resHom W₀ ⟨l, hl0⟩ ∈ centSec W U := by
      refine ⟨hrW, fun w hw => ?_⟩
      have h1 := hact (w : V) ((burnsideB55_mem_map_subtype W w).2 hw)
      have e1 : (((resHom W₀ ⟨l, hl0⟩ w * w⁻¹ : ↥W₀)) : V) = l (w : V) * (w : V)⁻¹ := rfl
      exact (burnsideB55_mem_map_subtype U _).1 (by rw [e1]; exact h1)
    have h2 : resHom W₀ ⟨l, hl0⟩ ∈ autSub L W₀ ⊓ centSec W U := ⟨hrK, hrc⟩
    rw [hf, Subgroup.mem_bot] at h2
    exact hfaith l hl fun v hv => by
      have h3 : ((resHom W₀ ⟨l, hl0⟩ ⟨v, hv⟩ : ↥W₀) : V) = v := by rw [h2]; rfl
      exact h3
  ·
    rw [burnsideB55_autSec_map W U hst, burnsideB55_autSec_map W U hL0,
      burnsideB55_genFitting_map_equiv, burnsideB55_autSec_eq _ hUW', burnsideB55_autSec_eq _ hUW',
      hF]
  ·
    obtain ⟨B, hBA, hB⟩ := hex
    rw [← burnsideB55_autSec_eq _ hUW'] at hBA hB
    refine ⟨B.map (MulAut.congr (burnsideB55_secEquiv W U)).toMonoidHom, ?_, ?_⟩
    · rw [burnsideB55_autSec_map W U hA0]
      exact Subgroup.map_mono hBA
    · rw [burnsideB55_autSec_map W U hst]
      exact isFFStarOffender_map_congr_equiv (burnsideB55_secEquiv W U) hB
  ·
    set e₁ := W.equivMapOfInjective W₀.subtype W₀.subtype_injective with he₁
    have hφcoe : ∀ x : ↥(W.map W₀.subtype), (((e₁.symm x : ↥W) : ↥W₀) : V) = (x : V) := fun x => by
      have := congrArg (fun y : ↥(W.map W₀.subtype) => (y : V)) (e₁.apply_symm_apply x)
      exact this
    refine burnsideB55_b42_transport (fun D => burnsideB55_realizes_transport
      (FFC.resEquiv hL0 hfaith) e₁.symm.toMonoidHom e₁.symm.surjective ?_ ?_
      (Subgroup.map_mono hUW') ?_ ?_) hpair
    · intro u
      show ((e₁.symm u : ↥W) : ↥W₀) ∈ U ↔ _
      rw [← burnsideB55_mem_map_subtype U, hφcoe]
    · intro h u hu
      apply Subtype.ext
      have h1 : ((FFC.resEquiv hL0 hfaith h : ↥(autSub L W₀)) : MulAut ↥W₀) = FFC.resG hL0 h :=
        FFC.resEquiv_apply hL0 hfaith h
      show (((e₁.symm ⟨(h : MulAut V) (u : V), hu⟩ : ↥W) : ↥W₀) : V) =
        (((FFC.resEquiv hL0 hfaith h : ↥(autSub L W₀)) : MulAut ↥W₀)
          ((e₁.symm u : ↥W) : ↥W₀) : ↥W₀)
      rw [h1, hφcoe, FFC.resG_apply, hφcoe]
    · intro h u hu
      exact ((hstab h (Subgroup.mem_sup_left h.2)).1 u).2 hu
    · intro h z hz
      exact ((hstab h (Subgroup.mem_sup_left h.2)).2 z).2 hz

open CFSG.Quasithin in
private theorem burnsideB55_iii (hB51 : AsB51) (hA21 : AsA21SQTKSection) {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} (hb : B53Hyp G)
    {L : Subgroup (MulAut V)} (hL : IsComponentOf L G) :
    ∃ A, IsFFStarOffender G A ∧ ⁅L, A⁆ = L ∧ ∃ X Y : Subgroup V, Y < X ∧
      (∀ a ∈ A, a ∈ stabSub X ∧ a ∈ stabSub Y) ∧ (∀ l ∈ L, l ∈ stabSub X ∧ l ∈ stabSub Y) ∧
      XMod.IsIrrSec ↥L Y X ∧
      (∀ l ∈ L, CFSG.ASVolI.ChB.ActsTrivOnSection l X Y → l = 1) ∧
      quasithinGenFitting (CFSG.ASVolI.ChB.autSec (L ⊔ A) X Y) = CFSG.ASVolI.ChB.autSec L X Y ∧
      (∃ B, B ≤ CFSG.ASVolI.ChB.autSec A X Y ∧
        IsFFStarOffender (CFSG.ASVolI.ChB.autSec (L ⊔ A) X Y) B) ∧ B42ModulePair L X Y := by
  obtain ⟨A, hA, hLA⟩ := B55.exists_offender B15P4.asB15Part4 hV hb.2.1 hL
  refine ⟨A, hA, hLA, ?_⟩
  obtain ⟨-, -, -, hst, -, -⟩ := FFC.B59.red_basic hV hL hA hLA
  have hfaith : ∀ l ∈ L, (∀ v ∈ FFC.B59.W0 L A, l v = v) → l = 1 := by
    have h0 : L ⊓ centSub (FFC.B59.W0 L A) = ⊥ := (B55.faithful_on_fixV hV hb.1 hL hA hLA).1
    intro g hg hgW
    have hmem : g ∈ L ⊓ centSub (FFC.B59.W0 L A) := ⟨hg, hgW⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  have hb51 := FFC.B59.b51Hyp_red hA21 hV hb.1 hb hL hA hLA
  have hVM : ∀ v : ↥(FFC.B59.W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨-, -, -, -, -, -, hoff, -, -⟩ := FFC.B59.red_aut hV hL hA hLA
  obtain ⟨W, U, hUW, hMW, hMU, hirr, hf, hex, hF, hpair⟩ :=
    burnsideB55_core hVM hB51 hb51 hoff
  exact burnsideB55_transport hst hfaith hUW hMW hMU hirr hf hex
    hF hpair

end BurnsideB55

section

open CFSG.Quasithin in
theorem as_B_5_5
    : B_5_5 := by
  intro V _ _ hV G hB
  refine ⟨fun L hL => ?_, burnsideB55_B55_two hV hB⟩
  obtain ⟨hn, hii⟩ := burnsideB55_B55_i_ii hV hB hL
  exact ⟨hn, hii, burnsideB55_iii B5.asB51_holds asA21SQTKSection hV hB hL,
    burnsideB55_B55_iv B15P4.asB15Part4 B5.asB51_holds asA21SQTKSection hV hB hL⟩

end

@[expose] def B_5_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)),
    (∀ v : V, v ^ 2 = 1) → G ≠ ⊥ → B53Hyp G → ¬ B56Cases G →
    ∀ L : Subgroup (MulAut V), IsComponentOf L G → CFSG.Open.pRank 3 L = 1

section

theorem as_B_5_7
    : B_5_7 := by
  intro V _ _ G hV hne hB hnot _ _
  exact (hnot (CFSG.Quasithin.asB56_holds V hV G hne hB)).elim

end

@[expose] def B_5_8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A, IsFFStarMin G A → A ≤ Subgroup.centralizer (fitOf G : Set (MulAut V))

section

theorem as_B_5_8 : B_5_8 := by
  intro V _ _ G hc A hA
  exact CFSG.Quasithin.FFC.asB58 V G hc A hA

end

@[expose] def B_5_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L : Subgroup (MulAut V), IsFFStarMin G A → IsComponentOf L G → ⁅L, A⁆ = L →
      B59Case1 A L ∨ B59Case2 A L ∨ B59Case3 A L ∨ B59Case4 A L ∨ B59Case5 A L

section

theorem as_B_5_9
    : B_5_9 := by
  have hP4 := CFSG.Quasithin.B15P4.asB15Part4
  have hB51 := CFSG.Quasithin.B5.asB51_holds
  have hB42 := CFSG.Quasithin.asB42_holds
  have hA21 := CFSG.Quasithin.asA21SQTKSection
  have h57 := CFSG.Quasithin.FFC.b57Input_of hP4 hB51 hA21
    (CFSG.Quasithin.FFC.b57Exc_of hP4 hB51 hA21)
  have hLast := CFSG.Quasithin.SmithB57.b59Last_holds hB51 hB42 hA21
  have hI16 := CFSG.Quasithin.asI16Cover_of
  intro V _ _ G hc A L hA hL hAL
  exact CFSG.Quasithin.FFC.B59.asB59_of_inputs hP4 hB51 hB42 hA21 h57 hLast hI16 V G hc A L hA hL hAL

end

@[expose] def B_5_10 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L : Subgroup (MulAut V), IsFFStarMin G A → IsComponentOf L G → ⁅L, A⁆ = L →
      ∀ G₁ : Subgroup (MulAut V), IsG1 A L G₁ →
        ((G₁ ≤ G ∧ (G₁.subgroupOf G).Normal ∧ ∀ g ∈ G, g ∈ stabSub (commV L) ∧ g ∈ stabSub (fixV G₁)) ∧
          ((G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) ≤ G ∧
            ((G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))).subgroupOf G).Normal)) ∧
        (IsIntDirProd G ![G₁, G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))] ∧
          G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V)) = G ⊓ centSub (commV L)) ∧
        (commV L ⊔ fixV G₁ = ⊤ ∨ IsExceptionalG1 L G₁)

section

theorem as_B_5_10
    : B_5_10 := by
  intro V _ _ G hc A L _ _ _ _ _
  exact (hc.not_cases (CFSG.Quasithin.asB56_holds V hc.hV G hc.ne_bot hc.hyp)).elim

end

@[expose] def B_5_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L : Subgroup (MulAut V), IsFFStarMin G A → IsComponentOf L G → ⁅L, A⁆ = L →
      ∀ G₁ : Subgroup (MulAut V), IsG1 A L G₁ →
        (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V)) ≠ ⊥ ∧
          (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) ⊓ centSub (fixV G₁) = ⊥ ∧
          autSub (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) (fixV G₁) =
            ffJ (autSub (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) (fixV G₁))) ∧
        (B56FactorList ↥(G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) ∧
          ∃ V₂' : Subgroup V, V₂' ≤ fixV G₁ ∧
            (∀ g ∈ G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V)), ∀ x ∈ V₂', g x ∈ V₂') ∧
            fixV G₁ = V₂' ⊔ (fixV (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) ⊓ fixV G₁) ∧
            B56PieceOnU (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) (fixV G₁) V₂'
              (fixV (G ⊓ Subgroup.centralizer (G₁ : Set (MulAut V))) ⊓ V₂'))

section

theorem as_B_5_11
    : B_5_11 := by
  intro V _ _ G hc A L _ _ _ _ _
  exact (hc.not_cases (CFSG.Quasithin.asB56_holds V hc.hV G hc.ne_bot hc.hyp)).elim

end

@[expose] def B_5_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L : Subgroup (MulAut V), IsFFStarMin G A → IsComponentOf L G → ⁅L, A⁆ = L →
      ∀ G₁ : Subgroup (MulAut V), IsG1 A L G₁ → IsExceptionalG1 L G₁

section

theorem as_B_5_12
    : B_5_12 := by
  intro V _ _ G hc A L _ _ _ _ _
  exact (hc.not_cases (CFSG.Quasithin.asB56_holds V hc.hV G hc.ne_bot hc.hyp)).elim

end

@[expose] def B_5_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), G ≠ ⊥ → B53Hyp (dualSub G) → qOf G ≤ 2

section

theorem as_B_5_13
    : B_5_13 := by
  intro V _ _ hV G hne hB
  have hsq := CFSG.Quasithin.FFC.isQuotientOfSQTKTauCeti_of_b53 hB
  exact CFSG.Quasithin.b513_of_nonsolvable CFSG.Quasithin.B513N.b513Nonsolvable_holds V hV G hne hB.1 hB.2.1 hsq

end

end CFSG.ASVolI
