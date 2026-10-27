module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalF11
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem521
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem527

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def FactU3Cover : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (k : ℕ), 2 ≤ k → CFSG.IsQuasisimple X →
    LieModel (X ⧸ Subgroup.center X) .PSU 3 2 k → IsRankOneListed X

@[expose] def FactL2LieParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (k : ℕ), 2 ≤ k →
    (IsSL3Ch5 k Y ∨ LieModel Y .PSp 2 2 k) → ∀ U : Subgroup Y, IsSylowTwoOf U ⊤ →
      ∃ P : Fin 2 → Subgroup Y, P 0 ≠ P 1 ∧
        (∀ Q : Subgroup Y, Subgroup.normalizer (U : Set Y) ≤ Q → (Q ⋖ ⊤ ↔ ∃ j, Q = P j)) ∧
        (∀ j, Subgroup.normalizer (U : Set Y) ⋖ P j ∧ U ≤ perfectCore (P j) ∧
          IsPSL 2 2 k (ModO2 (perfectCore (P j)))) ∧
        perfectCore (P 0) ⊔ perfectCore (P 1) = ⊤

@[expose] def Stmt5_2_L2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D K₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → quasithinIsCComponent K₁ H →
    oTwoUpper H = conjClosure K₁ T → K₁ < oTwoUpper H → IsBenderAny (O2Q K₁) →
      borelOf K₁ T ≤ M ∧
        (∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          X ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
          Odd (Nat.card X) → X ≤ Subgroup.normalizer (K₁ : Set G)) ∧
        ∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
            X ≤ Subgroup.normalizer (P : Set G)) →
          X ≤ Subgroup.normalizer (K₁ : Set G)

section Bender

theorem isRankOneListed_of_isBenderAny (hU3 : FactU3Cover) {X : Type} [Group X] [Finite X]
    (h : IsBenderAny X) : IsRankOneListed X := by
  obtain ⟨k, hk, hB⟩ := h
  rcases hB with hL | hS | ⟨hq, hU⟩
  · exact isRankOneListed_of_lieModel (by omega) hL
  · obtain ⟨a, -, ⟨e⟩⟩ := exists_mulEquiv_sz_of_suzukiModel hS
    exact Or.inr (Or.inl ⟨a, ⟨e⟩⟩)
  · exact hU3 X k hk hq hU

theorem isRankOneListed_oTwoQuot_of_isBenderAny (hU3 : FactU3Cover) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (h : IsBenderAny (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsRankOneListed (oTwoQuot ↥L) := by
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* oTwoQuot ↥L :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)
  exact IsRankOneListed.of_mulEquiv e (isRankOneListed_of_isBenderAny hU3 h)

end Bender

section Lift

variable {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ}

omit [Finite Γ] in
theorem map_comap_modO2Image_of_le {A : Subgroup Γ} (hAK : A ≤ K) (hOA : pCoreOf 2 K ≤ A) :
    ((modO2Image K A).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype = A := by
  rw [Vol2.Ch11.SecS.map_comap_modO2Image hAK, sup_eq_left.mpr hOA]

omit [Finite Γ] in
theorem le_sup_of_modO2Image_le {A B : Subgroup Γ} (hAK : A ≤ K) (hBK : B ≤ K)
    (h : modO2Image K A ≤ modO2Image K B) : A ≤ B ⊔ pCoreOf 2 K := by
  rw [← Vol2.Ch11.SecS.map_comap_modO2Image hBK]
  exact le_sup_left.trans ((Vol2.Ch11.SecS.map_comap_modO2Image hAK).symm.le.trans
    (Subgroup.map_mono (Subgroup.comap_mono h)))

theorem modO2Image_perfectCore {P : Subgroup Γ} (hPK : P ≤ K) :
    modO2Image K (perfectCore P) = perfectCore (modO2Image K P) := by
  unfold modO2Image
  have h : (perfectCore P).subgroupOf K = perfectCore (P.subgroupOf K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPK,
      Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le P).trans hPK)]
  rw [h, map_perfectCore]

omit [Finite Γ] in
theorem IsMaxParabolicOver.pCoreOf_le {S P : Subgroup Γ} (hP : IsMaxParabolicOver K S P)
    (hSK : S ≤ K) (hOS : pCoreOf 2 K ≤ S) : pCoreOf 2 K ≤ P :=
  hOS.trans ((le_inf hSK Subgroup.le_normalizer).trans hP.2.1)

theorem normalizer_modO2Image_le {S P : Subgroup Γ} (hSK : S ≤ K) (hOS : pCoreOf 2 K ≤ S)
    (hP : K ⊓ Subgroup.normalizer (S : Set Γ) ≤ P) :
    Subgroup.normalizer (modO2Image K S : Set (O2Q K)) ≤ modO2Image K P := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  intro y hy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
  have ha : (a : Γ) ∈ Subgroup.normalizer (S : Set Γ) := by
    refine mem_normalizer_of_conj_mem' fun s hs => ?_
    have h1 : π (a * ⟨s, hSK hs⟩ * a⁻¹) ∈ modO2Image K S := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp ⟨⟨s, hSK hs⟩, hs, rfl⟩
    have h2 : ((a * ⟨s, hSK hs⟩ * a⁻¹ : ↥K) : Γ) ∈
        ((modO2Image K S).comap π).map K.subtype := ⟨_, h1, rfl⟩
    rw [map_comap_modO2Image_of_le hSK hOS] at h2
    simpa using h2
  exact ⟨a, Subgroup.mem_subgroupOf.mpr (hP ⟨a.2, ha⟩), rfl⟩

theorem IsMaxParabolicOver.modO2Image_spec {S P : Subgroup Γ} (hP : IsMaxParabolicOver K S P)
    (hSK : S ≤ K) (hOS : pCoreOf 2 K ≤ S) :
    Subgroup.normalizer (modO2Image K S : Set (O2Q K)) ≤ modO2Image K P ∧
      modO2Image K P ⋖ ⊤ := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hPK : P ≤ K := hP.1
  have hOP : pCoreOf 2 K ≤ P := hP.pCoreOf_le hSK hOS
  refine ⟨normalizer_modO2Image_le hSK hOS hP.2.1,
    lt_top_iff_ne_top.mpr fun htop => hP.2.2.1 ?_, fun Q hPQ hQ => ?_⟩
  · have h := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hPK htop
    rw [sup_eq_left.mpr hOP] at h
    exact le_antisymm hPK h
  · set Q' := (Q.comap π).map K.subtype with hQ'
    have hPQ' : P ≤ Q' := by
      rw [← map_comap_modO2Image_of_le hPK hOP]
      exact Subgroup.map_mono (Subgroup.comap_mono hPQ.le)
    have hQ'ne : Q' ≠ K := by
      intro h
      apply hQ.ne
      have h1 : Q.comap π = ⊤ := by
        apply Subgroup.map_injective K.subtype_injective
        rw [← hQ', h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Q, h1,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have heq := hP.2.2.2 Q' hPQ' (Subgroup.map_subtype_le _) hQ'ne
    apply hPQ.ne'
    have h2 : Q.comap π = P.subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [← hQ', heq, Subgroup.map_subgroupOf_eq_of_le hPK]
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Q, h2]
    rfl

omit [Finite Γ] in
theorem exists_surjective_modO2 {A : Subgroup Γ} (hAK : A ≤ K) :
    ∃ g : ↥A →* ModO2 (modO2Image K A), Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  let e : ↥A ≃* ↥(A.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hAK).symm
  let f : ↥A →* ↥(modO2Image K A) := (π.subgroupMap (A.subgroupOf K)).comp e.toMonoidHom
  have hf : Function.Surjective f := (π.subgroupMap_surjective _).comp e.surjective
  have hfker : IsPGroup 2 f.ker := by
    rintro ⟨x, hx⟩
    have h1 : ((e x : ↥(A.subgroupOf K)) : ↥K) ∈ CFSG.pCore 2 ↥K := by
      have h2 : π ((e x : ↥(A.subgroupOf K)) : ↥K) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, h1⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have h3 := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : Γ)) hm
    simpa [e] using h3
  refine ⟨(QuotientGroup.mk' _).comp f, (QuotientGroup.mk'_surjective _).comp hf, ?_⟩
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hfker

theorem eq_perfectCore_of_mem_cComp {P L : Subgroup Γ} (hL : L ∈ cComp P) {S : Type} [Group S]
    (hS : IsSimpleGroup S) (g : ↥(perfectCore P) →* S) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : L = perfectCore P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLA : L ≤ perfectCore P :=
    le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
  have hsub : IsSubnormal L (perfectCore P) :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hL) hLA (perfectCore_le P)
  have hsub' : ((L.subgroupOf (perfectCore P)).map g).IsSubnormal := by
    have h1 : IsSubnormal (L.subgroupOf (perfectCore P)) ((perfectCore P).subgroupOf
        (perfectCore P)) := A4.subnormal_subgroupOf (perfectCore P) hsub
    rw [Subgroup.subgroupOf_self] at h1
    exact (A3.subnormal_top_iff.mp h1).map hg
  rcases hsub'.eq_bot_or_top_of_isSimpleGroup hS with hbot | htop
  · exfalso
    have hle : L.subgroupOf (perfectCore P) ≤ g.ker := fun x hx => by
      have : g x ∈ (L.subgroupOf (perfectCore P)).map g := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have h2 : IsPGroup 2 ↥L := (hker.to_le hle).of_equiv (Subgroup.subgroupOfEquivOfLe hLA)
    have := h2.isNilpotent
    exact not_isSolvable_of_mem_cComp hL inferInstance
  · have hle : perfectCore P ≤ L ⊔ g.ker.map (perfectCore P).subtype := by
      intro x hx
      have hmem : g ⟨x, hx⟩ ∈ (L.subgroupOf (perfectCore P)).map g := by
        rw [htop]
        trivial
      obtain ⟨y, hy, hyx⟩ := hmem
      have h1 : y⁻¹ * ⟨x, hx⟩ ∈ g.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hx' : x = (y : Γ) * ((y⁻¹ * ⟨x, hx⟩ : ↥(perfectCore P)) : Γ) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hx']
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
        (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)
    exact eq_of_isSubnormal_of_le_sup hsub (perfectCore_perfect P) (hker.map _)
      (Subgroup.map_subtype_le _) hle le_rfl

theorem eq_perfectCore_of_isPSL {S P L : Subgroup Γ} {k : ℕ} (hS : IsSylowTwoOf S K)
    (hP : IsMaxParabolicOver K S P) (hL : L ∈ cComp P)
    (hSB : modO2Image K S ≤ modO2Image K (perfectCore P))
    (hB : IsPSL 2 2 k (ModO2 (modO2Image K (perfectCore P)))) :
    L = perfectCore P ∧ IsPSL 2 2 k (ModO2 L) ∧ S ≤ L ⊔ pCoreOf 2 K := by
  have hAK : perfectCore P ≤ K := (perfectCore_le P).trans hP.1
  obtain ⟨g, hg, hker⟩ := exists_surjective_modO2 hAK
  have hsimple : IsSimpleGroup (ModO2 (modO2Image K (perfectCore P))) :=
    isSimpleGroup_of_lieModel_PSL2 (Or.inl ⟨by simp [classicalTags], hB⟩)
  have hLeq := eq_perfectCore_of_mem_cComp hL hsimple g hg hker
  refine ⟨hLeq, ?_, ?_⟩
  · have hperf : Group.IsPerfect (ModO2 (modO2Image K (perfectCore P))) := by
      have : Group.IsPerfect ↥(modO2Image K (perfectCore P)) :=
        Subgroup.isPerfect_iff.mpr (Vol2.Ch11.SecS.modO2Image_perfect hAK (perfectCore_perfect P))
      exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hnc := Group.IsPerfect.not_isMulCommutative (ModO2 (modO2Image K (perfectCore P)))
    have hab : ∃ a b : ModO2 (modO2Image K (perfectCore P)), a * b ≠ b * a := by
      by_contra hall
      exact hnc ⟨⟨fun a b => by_contra fun h => hall ⟨a, b, h⟩⟩⟩
    subst hLeq
    exact IsPSL.of_mulEquiv (Vol2Native.A312L.modO2EquivOfHom hab g hg hker).symm hB
  · rw [hLeq]
    exact le_sup_of_modO2Image_le hS.1 hAK hSB

omit [Finite Γ] in
theorem IsMaxParabolicOver.map_conj {S P : Subgroup Γ} (hP : IsMaxParabolicOver K S P) {x : Γ}
    (hxK : x ∈ Subgroup.normalizer (K : Set Γ)) (hxS : x ∈ Subgroup.normalizer (S : Set Γ)) :
    IsMaxParabolicOver K S (P.map (MulAut.conj x).toMonoidHom) := by
  set c := (MulAut.conj x).toMonoidHom with hc
  have hcK : K.map c = K := CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp hxK
  have hcB : (K ⊓ Subgroup.normalizer (S : Set Γ)).map c =
      K ⊓ Subgroup.normalizer (S : Set Γ) :=
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (mem_normalizer_inf_normalizer hxK hxS)
  have hinj : Function.Injective c := (MulAut.conj x).injective
  have hsurj : Function.Surjective c := (MulAut.conj x).surjective
  refine ⟨?_, ?_, fun h => hP.2.2.1 (Subgroup.map_injective hinj (by rw [h, hcK])),
    fun Q hPQ hQK hQne => ?_⟩
  · rw [← hcK]
    exact Subgroup.map_mono hP.1
  · rw [← hcB]
    exact Subgroup.map_mono hP.2.1
  · have hcomap : Q.comap c ≤ K := by
      rw [← Subgroup.comap_map_eq_self_of_injective hinj K, hcK]
      exact Subgroup.comap_mono hQK
    have h1 : Q.comap c = P := hP.2.2.2 _ (Subgroup.map_le_iff_le_comap.mp hPQ) hcomap
      (fun h => hQne (by rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Q, h, hcK]))
    rw [← h1, Subgroup.map_comap_eq_self_of_surjective hsurj]

omit [Finite Γ] in
theorem mem_normalizer_of_odd_of_pair {p : Subgroup Γ → Prop} {A : Subgroup Γ} (hA : p A)
    (h2 : ∀ P₁ P₂ P₃ : Subgroup Γ, p P₁ → p P₂ → p P₃ → P₁ = P₂ ∨ P₂ = P₃ ∨ P₁ = P₃)
    {x : Γ} (hx : Odd (orderOf x)) (hc : ∀ Q, p Q → p (Q.map (MulAut.conj x).toMonoidHom)) :
    x ∈ Subgroup.normalizer (A : Set Γ) := by
  set c := (MulAut.conj x).toMonoidHom with hc'
  have hA2 := hc A hA
  have hA3 := hc _ hA2
  have hcc : (A.map c).map c = A.map (MulAut.conj (x * x)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [hc', MulAut.conj_apply, mul_assoc]
  rcases h2 A _ _ hA hA2 hA3 with h | h | h
  · exact CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr h.symm
  · exact CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr
      (Subgroup.map_injective (MulAut.conj x).injective h).symm
  · rw [hcc] at h
    have hxx : x * x ∈ Subgroup.normalizer (A : Set Γ) :=
      CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr h.symm
    obtain ⟨r, hr⟩ := hx
    have hpow : x = (x * x) ^ (r + 1) := by
      rw [← sq, ← pow_mul, show 2 * (r + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hpow]
    exact Subgroup.pow_mem _ hxx _

omit [Finite Γ] in
theorem mem_normalizer_of_odd_of_two {S P : Subgroup Γ} (hP : IsMaxParabolicOver K S P)
    (h2 : ∀ P₁ P₂ P₃ : Subgroup Γ, IsMaxParabolicOver K S P₁ → IsMaxParabolicOver K S P₂ →
      IsMaxParabolicOver K S P₃ → P₁ = P₂ ∨ P₂ = P₃ ∨ P₁ = P₃)
    {x : Γ} (hx : Odd (orderOf x)) (hxK : x ∈ Subgroup.normalizer (K : Set Γ))
    (hxS : x ∈ Subgroup.normalizer (S : Set Γ)) : x ∈ Subgroup.normalizer (P : Set Γ) :=
  mem_normalizer_of_odd_of_pair hP h2 hx fun _ hQ => hQ.map_conj hxK hxS

theorem exists_parabolics (hF : FactL2LieParabolic) {S : Subgroup Γ} {k : ℕ} (hk : 2 ≤ k)
    (htype : IsSL3Ch5 k (O2Q K) ∨ LieModel (O2Q K) .PSp 2 2 k) (hS : IsSylowTwoOf S K) :
    ∃ Pj : Fin 2 → Subgroup (O2Q K),
      (∀ P, IsMaxParabolicOver K S P → ∃ j, modO2Image K P = Pj j) ∧
      (∀ j, Subgroup.normalizer (modO2Image K S : Set (O2Q K)) ⋖ Pj j ∧
        modO2Image K S ≤ perfectCore (Pj j) ∧ IsPSL 2 2 k (ModO2 (perfectCore (Pj j)))) ∧
      perfectCore (Pj 0) ⊔ perfectCore (Pj 1) = ⊤ := by
  obtain ⟨Pj, -, hiff, hj, hgen⟩ :=
    hF (O2Q K) k hk htype (modO2Image K S) (Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hS)
  refine ⟨Pj, fun P hP => ?_, hj, hgen⟩
  obtain ⟨hN, hcov⟩ := hP.modO2Image_spec hS.1 (F7.isSylowTwoOf_pCoreOf_le hS)
  exact (hiff _ hN).mp hcov

theorem maxParabolic_two (hF : FactL2LieParabolic) {S : Subgroup Γ} {k : ℕ} (hk : 2 ≤ k)
    (htype : IsSL3Ch5 k (O2Q K) ∨ LieModel (O2Q K) .PSp 2 2 k) (hS : IsSylowTwoOf S K) :
    ∀ P₁ P₂ P₃ : Subgroup Γ, IsMaxParabolicOver K S P₁ → IsMaxParabolicOver K S P₂ →
      IsMaxParabolicOver K S P₃ → P₁ = P₂ ∨ P₂ = P₃ ∨ P₁ = P₃ := by
  obtain ⟨Pj, hPj, -, -⟩ := exists_parabolics hF hk htype hS
  have hOS : pCoreOf 2 K ≤ S := F7.isSylowTwoOf_pCoreOf_le hS
  have hinj : ∀ {Q₁ Q₂ : Subgroup Γ}, IsMaxParabolicOver K S Q₁ → IsMaxParabolicOver K S Q₂ →
      modO2Image K Q₁ = modO2Image K Q₂ → Q₁ = Q₂ := fun hQ₁ hQ₂ he => by
    rw [← map_comap_modO2Image_of_le hQ₁.1 (hQ₁.pCoreOf_le hS.1 hOS),
      ← map_comap_modO2Image_of_le hQ₂.1 (hQ₂.pCoreOf_le hS.1 hOS), he]
  intro P₁ P₂ P₃ h₁ h₂ h₃
  obtain ⟨j₁, e₁⟩ := hPj P₁ h₁
  obtain ⟨j₂, e₂⟩ := hPj P₂ h₂
  obtain ⟨j₃, e₃⟩ := hPj P₃ h₃
  have hj : j₁ = j₂ ∨ j₂ = j₃ ∨ j₁ = j₃ := by
    have := j₁.isLt
    have := j₂.isLt
    have := j₃.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hj with h | h | h
  · exact Or.inl (hinj h₁ h₂ (by rw [e₁, e₂, h]))
  · exact Or.inr (Or.inl (hinj h₂ h₃ (by rw [e₂, e₃, h])))
  · exact Or.inr (Or.inr (hinj h₁ h₃ (by rw [e₁, e₃, h])))

omit [Finite Γ] in
theorem IsMaxParabolicOver.isMaxParabolic2 {S P : Subgroup Γ} (hP : IsMaxParabolicOver K S P)
    (hS : IsSylowTwoOf S K) : IsMaxParabolic2 K P :=
  ⟨⟨hP.1, S, hS, hP.2.1⟩, hP.2.2.1, fun Q hQ hQK hPQ => hP.2.2.2 Q hPQ hQ.1 hQK⟩

omit [Finite Γ] in
theorem modO2Image_sup {A B : Subgroup Γ} (hA : A ≤ K) (hB : B ≤ K) :
    modO2Image K (A ⊔ B) = modO2Image K A ⊔ modO2Image K B := by
  unfold modO2Image
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem IsMaxParabolicOver.isRankOneParabolicOver (hF : FactL2LieParabolic) {S P : Subgroup Γ}
    {k : ℕ} (hk : 2 ≤ k) (htype : IsSL3Ch5 k (O2Q K) ∨ LieModel (O2Q K) .PSp 2 2 k)
    (hS : IsSylowTwoOf S K) (hP : IsMaxParabolicOver K S P) : IsRankOneParabolicOver K S P := by
  obtain ⟨Pj, hPj, hj, -⟩ := exists_parabolics hF hk htype hS
  obtain ⟨j, hPeq⟩ := hPj P hP
  have hOS : pCoreOf 2 K ≤ S := F7.isSylowTwoOf_pCoreOf_le hS
  set B := K ⊓ Subgroup.normalizer (S : Set Γ) with hB
  have hBK : B ≤ K := inf_le_left
  have hOB : pCoreOf 2 K ≤ B := hOS.trans (le_inf hS.1 Subgroup.le_normalizer)
  have hBeq : modO2Image K B = Subgroup.normalizer (modO2Image K S : Set (O2Q K)) :=
    le_antisymm (Vol2.Ch11.SecS.modO2Image_le_normalizer inf_le_right)
      (normalizer_modO2Image_le hS.1 hOS le_rfl)
  have hcov := (hj j).1
  rw [← hBeq, ← hPeq] at hcov
  have hinj : ∀ {Q : Subgroup Γ}, Q ≤ K → B ≤ Q → ∀ {Q' : Subgroup Γ}, Q' ≤ K → B ≤ Q' →
      modO2Image K Q = modO2Image K Q' → Q = Q' := fun hQ hBQ _ hQ' hBQ' he => by
    rw [← map_comap_modO2Image_of_le hQ (hOB.trans hBQ),
      ← map_comap_modO2Image_of_le hQ' (hOB.trans hBQ'), he]
  refine ⟨lt_of_le_of_ne hP.2.1 fun h => hcov.lt.ne (congrArg (modO2Image K) h), hP.1,
    fun Q hBQ hQP => ?_⟩
  have h1 : modO2Image K B ≤ modO2Image K Q :=
    Subgroup.map_mono (fun x hx => hBQ.le hx : B.subgroupOf K ≤ Q.subgroupOf K)
  have h2 : modO2Image K Q ≤ modO2Image K P :=
    Subgroup.map_mono (fun x hx => hQP hx : Q.subgroupOf K ≤ P.subgroupOf K)
  rcases hcov.eq_or_eq h1 h2 with h | h
  · exact absurd (hinj (hQP.trans hP.1) hBQ.le hBK le_rfl h) hBQ.ne'
  · exact hinj (hQP.trans hP.1) hBQ.le hP.1 hP.2.1 h

end Lift


theorem nonBender_type (h510 : Stmt5_1_10) {G : Type} [Group G] [Finite G]
    {T M L H B D K₁ : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) (hK₁ : quasithinIsCComponent K₁ H)
    (hnb : ¬ IsBenderAny (O2Q K₁)) (hK1eq : K₁ = oTwoUpper H) :
    ∃ k : ℕ, 2 ≤ k ∧
      (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
      E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H) ∧
      M ⊓ oTwoUpper H =
        oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  obtain ⟨k, hk, hBorel, -, K₁', hK₁', -, hcases'⟩ := h510 G T M L H B D n hyp hN
  refine ⟨k, hk.1, ?_⟩
  rcases hcases' with ⟨hlt, -⟩ | ⟨-, h2⟩ | ⟨-, h2, h3⟩
  · exfalso
    rw [← hK1eq] at hlt
    exact not_subnormal_of_mem_cComp hK₁ hlt hK₁'.1 hK₁'.2.1 hK₁'.2.2.1
  · rw [hK1eq] at hnb
    exact absurd ⟨k, hk.1, h2⟩ hnb
  · exact ⟨h2, h3, hyp.borel_eq hBorel⟩

theorem l2Lie_nonBender (hF : FactL2LieParabolic) {G : Type} [Group G] [Finite G]
    {T M K P L₂ : Subgroup G} {k : ℕ} (hk : 2 ≤ k)
    (htype : IsSL3Ch5 k (O2Q K) ∨ LieModel (O2Q K) .PSp 2 2 k) (hTK : IsSylowTwoOf (T ⊓ K) K)
    (hMK : M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hP : IsMaxParabolicOver K (T ⊓ K) P) (hL₂ : quasithinIsCComponent L₂ P) :
    L₂ = perfectCore P ∧ IsPSL 2 2 k (ModO2 L₂) ∧ borelOf L₂ T ≤ M ∧
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (K : Set G) →
        X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → Odd (Nat.card X) →
        X ≤ Subgroup.normalizer (L₂ : Set G) := by
  obtain ⟨Pj, hPj, hj, -⟩ := exists_parabolics hF hk htype hTK
  have hOS : pCoreOf 2 K ≤ T ⊓ K := F7.isSylowTwoOf_pCoreOf_le hTK
  obtain ⟨j, hPeq⟩ := hPj P hP
  have hPK : P ≤ K := hP.1
  have hcore : modO2Image K (perfectCore P) = perfectCore (Pj j) := by
    rw [modO2Image_perfectCore hPK, hPeq]
  obtain ⟨hL₂eq, hpsl, hTKL⟩ := eq_perfectCore_of_isPSL hTK hP hL₂
    (by rw [hcore]; exact (hj j).2.1) (by rw [hcore]; exact (hj j).2.2)
  have hL₂K : L₂ ≤ K := hL₂eq ▸ (perfectCore_le P).trans hPK
  have hON : pCoreOf 2 K ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [hL₂eq]
    exact (hP.pCoreOf_le hTK.1 hOS).trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))
  have hTKeq : T ⊓ K = pCoreOf 2 K ⊔ (T ⊓ L₂) := by
    have h1 := A3.eq_sup_inf_of_le_sup hON hOS (by rw [sup_comm]; exact hTKL)
    rw [inf_assoc, inf_eq_right.mpr hL₂K] at h1
    exact h1
  have hborel : borelOf L₂ T ≤ M := by
    intro y hy
    obtain ⟨hyL, hyN⟩ := hy
    have hyK : y ∈ K := hL₂K hyL
    have hyO : y ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K hyK
    have hyTK : y ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [hTKeq, CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, Subgroup.map_sup,
        CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp hyO,
        CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp hyN]
    have hyMK : y ∈ M ⊓ K := by
      rw [hMK]
      exact ⟨hyK, hyTK⟩
    exact hyMK.1
  refine ⟨hL₂eq, hpsl, hborel, fun X hXK hXT hXodd x hx => ?_⟩
  have hxodd : Odd (orderOf x) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : X)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hXodd this
  have hxP := mem_normalizer_of_odd_of_two hP (maxParabolic_two hF hk htype hTK) hxodd
    (hXK hx) (hXT hx)
  rw [hL₂eq]
  exact normalizer_le_normalizer_perfectCore P hxP

theorem stmt5_2_L2Lie_of (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hTwo : Stmt5_2_L2Two)
    (h510 : Stmt5_1_10) : Stmt5_2_L2Lie := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  have hMK := hyp.borel_eq hBorel
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨hbend, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  ·
    refine ⟨isRankOneListed_oTwoQuot_of_isBenderAny hU3 hbend, ?_⟩
    have hle : L₂ ≤ oTwoUpper H := by
      rw [hKeq]
      exact le_conjClosure L₂ T
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨h1, h2, -⟩ := hTwo G T M L H B D L₂ n hyp hN hK₁ hKeq hlt hbend
      exact ⟨h1, h2⟩
    · rw [heq]
      refine ⟨?_, fun X hXK _ _ => hXK⟩
      show oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤ M
      rw [← hMK]
      exact inf_le_left
  ·
    obtain ⟨k', hk', htype, -, -⟩ := nonBender_type h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨-, hpsl, hborel, hX⟩ := l2Lie_nonBender hF hk' htype hTK hMK hP hL₂P
    exact ⟨isRankOneListed_oTwoQuot (by omega) (Or.inl ⟨by simp [classicalTags], hpsl⟩), hborel,
      hX⟩


theorem stmt5_2_L2Gen_of (hF : FactL2LieParabolic) (h510 : Stmt5_1_10) : Stmt5_2_L2Gen := by
  intro G _ _ T M L H B D K₁ P L₂ n hyp hN hK₁ _ hnb hK1eq hP hL₂P
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, hdiag, hMK⟩ := nonBender_type h510 hyp hN hK₁ hnb hK1eq
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [← hK1eq]
    exact hK₁.2.1
  obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (P : Set G) := by
    by_contra hall
    push Not at hall
    exact hdiag P (hP.isMaxParabolic2 hTK) hP.2.1 hall
  have htK : t ∈ Subgroup.normalizer (oTwoUpper H : Set G) :=
    le_normalizer_oTwoUpper H (hTH.1 ht)
  have htTK : t ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, htK⟩
  have hP' := hP.map_conj htK htTK
  have hne : P.map (MulAut.conj t).toMonoidHom ≠ P := fun he =>
    htP (CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr he)
  obtain ⟨Pj, hPj, -, hgen⟩ := exists_parabolics hF hk htype hTK
  obtain ⟨j, hPeq⟩ := hPj P hP
  obtain ⟨j', hP'eq⟩ := hPj _ hP'
  have hOS : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hjj : j ≠ j' := by
    rintro rfl
    apply hne
    calc P.map (MulAut.conj t).toMonoidHom = _ :=
          (map_comap_modO2Image_of_le hP'.1 (hP'.pCoreOf_le hTK.1 hOS)).symm
      _ = _ := by rw [hP'eq, ← hPeq]
      _ = P := map_comap_modO2Image_of_le hP.1 (hP.pCoreOf_le hTK.1 hOS)
  have hgen' : perfectCore (Pj j) ⊔ perfectCore (Pj j') = ⊤ := by
    fin_cases j <;> fin_cases j'
    · exact absurd rfl hjj
    · exact hgen
    · rw [sup_comm]
      exact hgen
    · exact absurd rfl hjj
  have hL₂K : L₂ ≤ oTwoUpper H := hL₂eq ▸ (perfectCore_le P).trans hP.1
  have hL₂tK : L₂.map (MulAut.conj t).toMonoidHom ≤ oTwoUpper H := by
    rw [← CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp htK]
    exact Subgroup.map_mono hL₂K
  have hL₂t : L₂.map (MulAut.conj t).toMonoidHom =
      perfectCore (P.map (MulAut.conj t).toMonoidHom) := by
    rw [hL₂eq, map_perfectCore]
  have hKle : oTwoUpper H ≤
      L₂ ⊔ L₂.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 (oTwoUpper H) := by
    refine Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top (sup_le hL₂K hL₂tK) ?_
    rw [modO2Image_sup hL₂K hL₂tK, hL₂t, hL₂eq, modO2Image_perfectCore hP.1,
      modO2Image_perfectCore hP'.1, hPeq, hP'eq]
    exact hgen'
  have hCK : conjClosure L₂ T ≤ oTwoUpper H := conjClosure_le fun s hs y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH.1 hs)) y).mp (hL₂K hy)
  have hle : oTwoUpper H ≤ conjClosure L₂ T ⊔ pCoreOf 2 (oTwoUpper H) := by
    refine hKle.trans (sup_le (sup_le ?_ ?_) le_sup_right)
    · exact (le_conjClosure L₂ T).trans le_sup_left
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_left (mem_conjClosure ht hy)
  have hOC : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (conjClosure L₂ T : Set G) :=
    (hOS.trans inf_le_left).trans (le_normalizer_conjClosure L₂ T)
  exact le_antisymm (le_of_perfect_of_le_sup hKperf hle (pCoreOf_isPGroup 2 _) hOC) hCK

theorem stmt5_2_1_par_of (hF : FactL2LieParabolic) (hTwo : Stmt5_2_L2Two) (h510 : Stmt5_1_10) :
    Stmt5_2_1_par := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂ _ X hXK hXP
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨hbend, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  · have hle : L₂ ≤ oTwoUpper H := by
      rw [hKeq]
      exact le_conjClosure L₂ T
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (hTwo G T M L H B D L₂ n hyp hN hK₁ hKeq hlt hbend).2.2 X hXK hXP
    · rw [heq]
      exact hXK
  · obtain ⟨k, hk, htype, -, hMK⟩ := nonBender_type h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    rw [hL₂eq]
    exact (hXP P (hP.isRankOneParabolicOver hF hk htype hTK)).trans
      (normalizer_le_normalizer_perfectCore P)

section Odd

variable {Γ : Type} [Group Γ]

theorem inf_sup_le_of_odd {N B L : Subgroup Γ} (hN : IsPGroup 2 N) (hB : Odd (Nat.card B))
    (hNL : N ≤ Subgroup.normalizer (L : Set Γ)) : B ⊓ (N ⊔ L) ≤ L := by
  rintro b ⟨hbB, hbNL⟩
  rw [sup_comm] at hbNL
  obtain ⟨l, hl, m, hm, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNL).mp hbNL
  have hl₁ : m⁻¹ * l * m ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNL hm)) l).mp hl
    simpa using this
  have hb : l * m = m * (m⁻¹ * l * m) := by group
  obtain ⟨e, he⟩ := hN ⟨m, hm⟩
  have he' : m ^ 2 ^ e = 1 := congrArg Subtype.val he
  obtain ⟨c, hc, hpow⟩ := exists_pow_mul_eq_pow_mul (hNL hm) hl₁ (2 ^ e)
  have hpowL : (l * m) ^ 2 ^ e ∈ L := by
    rw [hb, hpow, he', one_mul]
    exact hc
  have hodd : Odd (orderOf (l * m)) := by
    have := orderOf_dvd_natCard (⟨l * m, hbB⟩ : B)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hB this
  have hcop : Nat.Coprime (2 ^ e) (orderOf (l * m)) :=
    Nat.Coprime.pow_left e
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (Odd.not_two_dvd_nat hodd))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact L.pow_mem hpowL u

theorem le_sup_inf_of_odd {N B L R : Subgroup Γ} (hN : IsPGroup 2 N) (hB : Odd (Nat.card B))
    (hBN : B ≤ Subgroup.normalizer (N : Set Γ)) (hNL : N ≤ Subgroup.normalizer (L : Set Γ))
    (hR : R ≤ N ⊔ B) (hRL : R ≤ L) : R ≤ N ⊔ (B ⊓ L) := by
  intro r hr
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBN).mp (hR hr)
  have hbL : b ∈ L := by
    refine inf_sup_le_of_odd hN hB hNL ⟨hb, ?_⟩
    have hb' : b = a⁻¹ * (a * b) := by group
    rw [hb']
    exact (N ⊔ L).mul_mem (Subgroup.mem_sup_left (N.inv_mem ha)) (Subgroup.mem_sup_right (hRL hr))
  exact (N ⊔ (B ⊓ L)).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hb, hbL⟩)

end Odd

theorem IsL2Choice.inf_le_normalizer (hF : FactL2LieParabolic) (h510 : Stmt5_1_10)
    {G : Type} [Group G] [Finite G] {T M L H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_1_8 G T M L H n) (hN : IsNotation5_1_9 T M L H B D) (hL₂ : IsL2Choice T H L₂) :
    T ⊓ oTwoUpper H ≤ Subgroup.normalizer (L₂ : Set G) := by
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  · refine inf_le_right.trans ?_
    rw [hKeq]
    exact conjClosure_le fun s hs y hy => le_normalizer_of_mem_cComp hK₁
      (map_conj_mem_cComp hK₁ (hTH.1 hs)) ⟨y, hy, rfl⟩
  · obtain ⟨k, hk, htype, -, hMK⟩ := nonBender_type h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    rw [hL₂eq]
    exact ((le_inf inf_le_right Subgroup.le_normalizer).trans hP.2.1).trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))

theorem stmt5_2_6_borel_of (hF : FactL2LieParabolic) (hLie : Stmt5_2_L2Lie)
    (h510 : Stmt5_1_10) : Stmt5_2_6_borel := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  obtain ⟨-, hR, hX⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hSK : sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hMK := hyp.toHyp5_1_8.borel_eq hBorel
  have hL₂K : L₂ ≤ oTwoUpper H := hyp.choice.le_oTwoUpper
  have hSL₂ : sec52S M H ⊓ L₂ = T ⊓ L₂ := by
    calc sec52S M H ⊓ L₂ = sec52S M H ⊓ oTwoUpper H ⊓ L₂ := by
          rw [inf_assoc, inf_eq_right.mpr hL₂K]
      _ = T ⊓ oTwoUpper H ⊓ L₂ := by rw [hSK]
      _ = T ⊓ L₂ := by rw [inf_assoc, inf_eq_right.mpr hL₂K]
  have hborel : borelOf L₂ (sec52S M H) = borelOf L₂ T := by
    unfold borelOf
    rw [hSL₂]
  have hBKle : B ≤ oTwoUpper H := hBK.1.trans inf_le_right
  have hBTK : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    have := hBK.1
    rw [hMK] at this
    exact this.trans inf_le_right
  have hBL₂ : B ≤ Subgroup.normalizer (L₂ : Set G) :=
    hX B (hBKle.trans Subgroup.le_normalizer) hBTK hBK.2.1
  have hTKL₂ := hyp.choice.inf_le_normalizer hF h510 hyp.toHyp5_1_8 hN
  have hTKS : T ⊓ oTwoUpper H ≤ sec52S M H := hSK ▸ inf_le_left
  rw [hborel]
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  ·
    have hRMK : borelOf L₂ T ≤ T ⊓ oTwoUpper H ⊔ B := by
      have hTMK : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
        A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ h.T_le) inf_le_right
      rw [sup_comm, sup_eq_of_isHall_of_isSylowTwoOf hBK hTMK]
      exact le_inf hR (inf_le_left.trans hL₂K)
    exact (le_sup_inf_of_odd hTK.2.1 hBK.2.1 hBTK hTKL₂ hRMK inf_le_left).trans
      (sup_le (hTKS.trans le_sup_left) le_sup_right)
  ·
    intro x hx
    refine Subgroup.mem_sup_right ⟨hx.2, ?_⟩
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hBTK hx.1, Subgroup.le_normalizer hx.2⟩
    rwa [inf_assoc, inf_eq_right.mpr hL₂K] at h1

end CFSG.Quasithin.H13
