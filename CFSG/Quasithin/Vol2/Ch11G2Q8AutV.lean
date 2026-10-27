module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NormS
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2W

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {K : Type} [Field K] [CharP K 2]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem exists_smul_frob_of_normalizes [Finite K] (hf : IsCoord (lmG K) H Z π f) {c₀ : K}
    (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (τ : MulAut W) (hτ : ∀ z ∈ Z, τ z ∈ Z) (hτ' : ∀ z ∈ Z, τ⁻¹ z ∈ Z)
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) (hτH' : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H) :
    ∃ (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K), c ≠ 0 ∧
      ∀ w, f (τ w) = c • g2Act γ (frobQ σ (f w)) := by
  have hx0 : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨σ₀, hσ₀⟩ := hf.exists_semilinear (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hx0 τ hτ hτ' hτH'
  have hσinj : Function.Injective σ₀ := σ₀.injective
  have hTf : ∀ w, hf.autMap τ hτ (f w) = f (τ w) := hf.autMap_apply τ hτ
  have hT'f : ∀ w, hf.autMap τ⁻¹ hτ' (f w) = f (τ⁻¹ w) := hf.autMap_apply τ⁻¹ hτ'
  have hTb : Function.Bijective (hf.autMap τ hτ) := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := hf.surj x
      obtain ⟨v, rfl⟩ := hf.surj y
      have h1 := congrArg (hf.autMap τ⁻¹ hτ') hxy
      rwa [hTf, hTf, hT'f, hT'f, MulAut.inv_apply_self, MulAut.inv_apply_self] at h1
    · obtain ⟨u, rfl⟩ := hf.surj x
      exact ⟨f (τ⁻¹ u), by rw [hTf, MulAut.apply_inv_self]⟩
  have hT : ∀ γ : ↥(cayleyGroup K), ∃ γ' : ↥(cayleyGroup K),
      ∀ w, hf.autMap τ hτ (g2Act γ w) = g2Act γ' (hf.autMap τ hτ w) := by
    intro γ
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨_, hτH _ (rhoG hc0 hc1 π γ).2⟩
    refine ⟨δ, fun w => ?_⟩
    obtain ⟨x, rfl⟩ := hf.surj w
    rw [← IsCoord.actG hf hc0 hc1, hTf, hTf, ← IsCoord.actG hf hc0 hc1, hδ]
    change f (τ _) = f ((τ * _ * τ⁻¹) (τ x))
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  obtain ⟨c, γ, hc, hcγ⟩ := exists_eq_smul_frob_of_normG2 hK hn (hf.autMap τ hτ) hTb
    (RingEquiv.ofBijective σ₀ ⟨hσinj, Finite.surjective_of_injective hσinj⟩)
    (fun c x => hσ₀ c x) hT
  exact ⟨c, γ, _, hc, fun w => by rw [← hTf, hcγ]⟩

end Real

theorem exists_coord_flagG2 {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ V₃ : Subgroup G}
    {n : ℕ} (hfl : SecB.FlagG2 L V X T V₁ V₂ V₃ n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)) (f : ↥V → (Ix3 → K))
        (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
        (c₀ : K) (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K)),
        (∀ x : MulAut ↥V, x ∈ autOn (T ⊓ L) V ↔
          ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥(autOn L V)) : MulAut ↥V)) ∧
        V₁.subgroupOf V = hf.pre (gmapG g (stdF K 1)).toAddSubgroup ∧
        V₂.subgroupOf V = hf.pre (gmapG g (stdF K 2)).toAddSubgroup ∧
        V₃.subgroupOf V = hf.pre (gmapG g (stdF K 3)).toAddSubgroup := by
  obtain ⟨hcomm, hnat⟩ := hfl.nat
  refine ⟨hcomm, ?_⟩
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hLV := hfl.le_normalizer
  have h₁ : V₁ ≤ V := hfl.le₁₂.trans (hfl.le₂₃.trans hfl.le₃)
  have h₂ : V₂ ≤ V := hfl.le₂₃.trans hfl.le₃
  obtain ⟨K, _, _, hK, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V),
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | hG2
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK,
          ⟨(MulEquiv.ofBijective π hbij).symm.trans
            (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hfl.kind).elim
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩
        hfl.kind).elim
    · exact hG2
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1
    (SecA.isSylowTwoOf_autOn hLV hTL)
  have hflag : ∀ {i : ℕ} {U : Subgroup G}, U ≤ V →
      V ⊓ Subgroup.centralizer (L : Set G) ≤ U →
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) →
      T ≤ Subgroup.normalizer (U : Set G) →
      U.subgroupOf V = hf.pre (gmapG g (stdF K i)).toAddSubgroup := by
    intro i U hUV hCU hst hidx hTU
    have hFW : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) (Nat.card K) i (U.subgroupOf V) := by
      refine ⟨fun z hz => hCU ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
      · have := (SecA.isEndStable_iff hLV _ U).mp hst
        rwa [SecA.inf_centralizer_subgroupOf] at this
      · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, hK,
          pow_mul]
      · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
        exact (SecA.conjV_mem_stabW_iff hUV hyV).mpr (hTU hy.1)
    obtain ⟨S, hS, hc, hU⟩ := exists_eq_preG_of_isFlagW hsq hf hc0 hc1 hg hFW
    rw [hU, eq_stdF_of_card hS hc]
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, c₀, hc0, hc1, g, hg,
    hflag h₁ hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one]) hfl.T_le_V₁,
    hflag h₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂ hfl.T_le_V₂,
    hflag hfl.le₃ (hfl.cV_le.trans (hfl.le₁₂.trans hfl.le₂₃)) hfl.stable₃ hfl.index₃
      hfl.T_le_V₃⟩

section FlagReal

variable {G : Type} [Group G] {L V : Subgroup G} [IsMulCommutative ↥V]
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)} {Z : Subgroup ↥V}

theorem exists_rhoG_eq_conjV (hf : IsCoord (lmG K) (autOn L V) Z π f) {c₀ : K}
    (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {x : G} (hxL : x ∈ L)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    ∃ a : ↥(cayleyGroup K),
      ((rhoG hc0 hc1 π a : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V x hxV := by
  obtain ⟨a, ha⟩ := (rhoG_bijective hf hc0 hc1).2
    ⟨SecA.conjV V x hxV, SecA.conjV_mem_autOn hxL hxV⟩
  exact ⟨a, by rw [ha]⟩

theorem subgroupOf_conjSubgroup_eq (hf : IsCoord (lmG K) (autOn L V) Z π f) {c₀ : K}
    (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {U : Subgroup G} {g : ↥(cayleyGroup K)}
    {S : Submodule K (Ix3 → K)} (hU : U.subgroupOf V = hf.pre (gmapG g S).toAddSubgroup)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) {a : ↥(cayleyGroup K)}
    (ha : ((rhoG hc0 hc1 π a : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V x hxV) :
    (conjSubgroup U x).subgroupOf V = hf.pre (gmapG (a⁻¹ * g) S).toAddSubgroup := by
  ext w
  rw [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff]
  change _ ↔ f w ∈ gmapG (a⁻¹ * g) S
  have h1 : x * (w : G) * x⁻¹ ∈ U ↔ SecA.conjV V x hxV w ∈ U.subgroupOf V := by
    rw [Subgroup.mem_subgroupOf, SecA.conjV_apply_coe]
  rw [h1, hU]
  change f (SecA.conjV V x hxV w) ∈ gmapG g S ↔ _
  rw [← ha, IsCoord.actG hf hc0 hc1, mem_gmapG, mem_gmapG, _root_.mul_inv_rev, inv_inv,
    g2Act_mul_apply]

omit [IsMulCommutative ↥V] in
theorem conjV_mem_centralizer {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) {z : ↥V}
    (hz : z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V) :
    SecA.conjV V y hyV z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := by
  rw [Subgroup.mem_subgroupOf, SecA.conjV_apply_coe, Subgroup.mem_centralizer_iff]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
  intro l hl
  have h1 : y⁻¹ * l * y ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyL) l).mp hl
    rwa [inv_inv] at this
  have h2 := hz _ h1
  calc l * (y * (z : G) * y⁻¹) = y * ((y⁻¹ * l * y) * z) * y⁻¹ := by group
    _ = y * ((z : G) * (y⁻¹ * l * y)) * y⁻¹ := by rw [h2]
    _ = y * z * y⁻¹ * l := by group

omit [IsMulCommutative ↥V] in
theorem conjV_mul_conjV_inv_mem {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) {h : MulAut ↥V} (hh : h ∈ autOn L V) :
    SecA.conjV V y hyV * h * (SecA.conjV V y hyV)⁻¹ ∈ autOn L V := by
  obtain ⟨x, hxL, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hh
  rw [SecA.conjV_conj]
  exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hyL x).mp hxL) _

theorem exists_smul_frob_conjV [Finite K] {X : Subgroup G}
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {e : G} (he : e ∈ X ⊓ Subgroup.normalizer (V : Set G)) :
    ∃ (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K), c ≠ 0 ∧
      ∀ w, f (SecA.conjV V e he.2 w) = c • g2Act γ (frobQ σ (f w)) := by
  have heL := hXN he
  have heL' : e⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ heL
  have hinv : (SecA.conjV V e he.2)⁻¹ = SecA.conjV V e⁻¹ (Subgroup.inv_mem _ he.2) :=
    (SecA.conjV_inv V he.2).symm
  refine exists_smul_frob_of_normalizes hf hc0 hc1 hK hn (SecA.conjV V e he.2)
    (fun z hz => conjV_mem_centralizer heL he.2 hz)
    (fun z hz => by rw [hinv]; exact conjV_mem_centralizer heL' _ hz)
    (fun h hh => conjV_mul_conjV_inv_mem heL he.2 hh) fun h hh => ?_
  have := conjV_mul_conjV_inv_mem heL' (Subgroup.inv_mem _ he.2) hh
  rwa [← hinv, inv_inv] at this

end FlagReal

end CFSG.Quasithin.Vol2.Ch11.G2Q8
