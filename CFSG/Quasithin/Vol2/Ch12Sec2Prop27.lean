module

public import CFSG.Quasithin.Vol2.Ch12Sec2Affine
public import CFSG.Quasithin.Vol2.Ch12Sec2SettingK
public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem exists_section_of_complement {G H : Type} [Group G] [Group H] {L V X : Subgroup G}
    (α : ↥L →* H) (hα : Function.Surjective α)
    (hker : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ V) (hXL : X ≤ L) (hXV : X ⊓ V = ⊥)
    (hXVL : X ⊔ V = L) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ s : H →* ↥L, ∀ g, α (s g) = g := by
  have hbij : Function.Bijective (α.comp (Subgroup.inclusion hXL)) := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro x hx
      have h2 : (x : G) ∈ X ⊓ V := ⟨x.2, (hker _).mp hx⟩
      rw [hXV, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    · intro g
      obtain ⟨l, rfl⟩ := hα g
      have hl : (l : G) ∈ ((X ⊔ V : Subgroup G) : Set G) := by rw [hXVL]; exact l.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right X V (hXL.trans hLV)] at hl
      obtain ⟨x, hx, v, hv, hxv⟩ := hl
      have hvL : v ∈ L := by
        have : v = x⁻¹ * l := by rw [← hxv]; group
        rw [this]
        exact L.mul_mem (L.inv_mem (hXL hx)) l.2
      refine ⟨⟨x, hx⟩, ?_⟩
      have hl' : l = ⟨x, hXL hx⟩ * ⟨v, hvL⟩ := Subtype.ext hxv.symm
      rw [hl', map_mul, (hker ⟨v, hvL⟩).mpr hv, mul_one]
      rfl
  refine ⟨(Subgroup.inclusion hXL).comp (MulEquiv.ofBijective _ hbij).symm.toMonoidHom,
    fun g => ?_⟩
  exact (MulEquiv.ofBijective _ hbij).apply_symm_apply g

theorem centralizer_subgroupOf_eq {G : Type} [Group G] {L : Subgroup G} (z : G) (hz : z ∈ L) :
    (Subgroup.centralizer ({z} : Set G)).subgroupOf L =
      Subgroup.centralizer ({⟨z, hz⟩} : Set ↥L) := by
  ext l
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem eq_one_of_mulVec_eq_self {n : ℕ} {K : Type} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ v, A.mulVec v = v) : A = 1 :=
  Matrix.ext_of_mulVec_single fun i => by rw [h, Matrix.one_mulVec]

theorem mem_statedSL_zmod_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) :
    g ∈ Assembly.LowTwoRank.StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

@[expose] def tr10M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def tr10 : GL (Fin 4) (ZMod 2) :=
  ⟨tr10M, tr10M, by decide, by decide⟩

theorem tr10_mulVec : tr10M.mulVec (Pi.single 0 1) ≠ Pi.single 0 1 := by
  decide

theorem card_multiplicative_fin_four : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  simp

theorem stmt12_2_27_four (hAsc : Asc94_M24He_L52TypeK) (h1226 : Stmt12_2_6) {G : Type} [Group G]
    [Finite G] {T L V : Subgroup G} (hH : Hyp1223 G T L V) (hE : NoEscape12_2_13 L V)
    (hB : IsLnBlock L 4) (hV : Nat.card V = 2 ^ 4)
    (hML : Subgroup.normalizer (L : Set G) = L) (hVO : V = pCoreOf 2 L)
    (hX : ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L) :
    Nonempty (G ≃* NativeSporadic.M24) ∨ LieModel G .PSL 5 2 1 := by
  obtain ⟨X, hXL, hXV, hXVL⟩ := hX
  obtain ⟨hS, α, hαs, hαker, β, hβs, -, hβeq⟩ := hB
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, -⟩ := hS
  have hLV := le_normalizer_of_hyp1223 hH
  have hQ : blockQ L = V := by rw [blockQ, hVO]
  have hU : blockU L = V := by
    rw [blockU, hQ]
    exact commutator_eq_of_hyp1223 hH
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := by
    have := hUQ
    rw [hU, hQ] at this
    exact this.trans inf_le_right
  have : IsMulCommutative ↥V := Subgroup.le_centralizer_iff_isMulCommutative.mp hVC
  have hVL : V ≤ L := by rw [hVO]; exact Subgroup.map_subtype_le _
  have hUL : blockU L ≤ L := hU.le.trans hVL
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by rw [hU]; exact hLV
  have hmemV : ∀ l : ↥L, l ∈ CFSG.pCore 2 ↥L ↔ (l : G) ∈ V := fun l => by
    rw [hVO]
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  have hαker' : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ V := fun l => by
    rw [← MonoidHom.mem_ker, hαker]
    exact hmemV l
  have hker : α.ker = (blockU L).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, hαker', Subgroup.mem_subgroupOf, hU]
  obtain ⟨s, hs⟩ := exists_section_of_complement α hαs hαker' hXL hXV hXVL hLV
  have hβbij : Function.Bijective β := hβs.bijective_of_nat_card_le (by
    rw [card_multiplicative_fin_four, hU, hV]
    norm_num)
  obtain ⟨z, hz⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hzV : (z : G) ∈ V := by rw [← hU]; exact z.2
  have hz1 : (z : G) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    have h2 := congrArg Multiplicative.toAdd hz
    rw [h1, map_one, toAdd_one, toAdd_ofAdd] at h2
    exact absurd (congrFun h2 0) (by decide)
  have hord : orderOf (z : G) = 2 := orderOf_eq_prime (hU2 _ z.2) hz1
  have hCL : Subgroup.centralizer ({(z : G)} : Set G) ≤ L :=
    (hE (z : G) hzV hz1).trans hML.le
  have e : ↥(Subgroup.centralizer ({(z : G)} : Set G)) ≃*
      ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) :=
    ((Subgroup.subgroupOfEquivOfLe hCL).symm.trans
      (MulEquiv.subgroupCongr (centralizer_subgroupOf_eq (z : G) (hUL z.2)))).trans
      ((centralizerEquivGL hLU α hker s hs β hβeq hUL hβbij z hz).trans
        centralizerTransvectionEquiv.symm)
  have hVQ : V ≤ pCoreOf 2 (Subgroup.centralizer ({(z : G)} : Set G)) := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ (hCL.trans hLV) (IsPGroup.of_card hV)
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv) (z : G) hzV).symm
  obtain ⟨ℓ, hℓ⟩ := hαs ⟨tr10, mem_statedSL_zmod_two tr10⟩
  have hwmem : (ℓ : G) * z * (ℓ : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (hLU ℓ.2) z).mp z.2
  have hβw : Multiplicative.toAdd (β ⟨_, hwmem⟩) = tr10M.mulVec (Pi.single 0 1) := by
    have h := hβeq ℓ z ⟨_, hwmem⟩ rfl
    rw [hℓ, hz, toAdd_ofAdd] at h
    exact h
  have hwz : (ℓ : G) * z * (ℓ : G)⁻¹ ≠ z := by
    intro h
    have h1 : (⟨_, hwmem⟩ : ↥(blockU L)) = z := Subtype.ext h
    rw [h1, hz, toAdd_ofAdd] at hβw
    exact tr10_mulVec hβw.symm
  have hg : ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({(z : G)} : Set G)) ∧
      g⁻¹ * z * g ≠ z := by
    refine ⟨(ℓ : G)⁻¹, ?_, ?_⟩
    · rw [inv_inv]
      exact hVQ (by rw [← hU]; exact hwmem)
    · rw [inv_inv]
      exact hwz
  have hV1 : V ≠ ⊥ := hH.irrPlus.2.1
  have hNL : Subgroup.normalizer (V : Set G) ≤ L := by
    have h6 := (h1226 G T L V hH).2 V (Subgroup.normalizer (V : Set G)) hV1 le_rfl le_rfl
    rw [inf_idem, hML] at h6
    exact inf_eq_left.mp h6
  have hCV : ∀ x : ↥L, (x : G) ∈ Subgroup.centralizer (V : Set G) → (x : G) ∈ V := by
    intro x hx
    have hfix : ∀ v : Fin 4 → ZMod 2,
        ((α x : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v := by
      intro v
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
      have huV : (u : G) ∈ V := by rw [← hU]; exact u.2
      have hxu := Subgroup.mem_centralizer_iff.mp hx (u : G) huV
      have hcomm : (u : G) = (x : G) * u * (x : G)⁻¹ := by
        calc (u : G) = (u : G) * x * (x : G)⁻¹ := by group
          _ = x * u * (x : G)⁻¹ := by rw [hxu]
      have := hβeq x u u hcomm
      rw [hu, toAdd_ofAdd] at this
      exact this.symm
    have hα1 : α x = 1 :=
      Subtype.ext (Units.ext (eq_one_of_mulVec_eq_self _ hfix))
    exact (hαker' x).mp hα1
  have hE16 : ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* GL (Fin 4) (ZMod 2),
        Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
          (Subgroup.normalizer (E : Set G)) := by
    refine ⟨V, ⟨inferInstance, fun x hx => hU2 x (by rw [hU]; exact hx)⟩,
      hV.trans (by norm_num), (Assembly.LowTwoRank.StatedSL 4 (ZMod 2)).subtype.comp
        (α.comp (Subgroup.inclusion hNL)), ?_, ?_⟩
    · intro g
      obtain ⟨l, hl⟩ := hαs ⟨g, mem_statedSL_zmod_two g⟩
      refine ⟨⟨l, hLV l.2⟩, ?_⟩
      have h1 : Subgroup.inclusion hNL ⟨(l : G), hLV l.2⟩ = l := Subtype.ext rfl
      show ((α (Subgroup.inclusion hNL ⟨(l : G), hLV l.2⟩) : GL (Fin 4) (ZMod 2))) = g
      rw [h1, hl]
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have key : ((Assembly.LowTwoRank.StatedSL 4 (ZMod 2)).subtype.comp
          (α.comp (Subgroup.inclusion hNL))) x = 1 ↔ α (Subgroup.inclusion hNL x) = 1 :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      rw [key, hαker']
      exact ⟨fun h => hVC h, fun h => hCV _ h⟩
  obtain ⟨-, h2⟩ := hAsc G (z : G) hH.simple hH.qtke.1 hord ⟨e⟩ hg
  rcases (h2 hE16).2 with h | h
  · exact Or.inr h
  · exact Or.inl h

end CFSG.Quasithin.H13
