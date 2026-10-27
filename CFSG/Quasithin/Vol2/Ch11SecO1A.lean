module

public import CFSG.Quasithin.Vol2.KGNatReal
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Coord

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M] {LM : LinModel D K M}

theorem IsCoord.injective_of_bot {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : D.Gam →* ↥H} {f : W → M} (hf : IsCoord LM H ⊥ π f) : Function.Injective f :=
  fun u v h => mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff u v).mp h))

variable {L V : Subgroup G} [IsMulCommutative ↥V] {Z : Subgroup ↥V}
  {π : D.Gam →* ↥(autOn L V)} {f : ↥V → M}

theorem IsCoord.exists_conj (hf : IsCoord LM (autOn L V) Z π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {l : G} (hl : l ∈ L) :
    ∃ γ : D.Gam, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = LM.lin γ (f v) := by
  obtain ⟨γ, hγ⟩ := hf.exists_lin ⟨SecA.conjV V l (hLV hl), SecA.conjV_mem_autOn hl (hLV hl)⟩
  refine ⟨γ, fun v w hw => ?_⟩
  have hw' : w = SecA.conjV V l (hLV hl) v := Subtype.ext (by rw [SecA.conjV_apply_coe, hw])
  rw [hw']
  exact hγ v

theorem IsCoord.exists_mem (hf : IsCoord LM (autOn L V) Z π f) (γ : D.Gam) :
    ∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G),
      ((π γ : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V l hl ∧
        ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = LM.lin γ (f v) := by
  obtain ⟨l, hl, hlV, he⟩ := SecA.mem_autOn_iff.mp (π γ).2
  refine ⟨l, hl, hlV, he, fun v w hw => ?_⟩
  have hw' : w = ((π γ : ↥(autOn L V)) : MulAut ↥V) v := by
    rw [he]
    exact Subtype.ext (by rw [SecA.conjV_apply_coe, hw])
  rw [hw']
  exact hf.act γ v

end Coord

section Setting

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isMulCommutative (hS : SecD.NatSetting11 G T L I n) : IsMulCommutative ↥(fsuV T I) :=
  hS.elem.1

theorem sq_eq_one (hS : SecD.NatSetting11 G T L I n) (w : ↥(fsuV T I)) : w ^ 2 = 1 :=
  Subtype.ext (by simpa using hS.elem.2 w w.2)

theorem subgroupOf_centralizer_eq_bot (hS : SecD.NatSetting11 G T L I n) :
    (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
  rw [hS.cV] at hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))

theorem realizes_cases [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n) :
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L (fsuV T I)),
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π) := by
  have hZ := subgroupOf_centralizer_eq_bot hS
  obtain ⟨_, hnat⟩ := hS.nat
  rcases hnat with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
    ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
  · rw [hZ] at hπ
    exact Or.inl ⟨K, inferInstance, inferInstance, hK, π, hπ⟩
  · rw [hZ] at hπ
    exact Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hK, π, hπ⟩)
  · rw [hZ] at hπ
    exact Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, π, hπ⟩)

theorem exists_realizes_sl3 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π := by
  have hn : 2 ≤ n := hS.one_lt
  have hZ := subgroupOf_centralizer_eq_bot hS
  obtain ⟨_, hnat⟩ := hS.nat
  rcases hnat with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · rw [hZ] at hπ
    exact ⟨K, inferInstance, inferInstance, hK, π, hπ⟩
  · exact (SecA.kind_not_SL3_Sp4 (by omega) hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (SecA.kind_not_SL3_G2 factG2DerivedOrder_holds hn hk
      ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem exists_realizes_sp4 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I)),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π := by
  have hn : 2 ≤ n := hS.one_lt
  have hZ := subgroupOf_centralizer_eq_bot hS
  obtain ⟨_, hnat⟩ := hS.nat
  rcases hnat with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact (SecA.kind_not_SL3_Sp4 (by omega) ⟨K, inferInstance, inferInstance, hK, he⟩ hk).elim
  · rw [hZ] at hπ
    exact ⟨K, inferInstance, inferInstance, hK, π, hπ⟩
  · exact (SecA.kind_not_Sp4_G2 factG2DerivedOrder_holds hn hk
      ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem exists_coord_sl3 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))) (f : ↥(fsuV T I) → (Fin 3 → K)),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π ∧
          IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := exists_realizes_sl3 hS hk
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  exact ⟨K, inferInstance, inferInstance, hK, π, f, hπ, hf⟩

theorem exists_coord_sp4 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))) (f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π ∧
          IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := exists_realizes_sp4 hS hk
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  exact ⟨K, inferInstance, inferInstance, hK, π, f, hπ, hf⟩

theorem inf_centralizer_eq (hS : SecD.NatSetting11 G T L I n) :
    L ⊓ Subgroup.centralizer (fsuV T I : Set G) = pCoreOf 2 L := by
  obtain ⟨e⟩ := hS.quot
  exact SecA.inf_centralizer_eq_pCoreOf hS.le_normalizer e

theorem isPGroup_inf_centralizer (hS : SecD.NatSetting11 G T L I n) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  rw [inf_centralizer_eq hS]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L

theorem isSylowTwoOf_inf (hS : SecD.NatSetting11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
  B6.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer hS.normal)

theorem isSylowTwoOf_P (hS : SecD.NatSetting11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) (fsuV T I)) (autOn L (fsuV T I)) :=
  SecA.isSylowTwoOf_autOn hS.le_normalizer (isSylowTwoOf_inf hS)

theorem isFlagW_of_isVi (hS : SecD.NatSetting11 G T L I n) {i : ℕ} {U : Subgroup G}
    (hU : IsVi T L I n i U) :
    SecA.IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) i
      (U.subgroupOf (fsuV T I)) := by
  have hL := hS.le_normalizer
  rw [← subgroupOf_centralizer_eq_bot hS]
  refine ⟨fun z hz => SecA.IsVi.cV_le hU ⟨z.2, hz⟩, ?_, ?_, fun g hg => ?_⟩
  · have := (SecA.isEndStable_iff hL _ U).mp (SecA.IsVi.isEndStable hU)
    rwa [SecA.inf_centralizer_subgroupOf] at this
  · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf (SecA.IsVi.le_fsuV hU),
      SecA.IsVi.relIndex_eq hU, pow_mul]
  · obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hg
    exact (SecA.conjV_mem_stabW_iff (SecA.IsVi.le_fsuV hU) hxV).mpr
      (SecA.IsVi.le_normalizer hU hx.1)

end Setting

end CFSG.Quasithin.Vol2.Ch11.SecO1
