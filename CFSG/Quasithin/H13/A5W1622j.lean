module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.H13.A5W1622h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem isSylowTwoOf_sylowA :
    IsSylowTwoOf (L246.C123.sylowA) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [L246.C123.card_sylowA]; norm_num), ?_⟩
  rw [show (L246.C123.sylowA.subgroupOf ⊤).index = L246.C123.sylowA.index from
    Subgroup.relIndex_top_right _]
  have hidx := Subgroup.card_mul_index (L246.C123.sylowA)
  rw [L246.C123.card_sylowA, L246.C123.card_A7] at hidx
  omega

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_excA7Block
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two)
    (h132fsu : Stmt13_3_2_three_fsu) (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1)
    (h1327 : Stmt13_2_7) (h39 : Vol2Native.A39ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsExcA7Block K₀) : False := by
  classical
  obtain ⟨hshort, ⟨α, hα, hker⟩, hidx⟩ := hblk
  have hcard : Nat.card (blockQuot K₀) = 16 := hidx
  refine S.false_of_blockModel h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀ hTK₀
    hz hLvK₀ hchar hshort α hα hker isSylowTwoOf_sylowA ?_
  intro n p hn hp hnS hpS x hx
  set act := blockLiftAct hshort α hα hker with hact
  have hfix : ∀ v : blockQuot K₀, (∀ g, act g v = v) → v = 1 := fun v hv =>
    fixed_eq_one_of_short hshort (by rw [hcard]; norm_num) fun ℓ => by
      rw [← blockLiftAct_apply hshort α hα hker ℓ]
      exact hv _
  have hinj : Function.Injective act := by
    have := L246.C123.isSimple_A7
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal act.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      apply hn
      refine hfix n fun g => ?_
      have hg : g ∈ act.ker := h ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker.mp hg, MulAut.one_apply]
  let _ : CommGroup (blockQuot K₀) :=
    { (inferInstance : Group (blockQuot K₀)) with mul_comm := blockQuot_comm hshort }
  have hnp : p = n :=
    L246.C123.fixU_eq_of_card_eight act hcard hinj L246.C123.card_sylowA hn
      (L246.C123.mem_fixU.mpr hnS) (L246.C123.mem_fixU.mpr hpS) hp
  rw [hnp]
  exact hx

end Setting

end CFSG.Quasithin.H13.A5
