module

public import CFSG.Quasithin.Vol2.Ch10SecKRTg
public import CFSG.Quasithin.Vol2.Ch10SecKRTc
public import CFSG.Quasithin.Vol2.Ch10SecKRTf
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

theorem b56Card_of_lieModel {X : Type} [Group X] {n : ℕ} (h : LieModel X .PSL 2 2 n) :
    SecC.C10KH.B56Card (Nat.card X) := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hn, hc⟩ := Ch11.SecA.card_of_isPSL_two_two h
    refine Or.inl ⟨n, hn, ?_⟩
    rw [hc, Ch11.SecA.oSL2, pow_mul, ← pow_mul 2 n 2, mul_comm n 2, pow_mul]
  all_goals exact absurd h0 (by norm_num)

theorem b56Card_of_statedSL3 {X : Type} [Group X] {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
    SecC.C10KH.B56Card (Nat.card X) := by
  refine Or.inr (Or.inl ⟨m, SecC.C10KH.one_le_of_card_field hF, ?_⟩)
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF]

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

theorem card_of_not_normal (h56 : AsB56) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1022 : Stmt10_2_2) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hTJ : ¬ T ≤ Subgroup.normalizer (J : Set G)) :
    ∃ M : ℕ, SecC.C10KH.B56Card M ∧
      (Nat.card ↥(modO2Image M₁ J) = M ∨ Nat.card ↥(modO2Image M₁ J) = 3 * M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, hne, hJt, horb, hsJ⟩ := orbit h37 h38 cfg hTJ
  set Jt := J.map (MulAut.conj t).toMonoidHom with hJtdef
  have hTN := T_le_normalizer_sup cfg ht horb
  have hH₀ : (J ⊔ Jt) ⊔ T ≤ M₁ := sup_le (sup_le (J_le cfg) (le_of_mem_cComp hJt)) (T_le cfg)
  have ff := ffSet h1022 cfg le_sup_right hH₀
    (H_le_of cfg le_sup_right ((conjClosure_K_le cfg horb).trans le_sup_left))
  set V := conjClosure (quasithinOmegaOneCenter T) ((J ⊔ Jt) ⊔ T) with hVdef
  have hel : IsElemAbelian 2 V := ff.elem
  have : IsMulCommutative ↥V := hel.1
  have hH₀V : (J ⊔ Jt) ⊔ T ≤ Subgroup.normalizer (V : Set G) := ff.red.2.1
  have hNV : J ⊔ Jt ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hH₀V
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hNV
  have hJtV : Jt ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hNV
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hH₀V (Subgroup.mem_sup_right ht)
  have hOV : pCoreOf 2 M₁ ≤ Subgroup.centralizer (V : Set G) :=
    ff.o2.trans (pCoreOf_le_centralizer_of_isTwoReducedIn ff.red)
  have hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G) :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp cfg.hJ)).trans hOV
  have hnt : ¬ J ≤ Subgroup.centralizer (V : Set G) := fun h => ff.K_not (cfg.hKJ.trans h)
  obtain ⟨π, hπ⟩ := exists_pi cfg hel hJV hO
  obtain ⟨e⟩ := modO2_mulEquiv cfg.hJ
  have hsJb : IsSimpleGroup ↥(modO2Image M₁ J) := e.symm.isSimpleGroup
  obtain ⟨x, hx⟩ := exists_ne_one_autI hel hJV hnt
  have hπi : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).mp h
    · exfalso
      obtain ⟨y, rfl⟩ := hπ x
      exact hx (show y ∈ π.ker from h ▸ Subgroup.mem_top y)
  set eπ := MulEquiv.ofBijective π ⟨hπi, hπ⟩
  set K₁ := autOn J V with hK₁
  set K₂ := autOn Jt V with hK₂
  have hs₁ : IsSimpleGroup ↥K₁ := eπ.symm.isSimpleGroup
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := by
    rw [hK₁, ← S153D.autOn_commutator hJV hJV, perfect_of_mem_cComp cfg.hJ]
  have hnc₁ : ∃ a b : ↥K₁, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hb : ⁅K₁, K₁⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        congrArg Subtype.val (hcon ⟨b, hb⟩ ⟨a, ha⟩)
    rw [hperf₁] at hb
    exact (Subgroup.nontrivial_iff_ne_bot K₁).mp hs₁.toNontrivial hb
  obtain ⟨hq₁, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc₁
  set s := conjAct V ⟨t, htV⟩ with hs
  have hK₂eq : K₂ = K₁.map (MulAut.conj s).toMonoidHom := H13.autOn_map_conj htV
  have hsX : s ∈ autOn ((J ⊔ Jt) ⊔ T) V :=
    CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨t, htV⟩, Subgroup.mem_sup_right ht, rfl⟩
  let c : ↥K₁ ≃* ↥(K₁.map (MulAut.conj s).toMonoidHom) :=
    K₁.equivMapOfInjective _ (MulAut.conj s).injective
  have hq₂ : CFSG.IsQuasisimple ↥K₂ := by
    rw [hK₂eq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv c hq₁
  have hs₂ : IsSimpleGroup ↥K₂ := by
    rw [hK₂eq]
    exact c.symm.isSimpleGroup
  have hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a :=
    autOn_commute' ((commutator_le_pCoreOf h37 cfg hJt hne).trans hOV)
  have hinf : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyz : (⟨y, hy.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2 y hy.2)
    rw [hZ, Subgroup.mem_bot] at hyz
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hyz)
  set X := autOn ((J ⊔ Jt) ⊔ T) V with hX
  have hKsup : autOn (J ⊔ Jt) V = K₁ ⊔ K₂ := H13.autOn_sup hJV hJtV
  have hKX : K₁ ⊔ K₂ ≤ X := hKsup ▸ InternalSec.autOn_le_autOn_of_le le_sup_left
  have hNN : (J ⊔ Jt) ⊔ T ≤ Subgroup.normalizer ((J ⊔ Jt : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hTN
  have hXK : X ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    rw [← hKsup]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => InternalSec.autOn_normal_of (U := V) hNN y hy k hk, fun hk => ?_⟩
    have := InternalSec.autOn_normal_of (U := V) hNN y⁻¹ (X.inv_mem hy) _ hk
    simpa [mul_assoc] using this
  have h2X : ∀ y ∈ X, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₂ := by
    rw [← hKsup]
    exact two_pow_mem_autOn cfg.hyp.fsu.sylow.1 hTN
  have hO2 : pCoreOf 2 X = ⊥ := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot ff.red
  obtain ⟨A, hA⟩ := exists_ffStarOffender hel ff.red ff.sylow ff.thompson
  obtain ⟨hK₁J, hK₂J⟩ := le_ffJ_of_simple hs₁ hperf₁ hsX hK₂eq hc hKX hXK h2X hO2 hA
  have hJK := (B6.ffJ_le X).trans hXK
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hel.2 v v.2)
  have hJne : ffJ X ≠ ⊥ := fun h => hA.2.1 (le_bot_iff.mp (h ▸ B6.le_ffJ hA))
  have hcases := h56 ↥V hV2 (ffJ X) hJne (InternalSec.b53Hyp_ffJ_autOn hH₀V ff.sqtk hO2)
  have hcard : Nat.card ↥(modO2Image M₁ J) = Nat.card ↥K₁ := Nat.card_congr eπ.toEquiv
  rcases Ch3Sec3.type_of_b56Cases hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hcases with
    ⟨n', hL⟩ | ⟨m', F, _, _, hF, ⟨eF⟩⟩
  · exact ⟨_, b56Card_of_lieModel hL, Or.inl hcard⟩
  · exact ⟨_, b56Card_of_statedSL3 hF eF, Or.inl hcard⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
