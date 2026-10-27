module

public import CFSG.Quasithin.H13.A5W1622h
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six
public import CFSG.Quasithin.EmptyFaithful.ModBLin
public import CFSG.Quasithin.EmptyFaithful.ModBAlt6

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Fischer
open scoped Matrix

theorem modelFix_hatA6 {N : Type} [CommGroup N] [Finite N] (hN2 : ∀ n : N, n ^ 2 = 1)
    (hcard : Nat.card N = 2 ^ 6) {X : Type} [Group X] [Finite X]
    (hX : IsHat X ↥(alternatingGroup (Fin 6))) (act : X →* MulAut N)
    (hinj : Function.Injective act) {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤) :
    ModelFix act S₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive N) := H13.zmod2ModuleOfExp hN2
  have : Finite (Additive N) := Finite.of_equiv N Additive.ofMul
  have hW : Nat.card (Additive N) = 2 ^ 6 := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  let ρ : X →* (Additive N →ₗ[ZMod 2] Additive N) := H13.linAutHom.comp act
  have hρ : Function.Injective ρ := H13.linAutHom_injective.comp hinj
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hX
  obtain ⟨Φ, μ, hμ, -, hΦ, hscal⟩ := H13.exists_f4_model hW hq.1 ρ hρ hZ
  have hS₀nc : ¬ ∀ s ∈ S₀, ∀ t ∈ S₀, s * t = t * s := by
    intro hc
    let π : X →* ↥(alternatingGroup (Fin 6)) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hidx : ¬ 2 ∣ S₀.index := by
      have := hS₀.2.2
      rwa [show (S₀.subgroupOf ⊤).index = S₀.index from Subgroup.relIndex_top_right S₀] at this
    let P : Sylow 2 X := hS₀.2.1.toSylow hidx
    apply ModB.alt6_sylow_not_comm (P.mapSurjective hπ)
    intro a ha b hb
    rw [Sylow.coe_mapSurjective] at ha hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    rw [← map_mul, ← map_mul, hc s hs t ht]
  refine modelFix_of_center fun n p hn hp hnS hpS => ?_
  have hΦact : ∀ (g : X) (w : N), Φ (Additive.ofMul (act g w)) =
      ((μ g : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ
        Φ (Additive.ofMul w) := fun g w => hΦ g (Additive.ofMul w)
  have hfixΦ : ∀ w : N, (∀ s ∈ S₀, act s w = w) → ∀ s : ↥S₀,
      ((μ.comp S₀.subtype s : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4) *ᵥ Φ (Additive.ofMul w) = Φ (Additive.ofMul w) := by
    intro w hw s
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← hΦact, hw s s.2]
  have hne : ∀ w : N, w ≠ 1 → Φ (Additive.ofMul w) ≠ 0 := by
    intro w hw h
    apply hw
    have h0 : Additive.ofMul w = 0 := Φ.injective (h.trans Φ.map_zero.symm)
    exact h0
  by_cases hli : LinearIndependent F4 ![Φ (Additive.ofMul n), Φ (Additive.ofMul p)]
  · exfalso
    apply hS₀nc
    intro s hs t ht
    have h := ModB.commute_of_fixing F4.card hS₀.2.1 (μ.comp S₀.subtype) hli
      (hfixΦ n hnS) (hfixΦ p hpS) ⟨s, hs⟩ ⟨t, ht⟩
    apply hμ
    rw [map_mul, map_mul]
    exact h
  obtain ⟨c, hc⟩ : ∃ c : F4, Φ (Additive.ofMul n) = c • Φ (Additive.ofMul p) := by
    rw [LinearIndependent.pair_iff] at hli
    push Not at hli
    obtain ⟨s, t, hst, hst0⟩ := hli
    by_cases hs : s = 0
    · exfalso
      have ht : t ≠ 0 := hst0 hs
      rw [hs, zero_smul, zero_add, smul_eq_zero] at hst
      rcases hst with h | h
      · exact ht h
      · exact hne p hp h
    · refine ⟨-(s⁻¹ * t), ?_⟩
      calc Φ (Additive.ofMul n) = s⁻¹ • (s • Φ (Additive.ofMul n)) := by
            rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(t • Φ (Additive.ofMul p))) := by rw [eq_neg_of_add_eq_zero_left hst]
        _ = -(s⁻¹ * t) • Φ (Additive.ofMul p) := by rw [smul_neg, smul_smul, neg_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hne n hn hc
  obtain ⟨z, hz, hμz⟩ : ∃ z ∈ Subgroup.center X,
      ((μ z : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = c • 1 := by
    choose f hf using hscal
    have hf0 : ∀ g (hg : g ∈ Subgroup.center X), f g hg ≠ 0 := by
      intro g hg h0
      have := hf g hg
      rw [h0, zero_smul] at this
      exact (μ g).ne_zero this
    let F' : ↥(Subgroup.center X) → {c : F4 // c ≠ 0} := fun g => ⟨f g g.2, hf0 g g.2⟩
    have hF'inj : Function.Injective F' := by
      intro g h hgh
      have e1 : f g g.2 = f h h.2 := congrArg Subtype.val hgh
      have e2 : μ g = μ h := Units.ext (by rw [hf g g.2, hf h h.2, e1])
      exact Subtype.ext (hμ e2)
    have h3 : Nat.card {c : F4 // c ≠ 0} = 3 := by
      rw [← Nat.card_congr unitsEquivNeZero, Nat.card_units, Nat.card_eq_fintype_card, F4.card]
    obtain ⟨g, hg⟩ := (hF'inj.bijective_of_nat_card_le (by rw [h3, hZ])).2 ⟨c, hc0⟩
    refine ⟨g, g.2, ?_⟩
    rw [hf g g.2]
    exact congrArg (fun d : {c : F4 // c ≠ 0} => (d : F4) • (1 : Matrix (Fin 3) (Fin 3) F4)) hg
  refine ⟨z, hz, ?_⟩
  apply Additive.ofMul.injective
  apply Φ.injective
  rw [hΦact z p, hμz, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact hc

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_hatA6Block (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsHatA6Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, hhat, hcardU, hCU⟩ := hblk
  let α : ↥K₀ →* ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ := QuotientGroup.mk' _
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective _
  have hker : α.ker = CFSG.pCore 2 ↥K₀ := QuotientGroup.ker_mk' _
  obtain ⟨P⟩ : Nonempty (Sylow 2 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) := inferInstance
  have hS₀ : IsSylowTwoOf (P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) ⊤ := by
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [show ((P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)).subgroupOf ⊤).index =
      (P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)).index from Subgroup.relIndex_top_right _]
    exact P.not_dvd_index
  refine S.false_of_blockModelU h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hchar hshort α hα hker hS₀ ?_
  have hinj : Function.Injective (blockLiftConj hshort α hα hker) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨ℓ, rfl⟩ := hα x
    rw [blockLiftConj_apply, A4.actionOn_eq_one_iff] at hx
    have hmem : (ℓ : G) ∈ pCoreOf 2 K₀ := by
      rw [← hCU]
      exact ⟨ℓ.2, hx⟩
    obtain ⟨q, hq, hqℓ⟩ := hmem
    have hqe : q = ℓ := Subtype.ext hqℓ
    subst hqe
    have hq' : q ∈ CFSG.pCore 2 ↥K₀ := by exact hq
    rw [← MonoidHom.mem_ker, hker]
    exact hq'
  have hN2 : ∀ n : ↥(blockU K₀), n ^ 2 = 1 := fun n =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact C1.blockU_sq hshort _ n.2)
  let _ : CommGroup ↥(blockU K₀) :=
    { (inferInstance : Group ↥(blockU K₀)) with
      mul_comm := fun a b => Subtype.ext
        (C1.blockU_comm hshort _ a.2 _ (C1.blockU_le_blockQ hshort b.2)) }
  exact modelFix_hatA6 hN2 hcardU hhat (blockLiftConj hshort α hα hker) hinj hS₀

end Setting

end CFSG.Quasithin.H13.A5
