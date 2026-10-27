module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch11SecE42S2e

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem nonempty_modO2_modO2Image_equiv {H B : Subgroup G} (hBH : B ≤ H) :
    Nonempty (ModO2 (modO2Image H B) ≃* ↥B ⧸ CFSG.pCore 2 ↥B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hBH) with hf
  set ρ : ↥B →* ↥(modO2Image H B) :=
    (MulEquiv.subgroupCongr (range_modO2_eq hBH)).toMonoidHom.comp f.rangeRestrict with hρ
  have hρs : Function.Surjective ρ :=
    (MulEquiv.subgroupCongr (range_modO2_eq hBH)).surjective.comp f.rangeRestrict_surjective
  have hρk : ∀ b : ↥B, ρ b = 1 → (b : G) ∈ pCoreOf 2 H := by
    intro b hb
    have h1 : f b = 1 := by
      have := congrArg Subtype.val hb
      simpa [hρ] using this
    exact (mem_ker_modO2_iff hBH b).mp h1
  set τ := (QuotientGroup.mk' (CFSG.pCore 2 ↥(modO2Image H B))).comp ρ with hτ
  have hτs : Function.Surjective τ := (QuotientGroup.mk'_surjective _).comp hρs
  have hker : τ.ker = CFSG.pCore 2 ↥B := by
    refine le_antisymm ?_ ?_
    · refine le_sSup ⟨inferInstance, fun x => ?_⟩
      have hx : ρ x ∈ CFSG.pCore 2 ↥(modO2Image H B) := by
        have h1 : τ x = 1 := x.2
        have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(modO2Image H B)) (ρ x) = 1 := h1
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image H B))) ⟨_, hx⟩
      have h1 : ρ ((x : ↥B) ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val ha
      obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hρk _ h1⟩
      refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hb
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    · intro x hx
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have hle : (CFSG.pCore 2 ↥B).map ρ ≤ CFSG.pCore 2 ↥(modO2Image H B) :=
        le_sSup ⟨CFSG.pCore_normal.map ρ hρs, CFSG.pCore_isPGroup.map ρ⟩
      exact hle ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective τ hτs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem mem_reducedAggregate_of_mem {H T : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H)
    (hF : QuasithinUnique.CharTwo H) {z : G} (hzT : z ∈ T)
    (hzC : z ∈ Subgroup.centralizer (T : Set G)) (hz2 : z ^ 2 = 1) : z ∈ reducedAggregate H := by
  have hzZ : Subgroup.zpowers z ≤ quasithinOmegaOneCenter T :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure ⟨⟨hzT, hzC⟩, hz2⟩)
  have hR := isTwoReducedIn_conjClosure_of_sylowIn hT.1 hT.2.1 hT.2.2 hF hzZ
  rw [show reducedAggregate H = twoReducedJoin H from
    primeReducedAggregate_map_subtype_eq_twoReducedJoin H]
  exact (le_iSup₂_of_le (f := fun (V : Subgroup G) (_ : IsTwoReducedIn H V) => V)
    (conjClosure (Subgroup.zpowers z) H) hR le_rfl) ((le_conjClosure _ _) (Subgroup.mem_zpowers z))

theorem T_le_normalizer_of_le (hK : QuasithinUnique.LocalSQTK G)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat) {T K Kp : Subgroup G}
    (hloc : quasithinIsLocal T Kp) (hKl : K ∈ lFamily T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hKKp : K ≤ Kp) :
    T ≤ Subgroup.normalizer (Kp : Set G) := by
  intro t ht
  have hKp : Kp ∈ cComp (Kp ⊔ T) := hloc.2.1
  have hKpt := map_conj_mem_cComp hKp (Subgroup.mem_sup_right ht)
  have hKt : K ≤ Kp.map (MulAut.conj t).toMonoidHom := by
    intro k hk
    refine ⟨t⁻¹ * k * t, hKKp ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTK ht)) k).mp hk
      simpa using this
    · simp [MulAut.conj_apply, mul_assoc]
  have heq := QuasithinUnique.Vol2Native.lemma_1_2_4_unique hK h37 hloc.2.2.2 hKl hKp hKpt hKKp
    hKt
  exact A38.map_conj_eq_iff.mp heq.symm

omit [Finite G] in
theorem not_le_of_lt_of_mem_cComp {T K Kp Gz : Subgroup G} (hK : K ∈ cComp Gz) (hTGz : T ≤ Gz)
    (hloc : quasithinIsLocal T Kp) (hlt : K < Kp) : ¬ Kp ≤ Gz := by
  intro hle
  have hKp : Kp ∈ cComp (Kp ⊔ T) := hloc.2.1
  have hsub : IsSubnormal K (Kp ⊔ T) :=
    A3.subnormal_of_le_of_le hK.2.2.1 (hlt.le.trans le_sup_left) (sup_le hle hTGz)
  exact hKp.2.2.2 K hlt hK.1 hK.2.1 hsub

end CFSG.Quasithin.Vol2.Ch11.SecE
