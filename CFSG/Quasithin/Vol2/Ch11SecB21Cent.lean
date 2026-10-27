module

public import CFSG.Quasithin.Vol2.Ch11SecAViLevi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem commutator_fsuV_eq_self (h : Hyp11 G T L I n) : ⁅fsuV T I, L⁆ = fsuV T I := by
  have hL := L_le_normalizer_fsuV h
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (hL hl) v⁻¹).mp ((fsuV T I).inv_mem hv)
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact (fsuV T I).mul_mem hv h1
  · have hI : ⁅I, L⁆ = I := by
      have := h.fsu.irrPlus.2.2.2.1
      rwa [conjClosure_eq_self h] at this
    refine conjClosure_le fun t ht z hz => ?_
    have h1 : (⁅I, L⁆).map (MulAut.conj t).toMonoidHom ≤ ⁅fsuV T I, L⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono (Subgroup.map_le_iff_le_comap.mpr fun i hi => ?_)
        (Subgroup.map_le_iff_le_comap.mpr fun l hl => ?_)
      · show t * i * t⁻¹ ∈ fsuV T I
        exact mem_conjClosure ht hi
      · show t * l * t⁻¹ ∈ L
        exact (Subgroup.mem_normalizer_iff.mp (h.normal ht) l).mp hl
    rw [hI] at h1
    exact h1 ⟨z, hz, by simp⟩

theorem isPGroup_sup_inf_centralizer (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) :
    IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normal
  have hq := B6.isTwoQuotient_of_sup_eq hyp.fsu.sylow.1 hLT (sup_comm T L)
  have hO2 := centralizer_eq_pCoreOf h1102 hyp
  have hP : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  intro x
  obtain ⟨k, hk⟩ := hq x (Subgroup.mem_inf.mp x.2).1
  have hxk : (x : G) ^ 2 ^ k ∈ pCoreOf 2 L := by
    rw [← hO2]
    exact ⟨hk, Subgroup.pow_mem _ (Subgroup.mem_inf.mp x.2).2 _⟩
  obtain ⟨j, hj⟩ := hP ⟨_, hxk⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, hj']

theorem le_normalizer_inf_centralizer (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    {U : Subgroup G} (hVU : fsuV T I ≤ U) (hLTU : L ⊔ T ≤ Subgroup.normalizer (U : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := (L ⊔ T) ⊓ Subgroup.centralizer (U : Set G) with hYdef
  have hYV : Y ≤ (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hVU)
  have hY2 : IsPGroup 2 ↥Y := (isPGroup_sup_inf_centralizer h1102 hyp).to_le hYV
  have hYn : L ⊔ T ≤ Subgroup.normalizer (Y : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTU)
  have hYO : Y ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hYn hY2
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hYT : Y ≤ T := hYO.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hTS)
  have hYeq : T ⊓ Subgroup.centralizer (U : Set G) = Y :=
    le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf hYT inf_le_right)
  rw [hYeq]
  exact hYn

theorem isUniqueM_normalizer_inf_centralizer (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (hyp : Hyp11 G T L I n) {U : Subgroup G} (hVU : fsuV T I ≤ U)
    (hLTU : L ⊔ T ≤ Subgroup.normalizer (U : Set G)) (hUT : U ≤ T) (hUab : IsMulCommutative ↥U)
    (hU1 : U ≠ ⊥) :
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  set P := T ⊓ Subgroup.centralizer (U : Set G) with hPdef
  have hP2 : IsPGroup 2 ↥P := hyp.fsu.sylow.1.to_le inf_le_left
  have hUP : U ≤ P := by
    refine le_inf hUT fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact congrArg Subtype.val (hUab.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩)
  have hP1 : P ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUP))
  have hLTP := le_normalizer_inf_centralizer h1102 hyp hVU hLTU
  refine ⟨⟨isMaxTwoLocal_M h331 hyp, normalizer_le_of_isPGroup h331 hyp hP2 hP1 hLTP⟩,
    fun M' hM' => ?_⟩
  exact (isUniqueM_LT h331 hyp).2 M' ⟨hM'.1, hLTP.trans hM'.2⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
