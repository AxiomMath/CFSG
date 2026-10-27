module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOne
public import CFSG.Quasithin.Background.HFL3Lift
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Quasithin.SteinbergCBTwistedField

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem binaryNaturalSU3_eq_one_of_twoElement_centralizer
    {V : Type} [CommGroup V] [Finite V] {k : ℕ} (hk : 2 ≤ k)
    {R : Subgroup (MulAut V)} (hH : BinaryNaturalSU3 R ⊤ ⊥ k)
    {f : MulAut V} (hf : ∀ y ∈ R, f * y = y * f)
    (hf2 : ∃ n, orderOf f = 2 ^ n) : f = 1 := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, hπ⟩ := hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨e, he⟩ :=
    CFSG.Quasithin.H.exists_mulEquiv_of_realizesVia (Γ := StatedSU 3 (2 ^ k) K) hπ
  let f' : MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulAut.congr e f
  have hmapR : R.map (CFSG.Quasithin.H.congrHom e) =
      CFSG.Quasithin.H.natImage (StatedSU 3 (2 ^ k) K) :=
    CFSG.Quasithin.H.map_congrHom_eq_natImage
      (StatedSU 3 (2 ^ k) K) hπ.1 e he
  have hf'comm_all : ∀ z ∈ CFSG.Quasithin.H.natImage (StatedSU 3 (2 ^ k) K),
      f' * z = z * f' := by
    intro z hz
    rw [← hmapR] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    change MulAut.congr e f * MulAut.congr e y =
      MulAut.congr e y * MulAut.congr e f
    rw [← map_mul, ← map_mul, hf y hy]
  have hf'comm : ∀ γ : ↥(StatedSU 3 (2 ^ k) K),
      f' * CFSG.Quasithin.H.natAut (StatedSU 3 (2 ^ k) K) γ =
        CFSG.Quasithin.H.natAut (StatedSU 3 (2 ^ k) K) γ * f' :=
    fun γ => hf'comm_all _ ⟨γ, rfl⟩
  let F : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := fun v => CFSG.Quasithin.H.toAddMap f' v
      map_zero' := CFSG.Quasithin.H.toAddMap_zero f'
      map_add' := fun v w => CFSG.Quasithin.H.toAddMap_add f' v w }
  have hchar : CharP K 2 :=
    CFSG.Quasithin.SteinbergCB.charP_two_of_card (by omega) hKcard
  haveI : CharP K 2 := hchar
  obtain ⟨c, hc⟩ := CFSG.Quasithin.H.SU3.hasScalarCommutant' (n := k) (by omega) hKcard F (by
    intro γ hγ v
    have h := congrArg
      (fun g : MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K) =>
        CFSG.Quasithin.H.toAddMap g v) (hf'comm ⟨γ, hγ⟩)
    simpa [F, CFSG.Quasithin.H.toAddMap_mul, CFSG.Quasithin.H.toAddMap_natAut] using h)
  change ∀ v : Fin 3 → K, CFSG.Quasithin.H.toAddMap f' v = c • v at hc
  obtain ⟨n, hn⟩ := hf2
  have hf'pow : f' ^ (2 ^ n) = 1 := by
    dsimp [f']
    rw [← map_pow, ← hn, pow_orderOf_eq_one, map_one]
  have hpowapply : ∀ m : ℕ, ∀ v : Fin 3 → K,
      CFSG.Quasithin.H.toAddMap (f' ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero =>
        intro v
        simp [CFSG.Quasithin.H.toAddMap_one]
    | succ m ih =>
        intro v
        rw [pow_succ', CFSG.Quasithin.H.toAddMap_mul, hc, ih, pow_succ', smul_smul]
  have hc_eq_one : c = 1 := by
    have h1 : c ^ (2 ^ n) • (Pi.single 0 (1 : K) : Fin 3 → K) =
        (Pi.single 0 (1 : K) : Fin 3 → K) := by
      have := hpowapply (2 ^ n) (Pi.single 0 (1 : K))
      rw [hf'pow, CFSG.Quasithin.H.toAddMap_one] at this
      exact this.symm
    have h2 : c ^ (2 ^ n) = 1 := by
      have := congrFun h1 0
      simpa using this
    exact CFSG.Quasithin.H.L3Nine.eq_one_of_pow_two_pow h2
  have hf'one : f' = 1 := by
    apply CFSG.Quasithin.H.toAddMap_injective
    intro v
    have h := hc v
    rw [hc_eq_one, one_smul] at h
    rwa [CFSG.Quasithin.H.toAddMap_one]
  have h1 : MulAut.congr e f = 1 := by
    simpa [f'] using hf'one
  exact (MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm)

private theorem quotAct_eq_of_mem
    {U Z : Subgroup G} [(Z.subgroupOf U).Normal]
    {K K' : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hK'U : K' ≤ Subgroup.normalizer (U : Set G))
    (hK'Z : K' ≤ Subgroup.normalizer (Z : Set G))
    {k : G} (hk : k ∈ K) (hk' : k ∈ K') :
    CFSG.Quasithin.Vol2.Ch11.SecD.quotAct (K := K) hKU hKZ ⟨k, hk⟩ =
      CFSG.Quasithin.Vol2.Ch11.SecD.quotAct (K := K') hK'U hK'Z
        ⟨k, hk'⟩ := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
      rw [CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_mk,
        CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_mk]

theorem str86NF_unitary {L1 L2 S : Subgroup G} {k : ℕ}
    (hF : F112Hyp L1 L2 S) (hk : 2 ≤ k)
    (hQ1 : Q1 L1 L2 S = u3X1 L1 L2 S)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hNat : Str86X1Natural hF k hX1') :
    Str86NF L1 (Q1 L1 L2 S) (Z1 L1 L2 S) := by
  classical
  intro g hgpow hgL hgQ hcommL
  letI : CommGroup (u3M L1 L2 S) := u3MCommGroup hX1'
  letI : ((Z1 L1 L2 S).subgroupOf (u3X1 L1 L2 S)).Normal := u3M_normal L1 L2 S
  have hX : u3Lhat L1 L2 S ≤
      Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    sup_le (le_normalizer_u3X1_left (L1 := L1) (L2 := L2) (S := S))
      ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
        (f112_isSylowTwoOf_P1 hF.toW)).trans
        (le_normalizer_u3X1_sylow (L1 := L1) (L2 := L2) (S := S) hF))
  have hZ : u3Lhat L1 L2 S ≤
      Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    refine (sup_le (le_sup_left : L1 ≤ P1 L1 L2 S) ?_).trans ?_
    · exact (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
        (f112_isSylowTwoOf_P1 hF.toW)).trans
        (((le_sup_right : S ≤ bigB L1 L2 S)).trans
          (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S))
    · exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  let act : ↥(u3Lhat L1 L2 S) →* MulAut (u3M L1 L2 S) :=
    u3MAct (L1 := L1) (L2 := L2) (S := S) hX hZ
  have hbin : BinaryNaturalSU3 act.range ⊤ ⊥ k := by
    have h := hNat
    unfold Str86X1Natural at h
    exact h.2
  have hgU : g ∈ Subgroup.normalizer (u3X1 L1 L2 S : Set G) := by
    rw [← hQ1]
    exact hgQ
  have hgZ : g ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S) hgQ
  let H' : Subgroup G := u3Lhat L1 L2 S ⊔ Subgroup.zpowers g
  have hH'U : H' ≤ Subgroup.normalizer (u3X1 L1 L2 S : Set G) :=
    sup_le hX (Subgroup.zpowers_le.mpr hgU)
  have hH'Z : H' ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    sup_le hZ (Subgroup.zpowers_le.mpr hgZ)
  let act' : ↥H' →* MulAut (u3M L1 L2 S) :=
    CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hH'U hH'Z
  let gel : ↥H' := ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g)⟩
  let fg : MulAut (u3M L1 L2 S) := act' gel
  have hUZ : u3X1 L1 L2 S ≤
      Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    ((u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S))).trans
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf
          (Q1 L1 L2 S)))
  have hcommQ1 : ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S := by
    rw [hQ1]
    exact hX1'
  have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S :=
    CFSG.Quasithin.A4.omegaOneCenterOf_le (Q1 L1 L2 S)
  have hZcomm : ∀ z ∈ Z1 L1 L2 S, ∀ q ∈ Q1 L1 L2 S, z * q = q * z := by
    intro z hz q hq
    exact (Subgroup.mem_centralizer_iff.mp
      ((CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (Q1 L1 L2 S)).trans
        (CFSG.Quasithin.A4.centerOf_le_centralizer (Q1 L1 L2 S)) hz) q hq).symm
  have hact'_q_one : ∀ (k' : ↥H') (hk' : (k' : G) ∈ Q1 L1 L2 S),
      act' k' = 1 := by
    intro k' hk'
    dsimp only [act']
    rw [CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_eq_one_iff hUZ hH'U hH'Z k']
    intro u hu
    have huQ : u ∈ Q1 L1 L2 S := by rwa [← hQ1] at hu
    have hmem : ⁅(k' : G), u⁆ ∈ Z1 L1 L2 S := by
      have := Subgroup.commutator_mem_commutator hk' huQ
      rwa [hcommQ1] at this
    simpa [commutatorElement_def] using hmem
  have hcomm_act' : ∀ (l : G) (hl : l ∈ L1),
      act' gel * act' ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)⟩ =
        act' ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)⟩ * act' gel := by
    intro l hl
    have hgl : ⁅g, l⁆ ∈ Q1 L1 L2 S := by
      simpa [commutatorElement_def] using hcommL l hl
    have h1 : ⁅act' gel,
        act' ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      apply hact'_q_one
      have hcoe : (((⁅gel,
          ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)⟩⁆ : ↥H')) : G) =
          ⁅g, l⁆ := rfl
      rw [hcoe]
      exact hgl
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hact_eq : ∀ (l : G) (hl : l ∈ L1),
      act ⟨l, Subgroup.mem_sup_left hl⟩ =
        act' ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)⟩ := by
    intro l hl
    dsimp only [act, act']
    exact quotAct_eq_of_mem hX hZ hH'U hH'Z _ _
  have hgenL : ∀ (l : G) (hl : l ∈ L1),
      fg * act ⟨l, Subgroup.mem_sup_left hl⟩ =
        act ⟨l, Subgroup.mem_sup_left hl⟩ * fg := by
    intro l hl
    dsimp only [fg]
    rw [hact_eq l hl]
    exact hcomm_act' l hl
  have hgenQ : ∀ (q : G) (hq : q ∈ Q1 L1 L2 S),
      act ⟨q, Subgroup.mem_sup_right hq⟩ = 1 := by
    intro q hq
    change CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hX hZ
      ⟨q, Subgroup.mem_sup_right hq⟩ = 1
    rw [quotAct_eq_of_mem hX hZ hH'U hH'Z _ _]
    exact hact'_q_one ⟨q, Subgroup.mem_sup_left (Subgroup.mem_sup_right hq)⟩ hq
  have hP1L1 : P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  have hQ1L1 : Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (P1 L1 L2 S)).trans hP1L1
  have htop : (Subgroup.centralizer ({fg} : Set (MulAut (u3M L1 L2 S)))).comap act =
      ⊤ := by
    apply top_unique
    intro h _
    rw [Subgroup.mem_comap]
    obtain ⟨l, hl, q, hq, hdecomp⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ1L1).mp h.2
    have hh : h = ⟨l, Subgroup.mem_sup_left hl⟩ *
        ⟨q, Subgroup.mem_sup_right hq⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact hdecomp
    rw [hh, map_mul]
    refine (Subgroup.centralizer ({fg} : Set (MulAut (u3M L1 L2 S)))).mul_mem ?_ ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hgenL l hl).symm
    · rw [Subgroup.mem_centralizer_singleton_iff, hgenQ q hq]
      simp
  have hrange_comm : act.range ≤
      Subgroup.centralizer ({fg} : Set (MulAut (u3M L1 L2 S))) := by
    rintro y ⟨h, rfl⟩
    have hh : h ∈ (Subgroup.centralizer ({fg} : Set (MulAut (u3M L1 L2 S)))).comap act := by
      rw [htop]
      exact Subgroup.mem_top h
    exact (Subgroup.mem_comap.mp hh)
  obtain ⟨n, hn⟩ := hgpow
  have hfg2 : ∃ j : ℕ, orderOf fg = 2 ^ j := by
    have hdvd : orderOf fg ∣ 2 ^ n := by
      calc orderOf fg ∣ orderOf gel := orderOf_map_dvd act' gel
        _ = orderOf g := by
          rw [← Subgroup.orderOf_coe gel]
        _ = 2 ^ n := hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hrange_comm' : ∀ y ∈ act.range, fg * y = y * fg := by
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hrange_comm hy)).symm
  have hfg_one : fg = 1 :=
    binaryNaturalSU3_eq_one_of_twoElement_centralizer hk hbin hrange_comm' hfg2
  have hQg : ∀ u ∈ Q1 L1 L2 S, g * u * g⁻¹ * u⁻¹ ∈ Z1 L1 L2 S := by
    intro u hu
    have huU : u ∈ u3X1 L1 L2 S := hQ1 ▸ hu
    have h1 : CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hH'U hH'Z gel = 1 := by
      simpa [fg] using hfg_one
    have h2 := (CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_eq_one_iff
      hUZ hH'U hH'Z gel).mp h1
    exact h2 u huU
  constructor
  · intro u hu
    exact hQg u hu
  · intro z hz
    have hsubZ : ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤
        Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.commutator_le]
      intro u hu v hv
      have hzu : ⁅g, u⁆ ∈ Z1 L1 L2 S := by
        simpa [commutatorElement_def] using hQg u hu
      have hzv : ⁅g, v⁆ ∈ Z1 L1 L2 S := by
        simpa [commutatorElement_def] using hQg v hv
      have hzu_eq : g * u * g⁻¹ = ⁅g, u⁆ * u := by
        rw [commutatorElement_def]
        group
      have hzv_eq : g * v * g⁻¹ = ⁅g, v⁆ * v := by
        rw [commutatorElement_def]
        group
      have hconj : g * ⁅u, v⁆ * g⁻¹ = ⁅u, v⁆ := by
        calc g * ⁅u, v⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * v * g⁻¹⁆ := by
              rw [commutatorElement_def]
              group
          _ = ⁅⁅g, u⁆ * u, ⁅g, v⁆ * v⁆ := by rw [hzu_eq, hzv_eq]
          _ = ⁅⁅g, u⁆, ⁅g, v⁆⁆ * ⁅u, v⁆ :=
              CFSG.GroupTheory.commutatorElement_mul_of_commute hZcomm hzu hzv hu hv
          _ = 1 * ⁅u, v⁆ := by
              rw [commutatorElement_eq_one_iff_mul_comm.mpr
                (hZcomm _ hzu _ (hZ1Q1 hzv))]
          _ = ⁅u, v⁆ := one_mul _
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ⁅u, v⁆ * g = (g * ⁅u, v⁆ * g⁻¹) * g := by rw [hconj]
        _ = g * ⁅u, v⁆ := by group
    have hz' : z ∈ ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ := by
      rw [hcommQ1]
      exact hz
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hsubZ hz')).symm

end CFSG.Quasithin.Stroth

end
