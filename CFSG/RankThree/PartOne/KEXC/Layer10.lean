module

public import CFSG.RankThree.PartOne.KLAY10.Frame
public import CFSG.RankThree.PartOne.KLAY10.Radical
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.RankThree.PartOne.KLAY10 CFSG.Assembly.LowTwoRank

theorem isCentralPQuot_comp_conj {E P : Type*} [Group E] [Group P] {p : ℕ} {ε : E →* P}
    (hε : IsCentralPQuot p ε) (y : P) :
    IsCentralPQuot p ((MulAut.conj y).toMonoidHom.comp ε) := by
  have hker : ((MulAut.conj y).toMonoidHom.comp ε).ker = ε.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff (MulAut.conj y)
  refine ⟨(MulAut.conj y).surjective.comp hε.surjective, hker ▸ hε.central, ?_⟩
  rw [hker]
  exact hε.coprime

theorem pow_eq_one_of_mem_subgroupOf {G : Type} [Group G] {p : ℕ} {A L : Subgroup G}
    (hAel : IsElementaryAbelian p A) {a : ↥L} (ha : a ∈ (A ⊓ L).subgroupOf L) : a ^ p = 1 :=
  Subtype.ext (by
    simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (a : G)
      (Subgroup.mem_subgroupOf.1 ha).1)

theorem isPGroup_comap_map {Λ Q M : Type*} [Group Λ] [Group Q] [Group M] {S' : Subgroup Λ}
    (hS' : IsPGroup 2 S') (ε : Λ →* Q) {q : M →* Q} (hq : Function.Injective q) :
    IsPGroup 2 ↥((S'.map ε).comap q) := by
  rintro ⟨s, hs⟩
  obtain ⟨s₀, hs₀, hεs⟩ := hs
  obtain ⟨k, hk⟩ := hS' ⟨s₀, hs₀⟩
  refine ⟨k, Subtype.ext (hq ?_)⟩
  have h1 : s₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, ← hεs, ← map_pow, h1, map_one, map_one]

theorem kf1212LayerRow10 : KF1212LayerRow 10 := by
  intro G _ _ p A c L E ctx hmodel _ _
  classical
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, hmodL, hζ, ε, q, hε, hq, hqbij, hFT₁, hFT₂⟩ :=
    exists_r10frame hcore hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hpf : p ≤ 2 ^ f + 1 := Nat.le_of_dvd (by omega) hpq
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  obtain ⟨m, hmp, hm1, hmK⟩ := exists_root_not_mem hp hp2 hpq'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hmp
    exact zero_ne_one hmp
  let z : (Qext K)ˣ := Units.mk0 m hm0
  have hzp : z ^ p = 1 := Units.ext (by simpa [z] using hmp)
  have hz1 : z ≠ 1 := fun h1 => hm1 (by simpa [z] using congrArg Units.val h1)
  have hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)) := hmK
  have hmem : bAut z ∈ M10 K := by
    refine torusEquiv_mem_M10 hpq' (x := ![1, 1, z]) fun i => ?_
    fin_cases i <;> simp [hzp]
  have hb10 : b10 z hmem ≠ 1 := by
    intro h1
    have h2 : bAut z (e2v 1) = e2v 1 := by
      have := congrArg (fun g : ↥(M10 K) => (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (e2v 1)) h1
      exact this
    have h3 := congrFun h2 2
    rw [bAut_apply_two, e2v_two_coord, mul_one] at h3
    exact hz1 (Units.ext h3)
  have hKM := perfectResidual_centralizer_b10 hK4 hz1 hzK hmem
  set A₀' : Subgroup ↥L := (A ⊓ L).subgroupOf L with hA₀'
  have hAel := h.A_elem
  have hA₀e : ∀ a ∈ A₀', a ^ p = 1 := fun a ha => pow_eq_one_of_mem_subgroupOf hAel ha
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := (Sec12Three.A_eq_sup h ctx.generic).le
  have key : ∀ (ε' : ↥L →* StatedProj (StatedSp 3 K)) (_ : IsCentralPQuot p ε')
      (TX : Subgroup ↥(M10 K)), (∀ t ∈ TX, t ^ p = 1) → b10 z hmem ∈ TX →
      Nat.card ↥(TX ⊓ (blk2 (K := K)).range) = p →
      (∃ U : Subgroup ↥(M10 K), U ≤ (blk2 (K := K)).range ∧ IsPGroup 2 ↥U ∧
        TX ≤ Subgroup.normalizer (U : Set ↥(M10 K)) ∧ ∃ u ∈ U, ∃ t ∈ TX, u * t ≠ t * u) →
      A₀'.map ε' = TX.map q →
      ∃ (b : G) (KL : Subgroup G), LayerCore p A L b KL ∧ RowKClause p L KL 10 := by
    intro ε' hε' TX hTXe hbTX hTK ⟨U, hUle, hU2, hTU, hnc⟩ hAT
    have hbq : q (b10 z hmem) ∈ A₀'.map ε' := hAT ▸ Subgroup.mem_map_of_mem q hbTX
    obtain ⟨a, haA, hba⟩ := hbq
    have haAL : (a : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.1 haA
    have hbMp : b10 z hmem ^ p = 1 := hTXe _ hbTX
    obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
      (IsPGroup.of_card h.A_card) hAel ctx.L_le_centralizer hA ε' q hε' hq haAL.1 a.2 hbMp
      (by simpa using hba) hTXe hAT
      (isQuasisimple_perfectResidual_centralizer_b10 hK4 hz1 hzK hmem)
      (by
        rw [hKM, card_center_range_blk2]
        exact hp.not_dvd_one)
      (by rw [hKM]; exact hTK) (by rw [hKM]; exact hUle) hU2 hTU hnc
    have hb1 : (a : G) ≠ 1 := by
      intro h1
      apply hb10
      apply hqbij.1
      rw [← hba, map_one]
      have : a = 1 := Subtype.ext h1
      rw [this, map_one]
    refine ⟨(a : G), KL, ⟨⟨haAL.1, a.2, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
    refine ⟨f, hf1, hpq, hmodL, ⟨Nat.prime_two, hf1, by norm_num, ?_⟩, K, hKf, hKfin, hK, ?_⟩
    · intro h2
      have := congrArg Prod.snd h2
      simp only at this
      omega
    · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
      obtain ⟨e₄⟩ := exists_model_range_blk2 (K := K)
      exact ⟨eqv.trans (e₃.trans e₄)⟩
  set T₀ : Subgroup ↥(M10 K) := (A₀'.map ε).comap q with hT₀
  have hT₀map : T₀.map q = A₀'.map ε := Subgroup.map_comap_eq_self_of_surjective hqbij.2 _
  have hA₀card : Nat.card A₀' = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
      hA₀', Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    exact hcore.A₀_card
  have hmapcard : Nat.card (A₀'.map ε) = Nat.card A₀' := by
    have hinj : Function.Injective (ε.subgroupMap A₀') := by
      intro x y hxy
      have h1 : ε (x : ↥L) = ε (y : ↥L) := congrArg Subtype.val hxy
      exact Subtype.ext (hε.eq_of_map_eq (hA₀e _ x.2) (hA₀e _ y.2) h1)
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, ε.subgroupMap_surjective _⟩)).symm
  have hT₀card : Nat.card T₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hqbij.1 (K := T₀), hT₀map, hmapcard, hA₀card]
  have hT₀T : ∀ t ∈ T₀, ∃ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) ∧
      (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := ht
    have haF : (a : G) ∈ E ⊓ L := hcore.A₀_le_F (Subgroup.mem_subgroupOf.1 ha)
    obtain ⟨t', ht', hεt'⟩ := hFT₂ ⟨(a : G), haF⟩
    have htt' : t = t' := hqbij.1 (hat.symm.trans hεt')
    subst htt'
    obtain ⟨d, hd⟩ := Subgroup.mem_subgroupOf.1 ht'
    exact ⟨sqCoords d, sqCoords_pow d, hd.symm⟩
  obtain ⟨S, hSL, hS1, hS2, hSn, hSS⟩ := hcore.A₀_invariant
  set S' : Subgroup ↥L := S.subgroupOf L with hS'
  have hS'2 : IsPGroup 2 ↥S' := by
    rintro ⟨s₀, hs₀⟩
    obtain ⟨k, hk⟩ := hS2 ⟨(s₀ : G), hs₀⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa [Subgroup.coe_pow] using h1
  set SM : Subgroup ↥(M10 K) := (S'.map ε).comap q with hSM
  have hSM2 : IsPGroup 2 ↥SM := isPGroup_comap_map hS'2 ε hqbij.1
  have hSMne : SM ≠ ⊥ := by
    intro hbot
    apply hS1
    have hcen : ∀ s ∈ S, ∀ a ∈ A ⊓ L, s * a = a * s := by
      intro s hs a ha
      have hs' : (⟨s, hSL hs⟩ : ↥L) ∈ S' := hs
      obtain ⟨t, ht⟩ := hqbij.2 (ε ⟨s, hSL hs⟩)
      have htS : t ∈ SM := ⟨⟨s, hSL hs⟩, hs', ht.symm⟩
      rw [hbot, Subgroup.mem_bot] at htS
      have h1 : ε ⟨s, hSL hs⟩ = 1 := by rw [← ht, htS, map_one]
      have h2 : (⟨s, hSL hs⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hε.central ((MonoidHom.mem_ker).2 h1)
      have := Subgroup.mem_center_iff.1 h2 ⟨a, ha.2⟩
      exact congrArg Subtype.val this.symm
    rw [hSS, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    exact (hcen s hs a ha).symm
  have hT₀S : ∀ t ∈ T₀, ∀ s ∈ SM, t * s * t⁻¹ ∈ SM := by
    intro t ht s hs
    obtain ⟨a, ha, hat⟩ := ht
    obtain ⟨s₀, hs₀, hεs⟩ := hs
    have haAL : (a : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.1 ha
    have hconj : (a * s₀ * a⁻¹ : ↥L) ∈ S' := by
      have := Subgroup.mem_normalizer_iff.1 (hSn haAL) (s₀ : G)
      exact (this.1 hs₀ : (a : G) * (s₀ : G) * (a : G)⁻¹ ∈ S)
    refine ⟨a * s₀ * a⁻¹, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv, hat, hεs, map_mul, map_mul, map_inv]
  obtain ⟨g, hg⟩ := exists_standard_plane hp hp2 hpq' T₀ hT₀T hT₀card SM hSM2 hSMne hT₀S
  set ε' : ↥L →* StatedProj (StatedSp 3 K) := (MulAut.conj (q g)).toMonoidHom.comp ε with hε'
  have hε'c : IsCentralPQuot p ε' := isCentralPQuot_comp_conj hε (q g)
  have hcomm : ((MulAut.conj (q g)).toMonoidHom).comp q = q.comp (MulAut.conj g).toMonoidHom := by
    ext t
    simp [map_mul, map_inv]
  have hAT' : A₀'.map ε' = (T₀.map (MulAut.conj g).toMonoidHom).map q := by
    calc A₀'.map ε' = (A₀'.map ε).map (MulAut.conj (q g)).toMonoidHom := by
          rw [hε', Subgroup.map_map]
      _ = (T₀.map q).map (MulAut.conj (q g)).toMonoidHom := by rw [hT₀map]
      _ = T₀.map (((MulAut.conj (q g)).toMonoidHom).comp q) := Subgroup.map_map _ _ _
      _ = T₀.map (q.comp (MulAut.conj g).toMonoidHom) := by rw [hcomm]
      _ = (T₀.map (MulAut.conj g).toMonoidHom).map q := (Subgroup.map_map _ _ _).symm
  rcases hg with hg | hg
  · exact key ε' hε'c (TI p K) (fun t ht => pow_eq_one_of_mem_torusSub (P := planeI p K)
      (fun x hx => hx.1) ht)
      (b10_mem_TI hzp hmem) (card_TI_inf_blk2 hp hpq' hζ hz1 hzK)
      (exists_U_typeI hpq' hzp hz1 hzK) (hg ▸ hAT')
  · exact key ε' hε'c (TII p K) (fun t ht => pow_eq_one_of_mem_torusSub (P := planeII p K)
      (fun x hx => hx.1) ht)
      (b10_mem_TII hzp hmem) (card_TII_inf_blk2 hp hpq' hζ hz1 hzK)
      (exists_U_typeII hpq' hzp hz1 hzK) (hg ▸ hAT')

end CFSG.RankThree.PartOne.KEXC
