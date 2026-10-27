module

public import CFSG.Milestones.ASVolI.F431.BCoreSpA
public import CFSG.Quasithin.Background.F7TwoInvSp4Odd
public import CFSG.Milestones.ASVolI.F431.BCoreGen
public import CFSG.Milestones.ASVolI.F431.BCoreGenQ

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open

open scoped commutatorElement

namespace SpOut2

section PCoreBorel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type} [Group H] [Finite H]
  {m : ℕ} {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ} {R : Fin 2 → Subgroup (antiSp F)}
  {i : Fin 3 → antiSp F} {N : Fin 2 → Subgroup H}

theorem burnsideF4m_sp_mem_U_of_pCore (C : OutCtx m Φ ψ k₀ (antiUnipotent F) R i N)
    {w : antiSp F} (hw : Φ w ∈ pCoreOf 2 (N 0 ⊓ N 1)) : w ∈ antiUnipotent F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (antiSp F) := Finite.of_injective Φ C.P.inj
  set Hc : Subgroup (antiSp F) := (N 0 ⊓ N 1).comap Φ with hHc
  set X' : Subgroup (antiSp F) := (pCoreOf 2 (N 0 ⊓ N 1)).comap Φ with hX'
  have hUH : antiUnipotent F ≤ Hc := by
    intro u hu
    have hT : Φ u ∈ spT Φ ψ (antiUnipotent F) := (C.P.mem_spT_iff C.X.U_fr).mpr ⟨u, hu, 0, by simp⟩
    exact le_inf (C.T_le 0) (C.T_le 1) hT
  have hXH : X' ≤ Hc := fun x hx => CFSG.LieType.BorelTits.pCoreOf_le 2 (N 0 ⊓ N 1) hx
  have hHX : Hc ≤ Subgroup.normalizer (X' : Set (antiSp F)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (N 0 ⊓ N 1) hh) (Φ x)
    simp only [hX', Subgroup.mem_comap, map_mul, map_inv]
    exact h1
  have hXp : IsPGroup 2 ↥X' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (N 0 ⊓ N 1)).comap_of_injective Φ C.P.inj
  have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXH hHX hXp
  have h2 := CFSG.ASVolI.burnsideF4gG2Inv_pCoreOf_le_of_sylow C.hD.borel.sylow hUH
  exact h2 (h1 hw)

theorem burnsideF4m_sp_pCore_inf_le_range (C : OutCtx m Φ ψ k₀ (antiUnipotent F) R i N) :
    pCoreOf 2 (N 0 ⊓ N 1) ≤ Φ.range := by
  intro y hy
  have hT : spT Φ ψ (antiUnipotent F) ≤ N 0 ⊓ N 1 := le_inf (C.T_le 0) (C.T_le 1)
  have hsyl : IsSylowTwoOf (spT Φ ψ (antiUnipotent F)) (N 0 ⊓ N 1) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right C.sylow hT le_top
  have hyT := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl hy
  obtain ⟨u, hu, s, rfl⟩ := (C.P.mem_spT_iff C.X.U_fr).mp hyT
  have htorus : frobAut F ^ (k₀ * (oddPart ψ * s)) = 1 := by
    refine burnsideF4m_sp_frob_eq_one_of_torusU C.hn C.hF _ hu ?_
    intro μ
    set x := dHom F (axisOf 1) μ with hxdef
    have hxU : x ∈ Subgroup.normalizer (antiUnipotent F : Set (antiSp F)) :=
      burnsideF4m_sp_dElt_mem_normalizer μ
    have hxN : Φ x ∈ N 0 ⊓ N 1 := by
      refine ⟨?_, ?_⟩
      · rw [C.hN 0]
        exact map_mem_normalizer_map Φ (C.hD.borel.lt₁.le hxU)
      · rw [C.hN 1]
        exact map_mem_normalizer_map Φ (C.hD.borel.lt₂.le hxU)
    have hc1 := pCoreOf_conj_mem hxN hy
    have hc2 := Subgroup.mul_mem _ hc1 (Subgroup.inv_mem _ hy)
    have h3 := C.P.act_psi2_pow s x⁻¹
    simp only [map_inv] at h3
    have e : Φ x * (Φ u * psi2 ψ ^ s) * (Φ x)⁻¹ * (Φ u * psi2 ψ ^ s)⁻¹ =
        Φ (x * u * ((frobAut F ^ (k₀ * (oddPart ψ * s))) x)⁻¹ * u⁻¹) := by
      calc Φ x * (Φ u * psi2 ψ ^ s) * (Φ x)⁻¹ * (Φ u * psi2 ψ ^ s)⁻¹
          = Φ x * Φ u * (psi2 ψ ^ s * (Φ x)⁻¹ * (psi2 ψ ^ s)⁻¹) * (Φ u)⁻¹ := by group
        _ = Φ (x * u * ((frobAut F ^ (k₀ * (oddPart ψ * s))) x)⁻¹ * u⁻¹) := by
          rw [h3]
          simp only [map_mul, map_inv]
    rw [e] at hc2
    exact burnsideF4m_sp_mem_U_of_pCore C hc2
  have h1 : psi2 ψ ^ s = 1 := by
    rw [psi2_pow_eq, C.P.pow_eq_one_iff]
    exact htorus
  rw [h1, mul_one]
  exact ⟨u, rfl⟩

end PCoreBorel

end SpOut2

end CFSG.Quasithin.H13.F431

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.UnbalancedCatalog

section Generic

theorem burnsideF4m_le_of_simple {H : Type} [Group H] {N N' : Subgroup H} [hN : N.Normal]
    [hN' : N'.Normal] (hs : IsSimpleGroup ↥N) (hC : Subgroup.centralizer (N : Set H) = ⊥)
    (hne : N' ≠ ⊥) : N ≤ N' := by
  haveI hn : (N'.subgroupOf N).Normal := Subgroup.Normal.subgroupOf hN' N
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.subgroupOf N) with h | h
  · exfalso
    apply hne
    have hinf : N ⊓ N' = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxN'⟩
      have : (⟨x, hxN⟩ : ↥N) ∈ N'.subgroupOf N := hxN'
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    have hc : ⁅N', N⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_le_inf N' N).trans ?_)
      rw [inf_comm, hinf]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at hc
    exact le_bot_iff.mp hc
  · intro x hx
    have : (⟨x, hx⟩ : ↥N) ∈ N'.subgroupOf N := by rw [h]; exact Subgroup.mem_top _
    exact this

end Generic

section Sp4

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_core_theta {κ : GLKind} {p : ℕ} [Finite E] [Gp.Normal]
    (hyp : HypF_4_4g κ p f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    ∃ θ : E ≃* ↥(burnsideF4d_lieExtE hyp hyam).K,
      (∀ e, θ e ∈ (burnsideF4d_lieExtE hyp hyam).Mb1 ↔ e ∈ M₁) ∧
      (∀ e, θ e ∈ (burnsideF4d_lieExtE hyp hyam).Mb2 ↔ e ∈ M₂) ∧
      (∀ e, ((θ e : ↥(burnsideF4d_lieExtE hyp hyam).K) : MulAut ↥Gp) = burnsideF4d_rho Gp e) := by
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : (burnsideF4d_lieExtE hyp hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp hyam
  let θ : E ≃* ↥(burnsideF4d_lieExtE hyp hyam).K :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hK.symm)
  have hθ : ∀ e : E, ((θ e : ↥(burnsideF4d_lieExtE hyp hyam).K) : MulAut ↥Gp) =
      burnsideF4d_rho Gp e := fun e => rfl
  have hN1 : (burnsideF4d_lieExtE hyp hyam).N1 = M₁.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N1_eq hyp hyam
  have hN2 : (burnsideF4d_lieExtE hyp hyam).N2 = M₂.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N2_eq hyp hyam
  refine ⟨θ, fun e => ?_, fun e => ?_, hθ⟩
  · rw [Subgroup.mem_subgroupOf, hθ, hN1]
    constructor
    · rintro ⟨e', he', hee'⟩
      rw [← hinj hee']
      exact he'
    · intro he
      exact ⟨e, he, rfl⟩
  · rw [Subgroup.mem_subgroupOf, hθ, hN2]
    constructor
    · rintro ⟨e', he', hee'⟩
      rw [← hinj hee']
      exact he'
    · intro he
      exact ⟨e, he, rfl⟩

theorem burnsideF4m_core_map_eq_of_iff {A B : Type} [Group A] [Group B] (θ : A ≃* B)
    {M : Subgroup A} {N : Subgroup B} (h : ∀ a, θ a ∈ N ↔ a ∈ M) : M.map θ.toMonoidHom = N := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (h a).2 ha
  · intro hb
    refine ⟨θ.symm b, (h _).1 ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply]
    · simp

theorem burnsideF4m_sp4_core_of_outCtx [Finite E] [Gp.Normal]
    (hcen : Subgroup.centralizer (Gp : Set E) = ⊥) (hsGp : IsSimpleGroup ↥Gp)
    {H : Type} [Group H] [Finite H] (θ : E ≃* H) {N : Fin 2 → Subgroup H}
    (hθ1 : ∀ e, θ e ∈ N 0 ↔ e ∈ M₁) (hθ2 : ∀ e, θ e ∈ N 1 ↔ e ∈ M₂)
    {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}
    {R : Fin 2 → Subgroup (antiSp F)} {i : Fin 3 → antiSp F}
    (C : OutCtx m Φ ψ k₀ (antiUnipotent F) R i N) :
    (∀ x ∈ centerOf (perfectCore M₁), x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) ∧
    pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
    pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 := C.hm
  have hF := C.hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hθM1 : M₁.map θ.toMonoidHom = N 0 := burnsideF4m_core_map_eq_of_iff θ hθ1
  have hθM2 : M₂.map θ.toMonoidHom = N 1 := burnsideF4m_core_map_eq_of_iff θ hθ2
  set Inn : Subgroup H := Gp.map θ.toMonoidHom with hInn
  haveI hInnN : Inn.Normal := Subgroup.Normal.map inferInstance θ.toMonoidHom θ.surjective
  haveI hRN : Φ.range.Normal := C.P.range_normal
  have hCR : Subgroup.centralizer (Φ.range : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine C.P.cen k fun x => ?_
    have := Subgroup.mem_centralizer_iff.mp hk (Φ x) ⟨x, rfl⟩
    rw [← this, mul_inv_cancel_right]
  have hCI : Subgroup.centralizer (Inn : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hk' : θ.symm k ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      apply θ.injective
      have := Subgroup.mem_centralizer_iff.mp hk (θ g) ⟨g, hg, rfl⟩
      simpa [map_mul] using this
    rw [hcen, Subgroup.mem_bot] at hk'
    simpa using congrArg θ hk'
  have hsR : IsSimpleGroup ↥Φ.range := by
    haveI := (CFSG.Quasithin.F7Two.isSimpleGroup_antiSp (K := F) hF4).1
    exact (MonoidHom.ofInjective C.P.inj).symm.isSimpleGroup
  have hsI : IsSimpleGroup ↥Inn := by
    haveI := hsGp
    exact (θ.subgroupMap Gp).symm.isSimpleGroup
  have hneR : Φ.range ≠ ⊥ := by
    intro h0
    have := hsR.toNontrivial
    obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (1 : ↥Φ.range)
    rw [h0, Subgroup.mem_bot] at ha
    exact hne (Subtype.ext ha)
  have hneI : Inn ≠ ⊥ := by
    intro h0
    have := hsI.toNontrivial
    obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (1 : ↥Inn)
    rw [h0, Subgroup.mem_bot] at ha
    exact hne (Subtype.ext ha)
  have hRI : Φ.range = Inn :=
    le_antisymm (burnsideF4m_le_of_simple hsR hCR hneI) (burnsideF4m_le_of_simple hsI hCI hneR)
  have hθinj : Function.Injective θ.toMonoidHom := θ.injective
  have hpull : ∀ {A : Subgroup E}, A.map θ.toMonoidHom ≤ Φ.range → A ≤ Gp := by
    intro A hA x hx
    have h := hA ⟨x, hx, rfl⟩
    rw [hRI] at h
    exact (Subgroup.mem_map_iff_mem hθinj).mp h
  have hQ : ∀ (j : Fin 2) {M : Subgroup E}, M.map θ.toMonoidHom = N j →
      pCoreOf 2 M = pCoreOf 2 (Gp ⊓ M) := by
    intro j M hM
    refine burnsideF4m_pCoreOf_eq_inf_of_le Gp M (hpull ?_)
    rw [← CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hθinj, hM]
    have := C.spQ_eq j
    unfold spQ at this
    rw [OutCtx.spN_eq j] at this
    rw [this]
    exact Subgroup.map_le_range Φ (R j)
  have hQ12 : pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    refine burnsideF4m_pCoreOf_eq_inf_of_le Gp (M₁ ⊓ M₂) (hpull ?_)
    rw [← CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hθinj, Subgroup.map_inf_eq _ _ _ hθinj,
      hθM1, hθM2]
    exact burnsideF4m_sp_pCore_inf_le_range C
  have hZ : ∀ (j : Fin 2) {M : Subgroup E}, M.map θ.toMonoidHom = N j →
      ∀ x ∈ centerOf (perfectCore M), x ∈ ctr (oPPrime 2 (Gp ⊓ M)) := by
    intro j M hM x hx
    have hθx : θ x ∈ centerOf (perfectCore (M.map θ.toMonoidHom)) := by
      rw [burnsideF4m_perfectCore_map _ hθinj, burnsideF4m_centerOf_map _ hθinj]
      exact ⟨x, hx, rfl⟩
    rw [hM] at hθx
    have hspZ := C.spZ_eq j
    unfold spZ at hspZ
    rw [OutCtx.spN_eq j] at hspZ
    rw [hspZ] at hθx
    obtain ⟨z, hz, hzx⟩ := hθx
    have hmod : spZc R j ≤ ctr (oPPrime 2 (Subgroup.normalizer (R j : Set (antiSp F)))) :=
      burnsideF4m_sp_center_le C.hD.borel.sylow (C.hD.shape.Q_norm j) (C.hD.Z_le j)
    have hz' := hmod hz
    have hGM : (Gp ⊓ M).map θ.toMonoidHom =
        (Subgroup.normalizer (R j : Set (antiSp F))).map Φ := by
      rw [Subgroup.map_inf_eq _ _ _ hθinj, hM, ← hInn, ← hRI, inf_comm, ← C.N_inf_range j]
    have hmem : θ x ∈ (ctr (oPPrime 2 (Gp ⊓ M))).map θ.toMonoidHom := by
      rw [← burnsideF4m_ctr_map _ hθinj, ← burnsideF4gD4Inv_map_oPPrime _ hθinj, hGM,
        burnsideF4gD4Inv_map_oPPrime _ C.P.inj, burnsideF4m_ctr_map _ C.P.inj]
      exact ⟨z, hz', hzx⟩
    exact (Subgroup.mem_map_iff_mem hθinj).mp hmem
  exact ⟨hZ 0 hθM1, hZ 1 hθM2, hQ 0 hθM1, hQ 1 hθM2, hQ12⟩

theorem burnsideF4m_sp4_core [Finite E] (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    (hodd : ¬ Odd Gp.index) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.Sp4 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) ∧
    pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
    pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4gSp_yam_of_marking hf marking
  rw [← h1, ← h2] at hTD
  obtain ⟨θ, hθ1, hθ2, -⟩ := burnsideF4m_core_theta hyp.toHypF_4_4g hTD
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).K := Finite.of_equiv E θ.toEquiv
  have hD := burnsideF4g_lieModel_Sp4 hf hyp.model
  have hev : ¬ Odd (Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).K / Nat.card ↥Gp) := by
    have hK : Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).K = Nat.card E :=
      Nat.card_congr θ.toEquiv.symm
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [← this, Nat.mul_div_cancel_left _ hpos]
    exact hodd
  have hsGp : IsSimpleGroup ↥Gp := by
    obtain ⟨-, F', fF', finF', cF', hF', ⟨e'⟩⟩ := exists_equiv_antiSp hD
    have hF'4 : 4 ≤ Nat.card F' := by
      rw [hF']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    haveI := (CFSG.Quasithin.F7Two.isSimpleGroup_antiSp (K := F') hF'4).1
    exact e'.isSimpleGroup
  obtain ⟨m, F, fF, finF, cF, Φ, ψ, k₀, R, i, -, C, -, -⟩ :=
    SpOut2.exists_outCtx hD (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt hev
  obtain ⟨c1, c2, q1, q2, q12⟩ := burnsideF4m_sp4_core_of_outCtx hyp.centralizer_trivial hsGp θ
    (N := ![(burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).Mb1,
      (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).Mb2]) hθ1 hθ2 C
  exact ⟨fun x hx _ _ => c1 x hx, fun x hx _ _ => ⟨rfl, c2 x hx⟩, q1, q2, q12⟩

end Sp4

end CFSG.ASVolI
