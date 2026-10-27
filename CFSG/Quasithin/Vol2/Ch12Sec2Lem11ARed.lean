module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11AAlt
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11Stmts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

namespace Lem11A

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem finite_mulAut (V : Type) [Group V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun σ : MulAut V => (σ : V → V)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem le_centralizer_of_perm3 {T L V A : Subgroup G} (hH : Hyp1223 G T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hperm : Perm3 ↥(autOn L V)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hAp : IsPGroup p ↥A) (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hAL : autOn A V ≤ autOn L V) : A ≤ Subgroup.centralizer (V : Set G) := by
  have : Finite (MulAut ↥V) := finite_mulAut ↥V
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_hyp1223 hH
  have hTLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow le_sup_right
  have hprod : ∀ h ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, h = l * t := by
    intro h hh
    have hmem : h ∈ ((L ⊔ T : Subgroup G) : Set G) := hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hH.normalizes] at hmem
    obtain ⟨l, hl, t, ht, rfl⟩ := hmem
    exact ⟨l, hl, t, ht, rfl⟩
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    Setup.Wreath.isSylowTwoOf_inf_of_prod hTLT le_sup_left hprod
  have hS₀ : IsSylowTwoOf (autOn (T ⊓ L) V) (autOn L V) :=
    Lem22.isSylowTwoOf_map_hom (Lem22.isSylowTwoOf_subgroupOf_of_le hLV hTL) (conjAct V)
  have hT2 : IsPGroup 2 ↥(autOn T V) :=
    (hTLT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map (conjAct V)
  have hS₀le : autOn (T ⊓ L) V ≤ autOn T V ⊓ autOn L V :=
    le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
      (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))
  have hSb : IsSylowTwoOf (autOn T V ⊓ autOn L V) (autOn L V) := by
    refine ⟨inf_le_right, hT2.to_le inf_le_left, fun h2 => hS₀.2.2 (h2.trans ?_)⟩
    exact Subgroup.index_dvd_of_le (Subgroup.comap_mono hS₀le)
  have hAb : IsPGroup p ↥(autOn A V) :=
    (hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm).map (conjAct V)
  by_contra hAC
  have hAb1 : autOn A V ≠ ⊥ := by
    intro h0
    apply hAC
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hmem : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V :=
      ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    have h1 : a * v * a⁻¹ = v := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) hmem
    calc v * a = a * v * a⁻¹ * a := by rw [h1]
      _ = a * v := by group
  have hSX : ∀ s ∈ autOn T V ⊓ autOn L V, ∀ x ∈ autOn A V,
      ∃ x' ∈ autOn A V, ∃ s' ∈ autOn T V ⊓ autOn L V, s * x = x' * s' := by
    intro s hs x hx
    obtain ⟨⟨t, htT, rfl⟩, hsL⟩ := hs
    obtain ⟨a, haA, rfl⟩ := hx
    have htT' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp htT
    have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
    have hta : (t : G) * (a : G) ∈ (T : Set G) * (A : Set G) := Set.mul_mem_mul htT' haA'
    rw [← hAT] at hta
    obtain ⟨a', ha', t', ht', he⟩ := hta
    have hconj : conjAct V t * conjAct V a =
        conjAct V ⟨a', hAN ha'⟩ * conjAct V ⟨t', hTV ht'⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact he.symm
    have hx'L : conjAct V ⟨a', hAN ha'⟩ ∈ autOn L V :=
      hAL ⟨⟨a', hAN ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩
    have hxL : conjAct V a ∈ autOn L V := hAL ⟨a, haA, rfl⟩
    refine ⟨conjAct V ⟨a', hAN ha'⟩, ⟨⟨a', hAN ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩,
      conjAct V ⟨t', hTV ht'⟩, ⟨⟨⟨t', hTV ht'⟩, Subgroup.mem_subgroupOf.mpr ht', rfl⟩, ?_⟩, hconj⟩
    have he' : conjAct V ⟨t', hTV ht'⟩ =
        (conjAct V ⟨a', hAN ha'⟩)⁻¹ * (conjAct V t * conjAct V a) := by
      rw [hconj]
      group
    rw [he']
    exact (autOn L V).mul_mem ((autOn L V).inv_mem hx'L) ((autOn L V).mul_mem hsL hxL)
  have hS : IsSylowTwoOf ((autOn T V ⊓ autOn L V).subgroupOf (autOn L V)) ⊤ :=
    KGMinPar.isSylowTwoOf_subgroupOf hSb
  have hX : IsPGroup p ↥((autOn A V).subgroupOf (autOn L V)) :=
    hAb.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
  have hX1 : (autOn A V).subgroupOf (autOn L V) ≠ ⊥ := by
    intro h0
    apply hAb1
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hAL hx⟩ : ↥(autOn L V)) ∈ (autOn A V).subgroupOf (autOn L V) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [h0, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hSX' : ∀ s ∈ (autOn T V ⊓ autOn L V).subgroupOf (autOn L V),
      ∀ x ∈ (autOn A V).subgroupOf (autOn L V),
      ∃ x' ∈ (autOn A V).subgroupOf (autOn L V),
        ∃ s' ∈ (autOn T V ⊓ autOn L V).subgroupOf (autOn L V), s * x = x' * s' := by
    intro s hs x hx
    obtain ⟨x', hx', s', hs', he⟩ := hSX s (Subgroup.mem_subgroupOf.mp hs) x
      (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨⟨x', hAL hx'⟩, Subgroup.mem_subgroupOf.mpr hx', ⟨s', hSb.1 hs'⟩,
      Subgroup.mem_subgroupOf.mpr hs', Subtype.ext he⟩
  have h3 := hperm _ _ p hS hp (by omega) hX hX1 hSX'
  omega

omit [Finite G] in
theorem pCoreOf_eq_map' (L : Subgroup G) : pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype := by
  show (CFSG.Open.pCore 2 ↥L).map L.subtype = _
  try with_reducible rfl

omit [Finite G] in
theorem nonempty_autOn_equiv_of_ker {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Γ : Type} [Group Γ] (φ : ↥L →* Γ)
    (hφ : Function.Surjective φ)
    (hk : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    Nonempty (↥(autOn L V) ≃* Γ) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective (autOnSurj hLV)
      (autOnSurj_surjective hLV)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_autOnSurj hLV).trans hk.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩

theorem nonempty_autOn_equiv_quot {T L V : Subgroup G} (hH : Hyp1223 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    [IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)] :
    Nonempty (↥(autOn L V) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hle : CFSG.pCore 2 ↥L ≤ (autOnSurj hLV).ker := by
    intro x hx
    rw [mem_ker_autOnSurj]
    apply pCoreOf_le_centralizer_of_hyp1223 hH hred
    rw [pCoreOf_eq_map' L]
    exact ⟨x, hx, rfl⟩
  set q := QuotientGroup.lift (CFSG.pCore 2 ↥L) (autOnSurj hLV) hle with hq
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := autOnSurj_surjective hLV y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hqi : Function.Injective q := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal q.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff q).mp h
    · exfalso
      apply not_le_centralizer_of_hyp1223 hH
      intro l hl
      have h1 : (QuotientGroup.mk ⟨l, hl⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ q.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at h1
      have h2 : (⟨l, hl⟩ : ↥L) ∈ (autOnSurj hLV).ker := h1
      exact (mem_ker_autOnSurj hLV _).mp h2
  exact ⟨(MulEquiv.ofBijective q ⟨hqi, hqs⟩).symm⟩

theorem perm3_autOn
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    [hcomm : IsMulCommutative ↥V] (hmod : Modules12_2_2 L V) : Perm3 ↥(autOn L V) := by
  have : Finite (MulAut ↥V) := finite_mulAut ↥V
  have hLV := le_normalizer_of_hyp1223 hH
  rcases hmod with ⟨n, hn, -, hnat⟩ | ⟨⟨eQ⟩, -, -⟩ | ⟨⟨eQ⟩, -, -⟩ |
    ⟨n, hn5, hn8, ⟨φ, hφs, hφk⟩, -⟩ | ⟨-, φ, hφs, hφk⟩ | ⟨hlie, -⟩ | ⟨-, hZ3, ⟨eA⟩, hLC, -, -⟩
  ·
    have htop := eq_top_of_binaryNaturalSL_one hnat
    obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
    have hcard : Nat.card ↥V = 2 ^ n := by
      have h1 := card_eq_of_realizesVia_nat hπ
      rw [Subgroup.card_top, Subgroup.card_bot, mul_one, Nat.card_fun, hK, Nat.card_fin] at h1
      rw [h1, pow_one]
    have hcomm' : ∀ x y : ↥V, x * y = y * x := fun x y => hcomm.is_comm.comm x y
    rw [htop]
    exact Perm3.of_mulEquiv Subgroup.topEquiv
      (perm3_mulAut ↥V n hn hcard hcomm' (sq_eq_one_of_hyp1223 hH hred))
  ·
    have := isSimpleGroup_sl_zmodTwo (n := 3) (by norm_num)
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := eQ.isSimpleGroup
    obtain ⟨e⟩ := nonempty_autOn_equiv_quot hH hred
    exact Perm3.of_mulEquiv (e.trans eQ) perm3_sl_three
  ·
    have := isSimpleGroup_sl_zmodTwo (n := 5) (by norm_num)
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := eQ.isSimpleGroup
    obtain ⟨e⟩ := nonempty_autOn_equiv_quot hH hred
    exact Perm3.of_mulEquiv (e.trans eQ) perm3_sl_five
  ·
    obtain ⟨e⟩ := nonempty_autOn_equiv_of_ker hLV φ hφs hφk
    interval_cases n
    · exact Perm3.of_mulEquiv e perm3_alt_five
    · exact Perm3.of_mulEquiv e perm3_alt_six
    · exact Perm3.of_mulEquiv e perm3_alt_seven
    · exact Perm3.of_mulEquiv e perm3_alt_eight
  ·
    obtain ⟨e⟩ := nonempty_autOn_equiv_of_ker hLV φ hφs hφk
    exact Perm3.of_mulEquiv e perm3_alt_seven
  ·
    obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hlie
    obtain ⟨e2⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
    have := CFSG.Quasithin.isSimpleGroup_u33Pres
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (e1.trans e2.symm).isSimpleGroup
    obtain ⟨e⟩ := nonempty_autOn_equiv_quot hH hred
    obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hlie
    exact Perm3.of_mulEquiv (e.trans eU) perm3_u33
  ·
    have hk : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker =
        (Subgroup.centralizer (V : Set G)).subgroupOf L := by
      rw [QuotientGroup.ker_mk']
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have h1 : (x : G) ∈ pCoreOf 2 L := by
          rw [pCoreOf_eq_map' L]
          exact ⟨x, hx, rfl⟩
        rw [← hLC] at h1
        exact h1.2
      · intro hx
        have h1 : (x : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := ⟨x.2, hx⟩
        rw [hLC, pCoreOf_eq_map' L] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        rwa [show y = x from Subtype.ext hyx] at hy
    obtain ⟨e⟩ := nonempty_autOn_equiv_of_ker hLV (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) hk
    refine Perm3.of_mulEquiv e (Perm3.of_surjective
      (eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))))
      (eA.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ perm3_alt_six)
    have hker : (eA.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))).ker =
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])

end Lem11A

open Lem11A

theorem lem12211A315_of
    (h1222 : Stmt12_2_2) : Lem12211A315 := by
  intro G _ _ T L V h A p hp hp3 hAMV hAp _ hAT hAL
  obtain ⟨-, -, hall⟩ := ((h1222 G T h.simple h.nonabelian h.qtke h.sylow).resolve_left
    h.notAlt) L h.maximal h.faithful h.quasisimple
  obtain ⟨⟨-, hTV, hred, -⟩, -, -, hcomm, hmod⟩ := hall V h.irrPlus
  exact le_centralizer_of_perm3 h hTV (perm3_autOn h hred hmod) hp hp3
    (hAMV.trans inf_le_right) hAp hAT hAL

end CFSG.Quasithin.H13
