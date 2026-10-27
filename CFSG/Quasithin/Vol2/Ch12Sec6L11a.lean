module

public import CFSG.Quasithin.Vol2.Ch12Sec6L610
public import CFSG.Quasithin.Vol2.Ch12Sec6L16d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem not_le_M_of_lt (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hlt : Lv L v < Kv) :
    ¬ Kv ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hL5 := S126L1a.part5 h1222 h1228 hC.hyp
  have hKp : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hKG : Kv ≤ Gv v := by
    rw [hC.kv_eq]
    exact ((Subgroup.closure_le _).2 fun x hx => hx.1).trans (perfectCore_le _)
  have hKL : Kv ≤ L := by
    have h1 : Kv ≤ oThreePrimeResidual (Subgroup.normalizer (L : Set G)) := by
      have hgen : Kv = oThreePrimeResidual (perfectCore (Gv v)) := hC.kv_eq
      calc Kv = oThreePrimeResidual (perfectCore (Gv v)) := hgen
        _ ≤ oThreePrimeResidual (Subgroup.normalizer (L : Set G)) := by
          refine (Subgroup.closure_le _).2 fun x hx => Subgroup.subset_closure ⟨hKM ?_, hx.2⟩
          rw [hgen]
          exact Subgroup.subset_closure hx
    rwa [hL5] at h1
  exact hlt.not_ge (le_perfectCore_of_perfect (le_inf hKL hKG) hKp)

noncomputable abbrev evC (i : Fin 8) : PermMod 8 →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 8 => ZMod 2) i)

noncomputable abbrev core01 : Subgroup ↥(coreMod 8) :=
  ((evC 0).comp (coreMod 8).subtype).ker ⊓ ((evC 1).comp (coreMod 8).subtype).ker

theorem mem_core01 {c : ↥(coreMod 8)} :
    c ∈ core01 ↔ Multiplicative.toAdd (c : PermMod 8) 0 = 0 ∧
      Multiplicative.toAdd (c : PermMod 8) 1 = 0 := by
  simp only [core01, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.coe_subtype, AddMonoidHom.toMultiplicative_apply_apply, Pi.evalAddMonoidHom_apply]
  exact ⟨fun h => ⟨toAdd_eq_zero.1 (congrArg Multiplicative.toAdd h.1 |>.trans toAdd_one),
    toAdd_eq_zero.1 (congrArg Multiplicative.toAdd h.2 |>.trans toAdd_one)⟩,
    fun h => ⟨by rw [h.1]; rfl, by rw [h.2]; rfl⟩⟩

theorem coord_mul_coreAct_inv (c : ↥(coreMod 8)) (σ : Equiv.Perm (Fin 8)) {i : Fin 8}
    (hσ : σ⁻¹ i = i) :
    Multiplicative.toAdd ((c * coreAct 8 σ c⁻¹ : ↥(coreMod 8)) : PermMod 8) i = 0 := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coreAct_coe, toAdd_mul, toAdd_inv,
    Pi.add_apply, Pi.neg_apply, permAct_apply, map_inv]
  rw [hσ]
  ring

theorem coord_of_mem_Vv (h1222 : Stmt12_2_2) {F : Frame126 T L V} (E : S126FE.Frame126E F)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {u : G} (hu : u ∈ V) (huv : u ∈ Vv L V v) : E.γ ⟨u, hu⟩ ∈ core01 := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have key : ∀ x (hx : x ∈ V), ∀ l ∈ Lv L v, ∃ hy : l * x⁻¹ * l⁻¹ ∈ V,
      E.γ (⟨x, hx⟩ * ⟨_, hy⟩) ∈ core01 := by
    intro x hx l hl
    have hlL : l ∈ L := Lv_le_L L v hl
    have hlV : l ∈ Subgroup.normalizer (V : Set G) := hLV hlL
    have hσ : psiP F hH ⟨l, hlL⟩ ∈ A6s := psiP_mem_A6s h1222 F hH hv hβ
      (show (⟨l, hlL⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hl)
    obtain ⟨hσ0, hσ1, -⟩ := mem_A6s.1 hσ
    have hy : l * x⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hlV _).1 (V.inv_mem hx)
    have hγ : E.γ ⟨_, hy⟩ = coreAct 8 (psiP F hH ⟨l, hlL⟩) (E.γ ⟨x, hx⟩⁻¹) :=
      E.act l (Subgroup.le_normalizer hlL) hlV _ (actsAs_psiP F hH ⟨l, hlL⟩) ⟨x, hx⟩⁻¹ ⟨_, hy⟩
        rfl
    have hm : E.γ (⟨x, hx⟩ * ⟨_, hy⟩) =
        E.γ ⟨x, hx⟩ * coreAct 8 (psiP F hH ⟨l, hlL⟩) (E.γ ⟨x, hx⟩)⁻¹ := by
      rw [map_mul, hγ, map_inv]
    refine ⟨hy, ?_⟩
    rw [hm]
    refine mem_core01.2 ⟨coord_mul_coreAct_inv _ _ ?_, coord_mul_coreAct_inv _ _ ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hσ0]
    · rw [Equiv.Perm.inv_eq_iff_eq, hσ1]
  have hle : Vv L V v ≤ (core01.comap E.γ.toMonoidHom).map V.subtype := by
    rw [Vv, Subgroup.commutator_le]
    intro x hx l hl
    obtain ⟨hy, hmem⟩ := key x hx l hl
    refine ⟨⟨x, hx⟩ * ⟨_, hy⟩, hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, commutatorElement_def]
    group
  obtain ⟨w, hw, hwu⟩ := hle huv
  have hwu' : w = ⟨u, hu⟩ := Subtype.ext hwu
  rw [← hwu']
  exact hw

theorem pv_zero_of_two_le : ∀ i j : Fin 8, 2 ≤ i.val → 2 ≤ j.val →
    B5FinS8.pv i j 0 = 0 ∧ B5FinS8.pv i j 1 = 0 := by
  decide

theorem mem_six_of_two_le : ∀ i : Fin 8, 2 ≤ i.val → i ∈ six := by
  decide

theorem eq_of_mk_eq {x y : ↥(coreMod 8)} (hx : Multiplicative.toAdd (x : PermMod 8) 0 = 0)
    (hy : Multiplicative.toAdd (y : PermMod 8) 0 = 0)
    (h : (QuotientGroup.mk x : D8) = QuotientGroup.mk y) : x = y := by
  have h1 : (QuotientGroup.mk (x⁻¹ * y) : D8) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel]
  rcases (S126FE.mk_eq_one_iff _).1 h1 with h2 | h2
  · exact inv_mul_eq_one.1 h2
  · exfalso
    have h3 := congrArg (fun c : ↥(coreMod 8) => Multiplicative.toAdd (c : PermMod 8) 0) h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
      Pi.neg_apply, hx, hy, neg_zero, add_zero] at h3
    exact absurd h3 (by decide)

theorem gamma_of_mem_Delta (h1222 : Stmt12_2_2) {F : Frame126 T L V} (E : S126FE.Frame126E F)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {u : G} (hu : u ∈ Delta F v) :
    ∃ huV : u ∈ V, ∃ i j : Fin 8, i ∈ six ∧ j ∈ six ∧ i ≠ j ∧ E.γ ⟨u, huV⟩ = pe i j ∧
      F.β ⟨u, huV⟩ = QuotientGroup.mk (pe i j) := by
  obtain ⟨huV, huv, i, j, hi, hj, hij, hβu⟩ := hu
  refine ⟨huV, i, j, mem_six_of_two_le i hi, mem_six_of_two_le j hj, hij, ?_, hβu⟩
  have hc := mem_core01.1 (coord_of_mem_Vv h1222 E hH hv hβ huV huv)
  refine eq_of_mk_eq hc.1 ?_ ?_
  · rw [S126L20a.toAdd_pe]
    exact (pv_zero_of_two_le i j hi hj).1
  · rw [← E.β_eq, hβu]

theorem exists_conj_eq_of_mem_Delta (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hA : WtTwo F v ∨ V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {u : G}
    (hu : u ∈ Delta F v) : ∃ l ∈ L, l * v * l⁻¹ = u := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  rcases hA with ⟨E, hv', hw⟩ | hZ
  · obtain ⟨huV, i, j, -, -, hij, hγu, hβu⟩ := gamma_of_mem_Delta h1222 E hH hv hβ hu
    obtain ⟨g, -, hg01⟩ := exists_conj_Lv F hH hv hβ huV hij hβu
    have hwV : (g : G) * v * (g : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV g.2) v).1 hv
    have hpe : pe (psiP F hH g 0) (psiP F hH g 1) = pe i j := by
      rcases hg01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, S126L20a.pe_comm]
    have hγv : E.γ ⟨v, hv⟩ = pe 0 1 := gamma_eq_pe F E hv hβ hw
    have hγw : E.γ ⟨_, hwV⟩ = coreAct 8 (psiP F hH g) (E.γ ⟨v, hv⟩) :=
      E.act g (Subgroup.le_normalizer g.2) (hLV g.2) _ (actsAs_psiP F hH g) ⟨v, hv⟩ ⟨_, hwV⟩ rfl
    have heq : (⟨_, hwV⟩ : ↥V) = ⟨u, huV⟩ :=
      E.γ.injective (by rw [hγw, hγv, S126L20a.coreAct_pe, hpe, hγu])
    exact ⟨g, g.2, congrArg Subtype.val heq⟩
  · obtain ⟨huV, -, i, j, -, -, hij, hβu⟩ := hu
    obtain ⟨g, -, hg01⟩ := exists_conj_Lv F hH hv hβ huV hij hβu
    have hwV : (g : G) * v * (g : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV g.2) v).1 hv
    have hpe : pe (psiP F hH g 0) (psiP F hH g 1) = pe i j := by
      rcases hg01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, S126L20a.pe_comm]
    have hβw : F.β ⟨_, hwV⟩ = F.β ⟨u, huV⟩ := by
      have hact := actsAs_psiP F hH g ⟨v, hv⟩ ⟨_, hwV⟩ rfl
      rw [hact, hβ, S126L20a.dAct_pe, hpe, hβu]
    have h1 : F.β (⟨_, hwV⟩ * (⟨u, huV⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, hβw, mul_inv_cancel]
    have hmem : (g : G) * v * (g : G)⁻¹ * u⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨V.mul_mem hwV (V.inv_mem huV), (F.β_ker _).1 h1⟩
    rw [hZ, Subgroup.mem_bot] at hmem
    exact ⟨g, g.2, mul_inv_eq_one.1 hmem⟩

theorem exists_A6s_pair {i j i' j' : Fin 8} (hi : i ∈ six) (hj : j ∈ six) (hij : i ≠ j)
    (hi' : i' ∈ six) (hj' : j' ∈ six) (hij' : i' ≠ j') :
    ∃ τ ∈ A6s, τ i = i' ∧ τ j = j' := by
  classical
  obtain ⟨hi0, hi1⟩ := (mem_six_iff i).1 hi
  obtain ⟨hj0, hj1⟩ := (mem_six_iff j).1 hj
  obtain ⟨hi0', hi1'⟩ := (mem_six_iff i').1 hi'
  obtain ⟨hj0', hj1'⟩ := (mem_six_iff j').1 hj'
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 4 := by
    have h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 6 := by
      have := alternatingGroup.isMultiplyPretransitive (Fin 8)
      rwa [Nat.card_fin] at this
    exact MulAction.isMultiplyPretransitive_of_le (show 4 ≤ 6 by norm_num)
      (by rw [Nat.card_fin]; norm_num)
  let e : Fin 4 ↪ Fin 8 := ⟨![0, 1, i, j], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩
  let e' : Fin 4 ↪ Fin 8 := ⟨![0, 1, i', j'], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) e e'
  have hτi : ∀ a : Fin 4, (τ : Equiv.Perm (Fin 8)) (e a) = e' a := fun a => by
    have := congrArg (fun f : Fin 4 ↪ Fin 8 => f a) hτ
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using this
  refine ⟨τ, mem_A6s.2 ⟨hτi 0, hτi 1, τ.2⟩, hτi 2, hτi 3⟩

theorem eq_of_beta_eq_of_mem_Vv (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u u' : G} (hu : u ∈ V)
    (hu' : u' ∈ V) (huv : u ∈ Vv L V v) (huv' : u' ∈ Vv L V v)
    (h : F.β ⟨u, hu⟩ = F.β ⟨u', hu'⟩) : u = u' := by
  by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · have h1 : F.β (⟨u, hu⟩ * (⟨u', hu'⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hmem : u * u'⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨V.mul_mem hu (V.inv_mem hu'), (F.β_ker _).1 h1⟩
    rw [hZ, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.1 hmem
  · obtain ⟨E⟩ := S126FE.exists_frame126E h1222 F hH hZ
    have hc := mem_core01.1 (coord_of_mem_Vv h1222 E hH hv hβ hu huv)
    have hc' := mem_core01.1 (coord_of_mem_Vv h1222 E hH hv hβ hu' huv')
    have heq : E.γ ⟨u, hu⟩ = E.γ ⟨u', hu'⟩ :=
      eq_of_mk_eq hc.1 hc'.1 (by rw [← E.β_eq, ← E.β_eq, h])
    exact congrArg Subtype.val (E.γ.injective heq)

omit [IsMulCommutative ↥V] in
theorem Lv_le_normalizer_Vv (hH : Hyp126 G T L V) (v : G) :
    Lv L v ≤ Subgroup.normalizer (Vv L V v : Set G) :=
  le_normalizer_commutator_of_le ((Lv_le_L L v).trans hH.hyp.irrPlus.2.2.1)
    Subgroup.le_normalizer

theorem exists_Lv_conj_eq (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u u' : G}
    (hu : u ∈ Delta F v) (hu' : u' ∈ Delta F v) : ∃ l ∈ Lv L v, l * u * l⁻¹ = u' := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨huV, huv, i, j, hi, hj, hij, hβu⟩ := hu
  obtain ⟨huV', huv', i', j', hi', hj', hij', hβu'⟩ := hu'
  obtain ⟨τ, hτ, hτi, hτj⟩ := exists_A6s_pair (mem_six_of_two_le i hi) (mem_six_of_two_le j hj)
    hij (mem_six_of_two_le i' hi') (mem_six_of_two_le j' hj') hij'
  obtain ⟨l, hl, hlτ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ τ hτ
  have hwV : (l : G) * u * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV l.2) u).1 huV
  have hwv : (l : G) * u * (l : G)⁻¹ ∈ Vv L V v :=
    (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) u).1 huv
  have hβw : F.β ⟨_, hwV⟩ = F.β ⟨u', huV'⟩ := by
    have hact := actsAs_psiP F hH l ⟨u, huV⟩ ⟨_, hwV⟩ rfl
    rw [hact, hβu, hlτ, S126L20a.dAct_pe, hτi, hτj, hβu']
  exact ⟨l, hl, eq_of_beta_eq_of_mem_Vv h1222 hH hv hβ hwV huV' hwv huv' hβw⟩

theorem mem_M_of_perm_Delta (h1222 : Stmt12_2_2) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hLK : Lv L v = Kv) {g : G}
    (hgΔ : ∀ u ∈ Delta F v, g * u * g⁻¹ ∈ Delta F v) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  by_cases hA : WtTwo F v ∨ V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  ·
    have hLu : ∀ u ∈ Delta F v, Lv L u = oThreePrimeResidual (perfectCore (Gv u)) := by
      intro u hu
      obtain ⟨l, hl, rfl⟩ := exists_conj_eq_of_mem_Delta h1222 hH hv hβ hA hu
      rw [Lv_conj hl, hLK, hC.kv_eq, map_conj_oThreePrimeResidual, map_perfectCore,
        map_conj_Gv]
    have hgLu : ∀ u ∈ Delta F v,
        (Lv L u).map (MulAut.conj g).toMonoidHom = Lv L (g * u * g⁻¹) := by
      intro u hu
      rw [hLu u hu, hLu _ (hgΔ u hu), map_conj_oThreePrimeResidual, map_perfectCore,
        map_conj_Gv]
    rw [← lemma12_6_10_of h1222 G T L V F v Kv S hC]
    set K := ⨆ u ∈ Delta F v, Lv L u with hK
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_iSup]
      refine iSup_le fun u => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hu => ?_
      rw [hgLu u hu]
      exact le_iSup₂_of_le (g * u * g⁻¹) (hgΔ u hu) le_rfl
    refine (Subgroup.mem_normalizer_iff_map_conj_eq).2 (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  ·
    rw [not_or] at hA
    obtain ⟨hwt, hZ⟩ := hA
    obtain ⟨E⟩ := S126FE.exists_frame126E h1222 F hH hZ
    obtain ⟨u0, hu0, -⟩ := exists_mem_Delta h1222 F hH hv hβ (a := 2) (b := 3) (by decide)
      (by decide) (by decide)
    obtain ⟨l, hl, hlu⟩ := exists_Lv_conj_eq h1222 hH hv hβ (hgΔ u0 hu0) hu0
    have hwt0 : WtTwo F u0 := by
      obtain ⟨huV, i, j, -, -, hij, hγu, -⟩ := gamma_of_mem_Delta h1222 E hH hv hβ hu0
      exact ⟨E, huV, by rw [hγu]; exact S126L20a.wt_pe hij⟩
    have hGu : Gv u0 ≤ Subgroup.normalizer (L : Set G) := by
      by_contra h
      exact hwt (hC.choice hZ ⟨u0, hwt0, h⟩)
    have hlg : l * g ∈ Gv u0 := by
      show l * g ∈ Subgroup.centralizer {u0}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * g * u0 = l * (g * u0 * g⁻¹) * l⁻¹ * (l * g) := by group
        _ = u0 * (l * g) := by rw [hlu]
    have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (Lv_le_L L v hl)
    have e : g = l⁻¹ * (l * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hlM) (hGu hlg)

end S126T2

end CFSG.Quasithin.H13
