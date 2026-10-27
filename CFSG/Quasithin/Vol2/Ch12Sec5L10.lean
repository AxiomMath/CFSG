module

public import CFSG.Quasithin.Vol2.Ch12Sec5L10m
public import CFSG.Quasithin.Vol2.Ch12Sec5L9

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125L7 S125L9 Matrix
open scoped IsMulCommutative commutatorElement

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "W10" => Fin 10 → ZMod 2

namespace S125L10

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem isUpperTri_of_mem (F : Frame125 T L V) {u : SL5} (hu : psiL F u ∈ autOn T V) :
    IsUpperTri u := by
  obtain ⟨t, htN, htT, hta⟩ := mem_autOn_iff_exists.mp hu
  obtain ⟨u', hu', hact⟩ := F.borel t htT
  have heq : psiL F u' = psiL F u := by
    rw [← hta]
    refine MulEquiv.ext fun v => F.e.injective (Multiplicative.toAdd.injective ?_)
    rw [e_psiL, hact v (conjAct V ⟨t, htN⟩ v) rfl, toAdd_ofAdd]
  rw [← psiL_injective F heq]
  exact hu'

omit [Finite G] in
theorem psiL_gamma (F : Frame125 T L V) {a : MulAut ↥V} (ha : a ∈ autOn L V) :
    psiL F (F.γ ⟨a, ha⟩) = a := by
  change ((F.γ.symm (F.γ ⟨a, ha⟩) : ↥(autOn L V)) : MulAut ↥V) = a
  rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem mem_urad_of_fix {u : SL5} (hu : IsUpperTri u)
    (hfix : ∀ k : Fin 10, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7) →
      JonesParshall.wedgeRep u (Pi.single k 1) = Pi.single k 1) : u ∈ S125L7m.Urad := by
  have huni := S125L7m.eq_uni hu
  have hf : ∀ k : Fin 10, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 7) →
      JonesParshall.wedgeMat (S125L7m.uni (S125L7m.cv u)) *ᵥ Pi.single k 1 = Pi.single k 1 :=
    fun k hk => by rw [← huni, ← S125ZV.wedgeRep_apply]; exact hfix k hk
  have e1 := (S125L7m.fix1 _).1 (hf 1 (by tauto))
  have e4 := (S125L7m.fix4 _ e1).1 (hf 4 (by tauto))
  have e2 := (S125L7m.fix2 _).1 (hf 2 (by tauto))
  have e5 := (S125L7m.fix5 _ e4.1 e4.2 e1 e2.1 e2.2).1 (hf 5 (by tauto))
  exact ⟨_, huni.trans (S125L7m.uni_eq_ub e4.1 e4.2 e5 e1 e2.1 e2.2)⟩

theorem autOn_R6_eq (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (ri T L F.V6) V = S125L7m.Urad.map (psiL F) := by
  obtain ⟨-, -, -, hRC, -, -⟩ := (lemma12_5_2_of h1222 G T L V F hH).2.2.2
  have hRT : ri T L F.V6 ≤ T :=
    pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hle : autOn (ri T L F.V6) V ≤ S125L7m.Urad.map (psiL F) := by
    intro a ha
    have haT : a ∈ autOn T V := A4.autOn_mono hRT ha
    have haL : a ∈ autOn L V := S125St.autOn_T_le F haT
    have hψ := psiL_gamma F haL
    have hψT : psiL F (F.γ ⟨a, haL⟩) ∈ autOn T V := by rw [hψ]; exact haT
    refine ⟨F.γ ⟨a, haL⟩, mem_urad_of_fix (isUpperTri_of_mem F hψT) fun k hk => ?_, hψ⟩
    obtain ⟨r, hrN, hrR, hra⟩ := mem_autOn_iff_exists.mp ha
    set v : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single k 1)) with hv
    have hv6 : (v : G) ∈ F.V6 := by
      refine (mem_sub_iff F _ v).2 fun j hj => ?_
      rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      refine Pi.single_eq_of_ne (fun h => hj ?_) _
      rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hfixv : psiL F (F.γ ⟨a, haL⟩) v = v := by
      rw [hψ, ← hra]
      apply Subtype.ext
      change r * (v : G) * r⁻¹ = v
      rw [(Subgroup.mem_centralizer_iff.1 (hRC hrR) _ hv6).symm]
      group
    have h := (psiL_fix_iff F _ v).1 hfixv
    rwa [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_map_urad, S125L9a.card_R6 h1222 F hH])

@[expose] noncomputable def phiA {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    ↥A →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hA)

omit [Finite G] in
theorem range_phiA {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (phiA hA).range = autOn A V := by
  unfold phiA autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem padicValNat_le_three {n : ℕ} (h : n ≤ 8) : padicValNat 2 n ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  calc padicValNat 2 n ≤ Nat.log 2 n := padicValNat_le_nat_log n
    _ ≤ Nat.log 2 8 := Nat.log_mono_right h
    _ = 3 := by decide

theorem padicValNat_lt_two {n : ℕ} (h0 : n ≠ 0) (h : n ≤ 2) : padicValNat 2 n < 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  interval_cases n
  · exact absurd rfl h0
  · simp
  · simp

omit [Finite G] in
theorem centralizer_le_normalizer_conj (hr : 3 < E3.rParam V) {g : G} {U : Subgroup G}
    (hUV : U ≤ conjSubgroup V g) (hU : E3.mQuot (conjSubgroup V g) U ≤ 3) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hVg : B3.cj g (conjSubgroup V g) = V := by
    ext x
    rw [B3.mem_cj, mem_conjSubgroup_iff]
    constructor <;> intro hx <;> convert hx using 1 <;> group
  have hU'V : B3.cj g U ≤ V := hVg ▸ cj_le_cj hUV
  have hm : E3.mQuot V (B3.cj g U) = E3.mQuot (conjSubgroup V g) U := by
    unfold E3.mQuot
    have h1 : (B3.cj g U).relIndex (B3.cj g (conjSubgroup V g)) =
        U.relIndex (conjSubgroup V g) :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _
        (MulAut.conj g).injective
    rw [hVg] at h1
    rw [h1]
  have hC : Subgroup.centralizer (B3.cj g U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    by_contra hC
    have h1 : E3.rParam V ≤ (E3.mQuot V (B3.cj g U) : ℕ∞) :=
      iInf₂_le (f := fun U (_ : U ∈ {U : Subgroup G | U ≤ V ∧
        ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)}) =>
          (E3.mQuot V U : ℕ∞)) _ ⟨hU'V, hC⟩
    have h3 : (E3.mQuot V (B3.cj g U) : ℕ∞) ≤ 3 := by
      rw [hm]
      exact_mod_cast hU
    exact absurd (lt_of_lt_of_le hr (h1.trans h3)) (lt_irrefl _)
  intro y hy
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer (B3.cj g U : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hy u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
      _ = g * (y * u) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * (g * u * g⁻¹) := by group
  have hN := hC hy'
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro z
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have h1 := hN (g * z * g⁻¹)
  convert h1 using 2
  group

theorem le_centralizer_of_le_normalizer (h1222 : Stmt12_2_2) (hH : Hyp125 G T L V)
    (h7 : Concl12_5_7 T L V) (hV2 : IsPGroup 2 V) {g : G}
    (hgN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G)) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hidx : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (V : Set G))).index := by
    intro h2
    apply hyp.sylow.2
    rw [← Subgroup.relIndex_mul_index hf.T_le]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨m, hmN, hm⟩ := B3.exists_conj_le_sylow_sub hf.T_le hyp.sylow.1 hidx hgN (hV2.map _)
  have h1 : B3.cj m (conjSubgroup V g) = CFSG.conjugate V (g * m⁻¹) := cj_conjugate m g V
  have hW : CFSG.conjugate V (g * m⁻¹) ≤ E3.wClos V 0 T :=
    le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) (CFSG.conjugate V (g * m⁻¹))
      ⟨h1 ▸ hm, g * m⁻¹, le_rfl, E3.mQuot_self _⟩ le_rfl
  have h2 : B3.cj m (conjSubgroup V g) ≤ Subgroup.centralizer (V : Set G) := h1 ▸ (hW.trans h7.1)
  have h3 := cj_le_cj (g := m⁻¹) h2
  rwa [cj_inv_cj, cj_centralizer, cj_eq_self_of_mem_normalizer (Subgroup.inv_mem _ hmN)] at h3

theorem geo (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hr : 3 < E3.rParam V) (h9 : Concl12_5_9 T L V F) (hV2 : IsPGroup 2 V)
    {A : Subgroup G} (hAT : A ≤ T) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hA1 : E3.mQuot (conjSubgroup V g) A = 1) (hAV : ⁅V, A⁆ ≠ ⊥) :
    ∀ B : Subgroup SL5, B ≤ (autOn A V).comap (psiL F) →
      B.relIndex ((autOn A V).comap (psiL F)) ≤ 4 → ∀ x : W10,
        (∀ u ∈ B, JonesParshall.wedgeRep u x = x) →
          ∀ u ∈ (autOn A V).comap (psiL F),
            JonesParshall.wedgeRep u x ≠ x + Pi.single 0 1 := by
  intro B hBE hBi x hx u hu hux
  have hf := S125Ex.Facts125.of h1222 hH
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hf.T_le
  have hAL : autOn A V ≤ autOn L V := (A4.autOn_mono hAT).trans (S125St.autOn_T_le F)
  have hEA : ((autOn A V).comap (psiL F)).map (psiL F) = autOn A V := by
    rw [Subgroup.map_comap_eq, range_psiL, inf_of_le_right hAL]
  set BA : Subgroup ↥A := (B.map (psiL F)).comap (phiA hAN) with hBA
  have hBGA : BA.map A.subtype ≤ A := Subgroup.map_subtype_le _
  have hidx : (BA.map A.subtype).relIndex A ≤ 4 := by
    have h1 : (BA.map A.subtype).relIndex A = BA.index := by
      rw [Subgroup.relIndex]
      congr 1
      exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [h1, hBA, Subgroup.index_comap, range_phiA, ← hEA,
      Subgroup.relIndex_map_map_of_injective _ _ (psiL_injective F)]
    exact hBi
  have hVg2 : IsPGroup 2 (conjSubgroup V g) := hV2.map _
  have hAidx : A.relIndex (conjSubgroup V g) = 2 := by
    rw [E3.relIndex_eq_two_pow hVg2, hA1, pow_one]
  have hm : E3.mQuot (conjSubgroup V g) (BA.map A.subtype) ≤ 3 := by
    unfold E3.mQuot
    rw [← Subgroup.relIndex_mul_relIndex _ A _ hBGA hAg, hAidx]
    exact padicValNat_le_three (by omega)
  have hCN := centralizer_le_normalizer_conj hr (hBGA.trans hAg) hm
  set v : ↥V := F.e.symm (Multiplicative.ofAdd x) with hvdef
  have hvx : Multiplicative.toAdd (F.e v) = x := by
    rw [hvdef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hvC : (v : G) ∈ Subgroup.centralizer ((BA.map A.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨w, hw, hwb⟩ := hb
    have hfix : phiA hAN b v = v := by
      rw [← hwb, psiL_fix_iff, hvx]
      exact hx w hw
    have h1 : (b : G) * v * (b : G)⁻¹ = v := congrArg Subtype.val hfix
    change (b : G) * v = v * b
    calc (b : G) * v = ((b : G) * v * (b : G)⁻¹) * b := by group
      _ = v * b := by rw [h1]
  have hvN := hCN hvC
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ↥A, phiA hAN a₀ = psiL F u := by
    have h1 : psiL F u ∈ (phiA hAN).range := by
      rw [range_phiA]
      exact hu
    exact h1
  set v₁ : ↥V := v * (phiA hAN a₀ v)⁻¹ with hv₁def
  have hv₁G : (v₁ : G) = (v : G) * a₀ * (v : G)⁻¹ * (a₀ : G)⁻¹ := by
    change (v : G) * ((a₀ : G) * v * (a₀ : G)⁻¹)⁻¹ = _
    group
  have hv1 : Multiplicative.toAdd (F.e v₁) = Pi.single 0 1 := by
    rw [hv₁def, map_mul, map_inv, toAdd_mul, toAdd_inv, ha₀, e_psiL, hvx, hux,
      show x + -(x + Pi.single 0 1) = -(Pi.single 0 1 : W10) by abel]
    funext k
    exact ZMod.neg_eq_self_mod_two _
  have hv₁V1 : (v₁ : G) ∈ F.V1 := (mem_sub_iff F {0} v₁).2 fun k hk => by
    rw [hv1]
    exact Pi.single_eq_of_ne (by simpa using hk) _
  have hv₁1 : (v₁ : G) ≠ 1 := by
    intro h
    have h1 : v₁ = 1 := Subtype.ext h
    have h2 := congrArg (fun w => Multiplicative.toAdd (F.e w) 0) h1
    simp only [hv1, map_one, toAdd_one] at h2
    simp at h2
  have hV1g : F.V1 ≤ conjSubgroup V g := by
    rw [S125L9a.eq_zpowers (S125L9a.card_V1 F) hv₁V1 hv₁1, Subgroup.zpowers_le, hv₁G]
    have h1 : (v : G) * a₀ * (v : G)⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN _).1 (hAg a₀.2)
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hAg a₀.2))
  have hgN : g ∉ Subgroup.normalizer (V : Set G) := by
    intro hgN
    apply hAV
    have hVg : conjSubgroup V g = V := cj_eq_self_of_mem_normalizer (Subgroup.inv_mem _ hgN)
    have hAV' : A ≤ V := hVg ▸ hAg
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hf.comm.is_comm.comm ⟨z, hAV' hz⟩ ⟨y, hy⟩ |> congrArg Subtype.val)
  have h12 := (h9.2.2 g hgN hV1g).2
  apply hAV
  exact eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl hAg).trans h12.le)

theorem autOn_le_R6 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (h6 : Concl12_5_6 L V) (h7 : Concl12_5_7 T L V) (h9 : Concl12_5_9 T L V F)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 1 T)
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autOn A V ≤ S125L7m.Urad.map (psiL F) := by
  obtain ⟨hAT, g, hAg, hA1⟩ := hA
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hV : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  have hE : E6.HypE61 T (Subgroup.normalizer (L : Set G)) V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  obtain ⟨hr, -, hs⟩ := h6 hV
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hf.T_le
  have hAV' : ⁅V, A⁆ ≠ ⊥ := fun h => hAV (Subgroup.le_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h))
  have hKA : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = A := by
    have hle : A ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) := le_inf hAg hAN
    have hne : ¬ conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := fun h =>
      hAV (hAg.trans (le_centralizer_of_le_normalizer h1222 hH h7 hE.isPGroup_V h))
    have hVg2 : IsPGroup 2 (conjSubgroup V g) := hE.isPGroup_V.map _
    have h2 : A.relIndex (conjSubgroup V g) = 2 := by
      rw [E3.relIndex_eq_two_pow hVg2, hA1, pow_one]
    have hm := Subgroup.relIndex_mul_relIndex A (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))
      (conjSubgroup V g) hle inf_le_left
    rw [h2] at hm
    have hK1 : (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)).relIndex
        (conjSubgroup V g) ≠ 1 := fun h1 =>
      hne ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
    have hA1' : A.relIndex (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = 1 := by
      have hd : (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)).relIndex
          (conjSubgroup V g) ∣ 2 := Dvd.intro_left _ hm
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact absurd h hK1
      · rw [h] at hm
        omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 hA1') hle
  have hb : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      E3.sParam hV := by
    rw [hKA, hA1, hs]
    norm_num
  have hne' : ⁅V, conjSubgroup V g⁆ ≠ ⊥ := fun h =>
    hAV' (eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl hAg).trans h.le))
  have hAset := E3.e3_10_two hV hb hne'
  rw [hKA, hA1, hs] at hAset
  obtain ⟨-, -, hAel, hAfix⟩ := hAset
  have hAL : autOn A V ≤ autOn L V := (A4.autOn_mono hAT).trans (S125St.autOn_T_le F)
  set E : Subgroup SL5 := (autOn A V).comap (psiL F) with hE'
  have hEA : E.map (psiL F) = autOn A V := by
    rw [hE', Subgroup.map_comap_eq, range_psiL, inf_of_le_right hAL]
  have h1 : ∀ u ∈ E, IsUpperTri u := fun u hu => isUpperTri_of_mem F (A4.autOn_mono hAT hu)
  have h2 : ∀ u ∈ E, u * u = 1 := by
    intro u hu
    have hsq : psiL F u ^ 2 = 1 := hAel.2 (psiL F u) hu
    apply psiL_injective F
    rw [map_mul, map_one, ← pow_two]
    exact hsq
  have h4 : ∀ B : Subgroup SL5, B ≤ E → B.relIndex E ≤ 2 → ∀ x : W10,
      (∀ u ∈ B, JonesParshall.wedgeRep u x = x) → ∀ u ∈ E, JonesParshall.wedgeRep u x = x := by
    intro B hBE hBi x hx u hu
    have hBA : B.map (psiL F) ≤ autOn A V := hEA ▸ Subgroup.map_mono hBE
    have hrel : (B.map (psiL F)).relIndex (autOn A V) = B.relIndex E := by
      rw [← hEA]
      exact Subgroup.relIndex_map_map_of_injective _ _ (psiL_injective F)
    have hm : E3.mQuot (autOn A V) (B.map (psiL F)) < 3 - 1 := by
      unfold E3.mQuot
      rw [hrel]
      exact padicValNat_lt_two Subgroup.index_ne_zero_of_finite hBi
    have hfixB := hAfix (B.map (psiL F)) hBA hm
    set v : ↥V := F.e.symm (Multiplicative.ofAdd x) with hvdef
    have hvx : Multiplicative.toAdd (F.e v) = x := by
      rw [hvdef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hvB : IntMod.mk hV v ∈ fixV (V := IntMod V hV) (B.map (psiL F)) := by
      rintro _ ⟨w, hw, rfl⟩
      change psiL F w v = v
      rw [psiL_fix_iff, hvx]
      exact hx w hw
    rw [hfixB] at hvB
    have h5 : psiL F u v = v := hvB (psiL F u) hu
    rwa [psiL_fix_iff, hvx] at h5
  have hEU := S125L10m.le_urad h1 h2 h4 (geo h1222 F hH hr h9 hE.isPGroup_V hAT hAg hA1 hAV')
  rw [← hEA]
  exact Subgroup.map_mono hEU

@[expose] noncomputable def P6 (F : Frame125 T L V) : Subgroup G :=
  ((S125L7m.Urad.map (psiL F)).comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

omit [Finite G] in
theorem autOn_P6_le (F : Frame125 T L V) : autOn (P6 F) V ≤ S125L7m.Urad.map (psiL F) := by
  intro a ha
  obtain ⟨x, hxN, ⟨y, hy, hyx⟩, rfl⟩ := mem_autOn_iff_exists.mp ha
  have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) = y := Subtype.ext hyx.symm
  rw [this]
  exact hy

omit [Finite G] in
theorem P6_le_centralizer (F : Frame125 T L V) :
    P6 F ≤ Subgroup.centralizer (F.V6 : Set G) := by
  rintro _ ⟨y, ⟨u, ⟨b, hb⟩, hyu⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨w, hw, rfl⟩
  have hfix : psiL F u w = w := by
    rw [psiL_fix_iff, show u = S125L7m.Ub b from Subtype.ext hb]
    exact coordSub_le_fixSub b hw
  rw [hyu] at hfix
  have h1 : (y : G) * w * (y : G)⁻¹ = w := congrArg Subtype.val hfix
  change (w : G) * y = y * w
  calc (w : G) * y = ((y : G) * w * (y : G)⁻¹) * y := by rw [h1]
    _ = y * w := by group

theorem wClos_le_P6 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (h6 : Concl12_5_6 L V) (h7 : Concl12_5_7 T L V) (h9 : Concl12_5_9 T L V F) :
    E3.wClos V 1 T ≤ P6 F := by
  have hf := S125Ex.Facts125.of h1222 hH
  refine iSup₂_le fun A hA => ?_
  intro a ha
  have haN : a ∈ Subgroup.normalizer (V : Set G) := hf.T_le (hA.1 ha)
  refine ⟨⟨a, haN⟩, ?_, rfl⟩
  change conjAct V ⟨a, haN⟩ ∈ S125L7m.Urad.map (psiL F)
  by_cases hAV : A ≤ Subgroup.centralizer (V : Set G)
  · rw [A4.conjAct_eq_one_iff.2 (hAV ha)]
    exact Subgroup.one_mem _
  · exact autOn_le_R6 h331 h1222 h323 h3228 F hH h6 h7 h9 hA hAV
      (mem_autOn_iff_exists.mpr ⟨a, haN, ha, rfl⟩)

theorem part1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (h6 : Concl12_5_6 L V) (h7 : Concl12_5_7 T L V) (h9 : Concl12_5_9 T L V F) :
    E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G) ∨
      autOn (E3.wClos V 1 T) V = autOn (ri T L F.V6) V := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  by_cases hW : E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl hW
  right
  rw [autOn_R6_eq h1222 F hH]
  refine le_antisymm ((A4.autOn_mono (wClos_le_P6 h331 h1222 h323 h3228 F hH h6 h7 h9)).trans
    (autOn_P6_le F)) ?_
  obtain ⟨A, hA, hAV⟩ : ∃ A ∈ E3.gammaSet V 1 T, ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hW (iSup₂_le fun A hA => hc A hA)
  have hAR := autOn_le_R6 h331 h1222 h323 h3228 F hH h6 h7 h9 hA hAV
  obtain ⟨hAT, g, hAg, hA1⟩ := hA
  have hRT : ri T L F.V6 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hL6 : li L F.V6 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hOR : pCoreOf 2 (L ⊔ T) ≤ ri T L F.V6 := by
    have hp : IsPGroup 2 (pCoreOf 2 (L ⊔ T)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact LieType.BorelTits.pCoreOf_isPGroup 2 _
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hp
    · rw [pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hyp]
      exact inf_le_left.trans le_sup_right
    · exact (sup_le_sup_right hL6 T).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hf.T_le
  have hAR6 : A ≤ ri T L F.V6 := by
    intro a ha
    have h1 : conjAct V ⟨a, hAN ha⟩ ∈ autOn (ri T L F.V6) V := by
      rw [autOn_R6_eq h1222 F hH]
      exact hAR (mem_autOn_iff_exists.mpr ⟨a, hAN ha, ha, rfl⟩)
    obtain ⟨r, hrN, hrR, hra⟩ := mem_autOn_iff_exists.mp h1
    have hc : a * r⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have h2 : conjAct V (⟨a, hAN ha⟩ * ⟨r, hrN⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hra, mul_inv_cancel]
      exact A4.conjAct_eq_one_iff.1 h2
    have hO : a * r⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
      rw [pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hyp]
      exact ⟨T.mul_mem (hAT ha) (T.inv_mem (hRT hrR)), hc⟩
    have h3 := (ri T L F.V6).mul_mem (hOR hO) hrR
    rwa [inv_mul_cancel_right] at h3
  obtain ⟨b, hb0, hbA⟩ : ∃ b : Fin 4 → ZMod 2, b ≠ 0 ∧ psiL F (S125L7m.Ub b) ∈ autOn A V := by
    have hne : autOn A V ≠ ⊥ := by
      intro h
      apply hAV
      intro a ha
      have h1 : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V := mem_autOn_iff_exists.mpr ⟨a, hAN ha, ha, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact A4.conjAct_eq_one_iff.1 h1
    obtain ⟨c, hcA, hc1⟩ := (Subgroup.bot_or_exists_ne_one (autOn A V)).resolve_left hne
    obtain ⟨u, ⟨b, hb⟩, rfl⟩ := hAR hcA
    have hu : u = S125L7m.Ub b := Subtype.ext hb
    subst hu
    refine ⟨b, fun h => hc1 ?_, hcA⟩
    rw [h, show S125L7m.Ub 0 = 1 from Subtype.ext S125L7m.ub_zero, map_one]
  have hst := isStab_V6 F hf.normalizes hf.T_le
  have hM6 := (lemma12_5_2_of h1222 G T L V F hH).2.2.2.1
  rintro _ ⟨u, ⟨b', hb'⟩, rfl⟩
  have hu : u = S125L7m.Ub b' := Subtype.ext hb'
  subst hu
  by_cases hb'0 : b' = 0
  · rw [hb'0, show S125L7m.Ub 0 = 1 from Subtype.ext S125L7m.ub_zero, map_one]
    exact Subgroup.one_mem _
  set y : SL5 := S125L10m.YB b' * (S125L10m.YB b)⁻¹ with hy
  have hyU : y * S125L7m.Ub b * y⁻¹ = S125L7m.Ub b' := by
    have h1 := S125L10m.YB_conj hb0
    have h2 := S125L10m.YB_conj hb'0
    rw [hy, ← h2, ← h1]
    group
  have hyS : y ∈ stabK 4 := Subgroup.mul_mem _ (mem_stabK.2 (S125L10m.YB_stab b'))
    (Subgroup.inv_mem _ (mem_stabK.2 (S125L10m.YB_stab b)))
  have hψy : psiL F y ∈ autOn (li L F.V6) V := by
    rw [← hM6]
    exact (hst.2 (F.γ.symm y)).2 (by rw [MulEquiv.apply_symm_apply]; exact mem_stabK.1 hyS)
  obtain ⟨x, hxN, hxL6, hxy⟩ := mem_autOn_iff_exists.mp hψy
  have hxR : x ∈ Subgroup.normalizer (ri T L F.V6 : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_sup_left (a := li L F.V6) hxL6)
  have hAx : B3.cj x A ∈ E3.gammaSet V 1 T := by
    have hcj : B3.cj x (conjSubgroup V g) = conjSubgroup V (g * x⁻¹) := cj_conjugate x g V
    refine ⟨(cj_le_cj hAR6).trans ((cj_eq_self_of_mem_normalizer hxR).le.trans hRT),
      g * x⁻¹, hcj ▸ cj_le_cj hAg, ?_⟩
    rw [← hcj]
    unfold E3.mQuot
    have h1 : (B3.cj x A).relIndex (B3.cj x (conjSubgroup V g)) = A.relIndex (conjSubgroup V g) :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom) _ _
        (MulAut.conj x).injective
    rw [h1]
    exact hA1
  obtain ⟨a₀, ha₀N, ha₀A, ha₀⟩ := mem_autOn_iff_exists.mp hbA
  have hmem : psiL F (S125L7m.Ub b') ∈ autOn (B3.cj x A) V := by
    have hxa : x * a₀ * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN ha₀N) (Subgroup.inv_mem _ hxN)
    refine mem_autOn_iff_exists.mpr ⟨x * a₀ * x⁻¹, hxa, ⟨a₀, ha₀A, by
      simp [MulAut.conj_apply]⟩, ?_⟩
    have e : (⟨x * a₀ * x⁻¹, hxa⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxN⟩ * ⟨a₀, ha₀N⟩ * ⟨x, hxN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hxy, ha₀, ← map_inv, ← map_mul, ← map_mul, hyU]
  exact A4.autOn_mono (le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 1 T) => A) _ hAx le_rfl)
    hmem

theorem part2 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (h4 : Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h6 : Concl12_5_6 L V) (h7 : Concl12_5_7 T L V)
    (h9 : Concl12_5_9 T L V F) :
    Subgroup.centralizer (E3.cClos V 1 T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hW6 : E3.wClos V 1 T ≤ Subgroup.centralizer (F.V6 : Set G) :=
    (wClos_le_P6 h331 h1222 h323 h3228 F hH h6 h7 h9).trans (P6_le_centralizer F)
  have hV6 : F.V6 ≤ E3.cClos V 1 T :=
    le_inf ((Subgroup.map_subtype_le _).trans hf.le_T) (Subgroup.le_centralizer_iff.1 hW6)
  exact ((Subgroup.centralizer_le hV6).trans (Subgroup.centralizer_le_normalizer _)).trans h4

end S125L10

open S125L10

theorem lemma12_5_10_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (h4 : Lemma12_5_4six) (h6 : Lemma12_5_6) (h7 : Lemma12_5_7)
    (h9 : Lemma12_5_9) : Lemma12_5_10 := by
  intro G _ _ T L V F hH
  exact ⟨part1 h331 h1222 h323 h3228 F hH (h6 G T L V hH) (h7 G T L V hH) (h9 G T L V F hH),
    part2 h331 h1222 h323 h3228 F hH (h4 G T L V F hH) (h6 G T L V hH) (h7 G T L V hH)
      (h9 G T L V F hH)⟩


end CFSG.Quasithin.H13
