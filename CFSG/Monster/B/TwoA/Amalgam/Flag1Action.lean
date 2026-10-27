module

public import CFSG.Monster.B.TwoA.Unitary.Witt
public import CFSG.Monster.B.Classical.UnitaryPanelsFrame
public import CFSG.Monster.B.TwoA.Amalgam.DataBase

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary Matrix Module
open CFSG.Monster.B.Classical.UnitarySix (bar bar_bar bar_zero bar_one mul_bar_of_ne_zero
  IsFrame herm exists_SU_lines_of_frame isIsometry_of_mem det_of_mem exists_frame_of_triple
  exists_frame_of_pair exists_frame_of_isotropic)
open CFSG.Monster.B.Classical.UnitaryPanels (exists_eq_span_singleton_of_finrank_eq_one
  sup_span_singleton_eq)

@[expose] def barPowF (ε : ZMod 2) (c : F4) : F4 := if ε = 0 then c else bar c

theorem barPowF_zero_right (ε : ZMod 2) : barPowF ε 0 = 0 := by
  unfold barPowF
  split_ifs
  · rfl
  · exact bar_zero

theorem barPowF_ne_zero (ε : ZMod 2) {c : F4} (hc : c ≠ 0) : barPowF ε c ≠ 0 := by
  unfold barPowF
  split_ifs
  · exact hc
  · exact fun h => hc (CFSG.Monster.B.Classical.UnitarySix.bar_eq_zero_iff.1 h)

theorem barPowV_add (ε : ZMod 2) (s t : V6) : barPowV ε (s + t) = barPowV ε s + barPowV ε t := by
  unfold barPowV
  split_ifs
  · rfl
  · exact barV_add s t

theorem barPowV_smul (ε : ZMod 2) (c : F4) (s : V6) :
    barPowV ε (c • s) = barPowF ε c • barPowV ε s := by
  unfold barPowV barPowF
  split_ifs
  · rfl
  · exact barV_smul c s

theorem barPowV_injective (ε : ZMod 2) : Function.Injective (barPowV ε) := by
  intro s t h
  unfold barPowV at h
  split_ifs at h
  · exact h
  · rw [← barV_barV s, h, barV_barV]

theorem hU_barPowV (ε : ZMod 2) (s t : V6) :
    hU (barPowV ε s) (barPowV ε t) = barPowF ε (hU s t) := by
  unfold barPowV barPowF
  split_ifs
  · rfl
  · exact hU_barV s t

@[expose] def semMap (g : SUh) (ε : ZMod 2) (s : V6) : V6 :=
  barPowV ε (s ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))

theorem semMap_add (g : SUh) (ε : ZMod 2) (s t : V6) :
    semMap g ε (s + t) = semMap g ε s + semMap g ε t := by
  rw [semMap, semMap, semMap, add_vecMul, barPowV_add]

theorem semMap_smul (g : SUh) (ε : ZMod 2) (c : F4) (s : V6) :
    semMap g ε (c • s) = barPowF ε c • semMap g ε s := by
  rw [semMap, semMap, smul_vecMul, barPowV_smul]

theorem semMap_injective (g : SUh) (ε : ZMod 2) : Function.Injective (semMap g ε) :=
  (barPowV_injective ε).comp (vecMul_injective_iff_isUnit.2 (Units.isUnit _))

theorem hU_semMap (g : SUh) (ε : ZMod 2) (s t : V6) :
    hU (semMap g ε s) (semMap g ε t) = barPowF ε (hU s t) := by
  rw [semMap, semMap, hU_barPowV, (mem_SUh.1 g.2).2 s t]

theorem coe_sigmaAct (S : Submodule F4 V6) (g : SUh) (ε : ZMod 2) :
    ((sigmaAct S ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ : Submodule F4 V6) : Set V6) =
      semMap g ε '' S := by
  rw [sigmaAct_mk]
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  by_cases h : ε = 0
  · rw [subBarPow, ite_eq_left h]
    simp only [semMap, barPowV, ite_eq_left h]
    exact Submodule.mem_map
  · rw [subBarPow, ite_eq_right h, mem_subBar]
    simp only [semMap, barPowV, ite_eq_right h]
    constructor
    · rintro ⟨s, hs, e⟩
      refine ⟨s, hs, ?_⟩
      change s ᵥ* _ = barV x at e
      rw [e, barV_barV]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by rw [barV_barV]; rfl⟩

theorem exists_sigma_rep (x : SigmaU6) :
    ∃ (g : SUh) (ε : ZMod 2), x = ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ := by
  obtain ⟨xl, xr⟩ := x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective xl
  exact ⟨g, Multiplicative.toAdd xr, rfl⟩

theorem mem_sigmaAct_iff {S : Submodule F4 V6} {g : SUh} {ε : ZMod 2} {v : V6} :
    v ∈ sigmaAct S ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ ↔ ∃ s ∈ S, semMap g ε s = v := by
  rw [← SetLike.mem_coe, coe_sigmaAct]
  rfl

theorem sigmaAct_sigmaAct_inv (S : Submodule F4 V6) (x : SigmaU6) :
    sigmaAct (sigmaAct S x) x⁻¹ = S := by
  rw [← sigmaAct_mul, mul_inv_cancel, sigmaAct_one]

theorem sigmaAct_inv_sigmaAct (S : Submodule F4 V6) (x : SigmaU6) :
    sigmaAct (sigmaAct S x⁻¹) x = S := by
  rw [← sigmaAct_mul, inv_mul_cancel, sigmaAct_one]

theorem sigmaAct_mono {S S' : Submodule F4 V6} (h : S ≤ S') (x : SigmaU6) :
    sigmaAct S x ≤ sigmaAct S' x := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  rw [← SetLike.coe_subset_coe, coe_sigmaAct, coe_sigmaAct]
  exact Set.image_mono h

theorem sigmaAct_le_iff {S S' : Submodule F4 V6} (x : SigmaU6) :
    sigmaAct S x ≤ sigmaAct S' x ↔ S ≤ S' := by
  refine ⟨fun h => ?_, fun h => sigmaAct_mono h x⟩
  have := sigmaAct_mono h x⁻¹
  rwa [sigmaAct_sigmaAct_inv, sigmaAct_sigmaAct_inv] at this

theorem sigmaAct_left_injective (x : SigmaU6) : Function.Injective fun S => sigmaAct S x := by
  intro S S' h
  have := congrArg (fun P => sigmaAct P x⁻¹) h
  simpa only [sigmaAct_sigmaAct_inv] using this

theorem sigmaAct_inf (S S' : Submodule F4 V6) (x : SigmaU6) :
    sigmaAct (S ⊓ S') x = sigmaAct S x ⊓ sigmaAct S' x := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  apply SetLike.coe_injective
  rw [Submodule.coe_inf, coe_sigmaAct, coe_sigmaAct, coe_sigmaAct, Submodule.coe_inf]
  exact Set.image_inter (semMap_injective g ε)

theorem natCard_sigmaAct (S : Submodule F4 V6) (x : SigmaU6) :
    Nat.card (sigmaAct S x) = Nat.card S := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  have h := Nat.card_image_of_injective (semMap_injective g ε) (S : Set V6)
  rw [← coe_sigmaAct] at h
  exact h

theorem natCard_submodule_F4 (S : Submodule F4 V6) : Nat.card S = 4 ^ finrank F4 S := by
  classical
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F4), CFSG.Fischer.F4.card]

theorem finrank_sigmaAct (S : Submodule F4 V6) (x : SigmaU6) :
    finrank F4 (sigmaAct S x) = finrank F4 S := by
  have h := natCard_sigmaAct S x
  rw [natCard_submodule_F4, natCard_submodule_F4] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h

theorem sigmaAct_isotropic {S : Submodule F4 V6} (hS : ∀ s ∈ S, ∀ t ∈ S, hU s t = 0)
    (x : SigmaU6) : ∀ s ∈ sigmaAct S x, ∀ t ∈ sigmaAct S x, hU s t = 0 := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := mem_sigmaAct_iff.1 hs
  obtain ⟨b, hb, rfl⟩ := mem_sigmaAct_iff.1 ht
  rw [hU_semMap, hS a ha b hb, barPowF_zero_right]

@[expose] def UIso (d : ℕ) (S : Submodule F4 V6) : Prop :=
  finrank F4 S = d ∧ ∀ s ∈ S, ∀ t ∈ S, hU s t = 0

theorem uIso_three_iff (S : Submodule F4 V6) : UIso 3 S ↔ IsMaxIso S := Iff.rfl

theorem UIso.sigmaAct {d : ℕ} {S : Submodule F4 V6} (h : UIso d S) (x : SigmaU6) :
    UIso d (sigmaAct S x) :=
  ⟨(finrank_sigmaAct S x).trans h.1, sigmaAct_isotropic h.2 x⟩

theorem UIso.mono {d : ℕ} {S T : Submodule F4 V6} (hT : ∀ s ∈ T, ∀ t ∈ T, hU s t = 0)
    (hST : S ≤ T) (hS : finrank F4 S = d) : UIso d S :=
  ⟨hS, fun s hs t ht => hT s (hST hs) t (hST ht)⟩

@[expose] def sigStab (S : Submodule F4 V6) : Subgroup SigmaU6 where
  carrier := {x | sigmaAct S x = S}
  mul_mem' {x y} hx hy := by
    change sigmaAct S (x * y) = S
    rw [sigmaAct_mul, show sigmaAct S x = S from hx, show sigmaAct S y = S from hy]
  one_mem' := sigmaAct_one S
  inv_mem' {x} hx := by
    change sigmaAct S x⁻¹ = S
    conv_lhs => rw [← show sigmaAct S x = S from hx]
    exact sigmaAct_sigmaAct_inv S x

theorem mem_sigStab {S : Submodule F4 V6} {x : SigmaU6} : x ∈ sigStab S ↔ sigmaAct S x = S :=
  Iff.rfl

@[expose] def suElt (g : SUh) : SigmaU6 := ⟨(g : SUh ⧸ Zh), 1⟩

theorem sigmaAct_suElt (S : Submodule F4 V6) (g : SUh) :
    sigmaAct S (suElt g) = subMul S ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
  subBarPow_zero _

theorem sigmaAct_suElt_span (X : Set V6) (g : SUh) :
    sigmaAct (Submodule.span F4 X) (suElt g) =
      Submodule.span F4 ((· ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) '' X) := by
  rw [sigmaAct_suElt, subMul_span]

theorem span_smul_one {c : F4} (hc : c ≠ 0) (x : V6) :
    Submodule.span F4 {c • x} = Submodule.span F4 {x} :=
  Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) x

theorem span_smul_two {c d : F4} (hc : c ≠ 0) (hd : d ≠ 0) (x y : V6) :
    Submodule.span F4 {c • x, d • y} = Submodule.span F4 {x, y} := by
  rw [Submodule.span_insert, Submodule.span_insert, span_smul_one hc, span_smul_one hd]

theorem span_smul_three {c d f : F4} (hc : c ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) (x y z : V6) :
    Submodule.span F4 {c • x, d • y, f • z} = Submodule.span F4 {x, y, z} := by
  rw [Submodule.span_insert, Submodule.span_insert x, span_smul_one hc, span_smul_two hd hf]

theorem lo_zero : lo 0 = 0 := rfl

theorem lo_one : lo 1 = 1 := rfl

theorem lo_two : lo 2 = 2 := rfl

theorem sigmaAct_suElt_flag {g : SUh} {v : Fin 3 → V6}
    (hg : ∀ a : Fin 3, ∃ c : F4, c ≠ 0 ∧
      e6 (lo a) ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • v a) :
    sigmaAct Rsp (suElt g) = Submodule.span F4 {v 2} ∧
      sigmaAct Hsp (suElt g) = Submodule.span F4 {v 1, v 2} ∧
      sigmaAct Tsp (suElt g) = Submodule.span F4 {v 0, v 1, v 2} := by
  obtain ⟨c₀, hc₀, h₀⟩ := hg 0
  obtain ⟨c₁, hc₁, h₁⟩ := hg 1
  obtain ⟨c₂, hc₂, h₂⟩ := hg 2
  rw [lo_zero] at h₀
  rw [lo_one] at h₁
  rw [lo_two] at h₂
  refine ⟨?_, ?_, ?_⟩
  · rw [Rsp, sigmaAct_suElt_span, Set.image_singleton, h₂, span_smul_one hc₂]
  · rw [Hsp, sigmaAct_suElt_span, Set.image_insert_eq, Set.image_singleton, h₁, h₂,
      span_smul_two hc₁ hc₂]
  · rw [Tsp, sigmaAct_suElt_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      h₀, h₁, h₂, span_smul_three hc₀ hc₁ hc₂]

theorem e6_ne_zero (k : Fin 6) : e6 k ≠ 0 := by
  intro h
  have := congrFun h k
  simp [e6] at this

theorem Tsp_eq_plane : Tsp = plane 0 := by
  rw [Tsp, plane]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, planeRow_zero 0⟩
    · exact ⟨1, planeRow_zero 1⟩
    · exact ⟨2, planeRow_zero 2⟩
  · rintro ⟨a, rfl⟩
    rw [planeRow_zero]
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem isMaxIso_Tsp :
    IsMaxIso Tsp := Tsp_eq_plane ▸ isMaxIso_plane 0

theorem Rsp_le_Hsp : Rsp ≤ Hsp :=
  Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))

theorem Hsp_le_Tsp : Hsp ≤ Tsp := Submodule.span_mono (Set.subset_insert _ _)

theorem uIso_Tsp : UIso 3 Tsp := isMaxIso_Tsp

theorem finrank_Rsp : finrank F4 Rsp = 1 := finrank_span_singleton (e6_ne_zero 2)

theorem linearIndependent_e6_pair : LinearIndependent F4 ![e6 1, e6 2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [e6] at h1 h2
  exact ⟨h1, h2⟩

theorem range_pair (x y : V6) : Set.range ![x, y] = {x, y} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

theorem range_triple (x y z : V6) : Set.range ![x, y, z] = {x, y, z} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union, Set.singleton_union]

theorem finrank_Hsp : finrank F4 Hsp = 2 := by
  have h := finrank_span_eq_card linearIndependent_e6_pair
  rw [range_pair, Fintype.card_fin] at h
  exact h

theorem uIso_Hsp :
    UIso 2 Hsp := UIso.mono isMaxIso_Tsp.2 Hsp_le_Tsp finrank_Hsp

theorem uIso_Rsp :
    UIso 1 Rsp := UIso.mono isMaxIso_Tsp.2 (Rsp_le_Hsp.trans Hsp_le_Tsp) finrank_Rsp

theorem exists_SUh_of_frame {e : Fin 6 → V6} (he : IsFrame e) :
    ∃ g : SUh, ∀ a : Fin 3, ∃ c : F4, c ≠ 0 ∧
      e6 (lo a) ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • swV (e (lo a)) := by
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he
  set G : Matrix (Fin 6) (Fin 6) F4 := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hdet : (rowConj G).det = 1 := by rw [det_rowConj]; exact det_of_mem g
  have hA : GeneralLinearGroup.mkOfDetNeZero (rowConj G) (by rw [hdet]; exact one_ne_zero) ∈
      SUh := by
    refine ⟨hdet, fun s t => ?_⟩
    change hU (s ᵥ* rowConj G) (t ᵥ* rowConj G) = hU s t
    rw [vecMul_rowConj, vecMul_rowConj, hU_swV, isIsometry_of_mem g, herm_swV]
  refine ⟨⟨_, hA⟩, fun a => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hg (lo a)
  refine ⟨c, hc0, ?_⟩
  change e6 (lo a) ᵥ* rowConj G = c • swV (e (lo a))
  rw [e6, vecMul_rowConj, swV_single_lo, hc]
  rfl

theorem isFrame_comp {e : Fin 6 → V6} (he : IsFrame e) (τ : Fin 6 → Fin 6)
    (hτ : ∀ i j : Fin 6, τ j = Fin.rev (τ i) ↔ j = Fin.rev i) : IsFrame fun i => e (τ i) := by
  intro i j
  rw [he]
  simp only [hτ]

theorem exists_SUh_triple {v : Fin 3 → V6} (hli : LinearIndependent F4 v)
    (hiso : ∀ a b, hU (v a) (v b) = 0) :
    ∃ g : SUh, ∀ a : Fin 3, ∃ c : F4, c ≠ 0 ∧
      e6 (lo a) ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • v a := by
  have hiso' : ∀ a b, herm (swV (v a)) (swV (v b)) = 0 := fun a b => by
    rw [herm_swV]
    exact hiso a b
  have hli' : LinearIndependent F4 ![swV (v 0), swV (v 1), swV (v 2)] := by
    have h1 : LinearIndependent F4 (fun a => swLin (v a)) := hli.map' swLin.toLinearMap
      (LinearMap.ker_eq_bot.2 swLin.injective)
    have h2 : ![swV (v 0), swV (v 1), swV (v 2)] = fun a => swLin (v a) := by
      funext a
      fin_cases a <;> rfl
    rw [h2]
    exact h1
  obtain ⟨e, he, e0, e1, e2⟩ := exists_frame_of_triple hli' (hiso' 0 0) (hiso' 0 1)
    (hiso' 0 2) (hiso' 1 1) (hiso' 1 2) (hiso' 2 2)
  obtain ⟨g, hg⟩ := exists_SUh_of_frame he
  refine ⟨g, fun a => ?_⟩
  obtain ⟨c, hc0, hc⟩ := hg a
  refine ⟨c, hc0, ?_⟩
  have hea : e (lo a) = swV (v a) := by
    fin_cases a
    · exact e0
    · exact e1
    · exact e2
  rw [hc, hea, swV_swV]

theorem lt_of_finrank {S S' : Submodule F4 V6} (h : S ≤ S') (hd : finrank F4 S < finrank F4 S') :
    S < S' :=
  lt_of_le_of_ne h fun e => by rw [e] at hd; exact lt_irrefl _ hd

theorem span_three_eq {X Y : Submodule F4 V6} {v₀ v₁ v₂ : V6} (hY : Y = Submodule.span F4 {v₁, v₂})
    (hXY : Y ≤ X) (hd : finrank F4 X = finrank F4 Y + 1) (h₀ : v₀ ∈ X) (h₀' : v₀ ∉ Y) :
    X = Submodule.span F4 {v₀, v₁, v₂} := by
  rw [Submodule.span_insert, sup_comm, ← hY]
  exact (sup_span_singleton_eq hXY hd h₀ h₀').symm

theorem exists_SUh_flag {R H T : Submodule F4 V6} (hR : UIso 1 R) (hH : UIso 2 H)
    (hT : UIso 3 T) (hRH : R ≤ H) (hHT : H ≤ T) :
    ∃ g : SUh, sigmaAct Rsp (suElt g) = R ∧ sigmaAct Hsp (suElt g) = H ∧
      sigmaAct Tsp (suElt g) = T := by
  obtain ⟨v₂, hv₂0, hRv⟩ := exists_eq_span_singleton_of_finrank_eq_one hR.1
  obtain ⟨v₁, hv₁H, hv₁R⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_finrank hRH (by rw [hR.1, hH.1]; omega))
  obtain ⟨v₀, hv₀T, hv₀H⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_finrank hHT (by rw [hH.1, hT.1]; omega))
  have hHv : H = Submodule.span F4 {v₁, v₂} := by
    rw [Submodule.span_insert, sup_comm, ← hRv]
    exact (sup_span_singleton_eq hRH (by rw [hR.1, hH.1]) hv₁H hv₁R).symm
  have hTv : T = Submodule.span F4 {v₀, v₁, v₂} :=
    span_three_eq hHv hHT (by rw [hH.1, hT.1]) hv₀T hv₀H
  have hli : LinearIndependent F4 ![v₀, v₁, v₂] := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, range_triple, Set.finrank,
      ← hTv, hT.1]
  have hv₂R : v₂ ∈ R := hRv ▸ Submodule.mem_span_singleton_self v₂
  have hmem : ∀ a, ![v₀, v₁, v₂] a ∈ T := by
    intro a
    fin_cases a
    · exact hv₀T
    · exact hHT hv₁H
    · exact hHT (hRH hv₂R)
  obtain ⟨g, hg⟩ := exists_SUh_triple hli fun a b => hT.2 _ (hmem a) _ (hmem b)
  obtain ⟨e1, e2, e3⟩ := sigmaAct_suElt_flag hg
  exact ⟨g, e1.trans hRv.symm, e2.trans hHv.symm, e3.trans hTv.symm⟩

theorem exists_flag_of_three {T : Submodule F4 V6} (hT : UIso 3 T) :
    ∃ R H : Submodule F4 V6, UIso 1 R ∧ UIso 2 H ∧ R ≤ H ∧ H ≤ T := by
  obtain ⟨g, hg⟩ := exists_SUh_plane0 hT
  have hT' : sigmaAct Tsp (suElt g) = T := by rw [sigmaAct_suElt, Tsp_eq_plane, hg]
  refine ⟨sigmaAct Rsp (suElt g), sigmaAct Hsp (suElt g), uIso_Rsp.sigmaAct _,
    uIso_Hsp.sigmaAct _, sigmaAct_mono Rsp_le_Hsp _, ?_⟩
  rw [← hT']
  exact sigmaAct_mono Hsp_le_Tsp _

theorem exists_one_le {H : Submodule F4 V6} (hH : 0 < finrank F4 H) :
    ∃ v : V6, v ≠ 0 ∧ v ∈ H ∧ finrank F4 (Submodule.span F4 {v}) = 1 := by
  have hne : H ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hH
    exact lt_irrefl 0 hH
  obtain ⟨v, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, hv.2, hv.1, finrank_span_singleton hv.2⟩

theorem exists_pair_of_two {H : Submodule F4 V6} (hH : finrank F4 H = 2) :
    ∃ v w : V6, H = Submodule.span F4 {v, w} ∧ LinearIndependent F4 ![v, w] := by
  obtain ⟨w, hw0, hwH, hw1⟩ := exists_one_le (by rw [hH]; norm_num)
  have hle : Submodule.span F4 {w} ≤ H := (Submodule.span_singleton_le_iff_mem _ _).2 hwH
  obtain ⟨v, hvH, hvw⟩ := IsConcreteLE.exists_of_lt (lt_of_finrank hle (by rw [hw1, hH]; norm_num))
  have hHv : H = Submodule.span F4 {v, w} := by
    rw [Submodule.span_insert, sup_comm]
    exact (sup_span_singleton_eq hle (by rw [hw1, hH]) hvH hvw).symm
  refine ⟨v, w, hHv, ?_⟩
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, range_pair, Set.finrank,
    ← hHv, hH]

theorem exists_flag_of_two {H : Submodule F4 V6} (hH : UIso 2 H) :
    ∃ R T : Submodule F4 V6, UIso 1 R ∧ UIso 3 T ∧ R ≤ H ∧ H ≤ T := by
  obtain ⟨v, w, hHvw, hli⟩ := exists_pair_of_two hH.1
  have hvH : v ∈ H := hHvw ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hwH : w ∈ H := hHvw ▸ Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hli' : LinearIndependent F4 ![swV v, swV w] := by
    have h1 : LinearIndependent F4 (fun a => swLin (![v, w] a)) := hli.map' swLin.toLinearMap
      (LinearMap.ker_eq_bot.2 swLin.injective)
    have h2 : ![swV v, swV w] = fun a => swLin (![v, w] a) := by
      funext a
      fin_cases a <;> rfl
    rw [h2]
    exact h1
  have hiso : ∀ x ∈ H, ∀ y ∈ H, herm (swV x) (swV y) = 0 := fun x hx y hy => by
    rw [herm_swV]
    exact hH.2 x hx y hy
  obtain ⟨e, he, e0, e1⟩ := exists_frame_of_pair hli' (hiso v hvH v hvH) (hiso w hwH w hwH)
    (hiso v hvH w hwH)
  have hf := isFrame_comp he ![2, 0, 1, 4, 5, 3] (by decide)
  obtain ⟨g, hg⟩ := exists_SUh_of_frame hf
  have hg' : ∀ a : Fin 3, ∃ c : F4, c ≠ 0 ∧
      e6 (lo a) ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • ![swV (e 2), v, w] a := by
    intro a
    obtain ⟨c, hc0, hc⟩ := hg a
    refine ⟨c, hc0, ?_⟩
    rw [hc]
    fin_cases a
    · rfl
    · change c • swV (e 0) = c • v
      rw [e0, swV_swV]
    · change c • swV (e 1) = c • w
      rw [e1, swV_swV]
  obtain ⟨-, hH', -⟩ := sigmaAct_suElt_flag hg'
  have hH'' : sigmaAct Hsp (suElt g) = H := hH'.trans hHvw.symm
  refine ⟨sigmaAct Rsp (suElt g), sigmaAct Tsp (suElt g), uIso_Rsp.sigmaAct _,
    uIso_Tsp.sigmaAct _, ?_, ?_⟩
  · rw [← hH'']
    exact sigmaAct_mono Rsp_le_Hsp _
  · rw [← hH'']
    exact sigmaAct_mono Hsp_le_Tsp _

theorem exists_flag_of_one {R : Submodule F4 V6} (hR : UIso 1 R) :
    ∃ H T : Submodule F4 V6, UIso 2 H ∧ UIso 3 T ∧ R ≤ H ∧ H ≤ T := by
  obtain ⟨v, hv0, hRv⟩ := exists_eq_span_singleton_of_finrank_eq_one hR.1
  have hvR : v ∈ R := hRv ▸ Submodule.mem_span_singleton_self v
  have hsw0 : swV v ≠ 0 := fun h => hv0 (by rw [← swV_swV v, h]; rfl)
  have hiso : herm (swV v) (swV v) = 0 := by
    rw [herm_swV]
    exact hR.2 v hvR v hvR
  obtain ⟨e, he, e0⟩ := exists_frame_of_isotropic hsw0 hiso
  have hf := isFrame_comp he ![1, 2, 0, 5, 3, 4] (by decide)
  obtain ⟨g, hg⟩ := exists_SUh_of_frame hf
  have hg' : ∀ a : Fin 3, ∃ c : F4, c ≠ 0 ∧
      e6 (lo a) ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        c • ![swV (e 1), swV (e 2), v] a := by
    intro a
    obtain ⟨c, hc0, hc⟩ := hg a
    refine ⟨c, hc0, ?_⟩
    rw [hc]
    fin_cases a
    · rfl
    · rfl
    · change c • swV (e 0) = c • v
      rw [e0, swV_swV]
  obtain ⟨hR', -, -⟩ := sigmaAct_suElt_flag hg'
  have hR'' : sigmaAct Rsp (suElt g) = R := hR'.trans hRv.symm
  refine ⟨sigmaAct Hsp (suElt g), sigmaAct Tsp (suElt g), uIso_Hsp.sigmaAct _,
    uIso_Tsp.sigmaAct _, ?_, sigmaAct_mono Hsp_le_Tsp _⟩
  rw [← hR'']
  exact sigmaAct_mono Rsp_le_Hsp _

theorem exists_flag_of_one_three {R T : Submodule F4 V6} (hR : UIso 1 R) (hT : UIso 3 T)
    (hRT : R ≤ T) : ∃ H : Submodule F4 V6, UIso 2 H ∧ R ≤ H ∧ H ≤ T := by
  obtain ⟨v, hv0, hRv⟩ := exists_eq_span_singleton_of_finrank_eq_one hR.1
  obtain ⟨w, hwT, hwR⟩ := IsConcreteLE.exists_of_lt (lt_of_finrank hRT (by rw [hR.1, hT.1]; omega))
  have hvT : v ∈ T := hRT (hRv ▸ Submodule.mem_span_singleton_self v)
  have hli : LinearIndependent F4 ![v, w] := by
    rw [LinearIndependent.pair_iff' hv0]
    intro a ha
    apply hwR
    rw [hRv, ← ha]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hd : finrank F4 (Submodule.span F4 {v, w}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [range_pair, Fintype.card_fin] at h
    exact h
  have hle : Submodule.span F4 {v, w} ≤ T := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hvT
    · exact hwT
  refine ⟨Submodule.span F4 {v, w}, UIso.mono hT.2 hle hd, ?_, hle⟩
  rw [hRv]
  exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))

theorem exists_one_le_two {H : Submodule F4 V6} (hH : UIso 2 H) :
    ∃ R : Submodule F4 V6, UIso 1 R ∧ R ≤ H := by
  obtain ⟨v, -, hvH, hv1⟩ := exists_one_le (by rw [hH.1]; norm_num)
  have hle : Submodule.span F4 {v} ≤ H := (Submodule.span_singleton_le_iff_mem _ _).2 hvH
  exact ⟨_, UIso.mono hH.2 hle hv1, hle⟩

end CFSG.Monster.B.TwoA.Amalgam
