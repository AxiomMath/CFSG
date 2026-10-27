module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4DatumComplementAux
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggR4_datum_complement {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J) (hCard : Nat.card Bs = 3 ^ 5)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Γ → MulAut ↥Bs} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α)
    (hF4 : ∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i))
    (hGen : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∃ (Hb : Subgroup G) (ι' : Additive ↥Hb ≃+ ↥(Submodule.span (ZMod 3) (Set.range h)))
      (φ' : Γ → MulAut ↥Hb) (h' : Γ → ↥(Submodule.span (ZMod 3) (Set.range h)))
      (α' : Γ → Module.Dual (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range h))),
      Hb ≤ Bs ∧ Hb ⊓ Subgroup.zpowers x = ⊥ ∧ Nat.card Hb = 3 ^ 4 ∧ IsElemAbelian 3 Hb ∧
        GGExtDatum ι' C φ' h' α' ∧ ggAutomizer L Hb = Subgroup.closure (Set.range φ') := by
  obtain ⟨hp3, hBsEab, hxBs, hLx, -⟩ := hCfg.tableB_facts
  have hx1 : x ≠ 1 := hCfg.1.2.2.2.2.2.2.1.2.2.1
  have hordx : orderOf x = 3 := hCfg.orderOf_x
  set V' : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h) with hV'
  set Hb₀ : Subgroup ↥Bs := dcm_preimage ι V'
  set Hb : Subgroup G := Hb₀.map Bs.subtype
  set eH : ↥Hb₀ ≃* ↥Hb :=
    Subgroup.equivMapOfInjective Hb₀ Bs.subtype Bs.subtype_injective
  set e_cmp : Additive ↥Hb₀ ≃+ V' := dcm_preimage_equiv ι V'
  set ι' : Additive ↥Hb ≃+ V' := eH.toAdditive.symm.trans e_cmp with hι'
  set h' : Γ → V' := fun j => ⟨h j, Submodule.subset_span ⟨j, rfl⟩⟩ with hh'
  set α' : Γ → Module.Dual (ZMod 3) V' := fun i => (α i).comp V'.subtype with hα'
  have hφHmem : ∀ (i : Γ) (b : ↥Bs), b ∈ Hb₀ → (φ i) b ∈ Hb₀ := by
    intro i b hb
    rw [dcm_preimage_mem, ← ggLin_apply_ofMul (p := 3) ι (φ i) b, hD.lin i]
    exact V'.sub_mem ((dcm_preimage_mem ι V' b).mp hb)
      (V'.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  have hφH : ∀ i, φ i ∈ dcm_stab Hb₀ := by
    intro i
    change Subgroup.map (φ i : ↥Bs →* ↥Bs) Hb₀ = Hb₀
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      intro b hb
      exact hφHmem i b hb
    · exact le_of_eq (Subgroup.card_map_of_injective (φ i).injective).symm
  set φ'' : Γ → MulAut ↥Hb₀ := fun i => dcm_restrict Hb₀ ⟨φ i, hφH i⟩
  set φ' : Γ → MulAut ↥Hb := fun i => MulAut.congr eH (φ'' i) with hφ'
  set resG : ↥(dcm_stab Hb₀) →* MulAut ↥Hb :=
    (MulAut.congr eH).toMonoidHom.comp (dcm_restrict Hb₀) with hresG
  have heH_coe : ∀ b : ↥Hb₀, ((eH b : ↥Hb) : G) = (b : G) := by
    intro b
    exact Subgroup.coe_equivMapOfInjective_apply Hb₀ Bs.subtype Bs.subtype_injective b
  have heH_symm_coe : ∀ a : ↥Hb, ((eH.symm a : ↥Hb₀) : G) = (a : G) := by
    intro a
    have h := heH_coe (eH.symm a)
    rw [eH.apply_symm_apply] at h
    exact h.symm
  have hφ''_coe : ∀ (i : Γ) (b : ↥Hb₀), ((φ'' i b : ↥Hb₀) : ↥Bs) = (φ i : MulAut ↥Bs) b := by
    intro i b
    exact dcm_restrict_coe Hb₀ ⟨φ i, hφH i⟩ b
  have hφ'_coe : ∀ (i : Γ) (a : ↥Hb),
      ((φ' i a : ↥Hb) : G) = ((φ i (eH.symm a) : ↥Bs) : G) := by
    intro i a
    have h1 : (φ' i a : ↥Hb) = eH (φ'' i (eH.symm a)) := by
      simp [hφ', MulAut.congr_apply]
    rw [h1, heH_coe, hφ''_coe]
  have hres_coe : ∀ (e : ↥(dcm_stab Hb₀)) (a : ↥Hb),
      ((resG e a : ↥Hb) : G) = ((e : MulAut ↥Bs) (eH.symm a) : G) := by
    intro e a
    have h1 : resG e a = eH (dcm_restrict Hb₀ e (eH.symm a)) := by
      simp [hresG, MulAut.congr_apply]
    rw [h1, heH_coe]
    exact congrArg (fun x : ↥Bs => (x : G)) (dcm_restrict_coe Hb₀ e (eH.symm a))
  have hb_le : Hb ≤ Bs := Subgroup.map_subtype_le Hb₀
  set lift : ↥Hb → ↥Bs := fun a => ⟨(a : G), hb_le a.2⟩
  have hfixS : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    change ψ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs)
    rw [MulAction.mem_stabilizer_iff]
    obtain ⟨g, hgL, hgN, hg⟩ := hψ
    apply Subtype.ext
    change ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = x
    rw [hg]
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)]
    group
  have hfix : ∀ i : Γ, φ i ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    intro i
    have hmem : φ i ∈ ggAutomizer L Bs := by
      rw [hGen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp (hfixS hmem)
  set vx : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) with hvx
  have hα : ∀ i : Γ, α i vx = 0 := by
    intro i
    have h1 : ggLin (p := 3) ι (φ i) vx = vx := by
      rw [ggLin_apply_ofMul]
      exact congrArg (fun b : ↥Bs => ι (Additive.ofMul b)) (hfix i)
    have h2 : vx - α i vx • h i = vx := by
      rw [← hD.lin i vx]
      exact h1
    have h3 : α i vx • h i = 0 := sub_eq_self.mp h2
    exact (smul_eq_zero.mp h3).resolve_right (hD.indep.ne_zero i)
  have hvxne : vx ≠ 0 := by
    intro h0
    rw [hvx] at h0
    have h0' : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 :=
      ι.injective (by rw [h0, map_zero])
    have h1' : (⟨x, hxBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0')
    exact hx1 (Subtype.ext_iff.mp h1')
  obtain ⟨e, he⟩ := hF4
  have hvxnot : vx ∉ V' := by
    intro hvxmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hvxmem
    have hsum : ∀ i : Fin 4,
        ∑ k : Fin 4, ((C (e i) (e k) : ℤ) : ZMod 3) * c (e k) = 0 := by
      intro i
      have h1 : ∑ j : Γ, c j * ((C (e i) j : ℤ) : ZMod 3) = 0 := by
        have h2 := hα (e i)
        rw [← hc] at h2
        simpa [map_sum, map_smul, smul_eq_mul, hD.pair] using h2
      have h3 : ∑ k : Fin 4, c (e k) * ((C (e i) (e k) : ℤ) : ZMod 3) = 0 := by
        rw [← h1]
        exact Equiv.sum_comp e (fun j => c j * ((C (e i) j : ℤ) : ZMod 3))
      simpa [mul_comm] using h3
    have hd : (fun k : Fin 4 => c (e k)) = 0 := by
      rcases he with he | he
      · exact dcm_F4_mulVec_zero _ (fun i => by simpa [he i] using hsum i)
      · exact dcm_F4t_mulVec_zero _ (fun i => by simpa [he i] using hsum i)
    have hcz : c = 0 := by
      funext j
      have := congrFun hd (e.symm j)
      simpa using this
    have : vx = 0 := by
      rw [← hc, hcz]
      simp
    exact hvxne this
  have hcardz : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hordx]
  have hcardHb : Nat.card Hb = 3 ^ 4 := by
    have h1 : Nat.card Hb₀ = Nat.card V' :=
      Nat.card_congr (Additive.ofMul.trans e_cmp.toEquiv)
    have h2 : Nat.card Hb = Nat.card Hb₀ := Nat.card_congr eH.symm.toEquiv
    have h3 : Nat.card V' = 3 ^ 4 := by
      have hfininst : Module.Finite (ZMod 3) V' := by
        rw [hV']
        exact Module.Finite.span_of_finite (R := ZMod 3) (M := V) (Set.finite_range h)
      have hcardV : Nat.card V' = Nat.card (ZMod 3) ^ Module.finrank (ZMod 3) V' :=
        @Module.natCard_eq_pow_finrank (ZMod 3) V' _ _ _ hfininst
      have hfin : Module.finrank (ZMod 3) V' = Fintype.card Γ := by
        rw [hV']; exact finrank_span_eq_card hD.indep
      rw [hcardV, Nat.card_zmod, hfin, ← Fintype.card_congr e, Fintype.card_fin]
    rw [h2, h1, h3]
  have hxnotHb : x ∉ Hb := by
    intro hxh
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hxh
    refine hvxnot ?_
    have hb' : b = (⟨x, hxBs⟩ : ↥Bs) := Subtype.ext hbeq
    rw [hvx, ← hb']
    exact (dcm_preimage_mem ι V' b).mp hb
  have hdisj : Hb ⊓ Subgroup.zpowers x = ⊥ := by
    have hcard_sub : Nat.card ↥((Hb ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x)) =
        Nat.card ↥(Hb ⊓ Subgroup.zpowers x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hdiv : Nat.card ↥(Hb ⊓ Subgroup.zpowers x) ∣ 3 := by
      have h := Subgroup.card_subgroup_dvd_card
        ((Hb ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x))
      rw [hcardz] at h
      rwa [hcard_sub] at h
    have hne : Nat.card ↥(Hb ⊓ Subgroup.zpowers x) ≠ 3 := by
      intro h3
      have heq : Hb ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcardz])
      exact hxnotHb (show x ∈ Hb from (by
        have : x ∈ Hb ⊓ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers x
        exact this.1))
    have h1 : Nat.card ↥(Hb ⊓ Subgroup.zpowers x) = 1 := by
      rcases hp3.eq_one_or_self_of_dvd _ hdiv with h | h
      · exact h
      · exact absurd h hne
    exact Subgroup.card_eq_one.mp h1
  have hsup : Hb ⊔ Subgroup.zpowers x = Bs := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (Subgroup.map_subtype_le Hb₀) (Subgroup.zpowers_le.mpr hxBs)
    · rw [hCard,
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Hb
          (Subgroup.zpowers x) ?_ (disjoint_iff.mpr hdisj),
        hcardHb, hcardz]
      · norm_num
      · exact (Subgroup.zpowers_le.mpr (by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (hBsEab.comm hxBs (hb_le hy)).symm)).trans
          (Subgroup.centralizer_le_normalizer (Hb : Set G))
  have hElem : IsElemAbelian 3 Hb := hBsEab.mono hb_le
  have hnormalizer : L ⊓ Subgroup.normalizer (Hb : Set G) ≤
      L ⊓ Subgroup.normalizer (Bs : Set G) := by
    intro g hg
    obtain ⟨hgL, hgN⟩ := hg
    refine ⟨hgL, ?_⟩
    have hmapH : Subgroup.map (MulAut.conj g).toMonoidHom Hb = Hb :=
      dcm_map_conj_eq_iff.mpr hgN
    have hmapK : Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.zpowers x) =
        Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change (MulAut.conj g) x = x
      rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)]
      group
    rw [← hsup]
    exact dcm_map_conj_eq_iff.mp (by rw [Subgroup.map_sup, hmapH, hmapK])
  have hgginv : ∀ {ψ : MulAut ↥Bs}, ψ ∈ ggInduced L Bs → ψ⁻¹ ∈ ggInduced L Bs := by
    intro ψ hψ
    obtain ⟨g, hgL, hgN, hg⟩ := hψ
    refine ⟨g⁻¹, Subgroup.inv_mem _ hgL, Subgroup.inv_mem _ hgN, fun b => ?_⟩
    have happ : ψ (ψ⁻¹ b) = b := by simp
    have h := hg (ψ⁻¹ b)
    have hb : (b : G) = g * ((ψ⁻¹ b : ↥Bs) : G) * g⁻¹ := by
      rw [← h]
      exact (congrArg (fun x : ↥Bs => (x : G)) happ).symm
    rw [hb]; group
  let Ssub : Subgroup (MulAut ↥Bs) :=
    { carrier := ggInduced L Bs
      one_mem' := one_mem_ggInduced L Bs
      mul_mem' := fun ha hb => mul_mem_ggInduced ha hb
      inv_mem' := fun ha => hgginv ha }
  have hSsub_eq : Ssub = ggAutomizer L Bs := by
    rw [ggAutomizer, ← Subgroup.closure_eq Ssub]
    rfl
  have hφigg : ∀ i, φ i ∈ ggInduced L Bs := by
    intro i
    have h1 : φ i ∈ ggAutomizer L Bs := by
      rw [hGen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have h2 : φ i ∈ Ssub := by rwa [hSsub_eq]
    exact h2
  set A : Subgroup (MulAut ↥Bs) := Subgroup.closure (ggInduced L Bs) with hA
  have hrange_dcm : Subgroup.closure (Set.range φ) ≤ dcm_stab Hb₀ :=
    (Subgroup.closure_le _).mpr (fun _ he => by
      obtain ⟨i, rfl⟩ := he
      exact hφH i)
  have hAle : A ≤ dcm_stab Hb₀ := by
    rw [hA, show Subgroup.closure (ggInduced L Bs) = Subgroup.closure (Set.range φ) from hGen]
    exact hrange_dcm
  set resA : ↥A →* MulAut ↥Hb := resG.comp (Subgroup.inclusion hAle)
  have hphiA : ∀ i, φ i ∈ A := by
    intro i
    rw [hA, show Subgroup.closure (ggInduced L Bs) = Subgroup.closure (Set.range φ) from hGen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hrangeA : Subgroup.subtype A '' Set.range (fun i => (⟨φ i, hphiA i⟩ : ↥A)) =
      Set.range φ := by
    ext x; exact ⟨by rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩,
      by rintro ⟨i, rfl⟩; exact ⟨⟨φ i, hphiA i⟩, ⟨i, rfl⟩, rfl⟩⟩
  have hT : Subgroup.closure (Set.range (fun i => (⟨φ i, hphiA i⟩ : ↥A))) = ⊤ := by
    have hmapT : Subgroup.map (Subgroup.subtype A)
        (Subgroup.closure (Set.range (fun i => (⟨φ i, hphiA i⟩ : ↥A)))) = A := by
      rw [MonoidHom.map_closure, hrangeA, hA]
      exact (show Subgroup.closure (ggInduced L Bs) = Subgroup.closure (Set.range φ) from hGen).symm
    have hcomap : Subgroup.comap (Subgroup.subtype A) A = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro y; exact y.2
    rw [← Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective A)
      (Subgroup.closure (Set.range (fun i => (⟨φ i, hphiA i⟩ : ↥A)))), hmapT, hcomap]
  have hresArange : resA.range = Subgroup.closure (Set.range φ') := by
    rw [MonoidHom.range_eq_map, ← hT, MonoidHom.map_closure]
    congr 1
    ext x; exact ⟨by rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩,
      by rintro ⟨i, rfl⟩; exact ⟨⟨φ i, hphiA i⟩, ⟨i, rfl⟩, rfl⟩⟩
  have hφ'mem : ∀ i, φ' i ∈ ggInduced L Hb := by
    intro i
    obtain ⟨g, hgL, hgN, hg⟩ := hφigg i
    refine ⟨g, hgL, ?_, ?_⟩
    · apply dcm_map_conj_eq_iff.mp
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.map_le_iff_le_comap]
        intro h hh
        rw [Subgroup.mem_comap]
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hh
        change g * (b : G) * g⁻¹ ∈ Hb
        rw [← hg b]
        exact Subgroup.mem_map.mpr ⟨(φ i) b, hφHmem i b hb, rfl⟩
      · exact le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    · intro a
      rw [hφ'_coe, hg, heH_symm_coe]
  have hmem_ind : ∀ ψ ∈ ggInduced L Hb, ψ ∈ resA.range := by
    intro ψ hψ
    obtain ⟨g, hgL, hgN, hg⟩ := hψ
    have hgBsN : g ∈ Subgroup.normalizer (Bs : Set G) := (hnormalizer ⟨hgL, hgN⟩).2
    let eg : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨g, hgBsN⟩
    have heg : eg ∈ ggInduced L Bs :=
      ⟨g, hgL, hgBsN, fun b => Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨g, hgBsN⟩ b⟩
    have hegA : eg ∈ A := by
      rw [hA]
      exact Subgroup.subset_closure heg
    refine ⟨⟨eg, hegA⟩, ?_⟩
    apply MulEquiv.ext; intro a
    apply Subtype.ext
    have h1 : resA ⟨eg, hegA⟩ a = resG ⟨eg, hAle hegA⟩ a := rfl
    rw [h1, hres_coe, Subgroup.normalizerMonoidHom_apply_apply_coe, heH_symm_coe]
    exact (hg a).symm
  have hauto : ggAutomizer L Hb = Subgroup.closure (Set.range φ') := by
    rw [← hresArange]
    apply le_antisymm
    · rw [ggAutomizer, Subgroup.closure_le]
      exact hmem_ind
    · rw [hresArange, ggAutomizer]
      exact Subgroup.closure_mono (fun _ hψ => by
        obtain ⟨i, rfl⟩ := hψ
        exact hφ'mem i)
  have hmemD : ∀ i : Γ, φ' i ∈ ggInduced ⊤ Hb := by
    intro i
    obtain ⟨g, -, hgN, hg⟩ := hφ'mem i
    exact ⟨g, trivial, hgN, hg⟩
  have hι'_coe : ∀ a : Additive ↥Hb,
      ((ι' a : V') : V) = ι (Additive.ofMul (lift (Additive.toMul a))) := by
    intro a
    have hsymm : eH.toAdditive.symm a = Additive.ofMul (eH.symm (Additive.toMul a)) := rfl
    have hcoe : ((eH.symm (Additive.toMul a) : ↥Hb₀) : ↥Bs) = lift (Additive.toMul a) := by
      apply Subtype.ext
      exact heH_symm_coe (Additive.toMul a)
    rw [hι', AddEquiv.trans_apply, hsymm, dcm_preimage_equiv_coe]
    exact congrArg (fun x : ↥Bs => ι (Additive.ofMul x)) hcoe
  have hlinD : ∀ i w, ggLin (p := 3) ι' (φ' i) w = w - α' i w • h' i := by
    intro i w
    apply Subtype.ext
    have hL : ((ggLin (p := 3) ι' (φ' i) w : V') : V) = ggLin (p := 3) ι (φ i) w := by
      rw [ggLin_apply, hι'_coe, toMul_ofMul]
      have h1 : lift ((φ' i) (Additive.toMul (ι'.symm w))) =
          (φ i) (eH.symm (Additive.toMul (ι'.symm w))) := by
        apply Subtype.ext
        exact hφ'_coe i (Additive.toMul (ι'.symm w))
      rw [h1, ← ggLin_apply_ofMul (p := 3)]
      congr 1
      have hw : w = ι (Additive.ofMul (eH.symm (Additive.toMul (ι'.symm w)))) := by
        have h2 := hι'_coe (ι'.symm w)
        rw [ι'.apply_symm_apply] at h2
        have h3 : eH.symm (Additive.toMul (ι'.symm w)) = lift (Additive.toMul (ι'.symm w)) := by
          apply Subtype.ext
          exact heH_symm_coe (Additive.toMul (ι'.symm w))
        rw [h3]
        exact h2
      rw [← hw]
    have hR : ((w - α' i w • h' i : V') : V) = w - α i w • h i := by
      simp [hα', hh']
    rw [hL, hR, hD.lin i]
  refine ⟨Hb, ι', φ', h', α', hb_le, hdisj, hcardHb, hElem, ?_, hauto⟩
  refine ⟨hmemD, hlinD, ?_, ?_, hD.diag⟩
  · intro i j
    simp [hα', hh', hD.pair i j]
  · exact LinearIndependent.of_comp V'.subtype (by simpa [hh', Function.comp_def] using hD.indep)

end CFSG.StandardType

end
