module

public import CFSG.Quasithin.Vol2.Ch12Sec6L28b
public import CFSG.Quasithin.Vol2.Ch12Sec6L23a
public import CFSG.Quasithin.Vol2.Ch12Sec6L24d
public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.EmptyFaithful.S153DGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126
  S126F S126L19 S126L19a Equiv
open scoped IsMulCommutative commutatorElement

namespace S126D29

@[expose] def xA (i : Fin 8) : ZMod 2 := if i.val < 4 then 0 else 1

theorem toAdd_iota_e0123 : Multiplicative.toAdd (iota e0123) = xA := by
  funext i
  change Multiplicative.toAdd (nrm (eset {0, 1, 2, 3})) i = xA i
  rw [nrm_apply]
  fin_cases i <;> decide

theorem zmod2_eq_add {a b c : ZMod 2} (h : a + b = c) : a = b + c := by
  revert a b c
  decide

theorem zmod2_four (a b : ZMod 2) : a + (b + (a + b)) = 0 := by
  revert a b
  decide

theorem top_perfect {X : Type*} [Group X] {Q : Subgroup X} (hQ : ⁅Q, Q⁆ = Q) :
    ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ = (⊤ : Subgroup ↥Q) := by
  have h := S126T2.perfect_subgroupOf hQ (le_refl Q)
  rwa [Subgroup.subgroupOf_self] at h

theorem card_le_four (p : Fin 8 → Prop) [DecidablePred p] (h : (Finset.univ.filter p).card ≤ 4) :
    Nat.card {i : Fin 8 // p i} ≤ 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem eq_bot_of_perfect {Q : Subgroup (Perm (Fin 8))} (hQ : ⁅Q, Q⁆ = Q)
    (hfix : ∀ σ ∈ Q, dAct σ e0123 = e0123) : Q = ⊥ := by
  have hB : ∀ σ ∈ Q, ∀ i, xA (σ i) + xA (σ 0) = xA i := by
    intro σ hσ i
    have h := cond_of_fix (hfix _ (Q.inv_mem hσ)) i
    rwa [inv_inv, toAdd_iota_e0123] at h
  have hadd : ∀ σ ∈ Q, ∀ τ : Perm (Fin 8), xA ((σ * τ) 0) = xA (σ 0) + xA (τ 0) := fun σ hσ τ =>
    zmod2_eq_add (hB σ hσ (τ 0))
  have hx0 : xA 0 = 0 := rfl
  have hinv : ∀ σ ∈ Q, xA (σ⁻¹ 0) = xA (σ 0) := by
    intro σ hσ
    have h := hadd σ hσ σ⁻¹
    rw [mul_inv_cancel, Perm.one_apply, hx0] at h
    have h' := zmod2_eq_add h.symm
    rw [add_zero] at h'
    exact h'.symm
  let S : Subgroup (Perm (Fin 8)) :=
    { carrier := {σ | σ ∈ Q ∧ xA (σ 0) = 0}
      one_mem' := ⟨Q.one_mem, hx0⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨Q.mul_mem ha.1 hb.1, by rw [hadd a ha.1, ha.2, hb.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [hinv a ha.1, ha.2]⟩ }
  have hQS : Q ≤ S := by
    rw [← hQ]
    refine Subgroup.commutator_le.2 fun σ hσ τ hτ => ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hσ hτ)
      (Q.inv_mem hσ)) (Q.inv_mem hτ), ?_⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc, hadd σ hσ, hadd τ hτ,
      hadd σ⁻¹ (Q.inv_mem hσ), hinv σ hσ, hinv τ hτ]
    exact zmod2_four _ _
  have hpres : ∀ σ ∈ Q, ∀ i, xA (σ i) = xA i := fun σ hσ i => by
    have h := hB σ hσ i
    rwa [(hQS hσ).2, add_zero] at h
  let ρ : ∀ c : ZMod 2, ↥Q →* Perm {i : Fin 8 // xA i = c} := fun c =>
    { toFun := fun σ => (σ : Perm (Fin 8)).subtypePerm fun i => by rw [hpres σ σ.2 i]
      map_one' := by
        ext
        rfl
      map_mul' := fun _ _ => by
        ext
        rfl }
  have hρ : ∀ c : ZMod 2, ∀ σ : ↥Q, ρ c σ = 1 := by
    intro c σ
    have : Group.IsSolvable (Perm {i : Fin 8 // xA i = c}) :=
      Perm.isSolvable (card_le_four _ (by revert c; decide))
    have h := S126T2.map_eq_bot_of_perfect (top_perfect hQ) (ρ c) inferInstance
    rw [Subgroup.map_eq_bot_iff] at h
    exact h (Subgroup.mem_top σ)
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext i
  have h := congrArg (fun π : Perm {j : Fin 8 // xA j = xA i} => (π ⟨i, rfl⟩ : Fin 8))
    (hρ (xA i) ⟨σ, hσ⟩)
  exact congrArg Fin.val h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem le_centralizer_V (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPM : P ≤ Subgroup.normalizer (L : Set G))
    (hPz : P ≤ Subgroup.centralizer (F.V1 : Set G)) : P ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨zv, hzv⟩ := F.β_surj e0123
  have hz1 : (zv : G) ∈ F.V1 := (S126L24.mem_preV zv.2).2 (hzv ▸ e0123_mem_W1)
  have hzne : (zv : G) ≠ 1 := fun h => e0123_ne_one (by
    rw [← hzv, show zv = 1 from Subtype.ext h, map_one])
  have hcz : ∀ p ∈ P, p * zv = zv * p := fun p hp =>
    (Subgroup.mem_centralizer_iff.1 (hPz hp) _ hz1).symm
  obtain ⟨-, -, hTI, -⟩ := S126L20.facts h1222 hH
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := fun p hp =>
    S126N.mem_normalizer_of_TI hTI zv.2 hzne (hPM hp) (hcz p hp)
  set MV := hH.hyp.MV with hMVdef
  have hMVN : MV ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hPMV : P ≤ MV := le_inf hPM hPV
  set e := S126L28.betaEquiv F hZ with he
  have hA := S126L28.mvbar_act F hH hZ
  let ψ : ↥MV →* ↥hH.hyp.MVbar := (A4.actionOn V MV hMVN).codRestrict hH.hyp.MVbar
    fun x => (A4.mem_autOn_iff hMVN).2 ⟨x, rfl⟩
  let Φ : ↥MV →* Perm (Fin 8) := (S126L28.psiP e hA).comp ψ
  have hQ := S126T2.perfect_subgroupOf hP hPMV
  have hbot : (P.subgroupOf MV).map Φ = ⊥ := by
    refine eq_bot_of_perfect (by rw [← Subgroup.map_commutator, hQ]) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h := S126L28.psiP_spec e hA (ψ x) zv
    have hfix : ((ψ x : MulAut ↥V) zv) = zv := by
      apply Subtype.ext
      change (x : G) * zv * (x : G)⁻¹ = zv
      rw [hcz x (Subgroup.mem_subgroupOf.1 hx), mul_inv_cancel_right]
    rw [hfix] at h
    have he' : e zv = e0123 := hzv
    rw [he'] at h
    exact h.symm
  intro p hp
  have hpx : (⟨p, hPMV hp⟩ : ↥MV) ∈ P.subgroupOf MV := hp
  have h1 : Φ ⟨p, hPMV hp⟩ = 1 := by
    have := Subgroup.mem_map_of_mem Φ hpx
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have h2 : ψ ⟨p, hPMV hp⟩ = 1 := S126L28.psiP_injective e hA (h1.trans (map_one _).symm)
  have h3 : A4.actionOn V MV hMVN ⟨p, hPMV hp⟩ = 1 := congrArg Subtype.val h2
  exact (A4.actionOn_eq_one_iff hMVN _).1 h3

theorem L_le_normalizer (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPM : P ≤ Subgroup.normalizer (L : Set G)) (hPV : P ≤ Subgroup.centralizer (V : Set G))
    (hTP : T ≤ Subgroup.normalizer (P : Set G)) : L ≤ Subgroup.normalizer (P : Set G) := by
  have hyp := hH.hyp
  obtain ⟨-, hTV, -, -, -⟩ := S126L23a.basics h1222 F hH
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normalizes
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  set R := pCoreOf 2 (L ⊔ T) with hRdef
  have hCLV : L ⊓ Subgroup.centralizer (V : Set G) ≤ R :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left)
      (B2F.le_normalizer_inf hXL (B2F.le_normalizer_centralizer hXV)) (S126T2.isPGroup_CL h1222 hH)
  have hVcl : conjClosure V T = V :=
    le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (hTV ht) _).mp hz)
      (le_conjClosure V T)
  obtain ⟨-, -, hO⟩ := h3228 G T L V hyp.fsu
  rw [hyp.conjClosure_eq, hVcl] at hO
  have hRT : R ≤ T := by
    rw [hRdef, hO]
    exact inf_le_left
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hRN : L ⊔ T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
  have hcomm : ∀ l ∈ L, ∀ p ∈ P, l * p * l⁻¹ * p⁻¹ ∈ R := by
    intro l hl p hp
    refine hCLV ⟨?_, ?_⟩
    · have h1 : p * l⁻¹ * p⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hPM hp) _).1 (L.inv_mem hl)
      have h2 := L.mul_mem hl h1
      rwa [show l * (p * l⁻¹ * p⁻¹) = l * p * l⁻¹ * p⁻¹ by group] at h2
    · have h1 : l * p * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.1 (B2F.le_normalizer_centralizer hLV hl) p).1 (hPV hp)
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hPV hp))
  have hPR : perfectCore (P ⊔ R) = P :=
    S126T2.perfectCore_sup_eq hP (hRT.trans hTP) hR2
  intro l hl
  have hmap : (P ⊔ R).map (MulAut.conj l) ≤ P ⊔ R := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      have e : (MulAut.conj l : G →* G) p = (l * p * l⁻¹ * p⁻¹) * p := by
        rw [MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm l hl p hp)) (Subgroup.mem_sup_left hp)
    · rw [(Subgroup.mem_normalizer_iff_map_conj_eq.1 (hRN (Subgroup.mem_sup_left hl)))]
      exact le_sup_right
  have hlN : l ∈ Subgroup.normalizer ((P ⊔ R : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (fun a b h => (MulAut.conj l).injective h)])
  have := normalizer_le_normalizer_perfectCore (P ⊔ R) hlN
  rwa [hPR] at this

theorem pCoreOf_ne_bot_of_normal {H X : Subgroup G} (hF : CharTwo H) (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G)) (hX1 : X ≠ ⊥) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have h1 : X ⊓ pCoreOf 2 H ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hQ2.to_le inf_le_right)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hQn (hXH hg)⟩
  rw [hbot, le_bot_iff] at h1
  have hXQ : X ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hqx : q * x * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXn (pCoreOf_le 2 H hq)) x).mp hx
    have hxq : x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hXH hx)) q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
    have hcomm : q * x * q⁻¹ * x⁻¹ ∈ X ⊓ pCoreOf 2 H := by
      refine ⟨X.mul_mem hqx (X.inv_mem hx), ?_⟩
      have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 H).mul_mem hq hxq
    rw [h1, Subgroup.mem_bot] at hcomm
    have h2 := mul_inv_eq_one.mp hcomm
    calc q * x = (q * x * q⁻¹) * q := by group
      _ = x * q := by rw [h2]
  have hXle : X ≤ X ⊓ pCoreOf 2 H := le_inf le_rfl fun x hx => hF ⟨hXH hx, hXQ hx⟩
  exact hX1 (le_bot_iff.1 (h1 ▸ hXle))

omit [IsMulCommutative ↥V] in
theorem normalizer_le_M (h331 : Stmt3_3_1) (hH : Hyp126 G T L V) {H P : Subgroup G}
    (hTH : T ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥) (hPH : P ≤ H)
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hP1 : P ≠ ⊥)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hyp.sylow.1, fun h => hyp.sylow.2 (by
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e] at h)⟩
  have hF : CharTwo H := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hyp.qtke.2.1 hTs hTH hO2
  have hW1 := pCoreOf_ne_bot_of_normal hF hPH hHP hP1
  have hNW : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 P
  obtain ⟨⟨-, -, huniq⟩, -, -⟩ := S126L23a.stmt331 h331 hH
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 P, hW1, pCoreOf_isPGroup 2 P, rfl⟩ : IsTwoLocal _)
  have hLT : L ⊔ T ≤ M' := (sup_le hLP (hTH.trans hHP)).trans (hNW.trans hle)
  exact hNW.trans (hle.trans (huniq M' hM' hLT).le)

theorem not_perfectCore_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {H : Subgroup G} (hTH : T ≤ H) (hO2 : pCoreOf 2 H ≠ ⊥)
    (hHC : H ≤ Subgroup.centralizer (F.V1 : Set G))
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) (hns : ¬ Group.IsSolvable ↥H) :
    ¬ perfectCore H ≤ Subgroup.normalizer (L : Set G) := by
  intro hPM
  have hPP := perfectCore_perfect H
  have hP1 : perfectCore H ≠ ⊥ := fun h => hns ((isSolvable_iff_perfectCore_eq_bot H).2 h)
  have hPV := le_centralizer_V h1222 F hH hZ hPP hPM ((perfectCore_le H).trans hHC)
  have hHP : H ≤ Subgroup.normalizer (perfectCore H : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H)
  have hLP := L_le_normalizer h1222 h3228 F hH hPP hPM hPV (hTH.trans hHP)
  exact hHM (hHP.trans (normalizer_le_M h331 hH hTH hO2 (perfectCore_le H) hHP hP1 hLP))

omit [Finite G] [IsMulCommutative ↥V] in
theorem oTwoUpper_L₁Of (L V₁ : Subgroup G) : oTwoUpper (L₁Of L V₁) = L₁Of L V₁ := by
  rw [L₁Of, oTwoRes_eq_oTwoUpper]
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).2 fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

end S126D29

theorem display12_6_29_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h1221 : Lemma12_6_21) (h1229 : Lemma12_6_29) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Display12_6_29 := by
  intro G _ _ T L V _ F hH hZ
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hcard : Nat.card F.V1 = 2 := (S126L23d.part2 h1222 F hH hZ).2
  have hNC := normalizer_eq_centralizer_of_card_eq_two hcard
  have hG1 := S126L24.inHz_G1 h1222 h1221 F hH hZ
  rw [hNC] at hG1
  refine ⟨hG1, fun H hHz => ?_⟩
  obtain ⟨⟨hLTH, hO2⟩, hHM, hHC⟩ := hHz
  have hTH : T ≤ H := le_sup_right.trans hLTH
  have hL1H : L₁Of L F.V1 ≤ H := le_sup_left.trans hLTH
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    hHM (h1229 G T L V F hH hZ H ⟨hTH, hO2⟩ (Or.inr hs))
  have hPM := S126D29.not_perfectCore_le h331 h1222 h3228 F hH hZ hTH hO2 hHC hHM hns
  obtain ⟨K, hK, hKM⟩ : ∃ K ∈ cComp H, ¬ K ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hPM
    rw [← Vol2Native.lemma_1_2_1_one hloc h39 hO2]
    exact sSup_le hcon
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1K : L₁Of L F.V1 ≤ Subgroup.normalizer (K : Set G) :=
    S153D.le_normalizer_of_oTwoUpper_eq hKH hL1H (S126D29.oTwoUpper_L₁Of L F.V1)
      ((Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK).imp id fun h => h.1)
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_le ⟨le_top, hyp.sylow.1, fun h => hyp.sylow.2 (by
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e] at h)⟩ hTH
  have hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hO2 hTs hK
  have hK0H : conjClosure K T ≤ H :=
    conjClosure_le fun t ht k hk => H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
  set X := conjClosure K T ⊔ (L₁Of L F.V1 ⊔ T) with hXdef
  have hXH : X ≤ H := sup_le hK0H hLTH
  obtain ⟨hVT, -, -, -, -⟩ := S126L23a.basics h1222 F hH
  have hV1T : F.V1 ≤ T := (Subgroup.map_subtype_le _).trans hVT
  have hV1X : F.V1 ≤ X := hV1T.trans (le_sup_right.trans le_sup_right)
  have hO2X : pCoreOf 2 X ≠ ⊥ := by
    intro hbot
    have hle : F.V1 ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hV1X
      ((hXH.trans hHC).trans (Subgroup.centralizer_le_normalizer _)) (hyp.sylow.1.to_le hV1T)
    rw [hbot, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hcard
    omega
  exact ⟨K, hK, hKM, hL1K, hK0, ⟨le_sup_right, hO2X⟩,
    fun h => hKM ((le_conjClosure K T).trans (le_sup_left.trans h)), hXH.trans hHC⟩

end CFSG.Quasithin.H13
