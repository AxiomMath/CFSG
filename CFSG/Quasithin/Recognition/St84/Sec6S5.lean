module

public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.Quasithin.Recognition.St84.EdgeStabB

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open
open scoped MatrixGroups Pointwise commutatorElement FixedPoints

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

noncomputable def nbrAction (i : ℤ) : SubMulAction ↥(X.Gi i) V where
  carrier := Γ.neighborSet (X.vert i)
  smul_mem' := by
    intro g a ha
    rw [SimpleGraph.mem_neighborSet] at ha ⊢
    have hg : (g : G) • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp g.2
    rw [← hg]
    exact (X.hyp.adj_smul (g : G) (X.vert i) a).mpr ha

theorem mem_nbrAction {i : ℤ} {a : V} : a ∈ X.nbrAction i ↔ Γ.Adj (X.vert i) a :=
  Iff.rfl

noncomputable def nbrEquiv (i : ℤ) (hn : X.n i = 2) : ↥(X.nbrAction i) ≃ Fin 5 := by
  classical
  haveI : Finite ↥(X.nbrAction i) := (X.hyp.finite_neighborSet (X.vert i)).to_subtype
  letI : Fintype ↥(X.nbrAction i) := Fintype.ofFinite _
  refine Fintype.equivFinOfCardEq ?_
  rw [← Nat.card_eq_fintype_card]
  have h : (Γ.neighborSet (X.vert i)).ncard = 5 := by
    have h' : Nat.card (Γ.neighborSet (X.vert i)) = 2 ^ (2 : ℕ) + 1 := by
      simpa only [show nOf Γ (X.vert i) = 2 from hn] using (X.hyp.valency (X.vert i)).2
    rw [← Nat.card_coe_set_eq]
    norm_num at h' ⊢
    exact h'
  have e : ↥(X.nbrAction i) ≃ ↥(Γ.neighborSet (X.vert i)) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq]
  exact h

@[expose] noncomputable def nbrRep (i : ℤ) (hn : X.n i = 2) :
    ↥(X.Gi i) →* Equiv.Perm (Fin 5) :=
  (X.nbrEquiv i hn).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (↥(X.Gi i)) ↥(X.nbrAction i))

theorem nbrRep_apply (i : ℤ) (hn : X.n i = 2) (g : ↥(X.Gi i)) (w : ↥(X.nbrAction i)) :
    X.nbrRep i hn g (X.nbrEquiv i hn w) = X.nbrEquiv i hn (g • w) := by
  simp [nbrRep, MulAction.toPermHom_apply, Equiv.permCongr_apply]

theorem mem_ker_nbrRep_iff (i : ℤ) (hn : X.n i = 2) (g : ↥(X.Gi i)) :
    g ∈ (X.nbrRep i hn).ker ↔
      ∀ w : ↥(X.nbrAction i), g • w = w := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h w
    apply (X.nbrEquiv i hn).injective
    rw [← X.nbrRep_apply i hn g w, h]
    rfl
  · intro h
    ext y
    obtain ⟨w, rfl⟩ := (X.nbrEquiv i hn).surjective y
    rw [X.nbrRep_apply i hn g w, h w]
    rfl

theorem nbrRep_ker_inf_L (i : ℤ) (hn : X.n i = 2) :
    (X.nbrRep i hn).ker ⊓ (X.L i).subgroupOf (X.Gi i) =
      (X.Q i).subgroupOf (X.Gi i) := by
  classical
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  ext g
  constructor
  · rintro ⟨hgker, hgL⟩
    have hfix : ∀ a : V, Γ.Adj (X.vert i) a → (g : G) • a = a := by
      intro a ha
      have h := (X.mem_ker_nbrRep_iff i hn g).mp hgker ⟨a, ha⟩
      exact congrArg Subtype.val h
    have hgL' : (g : G) ∈ X.L i := hgL
    have hmem := hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
      (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1
      (x := ⟨(g : G), hgL'⟩) (by
        intro a ha
        exact hfix a ha)
    simpa [Setup.Q, Subgroup.mem_subgroupOf] using hmem
  · intro hgQ
    constructor
    · change g ∈ (X.nbrRep i hn).ker
      rw [X.mem_ker_nbrRep_iff i hn g]
      intro w
      apply Subtype.ext
      exact (X.hyp.isLocL2_oTwoPrime (X.vert i)).Q_fixes_neighbors X.hyp.adj_smul
        (X.hyp.finite_stab (X.vert i)) (X.hyp.valency (X.vert i)).2
        (X.hyp.valency (X.vert i)).1 w.1 w.2 (g : G)
        (by simpa [Setup.Q, Setup.Gi, Subgroup.mem_subgroupOf] using hgQ)
    · have hgQ' : (g : G) ∈ X.Q i := Subgroup.mem_subgroupOf.mp hgQ
      exact hN.oTwo_le hgQ'

theorem nbrRep_map_L (i : ℤ) (hn : X.n i = 2) :
    ((X.L i).subgroupOf (X.Gi i)).map (X.nbrRep i hn) = alternatingGroup (Fin 5) := by
  classical
  letI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  let H : Subgroup ↥(X.Gi i) := (X.L i).subgroupOf (X.Gi i)
  let QG : Subgroup ↥(X.Gi i) := (X.Q i).subgroupOf (X.Gi i)
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hQH : QG ≤ H := by
    intro x hx
    exact hN.oTwo_le hx
  let φ : ↥H →* Equiv.Perm (Fin 5) := (X.nbrRep i hn).comp H.subtype
  have hrange : φ.range = H.map (X.nbrRep i hn) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = QG.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hmem : (x : ↥(X.Gi i)) ∈
          (X.nbrRep i hn).ker ⊓ (X.L i).subgroupOf (X.Gi i) := ⟨hx, x.2⟩
      rw [X.nbrRep_ker_inf_L i hn] at hmem
      exact hmem
    · intro hx
      have hmem : (x : ↥(X.Gi i)) ∈ QG := hx
      have hmem' : (x : ↥(X.Gi i)) ∈
          (X.nbrRep i hn).ker ⊓ (X.L i).subgroupOf (X.Gi i) := by
        rw [X.nbrRep_ker_inf_L i hn]
        exact hmem
      exact hmem'.1
  have hquot60 : Nat.card (↥(X.L i) ⧸ CFSG.pCore 2 ↥(X.L i)) = 60 := by
    obtain ⟨ePSL⟩ := hN.quot
    obtain ⟨eA5⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    calc Nat.card (↥(X.L i) ⧸ CFSG.pCore 2 ↥(X.L i))
        = Nat.card (PSL(2, GaloisField 2 (X.n i))) := Nat.card_congr ePSL.toEquiv
      _ = Nat.card (PSL(2, GaloisField 2 2)) := by
          rw [show X.n i = 2 from hn]
      _ = Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr eA5.toEquiv
      _ = 60 := by
          rw [nat_card_alternatingGroup]
          norm_num [Nat.factorial]
  have hcardL : Nat.card ↥H = Nat.card ↥(X.L i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoPrime_le (X.Gi i))).toEquiv
  have hcardQ0 : Nat.card ↥(QG.subgroupOf H) = Nat.card ↥QG :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hcardQ1 : Nat.card ↥QG = Nat.card ↥(X.Q i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.openPCoreOf_le 2 (X.Gi i))).toEquiv
  have hcardQ : Nat.card ↥(φ.ker) = Nat.card ↥(X.Q i) := by
    rw [hker, hcardQ0, hcardQ1]
  have hquotcard : Nat.card (↥H ⧸ φ.ker) * Nat.card ↥(φ.ker) = Nat.card ↥H :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hLCard : Nat.card ↥(X.L i) = 60 * Nat.card ↥(X.Q i) := by
    have h := (Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(X.L i))).symm
    rw [← h, hquot60]
    congr 1
    rw [← CFSG.openPCoreOf_subgroupOf 2 (X.L i), hN.pCoreOf_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.oTwo_le).toEquiv
  have hQpos : 0 < Nat.card ↥(φ.ker) := Nat.card_pos
  have hQpos' : 0 < Nat.card ↥(X.Q i) := hcardQ ▸ hQpos
  have hquotCard60 : Nat.card (↥H ⧸ φ.ker) = 60 := by
    have h : Nat.card (↥H ⧸ φ.ker) * Nat.card ↥(X.Q i) =
        60 * Nat.card ↥(X.Q i) := by
      rw [← hcardQ, hquotcard, hcardL, hLCard, hcardQ]
    exact Nat.eq_of_mul_eq_mul_right hQpos' h
  have hrange60 : Nat.card φ.range = 60 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hquotCard60]
  have hindex : φ.range.index = 2 := by
    have h := Subgroup.index_mul_card (H := φ.range)
    have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hrange60, hperm] at h
    omega
  rw [← hrange]
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex

end Setup

namespace Setup

variable (X : Setup Γ G)

theorem commutator_mem_Q_of_fixes_neighbors (j : ℤ) {k : G}
    (hk2 : k ∈ X.Gi j)
    (hfix : ∀ w : V, Γ.Adj (X.vert j) w → k • w = w) :
    ∀ l ∈ X.L j, ⁅k, l⁆ ∈ X.Q j := by
  classical
  haveI : Finite ↥(X.Gi j) := X.hyp.finite_stab (X.vert j)
  have hkNorm : k ∈ Subgroup.normalizer (X.L j : Set G) :=
    le_normalizer_oTwoPrime (X.Gi j) hk2
  have hkfixinv : ∀ w : V, Γ.Adj (X.vert j) w → k⁻¹ • w = w := by
    intro w hw
    have hkw : Γ.Adj (X.vert j) (k⁻¹ • w) := by
      have hkadj : (k⁻¹ : G) • X.vert j = X.vert j := by
        have h := congrArg (fun v => k⁻¹ • v) (MulAction.mem_stabilizer_iff.mp hk2)
        simpa using h.symm
      rw [← hkadj]
      exact (X.hyp.adj_smul k⁻¹ (X.vert j) w).mpr hw
    have h := hfix (k⁻¹ • w) hkw
    simpa using h.symm
  intro l hl
  have hlG : l ∈ X.Gi j := (oTwoPrime_le (X.Gi j)) hl
  have hkl : k * l * k⁻¹ ∈ X.L j :=
    (Subgroup.mem_normalizer_iff.mp hkNorm l).mp hl
  have hcommL : k * l * k⁻¹ * l⁻¹ ∈ X.L j :=
    (X.L j).mul_mem hkl ((X.L j).inv_mem hl)
  have hfixall : ∀ w : V, Γ.Adj (X.vert j) w → (k * l * k⁻¹ * l⁻¹) • w = w := by
    intro w hw
    have hlw : Γ.Adj (X.vert j) (l • w) := by
      have hlfix : l • X.vert j = X.vert j := MulAction.mem_stabilizer_iff.mp hlG
      rw [← hlfix]
      exact (X.hyp.adj_smul l (X.vert j) w).mpr hw
    have hlw' : Γ.Adj (X.vert j) (l⁻¹ • w) := by
      have hlfix : l⁻¹ • X.vert j = X.vert j := by
        have h := congrArg (fun v => l⁻¹ • v) (MulAction.mem_stabilizer_iff.mp hlG)
        simpa using h.symm
      rw [← hlfix]
      exact (X.hyp.adj_smul l⁻¹ (X.vert j) w).mpr hw
    calc (k * l * k⁻¹ * l⁻¹) • w = k • (l • (k⁻¹ • (l⁻¹ • w))) := by simp [mul_smul]
      _ = k • (l • (l⁻¹ • w)) := by rw [hkfixinv (l⁻¹ • w) hlw']
      _ = k • w := by rw [smul_inv_smul]
      _ = w := hfix w hw
  have hN := X.hyp.isLocL2_oTwoPrime (X.vert j)
  have := hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul (X.hyp.finite_stab (X.vert j))
    (X.hyp.valency (X.vert j)).2 (X.hyp.valency (X.vert j)).1
    (x := ⟨k * l * k⁻¹ * l⁻¹, hcommL⟩) hfixall
  simpa [Setup.Q, Setup.Gi, commutatorElement_def] using this

theorem L_eq_centralizer_sup_Q (j : ℤ) {k : G}
    (hk1 : k ∈ X.Gi (j - 1)) (hk2 : k ∈ X.Gi j) (hodd : Odd (orderOf k))
    (hfix : ∀ w : V, Γ.Adj (X.vert j) w → k • w = w) :
    X.L j = (X.L j ⊓ Subgroup.centralizer ({k} : Set G)) ⊔ X.Q j := by
  classical
  haveI : Finite ↥(X.Gi j) := X.hyp.finite_stab (X.vert j)
  have hL2 : IsLocL2 Γ G (X.vert j) (X.n j) (X.L j) := X.hyp.isLocL2_oTwoPrime (X.vert j)
  let A : Subgroup G := Subgroup.zpowers k
  haveI : Finite ↥(X.L j) := Finite.of_injective
    (fun x : ↥(X.L j) => (⟨(x : G), oTwoPrime_le (X.Gi j) x.2⟩ : ↥(X.Gi j)))
    (fun a b h => Subtype.ext (congrArg (fun z : ↥(X.Gi j) => (z : G)) h))
  have hAGi : A ≤ X.Gi j := Subgroup.zpowers_le.mpr hk2
  haveI : Finite ↥A := Finite.of_injective
    (fun a : ↥A => (⟨(a : G), hAGi a.2⟩ : ↥(X.Gi j)))
    (fun a b h => Subtype.ext (congrArg (fun z : ↥(X.Gi j) => (z : G)) h))
  have hAL : A ≤ Subgroup.normalizer (X.L j : Set G) :=
    hAGi.trans (le_normalizer_oTwoPrime (X.Gi j))
  letI : Subgroup.Normalizes A (X.L j) := ⟨hAL⟩
  let N : Subgroup ↥(X.L j) := (X.Q j).subgroupOf (X.L j)
  have hN_eq : N = CFSG.pCore 2 ↥(X.L j) := by
    rw [show N = (pCoreOf 2 (X.L j)).subgroupOf (X.L j) from by
      simp [N, hL2.pCoreOf_eq]]
    exact CFSG.openPCoreOf_subgroupOf 2 (X.L j)
  haveI : N.Normal := by
    rw [hN_eq]
    infer_instance
  have hNinv : IsInvariant ↥A ↥(X.L j) N := by
    refine ⟨fun a g => ?_⟩
    constructor
    · intro hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have haQ : (a : G) ∈ Subgroup.normalizer (X.Q j : Set G) :=
        (Subgroup.zpowers_le.mpr hk2).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi j)) a.2
      exact (Subgroup.mem_normalizer_iff.mp haQ (g : G)).mp hg
    · intro hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hg
      have haQ : (a : G) ∈ Subgroup.normalizer (X.Q j : Set G) :=
        (Subgroup.zpowers_le.mpr hk2).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi j)) a.2
      have hmem := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (X.Q j : Set G)).inv_mem haQ) ((a : G) * (g : G) * (a : G)⁻¹)).mp hg
      simpa [mul_assoc] using hmem
  have hNp : IsPGroup 2 N := by
    rw [hN_eq]
    exact CFSG.pCore_isPGroup (G := ↥(X.L j)) (p := 2)
  have hNsolv : Group.IsSolvable N := by
    haveI : Group.IsNilpotent N := hNp.isNilpotent
    infer_instance
  letI : Group.IsSolvable N := hNsolv
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card N) := by
    have hAcard : Nat.card ↥A = orderOf k := by rw [Nat.card_zpowers]
    obtain ⟨n, hnN⟩ := IsPGroup.iff_card.mp hNp
    rw [hAcard, hnN]
    exact Nat.Coprime.pow_right n
      ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd.not_two_dvd_nat).symm
  letI : MulDistribMulAction ↥A (↥(X.L j) ⧸ N) :=
    CFSG.quotientMulDistribMulAction (A := ↥A) (G := ↥(X.L j)) (H := N) hNinv
  let gA : ↥A := ⟨k, Subgroup.mem_zpowers k⟩
  have htop_zpowers : Subgroup.zpowers gA = (⊤ : Subgroup ↥A) := by
    ext a
    constructor
    · intro _; exact Subgroup.mem_top a
    · intro _
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext hm⟩
  have hstabQ : ∀ q : ↥(X.L j) ⧸ N, gA • q = q → ∀ a : ↥A, a • q = q := by
    intro q hq a
    have hle : (⊤ : Subgroup ↥A) ≤ MulAction.stabilizer ↥A q := by
      rw [← htop_zpowers]
      exact Subgroup.zpowers_le.mpr hq
    exact hle (Subgroup.mem_top a)
  have hstabL : ∀ c : ↥(X.L j), gA • c = c → ∀ a : ↥A, a • c = c := by
    intro c hc a
    have hle : (⊤ : Subgroup ↥A) ≤ MulAction.stabilizer ↥A c := by
      rw [← htop_zpowers]
      exact Subgroup.zpowers_le.mpr hc
    exact hle (Subgroup.mem_top a)
  have hgAfix : ∀ q : ↥(X.L j) ⧸ N, gA • q = q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro l
    have hcomm := commutator_mem_Q_of_fixes_neighbors X j hk2 hfix (l : G) l.2
    have hmem : ((gA • l) * l⁻¹ : ↥(X.L j)) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      change ((gA • l : ↥(X.L j)) : G) * ((l⁻¹ : ↥(X.L j)) : G) ∈ X.Q j
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, Subgroup.coe_inv]
      simpa [gA, commutatorElement_def, mul_assoc] using hcomm
    have h1 : (((gA • l) * l⁻¹ : ↥(X.L j)) : ↥(X.L j) ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [MulAction.Quotient.smul_coe]
    have h1q : ((gA • l : ↥(X.L j)) : ↥(X.L j) ⧸ N) *
        ((l : ↥(X.L j)) : ↥(X.L j) ⧸ N)⁻¹ = 1 := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h1
    calc ((gA • l : ↥(X.L j)) : ↥(X.L j) ⧸ N)
        = ((gA • l : ↥(X.L j)) : ↥(X.L j) ⧸ N) *
            ((l : ↥(X.L j)) : ↥(X.L j) ⧸ N)⁻¹ * ((l : ↥(X.L j)) : ↥(X.L j) ⧸ N) := by group
      _ = 1 * ((l : ↥(X.L j)) : ↥(X.L j) ⧸ N) := by rw [h1q]
      _ = ((l : ↥(X.L j)) : ↥(X.L j) ⧸ N) := one_mul _
  have htop : fixedPointSubgroup ↥A (↥(X.L j) ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    intro a
    exact hstabQ q (hgAfix q) a
  let C : Subgroup ↥(X.L j) := fixedPointSubgroup ↥A ↥(X.L j)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    (A := ↥A) (G := ↥(X.L j))
    N hNinv hNsolv hcop
  rw [htop] at hlift
  have hCg_eq : C.map (X.L j).subtype =
      X.L j ⊓ Subgroup.centralizer ({k} : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      change (c : G) ∈ Subgroup.centralizer ({k} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgAc : gA • c = c := hc gA
      have h := congrArg Subtype.val hgAc
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h
      calc (c : G) * k = (k * c * k⁻¹) * k := by rw [h]
        _ = k * c := by group
    · rintro ⟨hxL, hxc⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      intro a
      have hgA : gA • (⟨x, hxL⟩ : ↥(X.L j)) = ⟨x, hxL⟩ := by
        apply Subtype.ext
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        change k * x * k⁻¹ = x
        change x ∈ Subgroup.centralizer ({k} : Set G) at hxc
        rw [Subgroup.mem_centralizer_singleton_iff] at hxc
        have h1 : k * x = x * k := hxc.symm
        rw [h1]
        group
      exact hstabL (⟨x, hxL⟩ : ↥(X.L j)) hgA a
  have hQleL : X.Q j ≤ X.L j := hL2.oTwo_le
  have hle : X.L j ≤ C.map (X.L j).subtype ⊔ X.Q j := by
    intro x hxL
    let l : ↥(X.L j) := ⟨x, hxL⟩
    have hqtop : (l : ↥(X.L j) ⧸ N) ∈ (⊤ : Subgroup (↥(X.L j) ⧸ N)) := Subgroup.mem_top _
    rw [hlift] at hqtop
    obtain ⟨c, hc, hcl⟩ := Subgroup.mem_map.mp hqtop
    have hmemN : (c⁻¹ * l : ↥(X.L j)) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change ((QuotientGroup.mk' N) c)⁻¹ * (QuotientGroup.mk' N) l = 1
      rw [show (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) l from hcl]
      exact inv_mul_cancel _
    have hcCg : (c : G) ∈ C.map (X.L j).subtype := ⟨c, hc, rfl⟩
    have hqQ : ((c⁻¹ * l : ↥(X.L j)) : G) ∈ X.Q j :=
      Subgroup.mem_subgroupOf.mp hmemN
    have hcval : (((c⁻¹ * l : ↥(X.L j)) : G)) = (c : G)⁻¹ * x := by
      simp [l]
    have hprod : (c : G) * ((c⁻¹ * l : ↥(X.L j)) : G) = x := by
      rw [hcval]
      group
    rw [← hprod]
    exact Subgroup.mul_mem_sup hcCg hqQ
  apply le_antisymm
  · rw [hCg_eq] at hle
    exact hle
  · exact sup_le inf_le_left hQleL

theorem centralizer_transitive (j : ℤ) {k : G}
    (hk1 : k ∈ X.Gi (j - 1)) (hk2 : k ∈ X.Gi j) (hodd : Odd (orderOf k))
    (hfix : ∀ w : V, Γ.Adj (X.vert j) w → k • w = w) :
    ∀ a b : V, Γ.Adj (X.vert j) a → Γ.Adj (X.vert j) b →
      ∃ g ∈ Subgroup.centralizer ({k} : Set G) ⊓ X.Gi j, g • a = b := by
  classical
  have hL2 : IsLocL2 Γ G (X.vert j) (X.n j) (X.L j) := X.hyp.isLocL2_oTwoPrime (X.vert j)
  have hLeq := X.L_eq_centralizer_sup_Q j hk1 hk2 hodd hfix
  have hQleL : X.Q j ≤ X.L j := hL2.oTwo_le
  haveI : ((X.Q j).subgroupOf (X.L j)).Normal := by
    rw [show (X.Q j).subgroupOf (X.L j) = CFSG.pCore 2 ↥(X.L j) from by
      rw [← CFSG.openPCoreOf_subgroupOf 2 (X.L j), hL2.pCoreOf_eq]]
    infer_instance
  intro a b ha hb
  obtain ⟨l, hlL, hlab⟩ := hL2.trans a b ha hb
  have hsub : ((X.L j ⊓ Subgroup.centralizer ({k} : Set G)) ⊔ X.Q j).subgroupOf (X.L j) =
      (X.L j ⊓ Subgroup.centralizer ({k} : Set G)).subgroupOf (X.L j) ⊔
        (X.Q j).subgroupOf (X.L j) :=
    Subgroup.subgroupOf_sup inf_le_left hQleL
  have hl : (⟨l, hlL⟩ : ↥(X.L j)) ∈
      (X.L j ⊓ Subgroup.centralizer ({k} : Set G)).subgroupOf (X.L j) ⊔
        (X.Q j).subgroupOf (X.L j) := by
    rw [← hsub, ← hLeq]
    exact Subgroup.mem_subgroupOf.mpr hlL
  obtain ⟨c, hc, q, hq, hcq⟩ := Subgroup.mem_sup_of_normal_right.mp hl
  have hcLC : (c : G) ∈ X.L j ⊓ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_subgroupOf.mp hc
  have hqQ : (q : G) ∈ X.Q j := Subgroup.mem_subgroupOf.mp hq
  have hcGi : (c : G) ∈ X.Gi j := oTwoPrime_le (X.Gi j) hcLC.1
  have hqfix : (q : G) • a = a :=
    hL2.Q_fixes_neighbors X.hyp.adj_smul (X.hyp.finite_stab (X.vert j))
      (X.hyp.valency (X.vert j)).2 (X.hyp.valency (X.vert j)).1 a ha (q : G) hqQ
  refine ⟨(c : G), ⟨hcLC.2, hcGi⟩, ?_⟩
  have hmul : (⟨l, hlL⟩ : ↥(X.L j)) = c * q := hcq.symm
  have hval : l = (c : G) * (q : G) := by
    have := congrArg Subtype.val hmul
    simpa using this
  calc (c : G) • a = (c : G) • ((q : G) • a) := by rw [hqfix]
    _ = l • a := by rw [hval]; simp [mul_smul]
    _ = b := hlab

end Setup

end CFSG.Quasithin.St84
