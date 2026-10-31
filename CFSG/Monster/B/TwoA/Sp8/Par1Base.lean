
module

public import CFSG.Monster.B.TwoA.Sp8.A8Base
public import CFSG.Monster.B.TwoA.Sp8.QuadDataBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA

def cE : Ehat := ⟨cQ, cQ_mem_Ehat⟩

theorem psiW_cE :
    psiW cE = Unitary.sigmaW := by
  have e : cE = ehatEquiv ⟨dbar 0 2, dbar_mem_Ebar 0 2⟩ := rfl
  rw [e, psiW_ehatEquiv]
  have e2 := psiBar_kappa_rho (DQ_mem_centralizer (deltaPair 0 2))
  change wvEquiv hv0 (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv (DQ (deltaPair 0 2)),
    rhoEquiv_mem_Cgen (DQ_mem_centralizer (deltaPair 0 2))⟩,
    kappa_rho_mem_Ebar (DQ_mem_centralizer (deltaPair 0 2))⟩)) = _
  rw [e2, toAdd_ofAdd, wvEquiv_mk, Unitary.sigmaW]
  congr 1
  apply Subtype.ext
  change phi0 (coordOf (rMinus 0 2)) = pairCls 0 2 0
  rw [phi0_coordOf_rMinus (by decide), pairCls, pairVec_zero]

def sigLine :

    Submodule (ZMod 2) (Wv v0) := Submodule.span (ZMod 2) {Unitary.sigmaW}

theorem mem_sigLine
    {x : Wv v0} : x ∈ sigLine ↔ x = 0 ∨ x = Unitary.sigmaW := by
  rw [sigLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases zmod2_cases a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem sigmaW_mem_sigLine :
    Unitary.sigmaW ∈ sigLine :=
  Submodule.subset_span (Set.mem_singleton _)

theorem xhat_comm_cQ : xhat * cQ = cQ * xhat :=
  (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm

theorem cQ_mem_closure : cQ ∈ Subgroup.closure ({xhat, cQ} : Set Dfull) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem xhat_mem_closure : xhat ∈ Subgroup.closure ({xhat, cQ} : Set Dfull) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem EU_sigLine :
    EU sigLine = Subgroup.closure {xhat, cQ} := by
  apply le_antisymm
  · intro d hd
    obtain ⟨hdE, hdU⟩ := mem_EU.1 hd
    rcases mem_sigLine.1 hdU with h0 | h1
    · rcases (psiW_eq_zero_iff _).1 h0 with h | h
      · have e : d = 1 := congrArg Subtype.val h
        rw [e]
        exact Subgroup.one_mem _
      · have e : d = xhat := congrArg Subtype.val h
        rw [e]
        exact xhat_mem_closure
    · have h2 : psiW (⟨d, hdE⟩ * cE⁻¹) = 0 := by
        rw [psiW_mul, psiW_inv, h1, psiW_cE, add_neg_cancel]
      rcases (psiW_eq_zero_iff _).1 h2 with h | h
      · have e : d * cQ⁻¹ = 1 := congrArg Subtype.val h
        rw [mul_inv_eq_one.1 e]
        exact cQ_mem_closure
      · have e : d * cQ⁻¹ = xhat := congrArg Subtype.val h
        rw [mul_inv_eq_iff_eq_mul.1 e]
        exact Subgroup.mul_mem _ xhat_mem_closure cQ_mem_closure
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact xhat_mem_EU
    · exact mem_EU_of (e := cE) (by rw [psiW_cE]; exact sigmaW_mem_sigLine)

def P1 : Subgroup Dfull := Jhat ⊓ Subgroup.centralizer {cQ}

def N1 : Subgroup Dfull := Ehat ⊓ Subgroup.centralizer {cQ}

theorem P1_le_Jhat : P1 ≤ Jhat := inf_le_left

theorem N1_le_Ehat : N1 ≤ Ehat := inf_le_left

theorem N1_le_P1 : N1 ≤ P1 := fun _ h => ⟨Ehat_le_Jhat h.1, h.2⟩

theorem P1_eq_ZU :
    P1 = ZU sigLine := by
  ext g
  rw [ZU, EU_sigLine, Subgroup.centralizer_closure, P1, Subgroup.mem_inf, ← centralizer_xhat]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

theorem N1_eq :
    N1 = Ehat ⊓ ZU sigLine := by
  rw [← P1_eq_ZU, P1, N1, ← inf_assoc, inf_eq_left.2 Ehat_le_Jhat]

theorem N1_eq_EU :
    N1 = EU (bV.orthogonal sigLine) := by
  rw [N1_eq]
  exact Ehat_inf_centralizer_EU

theorem wFix_sigLine :
    wFix (sigLine : Set (Wv v0)) = Unitary.Usig := by
  ext k
  rw [mem_wFix, Unitary.mem_Usig]
  constructor
  · intro h
    exact h _ sigmaW_mem_sigLine
  · intro h x hx
    rcases mem_sigLine.1 hx with rfl | rfl
    · exact map_zero _
    · exact h

def p1Proj :
    P1 →* Unitary.Usig :=
  (MulEquiv.subgroupCongr wFix_sigLine).toMonoidHom.comp
    ((zuProj sigLine).comp (MulEquiv.subgroupCongr P1_eq_ZU).toMonoidHom)

theorem coe_p1Proj
    (g : P1) :
    (p1Proj g : Kstab v0) = jhatToKv0 ⟨g, P1_le_Jhat g.2⟩ := rfl

theorem p1Proj_surjective :
    Function.Surjective p1Proj := by
  rw [p1Proj, MonoidHom.coe_comp, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom]
  exact (MulEquiv.surjective _).comp (zuProj_surjective.comp (MulEquiv.surjective _))

theorem ker_p1Proj :
    p1Proj.ker = N1.subgroupOf P1 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, N1, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : jhatToKv0 ⟨g, P1_le_Jhat g.2⟩ = 1 :=
      (coe_p1Proj g).symm.trans (congrArg Subtype.val h)
    rw [← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf] at h1
    exact ⟨h1, g.2.2⟩
  · rintro ⟨hE, -⟩
    apply Subtype.ext
    rw [coe_p1Proj, jhatToKv0_eq_one_of_mem_Ehat _ hE]
    rfl

theorem map_P1 :
    (P1.subgroupOf Jhat).map jhatToKv0 = Unitary.Usig := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have h := (p1Proj ⟨g, hg⟩).2
    rw [coe_p1Proj] at h
    exact h
  · intro k hk
    obtain ⟨g, hg⟩ := p1Proj_surjective ⟨k, hk⟩
    exact ⟨⟨g, P1_le_Jhat g.2⟩, g.2, (coe_p1Proj g).symm.trans (congrArg Subtype.val hg)⟩

theorem P1_inf_ker : P1.subgroupOf Jhat ⊓ jhatToKv0.ker = N1.subgroupOf Jhat := by
  ext g
  rw [Subgroup.mem_inf, ker_jhatToKv0, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, N1, P1, Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨g.2, h.2⟩, h.1⟩⟩

theorem pCore_two_eq_bot_of_odd {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (hX : Odd (Nat.card X)) :
    CFSG.pCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  have hB := MulAction.IsBlock.orbit_of_normal (G := G) (N := CFSG.pCore 2 G) x
  have h1 := MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq hB ⟨x, MulAction.mem_orbit_self x⟩
  have hp : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h2 : (MulAction.orbit (CFSG.pCore 2 G) x).ncard ∣ 2 ^ k := by
    rw [← MulAction.index_stabilizer, ← hk]
    exact Subgroup.index_dvd_card _
  have h3 : (MulAction.orbit (CFSG.pCore 2 G) x).ncard ∣ Nat.card X := Dvd.intro _ h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hX)
  have h4 : (MulAction.orbit (CFSG.pCore 2 G) x).ncard = 1 :=
    Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h2 h3)
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h4
  have hx : x ∈ MulAction.orbit (CFSG.pCore 2 G) x := MulAction.mem_orbit_self x
  have hnx : (⟨n, hn⟩ : CFSG.pCore 2 G) • x ∈ MulAction.orbit (CFSG.pCore 2 G) x :=
    MulAction.mem_orbit _ _
  rw [ha, Set.mem_singleton_iff] at hx hnx
  exact hnx.trans hx.symm

instance N1_subgroupOf_normal :
    (N1.subgroupOf P1).Normal := ker_p1Proj ▸ p1Proj.normal_ker

def p1QuotEquiv :
    P1 ⧸ N1.subgroupOf P1 ≃* Unitary.Usig :=
  (QuotientGroup.quotientMulEquivOfEq ker_p1Proj.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p1Proj p1Proj_surjective)

@[instance_reducible] def jConj : MulAction Jhat Dfull :=
  MulAction.compHom Dfull ((MulAut.conj (G := Dfull)).comp Jhat.subtype)

theorem sigLine_orth_orth :
    bV.orthogonal (bV.orthogonal sigLine) = sigLine :=
  LinearMap.BilinForm.orthogonal_orthogonal bV_nondegenerate
    (fun x y h => by rw [bV_comm]; exact h) sigLine

theorem sigLine_le_orth :
    sigLine ≤ bV.orthogonal sigLine := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rcases mem_sigLine.1 hx with rfl | rfl <;> rcases mem_sigLine.1 hy with rfl | rfl
  · exact LinearMap.map_zero₂ _ _
  · exact map_zero _
  · exact LinearMap.map_zero₂ _ _
  · exact bV_self _

theorem EU_sigLine_le_N1 :
    EU sigLine ≤ N1 := by
  rw [N1_eq_EU]
  exact EU_mono sigLine_le_orth

theorem mem_center_N1
    {g : Dfull} (hg : g ∈ N1) :
    (∀ h ∈ N1, g * h = h * g) ↔ g ∈ EU sigLine := by
  constructor
  · intro hc
    have hg' := hg
    rw [N1_eq_EU] at hg'
    obtain ⟨hgE, -⟩ := mem_EU.1 hg'
    refine mem_EU.2 ⟨hgE, ?_⟩
    rw [← sigLine_orth_orth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨a, rfl, ha⟩ := exists_EU_of_mem hy
    have ha' : (a : Dfull) ∈ N1 := by
      rw [N1_eq_EU]
      exact ha
    have h1 := Ehat_comm a ⟨g, hgE⟩
    have h2 : (a : Dfull) * g = g * a := (hc a ha').symm
    have h3 : g * (a : Dfull) * xhat ^ (bV (psiW a) (psiW ⟨g, hgE⟩)).val = g * a * 1 := by
      rw [mul_one, ← h1, h2]
    exact (xhat_pow_val_eq_one_iff _).1 (mul_left_cancel h3)
  · intro hU h hh
    rw [N1_eq] at hh
    exact (Subgroup.mem_centralizer_iff.1 hh.2) g hU

theorem center_N1 :

    Subgroup.center N1 = (Subgroup.closure {xhat, cQ}).subgroupOf N1 := by
  ext g
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, ← EU_sigLine, ← mem_center_N1 g.2]
  constructor
  · intro h k hk
    exact (congrArg Subtype.val (h ⟨k, hk⟩)).symm
  · intro h k
    exact Subtype.ext (h k k.2).symm

theorem Ehat_sq_mem {e : Dfull} (he : e ∈ Ehat) : e * e = 1 ∨ e * e = xhat := by
  have h : psiW (⟨e, he⟩ * ⟨e, he⟩) = 0 := by
    rw [psiW_mul]
    exact ZModModule.add_self _
  rcases (psiW_eq_zero_iff _).1 h with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem Ehat_commutator
    {e f : Dfull} (he : e ∈ Ehat) (hf : f ∈ Ehat) :
    e * f * e⁻¹ * f⁻¹ = xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val := by
  have h1 : e * f = f * e * xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val :=
    Ehat_comm ⟨e, he⟩ ⟨f, hf⟩
  have hx : f * e * xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val =
      xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val * (f * e) :=
    xhat_pow_comm_of_mem_Jhat (Ehat_le_Jhat (Ehat.mul_mem hf he)) _
  calc e * f * e⁻¹ * f⁻¹ = (e * f) * (f * e)⁻¹ := by group
    _ = (f * e * xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val) * (f * e)⁻¹ := by rw [← h1]
    _ = xhat ^ (bV (psiW ⟨e, he⟩) (psiW ⟨f, hf⟩)).val := by rw [hx, mul_inv_cancel_right]

instance isElementaryAbelian_N1_quot :
    CFSG.IsElementaryAbelian 2 (N1 ⧸ Subgroup.center N1) where
  is_comm := ⟨fun a b => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, center_N1,
      Subgroup.mem_subgroupOf, ← EU_sigLine]
    have e : (((g * h)⁻¹ * (h * g) : N1) : Dfull) =
        (h : Dfull)⁻¹ * (g : Dfull)⁻¹ * (h : Dfull)⁻¹⁻¹ * (g : Dfull)⁻¹⁻¹ := by
      push_cast
      group
    rw [e, Ehat_commutator (Ehat.inv_mem (N1_le_Ehat h.2)) (Ehat.inv_mem (N1_le_Ehat g.2))]
    exact Subgroup.pow_mem _ xhat_mem_EU _⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, center_N1, Subgroup.mem_subgroupOf,
      ← EU_sigLine]
    have e : ((g ^ 2 : N1) : Dfull) = (g : Dfull) * g := by
      rw [Subgroup.coe_pow, sq]
    rw [e]
    rcases Ehat_sq_mem (N1_le_Ehat g.2) with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact xhat_mem_EU

end CFSG.Monster.B.TwoA.Sp8
