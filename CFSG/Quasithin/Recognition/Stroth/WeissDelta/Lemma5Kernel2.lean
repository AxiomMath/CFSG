module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5Kernel

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

private theorem exists_backward_path4 (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {x y : V} (hxy : Γ.Adj x y) :
    ∃ p : GPath Γ 4, p.NoBack ∧ p 3 = x ∧ p 4 = y := by
  obtain ⟨c, hxc, hcy⟩ := hne x y hxy
  obtain ⟨b, hcb, hbx⟩ := hne c x hxc.symm
  obtain ⟨a, hba, hac⟩ := hne b c hcb.symm
  refine ⟨path5 a b c x y hba.symm hcb.symm hxc.symm hxy,
    path5_noBack hba.symm hcb.symm hxc.symm hxy hac hbx hcy, ?_, ?_⟩
  · simp [path5]
  · simp [path5]

private def edgeUnionAll (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (x₀ : V) : Subgroup H :=
  ⨆ y ∈ Γ.neighborSet x₀, edgeUnion H Γ x₀ y

private theorem socleAt_le_edgeUnionAll_sup (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    {x₀ : V} (hR : RootFacts H Γ 4 x₀) {x₁ x₁' : V} (h1 : Γ.Adj x₀ x₁) (h1' : Γ.Adj x₀ x₁')
    (h11 : x₁ ≠ x₁') :
    socleAt H Γ x₀ ≤ edgeUnionAll H Γ x₀ ⊔ fixingSubgroup H (Γ.neighborSet x₀) := by
  obtain ⟨q, hqnb, hq3, hq4⟩ := exists_backward_path4 hne h1.symm
  obtain ⟨q', hq'nb, hq'3, hq'4⟩ := exists_backward_path4 hne h1'.symm
  have hle := hR.socle_le q q' hqnb hq'nb hq4 hq'4 (by rw [hq3, hq'3]; exact h11)
  have hqU : pathRootGroup H Γ q ≤ edgeUnionAll H Γ x₀ := by
    intro g hg
    refine Subgroup.mem_iSup_of_mem x₁ ?_
    refine Subgroup.mem_iSup_of_mem (by simpa using h1) ?_
    exact pathRootGroup_le_edgeUnion_penultimate hq3 hg
  have hq'U : pathRootGroup H Γ q' ≤ edgeUnionAll H Γ x₀ := by
    intro g hg
    refine Subgroup.mem_iSup_of_mem x₁' ?_
    refine Subgroup.mem_iSup_of_mem (by simpa using h1') ?_
    exact pathRootGroup_le_edgeUnion_penultimate hq'3 hg
  refine hle.trans ?_
  exact sup_le_sup (sup_le hqU hq'U) le_rfl

private theorem kernelCenter_le_centralizer_edgeUnionAll [Finite H]
    (hM : MoufangCondition H Γ 4) (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) {e : ℕ} {x₀ : V}
    (hC : ∀ g : H, CenterFacts H Γ (g • x₀) e)
    {x₁ : V} (h1 : Γ.Adj x₀ x₁) (h2 : secondKernel H Γ x₀ ≠ ⊥) :
    kernelCenter H Γ x₀ x₁ ≤
      Subgroup.centralizer (edgeUnionAll H Γ x₀ : Set H) := by
  refine Subgroup.le_centralizer_iff.mp ?_
  rw [edgeUnionAll]
  refine iSup_le fun y => iSup_le fun hy => ?_
  intro z hz
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro p hp
  by_cases hyx : y = x₁
  · subst hyx
    have hpC : p ∈ Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) :=
      kernelCenter_centralizes hp
    exact ((Subgroup.mem_centralizer_iff.mp hpC) z hz).symm
  · have hle := kernelCenter_le_kernelCenter_of_ne hM hW hne hval hloc hL hC h1
      (by simpa using hy) (Ne.symm hyx) h2
    have hpC : p ∈ Subgroup.centralizer (edgeUnion H Γ x₀ y : Set H) :=
      kernelCenter_centralizes (hle hp)
    exact ((Subgroup.mem_centralizer_iff.mp hpC) z hz).symm

theorem exists_odd_mem_fixingSubgroup_of_secondKernel_ne_bot [Finite H] {e : ℕ}
    (hM : MoufangCondition H Γ 4) (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) (hR : ∀ z, RootFacts H Γ 4 z) {x₀ : V}
    (hC : ∀ g : H, CenterFacts H Γ (g • x₀) e) (h2 : secondKernel H Γ x₀ ≠ ⊥)
    {x₁ x₁' : V} (h1 : Γ.Adj x₀ x₁) (h1' : Γ.Adj x₀ x₁') (h11 : x₁ ≠ x₁')
    {t : H} (ht : t ∈ socTorus H Γ x₀ x₁ x₁') :
    ∃ x₂ : V, Γ.Adj x₁ x₂ ∧ x₂ ≠ x₀ ∧ ∃ a : H,
      a ∈ fixingSubgroup H (Γ.neighborSet x₂) ∧
      a • x₀ = x₀ ∧ a • x₁ = x₁ ∧ a • x₁' = x₁' ∧ Odd (orderOf a) ∧
        a * (t ^ e)⁻¹ ∈ fixingSubgroup H (Γ.neighborSet x₀) := by
  classical
  let P := kernelCenter H Γ x₀ x₁
  let U := edgeUnionAll H Γ x₀
  have hPsocle : socleAt H Γ x₀ ≤ U ⊔ fixingSubgroup H (Γ.neighborSet x₀) :=
    socleAt_le_edgeUnionAll_sup hne (hR x₀) h1 h1' h11
  have hPcent : P ≤ Subgroup.centralizer (U : Set H) :=
    kernelCenter_le_centralizer_edgeUnionAll hM hW hne hval hloc hL hC h1 h2
  have htSoc : t ∈ socleAt H Γ x₀ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
  have htStab₁ : t ∈ MulAction.stabilizer H x₁ :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).2
  have htStab₁' : t ∈ MulAction.stabilizer H x₁' := (Subgroup.mem_inf.mp ht).2
  have htStab₀ : t ∈ MulAction.stabilizer H x₀ :=
    (socleAt_le_stabilizer (hL x₀).kernel_le) htSoc
  have hUstab : U ≤ MulAction.stabilizer H x₀ := by
    change (⨆ y ∈ Γ.neighborSet x₀, edgeUnion H Γ x₀ y) ≤ MulAction.stabilizer H x₀
    refine iSup_le fun y => iSup_le fun hy => ?_
    exact (edgeUnion_le_stabilizer (fun z => (hL z).kernel_le)
      (by simpa using hy)).trans inf_le_left
  have hnorm : U ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet x₀) : Set H) :=
    hUstab.trans stabilizer_le_normalizer_fixingSubgroup
  have htU : t ∈ U ⊔ fixingSubgroup H (Γ.neighborSet x₀) := hPsocle htSoc
  have ht' : t ∈ (↑(U ⊔ fixingSubgroup H (Γ.neighborSet x₀)) : Set H) := htU
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at ht'
  rcases ht' with ⟨a₀, ha₀U, k, hk, hak⟩
  let φ := localPermHom (H := H) Γ x₀
  have ha₀Stab : a₀ ∈ MulAction.stabilizer H x₀ := hUstab ha₀U
  have hkStab : k ∈ MulAction.stabilizer H x₀ := (hL x₀).kernel_le hk
  have hkφ : φ ⟨k, hkStab⟩ = 1 := by
    ext w
    rw [Equiv.Perm.one_apply, localPermHom_apply]
    exact (mem_fixingSubgroup_iff H).mp hk w.1 w.2
  have hφa₀ : φ ⟨a₀, ha₀Stab⟩ = φ ⟨t, htStab₀⟩ := by
    have hmul : (⟨a₀, ha₀Stab⟩ * ⟨k, hkStab⟩ : ↥(MulAction.stabilizer H x₀)) =
        ⟨t, htStab₀⟩ := by
      ext
      exact hak
    rw [← hmul, map_mul, hkφ, mul_one]
  have hTle : socTorus H Γ x₀ x₁ x₁' ≤ MulAction.stabilizer H x₀ :=
    (inf_le_left.trans inf_le_left).trans (socleAt_le_stabilizer (hL x₀).kernel_le)
  have hrelT : ((fixingSubgroup H (Γ.neighborSet x₀)).subgroupOf
      (MulAction.stabilizer H x₀)).relIndex
        ((socTorus H Γ x₀ x₁ x₁').subgroupOf (MulAction.stabilizer H x₀)) =
      (fixingSubgroup H (Γ.neighborSet x₀)).relIndex (socTorus H Γ x₀ x₁ x₁') :=
    Subgroup.relIndex_subgroupOf (K := socTorus H Γ x₀ x₁ x₁')
      (L := MulAction.stabilizer H x₀) hTle
  have hφtOdd : Odd (orderOf (φ ⟨t, htStab₀⟩)) := by
    have hcard : Nat.card (((socTorus H Γ x₀ x₁ x₁').subgroupOf
        (MulAction.stabilizer H x₀)).map φ) =
        (fixingSubgroup H (Γ.neighborSet x₀)).relIndex (socTorus H Γ x₀ x₁ x₁') := by
      calc
        Nat.card (((socTorus H Γ x₀ x₁ x₁').subgroupOf
            (MulAction.stabilizer H x₀)).map φ) =
            φ.ker.relIndex ((socTorus H Γ x₀ x₁ x₁').subgroupOf
              (MulAction.stabilizer H x₀)) :=
          (Subgroup.relIndex_ker _ φ).symm
        _ = ((fixingSubgroup H (Γ.neighborSet x₀)).subgroupOf
              (MulAction.stabilizer H x₀)).relIndex
              ((socTorus H Γ x₀ x₁ x₁').subgroupOf
                (MulAction.stabilizer H x₀)) := by
          rw [localPermHom_ker]
        _ = (fixingSubgroup H (Γ.neighborSet x₀)).relIndex
              (socTorus H Γ x₀ x₁ x₁') := hrelT
    have hmem : φ ⟨t, htStab₀⟩ ∈
        ((socTorus H Γ x₀ x₁ x₁').subgroupOf (MulAction.stabilizer H x₀)).map φ := by
      refine Subgroup.mem_map_of_mem φ ?_
      rw [Subgroup.mem_subgroupOf]
      exact ht
    exact Odd.of_dvd_nat
      (by rw [hcard]; exact (hL x₀).torusOdd x₁ x₁' h1 h1' h11)
      (Subgroup.orderOf_dvd_natCard _ hmem)
  have hφa₀Odd : Odd (orderOf (φ ⟨a₀, ha₀Stab⟩)) := by
    rw [hφa₀]
    exact hφtOdd
  obtain ⟨m, hmodd, hmφ⟩ := exists_odd_pow_map_eq φ ⟨a₀, ha₀Stab⟩ hφa₀Odd
  let a : H := ((⟨a₀, ha₀Stab⟩ ^ m : ↥(MulAction.stabilizer H x₀)) : H)
  have haStab₀ : a ∈ MulAction.stabilizer H x₀ :=
    ((⟨a₀, ha₀Stab⟩ : ↥(MulAction.stabilizer H x₀)) ^ m).2
  have haOdd : Odd (orderOf a) := by
    simpa [a] using hmodd
  have hφa : φ ⟨a, haStab₀⟩ = φ ⟨t, htStab₀⟩ := by
    have h : (⟨a, haStab₀⟩ : ↥(MulAction.stabilizer H x₀)) =
        ⟨a₀, ha₀Stab⟩ ^ m := Subtype.ext rfl
    rw [h, hmφ, hφa₀]
  have haFix₀ : a • x₀ = x₀ := MulAction.mem_stabilizer_iff.mp haStab₀
  have haFix₁ : a • x₁ = x₁ := by
    have hperm := congrArg
      (fun p : Equiv.Perm {w : V // Γ.Adj x₀ w} => p ⟨x₁, h1⟩) hφa
    rw [localPermHom_apply, localPermHom_apply] at hperm
    have hval := congrArg Subtype.val hperm
    simpa [MulAction.mem_stabilizer_iff.mp htStab₁] using hval
  have haFix₁' : a • x₁' = x₁' := by
    have hperm := congrArg
      (fun p : Equiv.Perm {w : V // Γ.Adj x₀ w} => p ⟨x₁', h1'⟩) hφa
    rw [localPermHom_apply, localPermHom_apply] at hperm
    have hval := congrArg Subtype.val hperm
    simpa [MulAction.mem_stabilizer_iff.mp htStab₁'] using hval
  have haU : a ∈ U := by
    have h := Subgroup.pow_mem U ha₀U m
    simpa [a, Subgroup.coe_pow] using h
  have haCentP : a ∈ Subgroup.centralizer (P : Set H) :=
    (Subgroup.le_centralizer_iff.mp hPcent) haU
  have hK₁ : Subgroup.zpowers a ≤
      MulAction.stabilizer H x₁ ⊓ MulAction.stabilizer H x₀ := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact MulAction.mem_stabilizer_iff.mpr haFix₁
    · exact MulAction.mem_stabilizer_iff.mpr haFix₀
  have hrel₁ : Odd ((fixingSubgroup H (Γ.neighborSet x₁)).relIndex
      (Subgroup.zpowers a)) := by
    have hcard : Nat.card (Subgroup.zpowers a) = orderOf a := Nat.card_zpowers a
    exact Odd.of_dvd_nat (by rw [hcard]; exact haOdd) (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨x₂, hx₁x₂, hx₂x₀, hx₂fix⟩ :=
    (hL x₁).oddFix x₀ h1.symm (Subgroup.zpowers a) hK₁ hrel₁
  have haFix₂ : a • x₂ = x₂ := hx₂fix a (Subgroup.mem_zpowers a)
  have hK₂ : Subgroup.zpowers a ≤
      MulAction.stabilizer H x₂ ⊓ MulAction.stabilizer H x₁ := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact MulAction.mem_stabilizer_iff.mpr haFix₂
    · exact MulAction.mem_stabilizer_iff.mpr haFix₁
  have hrel₂ : Odd ((fixingSubgroup H (Γ.neighborSet x₂)).relIndex
      (Subgroup.zpowers a)) := by
    have hcard : Nat.card (Subgroup.zpowers a) = orderOf a := Nat.card_zpowers a
    exact Odd.of_dvd_nat (by rw [hcard]; exact haOdd) (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨w, hx₂w, hwx₁, hwfix⟩ :=
    (hL x₂).oddFix x₁ hx₁x₂.symm (Subgroup.zpowers a) hK₂ hrel₂
  have haFixw : a • w = w := hwfix a (Subgroup.mem_zpowers a)
  obtain ⟨u, hx₀u, hu₁⟩ := hne x₀ x₁ h1
  obtain ⟨v, huv, hvx₀⟩ := hne u x₀ hx₀u.symm
  let q : GPath Γ 4 := path5 v u x₀ x₁ x₂ huv.symm hx₀u.symm h1 hx₁x₂
  have hqnb : q.NoBack :=
    path5_noBack huv.symm hx₀u.symm h1 hx₁x₂ hvx₀ hu₁ hx₂x₀.symm
  have hq2 : q 2 = x₀ := by simp [q, path5]
  have hq3 : q 3 = x₁ := by simp [q, path5]
  have hq4 : q 4 = x₂ := by simp [q, path5]
  have hRroot : IsRootAt H Γ x₂ x₁ (pathRootGroup H Γ q) := by
    have h := isRootAt_pathRootGroup (n := 4) (by norm_num) hM hW hne hval
      (fun z => (hL z).kernel_le) hqnb
    rw [hq4, hq3] at h
    exact h
  have hPleQ : P ≤ secondKernel H Γ x₀ := kernelCenter_le_secondKernel
  have hZle : P ≤ MulAction.stabilizer H x₂ ⊓ MulAction.stabilizer H x₁ := by
    intro z hz
    have hzQ := mem_secondKernel_iff.mp (hPleQ hz)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.2 x₁ h1 x₂ hx₁x₂
    · rw [MulAction.mem_stabilizer_iff]
      exact hzQ.1 x₁ h1
  let p : GPath Γ 4 := path5 u x₀ x₁ x₂ w hx₀u.symm h1 hx₁x₂ hx₂w
  have hpnb : p.NoBack :=
    path5_noBack hx₀u.symm h1 hx₁x₂ hx₂w hu₁ hx₂x₀.symm hwx₁.symm
  have hp2 : p 2 = x₁ := by simp [p, path5]
  have hp3 : p 3 = x₂ := by simp [p, path5]
  have hZconj : ∀ b ∈ GPath.stabPath (H := H) p, ∀ z ∈ P, b * z * b⁻¹ ∈ P := by
    intro b hb z hz
    have hb0 : b • x₀ = x₀ := by
      have h := (GPath.mem_stabPath_iff.mp hb) 1 (by norm_num)
      simpa [p, path5] using h
    have hb1 : b • x₁ = x₁ := by
      have h := (GPath.mem_stabPath_iff.mp hb) 2 (by norm_num)
      simpa [p, path5] using h
    exact kernelCenter_conj_mem hb0 hb1 hz
  have hTN : IsTorusNormalAt H Γ x₂ x₁ P := by
    have h := isTorusNormalAt_of_stabPath_conj hM hne (fun z => (hL z).kernel_le)
      (Z := P) hpnb (by simpa [hp3] using hZle.trans inf_le_left) hZconj
    simpa [hp3, hp2] using h
  have hcomm : ⁅pathRootGroup H Γ q, P⁆ ≤
      fixingSubgroup H (Γ.neighborSet x₂) := by
    rw [Subgroup.commutator_le]
    intro r hr z hz
    have hzU : z ∈ edgeUnion H Γ x₀ x₁ := kernelCenter_le_edgeUnion hz
    have hzC : z ∈ Subgroup.centralizer (edgeUnion H Γ x₀ x₁ : Set H) :=
      kernelCenter_centralizes hz
    have hrU : r ∈ edgeUnion H Γ x₀ x₁ :=
      pathRootGroup_le_edgeUnion_two_three hq2 hq3 hr
    have hcomm' : r * z = z * r := (Subgroup.mem_centralizer_iff.mp hzC) r hrU
    have hone : ⁅r, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm'
    rw [hone]
    exact Subgroup.one_mem _
  have hnot : ¬ P ≤ fixingSubgroup H (Γ.neighborSet x₂) := by
    intro hle
    refine kernelCenter_ne_bot hW hval hL h1 h2 ?_
    rw [eq_bot_iff]
    intro z hz
    have hzQ : z ∈ secondKernel H Γ x₀ := kernelCenter_le_secondKernel hz
    have hzF : z ∈ fixingSubgroup H (Γ.neighborSet x₂) := hle hz
    have hmem : z ∈ secondKernel H Γ x₀ ⊓ fixingSubgroup H (Γ.neighborSet x₂) :=
      Subgroup.mem_inf.mpr ⟨hzQ, hzF⟩
    rw [secondKernel_inf_fixingSubgroup_eq_bot hW hne h1 hx₁x₂ hx₂x₀] at hmem
    simpa using hmem
  obtain ⟨g, -, hgx₀⟩ := hloc x₁ x₀ x₂ h1.symm hx₁x₂
  have hCx : CenterFacts H Γ x₂ e := by
    have h := hC g
    rwa [hgx₀] at h
  have hzpow : ⁅Subgroup.zpowers a, P⁆ ≤
      fixingSubgroup H (Γ.neighborSet x₂) := by
    rw [Subgroup.commutator_le]
    intro y hy z hz
    have hycent : y ∈ Subgroup.centralizer (P : Set H) :=
      (Subgroup.zpowers_le.mpr haCentP) hy
    have hcomm' : y * z = z * y := ((Subgroup.mem_centralizer_iff.mp hycent) z hz).symm
    have hone : ⁅y, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm'
    rw [hone]
    exact Subgroup.one_mem _
  have haTriple : a ∈ MulAction.stabilizer H x₂ ⊓ MulAction.stabilizer H x₁ ⊓
      MulAction.stabilizer H w := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr haFix₂
    · exact MulAction.mem_stabilizer_iff.mpr haFix₁
    · exact MulAction.mem_stabilizer_iff.mpr haFixw
  have haeG1 : a ^ e ∈ fixingSubgroup H (Γ.neighborSet x₂) :=
    hCx.centralizer x₁ w hx₁x₂.symm hx₂w hwx₁.symm (pathRootGroup H Γ q) P hRroot
      hZle hTN hcomm hnot a haTriple haOdd hzpow
  have haeStab₀ : a ^ e ∈ MulAction.stabilizer H x₀ :=
    Subgroup.pow_mem _ haStab₀ e
  have hteStab₀ : t ^ e ∈ MulAction.stabilizer H x₀ :=
    Subgroup.pow_mem _ htStab₀ e
  have hφae : φ ⟨a ^ e, haeStab₀⟩ = φ ⟨t ^ e, hteStab₀⟩ := by
    have h1'' : (⟨a ^ e, haeStab₀⟩ : ↥(MulAction.stabilizer H x₀)) =
        ⟨a, haStab₀⟩ ^ e := Subtype.ext rfl
    have h2'' : (⟨t ^ e, hteStab₀⟩ : ↥(MulAction.stabilizer H x₀)) =
        ⟨t, htStab₀⟩ ^ e := Subtype.ext rfl
    calc
      φ ⟨a ^ e, haeStab₀⟩ = φ ((⟨a, haStab₀⟩ : ↥(MulAction.stabilizer H x₀)) ^ e) := by
        rw [h1'']
      _ = (φ ⟨a, haStab₀⟩) ^ e := map_pow _ _ _
      _ = (φ ⟨t, htStab₀⟩) ^ e := by rw [hφa]
      _ = φ ((⟨t, htStab₀⟩ : ↥(MulAction.stabilizer H x₀)) ^ e) :=
        (map_pow _ _ _).symm
      _ = φ ⟨t ^ e, hteStab₀⟩ := by rw [h2'']
  have hcong : a ^ e * (t ^ e)⁻¹ ∈ fixingSubgroup H (Γ.neighborSet x₀) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hmemstab : a ^ e * (t ^ e)⁻¹ ∈ MulAction.stabilizer H x₀ :=
      Subgroup.mul_mem _ haeStab₀ (Subgroup.inv_mem _ hteStab₀)
    have hφ1 : φ ⟨a ^ e * (t ^ e)⁻¹, hmemstab⟩ = 1 := by
      have h : (⟨a ^ e * (t ^ e)⁻¹, hmemstab⟩ :
          ↥(MulAction.stabilizer H x₀)) =
          ⟨a ^ e, haeStab₀⟩ * (⟨t ^ e, hteStab₀⟩)⁻¹ := Subtype.ext rfl
      rw [h, map_mul, map_inv, hφae, mul_inv_cancel]
    have hperm := congrArg
      (fun q : Equiv.Perm {w : V // Γ.Adj x₀ w} => q ⟨v, hv⟩) hφ1
    rw [localPermHom_apply] at hperm
    exact congrArg Subtype.val hperm
  have haeOdd : Odd (orderOf (a ^ e)) :=
    Odd.of_dvd_nat haOdd (orderOf_pow_dvd e)
  have haeFix₀ : a ^ e • x₀ = x₀ :=
    smul_eq_self_of_mem_zpowers
      (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) e) haFix₀
  have haeFix₁ : a ^ e • x₁ = x₁ :=
    smul_eq_self_of_mem_zpowers
      (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) e) haFix₁
  have haeFix₁' : a ^ e • x₁' = x₁' :=
    smul_eq_self_of_mem_zpowers
      (Subgroup.pow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) e) haFix₁'
  exact ⟨x₂, hx₁x₂, hx₂x₀, a ^ e, haeG1, haeFix₀, haeFix₁, haeFix₁', haeOdd, hcong⟩

theorem not_isPGroup_of_secondKernel_ne_bot [Finite H] (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4) (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hval : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ,
      Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e)
    (hloc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v)
    (hL : ∀ z, LocalFacts H Γ z) (hR : ∀ z, RootFacts H Γ 4 z)
    (hC : ∀ z, CenterFacts H Γ z 1) {p : GPath Γ 2} (hp : p.NoBack)
    (h2 : secondKernel H Γ (p 0) ≠ ⊥) :
    ¬ IsPGroup 2 ↥(fixingSubgroup H (Γ.neighborSet (p 2))) := by
  classical
  have h01 : Γ.Adj (p 0) (p 1) := by simpa using p.adj 0 (by norm_num)
  obtain ⟨x₁', hp0x₁', hx₁'p1, -⟩ := h3 (p 0) (p 1) (p 1) h01 h01
  let T := socTorus H Γ (p 0) (p 1) x₁'
  obtain ⟨u, hp0u, hup1, hux₁'⟩ := h3 (p 0) (p 1) x₁' h01 hp0x₁'
  have hTnot : ¬ T ≤ fixingSubgroup H (Γ.neighborSet (p 0)) := by
    intro hle
    have hfix : ∀ t ∈ T, t • u = u := by
      intro t ht
      exact (mem_fixingSubgroup_iff H).mp (hle ht) u hp0u
    have h := (hL (p 0)).torusFix (p 1) x₁' u h01 hp0x₁'
      hx₁'p1.symm hp0u hfix
    rcases h with h | h
    · exact hup1 h
    · exact hux₁' h
  obtain ⟨t, htT, htF⟩ := Set.not_subset.mp hTnot
  obtain ⟨x₂, hx₁x₂, hx₂p0, a, haG1, hap0, hap1, hax₁', haOdd, hacong⟩ :=
    exists_odd_mem_fixingSubgroup_of_secondKernel_ne_bot (e := 1) hM hW hne hval hloc
      hL hR (x₀ := p 0) (x₁ := p 1) (x₁' := x₁') (t := t)
      (fun g => hC (g • p 0)) h2 h01 hp0x₁' hx₁'p1.symm htT
  have ha_ne : a ≠ 1 := by
    intro ha1
    apply htF
    have h : t⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 0)) := by
      simpa [ha1] using hacong
    simpa using Subgroup.inv_mem _ h
  let q : GPath Γ 2 := path3 (p 0) (p 1) x₂ h01 hx₁x₂
  have hqnb : q.NoBack := path3_noBack h01 hx₁x₂ hx₂p0.symm
  have hq0 : q 0 = p 0 := by simp [q, path3]
  have hq1 : q 1 = p 1 := by simp [q, path3]
  have hp2ne : p 2 ≠ p 0 := (hp 0 (by norm_num)).symm
  have hy : Γ.Adj (q 1) x₂ := by rw [hq1]; exact hx₁x₂
  have hy' : Γ.Adj (q 1) (p 2) := by rw [hq1]; exact p.adj 1 (by norm_num)
  have hyne : x₂ ≠ q (1 - 1) := by simpa [hq0] using hx₂p0
  have hy'ne : p 2 ≠ q (1 - 1) := by simpa [hq0] using hp2ne
  obtain ⟨g, -, -, hgx₂⟩ := exists_smul_of_mem_stabPath_take_fixing
    (n := 4) (by norm_num) hM hne (s := 2) (p := q) hqnb (i := 1)
    (by norm_num) (by norm_num) (by norm_num) hy hy' hyne hy'ne
  let a' : H := g * a * g⁻¹
  have ha'G1 : a' ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
    have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g x₂
    rw [hgx₂] at h
    have hmem : (MulAut.conj g) a ∈ (fixingSubgroup H (Γ.neighborSet x₂)).map
        (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ haG1
    rw [← h] at hmem
    simpa [a', MulAut.conj_apply] using hmem
  have ha'Odd : Odd (orderOf a') := by
    have h : orderOf a' = orderOf a := by
      simpa [a', MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a
    rw [h]
    exact haOdd
  have ha'ne : a' ≠ 1 := by
    intro h
    apply ha_ne
    have h' : g * a * g⁻¹ = 1 := by simpa [a'] using h
    have : a = 1 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h']
        _ = 1 := by simp
    exact this
  intro hP
  let A : Subgroup H := fixingSubgroup H (Γ.neighborSet (p 2))
  have horder : orderOf a' = orderOf (⟨a', ha'G1⟩ : ↥A) :=
    Subgroup.orderOf_coe (⟨a', ha'G1⟩ : ↥A)
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨a', ha'G1⟩ : ↥A)
  have hk' : orderOf a' = 2 ^ k := horder.trans hk
  have hoddpow : Odd (2 ^ k) := by
    rw [← hk']
    exact ha'Odd
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ j =>
      exfalso
      apply Nat.not_odd_iff_even.mpr ?_ hoddpow
      rw [pow_succ, mul_comm]
      exact even_two_mul (2 ^ j)
  have hone : a' = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [hk', hk0, pow_zero]
  exact ha'ne hone

end CFSG.Quasithin.Stroth.WeissDelta

end
