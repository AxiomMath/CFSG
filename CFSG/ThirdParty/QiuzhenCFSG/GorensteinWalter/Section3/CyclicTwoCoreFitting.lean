module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem mem_centralizerIn_iff_fitting
    {G : Type u} [Group G]
    (X : Subgroup G) (s x : G) :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ s * x * s⁻¹ = x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
    rw [hcomm]
    group
  · rintro ⟨hxX, hxfix⟩
    refine ⟨hxX, ?_⟩
    change x ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxfix)

/-! ## The Sylow `p`-subgroups of the two centralizers

In the cyclic branch we have `U = F(U)·B` with `B = C_U(S)`.  For the
oriented pair `(t₁, t₂)` and `P = O_p(U)` (centralized by `t₁`, inverted by
`t₂`), the source asserts `P₂ ∈ Syl_p(C_U(V₂))` and `P₁ = P·P₂ ∈
Syl_p(C_U(V₁))`.  The lemmas below assemble the nilpotent decomposition
`F(U) = O_p(U) × O_{p'}(F(U))` and the centralizer product formula.
-/

/-- `O_p(F(U)) = O_p(U)` inside `U`. -/
public theorem pCore_fittingSubgroup_map_eq_pCore
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    (pCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype = pCore p U := by
  classical
  let F : Subgroup U := fittingSubgroup U
  have hF_char : F.Characteristic := inferInstance
  have hCore_char : (pCore p F).Characteristic := inferInstance
  apply le_antisymm
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, hf, hx⟩
    have hnorm : ((pCore p F).map F.subtype).Normal := by
      refine ⟨?_⟩
      intro n hn g
      rcases (Subgroup.mem_map).1 hn with ⟨yF, hyF, rfl⟩
      let φ : U ≃* U := MulAut.conj g
      have hmapF : F.map φ.toMonoidHom = F := by
        apply le_antisymm
        · intro y hy
          rcases (Subgroup.mem_map).1 hy with ⟨f, hf, rfl⟩
          have hfix : F.comap φ.toMonoidHom = F :=
            (Subgroup.characteristic_iff_comap_eq.mp hF_char) φ
          exact Subgroup.mem_comap.mp (by rw [hfix]; exact hf)
        · intro y hy
          have hfix : F.comap φ.symm.toMonoidHom = F :=
            (Subgroup.characteristic_iff_comap_eq.mp hF_char) φ.symm
          have hy' : (φ.symm y : U) ∈ F :=
            Subgroup.mem_comap.mp (by rw [hfix]; exact hy)
          refine Subgroup.mem_map.mpr ⟨φ.symm y, hy', ?_⟩
          simp
      let ψ : F ≃* F :=
        (MulEquiv.subgroupMap φ F).trans (MulEquiv.subgroupCongr hmapF)
      have hyF' : ψ yF ∈ pCore p F := by
        have hfix : (pCore p F).comap ψ.toMonoidHom = pCore p F :=
          (Subgroup.characteristic_iff_comap_eq.mp hCore_char) ψ
        exact Subgroup.mem_comap.mp (by rw [hfix]; exact hyF)
      exact Subgroup.mem_map.mpr ⟨ψ yF, hyF', by
        change (g : U) * (yF : U) * (g : U)⁻¹ = (g : U) * (yF : U) * (g : U)⁻¹
        rfl⟩
    have hpgroup : IsPGroup p ((pCore p F).map F.subtype) :=
      (pCore_isPGroup (p := p) (G := F)).map F.subtype
    rw [pCore]
    exact le_sSup (s := {K : Subgroup U | K.Normal ∧ IsPGroup p K})
      (a := (pCore p F).map F.subtype) ⟨hnorm, hpgroup⟩
      ((Subgroup.mem_map).2 ⟨f, hf, hx⟩)
  · intro x hx
    have hleF : pCore p U ≤ F := pCore_le_fitting (G := U) p
    have hnormalF : ((pCore p U).subgroupOf F).Normal := by
      exact (pCore_normal (p := p) (G := U)).subgroupOf F
    have hpgroupF : IsPGroup p ((pCore p U).subgroupOf F) := by
      exact (pCore_isPGroup (p := p) (G := U)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hleF).symm
    have hsub : (pCore p U).subgroupOf F ≤ pCore p F :=
      le_sSup ⟨hnormalF, hpgroupF⟩
    change x ∈ (pCore p F).map F.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hleF hx⟩, ?_, rfl⟩
    exact hsub (Subgroup.mem_subgroupOf.mpr hx)

/-- `O_p(F(U)) ⊓ O_{p'}(F(U)) = 1` inside `U`. -/
public theorem pCore_inf_pPrimeCore_fittingSubgroup_eq_bot
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    (pCore p (fittingSubgroup U)) ⊓
        (pPrimeCore p (fittingSubgroup U)) = ⊥ := by
  classical
  let F : Subgroup U := fittingSubgroup U
  apply le_bot_iff.mp
  intro x hx
  have hxP : x ∈ pCore p F := (Subgroup.mem_inf.mp hx).1
  have hxQ : x ∈ pPrimeCore p F := (Subgroup.mem_inf.mp hx).2
  have hcop : Nat.Coprime (Nat.card (pCore p F))
      (Nat.card (pPrimeCore p F)) := by
    rcases (pCore_isPGroup (p := p) (G := F)).exists_card_eq with ⟨n, hn⟩
    have hQcop : Nat.Coprime p (Nat.card (pPrimeCore p F)) :=
      pPrimeCore_coprime_card (p := p) (G := F)
    rw [hn]
    exact hQcop.pow_left n
  have hdisj : Disjoint (pCore p F) (pPrimeCore p F) :=
    Subgroup.disjoint_of_coprime_natCard hcop
  exact hdisj.le_bot ⟨hxP, hxQ⟩

/-- The ambient `O_p(U)` centralizes the ambient `O_{p'}(F(U))`. -/
public theorem qCoreOf_centralizes_pPrimeCore_fittingSubgroup
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    qCoreOf U p ≤ Subgroup.centralizer
      ((((pPrimeCore p (fittingSubgroup U)).map
          (fittingSubgroup U).subtype).map U.subtype) : Set G) := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let φ : F0 →* G := U.subtype.comp F0.subtype
  let P0 : Subgroup F0 := pCore p F0
  let Q0 : Subgroup F0 := pPrimeCore p F0
  let Q : Subgroup G := ((Q0.map F0.subtype).map U.subtype)
  have hP0map : P0.map φ = qCoreOf U p := by
    dsimp [φ]
    rw [← Subgroup.map_map (K := P0) U.subtype F0.subtype]
    rw [pCore_fittingSubgroup_map_eq_pCore U p]
    rfl
  have hQ0map : Q0.map φ = Q := by
    dsimp [φ, Q]
    rw [← Subgroup.map_map (K := Q0) U.subtype F0.subtype]
  have hinf0 : P0 ⊓ Q0 = ⊥ :=
    pCore_inf_pPrimeCore_fittingSubgroup_eq_bot U p
  have hdisj0 : Disjoint P0 Q0 :=
    disjoint_iff_inf_le.mpr (le_of_eq hinf0)
  have hcomm0 : ∀ x y : F0, x ∈ P0 → y ∈ Q0 → Commute x y :=
    Subgroup.commute_of_normal_of_disjoint P0 Q0 inferInstance inferInstance hdisj0
  intro p hp q hq
  rw [← hP0map] at hp
  rcases Subgroup.mem_map.mp hp with ⟨p0, hp0, rfl⟩
  change q ∈ Q at hq
  rw [← hQ0map] at hq
  rcases Subgroup.mem_map.mp hq with ⟨q0, hq0, rfl⟩
  exact ((hcomm0 p0 q0 hp0 hq0).map φ).symm

/-- In a nilpotent group, the `p`-core and the `p'`-core generate the whole
group (the Sylow-core decomposition). -/
public theorem top_le_pCore_sup_pPrimeCore
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQnil : Group.IsNilpotent Q) :
    (⊤ : Subgroup Q) ≤ pCore p Q ⊔ pPrimeCore p Q := by
  classical
  have : Group.IsNilpotent Q := hQnil
  have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup Q)) := by
    exact Group.nilpotent_of_mulEquiv
      (G := Q) (G' := ↥(⊤ : Subgroup Q))
      (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q))
  have hTop_le_iSup :
      (⊤ : Subgroup Q) ≤ ⨆ q : (Nat.card Q).primeFactors.attach, pCore q.1 Q :=
    normal_nilpotent_le_sup_pCore
      (G := Q) (N := (⊤ : Subgroup Q)) (hN := inferInstance) hnilTop
  refine hTop_le_iSup.trans ?_
  refine iSup_le ?_
  intro q
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := Q) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 Q)) := by
      rw [hn]
      have hpq : p ≠ q.1 := by
        intro h
        exact hqp h.symm
      exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact (le_sSup (s := {K : Subgroup Q | K.Normal ∧ Nat.Coprime p (Nat.card K)})
      (a := pCore q.1 Q) ⟨inferInstance, hcop⟩).trans le_sup_right



/-- `F(U) = O_p(U) ⊔ O_{p'}(F(U))` in the ambient group `G`. -/
public theorem fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    fittingSubgroupOf U =
      qCoreOf U p ⊔
        ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let P0 : Subgroup U := (pCore p F0).map F0.subtype
  let F'0 : Subgroup U := (pPrimeCore p F0).map F0.subtype
  have hP0 : P0 = pCore p U := pCore_fittingSubgroup_map_eq_pCore U p
  have hdecomp : F0 = P0 ⊔ F'0 := by
    apply le_antisymm
    · -- F0 ≤ P0 ⊔ F'0
      have htop : (⊤ : Subgroup F0) ≤ pCore p F0 ⊔ pPrimeCore p F0 :=
        top_le_pCore_sup_pPrimeCore (Q := F0) inferInstance
      have hmap : (⊤ : Subgroup F0).map F0.subtype ≤
          (pCore p F0 ⊔ pPrimeCore p F0).map F0.subtype :=
        Subgroup.map_mono htop
      have htopmap : (⊤ : Subgroup F0).map F0.subtype = F0 := by
        simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := F0))
      have hsupmap : (pCore p F0 ⊔ pPrimeCore p F0).map F0.subtype =
          P0 ⊔ F'0 := by
        simp [P0, F'0, Subgroup.map_sup]
      intro x hx
      have hx' : x ∈ (⊤ : Subgroup F0).map F0.subtype := by
        rw [htopmap]
        exact hx
      have hx'' : x ∈ (pCore p F0 ⊔ pPrimeCore p F0).map F0.subtype := hmap hx'
      rw [hsupmap] at hx''
      exact hx''
    · -- P0 ⊔ F'0 ≤ F0
      exact sup_le (Subgroup.map_subtype_le (H := F0) (pCore p F0))
        (Subgroup.map_subtype_le (H := F0) (pPrimeCore p F0))
  -- map through U.subtype
  calc
    fittingSubgroupOf U = F0.map U.subtype := rfl
    _ = (P0 ⊔ F'0).map U.subtype := by rw [hdecomp]
    _ = P0.map U.subtype ⊔ F'0.map U.subtype := Subgroup.map_sup _ _ _
    _ = qCoreOf U p ⊔ F'0.map U.subtype := by
      simp [P0, hP0, qCoreOf]
    _ = qCoreOf U p ⊔
        ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype := rfl

/-- Inside `F(U)`, the centralizer of `t` splits as the `p`-core plus the
`p'`-part of the centralizer, provided the `p`-core is centralized by `t`. -/
public theorem centralizerIn_fittingSubgroupOf_eq_pCore_sup_inter_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (t : G)
    (hPleC : qCoreOf U p ≤ centralizerIn (fittingSubgroupOf U) t) :
    centralizerIn (fittingSubgroupOf U) t =
      qCoreOf U p ⊔
        (centralizerIn (fittingSubgroupOf U) t ⊓
          ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype) := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let φ : F0 →* G := U.subtype.comp F0.subtype
  let F : Subgroup G := fittingSubgroupOf U
  let P : Subgroup G := qCoreOf U p
  let Q : Subgroup G :=
    ((pPrimeCore p F0).map F0.subtype).map U.subtype
  let A : Subgroup G := centralizerIn F t
  let P0 : Subgroup F0 := pCore p F0
  let Q0 : Subgroup F0 := pPrimeCore p F0
  have hP0map : P0.map φ = P := by
    dsimp [φ]
    rw [← Subgroup.map_map (K := P0) U.subtype F0.subtype]
    rw [pCore_fittingSubgroup_map_eq_pCore U p]
    rfl
  have hQ0map : Q0.map φ = Q := by
    dsimp [φ]
    rw [← Subgroup.map_map (K := Q0) U.subtype F0.subtype]
  have hQleF : Q ≤ F := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    have hyF0 : y ∈ F0 := Subgroup.map_subtype_le (H := F0) (pPrimeCore p F0) hy
    exact Subgroup.mem_map.mpr ⟨y, hyF0, rfl⟩
  have htop0 : (⊤ : Subgroup F0) ≤ P0 ⊔ Q0 :=
    top_le_pCore_sup_pPrimeCore (Q := F0) inferInstance
  have hinf0 : P0 ⊓ Q0 = ⊥ :=
    pCore_inf_pPrimeCore_fittingSubgroup_eq_bot U p
  have hdisj0 : Disjoint P0 Q0 := by
    exact disjoint_iff_inf_le.mpr (le_of_eq hinf0)
  have hcomm0 : ∀ x y : F0, x ∈ P0 → y ∈ Q0 → Commute x y :=
    Subgroup.commute_of_normal_of_disjoint P0 Q0 inferInstance inferInstance hdisj0
  apply le_antisymm
  · intro x hxA
    have hxF : x ∈ F := (mem_centralizerIn_iff_fitting F t x).mp hxA |>.1
    have hxfix : t * x * t⁻¹ = x :=
      (mem_centralizerIn_iff_fitting F t x).mp hxA |>.2
    have hxU : x ∈ U := fittingSubgroupOf_le U hxF
    let xU : U := ⟨x, hxU⟩
    have hxU0 : xU ∈ (F0 : Subgroup U) := by
      rcases (Subgroup.mem_map).1 hxF with ⟨u, hu, hxeq⟩
      have hxUeq : xU = u := by
        apply Subtype.ext
        exact hxeq.symm
      simpa [hxUeq] using hu
    let x0 : F0 := ⟨xU, hxU0⟩
    have hx0sup : x0 ∈ P0 ⊔ Q0 := htop0 (by trivial)
    have hprod : (↑(P0 ⊔ Q0) : Set F0) = (P0 : Set F0) * (Q0 : Set F0) :=
      Subgroup.mul_normal P0 Q0
    have hx0prod : (x0 : F0) ∈ (P0 : Set F0) * (Q0 : Set F0) := by
      rw [← hprod]
      exact hx0sup
    rcases hx0prod with ⟨p0, hp0, q0, hq0, hx0eq⟩
    let p : G := (φ p0 : G)
    let q : G := (φ q0 : G)
    have hpP : p ∈ P := by
      rw [← hP0map]
      exact Subgroup.mem_map.mpr ⟨p0, hp0, rfl⟩
    have hqQ : q ∈ Q := by
      rw [← hQ0map]
      exact Subgroup.mem_map.mpr ⟨q0, hq0, rfl⟩
    have hxeq : p * q = x := by
      have hφ : (φ (p0 * q0) : G) = x := by
        have hx0val : (φ x0 : G) = x := by
          simp [φ, x0, xU]
        simpa [hx0eq.symm] using hx0val
      simpa [p, q, map_mul] using hφ
    have hcommG : Commute p q := by
      have hc := hcomm0 p0 q0 hp0 hq0
      exact hc.map φ
    have hpA : p ∈ A := hPleC hpP
    have hpFix : t * p * t⁻¹ = p :=
      (mem_centralizerIn_iff_fitting F t p).mp hpA |>.2
    have hpInvFix : t * p⁻¹ * t⁻¹ = p⁻¹ := by
      calc
        t * p⁻¹ * t⁻¹ = (t * p * t⁻¹)⁻¹ := by group
        _ = p⁻¹ := by rw [hpFix]
    have hpInvComm : t * p⁻¹ = p⁻¹ * t := by
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hpInvFix)
    have hpq' : p⁻¹ * x = q := by
      calc
        p⁻¹ * x = p⁻¹ * (p * q) := by rw [hxeq]
        _ = q := by group
    have hqF : q ∈ F := hQleF hqQ
    have hqFix : t * q * t⁻¹ = q := by
      calc
        t * q * t⁻¹ = t * (p⁻¹ * x) * t⁻¹ := by rw [← hpq']
        _ = p⁻¹ * (t * x * t⁻¹) := by
          calc
            t * (p⁻¹ * x) * t⁻¹ = (t * p⁻¹) * x * t⁻¹ := by group
            _ = (p⁻¹ * t) * x * t⁻¹ := by rw [hpInvComm]
            _ = p⁻¹ * (t * x * t⁻¹) := by group
        _ = p⁻¹ * x := by rw [hxfix]
        _ = q := hpq'
    have hqA : q ∈ A :=
      (mem_centralizerIn_iff_fitting F t q).2 ⟨hqF, hqFix⟩
    have hxsup : x ∈ P ⊔ (A ⊓ Q) := by
      have hm : p * q ∈ P ⊔ (A ⊓ Q) :=
        Subgroup.mul_mem_sup hpP ⟨hqA, hqQ⟩
      simpa [hxeq] using hm
    exact hxsup
  · refine sup_le hPleC ?_
    intro x hx
    exact (Subgroup.mem_inf.mp hx).1

/-- A `p`-subgroup of `F(U)` lies in the ambient `p`-core `O_p(U)`. -/
public theorem pSubgroup_le_qCoreOf_of_le_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (X : Subgroup G) (hXp : IsPGroup p X) (hXF : X ≤ fittingSubgroupOf U) :
    X ≤ qCoreOf U p := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let φ : F0 →* G := U.subtype.comp F0.subtype
  have hφinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let X0 : Subgroup F0 := X.comap φ
  have hX0p : IsPGroup p X0 := hXp.comap_of_injective φ hφinj
  have hnil : Group.IsNilpotent F0 := by infer_instance
  have hX0core : X0 ≤ pCore p F0 := by
    intro x hx
    obtain ⟨Q, hX0Q⟩ := IsPGroup.exists_le_sylow (G := F0) (p := p) hX0p
    have hQnorm : (Q : Subgroup F0).Normal :=
      Group.IsNilpotent.sylow_normal hnil p Q
    have hQcore : (Q : Subgroup F0) ≤ pCore p F0 :=
      le_sSup ⟨hQnorm, Q.isPGroup'⟩
    exact hQcore (hX0Q hx)
  have hFleU : fittingSubgroupOf U ≤ U := fittingSubgroupOf_le U
  intro x hx
  have hxU : x ∈ U := hFleU (hXF hx)
  let xU : U := ⟨x, hxU⟩
  have hxU0 : xU ∈ (F0 : Subgroup U) := by
    rcases (Subgroup.mem_map).1 (hXF hx) with ⟨u, hu, hxeq⟩
    have hxUeq : xU = u := by
      apply Subtype.ext
      exact hxeq.symm
    simpa [hxUeq] using hu
  let xU0 : F0 := ⟨xU, hxU0⟩
  have hxU0X : xU0 ∈ X0 := by
    rw [Subgroup.mem_comap]
    simpa [φ] using hx
  have hxUcore : xU0 ∈ pCore p F0 := hX0core hxU0X
  have hxU0P : xU ∈ (pCore p F0).map F0.subtype :=
    (Subgroup.mem_map).2 ⟨xU0, hxUcore, rfl⟩
  have hP0 : (pCore p F0).map F0.subtype = pCore p U :=
    pCore_fittingSubgroup_map_eq_pCore U p
  have hxU : xU ∈ pCore p U := by
    simpa [hP0] using hxU0P
  exact (Subgroup.mem_map).2 ⟨xU, hxU, rfl⟩

/-- A `p`-core element inverted by `t` has no nontrivial fixed points in
`C_{F(U)}(t)`. -/
public theorem pCore_inf_centralizerIn_fittingSubgroupOf_eq_bot_of_inverted
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (t : G) (hodd : Nat.Coprime 2 (Nat.card (qCoreOf U p)))
    (hinv : ∀ x : G, x ∈ qCoreOf U p → t * x * t⁻¹ = x⁻¹) :
    qCoreOf U p ⊓ centralizerIn (fittingSubgroupOf U) t = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro x hx
  have hxP : x ∈ qCoreOf U p := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ centralizerIn (fittingSubgroupOf U) t :=
    (Subgroup.mem_inf.mp hx).2
  have hxfix : t * x * t⁻¹ = x :=
    (mem_centralizerIn_iff_fitting (fittingSubgroupOf U) t x).mp hxC |>.2
  have hxinv : t * x * t⁻¹ = x⁻¹ := hinv x hxP
  have hxinv_eq : x⁻¹ = x := hxinv.symm.trans hxfix
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := by rw [hxinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hordP : orderOf x ∣ Nat.card (qCoreOf U p) :=
    Subgroup.orderOf_dvd_natCard (qCoreOf U p) hxP
  have hord1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hodd hord2 hordP
  exact orderOf_eq_one_iff.mp hord1

/-- If every `p`-element of `O_p(U)` is inverted by `t`, then
`C_{F(U)}(t)` has order coprime to `p`. -/
public theorem centralizerIn_fittingSubgroupOf_card_coprime_of_inverted
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (t : G) (hodd : Nat.Coprime 2 (Nat.card (qCoreOf U p)))
    (hinv : ∀ x : G, x ∈ qCoreOf U p → t * x * t⁻¹ = x⁻¹) :
    Nat.Coprime p (Nat.card (centralizerIn (fittingSubgroupOf U) t)) := by
  classical
  let P : Subgroup G := qCoreOf U p
  let F : Subgroup G := fittingSubgroupOf U
  let A : Subgroup G := centralizerIn F t
  have hAll : ∀ X : Subgroup G, X ≤ A → IsPGroup p X → X = ⊥ := by
    intro X hXA hXp
    have hXF : X ≤ F := hXA.trans (by
      intro x hx
      exact (mem_centralizerIn_iff_fitting F t x).mp hx |>.1)
    have hXP : X ≤ P :=
      pSubgroup_le_qCoreOf_of_le_fittingSubgroupOf U p X hXp hXF
    apply le_bot_iff.mp
    intro x hx
    have hxP : x ∈ P := hXP hx
    have hxCent : x ∈ centralizerIn F t := hXA hx
    exact (le_bot_iff.mpr (pCore_inf_centralizerIn_fittingSubgroupOf_eq_bot_of_inverted
      U p t hodd hinv)) ⟨hxP, hxCent⟩
  by_contra hcop
  have hpdvd : p ∣ Nat.card A := by
    by_contra hnot
    exact hcop ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnot)
  let Q : Sylow p ↥A := default
  have hQne : (Q : Subgroup A) ≠ ⊥ := Sylow.ne_bot_of_dvd_card Q hpdvd
  have hQmapbot : (Q : Subgroup A).map A.subtype = ⊥ := by
    apply hAll ((Q : Subgroup A).map A.subtype) ?_ ?_
    · intro x hx
      rcases (Subgroup.mem_map).1 hx with ⟨a, ha, rfl⟩
      exact a.2
    · exact (Q.isPGroup').map A.subtype
  have hQbot : (Q : Subgroup A) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (Q : Subgroup A))
      (f := A.subtype) A.subtype_injective).mp hQmapbot
  exact hQne hQbot

/-- The `p'`-part of `F(U)` has order coprime to `p`. -/
public theorem pPrimeCore_map_card_coprime
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    Nat.Coprime p (Nat.card
      (((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype)) := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let Q0 : Subgroup F0 := pPrimeCore p F0
  have hQ0cop : Nat.Coprime p (Nat.card Q0) :=
    pPrimeCore_coprime_card (p := p) (G := F0)
  have hcop : Nat.Coprime p (Nat.card ((Q0.map F0.subtype).map U.subtype)) := by
    rw [Subgroup.card_map_of_injective (K := Q0.map F0.subtype) (f := U.subtype)
      U.subtype_injective]
    rw [Subgroup.card_map_of_injective (K := Q0) (f := F0.subtype)
      F0.subtype_injective]
    exact hQ0cop
  change Nat.Coprime p (Nat.card
    (((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype))
  simpa [F0, Q0] using hcop


end CFSG.GorensteinWalter
