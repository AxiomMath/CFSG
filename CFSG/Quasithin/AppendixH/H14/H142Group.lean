module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Open

section PCore

variable {X : Type*} [Group X]

theorem isPGroup_pCoreOf (p : ℕ) (H : Subgroup X) : IsPGroup p (pCoreOf p H) := by
  change IsPGroup p (Subgroup.map H.subtype (pCore p H))
  exact IsPGroup.map (H := pCore p H) (CFSG.pCore_isPGroup (G := ↥H)) H.subtype

theorem pCoreOf_le (p : ℕ) (H : Subgroup X) : pCoreOf p H ≤ H := by
  simpa [pCoreOf] using Subgroup.map_subtype_le (pCore p H)

theorem normal_subgroupOf_pCoreOf (p : ℕ) (H : Subgroup X) :
    ((pCoreOf p H).subgroupOf H).Normal := by
  have h : ((pCore p H).map H.subtype).subgroupOf H = pCore p H := by
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [pCoreOf, h]
  exact CFSG.pCore_normal

theorem le_pCoreOf_of_normal {p : ℕ} {H N : Subgroup X} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hp' : IsPGroup p (N.subgroupOf H) := hp.comap_subtype (K := H)
  have hle : N.subgroupOf H ≤ pCore p H := le_sSup ⟨hN, hp'⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hNH] at hmap
  simpa [pCoreOf] using hmap

theorem pCoreOf_map_conj (p : ℕ) (c : X) (H : Subgroup X) :
    pCoreOf p (H.map (MulAut.conj c).toMonoidHom) =
      (pCoreOf p H).map (MulAut.conj c).toMonoidHom := by
  let e : ↥H ≃* ↥(H.map (MulAut.conj c : X →* X)) := (MulAut.conj c).subgroupMap H
  have hcomp : (H.map (MulAut.conj c : X →* X)).subtype.comp e.toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp H.subtype := by
    ext k
    simp [e, MulEquiv.coe_subgroupMap_apply]
  calc
    pCoreOf p (H.map (MulAut.conj c).toMonoidHom)
        = (pCore p ↥(H.map (MulAut.conj c : X →* X))).map
            (H.map (MulAut.conj c : X →* X)).subtype := rfl
    _ = ((pCore p ↥H).map e.toMonoidHom).map
            (H.map (MulAut.conj c : X →* X)).subtype := by
          rw [← CFSG.pCore_map_iso p e]
    _ = (pCore p ↥H).map
            ((H.map (MulAut.conj c : X →* X)).subtype.comp e.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (pCore p ↥H).map ((MulAut.conj c).toMonoidHom.comp H.subtype) := by rw [hcomp]
    _ = ((pCore p ↥H).map H.subtype).map (MulAut.conj c).toMonoidHom := by
          rw [← Subgroup.map_map]
    _ = (pCoreOf p H).map (MulAut.conj c).toMonoidHom := rfl

theorem pCoreOf_le_of_sylow [Finite X] {H P : Subgroup X} (hPH : P ≤ H) (hP2 : IsPGroup 2 P)
    (hodd : ¬ 2 ∣ (P.subgroupOf H).index) : pCoreOf 2 H ≤ P := by
  let Q : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H
  let P' : Subgroup ↥H := P.subgroupOf H
  have hQeq : Q = pCore 2 ↥H := by
    show ((pCore 2 ↥H).map H.subtype).subgroupOf H = pCore 2 ↥H
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hQp : IsPGroup 2 Q := by
    rw [hQeq]
    exact CFSG.pCore_isPGroup
  haveI hQn : Q.Normal := by
    rw [hQeq]
    exact CFSG.pCore_normal
  have hP'p : IsPGroup 2 P' := hP2.comap_subtype (K := H)
  have hodd' : ¬ 2 ∣ P'.index := hodd
  have hle : Q ≤ P' := by
    have := IsPGroup.le_sylow_of_normal (p := 2) hQp (hP'p.toSylow hodd')
    rwa [IsPGroup.toSylow_coe hP'p hodd'] at this
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (pCoreOf_le 2 H), inf_of_le_left hPH] at hmap
  exact hmap

theorem pCoreOf_eq_of_selfCentralizing_irreducible [Finite X] {M E : Subgroup X} (hEM : E ≤ M)
    (hEn : ∀ g ∈ M, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hE2 : IsPGroup 2 E) (hEne : E ≠ ⊥)
    (hC : ∀ g ∈ M, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hirr : ∀ W : Subgroup X, W ≤ E → W ≠ ⊥ →
      (∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W) → W = E) :
    pCoreOf 2 M = E := by
  have hEnormM : (E.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEM]
    intro e m he hm
    exact hEn m hm e he
  have hE_le : E ≤ pCoreOf 2 M := le_pCoreOf_of_normal hEM hEnormM hE2
  have hPnormM : ((pCoreOf 2 M).subgroupOf M).Normal := normal_subgroupOf_pCoreOf 2 M
  have hPmem : ∀ g ∈ M, ∀ x ∈ pCoreOf 2 M, g * x * g⁻¹ ∈ pCoreOf 2 M := by
    intro g hg x hx
    exact (Subgroup.normal_subgroupOf_iff (pCoreOf_le 2 M)).mp hPnormM x g hx hg
  apply le_antisymm _ hE_le
  let P : Subgroup X := pCoreOf 2 M
  let C : Subgroup X := Subgroup.centralizer (P : Set X)
  let W : Subgroup X := E ⊓ C
  have hWle : W ≤ E := inf_le_left
  have hEnormP : (E.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hE_le]
    intro e p he hp
    exact (Subgroup.normal_subgroupOf_iff hEM).mp hEnormM e p he (pCoreOf_le 2 M hp)
  have hP_ne : E.subgroupOf P ≠ ⊥ := by
    intro h
    apply hEne
    rw [← Subgroup.map_subgroupOf_eq_of_le hE_le, h, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥P := (isPGroup_pCoreOf 2 M).isNilpotent
  haveI : (E.subgroupOf P).Normal := hEnormP
  have hcenter : (E.subgroupOf P) ⊓ Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hP_ne
  have hWne : W ≠ ⊥ := by
    intro hWbot
    rcases (Subgroup.ne_bot_iff_exists_ne_one.mp hcenter) with ⟨x, hxne⟩
    have hxE : (x.1.1 : X) ∈ E := x.2.1
    have hxW : (x.1.1 : X) ∈ W := by
      refine ⟨hxE, ?_⟩
      change (x.1.1 : X) ∈ Subgroup.centralizer (P : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2.2 ⟨h, hh⟩)
    have : (x.1.1 : X) = 1 := by
      rw [hWbot] at hxW
      simpa using hxW
    exact hxne (Subtype.ext (Subtype.ext this))
  have hEmap : ∀ g ∈ M, E.map (MulAut.conj g).toMonoidHom = E := by
    intro g hg
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact hEn g hg e he
    · intro e he
      refine ⟨g⁻¹ * e * g, ?_, ?_⟩
      · simpa using hEn g⁻¹ (inv_mem hg) e he
      · simp [MulAut.conj_apply, mul_assoc]
  have hCmap : ∀ g ∈ M, C.map (MulAut.conj g).toMonoidHom = C := by
    intro g hg
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      change c ∈ Subgroup.centralizer (P : Set X) at hc
      change (MulAut.conj g) c ∈ Subgroup.centralizer (P : Set X)
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro x hx
      have hxP : g⁻¹ * x * g ∈ P := by
        simpa using hPmem g⁻¹ (inv_mem hg) x hx
      have hcomm : c * (g⁻¹ * x * g) = (g⁻¹ * x * g) * c :=
        (hc (g⁻¹ * x * g) hxP).symm
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [← hcomm]
        _ = (g * c * g⁻¹) * x := by group
    · intro c hc
      refine ⟨g⁻¹ * c * g, ?_, ?_⟩
      · change c ∈ Subgroup.centralizer (P : Set X) at hc
        change g⁻¹ * c * g ∈ Subgroup.centralizer (P : Set X)
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro x hx
        have hxP : g * x * g⁻¹ ∈ P := hPmem g hg x hx
        have hcomm : c * (g * x * g⁻¹) = (g * x * g⁻¹) * c :=
          (hc (g * x * g⁻¹) hxP).symm
        calc x * (g⁻¹ * c * g) = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
          _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [← hcomm]
          _ = (g⁻¹ * c * g) * x := by group
      · simp [MulAut.conj_apply, mul_assoc]
  have hWinv : ∀ g ∈ M, W.map (MulAut.conj g).toMonoidHom = W := by
    intro g hg
    calc W.map (MulAut.conj g).toMonoidHom
        = (E ⊓ C).map (MulAut.conj g).toMonoidHom := rfl
      _ = E.map (MulAut.conj g).toMonoidHom ⊓ C.map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_inf E C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      _ = E ⊓ C := by rw [hEmap g hg, hCmap g hg]
      _ = W := rfl
  have hWE : W = E := hirr W hWle hWne hWinv
  have hEC : E ≤ C := by
    rw [← hWE]
    exact inf_le_right
  intro x hxP
  exact hC x (pCoreOf_le 2 M hxP)
    (fun e he => (Subgroup.mem_centralizer_iff.mp (hEC he)) x hxP)

theorem isElemAbelian_two_iff (E : Subgroup X) :
    IsElemAbelian 2 E ↔ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1 := by
  rw [IsElemAbelian, isMulCommutative_iff]
  constructor
  · rintro ⟨hcomm, hp⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      simpa using congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
    · intro x hx
      simpa [pow_two] using hp x hx
  · rintro ⟨hcomm, hsq⟩
    refine ⟨?_, ?_⟩
    · intro a b
      exact Subtype.ext (hcomm a.1 a.2 b.1 b.2)
    · intro x hx
      simpa [pow_two] using hsq x hx

end PCore

end CFSG.Quasithin.AppendixH.H14
