module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
public import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
public import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Involution
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.GroupTheory.OddOrderPGroup
import CFSG.RankThree.GF2n.Tim81.RootHypConj

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

namespace Sec5Hyp

private theorem exists_conj_mul_eq_of_mem_conjSubgroup
    {M V M₁ V₁ H₁ : Subgroup G} {g β x e : G}
    (hR : RootHyp M V) (hS₁ : Sec5Hyp M₁ V₁)
    (hSh₁ : Sec45Shape M₁ V₁ H₁ β) (hxH₁ : x ∈ H₁)
    (heP : e ∈ conjSubgroup x (Pc M₁ V₁)) (heK : e ∉ kOf V₁ H₁)
    (hcC : β * e ∈ Subgroup.centralizer (Tim79a.xOf V₁ H₁ : Set G))
    (hconj : conjSubgroup x V₁ = conjSubgroup (x * g) V) :
    ∀ u ∈ conjSubgroup x V₁, ∃ w ∈ Tim79a.xOf V₁ H₁, u * β = w * β * w⁻¹ := by
  intro u hu
  obtain ⟨w, hwW, hwe⟩ :=
    hSh₁.exists_commutator_eq_conj hS₁.toRootHyp hxH₁ heP heK hu
  refine ⟨w, hwW, ?_⟩
  let c : G := β * e
  have hu' : u ∈ conjSubgroup (x * g) V := by rwa [hconj] at hu
  have hu2 : u * u = 1 := hR.toHyp.mul_self_eq_one_of_mem_conj hu'
  have huW : u ∈ Tim79a.xOf V₁ H₁ := conjSubgroup_le_xOf_of_mem hxH₁ hu
  have heu : e * u = u * e := by
    obtain ⟨p, hpP₁, hp_eq⟩ := Subgroup.mem_map.mp heP
    obtain ⟨v, hvV₁, hv_eq⟩ := Subgroup.mem_map.mp hu
    have hpv : p * v = v * p := by
      have h1 : p ∈ Subgroup.centralizer (V₁ : Set G) :=
        (inf_le_right : Pc M₁ V₁ ≤ Subgroup.centralizer (V₁ : Set G)) hpP₁
      exact (Subgroup.mem_centralizer_iff.mp h1 v hvV₁).symm
    have hp_eq' : (MulAut.conj x) p = e := hp_eq
    have hv_eq' : (MulAut.conj x) v = u := hv_eq
    have h := congrArg (fun t => (MulAut.conj x) t) hpv
    simp only [map_mul] at h
    rwa [hp_eq', hv_eq'] at h
  have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp hcC u huW).symm
  have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hcC w hwW).symm
  have hwu : ⁅w, e⁆ = u := by
    rw [← commutatorElement_inv, hwe, inv_eq_of_mul_eq_one_right hu2]
  have heu' : e⁻¹ * u = u * e⁻¹ := by
    calc e⁻¹ * u = e⁻¹ * u * (e * e⁻¹) := by group
      _ = e⁻¹ * (u * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * u) * e⁻¹ := by rw [← heu]
      _ = u * e⁻¹ := by group
  have hwe' : w * e⁻¹ * w⁻¹ = u * e⁻¹ := by
    have h1 : w * e * w⁻¹ = u * e := by
      calc w * e * w⁻¹ = ⁅w, e⁆ * e := by rw [commutatorElement_def]; group
        _ = u * e := by rw [hwu]
    calc w * e⁻¹ * w⁻¹ = (w * e * w⁻¹)⁻¹ := by group
      _ = (u * e)⁻¹ := by rw [h1]
      _ = e⁻¹ * u := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2]
      _ = u * e⁻¹ := heu'
  have hβeq : β = c * e⁻¹ := by
    rw [show c = β * e from rfl]
    group
  have huβ : u * β = c * (u * e⁻¹) := by
    rw [hβeq]
    calc u * (c * e⁻¹) = (u * c) * e⁻¹ := by group
      _ = (c * u) * e⁻¹ := by rw [← hcu]
      _ = c * (u * e⁻¹) := by group
  have hwβ : w * β * w⁻¹ = c * (u * e⁻¹) := by
    rw [hβeq]
    calc w * (c * e⁻¹) * w⁻¹ = (w * c) * e⁻¹ * w⁻¹ := by group
      _ = (c * w) * e⁻¹ * w⁻¹ := by rw [← hcw]
      _ = c * (w * e⁻¹ * w⁻¹) := by group
      _ = c * (u * e⁻¹) := by rw [hwe']
  rw [huβ, hwβ]

private theorem false_of_conjSubgroup_mul_eq_base
    {M V V₁ : Subgroup G} {g h x β u : G}
    (hS : Sec5Hyp M V) (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (hVxV : conjSubgroup (x * g) V = V)
    (hconj : conjSubgroup x V₁ = conjSubgroup (x * g) V)
    (huVx : u ∈ conjSubgroup x V₁) (hu1 : u ≠ 1)
    (huβD : u * β ∈ Tim78.classD V) : False := by
  have hR := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hUh
  obtain ⟨y₁, hy₁H, -, hVy₁, -⟩ :=
    hR.exists_mem_conj_eq_of_eq_sup (H := hOf M V h) (h₀ := h) hSh.Pc_le hSh.hH
  have huV : u ∈ V := by
    rw [← hVxV]
    rwa [hconj] at huVx
  have hdmem : u * β ∈ V ⊔ conjSubgroup y₁ V := by
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left huV) ?_
    rw [← hVy₁]
    exact Subgroup.mem_sup_right hβU'
  have hyV₁ : conjSubgroup y₁ V ≠ V := by
    rw [← hVy₁]
    exact ne_of_mem_sigmaSet hR hUh
  have hd := (RootHyp.stmtI5b hR) (hOf M V h) h y₁ (u * β) hSh hy₁H hyV₁ hdmem huβD
  rcases hd with hd | hd
  · have hβV' : β ∈ V := by
      have h1 : u⁻¹ * (u * β) ∈ V := V.mul_mem (V.inv_mem huV) hd
      rwa [show u⁻¹ * (u * β) = β by group] at h1
    have hne' : V ⊓ conjSubgroup h V ≠ ⊥ := by
      intro hbot
      have hmem : β ∈ V ⊓ conjSubgroup h V := Subgroup.mem_inf.mpr ⟨hβV', hβU'⟩
      rw [hbot] at hmem
      exact hβ1 (Subgroup.mem_bot.mp hmem)
    have hne'' : conjSubgroup (1 : G) V ⊓ conjSubgroup h V ≠ ⊥ := by
      simpa [conjSubgroup_one] using hne'
    have heq : V = conjSubgroup h V := by
      simpa [conjSubgroup_one] using Tim78.conjSubgroup_eq_of_inf_ne_bot (V := V)
        hR.rootType.1 (g := 1) (h := h) hne''
    exact ne_of_mem_sigmaSet hR hUh heq.symm
  · rw [← hVy₁] at hd
    have huU' : u ∈ conjSubgroup h V := by
      have h1 : (u * β) * β⁻¹ ∈ conjSubgroup h V :=
        (conjSubgroup h V).mul_mem hd ((conjSubgroup h V).inv_mem hβU')
      rwa [show (u * β) * β⁻¹ = u by group] at h1
    have hne' : V ⊓ conjSubgroup h V ≠ ⊥ := by
      intro hbot
      have hmem : u ∈ V ⊓ conjSubgroup h V := Subgroup.mem_inf.mpr ⟨huV, huU'⟩
      rw [hbot] at hmem
      exact hu1 (Subgroup.mem_bot.mp hmem)
    have hne'' : conjSubgroup (1 : G) V ⊓ conjSubgroup h V ≠ ⊥ := by
      simpa [conjSubgroup_one] using hne'
    have heq : V = conjSubgroup h V := by
      simpa [conjSubgroup_one] using Tim78.conjSubgroup_eq_of_inf_ne_bot (V := V)
        hR.rootType.1 (g := 1) (h := h) hne''
    exact ne_of_mem_sigmaSet hR hUh heq.symm

private theorem mem_centralizer_xOf_mul_of_mem_sup_zpowers
    {M V M₁ V₁ H₁ P₁ : Subgroup G} {g x β e : G}
    (hS : Sec5Hyp M V) (hS₁ : Sec5Hyp M₁ V₁) (hSh₁ : Sec45Shape M₁ V₁ H₁ β)
    (hcKmem : ∀ z ∈ H₁, ⁅β * e, z⁆ ∈ kOf V₁ H₁)
    (hβsq : β * β = 1) (hβ1 : β ≠ 1)
    (heP : e ∈ conjSubgroup x P₁) (hP₁ : P₁ = conjSubgroup g (Pc M V))
    (hconj : ∀ z : G, conjSubgroup z V₁ = conjSubgroup (z * g) V)
    (hβxV : conjSubgroup β (conjSubgroup x V₁) = conjSubgroup x V₁) :
    β * e ∈ Subgroup.centralizer (Tim79a.xOf V₁ H₁ : Set G) := by
  have hR := hS.toRootHyp
  have hPx_eq : conjSubgroup x P₁ =
      Pc (conjSubgroup (x * g) M) (conjSubgroup (x * g) V) := by
    rw [Pc_conjSubgroup, ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, ← hP₁]
  have hPx2 : IsPGroup 2 (conjSubgroup x P₁) := by
    refine (inSubgroup_pCore_two (conjSubgroup (x * g) M)).1.to_le ?_
    rw [hPx_eq]
    exact inf_le_left
  have hβVx : conjSubgroup β (conjSubgroup (x * g) V) = conjSubgroup (x * g) V := by
    rw [← hconj x]
    exact hβxV
  have hβMx : β ∈ conjSubgroup (x * g) M := by
    have h1 : β ∈ Subgroup.normalizer (conjSubgroup (x * g) V : Set G) :=
      conjSubgroup_eq_self_iff.mp hβVx
    rwa [Tim78.normalizer_conjSubgroup,
      show Subgroup.normalizer (V : Set G) = M from hR.toHyp.normalizer_eq] at h1
  have hβNPx : β ∈ Subgroup.normalizer (conjSubgroup x P₁ : Set G) := by
    have hroot : RootHyp (conjSubgroup (x * g) M) (conjSubgroup (x * g) V) := hS.root (x * g)
    have hle := hroot.toHyp.le_normalizer_Pc hβMx
    rwa [← hPx_eq] at hle
  have hzpβ : IsPGroup 2 (Subgroup.zpowers β) := by
    have h2 : orderOf β = 2 :=
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hβsq) hβ1
    refine IsPGroup.of_card (p := 2) (G := ↥(Subgroup.zpowers β)) (n := 1) ?_
    rw [Nat.card_zpowers, h2, pow_one]
  have hjoin : IsPGroup 2 ↥(Subgroup.zpowers β ⊔ conjSubgroup x P₁) :=
    IsPGroup.to_sup_of_normal_right' (H := Subgroup.zpowers β)
      (K := conjSubgroup x P₁) hzpβ hPx2 (Subgroup.zpowers_le.mpr hβNPx)
  have hcP : β * e ∈ Subgroup.zpowers β ⊔ conjSubgroup x P₁ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers β))
      (Subgroup.mem_sup_right heP)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hjoin
    (⟨β * e, hcP⟩ : ↥(Subgroup.zpowers β ⊔ conjSubgroup x P₁))
  have hc2 : (β * e) ^ 2 ^ k = 1 := by
    have h1 := pow_orderOf_eq_one
      (⟨β * e, hcP⟩ : ↥(Subgroup.zpowers β ⊔ conjSubgroup x P₁))
    rw [hk] at h1
    simpa using congrArg Subtype.val h1
  exact hSh₁.mem_centralizer_xOf_of_commutator_mem_kOf hS₁.toRootHyp hcKmem hc2

private theorem le_normalizer_hOf_of_le_centralizer
    {V M₁ V₁ H₁ : Subgroup G} {β : G}
    (hS₁ : Sec5Hyp M₁ V₁) (hVU : V ≤ Subgroup.centralizer (V₁ : Set G))
    (hβV : β ∈ Subgroup.centralizer (V : Set G)) (hβsq : β * β = 1)
    (hH₁eq : H₁ = Pc M₁ V₁ ⊔ conjSubgroup β (Pc M₁ V₁)) :
    V ≤ Subgroup.normalizer (H₁ : Set G) ∧
      V ≤ Subgroup.centralizer (conjSubgroup β V₁ : Set G) := by
  have hVM₁ : V ≤ M₁ := by
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (V₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (hVU hv)
    rwa [show Subgroup.normalizer (V₁ : Set G) = M₁ from
      hS₁.toRootHyp.toHyp.normalizer_eq] at hvN
  have hVNP₁ : V ≤ Subgroup.normalizer (Pc M₁ V₁ : Set G) :=
    hVM₁.trans hS₁.toRootHyp.toHyp.le_normalizer_Pc
  have hVβV₁ : V ≤ Subgroup.centralizer (conjSubgroup β V₁ : Set G) := by
    intro v hv
    rw [CGT.Timmesfeld75.centralizer_conjSubgroup_eq, mem_conjSubgroup]
    have hvC : v ∈ Subgroup.centralizer (V₁ : Set G) := hVU hv
    have hβv : β * v = v * β := (Subgroup.mem_centralizer_iff.mp hβV v hv).symm
    rw [inv_eq_of_mul_eq_one_right hβsq, hβv, mul_assoc, hβsq, mul_one]
    exact hvC
  have hVNM₁ : V ≤ conjSubgroup β M₁ := by
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (conjSubgroup β V₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (hVβV₁ hv)
    rw [Tim78.normalizer_conjSubgroup] at hvN
    rwa [show Subgroup.normalizer (V₁ : Set G) = M₁ from
      hS₁.toRootHyp.toHyp.normalizer_eq] at hvN
  have hVNP₁' : V ≤ Subgroup.normalizer (conjSubgroup β (Pc M₁ V₁) : Set G) := by
    calc V ≤ conjSubgroup β M₁ := hVNM₁
      _ ≤ conjSubgroup β (Subgroup.normalizer (Pc M₁ V₁ : Set G)) :=
          conjSubgroup_mono hS₁.toRootHyp.toHyp.le_normalizer_Pc
      _ = Subgroup.normalizer (conjSubgroup β (Pc M₁ V₁) : Set G) :=
          (Tim78.normalizer_conjSubgroup β (Pc M₁ V₁)).symm
  refine ⟨?_, hVβV₁⟩
  intro v hv
  have h1 : v ∈ Subgroup.normalizer (Pc M₁ V₁ : Set G) := hVNP₁ hv
  have h2 : v ∈ Subgroup.normalizer (conjSubgroup β (Pc M₁ V₁) : Set G) := hVNP₁' hv
  have h3 := Subgroup.inf_normalizer_le_normalizer_sup (Pc M₁ V₁)
    (conjSubgroup β (Pc M₁ V₁)) (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  rw [hH₁eq]
  exact h3

private theorem commutator_eq_bot_of_mem_centralizer_xOf
    {M V V₁ H₁ : Subgroup G} {g x v₀ : G}
    (hR : RootHyp M V) (hv₀V : v₀ ∈ V) (hv₀1 : v₀ ≠ 1)
    (hv₀C : v₀ ∈ Subgroup.centralizer (Tim79a.xOf V₁ H₁ : Set G))
    (hxH₁ : x ∈ H₁)
    (hconj : conjSubgroup x V₁ = conjSubgroup (x * g) V) :
    ⁅V, conjSubgroup x V₁⁆ = ⊥ := by
  have hcommVVx : ⁅V, conjSubgroup (x * g) V⁆ = ⊥ := by
    have hv₀W : v₀ ∈ Subgroup.centralizer (conjSubgroup (x * g) V : Set G) := by
      refine Subgroup.centralizer_le ?_ hv₀C
      intro z hz
      rw [← hconj] at hz
      exact conjSubgroup_le_xOf_of_mem hxH₁ hz
    have hmemN : v₀ ∈ Subgroup.normalizer (conjSubgroup (x * g) V : Set G) :=
      Subgroup.centralizer_le_normalizer _ hv₀W
    have hinf : conjSubgroup (1 : G) V ⊓
        Subgroup.normalizer (conjSubgroup (x * g) V : Set G) ≠ ⊥ := by
      intro hbot
      have hmem : v₀ ∈ conjSubgroup (1 : G) V ⊓
          Subgroup.normalizer (conjSubgroup (x * g) V : Set G) := by
        simpa [conjSubgroup_one] using Subgroup.mem_inf.mpr ⟨hv₀V, hmemN⟩
      rw [hbot] at hmem
      exact hv₀1 (Subgroup.mem_bot.mp hmem)
    have hcomm := Tim78.commute_of_isRootTypeTI hR.rootType (g := (1 : G)) (h := x * g)
      hinf
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb'
    exact (hcomm a (by simpa [conjSubgroup_one] using ha) b hb').symm
  rw [hconj]
  exact hcommVVx

private theorem isHMember_conjSubgroup_hOf
    {M V : Subgroup G} {g x : G}
    (hS : Sec5Hyp M V) (hS₁ : Sec5Hyp (conjSubgroup g M) (conjSubgroup g V))
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUxSig : conjSubgroup x (conjSubgroup g V) ∈
      sigmaSet (conjSubgroup g M) (conjSubgroup g V))
    (hcommVxV : ⁅V, conjSubgroup x (conjSubgroup g V)⁆ = ⊥)
    (hVxV' : conjSubgroup x (conjSubgroup g V) ≠ V)
    (hconj : ∀ z : G, conjSubgroup z (conjSubgroup g V) = conjSubgroup (z * g) V) :
    conjSubgroup (x * g) V ∈ sigmaSet M V := by
  let P₁ : Subgroup G := Pc (conjSubgroup g M) (conjSubgroup g V)
  have hV₁Sig : V ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V) :=
    (hS.mem_sigmaSet_iff_self_mem (g := g)).mp hUg
  have hV₁Sig' : conjSubgroup g⁻¹ (conjSubgroup g V) ∈
      sigmaSet (conjSubgroup g M) (conjSubgroup g V) := by
    rw [hconj g⁻¹, show g⁻¹ * g = 1 by group, conjSubgroup_one]
    exact hV₁Sig
  have hV₁V : conjSubgroup g⁻¹ (conjSubgroup g V) = V := by
    rw [hconj g⁻¹, show g⁻¹ * g = 1 by group, conjSubgroup_one]
  have hIM : IsHMember (conjSubgroup x (conjSubgroup g M))
      (conjSubgroup x (conjSubgroup g V))
      (conjSubgroup g⁻¹ P₁ ⊔ conjSubgroup x P₁) :=
    h512 (conjSubgroup g M) (conjSubgroup g V) hS₁ (g⁻¹) x hUxSig hV₁Sig'
      (by rw [hV₁V]; exact hcommVxV)
      (by
        rw [hconj g⁻¹, show g⁻¹ * g = 1 by group, conjSubgroup_one]
        exact hVxV'.symm)
  have hP₁g : conjSubgroup g⁻¹ P₁ = Pc M V := by
    rw [show P₁ = Pc (conjSubgroup g M) (conjSubgroup g V) from rfl, Pc_conjSubgroup,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show g⁻¹ * g = 1 by group, conjSubgroup_one]
  have hMe : conjSubgroup x (conjSubgroup g M) = conjSubgroup (x * g) M :=
    CGT.Timmesfeld75.conjSubgroup_conjSubgroup x g M
  have hVe : conjSubgroup x (conjSubgroup g V) = conjSubgroup (x * g) V := hconj x
  have hPe : conjSubgroup g⁻¹ P₁ ⊔ conjSubgroup x P₁ =
      Pc M V ⊔ conjSubgroup (x * g) (Pc M V) := by
    rw [hP₁g, show P₁ = Pc (conjSubgroup g M) (conjSubgroup g V) from rfl, Pc_conjSubgroup,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup x g (Pc M V)]
  have hIM' : IsHMember (conjSubgroup (x * g) M) (conjSubgroup (x * g) V)
      (hOf M V (x * g)) := by
    rw [← hMe, ← hVe, show hOf M V (x * g) =
      Pc M V ⊔ conjSubgroup (x * g) (Pc M V) from rfl, ← hPe]
    exact hIM
  exact (mem_sigmaSet_iff hS.toRootHyp.toHyp).mpr
    ((hS.toRootHyp.isHMember_hOf_conj_iff (g := x * g)).mp hIM')

private theorem conjSubgroup_xV_ne_conjSubgroup_hV
    {M V M₁ H₁ : Subgroup G} {g h β x : G}
    (hR : RootHyp M V) (hS₁ : Sec5Hyp M₁ (conjSubgroup g V))
    (hSh₁ : Sec45Shape M₁ (conjSubgroup g V) H₁ β)
    (hxH₁ : x ∈ H₁) (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥) :
    conjSubgroup x (conjSubgroup g V) ≠ conjSubgroup h V := by
  intro heq
  have hβW : β ∈ Tim79a.xOf (conjSubgroup g V) H₁ := by
    have h1 : β ∈ conjSubgroup x (conjSubgroup g V) := by rw [heq]; exact hβU'
    exact conjSubgroup_le_xOf_of_mem hxH₁ h1
  have hβCW : β ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G) := by
    haveI : IsMulCommutative ↥(Tim79a.xOf (conjSubgroup g V) H₁) :=
      (hSh₁.isElemAbelian hS₁.toRootHyp).1
    exact Subgroup.le_centralizer _ hβW
  have hβCU : β ∈ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    Subgroup.centralizer_le (show (conjSubgroup g V : Set G) ⊆
      (Tim79a.xOf (conjSubgroup g V) H₁ : Set G) from
      fun z hz => le_xOf_self (conjSubgroup g V) H₁ hz) hβCW
  have hinf : conjSubgroup h V ⊓
      Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : β ∈ conjSubgroup h V ⊓
        Subgroup.normalizer (conjSubgroup g V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hβU', Subgroup.centralizer_le_normalizer _ hβCU⟩
    rw [hbot] at hmem
    exact hβ1 (Subgroup.mem_bot.mp hmem)
  have hcomm := Tim78.commute_of_isRootTypeTI hR.rootType (g := h) (h := g) hinf
  exact hne (by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c' hc'
    exact hcomm c' hc' a ha)

private theorem conjSubgroup_mem_normalizer_hOf_of_commutator_eq_bot
    {V M₁ V₁ H₁ : Subgroup G} {g h x x' : G}
    (hS₁ : Sec5Hyp M₁ V₁)
    (hconj : ∀ z : G, conjSubgroup z V₁ = conjSubgroup (z * g) V)
    (hxH₁ : x ∈ H₁) (hx'H₁ : x' ∈ H₁)
    (hH₁_eq : conjSubgroup x (Pc M₁ V₁) ⊔ conjSubgroup x' (Pc M₁ V₁) = H₁)
    (hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥)
    (hcommVx' : ⁅conjSubgroup h V, conjSubgroup (x' * g) V⁆ = ⊥) :
    ∀ a ∈ conjSubgroup h V, conjSubgroup a H₁ = H₁ := by
  have hU'NP : ∀ z : G, z ∈ H₁ → ⁅conjSubgroup h V, conjSubgroup (z * g) V⁆ = ⊥ →
      conjSubgroup h V ≤ Subgroup.normalizer (conjSubgroup z (Pc M₁ V₁) : Set G) := by
    intro z hzH hcommz u hu
    have huC : u ∈ Subgroup.centralizer (conjSubgroup (z * g) V : Set G) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcommz
      exact hcommz hu
    have huC' : u ∈ Subgroup.centralizer (conjSubgroup z V₁ : Set G) := by
      rw [hconj z]
      exact huC
    have huN : u ∈ Subgroup.normalizer (conjSubgroup z V₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ huC'
    rw [Tim78.normalizer_conjSubgroup] at huN
    rw [show Subgroup.normalizer (V₁ : Set G) = M₁ from
      hS₁.toRootHyp.toHyp.normalizer_eq] at huN
    rw [Tim78.normalizer_conjSubgroup]
    exact conjSubgroup_mono hS₁.toRootHyp.toHyp.le_normalizer_Pc huN
  intro a ha
  have h1 : a ∈ Subgroup.normalizer (conjSubgroup x (Pc M₁ V₁) : Set G) :=
    hU'NP x hxH₁ hcommVx ha
  have h2 : a ∈ Subgroup.normalizer (conjSubgroup x' (Pc M₁ V₁) : Set G) :=
    hU'NP x' hx'H₁ hcommVx' ha
  rw [conjSubgroup_eq_self_iff, ← hH₁_eq]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr ⟨h1, h2⟩)

private theorem false_of_commutator_eq_bot_two_conjugates
    {M V M₁ H₁ : Subgroup G} {g h β x x' : G}
    (hR : RootHyp M V) (hS₁ : Sec5Hyp M₁ (conjSubgroup g V))
    (hSh₁ : Sec45Shape M₁ (conjSubgroup g V) H₁ β)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hxH₁ : x ∈ H₁) (hx'H₁ : x' ∈ H₁)
    (hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥)
    (hcommVx' : ⁅conjSubgroup h V, conjSubgroup (x' * g) V⁆ = ⊥)
    (hnexx' : conjSubgroup x (conjSubgroup g V) ≠ conjSubgroup x' (conjSubgroup g V))
    (hnh : ∀ a ∈ conjSubgroup h V, conjSubgroup a H₁ = H₁)
    (hconj : ∀ z : G, conjSubgroup z (conjSubgroup g V) = conjSubgroup (z * g) V) :
    False := by
  have hU'2 : ∀ a ∈ conjSubgroup h V, a * a = 1 := fun a ha =>
    hR.toHyp.mul_self_eq_one_of_mem_conj ha
  have hU'c : ∀ a ∈ conjSubgroup h V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro a ha b hb
    have hV' : Assembly.IsElemAbelian 2 (conjSubgroup h V) :=
      hR.toHyp.elem.map (MulAut.conj h).toMonoidHom
    exact congrArg Subtype.val (hV'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU'card : 2 < Nat.card ↥(conjSubgroup h V) := by
    rw [card_conjSubgroup]; have := hR.four_le_card; omega
  have hU'₁ : ∀ a ∈ conjSubgroup h V,
      conjSubgroup a (conjSubgroup x (conjSubgroup g V)) =
        conjSubgroup x (conjSubgroup g V) := by
    intro a ha; rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcommVx
    have hmem : a ∈ Subgroup.centralizer
        (conjSubgroup x (conjSubgroup g V) : Set G) := by
      rw [hconj x]
      exact hcommVx ha
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hmem)
  have hU'₂ : ∀ a ∈ conjSubgroup h V,
      conjSubgroup a (conjSubgroup x' (conjSubgroup g V)) =
        conjSubgroup x' (conjSubgroup g V) := by
    intro a ha; rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcommVx'
    have hmem : a ∈ Subgroup.centralizer
        (conjSubgroup x' (conjSubgroup g V) : Set G) := by
      rw [hconj x']
      exact hcommVx' ha
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hmem)
  obtain ⟨b, hbU', hb1, hbC⟩ := hSh₁.exists_ne_one_mem_centralizer_xOf hS₁.toRootHyp
    (A := conjSubgroup h V) hU'2 hU'c hU'card hnh hxH₁ hx'H₁ hnexx' hU'₁ hU'₂
  have hbV : b ∈ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    Subgroup.centralizer_le (fun u hu => le_xOf_self (conjSubgroup g V) H₁ hu) hbC
  have hinfU : conjSubgroup h V ⊓
      Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : b ∈ conjSubgroup h V ⊓
        Subgroup.normalizer (conjSubgroup g V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hbU', Subgroup.centralizer_le_normalizer _ hbV⟩
    rw [hbot] at hmem
    exact hb1 (Subgroup.mem_bot.mp hmem)
  have hcomm := Tim78.commute_of_isRootTypeTI hR.rootType (g := h) (h := g) hinfU
  exact hne (by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hcomm c hc a ha)

private theorem sup_conjSubgroup_eq_hOf_of_conjSubgroup_ne
    {M₁ V₁ H₁ : Subgroup G} {β x x' : G}
    (hS₁ : Sec5Hyp M₁ V₁) (hSh₁ : Sec45Shape M₁ V₁ H₁ β)
    (hxH₁ : x ∈ H₁) (hx'H₁ : x' ∈ H₁)
    (hnexx' : conjSubgroup x V₁ ≠ conjSubgroup x' V₁) :
    conjSubgroup x (Pc M₁ V₁) ⊔ conjSubgroup x' (Pc M₁ V₁) = H₁ := by
  have hyH : x⁻¹ * x' ∈ H₁ := H₁.mul_mem (H₁.inv_mem hxH₁) hx'H₁
  have hyV : conjSubgroup (x⁻¹ * x') V₁ ≠ V₁ := by
    intro heq
    apply hnexx'
    have h3 : conjSubgroup x (conjSubgroup (x⁻¹ * x') V₁) = conjSubgroup x V₁ := by
      rw [heq]
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show x * (x⁻¹ * x') = x' by group] at h3
    exact h3.symm
  obtain ⟨p, hpP₁, hp⟩ :=
    RootHyp.stmtI5a hS₁.toRootHyp H₁ β (x⁻¹ * x') hSh₁ hyH hyV
  have hOfeq : hOf M₁ V₁ (x⁻¹ * x') = hOf M₁ V₁ β :=
    hS₁.toRootHyp.toHyp.hOf_eq_of_conjSubgroup_eq_conj hpP₁ hp
  have h1 : hOf M₁ V₁ (x⁻¹ * x') = H₁ := by
    rw [hOfeq]
    exact hSh₁.hH.symm
  have h2 : conjSubgroup x (hOf M₁ V₁ (x⁻¹ * x')) = conjSubgroup x H₁ :=
    congrArg (conjSubgroup x) h1
  have h3 : conjSubgroup x (hOf M₁ V₁ (x⁻¹ * x')) =
      conjSubgroup x (Pc M₁ V₁) ⊔ conjSubgroup x' (Pc M₁ V₁) := by
    rw [hOf, conjSubgroup_sup, CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show x * (x⁻¹ * x') = x' by group]
  rw [h3, conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hxH₁)] at h2
  exact h2

private theorem exists_involution_mem_conjSubgroup_not_conj_eq (hS : Sec5Hyp M V) {g h : G}
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥) :
    ∃ β ∈ conjSubgroup h V, β ≠ 1 ∧ β * β = 1 ∧
      conjSubgroup β (conjSubgroup g V) ≠ conjSubgroup g V := by
  classical
  have hR := hS.toRootHyp
  have hU'bot : conjSubgroup h V ≠ ⊥ := by
    intro hbot
    exact hR.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  obtain ⟨β₀, hβ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU'bot
  refine ⟨(β₀ : G), β₀.2, fun hh => hβ₀1 (Subtype.ext hh), ?_, ?_⟩
  · exact hR.toHyp.mul_self_eq_one_of_mem_conj β₀.2
  · intro heq
    apply hne
    have hmemN : (β₀ : G) ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
      conjSubgroup_eq_self_iff.mp heq
    have hinf : conjSubgroup h V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ := by
      intro hbot
      have hmem : (β₀ : G) ∈ conjSubgroup h V ⊓
          Subgroup.normalizer (conjSubgroup g V : Set G) :=
        Subgroup.mem_inf.mpr ⟨β₀.2, hmemN⟩
      rw [hbot] at hmem
      exact hβ₀1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    have hcomm := Tim78.commute_of_isRootTypeTI hR.rootType (g := h) (h := g) hinf
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb a ha

private theorem imgK_conjSubgroup_eq_of_sylow_fixed
    {V H P : Subgroup G} {b x : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hPle : P ≤ H) (hxH : x ∈ H)
    (hfix : ((imgK V H (conjSubgroup x P)).map ψ.toMonoidHom).map
        (MulAut.congr ψ (hBarConj hbH hbK)).toMonoidHom =
      (imgK V H (conjSubgroup x P)).map ψ.toMonoidHom) :
    imgK V H (conjSubgroup b (conjSubgroup x P)) = imgK V H (conjSubgroup x P) := by
  rw [CFSG.map_mulAut_congr] at hfix
  have h3 := Subgroup.map_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective hfix
  calc imgK V H (conjSubgroup b (conjSubgroup x P))
      = Subgroup.map (MulEquiv.toMonoidHom (hBarConj hbH hbK))
          (imgK V H (conjSubgroup x P)) :=
        (hBarConj_map_imgK hbH hbK (conjSubgroup_le_of_le_of_mem hPle hxH)).symm
    _ = imgK V H (conjSubgroup x P) := h3

private theorem false_of_fixing_second_sylow
    {M V M₁ H₁ : Subgroup G} {g h β x : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar (conjSubgroup g V) H₁ ≃* SL(2, F))
    (hR : RootHyp M V) (hS₁ : Sec5Hyp M₁ (conjSubgroup g V))
    (hSh₁ : Sec45Shape M₁ (conjSubgroup g V) H₁ β)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hxH₁ : x ∈ H₁) (hβH₁ : conjSubgroup β H₁ = H₁)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G))
    (root_comm : ∀ z : G,
      conjSubgroup β (conjSubgroup z (conjSubgroup g V)) =
        conjSubgroup z (conjSubgroup g V) →
      ⁅conjSubgroup h V, conjSubgroup (z * g) V⁆ = ⊥)
    (hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥)
    (hconj_eq : ∀ z : G, conjSubgroup z (conjSubgroup g V) = conjSubgroup (z * g) V)
    {S S' : Subgroup SL(2, F)}
    (hSx : S = (imgK (conjSubgroup g V) H₁
      (conjSubgroup x (Pc M₁ (conjSubgroup g V)))).map ψ.toMonoidHom)
    (hS'exp : ∀ a ∈ S', a * a = 1) (hS'card : Nat.card S' = Fintype.card F)
    (hS'ne : S' ≠ S)
    (hS'fix : S'.map (MulAut.congr ψ (hBarConj hβH' hβK₁)).toMonoidHom = S') :
    False := by
  obtain ⟨x', hx'H₁, hS'x'⟩ := hSh₁.exists_mem_eq_map_imgK hS₁.toRootHyp ψ hS'exp hS'card
  have hfixx' : imgK (conjSubgroup g V) H₁
        (conjSubgroup β (conjSubgroup x' (Pc M₁ (conjSubgroup g V)))) =
      imgK (conjSubgroup g V) H₁ (conjSubgroup x' (Pc M₁ (conjSubgroup g V))) :=
    imgK_conjSubgroup_eq_of_sylow_fixed hβH' hβK₁ ψ hSh₁.Pc_le hx'H₁ (by
      rw [← hS'x']
      exact hS'fix)
  have hβx'V : conjSubgroup β (conjSubgroup x' (conjSubgroup g V)) =
      conjSubgroup x' (conjSubgroup g V) :=
    hSh₁.conj_eq_of_imgK_eq hS₁.toRootHyp hβH₁ hx'H₁ hfixx'
  have hcommVx' : ⁅conjSubgroup h V, conjSubgroup (x' * g) V⁆ = ⊥ := root_comm x' hβx'V
  have hnexx' : conjSubgroup x (conjSubgroup g V) ≠
      conjSubgroup x' (conjSubgroup g V) := by
    intro heq
    apply hS'ne
    rw [hS'x', hSx]
    exact congrArg (fun T => (imgK (conjSubgroup g V) H₁ T).map ψ.toMonoidHom)
      (hS₁.toRootHyp.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq heq.symm)
  have hH₁_eq : conjSubgroup x (Pc M₁ (conjSubgroup g V)) ⊔
      conjSubgroup x' (Pc M₁ (conjSubgroup g V)) = H₁ :=
    sup_conjSubgroup_eq_hOf_of_conjSubgroup_ne hS₁ hSh₁ hxH₁ hx'H₁ hnexx'
  have hnh : ∀ a ∈ conjSubgroup h V, conjSubgroup a H₁ = H₁ :=
    conjSubgroup_mem_normalizer_hOf_of_commutator_eq_bot hS₁ hconj_eq hxH₁ hx'H₁
      hH₁_eq hcommVx hcommVx'
  exact false_of_commutator_eq_bot_two_conjugates hR hS₁ hSh₁ hne hxH₁ hx'H₁ hcommVx
    hcommVx' hnexx' hnh hconj_eq

private theorem false_of_mem_kOf
    {M V M₁ H₁ : Subgroup G} {g h β : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar (conjSubgroup g V) H₁ ≃* SL(2, F)) {s : SL(2, F)}
    (hR : RootHyp M V) (hS₁ : Sec5Hyp M₁ (conjSubgroup g V))
    (hSh₁ : Sec45Shape M₁ (conjSubgroup g V) H₁ β)
    (hβsq : β * β = 1) (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G))
    (hsθ : MulAut.congr ψ (hBarConj hβH' hβK₁) = MulAut.conj s) (hs1 : s = 1) :
    False := by
  have hb1 : hBarConj hβH' hβK₁ = 1 := by
    apply (MulAut.congr ψ).injective
    rw [show MulAut.congr ψ (hBarConj hβH' hβK₁) = MulAut.conj s from hsθ, hs1]
    calc MulAut.conj (1 : SL(2, F)) = 1 := map_one MulAut.conj
      _ = MulAut.congr ψ 1 := (map_one (MulAut.congr ψ)).symm
  have hβKmem : ∀ z ∈ H₁, ⁅β, z⁆ ∈ kOf (conjSubgroup g V) H₁ :=
    (hBarConj_eq_one_iff hβH' hβK₁).mp hb1
  have hβC : β ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G) :=
    hSh₁.mem_centralizer_xOf_of_commutator_mem_kOf hS₁.toRootHyp hβKmem (k := 1)
      (by simpa [pow_two] using hβsq)
  have hβCU : β ∈ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    Subgroup.centralizer_le (show (conjSubgroup g V : Set G) ⊆
      (Tim79a.xOf (conjSubgroup g V) H₁ : Set G) from
      fun u hu => le_xOf_self (conjSubgroup g V) H₁ hu) hβC
  have hβN : β ∈ Subgroup.normalizer (conjSubgroup g V : Set G) :=
    Subgroup.centralizer_le_normalizer _ hβCU
  have hbot : ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hR.conj_le_centralizer_of_mem_normalizer hβU' hβ1 hβN)
  exact hne hbot

private theorem false_of_mem_sup_of_ne
    (hR : RootHyp M V) {g h x β u : G} {V₁ : Subgroup G}
    (hUxNE : conjSubgroup x V₁ ≠ conjSubgroup h V)
    (hconjVx : conjSubgroup x V₁ = conjSubgroup (x * g) V)
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (huVx : u ∈ conjSubgroup x V₁) (hu1 : u ≠ 1)
    (hd : u * β ∈ conjSubgroup h V ∨ u * β ∈ conjSubgroup x V₁) : False := by
  rcases hd with hd | hd
  · have huU' : u ∈ conjSubgroup h V := by
      have h1 : (u * β) * β⁻¹ ∈ conjSubgroup h V :=
        (conjSubgroup h V).mul_mem hd ((conjSubgroup h V).inv_mem hβU')
      rwa [show (u * β) * β⁻¹ = u by group] at h1
    have hne' : conjSubgroup x V₁ ⊓ conjSubgroup h V ≠ ⊥ := by
      intro hbot
      have hmem : u ∈ conjSubgroup x V₁ ⊓ conjSubgroup h V :=
        Subgroup.mem_inf.mpr ⟨huVx, huU'⟩
      rw [hbot] at hmem
      exact hu1 (Subgroup.mem_bot.mp hmem)
    rw [hconjVx] at hne'
    exact hUxNE (by
      rw [hconjVx]
      exact Tim78.conjSubgroup_eq_of_inf_ne_bot hR.rootType.1 hne')
  · have hβUx : β ∈ conjSubgroup x V₁ := by
      have h1 : u⁻¹ * (u * β) ∈ conjSubgroup x V₁ :=
        (conjSubgroup x V₁).mul_mem ((conjSubgroup x V₁).inv_mem huVx) hd
      rwa [show u⁻¹ * (u * β) = β by group] at h1
    have hne' : conjSubgroup x V₁ ⊓ conjSubgroup h V ≠ ⊥ := by
      intro hbot
      have hmem : β ∈ conjSubgroup x V₁ ⊓ conjSubgroup h V :=
        Subgroup.mem_inf.mpr ⟨hβUx, hβU'⟩
      rw [hbot] at hmem
      exact hβ1 (Subgroup.mem_bot.mp hmem)
    rw [hconjVx] at hne'
    exact hUxNE (by
      rw [hconjVx]
      exact Tim78.conjSubgroup_eq_of_inf_ne_bot hR.rootType.1 hne')

private theorem conjSubgroup_ne_self_of_shape
    {M₁ V₁ H₁ : Subgroup G} {β x : G}
    (hS₁ : Sec5Hyp M₁ V₁) (hSh₁ : Sec45Shape M₁ V₁ H₁ β)
    (hβxV : conjSubgroup β (conjSubgroup x V₁) = conjSubgroup x V₁)
    (hH₁eq : H₁ = Pc M₁ V₁ ⊔ conjSubgroup β (Pc M₁ V₁)) :
    conjSubgroup x V₁ ≠ V₁ := by
  intro heq
  have hβM₁ : β ∈ M₁ := by
    have h1 : β ∈ Subgroup.normalizer (conjSubgroup x V₁ : Set G) :=
      conjSubgroup_eq_self_iff.mp hβxV
    rw [heq] at h1
    rwa [show Subgroup.normalizer (V₁ : Set G) = M₁ from
      hS₁.toRootHyp.toHyp.normalizer_eq] at h1
  have hβP : conjSubgroup β (Pc M₁ V₁) = Pc M₁ V₁ :=
    conjSubgroup_eq_self_iff.mpr (hS₁.toRootHyp.toHyp.le_normalizer_Pc hβM₁)
  apply hSh₁.not_le
  show H₁ ≤ M₁
  rw [hH₁eq, hβP, sup_idem]
  exact hS₁.toRootHyp.toHyp.Pc_le_M

private theorem exists_mem_centralizer_xOf_of_normalizer
    {M V M₁ H₁ : Subgroup G} {g h β y : G}
    (hS : Sec5Hyp M V) (hS₁ : Sec5Hyp M₁ (conjSubgroup g V))
    (hSh₁ : Sec45Shape M₁ (conjSubgroup g V) H₁ β)
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hβU' : β ∈ conjSubgroup h V) (hβsq : β * β = 1)
    (hβne : conjSubgroup β (conjSubgroup g V) ≠ conjSubgroup g V)
    (hH₁eq : H₁ = Pc M₁ (conjSubgroup g V) ⊔
      conjSubgroup β (Pc M₁ (conjSubgroup g V)))
    (hyH₁ : y ∈ H₁)
    (hVy : conjSubgroup β (conjSubgroup g V) = conjSubgroup y (conjSubgroup g V)) :
    ∃ v₀ ∈ V, v₀ ≠ 1 ∧
      v₀ ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G) := by
  have hR := hS.toRootHyp
  have hUV : conjSubgroup g V ≤ Subgroup.centralizer (V : Set G) :=
    (hS.le_M_of_mem_sigmaSet hUg).2
  have hVU : V ≤ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    Subgroup.le_centralizer_iff.mpr hUV
  have hβV : β ∈ Subgroup.centralizer (V : Set G) :=
    (hS.le_M_of_mem_sigmaSet hUh).2 hβU'
  have hVN := le_normalizer_hOf_of_le_centralizer hS₁ hVU hβV hβsq hH₁eq
  have hVNH₁ : V ≤ Subgroup.normalizer (H₁ : Set G) := hVN.1
  have hVβV₁ : V ≤ Subgroup.centralizer (conjSubgroup β (conjSubgroup g V) : Set G) := hVN.2
  have hAH : ∀ a ∈ V, conjSubgroup a H₁ = H₁ := fun a ha =>
    conjSubgroup_eq_self_iff.mpr (hVNH₁ ha)
  have hA2 : ∀ a ∈ V, a * a = 1 := fun a ha => by simpa [pow_two] using hR.toHyp.elem.2 a ha
  have hAc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR.toHyp.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA2card : 2 < Nat.card ↥V := by have := hR.four_le_card; omega
  have hne1y : conjSubgroup (1 : G) (conjSubgroup g V) ≠
      conjSubgroup y (conjSubgroup g V) := by
    rw [conjSubgroup_one, ← hVy]
    exact hβne.symm
  have hA₁ : ∀ a ∈ V,
      conjSubgroup a (conjSubgroup (1 : G) (conjSubgroup g V)) =
        conjSubgroup (1 : G) (conjSubgroup g V) := by
    intro a ha
    rw [conjSubgroup_one]
    exact conjSubgroup_eq_self_iff.mpr
      (Subgroup.centralizer_le_normalizer _ (hVU ha))
  have hA₂ : ∀ a ∈ V, conjSubgroup a (conjSubgroup y (conjSubgroup g V)) =
      conjSubgroup y (conjSubgroup g V) := by
    intro a ha
    rw [← hVy]
    exact conjSubgroup_eq_self_iff.mpr
      (Subgroup.centralizer_le_normalizer _ (hVβV₁ ha))
  exact hSh₁.exists_ne_one_mem_centralizer_xOf hS₁.toRootHyp
    (A := V) hA2 hAc hA2card hAH H₁.one_mem hyH₁ hne1y hA₁ hA₂

private theorem shape_of_conjSubgroup
    (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    {g h β : G}
    (hβc : ∀ β ∈ conjSubgroup h V,
      ⁅conjSubgroup g V, conjSubgroup β (conjSubgroup g V)⁆ = ⊥)
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hβU' : β ∈ conjSubgroup h V)
    (hβne : conjSubgroup β (conjSubgroup g V) ≠ conjSubgroup g V) :
    Sec45Shape (conjSubgroup g M) (conjSubgroup g V)
      (hOf (conjSubgroup g M) (conjSubgroup g V) β) β := by
  classical
  have hβM : β ∈ M := (hS.le_M_of_mem_sigmaSet hUh).1 hβU'
  have hβgSig : conjSubgroup (β * g) V ∈ sigmaSet M V := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hS.conj_mem_sigmaSet hβM hUg
  have hcommβg : ⁅conjSubgroup (β * g) V, conjSubgroup g V⁆ = ⊥ := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, Subgroup.commutator_comm]
    exact hβc β hβU'
  have hneβg : conjSubgroup (β * g) V ≠ conjSubgroup g V := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hβne
  have hfriend : IsHMember (conjSubgroup g M) (conjSubgroup g V)
      (conjSubgroup (β * g) (Pc M V) ⊔ conjSubgroup g (Pc M V)) :=
    h512 M V hS (β * g) g hUg hβgSig hcommβg hneβg
  have hP₁ : Pc (conjSubgroup g M) (conjSubgroup g V) = conjSubgroup g (Pc M V) :=
    Pc_conjSubgroup M V g
  have hH₁mem : IsHMember (conjSubgroup g M) (conjSubgroup g V)
      (hOf (conjSubgroup g M) (conjSubgroup g V) β) := by
    have hPβ : conjSubgroup (β * g) (Pc M V) =
        conjSubgroup β (Pc (conjSubgroup g M) (conjSubgroup g V)) := by
      rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, ← hP₁]
    rw [show hOf (conjSubgroup g M) (conjSubgroup g V) β =
        Pc (conjSubgroup g M) (conjSubgroup g V) ⊔
          conjSubgroup β (Pc (conjSubgroup g M) (conjSubgroup g V)) from rfl,
      ← hPβ, hP₁, sup_comm]
    exact hfriend
  have hβSig₁ : conjSubgroup β (conjSubgroup g V) ∈
      sigmaSet (conjSubgroup g M) (conjSubgroup g V) :=
    (mem_sigmaSet_iff (hS.conj g).toRootHyp.toHyp).mpr hH₁mem
  exact (hS.conj g).shape hβSig₁

private theorem hBarConj_mul_self_eq_one
    {V₁ H₁ : Subgroup G} {β : G} (hβsq : β * β = 1)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf V₁ H₁ : Set G)) :
    hBarConj hβH' hβK₁ * hBarConj hβH' hβK₁ = 1 := by
  rw [← hBarConj_mul hβH' hβK₁ hβH' hβK₁, hBarConj_eq_one_iff]
  intro z hz
  rw [hβsq]
  simpa using (kOf V₁ H₁).one_mem

private theorem exists_mem_conj_Pc_of_sylow_image
    {M₁ V₁ H₁ : Subgroup G} {x β : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V₁ H₁ ≃* SL(2, F))
    (hSh₁ : Sec45Shape M₁ V₁ H₁ β) (hxH₁ : x ∈ H₁)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf V₁ H₁ : Set G))
    {S : Subgroup SL(2, F)} {s : SL(2, F)} (hsS : s ∈ S)
    (hSx : S = (imgK V₁ H₁ (conjSubgroup x (Pc M₁ V₁))).map ψ.toMonoidHom)
    (hsθ : MulAut.congr ψ (hBarConj hβH' hβK₁) = MulAut.conj s) :
    ∃ (e : G) (heP : e ∈ conjSubgroup x (Pc M₁ V₁)) (heH : e ∈ H₁),
      ψ (piK V₁ H₁ ⟨e, heH⟩) = s ∧
      hBarConj hβH' hβK₁ =
        hBarConj (Subgroup.le_normalizer heH) (le_normalizer_kOf V₁ H₁ heH) := by
  rw [hSx] at hsS
  obtain ⟨y₀, hy₀img, hy₀ψ⟩ := Subgroup.mem_map.mp hsS
  obtain ⟨e₀, he₀P, he₀pi⟩ := (mem_imgK_iff).mp hy₀img
  let e : G := (e₀ : G)
  have heP : e ∈ conjSubgroup x (Pc M₁ V₁) := he₀P
  have heH : e ∈ H₁ := conjSubgroup_le_of_le_of_mem hSh₁.Pc_le hxH₁ heP
  have heq₀ : (⟨e, heH⟩ : ↥H₁) = e₀ := Subtype.ext rfl
  have hpi : ψ (piK V₁ H₁ ⟨e, heH⟩) = s := by
    rw [heq₀, he₀pi]
    exact hy₀ψ
  have hθe : MulAut.congr ψ (hBarConj hβH' hβK₁) =
      MulAut.congr ψ (hBarConj (Subgroup.le_normalizer heH)
        (le_normalizer_kOf V₁ H₁ heH)) := by
    rw [hsθ, hBarConj_of_mem heH, CFSG.mulAut_congr_conj, hpi]
  exact ⟨e, heP, heH, hpi, (MulAut.congr ψ).injective hθe⟩

private theorem exists_conj_mul_eq_of_hBarConj_eq_one
    {M V M₁ V₁ H₁ : Subgroup G} {g x β e : G}
    (hS : Sec5Hyp M V) (hS₁ : Sec5Hyp M₁ V₁) (hSh₁ : Sec45Shape M₁ V₁ H₁ β)
    (hβsq : β * β = 1) (hβ1 : β ≠ 1) (hxH₁ : x ∈ H₁)
    (heP : e ∈ conjSubgroup x (Pc M₁ V₁)) (heK : e ∉ kOf V₁ H₁)
    (hP₁ : Pc M₁ V₁ = conjSubgroup g (Pc M V))
    (hconj_eq : ∀ z : G, conjSubgroup z V₁ = conjSubgroup (z * g) V)
    (hβxV : conjSubgroup β (conjSubgroup x V₁) = conjSubgroup x V₁)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf V₁ H₁ : Set G))
    (hbar2 : hBarConj hβH' hβK₁ * hBarConj hβH' hβK₁ = 1) (heH : e ∈ H₁)
    (hbar_eq : hBarConj hβH' hβK₁ =
      hBarConj (Subgroup.le_normalizer heH) (le_normalizer_kOf V₁ H₁ heH)) :
    ∀ u ∈ conjSubgroup x V₁,
      ∃ w ∈ Tim79a.xOf V₁ H₁, u * β = w * β * w⁻¹ := by
  have hbar2e : hBarConj (Subgroup.le_normalizer heH)
      (le_normalizer_kOf V₁ H₁ heH) *
      hBarConj (Subgroup.le_normalizer heH) (le_normalizer_kOf V₁ H₁ heH) = 1 := by
    have h1 := hbar2
    rwa [hbar_eq] at h1
  have hcbar : hBarConj
      (Subgroup.mul_mem _ hβH' (Subgroup.le_normalizer heH))
      (Subgroup.mul_mem _ hβK₁ (le_normalizer_kOf V₁ H₁ heH)) = 1 := by
    rw [hBarConj_mul hβH' hβK₁ (Subgroup.le_normalizer heH)
      (le_normalizer_kOf V₁ H₁ heH), hbar_eq]
    exact hbar2e
  have hcKmem : ∀ z ∈ H₁, ⁅β * e, z⁆ ∈ kOf V₁ H₁ :=
    (hBarConj_eq_one_iff (Subgroup.mul_mem _ hβH'
      (Subgroup.le_normalizer heH))
      (Subgroup.mul_mem _ hβK₁
        (le_normalizer_kOf V₁ H₁ heH))).mp hcbar
  exact exists_conj_mul_eq_of_mem_conjSubgroup hS.toRootHyp hS₁ hSh₁ hxH₁ heP heK
    (mem_centralizer_xOf_mul_of_mem_sup_zpowers hS hS₁ hSh₁ hcKmem hβsq hβ1 heP hP₁
      hconj_eq hβxV) (hconj_eq x)

private theorem exists_conjSubgroup_hV_mem_sup_of_classD
    {M V V₁ : Subgroup G} {g h x β u c₂ : G}
    (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hUxNE : conjSubgroup x V₁ ≠ conjSubgroup h V)
    (hconjVx : conjSubgroup x V₁ = conjSubgroup (x * g) V)
    (hc₂ : c₂ = x * g * h⁻¹)
    (hVxgSig : conjSubgroup (x * g) V ∈ sigmaSet M V)
    (hcommVxU' : ⁅conjSubgroup (x * g) V, conjSubgroup h V⁆ = ⊥)
    (hβU' : β ∈ conjSubgroup h V)
    (huVx : u ∈ conjSubgroup x V₁)
    (huβD' : u * β ∈ Tim78.classD (conjSubgroup h V)) :
    ∃ y₂ : G, conjSubgroup c₂ (conjSubgroup h V) = conjSubgroup (x * g) V ∧
      conjSubgroup c₂ (conjSubgroup h V) = conjSubgroup y₂ (conjSubgroup h V) ∧
      (u * β ∈ conjSubgroup h V ∨ u * β ∈ conjSubgroup y₂ (conjSubgroup h V)) := by
  have hc₂V : conjSubgroup c₂ (conjSubgroup h V) = conjSubgroup (x * g) V := by
    rw [hc₂, CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show x * g * h⁻¹ * h = x * g by group]
  have hOfc₂ : hOf (conjSubgroup h M) (conjSubgroup h V) c₂ =
      conjSubgroup (x * g) (Pc M V) ⊔ conjSubgroup h (Pc M V) := by
    rw [hOf, Pc_conjSubgroup,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup c₂ h (Pc M V),
      show c₂ * h = x * g by rw [hc₂]; group, sup_comm]
  have hIh : IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (hOf (conjSubgroup h M) (conjSubgroup h V) c₂) := by
    rw [hOfc₂]
    exact h512 M V hS (x * g) h hUh hVxgSig hcommVxU' (by rw [← hconjVx]; exact hUxNE)
  have hS_h : Sec5Hyp (conjSubgroup h M) (conjSubgroup h V) := hS.conj h
  have hc₂Sig : conjSubgroup c₂ (conjSubgroup h V) ∈
      sigmaSet (conjSubgroup h M) (conjSubgroup h V) :=
    (mem_sigmaSet_iff hS_h.toRootHyp.toHyp).mpr hIh
  have hSh : Sec45Shape (conjSubgroup h M) (conjSubgroup h V)
      (hOf (conjSubgroup h M) (conjSubgroup h V) c₂) c₂ := hS_h.shape hc₂Sig
  obtain ⟨y₂, hy₂H, -, hVy₂, -⟩ :=
    hS_h.toRootHyp.exists_mem_conj_eq_of_eq_sup
      (H := hOf (conjSubgroup h M) (conjSubgroup h V) c₂) (h₀ := c₂)
      hSh.Pc_le hSh.hH
  have hyV₂ : conjSubgroup y₂ (conjSubgroup h V) ≠ conjSubgroup h V := by
    rw [← hVy₂, hc₂V, ← hconjVx]
    exact hUxNE
  have hdmem : u * β ∈ conjSubgroup h V ⊔ conjSubgroup y₂ (conjSubgroup h V) := by
    have h1 : u ∈ conjSubgroup y₂ (conjSubgroup h V) := by
      rw [← hVy₂, hc₂V, ← hconjVx]
      exact huVx
    exact (conjSubgroup h V ⊔ conjSubgroup y₂ (conjSubgroup h V)).mul_mem
      (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hβU')
  refine ⟨y₂, hc₂V, hVy₂, ?_⟩
  exact (RootHyp.stmtI5b hS_h.toRootHyp)
    (hOf (conjSubgroup h M) (conjSubgroup h V) c₂) c₂ y₂ (u * β) hSh hy₂H hyV₂ hdmem
    huβD'

private theorem false_of_conjSubgroup_ne_base_of_classD
    {M V H₁ : Subgroup G} {g h x β u v₀ : G}
    (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    (hR : RootHyp M V)
    (hS₁ : Sec5Hyp (conjSubgroup g M) (conjSubgroup g V))
    (hSh₁ : Sec45Shape (conjSubgroup g M) (conjSubgroup g V) H₁ β)
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hxH₁ : x ∈ H₁)
    (hH₁eq : H₁ = Pc (conjSubgroup g M) (conjSubgroup g V) ⊔
      conjSubgroup β (Pc (conjSubgroup g M) (conjSubgroup g V)))
    (hβxV : conjSubgroup β (conjSubgroup x (conjSubgroup g V)) =
      conjSubgroup x (conjSubgroup g V))
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (hconj_eq : ∀ z : G, conjSubgroup z (conjSubgroup g V) = conjSubgroup (z * g) V)
    (hVxV : conjSubgroup (x * g) V ≠ V)
    (hv₀V : v₀ ∈ V) (hv₀1 : v₀ ≠ 1)
    (hv₀C : v₀ ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G))
    (hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥)
    (huVx : u ∈ conjSubgroup x (conjSubgroup g V)) (hu1 : u ≠ 1)
    (huβD' : u * β ∈ Tim78.classD (conjSubgroup h V)) :
    False := by
  have hconjVx : conjSubgroup x (conjSubgroup g V) = conjSubgroup (x * g) V :=
    hconj_eq x
  have hVxV' : conjSubgroup x (conjSubgroup g V) ≠ V := by
    rw [hconjVx]
    exact hVxV
  have hUxneU : conjSubgroup x (conjSubgroup g V) ≠ conjSubgroup g V :=
    conjSubgroup_ne_self_of_shape hS₁ hSh₁ hβxV hH₁eq
  have hUxSig : conjSubgroup x (conjSubgroup g V) ∈
      sigmaSet (conjSubgroup g M) (conjSubgroup g V) :=
    hSh₁.conjSubgroup_mem_sigmaSet hS₁.toRootHyp hxH₁ hUxneU
  have hcommVxV : ⁅V, conjSubgroup x (conjSubgroup g V)⁆ = ⊥ :=
    commutator_eq_bot_of_mem_centralizer_xOf hR hv₀V hv₀1 hv₀C hxH₁ hconjVx
  have hVxgSig : conjSubgroup (x * g) V ∈ sigmaSet M V :=
    isHMember_conjSubgroup_hOf hS hS₁ h512 hUg hUxSig hcommVxV hVxV' hconj_eq
  have hUxNE : conjSubgroup x (conjSubgroup g V) ≠ conjSubgroup h V :=
    conjSubgroup_xV_ne_conjSubgroup_hV hR hS₁ hSh₁ hxH₁ hβU' hβ1 hne
  have hcommVxU' : ⁅conjSubgroup (x * g) V, conjSubgroup h V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommVx
  let c₂ : G := x * g * h⁻¹
  obtain ⟨y₂, hc₂V, hVy₂, hd⟩ :=
    exists_conjSubgroup_hV_mem_sup_of_classD (c₂ := c₂) hS h512 hUh hUxNE hconjVx
      rfl hVxgSig hcommVxU' hβU' huVx huβD'
  rcases hd with hd | hd
  · exact false_of_mem_sup_of_ne hR hUxNE hconjVx hβU' hβ1 huVx hu1 (Or.inl hd)
  · refine false_of_mem_sup_of_ne hR hUxNE hconjVx hβU' hβ1 huVx hu1 (Or.inr ?_)
    rw [← hVy₂, hc₂V, ← hconjVx] at hd
    exact hd

private theorem exists_classD_mul_of_conj_eq
    {M V H₁ : Subgroup G} {g h x β : G}
    (hR : RootHyp M V)
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1)
    (hβu : ∀ u ∈ conjSubgroup x (conjSubgroup g V),
      ∃ w ∈ Tim79a.xOf (conjSubgroup g V) H₁, u * β = w * β * w⁻¹) :
    ∃ u : G, u ∈ conjSubgroup x (conjSubgroup g V) ∧ u ≠ 1 ∧
      u * β ∈ Tim78.classD V ∧ u * β ∈ Tim78.classD (conjSubgroup h V) := by
  have hVxbot : conjSubgroup x (conjSubgroup g V) ≠ ⊥ := by
    intro hbot
    have h1 : conjSubgroup g V = ⊥ :=
      (conjSubgroup_eq_bot_iff (g := x) (A := conjSubgroup g V)).mp hbot
    exact hR.toHyp.ne_bot ((conjSubgroup_eq_bot_iff (g := g) (A := V)).mp h1)
  obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVxbot
  let u : G := (u₀ : G)
  have huVx : u ∈ conjSubgroup x (conjSubgroup g V) := u₀.2
  have hu1 : u ≠ 1 := fun hh => hu₀1 (Subtype.ext hh)
  obtain ⟨w, -, huw⟩ := hβu u huVx
  have hβDV : β ∈ Tim78.classD V := Tim78.mem_classD_of_mem_conjSubgroup hβU' hβ1
  have huβD : u * β ∈ Tim78.classD V := by
    rw [huw]
    exact Tim78.mem_classD_conj hβDV w
  have hβD' : β ∈ Tim78.classD (conjSubgroup h V) :=
    Tim78.mem_classD_of_mem_conjSubgroup (B := conjSubgroup h V) (g := 1) (a := β)
      (by rwa [conjSubgroup_one]) hβ1
  have huβD' : u * β ∈ Tim78.classD (conjSubgroup h V) := by
    rw [huw]
    exact Tim78.mem_classD_conj hβD' w
  exact ⟨u, huVx, hu1, huβD, huβD'⟩

private theorem false_of_inner_sylow
    {M V H₁ : Subgroup G} {g h x β v₀ : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {S : Subgroup SL(2, F)}
    (ψ : HBar (conjSubgroup g V) H₁ ≃* SL(2, F))
    (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    (hR : RootHyp M V)
    (hS₁ : Sec5Hyp (conjSubgroup g M) (conjSubgroup g V))
    (hSh₁ : Sec45Shape (conjSubgroup g M) (conjSubgroup g V) H₁ β)
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1) (hβsq : β * β = 1)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G))
    (hxH₁ : x ∈ H₁)
    (hH₁eq : H₁ = Pc (conjSubgroup g M) (conjSubgroup g V) ⊔
      conjSubgroup β (Pc (conjSubgroup g M) (conjSubgroup g V)))
    (hβxV : conjSubgroup β (conjSubgroup x (conjSubgroup g V)) =
      conjSubgroup x (conjSubgroup g V))
    (hconj_eq : ∀ z : G, conjSubgroup z (conjSubgroup g V) = conjSubgroup (z * g) V)
    (hP₁ : Pc (conjSubgroup g M) (conjSubgroup g V) = conjSubgroup g (Pc M V))
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hv₀V : v₀ ∈ V) (hv₀1 : v₀ ≠ 1)
    (hv₀C : v₀ ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G))
    (hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥)
    (hSx : S = (imgK (conjSubgroup g V) H₁
      (conjSubgroup x (Pc (conjSubgroup g M) (conjSubgroup g V)))).map ψ.toMonoidHom)
    (hinner : ∃ s : SL(2, F), s ∈ S ∧
      MulAut.congr ψ (hBarConj hβH' hβK₁) = MulAut.conj s) :
    False := by
  obtain ⟨s, hsS, hsθ⟩ := hinner
  obtain ⟨e, heP, heH, hpi, hbar_eq⟩ :=
    exists_mem_conj_Pc_of_sylow_image ψ hSh₁ hxH₁ hβH' hβK₁ hsS hSx hsθ
  have hbar2 := hBarConj_mul_self_eq_one hβsq hβH' hβK₁
  by_cases heK : e ∈ kOf (conjSubgroup g V) H₁
  · have hs1 : s = 1 := by
      rw [← hpi, (piK_eq_one_iff _).mpr heK, map_one]
    exact false_of_mem_kOf ψ hR hS₁ hSh₁ hβsq hβU' hβ1 hne hβH' hβK₁ hsθ hs1
  · have hβu := exists_conj_mul_eq_of_hBarConj_eq_one hS hS₁ hSh₁ hβsq hβ1 hxH₁ heP
      heK hP₁ hconj_eq hβxV hβH' hβK₁ hbar2 heH hbar_eq
    obtain ⟨u, huVx, hu1, huβD, huβD'⟩ :=
      exists_classD_mul_of_conj_eq hR hβU' hβ1 hβu
    by_cases hVxV : conjSubgroup (x * g) V = V
    · exact false_of_conjSubgroup_mul_eq_base hS hUh hβU' hβ1 hVxV (hconj_eq x)
        huVx hu1 huβD
    · exact false_of_conjSubgroup_ne_base_of_classD hS h512 hR hS₁ hSh₁ hUg hUh
        hne hxH₁ hH₁eq hβxV hβU' hβ1 hconj_eq hVxV hv₀V hv₀1 hv₀C hcommVx huVx hu1
        huβD'

private theorem exists_normalizer_and_centralizer
    {M V H₁ : Subgroup G} {g h β : G}
    (hS : Sec5Hyp M V)
    (hS₁ : Sec5Hyp (conjSubgroup g M) (conjSubgroup g V))
    (hSh₁ : Sec45Shape (conjSubgroup g M) (conjSubgroup g V) H₁ β)
    (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hβU' : β ∈ conjSubgroup h V) (hβsq : β * β = 1)
    (hβne : conjSubgroup β (conjSubgroup g V) ≠ conjSubgroup g V)
    (hH₁eq : H₁ = Pc (conjSubgroup g M) (conjSubgroup g V) ⊔
      conjSubgroup β (Pc (conjSubgroup g M) (conjSubgroup g V))) :
    conjSubgroup β H₁ = H₁ ∧
      β ∈ Subgroup.normalizer (H₁ : Set G) ∧
      β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G) ∧
      (∃ v₀ ∈ V, v₀ ≠ 1 ∧
        v₀ ∈ Subgroup.centralizer (Tim79a.xOf (conjSubgroup g V) H₁ : Set G)) := by
  obtain ⟨y, hyH₁, -, hVy, -⟩ :=
    hS₁.toRootHyp.exists_mem_conj_eq_of_eq_sup (H := H₁) (h₀ := β) hSh₁.Pc_le hH₁eq
  have hβH₁ : conjSubgroup β H₁ = H₁ := by
    rw [hH₁eq, conjSubgroup_sup, CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hβsq,
      conjSubgroup_one]
    exact sup_comm _ _
  have hβH' : β ∈ Subgroup.normalizer (H₁ : Set G) := conjSubgroup_eq_self_iff.mp hβH₁
  have hβK₁ : β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G) :=
    mem_normalizer_kOf_of_conj_eq hβH₁ hyH₁ hVy
  refine ⟨hβH₁, hβH', hβK₁, ?_⟩
  exact exists_mem_centralizer_xOf_of_normalizer hS hS₁ hSh₁ hUg hUh hβU' hβsq hβne
    hH₁eq hyH₁ hVy

private theorem exists_sylow_data_of_shape
    {M V H₁ : Subgroup G} {g h β : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar (conjSubgroup g V) H₁ ≃* SL(2, F))
    (hR : RootHyp M V)
    (hS₁ : Sec5Hyp (conjSubgroup g M) (conjSubgroup g V))
    (hSh₁ : Sec45Shape (conjSubgroup g M) (conjSubgroup g V) H₁ β)
    (hβU' : β ∈ conjSubgroup h V) (hβ1 : β ≠ 1) (hβsq : β * β = 1)
    (hβH' : β ∈ Subgroup.normalizer (H₁ : Set G))
    (hβK₁ : β ∈ Subgroup.normalizer (kOf (conjSubgroup g V) H₁ : Set G))
    (hβH₁ : conjSubgroup β H₁ = H₁) :
    ∃ (S : Subgroup SL(2, F)) (x : G), x ∈ H₁ ∧
      S = (imgK (conjSubgroup g V) H₁
        (conjSubgroup x (Pc (conjSubgroup g M) (conjSubgroup g V)))).map ψ.toMonoidHom ∧
      conjSubgroup β (conjSubgroup x (conjSubgroup g V)) = conjSubgroup x (conjSubgroup g V) ∧
      (∀ z : G, conjSubgroup β (conjSubgroup z (conjSubgroup g V)) =
          conjSubgroup z (conjSubgroup g V) →
        ⁅conjSubgroup h V, conjSubgroup (z * g) V⁆ = ⊥) ∧
      ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥ ∧
      ((∃ s : SL(2, F), s ∈ S ∧
          MulAut.congr ψ (hBarConj hβH' hβK₁) = MulAut.conj s) ∨
        ∃ S' : Subgroup SL(2, F), (∀ a ∈ S', a * a = 1) ∧
          Nat.card S' = Fintype.card F ∧ S' ≠ S ∧
          S'.map (MulAut.congr ψ (hBarConj hβH' hβK₁)).toMonoidHom = S') := by
  have hθ2 : MulAut.congr ψ (hBarConj hβH' hβK₁) *
      MulAut.congr ψ (hBarConj hβH' hβK₁) = 1 := by
    rw [← map_mul, hBarConj_mul_self_eq_one hβsq hβH' hβK₁, map_one]
  obtain ⟨S, hSexp, hScard, hSfix, hcase⟩ :=
    Sec2.MulAut.exists_sylow_inner_or_two_fixed (MulAut.congr ψ (hBarConj hβH' hβK₁)) hθ2
  obtain ⟨x, hxH₁, hSx⟩ := hSh₁.exists_mem_eq_map_imgK hS₁.toRootHyp ψ hSexp hScard
  have hfixx : imgK (conjSubgroup g V) H₁
        (conjSubgroup β (conjSubgroup x (Pc (conjSubgroup g M) (conjSubgroup g V)))) =
      imgK (conjSubgroup g V) H₁
        (conjSubgroup x (Pc (conjSubgroup g M) (conjSubgroup g V))) :=
    imgK_conjSubgroup_eq_of_sylow_fixed hβH' hβK₁ ψ hSh₁.Pc_le hxH₁ (by
      rw [← hSx]
      exact hSfix)
  have hβxV : conjSubgroup β (conjSubgroup x (conjSubgroup g V)) =
      conjSubgroup x (conjSubgroup g V) :=
    hSh₁.conj_eq_of_imgK_eq hS₁.toRootHyp hβH₁ hxH₁ hfixx
  have root_comm : ∀ z : G, conjSubgroup β (conjSubgroup z (conjSubgroup g V)) =
        conjSubgroup z (conjSubgroup g V) →
      ⁅conjSubgroup h V, conjSubgroup (z * g) V⁆ = ⊥ := by
    intro z hz
    rw [Subgroup.commutator_comm]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hR.conj_le_centralizer_of_mem_normalizer hβU' hβ1 ?_)
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_self_iff.mp hz
  have hcommVx : ⁅conjSubgroup h V, conjSubgroup (x * g) V⁆ = ⊥ := root_comm x hβxV
  exact ⟨S, x, hxH₁, hSx, hβxV, root_comm, hcommVx, hcase⟩

private theorem core (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    {g h : G} (hUg : conjSubgroup g V ∈ sigmaSet M V)
    (hUh : conjSubgroup h V ∈ sigmaSet M V)
    (hne : ⁅conjSubgroup g V, conjSubgroup h V⁆ ≠ ⊥)
    (hβc : ∀ β ∈ conjSubgroup h V,
      ⁅conjSubgroup g V, conjSubgroup β (conjSubgroup g V)⁆ = ⊥) : False := by
  classical
  have hR := hS.toRootHyp
  obtain ⟨β, hβU', hβ1, hβsq, hβne⟩ :=
    exists_involution_mem_conjSubgroup_not_conj_eq hS hne
  let M₁ : Subgroup G := conjSubgroup g M
  let V₁ : Subgroup G := conjSubgroup g V
  let P₁ : Subgroup G := Pc M₁ V₁
  have hS₁ : Sec5Hyp M₁ V₁ := hS.conj g
  have hP₁ : P₁ = conjSubgroup g (Pc M V) := Pc_conjSubgroup M V g
  have hconj_eq : ∀ z : G, conjSubgroup z V₁ = conjSubgroup (z * g) V := fun z =>
    CGT.Timmesfeld75.conjSubgroup_conjSubgroup z g V

  have hSh₁ : Sec45Shape M₁ V₁ (hOf M₁ V₁ β) β :=
    shape_of_conjSubgroup hS h512 hβc hUg hUh hβU' hβne
  let H₁ : Subgroup G := hOf M₁ V₁ β
  have hH₁eq : H₁ = P₁ ⊔ conjSubgroup β P₁ := rfl
  obtain ⟨hβH₁, hβH', hβK₁, v₀, hv₀V, hv₀1, hv₀C⟩ :=
    exists_normalizer_and_centralizer hS hS₁ hSh₁ hUg hUh hβU' hβsq hβne hH₁eq

  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSh₁.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  obtain ⟨S, x, hxH₁, hSx, hβxV, root_comm, hcommVx, hcase⟩ :=
    exists_sylow_data_of_shape ψ hR hS₁ hSh₁ hβU' hβ1 hβsq hβH' hβK₁ hβH₁
  rcases hcase with hinner | ⟨S', hS'exp, hS'card, hS'ne, hS'fix⟩
  ·
    exact false_of_inner_sylow ψ hS h512 hR hS₁ hSh₁ hβU' hβ1 hβsq hne hβH' hβK₁
      hxH₁ hH₁eq hβxV hconj_eq hP₁ hUg hUh hv₀V hv₀1 hv₀C hcommVx hSx hinner
  ·
    exact false_of_fixing_second_sylow ψ hR hS₁ hSh₁ hne hxH₁ hβH₁ hβH' hβK₁ root_comm
      hcommVx hconj_eq hSx hS'exp hS'card hS'ne hS'fix


private theorem commutator_eq_bot_of_isPGroup (hS : Sec5Hyp M V)
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V')
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hT : IsPGroup 2 ↥(U ⊔ U')) : ⁅U, U'⁆ = ⊥ := by
  classical
  suffices H : ∀ n : ℕ, ∀ U U' : Subgroup G, U ∈ sigmaSet M V → U' ∈ sigmaSet M V →
      Nat.card ↥(U ⊔ U') ≤ n → IsPGroup 2 ↥(U ⊔ U') → ⁅U, U'⁆ = ⊥ from
    H _ U U' hU hU' le_rfl hT
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U U' hU hU' hcard hT
    obtain ⟨g, hUeq, hHg⟩ := hU
    obtain ⟨h, hU'eq, hHh⟩ := hU'
    have hUg : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
    have hUh : conjSubgroup h V ∈ sigmaSet M V := ⟨h, rfl, hHh⟩
    rw [hUeq, hU'eq] at hT hcard ⊢
    by_contra hne
    have hUlt : conjSubgroup g V < conjSubgroup g V ⊔ conjSubgroup h V := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      have hle : conjSubgroup h V ≤ conjSubgroup g V := heq ▸ le_sup_right
      have hcard' : Nat.card ↥(conjSubgroup g V) ≤ Nat.card ↥(conjSubgroup h V) := by
        rw [card_conjSubgroup, card_conjSubgroup]
      have hU'eq' : conjSubgroup h V = conjSubgroup g V :=
        Subgroup.eq_of_le_of_card_ge hle hcard'
      apply hne
      rw [hU'eq', Subgroup.commutator_self_eq_bot_iff]
      exact (hS.toRootHyp.toHyp.elem.map (MulAut.conj g).toMonoidHom).1
    obtain ⟨X, hUX, hXT, hNX⟩ := CFSG.exists_normal_of_lt_of_isPGroup hT hUlt
    have key : ∀ β ∈ conjSubgroup h V,
        ⁅conjSubgroup g V, conjSubgroup β (conjSubgroup g V)⁆ = ⊥ := by
      intro β hβ
      have hβM : β ∈ M := (hS.le_M_of_mem_sigmaSet hUh).1 hβ
      have hβSig : conjSubgroup β (conjSubgroup g V) ∈ sigmaSet M V :=
        hS.conj_mem_sigmaSet hβM hUg
      have hβT : β ∈ conjSubgroup g V ⊔ conjSubgroup h V := Subgroup.mem_sup_right hβ
      have hXle : conjSubgroup β (conjSubgroup g V) ≤ X := by
        intro z hz
        obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.mp hz
        rw [← huz]
        change β * u * β⁻¹ ∈ X
        exact (Subgroup.mem_normalizer_iff.mp (hNX hβT) u).mp (hUX hu)
      have hXsup : conjSubgroup g V ⊔ conjSubgroup β (conjSubgroup g V) ≤ X :=
        sup_le hUX hXle
      have hT' : IsPGroup 2 ↥(conjSubgroup g V ⊔ conjSubgroup β (conjSubgroup g V)) := by
        refine hT.to_le (sup_le le_sup_left ?_)
        calc conjSubgroup β (conjSubgroup g V)
            ≤ conjSubgroup β (conjSubgroup g V ⊔ conjSubgroup h V) := conjSubgroup_mono le_sup_left
          _ = conjSubgroup g V ⊔ conjSubgroup h V :=
              conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hβT)
      have hcardlt : Nat.card ↥(conjSubgroup g V ⊔ conjSubgroup β (conjSubgroup g V)) < n := by
        have h1 : Nat.card ↥(conjSubgroup g V ⊔ conjSubgroup β (conjSubgroup g V)) ≤
            Nat.card ↥X := Subgroup.card_le_of_le hXsup
        have h2 : Nat.card ↥X < Nat.card ↥(conjSubgroup g V ⊔ conjSubgroup h V) :=
          Subgroup.card_lt_of_lt hXT
        omega
      exact ih (Nat.card ↥(conjSubgroup g V ⊔ conjSubgroup β (conjSubgroup g V))) hcardlt
        (conjSubgroup g V) (conjSubgroup β (conjSubgroup g V)) hUg hβSig le_rfl hT'
    exact core hS h512 hUg hUh hne key

theorem stmt513 (hS : Sec5Hyp M V)
    (h57 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt57 M' V')
    (h512 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt512 M' V') :
    Sec5.Stmt513 M V := by
  intro U hU U' hU'
  rcases h57 M V hS U hU U' hU' with ⟨hle, hc⟩ | ⟨hcap, hL2⟩ | ⟨-, hP2, hne⟩
  · exact Or.inl ⟨hc, hle⟩
  · exact Or.inr ⟨hL2, by rw [inf_comm]; exact hcap⟩
  · exact absurd (commutator_eq_bot_of_isPGroup hS h512 hU hU' hP2) hne

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81

end
