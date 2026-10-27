module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import CFSG.LocalAnalysis.StandardType.GGNbrTransvectionDichotomy
import CFSG.LocalAnalysis.StandardType.GGTBWNorm

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

section GlueIdentAutAux

variable {Bs K : Subgroup G} {z : G}

private theorem glueIdentAutAux_exists
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    ∃ a ∈ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range,
      GGOverGamma hN φ a := by
  classical
  obtain ⟨g, hgH, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := hNK ⟨hgN, hgH⟩
  let c : MulAut ↥K := K.normalizerMonoidHom ⟨g, hgK⟩
  have hcN : c ∈ Subgroup.normalizer
      (((ggGamma K hN).range : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) :=
    normalizerMonoidHom_mem_normalizer_range_ggGamma hN hgN hgK
  let a : MulAut ↥(ggGamma K hN).range := ggConjAut (ggGamma K hN).range hcN
  have ha : a ∈ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range :=
    ggConjAut_mem_ggAutomizer (H := ⊤) (Subgroup.mem_top c) hcN
  refine ⟨a, ha, ?_⟩
  intro b
  apply Subtype.ext
  have hgb : g * (b : G) * g⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hgN b).mp b.2
  have hb : φ b = (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) := Subtype.ext (hgφ b)
  dsimp only [a]
  rw [ggConjAut_apply]
  simp only [MonoidHom.coe_rangeRestrict]
  rw [hb, ggGamma_conj_normalizer K hN ⟨g, hgK⟩ b hgb]

private noncomputable def glueIdentAutAux_phi
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (φ : ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    MulAut ↥(ggGamma K hN).range :=
  Classical.choose (glueIdentAutAux_exists hN hNK φ.2)

private theorem glueIdentAutAux_phi_mem
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (φ : ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    glueIdentAutAux_phi hN hNK φ ∈
      ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range :=
  (Classical.choose_spec (glueIdentAutAux_exists hN hNK φ.2)).1

private theorem glueIdentAutAux_phi_over
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (φ : ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    GGOverGamma hN (φ : MulAut ↥Bs) (glueIdentAutAux_phi hN hNK φ) :=
  (Classical.choose_spec (glueIdentAutAux_exists hN hNK φ.2)).2

private noncomputable def glueIdentAutAux_hom
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs →*
      MulAut ↥(ggGamma K hN).range where
  toFun := glueIdentAutAux_phi hN hNK
  map_one' := by
    exact GGOverGamma.unique (glueIdentAutAux_phi_over hN hNK 1) GGOverGamma.one
  map_mul' := fun φ ψ => by
    exact GGOverGamma.unique (glueIdentAutAux_phi_over hN hNK (φ * ψ))
      ((glueIdentAutAux_phi_over hN hNK φ).mul (glueIdentAutAux_phi_over hN hNK ψ))

private theorem glueIdentAutAux_hom_ker_eq_one
    (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs)
    (hNT : GGNoTransvection 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    {φ : ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs}
    (hφ : glueIdentAutAux_hom hN hNK φ = 1) : φ = 1 := by
  classical
  have hover : GGOverGamma hN (φ : MulAut ↥Bs)
      (glueIdentAutAux_hom hN hNK φ) :=
    glueIdentAutAux_phi_over hN hNK φ
  rw [hφ] at hover
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hVp : ∀ v : ↥Bs, v ^ 3 = 1 := fun v => Subtype.ext (by simpa using hBs.2 v v.2)
  let N : Subgroup ↥Bs := (Subgroup.zpowers z).subgroupOf Bs
  have hNcard : Nat.card N ≤ 3 := by
    change Nat.card ↥((Subgroup.zpowers z).subgroupOf Bs) ≤ 3
    rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hz)).toEquiv,
      Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hBs.2 z hz))
  have hκN : ∀ v : ↥Bs, v⁻¹ * (φ : MulAut ↥Bs) v ∈ N := by
    intro v
    have hgamma : ggGamma K hN ((φ : MulAut ↥Bs) v) = ggGamma K hN v := by
      have hv := hover v
      simp only [MulAut.one_apply] at hv
      simpa only [MonoidHom.coe_rangeRestrict] using Subtype.ext_iff.mp hv
    have hcent : ((v⁻¹ * (φ : MulAut ↥Bs) v : ↥Bs) : G) ∈
        Subgroup.centralizer (K : Set G) := by
      rw [← ggGamma_eq_one_iff K hN (v⁻¹ * (φ : MulAut ↥Bs) v)]
      rw [map_mul, map_inv, hgamma, inv_mul_cancel]
    have hmem : ((v⁻¹ * (φ : MulAut ↥Bs) v : ↥Bs) : G) ∈ Subgroup.zpowers z := by
      have hinf : ((v⁻¹ * (φ : MulAut ↥Bs) v : ↥Bs) : G) ∈
          Bs ⊓ Subgroup.centralizer (K : Set G) :=
        ⟨(v⁻¹ * (φ : MulAut ↥Bs) v).2, hcent⟩
      rwa [hker] at hinf
    exact hmem
  have hfix : ∀ n ∈ N, (φ : MulAut ↥Bs) n = n := by
    intro n hn
    obtain ⟨g, hgH, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp φ.2
    have hgz : z * g = g * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp hgH).symm
    have hzg : z ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgz
    have hle : Subgroup.zpowers z ≤ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.zpowers_le.mpr hzg
    have hgn : g * (n : G) = (n : G) * g :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (hle (Subgroup.mem_subgroupOf.mp hn))).symm
    apply Subtype.ext
    rw [hgφ n, hgn]
    group
  have hmem : (φ : MulAut ↥Bs) ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgH, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp φ.2
    exact ⟨g, Subgroup.mem_top g, hgN, hgφ⟩
  rcases mulAut_eq_one_or_transvection Nat.prime_three hVc hVp N hNcard
      (φ : MulAut ↥Bs) hκN hfix with h1 | h2
  · exact Subtype.ext h1
  · exact absurd h2 (hNT (φ : MulAut ↥Bs) hmem)

private theorem glueIdentAutAux_hom_injective
    (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs)
    (hNT : GGNoTransvection 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Function.Injective (glueIdentAutAux_hom (z := z) hN hNK) := by
  intro φ ψ hφψ
  have h1 : glueIdentAutAux_hom (z := z) hN hNK (φ⁻¹ * ψ) = 1 := by
    rw [map_mul, map_inv, hφψ, inv_mul_cancel]
  have h2 : φ⁻¹ * ψ = 1 :=
    glueIdentAutAux_hom_ker_eq_one hBs hz hNT hN hNK hker h1
  exact inv_mul_eq_one.mp h2

end GlueIdentAutAux

theorem exists_le_automizer_of_le_centralizer {Bs K : Subgroup G} {z : G}
    (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hNT : GGNoTransvection 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    {S : Subgroup (MulAut ↥Bs)}
    (hS : S ≤ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    ∃ W : Subgroup (MulAut ↥(ggGamma K hN).range),
      W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range ∧
        Nat.card W = Nat.card S := by
  classical
  let A : Subgroup (MulAut ↥Bs) :=
    ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs
  let E : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let Φ : A →* MulAut ↥E := glueIdentAutAux_hom (z := z) hN hNK
  let W : Subgroup (MulAut ↥E) := (S.subgroupOf A).map Φ
  have hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) E := by
    intro w hw
    rcases Subgroup.mem_map.mp hw with ⟨φ, -, rfl⟩
    exact glueIdentAutAux_phi_mem hN hNK φ
  have hinj : Function.Injective Φ :=
    glueIdentAutAux_hom_injective hBs hz hNT hN hNK hker
  have hcard : Nat.card W = Nat.card S := by
    rw [Subgroup.card_map_of_injective (f := Φ) (K := S.subgroupOf A) hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  exact ⟨W, hW, hcard⟩

theorem card_automizer_centralizer_le {Bs K : Subgroup G} {z : G}
    (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hNT : GGNoTransvection 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    Nat.card (ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) ≤
      Nat.card (ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range) := by
  obtain ⟨W, hW, hcard⟩ := exists_le_automizer_of_le_centralizer hBs hz hNT hN hNK hker le_rfl
  rw [← hcard]
  exact Subgroup.card_le_of_le hW

end CFSG.StandardType.FrameRoute

end
