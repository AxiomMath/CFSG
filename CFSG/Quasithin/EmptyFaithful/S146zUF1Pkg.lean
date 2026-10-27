module

public import CFSG.Quasithin.EmptyFaithful.S146zUC1Data
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Def
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Ker
import CFSG.Quasithin.EmptyFaithful.SBc16SAut
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open CFSG.Quasithin.S153M
open scoped Pointwise commutatorElement

namespace S146zU

theorem centreless_of_L216Cover {X : Type} [Group X] {N : Subgroup X} (h : L216Cover ↥N) :
    ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
  obtain ⟨e⟩ := h
  intro n hn hc
  have hcen : e ⟨n, hn⟩ ∈ Subgroup.center SBc16.L216 := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨m', rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc m' m'.2).symm
  rw [SBc16.center_L216, Subgroup.mem_bot] at hcen
  have : (⟨n, hn⟩ : ↥N) = 1 := e.injective (by rw [hcen, map_one])
  exact congrArg Subtype.val this

namespace UF1

section Kernel

variable {G : Type} [Group G] [Finite G] {H K W U : Subgroup G}

omit [Finite G] in
theorem mem_openPCore_iff_mem_pCoreOf (x : ↥H) :
    x ∈ CFSG.Open.pCore 2 ↥H ↔ (x : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff_open x).symm

theorem ker_inf_le_of_simple (hK : K ∈ cComp H)
    (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hKnt : ¬ K.subgroupOf H ≤ (actH hWN hUN).ker) :
    ∀ k ∈ K.subgroupOf H, actH hWN hUN k = 1 → k ∈ CFSG.Open.pCore 2 ↥H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨e'⟩ := e
  have : IsSimpleGroup SBc16.L216 := SBc16.isSimpleGroup_L216
  have : IsSimpleGroup (↥K ⧸ CFSG.Open.pCore 2 ↥K) := e'.isSimpleGroup
  let ρ₁ : ↥K →* MulAut ↥(tildeOf W U) := (actH hWN hUN).comp (Subgroup.inclusion hKH)
  have hO : CFSG.Open.pCore 2 ↥K ≤ ρ₁.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have h1 : (k : G) ∈ pCoreOf 2 K := ⟨k, hk, rfl⟩
    have h2 : (k : G) ∈ pCoreOf 2 H :=
      pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hK) h1
    exact hQ _ h2
  have hne : ρ₁.ker ≠ ⊤ := by
    intro htop
    apply hKnt
    intro k hk
    have : (⟨k, Subgroup.mem_subgroupOf.mp hk⟩ : ↥K) ∈ ρ₁.ker := htop ▸ Subgroup.mem_top _
    exact this
  have hker := ker_eq_of_isSimpleGroup_quotient ρ₁ hO hne
  intro k hk hφk
  have hk' : (⟨k, Subgroup.mem_subgroupOf.mp hk⟩ : ↥K) ∈ ρ₁.ker := hφk
  rw [hker] at hk'
  have h1 : (k : G) ∈ pCoreOf 2 K := ⟨_, hk', rfl⟩
  exact (mem_openPCore_iff_mem_pCoreOf k).mpr
    (pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hK) h1)

theorem mem_pCoreOf_of_commute_image {T V L V₁ Vp : Subgroup G}
    (hF : HypF918 T V L V₁ Vp H K) {t : G} (htH : t ∈ H)
    (hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H)
    (hK₀eq : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H)
    (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hcen : ∀ g ∈ H, (∀ k ∈ conjClosure K T, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      g ∈ pCoreOf 2 H)
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hKnt : ¬ K.subgroupOf H ≤ (actH hWN hUN).ker)
    (hφc : ∀ a ∈ (K.subgroupOf H).map (actH hWN hUN),
      ∀ b ∈ ((K.subgroupOf H).map (MulAut.conj (⟨t, htH⟩ : ↥H)).toMonoidHom).map (actH hWN hUN),
        a * b = b * a) :
    ∀ g : ↥H, (∀ κ ∈ (conjClosure K T).subgroupOf H,
      actH hWN hUN g * actH hWN hUN κ = actH hWN hUN κ * actH hWN hUN g) →
      (g : G) ∈ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  set t' : ↥H := ⟨t, htH⟩ with ht'
  set φ := actH hWN hUN with hφ
  have hmapconj := map_conj_subgroupOf hKH htH
  have hsup : K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom =
      (conjClosure K T).subgroupOf H := by
    rw [hmapconj, ← Subgroup.subgroupOf_sup hKH hKtH, hK₀eq]
  have hQ' : CFSG.Open.pCore 2 ↥H ≤ φ.ker := fun x hx =>
    hQ x ((mem_openPCore_iff_mem_pCoreOf x).mp hx)
  have hcomm' : ∀ a ∈ K.subgroupOf H, ∀ b ∈ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom,
      a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCore 2 ↥H := by
    intro a ha b hb
    rw [hmapconj] at hb
    refine (mem_openPCore_iff_mem_pCoreOf _).mpr (hcomm ?_)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
  have hK : L216Cover ↥((K.subgroupOf H).map φ) :=
    UC1.actH_image_L216Cover hF.K_cComp e hWN hUN hQ hKnt
  have hker := ker_inf_le_of_simple hF.K_cComp e hWN hUN hQ hKnt
  have hkerSup := ker_inf_sup_le φ hQ' t' hcomm' hφc (centreless_of_L216Cover hK) hker
  intro g hg
  refine hcen g g.2 fun k hk => ?_
  have hkH : k ∈ H := hF.K₀_le_H hk
  set κ : ↥H := ⟨k, hkH⟩ with hκ
  have hκmem : κ ∈ (conjClosure K T).subgroupOf H := hk
  have hn : (g : G) * k * (g : G)⁻¹ ∈ conjClosure K T :=
    (Subgroup.mem_normalizer_iff.mp (hF.K₀_normal g.2) k).mp hk
  have hcm : g * κ * g⁻¹ * κ⁻¹ ∈ (conjClosure K T).subgroupOf H := by
    refine Subgroup.mul_mem _ hn (Subgroup.inv_mem _ hκmem)
  have hφ1 : φ (g * κ * g⁻¹ * κ⁻¹) = 1 := by
    have h1 := hg κ hκmem
    simp only [map_mul, map_inv]
    rw [h1]
    group
  have hres := hkerSup _ (hsup ▸ hcm) hφ1
  exact (mem_openPCore_iff_mem_pCoreOf _).mp hres

end Kernel

end UF1

section Main

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem pairPkg_of_ffSection (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hF : HypF918 T V L V₁ Vp H K) (hS : SQTKGroup ↥H) (hHK₀ : H = conjClosure K T ⊔ T) {t : G}
    (htT : t ∈ T) (hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H)
    (hK₀eq : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H)
    (hperm : ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K : Set G))
    (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hcen : ∀ g ∈ H, (∀ k ∈ conjClosure K T, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      g ∈ pCoreOf 2 H)
    {W U : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hnt : ¬ (conjClosure K T).subgroupOf H ≤ (actH hWN hUN).ker)
    (hFF : IsFFModule (actH hWN hUN).range) :
    (∀ x : ↥H, actH hWN hUN x = 1 → (x : G) ∈ pCoreOf 2 H) ∧
      ∃ (L₁ L₂ : Subgroup (MulAut ↥(tildeOf W U))) (τ : MulAut ↥(tildeOf W U)),
        PairPkg (actH hWN hUN).range L₁ L₂ τ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have htH : t ∈ H := hF.T_le_H htT
  set t' : ↥H := ⟨t, htH⟩ with ht'
  set φ := actH hWN hUN with hφ
  have hmapconj := map_conj_subgroupOf hKH htH
  have hsup : K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom =
      (conjClosure K T).subgroupOf H := by
    rw [hmapconj, ← Subgroup.subgroupOf_sup hKH hKtH, hK₀eq]
  have hnt' : ¬ K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom ≤ φ.ker := by
    rw [hsup]
    exact hnt
  have hKnt : ¬ K.subgroupOf H ≤ φ.ker := by
    intro h
    apply hnt'
    refine sup_le h ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk1 : φ k = 1 := MonoidHom.mem_ker.mp (h hk)
    rw [MonoidHom.mem_ker]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hk1, mul_one,
      mul_inv_cancel]
  have hK : L216Cover ↥((K.subgroupOf H).map φ) :=
    UC1.actH_image_L216Cover hF.K_cComp e hWN hUN hQ hKnt
  obtain ⟨hJ, hTN, hc, hnorm, -, hL₂⟩ := kActionTwo_data_L216 hA21 h56 hF hS hHK₀ htT hKt hK₀eq
    hcomm hperm e hWN hUN hQ hnt hFF
  have key := UF1.mem_pCoreOf_of_commute_image hF htH hKt hK₀eq hcomm e hcen hWN hUN hQ hKnt hc
  refine ⟨fun x hx => key x fun κ _ => by rw [hx, one_mul, mul_one],
    (K.subgroupOf H).map φ, ((K.subgroupOf H).map (MulAut.conj t').toMonoidHom).map φ, φ t', ?_⟩
  have hK₂ : L216Cover ↥(((K.subgroupOf H).map (MulAut.conj t').toMonoidHom).map φ) := by
    rw [hL₂]
    exact UC1.L216Cover_map_conj (φ t') hK
  refine ⟨hTN, hc, UC1.card_of_L216Cover hK, UC1.card_of_L216Cover hK₂, hJ, hnorm, ?_⟩
  rintro _ ⟨g, rfl⟩ hl
  refine hQ g (key g fun κ hκ => hl (φ κ) ?_)
  rw [← Subgroup.map_sup, hsup]
  exact Subgroup.mem_map_of_mem φ hκ

end Main

end S146zU

end CFSG.Quasithin
