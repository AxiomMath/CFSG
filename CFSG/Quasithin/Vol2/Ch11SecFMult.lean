module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.Ch11SecFGroup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commutator_pCoreOf_le (L : Subgroup G) : ⁅pCoreOf 2 L, L⁆ ≤ pCoreOf 2 L :=
  (commutator_le_inf_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)).trans inf_le_left

theorem pCoreOf_eq_commutator (h13 : ASInputs.AS_I_1_3_Sp4)
    (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n) :
    pCoreOf 2 L = ⁅pCoreOf 2 L, L⁆ := by
  refine le_antisymm ?_ (commutator_pCoreOf_le L)
  have h1n : 2 ≤ n := hset.one_lt
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hk
  obtain ⟨q⟩ := hset.quot
  set C : Subgroup G := ⁅pCoreOf 2 L, L⁆ with hCdef
  have hCL : C ≤ L := (commutator_pCoreOf_le L).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  set N : Subgroup ↥L := C.subgroupOf L with hNdef
  have hNn : N.Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
      rw [hCdef]
      exact (le_sup_right : L ≤ pCoreOf 2 L ⊔ L).trans
        (A3.sup_le_normalizer_commutator (pCoreOf 2 L) L)
    exact (Subgroup.mem_normalizer_iff.mp (hLC l.2) x).mp hx
  set P : Subgroup ↥L := CFSG.pCore 2 ↥L with hPdef
  have hP : (pCoreOf 2 L).subgroupOf L = P := by
    rw [hPdef]
    show ((CFSG.Open.pCore 2 ↥L).map L.subtype).subgroupOf L = _
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hNP : N ≤ P := by
    rw [← hP]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact commutator_pCoreOf_le L hx
  let φ₀ : ↥L ⧸ N →* ↥L ⧸ P := QuotientGroup.map N P (MonoidHom.id _) hNP
  let φ : ↥L ⧸ N →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (e.toMonoidHom.comp q.toMonoidHom).comp φ₀
  have hφ₀s : Function.Surjective φ₀ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hφs : Function.Surjective φ := (e.surjective.comp q.surjective).comp hφ₀s
  have hL : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hset.perfect]
  have hperf : commutator (↥L ⧸ N) = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ (QuotientGroup.mk' N)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← commutator_def,
      ← commutator_def, hL, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1.symm
  have hker : φ.ker ≤ Subgroup.center (↥L ⧸ N) := by
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ P := by
      have h1 : e (q (φ₀ (QuotientGroup.mk a))) = 1 := hx
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h1
      exact (QuotientGroup.eq_one_iff a).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have haC : (a : G) ∈ pCoreOf 2 L := by
      rw [← hP] at ha
      exact ha
    have hmem : ((b * a)⁻¹ * (a * b) : ↥L) ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      have hc := Subgroup.commutator_mem_commutator (G := G) (H₁ := pCoreOf 2 L) (H₂ := L)
        (Subgroup.inv_mem _ haC) (Subgroup.inv_mem _ b.2)
      have heq : (((b * a)⁻¹ * (a * b) : ↥L) : G) = ⁅((a : G))⁻¹, ((b : G))⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [heq]
      exact hc
    exact hmem
  have hφi := h13 n h1n F hF (↥L ⧸ N) φ hφs hperf hker
  intro x hx
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  have hxP : (⟨x, hxL⟩ : ↥L) ∈ P := by
    rw [← hP, Subgroup.mem_subgroupOf]
    exact hx
  have h1 : φ (QuotientGroup.mk ⟨x, hxL⟩) = φ 1 := by
    rw [map_one]
    change e (q (QuotientGroup.mk ⟨x, hxL⟩)) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr hxP, map_one, map_one]
  have h2 := (QuotientGroup.eq_one_iff (N := N) _).mp (hφi h1)
  rw [hNdef, Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.Quasithin.Vol2.Ch11.SecF
