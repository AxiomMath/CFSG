module

public import CFSG.Quasithin.H13.L32AM50h
public import CFSG.Quasithin.H13.L32AM50i
public import CFSG.Quasithin.H13.L32AM50e
public import CFSG.Quasithin.H13.L32AM50g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (C : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem card_vHat (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Nat.card (vHat V H W) = 4 := by
  have hinf := L32A.Setting147.inf_V_eq C.S h1222 h1332 h1334 C.hV₁W C.hWU C.hHW
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hker : (InternalSec.secMk (W.subgroupOf (conjClosure V H))).ker =
      W.subgroupOf (conjClosure V H) := by
    ext u
    rw [MonoidHom.mem_ker, A6.A6Mod.secMk_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [vHat, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hVU,
    ← Subgroup.inf_relIndex_right, inf_comm W V, hinf]
  have h2 := Subgroup.relIndex_mul_card (fsuV1 T V) V
  rw [inf_eq_left.mpr (inf_le_left : fsuV1 T V ≤ V), hV8, hV12] at h2
  omega

end TopW

namespace Top50

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 7)} (C : Top50 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

theorem mem_normalizer_iff_stabHat {h : ↥H} (hh : π h ∈ alternatingGroup (Fin 7)) :
    (h : G) ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ↔
      π h ∈ C.stabHat (vHat V H W) := by
  rw [C.mem_normalizer_iff]
  constructor
  · intro hst
    refine ⟨hh, fun x hx => ?_⟩
    rw [C.iota_symm_eq hh, ← map_inv]
    exact hst x hx
  · rintro ⟨hγ, hst⟩ x hx
    rw [map_inv, ← C.iota_symm_eq hγ]
    exact hst x hx

end Top50

theorem mod50FourCase_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Mod50FourCase := by
  intro G _ _ T L V H W K π C _ _ _ h16 hGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpiA : ∀ h : ↥H, π h ∈ alternatingGroup (Fin 7) := fun h =>
    (C.act_mem_autK_iff h).mp (hGL ▸ ⟨h, rfl⟩)
  have hrange : π.range = alternatingGroup (Fin 7) :=
    le_antisymm (by rintro _ ⟨h, rfl⟩; exact hpiA h) C.hA7
  set N' := C.stabHat (vHat V H W) with hN'
  have hN'c : Nat.card N' = 72 := C.card_stabHat_eq h16 (C.card_vHat h1222 h1332 h1334)
  have hN'A : N' ≤ alternatingGroup (Fin 7) := fun γ hγ => hγ.1
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hTH : T ≤ H := le_sup_right.trans C.S.hz.1.1
  have hTN : ∀ t (ht : t ∈ T), π ⟨t, hTH ht⟩ ∈ N' := by
    intro t ht
    rw [← C.mem_normalizer_iff_stabHat (hpiA _)]
    have htV := hLTV (Subgroup.mem_sup_right ht)
    have htW := C.hHW (hTH ht)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htV htW ⊢
    rw [Subgroup.map_sup, htV, htW]
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow hTH
  have hS2 : IsPGroup 2 (T.subgroupOf H) :=
    hTsyl.2.1.comap_of_injective H.subtype H.subtype_injective
  have hDR : Alt7.taSub ≤ π.range := by
    rw [hrange]
    intro g hg
    exact mem_alternatingGroup.mpr (Alt7.ta_sign g hg)
  have hD2 : IsPGroup 2 (Alt7.taSub.subgroupOf π.range) :=
    (IsPGroup.of_card (n := 3) (Alt7.card_taSub.trans (by norm_num))).comap_of_injective _
      π.range.subtype_injective
  have hDi : ¬ 2 ∣ (Alt7.taSub.subgroupOf π.range).index := by
    have h1 := (Alt7.taSub.subgroupOf π.range).card_mul_index
    have h2 : Nat.card (Alt7.taSub.subgroupOf π.range) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, Alt7.card_taSub]
    have h3 : Nat.card π.range = 2520 := by rw [hrange, Alt7.card_alt7]
    rw [h2, h3] at h1
    rintro ⟨m, hm⟩
    omega
  obtain ⟨s, hs⟩ := exists_conj_map_eq_of_sylow π.rangeRestrict
    (MonoidHom.rangeRestrict_surjective π) hS2 hTsyl.2.2 hD2 hDi
  set σ : Perm (Fin 7) := (s : Perm (Fin 7)) with hσ
  set N'' := N'.map (MulAut.conj σ⁻¹).toMonoidHom with hN''
  have hmem'' : ∀ γ, σ⁻¹ * γ * σ ∈ N'' ↔ γ ∈ N' := by
    intro γ
    rw [hN'', Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp [mul_assoc]
  have hTA : Alt7.taSub ≤ N'' := by
    intro a ha
    have h1 : (⟨a, hDR ha⟩ : ↥π.range) ∈ Alt7.taSub.subgroupOf π.range :=
      Subgroup.mem_subgroupOf.mpr ha
    rw [← hs] at h1
    obtain ⟨_, ⟨t, ht, rfl⟩, hta⟩ := h1
    have e : a = σ⁻¹ * π t * σ := by
      have := congrArg Subtype.val hta
      simpa [MulAut.conj_apply, hσ, mul_assoc] using this.symm
    rw [e, hmem'']
    exact hTN t (Subgroup.mem_subgroupOf.mp ht)
  have hN''A : N'' ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨γ, hγ, rfl⟩
    have h1 := hN'A hγ
    rw [mem_alternatingGroup] at h1 ⊢
    simp [h1]
  have hN''c : Nat.card N'' = 72 := by
    rw [hN'', Subgroup.card_map_of_injective (MulAut.conj σ⁻¹).injective, hN'c]
  have hSt := Alt7.eq_stabSub_of_card hN''A hTA hN''c
  refine ⟨Alt7.d3.map σ.toEmbedding, by rw [Finset.card_map]; rfl, fun h => ?_⟩
  have hmemΔ : ∀ j, j ∈ Alt7.d3.map σ.toEmbedding ↔ σ⁻¹ j ∈ Alt7.d3 := by
    intro j
    rw [Finset.mem_map_equiv]
    rfl
  rw [C.mem_normalizer_iff_stabHat (hpiA h), ← hN', ← hmem'', hSt, Alt7.mem_stabSub]
  constructor
  · rintro ⟨-, hst⟩ j hj
    rw [hmemΔ] at hj ⊢
    have := hst _ hj
    simpa [Perm.mul_apply] using this
  · intro hst
    refine ⟨?_, fun i hi => ?_⟩
    · have h1 := hpiA h
      rw [mem_alternatingGroup] at h1
      simp [h1]
    · have hj : σ i ∈ Alt7.d3.map σ.toEmbedding := by
        rw [hmemΔ]
        simpa using hi
      have h2 := hst _ hj
      rw [hmemΔ] at h2
      simpa [Perm.mul_apply] using h2

theorem lemma14_7_50_mod_of_kIrr (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h38 : Lemma14_7_38) (h48 : Lemma14_7_48) (hIrr : Mod50KIrr) : Lemma14_7_50_Mod :=
  lemma14_7_50_mod_of h1222 h1332 h1334 hA37 hA38 hA39 h38 h48 hIrr
    (mod50FourCase_of h1222 h1332 h1334)

end CFSG.Quasithin.H13.L32A.C
