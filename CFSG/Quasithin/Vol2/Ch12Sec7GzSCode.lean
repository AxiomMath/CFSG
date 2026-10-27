module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSMData
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Vol2.Ch12Sec7ModG

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277MLine
open CFSG.Quasithin CFSG.Open
open scoped IsMulCommutative

section Basic

variable {G : Type} [Group G]

theorem comm_of_isElemAbelian {W : Subgroup G} (hW : IsElemAbelian 2 W) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) : x * y = y * x :=
  congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sq_eq_one_of_isElemAbelian {W : Subgroup G} (hW : IsElemAbelian 2 W) {x : G}
    (hx : x ∈ W) : x ^ 2 = 1 :=
  hW.2 x hx

end Basic

section Codes

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def cj (C : Coding ↥V) (g : Subgroup.normalizer (V : Set G)) : B6 :=
  C.cB (conjAct V g)

theorem conjAct_val (g : Subgroup.normalizer (V : Set G)) (x : ↥V) :
    ((conjAct V g x : ↥V) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

theorem cd_conj (C : Coding ↥V) (g : Subgroup.normalizer (V : Set G)) (x : ↥V) :
    C.cd (conjAct V g x) = (cj C g).app (C.cd x) :=
  C.cd_apply _ _

theorem isInv_cB (C : Coding ↥V) {a : MulAut ↥V} (h2 : a * a = 1) (h1 : a ≠ 1) :
    isInv (C.cB a) = true := by
  rw [isInv_iff]
  refine ⟨?_, fun h => h1 ((C.cB_eq_one).1 h)⟩
  rw [← C.cB_mul, h2, C.cB_one]

theorem card_orbitIn_eq_orbitSize {H : Subgroup (MulAut ↥V)} {C : Coding ↥V}
    (hC : IdentL C H) (v : ↥V) :
    Nat.card (Orbit.orbitIn H v) = orbitSize gm6 (C.cd v) := by
  classical
  have hset : C.cd '' Orbit.orbitIn H v = ↑((gm6.map fun B => B.app (C.cd v)).toFinset) := by
    ext c
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      exact ⟨C.cB a, (hC.1 a).1 ha, (C.cd_apply a v).symm⟩
    · intro hc
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hc
      obtain ⟨B, hB, rfl⟩ := hc
      obtain ⟨a, ha⟩ := hC.2 B hB
      refine ⟨a v, ⟨a, (hC.1 a).2 (ha ▸ hB), rfl⟩, ?_⟩
      rw [C.cd_apply, ha]
  have h1 : Nat.card (Orbit.orbitIn H v) = (C.cd '' Orbit.orbitIn H v).ncard := by
    rw [Set.ncard_image_of_injective _ C.cd_injective, Nat.card_coe_set_eq]
  rw [h1, hset, Set.ncard_coe_finset, orbitSize_eq]

theorem orbitSize_gm6_zero {H : Subgroup (MulAut ↥V)} {C : Coding ↥V} (hC : IdentL C H) :
    orbitSize gm6 0 = 1 := by
  have h := card_orbitIn_eq_orbitSize hC (1 : ↥V)
  rw [C.cd_one] at h
  rw [← h]
  have hs : Orbit.orbitIn H (1 : ↥V) = {1} := by
    ext w
    constructor
    · rintro ⟨a, -, rfl⟩
      rw [Set.mem_singleton_iff, map_one]
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨1, H.one_mem, map_one _⟩
  rw [hs, Nat.card_unique]

theorem mem_of_fix {K : Subgroup ↥V} (hK : Nat.card K = 16) {C : Coding ↥V} {A : MulAut ↥V}
    (hfix : ∀ x ∈ K, A x = x) (hlen : (fixList (C.cB A)).length ≤ 16) :
    ∀ x : ↥V, A x = x → x ∈ K := by
  classical
  intro x hx
  set F : Set ℕ := ↑((fixList (C.cB A)).toFinset) with hF
  set S : Set ℕ := C.cd '' (K : Set ↥V) with hS
  have hSF : S ⊆ F := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hF, Finset.mem_coe, List.mem_toFinset, mem_fixList]
    refine ⟨C.cd_lt y, ?_⟩
    rw [← C.cd_apply, hfix y hy]
  have hScard : S.ncard = 16 := by
    rw [hS, Set.ncard_image_of_injective _ C.cd_injective, ← hK]
    exact (Nat.card_coe_set_eq _).symm
  have hFcard : F.ncard ≤ 16 := by
    rw [hF, Set.ncard_coe_finset]
    exact (List.toFinset_card_le _).trans hlen
  have hSeq : S = F := Set.eq_of_subset_of_ncard_le hSF (by omega) (Set.toFinite _)
  have hxF : C.cd x ∈ F := by
    rw [hF, Finset.mem_coe, List.mem_toFinset, mem_fixList]
    refine ⟨C.cd_lt x, ?_⟩
    rw [← C.cd_apply, hx]
  rw [← hSeq] at hxF
  obtain ⟨y, hy, hyx⟩ := hxF
  have hyx' : y = x := C.cd_injective hyx
  exact hyx' ▸ hy

theorem eq_of_mem_invsD {Γ : List B6} {Dl : List ℕ} (hl : (invsD Γ Dl).length ≤ 3)
    {T : Set B6} (hT : ∀ B ∈ T, B ∈ invsD Γ Dl) (hcard : T.ncard = 3) (hfin : T.Finite)
    {B : B6} (hB : B ∈ invsD Γ Dl) : B ∈ T := by
  classical
  by_contra hBT
  have hins : (insert B T).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hBT hfin, hcard]
  have hle : (insert B T).ncard ≤ (invsD Γ Dl).length := by
    have hsub : insert B T ⊆ ↑((invsD Γ Dl).toFinset) := by
      intro x hx
      rcases hx with rfl | hx
      · exact List.mem_toFinset.2 hB
      · exact List.mem_toFinset.2 (hT x hx)
    calc (insert B T).ncard ≤ (↑((invsD Γ Dl).toFinset) : Set B6).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (invsD Γ Dl).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (invsD Γ Dl).length := List.toFinset_card_le _
  omega

theorem exists_normalizes_of_stabD {H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    {C : Coding ↥V} {Γ : List B6} (hΓ : ∀ B ∈ Γ, ∃ a ∈ autOn H V, C.cB a = B)
    {D : Subgroup G} (hDV : D ≤ V) {Dl : List ℕ}
    (hDl : ∀ x : ↥V, (x : G) ∈ D ↔ C.cd x ∈ Dl)
    {B : B6} (hB : B ∈ stabD Γ Dl) :
    ∃ g : G, g ∈ H ∧ g ∈ Subgroup.normalizer (D : Set G) ∧
      ∃ hg : g ∈ Subgroup.normalizer (V : Set G), C.cB (conjAct V ⟨g, hg⟩) = B := by
  obtain ⟨hBΓ, hBst⟩ := mem_stabD.1 hB
  obtain ⟨a, ha, hBa⟩ := hΓ B hBΓ
  obtain ⟨h, rfl⟩ := (A4.mem_autOn_iff hH).1 ha
  have hgV : (h : G) ∈ Subgroup.normalizer (V : Set G) := hH h.2
  refine ⟨(h : G), h.2, ?_, hgV, hBa⟩
  set g : G := (h : G) with hg
  have hmap : ∀ n ∈ D, g * n * g⁻¹ ∈ D := by
    intro n hn
    have hnV : n ∈ V := hDV hn
    have hc : C.cd (⟨n, hnV⟩ : ↥V) ∈ Dl := (hDl _).1 hn
    have hcj : cj C ⟨g, hgV⟩ = B := hBa
    have h1 : C.cd (conjAct V ⟨g, hgV⟩ ⟨n, hnV⟩) ∈ Dl := by
      rw [cd_conj, hcj]
      exact hBst _ hc
    exact (hDl _).2 h1
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hmap n hn
  · intro hn
    let φ : ↥D → ↥D := fun d => ⟨g * (d : G) * g⁻¹, hmap d d.2⟩
    have hφinj : Function.Injective φ := by
      intro d₁ d₂ hd
      have h1 : g * (d₁ : G) * g⁻¹ = g * (d₂ : G) * g⁻¹ := congrArg Subtype.val hd
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
    obtain ⟨d, hd⟩ := hφsurj ⟨g * n * g⁻¹, hn⟩
    have h2 : g * (d : G) * g⁻¹ = g * n * g⁻¹ := congrArg Subtype.val hd
    have hdn : (d : G) = n := mul_left_cancel (mul_right_cancel h2)
    rw [← hdn]
    exact d.2

end Codes

end CFSG.Quasithin.H13.I1277

end
