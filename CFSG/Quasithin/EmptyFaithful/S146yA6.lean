module

public import CFSG.Quasithin.EmptyFaithful.S146yCom
public import CFSG.Quasithin.EmptyFaithful.S146yU3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section A6

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.centralizerMod_le_normalizer_U₁ (hgen : A6CoverGen) (S : Setting146 G T M)
    {K U₁ U₂ : Subgroup G} {s u : G} (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s)
    (hKn : mcOf T ≤ Subgroup.normalizer (K : Set G)) (huU : u ∈ U₁)
    (hnc : ∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ Zz) :
    centralizerMod Zz (mcOf T) (Subgroup.zpowers u) ≤ Subgroup.normalizer (U₁ : Set G) := by
  intro x hx
  obtain ⟨hxH, hxZ, hxc⟩ := hx
  have hKU₁ := S.le_normalizer_U₁_of_decomp hK hdec
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hKn hxH
  have hxc' : x⁻¹ ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u) :=
    Subgroup.inv_mem _ ⟨hxH, hxZ, hxc⟩
  have hKU₁x : K ≤ Subgroup.normalizer (conjSub x U₁ : Set G) := le_normalizer_conjSub hxK hKU₁
  set W : Subgroup G := U₁ ⊓ conjSub x U₁ with hWdef
  have hZW : Zz ≤ W := by
    intro z hz
    refine ⟨hdec.Z₁ hz, mem_conjSub.mpr ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxZ) z).mp hz
    simpa using hdec.Z₁ this
  have huW : u ∈ W := by
    refine ⟨huU, mem_conjSub.mpr ?_⟩
    have h1 := hxc'.2.2 u (Subgroup.mem_zpowers u)
    have e : x⁻¹ * u * x = (x⁻¹ * u * x⁻¹⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact U₁.mul_mem (hdec.Z₁ h1) huU
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKU₁ hk, hKU₁x hk⟩
  have hcomm : ∀ y ∈ K, y * u * y⁻¹ * u⁻¹ ∈ W := by
    intro y hy
    have h1 : y * u * y⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hKU₁ hy) u).mp huU
    have h2 : y * u * y⁻¹ ∈ conjSub x U₁ := (Subgroup.mem_normalizer_iff.mp (hKU₁x hy) u).mp huW.2
    exact W.mul_mem ⟨h1, h2⟩ (W.inv_mem huW)
  have hWeq : W = U₁ := S.eq_of_commutators_mem hgen hK hdec huU hnc hZW inf_le_left hKW hcomm
  have hle : U₁ ≤ conjSub x U₁ := fun y hy => (hWeq ▸ hy : y ∈ W).2
  have hcard : Nat.card (conjSub x U₁) ≤ Nat.card U₁ := by rw [natCard_conjSub_eq]
  exact mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end A6

@[expose] def A6Index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u → KbarIsA6 K →
      (tZero T u).relIndex T = 2

theorem u1A6Res_of_gen_index (hgen : A6CoverGen) (hidx : A6Index) : U1A6Res := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx hA
  have hctx' := hctx
  obtain ⟨_c19, _c20, _c23, hK, c21, _c22, hdec, hch⟩ := hctx'
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rcases c21 with ⟨hper, -⟩ | ⟨-, hL3⟩ | ⟨-, -, -, -, -, -, hL3, -⟩
    · rw [← hper]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hA).elim
  obtain ⟨huU, hunc⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T := by
    rcases hch with ⟨-, huU, hunc, -⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
    · exact ⟨huU, hunc⟩
    · exact absurd (hKn (hTH ht)) htn
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG ((le_U_of_decomp hK hdec).1 huU)
  have hnc : ∃ x ∈ K, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hcon
    push Not at hcon
    exact hunc (commutator_zpowers_le_of_forall (fun k hk => S.normalizer_Z.ge (hKG hk))
      (fun z hz => S146T.comm_Z huG hz) hcon)
  exact ⟨S.centralizerMod_le_normalizer_U₁ hgen hK hdec hKn huU hnc,
    hidx G T M S hB K U₁ U₂ s u hctx hA⟩

theorem input14624U1_of_gen_index (hgen : A6CoverGen) (hidx : A6Index) : Input14624U1 :=
  input14624U1_of_A6 (u1A6Res_of_gen_index hgen hidx)

theorem input14624U3_of_gen_index (hgen : A6CoverGen) (hidx : A6Index) : Input14624U3 :=
  input14624U3_of_A6 (u1A6Res_of_gen_index hgen hidx)

end CFSG.Quasithin
