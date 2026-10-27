module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3L30
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 Equiv

abbrev c3 : Perm (Fin 3) := swap 0 1 * swap 1 2

theorem c3_pow_three : c3 ^ 3 = 1 := by decide +kernel

theorem c3_ne_one : c3 ≠ 1 := by decide +kernel

theorem exists_conj_swap3 : ∀ b : Perm (Fin 3), b ≠ 1 → b * b = 1 →
    ∃ g : Perm (Fin 3), g * b * g⁻¹ = swap 0 1 := by decide +kernel

theorem exists_conj_S3Syl {B : Subgroup (Perm (Fin 3))} (hne : B ≠ ⊥) (hexp : ∀ x ∈ B, x * x = 1) :
    ∃ g : Perm (Fin 3), B.map (MulAut.conj g).toMonoidHom = S3Syl := by
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hb : b.1 ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨g, hg⟩ := exists_conj_swap3 b.1 hb (hexp b.1 b.2)
  have hp : IsPGroup 2 B := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hexp x x.2⟩
  have hz : Subgroup.zpowers (b : Perm (Fin 3)) = B :=
    perm3_eq_of_le_of_isPGroup _ B hp (Subgroup.zpowers_le.mpr b.2)
      (by simpa using hb)
  refine ⟨g, ?_⟩
  rw [← hz, MonoidHom.map_zpowers]
  show Subgroup.zpowers (g * b.1 * g⁻¹) = Subgroup.zpowers (swap 0 1)
  rw [hg]

theorem hss18S3_holds (G : Type) [Group G] [Finite G] :
    ∀ X P Z : Subgroup G, PushHyp X P Z → Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) →
      ¬ thompsonJ P ≤ pCoreOf 2 X → IsNat3Sec X (zZero X Z) Z := by
  intro X P Z h he hJ
  obtain ⟨θ, hθ, hker⟩ := exists_toPerm_of_quot he
  obtain ⟨A, hA, hAQ⟩ := exists_offender hJ
  have hs := isSec_inf_centralizer_oTwoRes h.elemAbelian h.normal
  have hk := ker_le_cSecIn h θ hker (Z ⊓ Subgroup.centralizer (oTwoRes X : Set G))
  set M := secModule hs θ hθ hk with hM
  have hfix : fixW M ⊤ = ⊥ := fixW_top_eq_bot θ hθ h.elemAbelian h.normal hk
  have hmoved : ∃ σ ∈ alternatingGroup (Fin 3), ∃ w : M.W, M.act σ w ≠ w := by
    obtain ⟨d, hdL, hdX, k, hdk⟩ := exists_odd_elt (X := X) θ hθ (c := c3)
    have hc3 : orderOf c3 = 3 := orderOf_eq_prime c3_pow_three c3_ne_one
    obtain ⟨hodd, hne⟩ := odd_orderOf_pow_two_pow (c := c3) (by rw [hc3]; decide) k
    obtain ⟨z, hz, hzK⟩ := exists_moved h θ hker hdL hdX (by rw [hdk]; exact hodd)
      (by rw [hdk]; exact fun h1 => c3_ne_one (hne h1))
    refine ⟨θ ⟨d, hdX⟩, ?_, hs.proj ⟨z, hz⟩, fun h1 => hzK ?_⟩
    · rw [hdk, Equiv.Perm.mem_alternatingGroup, map_pow]
      have : Perm.sign c3 = 1 := by unfold c3; decide
      rw [this, one_pow]
    · rw [secModule_act_proj hs θ hθ hk ⟨d, hdX⟩ ⟨z, hz⟩] at h1
      exact (hs.proj_eq_proj_iff _ _).mp h1.symm
  have hnt : ∃ w : M.W, w ≠ 1 := by
    obtain ⟨σ, -, w, hw⟩ := hmoved
    exact ⟨w, fun h1 => hw (by rw [h1, map_one])⟩
  have hA3 : fixW M (alternatingGroup (Fin 3)) ≠ ⊤ := by
    obtain ⟨σ, hσ, w, hw⟩ := hmoved
    intro htop
    have : w ∈ fixW M (alternatingGroup (Fin 3)) := by rw [htop]; trivial
    exact hw (this σ hσ)
  set B : Subgroup (Perm (Fin 3)) := (A.subgroupOf X).map θ with hB
  have hAX : A ≤ X := hA.1.trans h.le_self
  have hBcard : Nat.card B = (A ⊓ pCoreOf 2 X).relIndex A := by
    rw [hB, card_map_subgroupOf_eq_relIndex θ hker hAX, Subgroup.inf_relIndex_left]
  have hBne : B ≠ ⊥ := by
    intro h1
    apply hAQ
    intro y hy
    have : θ ⟨y, hAX hy⟩ ∈ B := ⟨⟨y, hAX hy⟩, hy, rfl⟩
    rw [h1, Subgroup.mem_bot] at this
    exact (hker _).mp this
  have hBexp : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hA.2.1.2 y hy)
    rw [this, map_one]
  have hoff : (fixW M B).index ≤ (A ⊓ pCoreOf 2 X).relIndex A :=
    (index_fixW_secModule_le θ hθ h.elemAbelian h.normal hk
      (A := A) (Q' := Subgroup.centralizer (A : Set G))
      fun y hy q hq => Subgroup.mem_centralizer_iff.mp hq y hy).trans (offender_count h hA)
  have hBle : Nat.card B ≤ 2 := by
    refine perm3_card_le_two_of_isPGroup B fun x => ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hBexp x x.2
  obtain ⟨g, hg⟩ := exists_conj_S3Syl hBne hBexp
  have hidx : (fixW M S3Syl).index ≤ 2 := by
    rw [← hg, fidx_conj]
    omega
  obtain ⟨e⟩ := s3_lemma30_natural M hA3 hidx hfix
  have hf := (secModule_faithful_iff hs θ hθ hk).mp (e.faithful nat3_faithful)
  rw [zZero_eq]
  exact isModelSec_of_iso hs θ hθ (le_antisymm hk hf) e.symm

end CFSG.Quasithin.F53Push
