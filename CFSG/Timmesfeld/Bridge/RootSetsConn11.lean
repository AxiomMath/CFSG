module

public import CFSG.Timmesfeld.Bridge.RootSetsConn7

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem exists_conj_mem_isPGroup (hC : ConnCex D) (h : Step6 D a b c x z P) {B : Set G}
    (hB : ∀ β ∈ B, β ∈ D ∧ β ∈ P) {w : G} (hwB : ∀ β ∈ B, Commute w β) (hw2 : w * w = 1) :
    ∃ g : G, (∀ β ∈ B, Commute g β) ∧
      ∃ S : Subgroup G, IsPGroup 2 S ∧ P ≤ S ∧ g * w * g⁻¹ ∈ S := by
  have := hC.setting.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Subgroup.centralizer B with hR
  have hPR : P ≤ R := by
    intro p hp
    rw [h.hPL] at hp
    refine (Subgroup.closure_le _).2 (fun l hl => ?_) hp
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro β hβ
    exact (h.commute_of_mem hC (hB β hβ).1 hl.1 (hB β hβ).2 hl.2).eq
  have hwR : w ∈ R := by
    rw [hR, Subgroup.mem_centralizer_iff]
    intro β hβ
    exact (hwB β hβ).eq.symm
  obtain ⟨S₁, hS₁⟩ := (h.hP2.comap_subtype (K := R)).exists_le_sylow
  have hW : IsPGroup 2 (Subgroup.zpowers (⟨w, hwR⟩ : R)) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    have hw2' : (⟨w, hwR⟩ : R) * ⟨w, hwR⟩ = 1 := Subtype.ext hw2
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hw2', one_zpow]
  obtain ⟨S₂, hS₂⟩ := hW.exists_le_sylow
  obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq R S₂ S₁
  have hmem : g' * ⟨w, hwR⟩ * g'⁻¹ ∈ (S₁ : Subgroup R) := by
    rw [← hg']
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g') _
      (hS₂ (Subgroup.mem_zpowers _))
  refine ⟨g', fun β hβ => ?_, (S₁ : Subgroup R).map R.subtype, S₁.isPGroup'.map _,
    fun p hp => ⟨⟨p, hPR hp⟩, hS₁ hp, rfl⟩, ⟨_, hmem, rfl⟩⟩
  have := Subgroup.mem_centralizer_iff.1 g'.2 β hβ
  exact this.symm

theorem ncard_class_le (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P)
    {e₁ e₂ : G} (he₁ : e₁ ∈ D) (he₂ : e₂ ∈ D) (he₁P : e₁ ∈ P) (he₂P : e₂ ∈ P) :
    {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ℓ * e₁ ∈ qcore D x P}.ncard ≤
      {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ℓ * e₂ ∈ qcore D x P}.ncard := by
  classical
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  set X := lsub D x P with hX
  set Q := CFSG.pCore 2 X with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hBX := h.isBenderGroup_pCore hB hC
  obtain ⟨Sb, hSb⟩ := h.exists_sylow_ge hC
  set eX₁ : X := ⟨e₁, mem_lsub_of_mem he₁ he₁P⟩
  set eX₂ : X := ⟨e₂, mem_lsub_of_mem he₂ he₂P⟩
  have hS := h.setup hC
  have hmemS : ∀ y : X, (y : G) ∈ P → π y ∈ Sb := fun y hy => hSb ⟨y, hy, rfl⟩
  have hinv : ∀ y : X, (y : G) ∈ D → π y * π y = 1 := fun y hy => by
    rw [← map_mul, show y * y = 1 from Subtype.ext (hD.mul_self_eq_one hy), map_one]
  have hne1 : ∀ y : X, (y : G) ∈ D → π y ≠ 1 := fun y hy h1 =>
    h.not_mem_qcore hC hy ⟨y, (QuotientGroup.eq_one_iff y).1 h1, rfl⟩
  have hcen : ∀ y : X, (y : G) ∈ D → (y : G) ∈ P → π y ∈ Sb ∧ ∀ q ∈ Sb, Commute q (π y) :=
    fun y hy hyP => ⟨hmemS y hyP, fun q hq =>
      (Asc72.IsBenderGroup.commute_of_mul_self_eq_one hBX Sb (hmemS y hyP) (hinv y hy) q hq).symm⟩
  obtain ⟨gb, hgbN, hgb⟩ := Asc72.IsBenderGroup.exists_normalizer_conj hBX Sb
    (hcen eX₁ he₁ he₁P) (hne1 eX₁ he₁) (hcen eX₂ he₂ he₂P) (hne1 eX₂ he₂)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gb
  refine Set.ncard_le_ncard_of_injOn (fun ℓ => (g : G) * ℓ * (g : G)⁻¹) ?_ ?_ (Set.toFinite _)
  · intro ℓ ⟨hℓ, hℓP, hq⟩
    have hℓX : ℓ ∈ X := mem_lsub_of_mem hℓ hℓP
    set lX : X := ⟨ℓ, hℓX⟩
    have hyD : ((g * lX * g⁻¹ : X) : G) ∈ D := hN _ ℓ hℓ
    have hπℓ : π lX = π eX₁ := by
      obtain ⟨m, hm, hme⟩ := hq
      have hm' : m = lX * eX₁ := Subtype.ext hme
      have h1 : π (lX * eX₁) = 1 := by rw [← hm']; exact (QuotientGroup.eq_one_iff m).2 hm
      rw [map_mul] at h1
      calc π lX = π lX * (π eX₁ * π eX₁) := by rw [hinv eX₁ he₁, mul_one]
        _ = π eX₁ := by rw [← mul_assoc, h1, one_mul]
    have hyS : π (g * lX * g⁻¹) ∈ Sb := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hgbN (π lX)).1 (hmemS lX hℓP)
    have hyP := h.mem_of_mem_sylow hC hSb hyD hyS
    refine ⟨hyD, hyP, ⟨g * lX * g⁻¹ * eX₂, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩⟩
    change π (g * lX * g⁻¹ * eX₂) = 1
    rw [map_mul, map_mul, map_mul, map_inv, hπℓ, hgb, hinv eX₂ he₂]
  · intro u _ v _ huv
    exact mul_left_cancel (mul_right_cancel huv)

end Step6

end CFSG.Timmesfeld.Bridge
