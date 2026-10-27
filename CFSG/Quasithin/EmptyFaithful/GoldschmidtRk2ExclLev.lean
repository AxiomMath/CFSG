module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclNB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Lev

variable {Γ Y : Type} [Group Γ] [Finite Γ] [Group Y] [Finite Y]

@[expose] def lev (ρ : Γ →* Y) (B : Subgroup Y) : Subgroup Γ := perfectCore (B.comap ρ)

theorem lev_le (ρ : Γ →* Y) (B : Subgroup Y) : lev ρ B ≤ B.comap ρ := perfectCore_le _

theorem lev_perfect (ρ : Γ →* Y) (B : Subgroup Y) : ⁅lev ρ B, lev ρ B⁆ = lev ρ B :=
  perfectCore_perfect _

theorem comap_le_normalizer_lev (ρ : Γ →* Y) (B : Subgroup Y) :
    B.comap ρ ≤ Subgroup.normalizer (lev ρ B : Set Γ) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le _)).1 (perfectCore_normal _)

theorem map_lev {ρ : Γ →* Y} (hρ : Function.Surjective ρ) (B : Subgroup Y) :
    (lev ρ B).map ρ = perfectCore B := by
  rw [lev, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hρ]

@[expose] noncomputable def levHom {ρ : Γ →* Y} (hρ : Function.Surjective ρ) (B : Subgroup Y) :
    ↥(lev ρ B) →* ↥(perfectCore B) :=
  (ρ.comp (lev ρ B).subtype).codRestrict (perfectCore B) fun x => by
    rw [← map_lev hρ B]
    exact ⟨x, x.2, rfl⟩

theorem levHom_surjective {ρ : Γ →* Y} (hρ : Function.Surjective ρ) (B : Subgroup Y) :
    Function.Surjective (levHom hρ B) := by
  intro y
  have hy : (y : Y) ∈ (lev ρ B).map ρ := by rw [map_lev hρ B]; exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem mem_ker_levHom {ρ : Γ →* Y} (hρ : Function.Surjective ρ) (B : Subgroup Y)
    {x : ↥(lev ρ B)} : x ∈ (levHom hρ B).ker ↔ ρ x = 1 := by
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isPGroup_ker_levHom {ρ : Γ →* Y} (hρ : Function.Surjective ρ) {B : Subgroup Y}
    (h : ∀ x ∈ lev ρ B, ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) : IsPGroup 2 (levHom hρ B).ker := by
  intro x
  obtain ⟨k, hk⟩ := h x.1.1 x.1.2 ((mem_ker_levHom hρ B).1 x.2)
  exact ⟨k, Subtype.ext (Subtype.ext hk)⟩

end Lev

section Generation

theorem commutator_mul_central_left {H : Type*} [Group H] {c : H} (hc : c ∈ Subgroup.center H)
    (g h : H) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have h1 : c * h * c⁻¹ = h := by
    rw [(Subgroup.mem_center_iff.1 hc h).symm.symm.symm, mul_inv_cancel_right]
  calc ⁅g * c, h⁆ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = ⁅g, h⁆ := by rw [h1]; rfl

theorem commutator_mul_central_right {H : Type*} [Group H] {c : H} (hc : c ∈ Subgroup.center H)
    (g h : H) : ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have h1 : c * g⁻¹ * c⁻¹ = g⁻¹ := by
    rw [(Subgroup.mem_center_iff.1 hc g⁻¹).symm.symm.symm, mul_inv_cancel_right]
  calc ⁅g, h * c⁆ = g * h * (c * g⁻¹ * c⁻¹) * h⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = ⁅g, h⁆ := by rw [h1]; rfl

theorem eq_top_of_sup_center {H : Type*} [Group H]
    (hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) {B K : Subgroup H}
    (hK : K ≤ Subgroup.center H) (h : B ⊔ K = ⊤) : B = ⊤ := by
  have hKn : K.Normal := Subgroup.normal_of_le_center hK
  rw [eq_top_iff, ← hH, Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ B ⊔ K := h ▸ Subgroup.mem_top x
  have hy : y ∈ B ⊔ K := h ▸ Subgroup.mem_top y
  obtain ⟨b, hb, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  obtain ⟨b', hb', k', hk', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
  rw [commutator_mul_central_left (hK hk), commutator_mul_central_right (hK hk'),
    commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')

end Generation

section Main

variable {Γ Y : Type} [Group Γ] [Finite Γ] [Group Y] [Finite Y]

theorem sup_lev_eq_top {ρ : Γ →* Y} (hρ : Function.Surjective ρ) {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (hP : Rank2Pkg Y U P) {S : Subgroup Γ} (hS : S.map ρ = U)
    (hcent : ∀ x ∈ ρ.ker, ∀ g : Γ, ⁅x, g⁆ ∈ CFSG.Open.pCore 2 Γ)
    (hperf : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ⊔ CFSG.Open.pCore 2 Γ = ⊤) :
    lev ρ (P 0) ⊔ lev ρ (P 1) ⊔ S ⊔ CFSG.Open.pCore 2 Γ = ⊤ := by
  have : (CFSG.Open.pCore 2 Γ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set Q : Subgroup Γ := CFSG.Open.pCore 2 Γ with hQ
  set B : Subgroup Γ := lev ρ (P 0) ⊔ lev ρ (P 1) ⊔ S ⊔ Q with hB
  have hρB : B.map ρ = ⊤ := by
    rw [eq_top_iff, ← hP.sup_perfectCore_eq_top]
    rw [hB, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, map_lev hρ, map_lev hρ, hS]
    exact le_sup_of_le_left le_rfl
  have hBK : B ⊔ ρ.ker = ⊤ := by
    have := Subgroup.comap_map_eq ρ B
    rw [hρB, Subgroup.comap_top] at this
    exact this.symm
  set π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hK : ρ.ker.map π ≤ Subgroup.center (Γ ⧸ Q) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : π ⁅x, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcent x hx g)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hK' : B.map π ⊔ ρ.ker.map π = ⊤ := by
    rw [← Subgroup.map_sup, hBK, Subgroup.map_top_of_surjective _ hπs]
  have hquot : ⁅(⊤ : Subgroup (Γ ⧸ Q)), (⊤ : Subgroup (Γ ⧸ Q))⁆ = ⊤ := by
    have hQb : Q.map π = ⊥ := (Subgroup.map_eq_bot_iff Q).2 hker.ge
    have h1 : Subgroup.map π (⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ⊔ Q) = ⊤ := by
      rw [hperf, Subgroup.map_top_of_surjective _ hπs]
    rw [Subgroup.map_sup, hQb, sup_bot_eq, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hπs] at h1
    exact h1
  have hBtop : B.map π = ⊤ := eq_top_of_sup_center hquot hK hK'
  have hQB : π.ker ≤ B := by rw [hker]; exact le_sup_right
  calc B = (B.map π).comap π := (Subgroup.comap_map_eq_self hQB).symm
    _ = ⊤ := by rw [hBtop, Subgroup.comap_top]

theorem not_blockIrred_lev {ρ : Γ →* Y} (hρ : Function.Surjective ρ)
    (hQ : CFSG.Open.pCore 2 Γ ≤ ρ.ker)
    (hch : Subgroup.centralizer (CFSG.Open.pCore 2 Γ : Set Γ) ≤ CFSG.Open.pCore 2 Γ)
    {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (hP : Rank2Pkg Y U P) (j : Fin 2)
    (hodd : ∀ x ∈ lev ρ (P j), ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    ¬ BlockIrred (lev ρ (P j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 Γ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  refine not_blockIrred_of_levi (L := ⊤) (J := ↥(perfectCore (P j))) le_top
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) ?_ ?_ ?_ (lev_perfect ρ (P j)) (levHom hρ (P j))
    (levHom_surjective hρ _) (isPGroup_ker_levHom hρ hodd) ?_ ?_ ?_
  · rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact le_top
  · exact (hQ.trans (Subgroup.ker_le_comap ρ (P j))).trans (comap_le_normalizer_lev ρ (P j))
  · exact fun x hx => hch hx.2
  · intro x hxQ
    exact (mem_ker_levHom hρ _).2 (MonoidHom.mem_ker.1 (hQ hxQ))
  · exact charTwo_iff_internal.1 (hP.charTwo j)
  · exact hP.not_isSolvable_perfectCore j

end Main

end CFSG.Quasithin.Rk2
