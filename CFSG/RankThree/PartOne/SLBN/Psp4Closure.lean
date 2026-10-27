module

public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect

public section

namespace CFSG.RankThree.PartOne.SLBN

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.CentralExt.SpClosed

variable {K : Type} [Field K]

theorem sq_eq_one_of_proj_eq_one [Finite K] {g : StatedSp 2 K}
    (hg : (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) g :
      StatedProj (StatedSp 2 K)) = 1) : g ^ 2 = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  have hle := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two 2 K
  set Z := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) with hZ
  let x : Z := ⟨g, hg⟩
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have hx : x ^ Nat.card Z = 1 := pow_card_eq_one'
  have hcases : Nat.card Z = 1 ∨ Nat.card Z = 2 := by omega
  rcases hcases with h | h
  · rw [h, pow_one] at hx
    have : g = 1 := congrArg Subtype.val hx
    rw [this, one_pow]
  · rw [h] at hx
    exact congrArg Subtype.val hx

theorem ker_eq_bot_of_central_psp [Finite K] (hK : 5 ≤ Nat.card K) {Y : Type} [Group Y]
    (φ : Y →* StatedProj (StatedSp 2 K)) (hφ : Function.Surjective φ)
    (hmin : ∀ M : Subgroup Y, M.map φ = ⊤ → M = ⊤) (hker : IsPGroup 3 φ.ker)
    (hcen : φ.ker ≤ Subgroup.center Y) : φ.ker = ⊥ := by
  classical
  let proj : StatedSp 2 K →* StatedProj (StatedSp 2 K) := QuotientGroup.mk' _
  let E : Subgroup (Y × StatedSp 2 K) :=
    MonoidHom.eqLocus (φ.comp (MonoidHom.fst _ _)) (proj.comp (MonoidHom.snd _ _))
  let π : E →* StatedSp 2 K := (MonoidHom.snd Y (StatedSp 2 K)).comp E.subtype
  have hπ : Function.Surjective π := fun g => by
    obtain ⟨y, hy⟩ := hφ (proj g)
    exact ⟨⟨(y, g), hy⟩, rfl⟩
  have hcenπ : π.ker ≤ Subgroup.center E := by
    intro x hx
    have hx1 : x.1.2 = 1 := hx
    have hxE : φ x.1.1 = proj x.1.2 := x.2
    have hy : x.1.1 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hxE, hx1, map_one]
    have hyc := hcen hy
    rw [Subgroup.mem_center_iff] at hyc ⊢
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact hyc z.1.1
    · change z.1.2 * x.1.2 = x.1.2 * z.1.2
      rw [hx1, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := sp_exists_section_of_central (n := 2) le_rfl hK hπ hcenπ
  let τ : StatedSp 2 K →* Y := (MonoidHom.fst Y _).comp (E.subtype.comp σ)
  have hτ : ∀ g, φ (τ g) = proj g := fun g => by
    have h1 : φ (σ g).1.1 = proj (σ g).1.2 := (σ g).2
    have h2 : (σ g).1.2 = g := hσ g
    change φ (σ g).1.1 = _
    rw [h1, h2]
  have hrange : τ.range = ⊤ := by
    apply hmin
    rw [eq_top_iff]
    intro s _
    obtain ⟨g, hg⟩ : ∃ g : StatedSp 2 K, proj g = s := QuotientGroup.mk_surjective s
    exact ⟨τ g, ⟨g, rfl⟩, by rw [hτ, hg]⟩
  rw [eq_bot_iff]
  intro k hk
  have hk' : k ∈ τ.range := hrange ▸ Subgroup.mem_top k
  obtain ⟨g, rfl⟩ := hk'
  have hg : proj g = 1 := by rw [← hτ]; exact hk
  have hsq : τ g ^ 2 = 1 := by rw [← map_pow, sq_eq_one_of_proj_eq_one hg, map_one]
  obtain ⟨m, hm⟩ := hker ⟨τ g, hk⟩
  have h3 : τ g ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  have hd2 : orderOf (τ g) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hd3 : orderOf (τ g) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 2 (3 ^ m) := Nat.Coprime.pow_right m (by norm_num)
  have h1 : orderOf (τ g) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd3
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 h1

end CFSG.RankThree.PartOne.SLBN
