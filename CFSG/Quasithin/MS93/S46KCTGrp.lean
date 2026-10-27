module

public import CFSG.Quasithin.MS93.S468Red
public import CFSG.Quasithin.MS93.S46I4610

public section

namespace CFSG.Quasithin.MS93.S46.KCT

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S468
open scoped commutatorElement

section Abstract

variable {𝔾 : Type*} [Group 𝔾]

theorem commute_commutator {V W Q Z Zb : Subgroup 𝔾} (hVV : ⁅V, V⁆ ≤ Z)
    (hZV : Z ≤ Subgroup.centralizer (V : Set 𝔾)) (hWV : W ≤ V) (hWQ : ⁅W, Q⁆ ≤ Zb)
    (hZb : Zb ≤ Z) (hZbQ : Zb ≤ Subgroup.centralizer (Q : Set 𝔾))
    (hQW : Q ≤ Subgroup.normalizer (W : Set 𝔾)) {k z y : 𝔾} (hk : k ∈ Q)
    (hkV : k ∈ Subgroup.normalizer (V : Set 𝔾)) (hz : z ∈ V) (hzQ : z ∈ Q) (hy : y ∈ W) :
    Commute ⁅k, z⁆ y := by
  have hyV : y ∈ V := hWV hy
  set a := k * z * k⁻¹ with ha
  have haV : a ∈ V := (Subgroup.mem_normalizer_iff.mp hkV z).mp hz
  set y₀ := k⁻¹ * y * k with hy₀
  have hy₀W : y₀ ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (hQW (Q.inv_mem hk)) y).mp hy
    simpa [hy₀] using this
  have hζ : y⁻¹ * y₀ ∈ Zb := by
    have : ⁅y⁻¹, k⁻¹⁆ ∈ Zb := hWQ (Subgroup.commutator_mem_commutator (W.inv_mem hy)
      (Q.inv_mem hk))
    simpa [commutatorElement_def, hy₀, mul_assoc] using this
  have hc₁ : ⁅z, y₀⁆ ∈ Zb := by
    have := Zb.inv_mem (hWQ (Subgroup.commutator_mem_commutator hy₀W hzQ))
    rwa [commutatorElement_inv] at this
  have hkc : k * ⁅z, y₀⁆ * k⁻¹ = ⁅z, y₀⁆ := by
    have := Subgroup.mem_centralizer_iff.mp (hZbQ hc₁) k hk
    rw [this, mul_inv_cancel_right]
  have hconj : k * ⁅z, y₀⁆ * k⁻¹ = ⁅a, y⁆ := by
    simp only [commutatorElement_def, ha, hy₀]
    group
  have hζc : ∀ v ∈ V, v * (y⁻¹ * y₀) = (y⁻¹ * y₀) * v := fun v hv =>
    Subgroup.mem_centralizer_iff.mp (hZV (hZb hζ)) v hv
  have hzy₀ : ⁅z, y₀⁆ = ⁅z, y⁆ := by
    have e : y₀ = y * (y⁻¹ * y₀) := by group
    have hz' := hζc z⁻¹ (V.inv_mem hz)
    rw [e, commutatorElement_def, commutatorElement_def]
    calc z * (y * (y⁻¹ * y₀)) * z⁻¹ * (y * (y⁻¹ * y₀))⁻¹
        = z * y * ((y⁻¹ * y₀) * z⁻¹) * (y⁻¹ * y₀)⁻¹ * y⁻¹ := by group
      _ = z * y * (z⁻¹ * (y⁻¹ * y₀)) * (y⁻¹ * y₀)⁻¹ * y⁻¹ := by rw [hz']
      _ = z * y * z⁻¹ * y⁻¹ := by group
  have hc0 : ⁅a, y⁆ = ⁅z, y⁆ := by rw [← hconj, hkc, hzy₀]
  set c₀ := ⁅z, y⁆ with hc₀
  have hc₀Z : c₀ ∈ Z := hVV (Subgroup.commutator_mem_commutator hz hyV)
  have hca : Commute a c₀ := Subgroup.mem_centralizer_iff.mp (hZV hc₀Z) a haV
  have hcz : Commute z c₀ := Subgroup.mem_centralizer_iff.mp (hZV hc₀Z) z hz
  have h1 : a * y = c₀ * y * a := by
    rw [← hc0, commutatorElement_def]
    group
  have e1 : z⁻¹ * y * z * y⁻¹ = c₀⁻¹ := by
    calc z⁻¹ * y * z * y⁻¹ = z⁻¹ * (z * y * z⁻¹ * y⁻¹)⁻¹ * z := by group
      _ = z⁻¹ * c₀⁻¹ * z := by rw [hc₀, commutatorElement_def]
      _ = c₀⁻¹ := by rw [mul_assoc, ← hcz.inv_right.eq, inv_mul_cancel_left]
  have hk' : ⁅k, z⁆ = a * z⁻¹ := by rw [commutatorElement_def, ha]
  rw [Commute, SemiconjBy, hk']
  calc a * z⁻¹ * y = a * (z⁻¹ * y * z * y⁻¹) * y * z⁻¹ := by group
    _ = a * c₀⁻¹ * y * z⁻¹ := by rw [e1]
    _ = c₀⁻¹ * (a * y) * z⁻¹ := by rw [hca.inv_right.eq]; group
    _ = c₀⁻¹ * (c₀ * y * a) * z⁻¹ := by rw [h1]
    _ = y * (a * z⁻¹) := by group

theorem exists_pow_cube_eq_one {T : Subgroup 𝔾} (hT : IsPGroup 2 T) {d : 𝔾} (hd : d ^ 3 ∈ T) :
    ∃ N : ℕ, (d ^ N) ^ 3 = 1 ∧ d * (d ^ N)⁻¹ ∈ T := by
  obtain ⟨n, hn⟩ := hT ⟨d ^ 3, hd⟩
  have hn' : (d ^ 3) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨4 ^ n, ?_, ?_⟩
  · have e : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
      rw [← mul_pow]
      norm_num
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hn', one_pow]
  · have hmod : 4 ^ n % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    obtain ⟨t, ht⟩ : ∃ t, 4 ^ n = 3 * t + 1 := ⟨4 ^ n / 3, by
      have := Nat.div_add_mod (4 ^ n) 3
      omega⟩
    have : d * (d ^ 4 ^ n)⁻¹ = ((d ^ 3) ^ t)⁻¹ := by
      rw [ht, pow_succ, pow_mul]
      group
    rw [this]
    exact T.inv_mem (T.pow_mem hd _)

end Abstract

section Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commutator_mem_zh_of_cube (c : S46.Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1)
    (hψT : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    (h464 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam c.pu.le) δ ρ ≤ ZH _ ρ)
    (hodd : ∀ g ∈ stab (puAmalgam c.pu.le) α,
      g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) →
      (∀ z ∈ ZM (puAmalgam c.pu.le) α, ⁅z, g⁆ ∈ ZH _ β) → Odd (orderOf g) →
        ∀ x ∈ Vv (puAmalgam c.pu.le) β, ⁅x, g⁆ ∈ ZH _ β)
    {d : ↥(stab (puAmalgam c.pu.le) α)} (hdS : toSL3 ψ d ∈ (stabX0 : Subgroup (SL3 F)))
    (hd3 : ((d : (puAmalgam c.pu.le).Universal)) ^ 3 ∈ Qv (puAmalgam c.pu.le) β)
    {x : (puAmalgam c.pu.le).Universal} (hx : x ∈ Vv (puAmalgam c.pu.le) β) :
    ⁅(d : (puAmalgam c.pu.le).Universal), x⁆ ∈ ZH (puAmalgam c.pu.le) β := by
  have hβH : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  obtain ⟨N, hN3, hNT⟩ := exists_pow_cube_eq_one (isPGroup_qv _ c.pu.hyp20 hβH) hd3
  have hd₀S : toSL3 ψ (d ^ N) ∈ (stabX0 : Subgroup (SL3 F)) := by
    rw [map_pow]
    exact Subgroup.pow_mem _ hdS N
  have hd₀N := mem_normalizer_qv_of_toSL3_mem c.pu c.via hα hαβ hψU hψT hd₀S
  have hd₀Z := commutator_mem_zh_of_toSL3_mem c.pu c.via hα hαβ hψU hψT h464 hd₀S
  have hcoe : ((d ^ N : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) =
      (d : (puAmalgam c.pu.le).Universal) ^ N := by simp
  have hodd₀ : Odd (orderOf ((d ^ N : ↥(stab (puAmalgam c.pu.le) α)) :
      (puAmalgam c.pu.le).Universal)) := by
    rw [hcoe]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hN3)
  have hx₀ := hodd _ (d ^ N).2 hd₀N hd₀Z hodd₀ x hx
  rw [hcoe] at hx₀
  set s := (d : (puAmalgam c.pu.le).Universal) * ((d : (puAmalgam c.pu.le).Universal) ^ N)⁻¹
    with hs
  have e : ⁅(d : (puAmalgam c.pu.le).Universal), x⁆ =
      s * ⁅x, (d : (puAmalgam c.pu.le).Universal) ^ N⁆⁻¹ * s⁻¹ * ⁅s, x⁆ := by
    rw [hs, commutatorElement_inv]
    simp only [commutatorElement_def]
    group
  have h1 : s * ⁅x, (d : (puAmalgam c.pu.le).Universal) ^ N⁆⁻¹ * s⁻¹ =
      ⁅x, (d : (puAmalgam c.pu.le).Universal) ^ N⁆⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (Subgroup.inv_mem _ hx₀)) s hNT
    rw [this, mul_inv_cancel_right]
  have h2 : ⁅s, x⁆ ∈ ZH (puAmalgam c.pu.le) β := by
    have := S46.commutator_vv_qv_le_zh c.pu h464 hβH (Subgroup.commutator_mem_commutator hx hNT)
    rw [← commutatorElement_inv] at this
    simpa using Subgroup.inv_mem _ this
  rw [e, h1]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₀) h2

theorem zm_smul_le_vStar (c : S46.Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ)
    (hZγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α) {g : (puAmalgam c.pu.le).Universal}
    (hg : g ∈ stab (puAmalgam c.pu.le) α) :
    ZM (puAmalgam c.pu.le) (g • γ) ≤ S46.vStar c.pu.le L α := by
  have hgα : g • α = α := hg
  have hαρ : (puAmalgam c.pu.le).treeGraph.Adj α (g • β) := by
    have := (adj_smul _ g α β).mpr hαβ
    rwa [hgα] at this
  have hadj : (puAmalgam c.pu.le).treeGraph.Adj (g • β) (g • γ) :=
    (adj_smul _ g β γ).mpr hβγ
  have hnB : ¬ ZM (puAmalgam c.pu.le) (g • γ) ≤ Bloc c.pu.le L α := by
    intro hle
    apply hZγ
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [zm_smul, map_conj_inv_map_conj, ← hgα, bloc_smul c.pu, map_conj_inv_map_conj] at h1
    exact h1
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ (puAmalgam c.pu.le).treeGraph.neighborSet α) =>
    S46.vStarB c.pu.le L α β) (g • β) hαρ
    (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam c.pu.le) |
      (puAmalgam c.pu.le).treeGraph.Adj (g • β) ρ ∧
        ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α}) => ZM (puAmalgam c.pu.le) ρ)
      (g • γ) ⟨hadj, hnB⟩ le_rfl)

end Amalgam

end CFSG.Quasithin.MS93.S46.KCT
