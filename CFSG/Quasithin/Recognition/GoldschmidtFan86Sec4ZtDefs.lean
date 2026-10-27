module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mem_ZT_iff {T : Track Γ G} {d : ℤ} {z : G} :
    z ∈ ZT T d ↔ z ∈ T.fixer ∧ ∀ k ∈ nbrStab Γ G (T.line.vert d), k * z = z * k := by
  simp only [ZT, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem nbrStab_smul_iff (F : FanTree Γ G) (g : G) (v : V) (k : G) :
    k ∈ nbrStab Γ G (g • v) ↔ g⁻¹ * k * g ∈ nbrStab Γ G v := by
  constructor
  · intro hk w hw
    have hw' : Γ.Adj (g • v) (g • w) := (F.adj_smul g _ _).2 hw
    have := hk _ hw'
    rw [mul_smul, mul_smul, this, inv_smul_smul]
  · intro hk w hw
    have hw' : Γ.Adj v (g⁻¹ • w) := by
      have := (F.adj_smul g⁻¹ _ _).2 hw
      rwa [inv_smul_smul] at this
    have := hk _ hw'
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    have h2 : k • w = g • g⁻¹ • w := by rw [← this]; simp
    rw [h2, smul_inv_smul]

theorem zt_shift (F : FanTree Γ G) (T : Track Γ G) {d : ℤ} (h : ZT T d = ⊥) (k : ℤ) :
    ZT T (d + 2 * k) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_ZT_iff] at hz
  obtain ⟨hzf, hzc⟩ := hz
  have hw : (T.τ ^ k)⁻¹ * z * T.τ ^ k ∈ ZT T d := by
    rw [mem_ZT_iff]
    refine ⟨?_, fun k' hk' => ?_⟩
    · have := (T.conj_mem_fixer (-k) (h := z)).2 hzf
      simpa [zpow_neg] using this
    · have hm : T.τ ^ k * k' * (T.τ ^ k)⁻¹ ∈ nbrStab Γ G (T.line.vert (d + 2 * k)) := by
        rw [← T.zpow_smul_vert k d, nbrStab_smul_iff F]
        have e : (T.τ ^ k)⁻¹ * (T.τ ^ k * k' * (T.τ ^ k)⁻¹) * T.τ ^ k = k' := by group
        rw [e]
        exact hk'
      have := hzc _ hm
      calc k' * ((T.τ ^ k)⁻¹ * z * T.τ ^ k)
          = (T.τ ^ k)⁻¹ * ((T.τ ^ k * k' * (T.τ ^ k)⁻¹) * z) * T.τ ^ k := by group
        _ = (T.τ ^ k)⁻¹ * (z * (T.τ ^ k * k' * (T.τ ^ k)⁻¹)) * T.τ ^ k := by rw [this]
        _ = (T.τ ^ k)⁻¹ * z * T.τ ^ k * k' := by group
  rw [h] at hw
  have : (T.τ ^ k)⁻¹ * z * T.τ ^ k = 1 := hw
  have : z = 1 := by
    calc z = T.τ ^ k * ((T.τ ^ k)⁻¹ * z * T.τ ^ k) * (T.τ ^ k)⁻¹ := by group
      _ = 1 := by rw [this]; group
  exact Subgroup.mem_bot.2 this

end CFSG.Quasithin.Fan86
