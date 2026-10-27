module

public import CFSG.Quasithin.Recognition.CertU33DcPG
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Sporadic.Bridge

namespace GoldCMax

@[expose] def u33zc : U33G := u33GenPG 0 * u33GenPG 1

theorem u33_cen_check : ∀ i : Fin 32,
    u33GenP 0 * u33Tel u33GenP i = u33Tel u33GenP i * u33GenP 0 →
    u33GenP 1 * u33Tel u33GenP i = u33Tel u33GenP i * u33GenP 1 →
    u33GenP 2 * u33Tel u33GenP i = u33Tel u33GenP i * u33GenP 2 →
    ∃ k : Fin 4, u33Tel u33GenP i = (u33GenP 0 * u33GenP 1) ^ (k : ℕ) := by
  decide +kernel

theorem u33_gen_comm : ∀ n : Fin 5, n.val ≠ 3 →
    (u33GenP 0 * u33GenP 1) * u33GenP n = u33GenP n * (u33GenP 0 * u33GenP 1) := by
  decide +kernel

theorem u33PresHom_zc :
    u33PresHom u33zc = u33GenP 0 * u33GenP 1 := by
  simp [u33zc, map_mul, u33PresHom_genPG]

theorem zc_comm_gen {n : ℕ}
    (hn : n < 5) (hn3 : n ≠ 3) : u33zc * u33GenPG n = u33GenPG n * u33zc := by
  apply u33PresHom_injective
  rw [map_mul, map_mul, u33PresHom_zc, u33PresHom_genPG]
  exact u33_gen_comm ⟨n, hn⟩ hn3

theorem centerOf_T_le :
    centerOf u33Data.T ≤ Subgroup.zpowers u33zc := by
  rintro t ⟨htT, htc⟩
  obtain ⟨i, rfl⟩ := (u33Data.mem_T_iff t).mp htT
  have hcomm : ∀ n : ℕ, n < 3 →
      u33GenP n * u33Tel u33GenP i = u33Tel u33GenP i * u33GenP n := by
    intro n hn
    have hmem : u33GenPG n ∈ u33Data.T := by
      interval_cases n
      · exact u33Data.a_mem_T
      · exact u33Data.b_mem_T
      · exact u33Data.s_mem_T
    have h : u33PresHom (u33GenPG n * u33Tel u33GenPG i) =
        u33PresHom (u33Tel u33GenPG i * u33GenPG n) :=
      congrArg u33PresHom (Subgroup.mem_centralizer_iff.mp htc _ hmem)
    simpa only [map_mul, u33PresHom_genPG, u33Tel_hom] using h
  obtain ⟨k, hk⟩ := u33_cen_check i (hcomm 0 (by norm_num)) (hcomm 1 (by norm_num))
    (hcomm 2 (by norm_num))
  have : u33Tel u33GenPG i = u33zc ^ (k : ℕ) := by
    apply u33PresHom_injective
    rw [u33Tel_hom, hk, map_pow, u33PresHom_zc]
  show u33Tel u33GenPG i ∈ Subgroup.zpowers u33zc
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end GoldCMax

end CFSG.Quasithin
