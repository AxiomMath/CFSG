module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_zpowers_of_sq_eq_one {u : G} (hu2 : u ^ 2 = 1) :
    IsElemAbelian 2 (zpowers u) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]

private theorem centralizer_singleton_le_normalizer_zpowers (u : G) :
    centralizer ({u} : Set G) ≤ normalizer ((zpowers u : Subgroup G) : Set G) := by
  have h : centralizer ({u} : Set G) = centralizer ((zpowers u : Subgroup G) : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [h]
  exact centralizer_le_normalizer _

private theorem centralizer_le_of_rankThreeGamma_le {U M : Subgroup G}
    (hΓ : rankThreeGamma 1 2 U ≤ M) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) :
    centralizer ({u} : Set G) ≤ M := by
  have hQ : zpowers u ≤ U := (Subgroup.zpowers_le).2 hu
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hrk : 1 ≤ CFSG.Open.pRank 2 (zpowers u) :=
    UC6S846.le_pRank' Nat.prime_two (le_refl _) (isElemAbelian_zpowers_of_sq_eq_one hu2)
      (by rw [Nat.card_zpowers, hord, pow_one])
  have hN : normalizer ((zpowers u : Subgroup G) : Set G) ≤ rankThreeGamma 1 2 U := by
    unfold rankThreeGamma GLBCore
    exact le_sSup ⟨zpowers u, hQ, hrk, rfl⟩
  exact (centralizer_singleton_le_normalizer_zpowers u).trans (hN.trans hΓ)

private theorem mem_of_pRank_pos_of_le_inf_conjSubgroup {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) {g : G} {X : Subgroup G}
    (hX : X ≤ M ⊓ conjSubgroup M g) (hpos : 0 < CFSG.Open.pRank p X) : g ∈ M := by
  by_contra hg
  obtain ⟨E, hEX, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp X
  have hpE : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p (by omega)
  have hg' : g⁻¹ ∉ M := fun hh => hg (by simpa using M.inv_mem hh)
  exact hsp.2.2 g⁻¹ hg' (hpE.trans (Subgroup.card_dvd_of_le (hEX.trans hX)))

theorem sixteen_twentyTwo (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    ∀ g : G, g ∉ D.M → ∀ U : Subgroup G, U ≤ V → rankThreeGamma 1 2 U ≤ D.M →
      conjSubgroup U g ⊓ V = ⊥ := by
  intro g hg U hU hΓ
  obtain ⟨p, hp, hv⟩ := h21 V₀ V h
  have hpsig : p ∈ D.sig := by rw [hp]; exact Set.mem_singleton p
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (h1219 ▸ hpsig)
  have hVel : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hwU, hwV⟩ := Subgroup.mem_inf.1 hw
  have hu : g * w * g⁻¹ ∈ U := mem_conjSubgroup_iff.mp hwU
  have hu1 : g * w * g⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [e, h1]
    group
  have hcentu : centralizer ({g * w * g⁻¹} : Set G) ≤ D.M :=
    centralizer_le_of_rankThreeGamma_le hΓ hu hu1 (hVel.2 _ (hU hu))
  have hcentw : centralizer ({w} : Set G) ≤ conjSubgroup D.M g := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    apply hcentu
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hx]
      _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group
  exact hg (mem_of_pRank_pos_of_le_inf_conjSubgroup (D.sig_prime p hpsig).1 hsp
    (inf_le_inf_left _ hcentw) (hv w hwV hw1))

theorem R1622_of_R1621 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) : R1622 D :=
  fun _ _ h => sixteen_twentyTwo D hSg h1219 h21 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
