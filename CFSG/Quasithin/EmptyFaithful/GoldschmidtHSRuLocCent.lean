module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocComm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocQuot

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem hsru_cent {K R : Subgroup H} (hRK : R ≤ K) (hRn : (R.subgroupOf K).Normal)
    (hR2 : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) (hK : ⁅K, K⁆ = K)
    (hsimple : IsSimpleGroup (↥K ⧸ R.subgroupOf K)) {u y : H} (huK : u ∈ K) (hyK : y ∈ K)
    (hu : orderOf u = 7) (hy : orderOf y = 3)
    (hinv : ∀ t : H, orderOf t = 2 → ¬ 21 ∣ Nat.card (Subgroup.centralizer ({t} : Set H))) :
    ∀ k ∈ K, (∀ r ∈ R, k * r = r * k) → k ∈ R := by
  classical
  have hperf : Group.IsPerfect ↥K := isPerfect_of_comm_eq_self hK
  set N : Subgroup ↥K := R.subgroupOf K with hN
  set C : Subgroup ↥K := Subgroup.centralizer (N : Set ↥K) with hC
  have hCn : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hC, Subgroup.mem_centralizer_iff] at hx ⊢
    intro n hn
    have h1 : g⁻¹ * n * g ∈ N := by
      have := hRn.conj_mem n hn g⁻¹
      simpa using this
    have h2 := hx _ h1
    calc n * (g * x * g⁻¹) = g * ((g⁻¹ * n * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * n * g)) * g⁻¹ := by rw [h2]
      _ = (g * x * g⁻¹) * n := by group
  have hCN : C ≤ N := by
    have hmapn : (C.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map hCn _ (QuotientGroup.mk'_surjective N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' N)) with h | h
    · intro c hc
      have : QuotientGroup.mk' N c ∈ C.map (QuotientGroup.mk' N) := ⟨c, hc, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff c).mp this
    · exfalso
      have h2 : IsPGroup 2 (↥K ⧸ C) := by
        intro g
        induction g using QuotientGroup.induction_on with | _ g
        have hg : QuotientGroup.mk' N g ∈ C.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_top _
        obtain ⟨c, hc, hcg⟩ := hg
        have hn : c⁻¹ * g ∈ N := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hcg
          rw [hcg, inv_mul_cancel]
        have hnR : ((c⁻¹ * g : ↥K) : H) ∈ R := hn
        obtain ⟨m, hm⟩ := hR2 ⟨((c⁻¹ * g : ↥K) : H), hnR⟩
        refine ⟨m, ?_⟩
        have hm1 : ((c⁻¹ * g : ↥K) : H) ^ 2 ^ m = 1 := congrArg Subtype.val hm
        have hm' : (c⁻¹ * g) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm1)
        have : ((g : ↥K ⧸ C)) = ((c⁻¹ * g : ↥K) : ↥K ⧸ C) := by
          rw [QuotientGroup.eq]
          have := hCn.conj_mem c⁻¹ (C.inv_mem hc) g⁻¹
          simpa [mul_assoc] using this
        rw [this, ← QuotientGroup.mk_pow, hm']
        rfl
      have hperfQ : Group.IsPerfect (↥K ⧸ C) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
      have : Group.IsNilpotent (↥K ⧸ C) := h2.isNilpotent
      have hsub : Subsingleton (↥K ⧸ C) := by
        by_contra hns
        rw [not_subsingleton_iff_nontrivial] at hns
        have := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K ⧸ C)
        rw [Group.IsPerfect.commutator_eq_top] at this
        exact lt_irrefl _ this
      have hCtop : C = ⊤ := by
        rw [← Subgroup.index_eq_one]
        exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
      obtain ⟨⟨t, htR⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
      refine hno_of_inv hinv hR2 hu hy t htR (fun h => ht1 (Subtype.ext h)) ⟨?_, ?_⟩
      · have := (hCtop ▸ Subgroup.mem_top (⟨u, huK⟩ : ↥K))
        rw [hC, Subgroup.mem_centralizer_iff] at this
        exact congrArg Subtype.val (this ⟨t, hRK htR⟩ htR).symm
      · have := (hCtop ▸ Subgroup.mem_top (⟨y, hyK⟩ : ↥K))
        rw [hC, Subgroup.mem_centralizer_iff] at this
        exact congrArg Subtype.val (this ⟨t, hRK htR⟩ htR).symm
  intro k hk hkr
  have hkC : (⟨k, hk⟩ : ↥K) ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subtype.ext (hkr n hn).symm
  exact (Subgroup.mem_subgroupOf.mp (hCN hkC))

omit [Finite H] in
theorem hsru_notC {K P : Subgroup H} (hP2 : IsPGroup 2 ↥P) (h21 : 21 ∣ Nat.card K)
    (hinv : ∀ t : H, orderOf t = 2 → ¬ 21 ∣ Nat.card (Subgroup.centralizer ({t} : Set H)))
    {w : H} (hw : w ∈ P) (hw1 : w ≠ 1) : ∃ k ∈ K, k * w ≠ w * k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := exists_involution_pow hP2 hw hw1
  have hle : K ≤ Subgroup.centralizer ({w ^ n} : Set H) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.pow_right (show Commute k w from hcon k hk) n).eq
  exact hinv _ hn (h21.trans (Subgroup.card_dvd_of_le hle))

end CFSG.Quasithin.HSRuLoc.Mod
