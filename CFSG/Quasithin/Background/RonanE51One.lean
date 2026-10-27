module

public import CFSG.Quasithin.Background.RonanE51Basic
public import CFSG.Quasithin.Background.E2Basic
public import CFSG.Quasithin.Background.E1Sec6
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open
open scoped commutatorElement

theorem eq_of_le_frattiniIn_sup {Y : Type*} [Group Y] [Finite Y] {P X : Subgroup Y} (hXP : X ≤ P)
    (h : P ≤ frattiniIn P ⊔ X) : X = P := by
  have hΦP : frattiniIn P ≤ P := fun _ ⟨y, _, hy⟩ => hy ▸ y.2
  have h1 : (frattiniIn P ⊔ X).subgroupOf P = ⊤ := Subgroup.subgroupOf_eq_top.2 h
  rw [Subgroup.subgroupOf_sup hΦP hXP] at h1
  have h2 : (frattiniIn P).subgroupOf P = frattini ↥P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  rw [h2] at h1
  have h3 : X.subgroupOf P = ⊤ := frattini_nongenerating (by rw [sup_comm]; exact h1)
  exact le_antisymm hXP (Subgroup.subgroupOf_eq_top.1 h3)

theorem inf_le_twoResidual_of_isPGroup {Λ : Type*} [Group Λ] [Finite Λ] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S N : Subgroup Λ} (hN : IsPGroup p N) : S ⊓ N ≤ twoResidual S := by
  intro x hx
  obtain ⟨a, ha⟩ := hN ⟨x, hx.2⟩
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient S x hx.1
  refine E1.mem_of_pow_mem_of_coprime (a := p ^ a) (b := 2 ^ k) ?_ ?_ hk
  · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  · have : x ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
    rw [this]
    exact Subgroup.one_mem _

theorem le_pCore_of_eOne {Γ : Type} [Group Γ] [Finite Γ] {B : Subgroup Γ} (hE : E1.EOne Γ B)
    {S D : Subgroup Γ} [hSn : S.Normal] (hD2 : IsPGroup 2 D) (hDS : D ≤ S)
    (hS : twoResidual S ≤ (frattiniIn (CFSG.generalizedFitting (Γ ⧸ CFSG.pCore 2 Γ))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 Γ))) :
    D ≤ CFSG.pCore 2 Γ := by
  obtain ⟨p, hp, hp2, h22, -, -, -⟩ := hE
  have : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore 2 Γ with hQ
  set π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set P₀ : Subgroup (Γ ⧸ Q) := CFSG.pCore p (Γ ⧸ Q) with hP₀
  have hP₀p : IsPGroup p P₀ := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hP₀n : P₀.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have h2P : ∀ y : Γ ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ P₀ := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP Γ p) (fun q => by
      have hq : q ∈ E1.oTwoPTwo Γ p := by rw [h22]; exact Subgroup.mem_top q
      exact hq) x
    exact ⟨k, by rw [← map_pow]; exact hk⟩
  have hO2 : CFSG.pCore 2 (Γ ⧸ Q) = ⊥ := VolI.E54.pCore_two_quotient_eq_bot
  have hsolv₀ : Group.IsSolvable ↥P₀ := by
    have := hP₀p.isNilpotent
    infer_instance
  have hsolv : Group.IsSolvable (Γ ⧸ Q) := isSolvable_of_forall_pow_mem hsolv₀ h2P
  have hchar : Subgroup.centralizer (P₀ : Set (Γ ⧸ Q)) ≤ P₀ :=
    E2.centralizer_pCore_le hp h2P hO2 hsolv
  have hFP : CFSG.generalizedFitting (Γ ⧸ Q) = P₀ :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore (Γ ⧸ Q) p).1 hchar
  rw [hFP] at hS
  set Φ : Subgroup (Γ ⧸ Q) := frattiniIn P₀ with hΦ
  set S₁ : Subgroup (Γ ⧸ Q) := S.map π with hS₁
  set D₁ : Subgroup (Γ ⧸ Q) := D.map π with hD₁
  have hS₁n : S₁.Normal := Subgroup.Normal.map hSn π hπs
  have hD₁S₁ : D₁ ≤ S₁ := Subgroup.map_mono hDS
  have hres : twoResidual S₁ ≤ Φ := by
    rw [← E1.map_twoResidual π S]
    calc (twoResidual S).map π ≤ (Φ.comap π).map π := Subgroup.map_mono hS
      _ = Φ := Subgroup.map_comap_eq_self_of_surjective hπs Φ
  have hSP : S₁ ⊓ P₀ ≤ twoResidual S₁ := inf_le_twoResidual_of_isPGroup hp hp2 hP₀p
  have hcomm : ⁅P₀, D₁⁆ ≤ Φ := by
    have h1 : ⁅P₀, D₁⁆ ≤ ⁅P₀, S₁⁆ := Subgroup.commutator_mono le_rfl hD₁S₁
    have h2 : ⁅P₀, S₁⁆ ≤ P₀ ⊓ S₁ := Subgroup.commutator_le_inf P₀ S₁
    exact (h1.trans (h2.trans (by rw [inf_comm]; exact hSP))).trans hres
  have hD₁2 : IsPGroup 2 ↥D₁ := hD2.map π
  have hnorm : D₁ ≤ Subgroup.normalizer (P₀ : Set (Γ ⧸ Q)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hP₀n]
    exact le_top
  have hcop : Nat.Coprime 2 (Nat.card P₀) := by
    obtain ⟨n, hn⟩ := hP₀p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm)
  have hfac := E1.comm_sup_inf_centralizer_eq hnorm hD₁2 hcop hsolv₀
  have hX : P₀ ⊓ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q)) = P₀ :=
    eq_of_le_frattiniIn_sup inf_le_left
      (hfac.symm.le.trans (sup_le_sup_right hcomm _))
  have hPD : P₀ ≤ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q)) := by
    rw [← hX]
    exact inf_le_right
  have hD₁P : D₁ ≤ P₀ := by
    intro d hd
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (hPD hy) d hd).symm
  have hbot : D₁ = ⊥ := by
    have h1 := E1.inf_eq_bot_of_isPGroup hp hp2 hP₀p hD₁2
    rw [← h1]
    exact (inf_eq_right.2 hD₁P).symm
  intro d hd
  have h1 : π d ∈ D₁ := Subgroup.mem_map_of_mem π hd
  rw [hbot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff d).1 h1

end CFSG.Quasithin.RonanE51
