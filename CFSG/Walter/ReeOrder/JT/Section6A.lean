module

public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.ReeOrder.JT.Section4G
public import CFSG.Walter.ReeOrder.JT.Section4I

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_pgl2 (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    2 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
  have := GorensteinWalter.pgl2_card_formula K
  change Nat.card (GorensteinWalter.PGL2 K) = _ at this
  change 2 ∣ Nat.card (GorensteinWalter.PGL2 K)
  rw [this]
  obtain ⟨k, hk⟩ := hK
  rw [hk]
  exact Dvd.dvd.mul_left ⟨2 * k * k + 2 * k, by ring_nf; omega⟩ _

namespace JTHyp

variable (h : JTHyp G)

theorem odd_q (hp : h.p ≠ 2) : Odd h.q := by
  rw [JTHyp.q_eq]
  exact ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow

theorem odd_cases_F (hp : h.p ≠ 2) {H : Subgroup G} (hHF : H ≤ h.F)
    (hodd : Odd (Nat.card H)) :
    (∃ N : Subgroup G, N ≤ H ∧ (∀ x ∈ H, x ∈ Subgroup.normalizer (N : Set G)) ∧
      IsPGroup h.p N ∧ ∃ m t : ℕ, Nat.card N = h.p ^ m ∧ m ≤ h.f ∧
        Nat.card H = h.p ^ m * t ∧ t ∣ (h.q - 1) / 2 ∧ t ∣ h.p ^ m - 1) ∨
      Nat.card H ∣ (h.q + 1) / 2 := by
  classical
  have hqodd := h.odd_q hp
  set K := GaloisField h.p h.f
  have hKcard : Nat.card K = h.p ^ h.f := GaloisField.card h.p h.f h.f_pos
  have hKq : Nat.card K = h.q := hKcard.trans (JTHyp.q_eq h).symm
  set H' := (H.subgroupOf h.F).map h.iso.toMonoidHom with hH'def
  have eH : H ≃* H' :=
    (Subgroup.subgroupOfEquivOfLe hHF).symm.trans
      ((H.subgroupOf h.F).equivMapOfInjective _ h.iso.injective)
  have hH'card : Nat.card H' = Nat.card H := (Nat.card_congr eH.toEquiv).symm
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    rw [hKq]
    have : 2 ∣ h.q - 1 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    exact Nat.gcd_eq_right this
  have hgcd' : Nat.gcd (h.p ^ h.f - 1) 2 = 2 := by rw [← hKcard]; exact hgcd
  have hpu := psl2UnipotentFacts h.F h.iso hp h.f_pos
  have hmf : ∀ {N : Subgroup G} {m : ℕ}, N ≤ H → IsPGroup h.p N → Nat.card N = h.p ^ m →
      m ≤ h.f := by
    intro N m hNH hNp hNm
    have := hpu.card_dvd N (hNH.trans hHF) hNp
    rw [hNm] at this
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : h.p.Prime).one_lt).mp this
  have heven : ¬ 2 ∣ Nat.card H := fun h2 =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hKcard H' with
    hea | ⟨z, hz, hcard, -⟩ | ⟨z, -, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, htm, htq, N', C', hN'n, -, hN'card, -, hC'card, hdisj, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  ·
    left
    have hpg : IsPGroup h.p H := (IsElementaryAbelian.isPGroup h.p H').of_injective
      eH.toMonoidHom eH.injective
    obtain ⟨m, hm⟩ := hpg.exists_card_eq
    refine ⟨H, le_rfl, fun x hx => Subgroup.le_normalizer hx, hpg, m, 1, hm,
      hmf le_rfl hpg hm, by rw [hm, mul_one], one_dvd _, one_dvd _⟩
  · rw [hgcd, hKq] at hz
    rcases hz with hz | hz
    · left
      refine ⟨⊥, bot_le, fun x _ => ?_, IsPGroup.of_bot, 0, z, by simp, Nat.zero_le _,
        by rw [← hH'card, hcard, pow_zero, one_mul], hz, by simp⟩
      exact mem_normalizer_of_conj_mem fun y hy => by
        rw [Subgroup.mem_bot] at hy ⊢
        rw [hy, mul_one, mul_inv_cancel]
    · right
      rw [← hH'card, hcard]
      exact hz
  · exfalso
    rw [← hH'card, hcard] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul z)
  · exfalso
    rw [← hH'card, Nat.card_congr e.toEquiv, card_alternatingGroup_four] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [← hH'card, Nat.card_congr e.toEquiv, card_perm_four] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [← hH'card, Nat.card_congr e.toEquiv, card_alternatingGroup_five] at hodd
    exact absurd hodd (by decide)
  ·
    left
    set N₀ := N'.map eH.symm.toMonoidHom with hN₀def
    have hN₀n : N₀.Normal := Subgroup.Normal.map hN'n _ eH.symm.surjective
    set N := N₀.map H.subtype with hNdef
    have hNcard : Nat.card N = h.p ^ m := by
      rw [hNdef, Subgroup.card_map_of_injective H.subtype_injective, hN₀def,
        Subgroup.card_map_of_injective eH.symm.injective, hN'card]
    have hNp : IsPGroup h.p N := IsPGroup.of_card hNcard
    have hNH : N ≤ H := Subgroup.map_subtype_le _
    have hH'eq : Nat.card H' = h.p ^ m * t := by
      have hle : C' ≤ Subgroup.normalizer (N' : Set H') := by
        intro c _
        have := hN'n
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      have := card_sup_eq_mul_of_disjoint hle hdisj.symm
      rw [sup_comm, hsup, Subgroup.card_top, hC'card, hN'card, mul_comm] at this
      exact this
    refine ⟨N, hNH, fun x hx => ?_, hNp, m, t, hNcard, hmf hNH hNp hNcard,
      by rw [← hH'card, hH'eq], by rw [← hgcd', ← JTHyp.q_eq]; exact htq, htm⟩
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨n, hn, rfl⟩ := hy
    refine ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hN₀n.conj_mem n hn ⟨x, hx⟩, ?_⟩
    simp
  ·
    exfalso
    apply heven
    rw [← hH'card, Nat.card_congr e.toEquiv]
    refine Suzuki.two_dvd_card_psl2 (GaloisField h.p m) ⟨h.p, m, Fact.out,
      (Fact.out : h.p.Prime).odd_of_ne_two hp, Nat.pos_of_ne_zero hm, ?_⟩
    exact GaloisField.card h.p m hm
  ·
    exfalso
    apply heven
    rw [← hH'card, Nat.card_congr e.toEquiv]
    refine two_dvd_card_pgl2 (GaloisField h.p m) ?_
    rw [GaloisField.card h.p m hm]
    exact ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow

theorem odd_cases
    (hp : h.p ≠ 2) {u : G} (hu : orderOf u = 2) {H : Subgroup G}
    (hHu : H ≤ Subgroup.centralizer ({u} : Set G)) (hodd : Odd (Nat.card H)) :
    (∃ N : Subgroup G, N ≤ H ∧ (∀ x ∈ H, x ∈ Subgroup.normalizer (N : Set G)) ∧
      IsPGroup h.p N ∧ ∃ m t : ℕ, Nat.card N = h.p ^ m ∧ m ≤ h.f ∧
        Nat.card H = h.p ^ m * t ∧ t ∣ (h.q - 1) / 2 ∧ t ∣ h.p ^ m - 1) ∨
      Nat.card H ∣ (h.q + 1) / 2 := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set φ := (MulAut.conj g).toMonoidHom with hφdef
  set H' := H.map φ with hH'def
  have hH'card : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hH't : H' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hHu hx)
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hH'F : H' ≤ h.F := h.le_F_of_odd hH't (hH'card ▸ hodd)
  rcases h.odd_cases_F hp hH'F (hH'card ▸ hodd) with
    ⟨N, hNH, hNn, hNp, m, t, hNcard, hmf, hHcard, htq, htm⟩ | hdvd
  · left
    set ψ := (MulAut.conj g⁻¹).toMonoidHom with hψdef
    have hψφ : ∀ x : G, ψ (φ x) = x := fun x => by
      simp [hψdef, hφdef, MulAut.conj_apply, mul_assoc]
    refine ⟨N.map ψ, ?_, ?_, hNp.map ψ, m, t, ?_, hmf, hH'card ▸ hHcard, htq, htm⟩
    · rintro _ ⟨n, hn, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hNH hn
      rw [hψφ]
      exact hx
    · intro x hx
      have hφx : φ x ∈ Subgroup.normalizer (N : Set G) := hNn _ ⟨x, hx, rfl⟩
      have := Subgroup.le_normalizer_map ψ ⟨φ x, hφx, rfl⟩
      rwa [hψφ] at this
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hNcard]
  · right
    rwa [hH'card] at hdvd

theorem exists_conj_of_card_eq
    (hp : h.p ≠ 2) {R : Subgroup G} (hRF : R ≤ h.F)
    (hR : Nat.card R = h.q) {u : G} (hu : orderOf u = 2) {X : Subgroup G}
    (hXu : X ≤ Subgroup.centralizer ({u} : Set G)) (hX : Nat.card X = h.q) :
    ∃ g : G, X.map (MulAut.conj g).toMonoidHom = R := by
  classical
  have hqodd := h.odd_q hp
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  have hX'card : Nat.card X' = h.q := by
    rw [hX'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hX]
  have hX't : X' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hX'F : X' ≤ h.F := h.le_F_of_odd hX't (by rw [hX'card]; exact hqodd)
  set K := GaloisField h.p h.f
  have hKcard : Nat.card K = h.p ^ h.f := GaloisField.card h.p h.f h.f_pos
  have hfac : h.p ^ (Nat.card h.F).factorization h.p = h.q := by
    rw [Nat.card_congr h.iso.toEquiv,
      ← Sylow.card_eq_multiplicity (default : Sylow h.p PSL(2, K)), JTHyp.q_eq]
    exact psl2_card_sylow_p hKcard hp h.f_pos _
  have hsyl : ∀ Y : Subgroup G, Y ≤ h.F → Nat.card Y = h.q →
      Nat.card (Y.subgroupOf h.F) = h.p ^ (Nat.card h.F).factorization h.p := fun Y hYF hY => by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYF).toEquiv, hY, hfac]
  let S₁ : Sylow h.p h.F := Sylow.ofCard _ (hsyl X' hX'F hX'card)
  let S₂ : Sylow h.p h.F := Sylow.ofCard _ (hsyl R hRF hR)
  have hS₁ : (S₁ : Subgroup h.F) = X'.subgroupOf h.F := Sylow.coe_ofCard _ _
  have hS₂ : (S₂ : Subgroup h.F) = R.subgroupOf h.F := Sylow.coe_ofCard _ _
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq h.F S₁ S₂
  refine ⟨(k : G) * g, ?_⟩
  have hle : X.map (MulAut.conj ((k : G) * g)).toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have hgx : g * x * g⁻¹ ∈ X' := ⟨x, hx, rfl⟩
    have hmem : k * ⟨g * x * g⁻¹, hX'F hgx⟩ * k⁻¹ ∈ (S₂ : Subgroup h.F) := by
      rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      refine ⟨⟨g * x * g⁻¹, hX'F hgx⟩, ?_, rfl⟩
      rw [hS₁]
      exact hgx
    rw [hS₂, Subgroup.mem_subgroupOf] at hmem
    have : ((k * ⟨g * x * g⁻¹, hX'F hgx⟩ * k⁻¹ : h.F) : G) =
        (MulAut.conj ((k : G) * g)).toMonoidHom x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [← this]
    exact hmem
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [hR, Subgroup.card_map_of_injective (MulAut.conj _).injective, hX])

end JTHyp

end CFSG.Walter.JT
