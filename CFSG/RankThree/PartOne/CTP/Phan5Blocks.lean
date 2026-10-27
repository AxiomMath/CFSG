module

public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.RankThree.PartOne.CTP.PhanFour
public import CFSG.RankThree.PartOne.CTP.UnitaryEdge

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.CurtisTits

theorem weakPhanA_of_data
    {G : Type} [Group G] [Finite G] {n f p : ℕ}
    {K : Fin n → Subgroup G} {E : Subgroup G} (hf : 2 ≤ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1) (hE : IsElementaryAbelian p E) (hgen : (⨆ i, K i) = ⊤)
    (hK2 : ∀ i, StatedClassicalModel (K i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(K i ⊔ K j))
    (htor : CTTorusCondition p E K) :
    WeakPhanA (GaloisField 2 (2 * f)) 2 f n K (fun i j => K i ⊔ K j) := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hfd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hcomm' : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x := by
    intro i j hij x hx y hy
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    have hna : ¬ chainAdj i j := by
      rintro (h | h) <;> omega
    exact (Subgroup.mem_centralizer_iff.mp ((hcomm i j hne hna).1 hx) y hy).symm
  exact
    { iso := fun i => by
        obtain ⟨L, _, _, _, hL, ⟨ρ⟩⟩ := exists_sl2_equiv_of_model (hK2 i)
        obtain ⟨e⟩ := exists_suid_two_equiv_sl hF hL
        exact ⟨e.trans ρ⟩
      join := fun i j _ => rfl
      comm := hcomm'
      pair := by
        intro i j hij
        have hne : i ≠ j := by
          intro h
          subst h
          omega
        obtain ⟨θ₀, hsurj, hker₀⟩ :=
          exists_su3_surj_of_centrallyUThree hF (hadj i j (Or.inl hij.symm))
        obtain ⟨Li, _, _, _, hLi, ⟨ρi⟩⟩ := exists_sl2_equiv_of_model (hK2 i)
        obtain ⟨Lj, _, _, _, hLj, ⟨ρj⟩⟩ := exists_sl2_equiv_of_model (hK2 j)
        let θ : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 3 →* G :=
          (K i ⊔ K j).subtype.comp θ₀
        have hrange : θ.range = K i ⊔ K j := by
          rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
            Subgroup.range_subtype]
        have hker : θ.ker ≤ Subgroup.center
            (SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 3) := by
          intro x hx
          exact hker₀ (Subtype.ext hx)
        have hE' : EdgeTorus p E (K i) (K j) :=
          ⟨(htor.1 i).1, (htor.1 i).2, (htor.1 j).1, (htor.1 j).2, htor.2 i j hne⟩
        obtain ⟨c, hc1, hc2⟩ := unitary_edge_standardPair hfd hq hp hp2 hpq θ hker hE'
          hrange.symm hLi hLj ρi ρj
        exact ⟨θ, c, hrange, hker, Or.inl ⟨hc1, hc2⟩⟩
      gen := hgen }

theorem phan_blocks
    {G : Type} [Group G] [Finite G] {n f p : ℕ}
    {K : Fin n → Subgroup G} {E : Subgroup G} (hn : 3 ≤ n) (hf : 2 ≤ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1) (hE : IsElementaryAbelian p E) (hgen : (⨆ i, K i) = ⊤)
    (hK2 : ∀ i, StatedClassicalModel (K i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(K i ⊔ K j))
    (htor : CTTorusCondition p E K) :
    ∃ θ : Su (GaloisField 2 (2 * f)) 2 f (n + 1) →* G, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 2 (2 * f)) 2 f (n + 1)) ∧
      ∀ i : Fin n, (blockEmb2 (GaloisField 2 (2 * f)) 2 f n i).range.map θ = K i := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hW := weakPhanA_of_data hf hp hp3 hpq hE hgen hK2 hcomm hadj htor
  obtain ⟨F, hFι, hFinj, -⟩ := coherent_family hF (by omega) hW
  obtain ⟨ψ, hψ2, -⟩ := phanUniversalAt_of_four_le hF hq n F
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun i => ?_
    rw [← hFι i, ← hψ2 i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : CFSG.IsQuasisimple (Su (GaloisField 2 (2 * f)) 2 f (n + 1)) := by
    have h := (isQuasisimple_statedSU_of_card hF (n := n + 1) (by omega) (by
        intro h
        have : n + 1 = 3 := (Prod.mk.inj h).1
        omega)).1
    exact isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hF (n + 1))).symm h
  have hnontriv : ∃ k, ψ k ≠ 1 := by
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    have hsub : Subsingleton (Su (GaloisField 2 (2 * f)) 2 f 2) := by
      refine ⟨fun a b => hFinj i ?_⟩
      rw [← hψ2 i, MonoidHom.comp_apply, MonoidHom.comp_apply, hall, hall]
    have hcard : Nat.card (Su (GaloisField 2 (2 * f)) 2 f 2) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    have h1 : (1 : ℕ) < Nat.card (Su (GaloisField 2 (2 * f)) 2 f 2) := by
      obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
      rw [← Nat.card_congr (conjEquiv P hP).toEquiv, CFSG.LieType.Steinberg.card_SU_two hF]
      have h15 : 15 ≤ (2 ^ f) ^ 2 - 1 := by
        have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
        omega
      nlinarith
    omega
  refine ⟨ψ, hsurj, ker_le_center_of_isQuasisimple hquasi hnontriv, fun i => ?_⟩
  rw [← MonoidHom.range_comp, hψ2 i, hFι i]

end CFSG.RankThree.PartOne.CTP
