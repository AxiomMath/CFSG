module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineNormal
public import CFSG.GroupTheory.AbelianHallSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_inf_of_le_normalizer {H K X : Subgroup G}
    (hXH : X ≤ Subgroup.normalizer (H : Set G))
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  (le_inf hXH hXK).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem card_map_eq_card_of_inf_ker_bot {G' : Type} [Group G'] {f : G →* G'}
    (H : Subgroup G) (hH : H ⊓ f.ker = ⊥) :
    Nat.card (H.map f) = Nat.card H := by
  classical
  let g : ↥H → ↥(H.map f) := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have h1 : f ((x : G) / (y : G)) = 1 := by
        rw [map_div, div_eq_one]
        exact Subtype.ext_iff.mp hxy
      have h2 : (x : G) / (y : G) ∈ H ⊓ f.ker :=
        ⟨H.div_mem x.2 y.2, MonoidHom.mem_ker.mpr h1⟩
      rw [hH] at h2
      exact div_eq_one.mp (Subgroup.mem_bot.mp h2)
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

namespace Ctx23L

theorem comm_A_cartan (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {DL : Subgroup G}
    (hDL : DL ≤ CFSG.Quasithin.borelOf c.L D.T) :
    ∀ a ∈ K ⊓ Subgroup.normalizer (D.T : Set G), ∀ b ∈ DL,
      a * b * a⁻¹ * b⁻¹ ∈ D.T ⊓ K := by
  intro a ha b hb
  have hKleM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c hKleM hK.2.1
  have hDLleL : DL ≤ c.L := hDL.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)
  have hDLN : DL ≤ Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    hDL.trans (normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c)
  have hbM : b ∈ D.M := (hDLN hb).2
  have hMNK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleM).mp hKn
  have haK : a ∈ K := ha.1
  have hbK : b * a⁻¹ * b⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hMNK hbM) a⁻¹).mp (K.inv_mem haK)
  have hmemK : a * b * a⁻¹ * b⁻¹ ∈ K := by
    have := K.mul_mem haK hbK
    simpa only [mul_assoc] using this
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left.trans (Ctx23L.sup_le_N D Ch c))).mp
      (normal_L_N D Ch h4 h23 h208 h1930 c)
  have hN4 : Subgroup.normalizer (D.T : Set G) ≤ c.N :=
    normalizer_T_le_N c h1930 h4 h3 hPush
  have haN : a ∈ c.N := hN4 ha.2
  have hmemL : a * b * a⁻¹ * b⁻¹ ∈ c.L := by
    have ha' : a * b * a⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (hNL haN) b).mp (hDLleL hb)
    exact c.L.mul_mem ha' (c.L.inv_mem (hDLleL hb))
  have hmemCZ : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (D.Z : Set G) :=
    hKCZ hmemK
  have hN1 := L_inf_centralizer_Z_eq D Ch h4 h23 h1930 c
  have hmemTL : a * b * a⁻¹ * b⁻¹ ∈ D.T ⊓ c.L := by
    rw [← hN1]
    exact ⟨hmemL, hmemCZ⟩
  exact ⟨hmemTL.1, hmemK⟩

theorem rhoK_cartan_inner (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {e m : ℕ}
    (hL2 : IsL2 (Bar2 K) (2 ^ e * m)) (hm2 : 2 ≤ m) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G))
    (hA₀card : Nat.card A₀ = 2 ^ m - 1) {DL : Subgroup G}
    (hDL : DL ≤ CFSG.Quasithin.borelOf c.L D.T) (hDLodd : Odd (Nat.card DL)) {b : G}
    (hb : b ∈ DL) (hbK : b ∈ Subgroup.normalizer (K : Set G)) :
    ∃ y : Bar2 K, UC6S846.rhoL K ⟨b, hbK⟩ = MulAut.conj y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let TK : Subgroup G := D.T ⊓ K
  let θ : MulAut (Bar2 K) := UC6S846.rhoL K ⟨b, hbK⟩
  have hDLN : DL ≤ Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    hDL.trans (normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c)
  have hbTK : b ∈ Subgroup.normalizer (TK : Set G) :=
    CFSG.ABGLocalTools.mem_normalizer_inf (hDLN hb).1 hbK
  have hpres : ∀ x ∈ (S : Subgroup (Bar2 K)), θ x ∈ (S : Subgroup (Bar2 K)) := by
    intro x hx
    have hSbar : (S : Subgroup (Bar2 K)) =
        Subgroup.map q (TK.subgroupOf K) := hS
    have hmap : Subgroup.map θ.toMonoidHom (S : Subgroup (Bar2 K)) =
        (S : Subgroup (Bar2 K)) := by
      rw [hSbar]
      exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
        ⟨b, hbK⟩ hbTK
    rw [← hmap]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom hx
  have hbodd : Odd (orderOf b) := by
    have h := Odd.of_dvd_nat hDLodd (orderOf_dvd_natCard (⟨b, hb⟩ : ↥DL))
    exact (Subgroup.orderOf_coe (⟨b, hb⟩ : ↥DL)).symm ▸ h
  have hodd : Odd (orderOf θ) := by
    have h1 : orderOf θ ∣
        orderOf (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set G))) :=
      orderOf_map_dvd (UC6S846.rhoL K) ⟨b, hbK⟩
    have h2 : Odd (orderOf (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set G)))) := by
      have h3 : Odd (orderOf
          ((⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set G))) : G)) := by
        simpa using hbodd
      exact Subgroup.orderOf_coe (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set G))) ▸ h3
    exact Odd.of_dvd_nat h2 h1
  let H : Subgroup (Bar2 K) := Subgroup.map q (A₀.subgroupOf K)
  have hA₀leK : A₀ ≤ K := hA₀.trans inf_le_left
  have hA₀normTK : A₀ ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer (hA₀.trans inf_le_right)
      (hA₀leK.trans (Subgroup.le_normalizer (H := K)))
  have hHle : H ≤ Subgroup.normalizer ((S : Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    have hxTK : (x : G) ∈ Subgroup.normalizer (TK : Set G) :=
      hA₀normTK (Subgroup.mem_subgroupOf.mp hx)
    have hSmap : (S : Subgroup (Bar2 K)) = Subgroup.map q (TK.subgroupOf K) := hS
    have hconj : ∀ y ∈ (S : Subgroup (Bar2 K)),
        q x * y * (q x)⁻¹ ∈ (S : Subgroup (Bar2 K)) := by
      intro y hy
      rw [hSmap] at hy ⊢
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      have hzTK : (z : G) ∈ TK := Subgroup.mem_subgroupOf.mp hz
      have hc : (x : G) * (z : G) * (x : G)⁻¹ ∈ TK :=
        (Subgroup.mem_normalizer_iff.mp hxTK (z : G)).mp hzTK
      have heq : q x * q z * (q x)⁻¹ =
          q (⟨(x : G) * (z : G) * (x : G)⁻¹, hc.2⟩ : ↥K) := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [heq]
      exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hc)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact hconj z hz
    · rw [Subgroup.card_map_of_injective (MulAut.conj (q x)).injective]
  have hA₀odd : Odd (Nat.card A₀) := by
    rw [hA₀card]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hpc2 : IsPGroup 2 (CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  have hcardA₀sub : Nat.card (A₀.subgroupOf K) = Nat.card A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀leK).toEquiv
  have hcop : Nat.Coprime (Nat.card (A₀.subgroupOf K))
      (Nat.card (CFSG.pCore 2 ↥K)) := by
    obtain ⟨k, hk⟩ := hpc2.exists_card_eq
    rw [hcardA₀sub, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hA₀odd)
  have hHcard : Nat.card H = 2 ^ m - 1 := by
    rw [card_map_eq_card_of_inf_ker_bot (A₀.subgroupOf K) ?_, hcardA₀sub, hA₀card]
    simpa only [q, QuotientGroup.ker_mk'] using Subgroup.inf_eq_bot_of_coprime hcop
  have hfix : ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (Bar2 K)) := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
    have haA₀ : (a : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp ha
    have hcomm := comm_A_cartan D Ch h4 h23 h208 h1930 c h3 hPush hK hKn hDL
      (a : G) ⟨a.2, hA₀.trans inf_le_right haA₀⟩ b hb
    have hmemTK : b * (a : G) * b⁻¹ * (a : G)⁻¹ ∈ TK := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using TK.inv_mem hcomm
    have hcoe : b * (a : G) * b⁻¹ * (a : G)⁻¹ ∈ K := hmemTK.2
    have heq : θ (q a) * (q a)⁻¹ =
        q (⟨b * (a : G) * b⁻¹ * (a : G)⁻¹, hcoe⟩ : ↥K) := by
      rw [show θ (q a) = q ⟨b * (a : G) * b⁻¹,
          (Subgroup.mem_normalizer_iff.mp hbK (a : G)).mp a.2⟩ from
        rhoL_apply_mk hbK a, ← map_inv, ← map_mul]
      rfl
    have hSmap : (S : Subgroup (Bar2 K)) = Subgroup.map q (TK.subgroupOf K) := hS
    rw [heq, hSmap]
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hmemTK)
  obtain ⟨y, hy⟩ := kL2OddAutInner_holds (Bar2 K) e m hL2 S θ hodd hpres H hHle hHcard hfix
  exact ⟨y, hy.symm⟩

theorem exists_F (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {e m : ℕ}
    (hL2 : IsL2 (Bar2 K) (2 ^ e * m)) (hm2 : 2 ≤ m) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G))
    (hA₀card : Nat.card A₀ = 2 ^ m - 1) {DL : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T) (hDLcard : Nat.card DL = 2 ^
      CFSG.Open.pRank 2 D.Z - 1) (hDLcomm : IsMulCommutative DL) :
    ∃ F : Subgroup G, DL ≤ F ∧ F ≤ (K ⊓ Subgroup.normalizer (D.T : Set G)) ⊔ DL ∧
      Odd (Nat.card F) ∧ IsMulCommutative F ∧ (D.T ⊓ K) ⊓ F = ⊥ ∧
      (D.T ⊓ K) ⊔ ((K ⊓ Subgroup.normalizer (D.T : Set G)) ⊓ F) =
        K ⊓ Subgroup.normalizer (D.T : Set G) ∧
      F ⊓ K ≠ ⊥ ∧ F ≤ c.N ∧ F ≤ D.M ∧ F ≤ Subgroup.normalizer (D.T : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Astar : Subgroup G := K ⊓ Subgroup.normalizer (D.T : Set G)
  let TK : Subgroup G := D.T ⊓ K
  have hT2 : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG
  have hTK2 : IsPGroup 2 TK :=
    IsPGroup.to_inf_left (p := 2) (H := D.T) (K := K) hT2
  have hAstarK : Astar ≤ K := inf_le_left
  have hAstarNT : Astar ≤ Subgroup.normalizer (D.T : Set G) := inf_le_right
  have hAstarM : Astar ≤ D.M := hAstarK.trans (uc22p22a_le_of_isSubnormal hK.1)
  have hN4 : Subgroup.normalizer (D.T : Set G) ≤ c.N :=
    normalizer_T_le_N c h1930 h4 h3 hPush
  have hAstarN : Astar ≤ c.N := hAstarNT.trans hN4
  have hDLN : DL ≤ Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    hDLleB.trans (normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c)
  have hDLN' : DL ≤ Subgroup.normalizer (D.T : Set G) := hDLN.trans inf_le_left
  have hDLM : DL ≤ D.M := hDLN.trans inf_le_right
  have hMNK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (uc22p22a_le_of_isSubnormal hK.1)).mp hKn
  have hnpos : 0 < CFSG.Open.pRank 2 D.Z := by omega
  have hDLodd : Odd (Nat.card DL) := by
    rw [hDLcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hnpos
  have hPY₁ : TK ≤ Astar :=
    le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hY₁P : Astar ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer hAstarNT
      (hAstarK.trans (Subgroup.le_normalizer (H := K)))
  have hY₂P : DL ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer hDLN' (hDLM.trans hMNK)
  have hY₂Y₁ : DL ≤ Subgroup.normalizer (Astar : Set G) :=
    le_normalizer_inf_of_le_normalizer (hDLM.trans hMNK)
      (hDLN'.trans (Subgroup.le_normalizer (H := Subgroup.normalizer (D.T : Set G))))
  have hSylA : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ Astar) Astar := by
    have hSylL : CFSG.ABGLocalTools.IsSylowOf 2 D.T (D.T ⊔ Astar) :=
      D.sylowG.of_le le_sup_left le_top
    have hKN : D.T ⊔ Astar ≤ Subgroup.normalizer (Astar : Set G) :=
      sup_le
        (le_normalizer_inf_of_le_normalizer (T_le_normalizer_of_normal hK hKn)
          ((Subgroup.le_normalizer (H := D.T)).trans
            (Subgroup.le_normalizer (H := Subgroup.normalizer (D.T : Set G)))))
        (Subgroup.le_normalizer (H := Astar))
    exact hSylL.inf_of_le_normalizer le_sup_right hKN
  have hinfAT : D.T ⊓ Astar = TK := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · refine le_inf inf_le_left ?_
      exact le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hodd₁ : Odd (TK.relIndex Astar) := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylA).2.2
    rw [hinfAT] at h
    exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have h11 : ∀ x ∈ Astar, ∀ y ∈ Astar, x * y * x⁻¹ * y⁻¹ ∈ TK := by
    intro x hx y hy
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hx.1
    have hxTK : x ∈ Subgroup.normalizer (TK : Set G) := hY₁P hx
    have hinn : UC6S846.rhoL K ⟨x, hxK⟩ ∈
        (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range :=
      ⟨QuotientGroup.mk ⟨x, hx.1⟩, (UC6S846.rhoL_inner K x hx.1).symm⟩
    have hyB : y ∈ CFSG.Quasithin.borelOf K D.T := ⟨hy.1, hY₁P hy⟩
    exact commutator_mem_inf_of_rhoL_inner hK hKn kL2BorelComm_holds hL2 hxK hxTK hinn hyB
  have h12 : ∀ x ∈ Astar, ∀ y ∈ DL, x * y * x⁻¹ * y⁻¹ ∈ TK :=
    fun x hx y hy => comm_A_cartan D Ch h4 h23 h208 h1930 c h3 hPush hK hKn
      hDLleB x hx y hy
  obtain ⟨F, hDLleF, hFleAD, hFodd, hFcomm, hFinfTK, hFsupA⟩ :=
    CFSG.GroupTheory.exists_abelian_hall_sup (P := TK) (Y₁ := Astar) (Y₂ := DL)
      hTK2 hPY₁ hY₁P hY₂P hY₂Y₁ hodd₁ hDLodd hDLcomm h11 h12
  have hFleN : F ≤ c.N := hFleAD.trans (sup_le hAstarN (hDLN'.trans hN4))
  have hFleM : F ≤ D.M := hFleAD.trans (sup_le hAstarM hDLM)
  have hFleNT : F ≤ Subgroup.normalizer (D.T : Set G) :=
    hFleAD.trans (sup_le hAstarNT hDLN')
  have hKinfDL : K ⊓ DL = ⊥ := by
    have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
      le_centralizer_Z_of_perfect D Ch h4 h1930 c (uc22p22a_le_of_isSubnormal hK.1) hK.2.1
    have hN1 := L_inf_centralizer_Z_eq D Ch h4 h23 h1930 c
    have hDLleL : DL ≤ c.L := hDLleB.trans (CFSG.Quasithin.F1.borelOf_le c.L D.T)
    have hKL : K ⊓ DL ≤ c.L := inf_le_right.trans hDLleL
    have hleTL : K ⊓ DL ≤ D.T ⊓ c.L := by
      rw [← hN1]
      intro x hx
      exact ⟨hKL hx, hKCZ hx.1⟩
    have hleTK : K ⊓ DL ≤ TK :=
      le_inf (hleTL.trans (inf_le_left : D.T ⊓ c.L ≤ D.T)) inf_le_left
    have hbot : TK ⊓ DL = ⊥ := by
      have hle : TK ⊓ DL ≤ TK ⊓ F :=
        le_inf inf_le_left (inf_le_right.trans hDLleF)
      exact le_bot_iff.mp (hFinfTK ▸ hle)
    exact le_bot_iff.mp (le_inf hleTK inf_le_right |>.trans hbot.le)
  have hFA : F ⊓ K = F ⊓ Astar := by
    apply le_antisymm
    · intro f hf
      have hfAD : f ∈ Astar ⊔ DL := hFleAD hf.1
      have hfmem : f ∈ (↑(Astar ⊔ DL) : Set G) := hfAD
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Astar DL hY₂Y₁] at hfmem
      obtain ⟨a, ha, d, hd, hfad⟩ := hfmem
      have haK : a ∈ K := hAstarK ha
      have hdK : d ∈ K := by
        have hd_eq : d = a⁻¹ * f := by rw [← hfad]; group
        rw [hd_eq]
        exact K.mul_mem (K.inv_mem haK) hf.2
      have hd1 : d = 1 := by
        have hmem : d ∈ K ⊓ DL := ⟨hdK, hd⟩
        rwa [hKinfDL, Subgroup.mem_bot] at hmem
      refine ⟨hf.1, ?_⟩
      have hf_eq : f = a := by
        rw [← hfad]
        simp [hd1]
      rw [hf_eq]
      exact ha
    · exact le_inf inf_le_left (inf_le_right.trans hAstarK)
  have hFKne : F ⊓ K ≠ ⊥ := by
    intro hbot
    have hAeq : Astar = TK := by
      rw [← hFsupA, inf_comm, ← hFA, hbot, sup_bot_eq]
    have hA0leTK : A₀ ≤ TK := by
      rw [← hAeq]
      exact hA₀
    have hA₀odd : Odd (Nat.card A₀) := by
      rw [hA₀card]
      exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    have hbot2 : TK ⊓ A₀ = ⊥ :=
      CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hTK2 hA₀odd
    have hA0bot : A₀ = ⊥ := by
      rw [inf_eq_right.mpr hA0leTK] at hbot2
      exact hbot2
    have hcard1 : Nat.card A₀ = 1 := by rw [hA0bot]; simp
    have hpow : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm2
    rw [hA₀card] at hcard1
    omega
  exact ⟨F, hDLleF, hFleAD, hFodd, hFcomm, hFinfTK, hFsupA, hFKne, hFleN, hFleM,
    hFleNT⟩

theorem exists_hall_D_centralizing_F (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {e m : ℕ}
    (hL2 : IsL2 (Bar2 K) (2 ^ e * m)) (hm2 : 2 ≤ m) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G))
    (hA₀card : Nat.card A₀ = 2 ^ m - 1) {DL F : Subgroup G}
    (hDLleB : DL ≤ CFSG.Quasithin.borelOf c.L D.T)
    (hDLcard : Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    (hFleAD : F ≤ (K ⊓ Subgroup.normalizer (D.T : Set G)) ⊔ DL)
    (hFodd : Odd (Nat.card F)) (hFcomm : IsMulCommutative F) (hFleM : F ≤ D.M)
    (hFleNT : F ≤ Subgroup.normalizer (D.T : Set G)) :
    ∃ D' : Subgroup G, D' ≤ CFSG.Quasithin.borelOf K D.T ∧
      (D.T ⊓ K) ⊔ D' = CFSG.Quasithin.borelOf K D.T ∧
      D' ≤ Subgroup.centralizer (F : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Astar : Subgroup G := K ⊓ Subgroup.normalizer (D.T : Set G)
  let TK : Subgroup G := D.T ⊓ K
  let BK : Subgroup G := CFSG.Quasithin.borelOf K D.T
  have hT2 : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG
  have hTK2 : IsPGroup 2 TK :=
    IsPGroup.to_inf_left (p := 2) (H := D.T) (K := K) hT2
  have hAstarK : Astar ≤ K := inf_le_left
  have hAstarNT : Astar ≤ Subgroup.normalizer (D.T : Set G) := inf_le_right
  have hAstarM : Astar ≤ D.M := hAstarK.trans (uc22p22a_le_of_isSubnormal hK.1)
  have hMNK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (uc22p22a_le_of_isSubnormal hK.1)).mp hKn
  have hDLN : DL ≤ Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    hDLleB.trans (normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c)
  have hDLN' : DL ≤ Subgroup.normalizer (D.T : Set G) := hDLN.trans inf_le_left
  have hDLM : DL ≤ D.M := hDLN.trans inf_le_right
  have hY₂Y₁ : DL ≤ Subgroup.normalizer (Astar : Set G) :=
    le_normalizer_inf_of_le_normalizer (hDLM.trans hMNK)
      (hDLN'.trans (Subgroup.le_normalizer (H := Subgroup.normalizer (D.T : Set G))))
  have hY₁P : Astar ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer hAstarNT
      (hAstarK.trans (Subgroup.le_normalizer (H := K)))
  have hY₂P : F ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer hFleNT (hFleM.trans hMNK)
  have hDLP : DL ≤ Subgroup.normalizer (TK : Set G) :=
    le_normalizer_inf_of_le_normalizer hDLN' (hDLM.trans hMNK)
  have hBKK : BK ≤ K := CFSG.Quasithin.F1.borelOf_le K D.T
  have hBKNTK : BK ≤ Subgroup.normalizer (TK : Set G) :=
    CFSG.Quasithin.F1.borelOf_le_normalizer K D.T
  have hBKY₂ : F ≤ Subgroup.normalizer (BK : Set G) :=
    le_normalizer_inf_of_le_normalizer (hFleM.trans hMNK)
      (hY₂P.trans (Subgroup.le_normalizer (H := Subgroup.normalizer (TK : Set G))))
  have hSylBK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ BK) BK := by
    have hSylL : CFSG.ABGLocalTools.IsSylowOf 2 D.T (D.T ⊔ BK) :=
      D.sylowG.of_le le_sup_left le_top
    have hKN : D.T ⊔ BK ≤ Subgroup.normalizer (BK : Set G) :=
      sup_le
        (le_normalizer_inf_of_le_normalizer (T_le_normalizer_of_normal hK hKn)
          ((T_le_normalizer_inf hK hKn).trans
            (Subgroup.le_normalizer (H := Subgroup.normalizer (TK : Set G)))))
        (Subgroup.le_normalizer (H := BK))
    exact hSylL.inf_of_le_normalizer le_sup_right hKN
  have hinfTBK : D.T ⊓ BK = TK := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans hBKK)
    · exact le_inf inf_le_left (le_inf inf_le_right (Subgroup.le_normalizer (H := TK)))
  have hodd₁ : Odd (TK.relIndex BK) := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylBK).2.2
    rw [hinfTBK] at h
    exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have h11 : ∀ x ∈ BK, ∀ y ∈ BK, x * y * x⁻¹ * y⁻¹ ∈ TK := by
    intro x hx y hy
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hx.1
    have hinn : UC6S846.rhoL K ⟨x, hxK⟩ ∈
        (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range :=
      ⟨QuotientGroup.mk ⟨x, hx.1⟩, (UC6S846.rhoL_inner K x hx.1).symm⟩
    exact commutator_mem_inf_of_rhoL_inner hK hKn kL2BorelComm_holds hL2 hxK hx.2 hinn hy
  have h12 : ∀ x ∈ BK, ∀ f ∈ F, x * f * x⁻¹ * f⁻¹ ∈ TK := by
    intro x hx f hf
    have hFM : f ∈ D.M := hFleM hf
    have hfmem : f ∈ (↑(Astar ⊔ DL) : Set G) := hFleAD hf
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Astar DL hY₂Y₁] at hfmem
    obtain ⟨a, ha, d, hd, hfad⟩ := hfmem
    have hxa : x * a * x⁻¹ * a⁻¹ ∈ TK := h11 x hx a (le_inf hAstarK hY₁P ha)
    have hdK : d ∈ Subgroup.normalizer (K : Set G) := hMNK (hDLM hd)
    have hdInner : UC6S846.rhoL K ⟨d, hdK⟩ ∈
        (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
      obtain ⟨y, hy⟩ :=
        rhoK_cartan_inner D Ch h4 h23 h208 h1930 c h3 hPush hK hKn hL2 hm2 hA₀ hA₀card
          hDLleB (by
            rw [hDLcard]
            exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)) hd hdK
      exact ⟨y, hy.symm⟩
    have hxd0 : d * x * d⁻¹ * x⁻¹ ∈ TK :=
      commutator_mem_inf_of_rhoL_inner hK hKn kL2BorelComm_holds hL2 hdK (hDLP hd)
        hdInner hx
    have hxd : x * d * x⁻¹ * d⁻¹ ∈ TK := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using TK.inv_mem hxd0
    have haconj : a * (x * d * x⁻¹ * d⁻¹) * a⁻¹ ∈ TK :=
      (Subgroup.mem_normalizer_iff.mp (hY₁P ha) _).mp hxd
    have hprod : x * a * x⁻¹ * a⁻¹ * (a * (x * d * x⁻¹ * d⁻¹) * a⁻¹) =
        x * f * x⁻¹ * f⁻¹ := by
      rw [← hfad]
      group
    rw [← hprod]
    exact TK.mul_mem hxa haconj
  obtain ⟨H1, hFH1, hH1le, hH1odd, hH1comm, hH1inf, hH1sup⟩ :=
    CFSG.GroupTheory.exists_abelian_hall_sup (P := TK) (Y₁ := BK) (Y₂ := F)
      hTK2 (le_inf inf_le_right Subgroup.le_normalizer) hBKNTK hY₂P hBKY₂ hodd₁ hFodd
      hFcomm h11 h12
  refine ⟨BK ⊓ H1, inf_le_left, hH1sup, ?_⟩
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfH1 : f ∈ H1 := hFH1 hf
  have hcomm := hH1comm.is_comm.comm (⟨d, hd.2⟩ : ↥H1) (⟨f, hfH1⟩ : ↥H1)
  exact (Subtype.ext_iff.mp hcomm).symm

end Ctx23L

@[expose] def CartanCentralizerStep (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ K ∈ calC D.M, (K.subgroupOf D.M).Normal →
      ∀ e m : ℕ, 2 ≤ m → IsL2 (Bar2 K) (2 ^ e * m) →
      ∀ A₀ : Subgroup G, A₀ ≤ K ⊓ Subgroup.normalizer (D.T : Set G) →
        Nat.card A₀ = 2 ^ m - 1 →
        ∀ DL F : Subgroup G,
          DL ≤ CFSG.Quasithin.borelOf c.L D.T →
          Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1 → IsMulCommutative DL →
          (D.T ⊓ c.L) ⊔ DL = CFSG.Quasithin.borelOf c.L D.T →
          DL ≤ F → F ≤ (K ⊓ Subgroup.normalizer (D.T : Set G)) ⊔ DL →
          Odd (Nat.card F) → IsMulCommutative F → F ⊓ K ≠ ⊥ → F ≤ c.N → F ≤ D.M →
          F ≤ Subgroup.normalizer (D.T : Set G) →
          Subgroup.centralizer (F : Set G) ≤ c.N

theorem d2337_of (D : Data G) (Ch : Choice2011 G) (hStep : CartanCentralizerStep D Ch)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (hPush : Push2329 D Ch) :
    D2337 D Ch := by
  classical
  intro h1930 c h3 K hK hKn e m hm2 hL2 A₀ hA₀ hA₀card
  obtain ⟨DL, hDLleB, hDLcard, hDLcomm, -, hDLsup⟩ :=
    c.exists_cartan_L D Ch h4 h23 h1930 kL2BorelCard_holds kL2BorelComm_holds
  obtain ⟨F, hDLleF, hFleAD, hFodd, hFcomm, -, -, hFKne, hFleN, hFleM, hFleNT⟩ :=
    Ctx23L.exists_F D Ch h4 h23 h208 h1930 c h3 hPush hK hKn hL2 hm2 hA₀ hA₀card hDLleB
      hDLcard hDLcomm
  obtain ⟨D', -, hD'sup, hD'cent⟩ :=
    Ctx23L.exists_hall_D_centralizing_F D Ch h4 h23 h208 h1930 c h3 hPush hK hKn hL2 hm2
      hA₀ hA₀card hDLleB hDLcard hFleAD hFodd hFcomm hFleM hFleNT
  have hCFleN : Subgroup.centralizer (F : Set G) ≤ c.N :=
    hStep h1930 c h3 K hK hKn e m hm2 hL2 A₀ hA₀ hA₀card DL F hDLleB hDLcard hDLcomm hDLsup
      hDLleF hFleAD hFodd hFcomm hFKne hFleN hFleM hFleNT
  rw [← hD'sup]
  exact sup_le
    (inf_le_left.trans ((le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)))
    (hD'cent.trans hCFleN)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
