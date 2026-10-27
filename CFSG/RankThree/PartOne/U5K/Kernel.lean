module

public import CFSG.RankThree.PartOne.U5K.Assembly
public import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)

section KerG

variable {G : Type} [Group G] {f : ℕ} (I : Subgroup G)
  (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)

@[expose] noncomputable def kerG : Subgroup G :=
  (U5Act I e).ker.map (Subgroup.normalizer (I : Set G)).subtype

variable {I e}

theorem mem_kerG {x : G} :
    x ∈ kerG I e ↔ ∃ hx : x ∈ Subgroup.normalizer (I : Set G), U5Act I e ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem card_kerG : Nat.card (kerG I e) = Nat.card (U5Act I e).ker :=
  Subgroup.card_map_of_injective (Subgroup.normalizer (I : Set G)).subtype_injective

theorem conj_mem_kerG {n c : G} (hn : n ∈ Subgroup.normalizer (I : Set G)) (hc : c ∈ kerG I e) :
    n * c * n⁻¹ ∈ kerG I e := by
  obtain ⟨hcN, hc1⟩ := mem_kerG.1 hc
  have hmem : n * c * n⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normalizer (I : Set G)).mul_mem
      ((Subgroup.normalizer (I : Set G)).mul_mem hn hcN)
      ((Subgroup.normalizer (I : Set G)).inv_mem hn)
  refine mem_kerG.2 ⟨hmem, ?_⟩
  rw [map_conj_mk hn hcN hmem, hc1]
  simp

theorem le_normalizer_kerG {E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (I : Set G)) :
    E ≤ Subgroup.normalizer (kerG I e : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact conj_mem_kerG (hEN hn) hc
  · intro hc
    have := conj_mem_kerG (hEN (E.inv_mem hn)) hc
    simpa [mul_assoc] using this

end KerG

theorem ker_not_dvd_p_of_max {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {I E A : Subgroup G} {f : ℕ} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hEel : IsElementaryAbelian p E) (hEN : E ≤ Subgroup.normalizer (I : Set G)) (hAE : A ≤ E)
    (hEC : E ≤ Subgroup.centralizer (A : Set G))
    (hmax : ∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (A : Set G) →
      E ≤ F → F = E)
    (hfaith : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (I : Set G)), x ∈ E →
      U5Act I e ⟨x, hx⟩ = 1 → x = 1) :
    ¬ p ∣ Nat.card (U5Act I e).ker := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  set Cg : Subgroup G := kerG I e with hCg
  have hCgcard : Nat.card Cg = Nat.card (U5Act I e).ker := card_kerG
  have hdvdCg : p ∣ Nat.card Cg := hCgcard ▸ hdvd
  have hCgmem : ∀ x, x ∈ Cg ↔ ∃ hx : x ∈ Subgroup.normalizer (I : Set G),
      U5Act I e ⟨x, hx⟩ = 1 := fun x => mem_kerG
  have hEnorm : E ≤ Subgroup.normalizer (Cg : Set G) := le_normalizer_kerG hEN
  have hKN : Cg ⊔ E ≤ Subgroup.normalizer (Cg : Set G) :=
    sup_le Subgroup.le_normalizer hEnorm
  have : IsElementaryAbelian p ↥E := hEel
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p ↥E
  obtain ⟨P, hPsyl, hEP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (K := Cg ⊔ E) le_sup_right hEp
  have hPabg : CFSG.ABGLocalTools.IsSylowOf p P (Cg ⊔ E) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hPc : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ Cg) Cg :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPabg le_sup_left hKN
  have hPccard : Nat.card ↥(P ⊓ Cg) = p ^ (Nat.card Cg).factorization p := hPc.card_eq
  have hPcne : P ⊓ Cg ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(P ⊓ Cg) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hPccard] at h1
    have hpos : 0 < (Nat.card Cg).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hdvdCg
    have := Nat.one_lt_pow hpos.ne' hp.one_lt
    omega
  have hPp : IsPGroup p P := hPsyl.2.1
  have : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hPcP : P ⊓ Cg ≤ P := inf_le_left
  have hPnorm : P ≤ Subgroup.normalizer ((P ⊓ Cg : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hxn := Subgroup.mem_normalizer_iff.1 (hKN (hPsyl.1 hx)) g
    constructor
    · rintro ⟨hgP, hgC⟩
      exact ⟨P.mul_mem (P.mul_mem hx hgP) (P.inv_mem hx), hxn.1 hgC⟩
    · rintro ⟨hgP, hgC⟩
      refine ⟨?_, hxn.2 hgC⟩
      have := P.mul_mem (P.mul_mem (P.inv_mem hx) hgP) hx
      simpa [mul_assoc] using this
  have hnormsub : ((P ⊓ Cg).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPcP).2 hPnorm
  have hne : (P ⊓ Cg).subgroupOf P ≠ ⊥ := by
    intro h
    apply hPcne
    have := Subgroup.map_subgroupOf_eq_of_le hPcP
    rw [h, Subgroup.map_bot] at this
    exact this.symm
  have hH := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set H : Subgroup ↥P := (P ⊓ Cg).subgroupOf P ⊓ Subgroup.center ↥P with hHdef
  have hHp : IsPGroup p H := hPp.to_subgroup H
  have hHcard : p ∣ Nat.card H := by
    rcases hHp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.1 h1) hH
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hHcard
  set y : G := (((x : ↥H) : ↥P) : G) with hy
  have hyPc : y ∈ P ⊓ Cg := x.2.1
  have hyc : ∀ z ∈ P, z * y = y * z := fun z hz =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 x.2.2 ⟨z, hz⟩)
  have hyp : y ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa [hy] using congrArg (fun z : ↥H => (((z : ↥P) : G))) this
  have hy1 : y ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hyE : ∀ k ∈ E, k * y = y * k := fun k hk => hyc k (hEP hk)
  have hcomm : ∀ k ∈ E, ∀ l ∈ Subgroup.zpowers y, k * l = l * k := by
    intro k hk l hl
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact ((show Commute k y from hyE k hk).zpow_right m).eq
  have hZel : IsElementaryAbelian p ↥(Subgroup.zpowers y) :=
    Torsion37.isElementaryAbelian_of_forall
      (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow_self y m n).eq)
      (fun a ha => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow])
  have hFel : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers y) :=
    Torsion37.isElementaryAbelian_sup_of_commute hEel hZel hcomm
  have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hyE a (hAE ha)
  have hFC : E ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer (A : Set G) :=
    sup_le hEC (Subgroup.zpowers_le.2 hyA)
  have hFE := hmax _ hFel hFC le_sup_left
  have hyE' : y ∈ E := by
    have : y ∈ E ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rwa [hFE] at this
  obtain ⟨hyN, hy1'⟩ := (hCgmem y).1 hyPc.2
  exact hy1 (hfaith y hyN hyE' hy1')

end CFSG.RankThree.PartOne.U5K
