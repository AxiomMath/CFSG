module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup

private lemma a210el_exists_pow_modEq_one {b : ℕ} (hb : ¬ 3 ∣ b) :
    ∃ e : ℕ, b ∣ e ∧ e ≡ 1 [MOD 3] := by
  have hcop : Nat.Coprime b 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hb).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
  exact ⟨b * m, dvd_mul_right b m, by simpa [Nat.ModEq] using hm⟩

private lemma a210el_orderOf_apply {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type}
    [∀ i, Group (B i)] {Y : Type} [Group Y] (θ : Y →* ∀ i, B i) (y : ι → Y)
    (hord : ∀ j, orderOf (θ (y j)) = 3) (hsupp : ∀ j i, i ≠ j → θ (y j) i = 1)
    (j : ι) : orderOf (θ (y j) j) = 3 := by
  have hfun : θ (y j) = Pi.mulSingle j (θ (y j) j) := by
    funext i
    by_cases hi : i = j
    · subst hi; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, hsupp j i hi]
  calc orderOf (θ (y j) j) = orderOf (Pi.mulSingle j (θ (y j) j)) :=
        (orderOf_piMulSingle j (θ (y j) j)).symm
    _ = orderOf (θ (y j)) := by rw [← hfun]
    _ = 3 := hord j

private lemma a210el_mulSingle_eq_zpow {ι : Type} [DecidableEq ι] {B : ι → Type}
    [∀ i, Group (B i)] {Y : Type} [Group Y] (θ : Y →* ∀ i, B i) (y : ι → Y)
    (hsupp : ∀ j i, i ≠ j → θ (y j) i = 1) {j : ι} {p : ∀ i, B i} {m : ℤ}
    (hm : p j = (θ (y j) j) ^ m) :
    Pi.mulSingle j (p j) = (θ (y j)) ^ m := by
  ext i
  by_cases hi : i = j
  · subst hi
    rw [Pi.mulSingle_eq_same, hm]
    rfl
  · rw [Pi.mulSingle_eq_of_ne hi (p j)]
    show (1 : B i) = (θ (y j) i) ^ m
    rw [hsupp j i hi, one_zpow]

private noncomputable def a210el_piEquiv {ι : Type*} (B : ι → Type) [∀ i, Group (B i)]
    (S : ∀ i, Subgroup (B i)) :
    (∀ i, ↥(S i)) ≃* ↥(Subgroup.pi Set.univ S) where
  toFun x := ⟨fun i => (x i : B i), (Subgroup.mem_pi Set.univ).mpr fun i _ => (x i).2⟩
  invFun x := fun i => ⟨x.1 i, (Subgroup.mem_pi Set.univ).mp x.2 i (Set.mem_univ i)⟩
  left_inv x := by funext i; rfl
  right_inv x := by ext i; rfl
  map_mul' x y := by ext i; rfl

theorem exists_threeElem_lift {Y S : Type} [Group Y] [Finite Y] [Group S] (θ : Y →* S)
    {R : Subgroup Y} {x : S} (hx : x ∈ R.map θ) (hx3 : orderOf x = 3) :
    ∃ y ∈ R, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ θ y = x := by
  obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hx
  have hn0 : orderOf r ≠ 0 :=
    (Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard r) Nat.card_pos).ne'
  obtain ⟨a, b, hb, hnab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  obtain ⟨e, hbe, he⟩ := a210el_exists_pow_modEq_one hb
  refine ⟨r ^ e, R.pow_mem hrR e, ⟨a, ?_⟩, ?_⟩
  · obtain ⟨m, rfl⟩ := hbe
    have hordr : r ^ (b * m * 3 ^ a) = 1 := by
      rw [show b * m * 3 ^ a = (3 ^ a * b) * m by ring, pow_mul, ← hnab,
        pow_orderOf_eq_one, one_pow]
    rwa [← pow_mul]
  · rw [map_pow]
    have hxfin : IsOfFinOrder (θ r) := by
      rw [← orderOf_ne_zero_iff, hx3]
      norm_num
    have heq : (θ r) ^ e = (θ r) ^ 1 := by
      rw [hxfin.pow_eq_pow_iff_modEq, hx3]
      exact he
    rw [heq, pow_one]

theorem pRank_ge_of_abelian_surj {E V : Type} [CommGroup E] [Finite E] [CommGroup V] [Finite V]
    (φ : E →* V) (hφ : Function.Surjective φ) (hV : ∀ v : V, v ^ 3 = 1) {n : ℕ}
    (hn : 3 ^ n ≤ Nat.card V) : n ≤ CFSG.pRank 3 E := by
  let c : E →* E := powMonoidHom 3
  have hrange_le : c.range ≤ φ.ker := by
    rintro _ ⟨e, rfl⟩
    exact MonoidHom.mem_ker.mpr (by simp only [c, powMonoidHom_apply, map_pow, hV])
  have hcardE : Nat.card c.ker * Nat.card c.range = Nat.card E :=
    Subgroup.card_ker_mul_card_range c
  have hcardφ : Nat.card φ.ker * Nat.card V = Nat.card E :=
    Subgroup.card_ker_mul_card_of_surjective hφ
  have hVle : Nat.card V ≤ Nat.card c.ker := by
    have h1 : Nat.card V * Nat.card φ.ker ≤ Nat.card c.ker * Nat.card c.range := by
      refine le_of_eq ?_
      rw [mul_comm (Nat.card V) (Nat.card φ.ker), hcardφ, hcardE]
    have h2 : Nat.card c.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrange_le
    have h3 : Nat.card c.ker * Nat.card c.range ≤ Nat.card c.ker * Nat.card φ.ker :=
      Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right (h1.trans h3) Nat.card_pos
  have h3n : 3 ^ n ≤ Nat.card c.ker := hn.trans hVle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIsP : IsPGroup 3 ↥c.ker := fun a => ⟨1, by
    have ha : (a : E) ^ 3 = 1 := by
      simpa [c] using MonoidHom.mem_ker.mp a.2
    have hsub : a ^ 3 = 1 := Subtype.ext ha
    simpa using hsub⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hIsP
  have hnk : n ≤ k := by
    rw [hk] at h3n
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3n
  have hkrank : k ≤ CFSG.pRank 3 E := by
    have hk' : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup E) :=
      CFSG.SectionRank.le_pRank_of_injective (p := 3) (A := ↥c.ker) (G := E)
        (by norm_num) (fun a b => mul_comm' a b)
        (fun a => Subtype.ext (by simpa [c] using MonoidHom.mem_ker.mp a.2)) hk
        c.ker.subtype c.ker.subtype_injective le_top
    rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 E] at hk'
  exact hnk.trans hkrank

theorem card_le_pRank_of_commuting {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type}
    [∀ i, Group (B i)] {Y : Type} [Group Y] [Finite Y] (θ : Y →* ∀ i, B i) (y : ι → Y)
    (hcomm : ∀ j l, y j * y l = y l * y j) (hord : ∀ j, orderOf (θ (y j)) = 3)
    (hsupp : ∀ j i, i ≠ j → θ (y j) i = 1) : Fintype.card ι ≤ CFSG.pRank 3 Y := by
  classical
  let E : Subgroup Y := Subgroup.closure (Set.range y)
  let : IsMulCommutative ↥E :=
    Subgroup.isMulCommutative_closure (k := Set.range y) (by
      rintro a ⟨j, rfl⟩ b ⟨l, rfl⟩ _
      exact hcomm j l)
  let : CommGroup ↥E := IsMulCommutative.instCommGroup
  let V : Subgroup (∀ i, B i) := E.map θ
  have hVeq : V = Subgroup.closure (Set.range (fun j => θ (y j))) := by
    simp only [V, E, MonoidHom.map_closure, Set.range_comp']
  let : IsMulCommutative ↥V := Subgroup.map_isMulCommutative (H := E) θ
  let : CommGroup ↥V := IsMulCommutative.instCommGroup
  have hWexp : ∀ x ∈ Subgroup.closure (Set.range (fun j => θ (y j))), x ^ 3 = 1 := by
    intro x hx
    let : IsMulCommutative ↥(Subgroup.closure (Set.range (fun j => θ (y j)))) :=
      Subgroup.isMulCommutative_closure (k := Set.range (fun j => θ (y j))) (by
        rintro a ⟨j, rfl⟩ b ⟨l, rfl⟩ _
        show θ (y j) * θ (y l) = θ (y l) * θ (y j)
        rw [← map_mul, ← map_mul, hcomm j l])
    let : CommGroup ↥(Subgroup.closure (Set.range (fun j => θ (y j)))) :=
      IsMulCommutative.instCommGroup
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨j, rfl⟩
      rw [← hord j]
      exact pow_orderOf_eq_one _
    · simp
    · intro p q hp hq ihp ihq
      have hpq : p * q = q * p :=
        congrArg Subtype.val
          (mul_comm' (⟨p, hp⟩ : ↥(Subgroup.closure (Set.range (fun j => θ (y j)))))
            (⟨q, hq⟩ : ↥(Subgroup.closure (Set.range (fun j => θ (y j))))))
      rw [show (p * q) ^ 3 = p ^ 3 * q ^ 3 from (Commute.mul_pow hpq) 3, ihp, ihq, mul_one]
    · intro p hp ihp
      rw [inv_pow, ihp, inv_one]
  have hVexp : ∀ v : ↥V, v ^ 3 = 1 := by
    intro v
    have hv : (v : ∀ i, B i) ∈ Subgroup.closure (Set.range (fun j => θ (y j))) := by
      rw [← hVeq]; exact v.2
    exact Subtype.ext (hWexp (v : ∀ i, B i) hv)
  let S : ∀ j, Subgroup (B j) := fun j => Subgroup.zpowers (θ (y j) j)
  let P : Subgroup (∀ i, B i) := Subgroup.pi Set.univ S
  let φEV : ↥E →* ↥V := (θ.comp E.subtype).codRestrict V (fun e => by
    dsimp only [V]
    exact Subgroup.mem_map.mpr ⟨e.1, e.2, rfl⟩)
  have hφEV : Function.Surjective φEV := by
    rintro ⟨v, hv⟩
    dsimp only [V] at hv
    rw [Subgroup.mem_map] at hv
    obtain ⟨e, heE, hev⟩ := hv
    exact ⟨⟨e, heE⟩, Subtype.ext hev⟩
  have : Finite ↥V := Finite.of_surjective φEV hφEV
  have hPV : P ≤ V := by
    intro p hp
    rw [← Finset.noncommProd_mulSingle p]
    refine Subgroup.noncommProd_mem V _ (fun c _ => ?_)
    have hpc : p c ∈ S c := (Subgroup.mem_pi Set.univ).mp hp c (Set.mem_univ c)
    rw [Subgroup.mem_zpowers_iff] at hpc
    obtain ⟨m, hm⟩ := hpc
    rw [a210el_mulSingle_eq_zpow θ y hsupp hm.symm]
    exact V.zpow_mem (Subgroup.mem_map.mpr ⟨y c, Subgroup.subset_closure ⟨c, rfl⟩, rfl⟩) m
  have hcardP : Nat.card ↥P = 3 ^ Fintype.card ι := by
    have h1 : Nat.card ↥P = Nat.card (∀ j, ↥(S j)) :=
      Nat.card_congr (a210el_piEquiv B S).symm.toEquiv
    rw [h1, Nat.card_pi]
    calc ∏ j, Nat.card ↥(S j) = ∏ _j : ι, (3 : ℕ) := by
          refine Finset.prod_congr rfl (fun j _ => ?_)
          simp only [S, Nat.card_zpowers]
          exact a210el_orderOf_apply θ y hord hsupp j
      _ = 3 ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  have hcardPV : 3 ^ Fintype.card ι ≤ Nat.card ↥V := by
    rw [← hcardP]
    exact Subgroup.card_le_of_le hPV
  have hp := pRank_ge_of_abelian_surj φEV hφEV hVexp hcardPV
  refine hp.trans ?_
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥E,
    CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y]
  exact CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) E.subtype
    E.subtype_injective

end CFSG.LocalAnalysis.WeakClosure81.Asch210
