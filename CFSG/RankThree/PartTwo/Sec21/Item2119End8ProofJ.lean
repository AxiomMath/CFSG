module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofLoc
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2128

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

@[expose] def Item2129S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∃ S : Subgroup G,
            S ≤ y2128Of (Lf e) (F e) (q2127Of A d F) ∧
            y2128Of (Lf e) (F e) (q2127Of A d F) ≤ Subgroup.normalizer (S : Set G) ∧
            IsElemAbelian 3 S ∧ Nat.card S = 81 ∧ F e ⊓ Lf e ≤ S

namespace Item2119End8Proof

section General

variable {G : Type*} [Group G]

theorem thompsonSubgroup_eq_of {P S : Subgroup G} (hSP : S ≤ P) (hS : IsMulCommutative S)
    (hmax : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card S)
    (huniq : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B = Nat.card S → B = S) :
    CFSG.Open.thompsonSubgroup P = S := by
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hBP => iSup_le fun hB => iSup_le fun hBm => ?_
    exact (huniq B hBP hB (le_antisymm (hmax B hBP hB) (hBm S hSP hS))).le
  · exact le_iSup_of_le S (le_iSup_of_le hSP (le_iSup_of_le hS (le_iSup_of_le hmax le_rfl)))

theorem thompsonSubgroup_le (P : Subgroup G) : CFSG.Open.thompsonSubgroup P ≤ P :=
  CFSG.ambientMaxCardThompson_le P

theorem comm_sup {H K : Subgroup G} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  have h1 : H ⊔ K ≤ Subgroup.centralizer (H : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hH y hy x hx)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hHK y hy x hx)
  have h2 : H ⊔ K ≤ Subgroup.centralizer (K : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hHK x hx y hy).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hK y hy x hx)
  have h3 : H ⊔ K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (h3 hy) x hx

theorem comm_zpowers {x : G} {K : Subgroup G} (hx : ∀ y ∈ K, x * y = y * x) :
    ∀ z ∈ Subgroup.zpowers x, ∀ y ∈ K, z * y = y * z := by
  intro z hz y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (Commute.zpow_left (show Commute x y from hx y hy) i).eq

theorem comm_zpowers_self (x : G) :
    ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y :=
  comm_zpowers fun z hz => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (Commute.refl x) i).eq

theorem le_centralizer_of_mem {X : Subgroup G} (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {b : G}
    (hb : b ∈ X) : X ≤ Subgroup.centralizer ({b} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hX y hy b hb)

theorem isPGroup_of_pow {A : Subgroup G} (hA : ∀ x ∈ A, x ^ 3 = 1) : IsPGroup 3 A :=
  fun g => ⟨1, Subtype.ext (by simpa using hA _ g.2)⟩

end General

section Bound

variable {G : Type} [Group G] [Finite G]

theorem card_le_27_of_le_centralizer {A : Subgroup G} {d : G} {F : G → Subgroup G}
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hA27 : Nat.card A = 27) {b : G} (hb : b ∈ A)
    (hbd : b ∉ Subgroup.zpowers d) {X : Subgroup G} (hX3 : IsPGroup 3 X)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXb : X ≤ Subgroup.centralizer ({b} : Set G)) :
    Nat.card X ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl := h27 b hb hbd
  have h81 : Nat.card (A ⊔ F b : Subgroup G) = 81 := (hQ.2.2.2.2 b hb hbd).1
  have hle81 : Nat.card X ≤ 81 := by
    have h := Item2119End6Proof.card_le_three_pow_of_isPGroup hXb hX3
    rwa [← hsyl.card_eq, h81] at h
  by_contra hgt
  push Not at hgt
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hX3
  have hn4 : n = 4 := by
    have h1 : 3 ^ 3 < 3 ^ n := by rw [← hn]; omega
    have h2 : 3 ^ n ≤ 3 ^ 4 := by rw [← hn]; omega
    have h1' := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
    have h2' := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    omega
  have hX81 : Nat.card X = 81 := by rw [hn, hn4]; norm_num
  have hXsyl : IsSylowOf 3 X (Subgroup.centralizer ({b} : Set G)) :=
    isSylowOf_of_card hXb (by rw [hX81, ← h81, hsyl.card_eq])
  obtain ⟨k, -, hk⟩ := hsyl.exists_mem_conj hXsyl
  have hconj : ∀ y ∈ A ⊔ F b, k * y * k⁻¹ ∈ X := fun y hy =>
    (hk _).mpr (by rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]; exact hy)
  have hcomm : ∀ y ∈ A ⊔ F b, ∀ z ∈ A ⊔ F b, y * z = z * y := by
    intro y hy z hz
    have h := hXc _ (hconj y hy) _ (hconj z hz)
    have h' : k * (y * z) * k⁻¹ = k * (z * y) * k⁻¹ := by
      calc k * (y * z) * k⁻¹ = (k * y * k⁻¹) * (k * z * k⁻¹) := by group
        _ = (k * z * k⁻¹) * (k * y * k⁻¹) := h
        _ = k * (z * y) * k⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hFQ : F b ≤ q2127Of A d F :=
    le_sup_right.trans (le_iSup₂_of_le
      (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e) b ⟨hb, hbd⟩
      le_rfl)
  have hFA : F b ≤ A := by
    rw [← hQ.2.1]
    exact le_inf hFQ fun f hf => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hcomm x (Subgroup.mem_sup_left hx) f (Subgroup.mem_sup_right hf)
  rw [sup_eq_left.mpr hFA, hA27] at h81
  norm_num at h81

theorem mem_F {A : Subgroup G} {d : G} {Lf F : G → Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27)
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) : e ∈ F e := by
  obtain ⟨hFe, hF27, -, hAN, -⟩ := hF e he hed
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFC : F e ≤ Subgroup.centralizer ({e} : Set G) := le_sup_right.trans (h27 e he hed).le
  have hA3 : IsPGroup 3 A := isPGroup_of_pow hAe.2
  have hZ3 : IsPGroup 3 (Subgroup.zpowers e ⊔ F e : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (hA3.to_le (Subgroup.zpowers_le.mpr he))
      (isPGroup_of_pow hFe.2) (Subgroup.zpowers_le.mpr (hAN he))
  have hZc := comm_sup (comm_zpowers_self e) hFc
    (comm_zpowers fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hFC hy)).symm)
  have hZC : Subgroup.zpowers e ⊔ F e ≤ Subgroup.centralizer ({e} : Set G) :=
    le_centralizer_of_mem hZc (Subgroup.mem_sup_left (Subgroup.mem_zpowers e))
  have hcard := card_le_27_of_le_centralizer h27 hQ hA27 he hed hZ3 hZc hZC
  have heq : F e = Subgroup.zpowers e ⊔ F e :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hF27]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)

theorem le_F_of_le_centralizer {A : Subgroup G} {d : G} {Lf F : G → Subgroup G}
    (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) {X : Subgroup G} (hX3 : IsPGroup 3 X)
    (hXC : X ≤ Subgroup.centralizer (F e : Set G)) : X ≤ F e := by
  obtain ⟨hFe, hF27, -, -, -⟩ := hF e he hed
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have heF := mem_F hAe hA27 h27 hQ hF he hed
  have hFC : F e ≤ Subgroup.centralizer ({e} : Set G) := le_sup_right.trans (h27 e he hed).le
  intro x hx
  have hxc : ∀ y ∈ F e, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hXC hx) y hy).symm
  have hZ3 : IsPGroup 3 (Subgroup.zpowers x ⊔ F e : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (hX3.to_le (Subgroup.zpowers_le.mpr hx))
      (isPGroup_of_pow hFe.2)
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ (hXC hx)))
  have hZc := comm_sup (comm_zpowers_self x) hFc (comm_zpowers hxc)
  have hZC : Subgroup.zpowers x ⊔ F e ≤ Subgroup.centralizer ({e} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hxc e heF)))
      hFC
  have hcard := card_le_27_of_le_centralizer h27 hQ hA27 he hed hZ3 hZc hZC
  have heq : F e = Subgroup.zpowers x ⊔ F e :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hF27]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem card_le_729 {A : Subgroup G} {d : G} {Lf F : G → Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27)
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) {R : Subgroup G} (hR3 : IsPGroup 3 R)
    (hRY : R ≤ y2128Of (Lf e) (F e) (q2127Of A d F)) : Nat.card R ≤ 729 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYN, -, h216⟩ := h28 e he hed
  have hF27 : Nat.card (F e) = 27 := (hF e he hed).2.1
  have hRN : R ≤ Subgroup.normalizer (F e : Set G) := hRY.trans hYN
  have hmul := Item2119End3Proof.card_autIn_mul_card_inf hRN
  have hC : Nat.card (R ⊓ Subgroup.centralizer (F e : Set G) : Subgroup G) ≤ 27 := by
    rw [← hF27]
    exact Subgroup.card_le_of_le
      (le_F_of_le_centralizer hAe hA27 h27 hQ hF he hed hR3.to_inf_left inf_le_right)
  have hAut : Nat.card (Sec4.autIn R (F e)) ≤ 27 := by
    have hdvd : Nat.card (Sec4.autIn R (F e)) ∣ 216 := by
      rw [← h216]
      exact Subgroup.card_dvd_of_le (Item2119End3Proof.autIn_le_of_le (inf_le_left.trans hRY))
    have hp : IsPGroup 3 (Sec4.autIn R (F e)) := by
      unfold Sec4.autIn
      exact (hR3.to_inf_left.comap_subtype).map _
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    rw [hn] at hdvd ⊢
    have h27' : 3 ^ n ∣ 27 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 8))
        (by norm_num; exact hdvd)
    exact Nat.le_of_dvd (by norm_num) h27'
  calc Nat.card R
      = Nat.card (Sec4.autIn R (F e)) *
          Nat.card (R ⊓ Subgroup.centralizer (F e : Set G) : Subgroup G) := hmul.symm
    _ ≤ 27 * 27 := Nat.mul_le_mul hAut hC
    _ = 729 := by norm_num

end Bound

section Abelian

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_le_nine {A S : Subgroup G} (hA3 : IsPGroup 3 A)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS3 : IsPGroup 3 S)
    (hrank : ∀ b ∈ A, b ∉ S → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27)
    {a' : G} (ha' : a' ∈ A) (ha'S : a' ∉ S) :
    Nat.card (S ⊓ Subgroup.centralizer ({a'} : Set G) : Subgroup G) ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := S ⊓ Subgroup.centralizer ({a'} : Set G) with hCdef
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hSc x hx.1 y hy.1
  have ha'c : ∀ y ∈ C, a' * y = y * a' := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  have hC3 : IsPGroup 3 C := hS3.to_le inf_le_left
  have hZ3 : IsPGroup 3 (Subgroup.zpowers a' ⊔ C : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (hA3.to_le (Subgroup.zpowers_le.mpr ha')) hC3
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (ha'c y hy).symm)))
  have hZc := comm_sup (comm_zpowers_self a') hCc (comm_zpowers ha'c)
  have hZC := le_centralizer_of_mem hZc (Subgroup.mem_sup_left (Subgroup.mem_zpowers a'))
  have h27 := hrank a' ha' ha'S _ hZ3 hZc hZC
  have hlt : C < Subgroup.zpowers a' ⊔ C := by
    refine lt_of_le_of_ne le_sup_right fun h => ha'S ?_
    have : a' ∈ C := by rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a')
    exact this.1
  have hClt := Subgroup.card_lt_of_lt hlt
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hC3
  rw [hm] at hClt ⊢
  have hm2 : m < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
    (show 3 ^ m < 3 ^ 3 by omega)
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 9 := by norm_num

theorem eq_of_le_sup {A S B : Subgroup G} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA3 : IsPGroup 3 A) (hA27 : Nat.card A = 27) (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS3 : IsPGroup 3 S) (hS81 : Nat.card S = 81)
    (hAN : A ≤ Subgroup.normalizer (S : Set G)) (hAS : Nat.card (A ⊓ S : Subgroup G) = 3)
    (hrank : ∀ b ∈ A, b ∉ S → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27)
    (hBle : B ≤ A ⊔ S) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB81 : 81 ≤ Nat.card B) :
    B = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card (A ⊔ S : Subgroup G) = 729 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAN
    rw [sup_comm, inf_comm, hAS, hS81, hA27] at h
    omega
  have hPN : A ⊔ S ≤ Subgroup.normalizer (S : Set G) := sup_le hAN Subgroup.le_normalizer
  have hBN : B ≤ Subgroup.normalizer (S : Set G) := hBle.trans hPN
  by_cases hBS : B ≤ S
  · exact Subgroup.eq_of_le_of_card_ge hBS (by rw [hS81]; exact hB81)
  obtain ⟨x, hxB, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hBS
  have hxP : x ∈ ((A ⊔ S : Subgroup G) : Set G) := hBle hxB
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A S hAN] at hxP
  obtain ⟨a', ha', s, hs, rfl⟩ := Set.mem_mul.mp hxP
  have ha'S : a' ∉ S := fun h => hxS (S.mul_mem h hs)
  have hBS9 : Nat.card (S ⊓ B : Subgroup G) ≤ 9 := by
    refine le_trans (Subgroup.card_le_of_le ?_)
      (card_inf_centralizer_le_nine hA3 hSc hS3 hrank ha' ha'S)
    intro y hy
    refine ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : y * (a' * s) = (a' * s) * y := hBc y hy.2 _ hxB
    have h2 : y * s = s * y := hSc y hy.1 s hs
    have h3 : y * a' * s = a' * y * s := by
      calc y * a' * s = y * (a' * s) := by group
        _ = a' * s * y := h1
        _ = a' * (s * y) := by group
        _ = a' * (y * s) := by rw [h2]
        _ = a' * y * s := by group
    exact mul_right_cancel h3
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBN
  have hSBle : S ⊔ B ≤ A ⊔ S := sup_le le_sup_right hBle
  have hSB729 : Nat.card (S ⊔ B : Subgroup G) ≤ 729 := by
    rw [← hP]
    exact Subgroup.card_le_of_le hSBle
  rw [hS81] at hm
  have hB : Nat.card B = 81 := by
    have : 81 * Nat.card B ≤ 729 * 9 := by
      rw [← hm]
      exact Nat.mul_le_mul hSB729 hBS9
    omega
  rw [hB] at hm
  have hSB9 : Nat.card (S ⊓ B : Subgroup G) = 9 := by
    by_contra hne
    have h8 : Nat.card (S ⊓ B : Subgroup G) ≤ 8 := by omega
    have : Nat.card (S ⊔ B : Subgroup G) * Nat.card (S ⊓ B : Subgroup G) ≤ 729 * 8 :=
      Nat.mul_le_mul hSB729 h8
    omega
  rw [hSB9] at hm
  have hSBeq : S ⊔ B = A ⊔ S :=
    Subgroup.eq_of_le_of_card_ge hSBle (by rw [hP]; omega)
  have hcent : A ≤ Subgroup.centralizer ((S ⊓ B : Subgroup G) : Set G) := by
    have h : S ⊔ B ≤ Subgroup.centralizer ((S ⊓ B : Subgroup G) : Set G) :=
      sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => hSc z hz.1 y hy)
        (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => hBc z hz.2 y hy)
    rw [hSBeq] at h
    exact le_sup_left.trans h
  have hcent' : S ⊓ B ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer_iff.mp hcent
  obtain ⟨b, hbA, hbS⟩ : ∃ b ∈ A, b ∉ S := by
    by_contra hall
    push Not at hall
    have : A ⊓ S = A := inf_eq_left.mpr fun y hy => hall y hy
    rw [this, hA27] at hAS
    norm_num at hAS
  have hIc : ∀ x ∈ S ⊓ B, ∀ y ∈ S ⊓ B, x * y = y * x := fun x hx y hy => hSc x hx.1 y hy.1
  have hXc := comm_sup hAc hIc fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm
  have hX3 : IsPGroup 3 (A ⊔ (S ⊓ B) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hA3 (hS3.to_le inf_le_left)
      (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have hXC := le_centralizer_of_mem hXc (Subgroup.mem_sup_left hbA)
  have hX27 := hrank b hbA hbS _ hX3 hXc hXC
  have hm2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hcent'.trans (Subgroup.centralizer_le_normalizer _))
  rw [hA27, hSB9] at hm2
  have hinf : Nat.card (A ⊓ (S ⊓ B) : Subgroup G) ≤ 3 := by
    rw [← hAS]
    exact Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_left)
  have : 27 * 9 ≤ 27 * 3 := by
    rw [← hm2]
    exact Nat.mul_le_mul hX27 hinf
  omega

end Abelian

end Item2119End8Proof

open Item2119End8Proof

theorem item2129Loc_of_s (hS : Item2129S) : Item2129Loc := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 e he hed P hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSY, hYS, hSe, hS81, hFLS⟩ :=
    hS G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 e he hed
  set Q := q2127Of A d F with hQdef
  set Y := y2128Of (Lf e) (F e) Q with hYdef
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : IsPGroup 3 A := isPGroup_of_pow hAe.2
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hS3 : IsPGroup 3 S := isPGroup_of_pow hSe.2
  have hAFQ : A ⊔ F e ≤ Q :=
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      e ⟨he, hed⟩ le_rfl
  have hAY : A ≤ Y := le_sup_left.trans (hAFQ.trans le_sup_right)
  have hAN : A ≤ Subgroup.normalizer (S : Set G) := hAY.trans hYS
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQ.2.2.1] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  obtain ⟨hFe, hF27, -, -, -⟩ := hF e he hed
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hdF : d ∈ F e := Item2119End2Proof.mem_of_isQOf2127 hA27 hF27 hFc hAFQ
    (hQ.2.2.2.2 e he hed).1 hQ.2.1 hdA hdc
  have hdS : d ∈ S := hFLS ⟨hdF, (hLf e he hed).2.2.2.2.1⟩
  have hrankd : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbd X hX3 hXc hXC =>
    card_le_27_of_le_centralizer h27 hQ hA27 hb hbd hX3 hXc hXC
  have hASeq : A ⊓ S = Subgroup.zpowers d := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr ⟨hdA, hdS⟩)
    by_contra hxd
    have h := hrankd x hx.1 hxd S hS3 hSc (le_centralizer_of_mem hSc hx.2)
    rw [hS81] at h
    norm_num at h
  have hAS : Nat.card (A ⊓ S : Subgroup G) = 3 := by
    rw [hASeq, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hrank : ∀ b ∈ A, b ∉ S → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbS =>
    hrankd b hb fun h => hbS ((Subgroup.zpowers_le.mpr hdS) h)
  have hP729 : Nat.card (A ⊔ S : Subgroup G) = 729 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAN
    rw [sup_comm, inf_comm, hAS, hS81, hA27] at h
    omega
  have hP3 : IsPGroup 3 (A ⊔ S : Subgroup G) := IsPGroup.to_sup_of_normal_right' hA3 hS3 hAN
  have hPY : A ⊔ S ≤ Y := sup_le hAY hSY
  have hPcard : Nat.card P = 729 := by
    have h1 := card_le_729 hAe hA27 h27 hQ hF h28 he hed hP.isPGroup hP.le
    have h2 := Item2119End6Proof.card_le_three_pow_of_isPGroup hPY hP3
    rw [hP729, ← hP.card_eq] at h2
    omega
  have hP₀ : IsSylowOf 3 (A ⊔ S) Y := isSylowOf_of_card hPY (by rw [hP729, ← hPcard, hP.card_eq])
  obtain ⟨k, hkY, hk⟩ := hP₀.exists_mem_conj hP
  have hkN : k ∈ Subgroup.normalizer (S : Set G) := hYS hkY
  have hSP : S ≤ P := by
    intro s hs
    refine (hk s).mpr (Subgroup.mem_sup_right ?_)
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) s).mp hs
    rwa [inv_inv] at h
  have key : ∀ B : Subgroup G, B ≤ P → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → 81 ≤ Nat.card B →
      B = S := by
    intro B hBP hBc hB81
    set B' := B.map (MulAut.conj k⁻¹).toMonoidHom with hB'def
    have hB'le : B' ≤ A ⊔ S := by
      rintro _ ⟨x, hx, rfl⟩
      change (MulAut.conj k⁻¹) x ∈ A ⊔ S
      rw [MulAut.conj_apply, inv_inv]
      exact (hk x).mp (hBP hx)
    have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hBc x hx y hy]
    have hB'card : Nat.card B' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    have hB'S := eq_of_le_sup hAc hA3 hA27 hSc hS3 hS81 hAN hAS hrank hB'le hB'c
      (by rw [hB'card]; exact hB81)
    have hBS : B ≤ S := by
      intro x hx
      have hx' : (MulAut.conj k⁻¹).toMonoidHom x ∈ B' := ⟨x, hx, rfl⟩
      rw [hB'S] at hx'
      change (MulAut.conj k⁻¹) x ∈ S at hx'
      rw [MulAut.conj_apply, inv_inv] at hx'
      have h := (Subgroup.mem_normalizer_iff.mp hkN _).mp hx'
      rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h
    exact Subgroup.eq_of_le_of_card_ge hBS (by rw [hS81]; exact hB81)
  have hScomm : IsMulCommutative S := ⟨⟨fun x y => Subtype.ext (hSc x x.2 y y.2)⟩⟩
  have hJ : CFSG.Open.thompsonSubgroup P = S := by
    refine thompsonSubgroup_eq_of hSP hScomm (fun B hBP hB => ?_) (fun B hBP hB hcard => ?_)
    · by_contra hlt
      push Not at hlt
      have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
        congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have h := key B hBP hBc (by omega)
      rw [h] at hlt
      omega
    · have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
        congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact key B hBP hBc (by omega)
  rw [Concl2129Loc, hJ]
  exact ⟨hSe, hS81, hYS, hFLS⟩

end CFSG.RankThree.PartTwo.Sec21
