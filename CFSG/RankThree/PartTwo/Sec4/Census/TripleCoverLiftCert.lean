module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import Certificates.Data.TripleCoverLift.Check

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census
open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti
open scoped Matrix

@[expose] def liftRelHolds {G : Type*} [Group G] {r : ℕ} (unit : ℕ → G) (y : Fin r → G) :
    LiftRel → Prop
  | .inv n i => ∀ hi : i < r, unit n * y ⟨i, hi⟩ * (unit n)⁻¹ = (y ⟨i, hi⟩)⁻¹
  | .fix n i => ∀ hi : i < r, unit n * y ⟨i, hi⟩ * (unit n)⁻¹ = y ⟨i, hi⟩
  | .swap n i j => ∀ (hi : i < r) (hj : j < r), unit n * y ⟨i, hi⟩ * (unit n)⁻¹ = y ⟨j, hj⟩ ∧
      unit n * y ⟨j, hj⟩ * (unit n)⁻¹ = y ⟨i, hi⟩

@[expose] def invCovered (rels : List LiftRel) (i : ℕ) : Bool :=
  rels.any fun r => match r with
    | .inv _ i' => i' == i
    | _ => false

@[expose] def hasInv (rels : List LiftRel) (n j : ℕ) : Bool :=
  rels.any fun r => match r with
    | .inv n' j' => n' == n && j' == j
    | _ => false

@[expose] def pairCovered (rels : List LiftRel) (i j : ℕ) : Bool :=
  rels.any fun r => match r with
    | .fix n a => (a == i && hasInv rels n j) || (a == j && hasInv rels n i)
    | .swap _ a b => (a == i && b == j) || (a == j && b == i)
    | _ => false

@[expose] def liftCovers (D : LiftData) : Bool :=
  D.base.outs.length == 3 && invCovered D.rels 0 && invCovered D.rels 1 &&
    invCovered D.rels 2 && pairCovered D.rels 0 1 && pairCovered D.rels 0 2 &&
    pairCovered D.rels 1 2

namespace TripleCoverLift

section Normalizer

variable {G : Type} {X : Type*} [Group G] [Group X] {φ : G →* X}

theorem exists_normalized_two_subgroup [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {P : Subgroup X} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 W ∧
      ∀ g : G, φ g ∈ Subgroup.normalizer (P : Set X) →
        g ∈ Subgroup.normalizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_surjective φ hφ
  set Q := P.comap φ with hQ
  let ψ : Q →* P := (φ.comp Q.subtype).codRestrict P fun x => x.2
  have hψs : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hφ x
    exact ⟨⟨g, hx⟩, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center Q := by
    intro x hx
    have hx' : (x : G) ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx') y)
  have : Group.IsNilpotent P := hP2.isNilpotent
  have : Group.IsNilpotent Q := Subgroup.isNilpotent_of_ker_le_center ψ hψker
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := Sylow.nonempty
  have hSn : (S : Subgroup Q).Normal := inferInstance
  have hS1 : Subsingleton (Sylow 2 Q) := (Sylow.unique_of_normal S hSn).instSubsingleton
  have h2Q : 2 ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hP (Subgroup.eq_bot_of_card_eq P (by rw [hk, pow_zero]))
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_surjective hψs)
  have hfwd : ∀ g : G, φ g ∈ Subgroup.normalizer (P : Set X) →
      ∀ w ∈ (S : Subgroup Q).map Q.subtype, g * w * g⁻¹ ∈ (S : Subgroup Q).map Q.subtype := by
    intro g hg w hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hq : g * (s : G) * g⁻¹ ∈ Q := by
      change φ (g * (s : G) * g⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp s.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    set q : Q := ⟨g * (s : G) * g⁻¹, hq⟩
    have hqk : q ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have hsk : (s : G) ^ 2 ^ k = 1 := by
        have := congrArg (fun x : (S : Subgroup Q) => ((x : Q) : G)) hk
        simpa using this
      change (g * (s : G) * g⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hsk, mul_one, mul_inv_cancel]
    have hzq : IsPGroup 2 (Subgroup.zpowers q) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hqk)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    obtain ⟨T, hT⟩ := hzq.exists_le_sylow
    have hTS : T = S := Subsingleton.elim T S
    subst hTS
    exact ⟨q, hT (Subgroup.mem_zpowers q), rfl⟩
  refine ⟨(S : Subgroup Q).map Q.subtype, ?_, S.isPGroup'.map _, fun g hg => ?_⟩
  · intro hbot
    apply Sylow.ne_bot_of_dvd_card S h2Q
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ (S : Subgroup Q).map Q.subtype := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  · have hg' : φ g⁻¹ ∈ Subgroup.normalizer (P : Set X) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hfwd g hg w, fun h => ?_⟩
    have := hfwd g⁻¹ hg' _ h
    rwa [inv_inv, show g⁻¹ * (g * w * g⁻¹) * g = w by group] at this

theorem succ_le_localRank_of_lift_normalizer [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime) (hpk : p ∣ Nat.card φ.ker)
    {E : Subgroup X} (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1) {P : Subgroup X} (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hEP : E ≤ Subgroup.normalizer (P : Set X)) {r : ℕ}
    (hr : p ^ r ≤ Nat.card E) : r + 1 ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  set Z := Subgroup.zpowers (z : G)
  have hZk : Z ≤ φ.ker := by
    rw [Subgroup.zpowers_le]
    exact z.2
  have hZp : ∀ w ∈ Z, w ^ p = 1 := by
    rintro _ ⟨j, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
      pow_orderOf_eq_one, one_zpow]
  have hs : p ^ 1 ≤ Nat.card Z := by rw [Nat.card_zpowers, hzo, pow_one]
  set U := powOneSubgroup φ E p hcomm with hUdef
  have hUab : IsElemAbelian p U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (mem_powOneSubgroup.mp a.2).1 _
      (mem_powOneSubgroup.mp b.2).1)⟩⟩, fun x hx => (mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup p U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X := φ.comp U.subtype
  have hψr : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := hlift e he
      exact ⟨⟨y, mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun w hw => mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hw)]; exact E.one_mem, hZp w hw⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : p ^ 1 ≤ Nat.card ψ.ker := by
    calc p ^ 1 ≤ Nat.card Z := hs
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have hrk : r + 1 ≤ k := by
    have h1 : p ^ (r + 1) ≤ p ^ k := by
      rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, pow_add, mul_comm]
      exact Nat.mul_le_mul hψk hr
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  obtain ⟨W, hW, hW2, hWN⟩ := exists_normalized_two_subgroup hφ hker hP hP2
  have hUW : U ≤ Subgroup.normalizer (W : Set G) := fun x hx =>
    hWN x (hEP (mem_powOneSubgroup.mp hx).1)
  exact hrk.trans (le_localRank_of_le_normalizer hp hW hW2 hUab hk hUW)

end Normalizer

end TripleCoverLift

theorem four_le_twoLocalOddRank_of_liftConfig {G X : Type} [Group G] [Finite G] [Group X]
    {φ : G →* X} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) {P : Subgroup X} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (y : Fin 3 → X) (hy3 : ∀ i, y i ^ 3 = 1) (hcommy : ∀ i j, Commute (y i) (y j))
    (hEP : Subgroup.closure (Set.range y) ≤ Subgroup.normalizer (P : Set X))
    (hE : 27 ≤ Nat.card (Subgroup.closure (Set.range y)))
    (hinv : ∀ i, ∃ n : X, n * y i * n⁻¹ = (y i)⁻¹)
    (hpair : ∀ i j : Fin 3, i < j → ∃ n : X,
      (n * y i * n⁻¹ = y i ∧ n * y j * n⁻¹ = (y j)⁻¹) ∨
      (n * y j * n⁻¹ = y j ∧ n * y i * n⁻¹ = (y i)⁻¹) ∨
      (n * y i * n⁻¹ = y j ∧ n * y j * n⁻¹ = y i)) :
    4 ≤ CFSG.twoLocalOddRank G := by
  set E := Subgroup.closure (Set.range y)
  have hodd : Odd 3 := by decide
  have key : ∀ (a b : G) (i j : Fin 3), φ a = y i → φ b = y j → i < j → a * b = b * a := by
    intro a b i j hi hj hlt
    have hc : Commute (φ a) (φ b) := by
      rw [hi, hj]
      exact hcommy i j
    obtain ⟨n, hn | hn | hn⟩ := hpair i j hlt
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inl ⟨by rw [hi]; exact hn.1, by rw [hj]; exact hn.2⟩)
    · exact (TripleCoverLift.commute_of_conj hφ hker hodd hc.symm (by rw [hi]; exact hy3 i)
        (n := n) (Or.inl ⟨by rw [hj]; exact hn.1, by rw [hi]; exact hn.2⟩)).symm
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inr ⟨by rw [hi, hj]; exact hn.1, by rw [hi, hj]; exact hn.2⟩)
  have hS : ∀ a b : G, φ a ∈ Set.range y → φ b ∈ Set.range y → φ a ≠ φ b → a * b = b * a := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key a b i j hi.symm hj.symm hlt
    · exact (key b a j i hj.symm hi.symm hlt).symm
  have hcomm : ∀ x ∈ E.comap φ, ∀ z ∈ E.comap φ, x * z = z * x := fun x hx z hz =>
    TripleCoverLift.commute_of_mem_closure hφ hker hS hx hz
  have hlift : ∀ e ∈ E, ∃ g : G, φ g = e ∧ g ^ 3 = 1 := by
    intro e he
    refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hcomm Subgroup.subset_closure
      ?_ he
    rintro s ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hinv i
    exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd (hy3 i) hn
  have h4 := TripleCoverLift.succ_le_localRank_of_lift_normalizer hφ hker Nat.prime_three h3
    hcomm hlift hP hP2 hEP (r := 3) (by norm_num; exact hE)
  exact CFSG.RankThree.PartOne.Census3.four_le_twoLocalOddRank_of_localRank Nat.prime_three
    (by norm_num) h4

namespace LiftCert

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem exists_of_liftCheck [Inhabited M] (D : LiftData) (h : LiftData.check O D = true) :
    ∃ (P : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (y : Fin D.base.outs.length → (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (unit : ℕ → (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ),
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ (∀ i, y i ^ 3 = 1) ∧ (∀ i j, Commute (y i) (y j)) ∧
      Subgroup.closure (Set.range y) ≤ Subgroup.normalizer (P : Set _) ∧
      (∀ a : Fin D.base.outs.length → Fin 3, a ≠ 0 →
        (List.ofFn fun i => y i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ rel ∈ D.rels, liftRelHolds unit y rel := by
  classical
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold LiftData.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hprog⟩, houts⟩, hinv₁⟩, hinv₂⟩, hel⟩, hT₁⟩, hT₂⟩, hT₁₂⟩, hmov⟩,
    hconj⟩, hunits⟩, hrels⟩ := h
  have hA : Sp.WF (O.decode D.base.seedA) ∧ Sp.toMat (O.decode D.base.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.base.seedB) ∧ Sp.toMat (O.decode D.base.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ :=
    CFSG.RankThree.PartTwo.Census.OpsSpec.initRegs_regs Sp S hA hB D.base.nregs
  obtain ⟨hs, hok⟩ := CFSG.RankThree.PartTwo.Census.OpsSpec.run_regs Sp S D.base.prog hok0
    (by rw [hs0]; exact hprog)
  set R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  rw [hs0] at hs
  let mat : ℕ → S := fun r => if hr : r < R.size then ⟨Sp.toMat R[r]!, (hok r hr).2⟩ else 1
  have hmat : ∀ r, r < D.base.nregs →
      ((mat r : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat R[r]! := by
    intro r hr
    have hr' : r < R.size := by rw [hs]; exact hr
    simp only [mat, hr', dite_true]
  let unit : ℕ → Sˣ := fun r => if hx : ∃ e, 0 < e ∧ mat r ^ e = 1 then
      Units.ofPowEqOne (mat r) (Nat.find hx) (Nat.find_spec hx).2 (Nat.find_spec hx).1.ne'
    else 1
  have hunit : ∀ r e, 0 < e → mat r ^ e = 1 → ((unit r : S)) = mat r := by
    intro r e he h1
    have hx : ∃ e, 0 < e ∧ mat r ^ e = 1 := ⟨e, he, h1⟩
    simp only [unit, hx, dite_true, Units.val_ofPowEqOne]
  have hcoe : ∀ r e, r < D.base.nregs → 0 < e → Sp.toMat R[r]! ^ e = 1 →
      (((unit r : S) : Matrix (Fin d) (Fin d) (ZMod p))) = Sp.toMat R[r]! := by
    intro r e hr he h1
    rw [hunit r e he (Subtype.ext (by rw [SubmonoidClass.coe_pow, hmat r hr, h1]; rfl)),
      hmat r hr]
  have hWF : ∀ r, r < D.base.nregs → Sp.WF R[r]! := fun r hr => (hok r (by rw [hs]; exact hr)).1
  have hsqM : ∀ {T : M}, Sp.WF T → O.eq (O.mul T T) O.one = true →
      Sp.toMat T ^ 2 = 1 := fun {T} hT hT2 => by
    have := Sp.toMat_eq (Sp.mul_wf hT hT) Sp.one_wf hT2
    rwa [Sp.toMat_mul hT hT, Sp.toMat_one, ← sq] at this
  set t₁ := unit D.inv₁
  set t₂ := unit D.inv₂
  have ht₁ := hcoe D.inv₁ 2 hinv₁ (by norm_num) (hsqM (hWF _ hinv₁) hT₁)
  have ht₂ := hcoe D.inv₂ 2 hinv₂ (by norm_num) (hsqM (hWF _ hinv₂) hT₂)
  have hunitEq : ∀ {u v : Sˣ}, ((u : S) : Matrix (Fin d) (Fin d) (ZMod p)) =
      ((v : S) : Matrix (Fin d) (Fin d) (ZMod p)) → u = v := fun h => Units.ext (Subtype.ext h)
  have ht₁2 : t₁ ^ 2 = 1 := hunitEq (by
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, ht₁]
    exact hsqM (hWF _ hinv₁) hT₁)
  have ht₂2 : t₂ ^ 2 = 1 := hunitEq (by
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, ht₂]
    exact hsqM (hWF _ hinv₂) hT₂)
  have ht₁₂ : t₁ * t₂ = t₂ * t₁ := hunitEq (by
    simp only [Units.val_mul, Submonoid.coe_mul]
    rw [ht₁, ht₂]
    have := Sp.toMat_eq (Sp.mul_wf (hWF _ hinv₁) (hWF _ hinv₂))
      (Sp.mul_wf (hWF _ hinv₂) (hWF _ hinv₁)) hT₁₂
    rwa [Sp.toMat_mul (hWF _ hinv₁) (hWF _ hinv₂),
      Sp.toMat_mul (hWF _ hinv₂) (hWF _ hinv₁)] at this)
  set P := Subgroup.closure ({t₁, t₂} : Set Sˣ)
  have ht₁P : t₁ ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have ht₂P : t₂ ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hP : P ≠ ⊥ := by
    intro hbot
    have h1 := ht₁P
    rw [hbot, Subgroup.mem_bot] at h1
    have h1' : Sp.toMat R[D.inv₁]! = 1 := by
      rw [← ht₁]
      change ((t₁ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = 1
      rw [h1]
      rfl
    obtain ⟨k, -, hk⟩ := List.any_eq_true.1 hmov
    apply Sp.toVec_ne hk
    rw [Sp.toVec_vmul (Sp.unit_wf k) (hWF _ hinv₁), h1', Matrix.vecMul_one]
  have hP2 : IsPGroup 2 P := FourGroup.isPGroup_closure_pair ht₁2 ht₂2 ht₁₂
  set xs := D.base.outs.map fun r => R[r]!
  have hlen : xs.length = D.base.outs.length := List.length_map _
  have houts' : ∀ i : Fin D.base.outs.length, D.base.outs[i] < D.base.nregs := fun i =>
    of_decide_eq_true (List.all_eq_true.1 houts _ (List.getElem_mem i.isLt))
  have hxsi : ∀ i : Fin D.base.outs.length, xs[(i : ℕ)]'(by rw [hlen]; exact i.isLt) =
      R[D.base.outs[i]]! := fun i => List.getElem_map _
  have hw : ∀ X ∈ xs, Sp.WF X := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hWF r (of_decide_eq_true (List.all_eq_true.1 houts r hr))
  unfold Ops.elemOK at hel
  simp only [Bool.and_eq_true] at hel
  obtain ⟨⟨hcube, hcomms⟩, hker⟩ := hel
  have hpair := Sp.pairwise_of_commsOK hw hcomms
  have hcubeM : ∀ i : Fin D.base.outs.length, Sp.toMat R[D.base.outs[i]]! ^ 3 = 1 := fun i => by
    have hmem : R[D.base.outs[i]]! ∈ xs := List.mem_map.2 ⟨_, List.getElem_mem i.isLt, rfl⟩
    have hX := hw _ hmem
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf
      (List.all_eq_true.1 hcube _ hmem)
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  let y : Fin D.base.outs.length → Sˣ := fun i => unit D.base.outs[i]
  have hy : ∀ i, (((y i : S) : Matrix (Fin d) (Fin d) (ZMod p))) = Sp.toMat R[D.base.outs[i]]! :=
    fun i => hcoe _ 3 (houts' i) (by norm_num) (hcubeM i)
  have hy3 : ∀ i, y i ^ 3 = 1 := fun i => hunitEq (by
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, hy]
    exact hcubeM i)
  have hcommM : ∀ i j : Fin D.base.outs.length,
      Sp.toMat R[D.base.outs[i]]! * Sp.toMat R[D.base.outs[j]]! =
        Sp.toMat R[D.base.outs[j]]! * Sp.toMat R[D.base.outs[i]]! := by
    intro i j
    rw [← hxsi i, ← hxsi j]
    rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · exact List.pairwise_iff_getElem.1 hpair i j _ _ hij
    · rw [Fin.ext hij]
    · exact (List.pairwise_iff_getElem.1 hpair j i _ _ hij).symm
  have hyc : ∀ i j, Commute (y i) (y j) := fun i j => hunitEq (by
    simp only [Units.val_mul, Submonoid.coe_mul, hy]
    exact hcommM i j)
  have hyN : ∀ i, y i ∈ Subgroup.normalizer (P : Set Sˣ) := by
    intro i
    refine FourGroup.mem_normalizer_closure_of_pow_three (hy3 i) ?_
    have hc := List.all_eq_true.1 hconj _ (List.getElem_mem i.isLt)
    rw [Bool.and_eq_true] at hc
    have hX := hWF _ (houts' i)
    have key : ∀ (τ : Sˣ) (T : M), Sp.WF T →
        ((τ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T →
        LiftData.conjOK O R[D.base.outs[i]]! T R[D.inv₁]! R[D.inv₂]! = true →
        y i * τ * (y i)⁻¹ ∈ P := by
      intro τ T hT hτT hok'
      have hcase : ∀ σ ∈ P, ((σ : S) : Matrix (Fin d) (Fin d) (ZMod p)) *
          Sp.toMat R[D.base.outs[i]]! = Sp.toMat R[D.base.outs[i]]! * Sp.toMat T →
          y i * τ * (y i)⁻¹ ∈ P := by
        intro σ hσ he
        have e : y i * τ = σ * y i := hunitEq (by
          simp only [Units.val_mul, Submonoid.coe_mul]
          rw [hy, hτT]
          exact he.symm)
        rw [e, mul_inv_cancel_right]
        exact hσ
      rcases CFSG.RankThree.PartTwo.Census.OpsSpec.toMat_of_conjOK Sp hX hT (hWF _ hinv₁)
          (hWF _ hinv₂) hok' with he | he | he
      · exact hcase t₁ ht₁P (by rw [ht₁, he])
      · exact hcase t₂ ht₂P (by rw [ht₂, he])
      · refine hcase (t₁ * t₂) (P.mul_mem ht₁P ht₂P) ?_
        simp only [Units.val_mul, Submonoid.coe_mul]
        rw [ht₁, ht₂, he]
    rintro x (rfl | rfl)
    · exact key t₁ R[D.inv₁]! (hWF _ hinv₁) ht₁ hc.1
    · exact key t₂ R[D.inv₂]! (hWF _ hinv₂) ht₂ hc.2
  have hEN : Subgroup.closure (Set.range y) ≤ Subgroup.normalizer (P : Set Sˣ) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hyN i
  have hkerY : ∀ a : Fin D.base.outs.length → Fin 3, a ≠ 0 →
      (List.ofFn fun i => y i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha hprod
    let a' : Fin xs.length → Fin 3 := fun j => a (Fin.cast hlen j)
    have ha' : a' ≠ 0 := by
      intro h0
      apply ha
      funext i
      have := congrFun h0 (Fin.cast hlen.symm i)
      simpa [a'] using this
    refine Sp.ne_one_of_kerOK hw hker a' ha' ?_
    let f : Sˣ →* Matrix (Fin d) (Fin d) (ZMod p) := S.subtype.comp (Units.coeHom S)
    have hf : ∀ i (n : ℕ), f (y i ^ n) = Sp.toMat R[D.base.outs[i]]! ^ n := fun i n => by
      rw [map_pow]
      exact congrArg (· ^ n) (hy i)
    have h1 := congrArg f hprod
    rw [map_list_prod, List.map_ofFn, map_one, Function.comp_def,
      funext fun i => hf i _] at h1
    rw [List.ofFn_congr hlen]
    convert h1 using 3
    funext i
    have e1 : a' (Fin.cast hlen.symm i) = a i := by
      simp only [a', Fin.cast_cast, Fin.cast_eq_self]
    rw [e1, ← hxsi i]
    rfl
  have hnu : ∀ n, D.units.any (fun u => u.1 == n) = true →
      n < D.base.nregs ∧ (((unit n : S) : Matrix (Fin d) (Fin d) (ZMod p))) = Sp.toMat R[n]! := by
    intro n hn'
    obtain ⟨u, hu, hun⟩ := List.any_eq_true.1 hn'
    have hun' : u.1 = n := beq_iff_eq.1 hun
    have hu' := List.all_eq_true.1 hunits u hu
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu'
    obtain ⟨⟨hr, he⟩, hpow⟩ := hu'
    subst hun'
    have hpw := Sp.pow_spec (hWF _ hr) u.2
    have h1 : Sp.toMat R[u.1]! ^ u.2 = 1 := by
      have := Sp.toMat_eq hpw.1 Sp.one_wf hpow
      rwa [hpw.2, Sp.toMat_one] at this
    exact ⟨hr, hcoe _ u.2 hr he h1⟩
  have hgetE : ∀ (i : ℕ) (hi : i < D.base.outs.length),
      D.base.outs[i]! = D.base.outs[(⟨i, hi⟩ : Fin D.base.outs.length)] := fun i hi =>
    getElem!_pos _ i hi
  have hyi : ∀ i, (y i)⁻¹ = y i * y i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hy3 i)
  have hconjU : ∀ (n : ℕ) (u v : Sˣ) (U V : M), n < D.base.nregs → Sp.WF U → Sp.WF V →
      (((unit n : S) : Matrix (Fin d) (Fin d) (ZMod p))) = Sp.toMat R[n]! →
      ((u : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat U →
      ((v : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat V →
      O.eq (O.mul R[n]! U) (O.mul V R[n]!) = true → unit n * u * (unit n)⁻¹ = v := by
    intro n u v U V hnr hU hV hnM huU hvV heq
    have hNw := hWF _ hnr
    have := Sp.toMat_eq (Sp.mul_wf hNw hU) (Sp.mul_wf hV hNw) heq
    rw [Sp.toMat_mul hNw hU, Sp.toMat_mul hV hNw] at this
    have e : unit n * u = v * unit n := hunitEq (by
      simp only [Units.val_mul, Submonoid.coe_mul]
      rw [hnM, huU, hvV]
      exact this)
    rw [e, mul_inv_cancel_right]
  have hrelH : ∀ rel ∈ D.rels, liftRelHolds unit y rel := by
    intro rel hrel
    have hok' := List.all_eq_true.1 hrels rel hrel
    cases rel with
    | inv n i =>
      intro hi
      simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨⟨hnr, -⟩, hu⟩, heq⟩ := hok'
      rw [hgetE i hi] at heq
      have hYw := hWF _ (houts' ⟨i, hi⟩)
      rw [hyi]
      refine hconjU n _ _ _ _ hnr hYw (Sp.mul_wf hYw hYw) (hnu n hu).2 (hy _) ?_ heq
      simp only [Units.val_mul, Submonoid.coe_mul]
      rw [hy, Sp.toMat_mul hYw hYw]
    | fix n i =>
      intro hi
      simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨⟨hnr, -⟩, hu⟩, heq⟩ := hok'
      rw [hgetE i hi] at heq
      have hYw := hWF _ (houts' ⟨i, hi⟩)
      exact hconjU n _ _ _ _ hnr hYw hYw (hnu n hu).2 (hy _) (hy _) heq
    | swap n i j =>
      intro hi hj
      simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨⟨⟨⟨hnr, -⟩, -⟩, hu⟩, heq₁⟩, heq₂⟩ := hok'
      rw [hgetE i hi, hgetE j hj] at heq₁ heq₂
      have hYi := hWF _ (houts' ⟨i, hi⟩)
      have hYj := hWF _ (houts' ⟨j, hj⟩)
      exact ⟨hconjU n _ _ _ _ hnr hYi hYj (hnu n hu).2 (hy _) (hy _) heq₁,
        hconjU n _ _ _ _ hnr hYj hYi (hnu n hu).2 (hy _) (hy _) heq₂⟩
  exact ⟨P, y, unit, hP, hP2, hy3, hyc, hEN, hkerY, hrelH⟩

end LiftCert

section Covers

variable {X : Type*} [Group X] {r : ℕ} {rels : List LiftRel} {unit : ℕ → X} {y : Fin r → X}

theorem exists_inv_of_invCovered (hrel : ∀ rel ∈ rels, liftRelHolds unit y rel) {i : ℕ}
    (hi : i < r) (h : invCovered rels i = true) :
    ∃ n : X, n * y ⟨i, hi⟩ * n⁻¹ = (y ⟨i, hi⟩)⁻¹ := by
  obtain ⟨rel, hmem, hr⟩ := List.any_eq_true.1 h
  cases rel with
  | inv n i' =>
    obtain rfl : i' = i := beq_iff_eq.1 hr
    exact ⟨unit n, hrel _ hmem hi⟩
  | fix n i' => exact absurd hr (by simp)
  | swap n i' j' => exact absurd hr (by simp)

theorem inv_of_hasInv (hrel : ∀ rel ∈ rels, liftRelHolds unit y rel) {n j : ℕ} (hj : j < r)
    (h : hasInv rels n j = true) : unit n * y ⟨j, hj⟩ * (unit n)⁻¹ = (y ⟨j, hj⟩)⁻¹ := by
  obtain ⟨rel, hmem, hr⟩ := List.any_eq_true.1 h
  cases rel with
  | inv n' j' =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hrel _ hmem hj
  | fix n' i' => exact absurd hr (by simp)
  | swap n' i' j' => exact absurd hr (by simp)

theorem exists_pair_of_pairCovered (hrel : ∀ rel ∈ rels, liftRelHolds unit y rel) {i j : ℕ}
    (hi : i < r) (hj : j < r) (h : pairCovered rels i j = true) :
    ∃ n : X, (n * y ⟨i, hi⟩ * n⁻¹ = y ⟨i, hi⟩ ∧ n * y ⟨j, hj⟩ * n⁻¹ = (y ⟨j, hj⟩)⁻¹) ∨
      (n * y ⟨j, hj⟩ * n⁻¹ = y ⟨j, hj⟩ ∧ n * y ⟨i, hi⟩ * n⁻¹ = (y ⟨i, hi⟩)⁻¹) ∨
      (n * y ⟨i, hi⟩ * n⁻¹ = y ⟨j, hj⟩ ∧ n * y ⟨j, hj⟩ * n⁻¹ = y ⟨i, hi⟩) := by
  obtain ⟨rel, hmem, hr⟩ := List.any_eq_true.1 h
  cases rel with
  | inv n a => exact absurd hr (by simp)
  | fix n a =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hr
    rcases hr with ⟨rfl, hinv⟩ | ⟨rfl, hinv⟩
    · exact ⟨unit n, Or.inl ⟨hrel _ hmem hi, inv_of_hasInv hrel hj hinv⟩⟩
    · exact ⟨unit n, Or.inr (Or.inl ⟨hrel _ hmem hj, inv_of_hasInv hrel hi hinv⟩)⟩
  | swap n a b =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨unit n, Or.inr (Or.inr (hrel _ hmem hi hj))⟩
    · obtain ⟨h1, h2⟩ := hrel _ hmem hj hi
      exact ⟨unit n, Or.inr (Or.inr ⟨h2, h1⟩)⟩

end Covers

namespace LiftCert

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem four_le_twoLocalOddRank_of_check [Inhabited M] (D : LiftData)
    (h : LiftData.check O D = true) (hcov : liftCovers D = true) {G : Type} [Group G] [Finite G]
    {φ : G →* (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) : 4 ≤ CFSG.twoLocalOddRank G := by
  classical
  set X := (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ
  have : Finite X := Finite.of_surjective φ hφ
  obtain ⟨P, y, unit, hP, hP2, hy3, hyc, hEN, hkerY, hrel⟩ := exists_of_liftCheck Sp D h
  simp only [liftCovers, Bool.and_eq_true, beq_iff_eq] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hr3, hi0⟩, hi1⟩, hi2⟩, hp01⟩, hp02⟩, hp12⟩ := hcov
  let z : Fin 3 → X := fun i => y (Fin.cast hr3.symm i)
  have hz : ∀ i : Fin 3, z i = y ⟨i, by rw [hr3]; exact i.isLt⟩ := fun i => rfl
  have hrange : Set.range z = Set.range y := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hr3 i, by simp [z]⟩
  set C := Subgroup.closure (Set.range z)
  have hC : 27 ≤ Nat.card C := by
    let v : Fin 3 → C := fun i => ⟨z i, Subgroup.subset_closure ⟨i, rfl⟩⟩
    obtain ⟨E', -, hE'⟩ := CFSG.SectionRank.exists_elemAbelian_of_commuting v
      (fun i => Subtype.ext (by simpa [v] using hy3 _))
      (fun i j => Subtype.ext (hyc _ _).eq)
      (fun a ha hprod => by
        let a' : Fin D.base.outs.length → Fin 3 := fun j => a (Fin.cast hr3 j)
        have ha' : a' ≠ 0 := by
          intro h0
          apply ha
          funext i
          have := congrFun h0 (Fin.cast hr3.symm i)
          simpa [a'] using this
        apply hkerY a' ha'
        have h1 := congrArg C.subtype hprod
        rw [map_list_prod, List.map_ofFn, map_one] at h1
        rw [List.ofFn_congr hr3]
        convert h1 using 3
        funext i
        simp [a', v, z])
    calc 27 = Nat.card E' := by rw [hE']; norm_num
      _ ≤ Nat.card C := Subgroup.card_le_card_group E'
  have hzN : C ≤ Subgroup.normalizer (P : Set X) := by
    rw [show C = Subgroup.closure (Set.range y) by rw [← hrange]]
    exact hEN
  refine four_le_twoLocalOddRank_of_liftConfig hφ hker h3 hP hP2 z (fun i => hy3 _)
    (fun i j => hyc _ _) hzN hC ?_ ?_
  · intro i
    fin_cases i
    · exact exists_inv_of_invCovered hrel _ hi0
    · exact exists_inv_of_invCovered hrel _ hi1
    · exact exists_inv_of_invCovered hrel _ hi2
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact exists_pair_of_pairCovered hrel _ _ hp01
    · exact exists_pair_of_pairCovered hrel _ _ hp02
    · exact exists_pair_of_pairCovered hrel _ _ hp12

theorem tripleCoverSporadicRankFour_of_check [Inhabited M] (D : LiftData)
    (h : LiftData.check O D = true) (hcov : liftCovers D = true) {s : SporadicName}
    (b : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ ≃*
      (CFSGIndex.sporadic s).Group) : TripleCoverSporadicRankFour s := by
  intro G _ _ ⟨hq, h3, ⟨e⟩⟩
  refine four_le_twoLocalOddRank_of_check Sp D h hcov
    (CFSG.GH74.Generic.centralQuotientMap_surjective (e.trans b.symm))
    (CFSG.GH74.Generic.centralQuotientMap_ker (e.trans b.symm)).le ?_
  rw [CFSG.GH74.Generic.centralQuotientMap_ker]
  exact h3

end LiftCert

end CFSG.RankThree.PartTwo.Sec4.Census
