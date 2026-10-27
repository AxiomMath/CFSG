module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofSL2Aut
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofSL2Mat
public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofExc
import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj
import CFSG.GH74.GLS.Bg.TwoGroups.L26Cop

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item211Lie3Proof (IsScalar2)

section General

variable {M : Type} [Group M]

@[expose] def blockSub {S : Type} [Group S] (d : M) (ι : S →* M)
    (hc : ∀ B, ι B * d = d * ι B) : Subgroup M where
  carrier := {x | ∃ (k : ℤ) (B : S), x = d ^ k * ι B}
  mul_mem' := by
    rintro _ _ ⟨k, B, rfl⟩ ⟨l, B', rfl⟩
    refine ⟨k + l, B * B', ?_⟩
    have hcz : ι B * d ^ l = d ^ l * ι B := (Commute.zpow_right (hc B) l).eq
    rw [map_mul, zpow_add]
    calc d ^ k * ι B * (d ^ l * ι B') = d ^ k * (ι B * d ^ l) * ι B' := by group
      _ = d ^ k * (d ^ l * ι B) * ι B' := by rw [hcz]
      _ = d ^ k * d ^ l * (ι B * ι B') := by group
  one_mem' := ⟨0, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨k, B, rfl⟩
    refine ⟨-k, B⁻¹, ?_⟩
    have hcz : (ι B)⁻¹ * (d ^ k)⁻¹ = (d ^ k)⁻¹ * (ι B)⁻¹ :=
      ((Commute.zpow_right (hc B) k).inv_inv).eq
    rw [mul_inv_rev, map_inv, zpow_neg, hcz]

theorem mem_blockSub {S : Type} [Group S] {d : M} {ι : S →* M} {hc : ∀ B, ι B * d = d * ι B}
    {x : M} : x ∈ blockSub d ι hc ↔ ∃ (k : ℤ) (B : S), x = d ^ k * ι B :=
  Iff.rfl

theorem range_le_blockSub {S : Type} [Group S] {d : M} {ι : S →* M}
    {hc : ∀ B, ι B * d = d * ι B} : ι.range ≤ blockSub d ι hc := by
  rintro _ ⟨B, rfl⟩
  exact ⟨0, B, by simp⟩

theorem zpow_commute {S : Type} [Group S] {d : M} {ι : S →* M} (hc : ∀ B, ι B * d = d * ι B)
    (k : ℤ) (B : S) : ι B * d ^ k = d ^ k * ι B :=
  (Commute.zpow_right (hc B) k).eq

theorem pow_dk_mul {S : Type} [Group S] {d : M} {ι : S →* M} (hc : ∀ B, ι B * d = d * ι B)
    (k : ℤ) (B : S) (n : ℕ) : (d ^ k * ι B) ^ n = d ^ (k * n) * ι (B ^ n) := by
  have hcomm : Commute (d ^ k) (ι B) := (zpow_commute hc k B).symm
  rw [hcomm.mul_pow, map_pow, ← zpow_natCast, ← zpow_mul]

theorem pow_three_dk_mul {S : Type} [Group S] {d : M} {ι : S →* M}
    (hc : ∀ B, ι B * d = d * ι B) (hd3 : d ^ 3 = 1) (k : ℤ) (B : S) :
    (d ^ k * ι B) ^ 3 = ι (B ^ 3) := by
  rw [pow_dk_mul hc, show k * ((3 : ℕ) : ℤ) = 3 * k by push_cast; ring, zpow_mul,
    show d ^ (3 : ℤ) = d ^ (3 : ℕ) from zpow_ofNat d 3, hd3, one_zpow, one_mul]

theorem mem_range_of_pow_two {S : Type} [Group S] {d : M} {ι : S →* M}
    (hc : ∀ B, ι B * d = d * ι B) (hd3 : d ^ 3 = 1) {q : M} (hq : q ∈ blockSub d ι hc) {e : ℕ}
    (he : q ^ 2 ^ e = 1) : q ∈ ι.range := by
  obtain ⟨k, B, rfl⟩ := hq
  have hcop : Nat.Coprime 3 (orderOf (d ^ k * ι B)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one he)
      (Nat.Coprime.pow_right e (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, pow_three_dk_mul hc hd3, ← map_pow]
  exact ⟨_, rfl⟩

theorem le_conjClosure {D H : Subgroup M} : D ≤ conjClosure D H :=
  fun x hx => Subgroup.subset_closure ⟨1, H.one_mem, x, hx, by group⟩

theorem conjClosure_le {D H : Subgroup M} (hDH : D ≤ H) : conjClosure D H ≤ H :=
  (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg (hDH hx)) (H.inv_mem hg))

theorem conjClosure_le_of_commutator {D H N : Subgroup M} (hDN : D ≤ N) (hDH : D ≤ H)
    (hcomm : ∀ g ∈ H, ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ N) : conjClosure D H ≤ N := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, x, hx, rfl⟩
  have e : g * x * g⁻¹ = g * x * g⁻¹ * x⁻¹ * x := by group
  rw [SetLike.mem_coe, e]
  exact N.mul_mem (hcomm g hg x (hDH hx)) (hDN hx)

theorem mem_normalizer_conjClosure' {D H : Subgroup M} {k : M} (hk : k ∈ H) :
    k ∈ Subgroup.normalizer (conjClosure D H : Set M) := by
  have hconj : ∀ {k : M}, k ∈ H → ∀ y ∈ conjClosure D H, k * y * k⁻¹ ∈ conjClosure D H := by
    intro k hk y hy
    have hle : conjClosure D H ≤ (conjClosure D H).comap (MulAut.conj k).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, x, hx, rfl⟩
      refine Subgroup.subset_closure ⟨k * g, H.mul_mem hk hg, x, hx, ?_⟩
      change k * (g * x * g⁻¹) * k⁻¹ = k * g * x * (k * g)⁻¹
      group
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj hk y, fun hy => ?_⟩
  have e := hconj (H.inv_mem hk) _ hy
  rwa [inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at e

theorem conj_mem_conjClosure {D H : Subgroup M} {t : M} (htH : ∀ g ∈ H, t * g * t⁻¹ ∈ H)
    (htD : ∀ x ∈ D, t * x * t⁻¹ = x) {c : M} (hc : c ∈ conjClosure D H) :
    t * c * t⁻¹ ∈ conjClosure D H := by
  have hle : conjClosure D H ≤ (conjClosure D H).comap (MulAut.conj t).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨t * g * t⁻¹, htH g hg, x, hx, ?_⟩
    change t * (g * x * g⁻¹) * t⁻¹ = t * g * t⁻¹ * x * (t * g * t⁻¹)⁻¹
    calc t * (g * x * g⁻¹) * t⁻¹ = t * g * t⁻¹ * (t * x * t⁻¹) * (t * g * t⁻¹)⁻¹ := by group
      _ = t * g * t⁻¹ * x * (t * g * t⁻¹)⁻¹ := by rw [htD x hx]
  exact hle hc

theorem conj_mem_commutator {C : Subgroup M} {t : M} (ht : ∀ c ∈ C, t * c * t⁻¹ ∈ C) {y : M}
    (hy : y ∈ ⁅C, C⁆) : t * y * t⁻¹ ∈ ⁅C, C⁆ := by
  set φ := (MulAut.conj t).toMonoidHom with hφ
  have hmap : C.map φ ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    exact ht c hc
  have h1 : (⁅C, C⁆).map φ ≤ ⁅C, C⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact h1 ⟨y, hy, rfl⟩

theorem commutator_eq_range {C : Subgroup M} {S : Type} [Group S] (ι : S →* M)
    (hS : Group.IsPerfect S) (hιC : ι.range ≤ C)
    (hcomm : ∀ g ∈ C, ∀ h ∈ C, g * h * g⁻¹ * h⁻¹ ∈ ι.range) : ⁅C, C⁆ = ι.range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact hcomm g hg h hh
  · rw [← Item228Census3Proof.commutator_range_of_isPerfect hS ι]
    exact Subgroup.commutator_mono hιC hιC

@[expose] noncomputable def inducedAut {S : Type} [Group S] (ι : S →* M)
    (hι : Function.Injective ι) (t : M)
    (ht : ι.range.map (MulAut.conj t).toMonoidHom = ι.range) : MulAut S :=
  ((MonoidHom.ofInjective hι).trans ((MulEquiv.subgroupMap (MulAut.conj t) ι.range).trans
    (MulEquiv.subgroupCongr ht))).trans (MonoidHom.ofInjective hι).symm

theorem apply_inducedAut {S : Type} [Group S] (ι : S →* M) (hι : Function.Injective ι)
    (t : M) (ht : ι.range.map (MulAut.conj t).toMonoidHom = ι.range) (B : S) :
    ι (inducedAut ι hι t ht B) = t * ι B * t⁻¹ := by
  rw [inducedAut, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
  rfl

theorem map_conj_range_eq {S : Type} [Group S] (ι : S →* M) {t : M}
    (ht : ∀ B, t * ι B * t⁻¹ ∈ ι.range) (ht' : ∀ B, t⁻¹ * ι B * t ∈ ι.range) :
    ι.range.map (MulAut.conj t).toMonoidHom = ι.range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    exact ht B
  · rintro _ ⟨B, rfl⟩
    obtain ⟨B', hB'⟩ := ht' B
    refine ⟨ι B', ⟨B', rfl⟩, ?_⟩
    change t * ι B' * t⁻¹ = ι B
    rw [hB']
    group

theorem exists_mem_not_mem_zpowers {D : Subgroup M} {d : M} (hd3 : d ^ 3 = 1)
    (hD9 : Nat.card D = 9) : ∃ x ∈ D, x ∉ Subgroup.zpowers d := by
  by_contra h
  push Not at h
  have hfin : IsOfFinOrder d := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hd3⟩
  have : Finite (Subgroup.zpowers d) := hfin.finite_zpowers
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le h
  rw [Nat.card_zpowers, hD9] at hle
  have h3 : orderOf d ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hd3
  omega

theorem exists_pow_two_pow_eq_one {Q : Subgroup M} (hQ : IsPGroup 2 Q) {x : M} (hx : x ∈ Q) :
    ∃ e : ℕ, x ^ 2 ^ e = 1 := by
  obtain ⟨e, he⟩ := hQ ⟨x, hx⟩
  exact ⟨e, by simpa using congrArg Subtype.val he⟩

theorem eq_one_of_mem_two_of_cube {Q : Subgroup M} (hQ : IsPGroup 2 Q) {x : M} (hx : x ∈ Q)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨e, he⟩ := exists_pow_two_pow_eq_one hQ hx
  have h1 := orderOf_dvd_of_pow_eq_one he
  have h2 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ e) 3 :=
    Nat.Coprime.pow_left e (by norm_num)
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

end General

section Setup

variable {M : Type} [Group M] {I D T : Subgroup M} {d : M}

theorem le_inf_centralizer (hDe : IsElemAbelian 3 D) (hdD : d ∈ D) (hDI : D ≤ I) :
    D ≤ I ⊓ Subgroup.centralizer ({d} : Set M) := fun x hx =>
  Subgroup.mem_inf.mpr ⟨hDI hx, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdD⟩))⟩

theorem conj_mem_C {t : M} (hdD : d ∈ D) (htD : t ∈ Subgroup.centralizer (D : Set M))
    (htI : ∀ x ∈ I, t * x * t⁻¹ ∈ I) {c : M}
    (hc : c ∈ conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M))) :
    t * c * t⁻¹ ∈ conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M)) := by
  have htx : ∀ x ∈ D, t * x * t⁻¹ = x := fun x hx => by
    rw [(Subgroup.mem_centralizer_iff.mp htD x hx).symm, mul_inv_cancel_right]
  refine conj_mem_conjClosure (fun g hg => ?_) htx hc
  obtain ⟨hgI, hgd⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨htI g hgI, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp hgd
  have h2 := htx d hdD
  calc t * g * t⁻¹ * d = t * g * (t⁻¹ * d * t) * t⁻¹ := by group
    _ = t * g * d * t⁻¹ := by
        rw [show t⁻¹ * d * t = d by
          calc t⁻¹ * d * t = t⁻¹ * (t * d * t⁻¹) * t := by rw [h2]
            _ = d := by group]
    _ = t * (d * g) * t⁻¹ := by rw [mul_assoc t g d, h1]
    _ = (t * d * t⁻¹) * (t * g * t⁻¹) := by group
    _ = d * (t * g * t⁻¹) := by rw [h2]

end Setup

section SL2Block

variable {M : Type} [Group M] {F : Type} [Field F] [Finite F]

theorem excPlus_of_sl2Block {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {I D T : Subgroup M} {d : M} (ι : SL(2, F) →* M)
    (hι : Function.Injective ι) (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) (hdD : d ∈ D)
    (hDI : D ≤ I) (hιC : ∀ B, ι B ∈ I ⊓ Subgroup.centralizer ({d} : Set M))
    (hcomm : ∀ g ∈ I ⊓ Subgroup.centralizer ({d} : Set M),
      ∀ h ∈ I ⊓ Subgroup.centralizer ({d} : Set M), g * h * g⁻¹ * h⁻¹ ∈ ι.range)
    (hDdec : ∀ x ∈ D, ∃ (k : ℤ) (B : SL(2, F)), x = d ^ k * ι B)
    (hTD : T ≤ Subgroup.centralizer (D : Set M)) (hTI : ∀ t ∈ T, ∀ x ∈ I, t * x * t⁻¹ ∈ I) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M)) ⊓
        Subgroup.centralizer (T : Set M)) : Subgroup M) : Set M) := by
  classical
  set Cd := I ⊓ Subgroup.centralizer ({d} : Set M) with hCd
  set C := conjClosure D Cd with hC
  set H := C ⊓ Subgroup.centralizer (T : Set M) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hF4 : 4 ≤ Nat.card F := by omega
  have hcd : ∀ B, ι B * d = d * ι B := fun B =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hιC B)).2
  have hDCd : D ≤ Cd := le_inf_centralizer hDe hdD hDI
  have hDC : D ≤ C := le_conjClosure
  have hCCd : C ≤ Cd := conjClosure_le hDCd
  set N := blockSub d ι hcd with hN
  have hDN : D ≤ N := fun x hx => mem_blockSub.mpr (hDdec x hx)
  have hCN : C ≤ N := conjClosure_le_of_commutator hDN hDCd
    (fun g hg h hh => range_le_blockSub (hcomm g hg h hh))
  have hd3 : d ^ 3 = 1 := hDe.2 d hdD
  obtain ⟨x, hxD, hxd⟩ := exists_mem_not_mem_zpowers hd3 hD9
  obtain ⟨k, X, rfl⟩ := hDdec x hxD
  have hX1 : X ≠ 1 := by
    rintro rfl
    exact hxd (by rw [map_one, mul_one]; exact Subgroup.zpow_mem_zpowers d k)
  have hX3 : X ^ 3 = 1 := by
    have h1 : (d ^ k * ι X) ^ 3 = 1 := hDe.2 _ hxD
    rw [pow_three_dk_mul hcd hd3] at h1
    exact hι (h1.trans (map_one ι).symm)
  have hXns := not_isScalar2_of_cube h3 hX3 hX1
  have hιCC : ∀ a, ι a ∈ C := by
    refine Item211Lie3Proof.mem_of_normalizer hF4 h2 ι
      (fun a => mem_normalizer_conjClosure' (hιC a)) hXns hX3 (z := d ^ k)
      (fun a => zpow_commute hcd k a) ?_
    rw [zpow_commute hcd k X]
    exact hDC hxD
  have hS : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect hF4
  have hCC : ⁅C, C⁆ = ι.range := commutator_eq_range ι hS (by rintro _ ⟨a, rfl⟩; exact hιCC a)
    (fun g hg h hh => hcomm g (hCCd hg) h (hCCd hh))
  have htC : ∀ t ∈ T, ∀ c ∈ C, t * c * t⁻¹ ∈ C := fun t ht c hc =>
    conj_mem_C hdD (hTD ht) (hTI t ht) hc
  have htx : ∀ t ∈ T, ∀ y ∈ D, t * y * t⁻¹ = y := fun t ht y hy => by
    rw [(Subgroup.mem_centralizer_iff.mp (hTD ht) y hy).symm, mul_inv_cancel_right]
  have htι : ∀ t ∈ T, ∀ B, t * ι B * t⁻¹ ∈ ι.range := fun t ht B => by
    rw [← hCC]
    exact conj_mem_commutator (htC t ht) (hCC ▸ ⟨B, rfl⟩)
  have hrange : ∀ t ∈ T, ι.range.map (MulAut.conj t).toMonoidHom = ι.range := fun t ht =>
    map_conj_range_eq ι (htι t ht) (fun B => by
      have := htι t⁻¹ (T.inv_mem ht) B
      rwa [inv_inv] at this)
  have hfixB : ∀ t (ht : t ∈ T) (k : ℤ) (B : SL(2, F)), t * (d ^ k * ι B) * t⁻¹ = d ^ k * ι B →
      inducedAut ι hι t (hrange t ht) B = B := by
    intro t ht k B h
    apply hι
    rw [apply_inducedAut]
    have hdk : t * d ^ k * t⁻¹ = d ^ k := by
      rw [← conj_zpow, htx t ht d hdD]
    have e : t * (d ^ k * ι B) * t⁻¹ = (t * d ^ k * t⁻¹) * (t * ι B * t⁻¹) := by group
    rw [e, hdk] at h
    exact mul_left_cancel h
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨ky, By, rfl⟩ := hDdec y hy
  have hqH := hQH hq
  obtain ⟨eq2, heq2⟩ := exists_pow_two_pow_eq_one hQ2 hq
  obtain ⟨Bq, rfl⟩ := mem_range_of_pow_two hcd hd3 (hCN (Subgroup.mem_inf.mp hqH).1) heq2
  suffices hcomm' : Bq * By = By * Bq by
    calc ι Bq * (d ^ ky * ι By) = (ι Bq * d ^ ky) * ι By := by group
      _ = d ^ ky * (ι Bq * ι By) := by rw [zpow_commute hcd]; group
      _ = d ^ ky * (ι By * ι Bq) := by rw [← map_mul, hcomm', map_mul]
      _ = d ^ ky * ι By * ι Bq := by group
  by_cases hcase : ∃ t ∈ T, ∃ B, t * ι B * t⁻¹ ≠ ι B
  ·
    obtain ⟨t, ht, B₀, hB₀⟩ := hcase
    have hα : inducedAut ι hι t (hrange t ht) ≠ 1 := by
      intro h1
      apply hB₀
      rw [← apply_inducedAut ι hι t (hrange t ht), h1, MulAut.one_apply]
    have hfy : inducedAut ι hι t (hrange t ht) By = By :=
      hfixB t ht ky By (htx t ht _ hy)
    have hfq : inducedAut ι hι t (hrange t ht) Bq = Bq := by
      apply hι
      rw [apply_inducedAut, (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqH).2 t ht),
        mul_inv_cancel_right]
    exact commute_of_fix_of_ne_one hp hp5 hF hα hfq hfy
  ·
    push Not at hcase
    have hιH : ∀ a, ι a ∈ H := fun a => Subgroup.mem_inf.mpr ⟨hιCC a,
      Subgroup.mem_centralizer_iff.mpr fun t ht => mul_inv_eq_iff_eq_mul.mp (hcase t ht a)⟩
    have hιQ : ∀ a, ι a ∈ Subgroup.normalizer (Q : Set M) := fun a =>
      CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H (hιH a)
    let Nq : Subgroup SL(2, F) := Q.comap ι
    have hNqn : Nq.Normal := ⟨fun B hB a => by
      change ι (a * B * a⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hιQ a) _).mp hB⟩
    have hNq2 : ∀ B ∈ Nq, ∃ e : ℕ, B ^ 2 ^ e = 1 := by
      intro B hB
      obtain ⟨e, he⟩ := exists_pow_two_pow_eq_one hQ2 hB
      exact ⟨e, hι (by rw [map_pow, he, map_one])⟩
    have hcen := Item211Lie2Proof.le_center_of_normal_two hF4 Nq hNq2 (show Bq ∈ Nq from hq)
    exact Subgroup.mem_center_iff.mp hcen By |>.symm

end SL2Block

section PSL2Block

variable {M : Type} [Group M] [Finite M] {F : Type} [Field F] [Finite F]

omit [Finite M] [Finite F] in
theorem commute_of_ι_commute (h2 : (2 : F) ≠ 0) (ι : SL(2, F) →* M)
    (hιker : ∀ B, ι B = 1 ↔ B = 1 ∨ B = -1) {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1)
    {B : SL(2, F)} (h : ι B * ι X = ι X * ι B) : B * X = X * B := by
  have h1 : ι (B * X * B⁻¹ * X⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2' : B * X * B⁻¹ = X ∨ B * X * B⁻¹ = -X := by
    rcases (hιker _).mp h1 with h3 | h3
    · left
      exact mul_inv_eq_one.mp h3
    · right
      have e : B * X * B⁻¹ = B * X * B⁻¹ * X⁻¹ * X := by group
      rw [e, h3]
      apply Subtype.ext
      simp
  have h3 := conj_eq_of_conj_eq_or_neg h2 hX3 hX1 h2'
  calc B * X = B * X * B⁻¹ * B := by group
    _ = X * B := by rw [h3]

theorem centralizes_of_psl2Block (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {c : F} (hc : 3 * c ^ 2 = 1) {I D T : Subgroup M} {d : M} (ι : SL(2, F) →* M)
    (hιker : ∀ B, ι B = 1 ↔ B = 1 ∨ B = -1) (hDe : IsElemAbelian 3 D) (hdD : d ∈ D)
    (hDI : D ≤ I) (hιC : ∀ B, ι B ∈ I ⊓ Subgroup.centralizer ({d} : Set M))
    (hcomm : ∀ g ∈ I ⊓ Subgroup.centralizer ({d} : Set M),
      ∀ h ∈ I ⊓ Subgroup.centralizer ({d} : Set M), g * h * g⁻¹ * h⁻¹ ∈ ι.range)
    (hDdec : ∀ x ∈ D, ∃ (k : ℤ) (B : SL(2, F)), x = d ^ k * ι B)
    (hTD : T ≤ Subgroup.centralizer (D : Set M)) (hTI : ∀ t ∈ T, ∀ x ∈ I, t * x * t⁻¹ ∈ I)
    {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) (hXD : ι X ∈ D) :
    ∀ q ∈ inSubgroup (CFSG.pCore 2) (conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M)) ⊓
      Subgroup.centralizer (T : Set M)), q * ι X = ι X * q := by
  classical
  set Cd := I ⊓ Subgroup.centralizer ({d} : Set M) with hCd
  set C := conjClosure D Cd with hC
  set H := C ⊓ Subgroup.centralizer (T : Set M) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hcd : ∀ B, ι B * d = d * ι B := fun B =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hιC B)).2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDCd : D ≤ Cd := le_inf_centralizer hDe hdD hDI
  have hDC : D ≤ C := le_conjClosure
  have hCCd : C ≤ Cd := conjClosure_le hDCd
  set N := blockSub d ι hcd with hN
  have hDN : D ≤ N := fun x hx => mem_blockSub.mpr (hDdec x hx)
  have hCN : C ≤ N := conjClosure_le_of_commutator hDN hDCd
    (fun g hg h hh => range_le_blockSub (hcomm g hg h hh))
  have hd3 : d ^ 3 = 1 := hDe.2 d hdD
  have hXns := not_isScalar2_of_cube h3 hX3 hX1
  have hι1 : ι (-1) = 1 := (hιker _).mpr (Or.inr rfl)
  have hιCC : ∀ a, ι a ∈ C :=
    Item211Lie3Proof.mem_of_normalizer hF4 h2 ι (fun a => mem_normalizer_conjClosure' (hιC a))
      hXns hX3 (z := 1) (fun a => by rw [mul_one, one_mul]) (by rw [mul_one]; exact hDC hXD)
  have hcancel : ∀ (k : ℤ) (B : SL(2, F)) (y : M), y * d = d * y →
      (d ^ k * ι B) * y = y * (d ^ k * ι B) → ι B * y = y * ι B := by
    intro k B y hy h
    have hyk : y * d ^ k = d ^ k * y := (Commute.zpow_right (hy : Commute y d) k).eq
    have e : d ^ k * (ι B * y) = d ^ k * (y * ι B) := by
      calc d ^ k * (ι B * y) = (d ^ k * ι B) * y := by group
        _ = y * (d ^ k * ι B) := h
        _ = (y * d ^ k) * ι B := by group
        _ = d ^ k * (y * ι B) := by rw [hyk]; group
    exact mul_left_cancel e
  have hXd : ι X * d = d * ι X := hcd X
  set Z := zSL hc hX3 hX1 with hZ
  set z := ι Z with hz
  have hzC : z ∈ C := hιCC Z
  have hzd : z * d = d * z := hcd Z
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, zSL_mul_self, hι1]
  have hz1 : z ≠ 1 := by
    intro h
    obtain ⟨h1, h1'⟩ := zSL_ne hc hX3 hX1 h2
    rcases (hιker Z).mp h with h' | h'
    · exact h1 h'
    · exact h1' h'
  have hzX : z * ι X = ι X * z := by rw [hz, ← map_mul, ← map_mul, zSL_mul_comm]
  have hzD : ∀ y ∈ D, y * z = z * y := by
    intro y hy
    obtain ⟨k, By, rfl⟩ := hDdec y hy
    have hBX : By * X = X * By :=
      commute_of_ι_commute h2 ι hιker hX3 hX1 (hcancel k By (ι X) hXd (hDcomm _ hy _ hXD))
    have hBZ : By * Z = Z * By := commute_zSL_of_commute hc hX3 hX1 hBX
    calc d ^ k * ι By * z = d ^ k * ι (By * Z) := by rw [map_mul, mul_assoc]
      _ = d ^ k * ι (Z * By) := by rw [hBZ]
      _ = z * (d ^ k * ι By) := by
          rw [map_mul, ← mul_assoc, ← zpow_commute hcd k Z, mul_assoc]
  have htx : ∀ t ∈ T, ∀ y ∈ D, t * y * t⁻¹ = y := fun t ht y hy => by
    rw [(Subgroup.mem_centralizer_iff.mp (hTD ht) y hy).symm, mul_inv_cancel_right]
  have hzT : ∀ t ∈ T, t * z * t⁻¹ = z := by
    intro t ht
    set w := t * z * t⁻¹ with hw
    have hwC : w ∈ C := conj_mem_C hdD (hTD ht) (hTI t ht) hzC
    have h1 := htx t ht _ hXD
    have hwX : w * ι X = ι X * w := by
      calc w * ι X = t * z * t⁻¹ * (t * ι X * t⁻¹) := by rw [h1]
        _ = t * (z * ι X) * t⁻¹ := by group
        _ = t * (ι X * z) * t⁻¹ := by rw [hzX]
        _ = t * ι X * t⁻¹ * (t * z * t⁻¹) := by group
        _ = ι X * w := by rw [h1]
    have hw2 : w * w = 1 := by
      calc w * w = t * (z * z) * t⁻¹ := by rw [hw]; group
        _ = 1 := by rw [hz2]; group
    have hw1 : w ≠ 1 := by
      intro h
      apply hz1
      calc z = t⁻¹ * w * t := by rw [hw]; group
        _ = 1 := by rw [h]; group
    obtain ⟨W, hW⟩ := mem_range_of_pow_two hcd hd3 (hCN hwC) (e := 1) (by rw [pow_one, sq, hw2])
    have hWX : W * X = X * W := by
      refine commute_of_ι_commute h2 ι hιker hX3 hX1 ?_
      rw [hW]
      exact hwX
    have hW2 : W * W = 1 ∨ W * W = -1 := (hιker _).mp (by rw [map_mul, hW, hw2])
    rcases eq_or_of_commute_of_sq h3 hc hX3 hX1 hWX hW2 with hW' | hW' | hW' | hW'
    · exact absurd (by rw [← hW, hW', map_one]) hw1
    · exact absurd (by rw [← hW, hW', hι1]) hw1
    · rw [← hW, hW']
    · rw [← hW, hW', show -Z = -1 * Z from (neg_one_mul Z).symm, map_mul, hι1, one_mul]
  have hzH : z ∈ H := Subgroup.mem_inf.mpr ⟨hzC, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hzT t ht)⟩
  have hXH : ι X ∈ H := Subgroup.mem_inf.mpr ⟨hDC hXD, Subgroup.mem_centralizer_iff.mpr
    fun t ht => (Subgroup.mem_centralizer_iff.mp (hTD ht) _ hXD).symm⟩
  have hzN := CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hzH
  have hXN := CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hXH
  have hfix : ∀ g ∈ Q, g * z = z * g → g * ι X = ι X * g := by
    intro g hg hgz
    obtain ⟨l, Bg, hgdec⟩ := mem_blockSub.mp (hCN (Subgroup.mem_inf.mp (hQH hg)).1)
    have h1 : ι Bg * z = z * ι Bg := by
      refine hcancel l Bg z hzd ?_
      rw [← hgdec]
      exact hgz
    have h2' : Bg * Z * Bg⁻¹ = Z ∨ Bg * Z * Bg⁻¹ = -Z := by
      have e : ι (Bg * Z * Bg⁻¹ * Z⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hz, h1]
        group
      rcases (hιker _).mp e with h3' | h3'
      · left
        exact mul_inv_eq_one.mp h3'
      · right
        have e2 : Bg * Z * Bg⁻¹ = Bg * Z * Bg⁻¹ * Z⁻¹ * Z := by group
        rw [e2, h3']
        apply Subtype.ext
        simp
    have h3' := conj_eq_of_conj_zSL h2 hc hX3 hX1 h2'
    have h4 : g * ι X * g⁻¹ = ι X ∨ g * ι X * g⁻¹ = (ι X)⁻¹ := by
      have hgX : g * ι X * g⁻¹ = ι (Bg * X * Bg⁻¹) := by
        rw [hgdec, map_mul, map_mul, map_inv]
        have hdk : ι (Bg * X * Bg⁻¹) * d ^ l = d ^ l * ι (Bg * X * Bg⁻¹) :=
          zpow_commute hcd l _
        rw [map_mul, map_mul, map_inv] at hdk
        calc d ^ l * ι Bg * ι X * (d ^ l * ι Bg)⁻¹ =
            d ^ l * (ι Bg * ι X * (ι Bg)⁻¹) * (d ^ l)⁻¹ := by group
          _ = (ι Bg * ι X * (ι Bg)⁻¹) * d ^ l * (d ^ l)⁻¹ := by rw [← hdk]
          _ = ι Bg * ι X * (ι Bg)⁻¹ := by group
      rw [hgX]
      rcases h3' with h | h
      · left
        rw [h]
      · right
        rw [h, map_inv]
    rcases h4 with h4 | h4
    · exact mul_inv_eq_iff_eq_mul.mp h4
    · exfalso
      have hκ : g * ι X * g⁻¹ * (ι X)⁻¹ ∈ Q := by
        have e : g * ι X * g⁻¹ * (ι X)⁻¹ = g * (ι X * g⁻¹ * (ι X)⁻¹) := by group
        rw [e]
        exact Q.mul_mem hg ((Subgroup.mem_normalizer_iff.mp hXN _).mp (Q.inv_mem hg))
      rw [h4] at hκ
      have hX3' : (ι X) ^ 3 = 1 := by rw [← map_pow, hX3, map_one]
      have hκ3 : ((ι X)⁻¹ * (ι X)⁻¹) ^ 3 = 1 := by
        rw [← mul_inv_rev, inv_pow, ← sq, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hX3',
          one_pow, inv_one]
      have hκ1 := eq_one_of_mem_two_of_cube hQ2 hκ hκ3
      have hXi : ι X = 1 := by
        have e : ι X = (ι X) ^ 3 * ((ι X)⁻¹ * (ι X)⁻¹) := by group
        rw [e, hX3', hκ1, one_mul]
      rcases (hιker X).mp hXi with h5 | h5
      · exact hX1 h5
      · rw [h5, neg_one_pow_three] at hX3
        apply h2
        have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hX3
        simp at e
        linear_combination -e
  set α := Q.normalizerMonoidHom ⟨ι X, hXN⟩ with hα
  set τ := Q.normalizerMonoidHom ⟨z, hzN⟩ with hτ
  have hα3 : α ^ (3 ^ 1) = 1 := by
    rw [pow_one, hα, ← map_pow]
    convert map_one Q.normalizerMonoidHom
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hX3, map_one]
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    convert map_one Q.normalizerMonoidHom
    exact Subtype.ext hz2
  have hατ : α * τ = τ * α := by
    rw [hα, hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hzX.symm
  have hfix' : ∀ g : Q, τ g = g → α g = g := by
    intro g hg
    have hg' : z * (g : M) * z⁻¹ = g := congrArg Subtype.val hg
    have hgz : (g : M) * z = z * g := by
      calc (g : M) * z = z * g * z⁻¹ * z := by rw [hg']
        _ = z * g := by group
    apply Subtype.ext
    change ι X * (g : M) * (ι X)⁻¹ = g
    rw [← hfix g g.2 hgz]
    group
  have key := CFSG.GH74.GLS.Bg.TwoGroups.L26.axb hQ2 α τ 1 hα3 hτ2 hατ hfix'
  intro q hq
  have e : ι X * q * (ι X)⁻¹ = q := by
    have := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : M)) key
    exact this
  calc q * ι X = ι X * q * (ι X)⁻¹ * ι X := by rw [e]
    _ = ι X * q := by group

theorem excPlus_of_psl2Block (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {c : F} (hc : 3 * c ^ 2 = 1) {I D T : Subgroup M} {d : M} (ι : SL(2, F) →* M)
    (hιker : ∀ B, ι B = 1 ↔ B = 1 ∨ B = -1) (hDe : IsElemAbelian 3 D) (hdD : d ∈ D)
    (hDI : D ≤ I) (hιC : ∀ B, ι B ∈ I ⊓ Subgroup.centralizer ({d} : Set M))
    (hcomm : ∀ g ∈ I ⊓ Subgroup.centralizer ({d} : Set M),
      ∀ h ∈ I ⊓ Subgroup.centralizer ({d} : Set M), g * h * g⁻¹ * h⁻¹ ∈ ι.range)
    (hDdec : ∀ x ∈ D, ∃ (k : ℤ) (B : SL(2, F)), x = d ^ k * ι B)
    (hTD : T ≤ Subgroup.centralizer (D : Set M)) (hTI : ∀ t ∈ T, ∀ x ∈ I, t * x * t⁻¹ ∈ I) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M)) ⊓
        Subgroup.centralizer (T : Set M)) : Subgroup M) : Set M) := by
  have hcd : ∀ B, ι B * d = d * ι B := fun B =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hιC B)).2
  have hd3 : d ^ 3 = 1 := hDe.2 d hdD
  have hι1 : ι (-1) = 1 := (hιker _).mpr (Or.inr rfl)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqC : q ∈ conjClosure D (I ⊓ Subgroup.centralizer ({d} : Set M)) :=
    (Subgroup.mem_inf.mp (Subgroup.map_subtype_le _ hq)).1
  have hqd : q * d = d * q := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp
    (conjClosure_le (le_inf_centralizer hDe hdD hDI) hqC)).2
  obtain ⟨k, By, rfl⟩ := hDdec y hy
  have hqdk : q * d ^ k = d ^ k * q := (Commute.zpow_right (hqd : Commute q d) k).eq
  suffices hB : q * ι By = ι By * q by
    calc q * (d ^ k * ι By) = d ^ k * (q * ι By) := by rw [← mul_assoc, hqdk, mul_assoc]
      _ = d ^ k * ι By * q := by rw [hB, mul_assoc]
  by_cases hB : By = 1 ∨ By = -1
  · rw [(hιker By).mpr hB, mul_one, one_mul]
  push Not at hB
  have hB3 : By ^ 3 = 1 ∨ By ^ 3 = -1 := by
    have h1 : (d ^ k * ι By) ^ 3 = 1 := hDe.2 _ hy
    rw [pow_three_dk_mul hcd hd3] at h1
    exact (hιker _).mp h1
  obtain ⟨X, hX3, hX1, hXB⟩ : ∃ X : SL(2, F), X ^ 3 = 1 ∧ X ≠ 1 ∧ ι X = ι By := by
    rcases hB3 with h | h
    · exact ⟨By, h, hB.1, rfl⟩
    · refine ⟨-1 * By, ?_, ?_, ?_⟩
      · rw [(Commute.mul_pow (neg_one_mul_comm By) 3), neg_one_pow_three, h]
        apply Subtype.ext
        simp
      · intro h1
        apply hB.2
        calc By = (-1) * (-1 * By) := by
              apply Subtype.ext
              simp
          _ = -1 := by rw [h1, mul_one]
      · rw [map_mul, hι1, one_mul]
  have hXD : ι X ∈ D := by
    rw [hXB]
    have e : ι By = (d ^ k)⁻¹ * (d ^ k * ι By) := by group
    rw [e]
    exact D.mul_mem (D.inv_mem (D.zpow_mem hdD k)) hy
  rw [← hXB]
  exact centralizes_of_psl2Block hF4 h2 h3 hc ι hιker hDe hdD hDI hιC hcomm hDdec hTD hTI
    hX3 hX1 hXD q hq

end PSL2Block

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
