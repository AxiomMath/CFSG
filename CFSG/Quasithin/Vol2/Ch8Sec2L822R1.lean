module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L319
open scoped IsMulCommutative commutatorElement

@[expose] def Input822ThreeInL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      Row711M22Code T L I → ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
        ∀ y : G, y ∈ fsuM T L → orderOf y = 3 → y ∈ fsuL0 T L

@[expose] def SchurM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → ∀ (N : Subgroup X) [N.Normal],
    N ≤ Subgroup.center X → Nonempty (X ⧸ N ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
      Nat.card N ∣ 12

section Generic

variable {X : Type} [Group X]

theorem res822_le_center_of_quasisimple {N : Subgroup X} [N.Normal] (hX : CFSG.IsQuasisimple X) (hN : N ≠ ⊤) :
    N ≤ Subgroup.center X := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  rcases hX.2.1.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have hmem : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    apply hN
    have hgen : ∀ x : X, ∃ n ∈ N, ∃ z ∈ Subgroup.center X, x = n * z := by
      intro x
      have hx : π x ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      have : (QuotientGroup.mk n : X ⧸ Subgroup.center X) = QuotientGroup.mk x := hnx
      exact (QuotientGroup.eq).mp this
    have hcen : Subgroup.center (X ⧸ N) = ⊤ := by
      rw [eq_top_iff]
      intro xb _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective xb
      obtain ⟨n, hn, z, hz, rfl⟩ := hgen a
      have hmk : (QuotientGroup.mk (n * z) : X ⧸ N) = QuotientGroup.mk z := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      rw [hmk, Subgroup.mem_center_iff]
      intro g
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hz) b
    have hcommQ : commutator (X ⧸ N) = ⊥ := (commutator_eq_bot_iff_center_eq_top (G := X ⧸ N)).mpr hcen
    have hcomm : commutator X ≤ N := by
      refine Subgroup.commutator_le.mpr ?_
      intro a _ b _
      have hmem : (⁅(QuotientGroup.mk a : X ⧸ N), (QuotientGroup.mk b : X ⧸ N)⁆) ∈ commutator (X ⧸ N) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hmap : (QuotientGroup.mk ⁅a, b⁆ : X ⧸ N) = ⁅(QuotientGroup.mk a : X ⧸ N), (QuotientGroup.mk b : X ⧸ N)⁆ :=
        map_commutatorElement (QuotientGroup.mk' N) a b
      rw [hcommQ, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff _).mp (hmap.trans hmem)
    rw [hX.1.commutator_eq_top] at hcomm
    exact eq_top_iff.mpr hcomm

theorem res822_not_two_dvd_card_of_central [Finite X] {N : Subgroup X} (hN : N ≤ Subgroup.center X)
    (hO : CFSG.pCore 2 X = ⊥) : ¬ 2 ∣ Nat.card N := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
  have hzc : (z : X) ∈ Subgroup.center X := hN z.2
  let W : Subgroup X := Subgroup.zpowers (z : X)
  have hWc : W ≤ Subgroup.center X := by
    rw [Subgroup.zpowers_le]
    exact hzc
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcn : n ∈ Subgroup.center X := hWc hn
    rw [(Subgroup.mem_center_iff.mp hcn) g, mul_inv_cancel_right]
    exact hn
  have hzX : orderOf (z : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hWp : IsPGroup 2 W :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzX]; norm_num)
  have hWle : W ≤ CFSG.pCore 2 X := CFSG.LieType.BorelTits.le_pCore 2 hWn hWp
  rw [hO, le_bot_iff] at hWle
  have hz1 : (z : X) = 1 := by
    have : (z : X) ∈ W := Subgroup.mem_zpowers _
    rw [hWle, Subgroup.mem_bot] at this
    exact this
  rw [hz1, orderOf_one] at hzX
  norm_num at hzX

theorem res822_center_bot_of_simple {Y : Type} [Group Y] [IsSimpleGroup Y] (hY : ¬ ∀ a b : Y, a * b = b * a) :
    Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    apply hY
    intro a b
    have ha : a ∈ Subgroup.center Y := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem res822_nonabelian_of_not_prime {Y : Type} [Group Y] [IsSimpleGroup Y] [Finite Y]
    (hnp : ¬ (Nat.card Y).Prime) : ¬ ∀ a b : Y, a * b = b * a := by
  intro hcomm
  letI : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
  exact hnp IsSimpleGroup.prime_card

theorem res822_ker_eq_center_of_quasisimple {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hX : CFSG.IsQuasisimple X) (hYnab : ¬ ∀ a b : Y, a * b = b * a) (ψ : X →* Y)
    (hψ : Function.Surjective ψ) : ψ.ker = Subgroup.center X := by
  have hYc := res822_center_bot_of_simple hYnab
  ext x
  constructor
  · intro hx
    have hN : ψ.ker ≠ ⊤ := by
      intro htop
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨g, rfl⟩ := hψ y
      have hg : g ∈ ψ.ker := htop ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      exact hy hg
    exact res822_le_center_of_quasisimple hX hN hx
  · intro hx
    rw [MonoidHom.mem_ker]
    have hcz : ψ x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := hψ y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx g)]
    rw [hYc, Subgroup.mem_bot] at hcz
    exact hcz

end Generic

section Action

variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
theorem res822_autOn_iso {V : Type} [CommGroup V] {A : Subgroup (MulAut V)}
    (h : MathieuCode22 A ⊤ ⊥) :
    Nonempty (↥A ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.Mathieu.code22_std h
  have hinj : Function.Injective (CFSG.Quasithin.H.congrHom e) := (MulAut.congr e).injective
  have e1 : ↥A ≃* ↥(A.map (CFSG.Quasithin.H.congrHom e)) :=
    Subgroup.equivMapOfInjective A (CFSG.Quasithin.H.congrHom e) hinj
  have e2 : ↥(A.map (CFSG.Quasithin.H.congrHom e)) ≃*
      ↥((CFSG.Quasithin.H.Mathieu.rhoC10 CFSG.Quasithin.H.Mathieu.mog22
        CFSG.Quasithin.H.Mathieu.mog22_le_mog22plus).range) :=
    MulEquiv.subgroupCongr he
  have e3 : ↥((CFSG.Quasithin.H.Mathieu.rhoC10 CFSG.Quasithin.H.Mathieu.mog22
        CFSG.Quasithin.H.Mathieu.mog22_le_mog22plus).range) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 :=
    (MonoidHom.ofInjective CFSG.Quasithin.H.ModelType.rhoC10_mog22_injective).symm.trans
      CFSG.Quasithin.H.Mathieu.mog22EquivM22
  exact ⟨e1.trans (e2.trans e3)⟩

@[expose] noncomputable def res822Act {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hLV)

theorem res822Act_range {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    (res822Act hLV).range = autOn L V := by
  unfold res822Act autOn
  rw [MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr y.2
  · intro hx
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

theorem res822Act_apply {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) (v : ↥V) :
    ((res822Act hLV l : MulAut ↥V) v : G) = (l : G) * (v : G) * (l : G)⁻¹ := by
  simp [res822Act, conjAct, Subgroup.normalizerMonoidHom_apply_apply_coe]

@[expose] noncomputable def res822Act' {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  (res822Act hLV).codRestrict (autOn L V) fun l => by
    rw [← res822Act_range hLV]
    exact MonoidHom.mem_range.mpr ⟨l, rfl⟩

theorem res822_pCore_map_ker {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY3 : 3 ∣ Nat.card Y) (φ : X →* Y) (hφ : Function.Surjective φ) :
    CFSG.pCore 2 X ≤ φ.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup Y := (CFSG.pCore 2 X).map φ
  haveI : K.Normal := Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hmem : φ x ∈ K := Subgroup.mem_map_of_mem φ hx
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hP : IsPGroup 2 Y := by
      intro y
      have hy : y ∈ K := h ▸ Subgroup.mem_top y
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := X)) ⟨p, hp⟩
      refine ⟨k, ?_⟩
      have hp1 : p ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [← map_pow, hp1, map_one]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
    have h3' : 3 ∣ 2 ^ n := hn ▸ hY3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
    norm_num at this

theorem res822_pCore_le_ker' {V L : Subgroup G} [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hA : Nonempty (↥(autOn L V) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    CFSG.pCore 2 ↥L ≤ (res822Act' hLV).ker := by
  obtain ⟨eA⟩ := hA
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  haveI : IsSimpleGroup ↥(autOn L V) := MulEquiv.isSimpleGroup eA
  have hcard : Nat.card ↥(autOn L V) = 443520 := (Nat.card_congr eA.toEquiv).trans
    CFSG.Sporadic.Mathieu.card_M22
  have hY3 : 3 ∣ Nat.card ↥(autOn L V) := by rw [hcard]; norm_num
  exact res822_pCore_map_ker hY3 (res822Act' hLV) (fun y => by
    obtain ⟨l, hl⟩ : y.1 ∈ (res822Act hLV).range := by rw [res822Act_range hLV]; exact y.2
    exact ⟨l, Subtype.ext hl⟩)

end Action

section Cover

variable {G : Type} [Group G]

theorem res822Act'_surjective {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (res822Act' hLV) := by
  intro y
  have hy : (y : MulAut ↥V) ∈ (res822Act hLV).range := by
    rw [res822Act_range hLV]
    exact y.2
  obtain ⟨l, hl⟩ := hy
  exact ⟨l, Subtype.ext hl⟩

theorem res822ThreeCover_of
    (h3228 : Stmt3_2_2_eight) (h711n : Stmt7_1_1_normal) (hthree : Input822ThreeInL) (hSchur : SchurM22) :
    Res822ThreeCover := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot hn
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
    rw [hL0] at hN
    exact le_sup_left.trans hN
  have hM : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hrowM
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  have hker : CFSG.pCore 2 ↥L ≤ (res822Act' hLV).ker := res822_pCore_le_ker' hLV (res822_autOn_iso hM)
  obtain ⟨eA⟩ := res822_autOn_iso hM
  haveI hSimpM22 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  haveI hSimpA : IsSimpleGroup ↥(autOn L (fsuV T I)) := MulEquiv.isSimpleGroup eA
  have hcardA : Nat.card ↥(autOn L (fsuV T I)) = 443520 :=
    (Nat.card_congr eA.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  have hnabA : ¬ ∀ a b : ↥(autOn L (fsuV T I)), a * b = b * a :=
    res822_nonabelian_of_not_prime (by rw [hcardA]; norm_num)
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hyp.fsu.quasisimple
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L (fsuV T I)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) (res822Act' hLV) hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨l, hl⟩ := res822Act'_surjective hLV y
    exact ⟨QuotientGroup.mk l, by simp [ψ, hl]⟩
  have hkerψ : ψ.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    res822_ker_eq_center_of_quasisimple hQ hnabA ψ hψs
  have eK : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ ψ.ker ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22 :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).trans eA
  have hdvd : Nat.card ψ.ker ∣ 12 := hSchur _ hQ ψ.ker hkerψ.le ⟨eK⟩
  have hO : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := CFSG.Quasithin.B6.pCore_quotient_pCore
  have hodd : ¬ 2 ∣ Nat.card ψ.ker := res822_not_two_dvd_card_of_central hkerψ.le hO
  have hn' := hn
  unfold NoThreeInCV at hn'
  push_neg at hn'
  obtain ⟨y, hyM, hycent, hy3⟩ := hn'
  have hyL : y ∈ L := by
    have h := hthree G T L I hyp h731 h821 hc hrow hrowM hnot y hyM hy3
    rw [hL0] at h
    exact h
  let ly : ↥L := ⟨y, hyL⟩
  have hly : res822Act' hLV ly = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    change (res822Act hLV ly) v = (1 : MulAut ↥(fsuV T I)) v
    rw [MulAut.one_apply]
    apply Subtype.ext
    show ((res822Act hLV ly) v : G) = (v : G)
    rw [res822Act_apply]
    exact hycent v v.2
  have hmemK : (QuotientGroup.mk ly : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    show QuotientGroup.lift (CFSG.pCore 2 ↥L) (res822Act' hLV) hker (QuotientGroup.mk ly) = 1
    rw [QuotientGroup.lift_mk]
    exact hly
  have hmk_ne : (QuotientGroup.mk ly : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := by
    intro h1
    have hmem : ly ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff ly).mp h1
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2) ⟨ly, hmem⟩
    have hyk : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa [ly] using this
    have h3d : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
    rw [hy3] at h3d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    norm_num at this
  have hker1 : ψ.ker ≠ ⊥ := by
    intro hb
    apply hmk_ne
    have h := hmemK
    rw [hb, Subgroup.mem_bot] at h
    exact h
  have hcard1 : Nat.card ψ.ker ≠ 1 := fun h1 => hker1 (Subgroup.eq_bot_of_card_eq _ h1)
  have hcard3 : Nat.card ψ.ker = 3 := by
    generalize hk : Nat.card ψ.ker = k at hdvd hodd hcard1 ⊢
    have hle : k ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases k <;> omega
  have hIsHat : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
    refine ⟨hQ, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans eK⟩⟩
    rw [← hkerψ]
    exact hcard3
  have hS : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    unfold pCoreOf
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
  unfold CoverM22
  rw [hL0]
  refine ⟨by rw [hS]; infer_instance, ?_⟩
  exact IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hS).symm hIsHat

theorem res822_psi_of {V L : Subgroup G} [Finite G]
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hA : Nonempty (↥(autOn L V) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V), Function.Surjective ψ ∧
      ψ.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      ∀ l : ↥L, ψ (QuotientGroup.mk l) = res822Act' hLV l := by
  obtain ⟨eA⟩ := hA
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  haveI hSimpA : IsSimpleGroup ↥(autOn L V) := MulEquiv.isSimpleGroup eA
  have hcardA : Nat.card ↥(autOn L V) = 443520 :=
    (Nat.card_congr eA.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  have hnabA : ¬ ∀ a b : ↥(autOn L V), a * b = b * a :=
    res822_nonabelian_of_not_prime (by rw [hcardA]; norm_num)
  have hker : CFSG.pCore 2 ↥L ≤ (res822Act' hLV).ker := res822_pCore_le_ker' hLV ⟨eA⟩
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) (res822Act' hLV) hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨l, hl⟩ := res822Act'_surjective hLV y
    exact ⟨QuotientGroup.mk l, by simp [ψ, hl]⟩
  refine ⟨ψ, hψs, res822_ker_eq_center_of_quasisimple hQ hnabA ψ hψs, fun l => ?_⟩
  exact QuotientGroup.lift_mk (N := CFSG.pCore 2 ↥L) (φ := res822Act' hLV) hker l

end Cover

end CFSG.Quasithin.H13
