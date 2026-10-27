module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34KG
public import CFSG.Quasithin.Vol2.Ch3zCmp
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin.H13.Ch9.L34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits Ch3z D15Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isPSL_of_commute {Γ : Type} [Group Γ] {L : Subgroup Γ}
    (hL : IsPSL 3 2 2 ↥L) {z : Γ} (hz : z ∈ L) (hc : ∀ l ∈ L, z * l = l * z) : z = 1 := by
  have hS : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hL).2
  have hnab : ∃ a b : ↥L, a * b ≠ b * a :=
    Vol2Native.A312L.Seven.nonabelian_of_card_not_prime (by
      rw [Ch1Four.card_of_isPSL_three_four hL]; norm_num)
  have hZ : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center ↥L := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hzZ : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hc l l.2).symm
  rw [hZ, Subgroup.mem_bot] at hzZ
  exact congrArg Subtype.val hzZ


theorem isPSL_chiefImg {H T M₂ K U L N : Subgroup G} (hmp : MinParabolic H T M₂) (hUT : U ≤ T)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hE : IsElemAbelian 2 (chiefMod L N)) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hJ : IsPGroup 2 (kerIn M₂ H))
    (hKL : IsPSL 3 2 2 (O2Q K)) :
    IsPSL 3 2 2 ↥(chiefImg (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hHL := D14.le_normalizer_of_isNormalIn hstep.2.1 with hHLdef
  set hHN := D14.le_normalizer_of_isNormalIn hstep.1 with hHNdef
  have hUH : U ≤ H := hUT.trans hmp.isSylow.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  let ρ : ↥K →* ↥(chiefImg hHL hHN K) :=
    ((chiefPsi hHL hHN).comp (Subgroup.inclusion hKH)).codRestrict _
      (fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hker : ∀ k : ↥K, ρ k = 1 ↔ (k : G) ∈ centralizerMod L H N := by
    intro k
    have e : ρ k = 1 ↔ chiefHom hHL hHN (Subgroup.inclusion hKH k) = 1 := by
      constructor
      · intro h1
        exact Subtype.ext (congrArg Subtype.val h1 :)
      · intro h1
        exact Subtype.ext (congrArg Subtype.val h1 :)
    rw [e, chiefHom_eq_one_iff hHL hHN hNL]
    rfl
  have heq : CFSG.pCore 2 ↥K = ρ.ker := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker, hker]
      have h1 : (x : G) ∈ pCoreOf 2 K := ⟨x, by exact hx, rfl⟩
      have h2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
          (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
          (pCoreOf_isPGroup 2 K)
      exact pCoreOf_le_centralizerMod hUH hstep hE (h2 h1)
    · have hker2 : IsPGroup 2 ρ.ker := by
        rintro ⟨k, hk⟩
        have hkC : (k : G) ∈ centralizerMod L H N := (hker k).mp hk
        have hkJ := centralizerMod_le_kerIn hmp hUT hstep hnc hkC
        obtain ⟨m, hm⟩ := hJ ⟨k, hkJ⟩
        refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
        simpa using congrArg Subtype.val hm
      exact le_sSup ⟨inferInstance, hker2⟩
  have e : O2Q K ≃* ↥(chiefImg hHL hHN K) :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hKL

omit [Finite G] in
theorem isQuadratic_chief {L N A : Subgroup G} (hE : IsElemAbelian 2 (chiefMod L N))
    (hquad : ⁅⁅N, A⁆, A⁆ ≤ L) :
    @IsQuadratic ↥(chiefMod L N) (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (L : Set G)) L A) (chiefMod L N)) := by
  refine isQuadratic_autOn_of_forall hE fun s₁ hs₁ s₂ hs₂ w hw => ?_
  obtain ⟨a₁, ha₁, rfl⟩ := mem_secImg.mp hs₁
  obtain ⟨a₂, ha₂, rfl⟩ := mem_secImg.mp hs₂
  obtain ⟨n, hn, rfl⟩ := mem_secImg.mp hw
  set z : G := (a₁ : G) * n * (a₁ : G)⁻¹ * (n : G)⁻¹ with hz
  have hzc : z ∈ ⁅N, A⁆ := by
    have h1 := Subgroup.commutator_mem_commutator hn ha₁
    have h2 := ⁅N, A⁆.inv_mem h1
    rw [commutatorElement_def] at h2
    have e : ((n : G) * a₁ * (n : G)⁻¹ * (a₁ : G)⁻¹)⁻¹ = z := by rw [hz]; group
    rwa [e] at h2
  have hx : ⁅z, (a₂ : G)⁆ ∈ L := hquad (Subgroup.commutator_mem_commutator hzc ha₂)
  have hxL : (a₂ : G) * z * (a₂ : G)⁻¹ * z⁻¹ ∈ L := by
    have h2 := L.inv_mem hx
    rw [commutatorElement_def] at h2
    have e : (z * a₂ * z⁻¹ * (a₂ : G)⁻¹)⁻¹ = (a₂ : G) * z * (a₂ : G)⁻¹ * z⁻¹ := by group
    rwa [e] at h2
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := by
    rw [hz]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ a₁.2 n.2) (Subgroup.inv_mem _ a₁.2))
      (Subgroup.inv_mem _ n.2)
  have e1 : secMk (Subgroup.normalizer (L : Set G)) L a₁ *
      secMk (Subgroup.normalizer (L : Set G)) L n *
      (secMk (Subgroup.normalizer (L : Set G)) L a₁)⁻¹ *
      (secMk (Subgroup.normalizer (L : Set G)) L n)⁻¹ =
      secMk (Subgroup.normalizer (L : Set G)) L ⟨z, hzN⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  rw [e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact secMk_eq_one_iff.mpr hxL

theorem cube_of_chief (hKG : FactL34QuadThree) {H T M₂ K U : Subgroup G}
    (hmp : MinParabolic H T M₂) (hUT : U ≤ T) (hUe : IsElemAbelian 2 U) (hKH : K ≤ H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hH : H = K ⊔ T)
    (hJ : IsPGroup 2 (kerIn M₂ H)) (hKL : IsPSL 3 2 2 (O2Q K)) {L N : Subgroup G}
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) {A : Subgroup G} (hAT : A ≤ T)
    (hAe : IsElemAbelian 2 A) (hquad : ⁅⁅N, A⁆, A⁆ ≤ L) :
    ((centralizerMod L A N).relIndex A) ^ 3 ≤ (centralizerMod L N A).relIndex N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hmp.isSylow.1
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  have hUH : U ≤ H := hUT.trans hTH
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer hTK
  set hHL := D14.le_normalizer_of_isNormalIn hstep.2.1 with hHLdef
  set hHN := D14.le_normalizer_of_isNormalIn hstep.1 with hHNdef
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUH).trans hHL
  have hAH : A ≤ H := hAT.trans hTH
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans hHL
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := hAH.trans hHN
  have hE : IsElemAbelian 2 (chiefMod L N) := isElemAbelian_secImg_of_le hUe hNU
  by_cases hnt : ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L
  · have hCA : centralizerMod L A N = A := le_antisymm (centralizerMod_le_left _ _ _)
      fun b hb => ⟨hb, hAL hb, hnt b hb⟩
    rw [hCA, Subgroup.relIndex_self, one_pow]
    exact Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)
  let _ : CommGroup ↥(chiefMod L N) := commGroupOfElemAbelian hE
  have hsq : ∀ v : ↥(chiefMod L N), v ^ 2 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  set X := chiefAut H L N with hXdef
  set L' := chiefImg hHL hHN K with hL'def
  set A' := autOn (secImg (Subgroup.normalizer (L : Set G)) L A) (chiefMod L N) with hA'def
  have hXpsi : ∀ x ∈ X, ∃ h : ↥H, chiefPsi hHL hHN h = x := by
    intro x hx
    obtain ⟨h, hh⟩ := chiefHom_surjective hHL hHN ⟨x, hx⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  have hirr : XMod.IsIrrSec ↥X (⊥ : Subgroup ↥(chiefMod L N)) ⊤ := by
    refine ⟨bot_lt_iff_ne_bot.mpr ?_, fun J hJ _ _ => ?_⟩
    · intro htop
      obtain ⟨n, hnN, hnL⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hstep.2.2.1).2
      have h1 : chiefIota hNL ⟨n, hnN⟩ ∈ (⊤ : Subgroup ↥(chiefMod L N)) := Subgroup.mem_top _
      rw [htop, Subgroup.mem_bot, chiefIota_eq_one_iff] at h1
      exact hnL h1
    · exact chiefMod_irr hstep hUH J (fun x hx w hw => hJ ⟨x, hx⟩ w hw)
  have hL'X : L' ≤ X := by
    rintro _ ⟨k, -, rfl⟩
    exact chiefPsi_mem hHL hHN k
  have hXL' : X ≤ Subgroup.normalizer (L' : Set (MulAut ↥(chiefMod L N))) := by
    intro x hx
    obtain ⟨h, rfl⟩ := hXpsi x hx
    have key : ∀ g : ↥H, ∀ y ∈ L', chiefPsi hHL hHN g * y * (chiefPsi hHL hHN g)⁻¹ ∈ L' := by
      rintro g _ ⟨k, hk, rfl⟩
      refine ⟨g * k * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHK g.2) k).mp (Subgroup.mem_subgroupOf.mp hk)
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨key h y, fun hy => ?_⟩
    have := key h⁻¹ _ hy
    simpa [map_inv, mul_assoc] using this
  have hPSL : IsPSL 3 2 2 ↥L' := isPSL_chiefImg hmp hUT hstep hnc hE hKH hHK hJ hKL
  have hX2 : ∀ c ∈ X, ∃ m : ℕ, c ^ 2 ^ m ∈ L' := by
    intro c hcX
    obtain ⟨⟨h, hhH⟩, hh⟩ := hXpsi c hcX
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K T hTK
    have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := hH ▸ hhH
    rw [hmul] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hpsi : c = chiefPsi hHL hHN ⟨k, hKH hk⟩ * chiefPsi hHL hHN ⟨t, hTH ht⟩ := by
      rw [← hh, ← map_mul]
      rfl
    have hcL' : c ^ 2 ^ m ∈ L' := by
      have hnorm : (L'.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hL'X).mpr hXL'
      set π := QuotientGroup.mk' (L'.subgroupOf X) with hπ
      have hkL : (⟨chiefPsi hHL hHN ⟨k, hKH hk⟩, chiefPsi_mem hHL hHN _⟩ : ↥X) ∈
          L'.subgroupOf X := Subgroup.mem_subgroupOf.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩
      have h1 : π ⟨c, hcX⟩ = π ⟨chiefPsi hHL hHN ⟨t, hTH ht⟩, chiefPsi_mem hHL hHN _⟩ := by
        have e : (⟨c, hcX⟩ : ↥X) = ⟨chiefPsi hHL hHN ⟨k, hKH hk⟩, chiefPsi_mem hHL hHN _⟩ *
            ⟨chiefPsi hHL hHN ⟨t, hTH ht⟩, chiefPsi_mem hHL hHN _⟩ := Subtype.ext hpsi
        have hk1 : π ⟨chiefPsi hHL hHN ⟨k, hKH hk⟩, chiefPsi_mem hHL hHN _⟩ = 1 := by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hkL
        rw [e, map_mul, hk1, one_mul]
      have h2 : π (⟨c, hcX⟩ ^ 2 ^ m) = 1 := by
        rw [map_pow, h1, ← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have e : (⟨chiefPsi hHL hHN ⟨t, hTH ht⟩, chiefPsi_mem hHL hHN _⟩ : ↥X) ^ 2 ^ m = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, ← map_pow]
          have : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ m = 1 := Subtype.ext (by simpa using htm)
          rw [this, map_one]
          rfl
        rw [e]
        exact Subgroup.one_mem _
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 := h2
      rw [Subgroup.mem_subgroupOf] at h3
      simpa using h3
    exact ⟨m, hcL'⟩
  have hCX : ∀ x ∈ X, (∀ l ∈ L', x * l = l * x) → x = 1 := by
    set C : Subgroup (MulAut ↥(chiefMod L N)) :=
      X ⊓ Subgroup.centralizer (L' : Set (MulAut ↥(chiefMod L N))) with hCdef
    have hCn : (C.subgroupOf X).Normal := by
      refine ⟨fun c hc y => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      refine ⟨X.mul_mem (X.mul_mem y.2 hc.1) (X.inv_mem y.2),
        Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hl' : (y : MulAut ↥(chiefMod L N))⁻¹ * l * (y : MulAut ↥(chiefMod L N)) ∈ L' := by
        have := (Subgroup.mem_normalizer_iff''.mp (hXL' y.2) l).mp hl
        exact this
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc l * ((y : MulAut ↥(chiefMod L N)) * (c : MulAut ↥(chiefMod L N)) *
            (y : MulAut ↥(chiefMod L N))⁻¹)
          = (y : MulAut ↥(chiefMod L N)) *
            (((y : MulAut ↥(chiefMod L N))⁻¹ * l * (y : MulAut ↥(chiefMod L N))) *
              (c : MulAut ↥(chiefMod L N))) * (y : MulAut ↥(chiefMod L N))⁻¹ := by group
        _ = (y : MulAut ↥(chiefMod L N)) * ((c : MulAut ↥(chiefMod L N)) *
              ((y : MulAut ↥(chiefMod L N))⁻¹ * l * (y : MulAut ↥(chiefMod L N)))) *
              (y : MulAut ↥(chiefMod L N))⁻¹ := by rw [h1]
        _ = _ := by group
    have hC2 : IsPGroup 2 ↥C := by
      rintro ⟨c, hcX, hcC⟩
      obtain ⟨m, hcL'⟩ := hX2 c hcX
      have hcC' : c ^ 2 ^ m ∈ Subgroup.centralizer (L' : Set (MulAut ↥(chiefMod L N))) :=
        Subgroup.pow_mem _ hcC _
      have h1 : c ^ 2 ^ m = 1 := eq_one_of_isPSL_of_commute hPSL hcL' fun l hl =>
        (Subgroup.mem_centralizer_iff.mp hcC' l hl).symm
      exact ⟨m, Subtype.ext (by simpa using h1)⟩
    have hC : C = ⊥ := normal_two_eq_bot hUH hstep hE C inf_le_left hCn hC2
    intro x hx hcomm
    have hxC : x ∈ C := ⟨hx, Subgroup.mem_centralizer_iff.mpr fun l hl => (hcomm l hl).symm⟩
    rw [hC] at hxC
    exact (Subgroup.mem_bot.mp hxC)
  have hAn : secImg (Subgroup.normalizer (L : Set G)) L A ≤
      Subgroup.normalizer (chiefMod L N : Set (SecQuot (Subgroup.normalizer (L : Set G)) L)) :=
    secImg_le_normalizer_secImg hAN
  have hA'X : A' ≤ X := autOn_le_autOn _ (secImg_mono hAH)
  have hA'ne : A' ≠ ⊥ := by
    refine autOn_ne_bot_of_not_le_centralizer hAn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hAL hb⟩) hb))
      (secMk (Subgroup.normalizer (L : Set G)) L ⟨e, hNL he⟩)
      (secMk_mem_secImg (x := ⟨e, hNL he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hAL hb⟩) (y := ⟨e, hNL he⟩) this.symm
  have hA'el : IsElemAbelian2 A' := isElemAbelian2_autOn hE (isElemAbelian_secImg hAe) hAn
  have hA'q : IsQuadratic A' := isQuadratic_chief hE hquad
  have hkg := hKG ↥(chiefMod L N) hsq X hirr L' hL'X hXL' hPSL hCX hX2 A' hA'X hA'ne hA'el hA'q
  have c1 : Nat.card ↥A' = (centralizerMod L A N).relIndex A := card_autOn_secImg hAL hNL hAN
  have c2 := card_fixV_autOn_eq hE hAn
  have c3 := relIndex_secImg_fix (K := L) (E := N) (X := A) hAL hNL
  have hmul := Subgroup.relIndex_mul_card
    (chiefMod L N ⊓ Subgroup.centralizer (secImg (Subgroup.normalizer (L : Set G)) L A :
      Set (SecQuot (Subgroup.normalizer (L : Set G)) L))) (chiefMod L N)
  rw [inf_eq_left.mpr inf_le_left] at hmul
  rw [c1, c2] at hkg
  have hpos : 0 < Nat.card ↥(chiefMod L N ⊓ Subgroup.centralizer
      (secImg (Subgroup.normalizer (L : Set G)) L A :
        Set (SecQuot (Subgroup.normalizer (L : Set G)) L))) := Nat.card_pos
  rw [← c3]
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  exact hkg.trans hmul.symm.le

end CFSG.Quasithin.H13.Ch9.L34

