module

public import CFSG.Quasithin.Vol2.Asc94.HeNB3

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow Hexa CFSG.Monster.B.Co2

namespace Step46NBAux

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G} {X L : Subgroup G} {ι : ↥X →* Equiv.Perm (Fin 64)} {ψ : ↥L →* Equiv.Perm (Fin 64)}

theorem sq_mem_zpowers_NB (hQ : Sec4QNB G A R g E F S₁ Q z) {q : G} (hq : q ∈ Q) :
    q ^ 2 ∈ zpowers z := by
  have h1 := CFSG.RankThree.Literature.FSmith.sq_mem_center hQ.extraspecial ⟨q, hq⟩
  have h2 : q ^ 2 ∈ centerIn Q := by
    refine mem_centerIn.mpr ⟨Q.pow_mem hq 2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)
    simpa using this
  rwa [hQ.center_Q] at h2

theorem exists_sylModelQE_of_step44_NB
    (h44 : Step44iiNB) {A R : Subgroup G} {g : G} {E F S₁ : Subgroup G}
    (hset : Sec4SettingNB G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ∃ (Q E' F' U : Subgroup G) (z : G) (k : ℕ), SylModel S₁ Q E' F' U z k ∧
      SylQE S₁ Q E' F' z := by
  rcases h44 G A R g E F hset S₁ hSN with ⟨_hc, P, ⟨e⟩⟩ |
    ⟨_hc, H, _, _, K, hKn, hK, hi, hC, P, ⟨e⟩⟩
  · obtain ⟨e0⟩ := nonempty_sylow_he_equiv P
    obtain ⟨Q, E', F', U, z, hm, hq⟩ :=
      exists_sylModelQE_of_equiv sylModel16 sylQE16 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 4, hm, hq⟩
  · obtain ⟨e0⟩ := nonempty_sylow_aut_equiv hKn hK hi hC P
    obtain ⟨Q, E', F', U, z, hm, hq⟩ :=
      exists_sylModelQE_of_equiv sylModel32 sylQE32 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 8, hm, hq⟩

theorem sec4Q_qe_NB
    (h44 : Step44iiNB) {A R : Subgroup G} {g : G}
    {E F S₁ Q : Subgroup G} {z : G} (hQ : Sec4QNB G A R g E F S₁ Q z) :
    Nat.card (Q ⊓ E : Subgroup G) = 16 ∧ Nat.card (Q ⊓ F : Subgroup G) = 16 ∧
      (∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z) ∧
      ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
        (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q := by
  obtain ⟨Q', E', F', U, z', k, hm, hq⟩ := exists_sylModelQE_of_step44_NB h44 hQ.setting hQ.sylowN
  have hzz : zpowers z' = zpowers z := by rw [← hm.center_X, hQ.center_S₁]
  have hQQ : Q' = Q := (hm.unique Q hQ.le hQ.card
    (fun x hx => by rw [hzz]; exact sq_mem_zpowers_NB hQ hx)
    (fun x hx y hy => by rw [hzz]; exact hQ.commutator_mem hx hy)).symm
  subst hQQ
  have hEF := HeTriNB.sup_le_of_isSylowOf_normalizer hQ.setting hQ.sylowN
  have hcard : ∀ V : Subgroup G, V ≤ S₁ → IsElemAbelian 2 V → Nat.card V = 64 →
      Nat.card (Q' ⊓ V : Subgroup G) = 16 := by
    intro V hV hVe hc
    rcases hm.uniqE V hV hVe (by rw [hc]; norm_num) with rfl | rfl
    · exact hq.cardQE
    · exact hq.cardQF
  refine ⟨hcard E (le_sup_left.trans hEF) hQ.setting.frame.elemE hQ.setting.frame.cardE,
    hcard F (le_sup_right.trans hEF) hQ.setting.frame.elemF hQ.setting.frame.cardF,
    fun x hx hc => ?_, fun Q'' hle hc hsq hcomm => ?_⟩
  · rw [← hzz]
    exact hq.cent x hx hc
  · rw [← hzz] at hsq hcomm
    exact hm.unique Q'' hle hc hsq hcomm

theorem image_Q_NB (hd : NXDatum X L ι ψ) (hQ : Sec4QNB G A R g E F S₁ Q z) (hQL : Q ≤ L)
    (hLN : L ≤ normalizer (X : Set G)) (hzX : z ∈ X) (hXS : X ≤ S₁)
    (hQX : Nat.card (Q ⊓ X : Subgroup G) = 16)
    (hcent : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z) :
    (Q.subgroupOf L).map ψ ≤ hexaM ∧ (∀ v ∈ (Q.subgroupOf L).map ψ, v * v = 1) ∧
      (∀ v ∈ (Q.subgroupOf L).map ψ, v * ι ⟨z, hzX⟩ = ι ⟨z, hzX⟩ * v) ∧
      Nat.card ((Q.subgroupOf L).map ψ) = 8 ∧
      ∀ τ ∈ hexaT, (∀ v ∈ (Q.subgroupOf L).map ψ, τ * v = v * τ) → τ = 1 ∨ τ = ι ⟨z, hzX⟩ := by
  have hzQ : zpowers z ≤ X := zpowers_le.mpr hzX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    exact hd.psi_mem q
  · rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, hd.psi_eq_one_iff]
    have h1 := CFSG.RankThree.Literature.FSmith.sq_mem_center hQ.extraspecial
      ⟨(q : G), mem_subgroupOf.mp hq⟩
    have h2 : (q : G) * q ∈ centerIn Q := by
      refine mem_centerIn.mpr ⟨Q.mul_mem (mem_subgroupOf.mp hq) (mem_subgroupOf.mp hq),
        mem_centralizer_iff.mpr fun w hw => ?_⟩
      have := congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)
      simpa [pow_two] using this
    rw [hQ.center_Q] at h2
    exact hzQ (by simpa using h2)
  · rintro _ ⟨q, hq, rfl⟩
    have hqz : (q : G) * z * (q : G)⁻¹ = z := by
      have := mem_centralizer_singleton_iff.mp (hQ.Q_le_centralizer (mem_subgroupOf.mp hq))
      rw [this, mul_inv_cancel_right]
    have h := hd.equiv q ⟨z, hzX⟩ ⟨z, hzX⟩ hqz.symm
    calc ψ q * ι ⟨z, hzX⟩ = ψ q * ι ⟨z, hzX⟩ * (ψ q)⁻¹ * ψ q := by group
      _ = ι ⟨z, hzX⟩ * ψ q := by rw [← h]
  · have h1 := Subgroup.relIndex_mul_card (H := ψ.ker) (K := Q.subgroupOf L)
    rw [Subgroup.relIndex_ker, hd.ker] at h1
    have h2 : X.subgroupOf L ⊓ Q.subgroupOf L = (X ⊓ Q).subgroupOf L := by
      ext x
      simp only [mem_inf, mem_subgroupOf]
    have h3 : Nat.card ((X ⊓ Q).subgroupOf L) = Nat.card (Q ⊓ X : Subgroup G) := by
      rw [inf_comm]
      exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hQL)).toEquiv
    have h4 : Nat.card (Q.subgroupOf L) = 2 ^ 7 := by
      rw [← hQ.card]
      exact Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv
    rw [h2, h3, hQX, h4] at h1
    omega
  · intro τ hτ hc
    rw [← hd.rangeι] at hτ
    obtain ⟨x, rfl⟩ := hτ
    have hxc : ∀ y ∈ Q, (x : G) * y = y * x := by
      intro y hy
      have hyL : y ∈ L := hQL hy
      have hy' : (⟨y, hyL⟩ : ↥L) ∈ Q.subgroupOf L := mem_subgroupOf.mpr hy
      have hmem : y * x * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hLN hyL) x).mp x.2
      have he := hd.equiv ⟨y, hyL⟩ x ⟨y * x * y⁻¹, hmem⟩ rfl
      have hcomm := hc (ψ ⟨y, hyL⟩) ⟨_, hy', rfl⟩
      have he' : ι ⟨y * x * y⁻¹, hmem⟩ = ι x := by
        rw [he, ← hcomm]
        group
      have := congrArg Subtype.val (hd.inj he')
      simp only at this
      calc (x : G) * y = y * x * y⁻¹ * y := by rw [this]
        _ = y * x := by group
    rcases eq_one_or_eq_of_mem_zpowers hQ.order_z (hcent x (hXS x.2) hxc) with h | h
    · left
      rw [show x = 1 from Subtype.ext h, map_one]
    · right
      rw [show x = ⟨z, hzX⟩ from Subtype.ext h]

theorem z_mem_of_card_NB (hQ : Sec4QNB G A R g E F S₁ Q z) {X : Subgroup G}
    (hQN : Q ≤ normalizer (X : Set G)) (hQX : Nat.card (Q ⊓ X : Subgroup G) = 16) : z ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.extraspecial.1.isNilpotent
  have hN : (X.subgroupOf Q).Normal := by
    constructor
    intro x hx q
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hQN q.2) x).mp hx
  have hne : X.subgroupOf Q ≠ ⊥ := by
    intro h
    have h1 : Nat.card (X.subgroupOf Q) = 16 := by
      rw [← hQX, inf_comm, ← inf_subgroupOf_right X Q]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h, card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyX : ((y : Q) : G) ∈ X := mem_subgroupOf.mp (mem_inf.mp y.2).1
  have hyZ : ((y : Q) : G) ∈ centerIn Q := by
    refine mem_centerIn.mpr ⟨(y : Q).2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.mp (mem_inf.mp y.2).2) ⟨w, hw⟩)
  rw [hQ.center_Q] at hyZ
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z hyZ with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy1
  · rwa [← h]

theorem step46_X_NB
    (h44 : Step44iiNB)
    (hNX : Sec4NXModelNB) (hQ : Sec4QNB G A R g E F S₁ Q z) (hX : X = E ∨ X = F) :
    X ≤ iX z X ∧
      (∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
        Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X)) ∧
      ¬ iX z X ≤ normalizer (R : Set G) ∧ Nat.card (Q ⊓ X : Subgroup G) = 16 ∧
      iX z X ≤ normalizer (Q : Set G) ∧ (∃ h : G, h * z * h⁻¹ ∈ Q ∧ h * z * h⁻¹ ≠ z) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3 := by
  have hF : HexaFacts := hexaFacts
  have hset := hQ.setting
  obtain ⟨hQE, hQF, hcent, huniq⟩ := sec4Q_qe_NB h44 hQ
  have hEF := HeTriNB.sup_le_of_isSylowOf_normalizer hset hQ.sylowN
  have hXS : X ≤ S₁ := by
    rcases hX with rfl | rfl
    exacts [le_sup_left.trans hEF, le_sup_right.trans hEF]
  have hQX : Nat.card (Q ⊓ X : Subgroup G) = 16 := by
    rcases hX with rfl | rfl
    exacts [hQE, hQF]
  have hQN : Q ≤ normalizer (X : Set G) := by
    rcases hX with rfl | rfl
    exacts [hQ.normE, hQ.normF]
  have hX64 : Nat.card X = 2 ^ 6 := by
    rcases hX with rfl | rfl
    exacts [hset.frame.cardE, hset.frame.cardF]
  have hXC : X ≤ centralizer ({z} : Set G) := hXS.trans hQ.le_centralizer
  have hzX : z ∈ X := z_mem_of_card_NB hQ hQN hQX
  have hLN : AS76b.oUpperTwoPrime (normalizer (X : Set G)) ≤ normalizer (X : Set G) :=
    oUpper_le' _
  have hQL : Q ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := le_oUpper_of_card hQN hQ.card
  obtain ⟨ι, ψ, hψs, hψk, hψe, hιR⟩ := hNX G A R g E F hset X (by
    rcases hX with rfl | rfl <;> simp)
  have hd0 : NXDatum X _ (hexaT.subtype.comp ι.toMonoidHom) (hexaM.subtype.comp ψ) :=
    { inj := hexaT.subtype_injective.comp ι.injective
      rangeι := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
          ← MonoidHom.range_eq_map, range_subtype]
      rangeψ := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψs, ← MonoidHom.range_eq_map,
          range_subtype]
      ker := by
        rw [← hψk]
        ext ℓ
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype,
          OneMemClass.coe_eq_one]
      equiv := fun ℓ x y hy => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
        exact hψe ℓ x y hy }
  set ι₀ := hexaT.subtype.comp ι.toMonoidHom with hι₀
  set ψ₀ := hexaM.subtype.comp ψ with hψ₀
  obtain ⟨hV1, hV2, hV3, hV4, -⟩ := image_Q_NB hd0 hQ hQL hLN hzX hXS hQX hcent
  have ht1 : ι₀ ⟨z, hzX⟩ ≠ 1 := by
    intro h
    rw [← map_one ι₀] at h
    exact hQ.z_ne_one (congrArg Subtype.val (hd0.inj h))
  obtain ⟨m, hm, hmt⟩ := hF.orbit _ (hd0.iota_mem _) ht1 _ hV1 hV3 hV2 (by rw [hV4]; norm_num)
  have hd1 := hd0.conj hF hm
  set ι₁ := (MulAut.conj m).toMonoidHom.comp ι₀ with hι₁
  set ψ₁ := (MulAut.conj m).toMonoidHom.comp ψ₀ with hψ₁
  have hz0 : ι₁ ⟨z, hzX⟩ = hexaT0P := by
    rw [hι₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hmt
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := image_Q_NB hd1 hQ hQL hLN hzX hXS hQX hcent
  obtain ⟨hXI, hIeq⟩ := hd1.iX_eq hF rfl hzX hz0 hXC hX64
  have hIL : iX z X ≤ AS76b.oUpperTwoPrime (normalizer (X : Set G)) := hIeq ▸ inf_le_left
  have hIC : iX z X ≤ centralizer ({z} : Set G) := hIeq ▸ inf_le_right
  have hIC0 : ∀ k : ↥(iX z X), ψ₁ (inclusion hIL k) ∈ hexaC0 := fun k =>
    (hd1.psi_mem_C0_iff hF hLN hzX hz0 _).2 (hIC k.2)
  have hC0M : hexaC0 ≤ hexaM := hF.cent ▸ inf_le_left
  have hsurj : ∀ c ∈ hexaC0, ∃ k : ↥(iX z X), ψ₁ (inclusion hIL k) = c := by
    intro c hc
    have hr : c ∈ ψ₁.range := hd1.rangeψ ▸ hC0M hc
    obtain ⟨ℓ, rfl⟩ := hr
    have hℓC := (hd1.psi_mem_C0_iff hF hLN hzX hz0 ℓ).1 hc
    have hℓI : (ℓ : G) ∈ iX z X := by
      rw [hIeq]
      exact ⟨ℓ.2, hℓC⟩
    exact ⟨⟨ℓ, hℓI⟩, rfl⟩
  obtain ⟨e0⟩ := hF.iso
  let ψI : ↥(iX z X) →* ↥hexaC0 := (ψ₁.comp (inclusion hIL)).codRestrict hexaC0 hIC0
  have hV1C0 : (Q.subgroupOf _).map ψ₁ ≤ hexaC0 := by
    intro v hv
    rw [← hF.cent]
    refine ⟨hW1 hv, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hz0]
    exact hW3 v hv
  have hVN : (Q.subgroupOf _).map ψ₁ = hexaN0 := by
    refine Subgroup.eq_of_le_of_card_ge (hF.normalE8 _ hV1C0 hW2 fun τ hτ hc => ?_) ?_
    · rw [← hz0]
      exact hW5 τ hτ hc
    · rw [hF.cardN, hW4]
  have hIQ : iX z X ≤ normalizer (Q : Set G) := by
    intro ℓ hℓ
    have hℓL := hIL hℓ
    have hℓC := hIC hℓ
    have hψℓ : ψ₁ ⟨ℓ, hℓL⟩ ∈ normalizer (hexaN0 : Set (Equiv.Perm (Fin 64))) :=
      hF.normN (hIC0 ⟨ℓ, hℓ⟩)
    have hS : Q.map (MulAut.conj ℓ).toMonoidHom ≤ S₁ := by
      rintro _ ⟨q, hq, rfl⟩
      have hqL := hQL hq
      have hmem : ψ₁ (⟨ℓ, hℓL⟩ * ⟨q, hqL⟩ * (⟨ℓ, hℓL⟩)⁻¹) ∈ hexaN0 := by
        rw [map_mul, map_mul, map_inv]
        refine (mem_normalizer_iff.mp hψℓ _).mp ?_
        rw [← hVN]
        exact ⟨⟨q, hqL⟩, mem_subgroupOf.mpr hq, rfl⟩
      rw [← hVN] at hmem
      obtain ⟨q', hq', he⟩ := hmem
      have h1 : ψ₁ ((⟨ℓ, hℓL⟩ * ⟨q, hqL⟩ * (⟨ℓ, hℓL⟩)⁻¹) * q'⁻¹) = 1 := by
        rw [map_mul, ← he, map_inv, mul_inv_cancel]
      have h2 := (hd1.psi_eq_one_iff _).1 h1
      simp only [coe_mul, coe_inv] at h2
      have h3 : ℓ * q * ℓ⁻¹ = ℓ * q * ℓ⁻¹ * (q' : G)⁻¹ * q' := by group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h3]
      exact S₁.mul_mem (hXS h2) (hQ.le (mem_subgroupOf.mp hq'))
    have hcard : Nat.card (Q.map (MulAut.conj ℓ).toMonoidHom) = 2 ^ 7 := by
      rw [card_map_of_injective (MulAut.conj ℓ).injective, hQ.card]
    have heq := huniq _ hS hcard (by
      rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow]
      exact conj_mem_zpowers hℓC (sq_mem_zpowers_NB hQ hq)) (by
      rintro _ ⟨q, hq, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h := conj_mem_zpowers hℓC (hQ.commutator_mem hq hv)
      convert h using 1
      group)
    exact mem_normalizer_iff_map_conj_eq.mpr heq
  have hN0C : hexaN0 ≤ hexaC0 := hVN ▸ hV1C0
  have h3 : ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3 := by
    intro c hcI hcQ hc3
    have hcL := hIL hcI
    set y : ↥hexaC0 := ⟨ψ₁ ⟨c, hcL⟩, hIC0 ⟨c, hcI⟩⟩ with hydef
    have hc3' : (⟨c, hcL⟩ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) ^ 3 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, ← hc3, pow_orderOf_eq_one]; rfl)
    have hy3 : y ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hydef]
      simp only
      rw [← map_pow, hc3', map_one]
      rfl)
    have hy1 : y ≠ 1 := by
      intro h
      have h1 : ψ₁ ⟨c, hcL⟩ = 1 := congrArg Subtype.val h
      have hcX := (hd1.psi_eq_one_iff _).1 h1
      have hc2 : c ^ 2 = 1 := by
        have := (Subgroup.mem_carrier.mp (show c ∈ X from hcX))
        rcases hX with rfl | rfl
        · exact hset.frame.elemE.2 c hcX
        · exact hset.frame.elemF.2 c hcX
      have := orderOf_dvd_of_pow_eq_one hc2
      rw [hc3] at this
      exact absurd this (by norm_num)
    have hcomm : ∀ n : ↥hexaN0, y * ⟨n, hN0C n.2⟩ = ⟨n, hN0C n.2⟩ * y := by
      intro n
      have hn : (n : Equiv.Perm (Fin 64)) ∈ (Q.subgroupOf _).map ψ₁ := by
        rw [hVN]
        exact n.2
      obtain ⟨q, hq, hqe⟩ := hn
      apply Subtype.ext
      show ψ₁ ⟨c, hcL⟩ * (n : Equiv.Perm (Fin 64)) = (n : Equiv.Perm (Fin 64)) * ψ₁ ⟨c, hcL⟩
      rw [← hqe, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hcQ _ (mem_subgroupOf.mp hq)).symm
    have hle := card_centralizer_le_six (e0 y) (by rw [← map_pow, hy3, map_one])
      (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hy1)
    let f : ↥hexaN0 → {w // e0 y * w = w * e0 y} := fun n =>
      ⟨e0 ⟨n, hN0C n.2⟩, by rw [← map_mul, ← map_mul, hcomm n]⟩
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun w => (e0.symm w.1 : ↥hexaC0)) hab
      simp only [f, MulEquiv.symm_apply_apply] at this
      exact Subtype.ext (congrArg (fun w : ↥hexaC0 => (w : Equiv.Perm (Fin 64))) this)
    have h8 := Nat.card_le_card_of_injective f hf
    rw [hF.cardN, Nat.card_eq_fintype_card, Fintype.card_subtype] at h8
    omega
  refine ⟨hXI, ⟨e0.toMonoidHom.comp ψI, ?_, ?_⟩, ?_, hQX, hIQ, ?_, h3⟩
  ·
    intro y
    obtain ⟨c, rfl⟩ := e0.surjective y
    obtain ⟨k, hk⟩ := hsurj c c.2
    refine ⟨k, ?_⟩
    have hkc : ψI k = c := Subtype.ext hk
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hkc]
  ·
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, mem_subgroupOf, ← OneMemClass.coe_eq_one]
    change ψ₁ (inclusion hIL k) = 1 ↔ _
    rw [hd1.psi_eq_one_iff]
    rfl
  ·
    intro hIR
    obtain ⟨g0, hg0, r, hr, hn⟩ := hF.move m hm
    obtain ⟨k, hk⟩ := hsurj g0 hg0
    have hk' : m⁻¹ * g0 * m = ψ₀ (inclusion hIL k) := by
      rw [← hk, hψ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hrT : r ∈ ι₀.range := hd0.rangeι ▸ hF.R0T hr
    obtain ⟨x, rfl⟩ := hrT
    have hxR : (x : G) ∈ R := (hιR x).2 hr
    have hkN : (k : G) ∈ normalizer (R : Set G) := hIR k.2
    have hwR : (k : G) * x * (k : G)⁻¹ ∈ R := (mem_normalizer_iff.mp hkN x).mp hxR
    have hwX : (k : G) * x * (k : G)⁻¹ ∈ X := (mem_normalizer_iff.mp (hLN (hIL k.2)) x).mp x.2
    have he := hd0.equiv (inclusion hIL k) x ⟨_, hwX⟩ rfl
    have hmem : ι₀ ⟨_, hwX⟩ ∈ hexaR0 := (hιR ⟨_, hwX⟩).1 hwR
    rw [he, ← hk'] at hmem
    exact hn hmem
  ·
    obtain ⟨a, ha, x, hx, hc1, hc2, m', hm', hmc⟩ := hF.fuse
    rw [← hVN] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    have hxT : x ∈ ι₁.range := hd1.rangeι ▸ hx
    obtain ⟨x', rfl⟩ := hxT
    have hqN : (q : G) ∈ normalizer (X : Set G) := hLN q.2
    have hy1 : (q : G) * x' * (q : G)⁻¹ ∈ X := (mem_normalizer_iff.mp hqN x').mp x'.2
    have hyX : (q : G) * x' * (q : G)⁻¹ * (x' : G)⁻¹ ∈ X := X.mul_mem hy1 (X.inv_mem x'.2)
    have hyQ : (q : G) * x' * (q : G)⁻¹ * (x' : G)⁻¹ ∈ Q := by
      have hxN : (x' : G) ∈ normalizer (Q : Set G) := hIQ (hXI x'.2)
      have h1 : (x' : G) * (q : G)⁻¹ * (x' : G)⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp hxN _).mp (Q.inv_mem (mem_subgroupOf.mp hq))
      have h2 : (q : G) * x' * (q : G)⁻¹ * (x' : G)⁻¹ =
          q * ((x' : G) * (q : G)⁻¹ * (x' : G)⁻¹) := by
        group
      rw [h2]
      exact Q.mul_mem (mem_subgroupOf.mp hq) h1
    have hιy : ι₁ ⟨_, hyX⟩ = ψ₁ q * ι₁ x' * (ψ₁ q)⁻¹ * (ι₁ x')⁻¹ := by
      have he := hd1.equiv q x' ⟨_, hy1⟩ rfl
      rw [← he, ← map_inv, ← map_mul]
      rfl
    have hm'r : m' ∈ ψ₁.range := hd1.rangeψ ▸ hm'
    obtain ⟨ℓ', rfl⟩ := hm'r
    have hw : (ℓ' : G) * ((q : G) * x' * (q : G)⁻¹ * (x' : G)⁻¹) * (ℓ' : G)⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hLN ℓ'.2) _).mp hyX
    have he' := hd1.equiv ℓ' ⟨_, hyX⟩ ⟨_, hw⟩ rfl
    rw [hιy, hmc, ← hz0] at he'
    have hzeq := congrArg Subtype.val (hd1.inj he')
    simp only at hzeq
    refine ⟨(ℓ' : G)⁻¹, ?_, ?_⟩
    · rw [inv_inv, ← hzeq]
      convert hyQ using 1
      group
    · intro hz'
      apply hc2
      have h1 : (q : G) * x' * (q : G)⁻¹ * (x' : G)⁻¹ = z := by
        rw [← hz']
        rw [inv_inv, ← hzeq]
        group
      rw [← hιy, ← hz0]
      exact congrArg ι₁ (Subtype.ext h1)

end Step46NBAux

theorem step46NB_of
    (h44 : Step44iiNB)
    (hNX : Sec4NXModelNB) :
    ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
      Sec4QNB G A R g E F S₁ Q z →
        (∀ X ∈ ({E, F} : Set (Subgroup G)),
          X ≤ iX z X ∧
          (∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
            Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X)) ∧
          ¬ iX z X ≤ normalizer (R : Set G) ∧
          Nat.card (Q ⊓ X : Subgroup G) = 16) ∧
        iX z E ⊔ iX z F ≤ normalizer (Q : Set G) := by
  intro G _ _ A R g E F S₁ Q z hQ
  have hE := Step46NBAux.step46_X_NB h44 hNX hQ (X := E) (Or.inl rfl)
  have hF := Step46NBAux.step46_X_NB h44 hNX hQ (X := F) (Or.inr rfl)
  refine ⟨fun X hX => ?_, sup_le hE.2.2.2.2.1 hF.2.2.2.2.1⟩
  rcases hX with rfl | hX
  · exact ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1⟩
  · rw [Set.mem_singleton_iff] at hX
    subst hX
    exact ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1⟩

end CFSG.ComponentClassification.AS81
