module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5GA
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5GB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5GC
public import CFSG.Quasithin.EmptyFaithful.LRed6ModLemma

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

theorem hatMod_of_b56Case1_ch615 {W : Type} [CommGroup W] [Finite W] (hsq : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup (MulAut W)} (h1 : B56Case1 J)
    (h1080 : Nat.card ↥(quasithinGenFitting J) = 1080)
    (hfix : fixV (quasithinGenFitting J) = ⊥) : MS93.S38H.HatMod (quasithinGenFitting J) := by
  set F := quasithinGenFitting J with hFdef
  have hS : LRed6.InS (Nat.card ↥F) := Or.inr (Or.inl h1080)
  obtain ⟨⟨-, hcases⟩, hP2, -⟩ := h1.2.1
  have hdir : IsIntDirect (commV F) (fixV F) ⊤ := by
    by_contra hnd
    exact LRed6.not_naturalList2_of_card_1080 h1080 (hP2.2 hnd).2
  have htop : commV F = ⊤ := by
    have h := hdir.1
    rwa [hfix, sup_bot_eq] at h
  have hB42 : B42ModulePair F (commV F) (fixV F ⊓ commV F) := by
    rcases hcases with hi | hii | ⟨m, hiii⟩ | hiv
    · exact hi.2.1
    · exfalso
      obtain ⟨-, m, K, _, _, hK, I, π, -, -, hreal, -, -⟩ := hii
      have hc := (card_eq_of_nat_realizes1527d (hreal 0)).symm
      rw [card_statedSL_three1527d, hK] at hc
      exact LRed6.sl3_num hS hc
    · exfalso
      obtain ⟨hm, π, U₁, U₂, -, hreal, -⟩ := hiii.2
      rcases LRed6.card_of_surj_sl_two (by omega) π hreal.1 with h | h
      · exact absurd (h.symm.trans h1080) (by norm_num)
      · rcases hm with rfl | rfl
        · rw [card_statedSL_four_zmod1527d] at h
          exact absurd (h.symm.trans h1080) (by norm_num)
        · rw [card_statedSL_five_zmod1527d] at h
          exact absurd (h.symm.trans h1080) (by norm_num)
    · exfalso
      obtain ⟨-, m, hm, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
      rcases LRed6.card_of_surj_sl_two (by omega) π (hreal ⟨0, by omega⟩).1 with h | h
      · exact absurd (h.symm.trans h1080) (by norm_num)
      · rcases hm with rfl | rfl
        · rw [card_statedSL_four_zmod1527d] at h
          exact absurd (h.symm.trans h1080) (by norm_num)
        · rw [card_statedSL_five_zmod1527d] at h
          exact absurd (h.symm.trans h1080) (by norm_num)
  rw [htop, hfix, bot_inf_eq] at hB42
  have h6 : TripleA6Six F ⊤ ⊥ := by
    rcases LRed6.modelShape_of_card hS hB42 with h | h | h | h | h
    · exfalso
      obtain ⟨π, hπ⟩ := h
      have hc := LRed6.card_eq_of_faithful (FFC.altDn_faithful (by norm_num)) hπ
      change Nat.card ↥F = Nat.card ↥(alternatingGroup (Fin 6)) at hc
      rw [card_alt_six_ch615] at hc
      omega
    · exfalso
      have := Vol2.Ch10.SecB.C11AmS.K8.card_of_alt7 h
      omega
    · exfalso
      have := Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four h
      omega
    · exact h
    · exfalso
      obtain ⟨K, _, _, hK, π, hπ⟩ := h
      have hG2 := card_quasithinG2_1527d hK
      rw [hK] at hG2
      have hfin : Finite ↥(CFSG.Open.quasithinG2 K) :=
        Nat.finite_of_card_ne_zero (by rw [hG2]; norm_num)
      have h1 : Nat.card ↥F ∣
          Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
        Subgroup.card_dvd_of_surjective hπ.1
      have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ∣
          Nat.card ↥(CFSG.Open.quasithinG2 K) := by
        refine Subgroup.card_dvd_of_le ?_
        rw [Subgroup.commutator_le]
        intro a ha b hb
        exact (CFSG.Open.quasithinG2 K).mul_mem
          ((CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem ha hb)
            ((CFSG.Open.quasithinG2 K).inv_mem ha)) ((CFSG.Open.quasithinG2 K).inv_mem hb)
      have h3 := h1.trans h2
      rw [hG2, h1080] at h3
      norm_num at h3
  exact MS93.S38H.HatMod.of_tripleA6Six hsq h6

theorem card_sylow_1080_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {S F : Subgroup Γ}
    (hS : IsSylowTwoOf S F) (hF : Nat.card ↥F = 1080) : Nat.card ↥S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSF, hS2, hodd⟩ := hS
  have h := Subgroup.relIndex_mul_card S F
  rw [inf_eq_left.mpr hSF, hF] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  rw [hk] at h ⊢
  change ¬ 2 ∣ S.relIndex F at hodd
  generalize S.relIndex F = r at h hodd
  have hk4 : k < 4 := by
    by_contra hk'
    have h1 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h2 : 2 ^ k ∣ 1080 := ⟨r, by rw [mul_comm]; exact h.symm⟩
    have := h1.trans h2
    norm_num at this
  interval_cases k
  · simp only [pow_zero, mul_one] at h
    omega
  · simp only [pow_one] at h
    omega
  · norm_num at h
    omega
  · rfl

theorem comm_z_of_odd_ch615 {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {zH : ↥H}
    (hcen : Subgroup.center ↥H = Subgroup.zpowers zH) (h3 : (zH : MulAut W) ^ 3 = 1)
    (hz1 : (zH : MulAut W) ≠ 1) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (H : Set (MulAut W))) (hxo : Odd (orderOf x)) :
    x * zH = zH * x := by
  rcases HatA6.conj_z_cases hcen h3 hz1 hxN with h | h
  · exact h
  set z : MulAut W := (zH : MulAut W) with hz
  have hz3 : z * z * z = 1 := by rw [← pow_three']; exact h3
  have hx2 : Commute (x * x) z := by
    show x * x * z = z * (x * x)
    calc x * x * z = x * (x * z) := by group
      _ = x * (z * z * x) := by rw [h]
      _ = (x * z) * z * x := by group
      _ = (z * z * x) * z * x := by rw [h]
      _ = z * z * (x * z) * x := by group
      _ = z * z * (z * z * x) * x := by rw [h]
      _ = (z * z * z) * (z * (x * x)) := by group
      _ = z * (x * x) := by rw [hz3, one_mul]
  obtain ⟨k, hk⟩ := hxo
  have hx : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul]
    calc x = x ^ (orderOf x) * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [hk, ← pow_succ]; ring_nf
  rw [hx]
  exact (hx2.pow_left (k + 1)).eq

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C


theorem false_of_case1_hat_nofix_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (hh : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) : False := by
  classical
  set F := quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) with hFdef
  have h1080 : Nat.card ↥F = 1080 := (HatA6.quasisimple_card hh.1.1 hh.2.1 hh.2.2.some).2
  have hout := hout_of_isHat_ch615 hh
  have hFX : F ≤ autI hU (borelL T L ⊔ H) := (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hout
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  set S := autI hU T ⊓ F with hSdef
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hTN : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)) :=
    fun x hx => hXF (autI_mono hU hTX hx)
  have hDX : autI hU D ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (hD.1.trans le_sup_left)
  have hDB : autI hU D ≤ autI hU (borelL T L) := autI_mono hU hD.1
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hDcomm : ∀ a ∈ autI hU D, ∀ b ∈ autI hU D, a * b = b * a := by
    have := (c.autI_hall_ch615 hU hD).1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(autI hU D))
    intro a ha b hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have := congrArg Subtype.val ((Commute.zpow_zpow_self g i j).eq)
    rw [hi, hj] at this
    exact this
  have hDcen : ¬ ∀ d ∈ autI hU D, ∀ x ∈ F, d * x = x * d := by
    intro h
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [h y hy k (hKF hk), mul_inv_cancel_right]
    exact hk
  have hHat := hatMod_of_b56Case1_ch615 IntMod.sq_eq_one h1 h1080 hfix
  obtain ⟨zH, hcen, h3, hfp⟩ := hHat.exists_z
  have hz1 : (zH : MulAut (IntMod (UX615 T L H) hU)) ≠ 1 := by
    intro h
    have hall : ∀ v : IntMod (UX615 T L H) hU, v = 1 := fun v => hfp v (by rw [h]; rfl)
    have h64 := hHat.card
    have : Nat.card (IntMod (UX615 T L H) hU) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => by rw [hall a, hall b]⟩, ⟨1⟩⟩
    rw [this] at h64
    norm_num at h64
  have hcen3 : ∀ z ∈ F, (∀ w ∈ F, z * w = w * z) → z ^ 3 = 1 := by
    intro z hzF hzc
    have hzc' : (⟨z, hzF⟩ : ↥F) ∈ Subgroup.center ↥F :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hzc y y.2).symm
    have h1'' : orderOf (⟨⟨z, hzF⟩, hzc'⟩ : ↥(Subgroup.center ↥F)) ∣ 3 :=
      hh.2.1 ▸ orderOf_dvd_natCard _
    have h2'' : orderOf z = orderOf (⟨⟨z, hzF⟩, hzc'⟩ : ↥(Subgroup.center ↥F)) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [← h2''] at h1''
    exact orderOf_dvd_iff_pow_eq_one.mp h1''
  have hDF : autI hU D ≤ F := fun δ hδ =>
    hHat.mem_of_comm_z hcen (hXF (hDX hδ))
      (comm_z_of_odd_ch615 hcen h3 hz1 (hXF (hDX hδ)) (hDsodd δ hδ))
  have hJS : autI hU (thompsonJ T) ≤ S := by
    refine (c.autI_thompsonJ_le_ch615 hU).trans ((Subgroup.closure_le _).mpr ?_)
    rintro y ⟨A, -, hoff, hyA⟩
    have h0 := hoff.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0
    have hle := (hHat.offender_basic (hoff.1.trans hTN) hoff.2.2.1 hoff.2.1 h0).1
    exact ⟨hoff.1 hyA, hle hyA⟩
  have hKS : autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), S⁆ :=
    (c.le_commutator_ch615 hU).trans (Subgroup.commutator_mono le_rfl hJS)
  have hS8 := card_sylow_1080_ch615 hS h1080
  obtain ⟨P, hSP, hPF, hP24, hPfix, hPZ⟩ := exists_stab_ch615 hHat hS.le hS8
  obtain ⟨φ, hφs, hker⟩ := exists_quot_hat_ch615 hh
  have hS₀ : IsSylowTwoOf ((S.subgroupOf F).map φ) ⊤ := by
    have := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS φ
    rwa [MonoidHom.range_eq_top.mpr hφs] at this
  obtain ⟨h₀, -, hh₀⟩ := CFSG.QuasithinUnique.L246C127.Even6.isSylow_D.exists_conj hS₀
  set ψ : ↥F →* Equiv.Perm (Fin 6) :=
    (MulAut.conj ((h₀ : Equiv.Perm (Fin 6))⁻¹)).toMonoidHom.comp
      ((alternatingGroup (Fin 6)).subtype.comp φ) with hψ
  have hψv : ∀ x : ↥F, ψ x = (h₀ : Equiv.Perm (Fin 6))⁻¹ * (φ x : Equiv.Perm (Fin 6)) *
      (h₀ : Equiv.Perm (Fin 6)) := fun x => by simp [hψ]
  have hψker : ∀ x y : ↥F, ψ x = ψ y → ((x⁻¹ * y : ↥F) : MulAut _) ∈ F ∧
      ∀ w ∈ F, ((x⁻¹ * y : ↥F) : MulAut _) * w = w * ((x⁻¹ * y : ↥F) : MulAut _) := by
    intro x y hxy
    have h1' : φ x = φ y := by
      rw [hψv, hψv] at hxy
      exact Subtype.ext (mul_left_cancel (mul_right_cancel hxy))
    have h2 : x⁻¹ * y ∈ Subgroup.center ↥F :=
      (hker _).mp (by rw [map_mul, map_inv, h1', inv_mul_cancel])
    exact mem_map_center_iff_ch615.mp ⟨x⁻¹ * y, h2, rfl⟩
  set img : Subgroup (MulAut (IntMod (UX615 T L H) hU)) → Subgroup (Equiv.Perm (Fin 6)) :=
    fun R => (R.subgroupOf F).map ψ with himg
  have hin : ∀ (R : Subgroup (MulAut _)) (x : ↥F), (x : MulAut _) ∈ R → ψ x ∈ img R :=
    fun R x hx => ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hout' : ∀ (R : Subgroup (MulAut _)) (y : Equiv.Perm (Fin 6)), y ∈ img R →
      ∃ x : ↥F, (x : MulAut _) ∈ R ∧ ψ x = y := by
    rintro R _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hA : ∀ R, img R ≤ alternatingGroup (Fin 6) := by
    rintro R _ ⟨x, -, rfl⟩
    rw [hψv]
    have := (φ x).2
    rw [Equiv.Perm.mem_alternatingGroup] at this ⊢
    simp [this]
  have himgS : img S = CFSG.QuasithinUnique.L246C127.Even6.D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have h1' : φ x ∈ (S.subgroupOf F).map φ := ⟨x, hx, rfl⟩
      rw [hh₀] at h1'
      obtain ⟨d, hd, hde⟩ := h1'
      rw [hψv, ← hde]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      have : (h₀ : Equiv.Perm (Fin 6))⁻¹ * ((h₀ : Equiv.Perm (Fin 6)) * (d : Equiv.Perm (Fin 6)) *
          (h₀ : Equiv.Perm (Fin 6))⁻¹) * (h₀ : Equiv.Perm (Fin 6)) = d := by group
      rw [this]
      exact Subgroup.mem_subgroupOf.mp hd
    · intro d hdD
      have hdA := CFSG.QuasithinUnique.L246C127.Even6.D_le hdD
      have h1' : MulAut.conj h₀ (⟨d, hdA⟩ : ↥(alternatingGroup (Fin 6))) ∈
          (S.subgroupOf F).map φ := by
        rw [hh₀]
        exact ⟨⟨d, hdA⟩, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
      obtain ⟨x, hx, hxe⟩ := h1'
      refine ⟨x, hx, ?_⟩
      rw [hψv, hxe]
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hDimg : ∀ R, S ≤ R → CFSG.QuasithinUnique.L246C127.Even6.D ≤ img R := by
    intro R hSR
    rw [← himgS]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (hSR (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have hsolv : ∀ R, R ≤ F → Group.IsSolvable ↥R → Group.IsSolvable ↥(img R) := by
    intro R hRF hR
    have : Group.IsSolvable ↥(R.subgroupOf F) := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRF).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (ψ.subgroupMap_surjective _)
  set PK := autI hU (oTwoUpper H) ⊔ S with hPK
  set PD := autI hU (borelL T L ⊔ T) ⊓ F with hPD
  have hSPK : S ≤ PK := le_sup_right
  have hPKF : PK ≤ F := sup_le hKF inf_le_right
  have hSPD : S ≤ PD := le_inf (inf_le_left.trans (autI_mono hU le_sup_right)) inf_le_right
  have hDPD : autI hU D ≤ PD := le_inf (autI_mono hU (hD.1.trans le_sup_left)) hDF
  have hPKs : Group.IsSolvable ↥PK := by
    have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
    have hSs : Group.IsSolvable ↥S := by
      have := hS.isPGroup.isNilpotent
      infer_instance
    exact A3.isSolvable_sup_of_le_normalizer
      (inf_le_left.trans (c.autI_le_normalizer_oTwoUpper_ch615 hU))
  have hPDs : Group.IsSolvable ↥PD := by
    have := c.isSolvable_autI_ch615 hU
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_left : PD ≤ autI hU (borelL T L ⊔ T)))
  have hnotA6 : ∀ R, R ≤ F → Group.IsSolvable ↥R → img R ≠ alternatingGroup (Fin 6) := by
    intro R hRF hR h
    have := hsolv R hRF hR
    rw [h] at this
    exact not_isSolvable_alt_six_ch615 this
  have hgen : alternatingGroup (Fin 6) ≤ img PK ⊔ img PD := by
    set R := PK ⊔ PD with hR
    have hRF : R ≤ F := sup_le hPKF inf_le_right
    have hsup : img R = img PK ⊔ img PD := by
      simp only [himg]
      rw [Subgroup.subgroupOf_sup hPKF inf_le_right, Subgroup.map_sup]
    rw [← hsup]
    have hXR : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (R : Set (MulAut _)) := by
      refine (c.autI_le_sup_ch615 hU hD).trans (sup_le (sup_le ?_ ?_) ?_)
      · exact fun δ hδ => Subgroup.le_normalizer (Subgroup.mem_sup_right (hDPD hδ))
      · intro t ht
        refine mem_normalizer_sup_ch615 (mem_normalizer_sup_ch615
          (c.autI_le_normalizer_oTwoUpper_ch615 hU ht) ?_) ?_
        · refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ⟨?_, ?_⟩
          · exact (autI hU T).mul_mem ((autI hU T).mul_mem ht hy.1) ((autI hU T).inv_mem ht)
          · exact (Subgroup.mem_normalizer_iff.mp (hTN ht) y).mp hy.2
        · refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ⟨?_, ?_⟩
          · have htY : t ∈ autI hU (borelL T L ⊔ T) := autI_mono hU le_sup_right ht
            exact (autI hU _).mul_mem ((autI hU _).mul_mem htY hy.1) ((autI hU _).inv_mem htY)
          · exact (Subgroup.mem_normalizer_iff.mp (hTN ht) y).mp hy.2
      · exact fun k hk => Subgroup.le_normalizer
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk))
    have hn : ((img R).subgroupOf (alternatingGroup (Fin 6))).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      obtain ⟨g', hg'⟩ : ∃ g' : ↥F, ψ g' = g := by
        obtain ⟨x, hx⟩ := hφs (MulAut.conj h₀ g)
        refine ⟨x, ?_⟩
        rw [hψv, hx]
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      obtain ⟨x, hxR, hxa⟩ := hout' R _ ha
      have hconj : ((g' * x * g'⁻¹ : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hXR (hFX g'.2)) x).mp hxR
      have := hin R (g' * x * g'⁻¹) hconj
      rw [map_mul, map_mul, map_inv, hg', hxa] at this
      simpa using this
    have := isSimpleGroup_alt_six_ch615
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exfalso
      have hD8 := card_D6_ch615
      have hle : CFSG.QuasithinUnique.L246C127.Even6.D ≤ img R :=
        hDimg R (hSPK.trans le_sup_left)
      have h2 : ∀ d ∈ CFSG.QuasithinUnique.L246C127.Even6.D, d = 1 := by
        intro d hd
        have h1' : (⟨d, CFSG.QuasithinUnique.L246C127.Even6.D_le hd⟩ :
            ↥(alternatingGroup (Fin 6))) ∈ (img R).subgroupOf (alternatingGroup (Fin 6)) :=
          Subgroup.mem_subgroupOf.mpr (hle hd)
        rw [hb, Subgroup.mem_bot] at h1'
        exact congrArg Subtype.val h1'
      have : CFSG.QuasithinUnique.L246C127.Even6.D = ⊥ :=
        eq_bot_iff.mpr fun d hd => Subgroup.mem_bot.mpr (h2 d hd)
      rw [this, Subgroup.card_bot] at hD8
      norm_num at hD8
    · intro g hg
      have : (⟨g, hg⟩ : ↥(alternatingGroup (Fin 6))) ∈
          (img R).subgroupOf (alternatingGroup (Fin 6)) := by rw [ht]; exact Subgroup.mem_top _
      exact this
  have hcases1 := over6_ch615 (hDimg PK hSPK) (hA PK)
  have hcases2 := over6_ch615 (hDimg PD hSPD) (hA PD)
  have hcases3 := over6_ch615 (hDimg P hSP) (hA P)
  have himgP : Nat.card ↥(img P) = 24 := by
    have hinj : Function.Injective (ψ.comp (P.subgroupOf F).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1' : ψ 1 = ψ (x : ↥F) := by rw [map_one]; exact hx.symm
      obtain ⟨-, hc⟩ := hψker 1 x h1'
      simp only [inv_one, one_mul] at hc
      have := hPZ ((x : ↥F) : MulAut _) (Subgroup.mem_subgroupOf.mp x.2) hc
      exact Subtype.ext (Subtype.ext this)
    have h1' : img P = (ψ.comp (P.subgroupOf F).subtype).range := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
    rw [h1', ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv, hP24]
  have h3' : img P = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L1} ∨
      img P = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L2} := by
    rcases hcases3 with h | h | h | h
    · rw [h, card_D6_ch615] at himgP
      norm_num at himgP
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, CFSG.QuasithinUnique.L246C127.Even6.card_alt] at himgP
      norm_num at himgP
  have h1' : img PK = CFSG.QuasithinUnique.L246C127.Even6.D ∨
      img PK = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L1} ∨
      img PK = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L2} := by
    rcases hcases1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h (hnotA6 PK hPKF hPKs)
  have h2' : img PD = CFSG.QuasithinUnique.L246C127.Even6.D ∨
      img PD = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L1} ∨
      img PD = Subgroup.closure {g | g ∈ CFSG.QuasithinUnique.L246C127.Even6.L2} := by
    rcases hcases2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h (hnotA6 PD inf_le_right hPDs)
  have hPZle : ∀ R : Subgroup (MulAut _), img R ≤ img P → ∀ x ∈ R, x ∈ F →
      ∃ p ∈ P, ∃ z : MulAut _, z ∈ F ∧ (∀ w ∈ F, z * w = w * z) ∧ x = p * z := by
    intro R hle x hxR hxF
    obtain ⟨y, hyP, hye⟩ := hout' P _ (hle (hin R ⟨x, hxF⟩ hxR))
    obtain ⟨hzF, hzc⟩ := hψker y ⟨x, hxF⟩ hye
    refine ⟨y, hyP, _, hzF, hzc, ?_⟩
    simp
  rcases eq_of_gen6_ch615 h1' h2' h3' hgen with hK | hDe
  ·
    apply c.not_fix_oTwoUpper_ch615 hU
    have hKP : autI hU (oTwoUpper H) ≤ P := by
      refine hKS.trans ?_
      rw [Subgroup.commutator_le]
      intro k hk s hs
      obtain ⟨p, hp, z, -, hzc, rfl⟩ := hPZle PK hK.le k (Subgroup.mem_sup_left hk) (hKF hk)
      have hzs := hzc s hs.2
      have e : ⁅p * z, s⁆ = ⁅p, s⁆ := by
        simp only [commutatorElement_def]
        calc p * z * s * (p * z)⁻¹ * s⁻¹ = p * (z * s) * z⁻¹ * p⁻¹ * s⁻¹ := by group
          _ = p * (s * z) * z⁻¹ * p⁻¹ * s⁻¹ := by rw [hzs]
          _ = p * s * p⁻¹ * s⁻¹ := by group
      rw [e]
      exact P.mul_mem (P.mul_mem (P.mul_mem hp (hSP hs)) (P.inv_mem hp)) (P.inv_mem (hSP hs))
    intro w hw k hk
    exact hPfix k (hKP hk) w fun s hs => hw s hs.1
  ·
    have hDPZ : ∀ δ ∈ autI hU D, ∃ p ∈ P, ∃ z : MulAut _, z ∈ F ∧ (∀ w ∈ F, z * w = w * z) ∧
        δ = p * z := fun δ hδ => hPZle PD hDe.le δ (hDPD hδ) (hDF hδ)
    have hD3 : ∀ δ ∈ autI hU D, δ ^ 3 = 1 := by
      intro δ hδ
      obtain ⟨p, hp, z, hzF, hzc, rfl⟩ := hDPZ δ hδ
      have hpz : Commute p z := (hzc p (hPF hp) : Commute z p).symm
      have hz3 : z ^ 3 = 1 := hcen3 z hzF hzc
      have hpodd : Odd (orderOf p) := by
        have h1'' : p = p * z * z⁻¹ := by group
        have hzo : Odd (orderOf z⁻¹) := by
          rw [orderOf_inv]
          exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz3)
        rw [h1'']
        have hc' : Commute (p * z) z⁻¹ := (hpz.mul_left (Commute.refl z)).inv_right
        exact Odd.of_dvd_nat ((hDsodd _ hδ).mul hzo) hc'.orderOf_mul_dvd_mul_orderOf
      have hp3 : p ^ 3 = 1 := by
        have hd24 : orderOf p ∣ 24 := hP24 ▸ Subgroup.orderOf_dvd_natCard P hp
        have : orderOf p ∣ 3 := by
          have h8 := Nat.Coprime.dvd_of_dvd_mul_left
            (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hpodd))
            (show orderOf p ∣ 2 ^ 3 * 3 by norm_num; exact hd24)
          exact h8
        exact orderOf_dvd_iff_pow_eq_one.mp this
      rw [hpz.mul_pow, hp3, hz3, one_mul]
    by_cases hDP : autI hU D ≤ P
    ·
      have hDne : ∃ δ ∈ autI hU D, δ ≠ 1 := by
        by_contra h
        push Not at h
        exact hDcen fun d hd x _ => by rw [h d hd, one_mul, mul_one]
      obtain ⟨δ, hδ, hδ1⟩ := hDne
      exact c.not_fix_hall_ch615 hU hD hδ hδ1 fun w hw =>
        hPfix δ (hDP hδ) w fun s hs => hw s hs.1
    · obtain ⟨δ₀, hδ₀, hδ₀P⟩ := Set.not_subset.mp hDP
      have hδ₀1 : δ₀ ≠ 1 := fun h => hδ₀P (h ▸ P.one_mem)
      have hDP1 : ∀ δ ∈ autI hU D, δ ∈ P → δ = 1 := by
        intro δ hδ hδP
        by_contra hδ1
        have := c.mem_zpowers_of_autI_borelL_prime_ch615 hU Nat.prime_three (by norm_num)
          (hDB hδ) (hDB hδ₀) (hD3 δ hδ) (hD3 δ₀ hδ₀) (hDcomm δ hδ δ₀ hδ₀) hδ1
        exact hδ₀P ((Subgroup.zpowers_le.mpr hδP) this)
      obtain ⟨p₀, hp₀, z₀, hz₀F, hz₀c, hδ₀e⟩ := hDPZ δ₀ hδ₀
      have hδ₀S : ∀ s ∈ S, δ₀ * s * δ₀⁻¹ ∈ S := by
        intro s hs
        obtain ⟨δ', hδ', t', ht', he⟩ := c.autI_hall_mul_ch615 hU hD s hs.1 δ₀⁻¹
          ((autI hU D).inv_mem hδ₀)
        have ht'F : t' ∈ F := by
          have : t' = δ'⁻¹ * s * δ₀⁻¹ := by rw [mul_assoc, he]; group
          rw [this]
          exact F.mul_mem (F.mul_mem (F.inv_mem (hDF hδ')) hs.2) (F.inv_mem (hDF hδ₀))
        have ht'S : t' ∈ S := ⟨ht', ht'F⟩
        have hconjP : δ₀ * s * δ₀⁻¹ ∈ P := by
          rw [hδ₀e]
          have hzs := hz₀c s hs.2
          have e : p₀ * z₀ * s * (p₀ * z₀)⁻¹ = p₀ * s * p₀⁻¹ := by
            calc p₀ * z₀ * s * (p₀ * z₀)⁻¹ = p₀ * (z₀ * s) * z₀⁻¹ * p₀⁻¹ := by group
              _ = p₀ * (s * z₀) * z₀⁻¹ * p₀⁻¹ := by rw [hzs]
              _ = p₀ * s * p₀⁻¹ := by group
          rw [e]
          exact P.mul_mem (P.mul_mem hp₀ (hSP hs)) (P.inv_mem hp₀)
        have hδδ : δ₀ * δ' = 1 := by
          refine hDP1 _ ((autI hU D).mul_mem hδ₀ hδ') ?_
          have : δ₀ * δ' = δ₀ * s * δ₀⁻¹ * t'⁻¹ := by
            calc δ₀ * δ' = δ₀ * (δ' * t') * t'⁻¹ := by group
              _ = δ₀ * (s * δ₀⁻¹) * t'⁻¹ := by rw [he]
              _ = δ₀ * s * δ₀⁻¹ * t'⁻¹ := by group
          rw [this]
          exact P.mul_mem hconjP (P.inv_mem (hSP ht'S))
        have : δ₀ * s * δ₀⁻¹ = t' := by
          calc δ₀ * s * δ₀⁻¹ = δ₀ * (s * δ₀⁻¹) := by group
            _ = δ₀ * (δ' * t') := by rw [he]
            _ = (δ₀ * δ') * t' := by group
            _ = t' := by rw [hδδ, one_mul]
        rw [this]
        exact ht'S
      have hSs : Group.IsSolvable ↥S := by
        have := hS.isPGroup.isNilpotent
        infer_instance
      obtain ⟨s₀, hs₀, z₁, hz₁, hδ₀e'⟩ := exists_mul_center_of_normalizes_ch615 hh hS le_rfl
        hS.le hSs (hDF hδ₀) hδ₀S
      obtain ⟨-, hz₁c⟩ := mem_map_center_iff_ch615.mp hz₁
      have hδ₀z : Commute δ₀ z₁ := (hz₁c δ₀ (hDF hδ₀) : Commute z₁ δ₀).symm
      have hz₁3 : z₁ ^ 3 = 1 := hcen3 z₁ (mem_map_center_iff_ch615.mp hz₁).1 hz₁c
      have hs₀1 : s₀ = 1 := by
        refine eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup hs₀ ?_
        have e : s₀ = δ₀ * z₁⁻¹ := by rw [hδ₀e']; group
        have hzo : Odd (orderOf z₁⁻¹) := by
          rw [orderOf_inv]
          exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz₁3)
        rw [e]
        exact Odd.of_dvd_nat ((hDsodd δ₀ hδ₀).mul hzo) hδ₀z.inv_right.orderOf_mul_dvd_mul_orderOf
      have hδ₀c : ∀ w ∈ F, δ₀ * w = w * δ₀ := by
        intro w hw
        rw [hδ₀e', hs₀1, one_mul]
        exact hz₁c w hw
      apply hDcen
      intro δ hδ w hw
      have hmem := c.mem_zpowers_of_autI_borelL_prime_ch615 hU Nat.prime_three (by norm_num)
        (hDB hδ₀) (hDB hδ) (hD3 δ₀ hδ₀) (hD3 δ hδ) (hDcomm δ₀ hδ₀ δ hδ) hδ₀1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact ((Commute.zpow_left (hδ₀c w hw : Commute δ₀ w) k)).eq

end Cx615C



namespace Cx615C

theorem false_of_case1_hat_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (hh : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      ↥(alternatingGroup (Fin 6))) : False := by
  by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
  · exact c.false_of_case1_hat_nofix_ch615 hU hN h1 hh hfix
  · exact c.false_of_case1_hat_fix_ch615 h432 hU hN hh hfix

end Cx615C


theorem res615EFF_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (hB56 : AsB56) : Res615EFF :=
  res615EFF_of_hat_ch615 h331 h432 hB56 fun _ _ _ _ _ _ _ _ _ c hU hN h1 hh =>
    (c.false_of_case1_hat_ch615 h432 hU hN h1 hh).elim

end CFSG.Quasithin.H13
