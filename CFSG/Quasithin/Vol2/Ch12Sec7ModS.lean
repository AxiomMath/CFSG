module

import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModO

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem w6m_inGm : (⟨2, 8, 32⟩ : Mc).Valid ∧ inGm ⟨2, 8, 32⟩ = true := by decide

theorem w6_app : ∀ v < 64, w6.app v = wV v := by decide

theorem w6_ne_id : w6 ≠ B6.id := by decide

theorem zs6_eq : zs6 = [B6.id, w6, w6.comp w6] := by decide

theorem wV_lt : ∀ v < 64, wV v < 64 := by decide

theorem wV_cube : ∀ v < 64, wV (wV (wV v)) = v := by decide

theorem sig6_wV : ∀ v < 64, sig6.app (wV v) = wV (wV (sig6.app v)) := by decide

theorem sig6_sig6 : sig6.comp sig6 = B6.id := by decide

theorem sig6_valid : sig6.Valid := by decide

theorem oVecL_iff : ∀ c < 64, c ∈ oVecL ↔ c ≠ 0 ∧ pn c ∈ oPts := by decide

theorem sig6_oVec : ∀ c ∈ oVecL, sig6.app c ∈ oVecL := by decide

theorem oPts_oVec : ∀ p ∈ oPts, p ∈ oVecL := by decide

theorem oVecL_lt : ∀ c ∈ oVecL, c < 64 := by decide

theorem wV_one : wV 1 = 2 ∧ wV 4 = 8 ∧ wV 16 = 32 := by decide

theorem w6_gm6 : w6 ∈ gm6 := gm6_of_gmList w6m_inGm

theorem eq_toB6_of_comm {B : B6} (hB : ∀ v < 64, B.app (wV v) = wV (B.app v)) :
    B = (⟨B.c0, B.c2, B.c4⟩ : Mc).toB6 := by
  obtain ⟨h1, h4, h16⟩ := wV_one
  have e1 : B.c1 = wV B.c0 := by
    have := hB 1 (by norm_num)
    rwa [h1, B6.app_c0, B6.app_c1] at this
  have e4 : B.c3 = wV B.c2 := by
    have := hB 4 (by norm_num)
    rwa [h4, B6.app_c2, B6.app_c3] at this
  have e16 : B.c5 = wV B.c4 := by
    have := hB 16 (by norm_num)
    rwa [h16, B6.app_c4, B6.app_c5] at this
  cases B
  simp only at e1 e4 e16
  simp only [Mc.toB6, e1, e4, e16]

theorem mem_gm6_of_linear {B : B6} (hv : B.Valid)
    (hlin : ∀ v < 64, B.app (wV v) = wV (B.app v))
    (hinj : ∀ u < 64, ∀ u' < 64, B.app u = B.app u' → u = u')
    (hO : ∀ c ∈ oVecL, B.app c ∈ oVecL) : B ∈ gm6 := by
  set A : Mc := ⟨B.c0, B.c2, B.c4⟩ with hA
  have hBA := eq_toB6_of_comm hlin
  obtain ⟨h0, -, h2, -, h4, -⟩ := hv
  have hAv : A.Valid := ⟨h0, h2, h4⟩
  have happ : ∀ v < 64, A.app v = B.app v := fun v hv => by
    rw [← toB6_app A hv, ← hBA]
  rw [hBA]
  refine gm6_of_gmList ⟨hAv, ?_⟩
  simp only [inGm, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq]
  refine ⟨fun p hp => ?_, ?_⟩
  · have hplt := oPts_lt p hp
    rw [happ p hplt]
    exact ((oVecL_iff _ (oVecL_lt _ (hO p (oPts_oVec p hp)))).1 (hO p (oPts_oVec p hp))).2
  · refine List.Nodup.map_on ?_ oPts_nodup
    intro p hp q hq hpq
    have hp' := hO p (oPts_oVec p hp)
    have hq' := hO q (oPts_oVec q hq)
    rw [happ p (oPts_lt p hp), happ q (oPts_lt q hq)] at hpq
    obtain ⟨c, hc, hc0, he⟩ := pn_eq_imp (oVecL_lt _ hp') (oVecL_lt _ hq')
      ((oVecL_iff _ (oVecL_lt _ hp')).1 hp').1 ((oVecL_iff _ (oVecL_lt _ hq')).1 hq').1 hpq
    rw [← happ p (oPts_lt p hp), ← happ q (oPts_lt q hq), ← Mc.app_sV hAv hc (oPts_lt p hp),
      happ _ (sV_lt_64 _ hc _ (oPts_lt p hp)), happ _ (oPts_lt q hq)] at he
    have := hinj _ (oPts_lt q hq) _ (sV_lt_64 _ hc _ (oPts_lt p hp)) he
    exact (oPts_eq_of_sV q hq p hp c hc this).symm

theorem Coding.cB_app_injective {W : Type} [CommGroup W] (C : Coding W) (a : MulAut W)
    {u u' : ℕ} (hu : u < 64) (hu' : u' < 64) (h : (C.cB a).app u = (C.cB a).app u') : u = u' := by
  rw [← C.cd_dc u hu, ← C.cd_dc u' hu', ← C.cd_apply, ← C.cd_apply] at h
  have := C.cd_injective h
  rw [← C.cd_dc u hu, ← C.cd_dc u' hu', C.cd_injective.eq_iff.2 (a.injective this)]

section Norm

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem normalizer_code
    {C : Coding W} {H : Subgroup (MulAut W)} (hC : IdentL C H) {m : MulAut W}
    (hm : ∀ a, a ∈ H ↔ m * a * m⁻¹ ∈ H) :
    C.cB m ∈ nm6 ∧ (∀ c ∈ oVecL, (C.cB m).app c ∈ oVecL) ∧
      ((∀ v < 64, (C.cB m).app (wV v) = wV ((C.cB m).app v)) ∨
        (∀ v < 64, (C.cB m).app (wV v) = wV (wV ((C.cB m).app v)))) := by
  set B := C.cB m with hB
  have hv := C.cB_valid m
  have hinj : ∀ u < 64, ∀ u' < 64, B.app u = B.app u' → u = u' :=
    fun u hu u' hu' h => C.cB_app_injective m hu hu' h
  have hHinv : ∀ b, b ∈ H → m⁻¹ * b * m ∈ H := fun b hb => (hm _).2 (by simpa [mul_assoc] using hb)
  obtain ⟨w, hw⟩ := hC.2 w6 w6_gm6
  have hwH : w ∈ H := (hC.1 w).2 (hw ▸ w6_gm6)
  have hwc : ∀ b ∈ H, w * b = b * w := fun b hb => C.cB_injective (by
    rw [C.cB_mul, C.cB_mul, hw]
    exact zs6_comm w6 (by rw [zs6_eq]; simp) _ ((hC.1 b).1 hb))
  have hzc : C.cB (m * w * m⁻¹) ∈ zs6 := by
    refine cert_center _ ((hC.1 _).1 ((hm w).1 hwH)) fun D hD => ?_
    obtain ⟨b, rfl⟩ := hC.2 D hD
    have hbH : b ∈ H := (hC.1 b).2 hD
    have hb' := hHinv b hbH
    rw [← C.cB_mul, ← C.cB_mul]
    congr 1
    calc m * w * m⁻¹ * b = m * (w * (m⁻¹ * b * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * b * m) * w) * m⁻¹ := by rw [hwc _ hb']
      _ = b * (m * w * m⁻¹) := by group
  have hz1 : C.cB (m * w * m⁻¹) ≠ B6.id := by
    intro e
    have : m * w * m⁻¹ = 1 := C.cB_eq_one.1 e
    have hw1 : w = 1 := by
      have := congrArg (fun x => m⁻¹ * x * m) this
      simpa [mul_assoc] using this
    apply w6_ne_id
    rw [← hw, hw1, C.cB_one]
  have hrel : B.comp w6 = (C.cB (m * w * m⁻¹)).comp B := by
    rw [hB, ← hw, ← C.cB_mul, ← C.cB_mul]
    congr 1
    group
  have happ : ∀ v < 64, B.app (wV v) = (C.cB (m * w * m⁻¹)).app (B.app v) := by
    intro v hv'
    have := congrArg (fun D : B6 => D.app v) hrel
    simp only [B6.app_comp, w6_app v hv'] at this
    exact this
  have hO : ∀ c ∈ oVecL, B.app c ∈ oVecL := by
    intro c hc
    have hclt := oVecL_lt c hc
    obtain ⟨g, hg, hg5, hg1, hgc⟩ := cert_fix5b c hc
    obtain ⟨gh, rfl⟩ := hC.2 g hg
    have hghH : gh ∈ H := (hC.1 gh).2 hg
    have hg'H := (hm gh).1 hghH
    have hg'5 : (C.cB (m * gh * m⁻¹)).pow 5 = B6.id := by
      rw [← C.cB_pow, show (m * gh * m⁻¹) ^ 5 = m * gh ^ 5 * m⁻¹ from conj_pow]
      rw [(C.pow_eq_one_iff gh 5).2 hg5]
      simp [C.cB_one]
    have hg'1 : C.cB (m * gh * m⁻¹) ≠ B6.id := by
      intro e
      have : m * gh * m⁻¹ = 1 := C.cB_eq_one.1 e
      have : gh = 1 := by
        have := congrArg (fun x => m⁻¹ * x * m) this
        simpa [mul_assoc] using this
      exact hg1 (by rw [this, C.cB_one])
    have hfix : (C.cB (m * gh * m⁻¹)).app (B.app c) = B.app c := by
      have e : (C.cB (m * gh * m⁻¹)).comp B = B.comp (C.cB gh) := by
        rw [hB, ← C.cB_mul, ← C.cB_mul]
        congr 1
        group
      have := congrArg (fun D : B6 => D.app c) e
      simp only [B6.app_comp] at this
      rw [this, hgc]
    have hBc0 : B.app c ≠ 0 := by
      intro h0
      have : c = 0 := hinj c hclt 0 (by norm_num) (by rw [h0, B6.app_zero])
      exact ((oVecL_iff c hclt).1 hc).1 this
    by_contra hnot
    exact cert_fix5a _ (List.mem_range.2 (B6.app_lt hv c)) hBc0 hnot _
      ((hC.1 _).1 hg'H) hg'5 hg'1 hfix
  have hz : C.cB (m * w * m⁻¹) = w6 ∨ C.cB (m * w * m⁻¹) = w6.comp w6 := by
    rw [zs6_eq] at hzc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzc
    rcases hzc with h1 | h1 | h1
    · exact absurd h1 hz1
    · exact Or.inl h1
    · exact Or.inr h1
  have hcase : (∀ v < 64, B.app (wV v) = wV (B.app v)) ∨
      (∀ v < 64, B.app (wV v) = wV (wV (B.app v))) := by
    rcases hz with h1 | h1
    · left
      intro v hv'
      rw [happ v hv', h1, w6_app _ (B6.app_lt hv v)]
    · right
      intro v hv'
      rw [happ v hv', h1, B6.app_comp, w6_app _ (B6.app_lt hv v),
        w6_app _ (wV_lt _ (B6.app_lt hv v))]
  refine ⟨?_, hO, hcase⟩
  rcases hcase with hlin | hsemi
  · exact List.mem_append.2 (Or.inl (mem_gm6_of_linear hv hlin hinj hO))
  ·
    set B' := B.comp sig6 with hB'
    have hB'v : B'.Valid := B6.comp_valid hv _
    have hlin' : ∀ v < 64, B'.app (wV v) = wV (B'.app v) := by
      intro v hv'
      have hs := B6.app_lt sig6_valid v
      rw [hB', B6.app_comp, B6.app_comp, sig6_wV v hv', hsemi _ (wV_lt _ hs), hsemi _ hs,
        wV_cube _ (B6.app_lt hv _)]
    have hinj' : ∀ u < 64, ∀ u' < 64, B'.app u = B'.app u' → u = u' := by
      intro u hu u' hu' h
      rw [hB', B6.app_comp, B6.app_comp] at h
      have := hinj _ (B6.app_lt sig6_valid u) _ (B6.app_lt sig6_valid u') h
      have e := congrArg sig6.app this
      rw [← B6.app_comp, ← B6.app_comp, sig6_sig6, B6.id_app u hu, B6.id_app u' hu'] at e
      exact e
    have hO' : ∀ c ∈ oVecL, B'.app c ∈ oVecL := fun c hc => by
      rw [hB', B6.app_comp]
      exact hO _ (sig6_oVec c hc)
    have hgm := mem_gm6_of_linear hB'v hlin' hinj' hO'
    refine List.mem_append.2 (Or.inr (List.mem_map.2 ⟨B', hgm, ?_⟩))
    rw [hB', B6.comp_assoc, sig6_sig6, B6.comp_id]

end Norm

section Six

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem gcd_three_pow_sixty (k : ℕ) : Nat.gcd (3 ^ k) 60 ∣ 3 := by
  have hg : Nat.gcd (3 ^ k) 60 ∣ 3 ^ k := Nat.gcd_dvd_left _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hg
  rw [hj]
  have hj60 : 3 ^ j ∣ 60 := hj ▸ Nat.gcd_dvd_right _ _
  have : j ≤ 1 := by
    by_contra hj2
    have : 3 ^ 2 ∣ 60 := dvd_trans (pow_dvd_pow 3 (by omega)) hj60
    norm_num at this
  exact (pow_dvd_pow 3 this).trans (by norm_num)

theorem pow_three_eq_one (h1222 : Stmt12_2_2)
    (h : Hyp1271 G T L V) {x : G} (hxL : x ∈ L) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := exists_identL_G h1222 h
  have hxN := L_le_normalizer h hxL
  set a := conjAct V ⟨x, hxN⟩ with ha
  have hagm : C.cB a ∈ gm6 := (hC.1 a).1 (conjAct_mem_autOn hxL hxN)
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (gm6_pow60 _ hagm)
  have hak : a ^ 3 ^ k = 1 := by
    rw [ha, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 ^ k = 1 :=
      Subtype.ext (by simp [hk])
    rw [this, map_one]
  have ha3 : a ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_trans
    (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hak) (orderOf_dvd_of_pow_eq_one h60))
    (gcd_three_pow_sixty k))
  have hx3N : x ^ 3 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hxN 3
  have hx3C : x ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    rw [← conjAct_eq_one' hx3N]
    have e : conjAct V ⟨x ^ 3, hx3N⟩ = a ^ 3 := by rw [ha, ← map_pow]; rfl
    rw [e, ha3]
  have hx3O : x ^ 3 ∈ pCoreOf 2 L := by
    rw [← inf_centralizer_eq_of_1222 h1222 h]
    exact Subgroup.mem_inf.2 ⟨L.pow_mem hxL 3, hx3C⟩
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hx3O⟩
  have hj' : (x ^ 3) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hk' : (x ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have hd : orderOf (x ^ 3) ∣ Nat.gcd (2 ^ j) (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one hcop] at hd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

theorem lemma12_7_2_six (h1222 : Stmt12_2_2)
    (h128 : Stmt12_2_8) (h : Hyp1271 G T L V) :
    thetaOf (Subgroup.normalizer (L : Set G)) = L := by
  apply le_antisymm
  · rw [thetaOf, Subgroup.closure_le]
    rintro x ⟨hxM, hx3⟩
    exact mem_L_of_orderOf_three h128 h hxM hx3
  · rcases h128 G T L V h.hyp with h1 | (he | hL32) | ⟨-, h3⟩
    · conv_lhs => rw [← h1]
      rw [Subgroup.closure_le]
      rintro x ⟨hxM, k, hk⟩
      have hxL : x ∈ L := by
        rw [← h1]
        exact Subgroup.subset_closure ⟨hxM, k, hk⟩
      have hx3 := pow_three_eq_one h1222 h hxL hk
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨hxM, orderOf_eq_prime hx3 hx1⟩
    · exfalso
      obtain ⟨e⟩ := he
      have h135 := dvd_card_quot_pCore h.hatA6 e
      rw [nat_card_alternatingGroup, Nat.card_fin] at h135
      exact absurd h135 (by decide)
    · exfalso
      have h135 := dvd_card_quot_pCore h.hatA6 (MulEquiv.refl _)
      rcases hL32 with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [card_of_statedPSL (by norm_num) hM] at h135
        exact absurd h135 (by decide)
      all_goals exact absurd h0 (by norm_num)
    · rw [thetaOf]
      exact h3.le

end Six

end CFSG.Quasithin.H13.S127.Mod

end
