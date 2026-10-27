module

public import CFSG.Quasithin.H13.L32AC42e
public import CFSG.Quasithin.H13.L32AC42b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (D : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]

@[expose] noncomputable def actS : ↥H ⧸ CFSG.pCore 2 ↥H →* MulAut (Hat V H W) :=
  QuotientGroup.lift _ D.act fun h hh => by
    rw [MonoidHom.mem_ker]
    refine D.act_eq_one_of_mem ?_
    rwa [← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hh

theorem actS_mk (h : ↥H) : D.actS (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) = D.act h := rfl

theorem actS_comm {K : Subgroup G} {y : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hy : y ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    {k : MulAut (Hat V H W)} (hk : k ∈ D.autOf K) : D.actS y * k = k * D.actS y := by
  obtain ⟨k', hk', rfl⟩ := hk
  have h1 := Subgroup.mem_centralizer_iff.mp hy _
    (mem_modO2Image'.mpr ⟨k', Subgroup.mem_subgroupOf.mp hk', rfl⟩)
  rw [← D.actS_mk, ← map_mul, ← map_mul, h1]

theorem fix_of_comm_irr {K : Subgroup G} {Vs : Subgroup (Hat V H W)}
    (hVinv : ∀ k ∈ D.autOf K, ∀ v ∈ Vs, k v ∈ Vs)
    (hirr : ∀ J ≤ Vs, (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = Vs) (hVs0 : Vs ≠ ⊥)
    {g : MulAut (Hat V H W)} (hg2 : g * g = 1) (hgc : ∀ k ∈ D.autOf K, g * k = k * g)
    (hgV : ∀ v ∈ Vs, g v ∈ Vs) : ∀ v ∈ Vs, g v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hP : IsPGroup 2 ↥(Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := if g = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    split_ifs with h1
    · rw [h1, orderOf_one, pow_zero]
    · rw [pow_one]
      exact orderOf_eq_prime (by rw [pow_two, hg2]) h1
  have hginv : g⁻¹ = g := (eq_inv_of_mul_eq_one_left hg2).symm
  have hst : g ∈ stabSub Vs := B5.mem_stabSub_of_inv hgV fun u hu => by rw [hginv]; exact hgV u hu
  have hgen : ∀ b ∈ Subgroup.zpowers g, ∀ m ∈ Vs, b m ∈ Vs := by
    rintro _ ⟨i, rfl⟩ m hm
    exact ((stabSub Vs).zpow_mem hst i m).mpr hm
  obtain ⟨m, hmV, hm1, hmf⟩ := B1.exists_fixed_ne_one D.hexp hP hgen hVs0
  set J := Vs ⊓ fixV (Subgroup.zpowers g) with hJ
  have hJinv : ∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J := by
    intro k hk v hv
    refine ⟨hVinv k hk v hv.1, mem_fixV.mpr fun b hb => ?_⟩
    obtain ⟨i, rfl⟩ := hb
    have hc : Commute (g ^ i) k := (Commute.zpow_left (show Commute g k from hgc k hk) i)
    rw [← MulAut.mul_apply, hc.eq, MulAut.mul_apply, mem_fixV.mp hv.2 _ ⟨i, rfl⟩]
  rcases hirr J inf_le_left hJinv with h0 | h1
  · exfalso
    have : m ∈ J := ⟨hmV, mem_fixV.mpr hmf⟩
    rw [h0, Subgroup.mem_bot] at this
    exact hm1 this
  · intro v hv
    have : v ∈ J := h1 ▸ hv
    exact mem_fixV.mp this.2 g (Subgroup.mem_zpowers g)

end TopW

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem actS_injective (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    Function.Injective D.actS := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) y
  rw [mk_pCore_eq_one_iff]
  exact C.faithful D h28 h1222 h1332 h1334 h5 hLie h hy

theorem fix_actS_eq_one (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h5 : Lemma14_7_5) {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V))
    (hx1 : x ≠ 1) {m : Hat V H I} (hm : D.actS x m = m) : m = 1 := by
  have hLz := eq_zpowers_of_card_three (C.card_lb h1222 h1332 h1334) hx hx1
  have hfix := C.fixV_autOf_l1 D h5 h1332
  have hmf : m ∈ fixV (D.autOf (l1 T L V)) := by
    rw [mem_fixV]
    rintro _ ⟨l, hl, rfl⟩
    have hlL : QuotientGroup.mk' (CFSG.pCore 2 ↥H) l ∈ modO2Image H (l1 T L V) :=
      mem_modO2Image'.mpr ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    rw [hLz] at hlL
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hlL
    have hst : D.actS x ∈ MulAction.stabilizer (MulAut (Hat V H I)) m :=
      MulAction.mem_stabilizer_iff.mpr hm
    have := MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer _ m).zpow_mem hst k)
    rw [← D.actS_mk, ← hk, map_zpow]
    exact this
  rw [hfix] at hmf
  exact Subgroup.mem_bot.mp hmf

omit D [IsMulCommutative ↥(conjClosure V H)] in
theorem pow_three_of_mem (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) : x ^ 3 = 1 := by
  have hd : orderOf x ∣ 3 := by
    rw [← C.card_lb h1222 h1332 h1334, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem actS_sq (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h5 : Lemma14_7_5) {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V))
    (hx1 : x ≠ 1) (m : Hat V H I) : D.actS x (D.actS x m) = m * D.actS x m := by
  set a := D.actS x with ha
  have ha3 : a (a (a m)) = m := by
    have h3 : a ^ 3 = 1 := by rw [ha, ← map_pow, C.pow_three_of_mem h1222 h1332 h1334 hx, map_one]
    have := congrArg (fun φ : MulAut (Hat V H I) => φ m) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfix : a (m * a m * a (a m)) = m * a m * a (a m) := by
    rw [map_mul, map_mul, ha3, mul_comm (a m * a (a m)) m, mul_assoc]
  have h1 := C.fix_actS_eq_one D h1222 h1332 h1334 h5 hx hx1 hfix
  rw [eq_inv_of_mul_eq_one_right h1]
  exact inv_eq_of_mul_eq_one_right (D.sec_sq _)

theorem actS_mem_stab (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h5 : Lemma14_7_5) {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V))
    (hx1 : x ≠ 1) (Vs : Subgroup (Hat V H I)) :
    D.actS x ∈ stabSub (Vs ⊔ Vs.map (D.actS x).toMonoidHom) := by
  set a := D.actS x with ha
  have hfwd : ∀ w ∈ Vs ⊔ Vs.map a.toMonoidHom, a w ∈ Vs ⊔ Vs.map a.toMonoidHom := by
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    obtain ⟨v, hv, rfl⟩ := hz
    rw [map_mul]
    refine mul_mem (Subgroup.mem_sup_right ⟨y, hy, rfl⟩) ?_
    show a (a v) ∈ _
    rw [C.actS_sq D h1222 h1332 h1334 h5 hx hx1]
    exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨v, hv, rfl⟩)
  have h3 : a ^ 3 = 1 := by rw [ha, ← map_pow, C.pow_three_of_mem h1222 h1332 h1334 hx, map_one]
  have hinv : a⁻¹ = a * a := by
    rw [eq_comm, ← mul_inv_eq_one, ← pow_two]
    calc a ^ 2 * a⁻¹⁻¹ = a ^ 3 := by rw [inv_inv, ← pow_succ]
      _ = 1 := h3
  refine B5.mem_stabSub_of_inv hfwd fun w hw => ?_
  rw [hinv, MulAut.mul_apply]
  exact hfwd _ (hfwd w hw)

theorem isCompl_of_stab (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x t : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) (hx1 : x ≠ 1)
    (ht : t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (htx : t * x * t⁻¹ = x⁻¹) {Vs : Subgroup (Hat V H I)} (hVs : Vs ∈ IrrPlus (D.autOf K) ⊤)
    (hst : ∀ g ∈ D.autOf T, g ∈ stabSub Vs) :
    (∀ J ≤ Vs, (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = Vs) ∧
      Vs ⊓ Vs.map (D.actS x).toMonoidHom = ⊥ ∧ Vs ⊔ Vs.map (D.actS x).toMonoidHom = ⊤ := by
  classical
  set a := D.actS x with ha
  obtain ⟨hinv, -, hlt, hirr0⟩ := mem_irrPlus_top_iff.mp hVs
  rw [C.fixV_autOf_K D, inf_bot_eq] at hlt hirr0
  have hVs0 : Vs ≠ ⊥ := fun h => (lt_irrefl _ (h ▸ hlt)).elim
  have hirr : ∀ J ≤ Vs, (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = Vs :=
    fun J hJ hJk => hirr0 J hJk bot_le hJ
  have hx3 := C.pow_three_of_mem h1222 h1332 h1334 hx
  have hLz := eq_zpowers_of_card_three (C.card_lb h1222 h1332 h1334) hx hx1
  have hac : ∀ k ∈ D.autOf K, a * k = k * a := fun k hk => D.actS_comm (C.hc hx) hk
  have hL : ∀ l : ↥H, (l : G) ∈ l1 T L V → ∃ k : ℤ, D.act l = a ^ k := by
    intro l hl
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) l ∈ modO2Image H (l1 T L V) :=
      mem_modO2Image'.mpr ⟨l, hl, rfl⟩
    rw [hLz] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨k, by rw [← D.actS_mk, ← hk, map_zpow]⟩
  have hT : ∀ g : ↥H, (g : G) ∈ T → ∃ j : ℤ, D.act g * a * (D.act g)⁻¹ = a ^ j := by
    intro g hg
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g * x * (QuotientGroup.mk' _ g)⁻¹ ∈
        modO2Image H (l1 T L V) := (C.lbNormal h1332).conj_mem x hx _
    rw [hLz] at h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨j, by rw [← D.actS_mk, ha, ← map_inv, ← map_mul, ← map_mul, ← hj, map_zpow]⟩
  have hKmem : ∀ g : ↥H, (g : G) ∈ K → D.act g ∈ D.autOf K := fun g hg => ⟨g, hg, rfl⟩
  have hTmem : ∀ g : ↥H, (g : G) ∈ T → D.act g ∈ D.autOf T := fun g hg => ⟨g, hg, rfl⟩
  have hne : Vs.map a.toMonoidHom ≠ Vs := by
    intro hxV
    have hast : a ∈ stabSub Vs := B5.mem_stabSub_of_inv
      (fun v hv => hxV ▸ (⟨v, hv, rfl⟩ : a v ∈ Vs.map a.toMonoidHom)) fun v hv => by
        rw [← hxV] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        simpa using hw
    have hVH := C.inv_of_gen D h1332 (J := Vs) (fun g hg y hy => hinv _ (hKmem g hg) y hy)
      (fun g hg y hy => by
        obtain ⟨k, hk⟩ := hL g hg
        rw [hk]
        exact ((stabSub Vs).zpow_mem hast k y).mpr hy)
      (fun g hg y hy => ((hst _ (hTmem g hg)) y).mpr hy)
    rcases D.irr Vs hVH with h0 | htop
    · exact hVs0 h0
    have ht2 : D.actS t * D.actS t = 1 := by
      rw [← map_mul, sq_eq_one_of_inv hx3 hx1 htx ht fun r hr =>
        C.mem_cent_cases h28 h1222 h1332 h1334 hLie hx hx1 ht htx hr, map_one]
    have htf := D.fix_of_comm_irr hinv hirr hVs0 ht2 (fun k hk => D.actS_comm ht hk)
      (fun v _ => htop ▸ Subgroup.mem_top _)
    have ht1 : D.actS t = 1 := MulEquiv.ext fun m => htf m (htop ▸ Subgroup.mem_top m)
    have ht1' : t = 1 :=
      C.actS_injective D h28 h1222 h1332 h1334 h5 hLie (ht1.trans (map_one _).symm)
    rw [ht1', one_mul, inv_one, mul_one] at htx
    exact hx1 (eq_one_of_cube_of_sq hx3 (by nth_rewrite 2 [htx]; exact mul_inv_cancel x))
  have hxVinv : ∀ k ∈ D.autOf K, ∀ v ∈ Vs.map a.toMonoidHom, k v ∈ Vs.map a.toMonoidHom := by
    rintro k hk _ ⟨v, hv, rfl⟩
    refine ⟨k v, hinv k hk v hv, ?_⟩
    show a (k v) = k (a v)
    rw [← MulAut.mul_apply, hac k hk, MulAut.mul_apply]
  have hcap : Vs ⊓ Vs.map a.toMonoidHom = ⊥ := by
    rcases hirr _ inf_le_left (fun k hk v hv => ⟨hinv k hk v hv.1, hxVinv k hk v hv.2⟩) with
      h0 | h1
    · exact h0
    · exfalso
      apply hne
      have hle : Vs ≤ Vs.map a.toMonoidHom := h1.symm.le.trans inf_le_right
      exact (Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective a.injective])).symm
  have hJ := C.actS_mem_stab D h1222 h1332 h1334 h5 hx hx1 Vs
  have hJH := C.inv_of_gen D h1332 (J := Vs ⊔ Vs.map a.toMonoidHom)
    (fun g hg y hy => by
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.mp hy
      rw [map_mul]
      exact mul_mem (Subgroup.mem_sup_left (hinv _ (hKmem g hg) y₁ hy₁))
        (Subgroup.mem_sup_right (hxVinv _ (hKmem g hg) y₂ hy₂)))
    (fun g hg y hy => by
      obtain ⟨k, hk⟩ := hL g hg
      rw [hk]
      exact ((stabSub _).zpow_mem hJ k y).mpr hy)
    (fun g hg y hy => by
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.mp hy
      obtain ⟨v, hv, rfl⟩ := hy₂
      obtain ⟨j, hj⟩ := hT g hg
      rw [map_mul]
      refine mul_mem (Subgroup.mem_sup_left (((hst _ (hTmem g hg)) y₁).mpr hy₁)) ?_
      have e : D.act g (a v) = (a ^ j) (D.act g v) := by
        rw [← hj, MulAut.mul_apply, MulAut.mul_apply]
        congr 2
        exact (MulEquiv.symm_apply_apply (D.act g) v).symm
      show D.act g (a v) ∈ _
      rw [e]
      exact ((stabSub _).zpow_mem hJ j _).mpr
        (Subgroup.mem_sup_left (((hst _ (hTmem g hg)) v).mpr hv)))
  rcases D.irr _ hJH with h0 | htop
  · exact absurd (le_bot_iff.mp (h0 ▸ le_sup_left)) hVs0
  · exact ⟨hirr, hcap, htop⟩

end Top42

end CFSG.Quasithin.H13.L32A.C
