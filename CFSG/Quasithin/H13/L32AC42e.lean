module

public import CFSG.Quasithin.H13.L32AC42d
public import CFSG.Quasithin.Background.F918N1

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem autOf_K_ne_bot : D.autOf K ≠ ⊥ := by
  intro h
  apply C.hKI
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have h1 : D.act ⟨k, C.hKH hk⟩ = 1 := by
    have : D.act ⟨k, C.hKH hk⟩ ∈ D.autOf K := ⟨⟨k, C.hKH hk⟩, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have h2 := I.inv_mem ((D.act_eq_one_iff_comm _).mp h1 u hu)
  rwa [show ((k : G) * u * k⁻¹ * u⁻¹)⁻¹ = ⁅u, k⁆ by rw [commutatorElement_def]; group] at h2

theorem fixV_autOf_K : fixV (D.autOf K) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (I.subgroupOf (conjClosure V H)) m
  rw [Subgroup.mem_bot, A6.A6Mod.secMk_eq_one_iff]
  refine C.mem_of_comm u.2 fun k hk => ?_
  have h1 := mem_fixV.mp hm (D.act ⟨k, C.hKH hk⟩) ⟨⟨k, C.hKH hk⟩, hk, rfl⟩
  rw [D.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff,
    Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] at h1
  exact h1

theorem act_comm {y k : ↥H} (hy : (y : G) ∈ l1 T L V) (hk : (k : G) ∈ K) :
    D.act y * D.act k = D.act k * D.act y := by
  have h1 : D.act (y * k * y⁻¹ * k⁻¹) = 1 := D.act_eq_one_of_mem (C.comm_mem hy hk)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc D.act y * D.act k = (D.act y * D.act k * (D.act y)⁻¹ * (D.act k)⁻¹) *
      (D.act k * D.act y) := by group
    _ = D.act k * D.act y := by rw [h1, one_mul]

theorem fixV_autOf_l1 (h5 : Lemma14_7_5) (h1332 : Stmt13_3_2) :
    fixV (D.autOf (l1 T L V)) = ⊥ := by
  have hHL := C.hHL h1332
  have hinv : ∀ h : ↥H, ∀ y ∈ fixV (D.autOf (l1 T L V)), D.act h y ∈ fixV (D.autOf (l1 T L V)) := by
    intro h y hy
    rw [mem_fixV]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : (h⁻¹ * l * h : ↥H) ∈ (l1 T L V).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hHL (H.inv_mem h.2)) l).mp hl
      simpa using this
    have h1 := mem_fixV.mp hy _ ⟨_, hl', rfl⟩
    calc D.act l (D.act h y) = D.act h (D.act (h⁻¹ * l * h) y) := by
          rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
          exact (MulEquiv.apply_symm_apply (D.act h) _).symm
      _ = D.act h y := by rw [h1]
  rcases D.irr (fixV (D.autOf (l1 T L V))) hinv with h0 | htop
  · exact h0
  · exfalso
    obtain ⟨-, -, -, -, -, -, h57⟩ := h5 G T L V H C.S (C.lbNormal h1332)
    refine absurd D.hWU (not_lt_of_ge ?_)
    rw [← h57]
    refine sup_le ?_ C.hV₁I
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : D.act ⟨l, C.hl1H hl⟩ = 1 := by
      refine MulEquiv.ext fun m => ?_
      have : m ∈ fixV (D.autOf (l1 T L V)) := by rw [htop]; exact Subgroup.mem_top m
      exact mem_fixV.mp this _ ⟨⟨l, C.hl1H hl⟩, hl, rfl⟩
    have h3 := I.inv_mem ((D.act_eq_one_iff_comm _).mp h1 u hu)
    rwa [show ((l : G) * u * l⁻¹ * u⁻¹)⁻¹ = ⁅u, l⁆ by rw [commutatorElement_def]; group] at h3

theorem faithful (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) (h : ↥H)
    (hh : D.act h = 1) : (h : G) ∈ pCoreOf 2 H := by
  classical
  set Kb := modO2Image H K with hKb
  set Lb := modO2Image H (l1 T L V) with hLb
  set N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    D.act.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hN
  have hNn : N.Normal := (MonoidHom.normal_ker D.act).map _ (QuotientGroup.mk'_surjective _)
  have hKbN : Kb.Normal := C.kbNormal
  have hLbN : Lb.Normal := C.lbNormal h1332
  have hmemN : ∀ g : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) g ∈ N → D.act g = 1 := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := hg
    have h1 : ((g'⁻¹ * g : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [← mk_pCore_eq_one_iff, map_mul, map_inv, hgg, inv_mul_cancel]
    have h2 := D.act_eq_one_of_mem h1
    rwa [map_mul, map_inv, MonoidHom.mem_ker.mp hg', inv_one, one_mul] at h2
  have hNK : N ⊓ Kb = ⊥ := by
    obtain ⟨hqX, -, -⟩ := kst_props C.hK C.hq hLie
    have hZ := C.center_eq_bot h28 h1222 h1332 h1334 hLie
    have : ((N ⊓ Kb).subgroupOf Kb).Normal := (Subgroup.normal_inf_normal N Kb).subgroupOf Kb
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqX
      ((N ⊓ Kb).subgroupOf Kb) with hc | ht
    · rw [eq_bot_iff]
      intro z hz
      have h1 := hc (show (⟨z, hz.2⟩ : ↥Kb) ∈ (N ⊓ Kb).subgroupOf Kb from hz)
      rw [hZ, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    · exfalso
      apply C.autOf_K_ne_bot D
      rw [eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      have hkb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) k ∈ Kb := mem_modO2Image'.mpr ⟨k, hk, rfl⟩
      have h1 : (⟨_, hkb⟩ : ↥Kb) ∈ (N ⊓ Kb).subgroupOf Kb := by
        rw [ht]
        exact Subgroup.mem_top _
      exact Subgroup.mem_bot.mpr (hmemN k h1.1)
  have hNL : N ⊓ Lb = ⊥ := by
    have hcard := C.card_lb h1222 h1332 h1334
    have hdvd : Nat.card ↥(N ⊓ Lb) ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle : Lb ≤ N := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_right : N ⊓ Lb ≤ Lb) (h3.trans hcard.symm).ge
        rw [← this]
        exact inf_le_left
      apply D.top_ne_bot
      rw [eq_bot_iff, ← C.fixV_autOf_l1 D h5 h1332]
      intro m _
      rw [mem_fixV]
      rintro _ ⟨l, hl, rfl⟩
      rw [hmemN l (hle (mem_modO2Image'.mpr ⟨l, hl, rfl⟩)), MulAut.one_apply]
  have hNC : N ≤ Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓
      Subgroup.centralizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine le_inf (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    · exact (Subgroup.commute_of_normal_of_disjoint N Kb hNn hKbN (disjoint_iff.mpr hNK) x y hx
        hy).eq.symm
    · exact (Subgroup.commute_of_normal_of_disjoint N Lb hNn hLbN (disjoint_iff.mpr hNL) x y hx
        hy).eq.symm
  have hNL' : N ≤ Lb := by
    have := C.cent_inf_cent h28 h1222 h1332 h1334 hLie
    rw [← hKb, ← hLb] at this
    exact this ▸ hNC
  have hNb : N = ⊥ := by
    rw [eq_bot_iff, ← hNL]
    exact le_inf le_rfl hNL'
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈ N := ⟨h, hh, rfl⟩
  rw [hNb, Subgroup.mem_bot] at h1
  exact (mk_pCore_eq_one_iff h).mp h1

theorem pCoreOf_range (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    pCoreOf 2 D.act.range = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Hat V H I)) := TopW.finite_mulAut
  set R := pCoreOf 2 D.act.range with hR
  set P : Subgroup ↥H := R.comap D.act with hP
  have hPn : P.Normal := by
    refine ⟨fun p hp g => ?_⟩
    show D.act (g * p * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 D.act.range ⟨g, rfl⟩) _).mp
      hp
  have hP2 : IsPGroup 2 ↥P := by
    intro p
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 D.act.range) ⟨D.act p, p.2⟩
    have h1 : D.act ((p : ↥H) ^ 2 ^ a) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 H)
      ⟨_, C.faithful D h28 h1222 h1332 h1334 h5 hLie _ h1⟩
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have hb' : (((p : ↥H) : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hPO : P ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hPn, hP2⟩
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨g, hg⟩ := (pCoreOf_le 2 _) hr
  have hgP : g ∈ P := by
    show D.act g ∈ R
    rw [hg]
    exact hr
  have hgO : (g : G) ∈ pCoreOf 2 H := by
    have := hPO hgP
    rwa [← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at this
  rw [Subgroup.mem_bot, ← hg]
  exact D.act_eq_one_of_mem hgO

theorem inv_of_gen (h1332 : Stmt13_3_2) {J : Subgroup (Hat V H I)}
    (hK : ∀ g : ↥H, (g : G) ∈ K → ∀ y ∈ J, D.act g y ∈ J)
    (hL : ∀ g : ↥H, (g : G) ∈ l1 T L V → ∀ y ∈ J, D.act g y ∈ J)
    (hT : ∀ g : ↥H, (g : G) ∈ T → ∀ y ∈ J, D.act g y ∈ J) :
    ∀ h : ↥H, ∀ y ∈ J, D.act h y ∈ J := by
  intro h y hy
  have hh : (h : G) ∈ K ⊔ (l1 T L V ⊔ T) := by rw [← C.hHeq]; exact h.2
  obtain ⟨k, hk, z, hz, hkz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    ((sup_le C.hl1H C.hTH).trans C.hKn)).mp hh
  obtain ⟨l, hl, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (Setting147.T_le_N_l1 C.S h1332)).mp hz
  have e : h = ⟨k, C.hKH hk⟩ * (⟨l, C.hl1H hl⟩ * ⟨t, C.hTH ht⟩) := Subtype.ext hkz
  rw [e, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  exact hK _ hk _ (hL _ hl _ (hT _ ht _ hy))

theorem faithVT (h1332 : Stmt13_3_2) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hTL : T ≤ Subgroup.normalizer (l1 T L V : Set G)) {B : Subgroup G}
    (hBR : B ≤ pCoreOf 2 (l1 T L V ⊔ T)) {VT : Subgroup (Hat V H I)}
    (hKs : D.autOf K ≤ stabSub VT) (hTs : D.autOf T ≤ stabSub VT) (hVT : VT ≠ ⊥) :
    D.autOf B ⊓ centSub VT = ⊥ := by
  classical
  let J : Subgroup (Hat V H I) :=
    Subgroup.closure {y | ∃ l : ↥H, (l : G) ∈ l1 T L V ∧ ∃ v ∈ VT, y = D.act l v}
  have hgen : ∀ g : ↥H, ((g : G) ∈ K ∨ (g : G) ∈ l1 T L V ∨ (g : G) ∈ T) →
      ∀ y ∈ J, D.act g y ∈ J := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, v, hv, rfl⟩ := hy
      rcases hg with hgK | hgL | hgT
      · have hc := C.act_comm D hl hgK
        have hv' : D.act g v ∈ VT := ((hKs ⟨g, hgK, rfl⟩) v).mpr hv
        have e : D.act g (D.act l v) = D.act l (D.act g v) := by
          rw [← MulAut.mul_apply, ← hc, MulAut.mul_apply]
        rw [e]
        exact Subgroup.subset_closure ⟨l, hl, _, hv', rfl⟩
      · have e : D.act g (D.act l v) = D.act (g * l) v := by rw [map_mul, MulAut.mul_apply]
        rw [e]
        exact Subgroup.subset_closure ⟨g * l, mul_mem hgL hl, v, hv, rfl⟩
      · have hl' : ((g * l * g⁻¹ : ↥H) : G) ∈ l1 T L V :=
          (Subgroup.mem_normalizer_iff.mp (hTL hgT) _).mp hl
        have hv' : D.act g v ∈ VT := ((hTs ⟨g, hgT, rfl⟩) v).mpr hv
        have e : D.act g (D.act l v) = D.act (g * l * g⁻¹) (D.act g v) := by
          rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
          congr 2
          exact (MulEquiv.symm_apply_apply (D.act g) v).symm
        rw [e]
        exact Subgroup.subset_closure ⟨_, hl', _, hv', rfl⟩
    | one => rw [map_one]; exact J.one_mem
    | mul a b _ _ ha hb => rw [map_mul]; exact J.mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact J.inv_mem ha
  have hJH := C.inv_of_gen D h1332 (fun g hg => hgen g (Or.inl hg))
    (fun g hg => hgen g (Or.inr (Or.inl hg))) (fun g hg => hgen g (Or.inr (Or.inr hg)))
  have hVTJ : VT ≤ J := fun v hv => Subgroup.subset_closure
    ⟨1, (l1 T L V).one_mem, v, hv, by rw [map_one, MulAut.one_apply]⟩
  rcases D.irr J hJH with h0 | h1
  · exact absurd (le_bot_iff.mp (h0 ▸ hVTJ)) hVT
  rw [eq_bot_iff]
  rintro _ ⟨⟨b, hb, rfl⟩, hbc⟩
  have hfix : ∀ y ∈ J, D.act b y = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, v, hv, rfl⟩ := hy
      have hbl : D.act b * D.act l = D.act l * D.act b := by
        have h2 : D.act (b * l * b⁻¹ * l⁻¹) = 1 := D.act_eq_one_of_mem
          (Setting147.comm_R1_l1 C.S h1332 hHL (hBR hb) hl)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
        calc D.act b * D.act l = (D.act b * D.act l * (D.act b)⁻¹ * (D.act l)⁻¹) *
            (D.act l * D.act b) := by group
          _ = D.act l * D.act b := by rw [h2, one_mul]
      rw [← MulAut.mul_apply, hbl, MulAut.mul_apply, mem_centSub.mp hbc v hv]
    | one => exact map_one _
    | mul a c _ _ ha hc => rw [map_mul, ha, hc]
    | inv a _ ha => rw [map_inv, ha]
  exact Subgroup.mem_bot.mpr (MulEquiv.ext fun m => hfix m (h1 ▸ Subgroup.mem_top m))

theorem d310 (h310 : D310) (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) {B : Subgroup G}
    (hB : IsF918B T L (fsuV1 T V) V H (conjClosure K T) B) :
    ∃ Vs : Subgroup (Hat V H I),
      Vs ∈ IrrPlusOn (D.autOf K) (orbSup (D.autOf T) Vs) (D.autOf T) ∧
        ((∀ t ∈ D.autOf T, t ∈ stabSub Vs) ∨ D310Two (D.autOf T) (D.autOf K) Vs) := by
  classical
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hBR : B ≤ pCoreOf 2 (l1 T L V ⊔ T) := hl1 ▸ hB.1
  have hBT : B ≤ T := hBR.trans (L32A.pCoreOf_le_of_le C.S.hyp le_sup_right)
  have hKT : conjClosure K T = K := conjClosure_T_eq_self (C.hTH.trans C.hKn)
  have hfaith := C.faithful D h28 h1222 h1332 h1334 h5 hLie
  have hne := C.autOf_K_ne_bot D
  have hO2 := C.pCoreOf_range D h28 h1222 h1332 h1334 h5 hLie
  have hHL := C.hHL h1332
  have hTL := Setting147.T_le_N_l1 C.S h1332
  refine D.d310 h310 C.hK C.hKn C.hq hne hO2 hB.2.1 hBT
    (fun b hb h => hfaith ⟨b, C.hTH (hBT hb)⟩ ((D.act_eq_one_iff_comm _).mpr h))
    (fun b hb hc => hB.2.2 b hb fun k hk => ?_) (fun Vs hVs => ?_)
  · rw [hKT] at hk
    have h1 : D.act (b * ⟨k, C.hKH hk⟩ * b⁻¹ * ⟨k, C.hKH hk⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc ⟨k, C.hKH hk⟩ hk]
      group
    exact hfaith _ h1
  have hD31 := D.d31 C.hK C.hKn C.hq hne hO2 hVs
  have hKs : D.autOf K ≤ stabSub (orbSup (D.autOf T) Vs) := fun x hx =>
    ((n1_sup_le_stabSub_sec hD31) (Subgroup.mem_sup_left hx)).1
  have hTs : D.autOf T ≤ stabSub (orbSup (D.autOf T) Vs) := le_stabSub_orbSup _ _
  have hVs0 : Vs ≠ ⊥ := by
    obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp (show Vs ∈ IrrPlus (D.autOf K) ⊤ from
      ⟨le_top, hVs.1.2⟩)
    exact fun h => (lt_irrefl _ (lt_of_le_of_lt bot_le (h ▸ hlt))).elim
  exact C.faithVT D h1332 hHL hTL hBR hKs hTs fun h => hVs0 (le_bot_iff.mp (h ▸ hVs.1.1))
end Top42

end CFSG.Quasithin.H13.L32A.C
