module

public import CFSG.Quasithin.H13.L32NLem14324e
public import CFSG.Quasithin.H13.L32NLem14323b
public import CFSG.Quasithin.Vol2.GoldschmidtL128Ten
public import CFSG.Quasithin.H13.L32NLem14324m
public import CFSG.Quasithin.H13.L32NLem14324n

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_conj {X : Subgroup G} {g x : G} : x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

structure Ctx5 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)) : Prop where
  hyp : Hyp14310One G T L V
  lt : fsuV1 T V < centerOf (fsuU T V)
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  aV₂ : a ∈ V₂
  a1 : a ∉ fsuV1 T V
  card_V1 : Nat.card ↥(fsuV1 T V) = 2
  UT : fsuU T V ≤ T
  T_le : T ≤ l32nH T V
  V_U : V ≤ fsuU T V
  VZ : V ⊓ centerOf (fsuU T V) = fsuV1 T V
  zUg_le : CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V
  zUg_ne : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥
  q_tilde : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)
  alt : ∀ v, D.B v v = 0
  nd : ∀ v, (∀ w, D.B v w = 0) → v = 0
  Todd : Odd ((D.img T).relIndex (D.img (l32nH T V)))
  rank3 : CFSG.Open.pRank 3
    (centralizerMod (fsuV1 T V) (Subgroup.normalizer (fsuV1 T V : Set G)) V₂) ≤ 1
  zI2 : centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g =
    centerOf (i128 T L V (fsuV1 T V))
  zU_le_Hg : centerOf (fsuU T V) ≤ CFSG.conjugate (l32nH T V) g
  i2_eq : i128 T L V (fsuV1 T V) = oTwoUpper (p128 T L V) ⊔ fsuU T V
  h1222 : Stmt12_2_2
  cardV : Nat.card V = 8
  LTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)
  span : Submodule.span (ZMod 2) (MulAction.orbit (D.img (l32nH T V)) (D.π a)) = ⊤

theorem exists_ctx5 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13) (h14312 : Lemma14312One)
    (hFixS : G11.SzG11S.TheoremG112FixS) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) {V₂ : Subgroup G} {g : G}
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) : ∃ a : G, Ctx5 G T L V V₂ g a D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  have h1283 := lemma12_8_3 h12213
  have h1284 := lemma12_8_4 h1222 h37 h38 h39
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  obtain ⟨a₀, -, -, -, hzUg⟩ :=
    data_of h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
  obtain ⟨H, -⟩ := fixS_of h1222 h12213 hFixS hs hgP hgN haV₂ ha1 D
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := L14332.relIndex_img_dvd D hTH (L14332.l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd
  have hZHg : centerOf (fsuU T V) ≤ CFSG.conjugate (l32nH T V) g := by
    have hgi := L14332.conj_zU_le h12813 hs ((p128 T L V).inv_mem hgP)
      (fun hm => hgN (by simpa using (l32nH T V).inv_mem hm))
    intro z hz
    rw [mem_conj]
    exact hgi (mem_conj.mpr (by simpa [mul_assoc] using hz))
  exact ⟨a, h, hlt, hV₂, hs, hgP, hgN, haV₂, ha1, hV1, h.fsuU_le h13322 hV h1283 h1284, hTH,
    le_conjClosure V _, lemma12_8_8_three h1222 h12213 hs, L14332.conj_zU_le h12813 hs hgP hgN,
    hzUg, (h1284 G T L V 3 (h.hyp1281One h13322 hV) (fsuV1 T V) (l32nH T V)
      (h.isTSub_fsuV1 hV) (h.isHzOne_l32nH h13322 hV h1283)).2.2.2,
    H.alt, H.nondegenerate, hTodd, (h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.2.2,
    (lemma12_8_10_of h1222 h12213 h37 h38 h39 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.1,
    hZHg, L128P.i128_eq_sup h1222 h12213 hs, h1222, hV8, hLTV, H.span_orbit⟩

namespace Ctx5

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx5 G T L V V₂ g a D)
include C

omit [Finite G] C in
theorem H_N : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V

theorem two_elem_of_le_T {x : G} (hx : x ∈ T) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := C.hyp.fsu.sylow.1 ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem zU_le_T : centerOf (fsuU T V) ≤ T := inf_le_left.trans C.UT

theorem V1_le_zU : fsuV1 T V ≤ centerOf (fsuU T V) := fun v hv => by
  have : v ∈ V ⊓ centerOf (fsuU T V) := by rw [C.VZ]; exact hv
  exact this.2

theorem eq_one_of_cube {z : G} (hz : z ∈ centerOf (fsuU T V)) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := C.two_elem_of_le_T (C.zU_le_T hz)
  have hd : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h3)
  rw [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem two_elem_of_centralizerMod {x : G}
    (hx : x ∈ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V)) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  rw [C.q_tilde] at hx
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem two_elem_of_ker {x : G} (hxH : x ∈ l32nH T V)
    (hxZ : ∀ z ∈ centerOf (fsuU T V), z * x = x * z)
    (hxU : ∀ u ∈ fsuU T V, x * u * x⁻¹ * u⁻¹ ∈ centerOf (fsuU T V)) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp : IsPGroup 2 ↥(centerOf (fsuU T V)) := C.hyp.fsu.sylow.1.to_le C.zU_le_T
  obtain ⟨e, he⟩ := hZp.exists_card_eq
  have key : ∀ u ∈ fsuU T V, ∀ m : ℕ,
      x ^ m * u * (x ^ m)⁻¹ = (x * u * x⁻¹ * u⁻¹) ^ m * u := by
    intro u hu m
    set c := x * u * x⁻¹ * u⁻¹ with hcdef
    have hxc : x * c * x⁻¹ = c := by rw [← hxZ c (hxU u hu)]; group
    have hxu : x * u * x⁻¹ = c * u := by rw [hcdef]; group
    induction m with
    | zero => simp
    | succ m ih =>
      calc x ^ (m + 1) * u * (x ^ (m + 1))⁻¹ = x * (x ^ m * u * (x ^ m)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (c ^ m * u) * x⁻¹ := by rw [ih]
        _ = (x * c * x⁻¹) ^ m * (x * u * x⁻¹) := by rw [conj_pow]; group
        _ = c ^ (m + 1) * u := by rw [hxc, hxu, pow_succ]; group
  have hcent : ∀ u ∈ fsuU T V, x ^ 2 ^ e * u * (x ^ 2 ^ e)⁻¹ * u⁻¹ = 1 := by
    intro u hu
    rw [key u hu]
    have hc : (x * u * x⁻¹ * u⁻¹) ^ 2 ^ e = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(centerOf (fsuU T V))) (x := ⟨_, hxU u hu⟩)
      rw [he] at h1
      simpa using congrArg Subtype.val h1
    rw [hc]
    group
  have hmod : x ^ 2 ^ e ∈ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) :=
    ⟨(l32nH T V).pow_mem hxH _, (l32nH T V).pow_mem hxH _, fun u hu => by
      rw [hcent u hu]
      exact one_mem _⟩
  obtain ⟨k, hk⟩ := C.two_elem_of_centralizerMod hmod
  exact ⟨e + k, by rw [pow_add, pow_mul, hk]⟩

theorem conj_eq_of_cube {y : G} (hyH : y ∈ l32nH T V)
    (hyZ : ∀ z ∈ centerOf (fsuU T V), z * y = y * z) (hy3 : y ^ 3 = 1) {u : G}
    (hu : u ∈ fsuU T V) (hπ : D.ρ ⟨y, H_N hyH⟩ (D.π u) = D.π u) : y * u * y⁻¹ = u := by
  rw [D.ρ_π _ u hu] at hπ
  have hyu : y * u * y⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (H_N hyH) u).mp hu
  have hc0 := (D.π_eq_iff _ hyu _ hu).mp hπ
  set c := u⁻¹ * (y * u * y⁻¹) with hcdef
  have hcZ : c ∈ centerOf (fsuU T V) := by
    have := (centerOf (fsuU T V)).inv_mem hc0
    rwa [show ((y * u * y⁻¹)⁻¹ * u)⁻¹ = c by rw [hcdef]; group] at this
  have hyc : y * c * y⁻¹ = c := by rw [← hyZ c hcZ]; group
  have hcu : u * c = c * u := Subgroup.mem_centralizer_iff.mp hcZ.2 u hu
  have e1 : y * u * y⁻¹ = u * c := by rw [hcdef]; group
  have key : ∀ m : ℕ, y ^ m * u * (y ^ m)⁻¹ = u * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (m + 1) * u * (y ^ (m + 1))⁻¹ = y * (y ^ m * u * (y ^ m)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * u * y⁻¹) * (y * c * y⁻¹) ^ m := by rw [ih, conj_pow]; group
        _ = u * c ^ (m + 1) := by rw [e1, hyc, pow_succ']; group
  have h3 := key 3
  rw [hy3, inv_one, one_mul, mul_one] at h3
  have hc3 : c ^ 3 = 1 := by
    have := congrArg (u⁻¹ * ·) h3
    simpa using this.symm
  rw [e1, C.eq_one_of_cube hcZ hc3, mul_one]

theorem πa_ne : D.π a ≠ 0 := fun h0 => C.a1 (by
  rw [← C.VZ]
  exact ⟨C.plane.1.1 C.aV₂, (L128A.HatU.π_eq_zero_iff D (C.V_U (C.plane.1.1 C.aV₂))).mp h0⟩)

theorem fix_T : ∀ t ∈ D.img T, t (D.π a) = D.π a := by
  intro t ht
  obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp ht
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  rw [D.ρ_π ⟨y, hyN⟩ a (C.V_U haV)]
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := C.plane.1.2.2
  have hTV₁ : T ≤ Subgroup.normalizer (fsuV1 T V : Set G) := C.setting.v1.2.2
  have h1 : y * a * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hTV₂ hy) a).mp C.aV₂
  have h2 : y * a * y⁻¹ ∉ fsuV1 T V := fun hm =>
    C.a1 ((Subgroup.mem_normalizer_iff.mp (hTV₁ hy) a).mpr hm)
  have hV₂4 : Nat.card V₂ = 4 := C.plane.1.2.1
  have hcard : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by rw [hV₂4, C.card_V1]
  have h3 := L32NSet14.mul_mem_of_card_eq_two_mul C.plane.2 hcard (by rw [C.card_V1]; norm_num)
    (V₂.inv_mem h1) C.aV₂ (fun hm => h2 (by simpa using (fsuV1 T V).inv_mem hm)) C.a1
  have h4 : (y * a * y⁻¹)⁻¹ * a ∈ centerOf (fsuU T V) := C.V1_le_zU h3
  exact (D.π_eq_iff _ (C.V_U (C.plane.1.1 h1)) _ (C.V_U haV)).mpr h4

theorem isSylow : IsSylowTwoOf (D.img T) (D.img (l32nH T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨L14323.img_mono D C.T_le, ?_, fun h => ?_⟩
  · exact (C.hyp.fsu.sylow.1.comap_of_injective (Subgroup.normalizer (fsuU T V : Set G)).subtype
      (Subgroup.normalizer (fsuU T V : Set G)).subtype_injective).map D.ρ
  · exact (Nat.not_even_iff_odd.mpr C.Todd) (even_iff_two_dvd.mpr h)

theorem img_cent_eq_bot (M : S8Five.Model5 (D.img (l32nH T V))) :
    D.img (l32nH T V ⊓ Subgroup.centralizer (centerOf (fsuU T V) : Set G)) = ⊥ := by
  classical
  set J := l32nH T V ⊓ Subgroup.centralizer (centerOf (fsuU T V) : Set G) with hJ
  set N := Subgroup.normalizer (fsuU T V : Set G) with hN
  by_contra hne
  have hJH : J ≤ l32nH T V := inf_le_left
  have hJn : ∀ γ ∈ D.img (l32nH T V), ∀ n ∈ D.img J, γ * n * γ⁻¹ ∈ D.img J := by
    intro γ hγ n hn
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    obtain ⟨j, hj, hjN, rfl⟩ := (L128A.HatU.mem_img D).mp hn
    have hZn : h ∈ Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
      L14332.normalizer_le_normalizer_centerOf _ hhN
    have hconj : h * j * h⁻¹ ∈ J := by
      refine ⟨(l32nH T V).mul_mem ((l32nH T V).mul_mem hh hj.1) ((l32nH T V).inv_mem hh),
        Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : h⁻¹ * z * h ∈ centerOf (fsuU T V) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hZn) z).mp hz
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hj.2 _ hz'
      calc z * (h * j * h⁻¹) = h * ((h⁻¹ * z * h) * j) * h⁻¹ := by group
        _ = h * (j * (h⁻¹ * z * h)) * h⁻¹ := by rw [hc]
        _ = h * j * h⁻¹ * z := by group
    have hmem := L128A.HatU.rho_mem_img D hconj (N.mul_mem (N.mul_mem hhN hjN) (N.inv_mem hhN))
    have e : D.ρ ⟨h, hhN⟩ * D.ρ ⟨j, hjN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ =
        D.ρ ⟨h * j * h⁻¹, N.mul_mem (N.mul_mem hhN hjN) (N.inv_mem hhN)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hmem
  have hAJ : M.A ≤ D.img J := M.alt_le_of_normal (L14323.img_mono D hJH) hJn hne
  obtain ⟨P, hPA, hP9, hPc, hP3, hPfix⟩ := M.exists_E9 C.isSylow C.πa_ne C.fix_T
  set R : Subgroup ↥N := J.subgroupOf N ⊓ P.comap D.ρ with hR
  have hRP : R.map D.ρ = P := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.2
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := hAJ (hPA hp)
      exact ⟨r, ⟨hr, hp⟩, rfl⟩
  have hker : ∀ r ∈ R, D.ρ r = 1 → ∃ k : ℕ, r ^ 2 ^ k = 1 := by
    intro r hr h1
    have hrJ : (r : G) ∈ J := hr.1
    obtain ⟨k, hk⟩ := C.two_elem_of_ker hrJ.1
      (fun z hz => Subgroup.mem_centralizer_iff.mp hrJ.2 z hz)
      ((L128A.HatU.rho_eq_one_iff D r).mp h1)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨Y, hYR, hY9, hYc, hY3, hYP⟩ := S8Five.exists_lift_nine D.ρ hRP hP9 hPc hP3 hker
  have hcent : ∀ y ∈ Y, ∀ v ∈ V₂, (y : G) * v * (y : G)⁻¹ = v := by
    intro y hy v hv
    have hyJ : (y : G) ∈ J := (hYR hy).1
    have hyZ : ∀ z ∈ centerOf (fsuU T V), z * (y : G) = (y : G) * z :=
      fun z hz => Subgroup.mem_centralizer_iff.mp hyJ.2 z hz
    have hy3 : (y : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hY3 y hy)
    have ha : (y : G) * a * (y : G)⁻¹ = a := by
      refine C.conj_eq_of_cube hyJ.1 hyZ hy3 (C.V_U (C.plane.1.1 C.aV₂)) ?_
      have := hPfix _ (hYP y hy)
      simpa using this
    have hcz : ∀ z ∈ fsuV1 T V, (y : G) * z * (y : G)⁻¹ = z := fun z hz => by
      rw [← hyZ z (C.V1_le_zU hz)]
      group
    by_cases hv1 : v ∈ fsuV1 T V
    · exact hcz v hv1
    · have hcard : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by
        rw [C.plane.1.2.1, C.card_V1]
        norm_num
      have hav : a⁻¹ * v ∈ fsuV1 T V :=
        L32NSet14.mul_mem_of_card_eq_two_mul C.plane.2 hcard (by rw [C.card_V1]; norm_num)
          (V₂.inv_mem C.aV₂) hv (fun hm => C.a1 (by simpa using (fsuV1 T V).inv_mem hm)) hv1
      calc (y : G) * v * (y : G)⁻¹
          = ((y : G) * a * (y : G)⁻¹) * ((y : G) * (a⁻¹ * v) * (y : G)⁻¹) := by group
        _ = v := by rw [ha, hcz _ hav]; group
  set YG := Y.map N.subtype with hYG
  have hYGle : YG ≤ centralizerMod (fsuV1 T V) (Subgroup.normalizer (fsuV1 T V : Set G)) V₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyJ : (y : G) ∈ J := (hYR hy).1
    exact ⟨hyJ.1, hyJ.1, fun v hv => by
      rw [show (N.subtype y : G) = (y : G) from rfl, hcent y hy v hv, mul_inv_cancel]
      exact one_mem _⟩
  have hYGe : IsElemAbelian 3 YG := by
    refine ⟨⟨⟨fun x z => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨z', hz', hze⟩ := z.2
      apply Subtype.ext
      change (x : G) * z = z * x
      rw [← hxe, ← hze]
      exact congrArg Subtype.val (hYc x' hx' z' hz')
    · obtain ⟨x', hx', rfl⟩ := hx
      exact congrArg Subtype.val (hY3 x' hx')
  have hYGc : Nat.card YG = 3 ^ 2 := by
    rw [hYG, Subgroup.card_map_of_injective N.subtype_injective, hY9]
    norm_num
  have h2 := CFSG.SectionRank.le_pRank (by norm_num) hYGle hYGe hYGc
  have := C.rank3
  omega

theorem exists_comm_ne (M : S8Five.Model5 (D.img (l32nH T V))) :
    ∃ w ∈ CFSG.conjugate (centerOf (fsuU T V)) g, ∃ z ∈ centerOf (fsuU T V),
      w * z * w⁻¹ * z⁻¹ ≠ 1 := by
  by_contra hall
  push Not at hall
  apply C.zUg_ne
  have hle : CFSG.conjugate (centerOf (fsuU T V)) g ≤
      l32nH T V ⊓ Subgroup.centralizer (centerOf (fsuU T V) : Set G) := by
    intro w hw
    refine ⟨C.zUg_le hw, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have h1 := hall w hw z hz
    calc z * w = (w * z * w⁻¹ * z⁻¹)⁻¹ * (w * z) := by group
      _ = w * z := by rw [h1, inv_one, one_mul]
  rw [eq_bot_iff, ← C.img_cent_eq_bot M]
  exact L14323.img_mono D hle

theorem centerOf_i2_ne (M : S8Five.Model5 (D.img (l32nH T V))) :
    centerOf (i128 T L V (fsuV1 T V)) ≠ ⊥ := by
  obtain ⟨w, hw, z, hz, hne⟩ := C.exists_comm_ne M
  have hwH := C.zUg_le hw
  have hzHg := C.zU_le_Hg hz
  have h1 : w * z * w⁻¹ * z⁻¹ ∈ centerOf (fsuU T V) := by
    have hwZ : w ∈ Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
      L14332.normalizer_le_normalizer_centerOf _ (H_N hwH)
    exact (centerOf (fsuU T V)).mul_mem ((Subgroup.mem_normalizer_iff.mp hwZ z).mp hz)
      ((centerOf (fsuU T V)).inv_mem hz)
  have h2 : w * z * w⁻¹ * z⁻¹ ∈ CFSG.conjugate (centerOf (fsuU T V)) g := by
    rw [mem_conj] at hw hzHg ⊢
    have hzN : g * z * g⁻¹ ∈ Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
      L14332.normalizer_le_normalizer_centerOf _ (H_N hzHg)
    have h3 := (Subgroup.mem_normalizer_iff.mp hzN _).mp ((centerOf (fsuU T V)).inv_mem hw)
    have e : g * (w * z * w⁻¹ * z⁻¹) * g⁻¹ =
        (g * w * g⁻¹) * ((g * z * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * z * g⁻¹)⁻¹) := by group
    rw [e]
    exact (centerOf (fsuU T V)).mul_mem hw h3
  intro hbot
  apply hne
  have hmem : w * z * w⁻¹ * z⁻¹ ∈ centerOf (i128 T L V (fsuV1 T V)) := by
    rw [← C.zI2]
    exact ⟨h1, h2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem zD_ne (M : S8Five.Model5 (D.img (l32nH T V))) :
    quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V (fsuV1 T V)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := centerOf (i128 T L V (fsuV1 T V)) with hN
  have hNT : N ≤ T := by
    rw [hN, ← C.zI2]
    exact inf_le_left.trans C.zU_le_T
  have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
    (L128P.le_p128.trans (le_normalizer_conjClosure _ _)).trans
      (L14332.normalizer_le_normalizer_centerOf _)
  have hT2 : IsPGroup 2 T := C.hyp.fsu.sylow.1
  have : Group.IsNilpotent T := hT2.isNilpotent
  have hnormal : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTN
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply C.centerOf_i2_ne M
    rw [← hN, ← Subgroup.map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  have hA := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set A : Subgroup ↥T := N.subgroupOf T ⊓ Subgroup.center ↥T with hAdef
  have hAp : IsPGroup 2 ↥A := (hT2.to_subgroup A)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA (Subgroup.card_eq_one.mp (by simpa using hn))
  obtain ⟨c, hc⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥A) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  set x : G := ((c : ↥T) : G) with hx
  have hxN : x ∈ N := (c.2.1 : (c : ↥T) ∈ N.subgroupOf T)
  have hxC : x ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun t ht => congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2.2 ⟨t, ht⟩)
  have hx2 : x ^ 2 = 1 := by
    have h1 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    simpa [hx] using congrArg (fun y : ↥A => ((y : ↥T) : G)) h1
  have hx1 : x ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  intro hbot
  apply hx1
  have hmem : x ∈ quasithinOmegaOneCenter T ⊓ N :=
    ⟨Subgroup.subset_closure ⟨⟨(c : ↥T).2, hxC⟩, hx2⟩, hxN⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

end Ctx5

end L14324

end CFSG.Quasithin.H13
