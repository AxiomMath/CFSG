module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsTwo
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace Sec10XSteps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem isMulCommutative_of_inf_centralizer_eq_bot (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSA : A ≤ Subgroup.normalizer (S : Set G)) (hUS : sec10U L a ≤ S)
    (hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a)
    (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) {w : G}
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwd : w * d * w⁻¹ = d)
    (hwc : w * c * w⁻¹ = c * d) : IsMulCommutative S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hdL' : d ∈ L := (hdL ▸ Subgroup.mem_zpowers d : d ∈ A ⊓ L).2
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd3' : d ^ 3 = 1 := h.pow_three hdA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  obtain ⟨-, hU4, -, -⟩ := sec10U_facts h
  have hdY : d ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hdL', Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hdA h.a_mem)⟩
  have hUd := inf_centralizer_eq_bot h hdY hd3' hd1
  set U := sec10U L a with hUdef
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.mem_A
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hE := Sec10XProof.isElemAbelian_of_le h hcdA
  have hE9 := (card_closure_c_d h hdL hd3).ge
  have hcd : c * d = d * c := h.comm h.mem_A hdA
  have hc3 := h.pow_three h.mem_A
  set Z := S ⊓ Subgroup.centralizer (S : Set G) with hZ
  have hZS : Z ≤ S := inf_le_left
  have hconjZ : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ Z, g * x * g⁻¹ ∈ Z := by
    intro g hg x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hs'
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * s := by group
  have hZN : ∀ g ∈ Subgroup.normalizer (S : Set G), g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hconjZ g hg x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hEZ : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hZN x (hSA (hcdA hx))
  have hU1 : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU4
    norm_num at hU4
  have hZU : Z ⊓ Subgroup.centralizer ({c} : Set G) ≠ ⊥ := by
    intro hbot
    have hZbot : Z ≤ ⊥ := le_of_inf_centralizer_le hc3 hd3' hcd hE hE9 (hS2.to_le hZS) hEZ
      (hZN w hwS) hwc hwd (fun x hx => by rw [Subgroup.mem_bot.mp hx]; simp)
      (le_of_eq hbot) (by rw [← hSd]; exact inf_le_inf_right _ hZS)
    have hSnt : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr
      (fun hb => hU1 (le_bot_iff.mp (hb ▸ hUS)))
    have hZnt : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center S)
    have hzZ : ((z : S) : G) ∈ Z := ⟨(z : S).2, Subgroup.mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩)⟩
    have := hZbot hzZ
    rw [Subgroup.mem_bot] at this
    exact hz1 (Subtype.ext (Subtype.ext this))
  have hZcU : Z ⊓ Subgroup.centralizer ({c} : Set G) = Z ⊓ U := by
    rw [← hSc, ← inf_assoc, inf_eq_left.mpr hZS]
  rw [hZcU] at hZU
  set T := Z ⊓ U with hT
  have hTU : T ≤ U := inf_le_right
  have hdN : d ∈ Subgroup.normalizer (T : Set G) := SteinbergBY.mem_normalizer_inf
    (hZN d (hSA hdA)) (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hdY)
  have hP : IsPGroup 3 (Subgroup.zpowers d) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hd3, pow_one])
  have hmod := Sec6.card_inf_centralizer_modEq hP (Subgroup.zpowers_le.mpr hdN)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hmod
  have hCT : T ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hUd]
    exact inf_le_inf_right _ hTU
  rw [hCT, Subgroup.card_bot] at hmod
  have hdvd : Nat.card T ∣ 4 := hU4 ▸ Subgroup.card_dvd_of_le hTU
  have hT4 : Nat.card T = 4 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card T = n := ⟨_, rfl⟩
    rw [hn] at hmod hdvd ⊢
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · exact absurd hdvd (by decide)
    · exact absurd (Subgroup.eq_bot_of_card_eq _ hn) hZU
    · exact absurd hmod (by decide)
    · exact absurd hdvd (by decide)
    · rfl
  have hUZ : U ≤ Z := by
    have heq : T = U := Subgroup.eq_of_le_of_card_ge hTU (by rw [hT4, hU4])
    rw [← heq]
    exact inf_le_left
  have hSZ : S ≤ Z := le_of_inf_centralizer_le hc3 hd3' hcd hE hE9 hS2 (hcdA.trans hSA) hwS
    hwc hwd (hconjZ w hwS) (by rw [hSc]; exact hUZ) (by rw [hSd]; exact bot_le)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact (Subgroup.mem_centralizer_iff.mp (hSZ y.2).2 x x.2)

theorem not_inf_centralizer_le_centralizer_a (h : Sec10Std G A c L a R) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSab : IsMulCommutative S) (hUS : sec10U L a ≤ S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) :
    ¬ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
        Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  obtain ⟨-, hU4, -, -⟩ := sec10U_facts h
  have hU2 : IsPGroup 2 (sec10U L a) := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  set U := sec10U L a with hUdef
  set P₀ := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hP₀
  have hU1 : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU4
    norm_num at hU4
  have haU : a ∈ Subgroup.centralizer (U : Set G) :=
    Sec10XProof.closure_a_c_le_centralizer_U h (Subgroup.subset_closure (by simp))
  have hSU : S ≤ Subgroup.centralizer (U : Set G) := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      congrArg Subtype.val (hSab.1.comm ⟨u, hUS hu⟩ ⟨s, hs⟩)
  have hCN : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (P₀ : Set G) :=
    Subgroup.zpowers_le.mpr (hCN haU)
  have hSN : S ≤ Subgroup.normalizer (P₀ : Set G) := hSU.trans hCN
  set α : Subgroup.zpowers a →* MulAut P₀ :=
    P₀.normalizerMonoidHom.comp (Subgroup.inclusion hzN) with hα
  set β : S →* MulAut P₀ := P₀.normalizerMonoidHom.comp (Subgroup.inclusion hSN) with hβ
  have hαapp : ∀ (g : Subgroup.zpowers a) (r : P₀), ((α g r : P₀) : G) = g * r * (g : G)⁻¹ :=
    fun _ _ => rfl
  have hβapp : ∀ (b : S) (r : P₀), ((β b r : P₀) : G) = b * r * (b : G)⁻¹ := fun _ _ => rfl
  have hgb : ∀ (g : Subgroup.zpowers a) (b : S), (g : G) * b = b * g := fun g b => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [← hk]
    have hba : (b : G) * a = a * b := Subgroup.mem_centralizer_singleton_iff.mp (hSa b.2)
    exact ((Commute.zpow_left (hba.symm : Commute a (b : G)) k).eq)
  have hcomm : ∀ g b, α g * β b = β b * α g := fun g b => by
    ext r
    simp only [MulAut.mul_apply]
    rw [hαapp, hβapp, hβapp, hαapp]
    calc (g : G) * ((b : G) * r * (b : G)⁻¹) * (g : G)⁻¹ =
        ((g : G) * b) * r * ((g : G) * b)⁻¹ := by group
      _ = ((b : G) * g) * r * ((b : G) * g)⁻¹ := by rw [hgb g b]
      _ = (b : G) * ((g : G) * r * (g : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix : ∀ g r, (∀ b, β b r = r) → α g r = r := by
    intro g r hr
    have hrS : (r : G) ∈ Subgroup.centralizer (S : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => by
        have h1 := congrArg Subtype.val (hr ⟨s, hs⟩)
        rw [hβapp] at h1
        calc s * (r : G) = s * r * s⁻¹ * s := by group
          _ = r * s := by rw [h1]
    have hra : (r : G) * a = a * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨r.2, hrS⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [hαapp, ← hk, ((Commute.zpow_left (hra.symm : Commute a (r : G)) k).eq),
      mul_inv_cancel_right]
  have hA2 : ¬ 2 ∣ Nat.card (Subgroup.zpowers a) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.pow_three h.a_mem) h.a_ne_one]
    norm_num
  have hα1 := GroupTheory.thompson_A_times_B (p := 2)
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) hA2 hS2 α β hcomm hfix
  have haP : a ∈ Subgroup.centralizer (P₀ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr => by
      have h1 := congrArg Subtype.val
        (DFunLike.congr_fun (hα1 ⟨a, Subgroup.mem_zpowers a⟩) ⟨r, hr⟩)
      rw [hαapp] at h1
      change a * r * a⁻¹ = r at h1
      calc r * a = a * r * a⁻¹ * a := by rw [h1]
        _ = a * r := by group
  have hbot := Sec6.inf_centralizer_inSubgroup_pCore_eq_bot h.charTwoType hU2 hU1
    (B := Subgroup.zpowers a) (fun b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        h.pow_three h.a_mem, one_zpow])
    (Subgroup.zpowers_le.mpr haU)
  have hmem : a ∈ Subgroup.zpowers a ⊓
      Subgroup.centralizer (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) :
        Set G) := ⟨Subgroup.mem_zpowers a, haP⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact h.a_ne_one hmem

theorem inf_centralizer_mul_pow_le (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hUmax : sec10U L a ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2))
    {S : Subgroup G} (hSA : A ≤ Subgroup.normalizer (S : Set G)) (hUS : sec10U L a ≤ S)
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwd : w * d * w⁻¹ = d)
    (hwc : w * c * w⁻¹ = c * d) (k : ℕ) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
        Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({c * d ^ k} : Set G) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdA := h.d_mem_A hdL
  obtain ⟨⟨hUH, hU2, hUA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hUmax
  set U := sec10U L a with hUdef
  set V := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
    Subgroup.centralizer (S : Set G) with hV
  have hV2 : IsPGroup 2 V := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le inf_le_left
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
        (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hUA hx)))
      (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hSA hx))
  set X := V ⊓ Subgroup.centralizer ({c * d ^ k} : Set G) with hX
  have hcdk : c * d ^ k ∈ A := A.mul_mem h.mem_A (A.pow_mem hdA k)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf (hAV hx) (Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx hcdk)))
  set Y := X.map (MulAut.conj (w ^ k)⁻¹).toMonoidHom with hY
  have hYmem : ∀ x ∈ X, (w ^ k)⁻¹ * x * w ^ k ∈ Y := fun x hx => by
    refine ⟨x, hx, ?_⟩
    change (w ^ k)⁻¹ * x * ((w ^ k)⁻¹)⁻¹ = _
    rw [inv_inv]
  have hYX : ∀ y ∈ Y, ∃ x ∈ X, y = (w ^ k)⁻¹ * x * w ^ k := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    change (w ^ k)⁻¹ * x * ((w ^ k)⁻¹)⁻¹ = _
    rw [inv_inv]
  have hY2 : IsPGroup 2 Y := (hV2.to_le inf_le_left).map _
  have hwkS : w ^ k ∈ Subgroup.normalizer (S : Set G) := Subgroup.pow_mem _ hwS k
  have hwkA : w ^ k ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hwA k
  have hYc : Y ≤ Subgroup.centralizer ({c} : Set G) := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hYX y hy
    exact (Sec10XSteps.exists_conj_mem_inf_centralizer (X := ⊤) (Subgroup.le_normalizer
      (Subgroup.mem_top w)) hwc hwd k ⟨Subgroup.mem_top x, hx.2⟩).2
  have hYU : Y ≤ Subgroup.centralizer (U : Set G) := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hYX y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : w ^ k * u * (w ^ k)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hwkS u).mp (hUS hu)
    have h1 := Subgroup.mem_centralizer_iff.mp hx.1.2 _ hu'
    calc u * ((w ^ k)⁻¹ * x * w ^ k) =
        (w ^ k)⁻¹ * ((w ^ k * u * (w ^ k)⁻¹) * x) * w ^ k := by group
      _ = (w ^ k)⁻¹ * (x * (w ^ k * u * (w ^ k)⁻¹)) * w ^ k := by rw [h1]
      _ = (w ^ k)⁻¹ * x * w ^ k * u := by group
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun g hg => by
    have hg' : w ^ k * g * (w ^ k)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwkA g).mp hg
    have hconj : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hYX y hy
      have h1 := (Subgroup.mem_normalizer_iff.mp (hAX hg') x).mp hx
      have h2 := hYmem _ h1
      have h3 : (w ^ k)⁻¹ * (w ^ k * g * (w ^ k)⁻¹ * x * (w ^ k * g * (w ^ k)⁻¹)⁻¹) * w ^ k =
          g * ((w ^ k)⁻¹ * x * w ^ k) * g⁻¹ := by group
      rwa [h3] at h2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact hconj y hy
    · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hU2' : IsPGroup 2 U := (isPiSubgroup_piOf_iff Nat.prime_two U).mp hU2
  have hYUn : Y ≤ Subgroup.normalizer (U : Set G) :=
    hYU.trans (Subgroup.centralizer_le_normalizer _)
  have hT2 : IsPGroup 2 (Y ⊔ U : Subgroup G) := IsPGroup.to_sup_of_normal_right' hY2 hU2' hYUn
  have hTH : Y ⊔ U ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le (hYc.trans (centralizer_le_normalizer_zpowers c)) hUH
  have hTA : A ≤ Subgroup.normalizer ((Y ⊔ U : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup_of_mem (hAY hg) (hUA hg)
  have hTU := (mem_maxInvariantPiSubgroups_iff.mp hUmax).2 (Y ⊔ U)
    ⟨hTH, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hT2, hTA⟩ le_sup_right
  intro x hx
  have hyU : (w ^ k)⁻¹ * x * w ^ k ∈ U := by
    rw [← hTU]
    exact Subgroup.mem_sup_left (hYmem x hx)
  have h1 := (Subgroup.mem_normalizer_iff.mp hwkS _).mp (hUS hyU)
  have h2 : w ^ k * ((w ^ k)⁻¹ * x * w ^ k) * (w ^ k)⁻¹ = x := by group
  rwa [h2] at h1

theorem not_inf_centralizer_d_le_centralizer_a (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hUmax : sec10U L a ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2))
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSab : IsMulCommutative S)
    (hSA : A ≤ Subgroup.normalizer (S : Set G)) (hUS : sec10U L a ≤ S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwS : w ∈ Subgroup.normalizer (S : Set G))
    (hwd : w * d * w⁻¹ = d) (hwc : w * c * w⁻¹ = c * d) :
    ¬ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
        Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  obtain ⟨⟨-, -, hUA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hUmax
  set V := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
    Subgroup.centralizer (S : Set G) with hV
  have hV2 : IsPGroup 2 V := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le inf_le_left
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
        (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hUA hx)))
      (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hSA hx))
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.mem_A
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hVM : V ≤ S ⊔ (V ⊓ Subgroup.centralizer ({d} : Set G)) :=
    le_of_inf_centralizer_mul_pow_le (h.pow_three h.mem_A) (h.pow_three hdA)
      (h.comm h.mem_A hdA) (Sec10XProof.isElemAbelian_of_le h hcdA)
      (card_closure_c_d h hdL hd3).ge hV2 (hcdA.trans hAV)
      (fun k => (inf_centralizer_mul_pow_le h hdL hUmax hSA hUS hwA hwS hwd hwc k).trans
        le_sup_left) le_sup_right
  exact not_inf_centralizer_le_centralizer_a h hS2 hSab hUS hSa
    (hVM.trans (sup_le hSa hle))

theorem exists_mem_closure_not_le (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hUmax : sec10U L a ∈
      maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2))
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSab : IsMulCommutative S)
    (hSA : A ≤ Subgroup.normalizer (S : Set G)) (hUS : sec10U L a ≤ S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G))
    (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwS : w ∈ Subgroup.normalizer (S : Set G))
    (hwd : w * d * w⁻¹ = d) (hwc : w * c * w⁻¹ = c * d) :
    ∃ e ∈ Subgroup.closure ({a, c} : Set G), e ∉ Subgroup.zpowers c ∧
      ¬ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
          Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  obtain ⟨⟨-, -, hUA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hUmax
  set V := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
    Subgroup.centralizer (S : Set G) with hV
  set X := V ⊓ Subgroup.centralizer ({d} : Set G) with hX
  have hX2 : IsPGroup 2 X :=
    ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le inf_le_left).to_le inf_le_left
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
        (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hUA hx)))
      (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hSA hx))
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf (hAV hx) (Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx hdA)))
  have hcop : Nat.Coprime 3 (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hacA := Sec10XProof.closure_a_c_le h
  have hnot := not_inf_centralizer_d_le_centralizer_a h97 h hdL hUmax hS2 hSab hSA hUS hSa hwA
    hwS hwd hwc
  by_contra hall
  push Not at hall
  apply hnot
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three
    (Sec10XProof.isElemAbelian_of_le h hacA) (by rw [Sec10XProof.card_closure_a_c h]; norm_num)
    (hacA.trans hAX) hcop fun v hv hv1 => ?_
  by_cases hvc : v ∈ Subgroup.zpowers c
  ·
    intro x hx
    have hcv : c ∈ Subgroup.zpowers v := by
      have hle : Subgroup.zpowers v ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hvc
      have heq : Subgroup.zpowers v = Subgroup.zpowers c := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_c,
          orderOf_eq_prime (h.pow_three (hacA hv)) hv1]
      rw [heq]
      exact Subgroup.mem_zpowers c
    have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcv
    have hxv' : Commute x v := hxv
    have hxc : x * c = c * x := by
      rw [← hm]
      exact (hxv'.zpow_right m).eq
    have hxS : x ∈ S := inf_centralizer_mul_pow_le h hdL hUmax hSA hUS hwA hwS hwd hwc 0
      ⟨hx.1.1, Subgroup.mem_centralizer_singleton_iff.mpr (by rw [pow_zero, mul_one]; exact hxc)⟩
    have hx1 : x ∈ S ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hxS, hx.1.2⟩
    rw [hSd, Subgroup.mem_bot] at hx1
    rw [hx1]
    exact Subgroup.one_mem _
  · have h1 := hall v hv hvc
    intro x hx
    exact h1 ⟨⟨⟨hx.1.1.1, hx.1.1.2⟩, hx.2⟩, hx.1.2⟩

theorem card_closure_e_d (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {e : G} (he : e ∈ Subgroup.closure ({a, c} : Set G))
    (hec : e ∉ Subgroup.zpowers c) : Nat.card (Subgroup.closure ({e, d} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  have hacA := Sec10XProof.closure_a_c_le h
  have heA : e ∈ A := hacA he
  have he3 : e ^ 3 = 1 := h.pow_three heA
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ Subgroup.one_mem _)
  have hcl : Subgroup.closure ({e, d} : Set G) = Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) :
      Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (h.comm heA hdA) k).eq
  have hde : d ∉ Subgroup.zpowers e := by
    intro hd
    have hdac : d ∈ Subgroup.closure ({a, c} : Set G) := Subgroup.zpowers_le.mpr he hd
    have hAle : A ≤ Subgroup.closure ({a, c} : Set G) := by
      rw [hAcl, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | hy
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hdac
    have := Subgroup.card_le_of_le hAle
    rw [h.card_eq, Sec10XProof.card_closure_a_c h] at this
    norm_num at this
  rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three (h.pow_three hdA) hde), Nat.card_zpowers,
    Nat.card_zpowers, orderOf_eq_prime he3 he1, hd3]

end Sec10XSteps

@[expose] def Step1012SClaim : Prop :=
  Sec4.Item4_5 → Sec9.Item97 → Item107 → Sec4.Item4_26Theta → Item1011Two →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ∀ S ∈ maxInvariantPiSubgroups
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
        sec10U L a ≤ S → S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a →
        S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ →
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) →
        w * a * w⁻¹ = a → w * d * w⁻¹ = d → w * c * w⁻¹ = c * d →
      IsMulCommutative S →
      ∀ e ∈ Subgroup.closure ({a, c} : Set G), e ∉ Subgroup.zpowers c →
        ¬ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
            Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
            Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer ({a} : Set G) →
        ¬ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
            Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
            Subgroup.centralizer ({d} : Set G) ≤ inSubgroup (aschbacherSolvableCore 3)
              (Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G)) →
        ∃ B : Subgroup G, B ≤ A ∧ d ∈ B ∧ Nat.card B = 9 ∧
          Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
            (Subgroup.centralizer (B : Set G)), A⁆ : Subgroup G))

section Main

theorem step1012S_of (hclaim : Step1012SClaim) (h463 : Item463Inv) : Step1012S := by
  intro h45 h97 h107 h426 h1011 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd w hwA hwS hwa
    hwd hwc
  exfalso
  have hdA := h.d_mem_A hdL
  obtain ⟨hSθ, hS2, hSA⟩ := hS.prop
  have hS2' : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2
  have hSab := Sec10XSteps.isMulCommutative_of_inf_centralizer_eq_bot h97 h hdL hS2' hSA hUS hSc
    hSd hwS hwd hwc
  have hSa : S ≤ Subgroup.centralizer ({a} : Set G) := hSθ.trans (Subgroup.map_subtype_le _)
  obtain ⟨e, he, hec, hea⟩ := Sec10XSteps.exists_mem_closure_not_le h97 h hdL hUmax hS2' hSab
    hSA hUS hSa hSd hwA hwS hwd hwc
  have heA : e ∈ A := Sec10XProof.closure_a_c_le h he
  set B := Subgroup.closure ({e, d} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact heA
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hdB : d ∈ B := Subgroup.subset_closure (by simp)
  have hB9 : Nat.card B = 9 := Sec10XSteps.card_closure_e_d h97 h hdL he hec
  by_cases hθ : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
      Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G) ≤ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer (B : Set G))
  ·
    obtain ⟨⟨-, -, hUA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hUmax
    have hX2 : IsPGroup 2 (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G)) ⊓
        Subgroup.centralizer (S : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G) : Subgroup G) :=
      (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have hAX : A ≤ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer (sec10U L a : Set G)) ⊓ Subgroup.centralizer (S : Set G) ⊓
        Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) :
          Subgroup G) : Set G) := fun x hx =>
      SteinbergBY.mem_normalizer_inf (SteinbergBY.mem_normalizer_inf
        (SteinbergBY.mem_normalizer_inf
          (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
            (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hUA hx)))
          (Sec10XSteps.normalizer_le_normalizer_centralizer_of (hSA hx)))
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx heA))))
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx hdA)))
    exact Sec10XSteps.false_of_even_commutator h45 h97 h463 h hdL hBA hdB hB9
      (Sec10XSteps.even_of_le_theta hX2 hAX h.a_mem hea hθ)
  · obtain ⟨B', hB'A, hdB', hB'9, heven⟩ := hclaim h45 h97 h107 h426 h1011 G A c L a R h d hdL
      hUθ hUmax S hS hUS hSc hSd w hwA hwS hwa hwd hwc hSab e he hec hea hθ
    exact Sec10XSteps.false_of_even_commutator h45 h97 h463 h hdL hB'A hdB' hB'9 heven

theorem sec10X_of_claim (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h107 : Item107)
    (h462 : Sec4.Item4_62) (h426 : Sec4.Item4_26Theta) (h463 : Item463Inv)
    (hclaim : Step1012SClaim) : Sec10X :=
  sec10X_of h45 h97 h107 h462 h426 h463 step1010U_holds
    (step1011Two_of h107 h463) (step1012S_of hclaim h463)

end Main

end CFSG.RankThree.PartTwo.Sec10
