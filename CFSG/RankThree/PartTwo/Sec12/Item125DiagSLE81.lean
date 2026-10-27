module

public import CFSG.RankThree.PartTwo.Sec12.Item125DiagBasic
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.GroupTheory.SteinbergBYAutCentralizerTheta

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item125Diag

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory.SteinbergBY (map_inSubgroup_aschbacherSolvableCore_mulEquiv)

variable {G : Type} [Group G] [Finite G]

theorem inf_le_inSubgroup_theta {X M : Subgroup G} (hMX : M ≤ X) :
    inSubgroup (aschbacherSolvableCore 3) X ⊓ M ≤ inSubgroup (aschbacherSolvableCore 3) M := by
  rintro x ⟨hxX, hxM⟩
  set T := inSubgroup (aschbacherSolvableCore 3) X with hT
  set N : Subgroup M := T.subgroupOf M with hNdef
  have hN : N.Normal := ⟨fun n hn m => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Sec13.conj_mem_inSubgroup_theta (hMX m.2) hn⟩
  set f : N →* T :=
    { toFun := fun n => ⟨(n : M), Subgroup.mem_subgroupOf.mp n.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hf
  have hfinj : Function.Injective f := fun a b h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : T => (x : G)) h
  have hTsolv : Group.IsSolvable T := by
    have := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective
      (aschbacherSolvableCore 3 X) X.subtype X.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hNsolv : Group.IsSolvable N := by
    have := hTsolv
    exact Group.isSolvable_of_isSolvable_injective hfinj
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    apply (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
    have h1 := Subgroup.card_dvd_of_injective f hfinj
    rw [hT, show Nat.card (inSubgroup (aschbacherSolvableCore 3) X) =
      Nat.card (aschbacherSolvableCore 3 X) from
        Subgroup.card_map_of_injective X.subtype_injective] at h1
    exact h3.trans h1
  have hle := (solvable_prime_complement_core_characterization (H := M) Nat.prime_three).2.2.2.1
    N hN hNsolv hN3
  exact ⟨⟨x, hxM⟩, hle (Subgroup.mem_subgroupOf.mpr hxX), rfl⟩

omit [Finite G] in
theorem map_conj_centralizer_singleton (g c : G) :
    (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * c * g⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * c = c * y := (Subgroup.mem_centralizer_singleton_iff.mp hy)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [hy']
      _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    have hx' : x * (g * c * g⁻¹) = (g * c * g⁻¹) * x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    refine ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · calc g⁻¹ * x * g * c = g⁻¹ * (x * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * x) * g := by rw [hx']
        _ = c * (g⁻¹ * x * g) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem mem_normalizer_zpowers_of_conj_mem {c g : G}
    (h : g * c * g⁻¹ ∈ Subgroup.zpowers c) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hle : Subgroup.zpowers (g * c * g⁻¹) ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr h
  have hcard : Nat.card (Subgroup.zpowers (g * c * g⁻¹)) = Nat.card (Subgroup.zpowers c) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have heq : Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  exact heq

omit [Finite G] in
theorem mk_mem_center_of_mem {W : Subgroup G} {w : G} (hw : w ∈ W)
    (hwM : w ∈ Subgroup.centralizer (W : Set G)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer (W : Set G))) ⟨w, hwM⟩ ∈
      Subgroup.center (Subgroup.centralizer (W : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer (W : Set G))) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact ((Subgroup.mem_centralizer_iff.mp m.2) w hw).symm

theorem conj_eq_of_mk_eq {M E : Subgroup G} (hEM : E ≤ M) (hE3 : IsPGroup 3 E) {a b : M}
    (hbE : (b : G) ∈ Subgroup.normalizer (E : Set G))
    (haE : (a : G) ∈ Subgroup.normalizer (E : Set G))
    (hab : QuotientGroup.mk' (aschbacherSolvableCore 3 M) a =
      QuotientGroup.mk' (aschbacherSolvableCore 3 M) b) {e : G} (he : e ∈ E) :
    (a : G) * e * (a : G)⁻¹ = (b : G) * e * (b : G)⁻¹ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
  set n : G := ((a⁻¹ * b : M) : G) with hn
  have hnθ : n ∈ inSubgroup (aschbacherSolvableCore 3) M := ⟨_, hab, rfl⟩
  have hnE : n ∈ Subgroup.normalizer (E : Set G) := by
    rw [hn, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem haE) hbE
  have hw1 : n * e * n⁻¹ * e⁻¹ ∈ E :=
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hnE e).mp he) (E.inv_mem he)
  have hw2 : n * e * n⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) M := by
    have h1 := Sec13.conj_mem_inSubgroup_theta (hEM he) (Subgroup.inv_mem _ hnθ)
    have e1 : n * e * n⁻¹ * e⁻¹ = n * (e * n⁻¹ * e⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hnθ h1
  have hw : n * e * n⁻¹ * e⁻¹ = 1 := by
    have h := inf_inSubgroup_theta_eq_bot hE3 (L := M)
    have hmem : n * e * n⁻¹ * e⁻¹ ∈ E ⊓ inSubgroup (aschbacherSolvableCore 3) M := ⟨hw1, hw2⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hne : n * e * n⁻¹ = e := by
    calc n * e * n⁻¹ = (n * e * n⁻¹ * e⁻¹) * e := by group
      _ = e := by rw [hw, one_mul]
  have hb : (b : G) = a * n := by rw [hn, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hb]
  calc (a : G) * e * (a : G)⁻¹ = a * (n * e * n⁻¹) * (a : G)⁻¹ := by rw [hne]
    _ = a * n * e * (a * n)⁻¹ := by group

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three' {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

namespace DiagHyp

variable {c : G} {L E : Subgroup G}

theorem exists_y (hD : DiagHyp c L E) {e₀ : G} (he₀ : e₀ ∈ E) (he₀c : e₀ ∉ Subgroup.zpowers c) :
    ∃ y : L, (y : G) ^ 3 = 1 ∧ (y : G) ∈ Subgroup.normalizer (E : Set G) ∧
      (y : G) * e₀ = e₀ * y ∧
      thetaBarAct L ⟨e₀, hD.le_normalizer he₀⟩ =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, hl3, hl, -⟩ := hD.exists_part he₀
  set b := QuotientGroup.mk' (aschbacherSolvableCore 3 L) l with hb
  obtain ⟨y₀, hy₀, hy₀N⟩ := hD.exists_lift_normalizer l fun e he =>
    hD.thetaBarAct_mul_inv_mem_center he he₀ hl
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← map_pow]
    have hl' : l ^ 3 = 1 := Subtype.ext (by simpa using hl3)
    rw [hl', map_one]
  have hb1 : b ≠ 1 := by
    intro h
    exact he₀c (hD.mem_zpowers_of_thetaBarAct he₀ (by rw [hl, h, map_one]))
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨m, hm, hym⟩ := exists_pow_orderOf_three (y := y₀) (by rw [hy₀]; exact hbo)
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
  set y := (y₀ ^ m) ^ r with hy
  have hyb : QuotientGroup.mk' (aschbacherSolvableCore 3 L) y = b := by
    rw [hy, map_pow, map_pow, hy₀, ← pow_mul, pow_eq_pow_mod (m * r) hb3, hr, pow_one]
  have hyN : (y : G) ∈ Subgroup.normalizer (E : Set G) := by
    rw [hy, Subgroup.coe_pow, Subgroup.coe_pow]
    exact pow_mem (pow_mem hy₀N m) r
  refine ⟨y, ?_, hyN, ?_, by rw [hl, hyb]⟩
  · have h1 := pow_orderOf_eq_one (y₀ ^ m)
    rw [hym] at h1
    have h2 : y ^ 3 = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, h1, one_pow]
    simpa using congrArg Subtype.val h2
  · have h1 := (hD.conj_eq_self_iff y hyN he₀ hl).mpr (by rw [hyb])
    calc (y : G) * e₀ = ((y : G) * e₀ * (y : G)⁻¹) * y := by group
      _ = e₀ * y := by rw [h1]

theorem exists_E81 (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G) (hD : DiagHyp c L E)
    (hFE : partTwoF G = partTwoE G)
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L))
    {g : G} (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hgH : g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 81 ∧
      F ≤ Subgroup.normalizer (L : Set G) ∧ c ∈ F ∧
      ∃ y : L, (y : G) ∈ F ∧ (y : G) ^ 3 = 1 ∧
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) y ∉
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ∧
        ∃ z ∈ F, z ∈ Sec4.thetaQuotCentralizer L ∧ z ∉ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hD.mem_thetaComponentsAt
  have hc3 := hD.orderOf_c
  set e₀ := g * c * g⁻¹ with he₀def
  set e₁ := g⁻¹ * c * g with he₁def
  have he₀ : e₀ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE c).mp hD.mem_E
  have he₁ : e₁ ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgE) c).mp hD.mem_E
    simpa using this
  have he₀c : e₀ ∉ Subgroup.zpowers c := fun h =>
    hgH (mem_normalizer_zpowers_of_conj_mem h)
  have he₁c : e₁ ∉ Subgroup.zpowers c := fun h =>
    hgH (inv_mem_iff.mp (mem_normalizer_zpowers_of_conj_mem (by simpa using h)))
  set W := Subgroup.zpowers c ⊔ Subgroup.zpowers e₀ with hW
  set M := Subgroup.centralizer (W : Set G) with hM
  set θM := aschbacherSolvableCore 3 M with hθM
  set πM := QuotientGroup.mk' θM with hπM
  have hWE : W ≤ E := sup_le (Subgroup.zpowers_le.mpr hD.mem_E) (Subgroup.zpowers_le.mpr he₀)
  have hmemM : ∀ g : G, g * c = c * g → g * e₀ = e₀ * g → g ∈ M := by
    intro g hgc hge
    have hle : W ≤ Subgroup.centralizer {g} :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hge.symm))
    rw [hM, Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hEM : E ≤ M := fun e he =>
    hmemM e (hD.comm he hD.mem_E) (hD.comm he he₀)
  have hcM : c ∈ M := hEM hD.mem_E
  have he₀M : e₀ ∈ M := hEM he₀
  have hMc : M ≤ Subgroup.centralizer ({c} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hg) c
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))).symm
  have hMe₀ : M ≤ Subgroup.centralizer ({e₀} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hg) e₀
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀))).symm
  have hθLM : ∀ g ∈ inSubgroup (aschbacherSolvableCore 3) L, g ∈ M →
      g ∈ inSubgroup (aschbacherSolvableCore 3) M := by
    intro g hg hgM
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL] at hg
    exact inf_le_inSubgroup_theta hMc ⟨hg.2, hgM⟩
  have h45L : ∀ w : G, w ^ 3 = 1 → w * c = c * w → w ∈ Subgroup.normalizer (L : Set G) := by
    intro w hw3 hwc
    exact le_normalizer_of_mem_thetaComponentsAt h45 hG hc3 hL
      (isPGroup_zpowers_of_pow_three' hw3)
      (Subgroup.zpowers_le.mpr (Sec13.centralizer_le_normalizer_zpowers c
        (Subgroup.mem_centralizer_singleton_iff.mpr hwc))) (Subgroup.mem_zpowers w)
  obtain ⟨y, hy3, hyN, hye₀, hyact⟩ := hD.exists_y he₀ he₀c
  obtain ⟨y₁, hy₁3, hy₁N, hy₁e₁, hy₁act⟩ := hD.exists_y he₁ he₁c
  have hyc : (y : G) * c = c * y :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer y.2))
  have hy₁c : (y₁ : G) * c = c * y₁ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer y₁.2))
  have hyM : (y : G) ∈ M := hmemM _ hyc hye₀
  set x := g * (y₁ : G) * g⁻¹ with hx
  have hxc : x * c = c * x := by
    have h1 : (y₁ : G) * e₁ = e₁ * y₁ := hy₁e₁
    rw [he₁def] at h1
    calc x * c = g * ((y₁ : G) * (g⁻¹ * c * g)) * g⁻¹ := by rw [hx]; group
      _ = g * ((g⁻¹ * c * g) * y₁) * g⁻¹ := by rw [h1]
      _ = c * x := by rw [hx]; group
  have hxe₀ : x * e₀ = e₀ * x := by
    calc x * e₀ = g * ((y₁ : G) * c) * g⁻¹ := by rw [hx, he₀def]; group
      _ = g * (c * y₁) * g⁻¹ := by rw [hy₁c]
      _ = e₀ * x := by rw [hx, he₀def]; group
  have hxM : x ∈ M := hmemM _ hxc hxe₀
  have hx3 : x ^ 3 = 1 := by rw [hx, conj_pow, hy₁3, mul_one, mul_inv_cancel]
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h45L x hx3 hxc
  have hxN : x ∈ Subgroup.normalizer (E : Set G) :=
    mul_mem (mul_mem hgE hy₁N) (inv_mem hgE)
  set Y := πM ⟨y, hyM⟩ with hY
  set X := πM ⟨x, hxM⟩ with hX
  set C := πM ⟨c, hcM⟩ with hC
  set E0 := πM ⟨e₀, he₀M⟩ with hE0
  have hCZ : C ∈ Subgroup.center (M ⧸ θM) :=
    mk_mem_center_of_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) hcM
  have hE0Z : E0 ∈ Subgroup.center (M ⧸ θM) :=
    mk_mem_center_of_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀)) he₀M
  obtain ⟨i, hi⟩ : ∃ i : ℤ, X * Y * X⁻¹ * Y⁻¹ = C ^ i := by
    have hxyL : x * y * x⁻¹ * (y : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxL _).mp y.2) (L.inv_mem y.2)
    have hxyM : x * y * x⁻¹ * (y : G)⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM)
    have hZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨_, hxyL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      have h1 : (⟨_, hxyL⟩ : L) = L.normalizerMonoidHom ⟨x, hxL⟩ y * y⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_inv, ← thetaBarAct_mk]
      refine mul_inv_mem_center_of_commute ?_
      rw [← hyact, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxe₀
    obtain ⟨k, hk⟩ := hD.exists_zpow_mul_mem_theta hZ
    have hmem : x * y * x⁻¹ * (y : G)⁻¹ * c ^ (-k) ∈ M := M.mul_mem hxyM (M.zpow_mem hcM _)
    obtain ⟨n, hn, hne⟩ := hθLM _ hk hmem
    have hn' : n = ⟨_, hmem⟩ := Subtype.ext hne
    have h2 : πM ⟨_, hmem⟩ = 1 := by
      rw [← hn', hπM, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    refine ⟨k, ?_⟩
    have e1 : (⟨_, hmem⟩ : M) =
        ⟨x, hxM⟩ * ⟨y, hyM⟩ * (⟨x, hxM⟩ : M)⁻¹ * (⟨y, hyM⟩ : M)⁻¹ * (⟨c, hcM⟩ : M) ^ (-k) :=
      Subtype.ext (by simp)
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, ← hY, ← hX,
      ← hC] at h2
    calc X * Y * X⁻¹ * Y⁻¹ = X * Y * X⁻¹ * Y⁻¹ * C ^ (-k) * C ^ k := by group
      _ = C ^ k := by rw [h2, one_mul]
  obtain ⟨j, hj⟩ : ∃ j : ℤ, Y * X * Y⁻¹ * X⁻¹ = E0 ^ j := by
    set y' := g⁻¹ * (y : G) * g with hy'
    have hy'3 : y' ^ 3 = 1 := by
      rw [hy', show g⁻¹ * (y : G) * g = g⁻¹ * y * g⁻¹⁻¹ by group, conj_pow, hy3, mul_one,
        mul_inv_cancel]
    have hy'c : y' * c = c * y' := by
      have h1 : (y : G) * (g * c * g⁻¹) = (g * c * g⁻¹) * y := hye₀
      calc y' * c = g⁻¹ * ((y : G) * (g * c * g⁻¹)) * g := by rw [hy']; group
        _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [h1]
        _ = c * y' := by rw [hy']; group
    have hy'e₁ : y' * e₁ = e₁ * y' := by
      calc y' * e₁ = g⁻¹ * ((y : G) * c) * g := by rw [hy', he₁def]; group
        _ = g⁻¹ * (c * y) * g := by rw [hyc]
        _ = e₁ * y' := by rw [hy', he₁def]; group
    have hy'L : y' ∈ Subgroup.normalizer (L : Set G) := h45L y' hy'3 hy'c
    have hwL : y' * y₁ * y'⁻¹ * (y₁ : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hy'L _).mp y₁.2) (L.inv_mem y₁.2)
    have hZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨_, hwL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      have h1 : (⟨_, hwL⟩ : L) = L.normalizerMonoidHom ⟨y', hy'L⟩ y₁ * y₁⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_inv, ← thetaBarAct_mk]
      refine mul_inv_mem_center_of_commute ?_
      rw [← hy₁act, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hy'e₁
    obtain ⟨k, hk⟩ := hD.exists_zpow_mul_mem_theta hZ
    have hkC : y' * y₁ * y'⁻¹ * (y₁ : G)⁻¹ * c ^ (-k) ∈
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL] at hk
      exact hk.2
    have hkg : g * (y' * y₁ * y'⁻¹ * (y₁ : G)⁻¹ * c ^ (-k)) * g⁻¹ ∈
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e₀} : Set G)) := by
      rw [← map_conj_centralizer_singleton, ← map_inSubgroup_aschbacherSolvableCore_mulEquiv
        Nat.prime_three]
      exact ⟨_, hkC, rfl⟩
    have e2 : g * (y' * y₁ * y'⁻¹ * (y₁ : G)⁻¹ * c ^ (-k)) * g⁻¹ =
        (y : G) * x * (y : G)⁻¹ * x⁻¹ * e₀ ^ (-k) := by
      rw [hy', hx, he₀def, conj_zpow]
      group
    rw [e2] at hkg
    have hmem : (y : G) * x * (y : G)⁻¹ * x⁻¹ * e₀ ^ (-k) ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM)) (M.inv_mem hxM))
        (M.zpow_mem he₀M _)
    obtain ⟨n, hn, hne⟩ := inf_le_inSubgroup_theta hMe₀ ⟨hkg, hmem⟩
    have hn' : n = ⟨_, hmem⟩ := Subtype.ext hne
    have h2 : πM ⟨_, hmem⟩ = 1 := by
      rw [← hn', hπM, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    refine ⟨k, ?_⟩
    have e1 : (⟨_, hmem⟩ : M) =
        ⟨y, hyM⟩ * ⟨x, hxM⟩ * (⟨y, hyM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M)⁻¹ * (⟨e₀, he₀M⟩ : M) ^ (-k) :=
      Subtype.ext (by simp)
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, ← hY, ← hX,
      ← hE0] at h2
    calc Y * X * Y⁻¹ * X⁻¹ = Y * X * Y⁻¹ * X⁻¹ * E0 ^ (-k) * E0 ^ k := by group
      _ = E0 ^ k := by rw [h2, one_mul]
  have hπE : ∀ (e : G) (he : e ∈ E), πM ⟨e, hEM he⟩ = 1 → e = 1 := by
    intro e he h1
    rw [hπM, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h := inf_inSubgroup_theta_eq_bot hD.isPGroup (L := M)
    have hmem : e ∈ E ⊓ inSubgroup (aschbacherSolvableCore 3) M := ⟨he, ⟨_, h1, rfl⟩⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hd1 : E0 ∉ Subgroup.zpowers C := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hmem : e₀ * c ^ (-k) ∈ E := E.mul_mem he₀ (E.zpow_mem hD.mem_E _)
    have h1 : πM ⟨e₀ * c ^ (-k), hEM hmem⟩ = 1 := by
      have e1 : (⟨e₀ * c ^ (-k), hEM hmem⟩ : M) = ⟨e₀, he₀M⟩ * (⟨c, hcM⟩ : M) ^ (-k) :=
        Subtype.ext (by simp)
      rw [e1, map_mul, map_zpow, ← hE0, ← hC, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
    have h2 := hπE _ hmem h1
    apply he₀c
    have e2 : e₀ = (e₀ * c ^ (-k)) * c ^ k := by group
    rw [e2, h2, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  have hCo : orderOf C = 3 := by
    refine orderOf_eq_prime ?_ fun h => hD.ne_one (hπE c hD.mem_E h)
    rw [hC, ← map_pow]
    have h3 : (⟨c, hcM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hD.pow_three hD.mem_E)
    rw [h3, map_one]
  have hE0o' : orderOf E0 = 3 := by
    refine orderOf_eq_prime ?_ fun h => hd1 (h ▸ Subgroup.one_mem _)
    rw [hE0, ← map_pow]
    have h3 : (⟨e₀, he₀M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hD.pow_three he₀)
    rw [h3, map_one]
  have hXY : X * Y = Y * X := by
    have hbot := inf_zpowers_eq_bot_of_not_mem hE0o' hd1
    have hmem : E0 ^ j ∈ Subgroup.zpowers C ⊓ Subgroup.zpowers E0 := by
      refine ⟨?_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩
      have e1 : E0 ^ j = (C ^ i)⁻¹ := by rw [← hj, ← hi]; group
      rw [e1]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : Y * X * Y⁻¹ * X⁻¹ = 1 := by rw [hj, hmem]
    calc X * Y = (Y * X * Y⁻¹ * X⁻¹)⁻¹ * (Y * X) := by group
      _ = Y * X := by rw [h1, inv_one, one_mul]
  have hmoved : ∀ {f : G} (hf : f ∈ E) (hfc : f ∉ Subgroup.zpowers c) (u : L),
      (u : G) ∈ Subgroup.normalizer (E : Set G) → (u : G) ^ 3 = 1 →
      thetaBarAct L ⟨f, hD.le_normalizer hf⟩ =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) u) →
      ∃ e' ∈ E, (u : G) * e' * (u : G)⁻¹ ≠ e' := by
    intro f hf hfc u huN hu3 huact
    obtain ⟨e', he', he'n⟩ : ∃ e' ∈ E, e' ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers f := by
      by_contra hcon
      push Not at hcon
      have h := Subgroup.card_le_of_le
        (show E ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers f from hcon)
      rw [hD.isE27.2, hD.card_sup_eq_nine hf hfc] at h
      omega
    obtain ⟨l', hl'3, hl', -⟩ := hD.exists_part he'
    have hb'3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) l' ^ 3 = 1 := by
      rw [← map_pow]
      have h3 : l' ^ 3 = 1 := Subtype.ext (by simpa using hl'3)
      rw [h3, map_one]
    have hub3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) u ^ 3 = 1 := by
      rw [← map_pow]
      have h3 : u ^ 3 = 1 := Subtype.ext (by simpa using hu3)
      rw [h3, map_one]
    have hnc := hD.commutator_ne_one hFE hperf hev hf he' hfc he'n huact hl' hub3 hb'3
    exact ⟨e', he', fun h => hnc ((hD.conj_eq_self_iff u huN he' hl').mp h)⟩
  obtain ⟨e', he', hye'⟩ := hmoved he₀ he₀c y hyN hy3 hyact
  obtain ⟨e'', he'', hy₁e''⟩ := hmoved he₁ he₁c y₁ hy₁N hy₁3 hy₁act
  set c' : E := ⟨c, hD.mem_E⟩ with hc'
  set Sc : Subgroup G := ((transvectionGroup E c').comap E.normalizerMonoidHom).map
    (Subgroup.normalizer (E : Set G)).subtype with hSc
  have hScmem : ∀ g ∈ Sc, ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := by
    rintro _ ⟨g, hg, rfl⟩ e he
    have h1 := (Subgroup.mem_comap.mp hg).2 ⟨e, he⟩
    rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
      Subgroup.coe_inv] at h1
    exact h1
  have hTE : ∀ g ∈ E, g ∈ Sc := by
    intro g hg
    refine ⟨⟨g, Subgroup.le_normalizer hg⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    refine ⟨Subtype.ext ?_, fun a => ?_⟩
    · rw [Sec4.normalizerMonoidHom_apply_coe]
      change g * c * g⁻¹ = c
      rw [hD.comm hg hD.mem_E, mul_inv_cancel_right]
    · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
        Subgroup.coe_inv, hD.comm hg a.2, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hySc : (y : G) ∈ Sc := by
    refine ⟨⟨y, hyN⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    refine ⟨Subtype.ext ?_, fun a => ?_⟩
    · rw [Sec4.normalizerMonoidHom_apply_coe]
      change (y : G) * c * (y : G)⁻¹ = c
      rw [hyc, mul_inv_cancel_right]
    · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
        Subgroup.coe_inv]
      exact hD.commutator_mem_zpowers y.2 hyN a.2
  set D := W ⊔ Subgroup.zpowers (y : G) with hDdef
  have hDSc : D ≤ Sc := sup_le (fun w hw => hTE w (hWE hw)) (Subgroup.zpowers_le.mpr hySc)
  have hDN : D ≤ Subgroup.normalizer (E : Set G) :=
    sup_le (fun w hw => Subgroup.le_normalizer (hWE hw)) (Subgroup.zpowers_le.mpr hyN)
  have himW : Subgroup.zpowers C ⊔ Subgroup.zpowers E0 ≤ (W.subgroupOf M).map πM := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact ⟨⟨c, hcM⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)), rfl⟩
    · exact ⟨⟨e₀, he₀M⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀)), rfl⟩
  have himD : Subgroup.zpowers C ⊔ Subgroup.zpowers E0 ⊔ Subgroup.zpowers Y ≤
      (D.subgroupOf M).map πM := by
    refine sup_le (himW.trans (Subgroup.map_mono ?_)) (Subgroup.zpowers_le.mpr ?_)
    · intro w hw
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hw))
    · exact ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), rfl⟩
  have hd2 : Y ∉ Subgroup.zpowers C ⊔ Subgroup.zpowers E0 := by
    intro h
    obtain ⟨w, hw, hwY⟩ := himW h
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
    have h1 := conj_eq_of_mk_eq hEM hD.isPGroup (a := ⟨y, hyM⟩) (b := w)
      (Subgroup.le_normalizer (hWE hwW)) hyN hwY.symm he'
    rw [hD.comm (hWE hwW) he', mul_inv_cancel_right] at h1
    exact hye' h1
  have hd3 : X ∉ Subgroup.zpowers C ⊔ Subgroup.zpowers E0 ⊔ Subgroup.zpowers Y := by
    intro h
    obtain ⟨d, hd, hdX⟩ := himD h
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hge'' : g * e'' * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE e'').mp he''
    have h1 := conj_eq_of_mk_eq hEM hD.isPGroup (a := ⟨x, hxM⟩) (b := d) (hDN hdD) hxN
      hdX.symm hge''
    have h2 := hScmem _ (hDSc hdD) _ hge''
    rw [← h1] at h2
    have hk := hD.commutator_mem_zpowers y₁.2 hy₁N he''
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hk
    have e3 : x * (g * e'' * g⁻¹) * x⁻¹ * (g * e'' * g⁻¹)⁻¹ = e₀ ^ k := by
      rw [hx, he₀def, conj_zpow, hk']
      group
    rw [e3] at h2
    have he₀3 : orderOf e₀ = 3 :=
      orderOf_eq_prime (hD.pow_three he₀) fun h => he₀c (h ▸ Subgroup.one_mem _)
    have hbot := inf_zpowers_eq_bot_of_not_mem he₀3 he₀c
    have hmem : e₀ ^ k ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers e₀ :=
      ⟨h2, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
    rw [hbot, Subgroup.mem_bot, he₀def, conj_zpow] at hmem
    have h3 : c ^ k = 1 := by
      have := congrArg (fun w => g⁻¹ * w * g) hmem
      simpa [mul_assoc] using this
    apply hy₁e''
    have h4 : (y₁ : G) * e'' * (y₁ : G)⁻¹ * e''⁻¹ = 1 := by rw [← hk', h3]
    calc (y₁ : G) * e'' * (y₁ : G)⁻¹ = ((y₁ : G) * e'' * (y₁ : G)⁻¹ * e''⁻¹) * e'' := by group
      _ = e'' := by rw [h4, one_mul]
  have hcube : ∀ (g : G) (hgM : g ∈ M), g ^ 3 = 1 → πM ⟨g, hgM⟩ ^ 3 = 1 := by
    intro g hgM hg3
    rw [← map_pow]
    have h3 : (⟨g, hgM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [h3, map_one]
  have hC3 : C ^ 3 = 1 := hcube c hcM (hD.pow_three hD.mem_E)
  have hC3' : ∀ w ∈ Subgroup.zpowers C, w ^ 3 = 1 := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hC3, one_zpow]
  have hYo : orderOf Y = 3 :=
    orderOf_eq_prime (hcube y hyM hy3) fun h => hd2 (h ▸ Subgroup.one_mem _)
  have hXo : orderOf X = 3 :=
    orderOf_eq_prime (hcube x hxM hx3) fun h => hd3 (h ▸ Subgroup.one_mem _)
  set B₁ := Subgroup.zpowers C ⊔ Subgroup.zpowers E0 with hB₁
  set B₂ := B₁ ⊔ Subgroup.zpowers Y with hB₂
  have hB₁Z : B₁ ≤ Subgroup.center (M ⧸ θM) :=
    sup_le (Subgroup.zpowers_le.mpr hCZ) (Subgroup.zpowers_le.mpr hE0Z)
  have hcenOf : ∀ (v : M ⧸ θM) (S : Subgroup (M ⧸ θM)), S ≤ Subgroup.centralizer {v} →
      v ∈ Subgroup.centralizer (S : Set (M ⧸ θM)) := fun v S hS =>
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hS hh))
  have hZcen : ∀ v : M ⧸ θM, Subgroup.center (M ⧸ θM) ≤ Subgroup.centralizer {v} :=
    fun v z hz => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp hz v).symm
  obtain ⟨hB₁9, hB₁c, hB₁e⟩ := card_sup_zpowers_of_disjoint
    (hcenOf E0 _ ((Subgroup.zpowers_le.mpr hCZ).trans (hZcen E0))) inferInstance hC3' hE0o'
    (inf_zpowers_eq_bot_of_not_mem hE0o' hd1)
  obtain ⟨hB₂27, hB₂c, hB₂e⟩ := card_sup_zpowers_of_disjoint
    (hcenOf Y _ (hB₁Z.trans (hZcen Y))) hB₁c hB₁e hYo (inf_zpowers_eq_bot_of_not_mem hYo hd2)
  have hB₂X : B₂ ≤ Subgroup.centralizer {X} :=
    sup_le (hB₁Z.trans (hZcen X))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hXY.symm))
  obtain ⟨hFt81, hFtc, hFte⟩ := card_sup_zpowers_of_disjoint (hcenOf X _ hB₂X) hB₂c hB₂e hXo
    (inf_zpowers_eq_bot_of_not_mem hXo hd3)
  rw [hB₂27, hB₁9, Nat.card_zpowers, hCo] at hFt81
  set Ft := B₂ ⊔ Subgroup.zpowers X with hFt
  have hFt81' : Nat.card Ft = 81 := by rw [hFt81]
  set Fhat : Subgroup G := (Ft.comap πM).map M.subtype with hFhat
  have hFhatM : Fhat ≤ M := Subgroup.map_subtype_le _
  have hFhatcard : Nat.card Fhat = Nat.card θM * 81 := by
    rw [hFhat, Subgroup.card_map_of_injective M.subtype_injective, ← hFt81']
    exact QuotientGroup.card_preimage_mk θM (Ft : Set (M ⧸ θM))
  have hmemF : ∀ (g : G) (hg : g ∈ M), πM ⟨g, hg⟩ ∈ Ft → g ∈ Fhat := fun g hg h =>
    ⟨⟨g, hg⟩, h, rfl⟩
  have hB₁Ft : B₁ ≤ Ft := le_sup_left.trans le_sup_left
  have hDF : D ≤ Fhat := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact hmemF c hcM (hB₁Ft (Subgroup.mem_sup_left (Subgroup.mem_zpowers C)))
    · exact hmemF e₀ he₀M (hB₁Ft (Subgroup.mem_sup_right (Subgroup.mem_zpowers E0)))
    · exact hmemF y hyM ((le_sup_left : B₂ ≤ Ft)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers Y)))
  have hD3 : IsPGroup 3 D :=
    IsPGroup.to_sup_of_normal_left' (hD.isPGroup.to_le hWE) (isPGroup_zpowers_of_pow_three' hy3)
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hyM))
  obtain ⟨Q, hQ⟩ := (hD3.comap_subtype (K := Fhat)).exists_le_sylow
  set F := (Q : Subgroup Fhat).map Fhat.subtype with hF
  have hFS : CFSG.ABGLocalTools.IsSylowOf 3 F Fhat := ⟨Q, rfl⟩
  have hDF' : D ≤ F := fun d hd => ⟨⟨d, hDF hd⟩, hQ hd, rfl⟩
  have hF81 : Nat.card F = 81 := by
    rw [hFS.card_eq, hFhatcard]
    have h3 : ¬ 3 ∣ Nat.card θM := three_not_dvd_card_aschbacherSolvableCore
    have hθ0 : Nat.card θM ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hθ0 (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3, zero_add, show (81 : ℕ) = 3 ^ 4 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  have hFM : F ≤ M := (Subgroup.map_subtype_le _).trans hFhatM
  have hFFt : ∀ (g : G) (hg : g ∈ F), πM ⟨g, hFM hg⟩ ∈ Ft := by
    intro g hg
    have hgF : g ∈ Fhat := (Subgroup.map_subtype_le _) hg
    obtain ⟨m, hm, hmg⟩ := hgF
    have hm' : m = ⟨g, hFM hg⟩ := Subtype.ext hmg
    rw [← hm']
    exact hm
  have hinj := injOn_mk_of_isPGroup (G := M) Nat.prime_three (A := F.subgroupOf M)
    hFS.isPGroup.comap_subtype
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
    · apply Subtype.ext
      have hab : πM ⟨(a : G) * b, hFM (F.mul_mem a.2 b.2)⟩ =
          πM ⟨(b : G) * a, hFM (F.mul_mem b.2 a.2)⟩ := by
        have e1 : (⟨(a : G) * b, hFM (F.mul_mem a.2 b.2)⟩ : M) =
            ⟨a, hFM a.2⟩ * ⟨b, hFM b.2⟩ := rfl
        have e2 : (⟨(b : G) * a, hFM (F.mul_mem b.2 a.2)⟩ : M) =
            ⟨b, hFM b.2⟩ * ⟨a, hFM a.2⟩ := rfl
        rw [e1, e2, map_mul, map_mul]
        exact congrArg Subtype.val (hFtc.is_comm.comm ⟨_, hFFt a a.2⟩ ⟨_, hFFt b b.2⟩)
      have h := hinj (Subgroup.mem_subgroupOf.mpr (F.mul_mem a.2 b.2))
        (Subgroup.mem_subgroupOf.mpr (F.mul_mem b.2 a.2)) hab
      exact congrArg (fun m : M => (m : G)) h
    · have h1 : πM ⟨g ^ 3, hFM (F.pow_mem hg 3)⟩ = πM 1 := by
        have e1 : (⟨g ^ 3, hFM (F.pow_mem hg 3)⟩ : M) = ⟨g, hFM hg⟩ ^ 3 :=
          Subtype.ext (by simp)
        rw [e1, map_pow, map_one]
        exact hFte _ (hFFt g hg)
      have h := hinj (Subgroup.mem_subgroupOf.mpr (F.pow_mem hg 3)) (Subgroup.one_mem _) h1
      exact congrArg (fun m : M => (m : G)) h
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := fun f hf =>
    h45L f (hFe.2 f hf) (Subgroup.mem_centralizer_singleton_iff.mp (hMc (hFM hf)))
  have hcF : c ∈ F := hDF' (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
  have he₀F : e₀ ∈ F :=
    hDF' (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀)))
  have hyF : (y : G) ∈ F := hDF' (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hyZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) y ∉
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro h
    apply he₀c
    apply hD.mem_zpowers_of_thetaBarAct he₀
    rw [hyact]
    exact conj_eq_one_of_mem_center h
  refine ⟨F, hFe, hF81, hFN, hcF, y, hyF, hy3, hyZ, (y : G)⁻¹ * e₀,
    F.mul_mem (F.inv_mem hyF) he₀F, ?_, ?_⟩
  · have hN : (y : G)⁻¹ * e₀ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (inv_mem (Subgroup.le_normalizer y.2)) (hD.le_normalizer he₀)
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct hN]
    have e1 : (⟨(y : G)⁻¹ * e₀, hN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨(y : G), Subgroup.le_normalizer y.2⟩)⁻¹ * ⟨e₀, hD.le_normalizer he₀⟩ := rfl
    rw [e1, map_mul, map_inv, hyact, thetaBarAct_of_mem y.2, inv_mul_cancel]
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply he₀c
    apply hD.mem_zpowers_of_mem_L he₀
    have e2 : e₀ = (y : G) * c ^ k := by rw [hk, mul_inv_cancel_left]
    rw [e2]
    exact L.mul_mem y.2 (L.zpow_mem hD.mem_L k)

end DiagHyp

end CFSG.RankThree.PartTwo.Sec12.Item125Diag
