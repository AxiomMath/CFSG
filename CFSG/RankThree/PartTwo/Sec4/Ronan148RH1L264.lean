module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.GorensteinWalter CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace L264

section Facts

variable {X : Type} [Group X] [Finite X]

theorem isCyclic_centralizer (e : X ≃* PSL2 (GaloisField 2 6)) {y : X} (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) : IsCyclic (Subgroup.centralizer ({y} : Set X)) :=
  Item462AltProof.ChevTwoL2.isCyclic_of_le_centralizer_psl2 (by norm_num)
    Item434SmallTwoOther.L264.card_gf64 e hy3 hy1
    fun u hu => (Subgroup.mem_centralizer_singleton_iff.mp hu).symm

theorem card_autFix_outer (e : X ≃* PSL2 (GaloisField 2 6))
    {α : MulAut X} (h3 : α ^ 3 = 1) (hα : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Nat.card (Sec4.autFix α) = 60 := by
  set α' := MulAut.congr e α with hα'def
  have h3' : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, h3, map_one]
  have hD : α' ∉ (pglAction (GaloisField 2 6)).range := by
    intro hD
    apply hα
    exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e α).mp
      (CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three hD h3')
  obtain ⟨-, h60⟩ := Item434SmallTwoOther.L264.isCoatom_and_card_fixed h3' hD
  rw [← autFix_eq_signalizerFixedSubgroup, autFix_congr,
    Subgroup.card_map_of_injective e.injective] at h60
  exact h60

theorem card_le_nine (e : X ≃* PSL2 (GaloisField 2 6)) {E : Subgroup (MulAut X)}
    (hE : ∀ α ∈ E, α ^ 3 = 1) :
    Nat.card E ≤ 9 ∧ (9 ≤ Nat.card E →
      ∃ α ∈ E, α ≠ 1 ∧ α ∈ (MulAut.conj : X →* MulAut X).range) := by
  set ψ : MulAut (PSL2 (GaloisField 2 6)) →* (GaloisField 2 6 ≃+* GaloisField 2 6) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut (GaloisField 2 6)).symm.toMonoidHom
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'def
  have hcardE : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hE' : ∀ β ∈ E', β ^ 3 = 1 := by
    rintro _ ⟨α, hα, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE α hα, map_one]
  have hker : Nat.card (E' ⊓ ψ.ker : Subgroup _) ≤ 3 :=
    Item434SmallTwoOther.L264.card_le_three_of_le_range_pglAction (fun β hβ => hE' β hβ.1)
      fun β hβ => CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hβ.2
  have himg : Nat.card (E'.map ψ) ≤ 3 :=
    Item434SmallTwoOther.L264.card_map_rightHom_le_three hE'
  have hcard := Item434Alt.card_eq_card_inf_ker_mul_card_map ψ E'
  refine ⟨?_, fun h9 => ?_⟩
  · rw [← hcardE, hcard]
    calc Nat.card (E' ⊓ ψ.ker : Subgroup _) * Nat.card (E'.map ψ) ≤ 3 * 3 :=
          Nat.mul_le_mul hker himg
      _ = 9 := by norm_num
  · have hker3 : 3 ≤ Nat.card (E' ⊓ ψ.ker : Subgroup _) := by
      by_contra hlt
      have : Nat.card E' ≤ 2 * 3 := by rw [hcard]; exact Nat.mul_le_mul (by omega) himg
      omega
    obtain ⟨c, hcE, hc1⟩ : ∃ c ∈ E' ⊓ ψ.ker, c ≠ 1 := by
      rcases (E' ⊓ ψ.ker).bot_or_exists_ne_one with hbot | h
      · rw [hbot, Subgroup.card_bot] at hker3
        omega
      · exact h
    obtain ⟨α, hαE, hαc⟩ := hcE.1
    refine ⟨α, hαE, fun h => hc1 ?_, ?_⟩
    · rw [← hαc, h, map_one]
    · have hinn := CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three
        (CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hcE.2) (hE' _ hcE.1)
      rw [← hαc] at hinn
      exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e α).mp hinn

theorem nine_dvd_card_centralizer (e : X ≃* PSL2 (GaloisField 2 6)) {y : X} (hy3 : y ^ 3 = 1) :
    9 ∣ Nat.card (Subgroup.centralizer ({y} : Set X)) := by
  obtain ⟨R, hR9, hRy⟩ := Item434SmallTwoOther.L264.exists_sylow_commute
    (t := e y) (by rw [← map_pow, hy3, map_one])
  have hle : R.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({y} : Set X) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hRy r hr
  have h := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective e.symm.injective] at h
  exact hR9.trans h

end Facts

theorem mem_zpowers_of_pow_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C] {g z : C} {n : ℕ}
    (hn : 0 < n) (hg : orderOf g = n) (hz : z ^ n = 1) : z ∈ Subgroup.zpowers g := by
  classical
  haveI : Fintype C := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) hn
  set T : Finset C := Finset.univ.filter (fun a => a ∈ Subgroup.zpowers g)
  set U : Finset C := Finset.univ.filter (fun a => a ^ n = 1)
  have hTU : T ⊆ U := by
    intro a ha
    simp only [T, U, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
      one_zpow]
  have hT : T.card = n := by
    have h1 : T.card = Fintype.card (Subgroup.zpowers g) := by
      rw [Fintype.card_subtype]
    rw [h1, ← Nat.card_eq_fintype_card, Nat.card_zpowers, hg]
  have hTU' : T = U := Finset.eq_of_subset_of_card_le hTU (by rw [hT]; exact hle)
  have hzU : z ∈ U := by simp [U, hz]
  rw [← hTU'] at hzU
  simpa [T] using hzU

section EF

variable {G : Type} [Group G] [Finite G]

theorem zpowers_inf_eq_bot {x : G} {H : Subgroup G} (hx3 : x ^ 3 = 1) (hxH : x ∉ H) :
    Subgroup.zpowers x ⊓ H = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  by_contra hz
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, orderOf_eq_prime hz3 hz])
  have hxz : x ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers x
  exact hxH ((Subgroup.zpowers_le.mpr hz2) hxz)

theorem exists_nine_le {W : Subgroup G} (hWe : CFSG.Assembly.IsElemAbelian 3 W)
    (hgt : 3 < Nat.card W) :
    ∃ W' : Subgroup G, W' ≤ W ∧ CFSG.Assembly.IsElemAbelian 3 W' ∧ Nat.card W' = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWpg : IsPGroup 3 W := fun g => ⟨1, Subtype.ext (by simpa using hWe.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWpg
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have h1 : 3 ^ k ≤ 3 := by
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    rw [hk] at hgt
    omega
  obtain ⟨W₀, hW₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
    (by rw [hk]; exact pow_dvd_pow 3 hk2)
  refine ⟨W₀.map W.subtype, Subgroup.map_subtype_le W₀,
    isElemAbelian_mono (Subgroup.map_subtype_le W₀) hWe, ?_⟩
  rw [Subgroup.card_map_of_injective W.subtype_injective, hW₀]
  norm_num

theorem mem_normalizer_zpowers_of_commute {g t : G} (h : t * g = g * t) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
    (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
  exact ((show Commute t g from h).zpow_left k).eq

theorem false_of_partTwo_ext (hEF : partTwoE G = partTwoF G) {E : Subgroup G}
    (hE : E ∈ partTwoE G) {f : G} (hf3 : f ^ 3 = 1) (hfE : f ∉ E) (hfc : ∀ e ∈ E, f * e = e * f) :
    False := by
  have hc : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute f x from hfc x hx).zpow_left k).eq.symm
  have hBe : CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers f) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hE.1
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hf3) hc
  have hf1 : f ≠ 1 := fun h => hfE (h ▸ E.one_mem)
  have hinf : E ⊓ Subgroup.zpowers f = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_eq_bot hf3 hfE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBc : Nat.card ↥(E ⊔ Subgroup.zpowers f) = 81 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (Subgroup.zpowers f) hc).1
    rw [hinf, Subgroup.card_bot, mul_one, hE.2.1, Nat.card_zpowers, orderOf_eq_prime hf3 hf1] at h
    rw [h]
  obtain ⟨M, hBM, hmax⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup G => CFSG.Assembly.IsElemAbelian 3 M) hBe
  have hMF : M ∈ partTwoF G :=
    ⟨hmax.prop, fun B' hB' hMB' => le_antisymm (hmax.2 hB' hMB') hMB', E, hE,
      le_trans le_sup_left hBM⟩
  have hME : M ∈ partTwoE G := by
    rw [hEF]
    exact hMF
  have hle := Subgroup.card_le_of_le hBM
  rw [hBc, hME.2.1] at hle
  norm_num at hle

end EF

theorem zmod3_sub_one_eq_zero : ∀ a : ZMod 3, a * (a * a) - 1 = 0 → a - 1 = 0 := by decide

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_mem_zpowers_three {x d : G} (hd3 : d ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers d) (hx1 : x ≠ 1) : d ∈ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
    exact hx1 hx
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hx
  have heq : Subgroup.zpowers x = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, orderOf_eq_prime hd3 hd1])
  exact heq ▸ Subgroup.mem_zpowers d

theorem conj_pow_eq_of_forall {L : Subgroup G} {x y : G} (hyL : y ∈ L)
    (h : ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹) (n : ℕ) :
    ∀ l ∈ L, x ^ n * l * (x ^ n)⁻¹ = y ^ n * l * (y ^ n)⁻¹ := by
  induction n with
  | zero => intro l _; simp
  | succ k ih =>
    intro l hl
    have hyl : y * l * y⁻¹ ∈ L := mul_mem (mul_mem hyL hl) (inv_mem hyL)
    calc x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ = x ^ k * (x * l * x⁻¹) * (x ^ k)⁻¹ := by
          rw [pow_succ]; group
      _ = x ^ k * (y * l * y⁻¹) * (x ^ k)⁻¹ := by rw [h l hl]
      _ = y ^ k * (y * l * y⁻¹) * (y ^ k)⁻¹ := ih _ hyl
      _ = y ^ (k + 1) * l * (y ^ (k + 1))⁻¹ := by rw [pow_succ]; group

theorem false_of_l264 (hEF : partTwoE G = partTwoF G)
    {A L : Subgroup G} (hA : Late.IsE27 A) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center L = ⊥) (eL : L ≃* PSL2 (GaloisField 2 6)) {d : G} (hdA : d ∈ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hLd : ¬ L ≤ Subgroup.centralizer {d}) {t f : G} (htL : t ∈ L) (ht2 : orderOf t = 2)
    (htd : t * d = d * t) (hfL : f ∈ L) (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1) (hfd : f * d = d * f)
    (hinner : ∀ y ∈ L, ¬ ∀ l ∈ L, d * l * d⁻¹ = y * l * y⁻¹) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLC : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hc : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hdA
  have hNL : ∀ x ∈ Subgroup.normalizer (L : Set G), ∀ l ∈ L, x * l * x⁻¹ ∈ L :=
    fun x hx l hl => (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hCL : ∀ w ∈ Subgroup.centralizer (L : Set G), ∀ l ∈ L, w * l = l * w :=
    fun w hw l hl => (Subgroup.mem_centralizer_iff.mp hw l hl).symm
  have hdL : d ∉ L := fun h => hinner d h fun l _ => rfl
  have hY : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (L : Set G) →
      CFSG.Assembly.IsElemAbelian 3 W → Nat.card W = 9 → (∀ w ∈ W, w * d = d * w) → False := by
    intro W hWL hWe hW9 hWd
    have hcE : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ W, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((show Commute d y from (hWd y hy).symm).zpow_left i).eq
    have hEe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers d ⊔ W) :=
      CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup
        (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hd3) hWe hcE
    have hdW : d ∉ W := by
      intro h
      apply hLd
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hCL d (hWL h) l hl).symm
    have hd1 : d ≠ 1 := fun h => hdW (h ▸ W.one_mem)
    have hinf : Subgroup.zpowers d ⊓ W = ⊥ := zpowers_inf_eq_bot hd3 hdW
    have hE27 : Nat.card ↥(Subgroup.zpowers d ⊔ W) = 27 := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcE).1
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hd3 hd1, hW9] at h
      rw [h]
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      norm_num at ht2
    have hEt : Subgroup.zpowers d ⊔ W ≤
        Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_commute htd)) ?_
      intro w hw
      exact mem_normalizer_zpowers_of_commute (hCL w (hWL hw) t htL).symm
    have hEmem : Subgroup.zpowers d ⊔ W ∈ partTwoE G :=
      ⟨hEe, hE27, Subgroup.zpowers t, fun h => ht1 (Subgroup.zpowers_eq_bot.mp h),
        IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ht2]; norm_num⟩, hEt⟩
    have hfE : f ∉ Subgroup.zpowers d ⊔ W := by
      intro hf
      have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcE).2
      have hf' : f ∈ ((Subgroup.zpowers d ⊔ W : Subgroup G) : Set G) := hf
      rw [hset] at hf'
      obtain ⟨x, hx, w, hw, hxw⟩ := Set.mem_mul.mp hf'
      have hwC : w ∈ Subgroup.centralizer (L : Set G) := hWL hw
      by_cases hx1 : x = 1
      · apply hf1
        have hfw : f = w := by rw [← hxw, hx1, one_mul]
        exact hLC f hfL (hfw ▸ hwC)
      · have hdx := mem_zpowers_of_mem_zpowers_three hd3 hx hx1
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hdx
        have hxe : x = f * w⁻¹ := by rw [← hxw]; group
        have hwf : Commute f w⁻¹ :=
          (show Commute f w from (hCL w hwC f hfL).symm).inv_right
        apply hinner (f ^ j) (zpow_mem hfL j)
        intro l hl
        have hwl : w⁻¹ ^ j * l = l * w⁻¹ ^ j :=
          hCL _ (zpow_mem (inv_mem hwC) j) l hl
        rw [← hj, hxe, hwf.mul_zpow]
        calc f ^ j * w⁻¹ ^ j * l * (f ^ j * w⁻¹ ^ j)⁻¹
            = f ^ j * (w⁻¹ ^ j * l) * (w⁻¹ ^ j)⁻¹ * (f ^ j)⁻¹ := by group
          _ = f ^ j * (l * w⁻¹ ^ j) * (w⁻¹ ^ j)⁻¹ * (f ^ j)⁻¹ := by rw [hwl]
          _ = f ^ j * l * (f ^ j)⁻¹ := by group
    have hEf : Subgroup.zpowers d ⊔ W ≤ Subgroup.centralizer {f} :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hfd.symm))
        fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hCL w (hWL hw) f hfL)
    exact false_of_partTwo_ext hEF hEmem hf3 hfE fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hEf he)).symm
  set W := A ⊓ Subgroup.centralizer (L : Set G) with hWdef
  have hWA : W ≤ A := inf_le_left
  have hWe : CFSG.Assembly.IsElemAbelian 3 W := isElemAbelian_mono hWA hA.1
  have hW3 : Nat.card W ≤ 3 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨W', hW'W, hW'e, hW'9⟩ := exists_nine_le hWe hgt
    exact hY W' (hW'W.trans inf_le_right) hW'e hW'9 fun w hw => hAc w (hWA (hW'W hw)) d hdA
  set ρ : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρdef
  have hρ : ∀ (a : A) (l : L), ((ρ a l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun a l => rfl
  have hker : Nat.card ρ.ker = Nat.card W := by
    have hk : ρ.ker = (Subgroup.centralizer (L : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro h l hl
        have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) h
        simp only [hρ, MulAut.one_apply] at h1
        calc l * (a : G) = (a : G) * l * (a : G)⁻¹ * a := by rw [h1]
          _ = a * l := by group
      · intro h
        ext l
        rw [hρ, MulAut.one_apply, ← h l l.2]
        group
    rw [hk, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardA : Nat.card A = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]
  rw [hA.2, hker] at hcardA
  have hR3 : ∀ α ∈ ρ.range, α ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 a a.2)
    rw [this, map_one]
  obtain ⟨hR9, hRin⟩ := card_le_nine eL hR3
  have hR9' : 9 ≤ Nat.card ρ.range := by
    by_contra h
    push Not at h
    have : Nat.card W * Nat.card ρ.range ≤ 3 * 8 := Nat.mul_le_mul hW3 (by omega)
    omega
  have hWge : 3 ≤ Nat.card W := by
    by_contra h
    push Not at h
    have : Nat.card W * Nat.card ρ.range ≤ 2 * 9 := Nat.mul_le_mul (by omega) hR9
    omega
  obtain ⟨_, ⟨a1, rfl⟩, hα1, ⟨t0', ht0'⟩⟩ := hRin hR9'
  have ha1A : (a1 : G) ∈ A := a1.2
  have ht0L : (t0' : G) ∈ L := t0'.2
  have ht0c : ∀ l ∈ L, (a1 : G) * l * (a1 : G)⁻¹ = (t0' : G) * l * (t0' : G)⁻¹ := by
    intro l hl
    have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) ht0'
    simp only [hρ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  have ht01 : (t0' : G) ≠ 1 := by
    intro h
    apply hα1
    rw [← ht0']
    have : t0' = 1 := Subtype.ext h
    rw [this, map_one]
  have ht03 : (t0' : G) ^ 3 = 1 := by
    have hp := conj_pow_eq_of_forall ht0L ht0c 3
    apply hLC _ (pow_mem ht0L 3)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hp l hl
    rw [show (a1 : G) ^ 3 = 1 from hA.1.2 _ ha1A, one_mul, inv_one, mul_one] at h1
    calc l * (t0' : G) ^ 3 = (t0' : G) ^ 3 * l * ((t0' : G) ^ 3)⁻¹ * (t0' : G) ^ 3 := by
          rw [← h1]
      _ = (t0' : G) ^ 3 * l := by group
  have ht0A : ∀ x ∈ A, x * (t0' : G) * x⁻¹ = t0' := by
    intro x hx
    have hsL : x * (t0' : G) * x⁻¹ ∈ L := hNL x (hAN hx) _ ht0L
    have hxa : x * (a1 : G) = a1 * x := hAc x hx _ ha1A
    have hsc : ∀ m ∈ L, (x * (t0' : G) * x⁻¹) * m * (x * (t0' : G) * x⁻¹)⁻¹ =
        (t0' : G) * m * (t0' : G)⁻¹ := by
      intro m hm
      have hlL : x⁻¹ * m * x ∈ L := by
        have h2 := hNL x⁻¹ (inv_mem (hAN hx)) m hm
        simpa using h2
      have hxa' : x * (a1 : G) * x⁻¹ = a1 := by rw [hxa]; group
      calc (x * (t0' : G) * x⁻¹) * m * (x * (t0' : G) * x⁻¹)⁻¹
          = x * ((t0' : G) * (x⁻¹ * m * x) * (t0' : G)⁻¹) * x⁻¹ := by group
        _ = x * ((a1 : G) * (x⁻¹ * m * x) * (a1 : G)⁻¹) * x⁻¹ := by rw [ht0c _ hlL]
        _ = (x * (a1 : G) * x⁻¹) * m * (x * (a1 : G) * x⁻¹)⁻¹ := by group
        _ = (a1 : G) * m * (a1 : G)⁻¹ := by rw [hxa']
        _ = (t0' : G) * m * (t0' : G)⁻¹ := ht0c m hm
    have hmem : (t0' : G)⁻¹ * (x * (t0' : G) * x⁻¹) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h2 := hsc m hm
      calc m * ((t0' : G)⁻¹ * (x * (t0' : G) * x⁻¹))
          = (t0' : G)⁻¹ * ((t0' : G) * m * (t0' : G)⁻¹) * (x * (t0' : G) * x⁻¹) := by group
        _ = (t0' : G)⁻¹ * ((x * (t0' : G) * x⁻¹) * m * (x * (t0' : G) * x⁻¹)⁻¹) *
            (x * (t0' : G) * x⁻¹) := by rw [h2]
        _ = (t0' : G)⁻¹ * (x * (t0' : G) * x⁻¹) * m := by group
    have h1 := hLC _ (mul_mem (inv_mem ht0L) hsL) hmem
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  set w : G := (t0' : G)⁻¹ * a1 with hw
  have hwC : w ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := ht0c l hl
    calc l * w = (t0' : G)⁻¹ * ((t0' : G) * l * (t0' : G)⁻¹) * a1 := by rw [hw]; group
      _ = (t0' : G)⁻¹ * ((a1 : G) * l * (a1 : G)⁻¹) * a1 := by rw [h1]
      _ = w * l := by rw [hw]; group
  have hwA : ∀ x ∈ A, x * w = w * x := by
    intro x hx
    have h1 := ht0A x hx
    have hxa : x * (a1 : G) = a1 * x := hAc x hx _ ha1A
    have hxt : x * (t0' : G) = t0' * x := by
      calc x * (t0' : G) = x * (t0' : G) * x⁻¹ * x := by group
        _ = t0' * x := by rw [h1]
    have hxt' : x * (t0' : G)⁻¹ = (t0' : G)⁻¹ * x := by
      calc x * (t0' : G)⁻¹ = (t0' : G)⁻¹ * ((t0' : G) * x) * (t0' : G)⁻¹ := by group
        _ = (t0' : G)⁻¹ * (x * (t0' : G)) * (t0' : G)⁻¹ := by rw [hxt]
        _ = (t0' : G)⁻¹ * x := by group
    calc x * w = x * (t0' : G)⁻¹ * a1 := by rw [hw]; group
      _ = (t0' : G)⁻¹ * x * a1 := by rw [hxt']
      _ = (t0' : G)⁻¹ * (x * a1) := by group
      _ = (t0' : G)⁻¹ * (a1 * x) := by rw [hxa]
      _ = w * x := by rw [hw]; group
  have hat : (a1 : G) * t0' = t0' * a1 := by
    have h1 := ht0c _ ht0L
    calc (a1 : G) * t0' = (a1 : G) * t0' * (a1 : G)⁻¹ * a1 := by group
      _ = (t0' : G) * t0' * (t0' : G)⁻¹ * a1 := by rw [h1]
      _ = t0' * a1 := by group
  have hw3 : w ^ 3 = 1 := by
    have hc : Commute (t0' : G)⁻¹ a1 := (show Commute (t0' : G) a1 from hat.symm).inv_left
    rw [hw, hc.mul_pow, inv_pow, ht03, inv_one, one_mul]
    exact hA.1.2 _ ha1A
  by_cases hwA' : w ∈ A
  swap
  ·
    obtain ⟨c, hcW, hc1⟩ : ∃ c ∈ W, c ≠ 1 := by
      rcases W.bot_or_exists_ne_one with hb | h
      · rw [hb, Subgroup.card_bot] at hWge
        omega
      · exact h
    have hcA : c ∈ A := hcW.1
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := hcW.2
    have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
    have hcw : c * w = w * c := hwA c hcA
    have hwc : w ∉ Subgroup.zpowers c := fun h => hwA' ((Subgroup.zpowers_le.mpr hcA) h)
    obtain ⟨hW'e, hW'9⟩ := e9_of_commute hc3 hc1 hw3 hcw hwc
    refine hY _ (sup_le (Subgroup.zpowers_le.mpr hcC) (Subgroup.zpowers_le.mpr hwC)) hW'e hW'9 ?_
    intro x hx
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers w ≤ Subgroup.centralizer {d} :=
      sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hAc c hcA d hdA)))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hwA d hdA).symm))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have ht0A' : (t0' : G) ∈ A := by
    have h1 : (t0' : G) = a1 * w⁻¹ := by rw [hw]; group
    rw [h1]
    exact mul_mem ha1A (inv_mem hwA')
  have ht0'3 : t0' ^ 3 = 1 := Subtype.ext (by simpa using ht03)
  have ht0'1 : t0' ≠ 1 := fun h => ht01 (congrArg Subtype.val h)
  set C : Subgroup L := Subgroup.centralizer ({t0'} : Set L) with hCdef
  haveI hCcyc : IsCyclic C := isCyclic_centralizer eL ht0'1 ht0'3
  have h9C : 9 ∣ Nat.card C := nine_dvd_card_centralizer eL ht0'3
  obtain ⟨c0, hc0⟩ := IsCyclic.exists_generator (α := C)
  have hoc0 : orderOf c0 = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hc0
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hdiv0 : Nat.card C / 9 ≠ 0 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hC0) h9C
    omega
  set g0 : C := c0 ^ (Nat.card C / 9) with hg0
  have hog0 : orderOf g0 = 9 := by
    rw [hg0, orderOf_pow_of_dvd hdiv0 (by rw [hoc0]; exact Nat.div_dvd_of_dvd h9C), hoc0]
    exact Nat.div_div_self h9C hC0
  set g : G := ((g0 : L) : G) with hgdef
  have hgL : g ∈ L := (g0 : L).2
  have hog : orderOf g = 9 := by
    rw [hgdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hog0]
  have hgt : g * t0' = t0' * g := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp g0.2
    exact congrArg Subtype.val h1
  have hkey : ∀ x ∈ A, ∃ k : ℤ, x * g * x⁻¹ = g ^ k ∧ (3 : ℤ) ∣ k - 1 := by
    intro x hx
    have hhL : x * g * x⁻¹ ∈ L := hNL x (hAN hx) g hgL
    have hht : (x * g * x⁻¹) * t0' = t0' * (x * g * x⁻¹) := by
      have h1 := ht0A x hx
      calc (x * g * x⁻¹) * t0' = x * g * x⁻¹ * (x * (t0' : G) * x⁻¹) := by rw [h1]
        _ = x * (g * t0') * x⁻¹ := by group
        _ = x * (t0' * g) * x⁻¹ := by rw [hgt]
        _ = (x * (t0' : G) * x⁻¹) * (x * g * x⁻¹) := by group
        _ = t0' * (x * g * x⁻¹) := by rw [h1]
    have hh9 : (x * g * x⁻¹) ^ 9 = 1 := by
      rw [show x * g * x⁻¹ = MulAut.conj x g from rfl, ← map_pow, ← hog, pow_orderOf_eq_one,
        map_one]
    have hhC : (⟨x * g * x⁻¹, hhL⟩ : L) ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hht)
    have hmem := mem_zpowers_of_pow_eq_one (C := C) (g := g0) (z := ⟨⟨x * g * x⁻¹, hhL⟩, hhC⟩)
      (by norm_num) hog0 (Subtype.ext (Subtype.ext (by simpa using hh9)))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : x * g * x⁻¹ = g ^ k := by
      have h1 := congrArg (fun z : C => ((z : L) : G)) hk
      simp only [Subgroup.coe_zpow] at h1
      exact h1.symm
    refine ⟨k, hk', ?_⟩
    have hconj : ∀ m : ℤ, x * g ^ m * x⁻¹ = g ^ (k * m) := by
      intro m
      rw [show x * g ^ m * x⁻¹ = MulAut.conj x (g ^ m) from rfl, map_zpow, MulAut.conj_apply, hk',
        ← zpow_mul]
    have hx3 : x ^ 3 = 1 := hA.1.2 x hx
    have h3 : g ^ (k * (k * k)) = g := by
      have e1 : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := by
        have : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * g * (x * (x * x))⁻¹ := by
          group
        rw [this, ← pow_three, hx3]
        group
      rw [hk', hconj k, hconj (k * k)] at e1
      exact e1
    have h91 : g ^ (k * (k * k) - 1) = 1 := by
      rw [zpow_sub, h3, zpow_one, mul_inv_cancel]
    have h9 : ((9 : ℕ) : ℤ) ∣ k * (k * k) - 1 := by
      rw [← hog]
      exact orderOf_dvd_iff_zpow_eq_one.mpr h91
    have h3' : ((k * (k * k) - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (dvd_trans (by norm_num) h9)
    have h4 := zmod3_sub_one_eq_zero (k : ZMod 3) (by push_cast at h3'; exact h3')
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).mp (by push_cast; exact h4)
  have hg3 : g ^ 3 ∈ Subgroup.zpowers (t0' : G) := by
    have ht0C : t0' ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hot0 : orderOf (⟨t0', ht0C⟩ : C) = 3 :=
      orderOf_eq_prime (Subtype.ext ht0'3) fun h => ht0'1 (congrArg Subtype.val h)
    have hmem := mem_zpowers_of_pow_eq_one (C := C) (g := ⟨t0', ht0C⟩) (z := g0 ^ 3)
      (by norm_num) hot0 (by rw [← pow_mul, show 3 * 3 = orderOf g0 by rw [hog0],
        pow_orderOf_eq_one])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 := congrArg (fun z : C => ((z : L) : G)) hm
    simp only [Subgroup.coe_zpow, Subgroup.coe_pow] at h1
    exact ⟨m, h1⟩
  have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
    intro x hx
    obtain ⟨k, hk, j, hj⟩ := hkey x hx
    have hu : g * (g ^ k)⁻¹ = (g ^ 3) ^ (-j) := by
      rw [← zpow_neg, ← zpow_one_add, ← zpow_natCast g 3, ← zpow_mul]
      congr 1
      push_cast
      omega
    have h1 : g * x * g⁻¹ = (g * (x * g * x⁻¹)⁻¹) * x := by group
    rw [h1, hk, hu]
    exact mul_mem ((Subgroup.zpowers_le.mpr ht0A') (zpow_mem hg3 (-j))) hx
  have hgN : g ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_map_le (by rintro _ ⟨x, hx, rfl⟩; exact hgA x hx)
  have h1 : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (hN hgN) d).mp (Subgroup.mem_zpowers d)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
  have huL : g * (d * g * d⁻¹)⁻¹ ∈ L := mul_mem hgL (inv_mem (hNL d hdN g hgL))
  have hu1 : g * (d * g * d⁻¹)⁻¹ ≠ 1 := by
    intro hu
    have hdg : d * g * d⁻¹ = g := (mul_inv_eq_one.mp hu).symm
    set αd : MulAut L := L.normalizerMonoidHom ⟨d, hdN⟩ with hαd
    have hαd3 : αd ^ 3 = 1 := by
      rw [hαd, ← map_pow]
      have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hd3)
      rw [this, map_one]
    have hαdout : αd ∉ (MulAut.conj : L →* MulAut L).range := by
      rintro ⟨y, hy⟩
      apply hinner (y : G) y.2
      intro l hl
      have h2 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) hy
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hαd] at h2
      exact h2.symm
    have h60 := card_autFix_outer eL hαd3 hαdout
    have hgfix : (⟨g, hgL⟩ : L) ∈ Sec4.autFix αd := Subtype.ext hdg
    have hdvd := Subgroup.orderOf_dvd_natCard (Sec4.autFix αd) hgfix
    rw [h60, Subgroup.orderOf_mk, hog] at hdvd
    norm_num at hdvd
  have hum : g * (d * g * d⁻¹)⁻¹ = d ^ (m - 1) := by
    have h2 : d ^ m = g * (d * g * d⁻¹)⁻¹ * d := by rw [hm]; group
    rw [zpow_sub_one, h2]
    group
  apply hdL
  have hdu := mem_zpowers_of_mem_zpowers_three hd3
    (show g * (d * g * d⁻¹)⁻¹ ∈ Subgroup.zpowers d from hum ▸ zpow_mem (Subgroup.mem_zpowers d) _)
    hu1
  exact (Subgroup.zpowers_le.mpr huL) hdu

end Cfg

end L264

open L264

section Row




theorem row427_l264
    {S : Type} [Group S] [Finite S] (eS : S ≃* PSL2 (GaloisField 2 6)) :
    Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK htype
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_psl2_even hL.1 hZ3
    (e.trans (eS.trans (projSLEquivPSL (GaloisField 2 6)).symm))
  let eL : ↥L ≃* PSL2 (GaloisField 2 6) := (quotCenterEquivOfEqBot hZ).trans (e.trans eS)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hcK : ∀ k ∈ K', k * d = d * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hK'd hk)
  have hLC : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hc : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hkill : ∀ y ∈ L, y ≠ 1 → y ^ 3 = 1 → (∀ k ∈ K', k * y = y * k) → False := by
    intro y hyL hy1 hy3 hky
    have hcyc := isCyclic_centralizer eL (y := ⟨y, hyL⟩) (fun h => hy1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hy3))
    have hcomm : ∀ a ∈ K', ∀ b ∈ K', a * b = b * a := by
      intro a ha b hb
      have haC : (⟨a, hK'L ha⟩ : L) ∈ Subgroup.centralizer ({⟨y, hyL⟩} : Set L) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hky a ha))
      have hbC : (⟨b, hK'L hb⟩ : L) ∈ Subgroup.centralizer ({⟨y, hyL⟩} : Set L) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hky b hb))
      have h1 := (IsCyclic.isMulCommutative
        (α := Subgroup.centralizer ({⟨y, hyL⟩} : Set L))).is_comm.comm ⟨_, haC⟩ ⟨_, hbC⟩
      exact congrArg (fun z : Subgroup.centralizer ({⟨y, hyL⟩} : Set L) => ((z : L) : G)) h1
    haveI : Group.IsPerfect K' := hK'q.1
    haveI : Nontrivial K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'q
    haveI : IsMulCommutative K' := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative K' inferInstance
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hinner : ∀ y ∈ L, ¬ ∀ l ∈ L, d * l * d⁻¹ = y * l * y⁻¹ := by
    intro y hyL hy
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hLd
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hy l hl
      simp only [one_mul, inv_one, mul_one] at h1
      exact (calc d * l = d * l * d⁻¹ * d := by group
        _ = l * d := by rw [h1]).symm
    have hy3 : y ^ 3 = 1 := by
      have hp := conj_pow_eq_of_forall hyL hy 3
      apply hLC _ (pow_mem hyL 3)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hp l hl
      rw [hd3, one_mul, inv_one, mul_one] at h1
      calc l * y ^ 3 = y ^ 3 * l * (y ^ 3)⁻¹ * y ^ 3 := by rw [← h1]
        _ = y ^ 3 * l := by group
    refine hkill y hyL hy1 hy3 fun k hk => ?_
    have h1 := hy k (hK'L hk)
    have h2 : d * k * d⁻¹ = k := by rw [← hcK k hk]; group
    rw [h2] at h1
    calc k * y = y * k * y⁻¹ * y := by rw [← h1]
      _ = y * k := by group
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, -⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have h60 : 60 ∣ Nat.card K' := by
      obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
      rw [ha]
      exact Dvd.intro _ rfl
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 2 (dvd_trans (by norm_num) h60)
    obtain ⟨f₀, hf₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 (dvd_trans (by norm_num) h60)
    have hf3 : (f₀ : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hf₀, pow_orderOf_eq_one, Subgroup.coe_one]
    have hf1 : (f₀ : G) ≠ 1 := by
      intro h
      have : f₀ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hf₀
      norm_num at hf₀
    exact false_of_l264 hEF hA hAN hZ eL hdA hN hLd (hK'L t₀.2)
      (by rw [Subgroup.orderOf_coe]; exact ht₀) (hcK _ t₀.2) (hK'L f₀.2) hf3 hf1 (hcK _ f₀.2)
      hinner
  ·
    have hdL : d ∈ L := hK'L (hK' ▸ hdK)
    exact hinner d hdL fun l _ => rfl

theorem rowOf427_l264
    : RowOf427 (projSL 2 (GaloisField 2 6)) := by
  intro S _ _ _ _ ⟨eSX⟩
  exact row427_l264 (eSX.trans (projSLEquivPSL (GaloisField 2 6)))

theorem rowOf427_sl2
    : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSL 2 (GaloisField 2 n)) := by
  intro n hn
  by_cases h6 : n = 6
  · subst h6
    exact rowOf427_l264
  · exact rowOf427_sl2_of_ne_six hn h6

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
